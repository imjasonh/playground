use clap::Parser;
use std::io::Write as _;
use std::path::{Path, PathBuf};

use nescript::analyzer;
use nescript::assets::{BackgroundData, PaletteData};
use nescript::errors::render_diagnostics;
use nescript::linker::{
    render_dbg, render_fceux_nl, render_fceux_ram_nl, render_mlb, render_source_map, LinkedRom,
};
use nescript::pipeline::{compile_source, CompileError, CompileOptions as PipelineOptions};

#[derive(Parser)]
#[command(name = "nescript", about = "NEScript compiler — NES game development")]
enum Cli {
    /// Compile a .ne source file into a .nes ROM
    Build {
        /// Input source file
        input: PathBuf,

        /// Output ROM file (default: input with .nes extension)
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Enable debug mode (runtime checks, debug.log)
        #[arg(long)]
        debug: bool,

        /// Dump generated 6502 assembly to stdout
        #[arg(long)]
        asm_dump: bool,

        /// Dump the lowered IR program to stdout (after optimization)
        #[arg(long)]
        dump_ir: bool,

        /// Dump a human-readable memory map of variable allocations
        /// to stdout.
        #[arg(long)]
        memory_map: bool,

        /// Dump a call graph showing which functions call which.
        #[arg(long)]
        call_graph: bool,

        /// Skip the IR optimizer pass. Useful for bisecting
        /// optimizer-introduced miscompiles: if a program misbehaves
        /// with the optimizer on but works with `--no-opt`, the bug
        /// lives in `src/optimizer/`.
        #[arg(long)]
        no_opt: bool,

        /// Write a Mesen-compatible symbol file (`.mlb`) next to the
        /// ROM. Contains one `<type>:<address>:<label>` entry per
        /// function, state handler, and user variable. Enables
        /// symbol-level debugging in Mesen / fceux without manual
        /// address lookups.
        #[arg(long, value_name = "PATH")]
        symbols: Option<PathBuf>,

        /// Write a plain-text source map (`.map`) next to the ROM.
        /// Each line has the form `<rom_offset_hex> <file_id>
        /// <line> <col>` and records the position of every IR-level
        /// statement in the assembled fixed bank. Useful for
        /// reverse-mapping a crash address back to the source.
        #[arg(long, value_name = "PATH")]
        source_map: Option<PathBuf>,

        /// Write a ca65-compatible debug-info file (`.dbg`) next
        /// to the ROM. The format is the same one `ld65` emits,
        /// so Mesen / Mesen2 / fceuX pick it up automatically and
        /// enable source-level stepping, labelled variable
        /// inspection, and symbol-based breakpoints. Implies
        /// `--source-map`-style `__src_<N>` marker emission so
        /// line records have something to point at.
        #[arg(long, value_name = "PATH")]
        dbg: Option<PathBuf>,

        /// Emit FCEUX-compatible per-bank `.nl` label files and a
        /// `.ram.nl` file next to the ROM. The argument is the
        /// prefix; FCEUX appends `.<bank>.nl` / `.ram.nl`. Unlike
        /// `.dbg` (which Mesen/Mesen2 understand natively), the
        /// `.nl` format is what FCEUX on Linux reads, and many
        /// users still prefer FCEUX over Mesen for its lighter
        /// footprint.
        #[arg(long, value_name = "PREFIX")]
        fceux_labels: Option<PathBuf>,
    },
    /// Type-check a source file without building
    Check {
        /// Input source file
        input: PathBuf,
    },
}

fn main() {
    let cli = Cli::parse();

    match cli {
        Cli::Build {
            input,
            output,
            debug,
            asm_dump,
            dump_ir,
            memory_map,
            call_graph,
            no_opt,
            symbols,
            source_map,
            dbg,
            fceux_labels,
        } => {
            let output = output.unwrap_or_else(|| input.with_extension("nes"));
            match compile(
                &input,
                &output,
                &CompileOptions {
                    debug,
                    asm_dump,
                    dump_ir,
                    memory_map,
                    call_graph,
                    no_opt,
                    symbols: symbols.clone(),
                    source_map: source_map.clone(),
                    dbg: dbg.clone(),
                    fceux_labels: fceux_labels.clone(),
                },
            ) {
                Ok(rom) => {
                    std::fs::write(&output, rom).unwrap_or_else(|e| {
                        eprintln!("error: failed to write {}: {e}", output.display());
                        std::process::exit(1);
                    });
                    println!(
                        "compiled {} -> {} ({} bytes)",
                        input.display(),
                        output.display(),
                        std::fs::metadata(&output).map_or(0, |m| m.len())
                    );
                }
                Err(()) => std::process::exit(1),
            }
        }
        Cli::Check { input } => match check(&input) {
            Ok(()) => println!("no errors found in {}", input.display()),
            Err(()) => std::process::exit(1),
        },
    }
}

/// Write a human-readable memory map of variable allocations to
/// `w`. Entries are sorted by address and labelled with their scope
/// (zero-page vs RAM). When `link_result` is `Some(_)`, a PRG ROM
/// section listing each palette and background data blob's CPU
/// address + size is appended — the CLI passes the linker result
/// whenever it's available, which is always unless the caller is
/// unit-testing the variable-only path.
///
/// This function is factored out of the direct `println!` path so
/// tests can drive it against an in-memory buffer and assert on the
/// rendered output.
fn write_memory_map(
    w: &mut impl std::io::Write,
    analysis: &nescript::analyzer::AnalysisResult,
    link_result: Option<&LinkedRom>,
    palettes: &[PaletteData],
    backgrounds: &[BackgroundData],
) -> std::io::Result<()> {
    let mut allocs: Vec<_> = analysis.var_allocations.iter().collect();
    // Sort by address, then by state-local owner (None before Some),
    // so the memory map groups overlaid state-locals together under
    // their shared base address.
    allocs.sort_by(|a, b| {
        a.address.cmp(&b.address).then_with(|| {
            analysis
                .state_local_owners
                .get(&a.name)
                .cmp(&analysis.state_local_owners.get(&b.name))
        })
    });

    let fmt_tag = |name: &str| -> String {
        match analysis.state_local_owners.get(name) {
            Some(state) => format!("[@{state}]"),
            None => "[USER]   ".to_string(),
        }
    };

    writeln!(w, "=== NEScript Memory Map ===")?;
    writeln!(w, "Zero Page ($00-$FF):")?;
    writeln!(
        w,
        "  $00-$0F  [SYSTEM]  reserved (frame flag, input, state, params, scratch)"
    )?;
    for a in allocs.iter().filter(|a| a.address < 0x100) {
        let tag = fmt_tag(&a.name);
        if a.size == 1 {
            writeln!(w, "  ${:04X}    {} {} (u8)", a.address, tag, a.name)?;
        } else {
            writeln!(
                w,
                "  ${:04X}-${:04X}  {} {} ({} bytes)",
                a.address,
                a.address + a.size - 1,
                tag,
                a.name,
                a.size
            )?;
        }
    }

    let ram_allocs: Vec<_> = allocs.iter().filter(|a| a.address >= 0x100).collect();
    if !ram_allocs.is_empty() {
        writeln!(w, "\nRAM ($0200-$07FF):")?;
        writeln!(w, "  $0200-$02FF  [SYSTEM]  OAM shadow buffer")?;
        for a in &ram_allocs {
            let tag = fmt_tag(&a.name);
            if a.size == 1 {
                writeln!(w, "  ${:04X}        {} {} (u8)", a.address, tag, a.name)?;
            } else {
                writeln!(
                    w,
                    "  ${:04X}-${:04X}  {} {} ({} bytes)",
                    a.address,
                    a.address + a.size - 1,
                    tag,
                    a.name,
                    a.size
                )?;
            }
        }
    }

    // Summary counts distinct byte addresses in use, not the sum of
    // allocation sizes, so overlaid state-locals are only counted
    // once per shared byte. Non-state-local allocations and the
    // per-state allocations each contribute their own bytes.
    let mut zp_bytes_used: std::collections::HashSet<u16> = std::collections::HashSet::new();
    let mut ram_bytes_used: std::collections::HashSet<u16> = std::collections::HashSet::new();
    for a in &allocs {
        for offset in 0..a.size {
            let byte = a.address + offset;
            if byte < 0x80 {
                zp_bytes_used.insert(byte);
            } else if byte >= 0x300 {
                ram_bytes_used.insert(byte);
            }
        }
    }
    let zp_used = zp_bytes_used.len();
    let ram_used = ram_bytes_used.len();
    writeln!(w)?;
    writeln!(w, "Zero Page: {zp_used}/128 bytes used")?;
    writeln!(w, "Main RAM:  {ram_used}/1280 bytes used")?;

    // PRG ROM: palette (32 B each) and background (960 + 64 B each)
    // data blobs. The linker emits each one under a well-known
    // label — `__palette_<name>`, `__bg_tiles_<name>`,
    // `__bg_attrs_<name>` — so we look those up in the label table
    // and render the CPU address + byte count.
    if let Some(link) = link_result {
        if !palettes.is_empty() || !backgrounds.is_empty() {
            writeln!(w, "\nPRG ROM data blobs:")?;
            let mut total: u32 = 0;
            for pal in palettes {
                let label = pal.label();
                match link.labels.get(&label).copied() {
                    Some(addr) => {
                        writeln!(w, "  ${addr:04X}        [PALETTE] {} (32 bytes)", pal.name)?;
                    }
                    None => {
                        writeln!(w, "  (unlinked)   [PALETTE] {} (32 bytes)", pal.name)?;
                    }
                }
                total += 32;
            }
            for bg in backgrounds {
                let tiles_label = bg.tiles_label();
                let attrs_label = bg.attrs_label();
                match link.labels.get(&tiles_label).copied() {
                    Some(addr) => {
                        writeln!(w, "  ${addr:04X}        [BG-TILES] {} (960 bytes)", bg.name)?;
                    }
                    None => {
                        writeln!(w, "  (unlinked)   [BG-TILES] {} (960 bytes)", bg.name)?;
                    }
                }
                match link.labels.get(&attrs_label).copied() {
                    Some(addr) => {
                        writeln!(w, "  ${addr:04X}        [BG-ATTRS] {} (64 bytes)", bg.name)?;
                    }
                    None => {
                        writeln!(w, "  (unlinked)   [BG-ATTRS] {} (64 bytes)", bg.name)?;
                    }
                }
                total += 960 + 64;
            }
            writeln!(w, "\nPRG ROM data total: {total} bytes")?;
        }
    }

    Ok(())
}

/// Print a human-readable memory map of variable allocations. Thin
/// wrapper around [`write_memory_map`] that drives stdout; tests
/// call `write_memory_map` directly against a `Vec<u8>`.
fn print_memory_map(
    analysis: &nescript::analyzer::AnalysisResult,
    link_result: Option<&LinkedRom>,
    palettes: &[PaletteData],
    backgrounds: &[BackgroundData],
) {
    let stdout = std::io::stdout();
    let mut handle = stdout.lock();
    // Infallible: stdout writes only return Err on broken pipes,
    // which is the caller's problem.
    let _ = write_memory_map(&mut handle, analysis, link_result, palettes, backgrounds);
    let _ = handle.flush();
}

/// Print a human-readable call graph of the analyzed program.
/// Entries show the max call depth reached from each entry point
/// (state handler) and the transitive callees.
fn print_call_graph(analysis: &nescript::analyzer::AnalysisResult) {
    use std::collections::BTreeMap;

    let sorted: BTreeMap<_, _> = analysis
        .call_graph
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    let max_depth = analysis.max_depths.values().copied().max().unwrap_or(0);

    println!("=== Call Graph (max depth: {max_depth} / 8) ===");
    if sorted.is_empty() {
        println!("  (no functions or handlers)");
        return;
    }
    for (caller, callees) in &sorted {
        if let Some(depth) = analysis.max_depths.get(caller) {
            println!("{caller} (max depth {depth})");
        } else {
            println!("{caller}");
        }
        if callees.is_empty() {
            println!("  └── (leaf)");
        } else {
            let count = callees.len();
            for (i, callee) in callees.iter().enumerate() {
                let branch = if i + 1 == count {
                    "└──"
                } else {
                    "├──"
                };
                println!("  {branch} {callee}");
            }
        }
    }
}

fn dump_asm(instructions: &[nescript::asm::Instruction]) {
    use nescript::asm::{AddressingMode, Opcode};
    for inst in instructions {
        // A bare `NOP` with a `Label` operand is a label *definition*
        // (the pseudo-instruction the codegen emits when marking a
        // position). Any other opcode with `Label` mode is an actual
        // instruction like `JSR foo` or `JMP bar`, so we show the
        // opcode + target.
        if inst.opcode == Opcode::NOP {
            if let AddressingMode::Label(name) = &inst.mode {
                println!("{name}:");
                continue;
            }
        }
        println!("    {:?} {:?}", inst.opcode, inst.mode);
    }
}

#[allow(clippy::struct_excessive_bools)]
struct CompileOptions {
    debug: bool,
    asm_dump: bool,
    dump_ir: bool,
    memory_map: bool,
    call_graph: bool,
    no_opt: bool,
    symbols: Option<PathBuf>,
    source_map: Option<PathBuf>,
    dbg: Option<PathBuf>,
    fceux_labels: Option<PathBuf>,
}

fn compile(input: &PathBuf, output: &Path, opts: &CompileOptions) -> Result<Vec<u8>, ()> {
    // File I/O + preprocessing lives here so the pipeline module
    // itself doesn't need to touch `std::fs`. That keeps the
    // pipeline usable from a future WASM host that routes asset
    // reads through a trait.
    let raw_source = std::fs::read_to_string(input).map_err(|e| {
        eprintln!("error: failed to read {}: {e}", input.display());
    })?;
    let source = nescript::parser::preprocess_source(&raw_source, Some(input)).map_err(|e| {
        eprintln!("error: {e}");
    })?;
    let filename = input.to_string_lossy();
    let source_dir = input.parent().unwrap_or_else(|| Path::new("."));

    // Hand everything else off to the shared pipeline function
    // so the CLI, the `compile` bench, and the integration-test
    // helper all run the same compile path. When this block
    // needs a new feature (new flag, new output, whatever), the
    // change lands in `pipeline::compile_source` and every
    // caller picks it up automatically.
    //
    // `--dbg` reuses the same `__src_<N>` markers that
    // `--source-map` emits, so either flag flips on source-loc
    // emission in the codegen.
    let pipeline_opts = PipelineOptions {
        debug: opts.debug,
        no_opt: opts.no_opt,
        emit_source_map: opts.source_map.is_some() || opts.dbg.is_some(),
    };
    let out = compile_source(&source, source_dir, &pipeline_opts).map_err(|e| match e {
        CompileError::Parse(diags) => {
            render_diagnostics(&source, &filename, &diags);
        }
        CompileError::ParseProducedNothing => {
            // The parser returned `None` with no diagnostics.
            // Extremely unusual (empty input or similar) and
            // there's nothing for the user to act on beyond a
            // generic message.
            eprintln!("error: parser produced no program");
        }
        CompileError::Analyze(diags) => {
            render_diagnostics(&source, &filename, &diags);
        }
        CompileError::AssetResolution(msg) => {
            eprintln!("error: {msg}");
        }
    })?;

    // Render any analyzer warnings that survived a successful
    // compile. Errors would have taken the `CompileError::Analyze`
    // path above and returned before we got here, so everything
    // left in `out.analysis.diagnostics` is a warning (W01xx).
    // Without this the CLI would silently swallow every warning
    // on a successful build, making them effectively invisible
    // — the warning machinery in the analyzer would still run,
    // but nobody would ever see its output unless they also
    // invoked `nescript check`.
    if !out.analysis.diagnostics.is_empty() {
        render_diagnostics(&source, &filename, &out.analysis.diagnostics);
    }

    // Post-link CLI-only side effects: the various `--dump-*`
    // flags and the two optional file outputs. These are not
    // part of the pipeline because they're stdout / filesystem
    // I/O, not compilation.
    if opts.dump_ir {
        print!("{}", out.ir_program.pretty());
    }
    if opts.call_graph {
        print_call_graph(&out.analysis);
    }
    if opts.asm_dump {
        dump_asm(&out.instructions);
    }
    if opts.memory_map {
        print_memory_map(
            &out.analysis,
            Some(&out.link_result),
            &out.palettes,
            &out.backgrounds,
        );
    }
    if let Some(path) = opts.symbols.as_ref() {
        let mlb = render_mlb(&out.link_result, &out.analysis.var_allocations);
        std::fs::write(path, mlb).map_err(|e| {
            eprintln!("error: failed to write symbol file {}: {e}", path.display());
        })?;
    }
    if let Some(path) = opts.source_map.as_ref() {
        let map = render_source_map(&out.link_result, &out.source_locs, &source);
        std::fs::write(path, map).map_err(|e| {
            eprintln!("error: failed to write source map {}: {e}", path.display());
        })?;
    }
    if let Some(path) = opts.dbg.as_ref() {
        let dbg = render_dbg(
            &out.link_result,
            &out.source_locs,
            &out.analysis.var_allocations,
            &source,
            input,
            output,
        );
        std::fs::write(path, dbg).map_err(|e| {
            eprintln!("error: failed to write dbg file {}: {e}", path.display());
        })?;
    }
    if let Some(prefix) = opts.fceux_labels.as_ref() {
        // FCEUX looks for `<rom-name>.<bank-index>.nl` per-bank and
        // `<rom-name>.ram.nl` for RAM symbols, where `<rom-name>`
        // is literally the ROM file name (typically something like
        // `foo.nes`). We treat `--fceux-labels <prefix>` as exactly
        // that stem and *append* the `.<bank>.nl` suffix rather than
        // using `with_extension` (which would strip whatever came
        // after the first `.`). This lets users pass either
        // `--fceux-labels foo` (→ foo.0.nl, foo.ram.nl) or
        // `--fceux-labels foo.nes` (→ foo.nes.0.nl, foo.nes.ram.nl,
        // matching FCEUX's default search paths).
        //
        // The fixed bank is always the last physical bank in the
        // ROM, so for a single-bank NROM layout the index is 0 and
        // for banked ROMs it's `total_banks - 1`. We derive the
        // index from the linker's reported fixed-bank file offset:
        // `(offset - 16) / PRG_BANK_SIZE`.
        const PRG_BANK_SIZE: usize = 16384;
        let bank_index = out.link_result.fixed_bank_file_offset.saturating_sub(16) / PRG_BANK_SIZE;
        let bank_nl = render_fceux_nl(&out.link_result);
        let bank_path = {
            let mut p = prefix.as_os_str().to_os_string();
            p.push(format!(".{bank_index}.nl"));
            PathBuf::from(p)
        };
        std::fs::write(&bank_path, bank_nl).map_err(|e| {
            eprintln!(
                "error: failed to write FCEUX bank label file {}: {e}",
                bank_path.display()
            );
        })?;
        let ram_nl = render_fceux_ram_nl(&out.analysis.var_allocations);
        let ram_path = {
            let mut p = prefix.as_os_str().to_os_string();
            p.push(".ram.nl");
            PathBuf::from(p)
        };
        std::fs::write(&ram_path, ram_nl).map_err(|e| {
            eprintln!(
                "error: failed to write FCEUX RAM label file {}: {e}",
                ram_path.display()
            );
        })?;
    }

    Ok(out.rom)
}

fn check(input: &PathBuf) -> Result<(), ()> {
    let raw_source = std::fs::read_to_string(input).map_err(|e| {
        eprintln!("error: failed to read {}: {e}", input.display());
    })?;

    let source = nescript::parser::preprocess_source(&raw_source, Some(input)).map_err(|e| {
        eprintln!("error: {e}");
    })?;

    let filename = input.to_string_lossy();

    let (program, parse_diags) = nescript::parser::parse(&source);
    if !parse_diags.is_empty() {
        render_diagnostics(&source, &filename, &parse_diags);
    }
    if parse_diags
        .iter()
        .any(nescript::errors::Diagnostic::is_error)
    {
        return Err(());
    }
    let program = program.ok_or(())?;

    let analysis = analyzer::analyze(&program);
    if !analysis.diagnostics.is_empty() {
        render_diagnostics(&source, &filename, &analysis.diagnostics);
    }
    if analysis
        .diagnostics
        .iter()
        .any(nescript::errors::Diagnostic::is_error)
    {
        return Err(());
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use nescript::analyzer::AnalysisResult;
    use nescript::linker::LinkedRom;
    use std::collections::HashMap;

    fn empty_analysis() -> AnalysisResult {
        AnalysisResult {
            symbols: HashMap::new(),
            var_allocations: Vec::new(),
            diagnostics: Vec::new(),
            call_graph: HashMap::new(),
            max_depths: HashMap::new(),
            state_local_owners: HashMap::new(),
            has_battery_saves: false,
        }
    }

    #[test]
    fn write_memory_map_without_link_result_covers_variable_path() {
        // Without a link result (e.g. the unit-test path that
        // only wants to inspect the variable allocator) the output
        // should still render the Zero Page / RAM sections and the
        // summary lines. No PRG ROM section appears because there
        // are no linked labels to point at.
        let analysis = empty_analysis();
        let mut buf = Vec::new();
        write_memory_map(&mut buf, &analysis, None, &[], &[]).unwrap();
        let s = String::from_utf8(buf).unwrap();
        assert!(s.contains("=== NEScript Memory Map ==="));
        assert!(s.contains("Zero Page"));
        assert!(s.contains("0/128 bytes used"));
        assert!(!s.contains("PRG ROM data blobs"));
    }

    #[test]
    fn write_memory_map_reports_palette_and_background_rom_addresses() {
        // With palettes and backgrounds plus a faked LinkedRom
        // carrying matching labels, the PRG ROM section should
        // render each blob's CPU address + size and a grand total.
        let analysis = empty_analysis();
        let palettes = vec![PaletteData {
            name: "Main".to_string(),
            colors: [0u8; 32],
        }];
        let backgrounds = vec![BackgroundData {
            name: "Stage".to_string(),
            tiles: [0u8; 960],
            attrs: [0u8; 64],
            chr_bytes: Vec::new(),
            chr_base_tile: 0,
        }];
        let mut labels = HashMap::new();
        labels.insert("__palette_Main".to_string(), 0xC100);
        labels.insert("__bg_tiles_Stage".to_string(), 0xC200);
        labels.insert("__bg_attrs_Stage".to_string(), 0xC5C0);
        let link = LinkedRom {
            rom: Vec::new(),
            labels,
            fixed_bank_file_offset: 16,
        };
        let mut buf = Vec::new();
        write_memory_map(&mut buf, &analysis, Some(&link), &palettes, &backgrounds).unwrap();
        let s = String::from_utf8(buf).unwrap();
        assert!(s.contains("PRG ROM data blobs:"));
        assert!(
            s.contains("$C100") && s.contains("[PALETTE] Main"),
            "missing palette line in: {s}"
        );
        assert!(
            s.contains("$C200") && s.contains("[BG-TILES] Stage"),
            "missing bg-tiles line in: {s}"
        );
        assert!(
            s.contains("$C5C0") && s.contains("[BG-ATTRS] Stage"),
            "missing bg-attrs line in: {s}"
        );
        // 32 (palette) + 960 + 64 (background) = 1056.
        assert!(s.contains("1056 bytes"), "missing total in: {s}");
    }

    #[test]
    fn write_memory_map_marks_unlinked_blobs() {
        // If a palette's label isn't in `link.labels` (e.g. the
        // linker skipped it for some reason), we still emit the
        // line but mark it "(unlinked)" so the user knows the
        // address isn't available.
        let analysis = empty_analysis();
        let palettes = vec![PaletteData {
            name: "Ghost".to_string(),
            colors: [0u8; 32],
        }];
        let link = LinkedRom {
            rom: Vec::new(),
            labels: HashMap::new(),
            fixed_bank_file_offset: 16,
        };
        let mut buf = Vec::new();
        write_memory_map(&mut buf, &analysis, Some(&link), &palettes, &[]).unwrap();
        let s = String::from_utf8(buf).unwrap();
        assert!(s.contains("(unlinked)"), "missing unlinked marker in: {s}");
        assert!(s.contains("[PALETTE] Ghost"));
    }
}
