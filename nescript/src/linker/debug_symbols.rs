//! Debug-symbol file writers.
//!
//! Produces Mesen-compatible `.mlb` label listings, plain-text source
//! maps, and ca65-compatible `.dbg` debug-info files from a
//! [`LinkedRom`]. These helpers are owned by the linker because
//! they're the only place in the compiler that can observe the final
//! CPU address of each label — and the CPU-to-ROM offset math needs
//! the `fixed_bank_file_offset` the linker hands back.
//!
//! Callers: `src/main.rs` invokes [`render_mlb`] when the user
//! passes `--symbols <path>`, [`render_source_map`] when the user
//! passes `--source-map <path>`, and [`render_dbg`] when the user
//! passes `--dbg <path>`. The functions themselves are pure string
//! producers so that unit tests can round-trip them without
//! touching the filesystem.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::Path;

use super::LinkedRom;
use crate::analyzer::VarAllocation;
use crate::lexer::Span;

/// Render an FCEUX-compatible label file for the fixed PRG bank.
///
/// FCEUX looks for `<rom-name>.<bank-index>.nl` per-bank label files
/// in the same directory as the ROM, then for a `<rom-name>.ram.nl`
/// for RAM/zero-page labels. Each line in a bank file has the form
/// `$XXXX#label_name#`, where `$XXXX` is the CPU address inside the
/// bank window (matching whatever the fixed bank is mapped at at
/// runtime — for `NEScript`, `$C000-$FFFF`). RAM entries use
/// `$XXXX#name#` in the `.ram.nl` file; FCEUX doesn't namespace
/// these per-bank.
///
/// Returns the bank-file contents. The caller is responsible for
/// writing it to disk under the correct per-bank name. RAM-label
/// output is produced by [`render_fceux_ram_nl`] below.
#[must_use]
pub fn render_fceux_nl(linked: &LinkedRom) -> String {
    let mut out = String::new();
    let sorted: BTreeMap<&String, &u16> = linked.labels.iter().collect();
    for (label, &&cpu_addr) in &sorted {
        let Some(display_name) = mlb_symbol_name(label) else {
            continue;
        };
        // FCEUX expects CPU addresses inside the bank window. The
        // fixed bank is always at $C000-$FFFF, which is what the
        // codegen emits, so the address passes through unchanged.
        let _ = writeln!(out, "${cpu_addr:04X}#{display_name}#");
    }
    out
}

/// Render an FCEUX-compatible RAM label file (`<rom>.ram.nl`).
/// Addresses are the analyzer's variable allocations (zero page
/// and main RAM) in ascending order.
#[must_use]
pub fn render_fceux_ram_nl(var_allocations: &[VarAllocation]) -> String {
    let mut out = String::new();
    let mut vars: Vec<&VarAllocation> = var_allocations.iter().collect();
    vars.sort_by_key(|a| a.address);
    for var in vars {
        let _ = writeln!(out, "${:04X}#{}#", var.address, var.name);
    }
    out
}

/// Render a Mesen-compatible `.mlb` symbol file from a
/// [`LinkedRom`].
///
/// Each line has the form `<type>:<hex-address>:<label>`. The type
/// byte follows Mesen's convention: `P` for PRG ROM offsets and
/// `R` for RAM (zero page and internal RAM share this namespace
/// because zero page is just the low 256 bytes of RAM on the NES).
///
/// Function and state-handler labels are emitted as `P` entries
/// with the address converted from a CPU address in `$C000-$FFFF`
/// into a PRG-relative ROM offset via
/// `linked.fixed_bank_file_offset`. User variables come from the
/// analyzer's `var_allocations` list and are emitted as `R`
/// entries at their assigned RAM addresses.
///
/// Internal labels (anything that doesn't look like a user
/// function or a well-known entry point) are skipped so the
/// resulting file focuses on the symbols a debugger user actually
/// cares about. Output is sorted deterministically so the file is
/// diff-friendly and so tests can assert against exact strings.
#[must_use]
pub fn render_mlb(linked: &LinkedRom, var_allocations: &[VarAllocation]) -> String {
    let mut out = String::new();

    let sorted: BTreeMap<&String, &u16> = linked.labels.iter().collect();
    let base_cpu_addr: u16 = 0xC000;
    for (label, &&cpu_addr) in &sorted {
        // Only translate labels that sit inside the fixed bank's
        // CPU window. In practice every label in `linked.labels`
        // already lives here (the assembler works on a single
        // bank at a time), but we guard anyway so a future
        // multi-bank label dump doesn't silently emit garbage
        // offsets.
        if cpu_addr < base_cpu_addr {
            continue;
        }
        let Some(display_name) = mlb_symbol_name(label) else {
            continue;
        };
        let rom_offset = linked.fixed_bank_file_offset + (cpu_addr - base_cpu_addr) as usize;
        // Mesen uses ROM file offsets *relative to the start of
        // the PRG region* (i.e. subtract the 16-byte header).
        // This keeps `.mlb` files portable between NES 2.0 and
        // iNES 1 headers.
        let prg_offset = rom_offset.saturating_sub(16);
        let _ = writeln!(out, "P:{prg_offset:04X}:{display_name}");
    }

    // Variables — emit in address order so the file is easy to
    // eyeball and diff. Duplicate names (e.g. struct fields under
    // two synthetic entries) are rare; when they do occur we keep
    // the first encounter.
    let mut vars: Vec<&VarAllocation> = var_allocations.iter().collect();
    vars.sort_by_key(|a| a.address);
    for var in vars {
        let _ = writeln!(out, "R:{:04X}:{}", var.address, var.name);
    }

    out
}

/// Determine whether a label should appear in the `.mlb` symbol
/// table, and if so under what name. Returns `None` for labels
/// that are internal bookkeeping (branch/skip stubs, temporary
/// jump targets) and wouldn't help a user navigate the ROM.
fn mlb_symbol_name(label: &str) -> Option<String> {
    // Function/state entry labels — strip the `__ir_fn_` prefix so
    // Mesen displays the user-facing name. `__ir_fn_Main_frame`
    // becomes `Main_frame`, for example.
    if let Some(rest) = label.strip_prefix("__ir_fn_") {
        return Some(rest.to_string());
    }
    // Bank trampolines and the main loop entry are useful entry
    // points for a reverse-engineering session.
    if label == "__ir_main_loop" {
        return Some("main_loop".to_string());
    }
    if let Some(rest) = label.strip_prefix("__tramp_") {
        return Some(format!("tramp_{rest}"));
    }
    // Hardware entry points. These are always present and
    // useful.
    if matches!(label, "__reset" | "__nmi" | "__irq" | "__irq_user") {
        return Some(label.trim_start_matches('_').to_string());
    }
    // Source-map markers are written to their own file via
    // `render_source_map`, not here.
    if label.starts_with("__src_") {
        return None;
    }
    // Everything else — per-block labels, fallthrough skips,
    // compiler-private helpers — gets filtered out to keep the
    // symbol file short and navigable.
    None
}

/// Render a plain-text source map from a [`LinkedRom`].
///
/// Each line has the form `<rom_offset_hex> <file_id> <line> <col>`.
/// Entries come from the `__src_<N>` marker labels the IR
/// codegen emits for every [`crate::ir::IrOp::SourceLoc`] — one
/// per lowered source statement — paired against their original
/// spans via the codegen's `source_locs` side table passed in as
/// `source_locs`.
///
/// `source` is the preprocessed source text. We translate each
/// span's byte offset into a `(line, col)` pair by scanning
/// through the source once. Files included via `include` share
/// the same file id in the preprocessed text, so a single scan
/// covers every entry.
///
/// The output is sorted by ROM offset so the file is diff-
/// friendly and so downstream tools can binary-search by address.
#[must_use]
pub fn render_source_map(
    linked: &LinkedRom,
    source_locs: &[(String, Span)],
    source: &str,
) -> String {
    let mut entries: Vec<(usize, u16, u32, u32)> = Vec::new();
    let base_cpu_addr: u16 = 0xC000;
    for (label, span) in source_locs {
        let Some(&cpu_addr) = linked.labels.get(label) else {
            continue;
        };
        if cpu_addr < base_cpu_addr {
            continue;
        }
        let rom_offset = linked.fixed_bank_file_offset + (cpu_addr - base_cpu_addr) as usize;
        let prg_offset = rom_offset.saturating_sub(16);
        let (line, col) = byte_offset_to_line_col(source, span.start as usize);
        entries.push((prg_offset, span.file_id, line, col));
    }
    entries.sort_unstable();

    let mut out = String::new();
    for (offset, file_id, line, col) in entries {
        let _ = writeln!(out, "{offset:04X} {file_id} {line} {col}");
    }
    out
}

/// Convert a byte offset into `source` into a 1-based
/// `(line, column)` pair. Used by the source-map emitter to
/// translate the compact byte-offset spans carried inside
/// [`crate::lexer::Span`] into human-readable positions. Offsets
/// past the end of the source clamp to the last line.
fn byte_offset_to_line_col(source: &str, offset: usize) -> (u32, u32) {
    let bytes = source.as_bytes();
    let limit = offset.min(bytes.len());
    let mut line: u32 = 1;
    let mut col: u32 = 1;
    for &b in &bytes[..limit] {
        if b == b'\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

/// Render a ca65-compatible `.dbg` debug-info file from a
/// [`LinkedRom`].
///
/// The `.dbg` format is the text-based side channel that `ld65`
/// emits alongside assembled binaries; source-level NES debuggers
/// (Mesen, Mesen2, `fceuX`) read it to let the user step by source
/// line, inspect labelled variables, and set breakpoints on
/// function names instead of raw addresses. `NEScript` isn't built
/// on top of ca65, but we synthesize a conformant file from the
/// same metadata the `.mlb` and `--source-map` writers use: the
/// linker's label table, the IR codegen's `__src_<N>` markers, and
/// the analyzer's variable allocations.
///
/// The emitted file contains:
///
/// * One `file` record for `input_path` — the preprocessed `.ne`
///   source the compiler parsed. All `SourceLoc` spans have
///   `file_id=0` (the preprocessor concatenates includes into a
///   single buffer, see `parser::preprocess`), so one file record
///   is enough.
/// * One `mod` record naming the build.
/// * One `seg` record covering the fixed bank at `$C000-$FFFF`,
///   with `ooffs` set to the PRG-relative byte offset of the fixed
///   bank's first byte. Mesen uses `ooffs + start - $C000` to map
///   a CPU address inside the segment to a ROM file byte.
/// * One `scope` record for the segment.
/// * One `span` + one `line` record for every `__src_<N>` marker
///   whose label resolved to a CPU address in the fixed bank. Each
///   span's size stretches from its own PRG offset to the next
///   sorted marker's PRG offset (and the last span runs to the end
///   of the fixed bank), so Mesen's source-line breakpoints cover
///   every byte the IR statement compiled into.
/// * One `sym` record per filtered code label (functions, state
///   handlers, hardware entry points, bank trampolines, main loop)
///   and one per user variable allocation. Code symbols carry
///   `seg=0`; variable symbols omit `seg` and use `addrsize=zeropage`
///   for zero-page addresses, `absolute` otherwise.
///
/// `output_path` is recorded in the segment's `oname=` field so
/// Mesen can verify that the `.dbg` matches the ROM it was built
/// alongside.
#[must_use]
pub fn render_dbg(
    linked: &LinkedRom,
    source_locs: &[(String, Span)],
    var_allocations: &[VarAllocation],
    source: &str,
    input_path: &Path,
    output_path: &Path,
) -> String {
    let base_cpu_addr: u16 = 0xC000;
    let fixed_bank_size: u32 = 0x4000;
    // Output-file byte offset of the first byte of the fixed bank.
    // `fixed_bank_file_offset` is measured from the iNES file start
    // (i.e., including the 16-byte iNES header), which is exactly
    // what ca65's `ooffs=` field wants. Mesen's DbgImporter computes
    // the final label address as `val - seg.start + ooffs - 16`
    // (the iNES header size), so passing the header-inclusive file
    // offset makes labels resolve to PRG-relative byte offsets —
    // matching the `.mlb` symbol-file convention the rest of the
    // toolchain uses. An earlier version of this code subtracted 16
    // here; that shifted every `.dbg` label 16 bytes past its real
    // PRG offset, which confused Mesen's source-line mapping for
    // the first few bytes of each function.
    let ooffs: usize = linked.fixed_bank_file_offset;

    // -------- spans + lines from source_locs --------
    //
    // Resolve each `__src_<N>` marker to its PRG offset (relative
    // to the start of the fixed bank) and collect with the span it
    // came from. Labels without a matching entry in `linked.labels`
    // are dropped — they can arise if the peephole pass folded
    // the marker away — and so are any addresses outside the
    // fixed bank window.
    let mut src_entries: Vec<(u32, &Span)> = Vec::new();
    for (label, span) in source_locs {
        let Some(&cpu_addr) = linked.labels.get(label) else {
            continue;
        };
        if cpu_addr < base_cpu_addr {
            continue;
        }
        let bank_offset = u32::from(cpu_addr - base_cpu_addr);
        src_entries.push((bank_offset, span));
    }
    // Sort by bank offset ascending; on ties, older entries win.
    src_entries.sort_by_key(|(off, _)| *off);
    src_entries.dedup_by_key(|(off, _)| *off);

    // Compute each span's size as the distance to the next marker.
    // The last marker stretches to the end of the fixed bank. Spans
    // of width 0 would be invalid, so we clamp to 1.
    let mut spans: Vec<(u32, u32)> = Vec::with_capacity(src_entries.len());
    for (i, (off, _span)) in src_entries.iter().enumerate() {
        let next_off = src_entries.get(i + 1).map_or(fixed_bank_size, |(n, _)| *n);
        let size = next_off.saturating_sub(*off).max(1);
        spans.push((*off, size));
    }

    // -------- symbol list --------
    //
    // Code labels from `linked.labels`, filtered through the same
    // user-friendly renamer the `.mlb` writer uses so internal
    // scaffolding (per-block skip labels, source-loc markers)
    // stays out of the debugger's symbol browser.
    let sorted_labels: BTreeMap<&String, &u16> = linked.labels.iter().collect();
    let mut code_syms: Vec<(String, u16)> = Vec::new();
    for (label, &&cpu_addr) in &sorted_labels {
        if cpu_addr < base_cpu_addr {
            continue;
        }
        let Some(display_name) = mlb_symbol_name(label) else {
            continue;
        };
        code_syms.push((display_name, cpu_addr));
    }

    let mut var_syms: Vec<&VarAllocation> = var_allocations.iter().collect();
    var_syms.sort_by_key(|a| a.address);

    let file_count = 1usize;
    let mod_count = 1usize;
    let scope_count = 1usize;
    let seg_count = 1usize;
    let line_count = src_entries.len();
    let span_count = spans.len();
    let sym_count = code_syms.len() + var_syms.len();

    let mut out = String::new();
    let _ = writeln!(out, "version\tmajor=2,minor=0");
    let _ = writeln!(
        out,
        "info\tcsym=0,file={file_count},lib=0,line={line_count},mod={mod_count},scope={scope_count},seg={seg_count},span={span_count},sym={sym_count},type=0"
    );

    // --- file ---
    let source_bytes = source.len();
    let file_name = escape_string(&input_path.display().to_string());
    let _ = writeln!(
        out,
        "file\tid=0,name=\"{file_name}\",size={source_bytes},mtime=0x00000000,mod=0"
    );

    // --- mod ---
    let mod_name = escape_string(
        input_path
            .file_stem()
            .map_or_else(
                || "program".to_string(),
                |s| s.to_string_lossy().into_owned(),
            )
            .as_str(),
    );
    let _ = writeln!(out, "mod\tid=0,name=\"{mod_name}\",file=0");

    // --- seg ---
    let seg_oname = escape_string(&output_path.display().to_string());
    let _ = writeln!(
        out,
        "seg\tid=0,name=\"CODE\",start=0x{base_cpu_addr:04X},size=0x{fixed_bank_size:04X},addrsize=absolute,type=ro,oname=\"{seg_oname}\",ooffs={ooffs}"
    );

    // --- scope (one default per module, covers the fixed bank) ---
    let _ = writeln!(
        out,
        "scope\tid=0,name=\"\",mod=0,size=0x{fixed_bank_size:04X}"
    );

    // --- spans ---
    for (i, (off, size)) in spans.iter().enumerate() {
        let _ = writeln!(out, "span\tid={i},seg=0,start={off},size={size},type=0");
    }

    // --- lines ---
    for (i, (_, span)) in src_entries.iter().enumerate() {
        let (line_num, _col) = byte_offset_to_line_col(source, span.start as usize);
        let _ = writeln!(out, "line\tid={i},file=0,line={line_num},span={i}");
    }

    // --- sym ---
    let mut sym_id: usize = 0;
    for (name, addr) in &code_syms {
        let safe_name = escape_string(name);
        let _ = writeln!(
            out,
            "sym\tid={sym_id},name=\"{safe_name}\",addrsize=absolute,size=1,scope=0,def=0,ref=0,val=0x{addr:04X},seg=0,type=lab"
        );
        sym_id += 1;
    }
    for v in &var_syms {
        let safe_name = escape_string(&v.name);
        // Zero page lives at $0000-$00FF and deserves the
        // `zeropage` addrsize so debuggers render accesses with
        // one-byte operands.
        let addrsize = if v.address < 0x0100 {
            "zeropage"
        } else {
            "absolute"
        };
        let _ = writeln!(
            out,
            "sym\tid={sym_id},name=\"{safe_name}\",addrsize={addrsize},size={size},scope=0,def=0,ref=0,val=0x{addr:04X},type=lab",
            addr = v.address,
            size = v.size,
        );
        sym_id += 1;
    }

    out
}

/// Escape a string for inclusion inside a `.dbg` quoted value. The
/// ca65 format uses C-style escapes, so a literal backslash or
/// double quote needs to be doubled with a backslash. Other ASCII
/// bytes pass through — the file is intentionally plain-ASCII so
/// third-party parsers don't have to handle UTF-8.
fn escape_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            _ => out.push(ch),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn make_linked(labels: &[(&str, u16)]) -> LinkedRom {
        let mut map = HashMap::new();
        for (name, addr) in labels {
            map.insert((*name).to_string(), *addr);
        }
        LinkedRom {
            rom: Vec::new(),
            labels: map,
            fixed_bank_file_offset: 16,
        }
    }

    #[test]
    fn mlb_skips_internal_labels_and_keeps_entry_points() {
        let linked = make_linked(&[
            ("__reset", 0xC010),
            ("__nmi", 0xC020),
            ("__ir_fn_Main_frame", 0xC100),
            ("__ir_fn_helper", 0xC200),
            ("__ir_skip_17", 0xC108), // internal, should not appear
            ("__ir_main_loop", 0xC080),
        ]);
        let vars = vec![
            VarAllocation {
                name: "score".into(),
                address: 0x0010,
                size: 1,
            },
            VarAllocation {
                name: "enemies".into(),
                address: 0x0300,
                size: 4,
            },
        ];
        let out = render_mlb(&linked, &vars);
        assert!(out.contains("Main_frame"), "should strip __ir_fn_ prefix");
        assert!(out.contains("helper"));
        assert!(out.contains("main_loop"));
        assert!(out.contains("reset"));
        assert!(out.contains("nmi"));
        assert!(
            !out.contains("__ir_skip_17"),
            "internal skip labels should not leak into the .mlb file"
        );
        // Var entries use the `R:` prefix and the raw RAM address.
        assert!(out.contains("R:0010:score"));
        assert!(out.contains("R:0300:enemies"));
    }

    #[test]
    fn mlb_uses_prg_relative_offsets() {
        // A label at CPU $C010 should land at PRG offset 0x0010
        // — the fixed bank's first byte sits at ROM file offset
        // 16 (post-header) and the .mlb format strips that
        // header back off.
        let linked = make_linked(&[("__ir_fn_foo", 0xC010)]);
        let out = render_mlb(&linked, &[]);
        assert!(
            out.contains("P:0010:foo"),
            "PRG-relative offset should be 0x0010, got:\n{out}"
        );
    }

    #[test]
    fn source_map_resolves_spans_to_line_and_column() {
        let source = "line one\nsecond line\nthird\n";
        // Byte offset 9 is the start of "second", which is line
        // 2 column 1.
        let span = Span::new(0, 9, 15);
        let linked = make_linked(&[("__src_0", 0xC000)]);
        let out = render_source_map(&linked, &[("__src_0".to_string(), span)], source);
        // PRG offset 0 (fixed_bank_file_offset=16, then subtract
        // 16 for PRG-relative) file_id 0 line 2 col 1.
        assert_eq!(out.trim(), "0000 0 2 1", "got:\n{out}");
    }

    #[test]
    fn source_map_output_is_sorted_by_offset() {
        let source = "a\nb\nc\n";
        let linked = make_linked(&[("__src_0", 0xC020), ("__src_1", 0xC010)]);
        let out = render_source_map(
            &linked,
            &[
                ("__src_0".to_string(), Span::new(0, 0, 1)),
                ("__src_1".to_string(), Span::new(0, 2, 3)),
            ],
            source,
        );
        let lines: Vec<_> = out.lines().collect();
        assert_eq!(lines.len(), 2);
        assert!(lines[0].starts_with("0010"));
        assert!(lines[1].starts_with("0020"));
    }

    #[test]
    fn dbg_emits_required_record_skeleton() {
        // Minimal case: one source-loc marker at $C010 (bank
        // offset 16) and two labels (__reset + one user function).
        // We expect one each of version / info / file / mod /
        // seg / scope, one span, one line, plus one sym per
        // filtered code label and one per variable.
        let source = "line one\nline two\n";
        let linked = make_linked(&[
            ("__reset", 0xC000),
            ("__ir_fn_Main_frame", 0xC010),
            ("__src_0", 0xC010),
        ]);
        let vars = vec![
            VarAllocation {
                name: "score".into(),
                address: 0x0010,
                size: 1,
            },
            VarAllocation {
                name: "buf".into(),
                address: 0x0300,
                size: 4,
            },
        ];
        let out = render_dbg(
            &linked,
            &[("__src_0".to_string(), Span::new(0, 9, 17))],
            &vars,
            source,
            Path::new("demo.ne"),
            Path::new("demo.nes"),
        );
        assert!(
            out.starts_with("version\tmajor=2,minor=0\n"),
            "header: {out}"
        );
        assert!(
            out.contains("info\tcsym=0,file=1,lib=0,line=1,mod=1,scope=1,seg=1,span=1,sym=4,type=0"),
            "info record should tally to 1 line, 1 span, 4 syms (__reset + Main_frame + 2 vars); got:\n{out}"
        );
        assert!(out.contains("file\tid=0,name=\"demo.ne\""));
        assert!(out.contains("mod\tid=0,name=\"demo\",file=0"));
        // `ooffs=16` is the NROM case: fixed bank starts right after
        // the 16-byte iNES header. Mesen applies its own header-size
        // subtraction when resolving labels, so a raw file offset
        // here produces PRG-relative label addresses out the other
        // side — see the `ooffs` assignment in `render_dbg`.
        assert!(out.contains(
            "seg\tid=0,name=\"CODE\",start=0xC000,size=0x4000,addrsize=absolute,type=ro,oname=\"demo.nes\",ooffs=16"
        ));
        assert!(out.contains("scope\tid=0,name=\"\",mod=0,size=0x4000"));
        // Single span: bank offset 16, stretches to end of bank
        // (0x4000 - 16 = 16368 bytes).
        assert!(
            out.contains("span\tid=0,seg=0,start=16,size=16368,type=0"),
            "span record missing or wrong size in:\n{out}"
        );
        // Line record: byte offset 9 in source = line 2.
        assert!(out.contains("line\tid=0,file=0,line=2,span=0"));
        // Code syms emitted as labels against seg 0.
        assert!(out.contains(
            "name=\"reset\",addrsize=absolute,size=1,scope=0,def=0,ref=0,val=0xC000,seg=0,type=lab"
        ));
        assert!(out.contains("name=\"Main_frame\""));
        // Variable syms: zero-page addrsize for $10, absolute for
        // $0300. No seg field on var syms.
        assert!(
            out.contains(
                "name=\"score\",addrsize=zeropage,size=1,scope=0,def=0,ref=0,val=0x0010,type=lab"
            ),
            "zero-page var should use addrsize=zeropage:\n{out}"
        );
        assert!(
            out.contains(
                "name=\"buf\",addrsize=absolute,size=4,scope=0,def=0,ref=0,val=0x0300,type=lab"
            ),
            "RAM var should use addrsize=absolute:\n{out}"
        );
    }

    #[test]
    fn dbg_span_sizes_stretch_between_adjacent_markers() {
        // Two source-loc markers at bank offsets 0x100 and 0x140:
        // the first span should be 0x40 bytes wide (distance to
        // the next marker), and the second should stretch to the
        // end of the fixed bank (0x4000 - 0x140 = 0x3EC0).
        let source = "a\nb\nc\n";
        let linked = make_linked(&[("__src_0", 0xC100), ("__src_1", 0xC140)]);
        let out = render_dbg(
            &linked,
            &[
                ("__src_0".to_string(), Span::new(0, 0, 1)),
                ("__src_1".to_string(), Span::new(0, 2, 3)),
            ],
            &[],
            source,
            Path::new("a.ne"),
            Path::new("a.nes"),
        );
        assert!(
            out.contains("span\tid=0,seg=0,start=256,size=64,type=0"),
            "first span should run to the next marker; got:\n{out}"
        );
        assert!(
            out.contains("span\tid=1,seg=0,start=320,size=16064,type=0"),
            "last span should stretch to end of fixed bank; got:\n{out}"
        );
    }

    #[test]
    fn dbg_skips_source_loc_without_resolved_address() {
        // A `__src_<N>` entry whose label didn't survive to the
        // final link (e.g. peephole folded it away) should be
        // dropped silently instead of polluting the output with a
        // span at offset 0.
        let source = "a\n";
        let linked = make_linked(&[("__src_0", 0xC010)]);
        let out = render_dbg(
            &linked,
            &[
                ("__src_0".to_string(), Span::new(0, 0, 1)),
                ("__src_missing".to_string(), Span::new(0, 0, 1)),
            ],
            &[],
            source,
            Path::new("a.ne"),
            Path::new("a.nes"),
        );
        assert!(
            out.contains("info\tcsym=0,file=1,lib=0,line=1,"),
            "only the resolved __src_ marker should count; got:\n{out}"
        );
    }

    #[test]
    fn dbg_ooffs_reflects_banked_rom_layout() {
        // On UxROM/MMC1 the fixed bank sits past the switchable
        // banks. The segment record's `ooffs` is the fixed bank's
        // file offset from the iNES header start (i.e., header +
        // switchable banks), so Mesen locates the fixed bank inside
        // the ROM file correctly and the header-size subtraction it
        // applies when resolving labels (see `render_dbg`) still
        // produces PRG-relative offsets.
        let mut labels = HashMap::new();
        labels.insert("__reset".to_string(), 0xC000);
        let linked = LinkedRom {
            rom: Vec::new(),
            labels,
            fixed_bank_file_offset: 16 + 16_384 * 3, // 3 switchable 16 KB banks
        };
        let out = render_dbg(
            &linked,
            &[],
            &[],
            "a\n",
            Path::new("a.ne"),
            Path::new("a.nes"),
        );
        let expected = 16 + 16_384 * 3; // iNES header + 3 switchable banks
        assert!(
            out.contains(&format!("ooffs={expected}")),
            "banked layout should move ooffs past the switchable banks; got:\n{out}"
        );
    }

    #[test]
    fn dbg_escapes_quotes_and_backslashes_in_paths() {
        // A path with a literal backslash or double quote must be
        // escaped in the `name=\"...\"` field; otherwise a
        // Windows-style path like `C:\games\demo.ne` would break
        // the record delimiter.
        let linked = make_linked(&[]);
        let out = render_dbg(
            &linked,
            &[],
            &[],
            "a\n",
            Path::new("demo\"tricky\\path.ne"),
            Path::new("demo.nes"),
        );
        assert!(
            out.contains("name=\"demo\\\"tricky\\\\path.ne\""),
            "quotes + backslashes should be escaped in file record; got:\n{out}"
        );
    }

    #[test]
    fn fceux_nl_emits_user_facing_labels_sorted_by_name() {
        let linked = make_linked(&[
            ("__reset", 0xC000),
            ("__nmi", 0xC100),
            ("__ir_fn_Main_frame", 0xC200),
            ("__ir_fn_helper", 0xC300),
            ("__ir_skip_42", 0xC180), // internal, must not appear
        ]);
        let out = render_fceux_nl(&linked);
        assert!(
            out.contains("$C000#reset#"),
            "reset entry point should be in .nl; got:\n{out}"
        );
        assert!(
            out.contains("$C100#nmi#"),
            "nmi entry point should be in .nl; got:\n{out}"
        );
        assert!(
            out.contains("$C200#Main_frame#"),
            "user frame handler should be in .nl; got:\n{out}"
        );
        assert!(
            out.contains("$C300#helper#"),
            "user function should be in .nl; got:\n{out}"
        );
        assert!(
            !out.contains("__ir_skip_42"),
            "internal skip labels should be filtered; got:\n{out}"
        );
        assert!(
            !out.contains("__ir_skip"),
            "no raw internal labels should leak; got:\n{out}"
        );
    }

    #[test]
    fn fceux_nl_empty_when_no_user_labels() {
        // Only internal labels — the .nl file should be empty
        // rather than containing every scaffold label.
        let linked = make_linked(&[("__ir_skip_0", 0xC010), ("__ir_skip_1", 0xC020)]);
        let out = render_fceux_nl(&linked);
        assert!(out.is_empty(), "no user labels → empty .nl; got:\n{out}");
    }

    #[test]
    fn fceux_ram_nl_sorted_by_address() {
        let vars = vec![
            VarAllocation {
                name: "enemies".into(),
                address: 0x0300,
                size: 4,
            },
            VarAllocation {
                name: "score".into(),
                address: 0x0010,
                size: 1,
            },
            VarAllocation {
                name: "pos_x".into(),
                address: 0x0020,
                size: 1,
            },
        ];
        let out = render_fceux_ram_nl(&vars);
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines.len(), 3);
        assert_eq!(lines[0], "$0010#score#");
        assert_eq!(lines[1], "$0020#pos_x#");
        assert_eq!(lines[2], "$0300#enemies#");
    }
}
