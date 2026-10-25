//! End-to-end compile pipeline.
//!
//! One shared function ([`compile_source`]) drives the full
//! `preprocess → parse → analyze → IR lower → optimize →
//! codegen → peephole → link` sequence on an in-memory source
//! string. The CLI ([`crate::main`]), the compile benchmark
//! (`benches/compile.rs`), and the integration-test helper
//! (`tests/integration_test.rs::compile_with_debug_artifacts`)
//! all route through this one function, so any future change to
//! the pipeline is picked up everywhere without hand-maintained
//! parallel copies.
//!
//! The CI `cargo test --all-targets` job used to panic for a
//! release where the bench's hand-maintained copy diverged from
//! the CLI after the banked-codegen landing — that class of bug
//! can't recur now that the bench calls [`compile_source`]
//! directly.
//!
//! This module deliberately takes **already-preprocessed source
//! text** and an **explicit source directory** rather than a
//! filesystem path, so it stays friendly to future WASM hosting:
//! the caller is the only layer that needs to touch `std::fs`.

use std::collections::HashMap;
use std::path::Path;

use crate::analyzer::{self, AnalysisResult};
use crate::asm::Instruction;
use crate::assets::{self, BackgroundData, MusicData, PaletteData, SfxData};
use crate::codegen::{peephole, IrCodeGen};
use crate::errors::Diagnostic;
use crate::ir::{self, IrProgram};
use crate::lexer::Span;
use crate::linker::{BankTrampoline, LinkedRom, Linker, PrgBank, SpriteData};
use crate::optimizer;
use crate::parser;
use crate::parser::ast::BankType;

/// Knobs that mirror the CLI `build` flags. New knobs should
/// default to the "release build" value so that old callers pick
/// up sensible behaviour on upgrade.
#[derive(Debug, Default, Clone, Copy)]
pub struct CompileOptions {
    /// Enable `--debug` mode: bounds checks, frame-overrun
    /// counter, `debug.log` / `debug.assert` emission.
    pub debug: bool,
    /// Skip the IR optimizer. Matches `--no-opt`.
    pub no_opt: bool,
    /// Emit `__src_<N>` label pseudo-ops for every lowered IR
    /// statement and record their spans on the codegen's
    /// [`IrCodeGen::source_locs`] side table. The CLI turns this
    /// on when `--source-map` is passed; the bench and release
    /// builds leave it off because the labels become peephole
    /// block boundaries and would shift ROM bytes.
    pub emit_source_map: bool,
}

/// Everything the CLI, the bench, and the integration tests need
/// from a full compile run. Carries the raw ROM plus enough
/// metadata to render a memory map, emit a `.mlb` symbol file, or
/// emit a source map — whatever the caller wants to do with it.
pub struct CompileOutput {
    /// Final assembled iNES ROM bytes (header + PRG + CHR).
    pub rom: Vec<u8>,
    /// Full linker result including the label table + fixed-bank
    /// PRG file offset. Used for `.mlb` / source-map rendering.
    pub link_result: LinkedRom,
    /// Analyzer result, kept around for post-link reporters that
    /// need the symbol table (`.mlb`) or the variable allocation
    /// map (`--memory-map`).
    pub analysis: AnalysisResult,
    /// The IR program post-(optional) optimization, kept so
    /// `--dump-ir` and the call-graph reporter have something to
    /// print without re-running the lowering.
    pub ir_program: IrProgram,
    /// Resolved sprite data (CHR + tile indices).
    pub sprites: Vec<SpriteData>,
    /// Resolved sfx envelopes.
    pub sfx: Vec<SfxData>,
    /// Resolved music note streams.
    pub music: Vec<MusicData>,
    /// Resolved palette blobs.
    pub palettes: Vec<PaletteData>,
    /// Resolved background blobs.
    pub backgrounds: Vec<BackgroundData>,
    /// Final post-peephole fixed-bank instruction stream. Used by
    /// `--asm-dump`.
    pub instructions: Vec<Instruction>,
    /// Source-location markers (`__src_<N>`, span) the codegen
    /// emitted when [`CompileOptions::emit_source_map`] is set.
    /// Empty when source maps are off.
    pub source_locs: Vec<(String, Span)>,
}

/// Why the pipeline couldn't finish. The CLI translates each
/// variant into a human-readable error; tests and benches can
/// `unwrap()` with a sensible panic message.
#[derive(Debug)]
pub enum CompileError {
    /// Parser produced one or more error-level diagnostics. The
    /// caller gets the full diagnostic vector so it can render
    /// whatever UI it wants.
    Parse(Vec<Diagnostic>),
    /// Parser returned `None` with no explicit errors (empty
    /// input or similarly pathological).
    ParseProducedNothing,
    /// Analyzer produced one or more error-level diagnostics.
    Analyze(Vec<Diagnostic>),
    /// One of the asset resolvers (sprites, sfx, music, palette,
    /// background) returned `Err`.
    AssetResolution(String),
}

/// Run the full compile pipeline on an already-preprocessed
/// source string.
///
/// `source_dir` is used to resolve `@chr("…")` / `@palette("…")`
/// / `@nametable("…")` / `@binary("…")` paths that the parser
/// stored verbatim. Pass `Path::new(".")` when the program
/// doesn't reference any external assets.
///
/// Returns either a full [`CompileOutput`] or a [`CompileError`]
/// describing the first phase that refused to continue. The
/// caller is responsible for rendering diagnostics — this
/// function never prints to stdout or stderr.
pub fn compile_source(
    source: &str,
    source_dir: &Path,
    opts: &CompileOptions,
) -> Result<CompileOutput, CompileError> {
    // Parse.
    let (program, parse_diags) = parser::parse(source);
    if parse_diags.iter().any(Diagnostic::is_error) {
        return Err(CompileError::Parse(parse_diags));
    }
    let program = program.ok_or(CompileError::ParseProducedNothing)?;

    // Analyze.
    let analysis = analyzer::analyze(&program);
    if analysis.diagnostics.iter().any(Diagnostic::is_error) {
        return Err(CompileError::Analyze(analysis.diagnostics));
    }

    // IR lowering plus (optionally) optimization.
    let mut ir_program = ir::lower(&program, &analysis);
    if !opts.no_opt {
        optimizer::optimize(&mut ir_program);
    }

    // Asset resolution. Each asset category reads its paths
    // relative to `source_dir`, so the caller picks which file
    // system view is "current".
    let sprites = assets::resolve_sprites(&program, source_dir)
        .map_err(|e| CompileError::AssetResolution(format!("sprites: {e}")))?;
    let sfx = assets::resolve_sfx(&program)
        .map_err(|e| CompileError::AssetResolution(format!("sfx: {e}")))?;
    let music = assets::resolve_music(&program)
        .map_err(|e| CompileError::AssetResolution(format!("music: {e}")))?;
    let palettes = assets::resolve_palettes(&program, source_dir)
        .map_err(|e| CompileError::AssetResolution(format!("palettes: {e}")))?;
    // Compute the first CHR tile index that backgrounds can claim.
    // Sprite tile 0 is the runtime default smiley; the resolver
    // packs user sprites in starting at tile 1, so the next free
    // tile is whatever sits past the last sprite. We derive it
    // from the resolved `SpriteData` rather than re-walking the
    // AST to keep the two sides honest.
    //
    // Hard-error if the sprite range already fills the 256-tile
    // pattern table. A silent cap would let a background tile
    // overwrite the last sprite tile — the kind of latent
    // miscompile we'd rather catch at link time than at runtime.
    // The check is lifted out of `resolve_backgrounds` so the
    // diagnostic mentions the sprite count, not just the
    // background that happened to trip the limit.
    let next_sprite_tile_u16 = sprites
        .iter()
        .map(|s| {
            let count = s.chr_bytes.len().div_ceil(16) as u16;
            u16::from(s.tile_index) + count
        })
        .max()
        .unwrap_or(1u16);
    let has_png_background = program.backgrounds.iter().any(|b| b.png_source.is_some());
    if has_png_background && next_sprite_tile_u16 >= 256 {
        return Err(CompileError::AssetResolution(format!(
            "sprite tile range ends at index {next_sprite_tile_u16} which leaves no room for \
             background tiles in the 256-tile pattern table; remove or shrink a sprite, or \
             use an inline background body instead of `@nametable(...)`"
        )));
    }
    #[allow(clippy::cast_possible_truncation)]
    let next_sprite_tile: u8 = next_sprite_tile_u16.min(255) as u8;
    let backgrounds = assets::resolve_backgrounds(&program, source_dir, next_sprite_tile)
        .map_err(|e| CompileError::AssetResolution(format!("backgrounds: {e}")))?;
    let rooms = assets::resolve_rooms(&program);

    // IR → 6502 codegen. We hold on to the codegen after
    // `generate()` because it carries the per-bank instruction
    // streams and the source-location markers.
    let mut codegen = IrCodeGen::new(&analysis.var_allocations, &ir_program)
        .with_sprites(&sprites)
        .with_audio(&sfx, &music)
        .with_debug(opts.debug)
        .with_source_map(opts.emit_source_map)
        .with_debug_port(program.game.debug_port);
    let mut instructions = codegen.generate(&ir_program);
    peephole::optimize(&mut instructions);

    // Pull the per-bank streams out, run peephole on each, and
    // reconstruct the trampoline requests. Programs with no
    // banked functions get empty maps here and the linker emits
    // byte-identical output to the pre-banked-codegen baseline.
    let mut banked_streams: HashMap<String, Vec<Instruction>> = codegen.banked_streams().clone();
    for stream in banked_streams.values_mut() {
        peephole::optimize(stream);
    }
    let mut bank_trampolines: HashMap<String, Vec<BankTrampoline>> = HashMap::new();
    for func in &ir_program.functions {
        if let Some(bank_name) = &func.bank {
            bank_trampolines
                .entry(bank_name.clone())
                .or_default()
                .push(BankTrampoline {
                    tramp_label: format!("__tramp_{}", func.name),
                    entry_label: format!("__ir_fn_{}", func.name),
                });
        }
    }

    let linker = Linker::with_mapper(program.game.mirroring, program.game.mapper)
        .with_header(program.game.header)
        .with_battery(analysis.has_battery_saves)
        .with_rooms(rooms);
    let switchable_banks: Vec<PrgBank> = program
        .banks
        .iter()
        .filter(|b| b.bank_type == BankType::Prg)
        .map(|b| {
            let stream = banked_streams.remove(&b.name).unwrap_or_default();
            let tramps = bank_trampolines.remove(&b.name).unwrap_or_default();
            if stream.is_empty() && tramps.is_empty() {
                PrgBank::empty(&b.name)
            } else {
                PrgBank::with_instructions(&b.name, stream, tramps)
            }
        })
        .collect();

    let link_result = linker.link_banked_with_ppu_detailed(
        &instructions,
        &sprites,
        &sfx,
        &music,
        &palettes,
        &backgrounds,
        &switchable_banks,
    );

    let source_locs = codegen.source_locs().to_vec();

    Ok(CompileOutput {
        rom: link_result.rom.clone(),
        link_result,
        analysis,
        ir_program,
        sprites,
        sfx,
        music,
        palettes,
        backgrounds,
        instructions,
        source_locs,
    })
}
