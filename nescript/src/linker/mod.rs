mod debug_symbols;
#[cfg(test)]
mod tests;

pub use debug_symbols::{
    render_dbg, render_fceux_nl, render_fceux_ram_nl, render_mlb, render_source_map,
};

use std::collections::HashMap;

use crate::asm;
use crate::asm::{AddressingMode as AM, Instruction, Opcode::*};
use crate::assets::{BackgroundData, MusicData, PaletteData, SfxData};
use crate::parser::ast::{HeaderFormat, Mapper, Mirroring};
use crate::rom::RomBuilder;
use crate::runtime;

/// Detailed result of a link pass. In addition to the final iNES
/// ROM bytes this carries the assembler's symbol table — each label
/// defined anywhere in the assembled fixed bank mapped to its CPU
/// address — and the byte offset at which the fixed bank starts
/// inside the PRG ROM region of the file.
///
/// The CLI uses this metadata to emit Mesen-compatible `.mlb`
/// symbol files and source-to-ROM maps (via the `--symbols` /
/// `--source-map` flags). Callers that only care about the ROM
/// bytes can read `.rom` and discard the rest.
#[derive(Debug, Clone)]
pub struct LinkedRom {
    /// Final iNES ROM bytes (header + PRG banks + CHR).
    pub rom: Vec<u8>,
    /// Every label defined in the fixed bank, mapped to its CPU
    /// address in the $C000-$FFFF window. Populated by the
    /// 6502 assembler's label pass.
    pub labels: HashMap<String, u16>,
    /// Byte offset of the fixed bank's first byte inside `rom`.
    /// For NROM this is `16` (just past the 16-byte iNES header).
    /// For banked mappers each switchable bank shifts it by 16 KB,
    /// so the fixed bank starts at `16 + 16_384 * switchable_bank_count`.
    pub fixed_bank_file_offset: usize,
}

/// Link compiled code into a complete NES ROM.
pub struct Linker {
    mirroring: Mirroring,
    mapper: Mapper,
    header_format: HeaderFormat,
    /// True when the program declared a `save { var ... }` block.
    /// Threaded through to [`RomBuilder::set_battery`] so the iNES
    /// header byte 6 bit 1 is set; emulators that respect it persist
    /// the `$6000-$7FFF` SRAM region across power cycles.
    has_battery: bool,
    /// Resolved room level data. Populated via [`Linker::with_rooms`]
    /// by the CLI / top-level compile. Each entry produces three
    /// data blocks in PRG ROM (`__room_tiles_N`, `__room_attrs_N`,
    /// `__room_col_N`) that `paint_room` and `collides_at` reference
    /// by symbol. Kept as an owned `Vec` so `Linker` can carry the
    /// data through the builder chain without threading yet another
    /// parameter through every entry point.
    rooms: Vec<crate::assets::RoomData>,
}

/// CHR data for a sprite, placed at a specific tile index in CHR ROM.
#[derive(Debug, Clone)]
pub struct SpriteData {
    pub name: String,
    pub tile_index: u8,
    /// Raw CHR bytes (16 bytes per 8x8 tile).
    pub chr_bytes: Vec<u8>,
}

/// A switchable PRG bank. Each switchable bank occupies a single
/// 16 KB slot in the ROM and can be mapped to $8000-$BFFF at runtime
/// by writing the bank's physical index to the mapper. The linker
/// places switchable banks in declaration order, followed by the
/// fixed bank at the end.
///
/// `instructions` is the assembly stream the IR codegen produced for
/// any user functions assigned to this bank — the linker assembles
/// it at base $8000, captures the resulting label addresses, and
/// merges them into the fixed bank's symbol table so cross-bank
/// trampolines can resolve their targets. An empty `instructions`
/// list is the legacy "reserve a slot" mode where the bank is just
/// padded with $FF.
///
/// `trampolines` lists each `(target_function, target_label)` pair
/// that needs a trampoline emitted in the fixed bank: callers JSR
/// the trampoline, the trampoline switches banks and JSRs the entry
/// label, then switches back. The IR codegen populates this list
/// from any function declared inside a `bank Foo { fun ... }` block
/// that's actually called from outside its bank.
#[derive(Debug, Clone)]
pub struct PrgBank {
    pub name: String,
    pub instructions: Vec<Instruction>,
    pub trampolines: Vec<BankTrampoline>,
}

/// A single cross-bank trampoline request. The linker emits one
/// `__tramp_<fn_name>` stub in the fixed bank for every entry in
/// this list — the stub pushes a fixed bank-select call, JSRs the
/// real function in the switchable bank, then restores the fixed
/// bank before returning.
#[derive(Debug, Clone)]
pub struct BankTrampoline {
    /// Label callers will `JSR` (e.g. `__tramp_big_helper`).
    pub tramp_label: String,
    /// Label inside the switchable bank holding the function body.
    /// Conventionally `__ir_fn_<fn_name>`.
    pub entry_label: String,
}

impl PrgBank {
    /// Create an empty named bank. Convenience for the compiler,
    /// which uses this when a `bank Foo: prg` declaration has no
    /// nested function bodies and exists only to reserve a 16 KB
    /// switchable slot the linker pads with $FF.
    #[must_use]
    pub fn empty(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            instructions: Vec::new(),
            trampolines: Vec::new(),
        }
    }

    /// Create a bank populated with the IR codegen's instruction
    /// stream for any functions assigned to it, plus the trampoline
    /// requests that should be emitted in the fixed bank.
    #[must_use]
    pub fn with_instructions(
        name: impl Into<String>,
        instructions: Vec<Instruction>,
        trampolines: Vec<BankTrampoline>,
    ) -> Self {
        Self {
            name: name.into(),
            instructions,
            trampolines,
        }
    }
}

/// True if `instructions` contains a label definition with the given
/// name. Labels are emitted as `NOP` pseudo-instructions whose mode
/// is `AddressingMode::Label(name)`.
fn has_label(instructions: &[Instruction], name: &str) -> bool {
    instructions
        .iter()
        .any(|i| matches!(&i.mode, AM::Label(n) if n == name))
}

/// A smiley face CHR tile for the default sprite (M1).
const DEFAULT_SPRITE_CHR: [u8; 16] = [
    // Plane 0 (low bits)
    0b0011_1100,
    0b0100_0010,
    0b1010_0101,
    0b1000_0001,
    0b1010_0101,
    0b1001_1001,
    0b0100_0010,
    0b0011_1100,
    // Plane 1 (high bits) — all zeros means color 1 only
    0b0011_1100,
    0b0111_1110,
    0b1111_1111,
    0b1111_1111,
    0b1111_1111,
    0b1111_1111,
    0b0111_1110,
    0b0011_1100,
];

/// Default palette data for M1 (writes to PPU $3F00). Spliced into
/// PRG under [`DEFAULT_PALETTE_LABEL`] when the program has no
/// user-declared palette, and loaded by
/// [`runtime::gen_initial_palette_load`] via the same indirect-loop
/// path that user palettes use — keeps the reset-time palette
/// loader small (one code path, ~20 bytes) instead of the old
/// 170-byte per-entry unrolled store sequence.
const DEFAULT_PALETTE: [u8; 32] = [
    // Background palettes
    0x0F, 0x00, 0x10, 0x20, // palette 0 (black, dark gray, light gray, white)
    0x0F, 0x06, 0x16, 0x26, // palette 1
    0x0F, 0x09, 0x19, 0x29, // palette 2
    0x0F, 0x01, 0x11, 0x21, // palette 3
    // Sprite palettes
    0x0F, 0x00, 0x10, 0x20, // sprite palette 0 (same as bg)
    0x0F, 0x14, 0x24, 0x34, // sprite palette 1
    0x0F, 0x1A, 0x2A, 0x3A, // sprite palette 2
    0x0F, 0x12, 0x22, 0x32, // sprite palette 3
];

/// Label under which [`DEFAULT_PALETTE`] is spliced into PRG when
/// emitted. Prefixed with `__` so it can never collide with a
/// user-declared palette's label, which the asset pipeline prefixes
/// with `__palette_`.
const DEFAULT_PALETTE_LABEL: &str = "__default_palette";

impl Linker {
    pub fn new(mirroring: Mirroring) -> Self {
        Self {
            mirroring,
            mapper: Mapper::NROM,
            header_format: HeaderFormat::Ines1,
            has_battery: false,
            rooms: Vec::new(),
        }
    }

    pub fn with_mapper(mirroring: Mirroring, mapper: Mapper) -> Self {
        Self {
            mirroring,
            mapper,
            header_format: HeaderFormat::Ines1,
            has_battery: false,
            rooms: Vec::new(),
        }
    }

    /// Supply the resolved `room` level data the CLI got back from
    /// [`crate::assets::resolve_rooms`]. The linker emits one set of
    /// tile / attribute / collision blobs per room and the codegen
    /// references them by symbol from `paint_room` / `collides_at`
    /// call sites.
    #[must_use]
    pub fn with_rooms(mut self, rooms: Vec<crate::assets::RoomData>) -> Self {
        self.rooms = rooms;
        self
    }

    /// Opt into the NES 2.0 header format for the emitted ROM.
    /// Chainable builder method — returns `self` so callers can
    /// write `Linker::with_mapper(m, p).with_header(HeaderFormat::Nes2)`.
    #[must_use]
    pub fn with_header(mut self, header: HeaderFormat) -> Self {
        self.header_format = header;
        self
    }

    /// Mark the ROM as battery-backed. Threaded through from
    /// `analysis.has_battery_saves`; flips iNES byte-6 bit-1.
    #[must_use]
    pub fn with_battery(mut self, has_battery: bool) -> Self {
        self.has_battery = has_battery;
        self
    }

    /// Link all code sections into a .nes ROM.
    ///
    /// This is a thin wrapper around [`Linker::link_with_assets`] that passes
    /// an empty sprite list, so the CHR ROM only contains the default smiley
    /// tile at index 0.
    pub fn link(&self, user_code: &[Instruction]) -> Vec<u8> {
        self.link_with_assets(user_code, &[])
    }

    /// Link all code sections into a .nes ROM, placing sprite CHR data at
    /// specific tile indices. No audio data is linked — use
    /// [`Linker::link_with_all_assets`] for audio.
    pub fn link_with_assets(&self, user_code: &[Instruction], sprites: &[SpriteData]) -> Vec<u8> {
        self.link_with_all_assets(user_code, sprites, &[], &[])
    }

    /// Link all code sections into a .nes ROM, placing both graphic
    /// assets (sprite CHR) and audio assets (sfx envelopes, music
    /// note streams) into the appropriate ROM regions.
    ///
    /// Audio data is spliced into PRG ROM under labels derived from
    /// each blob's name (see `SfxData::label` / `MusicData::label`).
    /// The linker only emits these blobs and the audio-driver body
    /// when user code contains the `__audio_used` marker label, so
    /// programs that never touch audio pay zero ROM cost.
    pub fn link_with_all_assets(
        &self,
        user_code: &[Instruction],
        sprites: &[SpriteData],
        sfx: &[SfxData],
        music: &[MusicData],
    ) -> Vec<u8> {
        self.link_banked(user_code, sprites, sfx, music, &[])
    }

    /// Link with the full asset pipeline plus zero or more
    /// switchable PRG banks. The switchable banks are written in
    /// declaration order and the fixed bank (which contains the
    /// runtime, NMI/IRQ handlers, vector table, bank-select
    /// subroutine, and all user code) is always placed last.
    ///
    /// For mappers that don't support banking (NROM) this is an
    /// error if any switchable banks are supplied. For banked
    /// mappers the linker also splices `gen_mapper_init` into the
    /// reset path and emits a `__bank_select` subroutine plus one
    /// `__tramp_<name>` trampoline for every bank that declares an
    /// `entry_label`.
    pub fn link_banked(
        &self,
        user_code: &[Instruction],
        sprites: &[SpriteData],
        sfx: &[SfxData],
        music: &[MusicData],
        switchable_banks: &[PrgBank],
    ) -> Vec<u8> {
        self.link_banked_with_ppu(user_code, sprites, sfx, music, &[], &[], switchable_banks)
    }

    /// Link with full asset pipeline including palette and
    /// background data blobs. Palettes and backgrounds each emit a
    /// labelled data block inside PRG ROM; the first declared
    /// palette / background is loaded at reset time before
    /// rendering is enabled, and any additional ones become
    /// addressable via `set_palette` / `load_background` (which
    /// queue a vblank-safe write).
    #[allow(clippy::too_many_arguments)]
    pub fn link_banked_with_ppu(
        &self,
        user_code: &[Instruction],
        sprites: &[SpriteData],
        sfx: &[SfxData],
        music: &[MusicData],
        palettes: &[PaletteData],
        backgrounds: &[BackgroundData],
        switchable_banks: &[PrgBank],
    ) -> Vec<u8> {
        self.link_banked_with_ppu_detailed(
            user_code,
            sprites,
            sfx,
            music,
            palettes,
            backgrounds,
            switchable_banks,
        )
        .rom
    }

    /// Like [`Linker::link_banked_with_ppu`] but returns the full
    /// [`LinkedRom`] record, carrying the assembler label table and
    /// the PRG offset of the fixed bank alongside the ROM bytes.
    /// This is the entry point used by the CLI when emitting a
    /// `.mlb` symbol file or a source-map file.
    #[allow(clippy::too_many_arguments)]
    pub fn link_banked_with_ppu_detailed(
        &self,
        user_code: &[Instruction],
        sprites: &[SpriteData],
        sfx: &[SfxData],
        music: &[MusicData],
        palettes: &[PaletteData],
        backgrounds: &[BackgroundData],
        switchable_banks: &[PrgBank],
    ) -> LinkedRom {
        assert!(
            switchable_banks.is_empty() || self.mapper != Mapper::NROM,
            "NROM does not support switchable PRG banks (got {} banks)",
            switchable_banks.len()
        );
        // CNROM has a fixed 32 KB PRG — user-declared switchable PRG
        // banks are meaningless. AxROM and GNROM switch 32 KB pages
        // as a unit, which the current 16 KB-per-bank trampoline
        // model doesn't support cleanly. Reject all three up front
        // so a silent layout mismatch doesn't produce a subtly
        // broken ROM.
        assert!(
            switchable_banks.is_empty()
                || !matches!(self.mapper, Mapper::CNROM | Mapper::AxROM | Mapper::GNROM),
            "{:?} does not yet support switchable PRG banks (got {} banks); \
             use MMC1/UxROM/MMC3 for per-function banking",
            self.mapper,
            switchable_banks.len()
        );
        self.link_banked_inner(
            user_code,
            sprites,
            sfx,
            music,
            palettes,
            backgrounds,
            switchable_banks,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn link_banked_inner(
        &self,
        user_code: &[Instruction],
        sprites: &[SpriteData],
        sfx: &[SfxData],
        music: &[MusicData],
        palettes: &[PaletteData],
        backgrounds: &[BackgroundData],
        switchable_banks: &[PrgBank],
    ) -> LinkedRom {
        // ROM layout.
        //
        // NROM: a single 16 KB PRG bank mapped at $C000-$FFFF.
        //
        // Banked (MMC1, UxROM, MMC3): `switchable_banks` switchable
        // 16 KB banks come first in physical order, followed by the
        // fixed bank. The fixed bank holds the runtime, NMI/IRQ
        // handlers, user code, bank-select routine, and all
        // trampolines — everything needed for control flow to work
        // at reset. The mapper is configured so the fixed bank
        // maps to $C000-$FFFF and one of the switchable banks maps
        // to $8000-$BFFF.
        let total_banks = switchable_banks.len() + 1;

        // Discovery pass: assemble each switchable bank that has
        // its own instruction stream so we know what labels live
        // inside it and at what $8000-window address. The bytes
        // produced here are discarded — any JSRs from the banked
        // code into fixed-bank labels (math runtime, audio tick,
        // other state handlers) will fail label resolution because
        // the fixed bank hasn't been assembled yet. We catch the
        // panic via a separate fixup-tolerant assembly variant
        // below; for the discovery pass we just need the label
        // addresses, so we seed the assembler with a placeholder
        // mapping (every label resolves to $C000) that's enough to
        // pass the second pass without panic.
        //
        // Banks with no instructions (the legacy "reserved slot"
        // mode used by every existing banked example) skip this
        // entirely and just contribute an empty payload below — the
        // code path is byte-for-byte equivalent to the pre-banked
        // codegen behaviour for those programs.
        let mut cross_bank_labels: HashMap<String, u16> = HashMap::new();
        for bank in switchable_banks {
            if bank.instructions.is_empty() {
                continue;
            }
            // Use placeholder seeding so unresolved references to
            // fixed-bank labels don't panic during the discovery
            // pass. The bytes are discarded; only the label table
            // matters here.
            let placeholder = HashMap::new();
            let discovery = asm::assemble_discover_labels(&bank.instructions, 0x8000, &placeholder);
            for (label, addr) in &discovery.labels {
                if cross_bank_labels.contains_key(label) {
                    panic!(
                        "duplicate label '{label}' across switchable banks; \
                         cannot resolve cross-bank reference"
                    );
                }
                cross_bank_labels.insert(label.clone(), *addr);
            }
        }

        let mut all_instructions = Vec::new();

        // Does this program need the OAM DMA plumbing? True when
        // either of two markers the IR codegen drops is present:
        //   - `__oam_used`: user code contains at least one `draw`.
        //   - `__sprite_cycle_used`: user code calls `cycle_sprites`
        //     (which rotates the DMA start offset each frame; it
        //     presupposes the DMA is running).
        // Gates the `$FE` OAM shadow fill inside `gen_init`, the
        // OAM DMA inside `gen_nmi`, and — cascaded via the
        // `has_visual_output` check below — the default palette /
        // smiley / rendering-enable machinery. Programs that don't
        // draw save ~520 cycles per NMI plus a handful of bytes.
        let has_oam =
            has_label(user_code, "__oam_used") || has_label(user_code, "__sprite_cycle_used");

        // RESET entry point
        all_instructions.push(Instruction::new(NOP, AM::Label("__reset".into())));

        // Hardware initialization
        all_instructions.extend(runtime::gen_init(has_oam));

        // Mapper configuration: for banked mappers, set up the PRG
        // layout so the fixed bank sits at $C000-$FFFF. NROM is a
        // no-op here.
        all_instructions.extend(runtime::gen_mapper_init(
            self.mapper,
            self.mirroring,
            total_banks,
        ));

        // Seed the PRNG state. Only emitted when the IR codegen
        // dropped the `__rand_used` marker — programs without PRNG
        // keep their reset path byte-identical.
        if has_label(user_code, "__rand_used") {
            all_instructions.extend(runtime::gen_prng_init());
        }

        // Whether the program produces any visual output. True if
        // the user declared a palette / sprite / background, or if
        // user code contains the `__oam_used` marker (i.e. draws).
        // A purely audio- or compute-only program is happy to leave
        // the PPU fully silent — no palette load, no rendering
        // enable, no default-sprite smiley in CHR — so we gate the
        // reset-time palette machinery on this flag. See the
        // sprite-chr / OAM-DMA gates for the other places it cascades.
        let has_visual_output =
            !palettes.is_empty() || !sprites.is_empty() || !backgrounds.is_empty() || has_oam;

        // Load the initial palette. If the program declared any
        // `palette` blocks, use the first one; otherwise fall back
        // to the built-in default palette so sprites show up in a
        // reasonable colour scheme without any user setup. Skipped
        // entirely for programs with no visual output — those leave
        // palette RAM in its power-on state (undefined on real
        // hardware, zeros under jsnes / Mesen) which is fine since
        // nothing gets rendered.
        //
        // IMPORTANT: `gen_init` leaves rendering fully disabled so
        // these $2006/$2007 writes are safe. We re-enable rendering
        // via `gen_enable_rendering` once all initial VRAM loads
        // complete — writing to $2007 with either the sprite or the
        // background layer active corrupts the PPU's internal
        // address register, which used to clobber everything past
        // about the first 72 bytes of a 1024-byte nametable load.
        if let Some(first_palette) = palettes.first() {
            all_instructions.extend(runtime::gen_initial_palette_load(&first_palette.label()));
        } else if has_visual_output {
            // No user palette but the program does render something
            // — fall back to a sensible built-in palette so the
            // sprites show up in a reasonable colour scheme without
            // any user setup. Uses the same indirect loop loader as
            // the user-palette path (reads a 32-byte blob through a
            // ZP pointer) — ~20 bytes of code plus a 32-byte data
            // block that gets spliced in below, versus the ~170
            // bytes the old inline-stores path cost. The data block
            // lives alongside the user palette blobs so the label
            // resolves in the normal assembly pass.
            all_instructions.extend(runtime::gen_initial_palette_load(DEFAULT_PALETTE_LABEL));
        }

        // Load the initial background if the program declared any.
        // Most programs don't, so the common case emits nothing
        // here and leaves nametable 0 zero-filled.
        let has_user_background = !backgrounds.is_empty();
        if let Some(first_bg) = backgrounds.first() {
            all_instructions.extend(runtime::gen_initial_background_load(
                &first_bg.tiles_label(),
                &first_bg.attrs_label(),
            ));
        }

        // Now that all palette and nametable writes are done, turn
        // rendering on. Programs with a declared background get
        // bg+sprites ($1E); programs without get sprites only ($10)
        // to preserve the pre-fix behaviour of example ROMs that
        // rely on a hidden nametable. Programs with no visual
        // output at all leave PPU_MASK at $00 from `gen_init` —
        // the PPU stays silent, saves 4 bytes and avoids exposing
        // an undefined palette on real hardware.
        if has_visual_output {
            all_instructions.extend(runtime::gen_enable_rendering(has_user_background));
        }

        // User code (var init + main loop)
        all_instructions.extend(user_code.iter().cloned());

        // Bank-select subroutine plus one trampoline per banked
        // function that the IR codegen reported as cross-bank-called.
        // Emitted only for banked mappers (NROM has no switchable
        // banks by definition). The helpers live in the fixed bank
        // so they're always reachable at $C000-$FFFF regardless of
        // which switchable bank is currently mapped at $8000.
        if self.mapper != Mapper::NROM {
            all_instructions.extend(runtime::gen_bank_select(self.mapper));
            for (i, bank) in switchable_banks.iter().enumerate() {
                if bank.trampolines.is_empty() {
                    continue;
                }
                #[allow(clippy::cast_possible_truncation)]
                let bank_num = i as u8;
                for tramp in &bank.trampolines {
                    all_instructions.extend(runtime::gen_bank_trampoline(
                        &tramp.tramp_label,
                        &tramp.entry_label,
                        bank_num,
                    ));
                }
            }
            if self.mapper == Mapper::UxROM {
                // UxROM needs a 256-byte bank-select bus-conflict
                // table in the fixed bank. The `__bank_select`
                // routine for UxROM writes to $FFF0 so the byte
                // at that address in ROM must match the bank being
                // selected — we splice in a 0..255 table just before
                // the vector area.
                all_instructions.extend(runtime::gen_uxrom_bank_table());
            }
        }

        // Math runtime routines. Gated on the `__mul_used` /
        // `__div_used` marker labels that the IR codegen drops at
        // the first `IrOp::Mul` / `IrOp::Div` / `IrOp::Mod`. The
        // optimizer rewrites multiplies and divides by constant
        // powers of two into shifts (and modulo by constant powers
        // of two into masks) before codegen runs, so these markers
        // only fire for genuinely runtime-costly math. Programs
        // without any surviving mul or div pay zero bytes here.
        let has_mul = has_label(user_code, "__mul_used");
        let has_div = has_label(user_code, "__div_used");
        if has_mul {
            all_instructions.extend(runtime::gen_multiply());
        }
        if has_div {
            all_instructions.extend(runtime::gen_divide());
        }

        // PRNG: splice the three entry points (`__rand8`, `__rand16`,
        // `__rand_seed`) whenever the codegen dropped the `__rand_used`
        // marker. Programs that never call `rand8()` / `rand16()` /
        // `seed_rand()` skip this entirely.
        let has_rand = has_label(user_code, "__rand_used");
        if has_rand {
            all_instructions.extend(runtime::gen_prng());
        }

        // Palette brightness: splice `__set_palette_brightness`
        // whenever `set_palette_brightness(level)` was called.
        // Fade builtins (`fade_out` / `fade_in`) also require the
        // brightness routine — the codegen's `emit_fade_marker`
        // forces `__palette_bright_used` whenever fade is used, so
        // this path picks up fade as a side effect.
        let has_palette_bright = has_label(user_code, "__palette_bright_used");
        if has_palette_bright {
            all_instructions.extend(runtime::gen_palette_brightness());
        }

        // Fade helpers (`__fade_out` / `__fade_in` plus the shared
        // `__wait_frame_rt` subroutine). Splices when user code
        // called `fade_out(n)` or `fade_in(n)`.
        let has_fade = has_label(user_code, "__fade_used");
        if has_fade {
            all_instructions.extend(runtime::gen_fade());
        }

        // VRAM update buffer drain. Splices the `__vram_buf_drain`
        // routine when any `nt_set` / `nt_attr` / `nt_fill_h`
        // intrinsic was lowered. The NMI handler JSRs it during
        // vblank.
        if has_label(user_code, "__vram_buf_used") {
            all_instructions.extend(runtime::gen_vram_buf_drain());
        }

        // `__collides_at` helper — spliced in when the codegen emits
        // the `__collides_at_used` marker. Programs that declare a
        // `room` but never call `collides_at(...)` skip the helper
        // entirely.
        if has_label(user_code, "__collides_at_used") {
            all_instructions.extend(runtime::gen_collides_at());
        }

        // Audio subsystem — linked in whenever user code touched
        // audio (detected via the `__audio_used` marker emitted by
        // the IR codegen). The driver body, period table, and
        // user/builtin data blobs are all spliced into PRG here.
        //
        // Order is important: the audio tick references both the
        // period table and the data blobs by label, so those labels
        // must be defined in the same assembly pass. The tick body
        // also has to exist before `__nmi` because NMI JSRs into
        // `__audio_tick` — so we emit it alongside the math
        // routines, well before the NMI handler below.
        let has_audio = has_label(user_code, "__audio_used");
        let has_noise = has_label(user_code, "__noise_used");
        let has_triangle = has_label(user_code, "__triangle_used");
        let has_sfx_pitch = has_label(user_code, "__sfx_pitch_used");
        if has_audio {
            all_instructions.extend(runtime::gen_audio_tick(
                has_noise,
                has_triangle,
                has_sfx_pitch,
            ));
            all_instructions.extend(runtime::gen_period_table());
            // Emit one data block per sfx blob: a label followed by
            // the envelope bytes. `play Name` codegen emits a
            // SymbolLo/SymbolHi pair that resolves to this label.
            for blob in sfx {
                all_instructions.extend(runtime::gen_data_block(
                    &blob.label(),
                    blob.envelope.clone(),
                ));
                // Optional pitch envelope blob. Only emitted for
                // sfx the compiler decided actually need per-frame
                // pitch updates — the pitch_envelope is empty for
                // single-pitch sfx and the `gen_data_block` call
                // is skipped, keeping ROM bytes identical to the
                // pre-pitch-envelope behaviour.
                if blob.has_pitch_envelope() {
                    all_instructions.extend(runtime::gen_data_block(
                        &blob.pitch_label(),
                        blob.pitch_envelope.clone(),
                    ));
                }
            }
            // Same for music: label + note stream.
            for blob in music {
                all_instructions
                    .extend(runtime::gen_data_block(&blob.label(), blob.stream.clone()));
            }
        }

        // Palette and background data blobs. Each palette is a
        // 32-byte block labelled `__palette_Name`; backgrounds are
        // split into two blocks (`__bg_tiles_Name`, `__bg_attrs_Name`)
        // so the reset loader and the NMI update helper can push
        // them with independent pointers. We always splice the
        // blobs whenever the program declares any palette or
        // background — there's no equivalent of `__audio_used`
        // because simply *declaring* a palette is enough to need
        // its bytes in ROM (the reset loader reads them).
        for pal in palettes {
            all_instructions.extend(runtime::gen_data_block(&pal.label(), pal.colors.to_vec()));
        }
        // When the program needs the built-in default palette (i.e.
        // it produces visual output but declared no palette of its
        // own), splice the 32-byte blob under `__default_palette`
        // so the reset-time loop loader above can resolve it.
        // Programs that declare a palette OR have no visual output
        // skip this entirely.
        if palettes.is_empty() && has_visual_output {
            all_instructions.extend(runtime::gen_data_block(
                DEFAULT_PALETTE_LABEL,
                DEFAULT_PALETTE.to_vec(),
            ));
        }
        for bg in backgrounds {
            all_instructions.extend(runtime::gen_data_block(
                &bg.tiles_label(),
                bg.tiles.to_vec(),
            ));
            all_instructions.extend(runtime::gen_data_block(
                &bg.attrs_label(),
                bg.attrs.to_vec(),
            ));
        }
        // Room data — one set of tile / attribute / collision blobs
        // per declared `room`. `paint_room Name` references the
        // first two through the same vblank update helper as
        // backgrounds, and `collides_at` indexes into the third.
        // Programs with no rooms emit nothing here.
        for room in &self.rooms {
            all_instructions.extend(runtime::gen_data_block(
                &room.tiles_label(),
                room.tiles.to_vec(),
            ));
            all_instructions.extend(runtime::gen_data_block(
                &room.attrs_label(),
                room.attrs.to_vec(),
            ));
            all_instructions.extend(runtime::gen_data_block(
                &room.collision_label(),
                room.collision.to_vec(),
            ));
        }

        // The NMI needs the palette/nametable update helper whenever
        // the program declared any palette or background, or the
        // IR codegen emitted the `__ppu_update_used` marker (which
        // signals that user code contains a `set_palette` or
        // `load_background` statement). Either condition brings in
        // the ~70-byte helper; programs that touch neither pay
        // zero bytes.
        let has_ppu_updates = !palettes.is_empty()
            || !backgrounds.is_empty()
            || !self.rooms.is_empty()
            || has_label(user_code, "__ppu_update_used");

        // NMI handler
        all_instructions.push(Instruction::new(NOP, AM::Label("__nmi".into())));
        // If user code emits an MMC3 reload hook, splice in a JSR
        // before the regular NMI runs. This reloads the scanline IRQ
        // counter each frame so the handler fires at the right line.
        // The presence of the `__ir_mmc3_reload` label is detected
        // during assembly via the labels map; we unconditionally
        // emit a conditional JSR whose target is resolved at link
        // time. The helper emits an RTS so it's safe to call even
        // when there's no work to do.
        if has_label(user_code, "__ir_mmc3_reload") {
            all_instructions.push(Instruction::new(JSR, AM::Label("__ir_mmc3_reload".into())));
        }
        // The audio tick JSR is emitted by `gen_nmi` itself, after
        // the register and scratch-slot saves, so it can freely
        // clobber A/X/Y and $02/$03 without corrupting user state.
        // The codegen emits a `__debug_mode` marker whenever
        // `--debug` is active; that tells the runtime to splice
        // in the extra frame-overrun check at the top of NMI.
        let debug_mode = has_label(user_code, "__debug_mode");
        // `__sprite_cycle_used` is dropped by the IR codegen
        // whenever a `cycle_sprites` statement is lowered. When
        // present, the NMI handler reads the rotating offset byte
        // at $07EF instead of writing a literal 0 to $2003 before
        // the OAM DMA, turning the classic "same sprites dropped
        // every frame" hardware symptom into visible flicker that
        // the eye reconstructs across frames.
        let has_sprite_cycle = has_label(user_code, "__sprite_cycle_used");
        let has_p1_input = has_label(user_code, "__p1_input_used");
        let has_p2_input = has_label(user_code, "__p2_input_used");
        // `__edge_input_used` is dropped whenever any `p1.a.pressed` /
        // `p1.a.released` site lowers. Tells the NMI to snapshot the
        // previous-frame input byte before the new strobe.
        let has_edge_input = has_label(user_code, "__edge_input_used");
        // `__vram_buf_used` is dropped by the IR codegen for any
        // `nt_set` / `nt_attr` / `nt_fill_h` call site. Brings in
        // both the `__vram_buf_drain` runtime routine and the
        // NMI-side JSR that calls it during vblank.
        let has_vram_buf = has_label(user_code, "__vram_buf_used");
        all_instructions.extend(runtime::gen_nmi(runtime::NmiOptions {
            has_ppu_updates,
            has_audio,
            debug_mode,
            has_sprite_cycle,
            has_oam,
            has_p2_input,
            has_p1_input,
            has_edge_input,
            has_vram_buf,
        }));

        // IRQ handler
        all_instructions.push(Instruction::new(NOP, AM::Label("__irq".into())));
        all_instructions.extend(runtime::gen_irq());

        // Assemble everything at $C000. The label-seed map is empty
        // for programs without any banked user code, which keeps the
        // result byte-identical to the pre-banked-codegen output for
        // every existing example. Programs with banked functions get
        // the per-bank label tables merged in here so cross-bank
        // trampolines can resolve their `__ir_fn_<name>` targets in
        // the second-pass fixup.
        let base_addr = 0xC000;
        let result = if cross_bank_labels.is_empty() {
            asm::assemble(&all_instructions, base_addr)
        } else {
            asm::assemble_with_labels(&all_instructions, base_addr, &cross_bank_labels)
        };

        // Build PRG ROM with vector table
        let mut prg = result.bytes;

        // Pad to fill the bank up to vector table location
        // Vector table is at $FFFA-$FFFF (relative offset: $3FFA in a 16 KB bank)
        let vector_offset = 0x3FFA;
        if prg.len() > vector_offset {
            panic!("PRG code exceeds 16 KB bank (code is {} bytes)", prg.len());
        }
        prg.resize(vector_offset, 0xFF);

        // Write vector table. IR codegen emits a richer IRQ handler
        // under `__irq_user` when the program has scanline handlers;
        // prefer that over the generic RTI stub at `__irq`.
        let nmi_addr = result.labels.get("__nmi").copied().unwrap_or(0xC000);
        let reset_addr = result.labels.get("__reset").copied().unwrap_or(0xC000);
        let irq_addr = result
            .labels
            .get("__irq_user")
            .or_else(|| result.labels.get("__irq"))
            .copied()
            .unwrap_or(0xC000);

        prg.extend_from_slice(&nmi_addr.to_le_bytes());
        prg.extend_from_slice(&reset_addr.to_le_bytes());
        prg.extend_from_slice(&irq_addr.to_le_bytes());

        // Build ROM
        let mut builder = RomBuilder::new(self.mirroring);
        builder.set_mapper(crate::rom::mapper_number(self.mapper));
        if self.header_format == HeaderFormat::Nes2 {
            builder.enable_nes2();
        }
        builder.set_battery(self.has_battery);

        // Multi-bank layout: each switchable bank is an independent
        // 16 KB slot whose contents are either the assembled
        // banked-instruction stream or empty padding (for "reserved
        // slot" mode), followed by the fixed bank (just assembled).
        // For NROM (no switchable banks) this collapses to the
        // legacy single-bank path.
        //
        // For banks that hold their own instruction streams we run
        // a second assembly pass here, this time seeding the
        // assembler with both the cross-bank labels (other banks'
        // discovery results) and the fixed bank's labels. This is
        // the pass that resolves any fixups from banked code into
        // the fixed bank — math runtime, audio tick, other state
        // handlers, etc.
        if switchable_banks.is_empty() {
            // AxROM (mapper 7) and GNROM (mapper 66) both map a
            // single 32 KB PRG page at $8000-$FFFF, so emulators
            // expect PRG size in multiples of 32 KB. For single-page
            // AxROM/GNROM we emit two 16 KB iNES banks: the first
            // is 0xFF fill (maps at $8000-$BFFF when bank 0 is
            // selected), and the second is our assembled fixed-bank
            // code (maps at $C000-$FFFF). Bank-select writes still
            // work — the mapper's register picks the 32 KB page —
            // but with a single PRG page the upper-half code is
            // always visible.
            if matches!(self.mapper, Mapper::AxROM | Mapper::GNROM) {
                let filler = vec![0xFF_u8; 16384];
                builder.set_prg_banks(vec![filler, prg]);
            } else {
                builder.set_prg(prg);
            }
        } else {
            // Build the merged label table the bank assembler
            // needs. Includes both the cross-bank labels gathered
            // during the discovery pass and every label the fixed
            // bank assembler just produced.
            let mut merged_labels = cross_bank_labels.clone();
            for (name, addr) in &result.labels {
                merged_labels.insert(name.clone(), *addr);
            }
            let mut banks: Vec<Vec<u8>> = Vec::with_capacity(total_banks);
            for bank in switchable_banks {
                let payload = if bank.instructions.is_empty() {
                    Vec::new()
                } else {
                    let final_pass =
                        asm::assemble_with_labels(&bank.instructions, 0x8000, &merged_labels);
                    final_pass.bytes
                };
                assert!(
                    payload.len() <= 16384,
                    "switchable bank '{}' exceeds 16 KB ({} bytes)",
                    bank.name,
                    payload.len()
                );
                banks.push(payload);
            }
            banks.push(prg);
            builder.set_prg_banks(banks);
        }

        // CHR ROM: tile 0 is reserved for the default smiley,
        // followed by any user-declared sprites placed at their
        // assigned tile indices, followed by any auto-generated
        // background CHR data at `chr_base_tile * 16`. Each
        // background's `chr_bytes` was sized by the resolver
        // against the sprite range so no two contiguous tile
        // ranges overlap, but we still bounds-check on copy in
        // case a future change shifts the layout.
        let mut chr = vec![0u8; 8192];
        // Tile 0 is reserved for the built-in smiley *only* when
        // something in the program depends on it. Three possible
        // sources of that dependency:
        //
        //   1. `__default_sprite_used` marker — user code runs at
        //      least one `draw` that falls back to tile 0, either
        //      because the sprite name doesn't resolve or because
        //      it uses a runtime `frame:` override.
        //   2. A background nametable references tile 0 directly.
        //      Some programs use the smiley as a placeholder
        //      background tile (see `examples/friendly_assets.ne`).
        //   3. A background's CHR was written at base tile 0 — the
        //      resolver shouldn't allow this today, but checking
        //      for `chr_base_tile == 0` keeps the gate honest.
        //
        // Programs whose draws all resolve to declared sprites with
        // static frames and whose backgrounds reference tiles 1+
        // skip the smiley emit and reclaim 16 CHR bytes.
        let bg_uses_tile_zero = backgrounds.iter().any(|bg| {
            // A nametable entry of 0 means "fetch tile 0" — the
            // PPU can't tell the difference between sprite and
            // background tiles, so we have to preserve the smiley
            // when any background map byte reads 0.
            bg.tiles.contains(&0)
        });
        let has_default_sprite = has_label(user_code, "__default_sprite_used") || bg_uses_tile_zero;
        if has_default_sprite {
            chr[..16].copy_from_slice(&DEFAULT_SPRITE_CHR);
        }
        for sprite in sprites {
            let offset = sprite.tile_index as usize * 16;
            let end = offset + sprite.chr_bytes.len();
            if end <= chr.len() {
                chr[offset..end].copy_from_slice(&sprite.chr_bytes);
            }
        }
        for bg in backgrounds {
            if bg.chr_bytes.is_empty() {
                continue;
            }
            let offset = bg.chr_base_tile as usize * 16;
            let end = offset + bg.chr_bytes.len();
            assert!(
                end <= chr.len(),
                "background '{}' auto-CHR ({} bytes at base tile {}) overflows the {}-byte CHR ROM; \
                 the resolver should have caught this — file a bug",
                bg.name,
                bg.chr_bytes.len(),
                bg.chr_base_tile,
                chr.len()
            );
            chr[offset..end].copy_from_slice(&bg.chr_bytes);
        }
        builder.set_chr(chr);

        let rom = builder.build();
        // The fixed bank sits after the iNES header (16 bytes) and
        // any switchable banks (16 KB each). Callers use this to
        // translate CPU addresses from `labels` into ROM file
        // offsets when emitting Mesen `.mlb` files.
        let fixed_bank_file_offset = 16 + switchable_banks.len() * 16_384;
        LinkedRom {
            rom,
            labels: result.labels,
            fixed_bank_file_offset,
        }
    }
}
