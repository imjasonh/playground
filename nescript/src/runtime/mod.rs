#[cfg(test)]
mod tests;

use crate::asm::{AddressingMode as AM, Instruction, Opcode::*};
use crate::parser::ast::{Mapper, Mirroring};

/// PPU register addresses
const PPU_CTRL: u16 = 0x2000;
const PPU_MASK: u16 = 0x2001;
const PPU_STATUS: u16 = 0x2002;
const OAM_ADDR: u16 = 0x2003;
const OAM_DMA: u16 = 0x4014;
const APU_STATUS: u16 = 0x4015;
const JOY1: u16 = 0x4016;
const APU_FRAME: u16 = 0x4017;

/// Zero-page locations used by the runtime.
pub const ZP_FRAME_FLAG: u8 = 0x00;
pub const ZP_INPUT_P1: u8 = 0x01;
pub const ZP_INPUT_P2: u8 = 0x08;
/// Runtime OAM cursor, incremented by 4 on every `draw` inside a
/// frame handler. The IR codegen resets this to 0 after the OAM
/// clear at the top of the handler, so each `draw` writes to the
/// next 4-byte sprite slot regardless of how many loop iterations
/// came before it. At 64 slots the u8 naturally wraps to 0 and
/// the oldest slot gets overwritten — the classic NES flicker
/// fallback.
pub const ZP_OAM_CURSOR: u8 = 0x09;
/// Pulse-1 SFX envelope pointer (2 bytes, lo/hi) — points at the
/// *current* frame's $4000 envelope byte inside the sfx blob. The
/// audio tick reads through this byte, writes to $4000, advances
/// the pointer, and keeps going until it reads a zero sentinel.
pub const ZP_SFX_PTR_LO: u8 = 0x0C;
pub const ZP_SFX_PTR_HI: u8 = 0x0D;
/// Pulse-2 music note-stream pointer (2 bytes, lo/hi) — points at
/// the *current* (pitch, duration) note pair inside the music blob.
pub const ZP_MUSIC_PTR_LO: u8 = 0x0E;
pub const ZP_MUSIC_PTR_HI: u8 = 0x0F;
/// Music base pointer (2 bytes) — start of the currently-loaded
/// track. Used by the loop-back branch when the driver hits the
/// end-of-track sentinel and the header loop flag is set.
pub const ZP_MUSIC_BASE_LO: u8 = 0x05;
pub const ZP_MUSIC_BASE_HI: u8 = 0x06;
/// Music state byte. Bit layout:
///   bit 0: 1 = track is looping, 0 = one-shot
///   bit 1: 1 = music is active (non-zero means "playing")
///   bits 2-5: latched pulse-2 envelope volume 0-15
///   bits 6-7: latched pulse-2 duty
/// Set on `start_music`, cleared (to 0) on `stop_music`. The driver
/// writes a fresh $4004 envelope byte every time it advances to a
/// new note using these bits so held notes don't decay.
pub const ZP_MUSIC_STATE: u8 = 0x07;
/// Pulse-1 SFX countdown — `0` means no sfx is playing.
/// Nonzero means the audio tick should read one envelope byte from
/// `ZP_SFX_PTR` each NMI and write it to $4000. When the tick reads
/// a zero sentinel it mutes pulse 1 and clears this byte.
pub const ZP_SFX_COUNTER: u8 = 0x0A;
/// Pulse-2 music duration countdown — frames remaining on the
/// currently-held music note. When it reaches zero, the tick
/// advances to the next (pitch, duration) pair.
pub const ZP_MUSIC_COUNTER: u8 = 0x0B;

// ── PPU update handshake ──
//
// When a program declares `palette` or `background` blocks the
// analyzer reserves `$11-$17` as runtime state for the vblank-safe
// update path. User code sets these from inside a frame handler
// (via `set_palette` / `load_background`), and the NMI handler
// applies any pending update while the PPU is blanked, then
// clears the flags.

/// Bitfield of pending PPU updates.
///   bit 0 = 1 → palette at `ZP_PENDING_PALETTE_*` is pending
///   bit 1 = 1 → background at `ZP_PENDING_BG_TILES_*` / `_ATTRS_*` is pending
pub const ZP_PPU_UPDATE_FLAGS: u8 = 0x11;
pub const ZP_PENDING_PALETTE_LO: u8 = 0x12;
pub const ZP_PENDING_PALETTE_HI: u8 = 0x13;
pub const ZP_PENDING_BG_TILES_LO: u8 = 0x14;
pub const ZP_PENDING_BG_TILES_HI: u8 = 0x15;
pub const ZP_PENDING_BG_ATTRS_LO: u8 = 0x16;
pub const ZP_PENDING_BG_ATTRS_HI: u8 = 0x17;
/// Pointer to the currently-painted room's collision bitmap. Set by
/// `paint_room Name` (via the codegen); read by the `__collides_at`
/// runtime helper to resolve each collision query against the
/// active room. Only reserved when the program declares a `room`;
/// otherwise the analyzer's user-ZP bump pointer starts at `$18` as
/// before.
pub const ZP_ROOM_COL_LO: u8 = 0x18;
pub const ZP_ROOM_COL_HI: u8 = 0x19;

// ── Debug instrumentation ──
//
// These slots are only touched by debug-mode ROMs. In release
// builds the analyzer is free to allocate over them.

/// Debug-mode frame-overrun counter. Incremented by the NMI
/// handler whenever it fires while the previous frame's ready
/// flag is still set — which means the main loop didn't consume
/// it, so user code spent more than one vblank-to-vblank window
/// processing the last frame. Read it with `peek(0x07FF)` or
/// `debug.frame_overrun_count()` in user code to see how many
/// overruns have happened since reset, or watch the address in
/// a Mesen memory viewer. Placed at the top of main RAM to
/// minimise the chance of a collision with analyzer-allocated
/// variables (which grow from $0300 upward).
pub const DEBUG_FRAME_OVERRUN_ADDR: u16 = 0x07FF;

/// Debug-mode "did the previous frame overrun" sticky bit. Set
/// to 1 by the NMI handler at the same time as it bumps
/// [`DEBUG_FRAME_OVERRUN_ADDR`], and cleared to 0 by either an
/// explicit `wait_frame` IR op *or* the implicit main-loop
/// flag-clear that runs between every dispatch — so a program
/// whose `on frame { ... }` body has no explicit `wait_frame`
/// still sees a fresh value next NMI. Exposed to user code as
/// `debug.frame_overran()` — a per-frame "did this frame finish
/// in time" predicate suited for `debug.assert(not debug.frame_overran())`
/// guards. Lives one byte below the cumulative counter so the
/// two can be inspected together in a Mesen memory viewer.
pub const DEBUG_FRAME_OVERRUN_FLAG_ADDR: u16 = 0x07FE;

/// Debug-mode cumulative sprite-per-scanline overflow counter.
/// Incremented by the NMI handler once per frame in which the
/// PPU's sprite overflow flag ($2002 bit 5) was set, i.e. any
/// scanline of the just-finished frame had more than 8 sprites
/// on it and the PPU silently dropped the excess. Read with
/// `peek(0x07FD)` or `debug.sprite_overflow_count()`.
///
/// The PPU hardware flag has two well-known quirks — it can
/// occasionally miss the 9th sprite or flag when none actually
/// overflowed — but it's right for the overwhelming majority of
/// cases and is essentially free to sample (one `LDA $2002; AND
/// #$20` at the top of NMI). Pairs with the compile-time W0109
/// warning: W0109 catches layouts knowable at compile time (text,
/// HUD, title screens) and this counter catches the dynamic
/// cases (enemy formations, projectile clusters) during
/// playtesting in debug builds. Release-mode ROMs never touch
/// this slot, so the analyzer is free to allocate over it.
pub const DEBUG_SPRITE_OVERFLOW_COUNT_ADDR: u16 = 0x07FD;

/// Debug-mode "did the previous frame hit the 8-sprites-per-
/// scanline limit" sticky bit. Set by the NMI handler together
/// with [`DEBUG_SPRITE_OVERFLOW_COUNT_ADDR`], and cleared to 0
/// by every `wait_frame` IR op (or the implicit main-loop
/// clear) so user code sees a fresh value every frame.
/// Exposed to user code as `debug.sprite_overflow()`, a
/// per-frame boolean suited for
/// `debug.assert(not debug.sprite_overflow())` guards during
/// playtesting.
pub const DEBUG_SPRITE_OVERFLOW_FLAG_ADDR: u16 = 0x07FC;

/// Runtime sprite-cycling offset. When any program statement
/// emits a `cycle_sprites` call the codegen drops the
/// `__sprite_cycle_used` marker, and the linker builds the
/// cycling variant of the NMI handler: instead of writing 0
/// to `OAM_ADDR` before the OAM DMA, it writes the current value
/// of this byte, which rotates the destination slot of the DMA
/// copy around the 64-slot OAM buffer. `cycle_sprites` adds 4
/// to this byte each call (naturally wrapping at 256 back to 0),
/// moving the copy start by one OAM slot per tick.
///
/// The result is the classic NES "sprite flicker" pattern: a
/// scene with >8 sprites on a scanline drops a different one
/// each frame rather than the same one every frame, so users
/// perceive flicker instead of permanent dropout — vastly
/// better UX because the eye reconstructs the missing pixels
/// from adjacent frames.
///
/// Programs that never use `cycle_sprites` leave this byte at
/// 0 forever and the NMI handler emits the original `LDA #0;
/// STA $2003` sequence, preserving byte-for-byte compatibility
/// with every existing golden ROM.
pub const SPRITE_CYCLE_ADDR: u16 = 0x07EF;

// ── Extra channel state ──
//
// The pulse-1 sfx and pulse-2 music channels live in zero page
// ($00-$0F) where every byte is precious. Adding new channel
// state there would either push user variables back by 6 bytes
// (breaking every existing example's ZP layout) or collide with
// runtime scratch slots. Instead, we park triangle and noise
// state at the very top of main RAM, just below the debug frame
// overrun counter, where analyzer-allocated globals rarely reach
// (they grow from $0300 upward). The few extra cycles per
// absolute access are negligible for a once-per-NMI tick.
//
// The state is only *referenced* by the audio tick when the
// corresponding `has_noise` / `has_triangle` flag is set — so
// programs that don't declare any noise/triangle sfx touch
// these addresses zero times, and the ROM bytes generated for
// an existing audio example are byte-identical to what today's
// compiler produces.
pub const AUDIO_NOISE_PTR_LO: u16 = 0x07F0;
pub const AUDIO_NOISE_PTR_HI: u16 = 0x07F1;
pub const AUDIO_NOISE_COUNTER: u16 = 0x07F2;
pub const AUDIO_TRIANGLE_PTR_LO: u16 = 0x07F3;
pub const AUDIO_TRIANGLE_PTR_HI: u16 = 0x07F4;
pub const AUDIO_TRIANGLE_COUNTER: u16 = 0x07F5;
/// Pulse-1 sfx per-frame pitch envelope pointer. Only populated
/// (and only read by the audio tick) in programs that declare at
/// least one sfx with a varying-pitch `pitch:` array; programs
/// that stick to scalar `pitch:` keep their byte-for-byte
/// pre-pitch-envelope ROM output. The tick treats a zero
/// high-byte as "no pitch update for the currently-playing sfx",
/// which lets a single program mix sfx with and without pitch
/// envelopes.
pub const AUDIO_SFX_PITCH_PTR_LO: u16 = 0x07F6;
pub const AUDIO_SFX_PITCH_PTR_HI: u16 = 0x07F7;

/// Previous-frame copies of the two controller bytes. Populated
/// by the NMI handler *after* the current-frame shift loop, so
/// `curr & ~prev` ("just pressed") and `prev & ~curr`
/// ("just released") compile to a single AND chain at the read
/// site. Only touched by programs that reference `p1.button.pressed`
/// / `.released` (detected via the `__edge_input_used` marker
/// label); programs without edge-triggered reads leave these
/// two bytes free.
pub const PREV_INPUT_P1: u16 = 0x07E6;
pub const PREV_INPUT_P2: u16 = 0x07E7;

/// VRAM update buffer.
///
/// User intrinsics (`nt_set`, `nt_attr`, `nt_fill_h`) append entries
/// to a 256-byte ring at `$0400-$04FF` during `on frame`; the NMI
/// handler drains the buffer to PPU `$2007` while it's safe to
/// write VRAM (vblank). Every entry has the form
/// `[len][addr_hi][addr_lo][byte_0]...[byte_(len-1)]`. A `len`
/// byte of zero is the end-of-buffer sentinel: the drain loop
/// stops there and resets the head pointer to zero.
///
/// The buffer is gated on the `__vram_buf_used` marker label —
/// programs that never call any of the buffer intrinsics keep
/// these 256 bytes free for analyzer allocation. When the marker
/// is present, the analyzer skips `$0400-$04FF` so user globals
/// are pushed into `$0500+`.
///
/// `VRAM_BUF_HEAD` is a single byte tracking the next-free offset
/// from `VRAM_BUF_BASE`. It lives in main RAM next to the buffer
/// itself rather than in zero page so it doesn't compete with the
/// runtime's other ZP slots; the codegen reads/writes it via
/// absolute addressing.
pub const VRAM_BUF_BASE: u16 = 0x0400;
pub const VRAM_BUF_END: u16 = 0x04FF;
pub const VRAM_BUF_HEAD: u16 = 0x07E5;

/// Fade-helper scratch bytes. `FADE_STEP_FRAMES` holds the
/// per-step frame count saved at the top of `__fade_out` /
/// `__fade_in`; `FADE_LEVEL` tracks the current brightness level
/// as the fade walks 4 → 0 or 0 → 4. Programs that never call the
/// builtins (detected via the absence of `__fade_used`) leave
/// these bytes free for analyzer allocation.
pub const FADE_STEP_FRAMES: u16 = 0x07E8;
pub const FADE_LEVEL: u16 = 0x07E9;

/// PRNG state — two bytes holding a 16-bit xorshift state.
/// Only touched by the `__rand8` / `__rand16` / `__rand_seed`
/// runtime routines, which the linker splices in whenever user
/// code contains the `__rand_used` marker label. The reset path
/// seeds the state to a non-zero constant (0xACE1) so the very
/// first `rand8()` call returns a useful value even without an
/// explicit `seed_rand`. Programs that never touch PRNG skip
/// both the state init and the routines, leaving these two
/// bytes free for the analyzer to allocate over.
pub const PRNG_STATE_LO: u16 = 0x07EA;
pub const PRNG_STATE_HI: u16 = 0x07EB;

/// Generate the NES hardware initialization sequence.
/// This runs at RESET and sets up the hardware before user code.
///
/// `has_oam` controls the $0200 OAM shadow fill inside the RAM
/// clear loop. When true, the shadow is filled with `$FE` so any
/// sprite slot not explicitly written by a later `draw` stays
/// off-screen (Y = $FE is out of the 240-line viewport). When
/// false — i.e. the program never draws — the shadow stays at $00
/// alongside the rest of RAM, saving ~4 bytes of init code since
/// the inner-loop doesn't need the two extra LDA / mid-loop value
/// swaps to load and restore the `$FE` immediate.
#[must_use]
pub fn gen_init(has_oam: bool) -> Vec<Instruction> {
    let mut out = Vec::new();

    // Disable IRQs and set decimal mode off
    out.push(Instruction::implied(SEI));
    out.push(Instruction::implied(CLD));

    // Disable APU frame counter IRQ
    out.push(Instruction::new(LDX, AM::Immediate(0x40)));
    out.push(Instruction::new(STX, AM::Absolute(APU_FRAME)));

    // Set up stack at $01FF
    out.push(Instruction::new(LDX, AM::Immediate(0xFF)));
    out.push(Instruction::implied(TXS));

    // Disable PPU rendering
    out.push(Instruction::new(LDA, AM::Immediate(0x00)));
    out.push(Instruction::new(STA, AM::Absolute(PPU_CTRL)));
    out.push(Instruction::new(STA, AM::Absolute(PPU_MASK)));

    // Disable DMC IRQs momentarily (will re-enable the square
    // channels below so `play`/`start_music` can make sound).
    out.push(Instruction::new(STA, AM::Absolute(APU_STATUS)));

    // Enable pulse 1 and pulse 2 channels for the minimal audio
    // driver. SFX runs on pulse 1, music on pulse 2. We leave
    // triangle / noise / DMC disabled — the engine is deliberately
    // simple and those channels would go unused anyway.
    out.push(Instruction::new(LDA, AM::Immediate(0x03)));
    out.push(Instruction::new(STA, AM::Absolute(APU_STATUS)));
    // Pre-silence both channels: `$30` on the volume register sets
    // constant-volume envelope with volume 0 and halts the length
    // counter, which is the canonical "silent but armed" state.
    out.push(Instruction::new(LDA, AM::Immediate(0x30)));
    out.push(Instruction::new(STA, AM::Absolute(0x4000)));
    out.push(Instruction::new(STA, AM::Absolute(0x4004)));
    // Clear sweep units so the channel tone doesn't auto-slide.
    out.push(Instruction::new(LDA, AM::Immediate(0x08)));
    out.push(Instruction::new(STA, AM::Absolute(0x4001)));
    out.push(Instruction::new(STA, AM::Absolute(0x4005)));
    // Restore the zero we need for the subsequent RAM clear below.
    out.push(Instruction::new(LDA, AM::Immediate(0x00)));

    // Wait for first vblank
    // vblankwait1:
    out.push(Instruction::new(NOP, AM::Label("__vblankwait1".into())));
    out.push(Instruction::new(BIT, AM::Absolute(PPU_STATUS)));
    out.push(Instruction::new(
        BPL,
        AM::LabelRelative("__vblankwait1".into()),
    ));

    // Clear RAM ($0000-$07FF). When the program uses sprites, the
    // $0200-$02FF OAM shadow gets filled with $FE so unused slots
    // stay off-screen (Y=$FE puts the sprite below scanline 240);
    // programs that never draw skip that swap and zero-fill the
    // whole 2 KB range uniformly.
    out.push(Instruction::new(LDA, AM::Immediate(0x00)));
    out.push(Instruction::new(LDX, AM::Immediate(0x00)));
    out.push(Instruction::new(NOP, AM::Label("__clrmem".into())));
    out.push(Instruction::new(STA, AM::AbsoluteX(0x0000)));
    out.push(Instruction::new(STA, AM::AbsoluteX(0x0100)));
    if has_oam {
        // OAM shadow: fill with $FE (hide sprites off-screen).
        out.push(Instruction::new(LDA, AM::Immediate(0xFE)));
        out.push(Instruction::new(STA, AM::AbsoluteX(0x0200)));
        out.push(Instruction::new(LDA, AM::Immediate(0x00)));
    } else {
        out.push(Instruction::new(STA, AM::AbsoluteX(0x0200)));
    }
    out.push(Instruction::new(STA, AM::AbsoluteX(0x0300)));
    out.push(Instruction::new(STA, AM::AbsoluteX(0x0400)));
    out.push(Instruction::new(STA, AM::AbsoluteX(0x0500)));
    out.push(Instruction::new(STA, AM::AbsoluteX(0x0600)));
    out.push(Instruction::new(STA, AM::AbsoluteX(0x0700)));
    out.push(Instruction::implied(INX));
    out.push(Instruction::new(BNE, AM::LabelRelative("__clrmem".into())));

    // Wait for second vblank
    out.push(Instruction::new(NOP, AM::Label("__vblankwait2".into())));
    out.push(Instruction::new(BIT, AM::Absolute(PPU_STATUS)));
    out.push(Instruction::new(
        BPL,
        AM::LabelRelative("__vblankwait2".into()),
    ));

    // Enable NMI so the frame handshake fires every vblank. We
    // deliberately leave PPU_MASK at 0 (rendering fully disabled)
    // here — the linker splices in palette and background loads
    // after this init, and $2007 writes during active rendering
    // corrupt their target addresses via the PPU's v-register
    // auto-increment glitch. Rendering is enabled by the linker
    // *after* all initial VRAM loads complete, via `gen_enable_rendering`.
    out.push(Instruction::new(LDA, AM::Immediate(0x80))); // enable NMI
    out.push(Instruction::new(STA, AM::Absolute(PPU_CTRL)));

    out
}

/// Emit the `PPU_MASK` write that turns on rendering. Called by
/// the linker at the very end of the reset path, after all
/// initial palette / background loads are done, so the initial
/// VRAM writes are never corrupted by a mid-frame `$2007` glitch.
///
/// `show_background` controls whether the background layer is
/// enabled alongside the sprite layer — programs that declare a
/// `background` block want both, programs that don't can skip
/// the background bit to match the pre-fix behaviour.
#[must_use]
pub fn gen_enable_rendering(show_background: bool) -> Vec<Instruction> {
    // $1E = show bg + sprites + left-8-px for both
    // $10 = show sprites only (no bg)
    let mask = if show_background { 0x1E } else { 0x10 };
    vec![
        Instruction::new(LDA, AM::Immediate(mask)),
        Instruction::new(STA, AM::Absolute(PPU_MASK)),
    ]
}

/// Generate the NMI handler.
/// Called every vblank by the NES hardware.
///
/// `has_ppu_updates` controls whether the handler runs the
/// palette / nametable update helper. When false, the handler skips
/// that block entirely so programs that never call `set_palette` /
/// `load_background` pay zero cycles or bytes for the feature.
///
/// `has_audio` controls whether the handler calls the audio tick.
/// When true, the JSR to `__audio_tick` is emitted *after* the
/// register and scratch-slot saves, so the tick is free to trash
/// A/X/Y and the mul/state ZP scratch ($02/$03) without corrupting
/// the user's main-loop state. Placing the JSR outside the
/// save/restore window used to silently clobber `ZP_CURRENT_STATE`
/// whenever a music note was played (the tick's period-table
/// lookup stashes the table's high byte into $03).
///
/// `debug_mode` enables frame-overrun detection: before touching
/// the frame-ready flag, the handler checks whether it's already
/// set — if it is, the previous frame's main-loop work never
/// finished (i.e. the program ran over its vblank budget) and
/// the handler bumps the counter at
/// [`DEBUG_FRAME_OVERRUN_ADDR`]. Release-mode ROMs never call
/// this with `debug_mode=true`, so the counter slot stays free
/// for user allocation.
///
/// `has_sprite_cycle` selects between two OAM DMA setup paths:
/// when false the NMI writes a literal 0 to `$2003` before
/// triggering the DMA (classic behaviour, byte-identical to
/// every pre-cycling ROM), and when true it reads the rotating
/// offset byte from [`SPRITE_CYCLE_ADDR`] so each frame's DMA
/// lands in a different slot of the PPU's OAM buffer. The
/// per-frame increment is emitted at the `cycle_sprites` call
/// site, not here, so programs can choose to cycle every frame
/// (one call in `on frame`) or every Nth frame.
/// Compile-time switches that pick which NMI-handler variant
/// the runtime emits. Each bool either inlines or skips a
/// self-contained block inside [`gen_nmi`]; programs that don't
/// opt into a feature pay zero ROM/cycle cost for it. Grouped
/// into a struct rather than passed as individual parameters
/// to avoid tripping the clippy `fn_params_excessive_bools`
/// lint and to give future additions (another marker-label-
/// triggered NMI block) an obvious extension point.
#[allow(clippy::struct_excessive_bools)]
#[derive(Debug, Clone, Copy, Default)]
pub struct NmiOptions {
    pub has_ppu_updates: bool,
    pub has_audio: bool,
    pub debug_mode: bool,
    pub has_sprite_cycle: bool,
    /// When false, skip the OAM DMA (`$2003` address write + `$4014`
    /// DMA trigger). A program that never `draw`s sprites has
    /// nothing interesting to transfer — every one of the 256 OAM
    /// bytes is either the $FE hide sentinel or a zeroed row —
    /// so the DMA is ~520 wasted cycles per NMI. Skipping it saves
    /// those cycles plus 9 bytes of NMI code.
    pub has_oam: bool,
    /// When false, drop the three instructions that shift `$4017`
    /// (JOY2) into `ZP_INPUT_P2` from the NMI's 8-iteration input
    /// loop. Single-player programs save ~6 bytes of code and ~88
    /// cycles per frame (LDA abs + LSR A + ROL zp = 11 cycles × 8
    /// iterations).
    pub has_p2_input: bool,
    /// When false, drop the three instructions that shift `$4016`
    /// (JOY1) into `ZP_INPUT_P1`. If both `has_p1_input` and
    /// `has_p2_input` are false the whole strobe-and-loop block
    /// disappears — programs that never touch `button.*` pay
    /// zero cycles for input sampling (~100 cycles: the 88-cycle
    /// body plus the ~12-cycle strobe and loop scaffold).
    pub has_p1_input: bool,
    /// When true, snapshot the previous-frame controller byte
    /// into `PREV_INPUT_P1` / `PREV_INPUT_P2` *before* the
    /// new-frame strobe-and-shift loop. This is the extra state
    /// the IR codegen's `ReadInputEdge` op reads to compute
    /// `p1.a.pressed` / `.released`. Programs that don't
    /// reference edge-triggered input leave this off and the
    /// two snapshot stores disappear.
    pub has_edge_input: bool,
    /// When true, JSR `__vram_buf_drain` from the NMI after the
    /// existing palette/background handshake. Programs that don't
    /// call any of the buffer intrinsics leave this off and the
    /// NMI body is byte-identical to the pre-buffer version.
    pub has_vram_buf: bool,
}

#[must_use]
pub fn gen_nmi(opts: NmiOptions) -> Vec<Instruction> {
    let NmiOptions {
        has_ppu_updates,
        has_audio,
        debug_mode,
        has_sprite_cycle,
        has_oam,
        has_p2_input,
        has_p1_input,
        has_edge_input,
        has_vram_buf,
    } = opts;
    let mut out = Vec::new();

    // Save registers
    out.push(Instruction::implied(PHA));
    out.push(Instruction::implied(TXA));
    out.push(Instruction::implied(PHA));
    out.push(Instruction::implied(TYA));
    out.push(Instruction::implied(PHA));

    // Save the multiply/divide scratch slots ($02/$03). $03 doubles
    // as `ZP_CURRENT_STATE` for the state dispatch, and user code
    // mid-multiply/divide has both slots live; preserving them here
    // keeps the invariant that NMI never clobbers user-visible ZP
    // state.
    out.push(Instruction::new(LDA, AM::ZeroPage(0x02)));
    out.push(Instruction::implied(PHA));
    out.push(Instruction::new(LDA, AM::ZeroPage(0x03)));
    out.push(Instruction::implied(PHA));

    // Debug-mode sprite overflow sampling. The PPU sets bit 5 of
    // $2002 when its sprite evaluation hits more than 8 in-range
    // sprites on any scanline of the frame it just finished
    // rendering. NMI fires at the start of vblank, right after
    // that rendering ends, so this is the exact moment the flag
    // is valid for "did the just-finished frame overflow". The
    // flag is cleared by the PPU at dot 1 of the pre-render line
    // (261), which is *before* the next NMI, so each NMI sees a
    // flag that reflects only the frame it follows.
    //
    // Reading $2002 has the side effects of (a) clearing the
    // vblank latch in bit 7 and (b) resetting the $2005/$2006
    // write-toggle. Both are harmless here: NMI was already
    // taken, and `gen_ppu_update_apply` below always opens its
    // own $2006 address with a fresh pair of writes so the reset
    // toggle doesn't confuse it.
    //
    // The counter/sticky pair mirrors the frame-overrun pattern
    // at $07FE/$07FF. Release builds don't emit this block at
    // all, so the two bytes at $07FC/$07FD stay free for the
    // analyzer to allocate over.
    if debug_mode {
        out.push(Instruction::new(LDA, AM::Absolute(PPU_STATUS)));
        out.push(Instruction::new(AND, AM::Immediate(0x20)));
        out.push(Instruction::new(
            BEQ,
            AM::LabelRelative("__debug_no_sprite_ovf".into()),
        ));
        out.push(Instruction::new(
            INC,
            AM::Absolute(DEBUG_SPRITE_OVERFLOW_COUNT_ADDR),
        ));
        // Reuse A, which still holds 0x20. Nonzero is enough for
        // the sticky bit; the exact value doesn't matter because
        // user code reads it as a boolean via
        // `debug.sprite_overflow()`.
        out.push(Instruction::new(
            STA,
            AM::Absolute(DEBUG_SPRITE_OVERFLOW_FLAG_ADDR),
        ));
        out.push(Instruction::new(
            NOP,
            AM::Label("__debug_no_sprite_ovf".into()),
        ));
    }

    // Run the audio driver's per-frame tick *after* the saves so it
    // can freely reuse A/X/Y and the $02/$03 scratch slots without
    // corrupting anything the main loop cares about. Programs that
    // never touch audio skip this splice entirely — no ROM cost.
    if has_audio {
        out.push(Instruction::new(JSR, AM::Label("__audio_tick".into())));
    }

    // OAM DMA — transfer sprite data from $0200. Skipped entirely
    // for programs that never `draw`: gated on `has_oam`, which the
    // linker sets from the `__oam_used` marker the IR codegen drops
    // at the first `IrOp::DrawSprite`. `has_sprite_cycle` is a
    // strict subset of `has_oam` so a program that opts into cycling
    // has definitely also drawn something.
    //
    // Programs that *do* draw choose between two paths: the classic
    // fixed-offset (LDA #0) and the rotating offset read from
    // SPRITE_CYCLE_ADDR used by `cycle_sprites`.
    if has_oam {
        if has_sprite_cycle {
            out.push(Instruction::new(LDA, AM::Absolute(SPRITE_CYCLE_ADDR)));
        } else {
            out.push(Instruction::new(LDA, AM::Immediate(0x00)));
        }
        out.push(Instruction::new(STA, AM::Absolute(OAM_ADDR)));
        out.push(Instruction::new(LDA, AM::Immediate(0x02)));
        out.push(Instruction::new(STA, AM::Absolute(OAM_DMA)));
    }

    // PPU updates: check the flags byte, apply any pending palette
    // or background write. Runs inside vblank where $2006/$2007
    // writes are safe. Gated on `has_ppu_updates` so programs that
    // never touch palette or background decls skip this entirely.
    if has_ppu_updates {
        out.extend(gen_ppu_update_apply());
    }

    // VRAM update buffer: drain any entries user code appended this
    // frame (via `nt_set` / `nt_attr` / `nt_fill_h`). Runs after the
    // palette/background handshake so compiler-queued PPU writes win
    // priority for vblank cycles. Gated on `has_vram_buf` — programs
    // that never touch the buffer skip the JSR + the 256-byte
    // reservation at `$0400-$04FF`.
    if has_vram_buf {
        out.push(Instruction::new(JSR, AM::Label("__vram_buf_drain".into())));
    }

    // Controller sampling. The strobe write to $4016 latches both
    // controller ports on the same clock, so the 8-iteration shift
    // loop that follows can read whichever of the two the program
    // actually uses. Programs that touch no `button.*` at all skip
    // the whole block.
    if has_p1_input || has_p2_input {
        // Before strobing: snapshot the previous frame's input
        // byte into main RAM so edge-triggered reads
        // (`p1.a.pressed` / `.released`) can compute
        // `curr & ~prev` / `prev & ~curr` at the user-code read
        // site. Gated on `has_edge_input` so programs without
        // edge reads skip the two (or four) store bytes and
        // leave the two PREV_INPUT slots free for the analyzer.
        if has_edge_input {
            if has_p1_input {
                out.push(Instruction::new(LDA, AM::ZeroPage(ZP_INPUT_P1)));
                out.push(Instruction::new(STA, AM::Absolute(PREV_INPUT_P1)));
            }
            if has_p2_input {
                out.push(Instruction::new(LDA, AM::ZeroPage(ZP_INPUT_P2)));
                out.push(Instruction::new(STA, AM::Absolute(PREV_INPUT_P2)));
            }
        }
        // Strobe: write 1 then 0 to $4016 so both port latches
        // capture the current button state.
        out.push(Instruction::new(LDA, AM::Immediate(0x01)));
        out.push(Instruction::new(STA, AM::Absolute(JOY1)));
        out.push(Instruction::new(LDA, AM::Immediate(0x00)));
        out.push(Instruction::new(STA, AM::Absolute(JOY1)));

        // 8 iterations of read-and-shift. Each active port costs
        // three instructions (LDA abs, LSR A, ROL zp) inside the
        // loop; inactive ports emit nothing.
        out.push(Instruction::new(LDX, AM::Immediate(0x08)));
        out.push(Instruction::new(NOP, AM::Label("__read_input".into())));
        if has_p1_input {
            out.push(Instruction::new(LDA, AM::Absolute(JOY1)));
            out.push(Instruction::new(LSR, AM::Accumulator));
            out.push(Instruction::new(ROL, AM::ZeroPage(ZP_INPUT_P1)));
        }
        if has_p2_input {
            out.push(Instruction::new(LDA, AM::Absolute(0x4017))); // JOY2
            out.push(Instruction::new(LSR, AM::Accumulator));
            out.push(Instruction::new(ROL, AM::ZeroPage(ZP_INPUT_P2)));
        }
        out.push(Instruction::implied(DEX));
        out.push(Instruction::new(
            BNE,
            AM::LabelRelative("__read_input".into()),
        ));
    }

    // Debug frame-overrun check. The frame flag is "set on NMI,
    // cleared by wait_frame". If we see it set at the top of a
    // new NMI, the main loop never reached its wait_frame since
    // the previous vblank — i.e. the frame overran. Bump a
    // counter at `DEBUG_FRAME_OVERRUN_ADDR` in that case so user
    // code can `peek(0x07FF)` to see how many overruns have
    // happened. The check is gated on `debug_mode` so release
    // builds emit nothing here.
    if debug_mode {
        // Read the previous flag. If zero, skip the bump.
        out.push(Instruction::new(LDA, AM::ZeroPage(ZP_FRAME_FLAG)));
        out.push(Instruction::new(
            BEQ,
            AM::LabelRelative("__debug_no_overrun".into()),
        ));
        out.push(Instruction::new(
            INC,
            AM::Absolute(DEBUG_FRAME_OVERRUN_ADDR),
        ));
        // Set the per-frame sticky bit. It stays set until the
        // next `wait_frame` clears it, so a single
        // `debug.assert(!debug.frame_overran())` guard at the top
        // of `on frame { ... }` catches any miss in the previous
        // window.
        out.push(Instruction::new(LDA, AM::Immediate(0x01)));
        out.push(Instruction::new(
            STA,
            AM::Absolute(DEBUG_FRAME_OVERRUN_FLAG_ADDR),
        ));
        out.push(Instruction::new(
            NOP,
            AM::Label("__debug_no_overrun".into()),
        ));
    }

    // Set frame-ready flag
    out.push(Instruction::new(LDA, AM::Immediate(0x01)));
    out.push(Instruction::new(STA, AM::ZeroPage(ZP_FRAME_FLAG)));

    // Restore the mul/state scratch slots ($03 then $02, reverse
    // order of the PHA pushes above).
    out.push(Instruction::implied(PLA));
    out.push(Instruction::new(STA, AM::ZeroPage(0x03)));
    out.push(Instruction::implied(PLA));
    out.push(Instruction::new(STA, AM::ZeroPage(0x02)));

    // Restore registers
    out.push(Instruction::implied(PLA));
    out.push(Instruction::implied(TAY));
    out.push(Instruction::implied(PLA));
    out.push(Instruction::implied(TAX));
    out.push(Instruction::implied(PLA));

    // Return from interrupt
    out.push(Instruction::implied(RTI));

    out
}

/// Generate the IRQ handler (just RTI for now).
pub fn gen_irq() -> Vec<Instruction> {
    vec![Instruction::implied(RTI)]
}

/// Generate the in-NMI PPU update helper. Checks
/// [`ZP_PPU_UPDATE_FLAGS`] and, if any bit is set, copies the
/// corresponding blob from PRG ROM to PPU RAM via `$2006`/`$2007`.
/// Safe because the NMI fires at the start of vblank, giving
/// ~2273 CPU cycles of safe PPU write time — enough for a full
/// palette (32 bytes, ~200 cycles) plus a full nametable
/// (1024 bytes, ~6500 cycles; this doesn't fit in a single frame
/// so big updates should be staged by the caller).
///
/// For simplicity and to keep the NMI bounded, this helper writes
/// the palette first and the nametable second, and only one of
/// each can be pending at a time. If a nametable write is larger
/// than vblank allows the program is responsible for either
/// keeping rendering disabled or splitting the update.
///
/// The helper clears the pending flag only for updates it actually
/// applied, so if a program ever queues a palette and a nametable
/// in the same frame both land on the same NMI.
fn gen_ppu_update_apply() -> Vec<Instruction> {
    let mut out = Vec::new();

    // Read flags. If zero, jump straight to the done label.
    out.push(Instruction::new(LDA, AM::ZeroPage(ZP_PPU_UPDATE_FLAGS)));
    out.push(Instruction::new(
        BEQ,
        AM::LabelRelative("__ppu_update_done".into()),
    ));

    // ── palette update (bit 0) ────────────────────────────────
    // Check bit 0; if clear, skip to background.
    out.push(Instruction::new(AND, AM::Immediate(0x01)));
    out.push(Instruction::new(
        BEQ,
        AM::LabelRelative("__ppu_update_no_palette".into()),
    ));
    // Set PPU addr to $3F00.
    out.push(Instruction::new(LDA, AM::Absolute(PPU_STATUS)));
    out.push(Instruction::new(LDA, AM::Immediate(0x3F)));
    out.push(Instruction::new(STA, AM::Absolute(0x2006)));
    out.push(Instruction::new(LDA, AM::Immediate(0x00)));
    out.push(Instruction::new(STA, AM::Absolute(0x2006)));
    // Loop: write 32 bytes via `LDA (zp),Y` indirect-indexed from
    // the pending palette pointer at $12/$13.
    out.push(Instruction::new(LDY, AM::Immediate(0x00)));
    out.push(Instruction::new(NOP, AM::Label("__ppu_pal_loop".into())));
    out.push(Instruction::new(LDA, AM::IndirectY(ZP_PENDING_PALETTE_LO)));
    out.push(Instruction::new(STA, AM::Absolute(0x2007)));
    out.push(Instruction::implied(INY));
    out.push(Instruction::new(CPY, AM::Immediate(32)));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__ppu_pal_loop".into()),
    ));

    out.push(Instruction::new(
        NOP,
        AM::Label("__ppu_update_no_palette".into()),
    ));

    // ── background update (bit 1) ────────────────────────────
    out.push(Instruction::new(LDA, AM::ZeroPage(ZP_PPU_UPDATE_FLAGS)));
    out.push(Instruction::new(AND, AM::Immediate(0x02)));
    out.push(Instruction::new(
        BEQ,
        AM::LabelRelative("__ppu_update_no_bg".into()),
    ));
    // Nametable 0 starts at $2000.
    out.push(Instruction::new(LDA, AM::Absolute(PPU_STATUS)));
    out.push(Instruction::new(LDA, AM::Immediate(0x20)));
    out.push(Instruction::new(STA, AM::Absolute(0x2006)));
    out.push(Instruction::new(LDA, AM::Immediate(0x00)));
    out.push(Instruction::new(STA, AM::Absolute(0x2006)));
    // Write 960 bytes as 4 loops of 240 (so Y fits in u8) — simpler
    // to write as an outer X counter across 4 × 240-byte pages.
    // X = 4 pages to go
    out.push(Instruction::new(LDX, AM::Immediate(4)));
    out.push(Instruction::new(NOP, AM::Label("__ppu_bg_outer".into())));
    out.push(Instruction::new(LDY, AM::Immediate(0x00)));
    out.push(Instruction::new(NOP, AM::Label("__ppu_bg_inner".into())));
    out.push(Instruction::new(LDA, AM::IndirectY(ZP_PENDING_BG_TILES_LO)));
    out.push(Instruction::new(STA, AM::Absolute(0x2007)));
    out.push(Instruction::implied(INY));
    out.push(Instruction::new(CPY, AM::Immediate(240)));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__ppu_bg_inner".into()),
    ));
    // After each 240-byte block, bump the pointer by 240 so the
    // next block reads from the following chunk of the blob.
    out.push(Instruction::new(LDA, AM::ZeroPage(ZP_PENDING_BG_TILES_LO)));
    out.push(Instruction::new(CLC, AM::Implied));
    out.push(Instruction::new(ADC, AM::Immediate(240)));
    out.push(Instruction::new(STA, AM::ZeroPage(ZP_PENDING_BG_TILES_LO)));
    out.push(Instruction::new(LDA, AM::ZeroPage(ZP_PENDING_BG_TILES_HI)));
    out.push(Instruction::new(ADC, AM::Immediate(0)));
    out.push(Instruction::new(STA, AM::ZeroPage(ZP_PENDING_BG_TILES_HI)));
    out.push(Instruction::implied(DEX));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__ppu_bg_outer".into()),
    ));
    // Now write the 64-byte attribute table (at $23C0 — right after
    // the nametable we just wrote). The PPU auto-increment sits at
    // $23C0 already since we wrote exactly 960 bytes after $2000.
    out.push(Instruction::new(LDY, AM::Immediate(0x00)));
    out.push(Instruction::new(
        NOP,
        AM::Label("__ppu_bg_attr_loop".into()),
    ));
    out.push(Instruction::new(LDA, AM::IndirectY(ZP_PENDING_BG_ATTRS_LO)));
    out.push(Instruction::new(STA, AM::Absolute(0x2007)));
    out.push(Instruction::implied(INY));
    out.push(Instruction::new(CPY, AM::Immediate(64)));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__ppu_bg_attr_loop".into()),
    ));
    out.push(Instruction::new(
        NOP,
        AM::Label("__ppu_update_no_bg".into()),
    ));

    // Clear all pending flags. Programs re-queue every frame if
    // they want repeating updates.
    out.push(Instruction::new(LDA, AM::Immediate(0x00)));
    out.push(Instruction::new(STA, AM::ZeroPage(ZP_PPU_UPDATE_FLAGS)));

    out.push(Instruction::new(NOP, AM::Label("__ppu_update_done".into())));

    out
}

/// Emit a reset-time write of a 32-byte palette blob (referenced
/// by label) to PPU `$3F00-$3F1F`. Rendering must be disabled
/// when this runs (it is, between `gen_init` and the linker's PPU
/// rendering-enable step). Uses the scratch ZP slots `$02/$03` to
/// hold the indirect pointer — safe because nothing else runs
/// between `gen_init` and user code.
#[must_use]
pub fn gen_initial_palette_load(label: &str) -> Vec<Instruction> {
    let mut out = Vec::new();
    out.push(Instruction::new(LDA, AM::Absolute(PPU_STATUS))); // reset latch
    out.push(Instruction::new(LDA, AM::Immediate(0x3F)));
    out.push(Instruction::new(STA, AM::Absolute(0x2006)));
    out.push(Instruction::new(LDA, AM::Immediate(0x00)));
    out.push(Instruction::new(STA, AM::Absolute(0x2006)));
    // Stash the palette label into scratch ZP for indirect LDA.
    out.push(Instruction::new(LDA, AM::SymbolLo(label.to_string())));
    out.push(Instruction::new(STA, AM::ZeroPage(0x02)));
    out.push(Instruction::new(LDA, AM::SymbolHi(label.to_string())));
    out.push(Instruction::new(STA, AM::ZeroPage(0x03)));
    out.push(Instruction::new(LDY, AM::Immediate(0x00)));
    let loop_label = format!("__init_pal_loop_{label}");
    out.push(Instruction::new(NOP, AM::Label(loop_label.clone())));
    out.push(Instruction::new(LDA, AM::IndirectY(0x02)));
    out.push(Instruction::new(STA, AM::Absolute(0x2007)));
    out.push(Instruction::implied(INY));
    out.push(Instruction::new(CPY, AM::Immediate(32)));
    out.push(Instruction::new(BNE, AM::LabelRelative(loop_label)));
    out
}

/// Emit a reset-time write of a 960-byte nametable + 64-byte
/// attribute table blob to nametable 0 (`$2000-$23FF`). Rendering
/// must be disabled when this runs. The caller passes the label of
/// the tiles blob and the label of the attribute blob separately —
/// the linker emits them as adjacent data blocks so they can be
/// resolved independently.
#[must_use]
pub fn gen_initial_background_load(tiles_label: &str, attrs_label: &str) -> Vec<Instruction> {
    let mut out = Vec::new();
    out.push(Instruction::new(LDA, AM::Absolute(PPU_STATUS)));
    out.push(Instruction::new(LDA, AM::Immediate(0x20)));
    out.push(Instruction::new(STA, AM::Absolute(0x2006)));
    out.push(Instruction::new(LDA, AM::Immediate(0x00)));
    out.push(Instruction::new(STA, AM::Absolute(0x2006)));

    // Write 960 bytes of tile data as 4 × 240 using two nested
    // counters. We stash the outer page index in a scratch ZP slot
    // because X is too small to index a 960-byte range directly.
    out.push(Instruction::new(LDX, AM::Immediate(0x00)));
    let page_loop = format!("__init_bg_page_{tiles_label}");
    let inner_loop = format!("__init_bg_inner_{tiles_label}");
    out.push(Instruction::new(NOP, AM::Label(page_loop.clone())));
    // Per-page offset: X*240. Computed via Y and clamped at 240.
    out.push(Instruction::new(LDY, AM::Immediate(0x00)));
    out.push(Instruction::new(NOP, AM::Label(inner_loop.clone())));
    // Fetch byte at blob[X*240 + Y]. We materialize the effective
    // absolute address by unrolling 4 separate LDA Absolute,Y
    // instructions, one per page, dispatched on X.
    // For simplicity and correctness we take the slower path:
    // compute (blob + X*240) as a ZP pointer and read via
    // `LDA (zp),Y`.
    // ZP scratch at $02/$03 (same slots used by the multiply/divide
    // contract; gen_init runs before any user code so they're free).
    out.push(Instruction::new(LDA, AM::SymbolLo(tiles_label.to_string())));
    out.push(Instruction::new(STA, AM::ZeroPage(0x02)));
    out.push(Instruction::new(LDA, AM::SymbolHi(tiles_label.to_string())));
    out.push(Instruction::new(STA, AM::ZeroPage(0x03)));
    // Add X*240 to the low byte (high byte carries via ADC).
    // Actually — to keep this simple, we instead track bytes
    // remaining as a 16-bit counter and use a generic LDA (ZP),Y
    // loop. Rewrite the routine as a flat byte-counted loop.
    // (Undo the per-page setup above by rebuilding the output
    // vector from scratch.)
    out.clear();

    out.push(Instruction::new(LDA, AM::Absolute(PPU_STATUS)));
    out.push(Instruction::new(LDA, AM::Immediate(0x20)));
    out.push(Instruction::new(STA, AM::Absolute(0x2006)));
    out.push(Instruction::new(LDA, AM::Immediate(0x00)));
    out.push(Instruction::new(STA, AM::Absolute(0x2006)));

    // Load tile blob pointer into $02/$03 scratch slots.
    out.push(Instruction::new(LDA, AM::SymbolLo(tiles_label.to_string())));
    out.push(Instruction::new(STA, AM::ZeroPage(0x02)));
    out.push(Instruction::new(LDA, AM::SymbolHi(tiles_label.to_string())));
    out.push(Instruction::new(STA, AM::ZeroPage(0x03)));

    // 4 pages × 240 bytes each = 960 bytes total.
    out.push(Instruction::new(LDX, AM::Immediate(4)));
    let outer = format!("__init_bg_outer_{tiles_label}");
    let inner = format!("__init_bg_inner_{tiles_label}");
    out.push(Instruction::new(NOP, AM::Label(outer.clone())));
    out.push(Instruction::new(LDY, AM::Immediate(0x00)));
    out.push(Instruction::new(NOP, AM::Label(inner.clone())));
    out.push(Instruction::new(LDA, AM::IndirectY(0x02)));
    out.push(Instruction::new(STA, AM::Absolute(0x2007)));
    out.push(Instruction::implied(INY));
    out.push(Instruction::new(CPY, AM::Immediate(240)));
    out.push(Instruction::new(BNE, AM::LabelRelative(inner)));
    // Advance pointer by 240.
    out.push(Instruction::new(LDA, AM::ZeroPage(0x02)));
    out.push(Instruction::new(CLC, AM::Implied));
    out.push(Instruction::new(ADC, AM::Immediate(240)));
    out.push(Instruction::new(STA, AM::ZeroPage(0x02)));
    out.push(Instruction::new(LDA, AM::ZeroPage(0x03)));
    out.push(Instruction::new(ADC, AM::Immediate(0)));
    out.push(Instruction::new(STA, AM::ZeroPage(0x03)));
    out.push(Instruction::implied(DEX));
    out.push(Instruction::new(BNE, AM::LabelRelative(outer)));

    // Now the 64 attribute bytes land at $23C0 — the PPU auto-
    // increment is already there after the 960 tile writes.
    out.push(Instruction::new(LDA, AM::SymbolLo(attrs_label.to_string())));
    out.push(Instruction::new(STA, AM::ZeroPage(0x02)));
    out.push(Instruction::new(LDA, AM::SymbolHi(attrs_label.to_string())));
    out.push(Instruction::new(STA, AM::ZeroPage(0x03)));
    out.push(Instruction::new(LDY, AM::Immediate(0x00)));
    let attr_loop = format!("__init_bg_attr_{attrs_label}");
    out.push(Instruction::new(NOP, AM::Label(attr_loop.clone())));
    out.push(Instruction::new(LDA, AM::IndirectY(0x02)));
    out.push(Instruction::new(STA, AM::Absolute(0x2007)));
    out.push(Instruction::implied(INY));
    out.push(Instruction::new(CPY, AM::Immediate(64)));
    out.push(Instruction::new(BNE, AM::LabelRelative(attr_loop)));
    out
}

/// Zero-page locations used by the multiply / divide routines.
/// `$02` is the "second operand" input slot — the multiplier for
/// `__multiply` and the divisor for `__divide`. `$04` is the
/// routines' private scratch: it holds the working multiplicand
/// (shifted left each iteration) for multiply and the running
/// dividend-turning-into-quotient for divide. Both routines keep
/// their running output in the accumulator, so `$03`
/// (`ZP_CURRENT_STATE` in the codegen) stays untouched — aliasing
/// `$03` across the divide routine used to zero it and hand
/// control to state 0 on the next frame.
const ZP_MUL_OPERAND: u8 = 0x02;
const ZP_DIV_DIVISOR: u8 = 0x02;

/// Generate 8x8 -> 8 software multiply routine.
///
/// Input: A = multiplicand, zero-page $02 = multiplier
/// Output: A = product (low byte; high byte is discarded for
/// unsigned u8 * u8 → u8 semantics)
///
/// Algorithm: shift-and-add. For each bit of the multiplier, if set,
/// add the (shifted) multiplicand to the running product. The
/// product is kept in the accumulator — not in ZP `$03` — so the
/// routine doesn't alias with `ZP_CURRENT_STATE`. `$02` is read-
/// only at the callsite (the divisor/multiplier input slot) and is
/// shifted in place here, which is fine because the caller re-
/// populates it on every `__multiply` call.
pub fn gen_multiply() -> Vec<Instruction> {
    let mut out = Vec::new();

    // Label for the subroutine entry
    out.push(Instruction::new(NOP, AM::Label("__multiply".into())));

    // Store multiplicand in $04 (working copy; we shift it left
    // each iteration to line up with the next multiplier bit).
    out.push(Instruction::new(STA, AM::ZeroPage(0x04)));

    // Running product starts at 0 in A.
    out.push(Instruction::new(LDA, AM::Immediate(0x00)));

    // Loop counter: 8 bits
    out.push(Instruction::new(LDX, AM::Immediate(0x08)));

    // __mul_loop:
    out.push(Instruction::new(NOP, AM::Label("__mul_loop".into())));

    // Shift multiplier right, check carry (current bit).
    out.push(Instruction::new(LSR, AM::ZeroPage(ZP_MUL_OPERAND)));
    out.push(Instruction::new(
        BCC,
        AM::LabelRelative("__mul_no_add".into()),
    ));

    // Carry set: add the current shifted multiplicand to the
    // running product in A. CLC first because LSR sets carry to the
    // shifted-out bit.
    out.push(Instruction::implied(CLC));
    out.push(Instruction::new(ADC, AM::ZeroPage(0x04)));

    // __mul_no_add:
    out.push(Instruction::new(NOP, AM::Label("__mul_no_add".into())));

    // Shift multiplicand left (double it) for the next bit
    // position.
    out.push(Instruction::new(ASL, AM::ZeroPage(0x04)));

    // Decrement counter
    out.push(Instruction::implied(DEX));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__mul_loop".into()),
    ));

    // A already holds the product.
    out.push(Instruction::implied(RTS));

    out
}

/// Generate the per-NMI audio tick. This is the heart of the audio
/// driver — it walks both the SFX envelope and the music note stream
/// every frame and writes the resulting APU register values.
///
/// The linker splices a `JSR __audio_tick` into the NMI handler
/// whenever user code contains any audio op (detected by the
/// `__audio_used` marker label), so programs that never call
/// `play`/`start_music`/`stop_music` pay zero ROM or cycle cost.
///
/// ## SFX channel (pulse 1)
///
/// State:
/// - `ZP_SFX_COUNTER` — nonzero while an sfx is playing
/// - `ZP_SFX_PTR_LO/HI` — pointer into the current sfx blob,
///   advanced one byte per frame
///
/// Each frame: if the counter is nonzero, read one byte through the
/// pointer, write it to `$4000`, and advance the pointer. A zero
/// byte is the sentinel; on it the driver mutes pulse 1 and clears
/// the counter.
///
/// ## Music channel (pulse 2)
///
/// State:
/// - `ZP_MUSIC_COUNTER` — frames remaining on the current note
/// - `ZP_MUSIC_STATE` — bit 1 set = active; bits encode duty/volume/loop
/// - `ZP_MUSIC_PTR_LO/HI` — pointer to the next (pitch,dur) pair
/// - `ZP_MUSIC_BASE_LO/HI` — loop-back start of the current track
///
/// Each frame: if the state says "active" and the counter is nonzero,
/// decrement the counter and bail. When it hits zero, advance past
/// the current (pitch,dur) pair and read the next one. `0xFF,0xFF`
/// is the end-of-track sentinel; the driver either rewinds to the
/// base pointer (looping tracks) or mutes pulse 2 (one-shot tracks).
///
/// ## Clobbers
///
/// A, X, Y. The NMI handler calls this from inside its own
/// save/restore block so caller registers are safe.
///
/// When `has_noise` / `has_triangle` are set, the driver gains an
/// extra per-channel slot: noise routes envelope bytes to `$400C`
/// and drives `$400E` / `$400F` on trigger; triangle writes linear-
/// counter reload values to `$4008`. These blocks are appended to
/// the tick after the music path so that programs which do not
/// declare any noise or triangle sfx produce byte-identical ROM
/// output — the old pulse-only path emits exactly the same
/// instruction stream as before. The linker decides whether to
/// enable each by scanning for the `__noise_used` and
/// `__triangle_used` marker labels emitted by the IR codegen.
pub fn gen_audio_tick(
    has_noise: bool,
    has_triangle: bool,
    has_sfx_pitch: bool,
) -> Vec<Instruction> {
    let mut out = Vec::new();

    out.push(Instruction::new(NOP, AM::Label("__audio_tick".into())));

    // ── SFX tick ──
    // If counter is zero, no sfx is playing; skip.
    out.push(Instruction::new(LDA, AM::ZeroPage(ZP_SFX_COUNTER)));
    out.push(Instruction::new(
        BEQ,
        AM::LabelRelative("__audio_sfx_done".into()),
    ));
    // Read next envelope byte via (ZP_SFX_PTR),Y with Y=0.
    out.push(Instruction::new(LDY, AM::Immediate(0)));
    out.push(Instruction::new(LDA, AM::IndirectY(ZP_SFX_PTR_LO)));
    // If it's the zero sentinel, silence pulse 1 and clear state.
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__audio_sfx_write".into()),
    ));
    // Sentinel branch: write mute byte to $4000 and clear counter.
    out.push(Instruction::new(LDA, AM::Immediate(0x30)));
    out.push(Instruction::new(STA, AM::Absolute(0x4000)));
    out.push(Instruction::new(LDA, AM::Immediate(0)));
    out.push(Instruction::new(STA, AM::ZeroPage(ZP_SFX_COUNTER)));
    out.push(Instruction::new(JMP, AM::Label("__audio_sfx_done".into())));
    // Non-sentinel branch: write envelope byte to $4000, advance ptr.
    out.push(Instruction::new(NOP, AM::Label("__audio_sfx_write".into())));
    out.push(Instruction::new(STA, AM::Absolute(0x4000)));
    // Advance the 16-bit pointer (lo, hi) by 1.
    out.push(Instruction::new(INC, AM::ZeroPage(ZP_SFX_PTR_LO)));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__audio_sfx_ptr_ok".into()),
    ));
    out.push(Instruction::new(INC, AM::ZeroPage(ZP_SFX_PTR_HI)));
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_sfx_ptr_ok".into()),
    ));
    // Optional per-frame pitch update. Only emitted in programs
    // that declare at least one varying-pitch sfx, gated on the
    // `__sfx_pitch_used` codegen marker. The block reads a byte
    // through (AUDIO_SFX_PITCH_PTR),Y, writes it to `$4002`
    // (pulse-1 period low), then advances the pointer in
    // lockstep with the volume envelope above. A zero high byte
    // in the pointer is treated as "no pitch envelope on the
    // currently-playing sfx" so a program can mix scalar-pitch
    // and varying-pitch sfx without the latter clobbering the
    // former when it isn't playing.
    //
    // The pointer lives in main RAM (no zero-page slot pressure)
    // and is copied into ZP scratch $02/$03 for the indirect
    // read because the 6502 has no `(abs),Y` mode — the same
    // technique used by `gen_noise_tick` / `gen_triangle_tick`.
    if has_sfx_pitch {
        // Bail out if the high byte is zero — sentinel for "the
        // currently-playing sfx has no pitch envelope".
        out.push(Instruction::new(LDA, AM::Absolute(AUDIO_SFX_PITCH_PTR_HI)));
        out.push(Instruction::new(
            BEQ,
            AM::LabelRelative("__audio_sfx_pitch_done".into()),
        ));
        // Stash main-RAM pointer in ZP scratch $02/$03.
        out.push(Instruction::new(LDA, AM::Absolute(AUDIO_SFX_PITCH_PTR_LO)));
        out.push(Instruction::new(STA, AM::ZeroPage(0x02)));
        out.push(Instruction::new(LDA, AM::Absolute(AUDIO_SFX_PITCH_PTR_HI)));
        out.push(Instruction::new(STA, AM::ZeroPage(0x03)));
        out.push(Instruction::new(LDY, AM::Immediate(0)));
        out.push(Instruction::new(LDA, AM::IndirectY(0x02)));
        // Zero pitch byte? Treat it as the matching mute sentinel
        // (volume envelope's zero will already mute on the next
        // tick) and skip the period write so we don't yank pulse-1
        // to a 0 period for one frame before muting.
        out.push(Instruction::new(
            BEQ,
            AM::LabelRelative("__audio_sfx_pitch_advance".into()),
        ));
        out.push(Instruction::new(STA, AM::Absolute(0x4002)));
        out.push(Instruction::new(
            NOP,
            AM::Label("__audio_sfx_pitch_advance".into()),
        ));
        // Advance the main-RAM pointer 1 byte.
        out.push(Instruction::new(INC, AM::Absolute(AUDIO_SFX_PITCH_PTR_LO)));
        out.push(Instruction::new(
            BNE,
            AM::LabelRelative("__audio_sfx_pitch_done".into()),
        ));
        out.push(Instruction::new(INC, AM::Absolute(AUDIO_SFX_PITCH_PTR_HI)));
        out.push(Instruction::new(
            NOP,
            AM::Label("__audio_sfx_pitch_done".into()),
        ));
    }
    out.push(Instruction::new(NOP, AM::Label("__audio_sfx_done".into())));

    // ── Music tick ──
    // Bit 1 of ZP_MUSIC_STATE is "music is active". If clear, skip.
    out.push(Instruction::new(LDA, AM::ZeroPage(ZP_MUSIC_STATE)));
    out.push(Instruction::new(AND, AM::Immediate(0x02)));
    out.push(Instruction::new(
        BEQ,
        AM::LabelRelative("__audio_music_done".into()),
    ));
    // Active. Decrement the note counter; if nonzero after, bail.
    out.push(Instruction::new(DEC, AM::ZeroPage(ZP_MUSIC_COUNTER)));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__audio_music_done".into()),
    ));
    // Counter just hit zero — time to advance. Fall through to the
    // "advance to next note" block below. The runtime calls this
    // block from two places: end-of-note and start_music (which sets
    // counter=0 then jumps here to trigger the first note).
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_music_advance".into()),
    ));
    // Read the next pitch byte. LDA sets Z based on the value so
    // we can dispatch on it cheaply:
    //   pitch == 0    → rest     (fall through to __rest)
    //   pitch == 0xFF → sentinel (BNE past rest, then CMP + BEQ)
    //   otherwise     → pitched  (fall through to __pitched)
    out.push(Instruction::new(LDY, AM::Immediate(0)));
    out.push(Instruction::new(LDA, AM::IndirectY(ZP_MUSIC_PTR_LO)));
    // Zero? → rest branch (mute pulse 2, skip period lookup).
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__audio_music_not_rest".into()),
    ));
    out.push(Instruction::new(LDA, AM::Immediate(0x30)));
    out.push(Instruction::new(STA, AM::Absolute(0x4004)));
    out.push(Instruction::new(
        JMP,
        AM::Label("__audio_music_load_dur".into()),
    ));
    // Not zero — check sentinel, otherwise it's a real note.
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_music_not_rest".into()),
    ));
    out.push(Instruction::new(CMP, AM::Immediate(0xFF)));
    out.push(Instruction::new(
        BEQ,
        AM::LabelRelative("__audio_music_eot".into()),
    ));
    // Fall through to the pitched branch — A still holds pitch.
    out.push(Instruction::new(
        JMP,
        AM::Label("__audio_music_pitched".into()),
    ));
    // Pitched branch: A already holds pitch (1..=60). Index the
    // period table and write $4006 (period lo) and $4007 (period
    // hi + length counter). Each table entry is 2 bytes.
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_music_pitched".into()),
    ));
    // Rewrite envelope byte ($4004) from music state so we don't
    // depend on pulse-2 length counter. Extract duty (bits 6-7) and
    // volume (bits 2-5) from state, shift into position, OR with $30
    // (length-halt + constant volume), write $4004.
    //
    // Save pitch in X so we still have it for the period lookup.
    out.push(Instruction::new(TAX, AM::Implied));
    // Build envelope byte.
    out.push(Instruction::new(LDA, AM::ZeroPage(ZP_MUSIC_STATE)));
    out.push(Instruction::new(AND, AM::Immediate(0xC0))); // keep duty bits
    out.push(Instruction::new(STA, AM::ZeroPage(0x04))); // scratch
    out.push(Instruction::new(LDA, AM::ZeroPage(ZP_MUSIC_STATE)));
    out.push(Instruction::new(AND, AM::Immediate(0x3C))); // keep volume<<2
    out.push(Instruction::new(LSR, AM::Accumulator));
    out.push(Instruction::new(LSR, AM::Accumulator));
    out.push(Instruction::new(ORA, AM::ZeroPage(0x04)));
    out.push(Instruction::new(ORA, AM::Immediate(0x30)));
    out.push(Instruction::new(STA, AM::Absolute(0x4004)));

    // Period lookup via a ZP pointer. X holds pitch (1..=60).
    //
    //   1. Set (ZP_SCRATCH = __period_table).
    //   2. A = (pitch - 1) * 2 — byte offset in the 2-byte-per-entry
    //      table.
    //   3. Y = A.
    //   4. LDA (ZP_SCRATCH),Y → period_lo → STA $4006.
    //   5. INY; LDA (ZP_SCRATCH),Y → period_hi → STA $4007.
    //
    // `$02`/`$03` are the multiply/divide scratch slots but the NMI
    // audio tick never calls mul/div, so they're free to reuse here.
    // A proper `Absolute,Y` addressing mode with a symbolic label
    // would save the pointer setup, but our asm layer doesn't have
    // that yet and the extra 8 cycles per frame are negligible.
    out.push(Instruction::new(LDA, AM::SymbolLo("__period_table".into())));
    out.push(Instruction::new(STA, AM::ZeroPage(0x02)));
    out.push(Instruction::new(LDA, AM::SymbolHi("__period_table".into())));
    out.push(Instruction::new(STA, AM::ZeroPage(0x03)));
    out.push(Instruction::new(TXA, AM::Implied));
    out.push(Instruction::new(SEC, AM::Implied));
    out.push(Instruction::new(SBC, AM::Immediate(1)));
    out.push(Instruction::new(ASL, AM::Accumulator));
    out.push(Instruction::new(TAY, AM::Implied));
    out.push(Instruction::new(LDA, AM::IndirectY(0x02)));
    out.push(Instruction::new(STA, AM::Absolute(0x4006)));
    out.push(Instruction::new(INY, AM::Implied));
    out.push(Instruction::new(LDA, AM::IndirectY(0x02)));
    // The period-table high byte already has the length-counter
    // load bits baked in (see `gen_period_table`), so a raw store
    // here retriggers the note. But retriggering every time the
    // duration expires is fine — it's how trackers work.
    out.push(Instruction::new(STA, AM::Absolute(0x4007)));

    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_music_load_dur".into()),
    ));
    // Advance pointer past the pitch byte we just consumed.
    out.push(Instruction::new(INC, AM::ZeroPage(ZP_MUSIC_PTR_LO)));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__audio_music_dur_hi_ok".into()),
    ));
    out.push(Instruction::new(INC, AM::ZeroPage(ZP_MUSIC_PTR_HI)));
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_music_dur_hi_ok".into()),
    ));
    // Read duration through the advanced pointer and stash it in
    // ZP_MUSIC_COUNTER.
    out.push(Instruction::new(LDY, AM::Immediate(0)));
    out.push(Instruction::new(LDA, AM::IndirectY(ZP_MUSIC_PTR_LO)));
    out.push(Instruction::new(STA, AM::ZeroPage(ZP_MUSIC_COUNTER)));
    // Advance past the duration byte.
    out.push(Instruction::new(INC, AM::ZeroPage(ZP_MUSIC_PTR_LO)));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__audio_music_ptr2_ok".into()),
    ));
    out.push(Instruction::new(INC, AM::ZeroPage(ZP_MUSIC_PTR_HI)));
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_music_ptr2_ok".into()),
    ));
    out.push(Instruction::new(
        JMP,
        AM::Label("__audio_music_done".into()),
    ));

    // ── End-of-track branch ──
    out.push(Instruction::new(NOP, AM::Label("__audio_music_eot".into())));
    // Check loop flag (bit 0 of ZP_MUSIC_STATE). If set, rewind ptr
    // to base and re-enter the advance path. Otherwise stop.
    out.push(Instruction::new(LDA, AM::ZeroPage(ZP_MUSIC_STATE)));
    out.push(Instruction::new(AND, AM::Immediate(0x01)));
    out.push(Instruction::new(
        BEQ,
        AM::LabelRelative("__audio_music_stop".into()),
    ));
    // Looping: copy base pointer back into current pointer and
    // re-enter the advance path.
    out.push(Instruction::new(LDA, AM::ZeroPage(ZP_MUSIC_BASE_LO)));
    out.push(Instruction::new(STA, AM::ZeroPage(ZP_MUSIC_PTR_LO)));
    out.push(Instruction::new(LDA, AM::ZeroPage(ZP_MUSIC_BASE_HI)));
    out.push(Instruction::new(STA, AM::ZeroPage(ZP_MUSIC_PTR_HI)));
    out.push(Instruction::new(
        JMP,
        AM::Label("__audio_music_advance".into()),
    ));
    // Non-looping stop: mute pulse 2 and clear music state.
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_music_stop".into()),
    ));
    out.push(Instruction::new(LDA, AM::Immediate(0x30)));
    out.push(Instruction::new(STA, AM::Absolute(0x4004)));
    out.push(Instruction::new(LDA, AM::Immediate(0)));
    out.push(Instruction::new(STA, AM::ZeroPage(ZP_MUSIC_STATE)));
    out.push(Instruction::new(STA, AM::ZeroPage(ZP_MUSIC_COUNTER)));

    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_music_done".into()),
    ));

    // ── Noise channel tick (optional, gated on `has_noise`) ──
    //
    // Structurally identical to the pulse-1 sfx tick above: walk a
    // per-frame envelope blob via an indirect-indexed load and
    // write each byte to the APU noise volume register at $400C.
    // The pointer lives in main RAM at [AUDIO_NOISE_PTR_LO,
    // AUDIO_NOISE_PTR_HI]; the tick stashes it in ZP scratch $02/$03
    // for the duration of the block because the 6502 has no
    // (abs),Y addressing.
    if has_noise {
        out.extend(gen_noise_tick());
    }

    // ── Triangle channel tick (optional, gated on `has_triangle`) ──
    //
    // Same shape as the noise tick but writes to $4008 (the linear
    // counter) instead of a volume register. Triangle has no volume,
    // so the envelope blob just encodes "keep the linear counter
    // loaded" (nonzero hold) or "silence" (the $80 sentinel).
    if has_triangle {
        out.extend(gen_triangle_tick());
    }

    out.push(Instruction::implied(RTS));

    out
}

/// Generate the noise-channel sfx tick. Appended to
/// [`gen_audio_tick`] only when the program declares at least one
/// noise sfx (`__noise_used` marker). Reads envelope bytes from the
/// main-RAM pointer at [`AUDIO_NOISE_PTR_LO`] / [`AUDIO_NOISE_PTR_HI`]
/// and writes them to the APU noise volume register at `$400C`.
/// A zero envelope byte is the mute sentinel — on it the tick
/// silences the channel and clears [`AUDIO_NOISE_COUNTER`].
fn gen_noise_tick() -> Vec<Instruction> {
    let mut out = Vec::new();
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_noise_tick".into()),
    ));
    // If counter is zero, no noise sfx is playing; skip the block.
    out.push(Instruction::new(LDA, AM::Absolute(AUDIO_NOISE_COUNTER)));
    out.push(Instruction::new(
        BEQ,
        AM::LabelRelative("__audio_noise_done".into()),
    ));
    // Load the main-RAM pointer into ZP scratch $02/$03 so we can
    // do an indirect-indexed read (6502 has no (abs),Y mode).
    out.push(Instruction::new(LDA, AM::Absolute(AUDIO_NOISE_PTR_LO)));
    out.push(Instruction::new(STA, AM::ZeroPage(0x02)));
    out.push(Instruction::new(LDA, AM::Absolute(AUDIO_NOISE_PTR_HI)));
    out.push(Instruction::new(STA, AM::ZeroPage(0x03)));
    // Read envelope byte through the scratch pointer.
    out.push(Instruction::new(LDY, AM::Immediate(0)));
    out.push(Instruction::new(LDA, AM::IndirectY(0x02)));
    // Zero sentinel? branch to the write path if nonzero.
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__audio_noise_write".into()),
    ));
    // Sentinel: mute pulse-noise ($4000-compatible encoding:
    // length-halt + constant-volume + volume 0) and clear the
    // counter so this block bails on subsequent NMIs.
    out.push(Instruction::new(LDA, AM::Immediate(0x30)));
    out.push(Instruction::new(STA, AM::Absolute(0x400C)));
    out.push(Instruction::new(LDA, AM::Immediate(0)));
    out.push(Instruction::new(STA, AM::Absolute(AUDIO_NOISE_COUNTER)));
    out.push(Instruction::new(
        JMP,
        AM::Label("__audio_noise_done".into()),
    ));
    // Write envelope byte and advance the 16-bit pointer by 1.
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_noise_write".into()),
    ));
    out.push(Instruction::new(STA, AM::Absolute(0x400C)));
    out.push(Instruction::new(INC, AM::Absolute(AUDIO_NOISE_PTR_LO)));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__audio_noise_ptr_ok".into()),
    ));
    out.push(Instruction::new(INC, AM::Absolute(AUDIO_NOISE_PTR_HI)));
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_noise_ptr_ok".into()),
    ));
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_noise_done".into()),
    ));
    out
}

/// Generate the triangle-channel sfx tick. Same shape as
/// [`gen_noise_tick`] but writes to `$4008` (the linear counter
/// reload) instead of a volume register. Triangle has no volume —
/// the envelope bytes are "keep holding" tokens that the runtime
/// keeps writing every frame so the linear counter never underruns
/// and the channel never auto-silences. A `0x80` byte is the mute
/// sentinel (linear control bit set, reload = 0 → silence next
/// frame).
fn gen_triangle_tick() -> Vec<Instruction> {
    let mut out = Vec::new();
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_triangle_tick".into()),
    ));
    // If counter is zero, no triangle sfx is playing.
    out.push(Instruction::new(LDA, AM::Absolute(AUDIO_TRIANGLE_COUNTER)));
    out.push(Instruction::new(
        BEQ,
        AM::LabelRelative("__audio_triangle_done".into()),
    ));
    // Stash pointer to ZP scratch for indirect-indexed load.
    out.push(Instruction::new(LDA, AM::Absolute(AUDIO_TRIANGLE_PTR_LO)));
    out.push(Instruction::new(STA, AM::ZeroPage(0x02)));
    out.push(Instruction::new(LDA, AM::Absolute(AUDIO_TRIANGLE_PTR_HI)));
    out.push(Instruction::new(STA, AM::ZeroPage(0x03)));
    out.push(Instruction::new(LDY, AM::Immediate(0)));
    out.push(Instruction::new(LDA, AM::IndirectY(0x02)));
    // Write the envelope byte to $4008. For triangle, `$80` is the
    // mute sentinel (linear counter reload = 0 with control bit
    // set). We detect it by CMP + BEQ so the counter can be cleared.
    out.push(Instruction::new(STA, AM::Absolute(0x4008)));
    out.push(Instruction::new(CMP, AM::Immediate(0x80)));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__audio_triangle_advance".into()),
    ));
    // Sentinel: clear counter so we bail next frame. The $80 write
    // above already mutes the triangle channel.
    out.push(Instruction::new(LDA, AM::Immediate(0)));
    out.push(Instruction::new(STA, AM::Absolute(AUDIO_TRIANGLE_COUNTER)));
    out.push(Instruction::new(
        JMP,
        AM::Label("__audio_triangle_done".into()),
    ));
    // Advance the pointer by 1 for the next frame.
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_triangle_advance".into()),
    ));
    out.push(Instruction::new(INC, AM::Absolute(AUDIO_TRIANGLE_PTR_LO)));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__audio_triangle_ptr_ok".into()),
    ));
    out.push(Instruction::new(INC, AM::Absolute(AUDIO_TRIANGLE_PTR_HI)));
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_triangle_ptr_ok".into()),
    ));
    out.push(Instruction::new(
        NOP,
        AM::Label("__audio_triangle_done".into()),
    ));
    out
}

/// Generate the builtin period table that the music tick uses to
/// translate note indices into pulse-channel period values. The
/// table covers five octaves (C1–B5) for 60 entries, 2 bytes each.
///
/// Entry 0 is `C1` (index 1 in user notes), entry 59 is `B5` (index
/// 60). Pitch 0 is the "rest" sentinel and is not present in the
/// table — the driver handles rests before indexing.
///
/// The high byte of each entry is `((period >> 8) & 0x07) | 0x08`.
/// Setting bit 3 pre-loads the length counter to index 1 (254 frames)
/// so any note held beyond the envelope will still play out naturally
/// when the track later falls into a rest — without this, pulse 2
/// would silence itself after ~4 frames on hardware.
#[must_use]
pub fn gen_period_table() -> Vec<Instruction> {
    // NTSC CPU = 1.789773 MHz. Pulse channel frequency:
    //   f = CPU / (16 * (period + 1))
    // Solving for period given a target frequency f:
    //   period = CPU / (16 * f) - 1
    //
    // We compute the 60 entries once at build time (here) using
    // equal-tempered tuning anchored at A4 = 440 Hz.
    const CPU: f64 = 1_789_773.0;
    const A4_HZ: f64 = 440.0;

    let mut out = Vec::new();
    out.push(Instruction::new(NOP, AM::Label("__period_table".into())));
    // Semitone offset from A4 for index `i` (0-based from C1).
    // A4 is MIDI 69. C1 is MIDI 24. So semitones from A4 to C1 is
    // -45 — our table starts at C1 so `offset(i) = i - 45`.
    let mut bytes: Vec<u8> = Vec::with_capacity(120);
    for i in 0i32..60 {
        let semitone_offset = f64::from(i - 45);
        let freq = A4_HZ * 2f64.powf(semitone_offset / 12.0);
        let period_f = CPU / (16.0 * freq) - 1.0;
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let period = period_f.round().clamp(0.0, 2047.0) as u16;
        let lo = (period & 0xFF) as u8;
        // High 3 bits of period + length counter load bits.
        // 0x08 = length counter index 1 = 254 frames.
        let hi = ((period >> 8) as u8 & 0x07) | 0x08;
        bytes.push(lo);
        bytes.push(hi);
    }
    out.push(Instruction::new(NOP, AM::Bytes(bytes)));
    out
}

/// Generate a labelled data block emitting `bytes` verbatim into the
/// ROM at the address the assembler places this block. Used by the
/// linker to splice compiled sfx and music blobs into the code
/// section so that `LDA #<Name; STA ptr_lo` from the IR codegen can
/// resolve to the right in-ROM address.
#[must_use]
pub fn gen_data_block(label: &str, bytes: Vec<u8>) -> Vec<Instruction> {
    vec![
        Instruction::new(NOP, AM::Label(label.to_string())),
        Instruction::new(NOP, AM::Bytes(bytes)),
    ]
}

/// Generate 8 / 8 -> 8 software divide routine (restoring division).
///
/// Input: A = dividend, zero-page $02 = divisor
/// Output: A = remainder, zero-page $04 = quotient
///
/// Keeps the running remainder in the accumulator (instead of ZP
/// $03) so the routine doesn't alias with `ZP_CURRENT_STATE` at
/// $03. Any program with a state machine reads $03 to dispatch
/// `on_frame`; the old shape zeroed it on every divide call and
/// kicked control back to state 0 (usually `Title`) on the very
/// next frame. The only caller-visible change is that `IrOp::Div`
/// now picks up the quotient from `$04` rather than `A` — see
/// `ir_codegen.rs` for the Div/Mod callsite shape. `$04` stays
/// inside the `$00-$0F` runtime reservation so it never collides
/// with user variables (analyzer starts user ZP at `$10` minimum).
pub fn gen_divide() -> Vec<Instruction> {
    let mut out = Vec::new();

    // Label for the subroutine entry
    out.push(Instruction::new(NOP, AM::Label("__divide".into())));

    // Stash dividend in $04. Over the course of the loop we shift
    // it left 8 times; the bits that fall out become the running
    // remainder (in A), and the bits shifted in (via `INC $04`
    // below) become the quotient, so $04 ends up holding exactly
    // the quotient we want to return.
    out.push(Instruction::new(STA, AM::ZeroPage(0x04)));

    // Running remainder starts at 0 in A.
    out.push(Instruction::new(LDA, AM::Immediate(0x00)));

    // Loop counter: 8 bits
    out.push(Instruction::new(LDX, AM::Immediate(0x08)));

    // __div_loop:
    out.push(Instruction::new(NOP, AM::Label("__div_loop".into())));

    // Shift the next bit of the dividend out of $04 into the carry,
    // then rotate it into the remainder accumulator.
    out.push(Instruction::new(ASL, AM::ZeroPage(0x04)));
    out.push(Instruction::new(ROL, AM::Accumulator));

    // Remainder >= divisor? CMP sets carry when A >= memory, clear
    // when A < memory. On `>=` we do the subtraction for real with
    // SBC (which still sees the same carry-set condition) and set
    // the quotient bit for this iteration. On `<` we leave A alone.
    out.push(Instruction::new(CMP, AM::ZeroPage(ZP_DIV_DIVISOR)));
    out.push(Instruction::new(
        BCC,
        AM::LabelRelative("__div_no_sub".into()),
    ));

    // Accept the subtraction into the remainder. SBC with carry set
    // performs a true subtract (no extra borrow).
    out.push(Instruction::new(SBC, AM::ZeroPage(ZP_DIV_DIVISOR)));

    // Set bit 0 of the quotient (stored in $04, whose low bit is
    // free because we just shifted left).
    out.push(Instruction::new(INC, AM::ZeroPage(0x04)));

    // __div_no_sub:
    out.push(Instruction::new(NOP, AM::Label("__div_no_sub".into())));

    // Decrement counter
    out.push(Instruction::implied(DEX));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__div_loop".into()),
    ));

    // A already holds the final remainder. $04 holds the quotient.
    out.push(Instruction::implied(RTS));

    out
}

/// Generate the runtime PRNG routines: `__rand8`, `__rand16`, and
/// `__rand_seed`. Spliced in by the linker only when user code
/// contains the `__rand_used` marker label (emitted by the IR
/// codegen whenever `rand8()`, `rand16()`, or `seed_rand()` is
/// referenced). Programs that never touch the PRNG pay zero ROM
/// or cycle cost.
///
/// ## Algorithm
///
/// A right-shifting Galois-configuration 16-bit LFSR with tap mask
/// `0xB400` on the high byte (polynomial `x^16 + x^14 + x^13 +
/// x^11 + 1`). From any non-zero seed it cycles through all 65535
/// non-zero 16-bit states before repeating. Per step:
///
/// ```text
/// carry = state & 1
/// state >>= 1
/// if carry: state ^= 0xB400
/// ```
///
/// State lives in main RAM at `PRNG_STATE_LO`/`PRNG_STATE_HI`; the
/// reset path seeds it to `0xACE1` so the first draw is useful
/// without requiring an explicit `seed_rand`.
///
/// ## Entry points
///
/// - `__rand8`: advances the state once, returns `A` = new low byte.
///   Clobbers A and flags. ~40 cycles.
/// - `__rand16`: advances once, returns `A` = new low byte,
///   `X` = new high byte — 16 bits from the same shift. Clobbers
///   A, X, and flags. ~50 cycles.
/// - `__rand_seed`: consumes `A` = low byte, `X` = high byte of the
///   new seed and writes them to the state slots. Forces bit 0 of
///   the low byte high so a zero seed (which would stick the LFSR)
///   becomes `(1, 0)`.
#[must_use]
pub fn gen_prng() -> Vec<Instruction> {
    let mut out = Vec::new();

    // ── __rand8 ──────────────────────────────────────────────
    // One Galois LFSR step: shift the 16-bit state right, XOR the
    // high byte with 0xB4 if the shifted-out bit was a 1. The
    // low tap byte is 0x00 so only the high byte needs EORing.
    out.push(Instruction::new(NOP, AM::Label("__rand8".into())));
    // LSR the high byte, ROR the low byte. Carry after ROR holds
    // the old bit 0 of state_lo (the feedback bit).
    out.push(Instruction::new(LSR, AM::Absolute(PRNG_STATE_HI)));
    out.push(Instruction::new(ROR, AM::Absolute(PRNG_STATE_LO)));
    // If the feedback bit was zero, skip the tap XOR.
    out.push(Instruction::new(
        BCC,
        AM::LabelRelative("__rand8_done".into()),
    ));
    out.push(Instruction::new(LDA, AM::Absolute(PRNG_STATE_HI)));
    out.push(Instruction::new(EOR, AM::Immediate(0xB4)));
    out.push(Instruction::new(STA, AM::Absolute(PRNG_STATE_HI)));
    out.push(Instruction::new(NOP, AM::Label("__rand8_done".into())));
    out.push(Instruction::new(LDA, AM::Absolute(PRNG_STATE_LO)));
    out.push(Instruction::implied(RTS));

    // ── __rand16 ─────────────────────────────────────────────
    // A single shift already produces 16 fresh bits (the full
    // post-shift state). Call `__rand8` once and return both
    // halves — A = lo, X = hi.
    out.push(Instruction::new(NOP, AM::Label("__rand16".into())));
    out.push(Instruction::new(JSR, AM::Label("__rand8".into())));
    out.push(Instruction::new(LDX, AM::Absolute(PRNG_STATE_HI)));
    out.push(Instruction::implied(RTS));

    // ── __rand_seed ──────────────────────────────────────────
    // Store A = lo, X = hi into the state. Force bit 0 of the
    // low byte high so a zero seed doesn't stick the LFSR.
    out.push(Instruction::new(NOP, AM::Label("__rand_seed".into())));
    out.push(Instruction::new(ORA, AM::Immediate(0x01)));
    out.push(Instruction::new(STA, AM::Absolute(PRNG_STATE_LO)));
    out.push(Instruction::new(STX, AM::Absolute(PRNG_STATE_HI)));
    out.push(Instruction::implied(RTS));

    out
}

/// Generate the `__set_palette_brightness` runtime routine.
/// Spliced in by the linker only when user code contains the
/// `__palette_bright_used` marker label.
///
/// Each level (passed in A, clamped to 0..=8) writes a specific
/// `$2001` PPU mask byte. The mapping is best thought of as a
/// "visual intensity dial" rather than a linear fade: the NES PPU
/// emphasis bits tint the display towards R / G / B rather than
/// truly darken or brighten, so the progression is a series of
/// distinct visual states. Levels 0 and 1 use low-level tricks
/// (rendering off, greyscale) to approximate black and dim; levels
/// 2-8 stack emphasis bits to shift the overall colour cast.
///
/// | level | mask | effect                           |
/// |-------|------|----------------------------------|
/// | 0     | $00  | rendering fully off (black)      |
/// | 1     | $01  | greyscale only (washed out)      |
/// | 2     | $1E  | normal sprites + background      |
/// | 3     | $3E  | + red emphasis                   |
/// | 4     | $5E  | + green emphasis                 |
/// | 5     | $9E  | + blue emphasis                  |
/// | 6     | $7E  | + red + green (yellow tint)      |
/// | 7     | $BE  | + red + blue (magenta tint)      |
/// | 8     | $FE  | all three emphasis bits          |
///
/// Levels above 8 clamp to 8. Implemented as a CPX dispatch tree
/// (one `CPX; BNE; LDA; STA; RTS` block per level) rather than a
/// table lookup because the assembler doesn't expose a
/// Label-relative `AbsoluteX` mode; the nine-entry tree is ~60
/// bytes, comparable to a data-table + indexed-load path.
#[must_use]
pub fn gen_palette_brightness() -> Vec<Instruction> {
    let mut out = Vec::new();
    out.push(Instruction::new(
        NOP,
        AM::Label("__set_palette_brightness".into()),
    ));
    // Clamp level (in A) to 8. If A >= 9, force A = 8.
    out.push(Instruction::new(CMP, AM::Immediate(9)));
    out.push(Instruction::new(
        BCC,
        AM::LabelRelative("__bright_clamped".into()),
    ));
    out.push(Instruction::new(LDA, AM::Immediate(8)));
    out.push(Instruction::new(NOP, AM::Label("__bright_clamped".into())));
    // Dispatch by level through a compare-and-set tree. Each level
    // maps to a specific `$2001` mask byte:
    //   0: $00 — all rendering off (blank)
    //   1: $01 — greyscale flag (dim-looking)
    //   2: $1E — normal sprites + bg
    //   3: $3E — +red emphasis
    //   4: $5E — +green emphasis
    //   5: $9E — +blue emphasis
    //   6: $7E — +red+green (yellow tint)
    //   7: $BE — +red+blue (magenta tint)
    //   8: $FE — all three emphasis bits (brightest)
    // The table is short enough that the linear CPX tree is
    // comparable in ROM cost to a proper table-indexed load and
    // avoids needing a Label-based AbsoluteX mode in the assembler.
    out.push(Instruction::implied(TAX));
    let entries: [(u8, u8); 9] = [
        (0, 0x00),
        (1, 0x01),
        (2, 0x1E),
        (3, 0x3E),
        (4, 0x5E),
        (5, 0x9E),
        (6, 0x7E),
        (7, 0xBE),
        (8, 0xFE),
    ];
    for (level, mask) in entries {
        out.push(Instruction::new(CPX, AM::Immediate(level)));
        out.push(Instruction::new(
            BNE,
            AM::LabelRelative(format!("__bright_not_{level}")),
        ));
        out.push(Instruction::new(LDA, AM::Immediate(mask)));
        out.push(Instruction::new(STA, AM::Absolute(PPU_MASK)));
        out.push(Instruction::implied(RTS));
        out.push(Instruction::new(
            NOP,
            AM::Label(format!("__bright_not_{level}")),
        ));
    }
    // Fall-through (shouldn't hit): leave PPU_MASK untouched.
    out.push(Instruction::implied(RTS));
    out
}

/// Generate the blocking fade helpers `__fade_out` and `__fade_in`,
/// plus the shared callable `__wait_frame_rt` they use internally.
/// Spliced by the linker whenever user code contains the
/// `__fade_used` marker label (emitted by the IR codegen's
/// `FadeOut` / `FadeIn` ops).
///
/// Both fade entry points take `step_frames` in `A` — the number
/// of frames to hold each brightness level before advancing. A
/// full fade-out runs through levels 4 → 3 → 2 → 1 → 0 (five
/// steps) and a fade-in runs 0 → 1 → 2 → 3 → 4, so the total
/// blocking time is `step_frames × 5` frames.
///
/// Internally the fade JSRs `__set_palette_brightness` for each
/// step and `__wait_frame_rt` between steps. `__set_palette_brightness`
/// is always linked in alongside fade (we can't emit it conditionally
/// without also forcing its marker). `__wait_frame_rt` spins on
/// `ZP_FRAME_FLAG` exactly the way an inline `wait_frame` does.
///
/// Main-RAM scratch bytes the routines use:
///   `FADE_STEP_FRAMES` ($07E8) — saved copy of `step_frames`
///   `FADE_LEVEL`       ($07E9) — current brightness level
///
/// Both slots are free for analyzer allocation in programs that
/// don't use fade (they never trigger the marker).
#[must_use]
pub fn gen_fade() -> Vec<Instruction> {
    let mut out = Vec::new();

    // ── __wait_frame_rt ──────────────────────────────────────
    // Callable wait-for-NMI: spin until `ZP_FRAME_FLAG` is
    // nonzero, then clear it and RTS. Mirrors the inline code
    // the IR codegen emits for `IrOp::WaitFrame`, but callable
    // with a JSR from inside other runtime routines.
    out.push(Instruction::new(NOP, AM::Label("__wait_frame_rt".into())));
    out.push(Instruction::new(
        NOP,
        AM::Label("__wait_frame_rt_loop".into()),
    ));
    out.push(Instruction::new(LDA, AM::ZeroPage(ZP_FRAME_FLAG)));
    out.push(Instruction::new(
        BEQ,
        AM::LabelRelative("__wait_frame_rt_loop".into()),
    ));
    out.push(Instruction::new(LDA, AM::Immediate(0)));
    out.push(Instruction::new(STA, AM::ZeroPage(ZP_FRAME_FLAG)));
    out.push(Instruction::implied(RTS));

    // ── __fade_out ───────────────────────────────────────────
    // A = step_frames on entry. Loops 4 → 3 → 2 → 1 → 0, calling
    // __set_palette_brightness each iteration and waiting
    // step_frames frames between steps.
    //
    // Zero-safety: if the caller passes A=0, the inner wait loop
    // would DEX-underflow from 0 to $FF and burn 256 frames per
    // step (~21 seconds on NTSC). Force a minimum of 1 so the
    // pathological "pass 0" case behaves as "1 frame per step"
    // instead of "hold forever".
    out.push(Instruction::new(NOP, AM::Label("__fade_out".into())));
    out.push(Instruction::new(ORA, AM::Immediate(0x00)));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__fade_out_ok".into()),
    ));
    out.push(Instruction::new(LDA, AM::Immediate(1)));
    out.push(Instruction::new(NOP, AM::Label("__fade_out_ok".into())));
    out.push(Instruction::new(STA, AM::Absolute(FADE_STEP_FRAMES)));
    out.push(Instruction::new(LDA, AM::Immediate(4)));
    out.push(Instruction::new(STA, AM::Absolute(FADE_LEVEL)));
    // Fall through into the shared loop that runs until FADE_LEVEL
    // underflows past 0 (BMI catches the $FF that DEC produces).
    out.push(Instruction::new(NOP, AM::Label("__fade_step".into())));
    out.push(Instruction::new(LDA, AM::Absolute(FADE_LEVEL)));
    out.push(Instruction::new(
        JSR,
        AM::Label("__set_palette_brightness".into()),
    ));
    // Wait step_frames frames.
    out.push(Instruction::new(LDA, AM::Absolute(FADE_STEP_FRAMES)));
    out.push(Instruction::implied(TAX));
    out.push(Instruction::new(NOP, AM::Label("__fade_wait".into())));
    out.push(Instruction::new(JSR, AM::Label("__wait_frame_rt".into())));
    out.push(Instruction::implied(DEX));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__fade_wait".into()),
    ));
    // Decrement the level and loop if it's still a valid level.
    // `__fade_out` is at entry point A; `__fade_in` jumps into a
    // sibling block below that decrements upward. Here, decrement
    // and bail out when we hit $FF (underflow past 0).
    out.push(Instruction::new(DEC, AM::Absolute(FADE_LEVEL)));
    out.push(Instruction::new(LDA, AM::Absolute(FADE_LEVEL)));
    out.push(Instruction::new(CMP, AM::Immediate(0xFF)));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__fade_step".into()),
    ));
    out.push(Instruction::implied(RTS));

    // ── __fade_in ────────────────────────────────────────────
    // A = step_frames on entry. Loops 0 → 1 → 2 → 3 → 4.
    // Uses its own top-of-loop label and increments rather than
    // decrementing; shares the step-wait body via a small duplicate
    // loop (cheaper than threading direction through the shared
    // body for a one-off five-step loop).
    out.push(Instruction::new(NOP, AM::Label("__fade_in".into())));
    out.push(Instruction::new(ORA, AM::Immediate(0x00)));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__fade_in_ok".into()),
    ));
    out.push(Instruction::new(LDA, AM::Immediate(1)));
    out.push(Instruction::new(NOP, AM::Label("__fade_in_ok".into())));
    out.push(Instruction::new(STA, AM::Absolute(FADE_STEP_FRAMES)));
    out.push(Instruction::new(LDA, AM::Immediate(0)));
    out.push(Instruction::new(STA, AM::Absolute(FADE_LEVEL)));
    out.push(Instruction::new(NOP, AM::Label("__fade_in_step".into())));
    out.push(Instruction::new(LDA, AM::Absolute(FADE_LEVEL)));
    out.push(Instruction::new(
        JSR,
        AM::Label("__set_palette_brightness".into()),
    ));
    out.push(Instruction::new(LDA, AM::Absolute(FADE_STEP_FRAMES)));
    out.push(Instruction::implied(TAX));
    out.push(Instruction::new(NOP, AM::Label("__fade_in_wait".into())));
    out.push(Instruction::new(JSR, AM::Label("__wait_frame_rt".into())));
    out.push(Instruction::implied(DEX));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__fade_in_wait".into()),
    ));
    out.push(Instruction::new(INC, AM::Absolute(FADE_LEVEL)));
    out.push(Instruction::new(LDA, AM::Absolute(FADE_LEVEL)));
    out.push(Instruction::new(CMP, AM::Immediate(5)));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__fade_in_step".into()),
    ));
    out.push(Instruction::implied(RTS));

    out
}

/// Generate the `__vram_buf_drain` runtime routine and the matching
/// reset-time clear. The drain is JSR'd from the NMI handler when
/// the `__vram_buf_used` marker is present.
///
/// On entry the buffer at `VRAM_BUF_BASE` (`$0400`) holds zero or
/// more entries followed by a zero-byte sentinel. Each entry is
/// `[len][addr_hi][addr_lo][byte_0]...[byte_(len-1)]`; the drain
/// walks them in order, programming `$2006` with the PPU address
/// then writing each data byte to `$2007`. When it hits a zero
/// `len` byte it resets `VRAM_BUF_HEAD` to zero (so the next
/// frame starts appending at the front of the buffer) and stores
/// `0` back at `VRAM_BUF_BASE` so an empty buffer continues to
/// drain cleanly without a re-init.
///
/// Cycle budget: one entry costs ~12 setup cycles + 8 cycles per
/// data byte. The 256-byte buffer can hold ~50 single-tile writes
/// (each 4 bytes: `len=1`, `addr_hi`, `addr_lo`, `byte`) which
/// drains in roughly 1000 cycles, well inside vblank's
/// ~2273-cycle budget.
///
/// Uses register `X` as the current buffer offset. Caller
/// (the NMI handler) is responsible for save/restore.
#[must_use]
pub fn gen_vram_buf_drain() -> Vec<Instruction> {
    let mut out = Vec::new();
    out.push(Instruction::new(NOP, AM::Label("__vram_buf_drain".into())));
    // X = current offset into VRAM_BUF_BASE.
    out.push(Instruction::new(LDX, AM::Immediate(0)));
    // Top of per-entry loop. A zero `len` byte is the sentinel.
    out.push(Instruction::new(NOP, AM::Label("__vram_buf_loop".into())));
    out.push(Instruction::new(LDA, AM::AbsoluteX(VRAM_BUF_BASE)));
    out.push(Instruction::new(
        BEQ,
        AM::LabelRelative("__vram_buf_done".into()),
    ));
    // A holds `len`. Stash it in Y for the inner data-copy loop.
    out.push(Instruction::implied(TAY));
    // PPU address: write addr_hi then addr_lo to $2006. The
    // entry layout is [len][addr_hi][addr_lo], so addr_hi is at
    // offset+1 and addr_lo at offset+2.
    out.push(Instruction::implied(INX));
    out.push(Instruction::new(LDA, AM::AbsoluteX(VRAM_BUF_BASE)));
    out.push(Instruction::new(STA, AM::Absolute(0x2006)));
    out.push(Instruction::implied(INX));
    out.push(Instruction::new(LDA, AM::AbsoluteX(VRAM_BUF_BASE)));
    out.push(Instruction::new(STA, AM::Absolute(0x2006)));
    // Inner loop: write `Y` data bytes from offset+3 onward to
    // $2007. The PPU's auto-increment (set in $2000 bit 2 — we
    // leave it at 1, the default) advances the VRAM pointer one
    // cell per write.
    out.push(Instruction::new(NOP, AM::Label("__vram_buf_data".into())));
    out.push(Instruction::implied(INX));
    out.push(Instruction::new(LDA, AM::AbsoluteX(VRAM_BUF_BASE)));
    out.push(Instruction::new(STA, AM::Absolute(0x2007)));
    out.push(Instruction::implied(DEY));
    out.push(Instruction::new(
        BNE,
        AM::LabelRelative("__vram_buf_data".into()),
    ));
    // Move past the last data byte's offset before looping.
    out.push(Instruction::implied(INX));
    out.push(Instruction::new(JMP, AM::Label("__vram_buf_loop".into())));
    out.push(Instruction::new(NOP, AM::Label("__vram_buf_done".into())));
    // Reset the head pointer so the next frame starts appending
    // at offset 0. We don't need to clobber the rest of the
    // buffer — the writer always lays down a fresh sentinel
    // after each append.
    out.push(Instruction::new(LDA, AM::Immediate(0)));
    out.push(Instruction::new(STA, AM::Absolute(VRAM_BUF_HEAD)));
    out.push(Instruction::new(STA, AM::Absolute(VRAM_BUF_BASE)));
    // Reset the PPU's internal scroll/address state. Each `$2006`
    // write during the drain updated the PPU's `t` register
    // (which holds the next scroll value); leaving it pointing
    // at our last buffer entry's address would cause the next
    // frame's rendering to start from a non-zero offset and the
    // visible image would shift up/right by however many cells
    // we wrote past `$2000`. The standard fix is to write `0` to
    // `$2006` twice (resetting `t` to nametable 0 / cell 0) and
    // then `0` to `$2005` twice (zero X / Y scroll). Two `$2006`
    // writes also reset the `$2006`/`$2005` write-toggle latch
    // to "high" so the next frame's drain sees a clean state.
    out.push(Instruction::new(LDA, AM::Immediate(0)));
    out.push(Instruction::new(STA, AM::Absolute(0x2006)));
    out.push(Instruction::new(STA, AM::Absolute(0x2006)));
    out.push(Instruction::new(STA, AM::Absolute(0x2005)));
    out.push(Instruction::new(STA, AM::Absolute(0x2005)));
    out.push(Instruction::implied(RTS));
    out
}

/// Emit the `__collides_at` runtime helper: a small subroutine
/// that answers "does the pixel at `(x, y)` fall inside a solid
/// metatile of the currently-painted room?". Spliced in whenever
/// the codegen emits the `__collides_at_used` marker.
///
/// **Contract**
/// - Input: `A = x` (screen pixel 0..255), `X = y` (screen pixel
///   0..239). `(x >> 4, y >> 4)` addresses the 16×15 metatile
///   grid; rooms span pixels `(0..255, 0..239)` exactly.
/// - Output: `A = 1` if the covering metatile is marked
///   `collide: true`, `A = 0` otherwise. Flags reflect the final
///   LDA so callers can BEQ / BNE directly.
/// - Clobbers: `A, X, Y`. Uses ZP `$04-$05` as a scratch pointer
///   (the same byte pair runtime helpers like `gen_audio_tick`
///   reuse as a temporary workspace), plus the room-pointer ZP
///   slots populated by `paint_room` at `$18-$19`.
/// - Out-of-range inputs (`y >= 240`) clamp to the last row
///   because the division only keeps bits 4-7, giving row 14.
///   Users can avoid the edge case by gating the query on their
///   own screen bounds.
///
/// **Lookup**
/// - Row = `y >> 4` (0..14, so fits in a single LSR-by-4).
/// - Col = `x >> 4` (0..15).
/// - Index = row * 16 + col = `(y & 0xF0) | (x >> 4)`. The `* 16`
///   is exactly what `y >> 4 << 4` = `y & 0xF0` computes, so no
///   multiply needed — that's why we laid out the bitmap at 16
///   columns wide in the first place.
/// - Load byte at `room_col_ptr + index`. The byte is 0 (no
///   collide) or 1 (collide); we hand it back unchanged.
pub fn gen_collides_at() -> Vec<Instruction> {
    let mut out = Vec::new();
    out.push(Instruction::new(NOP, AM::Label("__collides_at".into())));
    // Save x on the stack — we need A for the y-based offset.
    out.push(Instruction::implied(PHA));
    // Compute `y & 0xF0`. Y is already in X from the caller's
    // contract; transfer to A so we can mask it.
    out.push(Instruction::implied(TXA));
    out.push(Instruction::new(AND, AM::Immediate(0xF0)));
    // Stash the masked y (= row * 16) in Y.
    out.push(Instruction::implied(TAY));
    // Pull x back, shift right 4 to get the column (0..15).
    out.push(Instruction::implied(PLA));
    out.push(Instruction::new(LSR, AM::Accumulator));
    out.push(Instruction::new(LSR, AM::Accumulator));
    out.push(Instruction::new(LSR, AM::Accumulator));
    out.push(Instruction::new(LSR, AM::Accumulator));
    // Combine col (A) with row*16 (Y), producing the linear
    // metatile index in A.
    out.push(Instruction::new(STA, AM::ZeroPage(0x04)));
    out.push(Instruction::implied(TYA));
    out.push(Instruction::new(ORA, AM::ZeroPage(0x04)));
    // Use Y as the index into the room-pointer-relative bitmap.
    out.push(Instruction::implied(TAY));
    // Read `(ZP_ROOM_COL_LO),Y` — 0 or 1. The LDA sets Z and N;
    // the caller's BNE / BEQ / STA picks up whichever it needs.
    out.push(Instruction::new(LDA, AM::IndirectY(ZP_ROOM_COL_LO)));
    out.push(Instruction::implied(RTS));
    out
}

/// Emit the reset-time PRNG state seed. Spliced into the reset
/// path whenever `gen_prng` is linked in, so the first `rand8()`
/// call returns a useful value even without an explicit
/// `seed_rand`. The seed `0xACE1` is an arbitrary non-zero 16-bit
/// value — any non-zero value works since the Galois LFSR's orbit
/// visits all 65535 non-zero states.
#[must_use]
pub fn gen_prng_init() -> Vec<Instruction> {
    vec![
        Instruction::new(LDA, AM::Immediate(0xE1)),
        Instruction::new(STA, AM::Absolute(PRNG_STATE_LO)),
        Instruction::new(LDA, AM::Immediate(0xAC)),
        Instruction::new(STA, AM::Absolute(PRNG_STATE_HI)),
    ]
}

// ─── Bank switching ────────────────────────────────────────────────
//
// NEScript supports bank switching for MMC1, UxROM, and MMC3. The
// linker lays out PRG ROM with a single fixed bank ($C000-$FFFF)
// holding the runtime, NMI, IRQ vectors, and any cross-bank
// trampolines, plus zero or more switchable 16 KB banks mapped at
// $8000-$BFFF. The helpers below emit:
//
//   * `gen_mapper_init` — reset-time configuration that puts the
//     last physical bank at $C000 and (depending on the mapper)
//     sets a known mirroring mode so the compiler's
//     `Mirroring::{Horizontal,Vertical}` selection matches.
//   * `gen_bank_select` — a subroutine callable with the target bank
//     number in A that selects the correct switchable bank at $8000.
//   * `gen_bank_trampoline` — a per-(target, bank) stub placed in
//     the fixed bank. Callers `JSR` into the trampoline, which
//     records the current bank, switches to the target bank, calls
//     the entry label in that bank, and switches back.
//
// The trampolines never physically return to the switchable bank —
// control is always handed back to the fixed bank after the callee
// returns. Users don't touch these routines directly; the linker
// emits them from the `bank` declarations in the program AST.

/// Zero-page slot used by the bank-select routine to stash the
/// requested bank number so `__bank_return` can restore it when a
/// trampoline finishes.
pub const ZP_BANK_CURRENT: u8 = 0x10;

/// Generate the reset-time mapper initialization sequence. Splices
/// after `gen_init` but before any user code runs. For NROM this is
/// a no-op — `gen_init` already sets up everything NROM needs.
///
/// `total_prg_banks` is the total number of 16 KB PRG banks in the
/// ROM; MMC1/MMC3 need this to fix the *last* physical bank at
/// $C000. `UxROM` is hardwired — its last bank is always fixed.
#[must_use]
pub fn gen_mapper_init(
    mapper: Mapper,
    mirroring: Mirroring,
    total_prg_banks: usize,
) -> Vec<Instruction> {
    let mut out = match mapper {
        Mapper::NROM => Vec::new(),
        Mapper::MMC1 => gen_mmc1_init(mirroring),
        Mapper::UxROM => gen_uxrom_init(total_prg_banks),
        Mapper::MMC3 => gen_mmc3_init(mirroring),
        Mapper::AxROM => gen_axrom_init(mirroring),
        Mapper::CNROM => gen_cnrom_init(),
        Mapper::GNROM => gen_gnrom_init(),
    };
    // Initialize ZP_BANK_CURRENT to the fixed bank index for any
    // banked mapper. CNROM and AxROM don't use per-function bank
    // trampolines the same way MMC1/UxROM/MMC3 do — CNROM has a
    // fixed 32 KB PRG, and AxROM swaps 32 KB pages as one unit —
    // so they skip the `ZP_BANK_CURRENT` seed.
    if matches!(mapper, Mapper::MMC1 | Mapper::UxROM | Mapper::MMC3) && total_prg_banks > 0 {
        #[allow(clippy::cast_possible_truncation)]
        let fixed_bank_index = (total_prg_banks - 1) as u8;
        out.push(Instruction::new(LDA, AM::Immediate(fixed_bank_index)));
        out.push(Instruction::new(STA, AM::ZeroPage(ZP_BANK_CURRENT)));
    }
    out
}

/// `AxROM` (mapper 7) reset. The `AxROM` register is a single latch
/// at `$8000-$FFFF`:
///   bits 0-2 select the 32 KB PRG bank mapped at `$8000-$FFFF`
///   bit 4    selects single-screen nametable (0 = lower, 1 = upper)
///
/// We write `0` at reset so the ROM starts executing from bank 0
/// with the lower nametable active. Some `AxROM` boards (Battletoads,
/// Wizards & Warriors) are bus-conflict-prone so the write has to
/// hit a ROM byte that matches; the simplest safe approach is to
/// put a `0x00` byte at a known ROM address and STA there. For
/// `NEScript`'s usage pattern (single PRG bank → mapper 0-equivalent
/// layout) this is good enough for the demo to boot.
fn gen_axrom_init(mirroring: Mirroring) -> Vec<Instruction> {
    let mut out = Vec::new();
    out.push(Instruction::new(NOP, AM::Label("__axrom_init".into())));
    // Start with the lower or upper single-screen nametable active.
    // `Mirroring::Horizontal` → lower-screen (bit 4 = 0); `Vertical`
    // → upper-screen (bit 4 = 1). This keeps the existing mirroring
    // enum useful even though AxROM has no true horizontal/vertical
    // modes.
    let init_reg: u8 = match mirroring {
        Mirroring::Horizontal => 0x00,
        Mirroring::Vertical => 0x10,
    };
    out.push(Instruction::new(LDA, AM::Immediate(init_reg)));
    out.push(Instruction::new(STA, AM::Absolute(0x8000)));
    out
}

/// CNROM (mapper 3) reset. Fixed 32 KB PRG, 8 KB CHR bankswitching
/// via one write to `$8000-$FFFF`. At power-on the CHR bank is
/// undefined on some boards, so we explicitly write bank 0.
fn gen_cnrom_init() -> Vec<Instruction> {
    let mut out = Vec::new();
    out.push(Instruction::new(NOP, AM::Label("__cnrom_init".into())));
    out.push(Instruction::new(LDA, AM::Immediate(0x00)));
    out.push(Instruction::new(STA, AM::Absolute(0x8000)));
    out
}

/// `GNROM` (mapper 66) reset. Single register at `$8000-$FFFF`:
///   bits 4-5: select 32 KB PRG page at `$8000-$FFFF`
///   bits 0-1: select 8 KB CHR bank
/// At power-on both fields are nominally zero but some boards
/// leave them undefined, so we explicitly write `$00` — PRG page 0
/// with CHR bank 0.
fn gen_gnrom_init() -> Vec<Instruction> {
    let mut out = Vec::new();
    out.push(Instruction::new(NOP, AM::Label("__gnrom_init".into())));
    out.push(Instruction::new(LDA, AM::Immediate(0x00)));
    out.push(Instruction::new(STA, AM::Absolute(0x8000)));
    out
}

/// MMC1 reset: pulse the reset bit, then write the control register.
/// Control-register layout (5 bits, serialized LSB-first into any
/// $8000-$FFFF address):
///   bit 4   — CHR bank mode (0 = 8 KB, 1 = two 4 KB banks)
///   bit 3   — PRG bank mode bit 1
///   bit 2   — PRG bank mode bit 0
///             11 = 16 KB banks, fix last at $C000, switchable at $8000
///   bit 1-0 — mirroring
///             00 = 1-screen lo, 01 = 1-screen hi,
///             10 = vertical,    11 = horizontal
///
/// We pick mode `11` (fixed last bank) so the fixed bank appears at
/// $C000 exactly the same way as NROM, which lets us reuse the NROM
/// layout for all the runtime code that already exists.
fn gen_mmc1_init(mirroring: Mirroring) -> Vec<Instruction> {
    let mut out = Vec::new();
    out.push(Instruction::new(NOP, AM::Label("__mmc1_init".into())));
    // Reset pulse: any $8000-range write with bit 7 set flushes the
    // 5-bit shift register and resets the internal config to
    // mode 3 (fixed last, 16 KB banks).
    out.push(Instruction::new(LDA, AM::Immediate(0x80)));
    out.push(Instruction::new(STA, AM::Absolute(0x8000)));
    // Control register value.
    let mirror_bits = match mirroring {
        Mirroring::Horizontal => 0b11,
        Mirroring::Vertical => 0b10,
    };
    // 16 KB PRG, fix last at $C000 (bits 2-3 = 11), 8 KB CHR
    // (bit 4 = 0), plus mirroring bits.
    let control: u8 = 0b0_11_00 | mirror_bits;
    // Serialize the 5 bits into the shift register. Each write
    // uses STA $8000 (which maps to the control register because
    // the address falls in the $8000-$9FFF range).
    out.extend(gen_mmc1_serial_write(control, 0x8000));
    out
}

/// Emit 5 serialized writes of `value` to `addr`, shifting right
/// between writes. Used by MMC1 bank-switch code (registers all live
/// in $8000-$FFFF and are selected by the top two address bits).
fn gen_mmc1_serial_write(value: u8, addr: u16) -> Vec<Instruction> {
    let mut out = Vec::new();
    // Bit 0 goes out first, then bit 1, etc. We use immediate loads
    // for each bit so the sequence has no hidden dependencies on
    // the current A register.
    for i in 0..5 {
        let bit = (value >> i) & 1;
        out.push(Instruction::new(LDA, AM::Immediate(bit)));
        out.push(Instruction::new(STA, AM::Absolute(addr)));
    }
    out
}

/// `UxROM` reset: the last 16 KB PRG bank is always fixed at $C000,
/// and the switchable bank at $8000 defaults to bank 0 on power-on.
/// Some `UxROM` boards have bus conflicts — any write must match the
/// byte in ROM — so we use a small bank-select table at a known
/// address (`__bank_select_table`) generated into the fixed bank.
fn gen_uxrom_init(_total_banks: usize) -> Vec<Instruction> {
    // No explicit init required: UxROM powers up with bank 0 at
    // $8000 and the last bank fixed at $C000, which is exactly
    // what we want. We still emit the label so debuggers can find
    // the (empty) init span.
    vec![Instruction::new(NOP, AM::Label("__uxrom_init".into()))]
}

/// MMC3 reset: choose PRG mode 0 (last two banks fixed at
/// $C000-$FFFF) and initialise bank 0 at $8000, bank 1 at $A000.
/// Mirroring is programmed via $A000 (only meaningful when CHR
/// uses the internal mode — for our CHR ROM layout it's still
/// the safest place to latch).
fn gen_mmc3_init(mirroring: Mirroring) -> Vec<Instruction> {
    let mut out = Vec::new();
    out.push(Instruction::new(NOP, AM::Label("__mmc3_init".into())));

    // Select PRG-bank-0 register (6) with PRG mode bit 6 = 0
    // (meaning $8000 is switchable, $C000/$E000 are fixed at the
    // last two banks).
    out.push(Instruction::new(LDA, AM::Immediate(0x06)));
    out.push(Instruction::new(STA, AM::Absolute(0x8000)));
    out.push(Instruction::new(LDA, AM::Immediate(0x00))); // bank 0 at $8000
    out.push(Instruction::new(STA, AM::Absolute(0x8001)));

    // Select PRG-bank-1 register (7) and load bank 1 at $A000.
    out.push(Instruction::new(LDA, AM::Immediate(0x07)));
    out.push(Instruction::new(STA, AM::Absolute(0x8000)));
    out.push(Instruction::new(LDA, AM::Immediate(0x01)));
    out.push(Instruction::new(STA, AM::Absolute(0x8001)));

    // Mirroring: $A000, bit 0 — 0 = vertical, 1 = horizontal.
    let mirror = match mirroring {
        Mirroring::Horizontal => 0x01,
        Mirroring::Vertical => 0x00,
    };
    out.push(Instruction::new(LDA, AM::Immediate(mirror)));
    out.push(Instruction::new(STA, AM::Absolute(0xA000)));

    // Leave IRQs disabled until the user code enables them.
    out.push(Instruction::new(STA, AM::Absolute(0xE000)));

    out
}

/// Generate the `__bank_select` subroutine. Input: A = desired bank
/// number (0-based, physical PRG bank index). Output: that bank is
/// mapped to $8000-$BFFF. Clobbers A (and the internal shift
/// registers where applicable). The routine ends in RTS so callers
/// can `JSR __bank_select` anywhere it's callable from.
///
/// The bank number is stashed in `ZP_BANK_CURRENT` so `__bank_select`
/// and its trampolines can restore it after a callee returns.
#[must_use]
pub fn gen_bank_select(mapper: Mapper) -> Vec<Instruction> {
    let mut out = Vec::new();
    out.push(Instruction::new(NOP, AM::Label("__bank_select".into())));
    out.push(Instruction::new(STA, AM::ZeroPage(ZP_BANK_CURRENT)));
    match mapper {
        Mapper::NROM => {
            // NROM has no switchable banks, so the routine is a
            // no-op. We still emit it so user code can unconditionally
            // call `__bank_select` regardless of mapper.
            out.push(Instruction::implied(RTS));
        }
        Mapper::MMC1 => {
            // Write 5 bits of A (LSB first) into the shift register
            // at $E000 (PRG-bank select). Between writes we LSR A
            // to shift the next bit into position 0.
            for i in 0..5 {
                if i > 0 {
                    out.push(Instruction::new(LSR, AM::Accumulator));
                }
                out.push(Instruction::new(STA, AM::Absolute(0xE000)));
            }
            out.push(Instruction::implied(RTS));
        }
        Mapper::UxROM => {
            // UxROM: write the bank number to any address in
            // $8000-$FFFF. On boards with bus conflicts the CPU's
            // write and the ROM byte at that address are ANDed on
            // the data bus, so we must write to an address whose
            // ROM byte already equals the bank number. The linker
            // splices a 256-byte table (`__bank_select_table`,
            // bytes 0..255) into the fixed bank, and we index into
            // it with X = bank number: `STA __bank_select_table, X`
            // stores A (= bank number) at
            // `__bank_select_table + X`, whose ROM byte is exactly
            // X, so bus = A = X = ROM — no conflict.
            //
            // Previously this wrote to a fixed `$FFF0`, which
            // happens to work on emulators that don't simulate bus
            // conflicts (jsnes, Mesen permissive) but would glitch
            // on real hardware because a single ROM byte can't
            // match every possible bank number.
            out.push(Instruction::implied(TAX));
            out.push(Instruction::new(
                STA,
                AM::LabelAbsoluteX("__bank_select_table".into()),
            ));
            out.push(Instruction::implied(RTS));
        }
        Mapper::MMC3 => {
            // MMC3: `$8000 = 6` selects PRG-bank-0 register, then
            // write bank to `$8001`. We save/restore X because
            // some callers use X as a loop counter across the
            // switch.
            out.push(Instruction::implied(PHA));
            out.push(Instruction::new(LDA, AM::Immediate(0x06)));
            out.push(Instruction::new(STA, AM::Absolute(0x8000)));
            out.push(Instruction::implied(PLA));
            out.push(Instruction::new(STA, AM::Absolute(0x8001)));
            out.push(Instruction::implied(RTS));
        }
        Mapper::AxROM => {
            // AxROM: write the 32 KB PRG bank number to $8000-$FFFF.
            // Bit 4 selects the single-screen nametable; bits 0-2
            // select the PRG page. We don't preserve bit 4 here —
            // user code that toggles between lower/upper nametables
            // mid-run would need to OR it into A before calling.
            // The linker's single-bank AxROM layout never actually
            // invokes this routine today (no cross-bank trampolines
            // for AxROM yet), but we emit it for parity with the
            // other mappers.
            out.push(Instruction::new(STA, AM::Absolute(0x8000)));
            out.push(Instruction::implied(RTS));
        }
        Mapper::CNROM => {
            // CNROM: writing A to `$8000-$FFFF` selects an 8 KB CHR
            // bank. PRG is fixed so this routine is only ever useful
            // for user-driven CHR swaps. Note: real CNROM boards
            // have bus conflicts (CPU write vs ROM byte at target
            // address), so a production API should route through a
            // UxROM-style bus-conflict-safe table. No such API is
            // exposed to user source yet — declaring more than one
            // CHR bank in a CNROM program is currently a TODO.
            out.push(Instruction::new(STA, AM::Absolute(0x8000)));
            out.push(Instruction::implied(RTS));
        }
        Mapper::GNROM => {
            // GNROM: one register at `$8000-$FFFF` packs both a
            // 32 KB PRG page (bits 4-5) and an 8 KB CHR bank
            // (bits 0-1). The input A is the packed byte; user
            // code is responsible for composing it. Like CNROM
            // and AxROM, real boards have bus conflicts and a
            // production API should use a bus-conflict-safe
            // table.
            out.push(Instruction::new(STA, AM::Absolute(0x8000)));
            out.push(Instruction::implied(RTS));
        }
    }
    out
}

/// Generate a cross-bank trampoline stub. Placed in the fixed bank
/// and called by *any* user code via `JSR <tramp_label>` regardless
/// of which bank the caller currently lives in. Behavior:
///
///   1. Read [`ZP_BANK_CURRENT`] into A, push it on the hardware
///      stack — that's the bank we'll need to switch back to.
///   2. Load the target bank number into A, JSR `__bank_select`.
///   3. JSR the user-supplied entry label inside the target bank.
///   4. Pull the saved bank back into A and JSR `__bank_select` to
///      restore the caller's view of $8000-$BFFF.
///   5. RTS.
///
/// The save/restore via `ZP_BANK_CURRENT + PHA/PLA` makes the same
/// trampoline work for **fixed-bank → switchable-bank** *and*
/// **switchable-bank → switchable-bank** call directions: the
/// caller's bank ends up restored regardless of where the call
/// originated. Nested cross-bank calls compose because each
/// trampoline's PHA/PLA pair is balanced against its own JSR/RTS,
/// so the saved bank values stack like any other 6502 frame.
///
/// The trampoline body itself lives in the fixed bank, which is
/// always mapped at `$C000-$FFFF`, so it's reachable from every
/// switchable bank without further mapper trickery.
///
/// `tramp_label` is the label that callers will JSR (the IR codegen
/// emits `JSR __tramp_<fn_name>` at every cross-bank call site).
/// `entry_label` is the label inside the target bank that holds the
/// callee's first instruction — conventionally `__ir_fn_<fn_name>`,
/// the same label IR codegen would have emitted for an in-bank call.
/// `bank_index` is the physical PRG bank number of the target bank.
#[must_use]
pub fn gen_bank_trampoline(
    tramp_label: &str,
    entry_label: &str,
    bank_index: u8,
) -> Vec<Instruction> {
    let mut out = Vec::new();
    out.push(Instruction::new(NOP, AM::Label(tramp_label.to_string())));
    // Save the caller's current bank. `__bank_select` writes its
    // input into ZP_BANK_CURRENT, so this slot already mirrors the
    // last-selected bank (initialized to the fixed bank index by
    // `gen_mapper_init` so even fixed-bank callers see a sane
    // value the first time around).
    out.push(Instruction::new(LDA, AM::ZeroPage(ZP_BANK_CURRENT)));
    out.push(Instruction::implied(PHA));
    // Switch to target bank.
    out.push(Instruction::new(LDA, AM::Immediate(bank_index)));
    out.push(Instruction::new(JSR, AM::Label("__bank_select".into())));
    // Call the user's entry point in that bank. The label lives in
    // the switchable bank and is resolved by the linker after the
    // banked code is assembled.
    out.push(Instruction::new(JSR, AM::Label(entry_label.to_string())));
    // Restore the caller's bank (pulled from the stack) so control
    // returns with $8000-$BFFF showing whatever the caller had
    // mapped before the trampoline ran.
    out.push(Instruction::implied(PLA));
    out.push(Instruction::new(JSR, AM::Label("__bank_select".into())));
    out.push(Instruction::implied(RTS));
    out
}

/// Generate the bus-conflict avoidance table used by `UxROM`. The table
/// lives at a known offset in the fixed bank and contains 256 bytes
/// of increasing values (0, 1, 2, ...). Writing bank `n` to
/// `__bank_select_table + n` guarantees the bus value matches the
/// ROM byte at that address, avoiding conflict-driven glitches on
/// real `UxROM` hardware.
#[must_use]
pub fn gen_uxrom_bank_table() -> Vec<Instruction> {
    let bytes: Vec<u8> = (0..=255u16).map(|i| i as u8).collect();
    vec![
        Instruction::new(NOP, AM::Label("__bank_select_table".into())),
        Instruction::new(NOP, AM::Bytes(bytes)),
    ]
}
