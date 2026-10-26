mod lowering;
#[cfg(test)]
mod tests;

pub use lowering::{can_inline_fun, lower, RAW_ASM_PREFIX};

use crate::lexer::Span;
use std::fmt;

/// A unique identifier for a variable across the program.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId(pub u32);

/// A virtual register — unlimited supply, resolved during codegen.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IrTemp(pub u32);

/// Signedness of an arithmetic / comparison operand. The IR is
/// otherwise untyped — temps carry no width or sign information by
/// themselves — so ordering compares (`Lt`, `Gt`, `LtEq`, `GtEq`) and
/// any future sign-aware op carry this enum to tell the codegen which
/// branch lowering to emit. `Eq` / `Ne` and bitwise ops don't need it
/// because their bytewise result is the same either way.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Signedness {
    Unsigned,
    Signed,
}

impl fmt::Display for IrTemp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.0)
    }
}

impl fmt::Display for VarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

/// The top-level IR program.
#[derive(Debug, Clone)]
pub struct IrProgram {
    pub functions: Vec<IrFunction>,
    pub globals: Vec<IrGlobal>,
    pub rom_data: Vec<IrRomBlock>,
    /// Ordered list of state names (index = state dispatch number).
    pub states: Vec<String>,
    /// Name of the initial state when the ROM boots.
    pub start_state: String,
    /// Name → `VarId` for every variable the lowerer synthesized,
    /// including flattened struct fields (`"pos.x"`), function-scoped
    /// locals, and state-local variables. The codegen joins this with
    /// the analyzer's `var_allocations` list to populate `var_addrs`
    /// for every allocated byte — without it, assignments to
    /// synthesized field names (e.g. `pos.x = 100`) silently emit no
    /// code because the field's `VarId` never lands in the address
    /// map. This is the PR #31 state-local bug generalized.
    pub var_map: std::collections::HashMap<String, VarId>,
}

/// A global variable in the IR.
#[derive(Debug, Clone)]
pub struct IrGlobal {
    pub var_id: VarId,
    pub name: String,
    pub size: u16,
    /// Scalar initial value for single-byte globals. `None` means the
    /// RAM-clear at reset leaves this global at 0.
    pub init_value: Option<u16>,
    /// Per-byte initial contents for array-literal globals
    /// (e.g. `var xs: u8[4] = [1,2,3,4]`). Empty for scalars or
    /// uninitialized arrays. Each entry is the initial byte at offset
    /// `i` from the global's base address; trailing bytes not covered
    /// by the literal stay zero-filled by the hardware init's RAM
    /// clear. Mutually exclusive with a meaningful `init_value` in
    /// practice: `lower_program` takes one path for scalars and
    /// another for array literals.
    pub init_array: Vec<u8>,
}

/// A block of constant data to be placed in ROM.
#[derive(Debug, Clone)]
pub struct IrRomBlock {
    pub label: String,
    pub data: Vec<u8>,
}

/// An IR function (includes state handlers, user functions, etc.)
#[derive(Debug, Clone)]
pub struct IrFunction {
    pub name: String,
    pub blocks: Vec<IrBasicBlock>,
    pub locals: Vec<IrLocal>,
    pub param_count: usize,
    pub has_return: bool,
    /// When `Some(bank_name)`, this function was declared inside a
    /// `bank Foo { fun ... }` block in the source and its compiled
    /// bytes belong in the named switchable PRG bank instead of the
    /// fixed bank. The codegen separates the per-bank instruction
    /// streams during [`IrCodeGen::generate`] and the linker assembles
    /// each bank into its own 16 KB slot. State handlers and any
    /// top-level functions leave this `None` and live in the fixed
    /// bank alongside the runtime — the only mode prior to user-banked
    /// codegen.
    pub bank: Option<String>,
    pub source_span: Span,
}

/// A local variable within a function.
#[derive(Debug, Clone)]
pub struct IrLocal {
    pub var_id: VarId,
    pub name: String,
    pub size: u16,
}

/// A basic block — a straight-line sequence of ops ending with a terminator.
#[derive(Debug, Clone)]
pub struct IrBasicBlock {
    pub label: String,
    pub ops: Vec<IrOp>,
    pub terminator: IrTerminator,
}

/// An IR operation.
#[derive(Debug, Clone)]
pub enum IrOp {
    // Load/Store
    LoadImm(IrTemp, u8),
    LoadVar(IrTemp, VarId),
    StoreVar(VarId, IrTemp),

    // Arithmetic (8-bit)
    Add(IrTemp, IrTemp, IrTemp),
    Sub(IrTemp, IrTemp, IrTemp),
    Mul(IrTemp, IrTemp, IrTemp),
    And(IrTemp, IrTemp, IrTemp),
    Or(IrTemp, IrTemp, IrTemp),
    Xor(IrTemp, IrTemp, IrTemp),
    /// Shift `src` left by a compile-time-known count. Lowering
    /// extracts the count from constant RHS expressions; non-constant
    /// shifts lower to [`IrOp::ShiftLeftVar`].
    ShiftLeft(IrTemp, IrTemp, u8),
    /// Shift `src` right by a compile-time-known count.
    ShiftRight(IrTemp, IrTemp, u8),
    /// Shift `src` left by a runtime-variable count held in `amt`.
    /// Codegen emits a short loop. Never produced by the lowering
    /// when the RHS constant-folds; the optimizer may also turn this
    /// back into [`IrOp::ShiftLeft`] once `amt` is known.
    ShiftLeftVar(IrTemp, IrTemp, IrTemp),
    /// Shift `src` right by a runtime-variable count held in `amt`.
    ShiftRightVar(IrTemp, IrTemp, IrTemp),
    /// Software 8/8 divide: `dest = a / b`. Lowered to a `__divide`
    /// call in codegen; the strength reducer folds constant divisors
    /// into shifts / AND masks where possible before this runs.
    Div(IrTemp, IrTemp, IrTemp),
    /// Software 8/8 modulo: `dest = a % b`.
    Mod(IrTemp, IrTemp, IrTemp),
    Negate(IrTemp, IrTemp),
    Complement(IrTemp, IrTemp),

    // Comparison (sets a boolean temp)
    CmpEq(IrTemp, IrTemp, IrTemp),
    CmpNe(IrTemp, IrTemp, IrTemp),
    /// `dest = (a < b)`. `signed` selects between unsigned (`BCC`) and
    /// signed (`SBC` + `N XOR V`) branch lowering.
    CmpLt(IrTemp, IrTemp, IrTemp, Signedness),
    /// `dest = (a > b)`.
    CmpGt(IrTemp, IrTemp, IrTemp, Signedness),
    /// `dest = (a <= b)`.
    CmpLtEq(IrTemp, IrTemp, IrTemp, Signedness),
    /// `dest = (a >= b)`.
    CmpGtEq(IrTemp, IrTemp, IrTemp, Signedness),

    /// Sign-extend an 8-bit value into an 8-bit `dest` byte, producing
    /// `$FF` if `src`'s bit 7 is set and `$00` otherwise. Used by the
    /// IR lowering when a signed narrow value (i8) is widened to i16
    /// — the unsigned path emits `LoadImm 0` for the high byte instead.
    SignExtend(IrTemp, IrTemp),

    // Array access
    ArrayLoad(IrTemp, VarId, IrTemp),
    ArrayStore(VarId, IrTemp, IrTemp),

    // Function call
    Call(Option<IrTemp>, String, Vec<IrTemp>),

    // Hardware operations
    DrawSprite {
        sprite_name: String,
        x: IrTemp,
        y: IrTemp,
        frame: Option<IrTemp>,
    },
    /// Read a controller input byte into a temp.
    /// Second arg: 0 for player 1, 1 for player 2.
    ReadInput(IrTemp, u8),
    WaitFrame,
    /// `cycle_sprites` — bump the runtime sprite-cycling offset
    /// byte at `$07EF` by 4, with natural u8 wrap. Paired with
    /// the cycling variant of the NMI handler that reads this
    /// byte into `OAM_ADDR` before the OAM DMA so each frame's DMA
    /// lands in a different slot of the PPU OAM buffer.
    CycleSprites,
    Transition(String),
    /// Write PPU scroll registers (two writes to $2005: X then Y).
    Scroll(IrTemp, IrTemp),
    /// Debug: write a list of temps to the emulator debug port ($4800).
    /// Stripped in release mode by the codegen.
    DebugLog(Vec<IrTemp>),
    /// Debug: runtime assertion — if `cond` is zero, halt with debug marker.
    /// Stripped in release mode by the codegen.
    DebugAssert(IrTemp),
    /// Raw 6502 assembly text; parsed and emitted by the codegen.
    InlineAsm(String),
    /// `poke(addr, value)` — STA value to a fixed absolute address.
    Poke(u16, IrTemp),
    /// `peek(addr)` — LDA from a fixed absolute address into a temp.
    Peek(IrTemp, u16),

    // 16-bit operations — emitted for u16-typed expressions and
    // assignments. Each wide value is carried as a pair of 8-bit
    // temps `(lo, hi)`, so the existing temp-slot allocator still
    // works without modification.
    /// Load the high byte of a u16 variable (var address + 1).
    /// The existing `LoadVar` is repurposed as "load the low byte"
    /// because it loads from the var's base address — which is the
    /// low byte of a little-endian u16.
    LoadVarHi(IrTemp, VarId),
    /// Store the high byte of a u16 variable (var address + 1).
    StoreVarHi(VarId, IrTemp),
    /// 16-bit add: `(d_lo, d_hi) = (a_lo, a_hi) + (b_lo, b_hi)`.
    /// Codegen emits `CLC; LDA a_lo; ADC b_lo; STA d_lo; LDA a_hi;
    /// ADC b_hi; STA d_hi` — the ADC for the high byte propagates
    /// the carry flag set by the low-byte addition.
    Add16 {
        d_lo: IrTemp,
        d_hi: IrTemp,
        a_lo: IrTemp,
        a_hi: IrTemp,
        b_lo: IrTemp,
        b_hi: IrTemp,
    },
    /// 16-bit subtract: `(d_lo, d_hi) = (a_lo, a_hi) - (b_lo, b_hi)`.
    /// Uses SEC; SBC to propagate borrow through the high byte.
    Sub16 {
        d_lo: IrTemp,
        d_hi: IrTemp,
        a_lo: IrTemp,
        a_hi: IrTemp,
        b_lo: IrTemp,
        b_hi: IrTemp,
    },
    /// 16-bit equality comparison; `dest = (a == b) ? 1 : 0`.
    /// Lowered as two CMPs with a short-circuit on the low byte.
    CmpEq16 {
        dest: IrTemp,
        a_lo: IrTemp,
        a_hi: IrTemp,
        b_lo: IrTemp,
        b_hi: IrTemp,
    },
    /// 16-bit not-equal comparison.
    CmpNe16 {
        dest: IrTemp,
        a_lo: IrTemp,
        a_hi: IrTemp,
        b_lo: IrTemp,
        b_hi: IrTemp,
    },
    /// 16-bit less-than. `dest = (a < b) ? 1 : 0`. `signed` selects
    /// between unsigned (high-byte `BCC` + low-byte fall-through) and
    /// signed (`CMP lo / SBC hi` then `N XOR V`) branch lowering.
    CmpLt16 {
        dest: IrTemp,
        a_lo: IrTemp,
        a_hi: IrTemp,
        b_lo: IrTemp,
        b_hi: IrTemp,
        signed: Signedness,
    },
    /// 16-bit greater-than.
    CmpGt16 {
        dest: IrTemp,
        a_lo: IrTemp,
        a_hi: IrTemp,
        b_lo: IrTemp,
        b_hi: IrTemp,
        signed: Signedness,
    },
    /// 16-bit less-or-equal.
    CmpLtEq16 {
        dest: IrTemp,
        a_lo: IrTemp,
        a_hi: IrTemp,
        b_lo: IrTemp,
        b_hi: IrTemp,
        signed: Signedness,
    },
    /// 16-bit greater-or-equal.
    CmpGtEq16 {
        dest: IrTemp,
        a_lo: IrTemp,
        a_hi: IrTemp,
        b_lo: IrTemp,
        b_hi: IrTemp,
        signed: Signedness,
    },

    /// `set_palette Name` — queues a palette update for the next
    /// vblank. Codegen writes the palette's ROM label pointer into
    /// the runtime-reserved ZP slot and sets a pending bit; the NMI
    /// handler applies the write at the next vblank.
    SetPalette(String),
    /// `load_background Name` — queues a nametable update for the
    /// next vblank. Codegen writes both the tiles and attributes
    /// label pointers into their ZP slots and sets a pending bit;
    /// the NMI handler applies the writes at the next vblank.
    LoadBackground(String),
    /// `paint_room Name` — queues the room's compile-time-expanded
    /// nametable for vblank-safe blitting (same machinery as
    /// `LoadBackground`) AND installs the room's collision bitmap
    /// address into `ZP_ROOM_COL_LO` / `ZP_ROOM_COL_HI`. Subsequent
    /// `collides_at(x, y)` queries answer against that bitmap.
    PaintRoom(String),
    /// `collides_at(x, y)` — a boolean query against the currently-
    /// painted room's collision bitmap. Zero-argument use
    /// (`dest = collides_at(x, y)`) reads the pointed-to bitmap
    /// for the metatile covering `(x, y)`; returns 0 (no collision)
    /// or 1 (collision). Codegen lowers to a JSR into a shared
    /// `__collides_at` runtime helper that's spliced in when the
    /// `__collides_at_used` marker is present.
    CollidesAt {
        dest: IrTemp,
        x: IrTemp,
        y: IrTemp,
    },

    // Audio ops — map to the minimal APU driver emitted by the linker.
    /// `play SfxName` — trigger a one-shot sound effect on pulse 1.
    /// The sfx name is looked up in a builtin table; unrecognized names
    /// play a generic beep.
    PlaySfx(String),
    /// `start_music TrackName` — play a sustained tone on pulse 2 until
    /// `stop_music`. The track name is hashed into a tone parameter.
    StartMusic(String),
    /// `stop_music` — silence the music channel (pulse 2) and any
    /// currently-playing SFX tail.
    StopMusic,

    /// `rand8()` — pull the next 8 bits from the runtime PRNG into
    /// `dest`. Codegen emits a `JSR __rand8` and stores A. The
    /// `__rand_used` marker is emitted so the linker splices
    /// `gen_prng` into PRG ROM.
    Rand8(IrTemp),
    /// `rand16()` — pull the next 16 bits from the runtime PRNG into
    /// `(lo, hi)`. Emits `JSR __rand16` (which returns A=lo, X=hi)
    /// and stores both bytes.
    Rand16(IrTemp, IrTemp),
    /// `seed_rand(x)` — install `(lo, hi)` as the new PRNG state.
    /// Codegen loads the bytes into A/X and emits `JSR __rand_seed`.
    SeedRand(IrTemp, IrTemp),

    /// `set_palette_brightness(level)` — write the PPU mask
    /// emphasis / blanking bits that neslib calls `pal_bright`. The
    /// runtime translates levels 0..8 into the appropriate `$2001`
    /// mask byte. Codegen lowers to a JSR to `__set_palette_brightness`
    /// and emits the `__palette_bright_used` marker.
    SetPaletteBrightness(IrTemp),

    /// `fade_out(step_frames)` — block for
    /// `step_frames × 5` frames while walking brightness 4 → 0
    /// via `__set_palette_brightness`. Codegen lowers to a JSR
    /// to `__fade_out` and emits both `__fade_used` and
    /// `__palette_bright_used` markers.
    FadeOut(IrTemp),
    /// `fade_in(step_frames)` — block for
    /// `step_frames × 5` frames while walking brightness 0 → 4.
    FadeIn(IrTemp),

    /// `sprite_0_split(scroll_x, scroll_y)` — busy-wait for the
    /// PPU's sprite-0 hit flag (`$2002` bit 6) and then write
    /// the given scroll values to `$2005`. Used to implement
    /// fixed status-bar / scrolling-playfield splits on any
    /// mapper (unlike `on_scanline(N)`, which requires MMC3).
    Sprite0Split {
        scroll_x: IrTemp,
        scroll_y: IrTemp,
    },

    /// `nt_set(x, y, tile)` — append a single-tile nametable
    /// write to the VRAM update buffer. Codegen computes the
    /// PPU address `$2000 + y*32 + x` and lays down a
    /// `[len=1][addr_hi][addr_lo][tile]` record at the current
    /// `VRAM_BUF_HEAD`, then bumps the head by 4 and writes a
    /// fresh `0` sentinel. The NMI handler drains the buffer
    /// during vblank.
    NtSet {
        x: IrTemp,
        y: IrTemp,
        tile: IrTemp,
    },
    /// `nt_attr(x, y, value)` — same shape as `NtSet` but the
    /// PPU address resolves to the attribute table at
    /// `$23C0 + (y/4)*8 + (x/4)`. Useful for changing a 4×4-cell
    /// metatile group's sub-palette without rewriting the
    /// underlying tiles.
    NtAttr {
        x: IrTemp,
        y: IrTemp,
        value: IrTemp,
    },
    /// `nt_fill_h(x, y, len, tile)` — append a horizontal run of
    /// `len` copies of `tile` starting at nametable cell `(x, y)`.
    /// `len` is a runtime byte; the runtime must keep `len < 253`
    /// to leave space for the buffer header.
    NtFillH {
        x: IrTemp,
        y: IrTemp,
        len: IrTemp,
        tile: IrTemp,
    },

    /// Edge-triggered input read: `p1.a.pressed` / `p1.a.released`.
    /// `dest` receives a boolean (0 or the button mask) — set when
    /// the button is pressed-but-was-not this frame (for
    /// `.pressed`), or not-pressed-but-was last frame (for
    /// `.released`). `player` is 0 for P1, 1 for P2. `mask` is
    /// the button bit. `released` selects the released variant when
    /// true, pressed when false.
    ReadInputEdge {
        dest: IrTemp,
        player: u8,
        mask: u8,
        released: bool,
    },

    // Source mapping
    SourceLoc(Span),
}

/// A basic block terminator.
#[derive(Debug, Clone)]
pub enum IrTerminator {
    /// Unconditional jump to a label.
    Jump(String),
    /// Conditional branch: if temp != 0 goto `true_label` else goto `false_label`.
    Branch(IrTemp, String, String),
    /// Return from function, optionally with a value.
    Return(Option<IrTemp>),
    /// Unreachable (after infinite loops, etc.)
    Unreachable,
}

impl IrProgram {
    /// Count total number of IR operations across all functions.
    pub fn op_count(&self) -> usize {
        self.functions
            .iter()
            .flat_map(|f| &f.blocks)
            .map(|b| b.ops.len())
            .sum()
    }

    /// Human-readable pretty-print of the entire program — used by
    /// the `--dump-ir` CLI flag and by debugging sessions.
    pub fn pretty(&self) -> String {
        use std::fmt::Write;
        let mut out = String::new();
        out.push_str("# IR Program\n");
        let _ = writeln!(out, "# start_state = {}", self.start_state);
        let _ = writeln!(out, "# states = {:?}", self.states);
        if !self.globals.is_empty() {
            out.push_str("\n# Globals\n");
            for g in &self.globals {
                let _ = writeln!(
                    out,
                    "  {} {} (size={}) = {:?}",
                    g.var_id, g.name, g.size, g.init_value
                );
            }
        }
        for func in &self.functions {
            let _ = writeln!(
                out,
                "\nfn {}({} params, has_return={}):",
                func.name, func.param_count, func.has_return
            );
            for block in &func.blocks {
                let _ = writeln!(out, "  {}:", block.label);
                for op in &block.ops {
                    let _ = writeln!(out, "    {op:?}");
                }
                let _ = writeln!(out, "    -> {:?}", block.terminator);
            }
        }
        out
    }
}

impl IrFunction {
    /// Count total number of IR operations in this function.
    pub fn op_count(&self) -> usize {
        self.blocks.iter().map(|b| b.ops.len()).sum()
    }
}
