use crate::lexer::Span;

#[derive(Debug, Clone)]
pub struct Program {
    pub game: GameDecl,
    pub globals: Vec<VarDecl>,
    /// Battery-backed save variables, declared inside a top-level
    /// `save { var ... }` block. The analyzer allocates these at
    /// `$6000+` (the iNES SRAM region) instead of main RAM, and the
    /// ROM builder flips byte-6 bit-1 of the iNES header so
    /// emulators and cartridge boards persist this region across
    /// power cycles. SRAM is uninitialized at first power-on, so
    /// users should checksum or use a magic-byte sentinel to detect
    /// a fresh battery — the compiler does not auto-initialize
    /// save fields.
    pub saves: Vec<VarDecl>,
    pub constants: Vec<ConstDecl>,
    pub enums: Vec<EnumDecl>,
    pub structs: Vec<StructDecl>,
    pub functions: Vec<FunDecl>,
    pub states: Vec<StateDecl>,
    pub sprites: Vec<SpriteDecl>,
    pub palettes: Vec<PaletteDecl>,
    pub backgrounds: Vec<BackgroundDecl>,
    pub metasprites: Vec<MetaspriteDecl>,
    /// Top-level `metatileset Name { metatiles: [...] }` declarations.
    /// Each one is a packed library of 2×2 tile bundles plus a per-
    /// metatile collision flag, used by `room` to assemble level
    /// data and by `collides_at(x, y)` to answer the runtime
    /// "is this pixel inside a solid metatile?" query. See
    /// [`MetatilesetDecl`] for the data shape and the §H entry in
    /// `docs/future-work.md` for the design.
    pub metatilesets: Vec<MetatilesetDecl>,
    /// Top-level `room Name { metatileset: ..., layout: [...] }`
    /// declarations. Each room is a 16×15 grid of metatile IDs that
    /// the compiler expands into a 32×30 nametable + 64-byte
    /// attribute table + 240-byte collision bitmap, all PRG-resident.
    /// `paint_room Name` paints the expanded nametable; `collides_at`
    /// reads the collision bitmap.
    pub rooms: Vec<RoomDecl>,
    pub sfx: Vec<SfxDecl>,
    pub music: Vec<MusicDecl>,
    pub banks: Vec<BankDecl>,
    pub start_state: String,
    pub span: Span,
}

/// `metasprite Name { sprite: Tileset, dx: [...], dy: [...], frame: [...] }`
/// — a multi-tile sprite group authored as parallel offset arrays.
/// `draw Name at: (x, y)` lowers to one `DrawSprite` per tile, with
/// each tile's screen position computed as `(x + dx[i], y + dy[i])`
/// and its tile index taken from `frame[i]`. The underlying
/// `sprite:` field names a previously-declared sprite/tileset that
/// owns the actual CHR data — metasprites only describe layout.
///
/// All three offset/frame arrays must have the same length, which
/// becomes the metasprite's tile count. The lowering does the
/// per-tile cursor bump through the existing OAM cursor path so a
/// metasprite that draws four tiles consumes four OAM slots in the
/// same order the user wrote them.
///
/// Today only u8 (unsigned) offsets are supported. Negative
/// offsets aren't representable in the current `NesType::U8` array
/// literals — see `docs/future-work.md`.
#[derive(Debug, Clone)]
pub struct MetaspriteDecl {
    pub name: String,
    /// Underlying CHR-bearing sprite/tileset whose tiles are
    /// indexed by this metasprite's `frame:` entries. Looked up
    /// in [`Program::sprites`] at analysis time.
    pub sprite_name: String,
    pub dx: Vec<u8>,
    pub dy: Vec<u8>,
    pub frame: Vec<u8>,
    pub span: Span,
}

/// `metatileset Name { metatiles: [...] }` — a packed library of
/// 2×2 metatile definitions. Each metatile bundles four CHR tile
/// indices (top-left, top-right, bottom-left, bottom-right) plus a
/// per-metatile collision bool. The analyzer caps the metatile
/// count at 256 so a metatile ID fits in a single byte.
///
/// Pairs with [`RoomDecl`] (which references the metatileset by
/// name and lays out rooms as a 16×15 grid of metatile IDs) and the
/// `collides_at(x, y) -> bool` builtin (which reads the per-room
/// collision bitmap derived from this `collide` flag).
#[derive(Debug, Clone)]
pub struct MetatilesetDecl {
    pub name: String,
    pub metatiles: Vec<MetatileEntry>,
    pub span: Span,
}

/// One entry in a `metatileset { metatiles: [...] }` array. The
/// `id` field is mostly informational — entries are stored in
/// declaration order and looked up by index from `RoomDecl::layout`,
/// so the analyzer rejects out-of-order or duplicate IDs to keep
/// the source readable.
#[derive(Debug, Clone)]
pub struct MetatileEntry {
    pub id: u8,
    pub tiles: [u8; 4],
    pub collide: bool,
    pub span: Span,
}

/// `room Name { metatileset: M, layout: [16x15 metatile ids] }` — a
/// concrete level. The compiler:
///
/// - validates every `layout` byte against the named metatileset's
///   declared IDs (E0210);
/// - expands the 240 cells into a 32×30 (=960 byte) nametable using
///   each metatile's four tile indices;
/// - emits a 64-byte attribute table (currently all sub-palette 0;
///   a future revision can switch to per-quadrant palette hints);
/// - emits a 30-byte (240-bit) collision bitmap so `collides_at`
///   can answer in two indexed loads + a single shift.
///
/// At runtime, `paint_room Name` desugars to the existing
/// `load_background` machinery against the synthesized nametable
/// blob, and `collides_at(x, y)` JSRs into a small helper that
/// reads the room's collision bitmap.
#[derive(Debug, Clone)]
pub struct RoomDecl {
    pub name: String,
    pub metatileset: String,
    /// 240 bytes: row-major, row 0 = top of screen, x = column 0..15.
    pub layout: Vec<u8>,
    pub span: Span,
}

/// `enum Name { V1, V2, V3 }` — variants become u8 constants with
/// values equal to their declaration order (0, 1, 2, ...). Variant
/// names are global: they're flattened into the constants table so
/// they can be referenced directly without namespacing.
#[derive(Debug, Clone)]
pub struct EnumDecl {
    pub name: String,
    pub variants: Vec<(String, Span)>,
    pub span: Span,
}

/// `struct Name { field1: u8, field2: u8 }` — composite type with a
/// known layout. Fields are stored contiguously in memory in
/// declaration order (no padding). Only primitive-sized fields (u8,
/// i8, bool) are supported in the v1 layout.
#[derive(Debug, Clone)]
pub struct StructDecl {
    pub name: String,
    pub fields: Vec<StructField>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub name: String,
    pub field_type: NesType,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct SpriteDecl {
    pub name: String,
    pub chr_source: AssetSource,
    pub span: Span,
}

/// `palette Name { colors: [c0, c1, ..., c31] }` — declares a
/// 32-byte PPU palette (16 bytes background + 16 bytes sprite, in
/// the standard `$3F00-$3F1F` layout). Colors are NES master-palette
/// indices, `$00-$3F`. Shorter lists are zero-padded; longer lists
/// are rejected by the analyzer.
///
/// The first `palette` declared in a program is loaded into VRAM at
/// reset time. Other declarations sit in PRG ROM as named data
/// blobs and become active via `set_palette Name`, which queues the
/// write for the next vblank.
#[derive(Debug, Clone)]
pub struct PaletteDecl {
    pub name: String,
    pub colors: Vec<u8>,
    /// Optional PNG source — when set, the analyzer leaves `colors`
    /// empty and the asset resolver decodes the PNG into a 32-byte
    /// palette blob at compile time. Mutually exclusive with
    /// `colors` being non-empty in practice (the parser never fills
    /// both).
    pub png_source: Option<String>,
    pub span: Span,
}

/// `background Name { tiles: [960 bytes], attributes: [64 bytes] }`
/// — declares a full-screen nametable. `tiles` is a 32×30 grid of
/// CHR tile indices (`$0000-$03BF` of a nametable); `attributes` is
/// the 8×8 attribute table (`$03C0-$03FF`). Shorter lists are
/// zero-padded to fill the nametable; longer lists are rejected.
///
/// The first `background` declared in a program is loaded into
/// nametable 0 at reset time. Other declarations become active via
/// `load_background Name`, which queues the write for the next
/// vblank.
#[derive(Debug, Clone)]
pub struct BackgroundDecl {
    pub name: String,
    pub tiles: Vec<u8>,
    pub attributes: Vec<u8>,
    /// Optional PNG source for `background Name @nametable("file.png")`.
    /// When set, the asset resolver decodes the PNG into tile + attribute
    /// tables at compile time. Mutually exclusive with inline
    /// `tiles` / `attributes` (the parser never fills both).
    pub png_source: Option<String>,
    pub span: Span,
}

/// APU channel an sfx targets. Pulse1 is the historical default and
/// the only one populated from older programs that omit `channel:`.
/// Triangle and Noise were added as part of the "richer audio"
/// work — Triangle has no volume envelope (the channel is fixed
/// output), Noise uses a 16-entry period table rather than the
/// pulse channel's 60-entry one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Channel {
    Pulse1,
    Pulse2,
    Triangle,
    Noise,
}

/// `sfx Name { ... }` — a sound effect played on pulse 1 (by default).
/// SFX are frame-accurate envelopes: `pitch[i]` and `volume[i]`
/// describe the register state for frame `i`, advancing one entry
/// per NMI tick. `duty` selects the pulse duty cycle (0-3) for the
/// whole effect. The two arrays must have the same length; the runtime
/// drops the channel volume to 0 one frame after the last entry.
///
/// The `channel:` property (new) lets a declaration target the
/// triangle or noise channels instead of the default pulse 1. For
/// triangle, `volume` is meaningless (fixed-level channel) and the
/// per-frame "volume" byte is instead treated as a hold flag (nonzero
/// = sustain, zero = release/stop). For noise, `pitch` values are
/// interpreted as 0-15 indices into the APU's internal 16-entry
/// noise period table rather than raw 11-bit pulse periods.
#[derive(Debug, Clone)]
pub struct SfxDecl {
    pub name: String,
    /// Duty cycle bits (0-3). Each bit pattern picks a different
    /// pulse waveform; 2 (50%) sounds like a square wave. Not
    /// meaningful for triangle or noise channels.
    pub duty: u8,
    /// One period byte per frame, written to $4002 (pulse 1) or
    /// $400E (noise, low 4 bits only) on trigger.
    pub pitch: Vec<u8>,
    /// One volume byte per frame (0-15), combined with the duty bits
    /// and written to $4000 (pulse 1) / $400C (noise) / $4008
    /// (triangle; any nonzero value means "hold", zero means release).
    pub volume: Vec<u8>,
    /// APU channel this sfx drives. Defaults to [`Channel::Pulse1`]
    /// when the declaration omits the `channel:` property.
    pub channel: Channel,
    pub span: Span,
}

/// `music Name { ... }` — a background music track played on pulse 2.
/// Music is encoded as a list of `(note_index, duration_frames)`
/// pairs. Note index 0 is a rest; indexes 1..=60 look up a period in
/// the builtin period table (C1 through B5). The track loops by
/// default when it reaches the end.
#[derive(Debug, Clone)]
pub struct MusicDecl {
    pub name: String,
    /// Pulse-2 duty cycle (0-3).
    pub duty: u8,
    /// Constant volume (0-15) for pulse 2.
    pub volume: u8,
    /// True: the track loops when it reaches the end.
    /// False: the track mutes itself on completion.
    pub loops: bool,
    /// List of `(note_index, duration_frames)` pairs. A `note_index`
    /// of 0 is a rest; otherwise it's an index into the builtin
    /// period table (see `runtime::gen_period_table`).
    pub notes: Vec<MusicNote>,
    pub span: Span,
}

/// A single note in a music track: pitch + duration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MusicNote {
    /// 0 = rest; 1-60 = period table index; other values are invalid.
    pub pitch: u8,
    /// Number of frames to hold this note (1-255). 0 is invalid.
    pub duration: u8,
}

#[derive(Debug, Clone)]
pub enum AssetSource {
    Chr(String),
    Binary(String),
    Inline(Vec<u8>),
}

#[derive(Debug, Clone)]
pub struct GameDecl {
    pub name: String,
    pub mapper: Mapper,
    pub mirroring: Mirroring,
    /// iNES header flavor to emit. Defaults to [`HeaderFormat::Ines1`];
    /// programs can opt into NES 2.0 via `game Foo { header: nes2 }`.
    pub header: HeaderFormat,
    /// Absolute address the runtime should write to for `debug.log`
    /// output and `__debug_halt` sentinels. Defaults to `$4800`
    /// (the FCEUX convention). Programs targeting Mesen/Mesen2 can
    /// set `debug_port: mesen` in the `game { }` block, which
    /// selects `$4018` — Mesen's documented tracing port. Custom
    /// addresses (`debug_port: 0x2FFF`) are also accepted so ROMs
    /// for unusual debuggers can retarget the port.
    pub debug_port: u16,
    /// When true, every `on frame { }` handler automatically bumps
    /// the OAM cycle offset by 4 at the top — the same effect as
    /// calling `cycle_sprites` as the first statement. Paired with
    /// the `__sprite_cycle_used` runtime path this turns the NES's
    /// 8-sprites-per-scanline hardware dropout into per-frame
    /// flicker, which the eye reconstructs into a full sprite
    /// count across frames. Opt-in because it adds ~10 bytes per
    /// handler and the flicker only looks correct if user code
    /// isn't already managing priorities manually.
    pub sprite_flicker: bool,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mapper {
    NROM,
    MMC1,
    UxROM,
    MMC3,
    /// `AxROM` (mapper 7). Single-screen mirroring, up to 256 KB PRG
    /// bankswitched in 32 KB pages via one write to `$8000-$FFFF`.
    /// Register layout: bits 0-2 select the 32 KB PRG bank, bit 4
    /// selects single-screen nametable (0 = lower, 1 = upper).
    /// `Mirroring::Horizontal` → lower-screen, `Mirroring::Vertical`
    /// → upper-screen in the initial write at reset.
    AxROM,
    /// `CNROM` (mapper 3). Fixed 32 KB PRG, 8 KB CHR bankswitching
    /// via one write to `$8000-$FFFF`. Supports up to ~2 MB of CHR
    /// ROM though most commercial carts stopped at 32 KB. Useful
    /// for games that want static PRG but swap entire tile sheets
    /// per screen / level.
    CNROM,
    /// `GNROM` / `MHROM` (mapper 66). Combines `AxROM`-style 32 KB
    /// PRG pages with `CNROM`-style 8 KB CHR bankswitching in one
    /// register at `$8000-$FFFF`. Bits 4-5 select the PRG page,
    /// bits 0-1 select the CHR bank. Useful for small-to-medium
    /// homebrew games that outgrow NROM but don't need MMC1's
    /// mirroring control or MMC3's scanline IRQ.
    GNROM,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mirroring {
    Horizontal,
    Vertical,
}

/// iNES header format to emit in the .nes file.
///
/// `Ines1` is the classic 16-byte iNES 1.0 header that every
/// `NEScript` program has used to date. `Nes2` opts into the
/// backwards-compatible NES 2.0 extension: the header is still
/// 16 bytes, but byte 7 bits 2-3 are set to `10` and bytes 8-15
/// carry extended metadata (submapper, PRG/CHR size MSBs, PRG RAM,
/// CHR RAM, timing, etc.). NES 2.0 is strictly additive — any
/// emulator that doesn't understand it falls back to reading the
/// header as iNES 1.0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeaderFormat {
    Ines1,
    Nes2,
}

#[derive(Debug, Clone)]
pub struct BankDecl {
    pub name: String,
    pub bank_type: BankType,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BankType {
    Prg,
    Chr,
}

#[derive(Debug, Clone)]
pub struct StateDecl {
    pub name: String,
    pub locals: Vec<VarDecl>,
    pub on_enter: Option<Block>,
    pub on_exit: Option<Block>,
    pub on_frame: Option<Block>,
    pub on_scanline: Vec<(u8, Block)>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FunDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Option<NesType>,
    pub body: Block,
    pub is_inline: bool,
    /// When `Some(bank_name)`, the function was declared inside a
    /// `bank Foo { fun ... }` block and its compiled bytes live in
    /// the named switchable PRG bank. Calls from the fixed bank to
    /// this function go through a generated trampoline (see
    /// `runtime::gen_bank_trampoline`); calls from inside the same
    /// bank stay as direct JSRs. `None` means the function lives in
    /// the fixed bank along with the runtime, NMI/IRQ handlers, and
    /// every state handler — the only mode prior to the user-banked
    /// codegen work.
    pub bank: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub param_type: NesType,
}

#[derive(Debug, Clone)]
pub struct VarDecl {
    pub name: String,
    pub var_type: NesType,
    pub init: Option<Expr>,
    pub placement: Placement,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ConstDecl {
    pub name: String,
    pub const_type: NesType,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Placement {
    Fast,
    Slow,
    Auto,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NesType {
    U8,
    I8,
    U16,
    /// Signed 16-bit integer. Same two-byte layout as `U16` but the
    /// analyzer tracks the signedness on literals, casts, and
    /// assignments. Arithmetic emits the same carry-propagating
    /// paired operations as `U16`; comparisons are currently
    /// lowered through the same unsigned 16-bit compare path that
    /// `U16` uses (matching the existing `I8` behaviour). A proper
    /// signed-compare lowering would be a separate follow-up.
    I16,
    Bool,
    Array(Box<NesType>, u16),
    /// A user-declared struct, identified by its name. The analyzer
    /// looks up field layouts in the `StructDecl` table.
    Struct(String),
}

impl std::fmt::Display for NesType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::U8 => write!(f, "u8"),
            Self::I8 => write!(f, "i8"),
            Self::U16 => write!(f, "u16"),
            Self::I16 => write!(f, "i16"),
            Self::Bool => write!(f, "bool"),
            Self::Array(t, n) => write!(f, "{t}[{n}]"),
            Self::Struct(name) => write!(f, "{name}"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Expr {
    IntLiteral(u16, Span),
    BoolLiteral(bool, Span),
    Ident(String, Span),
    ArrayIndex(String, Box<Expr>, Span),
    /// Field access on a struct variable: `pos.x`.
    FieldAccess(String, String, Span),
    BinaryOp(Box<Expr>, BinOp, Box<Expr>, Span),
    UnaryOp(UnaryOp, Box<Expr>, Span),
    Call(String, Vec<Expr>, Span),
    ButtonRead(Option<Player>, String, Span),
    /// Edge-triggered button read: `p1.button.a.pressed` or
    /// `p1.button.a.released`. The final boolean says which edge
    /// (true = released, false = pressed) so a single variant
    /// covers both cases. The analyzer and lowering read
    /// `PREV_INPUT_P1` / `PREV_INPUT_P2` at the read site and
    /// XOR against the current byte to compute the edge.
    ButtonEdge(Option<Player>, String, bool, Span),
    ArrayLiteral(Vec<Expr>, Span),
    Cast(Box<Expr>, NesType, Span),
    /// Struct literal: `Name { field1: expr, field2: expr, ... }`.
    /// Only allowed in non-condition expression positions — the
    /// parser bans them inside `if`/`while`/`for` conditions to
    /// avoid ambiguity with the following block.
    StructLiteral(String, Vec<(String, Expr)>, Span),
    /// `debug.METHOD(args)` expression form. Today only the
    /// no-argument query methods (`frame_overrun_count`,
    /// `frame_overran`) are accepted; other names are rejected by
    /// the analyzer. Lowering inspects [`crate::ir::lowering`] and
    /// emits either a Peek of the corresponding runtime address (in
    /// debug mode) or a constant zero (in release mode), so the
    /// builtin compiles to nothing in release builds.
    DebugCall(String, Vec<Expr>, Span),
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Self::IntLiteral(_, s)
            | Self::BoolLiteral(_, s)
            | Self::Ident(_, s)
            | Self::ArrayIndex(_, _, s)
            | Self::FieldAccess(_, _, s)
            | Self::BinaryOp(_, _, _, s)
            | Self::UnaryOp(_, _, s)
            | Self::Call(_, _, s)
            | Self::ButtonRead(_, _, s)
            | Self::ButtonEdge(_, _, _, s)
            | Self::ArrayLiteral(_, s)
            | Self::Cast(_, _, s)
            | Self::StructLiteral(_, _, s)
            | Self::DebugCall(_, _, s) => *s,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    ShiftLeft,
    ShiftRight,
    Eq,
    NotEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    And,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Negate,
    Not,
    BitNot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Player {
    P1,
    P2,
}

#[derive(Debug, Clone)]
pub enum Statement {
    VarDecl(VarDecl),
    Assign(LValue, AssignOp, Expr, Span),
    If(Expr, Block, Vec<(Expr, Block)>, Option<Block>, Span),
    While(Expr, Block, Span),
    Loop(Block, Span),
    /// `for NAME in START..END { BODY }` — half-open range.
    /// Lowers to an index variable + while loop in IR.
    For {
        var: String,
        start: Expr,
        end: Expr,
        body: Block,
        span: Span,
    },
    Break(Span),
    Continue(Span),
    Return(Option<Expr>, Span),
    Draw(DrawStmt),
    Transition(String, Span),
    WaitFrame(Span),
    /// `cycle_sprites` — advance the runtime sprite-cycling offset
    /// by one slot (4 bytes). Each call rotates the start position
    /// of the next OAM DMA so scenes with more than 8 sprites on a
    /// scanline drop a different one each frame, turning permanent
    /// dropout into visible flicker. Compiles to `INC $07EF` (with
    /// natural u8 wrap at 256→0) plus the `__sprite_cycle_used`
    /// marker label the linker uses to select the cycling variant
    /// of the NMI handler.
    CycleSprites(Span),
    Call(String, Vec<Expr>, Span),
    /// `load_background Name` — queue the named background for a
    /// vblank-safe copy into nametable 0. Lowered to
    /// [`IrOp::LoadBackground`].
    LoadBackground(String, Span),
    /// `paint_room Name` — the room-aware sibling of
    /// `load_background`. The compiler synthesizes a background-
    /// shaped blob for the room at compile time; at runtime,
    /// `paint_room` queues that nametable update AND sets the
    /// current-room ZP pointer so `collides_at(x, y)` queries hit
    /// the right collision bitmap. Lowered to [`IrOp::PaintRoom`].
    PaintRoom(String, Span),
    /// `set_palette Name` — queue the named palette for a
    /// vblank-safe copy into `$3F00-$3F1F`. Lowered to
    /// [`IrOp::SetPalette`].
    SetPalette(String, Span),
    Scroll(Expr, Expr, Span),
    /// debug.log(expr, ...) — writes values to the emulator debug port.
    /// Stripped in release mode.
    DebugLog(Vec<Expr>, Span),
    /// debug.assert(cond) — runtime check, halts on failure.
    /// Stripped in release mode.
    DebugAssert(Expr, Span),
    /// Inline 6502 assembly captured verbatim. The body is parsed by
    /// the codegen stage using `asm::parse_inline`. `raw` variants
    /// skip variable substitution for completely unmanaged bytes.
    InlineAsm(String, Span),
    RawAsm(String, Span),
    /// Audio: `play SfxName` — trigger a one-shot sound effect on pulse 1.
    /// Compiles to a trigger sequence plus an envelope pointer store;
    /// the runtime NMI tick walks the envelope at one byte per frame.
    Play(String, Span),
    /// Audio: `start_music TrackName` — begin playing a looping music
    /// track on pulse 2, driven by the same NMI tick.
    StartMusic(String, Span),
    /// Audio: `stop_music` — silence pulse 2 and the music state machine.
    StopMusic(Span),
}

impl Statement {
    pub fn span(&self) -> Span {
        match self {
            Self::VarDecl(v) => v.span,
            Self::Draw(d) => d.span,
            Self::For { span, .. } => *span,
            Self::Assign(_, _, _, s)
            | Self::If(_, _, _, _, s)
            | Self::While(_, _, s)
            | Self::Loop(_, s)
            | Self::Break(s)
            | Self::Continue(s)
            | Self::Return(_, s)
            | Self::Transition(_, s)
            | Self::WaitFrame(s)
            | Self::CycleSprites(s)
            | Self::Call(_, _, s)
            | Self::LoadBackground(_, s)
            | Self::PaintRoom(_, s)
            | Self::SetPalette(_, s)
            | Self::Scroll(_, _, s)
            | Self::DebugLog(_, s)
            | Self::DebugAssert(_, s)
            | Self::InlineAsm(_, s)
            | Self::RawAsm(_, s)
            | Self::Play(_, s)
            | Self::StartMusic(_, s)
            | Self::StopMusic(s) => *s,
        }
    }
}

#[derive(Debug, Clone)]
pub struct DrawStmt {
    pub sprite_name: String,
    pub x: Expr,
    pub y: Expr,
    pub frame: Option<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum LValue {
    Var(String),
    ArrayIndex(String, Box<Expr>),
    /// Struct field: `pos.x = 5`. First string is the struct variable
    /// name, second is the field name.
    Field(String, String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Assign,
    PlusAssign,
    MinusAssign,
    AmpAssign,
    PipeAssign,
    CaretAssign,
    ShiftLeftAssign,
    ShiftRightAssign,
}
