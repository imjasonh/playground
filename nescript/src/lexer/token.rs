#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub file_id: u16,
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(file_id: u16, start: u32, end: u32) -> Self {
        Self {
            file_id,
            start,
            end,
        }
    }

    /// Create a dummy span for testing or synthetic nodes.
    pub fn dummy() -> Self {
        Self {
            file_id: 0,
            start: 0,
            end: 0,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // Literals
    IntLiteral(u16),
    StringLiteral(String),
    BoolLiteral(bool),

    // Identifiers and keywords
    Ident(String),
    KwGame,
    KwState,
    KwOn,
    KwFun,
    KwVar,
    KwConst,
    KwEnum,
    KwStruct,
    KwIf,
    KwElse,
    KwWhile,
    KwFor,
    KwIn,
    KwMatch,
    KwBreak,
    KwContinue,
    KwReturn,
    KwNot,
    KwAnd,
    KwOr,
    KwFast,
    KwSlow,
    KwInline,
    KwInclude,
    KwStart,
    KwTransition,
    KwSprite,
    KwMetasprite,
    KwBackground,
    KwPalette,
    KwSfx,
    KwMusic,
    KwSave,
    /// `metatileset Name { metatiles: [...] }` — a packed library of
    /// 2×2 metatile definitions (4 CHR tile indices per metatile,
    /// plus a `collide` flag). See `parse_metatileset_decl` in the
    /// parser. Paired with `room` for the level-data feature pulled
    /// from `docs/future-work.md` §H.
    KwMetatileset,
    /// `room Name { metatileset: Name, layout: [16x15 ids] }` — a
    /// concrete level laid out as a 16×15 grid of metatile IDs from
    /// the named metatileset. The compiler expands this into a
    /// 32×30 nametable + collision bitmap at compile time so the
    /// runtime cost matches the existing `background` path.
    KwRoom,
    /// `paint_room Name` — the room-flavoured sibling of
    /// `load_background`. Queues a nametable update for the next
    /// vblank using the room's compile-time-expanded tile grid, and
    /// also sets the runtime's "current room collision map"
    /// pointer so subsequent `collides_at(x, y)` queries answer
    /// against this room.
    KwPaintRoom,
    KwDraw,
    KwPlay,
    KwStopMusic,
    KwStartMusic,
    KwLoadBackground,
    KwSetPalette,
    KwScroll,
    KwAsm,
    KwRaw,
    KwBank,
    KwLoop,
    KwWaitFrame,
    KwCycleSprites,
    KwU8,
    KwI8,
    KwU16,
    KwI16,
    KwBool,
    KwDebug,
    KwAs,

    // Symbols
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Colon,
    Semicolon,
    Arrow,
    FatArrow,
    Dot,
    DotDot,
    At,

    // Operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Amp,
    Pipe,
    Caret,
    Tilde,
    ShiftLeft,
    ShiftRight,
    Eq,
    NotEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    Assign,
    PlusAssign,
    MinusAssign,
    AmpAssign,
    PipeAssign,
    CaretAssign,
    ShiftLeftAssign,
    ShiftRightAssign,

    // Raw text from `asm { ... }` or `raw asm { ... }` blocks.
    // The body is captured verbatim (including newlines) so the
    // inline-asm parser can tokenize its own mnemonics.
    AsmBody(String),

    // Special
    Eof,
}

impl std::fmt::Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IntLiteral(v) => write!(f, "{v}"),
            Self::StringLiteral(s) => write!(f, "\"{s}\""),
            Self::BoolLiteral(b) => write!(f, "{b}"),
            Self::Ident(s) => write!(f, "{s}"),
            Self::KwGame => write!(f, "game"),
            Self::KwState => write!(f, "state"),
            Self::KwOn => write!(f, "on"),
            Self::KwFun => write!(f, "fun"),
            Self::KwVar => write!(f, "var"),
            Self::KwConst => write!(f, "const"),
            Self::KwEnum => write!(f, "enum"),
            Self::KwStruct => write!(f, "struct"),
            Self::KwIf => write!(f, "if"),
            Self::KwElse => write!(f, "else"),
            Self::KwWhile => write!(f, "while"),
            Self::KwFor => write!(f, "for"),
            Self::KwIn => write!(f, "in"),
            Self::KwMatch => write!(f, "match"),
            Self::KwBreak => write!(f, "break"),
            Self::KwContinue => write!(f, "continue"),
            Self::KwReturn => write!(f, "return"),
            Self::KwNot => write!(f, "not"),
            Self::KwAnd => write!(f, "and"),
            Self::KwOr => write!(f, "or"),
            Self::KwFast => write!(f, "fast"),
            Self::KwSlow => write!(f, "slow"),
            Self::KwInline => write!(f, "inline"),
            Self::KwInclude => write!(f, "include"),
            Self::KwStart => write!(f, "start"),
            Self::KwTransition => write!(f, "transition"),
            Self::KwSprite => write!(f, "sprite"),
            Self::KwMetasprite => write!(f, "metasprite"),
            Self::KwBackground => write!(f, "background"),
            Self::KwPalette => write!(f, "palette"),
            Self::KwSfx => write!(f, "sfx"),
            Self::KwMusic => write!(f, "music"),
            Self::KwSave => write!(f, "save"),
            Self::KwMetatileset => write!(f, "metatileset"),
            Self::KwRoom => write!(f, "room"),
            Self::KwPaintRoom => write!(f, "paint_room"),
            Self::KwDraw => write!(f, "draw"),
            Self::KwPlay => write!(f, "play"),
            Self::KwStopMusic => write!(f, "stop_music"),
            Self::KwStartMusic => write!(f, "start_music"),
            Self::KwLoadBackground => write!(f, "load_background"),
            Self::KwSetPalette => write!(f, "set_palette"),
            Self::KwScroll => write!(f, "scroll"),
            Self::KwAsm => write!(f, "asm"),
            Self::KwRaw => write!(f, "raw"),
            Self::KwBank => write!(f, "bank"),
            Self::KwLoop => write!(f, "loop"),
            Self::KwWaitFrame => write!(f, "wait_frame"),
            Self::KwCycleSprites => write!(f, "cycle_sprites"),
            Self::KwU8 => write!(f, "u8"),
            Self::KwI8 => write!(f, "i8"),
            Self::KwU16 => write!(f, "u16"),
            Self::KwI16 => write!(f, "i16"),
            Self::KwBool => write!(f, "bool"),
            Self::KwDebug => write!(f, "debug"),
            Self::KwAs => write!(f, "as"),
            Self::LParen => write!(f, "("),
            Self::RParen => write!(f, ")"),
            Self::LBrace => write!(f, "{{"),
            Self::RBrace => write!(f, "}}"),
            Self::LBracket => write!(f, "["),
            Self::RBracket => write!(f, "]"),
            Self::Comma => write!(f, ","),
            Self::Colon => write!(f, ":"),
            Self::Semicolon => write!(f, ";"),
            Self::Arrow => write!(f, "->"),
            Self::FatArrow => write!(f, "=>"),
            Self::Dot => write!(f, "."),
            Self::DotDot => write!(f, ".."),
            Self::At => write!(f, "@"),
            Self::Plus => write!(f, "+"),
            Self::Minus => write!(f, "-"),
            Self::Star => write!(f, "*"),
            Self::Slash => write!(f, "/"),
            Self::Percent => write!(f, "%"),
            Self::Amp => write!(f, "&"),
            Self::Pipe => write!(f, "|"),
            Self::Caret => write!(f, "^"),
            Self::Tilde => write!(f, "~"),
            Self::ShiftLeft => write!(f, "<<"),
            Self::ShiftRight => write!(f, ">>"),
            Self::Eq => write!(f, "=="),
            Self::NotEq => write!(f, "!="),
            Self::Lt => write!(f, "<"),
            Self::Gt => write!(f, ">"),
            Self::LtEq => write!(f, "<="),
            Self::GtEq => write!(f, ">="),
            Self::Assign => write!(f, "="),
            Self::PlusAssign => write!(f, "+="),
            Self::MinusAssign => write!(f, "-="),
            Self::AmpAssign => write!(f, "&="),
            Self::PipeAssign => write!(f, "|="),
            Self::CaretAssign => write!(f, "^="),
            Self::ShiftLeftAssign => write!(f, "<<="),
            Self::ShiftRightAssign => write!(f, ">>="),
            Self::AsmBody(_) => write!(f, "<asm body>"),
            Self::Eof => write!(f, "EOF"),
        }
    }
}
