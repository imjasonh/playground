use crate::lexer::Span;
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Level {
    Error,
    Warning,
}

/// Error codes organized by compiler phase.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorCode {
    // E01xx: Lexer errors
    E0101, // unterminated string
    E0102, // invalid character
    E0103, // number literal overflow

    // E02xx: Type errors
    E0201, // type mismatch
    E0203, // invalid operation for type

    // E03xx: Memory errors
    E0301, // zero-page overflow / RAM exhausted

    // E04xx: Control flow errors
    E0401, // call depth exceeded
    E0402, // recursion detected
    E0404, // transition to undefined state

    // E05xx: Declaration errors
    E0501, // duplicate declaration
    E0502, // undefined variable
    E0503, // undefined function
    E0504, // missing start declaration
    E0505, // multiple start declarations
    E0506, // function has too many parameters (max 8)

    // E06xx: Unsupported-feature errors (parsed but not lowered)
    E0601, // state-local variable with array initializer is not supported
    E0603, // on_scanline handler requires mapper MMC3

    // W01xx: Warnings
    W0101, // expensive multiply/divide operation
    W0102, // loop without break or wait_frame
    W0103, // unused variable
    W0104, // unreachable code after terminator, or unreachable state
    W0105, // palette sub-palette universal mismatch (mirror collision)
    W0106, // implicit drop of non-void function return value
    W0107, // `fast` variable rarely accessed (wastes zero-page slot)
    W0108, // array elements past byte 255 unreachable via 8-bit X index
    W0109, // too many literal-coord sprite draws on one scanline (NES 8/scanline limit)
    W0110, // `inline fun` declined — body shape not splicable, fell back to regular call
    W0111, // initializer on a `save { var ... }` field (SRAM is preserved across power cycles, so init never runs)
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let code = match self {
            Self::E0101 => "E0101",
            Self::E0102 => "E0102",
            Self::E0103 => "E0103",
            Self::E0201 => "E0201",
            Self::E0203 => "E0203",
            Self::E0301 => "E0301",
            Self::E0401 => "E0401",
            Self::E0402 => "E0402",
            Self::E0404 => "E0404",
            Self::E0501 => "E0501",
            Self::E0502 => "E0502",
            Self::E0503 => "E0503",
            Self::E0504 => "E0504",
            Self::E0505 => "E0505",
            Self::E0506 => "E0506",
            Self::E0601 => "E0601",
            Self::E0603 => "E0603",
            Self::W0101 => "W0101",
            Self::W0102 => "W0102",
            Self::W0103 => "W0103",
            Self::W0104 => "W0104",
            Self::W0105 => "W0105",
            Self::W0106 => "W0106",
            Self::W0107 => "W0107",
            Self::W0108 => "W0108",
            Self::W0109 => "W0109",
            Self::W0110 => "W0110",
            Self::W0111 => "W0111",
        };
        write!(f, "{code}")
    }
}

impl ErrorCode {
    pub fn level(self) -> Level {
        match self {
            Self::W0101
            | Self::W0102
            | Self::W0103
            | Self::W0104
            | Self::W0105
            | Self::W0106
            | Self::W0107
            | Self::W0108
            | Self::W0109
            | Self::W0110
            | Self::W0111 => Level::Warning,
            _ => Level::Error,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub level: Level,
    pub code: ErrorCode,
    pub message: String,
    pub span: Span,
    pub labels: Vec<Label>,
    pub help: Option<String>,
    pub note: Option<String>,
}

impl Diagnostic {
    pub fn error(code: ErrorCode, message: impl Into<String>, span: Span) -> Self {
        Self {
            level: code.level(),
            code,
            message: message.into(),
            span,
            labels: Vec::new(),
            help: None,
            note: None,
        }
    }

    /// Construct a diagnostic with the level implied by the code
    /// (identical to [`Diagnostic::error`], but reads better at call
    /// sites that emit a warning code).
    pub fn warning(code: ErrorCode, message: impl Into<String>, span: Span) -> Self {
        Self::error(code, message, span)
    }

    #[must_use]
    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    #[must_use]
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.note = Some(note.into());
        self
    }

    #[must_use]
    pub fn with_label(mut self, span: Span, message: impl Into<String>) -> Self {
        self.labels.push(Label {
            span,
            message: message.into(),
        });
        self
    }

    pub fn is_error(&self) -> bool {
        self.level == Level::Error
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let level = match self.level {
            Level::Error => "error",
            Level::Warning => "warning",
        };
        write!(f, "{level}[{}]: {}", self.code, self.message)
    }
}
