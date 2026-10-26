#[cfg(test)]
mod tests;
mod token;

pub use token::{Span, Token, TokenKind};

use crate::errors::{Diagnostic, ErrorCode};

pub struct Lexer<'a> {
    source: &'a [u8],
    pos: usize,
    file_id: u16,
    diagnostics: Vec<Diagnostic>,
    /// When true, the next `{` that would normally be lexed as
    /// `LBrace` triggers raw-text capture until the matching `}`. Set
    /// right after emitting `KwAsm`.
    asm_body_pending: bool,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str, file_id: u16) -> Self {
        Self {
            source: source.as_bytes(),
            pos: 0,
            file_id,
            diagnostics: Vec::new(),
            asm_body_pending: false,
        }
    }

    pub fn lex(mut self) -> (Vec<Token>, Vec<Diagnostic>) {
        let mut tokens = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.pos >= self.source.len() {
                tokens.push(Token {
                    kind: TokenKind::Eof,
                    span: self.span(self.pos, self.pos),
                });
                break;
            }
            match self.next_token() {
                Some(tok) => tokens.push(tok),
                None => {
                    // Error already recorded, skip the bad character
                    self.pos += 1;
                }
            }
        }
        (tokens, self.diagnostics)
    }

    fn span(&self, start: usize, end: usize) -> Span {
        Span {
            file_id: self.file_id,
            start: start as u32,
            end: end as u32,
        }
    }

    fn peek(&self) -> Option<u8> {
        self.source.get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<u8> {
        self.source.get(self.pos + offset).copied()
    }

    fn advance(&mut self) -> u8 {
        let ch = self.source[self.pos];
        self.pos += 1;
        ch
    }

    fn skip_whitespace_and_comments(&mut self) {
        while self.pos < self.source.len() {
            let ch = self.source[self.pos];
            if ch == b' ' || ch == b'\t' || ch == b'\r' || ch == b'\n' {
                self.pos += 1;
            } else if ch == b'/' && self.peek_at(1) == Some(b'/') {
                // Line comment
                self.pos += 2;
                while self.pos < self.source.len() && self.source[self.pos] != b'\n' {
                    self.pos += 1;
                }
            } else {
                break;
            }
        }
    }

    fn next_token(&mut self) -> Option<Token> {
        let start = self.pos;
        let ch = self.advance();

        // If we're right after `asm` and see `{`, consume the entire
        // body until the matching `}` as a single `AsmBody` token.
        if self.asm_body_pending && ch == b'{' {
            self.asm_body_pending = false;
            return Some(self.capture_asm_body(start));
        }
        // Any non-`{` token clears the pending flag so we don't get
        // confused by things like `asm ;` (which is a syntax error
        // the parser will complain about).
        if self.asm_body_pending {
            self.asm_body_pending = false;
        }

        match ch {
            b'(' => Some(self.make_token(TokenKind::LParen, start)),
            b')' => Some(self.make_token(TokenKind::RParen, start)),
            b'{' => Some(self.make_token(TokenKind::LBrace, start)),
            b'}' => Some(self.make_token(TokenKind::RBrace, start)),
            b'[' => Some(self.make_token(TokenKind::LBracket, start)),
            b']' => Some(self.make_token(TokenKind::RBracket, start)),
            b',' => Some(self.make_token(TokenKind::Comma, start)),
            b':' => Some(self.make_token(TokenKind::Colon, start)),
            b';' => Some(self.make_token(TokenKind::Semicolon, start)),
            b'.' => {
                if self.peek() == Some(b'.') {
                    self.advance();
                    Some(self.make_token(TokenKind::DotDot, start))
                } else {
                    Some(self.make_token(TokenKind::Dot, start))
                }
            }
            b'@' => Some(self.make_token(TokenKind::At, start)),
            b'~' => Some(self.make_token(TokenKind::Tilde, start)),

            b'+' => {
                if self.peek() == Some(b'=') {
                    self.advance();
                    Some(self.make_token(TokenKind::PlusAssign, start))
                } else {
                    Some(self.make_token(TokenKind::Plus, start))
                }
            }
            b'-' => {
                if self.peek() == Some(b'=') {
                    self.advance();
                    Some(self.make_token(TokenKind::MinusAssign, start))
                } else if self.peek() == Some(b'>') {
                    self.advance();
                    Some(self.make_token(TokenKind::Arrow, start))
                } else {
                    Some(self.make_token(TokenKind::Minus, start))
                }
            }
            b'*' => Some(self.make_token(TokenKind::Star, start)),
            b'/' => Some(self.make_token(TokenKind::Slash, start)),
            b'%' => Some(self.make_token(TokenKind::Percent, start)),
            b'^' => {
                if self.peek() == Some(b'=') {
                    self.advance();
                    Some(self.make_token(TokenKind::CaretAssign, start))
                } else {
                    Some(self.make_token(TokenKind::Caret, start))
                }
            }

            b'&' => {
                if self.peek() == Some(b'=') {
                    self.advance();
                    Some(self.make_token(TokenKind::AmpAssign, start))
                } else {
                    Some(self.make_token(TokenKind::Amp, start))
                }
            }
            b'|' => {
                if self.peek() == Some(b'=') {
                    self.advance();
                    Some(self.make_token(TokenKind::PipeAssign, start))
                } else {
                    Some(self.make_token(TokenKind::Pipe, start))
                }
            }

            b'=' => {
                if self.peek() == Some(b'=') {
                    self.advance();
                    Some(self.make_token(TokenKind::Eq, start))
                } else if self.peek() == Some(b'>') {
                    self.advance();
                    Some(self.make_token(TokenKind::FatArrow, start))
                } else {
                    Some(self.make_token(TokenKind::Assign, start))
                }
            }
            b'!' => {
                if self.peek() == Some(b'=') {
                    self.advance();
                    Some(self.make_token(TokenKind::NotEq, start))
                } else {
                    self.diagnostics.push(
                        Diagnostic::error(
                            ErrorCode::E0102,
                            "unexpected character '!'",
                            self.span(start, self.pos),
                        )
                        .with_help("use 'not' for logical negation"),
                    );
                    None
                }
            }
            b'<' => {
                if self.peek() == Some(b'=') {
                    self.advance();
                    Some(self.make_token(TokenKind::LtEq, start))
                } else if self.peek() == Some(b'<') {
                    self.advance();
                    if self.peek() == Some(b'=') {
                        self.advance();
                        Some(self.make_token(TokenKind::ShiftLeftAssign, start))
                    } else {
                        Some(self.make_token(TokenKind::ShiftLeft, start))
                    }
                } else {
                    Some(self.make_token(TokenKind::Lt, start))
                }
            }
            b'>' => {
                if self.peek() == Some(b'=') {
                    self.advance();
                    Some(self.make_token(TokenKind::GtEq, start))
                } else if self.peek() == Some(b'>') {
                    self.advance();
                    if self.peek() == Some(b'=') {
                        self.advance();
                        Some(self.make_token(TokenKind::ShiftRightAssign, start))
                    } else {
                        Some(self.make_token(TokenKind::ShiftRight, start))
                    }
                } else {
                    Some(self.make_token(TokenKind::Gt, start))
                }
            }

            b'"' => self.lex_string(start),

            b'0'..=b'9' => self.lex_number(start),

            b'a'..=b'z' | b'A'..=b'Z' | b'_' => self.lex_identifier(start),

            _ => {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0102,
                    format!("unexpected character '{}'", ch as char),
                    self.span(start, self.pos),
                ));
                None
            }
        }
    }

    fn make_token(&self, kind: TokenKind, start: usize) -> Token {
        Token {
            kind,
            span: self.span(start, self.pos),
        }
    }

    fn lex_string(&mut self, start: usize) -> Option<Token> {
        let mut value = String::new();
        loop {
            match self.peek() {
                None | Some(b'\n') => {
                    self.diagnostics.push(Diagnostic::error(
                        ErrorCode::E0101,
                        "unterminated string literal",
                        self.span(start, self.pos),
                    ));
                    return None;
                }
                Some(b'"') => {
                    self.advance();
                    return Some(Token {
                        kind: TokenKind::StringLiteral(value),
                        span: self.span(start, self.pos),
                    });
                }
                Some(b'\\') => {
                    self.advance();
                    match self.peek() {
                        Some(b'n') => {
                            self.advance();
                            value.push('\n');
                        }
                        Some(b't') => {
                            self.advance();
                            value.push('\t');
                        }
                        Some(b'\\') => {
                            self.advance();
                            value.push('\\');
                        }
                        Some(b'"') => {
                            self.advance();
                            value.push('"');
                        }
                        _ => {
                            self.diagnostics.push(Diagnostic::error(
                                ErrorCode::E0102,
                                "invalid escape sequence",
                                self.span(self.pos - 1, self.pos + 1),
                            ));
                            if self.pos < self.source.len() {
                                self.advance();
                            }
                        }
                    }
                }
                Some(ch) => {
                    self.advance();
                    value.push(ch as char);
                }
            }
        }
    }

    fn lex_number(&mut self, start: usize) -> Option<Token> {
        // Check for hex (0x) or binary (0b) prefix
        if self.source[start] == b'0' {
            if self.peek() == Some(b'x') || self.peek() == Some(b'X') {
                self.advance();
                return self.lex_hex_number(start);
            }
            if self.peek() == Some(b'b') || self.peek() == Some(b'B') {
                self.advance();
                return self.lex_binary_number(start);
            }
        }

        // Decimal number
        while let Some(b'0'..=b'9' | b'_') = self.peek() {
            self.advance();
        }

        let text: String = self.source[start..self.pos]
            .iter()
            .filter(|&&b| b != b'_')
            .map(|&b| b as char)
            .collect();

        match text.parse::<u32>() {
            Ok(v) if u16::try_from(v).is_ok() => Some(Token {
                kind: TokenKind::IntLiteral(v as u16),
                span: self.span(start, self.pos),
            }),
            _ => {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0103,
                    "number literal exceeds u16 range (0–65535)",
                    self.span(start, self.pos),
                ));
                None
            }
        }
    }

    fn lex_hex_number(&mut self, start: usize) -> Option<Token> {
        let digit_start = self.pos;
        while let Some(b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F' | b'_') = self.peek() {
            self.advance();
        }
        if self.pos == digit_start {
            self.diagnostics.push(Diagnostic::error(
                ErrorCode::E0103,
                "expected hex digits after 0x",
                self.span(start, self.pos),
            ));
            return None;
        }
        let text: String = self.source[digit_start..self.pos]
            .iter()
            .filter(|&&b| b != b'_')
            .map(|&b| b as char)
            .collect();

        match u16::from_str_radix(&text, 16) {
            Ok(v) => Some(Token {
                kind: TokenKind::IntLiteral(v),
                span: self.span(start, self.pos),
            }),
            Err(_) => {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0103,
                    "hex literal exceeds u16 range (0x0000–0xFFFF)",
                    self.span(start, self.pos),
                ));
                None
            }
        }
    }

    fn lex_binary_number(&mut self, start: usize) -> Option<Token> {
        let digit_start = self.pos;
        while let Some(b'0' | b'1' | b'_') = self.peek() {
            self.advance();
        }
        if self.pos == digit_start {
            self.diagnostics.push(Diagnostic::error(
                ErrorCode::E0103,
                "expected binary digits after 0b",
                self.span(start, self.pos),
            ));
            return None;
        }
        let text: String = self.source[digit_start..self.pos]
            .iter()
            .filter(|&&b| b != b'_')
            .map(|&b| b as char)
            .collect();

        match u16::from_str_radix(&text, 2) {
            Ok(v) => Some(Token {
                kind: TokenKind::IntLiteral(v),
                span: self.span(start, self.pos),
            }),
            Err(_) => {
                self.diagnostics.push(Diagnostic::error(
                    ErrorCode::E0103,
                    "binary literal exceeds u16 range",
                    self.span(start, self.pos),
                ));
                None
            }
        }
    }

    fn lex_identifier(&mut self, start: usize) -> Option<Token> {
        while let Some(b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_') = self.peek() {
            self.advance();
        }
        let text = std::str::from_utf8(&self.source[start..self.pos]).unwrap();
        let kind = match text {
            "game" => TokenKind::KwGame,
            "state" => TokenKind::KwState,
            "on" => TokenKind::KwOn,
            "fun" => TokenKind::KwFun,
            "var" => TokenKind::KwVar,
            "const" => TokenKind::KwConst,
            "enum" => TokenKind::KwEnum,
            "struct" => TokenKind::KwStruct,
            "if" => TokenKind::KwIf,
            "else" => TokenKind::KwElse,
            "while" => TokenKind::KwWhile,
            "for" => TokenKind::KwFor,
            "in" => TokenKind::KwIn,
            "match" => TokenKind::KwMatch,
            "break" => TokenKind::KwBreak,
            "continue" => TokenKind::KwContinue,
            "return" => TokenKind::KwReturn,
            "true" => TokenKind::BoolLiteral(true),
            "false" => TokenKind::BoolLiteral(false),
            "not" => TokenKind::KwNot,
            "and" => TokenKind::KwAnd,
            "or" => TokenKind::KwOr,
            "fast" => TokenKind::KwFast,
            "slow" => TokenKind::KwSlow,
            "inline" => TokenKind::KwInline,
            "include" => TokenKind::KwInclude,
            "start" => TokenKind::KwStart,
            "transition" => TokenKind::KwTransition,
            "sprite" => TokenKind::KwSprite,
            "metasprite" => TokenKind::KwMetasprite,
            "background" => TokenKind::KwBackground,
            "palette" => TokenKind::KwPalette,
            "sfx" => TokenKind::KwSfx,
            "music" => TokenKind::KwMusic,
            "save" => TokenKind::KwSave,
            "metatileset" => TokenKind::KwMetatileset,
            "room" => TokenKind::KwRoom,
            "paint_room" => TokenKind::KwPaintRoom,
            "draw" => TokenKind::KwDraw,
            "play" => TokenKind::KwPlay,
            "stop_music" => TokenKind::KwStopMusic,
            "start_music" => TokenKind::KwStartMusic,
            "load_background" => TokenKind::KwLoadBackground,
            "set_palette" => TokenKind::KwSetPalette,
            "scroll" => TokenKind::KwScroll,
            "asm" => {
                self.asm_body_pending = true;
                TokenKind::KwAsm
            }
            "raw" => TokenKind::KwRaw,
            "bank" => TokenKind::KwBank,
            "loop" => TokenKind::KwLoop,
            "wait_frame" => TokenKind::KwWaitFrame,
            "cycle_sprites" => TokenKind::KwCycleSprites,
            "u8" => TokenKind::KwU8,
            "i8" => TokenKind::KwI8,
            "u16" => TokenKind::KwU16,
            "i16" => TokenKind::KwI16,
            "bool" => TokenKind::KwBool,
            "debug" => TokenKind::KwDebug,
            "as" => TokenKind::KwAs,
            _ => TokenKind::Ident(text.to_string()),
        };
        Some(Token {
            kind,
            span: self.span(start, self.pos),
        })
    }
}

impl Lexer<'_> {
    /// Capture everything between the `{` we just consumed and the
    /// matching `}` as an `AsmBody` token. Nested braces (e.g.
    /// `{variable}` substitution placeholders) are balanced by
    /// depth counting, so the body isn't cut short.
    fn capture_asm_body(&mut self, start: usize) -> Token {
        let body_start = self.pos;
        let mut depth = 1u32;
        while self.pos < self.source.len() && depth > 0 {
            match self.source[self.pos] {
                b'{' => depth += 1,
                b'}' => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
            self.pos += 1;
        }
        let body = String::from_utf8_lossy(&self.source[body_start..self.pos]).into_owned();
        if self.pos < self.source.len() {
            // Consume the closing brace
            self.pos += 1;
        } else {
            self.diagnostics.push(Diagnostic::error(
                ErrorCode::E0101,
                "unterminated `asm {` block",
                self.span(start, self.pos),
            ));
        }
        Token {
            kind: TokenKind::AsmBody(body),
            span: self.span(start, self.pos),
        }
    }
}

/// Convenience function for lexing a source string.
pub fn lex(source: &str) -> (Vec<Token>, Vec<Diagnostic>) {
    Lexer::new(source, 0).lex()
}
