pub mod ast;
pub mod preprocess;
#[cfg(test)]
mod tests;

pub use preprocess::preprocess as preprocess_source;

use crate::errors::{Diagnostic, ErrorCode};
use crate::lexer::{Span, Token, TokenKind};
use ast::*;

pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    diagnostics: Vec<Diagnostic>,
    /// When true, `parse_primary` refuses to consume an `Ident {`
    /// pattern as a struct literal — the `{` is reserved for the
    /// following `if` / `while` / `for` block. Struct literals in
    /// conditions must be parenthesized: `if x == (Foo { a: 1 })`.
    restrict_struct_literals: bool,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens,
            pos: 0,
            diagnostics: Vec::new(),
            restrict_struct_literals: false,
        }
    }

    pub fn parse(mut self) -> (Option<Program>, Vec<Diagnostic>) {
        match self.parse_program() {
            Ok(program) => (Some(program), self.diagnostics),
            Err(diag) => {
                self.diagnostics.push(diag);
                (None, self.diagnostics)
            }
        }
    }

    // ── Token helpers ──

    fn peek(&self) -> &TokenKind {
        self.tokens
            .get(self.pos)
            .map_or(&TokenKind::Eof, |t| &t.kind)
    }

    fn peek_at_offset(&self, offset: usize) -> Option<&TokenKind> {
        self.tokens.get(self.pos + offset).map(|t| &t.kind)
    }

    fn current_span(&self) -> Span {
        self.tokens.get(self.pos).map_or(Span::dummy(), |t| t.span)
    }

    fn advance(&mut self) -> &Token {
        let tok = &self.tokens[self.pos];
        if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
        }
        tok
    }

    fn expect(&mut self, expected: &TokenKind) -> Result<Span, Diagnostic> {
        if self.peek() == expected {
            let span = self.current_span();
            self.advance();
            Ok(span)
        } else {
            Err(Diagnostic::error(
                ErrorCode::E0201,
                format!("expected '{expected}', found '{}'", self.peek()),
                self.current_span(),
            ))
        }
    }

    fn expect_ident(&mut self) -> Result<(String, Span), Diagnostic> {
        if let TokenKind::Ident(name) = self.peek().clone() {
            let span = self.current_span();
            self.advance();
            Ok((name, span))
        } else {
            Err(Diagnostic::error(
                ErrorCode::E0201,
                format!("expected identifier, found '{}'", self.peek()),
                self.current_span(),
            ))
        }
    }

    /// Accept an identifier or a keyword that can be used as a name
    /// (e.g., button names like "start", "select").
    fn expect_name(&mut self) -> Result<(String, Span), Diagnostic> {
        let span = self.current_span();
        let name = match self.peek() {
            TokenKind::Ident(n) => n.clone(),
            // Keywords that double as button/property names
            TokenKind::KwStart => "start".to_string(),
            TokenKind::KwState => "state".to_string(),
            TokenKind::KwBreak => "break".to_string(),
            TokenKind::KwContinue => "continue".to_string(),
            TokenKind::KwReturn => "return".to_string(),
            _ => {
                return Err(Diagnostic::error(
                    ErrorCode::E0201,
                    format!("expected name, found '{}'", self.peek()),
                    span,
                ));
            }
        };
        self.advance();
        Ok((name, span))
    }

    // ── Program ──

    fn parse_program(&mut self) -> Result<Program, Diagnostic> {
        let mut game = None;
        let mut globals = Vec::new();
        let mut constants = Vec::new();
        let mut enums: Vec<EnumDecl> = Vec::new();
        let mut structs: Vec<StructDecl> = Vec::new();
        let mut functions = Vec::new();
        let mut states = Vec::new();
        let mut sprites = Vec::new();
        let mut palettes = Vec::new();
        let mut backgrounds = Vec::new();
        let mut metasprites = Vec::new();
        let mut metatilesets = Vec::new();
        let mut rooms = Vec::new();
        let mut sfx = Vec::new();
        let mut music = Vec::new();
        let mut saves: Vec<crate::parser::ast::VarDecl> = Vec::new();
        let mut banks = Vec::new();
        let mut start_state = None;
        let mut on_frame = None;
        let span = self.current_span();

        while *self.peek() != TokenKind::Eof {
            match self.peek().clone() {
                TokenKind::KwGame => {
                    game = Some(self.parse_game_decl()?);
                }
                TokenKind::KwFast | TokenKind::KwSlow => {
                    globals.push(self.parse_var_decl()?);
                }
                TokenKind::KwVar => {
                    globals.push(self.parse_var_decl()?);
                }
                TokenKind::KwFun | TokenKind::KwInline => {
                    functions.push(self.parse_fun_decl()?);
                }
                TokenKind::KwConst => {
                    constants.push(self.parse_const_decl()?);
                }
                TokenKind::KwEnum => {
                    enums.push(self.parse_enum_decl()?);
                }
                TokenKind::KwStruct => {
                    structs.push(self.parse_struct_decl()?);
                }
                TokenKind::KwState => {
                    states.push(self.parse_state_decl()?);
                }
                TokenKind::KwSprite => {
                    sprites.push(self.parse_sprite_decl()?);
                }
                TokenKind::KwMetasprite => {
                    metasprites.push(self.parse_metasprite_decl()?);
                }
                TokenKind::KwPalette => {
                    palettes.push(self.parse_palette_decl()?);
                }
                TokenKind::KwBackground => {
                    backgrounds.push(self.parse_background_decl()?);
                }
                TokenKind::KwMetatileset => {
                    metatilesets.push(self.parse_metatileset_decl()?);
                }
                TokenKind::KwRoom => {
                    rooms.push(self.parse_room_decl()?);
                }
                TokenKind::KwSfx => {
                    sfx.push(self.parse_sfx_decl()?);
                }
                TokenKind::KwMusic => {
                    music.push(self.parse_music_decl()?);
                }
                TokenKind::KwSave => {
                    // `save { var x: u8 = 0  var y: u16 = 100 }` —
                    // a block of variable declarations that the
                    // analyzer allocates at $6000+ (cartridge SRAM
                    // window) instead of main RAM. Parsed as a
                    // sequence of plain `VarDecl`s; the analyzer
                    // and ROM builder are what make them battery-
                    // backed.
                    self.advance();
                    self.expect(&TokenKind::LBrace)?;
                    while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
                        match self.peek().clone() {
                            TokenKind::KwVar | TokenKind::KwFast | TokenKind::KwSlow => {
                                saves.push(self.parse_var_decl()?);
                            }
                            other => {
                                return Err(Diagnostic::error(
                                    ErrorCode::E0201,
                                    format!(
                                        "expected `var` declaration inside `save {{ }}`, got `{other}`"
                                    ),
                                    self.current_span(),
                                ));
                            }
                        }
                    }
                    self.expect(&TokenKind::RBrace)?;
                }
                TokenKind::KwBank => {
                    let (bank, nested_funs) = self.parse_bank_decl()?;
                    banks.push(bank);
                    // Functions declared inside a `bank Foo { ... }`
                    // body land in the program's flat function list
                    // tagged with `bank: Some("Foo")`. The analyzer
                    // and the rest of the pipeline can then treat
                    // them uniformly while still knowing which bank
                    // each one belongs to.
                    functions.extend(nested_funs);
                }
                TokenKind::KwOn => {
                    // Top-level `on frame` — implicit single state for M1
                    on_frame = Some(self.parse_on_frame()?);
                }
                TokenKind::KwStart => {
                    let kw_span = self.current_span();
                    self.advance();
                    let (name, _) = self.expect_ident()?;
                    if start_state.is_some() {
                        return Err(Diagnostic::error(
                            ErrorCode::E0505,
                            "multiple 'start' declarations",
                            kw_span,
                        ));
                    }
                    start_state = Some(name);
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unexpected token '{}' at top level", self.peek()),
                        self.current_span(),
                    ));
                }
            }
        }

        let game = game.ok_or_else(|| {
            Diagnostic::error(ErrorCode::E0504, "missing 'game' declaration", span)
        })?;

        // If there's a top-level `on frame` but no explicit states,
        // wrap it in an implicit "Main" state
        if !states.is_empty() || on_frame.is_none() {
            // Multi-state or no frame handler — use states as-is
        } else if let Some(frame_block) = on_frame {
            states.push(StateDecl {
                name: "Main".to_string(),
                locals: Vec::new(),
                on_enter: None,
                on_exit: None,
                on_frame: Some(frame_block),
                on_scanline: Vec::new(),
                span,
            });
            if start_state.is_none() {
                start_state = Some("Main".to_string());
            }
        }

        let start_state = start_state.ok_or_else(|| {
            Diagnostic::error(ErrorCode::E0504, "missing 'start' declaration", span)
        })?;

        Ok(Program {
            game,
            globals,
            saves,
            constants,
            enums,
            structs,
            functions,
            states,
            sprites,
            palettes,
            backgrounds,
            metasprites,
            metatilesets,
            rooms,
            sfx,
            music,
            banks,
            start_state,
            span,
        })
    }

    fn parse_struct_decl(&mut self) -> Result<StructDecl, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwStruct)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LBrace)?;
        let mut fields = Vec::new();
        while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
            let field_span = self.current_span();
            let (field_name, _) = self.expect_ident()?;
            self.expect(&TokenKind::Colon)?;
            let field_type = self.parse_type()?;
            fields.push(StructField {
                name: field_name,
                field_type,
                span: field_span,
            });
            if *self.peek() == TokenKind::Comma {
                self.advance();
            } else if *self.peek() != TokenKind::RBrace {
                return Err(Diagnostic::error(
                    ErrorCode::E0201,
                    "expected ',' or '}' in struct body",
                    self.current_span(),
                ));
            }
        }
        self.expect(&TokenKind::RBrace)?;
        Ok(StructDecl {
            name,
            fields,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    fn parse_enum_decl(&mut self) -> Result<EnumDecl, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwEnum)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LBrace)?;
        let mut variants = Vec::new();
        while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
            let span = self.current_span();
            let (vname, _) = self.expect_ident()?;
            variants.push((vname, span));
            if *self.peek() == TokenKind::Comma {
                self.advance();
            } else if *self.peek() != TokenKind::RBrace {
                return Err(Diagnostic::error(
                    ErrorCode::E0201,
                    "expected ',' or '}' in enum body",
                    self.current_span(),
                ));
            }
        }
        self.expect(&TokenKind::RBrace)?;
        if variants.len() > 256 {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                "enum has more than 256 variants (u8 overflow)",
                start,
            ));
        }
        Ok(EnumDecl {
            name,
            variants,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    // ── Game declaration ──

    fn parse_game_decl(&mut self) -> Result<GameDecl, Diagnostic> {
        let start_span = self.current_span();
        self.expect(&TokenKind::KwGame)?;

        let name = if let TokenKind::StringLiteral(s) = self.peek().clone() {
            self.advance();
            s
        } else {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                "expected game name string",
                self.current_span(),
            ));
        };

        self.expect(&TokenKind::LBrace)?;

        let mut mapper = Mapper::NROM;
        let mut mirroring = Mirroring::Horizontal;
        let mut header = HeaderFormat::Ines1;
        // Default to the FCEUX `$4800` convention; programs
        // targeting Mesen can override to `$4018` via
        // `debug_port: mesen`.
        let mut debug_port: u16 = 0x4800;
        let mut sprite_flicker: bool = false;

        while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
            let (key, _) = self.expect_ident()?;
            self.expect(&TokenKind::Colon)?;
            match key.as_str() {
                "mapper" => {
                    let (val, _) = self.expect_ident()?;
                    mapper = match val.as_str() {
                        "NROM" => Mapper::NROM,
                        "MMC1" => Mapper::MMC1,
                        "UxROM" => Mapper::UxROM,
                        "MMC3" => Mapper::MMC3,
                        "AxROM" => Mapper::AxROM,
                        "CNROM" => Mapper::CNROM,
                        "GNROM" => Mapper::GNROM,
                        _ => {
                            return Err(Diagnostic::error(
                                ErrorCode::E0201,
                                format!("unknown mapper '{val}'"),
                                self.current_span(),
                            )
                            .with_help(
                                "supported mappers: NROM, MMC1, UxROM, MMC3, AxROM, CNROM, GNROM",
                            ));
                        }
                    };
                }
                "mirroring" => {
                    let (val, _) = self.expect_ident()?;
                    mirroring = match val.as_str() {
                        "horizontal" => Mirroring::Horizontal,
                        "vertical" => Mirroring::Vertical,
                        _ => {
                            return Err(Diagnostic::error(
                                ErrorCode::E0201,
                                format!("unknown mirroring '{val}'"),
                                self.current_span(),
                            ));
                        }
                    };
                }
                "header" => {
                    let (val, _) = self.expect_ident()?;
                    header = match val.as_str() {
                        "ines1" | "ines" => HeaderFormat::Ines1,
                        "nes2" => HeaderFormat::Nes2,
                        _ => {
                            return Err(Diagnostic::error(
                                ErrorCode::E0201,
                                format!("unknown header format '{val}'"),
                                self.current_span(),
                            )
                            .with_help("supported header formats: ines1, nes2"));
                        }
                    };
                }
                "sprite_flicker" => {
                    // The lexer emits `true` / `false` as
                    // `TokenKind::BoolLiteral` (not `Ident`), so
                    // match on the token rather than going through
                    // `expect_ident`.
                    match self.peek().clone() {
                        TokenKind::BoolLiteral(b) => {
                            self.advance();
                            sprite_flicker = b;
                        }
                        _ => {
                            return Err(Diagnostic::error(
                                ErrorCode::E0201,
                                "expected `true` or `false` for sprite_flicker",
                                self.current_span(),
                            ));
                        }
                    }
                }
                "debug_port" => {
                    // Accept either a named alias (`fceux`, `mesen`)
                    // or an integer literal for custom ports. The
                    // numeric path routes through the normal int
                    // literal parser so both decimal and `0x…`
                    // hex work.
                    match self.peek().clone() {
                        TokenKind::Ident(alias) => {
                            self.advance();
                            debug_port = match alias.as_str() {
                                "fceux" => 0x4800,
                                "mesen" => 0x4018,
                                _ => {
                                    return Err(Diagnostic::error(
                                        ErrorCode::E0201,
                                        format!("unknown debug port alias '{alias}'"),
                                        self.current_span(),
                                    )
                                    .with_help(
                                        "supported aliases: fceux ($4800), mesen ($4018); \
                                         or pass a numeric literal (e.g. `0x2FFF`)",
                                    ));
                                }
                            };
                        }
                        TokenKind::IntLiteral(n) => {
                            // IntLiteral is already a u16, so it
                            // can't exceed the 6502 address space —
                            // no range check needed.
                            self.advance();
                            debug_port = n;
                        }
                        _ => {
                            return Err(Diagnostic::error(
                                ErrorCode::E0201,
                                "expected an alias (`fceux`, `mesen`) or a numeric address",
                                self.current_span(),
                            ));
                        }
                    }
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unknown game property '{key}'"),
                        self.current_span(),
                    ));
                }
            }
        }
        self.expect(&TokenKind::RBrace)?;

        Ok(GameDecl {
            name,
            mapper,
            mirroring,
            header,
            debug_port,
            sprite_flicker,
            span: Span::new(
                start_span.file_id,
                start_span.start,
                self.current_span().end,
            ),
        })
    }

    // ── Variable declaration ──

    fn parse_var_decl(&mut self) -> Result<VarDecl, Diagnostic> {
        let start = self.current_span();
        let placement = match self.peek() {
            TokenKind::KwFast => {
                self.advance();
                Placement::Fast
            }
            TokenKind::KwSlow => {
                self.advance();
                Placement::Slow
            }
            _ => Placement::Auto,
        };
        self.expect(&TokenKind::KwVar)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::Colon)?;
        let var_type = self.parse_type()?;

        let init = if *self.peek() == TokenKind::Assign {
            self.advance();
            Some(self.parse_expr()?)
        } else {
            None
        };

        Ok(VarDecl {
            name,
            var_type,
            init,
            placement,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    // ── Const declaration ──

    fn parse_const_decl(&mut self) -> Result<ConstDecl, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwConst)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::Colon)?;
        let const_type = self.parse_type()?;
        self.expect(&TokenKind::Assign)?;
        let value = self.parse_expr()?;

        Ok(ConstDecl {
            name,
            const_type,
            value,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    // ── Function declaration ──

    fn parse_fun_decl(&mut self) -> Result<FunDecl, Diagnostic> {
        let start = self.current_span();
        let is_inline = if *self.peek() == TokenKind::KwInline {
            self.advance();
            true
        } else {
            false
        };
        self.expect(&TokenKind::KwFun)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LParen)?;

        let mut params = Vec::new();
        while *self.peek() != TokenKind::RParen && *self.peek() != TokenKind::Eof {
            let (pname, _) = self.expect_ident()?;
            self.expect(&TokenKind::Colon)?;
            let ptype = self.parse_type()?;
            params.push(Param {
                name: pname,
                param_type: ptype,
            });
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RParen)?;

        let return_type = if *self.peek() == TokenKind::Arrow {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        let body = self.parse_block()?;

        Ok(FunDecl {
            name,
            params,
            return_type,
            body,
            is_inline,
            // Bank tagging happens after the function is parsed —
            // top-level `fun` declarations leave it `None`, while
            // nested `bank Foo { fun bar() ... }` bodies overwrite
            // it to `Some("Foo")` on the way out of `parse_bank_decl`.
            bank: None,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    // ── State declaration ──

    fn parse_state_decl(&mut self) -> Result<StateDecl, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwState)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LBrace)?;

        let mut locals = Vec::new();
        let mut on_enter = None;
        let mut on_exit = None;
        let mut on_frame = None;
        let mut on_scanline: Vec<(u8, Block)> = Vec::new();

        while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
            match self.peek().clone() {
                TokenKind::KwFast | TokenKind::KwSlow | TokenKind::KwVar => {
                    locals.push(self.parse_var_decl()?);
                }
                TokenKind::KwOn => {
                    self.advance();
                    let (event, event_span) = self.expect_ident()?;
                    match event.as_str() {
                        "enter" => {
                            on_enter = Some(self.parse_block()?);
                        }
                        "exit" => {
                            on_exit = Some(self.parse_block()?);
                        }
                        "frame" => {
                            on_frame = Some(self.parse_block()?);
                        }
                        "scanline" => {
                            // Syntax: `on scanline(N) { ... }`
                            self.expect(&TokenKind::LParen)?;
                            let line = if let TokenKind::IntLiteral(v) = self.peek().clone() {
                                self.advance();
                                if v > 239 {
                                    return Err(Diagnostic::error(
                                        ErrorCode::E0201,
                                        format!("scanline value {v} out of range (0-239)"),
                                        self.current_span(),
                                    ));
                                }
                                v as u8
                            } else {
                                return Err(Diagnostic::error(
                                    ErrorCode::E0201,
                                    "expected integer scanline number",
                                    self.current_span(),
                                ));
                            };
                            self.expect(&TokenKind::RParen)?;
                            let body = self.parse_block()?;
                            on_scanline.push((line, body));
                        }
                        _ => {
                            return Err(Diagnostic::error(
                                ErrorCode::E0201,
                                format!("unknown event handler 'on {event}'"),
                                event_span,
                            ));
                        }
                    }
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unexpected token '{}' in state body", self.peek()),
                        self.current_span(),
                    ));
                }
            }
        }
        self.expect(&TokenKind::RBrace)?;

        Ok(StateDecl {
            name,
            locals,
            on_enter,
            on_exit,
            on_frame,
            on_scanline,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    // ── Bank declaration ──
    //
    // Two forms are accepted:
    //
    //   bank Foo: prg
    //   bank Foo: chr
    //
    //     The "type-only" form. Reserves a 16 KB switchable PRG slot
    //     or claims a CHR bank. No body — used to declare named slots
    //     that the linker pads with $FF and that user code can grow
    //     into later.
    //
    //   bank Foo { fun bar() { ... } fun baz() { ... } }
    //
    //     The "nested-decls" form. The body holds zero or more
    //     function declarations whose code lands inside the named
    //     PRG bank instead of the fixed bank. Functions declared
    //     here are pushed onto `Program.functions` like any other
    //     function but tagged with `bank: Some("Foo")` so the
    //     codegen + linker know where to put them.
    //
    //     The bank type is implicitly `prg` — there's no syntax for
    //     CHR-bank function nesting because CHR is data, not code.
    //     A bank declared this way can later be referenced from a
    //     fixed-bank function via a normal call expression; the
    //     codegen emits a trampoline in the fixed bank that switches
    //     banks and JSRs into the target.

    /// Parse one bank declaration. Returns the [`BankDecl`] and a
    /// vector of any function declarations nested inside the bank
    /// body (empty for the type-only form). The caller appends the
    /// nested functions to the program's flat function list, tagging
    /// each one with `bank: Some(name)` so the rest of the pipeline
    /// can treat them like any other function.
    fn parse_bank_decl(&mut self) -> Result<(BankDecl, Vec<FunDecl>), Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwBank)?;
        let (name, _) = self.expect_ident()?;
        // Disambiguate between the two forms based on the next token.
        // `:` introduces the bank type, `{` introduces a nested-decls
        // body. Anything else is a parse error.
        match self.peek() {
            TokenKind::Colon => {
                self.advance();
                let (type_str, _) = self.expect_ident()?;
                let bank_type = match type_str.as_str() {
                    "prg" => BankType::Prg,
                    "chr" => BankType::Chr,
                    _ => {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            format!("expected 'prg' or 'chr', found '{type_str}'"),
                            self.current_span(),
                        ));
                    }
                };
                Ok((
                    BankDecl {
                        name,
                        bank_type,
                        span: Span::new(start.file_id, start.start, self.current_span().end),
                    },
                    Vec::new(),
                ))
            }
            TokenKind::LBrace => {
                self.advance();
                let mut funs = Vec::new();
                while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
                    match self.peek() {
                        TokenKind::KwFun | TokenKind::KwInline => {
                            let mut fun = self.parse_fun_decl()?;
                            fun.bank = Some(name.clone());
                            funs.push(fun);
                        }
                        _ => {
                            return Err(Diagnostic::error(
                                ErrorCode::E0201,
                                format!(
                                    "unexpected token '{}' inside bank body; only function \
                                     declarations are supported",
                                    self.peek()
                                ),
                                self.current_span(),
                            ));
                        }
                    }
                }
                self.expect(&TokenKind::RBrace)?;
                Ok((
                    BankDecl {
                        name,
                        bank_type: BankType::Prg,
                        span: Span::new(start.file_id, start.start, self.current_span().end),
                    },
                    funs,
                ))
            }
            _ => Err(Diagnostic::error(
                ErrorCode::E0201,
                format!(
                    "expected ':' or '{{' after bank name, found '{}'",
                    self.peek()
                ),
                self.current_span(),
            )),
        }
    }

    // ── Top-level on frame ──

    fn parse_on_frame(&mut self) -> Result<Block, Diagnostic> {
        self.expect(&TokenKind::KwOn)?;
        let (event, _) = self.expect_ident()?;
        if event != "frame" {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                format!("expected 'frame' after 'on', found '{event}'"),
                self.current_span(),
            ));
        }
        self.parse_block()
    }

    // ── Sprite / Palette / Background declarations ──

    /// Sprite declarations accept one of two shapes:
    ///
    /// **Raw CHR bytes** — the original form, matching how CHR is
    /// stored on the cart:
    /// ```text
    /// sprite Heart {
    ///     chr: [0x66, 0xFF, 0xFF, 0xFF, 0x7E, 0x3C, 0x18, 0x00,
    ///           0x66, 0xFF, 0xFF, 0xFF, 0x7E, 0x3C, 0x18, 0x00]
    /// }
    /// // or from an external file:
    /// sprite Player { chr: @chr("assets/player.png") }
    /// ```
    ///
    /// **Pixel-art strings** — each string is one row of pixels, each
    /// character is one pixel's 2-bit palette index. Way easier to
    /// hand-author than hex:
    /// ```text
    /// sprite Arrow {
    ///     pixels: [
    ///         "...##...",
    ///         "...###..",
    ///         "########",
    ///         "########",
    ///         "########",
    ///         "########",
    ///         "...###..",
    ///         "...##..."
    ///     ]
    /// }
    /// ```
    ///
    /// Characters map to palette indices as follows:
    ///
    /// | Char(s)  | Index | Meaning                       |
    /// |----------|-------|-------------------------------|
    /// | `.` ` `  | 0     | transparent / background      |
    /// | `#` `1`  | 1     | sub-palette colour 1          |
    /// | `%` `2`  | 2     | sub-palette colour 2          |
    /// | `@` `3`  | 3     | sub-palette colour 3          |
    ///
    /// Rows must all be the same length, and both dimensions must be
    /// multiples of 8 (the NES tile size). Multi-tile sprites (16×8,
    /// 8×16, 16×16, …) are split into 8×8 tiles in row-major reading
    /// order so consecutive tile indices line up with what `draw`
    /// expects.
    fn parse_sprite_decl(&mut self) -> Result<SpriteDecl, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwSprite)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LBrace)?;

        let mut chr_source: Option<AssetSource> = None;

        while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
            let (key, key_span) = self.expect_ident()?;
            self.expect(&TokenKind::Colon)?;
            match key.as_str() {
                "chr" => {
                    if chr_source.is_some() {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            "sprite 'chr' and 'pixels' are mutually exclusive",
                            key_span,
                        ));
                    }
                    chr_source = Some(self.parse_asset_source()?);
                }
                "pixels" => {
                    if chr_source.is_some() {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            "sprite 'pixels' and 'chr' are mutually exclusive",
                            key_span,
                        ));
                    }
                    let bytes = self.parse_pixel_art(&name, key_span)?;
                    chr_source = Some(AssetSource::Inline(bytes));
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unknown sprite property '{key}'"),
                        self.current_span(),
                    ));
                }
            }
        }
        self.expect(&TokenKind::RBrace)?;

        let chr_source = chr_source.ok_or_else(|| {
            Diagnostic::error(
                ErrorCode::E0201,
                "sprite requires 'chr' or 'pixels' property",
                start,
            )
        })?;

        Ok(SpriteDecl {
            name,
            chr_source,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    /// Parse a `metasprite Name { sprite: ..., dx: [...], dy: [...],
    /// frame: [...] }` block. The body uses parallel byte arrays so
    /// the parser can reuse the existing [`Self::parse_byte_array`]
    /// helper for each one — the analyzer is responsible for
    /// asserting they're all the same length and that the named
    /// sprite exists.
    fn parse_metasprite_decl(&mut self) -> Result<MetaspriteDecl, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwMetasprite)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LBrace)?;

        let mut sprite_name: Option<String> = None;
        let mut dx: Option<Vec<u8>> = None;
        let mut dy: Option<Vec<u8>> = None;
        let mut frame: Option<Vec<u8>> = None;

        while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
            // Accept either a regular identifier or the `sprite`
            // keyword in the property-name position. We fall
            // through to the standard ident path for everything
            // else so misspellings still produce the usual
            // E0201 diagnostic.
            let (key, key_span) = if *self.peek() == TokenKind::KwSprite {
                let span = self.current_span();
                self.advance();
                ("sprite".to_string(), span)
            } else {
                self.expect_ident()?
            };
            self.expect(&TokenKind::Colon)?;
            match key.as_str() {
                "sprite" => {
                    let (sname, _) = self.expect_ident()?;
                    sprite_name = Some(sname);
                }
                "dx" => {
                    dx = Some(self.parse_byte_array("dx")?);
                }
                "dy" => {
                    dy = Some(self.parse_byte_array("dy")?);
                }
                "frame" => {
                    frame = Some(self.parse_byte_array("frame")?);
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unknown metasprite property '{key}'"),
                        key_span,
                    ));
                }
            }
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBrace)?;

        let sprite_name = sprite_name.ok_or_else(|| {
            Diagnostic::error(
                ErrorCode::E0201,
                format!("metasprite '{name}' is missing the required 'sprite:' property"),
                start,
            )
        })?;
        let dx = dx.ok_or_else(|| {
            Diagnostic::error(
                ErrorCode::E0201,
                format!("metasprite '{name}' is missing the required 'dx:' array"),
                start,
            )
        })?;
        let dy = dy.ok_or_else(|| {
            Diagnostic::error(
                ErrorCode::E0201,
                format!("metasprite '{name}' is missing the required 'dy:' array"),
                start,
            )
        })?;
        let frame = frame.ok_or_else(|| {
            Diagnostic::error(
                ErrorCode::E0201,
                format!("metasprite '{name}' is missing the required 'frame:' array"),
                start,
            )
        })?;

        Ok(MetaspriteDecl {
            name,
            sprite_name,
            dx,
            dy,
            frame,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    /// Parse `metatileset Name { metatiles: [{ id: N, tiles: [...],
    /// collide: true|false }, ...] }`. The body is a single
    /// `metatiles:` array of brace-delimited entries; each entry has
    /// the three fixed properties `id`, `tiles`, and `collide`. The
    /// analyzer enforces that each entry's `tiles:` array is exactly
    /// 4 bytes (top-left, top-right, bottom-left, bottom-right) and
    /// that the entries' IDs match their position in the array.
    fn parse_metatileset_decl(&mut self) -> Result<MetatilesetDecl, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwMetatileset)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LBrace)?;

        let mut metatiles: Option<Vec<MetatileEntry>> = None;

        while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
            let (key, key_span) = self.expect_ident()?;
            self.expect(&TokenKind::Colon)?;
            match key.as_str() {
                "metatiles" => {
                    metatiles = Some(self.parse_metatile_array()?);
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unknown metatileset property '{key}'"),
                        key_span,
                    ));
                }
            }
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBrace)?;

        let metatiles = metatiles.ok_or_else(|| {
            Diagnostic::error(
                ErrorCode::E0201,
                format!("metatileset '{name}' is missing the required 'metatiles:' array"),
                start,
            )
        })?;
        Ok(MetatilesetDecl {
            name,
            metatiles,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    /// Parse the body of a `metatileset` declaration's `metatiles:`
    /// array. Each entry is `{ id: N, tiles: [4 bytes], collide:
    /// true|false }`.
    fn parse_metatile_array(&mut self) -> Result<Vec<MetatileEntry>, Diagnostic> {
        self.expect(&TokenKind::LBracket)?;
        let mut out = Vec::new();
        while *self.peek() != TokenKind::RBracket && *self.peek() != TokenKind::Eof {
            let entry_start = self.current_span();
            self.expect(&TokenKind::LBrace)?;

            let mut id: Option<u8> = None;
            let mut tiles: Option<Vec<u8>> = None;
            let mut collide: Option<bool> = None;

            while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
                let (key, key_span) = self.expect_ident()?;
                self.expect(&TokenKind::Colon)?;
                match key.as_str() {
                    "id" => id = Some(self.parse_u8_literal("id")?),
                    "tiles" => tiles = Some(self.parse_byte_array("tiles")?),
                    "collide" => match self.peek().clone() {
                        TokenKind::BoolLiteral(b) => {
                            self.advance();
                            collide = Some(b);
                        }
                        other => {
                            return Err(Diagnostic::error(
                                ErrorCode::E0201,
                                format!("expected `true` or `false` for 'collide', got '{other}'"),
                                self.current_span(),
                            ));
                        }
                    },
                    _ => {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            format!("unknown metatile entry property '{key}'"),
                            key_span,
                        ));
                    }
                }
                if *self.peek() == TokenKind::Comma {
                    self.advance();
                }
            }
            self.expect(&TokenKind::RBrace)?;

            let id = id.ok_or_else(|| {
                Diagnostic::error(
                    ErrorCode::E0201,
                    "metatile entry is missing 'id'".to_string(),
                    entry_start,
                )
            })?;
            let tiles = tiles.ok_or_else(|| {
                Diagnostic::error(
                    ErrorCode::E0201,
                    "metatile entry is missing 'tiles'".to_string(),
                    entry_start,
                )
            })?;
            let collide = collide.unwrap_or(false);
            if tiles.len() != 4 {
                return Err(Diagnostic::error(
                    ErrorCode::E0201,
                    format!(
                        "metatile entry 'tiles' must have exactly 4 elements (TL,TR,BL,BR), got {}",
                        tiles.len()
                    ),
                    entry_start,
                ));
            }
            out.push(MetatileEntry {
                id,
                tiles: [tiles[0], tiles[1], tiles[2], tiles[3]],
                collide,
                span: entry_start,
            });
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(out)
    }

    /// Parse `room Name { metatileset: M, layout: [240 metatile ids] }`.
    /// Both properties are required. The analyzer enforces that the
    /// layout has exactly 240 entries (16 wide × 15 tall) and that
    /// every ID is defined by the named metatileset.
    fn parse_room_decl(&mut self) -> Result<RoomDecl, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwRoom)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LBrace)?;

        let mut metatileset: Option<String> = None;
        let mut layout: Option<Vec<u8>> = None;

        while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
            // Accept the `metatileset` keyword in the property-name
            // position so users can write the natural `metatileset:
            // MTS` form. Everything else falls through to the
            // standard identifier path.
            let (key, key_span) = if *self.peek() == TokenKind::KwMetatileset {
                let span = self.current_span();
                self.advance();
                ("metatileset".to_string(), span)
            } else {
                self.expect_ident()?
            };
            self.expect(&TokenKind::Colon)?;
            match key.as_str() {
                "metatileset" => {
                    let (mts_name, _) = self.expect_ident()?;
                    metatileset = Some(mts_name);
                }
                "layout" => {
                    layout = Some(self.parse_byte_array("layout")?);
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unknown room property '{key}'"),
                        key_span,
                    ));
                }
            }
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBrace)?;

        let metatileset = metatileset.ok_or_else(|| {
            Diagnostic::error(
                ErrorCode::E0201,
                format!("room '{name}' is missing the required 'metatileset:' property"),
                start,
            )
        })?;
        let layout = layout.ok_or_else(|| {
            Diagnostic::error(
                ErrorCode::E0201,
                format!("room '{name}' is missing the required 'layout:' array"),
                start,
            )
        })?;
        Ok(RoomDecl {
            name,
            metatileset,
            layout,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    /// Parse a pixel-art block of the form
    /// `[ "row0", "row1", ... ]` and lower it to CHR bytes.
    ///
    /// Each character is one pixel; see [`Self::parse_sprite_decl`]
    /// for the full character → palette-index mapping. All rows must
    /// be the same length and both dimensions must be multiples of 8.
    /// Multi-tile sprites are split into 8×8 tiles in row-major order
    /// so `tile_index, tile_index+1, ...` traverses the tiles in the
    /// same order your eye reads them.
    fn parse_pixel_art(
        &mut self,
        sprite_name: &str,
        key_span: Span,
    ) -> Result<Vec<u8>, Diagnostic> {
        self.expect(&TokenKind::LBracket)?;
        let mut rows: Vec<String> = Vec::new();
        while *self.peek() != TokenKind::RBracket && *self.peek() != TokenKind::Eof {
            match self.peek().clone() {
                TokenKind::StringLiteral(s) => {
                    self.advance();
                    rows.push(s);
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!(
                            "expected pixel row string in sprite '{sprite_name}', found '{}'",
                            self.peek()
                        ),
                        self.current_span(),
                    ));
                }
            }
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBracket)?;

        if rows.is_empty() {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                format!("sprite '{sprite_name}' 'pixels' list is empty"),
                key_span,
            ));
        }
        let width = rows[0].chars().count();
        for (i, row) in rows.iter().enumerate() {
            let len = row.chars().count();
            if len != width {
                return Err(Diagnostic::error(
                    ErrorCode::E0201,
                    format!(
                        "sprite '{sprite_name}' pixel row {i} has {len} cells but \
                         row 0 has {width}; every row must be the same width"
                    ),
                    key_span,
                ));
            }
        }
        let height = rows.len();
        if width == 0 || !width.is_multiple_of(8) {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                format!(
                    "sprite '{sprite_name}' width is {width}; must be a non-zero multiple of 8"
                ),
                key_span,
            ));
        }
        if !height.is_multiple_of(8) {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                format!("sprite '{sprite_name}' height is {height}; must be a multiple of 8"),
                key_span,
            ));
        }

        // Convert rows to a 2-bit palette-index grid.
        let mut grid: Vec<Vec<u8>> = Vec::with_capacity(height);
        for (ry, row) in rows.iter().enumerate() {
            let mut line = Vec::with_capacity(width);
            for (rx, ch) in row.chars().enumerate() {
                // Three vocabularies map to the same 0-3 index so
                // artists can use whichever feels natural:
                //   `. # % @` — shade-intensity glyphs (dense = hi)
                //   `0 1 2 3` — literal palette-index digits
                //   `. a b c` — letter form used by most NES tools
                let val = match ch {
                    '.' | ' ' | '0' => 0u8,
                    '#' | '1' | 'a' | 'A' => 1,
                    '%' | '2' | 'b' | 'B' => 2,
                    '@' | '3' | 'c' | 'C' => 3,
                    other => {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            format!(
                                "sprite '{sprite_name}' pixel at ({rx}, {ry}) has \
                                 invalid character '{other}'; use '.'/' '/'0' for \
                                 index 0, '#'/'1'/'a' for 1, '%'/'2'/'b' for 2, \
                                 '@'/'3'/'c' for 3"
                            ),
                            key_span,
                        ));
                    }
                };
                line.push(val);
            }
            grid.push(line);
        }

        // Encode into CHR tiles. Each 8×8 block becomes 16 bytes: the
        // first 8 are bit 0 of each pixel (bitplane 0), the next 8 are
        // bit 1 (bitplane 1). Tiles are emitted in row-major reading
        // order so consecutive tile indices match what you'd expect.
        let tiles_x = width / 8;
        let tiles_y = height / 8;
        let mut out = Vec::with_capacity(tiles_x * tiles_y * 16);
        for ty in 0..tiles_y {
            for tx in 0..tiles_x {
                let mut plane0 = [0u8; 8];
                let mut plane1 = [0u8; 8];
                for row_in_tile in 0..8 {
                    let y = ty * 8 + row_in_tile;
                    let mut p0 = 0u8;
                    let mut p1 = 0u8;
                    for col_in_tile in 0..8 {
                        let x = tx * 8 + col_in_tile;
                        let v = grid[y][x];
                        let shift = 7 - col_in_tile;
                        if v & 0b01 != 0 {
                            p0 |= 1 << shift;
                        }
                        if v & 0b10 != 0 {
                            p1 |= 1 << shift;
                        }
                    }
                    plane0[row_in_tile] = p0;
                    plane1[row_in_tile] = p1;
                }
                out.extend_from_slice(&plane0);
                out.extend_from_slice(&plane1);
            }
        }
        Ok(out)
    }

    // ── Palette / Background declarations ──

    /// `palette Name { colors: [c0, c1, ..., c31] }` — declares a
    /// 32-byte PPU palette. Colors shorter than 32 are zero-padded
    /// by the analyzer; colors longer than 32 are rejected.
    /// Palette declarations accept one of two shapes. They cannot be mixed:
    ///
    /// **Flat form** — a single 32-byte list matching the PPU layout:
    /// ```text
    /// palette Main {
    ///     colors: [0x0F, 0x01, 0x11, 0x21,  /* bg0..bg3, sp0..sp3 */ ...]
    /// }
    /// ```
    ///
    /// **Grouped form** — a per-slot declaration with an optional shared
    /// universal colour:
    /// ```text
    /// palette Main {
    ///     universal: black         // optional, defaults to black ($0F)
    ///     bg0: [dk_blue, blue, sky_blue]    // 3 colours — universal prepended
    ///     bg1: [dk_purple, purple, lavender]
    ///     bg2: [dk_red,    red,    peach]
    ///     bg3: [dk_green,  green,  mint]
    ///     sp0: [dk_blue,   blue,   sky_blue]
    ///     sp1: [dk_red,    red,    peach]
    ///     sp2: [dk_green,  green,  mint]
    ///     sp3: [dk_gray,   lt_gray, white]
    /// }
    /// ```
    ///
    /// Grouped form auto-fixes the `$3F10 / $3F14 / $3F18 / $3F1C` PPU
    /// mirror issue — every sub-palette's index-0 byte is forced to the
    /// same universal value, so sequential writes to
    /// `$3F00-$3F1F` never accidentally clobber the shared background
    /// colour.
    ///
    /// Any colour value (in either form) may be a raw byte literal
    /// (`0x0F`) or a named NES colour (`black`, `dk_blue`, `sky_blue`, …).
    /// See [`crate::assets::color_name_to_index`] for the full name list.
    fn parse_palette_decl(&mut self) -> Result<PaletteDecl, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwPalette)?;
        let (name, _) = self.expect_ident()?;

        // Shortcut form: `palette Name @palette("file.png")` — the PNG
        // is decoded at asset-resolve time into a 32-byte blob. No
        // `{ ... }` body follows. The in-source `@palette(...)` token
        // is distinct from the `palette` block keyword (they're
        // different TokenKinds); don't confuse them.
        if *self.peek() == TokenKind::At {
            let png_path = self.parse_named_asset_path("palette")?;
            return Ok(PaletteDecl {
                name,
                colors: Vec::new(),
                png_source: Some(png_path),
                span: Span::new(start.file_id, start.start, self.current_span().end),
            });
        }

        self.expect(&TokenKind::LBrace)?;

        // Flat-form output.
        let mut flat_colors: Option<Vec<u8>> = None;
        // Grouped-form scratch: 8 sub-palette slots, each up to 4
        // colours. `None` means "user didn't declare this slot".
        let mut slots: [Option<Vec<u8>>; 8] = Default::default();
        let mut universal: Option<u8> = None;
        let mut grouped_first_key: Option<Span> = None;

        while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
            let (key, key_span) = self.expect_ident()?;
            self.expect(&TokenKind::Colon)?;
            match key.as_str() {
                "colors" => {
                    if grouped_first_key.is_some() {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            "palette cannot mix 'colors' with grouped sub-palette \
                             fields (bg0..sp3 / universal); pick one form",
                            key_span,
                        ));
                    }
                    flat_colors = Some(self.parse_color_array("colors")?);
                }
                "universal" => {
                    if flat_colors.is_some() {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            "palette cannot mix 'colors' with 'universal'; pick one form",
                            key_span,
                        ));
                    }
                    grouped_first_key.get_or_insert(key_span);
                    universal = Some(self.parse_color_value("universal")?);
                }
                slot_name @ ("bg0" | "bg1" | "bg2" | "bg3" | "sp0" | "sp1" | "sp2" | "sp3") => {
                    if flat_colors.is_some() {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            format!(
                                "palette cannot mix 'colors' with '{slot_name}'; pick one form"
                            ),
                            key_span,
                        ));
                    }
                    grouped_first_key.get_or_insert(key_span);
                    let slot_idx = match slot_name {
                        "bg0" => 0,
                        "bg1" => 1,
                        "bg2" => 2,
                        "bg3" => 3,
                        "sp0" => 4,
                        "sp1" => 5,
                        "sp2" => 6,
                        "sp3" => 7,
                        _ => unreachable!(),
                    };
                    if slots[slot_idx].is_some() {
                        return Err(Diagnostic::error(
                            ErrorCode::E0501,
                            format!("duplicate sub-palette '{slot_name}'"),
                            key_span,
                        ));
                    }
                    let entries = self.parse_color_array(slot_name)?;
                    if entries.len() > 4 {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            format!(
                                "sub-palette '{slot_name}' has {} colours; maximum is 4 \
                                 (3 + optional leading universal override)",
                                entries.len()
                            ),
                            key_span,
                        ));
                    }
                    slots[slot_idx] = Some(entries);
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unknown palette property '{key}'"),
                        key_span,
                    ));
                }
            }
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBrace)?;

        let colors = if let Some(flat) = flat_colors {
            flat
        } else if grouped_first_key.is_some() {
            // Assemble the 32-byte blob from the grouped slots.
            // `$0F` is the canonical "one true black" universal that
            // every NES cart uses when nothing else is specified.
            let uni = universal.unwrap_or(0x0F);
            let mut out = vec![0u8; 32];
            for (slot_idx, slot) in slots.iter().enumerate() {
                let base = slot_idx * 4;
                out[base] = uni;
                if let Some(entries) = slot {
                    if entries.len() == 4 {
                        // Explicit override of the universal byte
                        // for this slot only.
                        out[base] = entries[0];
                        out[base + 1] = entries[1];
                        out[base + 2] = entries[2];
                        out[base + 3] = entries[3];
                    } else {
                        for (i, c) in entries.iter().enumerate() {
                            out[base + 1 + i] = *c;
                        }
                    }
                }
            }
            out
        } else {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                "palette requires either 'colors' or at least one sub-palette field \
                 (bg0..bg3 / sp0..sp3)",
                start,
            ));
        };

        Ok(PaletteDecl {
            name,
            colors,
            png_source: None,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    /// Parse a `@kind("path")` asset directive when the caller has
    /// already matched `@` at `self.peek()`. Verifies that `kind` is
    /// the expected identifier (e.g. `palette` or `nametable`) and
    /// returns the string literal inside the parentheses.
    ///
    /// Note: `palette` and `background` are reserved keywords in the
    /// lexer so `@palette` tokenises as `At` + `KwPalette` rather
    /// than `At` + `Ident("palette")`. We match both shapes so the
    /// directive kind can collide with a keyword without the user
    /// having to worry about it. `nametable` isn't a keyword today
    /// so it comes through as an `Ident`; if it ever becomes one,
    /// this branch will still work.
    fn parse_named_asset_path(&mut self, expected: &str) -> Result<String, Diagnostic> {
        self.expect(&TokenKind::At)?;
        let kind_span = self.current_span();
        let kind = match self.peek().clone() {
            TokenKind::Ident(name) => {
                self.advance();
                name
            }
            TokenKind::KwPalette => {
                self.advance();
                "palette".to_string()
            }
            TokenKind::KwBackground => {
                self.advance();
                "background".to_string()
            }
            other => {
                return Err(Diagnostic::error(
                    ErrorCode::E0201,
                    format!("expected '@{expected}(\"...\")', found '@{other}'"),
                    kind_span,
                ));
            }
        };
        if kind != expected {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                format!("expected '@{expected}(\"...\")', found '@{kind}'"),
                kind_span,
            ));
        }
        self.expect(&TokenKind::LParen)?;
        let path = if let TokenKind::StringLiteral(s) = self.peek().clone() {
            self.advance();
            s
        } else {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                format!(
                    "expected string path in '@{expected}(...)', found '{}'",
                    self.peek()
                ),
                self.current_span(),
            ));
        };
        self.expect(&TokenKind::RParen)?;
        Ok(path)
    }

    /// Parse a single NES colour value: either a `u8` integer literal or
    /// an identifier resolved via
    /// [`crate::assets::color_name_to_index`]. Used by palette
    /// declarations so either raw hex bytes (`0x0F`) or friendly names
    /// (`black`, `sky_blue`) can appear anywhere a colour is expected.
    fn parse_color_value(&mut self, prop: &str) -> Result<u8, Diagnostic> {
        match self.peek().clone() {
            TokenKind::IntLiteral(v) => {
                self.advance();
                if v > 0xFF {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("'{prop}' colour value {v} doesn't fit in a u8"),
                        self.current_span(),
                    ));
                }
                Ok(v as u8)
            }
            TokenKind::Ident(name) => {
                let span = self.current_span();
                self.advance();
                crate::assets::color_name_to_index(&name).ok_or_else(|| {
                    Diagnostic::error(
                        ErrorCode::E0201,
                        format!(
                            "unknown NES colour name '{name}' in '{prop}'; \
                             use a byte literal (0x00-0x3F) or a name like \
                             'black' / 'blue' / 'sky_blue'"
                        ),
                        span,
                    )
                })
            }
            _ => Err(Diagnostic::error(
                ErrorCode::E0201,
                format!(
                    "expected colour value for '{prop}' (byte literal or name), found '{}'",
                    self.peek()
                ),
                self.current_span(),
            )),
        }
    }

    /// Parse `[color, color, ...]` where each element is either a byte
    /// literal or a named NES colour. This is the "friendly" version of
    /// [`Self::parse_byte_array`] used everywhere a palette byte is
    /// expected.
    fn parse_color_array(&mut self, prop: &str) -> Result<Vec<u8>, Diagnostic> {
        self.expect(&TokenKind::LBracket)?;
        let mut out = Vec::new();
        while *self.peek() != TokenKind::RBracket && *self.peek() != TokenKind::Eof {
            out.push(self.parse_color_value(prop)?);
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(out)
    }

    /// Background declarations pick one of two authoring styles for
    /// the 32×30 nametable:
    ///
    /// **Raw bytes** — a flat list matching the PPU nametable layout,
    /// 960 tile indices in row-major order, optionally followed by a
    /// 64-byte attribute table:
    /// ```text
    /// background StageOne {
    ///     tiles: [0, 1, 2, 3, ...]
    ///     attributes: [0xFF, 0x55, ...]
    /// }
    /// ```
    ///
    /// **Tilemap + legend** — a legend mapping single characters to
    /// CHR tile indices, followed by a `map:` list-of-strings where
    /// each character is one cell of the nametable. Rows shorter than
    /// 32 cells are right-padded with tile 0; extra rows past row 30
    /// are an error. Optional `palette_map:` is a 16×15 grid of
    /// sub-palette indices `0`-`3`, one digit per 16×16 metatile,
    /// auto-packed into the 64-byte attribute table (no more hand-
    /// packing 2-bit pairs):
    /// ```text
    /// background StageOne {
    ///     legend {
    ///         '.': 0      // empty
    ///         '#': 1      // brick
    ///         'X': 2      // coin
    ///     }
    ///     map: [
    ///         "................................",
    ///         "................................",
    ///         "......##........##..............",
    ///         "....##..##....##..##............",
    ///         // ... up to 30 rows, 32 cells each
    ///     ]
    ///     palette_map: [
    ///         "0000000011110000",  // 16 metatile cols
    ///         "0000000011110000",
    ///         // ... up to 15 metatile rows
    ///     ]
    /// }
    /// ```
    fn parse_background_decl(&mut self) -> Result<BackgroundDecl, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwBackground)?;
        let (name, _) = self.expect_ident()?;

        // Shortcut form: `background Name @nametable("file.png")` —
        // the PNG is decoded at asset-resolve time into a 32×30 tile
        // map plus a 64-byte attribute table. No `{ ... }` body
        // follows.
        if *self.peek() == TokenKind::At {
            let png_path = self.parse_named_asset_path("nametable")?;
            return Ok(BackgroundDecl {
                name,
                tiles: Vec::new(),
                attributes: Vec::new(),
                png_source: Some(png_path),
                span: Span::new(start.file_id, start.start, self.current_span().end),
            });
        }

        self.expect(&TokenKind::LBrace)?;

        // Raw-form scratch.
        let mut tiles_raw: Option<Vec<u8>> = None;
        let mut attributes_raw: Option<Vec<u8>> = None;
        // Tilemap-form scratch.
        let mut legend: Option<std::collections::HashMap<char, u8>> = None;
        let mut legend_span: Option<Span> = None;
        let mut map_rows: Option<(Vec<String>, Span)> = None;
        let mut palette_rows: Option<(Vec<String>, Span)> = None;

        while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
            // `legend { ... }` uses a brace block rather than a
            // `key: value` pair, so detect it specially.
            if matches!(self.peek(), TokenKind::Ident(n) if n == "legend")
                && self.peek_at_offset(1) == Some(&TokenKind::LBrace)
            {
                let span = self.current_span();
                self.advance(); // `legend`
                self.advance(); // `{`
                let mut map: std::collections::HashMap<char, u8> = std::collections::HashMap::new();
                while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
                    let key_span = self.current_span();
                    let ch = match self.peek().clone() {
                        TokenKind::StringLiteral(s) => {
                            self.advance();
                            let mut chars = s.chars();
                            let c = chars.next().ok_or_else(|| {
                                Diagnostic::error(
                                    ErrorCode::E0201,
                                    "legend key must be a single character",
                                    key_span,
                                )
                            })?;
                            if chars.next().is_some() {
                                return Err(Diagnostic::error(
                                    ErrorCode::E0201,
                                    format!("legend key '{s}' has more than one character"),
                                    key_span,
                                ));
                            }
                            c
                        }
                        _ => {
                            return Err(Diagnostic::error(
                                ErrorCode::E0201,
                                format!(
                                    "expected string literal for legend key, found '{}'",
                                    self.peek()
                                ),
                                key_span,
                            ));
                        }
                    };
                    self.expect(&TokenKind::Colon)?;
                    let tile = self.parse_u8_literal("legend value")?;
                    if map.insert(ch, tile).is_some() {
                        return Err(Diagnostic::error(
                            ErrorCode::E0501,
                            format!("duplicate legend entry '{ch}'"),
                            key_span,
                        ));
                    }
                    if *self.peek() == TokenKind::Comma {
                        self.advance();
                    }
                }
                self.expect(&TokenKind::RBrace)?;
                if legend.is_some() {
                    return Err(Diagnostic::error(
                        ErrorCode::E0501,
                        "duplicate 'legend' block",
                        span,
                    ));
                }
                legend = Some(map);
                legend_span = Some(span);
                continue;
            }

            let (key, key_span) = self.expect_ident()?;
            self.expect(&TokenKind::Colon)?;
            match key.as_str() {
                "tiles" => {
                    if tiles_raw.is_some() || map_rows.is_some() {
                        return Err(Diagnostic::error(
                            ErrorCode::E0501,
                            "duplicate tile data in background declaration",
                            key_span,
                        ));
                    }
                    tiles_raw = Some(self.parse_byte_array("tiles")?);
                }
                "attributes" => {
                    if attributes_raw.is_some() || palette_rows.is_some() {
                        return Err(Diagnostic::error(
                            ErrorCode::E0501,
                            "duplicate attribute data in background declaration",
                            key_span,
                        ));
                    }
                    attributes_raw = Some(self.parse_byte_array("attributes")?);
                }
                "map" => {
                    if map_rows.is_some() || tiles_raw.is_some() {
                        return Err(Diagnostic::error(
                            ErrorCode::E0501,
                            "duplicate tile data in background declaration",
                            key_span,
                        ));
                    }
                    map_rows = Some((self.parse_string_array("map")?, key_span));
                }
                "palette_map" => {
                    if palette_rows.is_some() || attributes_raw.is_some() {
                        return Err(Diagnostic::error(
                            ErrorCode::E0501,
                            "duplicate attribute data in background declaration",
                            key_span,
                        ));
                    }
                    palette_rows = Some((self.parse_string_array("palette_map")?, key_span));
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unknown background property '{key}'"),
                        key_span,
                    ));
                }
            }
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBrace)?;

        // Resolve the tile source.
        let tiles = if let Some(flat) = tiles_raw {
            flat
        } else if let Some((rows, span)) = map_rows {
            let legend = legend.as_ref().ok_or_else(|| {
                Diagnostic::error(
                    ErrorCode::E0201,
                    "background 'map' requires a 'legend { ... }' block",
                    legend_span.unwrap_or(span),
                )
            })?;
            tilemap_to_bytes(&name, &rows, legend, span)?
        } else {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                "background requires a 'tiles' array or a 'map' + 'legend'",
                start,
            ));
        };

        // Resolve the attribute source.
        let attributes = if let Some(flat) = attributes_raw {
            flat
        } else if let Some((rows, span)) = palette_rows {
            palette_map_to_attrs(&name, &rows, span)?
        } else {
            Vec::new()
        };

        Ok(BackgroundDecl {
            name,
            tiles,
            attributes,
            png_source: None,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    /// Parse a `[string, string, ...]` list. Used by background
    /// `map:` and `palette_map:` where each string is one row of the
    /// grid and characters inside the string are cells.
    fn parse_string_array(&mut self, prop: &str) -> Result<Vec<String>, Diagnostic> {
        self.expect(&TokenKind::LBracket)?;
        let mut out = Vec::new();
        while *self.peek() != TokenKind::RBracket && *self.peek() != TokenKind::Eof {
            match self.peek().clone() {
                TokenKind::StringLiteral(s) => {
                    self.advance();
                    out.push(s);
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("expected string row in '{prop}', found '{}'", self.peek()),
                        self.current_span(),
                    ));
                }
            }
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(out)
    }

    // ── SFX / Music declarations ──

    /// `sfx Name { duty: N, pitch: ..., volume: [..] }`.
    ///
    /// The v1 audio driver latches the pulse-1 period **once** on
    /// trigger, so there's no point giving a per-frame pitch array —
    /// only `pitch[0]` is ever read. That's now reflected in the
    /// syntax:
    ///
    /// - `pitch: 0x50` — a single byte, latched at trigger time (the
    ///   natural form for the current driver).
    /// - `pitch: [0x50, 0x50, ...]` — still accepted for
    ///   backwards-compatibility with existing sources; the analyzer
    ///   requires the array length to match `volume`.
    ///
    /// `envelope:` is a friendlier alias for `volume:` — both mean the
    /// same thing (the per-frame volume ramp that shapes the sound).
    fn parse_sfx_decl(&mut self) -> Result<SfxDecl, Diagnostic> {
        // Scalar pitches expand to a per-frame array once we know
        // the envelope length, so we track both possibilities in
        // this local enum while parsing. Declared here so clippy's
        // `items_after_statements` stays happy.
        enum PitchSrc {
            Scalar(u8),
            Array(Vec<u8>),
        }

        let start = self.current_span();
        self.expect(&TokenKind::KwSfx)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LBrace)?;

        let mut duty: u8 = 2;
        let mut pitch_src: Option<PitchSrc> = None;
        let mut volume: Option<Vec<u8>> = None;
        let mut volume_key: &'static str = "volume";
        let mut channel: Channel = Channel::Pulse1;

        while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
            let (key, key_span) = self.expect_ident()?;
            self.expect(&TokenKind::Colon)?;
            match key.as_str() {
                "channel" => {
                    // `channel: pulse1 | pulse2 | triangle | noise`.
                    // Identifiers (not keywords) so the lexer passes
                    // them through as `Ident`.
                    let (ch_name, ch_span) = self.expect_ident()?;
                    channel = match ch_name.as_str() {
                        "pulse1" | "pulse" => Channel::Pulse1,
                        "pulse2" => Channel::Pulse2,
                        "triangle" => Channel::Triangle,
                        "noise" => Channel::Noise,
                        _ => {
                            return Err(Diagnostic::error(
                                ErrorCode::E0201,
                                format!(
                                    "unknown sfx channel '{ch_name}' \
                                     (expected pulse1, pulse2, triangle, or noise)"
                                ),
                                ch_span,
                            ));
                        }
                    };
                }
                "duty" => {
                    duty = self.parse_u8_literal("duty")?;
                    if duty > 3 {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            format!("sfx 'duty' must be 0-3, got {duty}"),
                            key_span,
                        ));
                    }
                }
                "pitch" => {
                    // Either a scalar (new form) or a [bytes] array
                    // (legacy form). Branch on the leading token.
                    if *self.peek() == TokenKind::LBracket {
                        pitch_src = Some(PitchSrc::Array(self.parse_byte_array("pitch")?));
                    } else {
                        pitch_src = Some(PitchSrc::Scalar(self.parse_u8_literal("pitch")?));
                    }
                }
                "volume" | "envelope" => {
                    if volume.is_some() {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            "sfx 'volume' / 'envelope' are aliases — pick one",
                            key_span,
                        ));
                    }
                    // Remember which spelling the user chose so
                    // diagnostics below match their source.
                    let prop = if key.as_str() == "envelope" {
                        "envelope"
                    } else {
                        "volume"
                    };
                    volume_key = prop;
                    let vals = self.parse_byte_array(prop)?;
                    for v in &vals {
                        if *v > 15 {
                            return Err(Diagnostic::error(
                                ErrorCode::E0201,
                                format!("sfx '{prop}' entries must be 0-15, got {v}"),
                                key_span,
                            ));
                        }
                    }
                    volume = Some(vals);
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unknown sfx property '{key}'"),
                        key_span,
                    ));
                }
            }
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBrace)?;

        let pitch_src = pitch_src.ok_or_else(|| {
            Diagnostic::error(ErrorCode::E0201, "sfx requires 'pitch' property", start)
        })?;
        let volume = volume.ok_or_else(|| {
            Diagnostic::error(
                ErrorCode::E0201,
                format!("sfx requires '{volume_key}' property (or its alias)"),
                start,
            )
        })?;

        if volume.is_empty() {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                format!("sfx '{volume_key}' array must have at least one frame"),
                start,
            ));
        }

        // Normalize to the legacy per-frame pitch array the rest of
        // the compiler already consumes. Scalar pitches just repeat.
        let pitch = match pitch_src {
            PitchSrc::Scalar(v) => vec![v; volume.len()],
            PitchSrc::Array(v) => {
                if v.is_empty() {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        "sfx 'pitch' array must have at least one frame",
                        start,
                    ));
                }
                if v.len() != volume.len() {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!(
                            "sfx 'pitch' and '{volume_key}' arrays must have the \
                             same length (pitch has {}, {volume_key} has {})",
                            v.len(),
                            volume.len()
                        ),
                        start,
                    ));
                }
                v
            }
        };

        Ok(SfxDecl {
            name,
            duty,
            pitch,
            volume,
            channel,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    /// `music Name { duty, volume, repeat, tempo, notes }`.
    ///
    /// Notes can be authored in two styles. The parser picks the style
    /// based on whether a `tempo:` field is present:
    ///
    /// **Raw form** (`tempo:` absent) — a flat list of `pitch, duration`
    /// integer pairs. Every entry is a `u8` literal and pairs are
    /// separated by commas:
    /// ```text
    /// music Theme {
    ///     notes: [
    ///         37, 20,    // C4 for 20 frames
    ///         41, 20,    // E4
    ///         44, 20,    // G4
    ///         0, 10,     // rest for 10 frames
    ///     ]
    /// }
    /// ```
    ///
    /// **Note-name form** (`tempo:` present) — each entry is a note
    /// name (`C4`, `Cs4`, `Db4`, …, `B5`) or `rest`, with an optional
    /// per-note duration override. Entries are separated by commas,
    /// and `tempo:` sets the default duration when none is given:
    /// ```text
    /// music Theme {
    ///     tempo: 20             // default frames per note
    ///     notes: [
    ///         C4, E4, G4, C5,   // all use tempo (20 frames each)
    ///         G4 40,            // this one is held twice as long
    ///         rest 10,          // short rest
    ///         E4, C4
    ///     ]
    /// }
    /// ```
    ///
    /// Integer literals still work inside the note-name form too —
    /// useful for raw period-table indices when you don't feel like
    /// spelling out a name.
    fn parse_music_decl(&mut self) -> Result<MusicDecl, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwMusic)?;
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LBrace)?;

        let mut duty: u8 = 2;
        let mut volume: u8 = 10;
        let mut loops: bool = true;
        let mut tempo: Option<u8> = None;
        // Defer note parsing until we've seen all the simple scalar
        // fields, so `tempo:` can be declared after `notes:` if the
        // user prefers that order — we stash the token position to
        // rewind to.
        let mut notes_pos: Option<(usize, Span)> = None;

        while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
            let (key, key_span) = self.expect_ident()?;
            self.expect(&TokenKind::Colon)?;
            match key.as_str() {
                "duty" => {
                    duty = self.parse_u8_literal("duty")?;
                    if duty > 3 {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            format!("music 'duty' must be 0-3, got {duty}"),
                            key_span,
                        ));
                    }
                }
                "volume" => {
                    volume = self.parse_u8_literal("volume")?;
                    if volume > 15 {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            format!("music 'volume' must be 0-15, got {volume}"),
                            key_span,
                        ));
                    }
                }
                "tempo" => {
                    let t = self.parse_u8_literal("tempo")?;
                    if t == 0 {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            "music 'tempo' must be >= 1 (frames per note)",
                            key_span,
                        ));
                    }
                    tempo = Some(t);
                }
                "repeat" => match self.peek().clone() {
                    TokenKind::BoolLiteral(b) => {
                        self.advance();
                        loops = b;
                    }
                    _ => {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            format!("expected bool for 'repeat', got '{}'", self.peek()),
                            key_span,
                        ));
                    }
                },
                "notes" => {
                    if notes_pos.is_some() {
                        return Err(Diagnostic::error(
                            ErrorCode::E0501,
                            "duplicate 'notes' in music declaration",
                            key_span,
                        ));
                    }
                    notes_pos = Some((self.pos, key_span));
                    // Skip past the notes list without parsing it yet
                    // — we need to know whether `tempo:` is set before
                    // picking between raw-pair form and note-name form.
                    self.skip_balanced_brackets()?;
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unknown music property '{key}'"),
                        key_span,
                    ));
                }
            }
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBrace)?;

        let (notes_token_pos, notes_span) = notes_pos.ok_or_else(|| {
            Diagnostic::error(ErrorCode::E0201, "music requires 'notes' property", start)
        })?;

        // Rewind to the `[` of the notes list and parse it with the
        // right format chosen by whether `tempo:` was set above.
        let saved_pos = self.pos;
        self.pos = notes_token_pos;
        let notes = if let Some(default_dur) = tempo {
            self.parse_named_notes(default_dur, notes_span)?
        } else {
            self.parse_flat_note_pairs(notes_span)?
        };
        // Restore the cursor past the closing brace so the outer
        // program loop keeps marching through the source.
        self.pos = saved_pos;

        if notes.is_empty() {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                "music 'notes' must contain at least one note",
                start,
            ));
        }

        Ok(MusicDecl {
            name,
            duty,
            volume,
            loops,
            notes,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    /// Fast-forward `self.pos` past a matched `[` … `]` pair, used by
    /// music parsing so the notes list can be re-scanned later once
    /// `tempo:` presence is known.
    fn skip_balanced_brackets(&mut self) -> Result<(), Diagnostic> {
        self.expect(&TokenKind::LBracket)?;
        let mut depth = 1i32;
        while depth > 0 {
            match self.peek().clone() {
                TokenKind::LBracket => {
                    depth += 1;
                    self.advance();
                }
                TokenKind::RBracket => {
                    depth -= 1;
                    self.advance();
                }
                TokenKind::Eof => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        "unterminated '[' in music notes",
                        self.current_span(),
                    ));
                }
                _ => {
                    self.advance();
                }
            }
        }
        Ok(())
    }

    /// Parse a legacy-form `notes: [pitch, duration, pitch, duration, ...]`
    /// flat pair list. Used when the music block has no `tempo:` field.
    fn parse_flat_note_pairs(&mut self, key_span: Span) -> Result<Vec<MusicNote>, Diagnostic> {
        let flat = self.parse_byte_array("notes")?;
        if flat.len() % 2 != 0 {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                "music 'notes' must have an even number of entries \
                 (pitch, duration, pitch, duration, ...) when 'tempo' is not set",
                key_span,
            ));
        }
        let mut out = Vec::with_capacity(flat.len() / 2);
        for pair in flat.chunks(2) {
            let pitch = pair[0];
            let duration = pair[1];
            if duration == 0 {
                return Err(Diagnostic::error(
                    ErrorCode::E0201,
                    "music note duration must be >= 1",
                    key_span,
                ));
            }
            if pitch > 60 {
                return Err(Diagnostic::error(
                    ErrorCode::E0201,
                    format!("music note pitch must be 0 (rest) or 1-60, got {pitch}"),
                    key_span,
                ));
            }
            out.push(MusicNote { pitch, duration });
        }
        Ok(out)
    }

    /// Parse a note-name form note list with entries like
    /// `C4`, `Cs4 40`, `rest`, `rest 10`. Each entry is a pitch
    /// (note-name identifier, `rest`, or integer literal) with an
    /// optional inline duration; missing durations default to `tempo`.
    /// Entries are comma-separated; trailing commas are allowed.
    fn parse_named_notes(
        &mut self,
        default_dur: u8,
        key_span: Span,
    ) -> Result<Vec<MusicNote>, Diagnostic> {
        self.expect(&TokenKind::LBracket)?;
        let mut out = Vec::new();
        while *self.peek() != TokenKind::RBracket && *self.peek() != TokenKind::Eof {
            // ── Parse the pitch ──
            let pitch = match self.peek().clone() {
                TokenKind::IntLiteral(v) => {
                    self.advance();
                    if v > 60 {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            format!("music note pitch must be 0 (rest) or 1-60, got {v}"),
                            key_span,
                        ));
                    }
                    v as u8
                }
                TokenKind::Ident(name) => {
                    let span = self.current_span();
                    self.advance();
                    crate::assets::note_name_to_index(&name).ok_or_else(|| {
                        Diagnostic::error(
                            ErrorCode::E0201,
                            format!(
                                "unknown note name '{name}'; use a name like C4/Cs4/Db4, \
                                 'rest', or a numeric pitch index 0-60"
                            ),
                            span,
                        )
                    })?
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!(
                            "expected note name or pitch index in music notes, found '{}'",
                            self.peek()
                        ),
                        self.current_span(),
                    ));
                }
            };

            // ── Optional duration override ──
            //
            // A bare integer literal before the next comma is the
            // duration for this note. Otherwise use the block's tempo.
            let duration = if let TokenKind::IntLiteral(v) = self.peek().clone() {
                self.advance();
                if v == 0 {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        "music note duration must be >= 1",
                        key_span,
                    ));
                }
                if v > 255 {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("music note duration {v} doesn't fit in a u8 (max 255)"),
                        key_span,
                    ));
                }
                v as u8
            } else {
                default_dur
            };

            out.push(MusicNote { pitch, duration });

            // Entries are comma-separated; trailing commas are fine.
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(out)
    }

    /// Parse a `[byte, byte, ...]` array. Used by sfx/music property
    /// parsing — the main `parse_asset_source` also does this, but
    /// without the array-literal-only restriction we want here.
    ///
    /// Also accepts the repetition shortcut `[value; count]` as a
    /// convenience for large arrays — room layouts (240 entries)
    /// and similar constant-fill blobs get unwieldy to spell out
    /// one byte at a time. `count` must be a u16 literal; `value`
    /// must be a u8 literal. This matches Rust's `[v; n]` form so
    /// the semantics should feel familiar.
    fn parse_byte_array(&mut self, prop: &str) -> Result<Vec<u8>, Diagnostic> {
        self.expect(&TokenKind::LBracket)?;
        let mut out = Vec::new();
        while *self.peek() != TokenKind::RBracket && *self.peek() != TokenKind::Eof {
            if let TokenKind::IntLiteral(v) = self.peek().clone() {
                self.advance();
                if v > 0xFF {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("'{prop}' entries must fit in a u8, got {v}"),
                        self.current_span(),
                    ));
                }
                // `[value; count]` repetition form. Only legal as
                // the first (and only) element; entries + `;` in
                // the same array don't compose.
                if *self.peek() == TokenKind::Semicolon && out.is_empty() {
                    self.advance();
                    let count_span = self.current_span();
                    let count = match self.peek().clone() {
                        TokenKind::IntLiteral(c) => {
                            self.advance();
                            c
                        }
                        other => {
                            return Err(Diagnostic::error(
                                ErrorCode::E0201,
                                format!("expected repetition count in '{prop}', found '{other}'"),
                                count_span,
                            ));
                        }
                    };
                    self.expect(&TokenKind::RBracket)?;
                    return Ok(vec![v as u8; count as usize]);
                }
                out.push(v as u8);
            } else {
                return Err(Diagnostic::error(
                    ErrorCode::E0201,
                    format!("expected byte value in '{prop}', found '{}'", self.peek()),
                    self.current_span(),
                ));
            }
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(out)
    }

    /// Parse a single u8 integer literal for a scalar property.
    fn parse_u8_literal(&mut self, prop: &str) -> Result<u8, Diagnostic> {
        match self.peek().clone() {
            TokenKind::IntLiteral(v) => {
                self.advance();
                if v > 0xFF {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("'{prop}' must fit in a u8, got {v}"),
                        self.current_span(),
                    ));
                }
                Ok(v as u8)
            }
            other => Err(Diagnostic::error(
                ErrorCode::E0201,
                format!("expected integer for '{prop}', got '{other}'"),
                self.current_span(),
            )),
        }
    }

    fn parse_asset_source(&mut self) -> Result<AssetSource, Diagnostic> {
        match self.peek() {
            TokenKind::At => {
                self.advance(); // consume '@'
                let (kind, _) = self.expect_ident()?;
                self.expect(&TokenKind::LParen)?;
                let path = if let TokenKind::StringLiteral(s) = self.peek().clone() {
                    self.advance();
                    s
                } else {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("expected string path, found '{}'", self.peek()),
                        self.current_span(),
                    ));
                };
                self.expect(&TokenKind::RParen)?;
                match kind.as_str() {
                    "chr" => Ok(AssetSource::Chr(path)),
                    "binary" => Ok(AssetSource::Binary(path)),
                    _ => Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unknown asset source kind '@{kind}'"),
                        self.current_span(),
                    )),
                }
            }
            TokenKind::LBracket => {
                self.advance();
                let mut bytes = Vec::new();
                while *self.peek() != TokenKind::RBracket && *self.peek() != TokenKind::Eof {
                    if let TokenKind::IntLiteral(v) = self.peek().clone() {
                        self.advance();
                        bytes.push(v as u8);
                    } else {
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            format!("expected byte value, found '{}'", self.peek()),
                            self.current_span(),
                        ));
                    }
                    if *self.peek() == TokenKind::Comma {
                        self.advance();
                    }
                }
                self.expect(&TokenKind::RBracket)?;
                Ok(AssetSource::Inline(bytes))
            }
            _ => Err(Diagnostic::error(
                ErrorCode::E0201,
                format!(
                    "expected asset source (@chr, @binary, or [...]), found '{}'",
                    self.peek()
                ),
                self.current_span(),
            )),
        }
    }

    // ── Block ──

    fn parse_block(&mut self) -> Result<Block, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::LBrace)?;

        let mut statements = Vec::new();
        while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
            statements.push(self.parse_statement()?);
            // Allow optional `;` between statements for readability.
            // Newlines are still the primary separator, but `;` lets
            // users put short statements on the same line:
            //   `x += 1; y += 1`
            while *self.peek() == TokenKind::Semicolon {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBrace)?;

        Ok(Block {
            statements,
            span: Span::new(start.file_id, start.start, self.current_span().end),
        })
    }

    // ── Statements ──

    fn parse_statement(&mut self) -> Result<Statement, Diagnostic> {
        match self.peek().clone() {
            TokenKind::KwFast | TokenKind::KwSlow | TokenKind::KwVar => {
                let decl = self.parse_var_decl()?;
                Ok(Statement::VarDecl(decl))
            }
            TokenKind::KwIf => self.parse_if(),
            TokenKind::KwWhile => self.parse_while(),
            TokenKind::KwFor => self.parse_for(),
            TokenKind::KwMatch => self.parse_match(),
            TokenKind::KwLoop => self.parse_loop(),
            TokenKind::KwBreak => {
                let span = self.current_span();
                self.advance();
                Ok(Statement::Break(span))
            }
            TokenKind::KwContinue => {
                let span = self.current_span();
                self.advance();
                Ok(Statement::Continue(span))
            }
            TokenKind::KwReturn => {
                let span = self.current_span();
                self.advance();
                let value = if *self.peek() == TokenKind::RBrace {
                    None
                } else {
                    Some(self.parse_expr()?)
                };
                Ok(Statement::Return(value, span))
            }
            TokenKind::KwDraw => self.parse_draw(),
            TokenKind::KwTransition => {
                let span = self.current_span();
                self.advance();
                let (name, _) = self.expect_ident()?;
                Ok(Statement::Transition(name, span))
            }
            TokenKind::KwWaitFrame => {
                let span = self.current_span();
                self.advance();
                Ok(Statement::WaitFrame(span))
            }
            TokenKind::KwCycleSprites => {
                let span = self.current_span();
                self.advance();
                Ok(Statement::CycleSprites(span))
            }
            TokenKind::KwLoadBackground => {
                let span = self.current_span();
                self.advance();
                let (name, _) = self.expect_ident()?;
                Ok(Statement::LoadBackground(name, span))
            }
            TokenKind::KwPaintRoom => {
                let span = self.current_span();
                self.advance();
                let (name, _) = self.expect_ident()?;
                Ok(Statement::PaintRoom(name, span))
            }
            TokenKind::KwSetPalette => {
                let span = self.current_span();
                self.advance();
                let (name, _) = self.expect_ident()?;
                Ok(Statement::SetPalette(name, span))
            }
            TokenKind::KwScroll => {
                let span = self.current_span();
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let x = self.parse_expr()?;
                self.expect(&TokenKind::Comma)?;
                let y = self.parse_expr()?;
                self.expect(&TokenKind::RParen)?;
                Ok(Statement::Scroll(x, y, span))
            }
            TokenKind::KwDebug => self.parse_debug_statement(),
            TokenKind::KwPlay => {
                let span = self.current_span();
                self.advance();
                let (name, _) = self.expect_ident()?;
                Ok(Statement::Play(name, span))
            }
            TokenKind::KwStartMusic => {
                let span = self.current_span();
                self.advance();
                let (name, _) = self.expect_ident()?;
                Ok(Statement::StartMusic(name, span))
            }
            TokenKind::KwStopMusic => {
                let span = self.current_span();
                self.advance();
                Ok(Statement::StopMusic(span))
            }
            TokenKind::KwAsm => {
                let span = self.current_span();
                self.advance(); // KwAsm
                                // The lexer emits an AsmBody token after `asm` when it
                                // sees the opening brace. Consume it here.
                if let TokenKind::AsmBody(body) = self.peek().clone() {
                    self.advance();
                    Ok(Statement::InlineAsm(body, span))
                } else {
                    Err(Diagnostic::error(
                        ErrorCode::E0201,
                        "expected `{` after `asm`",
                        self.current_span(),
                    ))
                }
            }
            TokenKind::KwRaw => {
                // `raw asm { ... }` — verbatim bytes, no `{var}`
                // substitution.
                let span = self.current_span();
                self.advance(); // KwRaw
                self.expect(&TokenKind::KwAsm)?;
                if let TokenKind::AsmBody(body) = self.peek().clone() {
                    self.advance();
                    Ok(Statement::RawAsm(body, span))
                } else {
                    Err(Diagnostic::error(
                        ErrorCode::E0201,
                        "expected `{` after `raw asm`",
                        self.current_span(),
                    ))
                }
            }
            TokenKind::Ident(_) => self.parse_assign_or_call(),
            _ => Err(Diagnostic::error(
                ErrorCode::E0201,
                format!("unexpected token '{}' in statement position", self.peek()),
                self.current_span(),
            )),
        }
    }

    fn parse_if(&mut self) -> Result<Statement, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwIf)?;
        let saved = self.restrict_struct_literals;
        self.restrict_struct_literals = true;
        let condition = self.parse_expr()?;
        self.restrict_struct_literals = saved;
        let then_block = self.parse_block()?;

        let mut else_ifs = Vec::new();
        let mut else_block = None;

        while *self.peek() == TokenKind::KwElse {
            self.advance();
            if *self.peek() == TokenKind::KwIf {
                self.advance();
                self.restrict_struct_literals = true;
                let cond = self.parse_expr()?;
                self.restrict_struct_literals = saved;
                let block = self.parse_block()?;
                else_ifs.push((cond, block));
            } else {
                else_block = Some(self.parse_block()?);
                break;
            }
        }

        Ok(Statement::If(
            condition, then_block, else_ifs, else_block, start,
        ))
    }

    fn parse_while(&mut self) -> Result<Statement, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwWhile)?;
        let saved = self.restrict_struct_literals;
        self.restrict_struct_literals = true;
        let condition = self.parse_expr()?;
        self.restrict_struct_literals = saved;
        let body = self.parse_block()?;
        Ok(Statement::While(condition, body, start))
    }

    fn parse_loop(&mut self) -> Result<Statement, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwLoop)?;
        let body = self.parse_block()?;
        Ok(Statement::Loop(body, start))
    }

    /// Parse `match expr { pat => { body }, pat => { body }, _ => { body } }`.
    /// Desugars to a chain of `if expr == pat { body } else if ...`
    /// at parse time — no dedicated AST variant needed.
    fn parse_match(&mut self) -> Result<Statement, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwMatch)?;
        let saved = self.restrict_struct_literals;
        self.restrict_struct_literals = true;
        let scrutinee = self.parse_expr()?;
        self.restrict_struct_literals = saved;
        self.expect(&TokenKind::LBrace)?;

        let mut arms: Vec<(Expr, Block)> = Vec::new();
        let mut default: Option<Block> = None;
        while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
            // A default arm is `_ => { ... }`.
            if let TokenKind::Ident(name) = self.peek().clone() {
                if name == "_" {
                    self.advance();
                    self.expect(&TokenKind::FatArrow)?;
                    let body = self.parse_block()?;
                    default = Some(body);
                    if *self.peek() == TokenKind::Comma {
                        self.advance();
                    }
                    continue;
                }
            }
            let pat_span = self.current_span();
            let pat = self.parse_expr()?;
            self.expect(&TokenKind::FatArrow)?;
            let body = self.parse_block()?;
            // Build `scrutinee == pat` as the branch condition.
            let cond = Expr::BinaryOp(
                Box::new(scrutinee.clone()),
                BinOp::Eq,
                Box::new(pat),
                pat_span,
            );
            arms.push((cond, body));
            if *self.peek() == TokenKind::Comma {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBrace)?;

        if arms.is_empty() {
            // `match x { _ => body }` or empty match — emit the
            // default block directly, or an empty no-op.
            if let Some(body) = default {
                return Ok(Statement::If(
                    Expr::BoolLiteral(true, start),
                    body,
                    Vec::new(),
                    None,
                    start,
                ));
            }
            return Ok(Statement::If(
                Expr::BoolLiteral(false, start),
                Block {
                    statements: Vec::new(),
                    span: start,
                },
                Vec::new(),
                None,
                start,
            ));
        }

        // Build an if/else-if chain. The first arm becomes the
        // `then` block; subsequent arms become `else if` entries;
        // the default arm (if any) becomes the final `else`.
        let (first_cond, first_body) = arms.remove(0);
        Ok(Statement::If(first_cond, first_body, arms, default, start))
    }

    fn parse_for(&mut self) -> Result<Statement, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwFor)?;
        let (var, _) = self.expect_ident()?;
        self.expect(&TokenKind::KwIn)?;
        let saved = self.restrict_struct_literals;
        self.restrict_struct_literals = true;
        let start_expr = self.parse_expr()?;
        self.expect(&TokenKind::DotDot)?;
        let end_expr = self.parse_expr()?;
        self.restrict_struct_literals = saved;
        let body = self.parse_block()?;
        Ok(Statement::For {
            var,
            start: start_expr,
            end: end_expr,
            body,
            span: start,
        })
    }

    fn parse_draw(&mut self) -> Result<Statement, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwDraw)?;
        let (sprite_name, _) = self.expect_ident()?;

        let mut x = None;
        let mut y = None;
        let mut frame = None;

        // Parse keyword arguments: at: (x, y), frame: n
        // Only consume an ident if it's followed by ':', indicating a keyword arg.
        while matches!(self.peek(), TokenKind::Ident(_))
            && self.peek_at_offset(1) == Some(&TokenKind::Colon)
        {
            let (key, _) = self.expect_ident()?;
            self.expect(&TokenKind::Colon)?;
            match key.as_str() {
                "at" => {
                    self.expect(&TokenKind::LParen)?;
                    x = Some(self.parse_expr()?);
                    self.expect(&TokenKind::Comma)?;
                    y = Some(self.parse_expr()?);
                    self.expect(&TokenKind::RParen)?;
                }
                "frame" => {
                    frame = Some(self.parse_expr()?);
                }
                _ => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!("unknown draw property '{key}'"),
                        self.current_span(),
                    ));
                }
            }
        }

        let x = x.ok_or_else(|| {
            Diagnostic::error(ErrorCode::E0201, "draw requires 'at: (x, y)'", start)
        })?;
        let y = y.ok_or_else(|| {
            Diagnostic::error(ErrorCode::E0201, "draw requires 'at: (x, y)'", start)
        })?;

        Ok(Statement::Draw(DrawStmt {
            sprite_name,
            x,
            y,
            frame,
            span: start,
        }))
    }

    /// Parse debug.log(...) or debug.assert(...)
    fn parse_debug_statement(&mut self) -> Result<Statement, Diagnostic> {
        let start = self.current_span();
        self.expect(&TokenKind::KwDebug)?;
        self.expect(&TokenKind::Dot)?;
        let (method, _) = self.expect_ident()?;
        self.expect(&TokenKind::LParen)?;
        match method.as_str() {
            "log" => {
                let mut args = Vec::new();
                while *self.peek() != TokenKind::RParen && *self.peek() != TokenKind::Eof {
                    args.push(self.parse_expr()?);
                    if *self.peek() == TokenKind::Comma {
                        self.advance();
                    }
                }
                self.expect(&TokenKind::RParen)?;
                Ok(Statement::DebugLog(args, start))
            }
            "assert" => {
                let cond = self.parse_expr()?;
                self.expect(&TokenKind::RParen)?;
                Ok(Statement::DebugAssert(cond, start))
            }
            _ => Err(Diagnostic::error(
                ErrorCode::E0201,
                format!("unknown debug method '{method}' (expected 'log' or 'assert')"),
                start,
            )),
        }
    }

    fn parse_assign_or_call(&mut self) -> Result<Statement, Diagnostic> {
        let start = self.current_span();
        let (name, _) = self.expect_ident()?;

        // Check for button.X pattern
        if name == "button" && *self.peek() == TokenKind::Dot {
            // This shouldn't be a statement on its own
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                "button read is an expression, not a statement",
                start,
            ));
        }

        match self.peek().clone() {
            TokenKind::Assign => {
                self.advance();
                let value = self.parse_expr()?;
                Ok(Statement::Assign(
                    LValue::Var(name),
                    AssignOp::Assign,
                    value,
                    start,
                ))
            }
            TokenKind::PlusAssign => {
                self.advance();
                let value = self.parse_expr()?;
                Ok(Statement::Assign(
                    LValue::Var(name),
                    AssignOp::PlusAssign,
                    value,
                    start,
                ))
            }
            TokenKind::MinusAssign => {
                self.advance();
                let value = self.parse_expr()?;
                Ok(Statement::Assign(
                    LValue::Var(name),
                    AssignOp::MinusAssign,
                    value,
                    start,
                ))
            }
            TokenKind::AmpAssign => {
                self.advance();
                let value = self.parse_expr()?;
                Ok(Statement::Assign(
                    LValue::Var(name),
                    AssignOp::AmpAssign,
                    value,
                    start,
                ))
            }
            TokenKind::PipeAssign => {
                self.advance();
                let value = self.parse_expr()?;
                Ok(Statement::Assign(
                    LValue::Var(name),
                    AssignOp::PipeAssign,
                    value,
                    start,
                ))
            }
            TokenKind::CaretAssign => {
                self.advance();
                let value = self.parse_expr()?;
                Ok(Statement::Assign(
                    LValue::Var(name),
                    AssignOp::CaretAssign,
                    value,
                    start,
                ))
            }
            TokenKind::ShiftLeftAssign => {
                self.advance();
                let value = self.parse_expr()?;
                Ok(Statement::Assign(
                    LValue::Var(name),
                    AssignOp::ShiftLeftAssign,
                    value,
                    start,
                ))
            }
            TokenKind::ShiftRightAssign => {
                self.advance();
                let value = self.parse_expr()?;
                Ok(Statement::Assign(
                    LValue::Var(name),
                    AssignOp::ShiftRightAssign,
                    value,
                    start,
                ))
            }
            TokenKind::LBracket => {
                // Array index assignment: name[index] = value
                self.advance();
                let index = self.parse_expr()?;
                self.expect(&TokenKind::RBracket)?;
                let op = self.parse_assign_op()?;
                let value = self.parse_expr()?;
                Ok(Statement::Assign(
                    LValue::ArrayIndex(name, Box::new(index)),
                    op,
                    value,
                    start,
                ))
            }
            TokenKind::Dot => {
                // Field assignment: `name.field = value`, including
                // chains (`outer.inner.field = value`) and array
                // fields (`name.inv[idx] = value`). The dotted
                // chain is eagerly joined into a single synthetic
                // identifier so the analyzer/lowering can treat it
                // identically to a flat variable name.
                let mut chain = vec![name];
                while *self.peek() == TokenKind::Dot {
                    self.advance();
                    let (field, _) = self.expect_ident()?;
                    chain.push(field);
                }
                if *self.peek() == TokenKind::LBracket {
                    self.advance();
                    let index = self.parse_expr()?;
                    self.expect(&TokenKind::RBracket)?;
                    let op = self.parse_assign_op()?;
                    let value = self.parse_expr()?;
                    let joined = chain.join(".");
                    return Ok(Statement::Assign(
                        LValue::ArrayIndex(joined, Box::new(index)),
                        op,
                        value,
                        start,
                    ));
                }
                let last = chain.pop().expect("at least one field consumed");
                let base = chain.join(".");
                let op = self.parse_assign_op()?;
                let value = self.parse_expr()?;
                Ok(Statement::Assign(
                    LValue::Field(base, last),
                    op,
                    value,
                    start,
                ))
            }
            TokenKind::LParen => {
                // Function call
                self.advance();
                let mut args = Vec::new();
                while *self.peek() != TokenKind::RParen && *self.peek() != TokenKind::Eof {
                    args.push(self.parse_expr()?);
                    if *self.peek() == TokenKind::Comma {
                        self.advance();
                    }
                }
                self.expect(&TokenKind::RParen)?;
                Ok(Statement::Call(name, args, start))
            }
            _ => Err(Diagnostic::error(
                ErrorCode::E0201,
                format!(
                    "expected assignment operator or '(' after identifier, found '{}'",
                    self.peek()
                ),
                self.current_span(),
            )),
        }
    }

    fn parse_assign_op(&mut self) -> Result<AssignOp, Diagnostic> {
        match self.peek() {
            TokenKind::Assign => {
                self.advance();
                Ok(AssignOp::Assign)
            }
            TokenKind::PlusAssign => {
                self.advance();
                Ok(AssignOp::PlusAssign)
            }
            TokenKind::MinusAssign => {
                self.advance();
                Ok(AssignOp::MinusAssign)
            }
            TokenKind::AmpAssign => {
                self.advance();
                Ok(AssignOp::AmpAssign)
            }
            TokenKind::PipeAssign => {
                self.advance();
                Ok(AssignOp::PipeAssign)
            }
            TokenKind::CaretAssign => {
                self.advance();
                Ok(AssignOp::CaretAssign)
            }
            TokenKind::ShiftLeftAssign => {
                self.advance();
                Ok(AssignOp::ShiftLeftAssign)
            }
            TokenKind::ShiftRightAssign => {
                self.advance();
                Ok(AssignOp::ShiftRightAssign)
            }
            _ => Err(Diagnostic::error(
                ErrorCode::E0201,
                format!("expected assignment operator, found '{}'", self.peek()),
                self.current_span(),
            )),
        }
    }

    // ── Type parsing ──

    fn parse_type(&mut self) -> Result<NesType, Diagnostic> {
        let base = match self.peek().clone() {
            TokenKind::KwU8 => {
                self.advance();
                NesType::U8
            }
            TokenKind::KwI8 => {
                self.advance();
                NesType::I8
            }
            TokenKind::KwU16 => {
                self.advance();
                NesType::U16
            }
            TokenKind::KwI16 => {
                self.advance();
                NesType::I16
            }
            TokenKind::KwBool => {
                self.advance();
                NesType::Bool
            }
            TokenKind::Ident(name) => {
                // User-declared struct types are referenced by name.
                // The analyzer validates that the name exists.
                self.advance();
                NesType::Struct(name)
            }
            _ => {
                return Err(Diagnostic::error(
                    ErrorCode::E0201,
                    format!("expected type, found '{}'", self.peek()),
                    self.current_span(),
                ));
            }
        };
        // Check for array suffix [N]
        if *self.peek() == TokenKind::LBracket {
            self.advance();
            if let TokenKind::IntLiteral(size) = self.peek().clone() {
                self.advance();
                self.expect(&TokenKind::RBracket)?;
                Ok(NesType::Array(Box::new(base), size))
            } else {
                Err(Diagnostic::error(
                    ErrorCode::E0201,
                    "expected array size",
                    self.current_span(),
                ))
            }
        } else {
            Ok(base)
        }
    }

    // ── Expression parsing (Pratt / precedence climbing) ──

    fn parse_expr(&mut self) -> Result<Expr, Diagnostic> {
        self.parse_or_expr()
    }

    fn parse_or_expr(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_and_expr()?;
        while *self.peek() == TokenKind::KwOr {
            let span = self.current_span();
            self.advance();
            let right = self.parse_and_expr()?;
            left = Expr::BinaryOp(Box::new(left), BinOp::Or, Box::new(right), span);
        }
        Ok(left)
    }

    fn parse_and_expr(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_comparison()?;
        while *self.peek() == TokenKind::KwAnd {
            let span = self.current_span();
            self.advance();
            let right = self.parse_comparison()?;
            left = Expr::BinaryOp(Box::new(left), BinOp::And, Box::new(right), span);
        }
        Ok(left)
    }

    fn parse_comparison(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_bitwise_or()?;
        loop {
            let (op, span) = match self.peek() {
                TokenKind::Eq => (BinOp::Eq, self.current_span()),
                TokenKind::NotEq => (BinOp::NotEq, self.current_span()),
                TokenKind::Lt => (BinOp::Lt, self.current_span()),
                TokenKind::Gt => (BinOp::Gt, self.current_span()),
                TokenKind::LtEq => (BinOp::LtEq, self.current_span()),
                TokenKind::GtEq => (BinOp::GtEq, self.current_span()),
                _ => break,
            };
            self.advance();
            let right = self.parse_bitwise_or()?;
            left = Expr::BinaryOp(Box::new(left), op, Box::new(right), span);
        }
        Ok(left)
    }

    fn parse_bitwise_or(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_bitwise_xor()?;
        while *self.peek() == TokenKind::Pipe {
            let span = self.current_span();
            self.advance();
            let right = self.parse_bitwise_xor()?;
            left = Expr::BinaryOp(Box::new(left), BinOp::BitwiseOr, Box::new(right), span);
        }
        Ok(left)
    }

    fn parse_bitwise_xor(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_bitwise_and()?;
        while *self.peek() == TokenKind::Caret {
            let span = self.current_span();
            self.advance();
            let right = self.parse_bitwise_and()?;
            left = Expr::BinaryOp(Box::new(left), BinOp::BitwiseXor, Box::new(right), span);
        }
        Ok(left)
    }

    fn parse_bitwise_and(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_shift()?;
        while *self.peek() == TokenKind::Amp {
            let span = self.current_span();
            self.advance();
            let right = self.parse_shift()?;
            left = Expr::BinaryOp(Box::new(left), BinOp::BitwiseAnd, Box::new(right), span);
        }
        Ok(left)
    }

    fn parse_shift(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_additive()?;
        loop {
            let (op, span) = match self.peek() {
                TokenKind::ShiftLeft => (BinOp::ShiftLeft, self.current_span()),
                TokenKind::ShiftRight => (BinOp::ShiftRight, self.current_span()),
                _ => break,
            };
            self.advance();
            let right = self.parse_additive()?;
            left = Expr::BinaryOp(Box::new(left), op, Box::new(right), span);
        }
        Ok(left)
    }

    fn parse_additive(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_multiplicative()?;
        loop {
            let (op, span) = match self.peek() {
                TokenKind::Plus => (BinOp::Add, self.current_span()),
                TokenKind::Minus => (BinOp::Sub, self.current_span()),
                _ => break,
            };
            self.advance();
            let right = self.parse_multiplicative()?;
            left = Expr::BinaryOp(Box::new(left), op, Box::new(right), span);
        }
        Ok(left)
    }

    fn parse_multiplicative(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_unary()?;
        loop {
            let (op, span) = match self.peek() {
                TokenKind::Star => (BinOp::Mul, self.current_span()),
                TokenKind::Slash => (BinOp::Div, self.current_span()),
                TokenKind::Percent => (BinOp::Mod, self.current_span()),
                _ => break,
            };
            self.advance();
            let right = self.parse_unary()?;
            left = Expr::BinaryOp(Box::new(left), op, Box::new(right), span);
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<Expr, Diagnostic> {
        let expr = match self.peek().clone() {
            TokenKind::Minus => {
                let span = self.current_span();
                self.advance();
                let expr = self.parse_unary()?;
                Expr::UnaryOp(UnaryOp::Negate, Box::new(expr), span)
            }
            TokenKind::KwNot => {
                let span = self.current_span();
                self.advance();
                let expr = self.parse_unary()?;
                Expr::UnaryOp(UnaryOp::Not, Box::new(expr), span)
            }
            TokenKind::Tilde => {
                let span = self.current_span();
                self.advance();
                let expr = self.parse_unary()?;
                Expr::UnaryOp(UnaryOp::BitNot, Box::new(expr), span)
            }
            _ => self.parse_primary()?,
        };
        self.parse_cast_suffix(expr)
    }

    fn parse_cast_suffix(&mut self, mut expr: Expr) -> Result<Expr, Diagnostic> {
        while *self.peek() == TokenKind::KwAs {
            let span = self.current_span();
            self.advance();
            let target_type = self.parse_type()?;
            expr = Expr::Cast(Box::new(expr), target_type, span);
        }
        Ok(expr)
    }

    fn parse_primary(&mut self) -> Result<Expr, Diagnostic> {
        match self.peek().clone() {
            TokenKind::IntLiteral(v) => {
                let span = self.current_span();
                self.advance();
                Ok(Expr::IntLiteral(v, span))
            }
            TokenKind::KwDebug => {
                // `debug.METHOD(args)` expression form. The
                // statement form is parsed separately by
                // parse_debug_statement; here we only accept the
                // value-returning methods.
                let span = self.current_span();
                self.advance();
                self.expect(&TokenKind::Dot)?;
                let (method, _) = self.expect_ident()?;
                self.expect(&TokenKind::LParen)?;
                let mut args = Vec::new();
                while *self.peek() != TokenKind::RParen && *self.peek() != TokenKind::Eof {
                    args.push(self.parse_expr()?);
                    if *self.peek() == TokenKind::Comma {
                        self.advance();
                    }
                }
                self.expect(&TokenKind::RParen)?;
                Ok(Expr::DebugCall(method, args, span))
            }
            TokenKind::BoolLiteral(v) => {
                let span = self.current_span();
                self.advance();
                Ok(Expr::BoolLiteral(v, span))
            }
            TokenKind::Ident(name) => {
                let span = self.current_span();
                self.advance();

                // Check for button.X or button.X.pressed/.released
                if name == "button" && *self.peek() == TokenKind::Dot {
                    self.advance();
                    let (button, _) = self.expect_name()?;
                    if *self.peek() == TokenKind::Dot {
                        self.advance();
                        if let TokenKind::Ident(edge) = self.peek().clone() {
                            if edge == "pressed" || edge == "released" {
                                self.advance();
                                return Ok(Expr::ButtonEdge(
                                    None,
                                    button,
                                    edge == "released",
                                    span,
                                ));
                            }
                        }
                        return Err(Diagnostic::error(
                            ErrorCode::E0201,
                            "expected 'pressed' or 'released' after button name",
                            self.current_span(),
                        ));
                    }
                    return Ok(Expr::ButtonRead(None, button, span));
                }

                // Check for p1.button.X / p2.button.X, optionally
                // followed by .pressed / .released for edge-triggered.
                if (name == "p1" || name == "p2") && *self.peek() == TokenKind::Dot {
                    self.advance();
                    // Expect 'button'
                    if let TokenKind::Ident(kw) = self.peek().clone() {
                        if kw == "button" {
                            self.advance();
                            self.expect(&TokenKind::Dot)?;
                            let (button, _) = self.expect_name()?;
                            let player = if name == "p1" {
                                Some(Player::P1)
                            } else {
                                Some(Player::P2)
                            };
                            if *self.peek() == TokenKind::Dot {
                                self.advance();
                                if let TokenKind::Ident(edge) = self.peek().clone() {
                                    if edge == "pressed" || edge == "released" {
                                        self.advance();
                                        return Ok(Expr::ButtonEdge(
                                            player,
                                            button,
                                            edge == "released",
                                            span,
                                        ));
                                    }
                                }
                                return Err(Diagnostic::error(
                                    ErrorCode::E0201,
                                    "expected 'pressed' or 'released' after button name",
                                    self.current_span(),
                                ));
                            }
                            return Ok(Expr::ButtonRead(player, button, span));
                        }
                    }
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        "expected 'button' after 'p1.' or 'p2.'",
                        self.current_span(),
                    ));
                }

                // Check for array index
                if *self.peek() == TokenKind::LBracket {
                    self.advance();
                    let index = self.parse_expr()?;
                    self.expect(&TokenKind::RBracket)?;
                    return Ok(Expr::ArrayIndex(name, Box::new(index), span));
                }

                // Check for function call
                if *self.peek() == TokenKind::LParen {
                    self.advance();
                    let mut args = Vec::new();
                    while *self.peek() != TokenKind::RParen && *self.peek() != TokenKind::Eof {
                        args.push(self.parse_expr()?);
                        if *self.peek() == TokenKind::Comma {
                            self.advance();
                        }
                    }
                    self.expect(&TokenKind::RParen)?;
                    return Ok(Expr::Call(name, args, span));
                }

                // Check for field access: `name.field`, including
                // chains like `outer.inner.field` for nested
                // structs and `name.field[idx]` for array fields.
                // The synthetic flat-name model used by the
                // analyzer/lowering keys symbols by the joined
                // dotted path, so we eagerly consume the entire
                // chain into a single identifier string.
                if *self.peek() == TokenKind::Dot {
                    let mut chain = vec![name];
                    while *self.peek() == TokenKind::Dot {
                        self.advance();
                        let (field, _) = self.expect_ident()?;
                        chain.push(field);
                    }
                    // After the dotted chain we may still see an
                    // array index — `player.inv[0]` becomes
                    // `ArrayIndex("player.inv", idx)`. Otherwise
                    // the last segment is the field of the path
                    // before it: `p.pos.x` becomes
                    // `FieldAccess("p.pos", "x")`.
                    if *self.peek() == TokenKind::LBracket {
                        self.advance();
                        let index = self.parse_expr()?;
                        self.expect(&TokenKind::RBracket)?;
                        let joined = chain.join(".");
                        return Ok(Expr::ArrayIndex(joined, Box::new(index), span));
                    }
                    let last = chain.pop().expect("at least one field consumed");
                    let base = chain.join(".");
                    return Ok(Expr::FieldAccess(base, last, span));
                }

                // Check for struct literal: `Name { field: expr, ... }`.
                // Disabled in condition contexts to keep parsing
                // unambiguous for `if`/`while`/`for`.
                if !self.restrict_struct_literals && *self.peek() == TokenKind::LBrace {
                    self.advance();
                    let mut fields = Vec::new();
                    while *self.peek() != TokenKind::RBrace && *self.peek() != TokenKind::Eof {
                        let (field_name, _) = self.expect_ident()?;
                        self.expect(&TokenKind::Colon)?;
                        // Struct literal field values can contain
                        // their own nested struct literals, so we
                        // temporarily allow them regardless of the
                        // outer restriction.
                        let saved = self.restrict_struct_literals;
                        self.restrict_struct_literals = false;
                        let value = self.parse_expr()?;
                        self.restrict_struct_literals = saved;
                        fields.push((field_name, value));
                        if *self.peek() == TokenKind::Comma {
                            self.advance();
                        } else if *self.peek() != TokenKind::RBrace {
                            return Err(Diagnostic::error(
                                ErrorCode::E0201,
                                "expected ',' or '}' in struct literal",
                                self.current_span(),
                            ));
                        }
                    }
                    self.expect(&TokenKind::RBrace)?;
                    return Ok(Expr::StructLiteral(name, fields, span));
                }

                Ok(Expr::Ident(name, span))
            }
            TokenKind::LBracket => {
                let span = self.current_span();
                self.advance();
                let mut elements = Vec::new();
                while *self.peek() != TokenKind::RBracket && *self.peek() != TokenKind::Eof {
                    elements.push(self.parse_expr()?);
                    if *self.peek() == TokenKind::Comma {
                        self.advance();
                    }
                }
                self.expect(&TokenKind::RBracket)?;
                Ok(Expr::ArrayLiteral(elements, span))
            }
            TokenKind::LParen => {
                self.advance();
                let expr = self.parse_expr()?;
                self.expect(&TokenKind::RParen)?;
                Ok(expr)
            }
            _ => Err(Diagnostic::error(
                ErrorCode::E0201,
                format!("expected expression, found '{}'", self.peek()),
                self.current_span(),
            )),
        }
    }
}

/// Convert a tilemap authored as rows of characters into the flat
/// byte array the nametable expects. Each row is up to 32 characters
/// wide; shorter rows pad with the default tile 0, longer rows are an
/// error. The full tile map is 30 rows × 32 cols = 960 bytes; fewer
/// rows are zero-padded (the analyzer does the final padding, so we
/// just emit whatever the user declared without the trailing zeros
/// here).
fn tilemap_to_bytes(
    bg_name: &str,
    rows: &[String],
    legend: &std::collections::HashMap<char, u8>,
    span: Span,
) -> Result<Vec<u8>, Diagnostic> {
    if rows.len() > 30 {
        return Err(Diagnostic::error(
            ErrorCode::E0201,
            format!(
                "background '{bg_name}' tilemap has {} rows; maximum is 30",
                rows.len()
            ),
            span,
        ));
    }
    let mut out = Vec::with_capacity(rows.len() * 32);
    for (ry, row) in rows.iter().enumerate() {
        let chars: Vec<char> = row.chars().collect();
        if chars.len() > 32 {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                format!(
                    "background '{bg_name}' tilemap row {ry} has {} cells; \
                     maximum is 32",
                    chars.len()
                ),
                span,
            ));
        }
        for (rx, ch) in chars.iter().enumerate() {
            let tile = legend.get(ch).copied().ok_or_else(|| {
                Diagnostic::error(
                    ErrorCode::E0201,
                    format!(
                        "background '{bg_name}' tilemap cell ({rx}, {ry}) uses \
                         character '{ch}' which is not in the legend"
                    ),
                    span,
                )
            })?;
            out.push(tile);
        }
        // Pad the remainder of this row with tile 0 so subsequent
        // rows land at the right column in the flat array.
        out.resize(out.len() + (32 - chars.len()), 0);
    }
    Ok(out)
}

/// Convert a `palette_map:` grid (rows of digit characters `0`-`3`,
/// one per 16×16 metatile) into the 64-byte attribute table the PPU
/// expects.
///
/// The attribute layout is notoriously awkward: each attribute byte
/// covers a 32×32-pixel region (four 16×16 metatiles) packed as
/// `BR BL TR TL` — top-left in the low bits, bottom-right in the high
/// bits. The attribute table is a fixed 8×8 = 64 bytes covering 16
/// metatile rows, even though only the top 15 (the visible 240
/// scanlines) render on screen. Programs may declare up to 16 rows
/// so the off-screen half picks up sensible attribute bytes; if
/// exactly 15 are given, the parser auto-replicates row 14 down
/// into row 15 so the last attribute byte stays consistent with
/// what's visible.
fn palette_map_to_attrs(bg_name: &str, rows: &[String], span: Span) -> Result<Vec<u8>, Diagnostic> {
    if rows.len() > 16 {
        return Err(Diagnostic::error(
            ErrorCode::E0201,
            format!(
                "background '{bg_name}' palette_map has {} rows; maximum is 16 \
                 (15 visible metatile rows + 1 off-screen row for the bottom \
                 half of the last attribute byte)",
                rows.len()
            ),
            span,
        ));
    }
    // Build a dense 16×16 grid of sub-palette indices (rows beyond
    // declared are 0). Using 16 metatile rows keeps the packing loop
    // branch-free.
    let mut grid = [[0u8; 16]; 16];
    for (ry, row) in rows.iter().enumerate() {
        let chars: Vec<char> = row.chars().collect();
        if chars.len() > 16 {
            return Err(Diagnostic::error(
                ErrorCode::E0201,
                format!(
                    "background '{bg_name}' palette_map row {ry} has {} cells; \
                     maximum is 16 (one per 16×16 metatile)",
                    chars.len()
                ),
                span,
            ));
        }
        for (rx, ch) in chars.iter().enumerate() {
            let idx = match ch {
                '0' => 0u8,
                '1' => 1,
                '2' => 2,
                '3' => 3,
                ' ' | '.' => 0,
                other => {
                    return Err(Diagnostic::error(
                        ErrorCode::E0201,
                        format!(
                            "background '{bg_name}' palette_map cell ({rx}, {ry}) \
                             has '{other}'; must be a sub-palette digit '0'-'3'"
                        ),
                        span,
                    ));
                }
            };
            grid[ry][rx] = idx;
        }
    }
    // If the user gave exactly 15 rows, replicate row 14 into row 15
    // so the last attribute byte's bottom-half picks up the same
    // sub-palette as the visible bottom of the screen. Users who
    // want explicit control over the off-screen row can supply all
    // 16 rows.
    if rows.len() == 15 {
        grid[15] = grid[14];
    }
    // Pack into the 8×8 attribute table. Each attribute byte covers
    // a 2×2 block of metatiles:
    //     bits 0-1 = top-left      (grid[ay*2  ][ax*2  ])
    //     bits 2-3 = top-right     (grid[ay*2  ][ax*2+1])
    //     bits 4-5 = bottom-left   (grid[ay*2+1][ax*2  ])
    //     bits 6-7 = bottom-right  (grid[ay*2+1][ax*2+1])
    let mut out = vec![0u8; 64];
    for ay in 0..8 {
        for ax in 0..8 {
            let tl = grid[ay * 2][ax * 2] & 0b11;
            let tr = grid[ay * 2][ax * 2 + 1] & 0b11;
            let bl = grid[ay * 2 + 1][ax * 2] & 0b11;
            let br = grid[ay * 2 + 1][ax * 2 + 1] & 0b11;
            out[ay * 8 + ax] = tl | (tr << 2) | (bl << 4) | (br << 6);
        }
    }
    Ok(out)
}

pub fn parse(source: &str) -> (Option<Program>, Vec<Diagnostic>) {
    let (tokens, lex_diags) = crate::lexer::lex(source);
    if lex_diags.iter().any(Diagnostic::is_error) {
        return (None, lex_diags);
    }
    let (program, mut parse_diags) = Parser::new(tokens).parse();
    let mut all_diags = lex_diags;
    all_diags.append(&mut parse_diags);
    (program, all_diags)
}
