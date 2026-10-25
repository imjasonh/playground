use super::*;

fn lex_ok(input: &str) -> Vec<TokenKind> {
    let (tokens, diags) = lex(input);
    assert!(diags.is_empty(), "unexpected errors: {diags:?}");
    tokens.into_iter().map(|t| t.kind).collect()
}

fn lex_err(input: &str) -> Vec<crate::errors::ErrorCode> {
    let (_tokens, diags) = lex(input);
    diags.into_iter().map(|d| d.code).collect()
}

// ── Literals ──

#[test]
fn lex_decimal_numbers() {
    assert_eq!(lex_ok("0"), vec![TokenKind::IntLiteral(0), TokenKind::Eof]);
    assert_eq!(
        lex_ok("42"),
        vec![TokenKind::IntLiteral(42), TokenKind::Eof]
    );
    assert_eq!(
        lex_ok("65535"),
        vec![TokenKind::IntLiteral(65535), TokenKind::Eof]
    );
}

#[test]
fn lex_hex_numbers() {
    assert_eq!(
        lex_ok("0xFF"),
        vec![TokenKind::IntLiteral(0xFF), TokenKind::Eof]
    );
    assert_eq!(
        lex_ok("0x00"),
        vec![TokenKind::IntLiteral(0), TokenKind::Eof]
    );
    assert_eq!(
        lex_ok("0xFFFF"),
        vec![TokenKind::IntLiteral(0xFFFF), TokenKind::Eof]
    );
}

#[test]
fn lex_binary_numbers() {
    assert_eq!(
        lex_ok("0b1010"),
        vec![TokenKind::IntLiteral(0b1010), TokenKind::Eof]
    );
    assert_eq!(
        lex_ok("0b0000_0001"),
        vec![TokenKind::IntLiteral(1), TokenKind::Eof]
    );
}

#[test]
fn lex_number_with_underscores() {
    assert_eq!(
        lex_ok("1_000"),
        vec![TokenKind::IntLiteral(1000), TokenKind::Eof]
    );
}

#[test]
fn lex_number_overflow() {
    use crate::errors::ErrorCode;
    assert_eq!(lex_err("65536"), vec![ErrorCode::E0103]);
    assert_eq!(lex_err("0x1FFFF"), vec![ErrorCode::E0103]);
}

#[test]
fn lex_string_literal() {
    assert_eq!(
        lex_ok(r#""hello""#),
        vec![TokenKind::StringLiteral("hello".into()), TokenKind::Eof]
    );
}

#[test]
fn lex_string_escapes() {
    assert_eq!(
        lex_ok(r#""a\nb""#),
        vec![TokenKind::StringLiteral("a\nb".into()), TokenKind::Eof]
    );
    assert_eq!(
        lex_ok(r#""a\\b""#),
        vec![TokenKind::StringLiteral("a\\b".into()), TokenKind::Eof]
    );
    assert_eq!(
        lex_ok(r#""a\"b""#),
        vec![TokenKind::StringLiteral("a\"b".into()), TokenKind::Eof]
    );
}

#[test]
fn lex_unterminated_string() {
    use crate::errors::ErrorCode;
    assert_eq!(lex_err(r#""hello"#), vec![ErrorCode::E0101]);
}

#[test]
fn lex_bool_literals() {
    assert_eq!(
        lex_ok("true false"),
        vec![
            TokenKind::BoolLiteral(true),
            TokenKind::BoolLiteral(false),
            TokenKind::Eof
        ]
    );
}

// ── Keywords ──

#[test]
fn lex_all_keywords() {
    let keywords = vec![
        ("game", TokenKind::KwGame),
        ("state", TokenKind::KwState),
        ("on", TokenKind::KwOn),
        ("fun", TokenKind::KwFun),
        ("var", TokenKind::KwVar),
        ("const", TokenKind::KwConst),
        ("enum", TokenKind::KwEnum),
        ("struct", TokenKind::KwStruct),
        ("for", TokenKind::KwFor),
        ("in", TokenKind::KwIn),
        ("match", TokenKind::KwMatch),
        ("if", TokenKind::KwIf),
        ("else", TokenKind::KwElse),
        ("while", TokenKind::KwWhile),
        ("break", TokenKind::KwBreak),
        ("continue", TokenKind::KwContinue),
        ("return", TokenKind::KwReturn),
        ("not", TokenKind::KwNot),
        ("and", TokenKind::KwAnd),
        ("or", TokenKind::KwOr),
        ("fast", TokenKind::KwFast),
        ("slow", TokenKind::KwSlow),
        ("inline", TokenKind::KwInline),
        ("include", TokenKind::KwInclude),
        ("start", TokenKind::KwStart),
        ("transition", TokenKind::KwTransition),
        ("sprite", TokenKind::KwSprite),
        ("background", TokenKind::KwBackground),
        ("palette", TokenKind::KwPalette),
        ("load_background", TokenKind::KwLoadBackground),
        ("set_palette", TokenKind::KwSetPalette),
        ("draw", TokenKind::KwDraw),
        ("play", TokenKind::KwPlay),
        ("asm", TokenKind::KwAsm),
        ("loop", TokenKind::KwLoop),
        ("wait_frame", TokenKind::KwWaitFrame),
        ("u8", TokenKind::KwU8),
        ("i8", TokenKind::KwI8),
        ("u16", TokenKind::KwU16),
        ("bool", TokenKind::KwBool),
        ("debug", TokenKind::KwDebug),
        ("as", TokenKind::KwAs),
    ];
    for (text, expected) in keywords {
        let tokens = lex_ok(text);
        assert_eq!(tokens[0], expected, "keyword mismatch for '{text}'");
    }
}

#[test]
fn lex_identifier_not_keyword() {
    assert_eq!(
        lex_ok("player_x"),
        vec![TokenKind::Ident("player_x".into()), TokenKind::Eof]
    );
    assert_eq!(
        lex_ok("myVar123"),
        vec![TokenKind::Ident("myVar123".into()), TokenKind::Eof]
    );
}

// ── Symbols and operators ──

#[test]
fn lex_single_char_symbols() {
    let symbols = vec![
        ("(", TokenKind::LParen),
        (")", TokenKind::RParen),
        ("{", TokenKind::LBrace),
        ("}", TokenKind::RBrace),
        ("[", TokenKind::LBracket),
        ("]", TokenKind::RBracket),
        (",", TokenKind::Comma),
        (":", TokenKind::Colon),
        (";", TokenKind::Semicolon),
        (".", TokenKind::Dot),
        ("@", TokenKind::At),
        ("~", TokenKind::Tilde),
        ("+", TokenKind::Plus),
        ("-", TokenKind::Minus),
        ("*", TokenKind::Star),
        ("/", TokenKind::Slash),
        ("%", TokenKind::Percent),
        ("&", TokenKind::Amp),
        ("|", TokenKind::Pipe),
        ("^", TokenKind::Caret),
        ("=", TokenKind::Assign),
        ("<", TokenKind::Lt),
        (">", TokenKind::Gt),
    ];
    for (text, expected) in symbols {
        let tokens = lex_ok(text);
        assert_eq!(tokens[0], expected, "symbol mismatch for '{text}'");
    }
}

#[test]
fn lex_multi_char_operators() {
    let ops = vec![
        ("==", TokenKind::Eq),
        ("!=", TokenKind::NotEq),
        ("<=", TokenKind::LtEq),
        (">=", TokenKind::GtEq),
        ("<<", TokenKind::ShiftLeft),
        (">>", TokenKind::ShiftRight),
        ("+=", TokenKind::PlusAssign),
        ("-=", TokenKind::MinusAssign),
        ("&=", TokenKind::AmpAssign),
        ("|=", TokenKind::PipeAssign),
        ("^=", TokenKind::CaretAssign),
        ("<<=", TokenKind::ShiftLeftAssign),
        (">>=", TokenKind::ShiftRightAssign),
        ("->", TokenKind::Arrow),
    ];
    for (text, expected) in ops {
        let tokens = lex_ok(text);
        assert_eq!(tokens[0], expected, "operator mismatch for '{text}'");
    }
}

// ── Comments ──

#[test]
fn lex_line_comments() {
    assert_eq!(
        lex_ok("42 // this is a comment"),
        vec![TokenKind::IntLiteral(42), TokenKind::Eof]
    );
    assert_eq!(
        lex_ok("// entire line comment\n42"),
        vec![TokenKind::IntLiteral(42), TokenKind::Eof]
    );
}

// ── Variable declaration ──

#[test]
fn lex_variable_declaration() {
    let tokens = lex_ok("var x: u8 = 42");
    assert_eq!(tokens[0], TokenKind::KwVar);
    assert_eq!(tokens[1], TokenKind::Ident("x".into()));
    assert_eq!(tokens[2], TokenKind::Colon);
    assert_eq!(tokens[3], TokenKind::KwU8);
    assert_eq!(tokens[4], TokenKind::Assign);
    assert_eq!(tokens[5], TokenKind::IntLiteral(42));
    assert_eq!(tokens[6], TokenKind::Eof);
}

// ── Complex expressions ──

#[test]
fn lex_game_declaration() {
    let tokens = lex_ok(r#"game "Hello" { mapper: NROM }"#);
    assert_eq!(tokens[0], TokenKind::KwGame);
    assert_eq!(tokens[1], TokenKind::StringLiteral("Hello".into()));
    assert_eq!(tokens[2], TokenKind::LBrace);
    assert_eq!(tokens[3], TokenKind::Ident("mapper".into()));
    assert_eq!(tokens[4], TokenKind::Colon);
    assert_eq!(tokens[5], TokenKind::Ident("NROM".into()));
    assert_eq!(tokens[6], TokenKind::RBrace);
}

// ── Spans ──

#[test]
fn lex_span_tracking() {
    let (tokens, _) = lex("var x");
    assert_eq!(tokens[0].span.start, 0);
    assert_eq!(tokens[0].span.end, 3);
    assert_eq!(tokens[1].span.start, 4);
    assert_eq!(tokens[1].span.end, 5);
}

// ── Error recovery ──

#[test]
fn lex_continues_after_error() {
    let (tokens, diags) = lex("42 $ 10");
    // Should get the valid tokens despite the error
    let kinds: Vec<_> = tokens.iter().map(|t| &t.kind).collect();
    assert!(kinds.contains(&&TokenKind::IntLiteral(42)));
    assert!(kinds.contains(&&TokenKind::IntLiteral(10)));
    assert_eq!(diags.len(), 1);
}

// ── Empty input ──

#[test]
fn lex_empty_input() {
    assert_eq!(lex_ok(""), vec![TokenKind::Eof]);
}

#[test]
fn lex_whitespace_only() {
    assert_eq!(lex_ok("   \n\t\r\n  "), vec![TokenKind::Eof]);
}

// ── Full program snippet ──

#[test]
fn lex_full_program_snippet() {
    let src = r#"
        game "Hello Sprite" {
            mapper: NROM
        }

        var px: u8 = 128
        var py: u8 = 120

        on frame {
            if button.right { px += 2 }
        }

        start Main
    "#;
    let (tokens, diags) = lex(src);
    assert!(diags.is_empty(), "unexpected errors: {diags:?}");
    // Just verify it doesn't crash and produces tokens
    assert!(tokens.len() > 10);
    assert_eq!(tokens.last().unwrap().kind, TokenKind::Eof);
}

// ── Hex edge cases ──

#[test]
fn lex_hex_no_digits() {
    use crate::errors::ErrorCode;
    assert_eq!(lex_err("0x"), vec![ErrorCode::E0103]);
}

#[test]
fn lex_binary_no_digits() {
    use crate::errors::ErrorCode;
    assert_eq!(lex_err("0b"), vec![ErrorCode::E0103]);
}
