use super::*;
use crate::parser::ast::*;

fn parse_ok(input: &str) -> Program {
    let (prog, diags) = parse(input);
    assert!(
        diags.is_empty(),
        "unexpected errors: {diags:?}\ninput: {input}"
    );
    prog.expect("expected successful parse")
}

fn parse_err(input: &str) -> Vec<crate::errors::ErrorCode> {
    let (_, diags) = parse(input);
    assert!(!diags.is_empty(), "expected errors but got none");
    diags.into_iter().map(|d| d.code).collect()
}

const MINIMAL_GAME: &str = r#"
game "Test" { mapper: NROM }
var px: u8 = 0
on frame {
    px = 1
}
start Main
"#;

// ── Game declaration ──

#[test]
fn parse_game_decl() {
    let prog = parse_ok(MINIMAL_GAME);
    assert_eq!(prog.game.name, "Test");
    assert_eq!(prog.game.mapper, Mapper::NROM);
}

#[test]
fn parse_game_with_mirroring() {
    let src = r#"
        game "Test" { mapper: NROM mirroring: vertical }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.game.mirroring, Mirroring::Vertical);
}

#[test]
fn parse_game_default_header_is_ines1() {
    // Programs that don't mention `header:` should default to
    // iNES 1.0 — the current behaviour every example relies on.
    let prog = parse_ok(MINIMAL_GAME);
    assert_eq!(prog.game.header, HeaderFormat::Ines1);
}

#[test]
fn parse_game_with_nes2_header() {
    // Opting into NES 2.0 via `header: nes2`.
    let src = r#"
        game "Test" { mapper: NROM header: nes2 }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.game.header, HeaderFormat::Nes2);
}

#[test]
fn parse_game_with_ines1_header_explicit() {
    // Explicitly asking for iNES 1.0 (the default) also parses.
    let src = r#"
        game "Test" { mapper: NROM header: ines1 }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.game.header, HeaderFormat::Ines1);
}

// ── Variables ──

#[test]
fn parse_global_var() {
    let prog = parse_ok(MINIMAL_GAME);
    assert_eq!(prog.globals.len(), 1);
    assert_eq!(prog.globals[0].name, "px");
    assert_eq!(prog.globals[0].var_type, NesType::U8);
}

#[test]
fn parse_multiple_globals() {
    let src = r#"
        game "Test" { mapper: NROM }
        var px: u8 = 128
        var py: u8 = 120
        on frame { px = 1 }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.globals.len(), 2);
    assert_eq!(prog.globals[0].name, "px");
    assert_eq!(prog.globals[1].name, "py");
}

// ── Constants ──

#[test]
fn parse_const_decl() {
    let src = r#"
        game "Test" { mapper: NROM }
        const SPEED: u8 = 2
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.constants.len(), 1);
    assert_eq!(prog.constants[0].name, "SPEED");
}

// ── On frame ──

#[test]
fn parse_on_frame_implicit_state() {
    let prog = parse_ok(MINIMAL_GAME);
    assert_eq!(prog.states.len(), 1);
    assert_eq!(prog.states[0].name, "Main");
    assert!(prog.states[0].on_frame.is_some());
    assert_eq!(prog.start_state, "Main");
}

// ── Statements ──

#[test]
fn parse_if_statement() {
    let src = r#"
        game "Test" { mapper: NROM }
        on frame {
            if button.right { px += 2 }
        }
        var px: u8 = 0
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    assert_eq!(frame.statements.len(), 1);
    assert!(matches!(frame.statements[0], Statement::If(..)));
}

#[test]
fn parse_if_else() {
    let src = r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame {
            if x == 0 {
                x = 1
            } else {
                x = 0
            }
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::If(_, _, _, else_block, _) => {
            assert!(else_block.is_some());
        }
        other => panic!("expected If, got {other:?}"),
    }
}

#[test]
fn parse_if_else_if() {
    let src = r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame {
            if x == 0 {
                x = 1
            } else if x == 1 {
                x = 2
            } else {
                x = 0
            }
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::If(_, _, else_ifs, else_block, _) => {
            assert_eq!(else_ifs.len(), 1);
            assert!(else_block.is_some());
        }
        other => panic!("expected If, got {other:?}"),
    }
}

#[test]
fn parse_while_loop() {
    let src = r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame {
            while x < 10 { x += 1 }
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    assert!(matches!(frame.statements[0], Statement::While(..)));
}

#[test]
fn parse_draw_statement() {
    let src = r#"
        game "Test" { mapper: NROM }
        var px: u8 = 0
        var py: u8 = 0
        on frame {
            draw Smiley at: (px, py)
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::Draw(d) => {
            assert_eq!(d.sprite_name, "Smiley");
        }
        other => panic!("expected Draw, got {other:?}"),
    }
}

#[test]
fn parse_draw_with_frame() {
    let src = r#"
        game "Test" { mapper: NROM }
        var px: u8 = 0
        var py: u8 = 0
        on frame {
            draw Smiley at: (px, py) frame: 0
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::Draw(d) => {
            assert!(d.frame.is_some());
        }
        other => panic!("expected Draw, got {other:?}"),
    }
}

#[test]
fn parse_metasprite_decl() {
    // A metasprite collects parallel `dx` / `dy` / `frame`
    // arrays plus a reference to the underlying sprite. The
    // parser preserves them verbatim — array length validation
    // happens later in the analyzer.
    let src = r#"
        game "T" { mapper: NROM }
        sprite Tile {
            pixels: [
                "@@@@@@@@",
                "@@@@@@@@",
                "@@@@@@@@",
                "@@@@@@@@",
                "@@@@@@@@",
                "@@@@@@@@",
                "@@@@@@@@",
                "@@@@@@@@"
            ]
        }
        metasprite Hero {
            sprite: Tile
            dx:    [0, 8, 0, 8]
            dy:    [0, 0, 8, 8]
            frame: [0, 1, 2, 3]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.metasprites.len(), 1);
    let ms = &prog.metasprites[0];
    assert_eq!(ms.name, "Hero");
    assert_eq!(ms.sprite_name, "Tile");
    assert_eq!(ms.dx, vec![0, 8, 0, 8]);
    assert_eq!(ms.dy, vec![0, 0, 8, 8]);
    assert_eq!(ms.frame, vec![0, 1, 2, 3]);
}

// ── Expressions ──

#[test]
fn parse_arithmetic() {
    let src = r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame {
            x = 1 + 2 * 3
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    // x = 1 + (2 * 3) -- multiplication binds tighter
    match &frame.statements[0] {
        Statement::Assign(_, _, Expr::BinaryOp(_, BinOp::Add, right, _), _) => {
            assert!(matches!(
                right.as_ref(),
                Expr::BinaryOp(_, BinOp::Mul, _, _)
            ));
        }
        other => panic!("expected assignment with Add, got {other:?}"),
    }
}

#[test]
fn parse_button_read() {
    let src = r#"
        game "Test" { mapper: NROM }
        var px: u8 = 0
        on frame {
            if button.right { px += 1 }
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::If(Expr::ButtonRead(_, button, _), _, _, _, _) => {
            assert_eq!(button, "right");
        }
        other => panic!("expected if with button read, got {other:?}"),
    }
}

#[test]
fn parse_comparison_ops() {
    let src = r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame {
            if x >= 10 { x = 0 }
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::If(Expr::BinaryOp(_, BinOp::GtEq, _, _), _, _, _, _) => {}
        other => panic!("expected if with GtEq, got {other:?}"),
    }
}

// ── State declarations ──

#[test]
fn parse_explicit_state() {
    let src = r#"
        game "Test" { mapper: NROM }
        state Title {
            on enter { wait_frame }
            on frame { wait_frame }
        }
        start Title
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.states.len(), 1);
    assert_eq!(prog.states[0].name, "Title");
    assert!(prog.states[0].on_enter.is_some());
    assert!(prog.states[0].on_frame.is_some());
}

// ── Error cases ──

#[test]
fn parse_missing_game() {
    use crate::errors::ErrorCode;
    let codes = parse_err("var x: u8 = 0\nstart Main");
    assert!(codes.contains(&ErrorCode::E0504));
}

#[test]
fn parse_missing_start_with_explicit_state() {
    use crate::errors::ErrorCode;
    // Explicit state without `start` declaration should fail
    let codes = parse_err(
        r#"
        game "T" { mapper: NROM }
        state Foo { on frame { wait_frame } }
    "#,
    );
    assert!(codes.contains(&ErrorCode::E0504));
}

#[test]
fn parse_on_frame_implies_start() {
    // Top-level `on frame` auto-creates implicit "Main" state and start
    let prog = parse_ok(r#"game "T" { mapper: NROM } on frame { wait_frame }"#);
    assert_eq!(prog.start_state, "Main");
}

// ── Full M1 program ──

#[test]
fn parse_full_m1_program() {
    let src = r#"
        game "Hello Sprite" {
            mapper: NROM
        }

        var px: u8 = 128
        var py: u8 = 120

        on frame {
            if button.right { px += 2 }
            if button.left  { px -= 2 }
            if button.down  { py += 2 }
            if button.up    { py -= 2 }

            draw Smiley at: (px, py)
        }

        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.game.name, "Hello Sprite");
    assert_eq!(prog.globals.len(), 2);
    assert_eq!(prog.states.len(), 1);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    assert_eq!(frame.statements.len(), 5); // 4 ifs + 1 draw
}

// ── Milestone 2: Functions ──

#[test]
fn parse_function_decl() {
    let src = r#"
        game "Test" { mapper: NROM }
        fun add(a: u8, b: u8) -> u8 {
            return a + b
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.functions.len(), 1);
    let f = &prog.functions[0];
    assert_eq!(f.name, "add");
    assert!(!f.is_inline);
    assert_eq!(f.params.len(), 2);
    assert_eq!(f.params[0].name, "a");
    assert_eq!(f.params[0].param_type, NesType::U8);
    assert_eq!(f.params[1].name, "b");
    assert_eq!(f.params[1].param_type, NesType::U8);
    assert_eq!(f.return_type, Some(NesType::U8));
    assert_eq!(f.body.statements.len(), 1);
}

#[test]
fn parse_inline_function() {
    let src = r#"
        game "Test" { mapper: NROM }
        inline fun double(x: u8) -> u8 {
            return x + x
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.functions.len(), 1);
    let f = &prog.functions[0];
    assert_eq!(f.name, "double");
    assert!(f.is_inline);
    assert_eq!(f.params.len(), 1);
    assert_eq!(f.params[0].name, "x");
    assert_eq!(f.return_type, Some(NesType::U8));
}

#[test]
fn parse_array_type() {
    let src = r#"
        game "Test" { mapper: NROM }
        var buf: u8[16] = [0, 0, 0]
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.globals.len(), 1);
    assert_eq!(
        prog.globals[0].var_type,
        NesType::Array(Box::new(NesType::U8), 16)
    );
    assert!(prog.globals[0].init.is_some());
}

#[test]
fn parse_array_literal() {
    let src = r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame {
            x = [1, 2, 3]
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::Assign(_, _, Expr::ArrayLiteral(elems, _), _) => {
            assert_eq!(elems.len(), 3);
        }
        other => panic!("expected assignment with ArrayLiteral, got {other:?}"),
    }
}

#[test]
fn parse_fast_var() {
    let src = r#"
        game "Test" { mapper: NROM }
        fast var x: u8 = 0
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.globals.len(), 1);
    assert_eq!(prog.globals[0].name, "x");
    assert_eq!(prog.globals[0].placement, Placement::Fast);
}

#[test]
fn parse_function_call_expr() {
    let src = r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame {
            x = add(1, 2)
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::Assign(_, _, Expr::Call(name, args, _), _) => {
            assert_eq!(name, "add");
            assert_eq!(args.len(), 2);
        }
        other => panic!("expected assignment with Call, got {other:?}"),
    }
}

// ── Milestone 3: Sprites / Palettes / Backgrounds ──

#[test]
fn parse_sprite_decl() {
    let src = r#"
        game "Test" { mapper: NROM }
        sprite Player {
            chr: [0x3C, 0x42, 0x81, 0x81, 0x81, 0x81, 0x42, 0x3C,
                  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.sprites.len(), 1);
    assert_eq!(prog.sprites[0].name, "Player");
    match &prog.sprites[0].chr_source {
        AssetSource::Inline(data) => {
            assert_eq!(data.len(), 16);
            assert_eq!(data[0], 0x3C);
        }
        other => panic!("expected Inline, got {other:?}"),
    }
}

// ── Palette / background declarations ──

#[test]
fn parse_palette_decl() {
    let src = r#"
        game "Test" { mapper: NROM }
        palette Main {
            colors: [0x0F, 0x00, 0x10, 0x20,
                     0x0F, 0x06, 0x16, 0x26,
                     0x0F, 0x09, 0x19, 0x29,
                     0x0F, 0x01, 0x11, 0x21]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.palettes.len(), 1);
    assert_eq!(prog.palettes[0].name, "Main");
    assert_eq!(prog.palettes[0].colors.len(), 16);
    assert_eq!(prog.palettes[0].colors[0], 0x0F);
    assert_eq!(prog.palettes[0].colors[15], 0x21);
}

#[test]
fn parse_background_decl_with_attributes() {
    let src = r#"
        game "Test" { mapper: NROM }
        background Title {
            tiles: [1, 2, 3, 4, 5]
            attributes: [0xFF, 0x55]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.backgrounds.len(), 1);
    assert_eq!(prog.backgrounds[0].name, "Title");
    assert_eq!(prog.backgrounds[0].tiles, vec![1, 2, 3, 4, 5]);
    assert_eq!(prog.backgrounds[0].attributes, vec![0xFF, 0x55]);
}

#[test]
fn parse_palette_decl_from_png_source() {
    // Shortcut form: `palette Name @palette("file.png")` sets
    // `png_source` and leaves `colors` empty. The asset resolver
    // decodes the actual bytes at compile time.
    let src = r#"
        game "Test" { mapper: NROM }
        palette Main @palette("art/main.png")
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.palettes.len(), 1);
    assert_eq!(prog.palettes[0].name, "Main");
    assert!(prog.palettes[0].colors.is_empty());
    assert_eq!(prog.palettes[0].png_source.as_deref(), Some("art/main.png"));
}

#[test]
fn parse_palette_decl_rejects_wrong_directive() {
    // The shortcut form insists the directive be `@palette`, not
    // some other `@foo`. We want a clear error the first time
    // someone confuses `@chr` / `@palette` / `@nametable`.
    let src = r#"
        game "Test" { mapper: NROM }
        palette Main @chr("art/main.png")
        on frame { wait_frame }
        start Main
    "#;
    let (_, diags) = parse(src);
    assert!(
        diags
            .iter()
            .any(|d: &crate::errors::Diagnostic| d.message.contains("@palette")),
        "expected diagnostic about @palette, got: {diags:?}"
    );
}

#[test]
fn parse_background_decl_from_png_source() {
    let src = r#"
        game "Test" { mapper: NROM }
        background Main @nametable("levels/stage1.png")
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.backgrounds.len(), 1);
    assert_eq!(prog.backgrounds[0].name, "Main");
    assert!(prog.backgrounds[0].tiles.is_empty());
    assert!(prog.backgrounds[0].attributes.is_empty());
    assert_eq!(
        prog.backgrounds[0].png_source.as_deref(),
        Some("levels/stage1.png")
    );
}

#[test]
fn parse_background_decl_without_attributes() {
    let src = r#"
        game "Test" { mapper: NROM }
        background Stage {
            tiles: [9, 9, 9]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.backgrounds[0].tiles, vec![9, 9, 9]);
    assert!(prog.backgrounds[0].attributes.is_empty());
}

#[test]
fn parse_set_palette_statement() {
    let src = r#"
        game "Test" { mapper: NROM }
        palette P { colors: [0x0F] }
        state Title {
            on frame {
                set_palette P
            }
        }
        start Title
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    assert_eq!(frame.statements.len(), 1);
    match &frame.statements[0] {
        Statement::SetPalette(name, _) => assert_eq!(name, "P"),
        other => panic!("expected SetPalette, got {other:?}"),
    }
}

#[test]
fn parse_load_background_statement() {
    let src = r#"
        game "Test" { mapper: NROM }
        background BG { tiles: [0] }
        state Title {
            on frame {
                load_background BG
            }
        }
        start Title
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    assert_eq!(frame.statements.len(), 1);
    match &frame.statements[0] {
        Statement::LoadBackground(name, _) => assert_eq!(name, "BG"),
        other => panic!("expected LoadBackground, got {other:?}"),
    }
}

// ── Audio subsystem: sfx / music declarations ──

#[test]
fn parse_sfx_decl_minimal() {
    let src = r#"
        game "T" { mapper: NROM }
        sfx Pickup {
            pitch: [0x60, 0x58, 0x50, 0x48]
            volume: [15, 12, 8, 4]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.sfx.len(), 1);
    let sfx = &prog.sfx[0];
    assert_eq!(sfx.name, "Pickup");
    assert_eq!(sfx.pitch, vec![0x60, 0x58, 0x50, 0x48]);
    assert_eq!(sfx.volume, vec![15, 12, 8, 4]);
    // Default duty is 2 (50% square).
    assert_eq!(sfx.duty, 2);
}

#[test]
fn parse_sfx_decl_with_duty() {
    let src = r#"
        game "T" { mapper: NROM }
        sfx Zap {
            duty: 3
            pitch: [0x20, 0x22, 0x24]
            volume: [15, 10, 5]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.sfx[0].duty, 3);
}

#[test]
fn parse_sfx_decl_rejects_mismatched_array_lengths() {
    let src = r#"
        game "T" { mapper: NROM }
        sfx Bad {
            pitch: [0x20, 0x22]
            volume: [15, 10, 5]
        }
        on frame { wait_frame }
        start Main
    "#;
    let (_, diags) = parse(src);
    assert!(
        diags.iter().any(crate::errors::Diagnostic::is_error),
        "mismatched pitch/volume lengths should error"
    );
}

#[test]
fn parse_sfx_decl_rejects_volume_over_15() {
    let src = r#"
        game "T" { mapper: NROM }
        sfx Bad {
            pitch: [0x20]
            volume: [16]
        }
        on frame { wait_frame }
        start Main
    "#;
    let (_, diags) = parse(src);
    assert!(
        diags.iter().any(crate::errors::Diagnostic::is_error),
        "volume > 15 should error"
    );
}

#[test]
fn parse_sfx_decl_rejects_duty_over_3() {
    let src = r#"
        game "T" { mapper: NROM }
        sfx Bad {
            duty: 4
            pitch: [0x20]
            volume: [8]
        }
        on frame { wait_frame }
        start Main
    "#;
    let (_, diags) = parse(src);
    assert!(
        diags.iter().any(crate::errors::Diagnostic::is_error),
        "duty > 3 should error"
    );
}

#[test]
fn parse_sfx_decl_defaults_channel_to_pulse1() {
    // Existing declarations (which never set `channel:`) should
    // default to `Channel::Pulse1` so their codegen path is
    // unchanged.
    let src = r#"
        game "T" { mapper: NROM }
        sfx Pickup {
            duty: 2
            pitch: [0x50, 0x48]
            volume: [15, 8]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.sfx[0].channel, crate::parser::ast::Channel::Pulse1);
}

#[test]
fn parse_sfx_decl_with_noise_channel() {
    let src = r#"
        game "T" { mapper: NROM }
        sfx Zap {
            channel: noise
            pitch: 5
            volume: [15, 10, 5]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.sfx.len(), 1);
    assert_eq!(prog.sfx[0].channel, crate::parser::ast::Channel::Noise);
    assert_eq!(prog.sfx[0].pitch, vec![5, 5, 5]);
    assert_eq!(prog.sfx[0].volume, vec![15, 10, 5]);
}

#[test]
fn parse_sfx_decl_with_triangle_channel() {
    let src = r#"
        game "T" { mapper: NROM }
        sfx Bass {
            channel: triangle
            pitch: 60
            volume: [1, 1, 1, 1, 1]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.sfx[0].channel, crate::parser::ast::Channel::Triangle);
    assert_eq!(prog.sfx[0].pitch, vec![60; 5]);
}

#[test]
fn parse_sfx_decl_rejects_unknown_channel() {
    let src = r#"
        game "T" { mapper: NROM }
        sfx Bad {
            channel: bogus
            pitch: 5
            volume: [8]
        }
        on frame { wait_frame }
        start Main
    "#;
    let (_, diags) = parse(src);
    assert!(
        diags.iter().any(crate::errors::Diagnostic::is_error),
        "unknown channel name should error"
    );
}

#[test]
fn parse_music_decl_minimal() {
    let src = r#"
        game "T" { mapper: NROM }
        music Theme {
            notes: [37, 8, 41, 8, 44, 8, 49, 16]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.music.len(), 1);
    let m = &prog.music[0];
    assert_eq!(m.name, "Theme");
    assert_eq!(m.notes.len(), 4);
    assert_eq!(m.notes[0].pitch, 37);
    assert_eq!(m.notes[0].duration, 8);
    assert_eq!(m.notes[3].pitch, 49);
    assert_eq!(m.notes[3].duration, 16);
    // Default music loops.
    assert!(m.loops);
}

#[test]
fn parse_music_decl_with_full_properties() {
    let src = r#"
        game "T" { mapper: NROM }
        music Victory {
            duty: 0
            volume: 12
            repeat: false
            notes: [37, 10, 41, 10, 44, 10, 49, 20]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    let m = &prog.music[0];
    assert_eq!(m.duty, 0);
    assert_eq!(m.volume, 12);
    assert!(!m.loops, "repeat: false should disable looping");
}

#[test]
fn parse_music_decl_rejects_odd_note_count() {
    let src = r#"
        game "T" { mapper: NROM }
        music Bad {
            notes: [37, 8, 41]
        }
        on frame { wait_frame }
        start Main
    "#;
    let (_, diags) = parse(src);
    assert!(
        diags.iter().any(crate::errors::Diagnostic::is_error),
        "odd note count should error — notes must come in (pitch, duration) pairs"
    );
}

#[test]
fn parse_music_decl_rejects_pitch_above_60() {
    let src = r#"
        game "T" { mapper: NROM }
        music Bad {
            notes: [100, 8]
        }
        on frame { wait_frame }
        start Main
    "#;
    let (_, diags) = parse(src);
    assert!(
        diags.iter().any(crate::errors::Diagnostic::is_error),
        "pitch above 60 should error"
    );
}

#[test]
fn parse_music_decl_rejects_zero_duration() {
    let src = r#"
        game "T" { mapper: NROM }
        music Bad {
            notes: [37, 0]
        }
        on frame { wait_frame }
        start Main
    "#;
    let (_, diags) = parse(src);
    assert!(
        diags.iter().any(crate::errors::Diagnostic::is_error),
        "zero duration should error"
    );
}

#[test]
fn parse_play_and_start_music_statements() {
    let src = r#"
        game "T" { mapper: NROM }
        on frame {
            play coin
            start_music theme
            stop_music
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let stmts = &prog.states[0].on_frame.as_ref().unwrap().statements;
    assert!(matches!(&stmts[0], Statement::Play(n, _) if n == "coin"));
    assert!(matches!(&stmts[1], Statement::StartMusic(n, _) if n == "theme"));
    assert!(matches!(&stmts[2], Statement::StopMusic(_)));
}

// ── Milestone 4: Optimization & Polish ──

#[test]
fn parse_cast_expression() {
    let src = r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        var y: u16 = 0
        on frame {
            y = x as u16
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::Assign(_, _, Expr::Cast(inner, target_type, _), _) => {
            assert!(matches!(inner.as_ref(), Expr::Ident(name, _) if name == "x"));
            assert_eq!(*target_type, NesType::U16);
        }
        other => panic!("expected assignment with Cast, got {other:?}"),
    }
}

#[test]
fn parse_scroll_statement() {
    let src = r#"
        game "Test" { mapper: NROM }
        var px: u8 = 0
        var py: u8 = 0
        on frame {
            scroll(px, py)
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    assert_eq!(frame.statements.len(), 1);
    match &frame.statements[0] {
        Statement::Scroll(x, y, _) => {
            assert!(matches!(x, Expr::Ident(name, _) if name == "px"));
            assert!(matches!(y, Expr::Ident(name, _) if name == "py"));
        }
        other => panic!("expected Scroll, got {other:?}"),
    }
}

// ── Milestone 5: Bank Switching & Release ──

#[test]
fn parse_mmc1_mapper() {
    let src = r#"
        game "Test" { mapper: MMC1 }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.game.mapper, Mapper::MMC1);
}

#[test]
fn parse_uxrom_mapper() {
    let src = r#"
        game "Test" { mapper: UxROM }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.game.mapper, Mapper::UxROM);
}

#[test]
fn parse_mmc3_mapper() {
    let src = r#"
        game "Test" { mapper: MMC3 }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.game.mapper, Mapper::MMC3);
}

#[test]
fn parse_semicolon_separators() {
    // `;` should act as an optional statement separator so short
    // statements can share a line.
    let src = r#"
        game "Test" { mapper: NROM }
        var a: u8 = 0
        var b: u8 = 0
        on frame {
            a += 1; b += 2
            if button.a { a -= 1; b -= 1 }
            wait_frame
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    // Top-level statements: two assigns + if + wait_frame
    assert_eq!(frame.statements.len(), 4);
}

#[test]
fn parse_match_statement() {
    let src = r#"
        game "Test" { mapper: NROM }
        enum State { Title, Playing, GameOver }
        var s: u8 = Title
        on frame {
            match s {
                Title => { s = Playing }
                Playing => { s = GameOver }
                _ => {}
            }
            wait_frame
        }
        start Main
    "#;
    // Match desugars to an If, so after parsing the first statement
    // inside the frame handler should be an If with two elifs and an
    // else.
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::If(_, _, elifs, else_block, _) => {
            assert_eq!(elifs.len(), 1, "expected 1 else-if, got {elifs:?}");
            assert!(else_block.is_some(), "expected an else block for `_`");
        }
        _ => panic!("expected If, got {:?}", frame.statements[0]),
    }
}

#[test]
fn parse_for_loop() {
    let src = r#"
        game "Test" { mapper: NROM }
        var sum: u8 = 0
        on frame {
            for i in 0..10 {
                sum += i
            }
            wait_frame
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    assert!(
        matches!(&frame.statements[0], Statement::For { var, .. } if var == "i"),
        "expected for loop, got {:?}",
        frame.statements[0]
    );
}

#[test]
fn parse_for_loop_with_const_bounds() {
    let src = r#"
        game "Test" { mapper: NROM }
        const START: u8 = 5
        const END: u8 = 15
        var total: u8 = 0
        on frame {
            for n in START..END { total += n }
            wait_frame
        }
        start Main
    "#;
    parse_ok(src);
}

#[test]
fn parse_audio_statements() {
    let src = r#"
        game "Audio" { mapper: NROM }
        on frame {
            play JumpSfx
            start_music MainTheme
            stop_music
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    assert!(matches!(frame.statements[0], Statement::Play(ref n, _) if n == "JumpSfx"));
    assert!(matches!(
        frame.statements[1],
        Statement::StartMusic(ref n, _) if n == "MainTheme"
    ));
    assert!(matches!(frame.statements[2], Statement::StopMusic(_)));
}

#[test]
fn parse_struct_decl() {
    let src = r#"
        game "Test" { mapper: NROM }
        struct Vec2 { x: u8, y: u8 }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.structs.len(), 1);
    assert_eq!(prog.structs[0].name, "Vec2");
    assert_eq!(prog.structs[0].fields.len(), 2);
    assert_eq!(prog.structs[0].fields[0].name, "x");
    assert_eq!(prog.structs[0].fields[1].name, "y");
}

#[test]
fn parse_struct_literal_expr() {
    let src = r#"
        game "Test" { mapper: NROM }
        struct Vec2 { x: u8, y: u8 }
        var pos: Vec2 = Vec2 { x: 10, y: 20 }
        on frame {
            pos = Vec2 { x: 1, y: 2 }
        }
        start Main
    "#;
    parse_ok(src);
}

#[test]
fn parse_struct_literal_in_if_condition_must_be_paren() {
    // `if x == Vec2 { ... }` is ambiguous: the `{` could be the if
    // block or the start of a struct literal. Without parens, the
    // parser should treat the struct literal fields as the if body.
    // This test just asserts the parser doesn't crash and doesn't
    // misinterpret the condition.
    let src = r#"
        game "Test" { mapper: NROM }
        struct Vec2 { x: u8, y: u8 }
        var pos: Vec2
        on frame {
            if pos.x == 5 { pos = Vec2 { x: 0, y: 0 } }
        }
        start Main
    "#;
    parse_ok(src);
}

#[test]
fn parse_struct_field_access_expr() {
    let src = r#"
        game "Test" { mapper: NROM }
        struct Vec2 { x: u8, y: u8 }
        var pos: Vec2
        on frame {
            pos.x = 10
            pos.y = pos.x
        }
        start Main
    "#;
    parse_ok(src);
}

#[test]
fn parse_enum_decl() {
    let src = r#"
        game "Test" { mapper: NROM }
        enum Direction { Up, Down, Left, Right }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.enums.len(), 1);
    assert_eq!(prog.enums[0].name, "Direction");
    assert_eq!(prog.enums[0].variants.len(), 4);
    assert_eq!(prog.enums[0].variants[0].0, "Up");
    assert_eq!(prog.enums[0].variants[3].0, "Right");
}

#[test]
fn parse_enum_trailing_comma_optional() {
    let src = r#"
        game "Test" { mapper: NROM }
        enum Flag { On, Off, }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.enums[0].variants.len(), 2);
}

#[test]
fn parse_multiple_start_declarations_error() {
    let src = r#"
        game "Test" { mapper: NROM }
        state A { on frame { wait_frame } }
        state B { on frame { wait_frame } }
        start A
        start B
    "#;
    let errors = parse_err(src);
    assert!(
        errors.contains(&crate::errors::ErrorCode::E0505),
        "duplicate start should produce E0505, got: {errors:?}"
    );
}

#[test]
fn parse_on_scanline_handler() {
    let src = r#"
        game "Test" { mapper: MMC3 }
        state Main {
            on frame { wait_frame }
            on scanline(120) { scroll(0, 0) }
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let state = prog.states.iter().find(|s| s.name == "Main").unwrap();
    assert_eq!(state.on_scanline.len(), 1);
    assert_eq!(state.on_scanline[0].0, 120);
}

#[test]
fn parse_multiple_on_scanline_handlers() {
    let src = r#"
        game "Test" { mapper: MMC3 }
        state Main {
            on frame { wait_frame }
            on scanline(64) { scroll(0, 0) }
            on scanline(192) { scroll(8, 0) }
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let state = prog.states.iter().find(|s| s.name == "Main").unwrap();
    assert_eq!(state.on_scanline.len(), 2);
    assert_eq!(state.on_scanline[0].0, 64);
    assert_eq!(state.on_scanline[1].0, 192);
}

#[test]
fn parse_bank_decl() {
    let src = r#"
        game "Test" { mapper: NROM }
        bank Level1Data: prg
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.banks.len(), 1);
    assert_eq!(prog.banks[0].name, "Level1Data");
    assert_eq!(prog.banks[0].bank_type, BankType::Prg);
}

// ── Edge cases and regression tests ──

#[test]
fn draw_followed_by_statement() {
    // Regression: draw keyword-arg parser used to consume the next statement's
    // identifier as a keyword arg, causing "expected ':'" errors.
    let src = r#"
        game "T" { mapper: NROM }
        var i: u8 = 0
        on frame {
            draw Sprite at: (0, 0)
            i += 1
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    assert_eq!(frame.statements.len(), 2); // draw + assignment
}

#[test]
fn draw_with_frame_followed_by_statement() {
    let src = r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        on frame {
            draw Sprite at: (0, 0) frame: 1
            x = 5
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    assert_eq!(frame.statements.len(), 2);
}

#[test]
fn nested_if_else_chain() {
    let src = r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        on frame {
            if x == 0 {
                x = 1
            } else if x == 1 {
                x = 2
            } else if x == 2 {
                x = 3
            } else {
                x = 0
            }
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::If(_, _, else_ifs, else_block, _) => {
            assert_eq!(else_ifs.len(), 2);
            assert!(else_block.is_some());
        }
        other => panic!("expected If, got {other:?}"),
    }
}

#[test]
fn deeply_nested_blocks() {
    let src = r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        on frame {
            if x == 0 {
                if x == 0 {
                    if x == 0 {
                        if x == 0 {
                            x = 1
                        }
                    }
                }
            }
        }
        start Main
    "#;
    parse_ok(src); // should not stack overflow
}

#[test]
fn empty_function_body() {
    let src = r#"
        game "T" { mapper: NROM }
        fun noop() {}
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.functions.len(), 1);
    assert!(prog.functions[0].body.statements.is_empty());
}

#[test]
fn empty_state_handlers() {
    let src = r#"
        game "T" { mapper: NROM }
        state Main {
            on enter {}
            on exit {}
            on frame {}
        }
        start Main
    "#;
    let prog = parse_ok(src);
    assert!(prog.states[0]
        .on_enter
        .as_ref()
        .unwrap()
        .statements
        .is_empty());
    assert!(prog.states[0]
        .on_exit
        .as_ref()
        .unwrap()
        .statements
        .is_empty());
    assert!(prog.states[0]
        .on_frame
        .as_ref()
        .unwrap()
        .statements
        .is_empty());
}

#[test]
fn button_start_in_condition() {
    // "start" is a keyword but valid as a button name
    let src = r#"
        game "T" { mapper: NROM }
        on frame {
            if button.start { wait_frame }
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::If(Expr::ButtonRead(_, button, _), _, _, _, _) => {
            assert_eq!(button, "start");
        }
        other => panic!("expected if with button.start, got {other:?}"),
    }
}

#[test]
fn button_select_in_condition() {
    let src = r#"
        game "T" { mapper: NROM }
        on frame {
            if button.select { wait_frame }
        }
        start Main
    "#;
    parse_ok(src); // "select" is a keyword too — must parse as button name
}

#[test]
fn multiple_draws_in_sequence() {
    let src = r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        on frame {
            draw A at: (0, 0)
            draw B at: (10, 10)
            draw C at: (20, 20)
            x += 1
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    assert_eq!(frame.statements.len(), 4); // 3 draws + 1 assignment
}

#[test]
fn parser_no_panic_on_garbage() {
    // The parser should never panic, only return errors.
    let garbage_inputs = [
        "",
        "{}{}{}",
        "game",
        "game \"\"",
        "game \"\" {",
        "game \"\" { mapper: }",
        "var : = 0",
        "fun () {}",
        "if if if",
        "while { }",
        "draw",
        "draw X",
        "draw X at:",
        "draw X at: (",
        "draw X at: (0",
        "draw X at: (0,",
        "draw X at: (0, 0",
        "sprite {",
        "palette { colors: }",
        "[[[",
        "))))",
        "0x 0b",
        "\"unterminated",
        "/* no block comments */",
        "!@#$%",
        &"x ".repeat(1000), // long input
    ];
    for input in &garbage_inputs {
        let _ = parse(input); // must not panic
    }
}

#[test]
fn lexer_no_panic_on_garbage() {
    use crate::lexer::lex;
    let garbage_inputs = [
        "\0\0\0",
        "\x01\x02\x03",
        "\"\\",
        "0x",
        "0b",
        "99999999999999999999",
        "0xFFFFFFFFFF",
        &"a".repeat(10000),
        "!!!!!!",
        "\t\r\n \t\r\n",
    ];
    for input in &garbage_inputs {
        let _ = lex(input); // must not panic
    }
}

// ── Code review regression tests ──

#[test]
fn unterminated_call_args_no_hang() {
    // Regression: parser used to infinite-loop on missing RParen in call args
    let _ = parse(r#"game "T" { mapper: NROM } on frame { foo(1, 2 } start Main"#);
    let _ = parse(r#"game "T" { mapper: NROM } var x: u8 = foo(1"#);
    // Must return (possibly with errors), not hang
}

#[test]
fn array_index_compound_assign() {
    // Regression: parse_assign_op was missing &= |= ^= for array elements
    let src = r#"
        game "T" { mapper: NROM }
        var buf: u8[4] = [0, 0, 0, 0]
        on frame {
            buf[0] &= 0x0F
            buf[1] |= 0x80
            buf[2] ^= 0xFF
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    assert_eq!(frame.statements.len(), 3);
}

#[test]
fn parse_p1_button_read() {
    let src = r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        on frame {
            if p1.button.a { x += 1 }
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::If(Expr::ButtonRead(Some(Player::P1), button, _), _, _, _, _) => {
            assert_eq!(button, "a");
        }
        other => panic!("expected P1 button read, got {other:?}"),
    }
}

#[test]
fn parse_p2_button_read() {
    let src = r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        on frame {
            if p2.button.start { x += 1 }
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::If(Expr::ButtonRead(Some(Player::P2), button, _), _, _, _, _) => {
            assert_eq!(button, "start");
        }
        other => panic!("expected P2 button read, got {other:?}"),
    }
}

#[test]
fn parse_shift_assign_operators() {
    let src = r#"
        game "T" { mapper: NROM }
        var x: u8 = 1
        on frame {
            x <<= 1
            x >>= 1
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    assert_eq!(frame.statements.len(), 2);
}

#[test]
fn parse_debug_log() {
    let src = r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        on frame {
            debug.log(x)
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::DebugLog(args, _) => assert_eq!(args.len(), 1),
        other => panic!("expected DebugLog, got {other:?}"),
    }
}

#[test]
fn parse_debug_log_multiple_args() {
    let src = r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        var y: u8 = 0
        on frame {
            debug.log(x, y, 42)
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    match &frame.statements[0] {
        Statement::DebugLog(args, _) => assert_eq!(args.len(), 3),
        other => panic!("expected DebugLog, got {other:?}"),
    }
}

#[test]
fn parse_debug_assert() {
    let src = r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        on frame {
            debug.assert(x == 0)
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    assert!(matches!(frame.statements[0], Statement::DebugAssert(..)));
}

#[test]
fn parse_debug_frame_overrun_count_expression() {
    // `debug.frame_overrun_count()` is an *expression* — distinct
    // from the `debug.log` / `debug.assert` *statements*. It should
    // parse to an Expr::DebugCall on the RHS of an assignment.
    let src = r#"
        game "T" { mapper: NROM }
        var n: u8 = 0
        on frame {
            n = debug.frame_overrun_count()
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    let stmt = &frame.statements[0];
    let Statement::Assign(_, _, rhs, _) = stmt else {
        panic!("expected assign, got {stmt:?}");
    };
    match rhs {
        Expr::DebugCall(method, args, _) => {
            assert_eq!(method, "frame_overrun_count");
            assert!(args.is_empty());
        }
        other => panic!("expected DebugCall expression, got {other:?}"),
    }
}

#[test]
fn parse_debug_frame_overran_in_assert() {
    // The flag-style query nests inside `debug.assert(...)` — i.e.
    // a debug-statement form whose argument is itself a
    // debug-expression form. This exercises both parser paths in
    // a single program.
    let src = r#"
        game "T" { mapper: NROM }
        on frame {
            debug.assert(not debug.frame_overran())
        }
        start Main
    "#;
    let prog = parse_ok(src);
    let frame = prog.states[0].on_frame.as_ref().unwrap();
    let Statement::DebugAssert(cond, _) = &frame.statements[0] else {
        panic!("expected DebugAssert");
    };
    let Expr::UnaryOp(UnaryOp::Not, inner, _) = cond else {
        panic!("expected not cond");
    };
    let Expr::DebugCall(method, _, _) = inner.as_ref() else {
        panic!("expected DebugCall inside not");
    };
    assert_eq!(method, "frame_overran");
}

// ── Named colour palettes ──

#[test]
fn parse_palette_with_named_colors_in_flat_list() {
    let src = r#"
        game "T" { mapper: NROM }
        palette Main {
            colors: [
                black, dk_blue, blue, sky_blue,
                black, dk_red, red, peach,
                black, dk_green, green, mint,
                black, dk_gray, lt_gray, white,
                black, dk_blue, blue, sky_blue,
                black, dk_red, red, peach,
                black, dk_green, green, mint,
                black, dk_gray, lt_gray, white
            ]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.palettes.len(), 1);
    assert_eq!(prog.palettes[0].colors.len(), 32);
    // `black` must resolve to the canonical `$0F` universal slot.
    assert_eq!(prog.palettes[0].colors[0], 0x0F);
    // `dk_blue` must resolve to `$01`.
    assert_eq!(prog.palettes[0].colors[1], 0x01);
}

#[test]
fn parse_palette_flat_colors_still_accept_hex() {
    // Backward compat: a pre-existing palette that uses raw bytes
    // must keep parsing identically.
    let src = r#"
        game "T" { mapper: NROM }
        palette Legacy {
            colors: [
                0x0F, 0x01, 0x11, 0x21,
                0x0F, 0x02, 0x12, 0x22,
                0x0F, 0x0C, 0x1C, 0x2C,
                0x0F, 0x0B, 0x1B, 0x2B,
                0x0F, 0x01, 0x11, 0x21,
                0x0F, 0x16, 0x27, 0x30,
                0x0F, 0x14, 0x24, 0x34,
                0x0F, 0x0B, 0x1B, 0x2B
            ]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.palettes[0].colors[0], 0x0F);
    assert_eq!(prog.palettes[0].colors[1], 0x01);
    assert_eq!(prog.palettes[0].colors[6], 0x12);
}

#[test]
fn parse_palette_with_grouped_subpalettes() {
    let src = r#"
        game "T" { mapper: NROM }
        palette Pretty {
            universal: black
            bg0: [dk_blue,  blue,   sky_blue]
            bg1: [dk_red,   red,    peach]
            bg2: [dk_green, green,  mint]
            bg3: [dk_gray,  lt_gray, white]
            sp0: [dk_blue,  blue,   sky_blue]
            sp1: [dk_red,   red,    peach]
            sp2: [dk_green, green,  mint]
            sp3: [dk_gray,  lt_gray, white]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    let colors = &prog.palettes[0].colors;
    assert_eq!(colors.len(), 32);
    // Every sub-palette's first byte must equal the universal
    // (black = $0F). This is the whole reason grouped form exists —
    // it auto-fixes the $3F10 mirror trap.
    for i in 0..8 {
        assert_eq!(
            colors[i * 4],
            0x0F,
            "sub-palette {i} universal byte should be black"
        );
    }
    assert_eq!(colors[1], 0x01); // dk_blue
    assert_eq!(colors[2], 0x11); // blue
    assert_eq!(colors[3], 0x21); // sky_blue
    assert_eq!(colors[5], 0x06); // bg1 dk_red
}

#[test]
fn parse_palette_grouped_without_universal_defaults_to_black() {
    let src = r#"
        game "T" { mapper: NROM }
        palette Pretty {
            bg0: [dk_blue, blue, sky_blue]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(
        prog.palettes[0].colors[0], 0x0F,
        "default universal = black"
    );
}

#[test]
fn parse_palette_grouped_allows_full_4_entry_slot_overriding_universal() {
    // Edge case: if the user provides all 4 colours for a slot, the
    // leading colour *overrides* the universal for that slot. This is
    // rarely useful but matches what a by-hand `colors:` list can do.
    let src = r#"
        game "T" { mapper: NROM }
        palette Mixed {
            universal: black
            bg0: [white, dk_blue, blue, sky_blue]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.palettes[0].colors[0], 0x30); // white overrides black
    assert_eq!(prog.palettes[0].colors[1], 0x01);
}

#[test]
fn parse_palette_rejects_mixing_flat_and_grouped_forms() {
    let src = r#"
        game "T" { mapper: NROM }
        palette Broken {
            colors: [0x0F, 0x01, 0x11, 0x21]
            bg0: [blue, sky_blue, white]
        }
        on frame { wait_frame }
        start Main
    "#;
    let diags = parse_err(src);
    assert!(
        diags.contains(&crate::errors::ErrorCode::E0201),
        "expected type-mismatch error for mixed palette form, got {diags:?}"
    );
}

#[test]
fn parse_palette_rejects_unknown_color_name() {
    let src = r#"
        game "T" { mapper: NROM }
        palette Bad {
            colors: [mauve, 0x01, 0x11, 0x21]
        }
        on frame { wait_frame }
        start Main
    "#;
    let diags = parse_err(src);
    assert!(diags.contains(&crate::errors::ErrorCode::E0201));
}

// ── Pixel-art sprites ──

#[test]
fn parse_sprite_with_pixel_art() {
    // A simple arrow. The lower-left `#` column is index 1 and the
    // right column is `@` = index 3, so we can check both planes.
    let src = r#"
        game "T" { mapper: NROM }
        sprite Arrow {
            pixels: [
                "........",
                "...##...",
                "..###...",
                ".####@@@",
                ".####@@@",
                "..###...",
                "...##...",
                "........"
            ]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.sprites.len(), 1);
    match &prog.sprites[0].chr_source {
        AssetSource::Inline(bytes) => {
            // 8×8 tile = 16 bytes of CHR.
            assert_eq!(bytes.len(), 16);
            // Row 3 (`. # # # # @ @ @`) is palette indices
            // `0 1 1 1 1 3 3 3`. Bitplane 0 (bit 0 of each index) is
            // `0 1 1 1 1 1 1 1` = 0b0111_1111 = 0x7F.
            // Bitplane 1 (bit 1 of each index) is `0 0 0 0 0 1 1 1`
            // = 0b0000_0111 = 0x07.
            assert_eq!(bytes[3], 0x7F, "row 3 plane 0");
            assert_eq!(bytes[11], 0x07, "row 3 plane 1");
        }
        _ => panic!("expected inline CHR bytes from pixel art"),
    }
}

#[test]
fn parse_sprite_pixel_art_multi_tile() {
    // 16×8 sprite → 2 tiles = 32 bytes, emitted in reading order.
    // (Escaped quotes because the pixel rows contain long `#` runs
    //  that collide with Rust's raw-string delimiter.)
    let filled = "\"################\"";
    let src = format!(
        "game \"T\" {{ mapper: NROM }}\n\
         sprite Wide {{\n\
             pixels: [{filled},{filled},{filled},{filled},\
                      {filled},{filled},{filled},{filled}]\n\
         }}\n\
         on frame {{ wait_frame }}\n\
         start Main\n"
    );
    let src = src.as_str();
    let prog = parse_ok(src);
    match &prog.sprites[0].chr_source {
        AssetSource::Inline(bytes) => {
            assert_eq!(bytes.len(), 32, "16x8 = 2 tiles = 32 bytes");
            // Every pixel is index 1: bitplane 0 = 0xFF, bitplane 1 = 0x00.
            for tile in 0..2 {
                for row in 0..8 {
                    assert_eq!(bytes[tile * 16 + row], 0xFF);
                    assert_eq!(bytes[tile * 16 + 8 + row], 0x00);
                }
            }
        }
        _ => panic!("expected inline CHR"),
    }
}

#[test]
fn parse_sprite_pixel_art_rejects_non_multiple_of_8() {
    let src = "\
        game \"T\" { mapper: NROM }\n\
        sprite Bad { pixels: [\"....\", \"####\", \"####\", \"....\"] }\n\
        on frame { wait_frame }\n\
        start Main\n\
    ";
    let diags = parse_err(src);
    assert!(diags.contains(&crate::errors::ErrorCode::E0201));
}

#[test]
fn parse_sprite_pixel_art_accepts_abc_alias() {
    // `.abc` is the vocabulary every NES tool uses for 2-bit pixel
    // art; the parser should accept it interchangeably with `.#%@`
    // and `.0123`. Two sprites written in the two forms must
    // encode to bit-identical CHR bytes.
    let letters = r#"
        game "T" { mapper: NROM }
        sprite A {
            pixels: [
                "........",
                "...aa...",
                "..abba..",
                ".abbccb.",
                ".abbccb.",
                "..abba..",
                "...aa...",
                "........"
            ]
        }
        on frame { wait_frame }
        start Main
    "#;
    let glyphs = r#"
        game "T" { mapper: NROM }
        sprite A {
            pixels: [
                "........",
                "...##...",
                "..#%%#..",
                ".#%%@@%.",
                ".#%%@@%.",
                "..#%%#..",
                "...##...",
                "........"
            ]
        }
        on frame { wait_frame }
        start Main
    "#;
    let p1 = parse_ok(letters);
    let p2 = parse_ok(glyphs);
    match (&p1.sprites[0].chr_source, &p2.sprites[0].chr_source) {
        (AssetSource::Inline(a), AssetSource::Inline(b)) => assert_eq!(a, b),
        _ => panic!("expected inline CHR on both sprites"),
    }
}

#[test]
fn parse_sprite_pixel_art_rejects_ragged_rows() {
    let src = r#"
        game "T" { mapper: NROM }
        sprite Bad {
            pixels: [
                "........",
                "......."
            ]
        }
        on frame { wait_frame }
        start Main
    "#;
    let diags = parse_err(src);
    assert!(diags.contains(&crate::errors::ErrorCode::E0201));
}

// ── SFX with scalar pitch + envelope alias ──

#[test]
fn parse_sfx_with_scalar_pitch_and_envelope_alias() {
    let src = r#"
        game "T" { mapper: NROM }
        sfx Pickup {
            duty: 2
            pitch: 0x50
            envelope: [15, 12, 9, 6, 3]
        }
        on frame { play Pickup }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.sfx.len(), 1);
    let s = &prog.sfx[0];
    // Scalar pitch expands to repeat for every envelope frame.
    assert_eq!(s.pitch, vec![0x50; 5]);
    assert_eq!(s.volume, vec![15, 12, 9, 6, 3]);
}

#[test]
fn parse_sfx_with_legacy_pitch_array_still_works() {
    let src = r#"
        game "T" { mapper: NROM }
        sfx Pickup {
            duty: 2
            pitch: [0x50, 0x50, 0x50]
            volume: [15, 10, 5]
        }
        on frame { play Pickup }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.sfx[0].pitch, vec![0x50, 0x50, 0x50]);
    assert_eq!(prog.sfx[0].volume, vec![15, 10, 5]);
}

#[test]
fn parse_sfx_rejects_mixing_volume_and_envelope() {
    let src = r#"
        game "T" { mapper: NROM }
        sfx Bad {
            pitch: 0x50
            volume: [10]
            envelope: [10]
        }
        on frame { play Bad }
        start Main
    "#;
    let diags = parse_err(src);
    assert!(diags.contains(&crate::errors::ErrorCode::E0201));
}

// ── Music with note names + tempo ──

#[test]
fn parse_music_with_note_names_and_tempo_default() {
    let src = r#"
        game "T" { mapper: NROM }
        music Theme {
            duty: 2
            volume: 10
            repeat: true
            tempo: 20
            notes: [C4, E4, G4, C5, G4, E4]
        }
        on frame { start_music Theme }
        start Main
    "#;
    let prog = parse_ok(src);
    let t = &prog.music[0];
    assert_eq!(t.notes.len(), 6);
    // C4 is index 37, E4 = 41, G4 = 44, C5 = 49.
    assert_eq!(t.notes[0].pitch, 37);
    assert_eq!(t.notes[0].duration, 20); // from tempo
    assert_eq!(t.notes[1].pitch, 41);
    assert_eq!(t.notes[2].pitch, 44);
    assert_eq!(t.notes[3].pitch, 49);
    assert_eq!(t.notes[3].duration, 20);
}

#[test]
fn parse_music_with_per_note_duration_override() {
    let src = r#"
        game "T" { mapper: NROM }
        music Theme {
            tempo: 20
            notes: [
                C4,
                E4 40,
                rest 10,
                G4
            ]
        }
        on frame { start_music Theme }
        start Main
    "#;
    let prog = parse_ok(src);
    let t = &prog.music[0];
    assert_eq!(t.notes[0].pitch, 37);
    assert_eq!(t.notes[0].duration, 20);
    assert_eq!(t.notes[1].pitch, 41);
    assert_eq!(t.notes[1].duration, 40); // override
    assert_eq!(t.notes[2].pitch, 0); // rest
    assert_eq!(t.notes[2].duration, 10);
    assert_eq!(t.notes[3].pitch, 44);
    assert_eq!(t.notes[3].duration, 20);
}

#[test]
fn parse_music_enharmonic_note_names() {
    let src = r#"
        game "T" { mapper: NROM }
        music Theme {
            tempo: 10
            notes: [Cs4, Db4, Ds4, Eb4]
        }
        on frame { start_music Theme }
        start Main
    "#;
    let prog = parse_ok(src);
    let t = &prog.music[0];
    // Cs4 == Db4 and Ds4 == Eb4.
    assert_eq!(t.notes[0].pitch, t.notes[1].pitch);
    assert_eq!(t.notes[2].pitch, t.notes[3].pitch);
}

#[test]
fn parse_music_legacy_flat_pair_form_still_works() {
    // No `tempo:` → legacy (pitch, duration) pair form.
    let src = r#"
        game "T" { mapper: NROM }
        music Theme {
            duty: 2
            volume: 10
            notes: [
                37, 20,
                41, 20,
                44, 20
            ]
        }
        on frame { start_music Theme }
        start Main
    "#;
    let prog = parse_ok(src);
    let t = &prog.music[0];
    assert_eq!(t.notes.len(), 3);
    assert_eq!(t.notes[0].pitch, 37);
    assert_eq!(t.notes[0].duration, 20);
}

#[test]
fn parse_music_rejects_unknown_note_name() {
    let src = r#"
        game "T" { mapper: NROM }
        music Theme {
            tempo: 20
            notes: [C4, Z9, G4]
        }
        on frame { start_music Theme }
        start Main
    "#;
    let diags = parse_err(src);
    assert!(diags.contains(&crate::errors::ErrorCode::E0201));
}

// ── Background tilemap + legend + palette_map ──

#[test]
fn parse_background_with_tilemap_and_legend() {
    let src = r##"
        game "T" { mapper: NROM }
        background StageOne {
            legend {
                ".": 0
                "#": 1
                "X": 2
            }
            map: [
                "................................",
                "................................",
                "......##........##..............",
                "....##..##....##..##............"
            ]
        }
        on frame { wait_frame }
        start Main
    "##;
    let prog = parse_ok(src);
    assert_eq!(prog.backgrounds.len(), 1);
    let tiles = &prog.backgrounds[0].tiles;
    // Four rows × 32 cells = 128 bytes declared.
    assert_eq!(tiles.len(), 128);
    // Row 2 (index 2*32 = 64), columns 6 and 7 should be tile 1.
    assert_eq!(tiles[2 * 32 + 6], 1);
    assert_eq!(tiles[2 * 32 + 7], 1);
    // Column 5 of row 2 is still the empty tile 0.
    assert_eq!(tiles[2 * 32 + 5], 0);
}

#[test]
fn parse_background_map_short_rows_pad_to_32_cells() {
    let src = "\
        game \"T\" { mapper: NROM }\n\
        background StageOne {\n\
            legend { \".\": 0, \"#\": 1 }\n\
            map: [\"##\", \"#.\"]\n\
        }\n\
        on frame { wait_frame }\n\
        start Main\n\
    ";
    let prog = parse_ok(src);
    let tiles = &prog.backgrounds[0].tiles;
    // 2 rows × 32 cols = 64 bytes. First two cells of row 0 are 1,
    // rest of row 0 is 0.
    assert_eq!(tiles.len(), 64);
    assert_eq!(tiles[0], 1);
    assert_eq!(tiles[1], 1);
    assert_eq!(tiles[2], 0);
    assert_eq!(tiles[32], 1); // row 1 col 0
    assert_eq!(tiles[33], 0); // row 1 col 1
}

#[test]
fn parse_background_map_rejects_unknown_legend_char() {
    let src = r##"
        game "T" { mapper: NROM }
        background Bad {
            legend { ".": 0, "#": 1 }
            map: ["..?.."]
        }
        on frame { wait_frame }
        start Main
    "##;
    let diags = parse_err(src);
    assert!(diags.contains(&crate::errors::ErrorCode::E0201));
}

#[test]
fn parse_background_map_requires_legend() {
    let src = r#"
        game "T" { mapper: NROM }
        background Bad {
            map: ["..##.."]
        }
        on frame { wait_frame }
        start Main
    "#;
    let diags = parse_err(src);
    assert!(diags.contains(&crate::errors::ErrorCode::E0201));
}

#[test]
fn parse_background_palette_map_packs_attributes() {
    let src = r#"
        game "T" { mapper: NROM }
        background Stage {
            legend { ".": 0 }
            map: ["................................"]
            palette_map: [
                "0011001100110011",
                "0011001100110011"
            ]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    let attrs = &prog.backgrounds[0].attributes;
    assert_eq!(attrs.len(), 64, "always packs to 64 attribute bytes");
    // Attribute byte [0,0] covers metatiles at:
    //   TL = grid[0][0] = 0
    //   TR = grid[0][1] = 0
    //   BL = grid[1][0] = 0
    //   BR = grid[1][1] = 0
    // So byte[0] = 0.
    assert_eq!(attrs[0], 0);
    // Byte [0,1] covers metatiles:
    //   TL = grid[0][2] = 1  TR = grid[0][3] = 1
    //   BL = grid[1][2] = 1  BR = grid[1][3] = 1
    // = (1) | (1 << 2) | (1 << 4) | (1 << 6) = 0x55
    assert_eq!(attrs[1], 0x55);
}

#[test]
fn parse_background_palette_map_15_rows_replicates_off_screen_row() {
    // When a program only declares 15 rows (the visible metatile
    // grid), the parser should replicate the bottom row into the
    // off-screen 16th row so the last attribute byte's bottom half
    // picks up the same sub-palette as the visible bottom.
    let src = r#"
        game "T" { mapper: NROM }
        background Stage {
            legend { ".": 0 }
            map: ["................................"]
            palette_map: [
                "2222222222222222",
                "2222222222222222",
                "2222222222222222",
                "2222222222222222",
                "2222222222222222",
                "2222222222222222",
                "2222222222222222",
                "2222222222222222",
                "2222222222222222",
                "2222222222222222",
                "2222222222222222",
                "2222222222222222",
                "2222222222222222",
                "2222222222222222",
                "2222222222222222"
            ]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    let attrs = &prog.backgrounds[0].attributes;
    // Every byte covers 4 metatiles at sub-palette 2, so each
    // byte should be 0b10_10_10_10 = 0xAA. Crucially, the last
    // attribute row (bytes 56-63) must also be 0xAA — if the
    // auto-replicate didn't happen, bytes 56-63 would be 0x0A
    // (top-half 2, bottom-half 0) since the 16th metatile row
    // would default to sub-palette 0.
    for b in attrs {
        assert_eq!(*b, 0xAA, "every attribute byte should be 2s");
    }
}

#[test]
fn parse_background_palette_map_16_rows_accepted() {
    // The parser accepts an explicit 16th row for programs that
    // want full control over the off-screen attribute byte.
    let src = r#"
        game "T" { mapper: NROM }
        background Stage {
            legend { ".": 0 }
            map: ["................................"]
            palette_map: [
                "1111111111111111", "1111111111111111",
                "1111111111111111", "1111111111111111",
                "1111111111111111", "1111111111111111",
                "1111111111111111", "1111111111111111",
                "1111111111111111", "1111111111111111",
                "1111111111111111", "1111111111111111",
                "1111111111111111", "1111111111111111",
                "1111111111111111",
                "2222222222222222"
            ]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    let attrs = &prog.backgrounds[0].attributes;
    // The last attribute byte's top half covers metatile row 14
    // (sub-palette 1) and bottom half covers metatile row 15
    // (sub-palette 2). Byte = (1) | (1 << 2) | (2 << 4) | (2 << 6)
    // = 0x01 | 0x04 | 0x20 | 0x80 = 0xA5.
    assert_eq!(attrs[63], 0xA5);
}

#[test]
fn parse_background_palette_map_rejects_17_rows() {
    let src = r#"
        game "T" { mapper: NROM }
        background Bad {
            legend { ".": 0 }
            map: ["."]
            palette_map: [
                "0000000000000000", "0000000000000000",
                "0000000000000000", "0000000000000000",
                "0000000000000000", "0000000000000000",
                "0000000000000000", "0000000000000000",
                "0000000000000000", "0000000000000000",
                "0000000000000000", "0000000000000000",
                "0000000000000000", "0000000000000000",
                "0000000000000000", "0000000000000000",
                "0000000000000000"
            ]
        }
        on frame { wait_frame }
        start Main
    "#;
    let diags = parse_err(src);
    assert!(diags.contains(&crate::errors::ErrorCode::E0201));
}

#[test]
fn parse_background_raw_tiles_and_attributes_still_work() {
    // Backward compat: legacy inline byte arrays should keep parsing
    // identically.
    let src = r#"
        game "T" { mapper: NROM }
        background Legacy {
            tiles: [0, 1, 2, 3]
            attributes: [0xFF, 0x55]
        }
        on frame { wait_frame }
        start Main
    "#;
    let prog = parse_ok(src);
    assert_eq!(prog.backgrounds[0].tiles, vec![0, 1, 2, 3]);
    assert_eq!(prog.backgrounds[0].attributes, vec![0xFF, 0x55]);
}
