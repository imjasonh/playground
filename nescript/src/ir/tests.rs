use super::*;
use crate::analyzer;
use crate::parser;

fn lower_ok(input: &str) -> IrProgram {
    let (prog, diags) = parser::parse(input);
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let prog = prog.unwrap();
    let analysis = analyzer::analyze(&prog);
    assert!(
        analysis.diagnostics.iter().all(|d| !d.is_error()),
        "analysis errors: {:?}",
        analysis.diagnostics
    );
    lower(&prog, &analysis)
}

#[test]
fn lower_minimal_program() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var px: u8 = 128
        on frame { px = 1 }
        start Main
    "#,
    );
    assert_eq!(ir.globals.len(), 1);
    assert_eq!(ir.globals[0].name, "px");
    assert_eq!(ir.globals[0].init_value, Some(128));
    // Should have at least one function (the frame handler)
    assert!(!ir.functions.is_empty());
}

#[test]
fn lower_var_assignment() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame { x = 42 }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .unwrap();
    // Should have a StoreVar op
    let has_store = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::StoreVar(..)));
    assert!(has_store, "should emit StoreVar for assignment");
}

#[test]
fn lower_plus_assign() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame { x += 5 }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .unwrap();
    let has_add = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::Add(..)));
    assert!(has_add, "should emit Add for += operator");
}

#[test]
fn lower_if_creates_branch() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame {
            if x == 0 { x = 1 }
        }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .unwrap();
    let has_branch = frame_fn
        .blocks
        .iter()
        .any(|b| matches!(&b.terminator, IrTerminator::Branch(..)));
    assert!(
        has_branch,
        "if statement should produce a Branch terminator"
    );
}

#[test]
fn lower_while_creates_loop() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame {
            while x < 10 { x += 1 }
        }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .unwrap();
    // A while loop needs at least 3 blocks: condition check, body, and exit
    assert!(
        frame_fn.blocks.len() >= 3,
        "while should create multiple blocks, got {}",
        frame_fn.blocks.len()
    );
}

#[test]
fn lower_button_read() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var px: u8 = 0
        on frame {
            if button.right { px += 1 }
        }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .unwrap();
    let has_input = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::ReadInput(_, _)));
    assert!(has_input, "button read should emit ReadInput op");
}

#[test]
fn lower_draw_sprite() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var px: u8 = 0
        var py: u8 = 0
        on frame { draw Smiley at: (px, py) }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .unwrap();
    let has_draw = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::DrawSprite { .. }));
    assert!(has_draw, "should emit DrawSprite op");
}

#[test]
fn lower_constants_become_immediates() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        const SPEED: u8 = 3
        var px: u8 = 0
        on frame { px += SPEED }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .unwrap();
    // SPEED should be lowered to LoadImm(_, 3)
    let has_imm3 = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::LoadImm(_, 3)));
    assert!(has_imm3, "constant should be inlined as LoadImm");
}

#[test]
fn lower_const_expressions_constant_fold() {
    // Constants may reference earlier constants and use arithmetic.
    // `B` resolves to `A + 3` = 8 at lowering time.
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        const A: u8 = 5
        const B: u8 = A + 3
        var x: u8 = B
        on frame { wait_frame }
        start Main
    "#,
    );
    let x_global = ir.globals.iter().find(|g| g.name == "x").unwrap();
    assert_eq!(x_global.init_value, Some(8));
}

#[test]
fn lower_const_bit_ops() {
    // Bitwise constant folding should work for things like defining
    // flags or masks based on other constants.
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        const FLAG_A: u8 = 1
        const FLAG_B: u8 = 2
        const BOTH: u8 = FLAG_A | FLAG_B
        var x: u8 = BOTH
        on frame { wait_frame }
        start Main
    "#,
    );
    let x_global = ir.globals.iter().find(|g| g.name == "x").unwrap();
    assert_eq!(x_global.init_value, Some(3));
}

#[test]
fn lower_multiple_states() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        state Title {
            on enter { wait_frame }
            on frame { wait_frame }
        }
        state Game {
            on frame { wait_frame }
        }
        start Title
    "#,
    );
    // Should have: Title_enter, Title_frame, Game_frame
    assert!(
        ir.functions.len() >= 3,
        "should have at least 3 functions for 2 states, got {}",
        ir.functions.len()
    );
    let names: Vec<&str> = ir.functions.iter().map(|f| f.name.as_str()).collect();
    assert!(
        names.iter().any(|n| n.contains("Title_enter")),
        "should have Title_enter handler"
    );
    assert!(
        names.iter().any(|n| n.contains("Title_frame")),
        "should have Title_frame handler"
    );
    assert!(
        names.iter().any(|n| n.contains("Game_frame")),
        "should have Game_frame handler"
    );
}

#[test]
fn lower_op_count() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame { x = 1 }
        start Main
    "#,
    );
    assert!(ir.op_count() > 0, "should have some IR ops");
}

#[test]
fn lower_wait_frame() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        on frame { wait_frame }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .unwrap();
    let has_wait = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::WaitFrame));
    assert!(has_wait, "should emit WaitFrame op");
}

#[test]
fn lower_debug_frame_overrun_count_emits_peek() {
    // `debug.frame_overrun_count()` lowers to a Peek of the
    // canonical $07FF runtime address. The release-mode codegen
    // gating happens later — at the IR level we always emit the
    // Peek so the optimizer/codegen has a single uniform shape.
    let ir = lower_ok(
        r#"
        game "T" { mapper: NROM }
        var n: u8 = 0
        on frame {
            n = debug.frame_overrun_count()
            wait_frame
        }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .unwrap();
    let peek_addr = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .find_map(|op| match op {
            IrOp::Peek(_, addr) => Some(*addr),
            _ => None,
        });
    assert_eq!(
        peek_addr,
        Some(0x07FF),
        "expected Peek($07FF) for frame_overrun_count"
    );
}

#[test]
fn lower_metasprite_draw_expands_to_one_op_per_tile() {
    // `draw Hero at: (10, 20)` where Hero is a 4-tile metasprite
    // should lower to four `DrawSprite` ops, each with the
    // metasprite's underlying sprite name and one tile from the
    // declaration's `frame:` array (offset by the sprite's base
    // tile index — the runtime smiley occupies tile 0, so a
    // single-sprite program starts user tiles at 1).
    let ir = lower_ok(
        r#"
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
            frame: [0, 0, 0, 0]
        }
        on frame {
            draw Hero at: (10, 20)
            wait_frame
        }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .unwrap();
    let ops: Vec<&IrOp> = frame_fn.blocks.iter().flat_map(|b| &b.ops).collect();
    let draws: Vec<_> = ops
        .iter()
        .filter_map(|op| match op {
            IrOp::DrawSprite { sprite_name, .. } => Some(sprite_name.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(
        draws.len(),
        4,
        "metasprite with 4 tiles should expand to 4 DrawSprite ops"
    );
    for name in &draws {
        assert_eq!(
            name, "Tile",
            "expanded ops should target the underlying sprite"
        );
    }
    // Each tile in the metasprite uses `frame: 0` relative to
    // the underlying sprite. The single-sprite program has `Tile`
    // at base index 1 (smiley occupies 0), so the resolved
    // absolute frame index for every expanded DrawSprite is 1 —
    // we should see at least one `LoadImm(_, 1)` matching that.
    let load_imm_1_count = ops
        .iter()
        .filter(|op| matches!(op, IrOp::LoadImm(_, 1)))
        .count();
    assert!(
        load_imm_1_count >= 4,
        "metasprite expansion should LoadImm(_, 1) at least once per tile (sprite Tile sits at base index 1, frame: [0,0,0,0]); got {load_imm_1_count}"
    );
}

#[test]
fn lower_nested_struct_literal_init_expands_to_leaves() {
    // A `Hero { pos: Vec2 { x: 1, y: 2 }, hp: 100, inv: [3,4,5,6] }`
    // initializer must produce one IrGlobal per leaf field with the
    // right scalar `init_value` / per-element `init_array`. The
    // intermediate `hero.pos` is registered with `size: 0` so name
    // lookups still work but no separate init bytes are emitted.
    let ir = lower_ok(
        r#"
        game "T" { mapper: NROM }
        struct Vec2 { x: u8, y: u8 }
        struct Hero { pos: Vec2, hp: u8, inv: u8[4] }
        var hero: Hero = Hero { pos: Vec2 { x: 1, y: 2 }, hp: 100, inv: [3, 4, 5, 6] }
        on frame { wait_frame }
        start Main
    "#,
    );
    let by_name = |n: &str| {
        ir.globals
            .iter()
            .find(|g| g.name == n)
            .unwrap_or_else(|| panic!("missing global: {n}"))
    };
    let pos_x = by_name("hero.pos.x");
    let pos_y = by_name("hero.pos.y");
    let hp = by_name("hero.hp");
    let inv = by_name("hero.inv");
    assert_eq!(pos_x.init_value, Some(1));
    assert_eq!(pos_y.init_value, Some(2));
    assert_eq!(hp.init_value, Some(100));
    assert_eq!(inv.init_array, vec![3, 4, 5, 6]);
    // The intermediate must exist with size 0 so codegen can
    // resolve `hero.pos` lookups even though it carries no bytes.
    let pos = by_name("hero.pos");
    assert_eq!(pos.size, 0);
    assert_eq!(pos.init_value, None);
    assert!(pos.init_array.is_empty());
}

#[test]
fn lower_debug_frame_overran_emits_peek_07fe() {
    let ir = lower_ok(
        r#"
        game "T" { mapper: NROM }
        var n: u8 = 0
        on frame {
            n = debug.frame_overran()
            wait_frame
        }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .unwrap();
    let peek_addr = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .find_map(|op| match op {
            IrOp::Peek(_, addr) => Some(*addr),
            _ => None,
        });
    assert_eq!(
        peek_addr,
        Some(0x07FE),
        "expected Peek($07FE) for frame_overran"
    );
}

#[test]
fn array_literal_global_init_is_captured() {
    // Regression test: `var xs: u8[4] = [1, 2, 3, 4]` used to lose
    // its initializer because `eval_const` returns None for
    // `Expr::ArrayLiteral` and `init_value` ended up `None`. The
    // fix captures the per-element values in a new `init_array`
    // field so the IR codegen can emit one `LDA #imm; STA base+i`
    // per byte at startup.
    let ir = lower_ok(
        r#"
        game "Arr" { mapper: NROM }
        var xs: u8[4] = [1, 2, 3, 4]
        on frame { wait_frame }
        start Main
    "#,
    );
    let xs = ir
        .globals
        .iter()
        .find(|g| g.name == "xs")
        .expect("`xs` global should exist");
    assert_eq!(
        xs.init_array,
        vec![1, 2, 3, 4],
        "array literal initializer should populate init_array: {:?}",
        xs.init_array
    );
}

#[test]
fn for_loop_counter_is_registered_as_handler_local() {
    // Regression test for bug B's secondary fix: `for i in 0..N`
    // implicitly declares the counter `i`, and the lowering must
    // push it onto `current_locals` so the IR codegen can give
    // it a backing address. Without this entry, every
    // `LoadVar(i)` / `StoreVar(i)` in the desugared while loop
    // silently emitted no code (the codegen's `var_addrs` lookup
    // returned None), the counter stayed at 0, the loop spun
    // forever, and any `draw` inside the loop kept writing to
    // the first OAM slot with the index-0 array element.
    let ir = lower_ok(
        r#"
        game "ForCounter" { mapper: NROM }
        var xs: u8[4] = [1, 2, 3, 4]
        var out: u8 = 0
        on frame {
            for i in 0..4 {
                out = xs[i]
            }
        }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    assert!(
        frame_fn.locals.iter().any(|l| l.name == "i"),
        "for-loop counter `i` should be registered as a handler local: {:?}",
        frame_fn.locals
    );
}

// Regression tests: shift / div / mod used to miscompile silently.
// `x << n` with a literal `n` always emitted ShiftLeft(..., 1) and
// `x / n` / `x % n` always emitted LoadImm(..., 0). These tests
// anchor the fixes from the code-review cleanup pass.

#[test]
fn lower_shift_left_with_literal_count_uses_that_count() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var x: u8 = 1
        on frame { x = x << 3 }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let has_shift3 = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::ShiftLeft(_, _, 3)));
    assert!(
        has_shift3,
        "expected ShiftLeft with count=3, got ops: {:?}",
        frame_fn
            .blocks
            .iter()
            .flat_map(|b| &b.ops)
            .collect::<Vec<_>>()
    );
}

#[test]
fn lower_shift_right_with_variable_count_uses_runtime_variant() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var x: u8 = 128
        var n: u8 = 2
        on frame { x = x >> n }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let has_shift_var = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::ShiftRightVar(..)));
    assert!(
        has_shift_var,
        "expected ShiftRightVar for runtime shift amount, got ops: {:?}",
        frame_fn
            .blocks
            .iter()
            .flat_map(|b| &b.ops)
            .collect::<Vec<_>>()
    );
}

#[test]
fn lower_divide_emits_div_op_not_load_imm_zero() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var x: u8 = 100
        var d: u8 = 7
        var q: u8 = 0
        on frame { q = x / d }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let has_div = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::Div(..)));
    assert!(
        has_div,
        "expected IrOp::Div for `q = x / d`, got ops: {:?}",
        frame_fn
            .blocks
            .iter()
            .flat_map(|b| &b.ops)
            .collect::<Vec<_>>()
    );
}

#[test]
fn lower_set_palette_emits_ir_op() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        palette Cool { colors: [0x0F, 0x01, 0x11, 0x21] }
        palette Warm { colors: [0x0F, 0x06, 0x16, 0x26] }
        on frame { set_palette Warm }
        start Main
    "#,
    );
    let has_set_palette = ir
        .functions
        .iter()
        .flat_map(|f| &f.blocks)
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::SetPalette(name) if name == "Warm"));
    assert!(
        has_set_palette,
        "expected IrOp::SetPalette(Warm) in lowered IR"
    );
}

#[test]
fn lower_load_background_emits_ir_op() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        background Stage { tiles: [0, 1, 2] }
        on frame { load_background Stage }
        start Main
    "#,
    );
    let has_load_bg = ir
        .functions
        .iter()
        .flat_map(|f| &f.blocks)
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::LoadBackground(name) if name == "Stage"));
    assert!(
        has_load_bg,
        "expected IrOp::LoadBackground(Stage) in lowered IR"
    );
}

#[test]
fn lower_modulo_emits_mod_op_not_load_imm_zero() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var x: u8 = 17
        var d: u8 = 5
        var r: u8 = 0
        on frame { r = x % d }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let has_mod = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::Mod(..)));
    assert!(
        has_mod,
        "expected IrOp::Mod for `r = x % d`, got ops: {:?}",
        frame_fn
            .blocks
            .iter()
            .flat_map(|b| &b.ops)
            .collect::<Vec<_>>()
    );
}

#[test]
fn wide_hi_does_not_leak_between_functions() {
    // Regression test for the `wide_hi` leak bug fixed on the
    // War bug-cleanup branch (see `git log`): the IR lowerer's
    // `wide_hi` map used to persist across function boundaries
    // even though `next_temp` resets to 0 per function. A
    // function whose body had no u16 ops would inherit stale
    // `(temp_id -> high_byte)` entries from earlier functions
    // and emit `CmpEq16` (or other 16-bit ops) where the
    // destination temp aliased one of the source temps.
    //
    // The shape that reproduces it: function A bumps a u16
    // global (creating wide entries); function B does u8 ==
    // const compares against a u8 global. Pre-fix, function B's
    // last few comparisons would lower to `CmpEq16`. Post-fix,
    // they all stay narrow.
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var clock: u16 = 0
        var phase: u8 = 0
        var hits: u8 = 0
        fun bump_a() { hits += 1 }
        fun bump_b() { hits += 2 }
        fun bump_c() { hits += 3 }
        fun bump_d() { hits += 4 }
        on frame {
            clock += 1
            if phase == 0 { bump_a() }
            if phase == 1 { bump_b() }
            if phase == 2 { bump_c() }
            if phase == 3 { bump_d() }
            wait_frame
        }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let mut wide_eq_dest_aliases = 0;
    for op in frame_fn.blocks.iter().flat_map(|b| &b.ops) {
        if let IrOp::CmpEq16 {
            dest, b_hi, a_hi, ..
        } = op
        {
            // The dest of a 16-bit compare must never alias one
            // of its operand high bytes — that's the symptom of
            // the `wide_hi` leak bug.
            if dest == b_hi || dest == a_hi {
                wide_eq_dest_aliases += 1;
            }
        }
    }
    assert_eq!(
        wide_eq_dest_aliases, 0,
        "wide CmpEq16 destination aliased a source operand — wide_hi leaked between functions"
    );
}

#[test]
fn inline_fun_expression_body_emits_no_call_at_use_site() {
    // Regression test for the real-inlining feature added on
    // the War bug-cleanup branch (see `git log`): `inline fun`
    // with a single-return-expression body should be spliced
    // at every call site instead of emitting a Call op. The
    // lowered frame handler should contain zero Call ops
    // targeting the inline function.
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        inline fun shift_right_4(c: u8) -> u8 {
            return c >> 4
        }
        var out: u8 = 0
        on frame { out = shift_right_4(0x90) }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let any_call_to_inline = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::Call(_, name, _) if name == "shift_right_4"));
    assert!(
        !any_call_to_inline,
        "frame handler should not contain a Call to the inlined function; ops: {:?}",
        frame_fn
            .blocks
            .iter()
            .flat_map(|b| &b.ops)
            .collect::<Vec<_>>()
    );
}

#[test]
fn inline_fun_void_body_statements_are_spliced() {
    // Void `inline fun` with a multi-statement body (no
    // control flow) should be spliced at every statement-
    // context call site. `set_phase(P_FLY_A)` should lower
    // to two StoreVar ops (phase = P_FLY_A, phase_timer = 0)
    // rather than a Call op.
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        const P_WAIT: u8 = 0
        const P_FLY:  u8 = 1
        var phase: u8 = 0
        var phase_timer: u8 = 0
        inline fun set_phase(p: u8) {
            phase = p
            phase_timer = 0
        }
        on frame { set_phase(P_FLY) }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let any_call_to_inline = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::Call(_, name, _) if name == "set_phase"));
    assert!(
        !any_call_to_inline,
        "frame handler should not contain a Call to set_phase; ops: {:?}",
        frame_fn
            .blocks
            .iter()
            .flat_map(|b| &b.ops)
            .collect::<Vec<_>>()
    );
}

#[test]
fn inline_fun_with_conditional_return_compiles_as_regular_call() {
    // A conditional early-return body (wrap52-style) is too
    // complex for the simple inliner. It should gracefully
    // fall back to a regular Call op — this is the intended
    // behaviour, not a bug. The important thing is that the
    // fallback is correct, not that it's inlined.
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        inline fun wrap52(v: u8) -> u8 {
            if v >= 52 { return v - 52 }
            return v
        }
        var out: u8 = 0
        on frame { out = wrap52(60) }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let calls_wrap52 = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::Call(_, name, _) if name == "wrap52"));
    assert!(
        calls_wrap52,
        "wrap52 has conditional early return — it should fall back to a Call op"
    );
}

#[test]
fn inline_fun_with_asm_param_substitutes_immediate() {
    // An `inline fun` whose body contains an `asm { ... }` block
    // referencing parameters via `{name}` substitution. When the
    // call site passes compile-time constants, the splicer
    // pre-substitutes each `{param}` with its `#$<value>`
    // immediate so the spliced body parses correctly. The end
    // result should contain no Call op for the inlined fun, and
    // the frame handler's instruction stream (after lowering) is
    // expected to contain an `LDA #$2A` (= 42) — the substituted
    // immediate.
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var sink: u8 = 0
        inline fun stash(value: u8) {
            asm {
                LDA {value}
                STA {sink}
            }
        }
        on frame { stash(42) }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let any_call = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::Call(_, name, _) if name == "stash"));
    assert!(!any_call, "stash should be inlined, no Call op left");
    let asm_body = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .find_map(|op| match op {
            IrOp::InlineAsm(body) => Some(body.clone()),
            _ => None,
        })
        .expect("inlined asm block should be present");
    assert!(
        asm_body.contains("#$2A"),
        "asm body should contain the substituted immediate `#$2A`; got: {asm_body}"
    );
    assert!(
        !asm_body.contains("{value}"),
        "`{{value}}` should have been pre-substituted; got: {asm_body}"
    );
}

#[test]
fn inline_fun_with_asm_falls_back_for_runtime_arg() {
    // When the call site passes a runtime value (a variable, not
    // a literal), there's no way to synthesize an immediate at
    // expansion time. The splicer should refuse to inline and
    // emit a regular Call instead — preserving correctness over
    // performance.
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var sink: u8 = 0
        var src: u8 = 7
        inline fun stash(value: u8) {
            asm {
                LDA {value}
                STA {sink}
            }
        }
        on frame { stash(src) }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let any_call = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::Call(_, name, _) if name == "stash"));
    assert!(
        any_call,
        "stash should fall back to a Call op when arg is runtime"
    );
}

#[test]
fn inline_fun_with_asm_param_cascades_through_nested_inline() {
    // Outer inline fun calls inner inline fun (with asm) using
    // its *own* parameter as the inner's argument. The outer's
    // parameter is bound to a compile-time constant at the
    // top-level call site, and that constness has to flow
    // through `eval_const` so the inner — which has an asm body
    // — sees its arg as constant too.
    //
    // Without the `inline_const_args_stack` lookup in
    // `eval_const`, the inner would treat the outer's param as
    // runtime and refuse to inline, falling back to a Call.
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var sink: u8 = 0
        inline fun inner(value: u8) {
            asm {
                LDA {value}
                STA {sink}
            }
        }
        inline fun outer(p: u8) { inner(p) }
        on frame { outer(123) }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let any_call = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::Call(_, name, _) if name == "outer" || name == "inner"));
    assert!(
        !any_call,
        "both inline funs should expand; no Call ops should remain"
    );
    let asm_body = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .find_map(|op| match op {
            IrOp::InlineAsm(body) => Some(body.clone()),
            _ => None,
        })
        .expect("inlined asm block should be present");
    // 123 = $7B
    assert!(
        asm_body.contains("#$7B"),
        "asm body should contain `#$7B` from the cascaded constant; got: {asm_body}"
    );
}

#[test]
fn inline_fun_nested_inlines_substitute_correctly() {
    // Two inline functions where the outer calls the inner
    // using its own parameter. Both should inline; the
    // result should have no Call ops in the frame handler
    // targeting either function.
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        inline fun double(x: u8) -> u8 { return x + x }
        inline fun quad(x: u8) -> u8 { return double(double(x)) }
        var out: u8 = 0
        on frame { out = quad(5) }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let any_inline_call = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::Call(_, name, _) if name == "double" || name == "quad"));
    assert!(
        !any_inline_call,
        "nested inline calls should both be expanded; frame ops: {:?}",
        frame_fn
            .blocks
            .iter()
            .flat_map(|b| &b.ops)
            .collect::<Vec<_>>()
    );
}

#[test]
fn cmp_on_i16_var_emits_signed_kind() {
    // Two i16 vars compared via `<` should lower to a CmpLt16 op
    // tagged `Signedness::Signed` so the codegen picks the
    // signed-branch lowering. This is the regression guard for
    // the §A-follow-up gap: before signedness tracking landed, a
    // negative i16 always compared greater than zero because the
    // BCC-based unsigned path saw $FFxx > $00yy.
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var a: i16 = -1
        var b: i16 = 1
        var hit: u8 = 0
        on frame { if a < b { hit = 1 } }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let cmp = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .find_map(|op| match op {
            IrOp::CmpLt16 { signed, .. } => Some(*signed),
            _ => None,
        })
        .expect("expected a CmpLt16 op");
    assert_eq!(cmp, Signedness::Signed);
}

#[test]
fn cmp_on_u16_var_stays_unsigned() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var a: u16 = 0
        var b: u16 = 1
        var hit: u8 = 0
        on frame { if a < b { hit = 1 } }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let cmp = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .find_map(|op| match op {
            IrOp::CmpLt16 { signed, .. } => Some(*signed),
            _ => None,
        })
        .expect("expected a CmpLt16 op");
    assert_eq!(cmp, Signedness::Unsigned);
}

#[test]
fn cmp_on_i8_var_emits_signed_kind() {
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var a: i8 = -1
        var b: i8 = 1
        var hit: u8 = 0
        on frame { if a < b { hit = 1 } }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let cmp = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .find_map(|op| match op {
            IrOp::CmpLt(_, _, _, signed) => Some(*signed),
            _ => None,
        })
        .expect("expected a CmpLt op");
    assert_eq!(cmp, Signedness::Signed);
}

#[test]
fn i8_widened_to_i16_emits_sign_extend() {
    // Loading an i8 as the rhs of an i16 add should sign-extend
    // the high byte rather than zero-extending it. The IR shape
    // we look for is a `SignExtend` op feeding the high-byte
    // input to the resulting `Add16`.
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var w: i16 = 0
        var n: i8 = -10
        on frame { w = w + n }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let has_sx = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|op| matches!(op, IrOp::SignExtend(_, _)));
    assert!(
        has_sx,
        "i8 → i16 widen should emit SignExtend; ops: {:?}",
        frame_fn
            .blocks
            .iter()
            .flat_map(|b| &b.ops)
            .collect::<Vec<_>>()
    );
}

#[test]
fn cast_to_u16_strips_signed_flag() {
    // An explicit `as u16` cast on an `i16` value should make the
    // subsequent compare lower as unsigned — the user has opted
    // out of signed semantics.
    let ir = lower_ok(
        r#"
        game "Test" { mapper: NROM }
        var a: i16 = -1
        var b: u16 = 1
        var hit: u8 = 0
        on frame { if (a as u16) < b { hit = 1 } }
        start Main
    "#,
    );
    let frame_fn = ir
        .functions
        .iter()
        .find(|f| f.name.contains("frame"))
        .expect("frame handler should exist");
    let cmp = frame_fn
        .blocks
        .iter()
        .flat_map(|b| &b.ops)
        .find_map(|op| match op {
            IrOp::CmpLt16 { signed, .. } => Some(*signed),
            _ => None,
        })
        .expect("expected a CmpLt16 op");
    assert_eq!(cmp, Signedness::Unsigned);
}
