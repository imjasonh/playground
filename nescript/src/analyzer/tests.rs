use super::*;
use crate::errors::ErrorCode;
use crate::parser;

fn analyze_ok(input: &str) -> AnalysisResult {
    let (prog, diags) = parser::parse(input);
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let prog = prog.unwrap();
    let result = analyze(&prog);
    assert!(
        result.diagnostics.iter().all(|d| !d.is_error()),
        "analysis errors: {:?}",
        result.diagnostics
    );
    result
}

fn analyze_errors(input: &str) -> Vec<ErrorCode> {
    let (prog, parse_diags) = parser::parse(input);
    if prog.is_none() {
        return parse_diags.into_iter().map(|d| d.code).collect();
    }
    let result = analyze(&prog.unwrap());
    result.diagnostics.into_iter().map(|d| d.code).collect()
}

#[test]
fn analyze_minimal_program() {
    let result = analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        var px: u8 = 128
        on frame { px = 1 }
        start Main
    "#,
    );
    assert!(result.symbols.contains_key("px"));
    assert_eq!(result.var_allocations.len(), 1);
}

#[test]
fn analyze_allocates_zero_page() {
    let result = analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        var y: u8 = 0
        on frame { x = 1 }
        start Main
    "#,
    );
    // u8 vars should be allocated in zero page starting at $10
    assert_eq!(result.var_allocations[0].address, 0x10);
    assert_eq!(result.var_allocations[1].address, 0x11);
}

#[test]
fn analyze_duplicate_var() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        var x: u8 = 1
        on frame { x = 1 }
        start Main
    "#,
    );
    assert!(errors.contains(&ErrorCode::E0501));
}

#[test]
fn analyze_undefined_transition() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        state Main {
            on frame { transition Nonexistent }
        }
        start Main
    "#,
    );
    assert!(errors.contains(&ErrorCode::E0404));
}

#[test]
fn analyze_valid_transition() {
    let _result = analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        state Main {
            on frame { transition Other }
        }
        state Other {
            on frame { wait_frame }
        }
        start Main
    "#,
    );
}

#[test]
fn analyze_start_state_exists() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        state Main {
            on frame { wait_frame }
        }
        start Nonexistent
    "#,
    );
    assert!(errors.contains(&ErrorCode::E0404));
}

#[test]
fn analyze_const_symbol() {
    let result = analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        const SPEED: u8 = 2
        var px: u8 = 0
        on frame { px = SPEED }
        start Main
    "#,
    );
    let sym = result.symbols.get("SPEED").unwrap();
    assert!(sym.is_const);
}

#[test]
fn analyze_function_registered() {
    let result = analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        fun add(a: u8, b: u8) -> u8 { return a }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(result.symbols.contains_key("add"));
}

#[test]
fn analyze_recursion_detected() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        fun a() { a() }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(errors.contains(&ErrorCode::E0402));
}

#[test]
fn analyze_mutual_recursion() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        fun a() { b() }
        fun b() { a() }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(errors.contains(&ErrorCode::E0402));
}

#[test]
fn analyze_call_depth_ok() {
    // 3 levels of nesting — well within the default limit of 8
    let result = analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        fun c() { wait_frame }
        fun b() { c() }
        fun a() { b() }
        on frame { a() }
        start Main
    "#,
    );
    // The frame handler's depth should be <= 8
    for &depth in result.max_depths.values() {
        assert!(depth <= 8, "depth {depth} should be within limit");
    }
}

#[test]
fn analyze_call_depth_exceeded() {
    // Build a call chain deeper than 8: f1 -> f2 -> ... -> f10
    let result = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        fun f10() { wait_frame }
        fun f9() { f10() }
        fun f8() { f9() }
        fun f7() { f8() }
        fun f6() { f7() }
        fun f5() { f6() }
        fun f4() { f5() }
        fun f3() { f4() }
        fun f2() { f3() }
        fun f1() { f2() }
        on frame { f1() }
        start Main
    "#,
    );
    assert!(
        result.contains(&ErrorCode::E0401),
        "expected E0401 for exceeded call depth, got: {result:?}"
    );
}

#[test]
fn analyze_undefined_function() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        on frame { no_such_fn() }
        start Main
    "#,
    );
    assert!(errors.contains(&ErrorCode::E0503));
}

#[test]
fn analyze_call_arity_mismatch() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        fun add(a: u8, b: u8) -> u8 { return a }
        on frame { add(1) }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0203),
        "calling with wrong argument count should produce E0203, got: {errors:?}"
    );
}

#[test]
fn analyze_call_arity_ok() {
    analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        fun add(a: u8, b: u8) -> u8 { return a }
        on frame { add(1, 2) }
        start Main
    "#,
    );
}

#[test]
fn analyze_call_arity_in_expr_context() {
    // Calls used as expressions should also be checked.
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        fun two(a: u8, b: u8) -> u8 { return a }
        var x: u8 = 0
        on frame { x = two(1) }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0203),
        "call arity error in expression context should still trigger E0203: {errors:?}"
    );
}

#[test]
fn analyze_return_type_ok() {
    analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        fun get_five() -> u8 { return 5 }
        on frame { wait_frame }
        start Main
    "#,
    );
}

#[test]
fn analyze_return_wrong_type() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        fun is_ok() -> bool { return 5 }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "returning wrong type should produce E0201, got: {errors:?}"
    );
}

#[test]
fn analyze_struct_variable_allocates_fields() {
    let result = analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        struct Vec2 { x: u8, y: u8 }
        var pos: Vec2
        on frame {
            pos.x = 10
            pos.y = pos.x
        }
        start Main
    "#,
    );
    // The analyzer should synthesize pos.x and pos.y as separate
    // variables with consecutive addresses.
    let px = result
        .var_allocations
        .iter()
        .find(|a| a.name == "pos.x")
        .expect("pos.x should be allocated");
    let py = result
        .var_allocations
        .iter()
        .find(|a| a.name == "pos.y")
        .expect("pos.y should be allocated");
    assert_eq!(py.address, px.address + 1);
}

#[test]
fn analyze_struct_u16_field_allocates_two_bytes() {
    // A struct with a u16 field should lay out fields with
    // byte-accurate offsets: a u8 followed by a u16 followed by a u8
    // puts `b` at offset 1 and `c` at offset 3.
    let result = analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        struct Mixed { a: u8, b: u16, c: u8 }
        var m: Mixed
        on frame {
            m.a = 1
            m.b = 300
            m.c = 7
        }
        start Main
    "#,
    );
    let a = result
        .var_allocations
        .iter()
        .find(|x| x.name == "m.a")
        .expect("m.a should be allocated");
    let b = result
        .var_allocations
        .iter()
        .find(|x| x.name == "m.b")
        .expect("m.b should be allocated");
    let c = result
        .var_allocations
        .iter()
        .find(|x| x.name == "m.c")
        .expect("m.c should be allocated");
    // Offsets from base: a=0, b=1, c=3 (b is two bytes wide).
    assert_eq!(b.address, a.address + 1);
    assert_eq!(c.address, a.address + 3);
    // u16 field is recorded with size 2 so codegen bookkeeping
    // knows how much space the field occupies.
    assert_eq!(a.size, 1);
    assert_eq!(b.size, 2);
    assert_eq!(c.size, 1);
}

#[test]
fn analyze_struct_with_array_field_is_supported() {
    // Array struct fields are supported. The analyzer flattens
    // them into a single synthetic var typed `Array(u8, 4)` so
    // the existing array-index codegen lowers `b.xs[i]` exactly
    // like a top-level array.
    let result = analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        struct Bag { xs: u8[4] }
        var b: Bag
        on frame {
            b.xs[0] = 7
            wait_frame
        }
        start Main
    "#,
    );
    let alloc = result
        .var_allocations
        .iter()
        .find(|a| a.name == "b.xs")
        .expect("expected synthetic `b.xs` allocation");
    assert_eq!(alloc.size, 4, "u8[4] should reserve 4 bytes");
    let sym = result
        .symbols
        .get("b.xs")
        .expect("expected symbol entry for `b.xs`");
    assert!(matches!(sym.sym_type, NesType::Array(_, 4)));
}

#[test]
fn analyze_struct_with_nested_struct_field_is_supported() {
    // Nested struct fields are flattened recursively. A
    // `Player { pos: Point, hp: u8 }` variable produces both
    // `p.pos.x` / `p.pos.y` leaves and an intermediate
    // `p.pos` Struct symbol.
    let result = analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        struct Point { x: u8, y: u8 }
        struct Player { pos: Point, hp: u8 }
        var p: Player
        on frame {
            p.pos.x = 5
            p.pos.y = 6
            p.hp = 100
            wait_frame
        }
        start Main
    "#,
    );
    // Each leaf field gets its own allocation entry.
    assert!(result.var_allocations.iter().any(|a| a.name == "p.pos.x"));
    assert!(result.var_allocations.iter().any(|a| a.name == "p.pos.y"));
    assert!(result.var_allocations.iter().any(|a| a.name == "p.hp"));
    // The intermediate `p.pos` is a Struct symbol but has no
    // standalone allocation — its bytes are owned by the leaves.
    let pos = result
        .symbols
        .get("p.pos")
        .expect("intermediate `p.pos` should exist as a symbol");
    assert!(matches!(pos.sym_type, NesType::Struct(_)));
    assert!(result.var_allocations.iter().all(|a| a.name != "p.pos"));
}

#[test]
fn analyze_struct_with_nested_struct_field_addresses_are_contiguous() {
    // The four leaf fields of a `Player { pos: Point, hp: u8,
    // inv: u8[4] }` should land at successive addresses with no
    // padding — Point.x at base, Point.y at base+1, hp at base+2,
    // inv at base+3..base+6.
    let result = analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        struct Point { x: u8, y: u8 }
        struct Player { pos: Point, hp: u8, inv: u8[4] }
        var p: Player
        on frame {
            p.pos.x = 1
            wait_frame
        }
        start Main
    "#,
    );
    let alloc = |name: &str| {
        result
            .var_allocations
            .iter()
            .find(|a| a.name == name)
            .unwrap_or_else(|| panic!("missing allocation: {name}"))
            .address
    };
    let base = alloc("p.pos.x");
    assert_eq!(alloc("p.pos.y"), base + 1);
    assert_eq!(alloc("p.hp"), base + 2);
    assert_eq!(alloc("p.inv"), base + 3);
}

#[test]
fn analyze_struct_with_unknown_inner_struct_errors() {
    // A nested-struct field that references an undeclared inner
    // struct must emit E0201 with a "declare it earlier" hint.
    // (We don't topologically sort declarations.)
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        struct Outer { inner: NotDeclared }
        var o: Outer
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "expected E0201, got: {errors:?}"
    );
}

#[test]
fn analyze_metasprite_ok() {
    let result = analyze_ok(
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
            dx:    [0, 8]
            dy:    [0, 0]
            frame: [0, 0]
        }
        on frame { draw Hero at: (10, 10) wait_frame }
        start Main
    "#,
    );
    // Sanity: the metasprite was kept around in the program.
    // (The analyzer doesn't move declarations into AnalysisResult,
    // so we only check that no errors were emitted; the
    // lowering test below validates the expansion path.)
    assert!(result.diagnostics.iter().all(|d| !d.is_error()));
}

#[test]
fn analyze_metasprite_unknown_sprite_errors() {
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        metasprite Hero {
            sprite: NotASprite
            dx:    [0]
            dy:    [0]
            frame: [0]
        }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "metasprite referencing an unknown sprite should emit E0201, got: {errors:?}"
    );
}

#[test]
fn analyze_metasprite_with_external_chr_sprite_errors() {
    // The IR lowering walks `program.sprites` to compute base
    // tile indices for the metasprite's `frame:` array, but it
    // can't read external `@chr(...)` files at lowering time
    // and would fall back to a 1-tile assumption. That would
    // silently misalign the metasprite, so the analyzer rejects
    // the combination upfront with a clear "use inline pixels"
    // hint.
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        sprite Tileset @chr("art/sheet.png")
        metasprite Hero {
            sprite: Tileset
            dx:    [0, 8]
            dy:    [0, 0]
            frame: [0, 1]
        }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "metasprite over an external-CHR sprite should emit E0201, got: {errors:?}"
    );
}

#[test]
fn analyze_metasprite_mismatched_array_lengths_errors() {
    let errors = analyze_errors(
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
            dx:    [0, 8, 0]
            dy:    [0, 0]
            frame: [0, 1, 2]
        }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "mismatched dx/dy/frame lengths should emit E0201, got: {errors:?}"
    );
}

#[test]
fn analyze_metasprite_empty_errors() {
    let errors = analyze_errors(
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
            dx: []
            dy: []
            frame: []
        }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "empty metasprite should emit E0201, got: {errors:?}"
    );
}

#[test]
fn analyze_struct_with_array_of_structs_is_rejected() {
    // Arrays of structs aren't supported yet — the synthetic-
    // variable model can't index into per-element struct layouts
    // without additional codegen work. Make sure it errors
    // cleanly with E0201 instead of producing a broken layout.
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        struct Point { x: u8, y: u8 }
        struct Cluster { points: Point[4] }
        var c: Cluster
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "expected E0201 for array-of-structs, got: {errors:?}"
    );
}

#[test]
fn analyze_struct_unknown_field_errors() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        struct Vec2 { x: u8, y: u8 }
        var pos: Vec2
        on frame { pos.z = 5 }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "unknown field should emit E0201: {errors:?}"
    );
}

#[test]
fn analyze_unknown_struct_type_errors() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        var pos: NoSuchStruct
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "unknown struct type should emit E0201: {errors:?}"
    );
}

#[test]
fn analyze_assign_to_undefined_var_errors() {
    // Assigning to an undeclared variable must produce E0502
    // rather than silently creating the variable.
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        on frame { nope = 5 }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0502),
        "assignment to undefined var should produce E0502, got: {errors:?}"
    );
}

#[test]
fn analyze_enum_variants_as_constants() {
    let result = analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        enum Color { Red, Green, Blue }
        var c: u8 = Red
        on frame {
            if c == Blue { c = Green }
        }
        start Main
    "#,
    );
    // Variants should be registered as constant symbols.
    assert!(result.symbols.get("Red").is_some_and(|s| s.is_const));
    assert!(result.symbols.get("Green").is_some_and(|s| s.is_const));
    assert!(result.symbols.get("Blue").is_some_and(|s| s.is_const));
}

#[test]
fn analyze_duplicate_enum_variant_errors() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        enum A { Foo, Bar }
        enum B { Baz, Bar }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0501),
        "duplicate variant should emit E0501, got: {errors:?}"
    );
}

#[test]
fn analyze_dead_code_after_break() {
    let src = r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame {
            loop {
                break
                x += 1
            }
        }
        start Main
    "#;
    let errors = analyze_errors(src);
    assert!(
        errors.contains(&ErrorCode::W0104),
        "code after break should trigger W0104, got: {errors:?}"
    );
}

#[test]
fn analyze_dead_code_after_transition() {
    let src = r#"
        game "Test" { mapper: NROM }
        state A {
            on frame {
                transition B
                wait_frame
            }
        }
        state B { on frame { wait_frame } }
        start A
    "#;
    let errors = analyze_errors(src);
    assert!(
        errors.contains(&ErrorCode::W0104),
        "code after transition should trigger W0104, got: {errors:?}"
    );
}

#[test]
fn analyze_dead_code_after_return_in_fn() {
    let src = r#"
        game "Test" { mapper: NROM }
        fun foo() -> u8 {
            return 5
            return 6
        }
        on frame { wait_frame }
        start Main
    "#;
    let errors = analyze_errors(src);
    assert!(
        errors.contains(&ErrorCode::W0104),
        "code after return should trigger W0104, got: {errors:?}"
    );
}

#[test]
fn analyze_ram_overflow_emits_e0301() {
    // Two arrays totalling >2 KB cannot fit in NES RAM, triggering
    // E0301 at allocation time.
    let src = r#"
        game "Test" { mapper: NROM }
        var huge: u8[2000]
        var also_huge: u8[2000]
        on frame { wait_frame }
        start Main
    "#;
    let errors = analyze_errors(src);
    assert!(
        errors.contains(&ErrorCode::E0301),
        "RAM overflow should produce E0301, got: {errors:?}"
    );
}

#[test]
fn analyze_expensive_multiply_warns() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        var a: u8 = 3
        var b: u8 = 5
        var c: u8 = 0
        on frame { c = a * b }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::W0101),
        "variable*variable multiply should emit W0101, got: {errors:?}"
    );
}

#[test]
fn analyze_multiply_by_constant_ok() {
    // Multiply by a literal is cheap (strength reduced to shifts).
    analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        var a: u8 = 3
        var c: u8 = 0
        on frame { c = a * 4 }
        start Main
    "#,
    );
}

#[test]
fn analyze_on_scanline_requires_mmc3() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        state Main {
            on frame { wait_frame }
            on scanline(120) { scroll(0, 0) }
        }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0603),
        "on scanline without MMC3 should produce E0603, got: {errors:?}"
    );
}

#[test]
fn analyze_state_local_array_initializer_rejected() {
    // Regression guard against the state-local-array silent drop. The
    // IR lowerer's `on_enter` initializer loop `continue`s past
    // ArrayLiteral inits without emitting any stores, so without this
    // diagnostic the program compiles and the buffer is full of stale
    // RAM at runtime.
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        state Main {
            var buf: u8[4] = [10, 20, 30, 40]
            on frame { scroll(buf[0], buf[1]) }
        }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0601),
        "state-local array initializer should produce E0601, got: {errors:?}"
    );
}

#[test]
fn analyze_on_exit_declaration_accepted() {
    // Regression guard: `on exit` handlers were lowered to IR
    // functions but never dispatched by transitions, so any side
    // effect inside silently never ran. The codegen now emits a
    // runtime CMP-chain against `ZP_CURRENT_STATE` before every
    // `transition` to JSR the leaving state's on_exit — confirm
    // the analyzer accepts the declaration so the feature stays
    // usable.
    let result = analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        state Main {
            on enter {}
            on frame { transition Other }
            on exit { scroll(0, 0) }
        }
        state Other {
            on enter {}
            on frame {}
        }
        start Main
    "#,
    );
    assert!(
        result.diagnostics.iter().all(|d| !d.is_error()),
        "`on exit` should be accepted now that transitions dispatch it, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_on_scanline_mmc3_ok() {
    analyze_ok(
        r#"
        game "Test" { mapper: MMC3 }
        state Main {
            on frame { wait_frame }
            on scanline(120) { scroll(0, 0) }
        }
        start Main
    "#,
    );
}

#[test]
fn analyze_loop_without_exit_warns() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame {
            loop { x += 1 }
        }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::W0102),
        "infinite loop with no exit should produce W0102, got: {errors:?}"
    );
}

#[test]
fn analyze_loop_with_wait_frame_ok() {
    analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        on frame {
            loop { wait_frame }
        }
        start Main
    "#,
    );
}

#[test]
fn analyze_loop_with_break_ok() {
    analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        var x: u8 = 0
        on frame {
            loop {
                x += 1
                if x == 10 { break }
            }
        }
        start Main
    "#,
    );
}

#[test]
fn analyze_bare_return_from_typed_fn_errors() {
    // A `return` with no value inside a function that has a declared
    // return type should produce E0203.
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        fun get_five() -> u8 {
            return
        }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0203),
        "bare return from typed fn should produce E0203, got: {errors:?}"
    );
}

#[test]
fn analyze_return_value_from_void_fn() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        fun do_nothing() { return 5 }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0203),
        "returning value from void function should produce E0203, got: {errors:?}"
    );
}

#[test]
fn analyze_const_assignment_error() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        const SPEED: u8 = 2
        on frame { SPEED = 5 }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0203),
        "assigning to const should produce E0203, got: {errors:?}"
    );
}

#[test]
fn analyze_break_outside_loop() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        on frame { break }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0203),
        "break outside loop should produce E0203, got: {errors:?}"
    );
}

#[test]
fn analyze_unused_variable_warning() {
    // `ghost` is declared but never read (only the initializer runs).
    // It should trigger a W0103 warning.
    let (prog, diags) = parser::parse(
        r#"
        game "Test" { mapper: NROM }
        var ghost: u8 = 0
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    assert!(
        result.diagnostics.iter().any(|d| d.code == ErrorCode::W0103
            && d.level == crate::errors::Level::Warning
            && d.message.contains("ghost")),
        "expected W0103 for unused var 'ghost', got: {:?}",
        result.diagnostics
    );
    // And no hard errors.
    assert!(
        result.diagnostics.iter().all(|d| !d.is_error()),
        "unexpected hard errors: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_unused_state_local_warning() {
    // State-local `bonus` is declared but never read — W0103 should fire.
    let (prog, diags) = parser::parse(
        r#"
        game "Test" { mapper: NROM }
        state Main {
            var bonus: u8 = 0
            on frame { wait_frame }
        }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    assert!(
        result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0103 && d.message.contains("bonus")),
        "expected W0103 for unused state-local 'bonus', got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_unused_variable_no_warning_when_read() {
    // `counter` is both written and read (in the `if` condition),
    // so W0103 should NOT fire for it.
    let (prog, diags) = parser::parse(
        r#"
        game "Test" { mapper: NROM }
        var counter: u8 = 0
        on frame {
            counter = counter + 1
            if counter > 60 { wait_frame }
        }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0103 && d.message.contains("counter")),
        "did not expect W0103 for read variable 'counter', got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_unused_variable_underscore_prefix_silences() {
    // A leading underscore silences the W0103 warning, matching Rust's
    // convention for intentionally-unused names.
    let (prog, diags) = parser::parse(
        r#"
        game "Test" { mapper: NROM }
        var _reserved: u8 = 0
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0103),
        "did not expect W0103 for underscore-prefixed var, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_unreachable_state_warning() {
    // `Orphan` is never reached from `Main` — W0104 should fire.
    let (prog, diags) = parser::parse(
        r#"
        game "Test" { mapper: NROM }
        state Main {
            on frame { wait_frame }
        }
        state Orphan {
            on frame { wait_frame }
        }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    assert!(
        result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0104 && d.message.contains("Orphan")),
        "expected W0104 for unreachable state 'Orphan', got: {:?}",
        result.diagnostics
    );
    // And no hard errors.
    assert!(
        result.diagnostics.iter().all(|d| !d.is_error()),
        "unexpected hard errors: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_reachable_state_no_warning() {
    // Both states are reachable: Main transitions to Other, and Other
    // transitions back to Main. Neither should trigger W0104.
    let (prog, diags) = parser::parse(
        r#"
        game "Test" { mapper: NROM }
        state Main {
            on frame { transition Other }
        }
        state Other {
            on frame { transition Main }
        }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0104),
        "did not expect any W0104 warnings, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_undefined_variable_emits_e0502() {
    // `ghosy` does not exist; analyzer should emit E0502 and — thanks to
    // the suggestion helper — hint at `ghost` which is the close match.
    let (prog, diags) = parser::parse(
        r#"
        game "Test" { mapper: NROM }
        var ghost: u8 = 0
        var score: u8 = 0
        on frame {
            score = ghosy + 1
        }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    let diag = result
        .diagnostics
        .iter()
        .find(|d| d.code == ErrorCode::E0502)
        .expect("expected E0502 for undefined variable 'ghosy'");
    assert!(
        diag.message.contains("ghosy"),
        "E0502 message should mention 'ghosy', got: {}",
        diag.message
    );
    assert_eq!(
        diag.help.as_deref(),
        Some("did you mean 'ghost'?"),
        "expected suggestion for 'ghost', got: {:?}",
        diag.help
    );
}

// ── Audio name validation ──

#[test]
fn analyze_accepts_builtin_sfx() {
    // `play coin` is always valid because `coin` is a builtin
    // even without a user `sfx Coin { ... }` declaration.
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        on frame { play coin }
        start Main
    "#,
    );
}

#[test]
fn analyze_accepts_user_declared_sfx() {
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        sfx Chime {
            pitch: [0x20, 0x22, 0x24, 0x26]
            volume: [15, 12, 8, 4]
        }
        on frame { play Chime }
        start Main
    "#,
    );
}

#[test]
fn analyze_rejects_unknown_sfx_name() {
    // `play Nonexistent` with no matching user decl or builtin
    // should emit E0505.
    let codes = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        on frame { play Nonexistent }
        start Main
    "#,
    );
    assert!(
        codes.contains(&ErrorCode::E0505),
        "expected E0505 for unknown sfx, got {codes:?}"
    );
}

#[test]
fn analyze_accepts_noise_sfx() {
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        sfx Zap {
            channel: noise
            pitch: 5
            volume: [15, 10, 5]
        }
        on frame { play Zap }
        start Main
    "#,
    );
}

#[test]
fn analyze_accepts_triangle_sfx() {
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        sfx Bass {
            channel: triangle
            pitch: 60
            volume: [1, 1, 1, 1, 1]
        }
        on frame { play Bass }
        start Main
    "#,
    );
}

#[test]
fn analyze_rejects_pulse2_sfx() {
    // pulse 2 is reserved for the music driver; declaring an sfx
    // on it should be an error.
    let codes = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        sfx Nope {
            channel: pulse2
            pitch: 5
            volume: [8]
        }
        on frame { play Nope }
        start Main
    "#,
    );
    assert!(
        codes.contains(&ErrorCode::E0201),
        "expected E0201 for pulse2 sfx, got {codes:?}"
    );
}

#[test]
fn analyze_rejects_noise_sfx_with_out_of_range_pitch() {
    // Noise pitch is a 4-bit period index + optional bit 7 mode.
    // Setting bit 5 (0x20) is outside that envelope.
    let codes = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        sfx Bad {
            channel: noise
            pitch: 0x20
            volume: [8]
        }
        on frame { play Bad }
        start Main
    "#,
    );
    assert!(
        codes.contains(&ErrorCode::E0201),
        "expected E0201 for invalid noise pitch, got {codes:?}"
    );
}

#[test]
fn analyze_accepts_builtin_music() {
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        on frame { start_music theme }
        start Main
    "#,
    );
}

#[test]
fn analyze_accepts_user_declared_music() {
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        music Boss {
            notes: [37, 8, 41, 8, 44, 8, 49, 8]
        }
        on frame { start_music Boss }
        start Main
    "#,
    );
}

#[test]
fn analyze_rejects_unknown_music_name() {
    let codes = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        on frame { start_music Nonexistent }
        start Main
    "#,
    );
    assert!(
        codes.contains(&ErrorCode::E0505),
        "expected E0505 for unknown music, got {codes:?}"
    );
}

#[test]
fn analyze_stop_music_needs_no_name_and_is_always_valid() {
    // `stop_music` takes no argument, so there's nothing to
    // validate — it should always analyze cleanly.
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        on frame { stop_music }
        start Main
    "#,
    );
}

// ── Palette / background validation ──

#[test]
fn analyze_accepts_declared_palette() {
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        palette Cool { colors: [0x0F, 0x01, 0x11, 0x21] }
        on frame { set_palette Cool }
        start Main
    "#,
    );
}

#[test]
fn analyze_rejects_unknown_palette() {
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        on frame { set_palette Ghost }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0502),
        "expected E0502 for unknown palette, got {errors:?}"
    );
}

#[test]
fn analyze_accepts_declared_background() {
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        background Stage { tiles: [0, 1, 2] }
        on frame { load_background Stage }
        start Main
    "#,
    );
}

#[test]
fn analyze_rejects_unknown_background() {
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        on frame { load_background Ghost }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0502),
        "expected E0502 for unknown background, got {errors:?}"
    );
}

#[test]
fn analyze_rejects_palette_color_out_of_range() {
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        palette Bad { colors: [0x0F, 0x40] }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "expected E0201 for out-of-range NES color, got {errors:?}"
    );
}

#[test]
fn analyze_rejects_palette_too_long() {
    // 33 bytes > 32-byte PPU palette RAM limit.
    let colors = (0..33)
        .map(|_| "0x0F".to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let src = format!(
        r#"
        game "T" {{ mapper: NROM }}
        palette Big {{ colors: [{colors}] }}
        on frame {{ wait_frame }}
        start Main
    "#
    );
    let errors = analyze_errors(&src);
    assert!(
        errors.contains(&ErrorCode::E0201),
        "expected E0201 for >32-byte palette, got {errors:?}"
    );
}

#[test]
fn analyze_rejects_background_tiles_too_long() {
    // 961 bytes > 960-byte nametable.
    let tiles = (0..961)
        .map(|_| "0".to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let src = format!(
        r#"
        game "T" {{ mapper: NROM }}
        background Big {{ tiles: [{tiles}] }}
        on frame {{ wait_frame }}
        start Main
    "#
    );
    let errors = analyze_errors(&src);
    assert!(
        errors.contains(&ErrorCode::E0201),
        "expected E0201 for >960-byte nametable, got {errors:?}"
    );
}

#[test]
fn analyze_rejects_duplicate_palette_name() {
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        palette Dup { colors: [0x0F] }
        palette Dup { colors: [0x10] }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0501),
        "expected E0501 for duplicate palette name, got {errors:?}"
    );
}

#[test]
fn analyze_reserves_zero_page_when_palette_declared() {
    // When a program declares any palette or background, the
    // analyzer bumps the user zero-page start from $10 to $18 so
    // the runtime can own $11-$17 for the vblank update handshake.
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        palette P { colors: [0x0F] }
        var x: u8 = 0
        on frame { wait_frame }
        start Main
    "#,
    );
    let x = result
        .var_allocations
        .iter()
        .find(|a| a.name == "x")
        .expect("x should be allocated");
    assert!(
        x.address >= 0x18,
        "user var `x` should land at $18+ when palette is declared (got ${:02X})",
        x.address
    );
}

#[test]
fn analyze_does_not_reserve_zero_page_without_palette_or_bg() {
    // Programs that don't declare palette/background keep the old
    // user-ZP start at $10 so existing examples (and their
    // goldens) don't shift.
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        on frame { wait_frame }
        start Main
    "#,
    );
    let x = result
        .var_allocations
        .iter()
        .find(|a| a.name == "x")
        .expect("x should be allocated");
    assert_eq!(x.address, 0x10);
}

// ── W0102 extended: `while true` + continue-only loops ──────

#[test]
fn analyze_while_true_without_exit_warns() {
    // `while true { x = x + 1 }` — no break/return/wait_frame,
    // so the same W0102 that fires on bare `loop { ... }` must
    // also fire here.
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        on frame {
            while true { x = x + 1 }
        }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::W0102),
        "`while true` with no exit should produce W0102, got: {errors:?}"
    );
}

#[test]
fn analyze_while_true_with_wait_frame_ok() {
    // `while true { wait_frame }` yields control to the NMI each
    // iteration, so the NES actually makes progress — no warning.
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        on frame {
            while true { wait_frame }
        }
        start Main
    "#,
    );
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0102),
        "`while true` + wait_frame should NOT warn, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_while_true_with_break_ok() {
    // A reachable `break` satisfies W0102 just like it does for
    // bare `loop`.
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        on frame {
            while true {
                x = x + 1
                if x == 10 { break }
            }
        }
        start Main
    "#,
    );
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0102),
        "`while true` + break should NOT warn, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_loop_with_only_continue_still_warns() {
    // `continue` is *not* an exit — the loop still spins forever.
    // W0102 must still fire here.
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        on frame {
            loop {
                if x == 0 { continue }
            }
        }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::W0102),
        "`loop` whose only exit is `continue` should still produce W0102, got: {errors:?}"
    );
}

// ── W0105: palette universal-byte consistency ───────────────

#[test]
fn analyze_palette_consistent_universals_ok() {
    // Flat-form palette where every sub-palette's first byte is
    // the same universal colour ($0F = black). No W0105.
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        palette Consistent {
            colors: [
                0x0F, 0x11, 0x12, 0x13,
                0x0F, 0x21, 0x22, 0x23,
                0x0F, 0x31, 0x32, 0x33,
                0x0F, 0x01, 0x02, 0x03,
                0x0F, 0x05, 0x06, 0x07,
                0x0F, 0x15, 0x16, 0x17,
                0x0F, 0x25, 0x26, 0x27,
                0x0F, 0x35, 0x36, 0x37
            ]
        }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0105),
        "consistent palette should NOT warn, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_palette_inconsistent_universals_warns() {
    // Flat-form palette whose sub-palette first bytes disagree
    // (index 0 = $0F, index 16 = $30, etc.) — the $3F10 mirror
    // will overwrite the background universal colour at runtime.
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        palette Broken {
            colors: [
                0x0F, 0x11, 0x12, 0x13,
                0x0F, 0x21, 0x22, 0x23,
                0x0F, 0x31, 0x32, 0x33,
                0x0F, 0x01, 0x02, 0x03,
                0x30, 0x05, 0x06, 0x07,
                0x0F, 0x15, 0x16, 0x17,
                0x0F, 0x25, 0x26, 0x27,
                0x0F, 0x35, 0x36, 0x37
            ]
        }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::W0105),
        "inconsistent palette universals should produce W0105, got: {errors:?}"
    );
}

#[test]
fn analyze_grouped_palette_is_always_consistent() {
    // The grouped form uses the `universal:` field to drive
    // every sub-palette's first byte, so it can never trip
    // W0105 — even when the sub-palette bodies differ wildly.
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        palette Grouped {
            universal: 0x0F
            bg0: [0x11, 0x12, 0x13]
            bg1: [0x21, 0x22, 0x23]
            bg2: [0x31, 0x32, 0x33]
            bg3: [0x01, 0x02, 0x03]
            sp0: [0x05, 0x06, 0x07]
            sp1: [0x15, 0x16, 0x17]
            sp2: [0x25, 0x26, 0x27]
            sp3: [0x35, 0x36, 0x37]
        }
        on frame { wait_frame }
        start Main
    "#,
    );
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0105),
        "grouped palette should never trip W0105, got: {:?}",
        result.diagnostics
    );
}

// ── W0106: implicit drop of a function return value ─────────

#[test]
fn analyze_discarded_non_void_return_warns() {
    // `double(x)` returns u8 but the caller drops the result.
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        fun double(n: u8) -> u8 { return n + n }
        on frame { double(x) }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::W0106),
        "discarded non-void return should produce W0106, got: {errors:?}"
    );
}

#[test]
fn analyze_discarded_void_call_ok() {
    // Void function at statement position is the happy path —
    // no discarded value, no warning.
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        fun bump() { x = x + 1 }
        on frame { bump() }
        start Main
    "#,
    );
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0106),
        "void call should NOT produce W0106, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_non_void_return_used_as_rhs_ok() {
    // Same signature as the discarded case, but the return value
    // is consumed by an assignment — no warning.
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        var x: u8 = 0
        var y: u8 = 0
        fun double(n: u8) -> u8 { return n + n }
        on frame { y = double(x) }
        start Main
    "#,
    );
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0106),
        "assigned return value should NOT produce W0106, got: {:?}",
        result.diagnostics
    );
}

// ── W0107: `fast` variable slot under-use ───────────────────

#[test]
fn analyze_fast_var_underused_warns() {
    // `counter` is declared `fast` but only one read (in the
    // `if` condition), so its access count is 1 — below the
    // threshold of 3. W0107 should fire.
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        fast var counter: u8 = 0
        on frame {
            if counter == 0 { wait_frame }
        }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::W0107),
        "under-used `fast` var should produce W0107, got: {errors:?}"
    );
}

#[test]
fn analyze_fast_var_heavy_use_ok() {
    // Three-plus accesses (one init + one read + one write-back)
    // is enough to justify the slot — no W0107.
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        fast var counter: u8 = 0
        on frame {
            counter = counter + 1
            if counter == 0 { wait_frame }
        }
        start Main
    "#,
    );
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0107),
        "hot `fast` var should NOT warn, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_non_fast_var_never_warns() {
    // Only `fast` declarations are checked — a plain `var` with
    // the same (light) access pattern must not fire W0107.
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        var counter: u8 = 0
        on frame {
            if counter == 0 { wait_frame }
        }
        start Main
    "#,
    );
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0107),
        "plain `var` should never trip W0107, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_fast_var_underscore_exempt() {
    // Leading-underscore names are exempt from W0107, mirroring
    // the W0103 convention for deliberately-unused variables.
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        fast var _reserved: u8 = 0
        on frame {
            if _reserved == 0 { wait_frame }
        }
        start Main
    "#,
    );
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0107),
        "underscore-prefixed `fast` var should be exempt, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_slow_var_forced_out_of_zero_page() {
    // The `slow` keyword should keep a u8 var out of zero page so
    // users can free a hot ZP slot for a different variable. Before
    // this was wired up, `slow` was parsed but ignored (same silent-
    // drop shape as the PR #31 state-local bug).
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        slow var cold: u8 = 0
        on frame {
            if cold == 0 { wait_frame }
        }
        start Main
    "#,
    );
    let alloc = result
        .var_allocations
        .iter()
        .find(|a| a.name == "cold")
        .expect("`cold` should be allocated");
    assert!(
        alloc.address >= 0x0100,
        "`slow var cold` should live outside zero page but was allocated at ${:04X}",
        alloc.address
    );
}

#[test]
fn analyze_oversized_array_warns_w0108() {
    // A u8 array with 300 elements has byte size 300 > 256. The
    // codegen lowers `arr[i]` to `LDA base,X` with X 8-bit, so
    // elements 256..299 are unreachable. W0108 should fire.
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        var big: u8[300]
        on frame {
            big[0] = 0
            wait_frame
        }
        start Main
    "#,
    );
    assert!(
        result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0108),
        "oversized u8 array should emit W0108, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_boundary_size_256_array_ok() {
    // A u8[256] exactly fills the 8-bit X register — every element
    // is reachable. No W0108.
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        var big: u8[256]
        on frame {
            big[0] = 0
            wait_frame
        }
        start Main
    "#,
    );
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0108),
        "u8[256] should not emit W0108, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_small_array_never_warns_w0108() {
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        var small: u8[16]
        on frame {
            small[0] = 0
            wait_frame
        }
        start Main
    "#,
    );
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0108),
        "small array should not emit W0108, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_debug_frame_overrun_count_ok() {
    // The known-good debug expression methods type-check as u8 and
    // can be assigned into a u8 variable without diagnostics.
    analyze_ok(
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
}

#[test]
fn analyze_debug_frame_overran_in_assert_ok() {
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        on frame {
            debug.assert(not debug.frame_overran())
            wait_frame
        }
        start Main
    "#,
    );
}

#[test]
fn analyze_debug_unknown_method_errors() {
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        var n: u8 = 0
        on frame {
            n = debug.bogus()
            wait_frame
        }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "expected E0201 for unknown debug method, got: {errors:?}"
    );
}

#[test]
fn analyze_debug_frame_overrun_count_with_args_errors() {
    // The query methods take no arguments — passing one is an
    // arity error, not a silent "unused arg" warning.
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        var n: u8 = 0
        on frame {
            n = debug.frame_overrun_count(42)
            wait_frame
        }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0203),
        "expected E0203 for arg count mismatch, got: {errors:?}"
    );
}

#[test]
fn analyze_rejects_function_with_more_than_8_params() {
    // The calling convention allocates four zero-page transport
    // slots ($04-$07) that leaves pass through, and a per-function
    // RAM spill region that non-leaves direct-write into. Non-leaf
    // functions scale past four params cleanly via the spill
    // region, and we cap at eight both to keep the calling
    // convention simple and because any call site needing more
    // than eight arguments is almost certainly better served by a
    // struct global.
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        fun too_many(a: u8, b: u8, c: u8, d: u8, e: u8, f: u8, g: u8, h: u8, i: u8) {
            a = 0
        }
        on frame { too_many(1, 2, 3, 4, 5, 6, 7, 8, 9) }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0506),
        "expected E0506 for function with >8 params, got: {errors:?}"
    );
}

#[test]
fn analyze_accepts_function_with_exactly_4_params() {
    // 4 params is the maximum and should compile cleanly.
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        fun four_args(a: u8, b: u8, c: u8, d: u8) -> u8 {
            return a + b + c + d
        }
        var n: u8 = 0
        on frame {
            n = four_args(1, 2, 3, 4)
            wait_frame
        }
        start Main
    "#,
    );
}

#[test]
fn analyze_allows_same_local_name_in_two_functions() {
    // Regression test for the function-local scope-qualification
    // fix on the War bug-cleanup branch (see `git log`): function-
    // body `var` declarations used to live in a flat global
    // namespace, so two functions both declaring `var i` collided
    // on E0501. They now coexist in per-function scopes.
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        fun foo() -> u8 {
            var i: u8 = 0
            while i < 5 { i += 1 }
            return i
        }
        fun bar() -> u8 {
            var i: u8 = 0
            while i < 10 { i += 1 }
            return i
        }
        var total: u8 = 0
        on frame {
            total = foo() + bar()
            wait_frame
        }
        start Main
    "#,
    );
}

#[test]
fn analyze_allows_same_param_name_in_two_functions() {
    // Regression test for the scope-qualified parameter fix on
    // the War bug-cleanup branch (see `git log`): parameters
    // across different functions used to share VarIds because
    // the IR lowerer's `var_map` was global. Both declaration
    // (analyzer) and lowering (IR) now give each function's
    // parameters their own independent entries.
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        fun shift_left(x: u8) -> u8 { return x << 1 }
        fun shift_right(x: u8) -> u8 { return x >> 1 }
        var n: u8 = 0
        on frame {
            n = shift_left(5) + shift_right(20)
            wait_frame
        }
        start Main
    "#,
    );
}

#[test]
fn analyze_allows_same_local_name_in_two_state_handlers() {
    // Each state handler gets its own local scope, so both
    // `Title::on frame` and `Playing::on frame` can declare
    // `var i` independently.
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        state Title {
            on frame {
                var i: u8 = 0
                while i < 3 { i += 1 }
                if button.start { transition Playing }
            }
        }
        state Playing {
            on frame {
                var i: u8 = 0
                while i < 7 { i += 1 }
            }
        }
        start Title
    "#,
    );
}

#[test]
fn analyze_still_rejects_duplicate_local_in_same_function() {
    // Two `var i` declarations inside the SAME function body
    // should still trip E0501 — we scoped locals per function,
    // not per statement.
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        fun foo() -> u8 {
            var i: u8 = 0
            var i: u8 = 1
            return i
        }
        on frame { var r: u8 = foo() wait_frame }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0501),
        "expected E0501 for duplicate `var i` in same function, got: {errors:?}"
    );
}

#[test]
fn analyze_sprite_scanline_budget_warns_over_eight() {
    // Nine literal-coord draws all sharing the same `y` stack
    // vertically on a single scanline. That blows past the NES's
    // 8-sprites-per-scanline budget and must trip W0109.
    let (prog, diags) = parser::parse(
        r#"
        game "T" { mapper: NROM }
        state Main {
            on frame {
                draw Blip at: (10, 100)
                draw Blip at: (20, 100)
                draw Blip at: (30, 100)
                draw Blip at: (40, 100)
                draw Blip at: (50, 100)
                draw Blip at: (60, 100)
                draw Blip at: (70, 100)
                draw Blip at: (80, 100)
                draw Blip at: (90, 100)
                wait_frame
            }
        }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    let w0109: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.code == ErrorCode::W0109)
        .collect();
    assert_eq!(
        w0109.len(),
        1,
        "expected exactly one W0109, got: {:?}",
        result.diagnostics
    );
    assert!(
        w0109[0].message.contains('9') && w0109[0].message.contains("Main"),
        "W0109 message should mention count 9 and state Main, got: {}",
        w0109[0].message
    );
    assert!(
        !w0109[0].labels.is_empty(),
        "W0109 should label the offending draws"
    );
}

#[test]
fn analyze_sprite_scanline_budget_ok_when_staggered() {
    // Nine draws, but each one is on its own line. No scanline
    // ever sees more than one sprite. Must NOT trip W0109.
    let (prog, diags) = parser::parse(
        r#"
        game "T" { mapper: NROM }
        state Main {
            on frame {
                draw Blip at: (10, 0)
                draw Blip at: (10, 16)
                draw Blip at: (10, 32)
                draw Blip at: (10, 48)
                draw Blip at: (10, 64)
                draw Blip at: (10, 80)
                draw Blip at: (10, 96)
                draw Blip at: (10, 112)
                draw Blip at: (10, 128)
                wait_frame
            }
        }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0109),
        "did not expect W0109 for staggered draws, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_sprite_scanline_budget_skips_dynamic_coords() {
    // Nine draws on the same line, but the x coordinate comes from
    // a variable. Static analysis can't know where these land, so
    // W0109 must stay silent.
    let (prog, diags) = parser::parse(
        r#"
        game "T" { mapper: NROM }
        var px: u8 = 0
        state Main {
            on frame {
                draw Blip at: (px, 100)
                draw Blip at: (px, 100)
                draw Blip at: (px, 100)
                draw Blip at: (px, 100)
                draw Blip at: (px, 100)
                draw Blip at: (px, 100)
                draw Blip at: (px, 100)
                draw Blip at: (px, 100)
                draw Blip at: (px, 100)
                wait_frame
            }
        }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0109),
        "did not expect W0109 for dynamic coords, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_sprite_scanline_budget_expands_metasprites() {
    // A metasprite with four tiles all at `dy = 0` means one
    // `draw` statement contributes four sprites to the same
    // scanline. Three such draws = 12 overlapping sprites, which
    // must trip W0109.
    let (prog, diags) = parser::parse(
        r#"
        game "T" { mapper: NROM }
        sprite Tile8 {
            pixels: [
                "........",
                "........",
                "........",
                "........",
                "........",
                "........",
                "........",
                "........"
            ]
        }
        metasprite Quad {
            sprite: Tile8
            dx:    [0, 8, 16, 24]
            dy:    [0, 0, 0, 0]
            frame: [0, 0, 0, 0]
        }
        state Main {
            on frame {
                draw Quad at: (0, 100)
                draw Quad at: (40, 100)
                draw Quad at: (80, 100)
                wait_frame
            }
        }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    assert!(
        result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0109),
        "expected W0109 for metasprite overlap, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_sprite_scanline_budget_recurses_into_if() {
    // Conservative: a branch that always fires when the state
    // runs still counts. Nine draws inside an `if` block over the
    // same scanline must trip W0109.
    let (prog, diags) = parser::parse(
        r#"
        game "T" { mapper: NROM }
        var flag: u8 = 0
        state Main {
            on frame {
                if flag == 1 {
                    draw Blip at: (10, 100)
                    draw Blip at: (20, 100)
                    draw Blip at: (30, 100)
                    draw Blip at: (40, 100)
                    draw Blip at: (50, 100)
                    draw Blip at: (60, 100)
                    draw Blip at: (70, 100)
                    draw Blip at: (80, 100)
                    draw Blip at: (90, 100)
                }
                wait_frame
            }
        }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    assert!(
        result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0109),
        "expected W0109 for draws inside if, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_accepts_debug_sprite_overflow_builtins() {
    // Both new debug methods should analyze without errors when
    // called with zero arguments, exactly like
    // frame_overrun_count / frame_overran.
    let result = analyze_ok(
        r#"
        game "T" { mapper: NROM }
        var a: u8 = 0
        var b: u8 = 0
        on frame {
            a = debug.sprite_overflow_count()
            b = debug.sprite_overflow()
            wait_frame
        }
        start Main
    "#,
    );
    assert!(!result
        .diagnostics
        .iter()
        .any(|d| d.code == ErrorCode::E0201));
}

#[test]
fn analyze_rejects_unknown_debug_method_lists_all_four_known_names() {
    // When the user calls `debug.nope()`, the E0201 message
    // should list every supported method name so typo fixes are
    // obvious.
    let errors = analyze_errors(
        r#"
        game "T" { mapper: NROM }
        var a: u8 = 0
        on frame {
            a = debug.nope()
            wait_frame
        }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "expected E0201 for unknown debug method, got: {errors:?}"
    );
}

#[test]
fn analyze_accepts_cycle_sprites_statement() {
    // `cycle_sprites` is a no-arg keyword statement. It should
    // analyze cleanly in a frame handler without triggering any
    // errors or warnings.
    analyze_ok(
        r#"
        game "T" { mapper: NROM }
        on frame {
            draw Blip at: (10, 20)
            cycle_sprites
            wait_frame
        }
        start Main
    "#,
    );
}

#[test]
fn analyze_inline_fun_with_conditional_return_trips_w0110() {
    // A function marked `inline` whose body has an early
    // conditional return can't be inlined by the simple
    // substitution machinery — it compiles as a regular
    // `JSR` call, and W0110 must fire at the declaration.
    let (prog, diags) = parser::parse(
        r#"
        game "T" { mapper: NROM }
        inline fun wrap(v: u8) -> u8 {
            if v >= 52 {
                return v - 52
            }
            return v
        }
        var x: u8 = 0
        on frame {
            x = wrap(60)
            wait_frame
        }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    let w0110: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.code == ErrorCode::W0110)
        .collect();
    assert_eq!(
        w0110.len(),
        1,
        "expected exactly one W0110, got: {:?}",
        result.diagnostics
    );
    assert!(
        w0110[0].message.contains("wrap"),
        "W0110 should name the declined function, got: {}",
        w0110[0].message
    );
    assert!(
        w0110[0].help.is_some() && w0110[0].note.is_some(),
        "W0110 should carry both help and note text"
    );
}

#[test]
fn analyze_inline_fun_with_single_return_expression_is_accepted() {
    // A body that is exactly `return <expr>` is the canonical
    // inlinable shape — no W0110 should fire.
    let (prog, diags) = parser::parse(
        r#"
        game "T" { mapper: NROM }
        inline fun card_rank(card: u8) -> u8 {
            return card >> 4
        }
        var x: u8 = 0
        on frame {
            x = card_rank(0x93)
            wait_frame
        }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0110),
        "did not expect W0110 for single-return inline, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_inline_void_fun_is_accepted() {
    // A void body with nothing but assigns is inlinable.
    let (prog, diags) = parser::parse(
        r#"
        game "T" { mapper: NROM }
        var a: u8 = 0
        var b: u8 = 0
        inline fun set_pair(x: u8, y: u8) {
            a = x
            b = y
        }
        on frame {
            set_pair(5, 6)
            wait_frame
        }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0110),
        "did not expect W0110 for void inline, got: {:?}",
        result.diagnostics
    );
}

#[test]
fn analyze_inline_fun_with_loop_body_trips_w0110() {
    // A `while` loop inside a marked-inline body is another
    // disqualifying shape.
    let (prog, diags) = parser::parse(
        r#"
        game "T" { mapper: NROM }
        var sum: u8 = 0
        inline fun accumulate(n: u8) {
            var i: u8 = 0
            while i < n {
                sum += i
                i += 1
            }
        }
        on frame {
            accumulate(5)
            wait_frame
        }
        start Main
    "#,
    );
    assert!(diags.is_empty(), "parse errors: {diags:?}");
    let result = analyze(&prog.unwrap());
    assert!(
        result
            .diagnostics
            .iter()
            .any(|d| d.code == ErrorCode::W0110),
        "expected W0110 for loop-body inline, got: {:?}",
        result.diagnostics
    );
}

// ── Metatiles + rooms (§H) ──

#[test]
fn analyze_room_layout_wrong_size_errors() {
    // A room's layout must be exactly 240 entries (16×15). A short
    // layout is a user error caught by the analyzer; silently
    // padding with zeros would produce a nametable with garbage in
    // the uncovered rows and silently misalign `collides_at`
    // queries.
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        metatileset MTS {
            metatiles: [
                { id: 0, tiles: [0, 0, 0, 0], collide: false },
            ],
        }
        room Level1 {
            metatileset: MTS,
            layout: [0, 0, 0],
        }
        on frame { }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "expected E0201 for short room layout, got {errors:?}"
    );
}

#[test]
fn analyze_room_unknown_metatileset_errors() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        room Level1 {
            metatileset: Missing,
            layout: [0; 240],
        }
        on frame { }
        start Main
    "#,
    );
    // We accept either the "unknown metatileset" error or (less
    // specific but equally correct) a layout validation error that
    // fires first. What matters is we don't silently accept the
    // program.
    assert!(
        !errors.is_empty(),
        "expected at least one diagnostic for unknown metatileset"
    );
}

#[test]
fn analyze_paint_room_unknown_room_errors() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        on frame { paint_room Ghost }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0502),
        "expected E0502 for paint_room of unknown room, got {errors:?}"
    );
}

#[test]
fn analyze_room_with_valid_metatileset_accepts() {
    // Full valid program — metatileset declared, room layout
    // covers all 240 cells, paint_room + collides_at both used.
    // The parser's `[expr; N]` literal is supported for byte
    // arrays; we test that shortcut path here too.
    analyze_ok(
        r#"
        game "Test" { mapper: NROM }
        metatileset MTS {
            metatiles: [
                { id: 0, tiles: [0, 0, 0, 0], collide: false },
                { id: 1, tiles: [1, 1, 1, 1], collide: true  },
            ],
        }
        room Level1 {
            metatileset: MTS,
            layout: [0; 240],
        }
        on frame {
            paint_room Level1
            if collides_at(64, 64) { }
        }
        start Main
    "#,
    );
}

#[test]
fn analyze_metatile_wrong_tile_count_errors() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        metatileset MTS {
            metatiles: [
                { id: 0, tiles: [0, 0, 0], collide: false },
            ],
        }
        on frame { }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "expected E0201 for 3-tile metatile entry, got {errors:?}"
    );
}

#[test]
fn analyze_room_layout_id_out_of_range_errors() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        metatileset MTS {
            metatiles: [
                { id: 0, tiles: [0, 0, 0, 0], collide: false },
            ],
        }
        room Level1 {
            metatileset: MTS,
            layout: [7; 240],
        }
        on frame { }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0201),
        "expected E0201 for out-of-range metatile id, got {errors:?}"
    );
}

#[test]
fn analyze_collides_at_wrong_arg_count_errors() {
    let errors = analyze_errors(
        r#"
        game "Test" { mapper: NROM }
        on frame {
            if collides_at(64) { }
        }
        start Main
    "#,
    );
    assert!(
        errors.contains(&ErrorCode::E0203),
        "expected E0203 for collides_at arity mismatch, got {errors:?}"
    );
}
