// Demonstrates nested struct fields and array fields inside structs.
//
// Two `Hero` instances each carry a `Vec2` position (a nested struct)
// and a small inventory `u8[4]` (an array field). Both heroes scoot
// across the screen in opposite directions, and their inventory bytes
// are advanced once per frame so the analyzer's flat-allocation model
// is exercised end-to-end.
//
// Compile with the default IR codegen:
//   nescript build examples/nested_structs.ne

game "NestedStructs" { mapper: NROM }

// Inner structs must be declared before any struct that nests them —
// the analyzer doesn't topologically sort declarations.
struct Vec2 {
    x: u8,
    y: u8,
}

// `pos` is a nested-struct field; `inv` is an array field. Both are
// fully addressable as `hero.pos.x` / `hero.inv[i]`. Layout in RAM
// is contiguous: pos.x, pos.y, hp, inv[0..3] — total 7 bytes per
// instance.
struct Hero {
    pos: Vec2,
    hp: u8,
    inv: u8[4],
}

// Hero positions are initialized inline. Both the nested
// `Vec2 { ... }` and the inline `inv: [1, 2, 3, 4]` array
// initializers are unpacked into per-leaf-field IR globals by
// `expand_struct_literal_init` in src/ir/lowering.rs, so each
// leaf gets its own `LDA #imm; STA addr` pair at reset.
var hero1: Hero = Hero { pos: Vec2 { x: 32, y: 96 }, hp: 100, inv: [1, 2, 3, 4] }
var hero2: Hero = Hero { pos: Vec2 { x: 200, y: 128 }, hp: 100, inv: [10, 20, 30, 40] }

on frame {
    // Walk both heroes — hero1 moves right, hero2 moves left, both
    // wrap around at the screen edge so the demo runs forever.
    hero1.pos.x += 1
    hero2.pos.x -= 1

    // Cycle the inventory bytes so the synthetic-array allocation
    // path takes a real read/write pair every frame.
    hero1.inv[0] += 1
    hero2.inv[0] += 1

    draw Smiley at: (hero1.pos.x, hero1.pos.y)
    draw Smiley at: (hero2.pos.x, hero2.pos.y)

    wait_frame
}

start Main
