// Comparisons — uses every comparison operator (==, !=, <, <=,
// >, >=) to drive a different pip on screen. Each pip only
// lights up when its corresponding comparison is true, so at
// any given moment the set of visible pips is a direct readout
// of which comparisons are passing.
//
// What this exercises end-to-end:
//   - All six comparison operators in `if` conditions
//   - Their lowering through `CmpKind::{Eq,Ne,Lt,LtEq,Gt,GtEq}`
//     in `src/codegen/ir_codegen.rs::gen_cmp`
//   - Each one correctly mapping to `BEQ`/`BNE`/`BCC`/`BCS` and
//     producing the expected truth value in a branch
//
// The `value` variable ramps from 0 to 255 so the six
// comparisons against MIDPOINT (=128) all fire across one cycle.
//
// Build: cargo run -- build examples/comparisons.ne

game "Comparisons" {
    mapper: NROM
}

const MIDPOINT: u8 = 128

var value: u8 = 0

on frame {
    // Slowly ramp through 0..255 and wrap. At the wrap the u8
    // overflow resets value to 0 — intentional, the pips will
    // re-animate.
    value += 1

    // Always-visible player sprite so the harness has at least
    // one solid OAM entry every frame. Its position reflects
    // the current ramp value — easy to read at a glance.
    draw Player at: (value, 120)

    // Each comparison drives a pip at a fixed X position along
    // the top. When its condition is true, the pip draws; when
    // false, the draw is skipped and the cursor's next slot
    // stays hidden from the OAM clear's $FE Y byte.
    if value == MIDPOINT    { draw Pip at: ( 32, 16) }
    if value != MIDPOINT    { draw Pip at: ( 64, 16) }
    if value <  MIDPOINT    { draw Pip at: ( 96, 16) }
    if value <= MIDPOINT    { draw Pip at: (128, 16) }
    if value >  MIDPOINT    { draw Pip at: (160, 16) }
    if value >= MIDPOINT    { draw Pip at: (192, 16) }
}

start Main
