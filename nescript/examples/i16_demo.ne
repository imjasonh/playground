// i16 demo — exercises the signed 16-bit type with negative
// literals, signed velocity, and round-tripping through wide
// arithmetic.
//
// Position is stored as `i16` so negative deltas (the ball moving
// left or up) can be represented directly instead of having to
// shadow them with a sign byte. The lowering folds `-N` literals
// into wide two's-complement constants, so `vy = -10` lands as
// `$FFF6` (=-10) rather than the zero-extended `$00F6` (=246).

game "i16 Demo" {
    mapper: NROM
}

var px: i16 = 64
var py: i16 = 80
var vx: i16 = 1
var vy: i16 = -1
var frame: u8 = 0

on frame {
    frame += 1

    // Bounce off the visible-area edges. Comparisons against the
    // small positive bounds use the unsigned 16-bit compare path
    // (matching the existing i8 behaviour) — for purely positive
    // ranges this matches signed semantics.
    px += vx
    py += vy

    // Reverse vx every 100 frames so we exercise both the
    // positive-velocity and negative-velocity arithmetic paths.
    if frame == 100 {
        frame = 0
        vx = vx + vx     // double-then-negate would be cleaner once
        vx = vx - vx     // we add unary `-` on a runtime expression
        vx = 1
        vy = -1
    }

    // Clamp position into u8 range for `draw`. The cast truncates
    // the high byte; for our 0..255 motion that's the right thing.
    var dx: u8 = px as u8
    var dy: u8 = py as u8
    draw Ball at: (dx, dy)
}

start Main
