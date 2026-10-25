// Bouncing Ball — a sprite that bounces around the screen automatically.
//
// Build:  cargo run -- build examples/bouncing_ball.ne
// Output: examples/bouncing_ball.nes
//
// Note: In M1 the sprite name in `draw` is parsed but not resolved.
// All sprites use tile 0 from the built-in CHR data (a smiley face).
// Custom sprite declarations come in M3.

game "Bouncing Ball" {
    mapper: NROM
}

var px: u8 = 64
var py: u8 = 64
var dx: u8 = 1     // 1 = moving right, 0 = moving left
var dy: u8 = 1     // 1 = moving down,  0 = moving up

on frame {
    // Move horizontally
    if dx == 1 {
        px += 1
        if px >= 240 { dx = 0 }
    } else {
        px -= 1
        if px == 0 { dx = 1 }
    }

    // Move vertically
    if dy == 1 {
        py += 1
        if py >= 224 { dy = 0 }
    } else {
        py -= 1
        if py == 0 { dy = 1 }
    }

    draw Ball at: (px, py)
}

start Main
