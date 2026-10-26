// Sprites and Scroll — demonstrates M3/M4 asset features.
//
// Shows: sprite declarations with inline CHR data, type casting,
// PPU scroll writes.
//
// Build: cargo run -- build examples/sprites_and_palettes.ne

game "Asset Demo" {
    mapper: NROM
}

// Define a sprite with ASCII pixel art. Each character maps to a
// 2-bit palette index: `.` = 0 (transparent), `#` = 1, `%` = 2,
// `@` = 3. The parser handles the 2-bitplane CHR encoding, so we
// never touch hex bytes by hand.
//
// Arrow — a right-facing arrow in palette-index 1.
sprite Arrow {
    pixels: [
        "...##...",
        "...###..",
        "#######.",
        "########",
        "########",
        "#######.",
        "...###..",
        "...##..."
    ]
}

// Heart — a full-colour heart in palette-index 3 (the brightest
// shade, `@`).
sprite Heart {
    pixels: [
        ".@@..@@.",
        "@@@@@@@@",
        "@@@@@@@@",
        "@@@@@@@@",
        ".@@@@@@.",
        "..@@@@..",
        "...@@...",
        "........"
    ]
}

var px: u8 = 128
var py: u8 = 120
var scroll_x: u8 = 0

on frame {
    // Movement
    if button.right { px += 2 }
    if button.left  { px -= 2 }
    if button.down  { py += 2 }
    if button.up    { py -= 2 }

    // Scroll background
    scroll_x += 1
    scroll(scroll_x, 0)

    // Type cast demo
    var wide: u16 = px as u16

    // Draw sprites
    draw Arrow at: (px, py)
    draw Heart at: (px, py - 16)
}

start Main
