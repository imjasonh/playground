// Palette brightness demo — cycle through the 9 brightness levels
// every ~20 frames. Exercises the `set_palette_brightness` builtin,
// which writes PPU mask emphasis bits for cheap neslib-style fades.

game "Palette Brightness Demo" {
    mapper: NROM
}

var frame: u8 = 0
var level: u8 = 4  // normal

on frame {
    frame += 1
    // Every 20 frames, bump the brightness level. Roll back to 0
    // at 9 so we cycle through the full 0..8 range.
    if frame >= 20 {
        frame = 0
        level += 1
        if level >= 9 {
            level = 0
        }
        set_palette_brightness(level)
    }

    draw Ball at: (120, 100)
}

start Main
