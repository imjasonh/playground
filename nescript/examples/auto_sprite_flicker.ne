// Auto sprite-flicker demo — same 12-sprite layout as
// `sprite_flicker_demo.ne`, but the explicit `cycle_sprites` call
// is replaced by the `game { sprite_flicker: true }` opt-in. The
// IR lowerer injects a `CycleSprites` op at the top of every
// `on frame` handler, which flips on the rotating-OAM NMI variant
// without any per-site boilerplate.

game "Auto Sprite Flicker Demo" {
    mapper: NROM
    sprite_flicker: true
}

on frame {
    // Twelve sprites on the same 8-pixel band, same as the
    // explicit sprite_flicker_demo — the PPU can only render
    // 8 per scanline.
    draw Star at: (16,  100)
    draw Star at: (32,  100)
    draw Star at: (48,  100)
    draw Star at: (64,  100)
    draw Star at: (80,  100)
    draw Star at: (96,  100)
    draw Star at: (112, 100)
    draw Star at: (128, 100)
    draw Star at: (144, 100)
    draw Star at: (160, 104)
    draw Star at: (176, 104)
    draw Star at: (192, 104)

    wait_frame
}

start Main
