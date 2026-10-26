// Sprite-flicker demo — showcases `cycle_sprites`, NEScript's
// opt-in mitigation for the NES's 8-sprites-per-scanline
// hardware limit.
//
// The PPU evaluates OAM each scanline and picks the first 8
// sprites that cover it; any 9th+ sprite on the same scanline
// is silently dropped. Without sprite cycling, the SAME sprite
// gets dropped every frame because the draw order is stable
// frame-to-frame — you get a permanent dropout that looks like
// a game bug.
//
// `cycle_sprites` rotates where the OAM DMA lands each frame,
// so the PPU's "first 8" sweep picks up a different subset
// each time. Sprites at the end of the OAM buffer still drop
// sometimes, but they drop *different* sprites on adjacent
// frames. The human eye reconstructs the missing pixels from
// frame persistence, so the failure mode looks like gentle
// flicker instead of missing objects. This is the classic NES
// technique used by Gradius, Battletoads, and every shmup
// that ever existed.
//
// This demo draws 12 sprites packed onto the same y row (row
// 100), two wider than the 8-per-scanline budget. Without the
// `cycle_sprites` call you would see sprites 9 through 12
// completely invisible forever. With it they flicker, and the
// scene is readable even though the hardware can only show 8
// of them on any single scanline.
//
// The W0109 analyzer warning fires at compile time for this
// layout because every coordinate is a literal — the three
// layers of defense (compile-time W0109, runtime flicker via
// `cycle_sprites`, debug-mode `debug.sprite_overflow*` telemetry)
// all apply here.
//
// Build: cargo run -- build examples/sprite_flicker_demo.ne

game "Sprite Flicker Demo" {
    mapper: NROM
}

on frame {
    // Twelve sprites on the same 8-pixel band: nine at y=100
    // plus three at y=104 (all overlap scanlines 104..107).
    // The PPU can only render 8 of them per scanline, so
    // without cycling four would be dropped every frame.
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

    // Rotate the OAM DMA offset by one slot. Over 12 frames
    // every sprite gets dropped approximately once, producing
    // visible flicker rather than permanent dropout.
    cycle_sprites

    wait_frame
}

start Main
