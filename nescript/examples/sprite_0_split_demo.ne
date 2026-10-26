// Sprite-0 split demo — `sprite_0_split(x, y)` busy-waits for the
// PPU's sprite-0 hit flag (`$2002` bit 6) and then writes the
// requested scroll values to `$2005`. This produces a mid-frame
// scroll change without needing MMC3's scanline IRQ, so the split
// works on NROM / UxROM / MMC1 — any mapper.
//
// For sprite-0 hit to actually fire we need:
//   1. A sprite in OAM slot 0 (the first `draw` in on_frame)
//   2. An opaque sprite pixel overlapping an opaque background
//      pixel at some visible scanline
//   3. Rendering enabled (automatic when we have a bg + palette)
//
// This demo draws the smiley as sprite 0 at (16, 24) so its bottom
// row falls on scanline 31, where it overlaps the background's
// smiley tiles. The split then resets the scroll so the second
// half of the frame scrolls independently from the first.

game "Sprite 0 Split Demo" {
    mapper: NROM
    mirroring: horizontal
}

palette Colors {
    universal: black
    bg0: [dk_blue, blue, sky_blue]
    bg1: [dk_red, red, lt_red]
    bg2: [dk_green, green, lt_green]
    bg3: [black, lt_gray, white]
    sp0: [dk_blue, blue, sky_blue]
    sp1: [red, orange, white]
    sp2: [dk_teal, teal, lt_teal]
    sp3: [dk_olive, olive, yellow]
}

background Tiled {
    // Every cell is tile 0 (the built-in smiley) so sprite 0's
    // opaque pixels overlap opaque background pixels at any
    // position on the screen — guaranteeing sprite-0 hit fires
    // on every frame regardless of sprite position.
    legend { ".": 0 }
    map: [
        "................................",
        "................................",
        "................................",
        "................................"
    ]
}

var top_scroll: u8 = 0

on frame {
    // Top half scrolls to the left each frame (wraps at 256).
    top_scroll += 1

    // Sprite 0 at row 24 → its bottom edge is at scanline 31,
    // which is inside the top-half scroll region. The hit fires
    // around scanline 31 of the current frame.
    draw Smiley at: (16, 24)

    // After sprite-0 fires we reset scroll_x to 0 and scroll_y
    // to 0, so the bottom half of the screen stays put while
    // the top half drifts. The effect is a "scrolling status
    // bar" pattern — classic technique for HUD-over-playfield.
    sprite_0_split(0, 0)

    // Set the top-half scroll AFTER sprite_0_split so the NEXT
    // frame's top half gets the drifting value. Writes to $2005
    // between NMI and sprite 0 affect the whole frame up to the
    // split point.
    scroll(top_scroll, 0)
}

start Main
