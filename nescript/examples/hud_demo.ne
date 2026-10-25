// HUD demo — the VRAM update buffer driving a classic status-bar
// layout above a scrolling playfield.
//
// The playfield shows a ball bouncing back and forth; every wall
// hit bumps a score counter that the HUD renders at the right of
// the status row. A "lives" indicator on the left ticks down
// periodically and resets, demonstrating both `nt_set` (for
// single-cell updates when state changes) and `nt_fill_h` (for
// repeatedly painting a multi-cell indicator). `nt_attr` calls at
// startup paint the top row in a distinct palette so the HUD
// reads as "UI chrome" instead of "gameplay background".
//
// User code never touches `$2006` / `$2007` directly — it just
// appends records to the 256-byte ring at `$0400-$04FF` and the
// NMI handler drains them during vblank. Only cells whose backing
// state changed get a buffer entry: the demo tracks `last_score`
// and `last_lives` so the common "state didn't change this frame"
// path appends nothing.
//
// The visible NES output at native 256×240 is intentionally
// readable rather than flashy — see the table-of-tiles layout
// rather than a polished AAA HUD. Run the ROM in any emulator to
// watch the lives countdown and score tick over time.

game "HUD Demo" {
    mapper: NROM
    mirroring: horizontal
}

palette GameColors {
    universal: black
    bg0: [dk_blue,  blue,     sky_blue]    // playfield tiles
    bg1: [red,      white,    yellow]      // HUD palette
    bg2: [dk_green, green,    lt_green]
    bg3: [dk_gray,  lt_gray,  white]
    sp0: [black,    yellow,   white]       // ball sprite (yellow)
    sp1: [red,      orange,   white]
    sp2: [dk_teal,  teal,     lt_teal]
    sp3: [dk_olive, olive,    yellow]
}

// ── HUD tile art. The compiler allocates sprite tiles in
//    declaration order starting at tile 1 (tile 0 is the built-in
//    smiley used by the playfield). The constants below match
//    that order so the call sites can use names instead of magic
//    numbers.
//
// `#` = palette index 1; with bg1 = [red, white, yellow] that's
// red. `%` = index 2 = white. `@` = index 3 = yellow.

// Solid fill (everything index 1 = red) — the "HUD chrome"
// background. Pre-painting row 1 with this tile gives the HUD
// strip a uniform red look so individual cell writes (hearts,
// digits) show up as obviously different content.
sprite Bar {
    pixels: [
        "########",
        "########",
        "########",
        "########",
        "########",
        "########",
        "########",
        "########"
    ]
}

// White heart-on-red — uses index 2 (white) for the heart shape,
// index 1 (red) for the surrounding fill. Stands out crisply
// against the all-red Bar tiles.
sprite Heart {
    pixels: [
        "########",
        "#%%##%%#",
        "%%%%%%%%",
        "%%%%%%%%",
        "#%%%%%%#",
        "##%%%%##",
        "###%%###",
        "########"
    ]
}

// Yellow digit glyphs — all use index 3 (yellow) for the strokes
// and index 1 (red) for the surrounding fill. Big enough that the
// digit is readable even at NES resolution.
sprite Digit0 {
    pixels: [
        "########",
        "##@@@@##",
        "#@####@#",
        "#@####@#",
        "#@####@#",
        "#@####@#",
        "##@@@@##",
        "########"
    ]
}
sprite Digit1 {
    pixels: [
        "########",
        "###@@###",
        "##@@@###",
        "###@@###",
        "###@@###",
        "###@@###",
        "##@@@@##",
        "########"
    ]
}
sprite Digit2 {
    pixels: [
        "########",
        "##@@@@##",
        "#@####@#",
        "####@@##",
        "##@@####",
        "#@######",
        "#@@@@@@#",
        "########"
    ]
}
sprite Digit3 {
    pixels: [
        "########",
        "##@@@@##",
        "#@####@#",
        "####@@##",
        "######@#",
        "#@####@#",
        "##@@@@##",
        "########"
    ]
}
sprite Digit4 {
    pixels: [
        "########",
        "####@@##",
        "###@@@##",
        "##@##@##",
        "#@@@@@@#",
        "####@@##",
        "####@@##",
        "########"
    ]
}
sprite Digit5 {
    pixels: [
        "########",
        "#@@@@@@#",
        "#@######",
        "#@@@@@##",
        "######@#",
        "#@####@#",
        "##@@@@##",
        "########"
    ]
}
sprite Digit6 {
    pixels: [
        "########",
        "##@@@@##",
        "#@####@#",
        "#@@@@@##",
        "#@####@#",
        "#@####@#",
        "##@@@@##",
        "########"
    ]
}
sprite Digit7 {
    pixels: [
        "########",
        "#@@@@@@#",
        "######@#",
        "#####@##",
        "####@###",
        "###@####",
        "###@####",
        "########"
    ]
}
sprite Digit8 {
    pixels: [
        "########",
        "##@@@@##",
        "#@####@#",
        "##@@@@##",
        "#@####@#",
        "#@####@#",
        "##@@@@##",
        "########"
    ]
}
sprite Digit9 {
    pixels: [
        "########",
        "##@@@@##",
        "#@####@#",
        "##@@@@@#",
        "######@#",
        "#@####@#",
        "##@@@@##",
        "########"
    ]
}

// Yellow ball for the playfield, uses sp0 sub-palette
// (index 1 = yellow against universal black).
sprite Ball {
    pixels: [
        "..####..",
        ".######.",
        "########",
        "########",
        "########",
        "########",
        ".######.",
        "..####.."
    ]
}

background Playfield {
    // Pre-paint row 1 (where the HUD lives) with the solid Bar
    // tile so single-cell writes (hearts and digits) stand out
    // crisply against the uniform red background. Row 0 keeps the
    // default smiley so the attribute-painted strip has visible
    // chrome above the HUD content. Rows 2+ are zero-padded by
    // the parser to fill the rest of the nametable with smileys
    // — that's the playfield.
    legend {
        ".": 0    // smiley (default)
        "B": 1    // Bar — declared first sprite, lands at tile 1
    }
    map: [
        "................................",  // row 0: smiley chrome
        "BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB"   // row 1: red Bar canvas for HUD
    ]
}

// Tile-index constants matching the sprite-declaration order.
const BAR_TILE:    u8 = 1
const HEART_TILE:  u8 = 2
const DIGIT_BASE:  u8 = 3   // Digit N is at tile DIGIT_BASE + N

// Ball position + velocity.
var bx: u8 = 64
var by: u8 = 100
var dx: u8 = 1         // 1 = moving right, 0 = moving left
var dy: u8 = 1         // 1 = moving down,  0 = moving up

// HUD state.
var score:       u8 = 0
var lives:       u8 = 5
var last_score:  u8 = 255   // 255 forces an initial paint on frame 0
var last_lives:  u8 = 255
var life_tick:   u8 = 0
var attr_set:    u8 = 0     // 1 once the HUD attribute has been painted

on frame {
    // ── One-shot: paint all 8 top-row attribute bytes so the
    //    entire top four rows pick up sub-palette 1 (red HUD
    //    palette). `0b01010101` means all four 16×16 sub-
    //    quadrants of each metatile use sub-palette 1.
    if attr_set == 0 {
        attr_set = 1
        nt_attr(0,  0, 0b01010101)
        nt_attr(4,  0, 0b01010101)
        nt_attr(8,  0, 0b01010101)
        nt_attr(12, 0, 0b01010101)
        nt_attr(16, 0, 0b01010101)
        nt_attr(20, 0, 0b01010101)
        nt_attr(24, 0, 0b01010101)
        nt_attr(28, 0, 0b01010101)
    }

    // ── Playfield: bounce the ball, count bounces as score. ──
    if dx == 1 {
        bx += 1
        if bx >= 240 {
            dx = 0
            score += 1
            if score >= 10 { score = 0 }
        }
    } else {
        bx -= 1
        if bx == 16 {
            dx = 1
            score += 1
            if score >= 10 { score = 0 }
        }
    }
    if dy == 1 {
        by += 1
        if by >= 200 { dy = 0 }
    } else {
        by -= 1
        if by == 32 { dy = 1 }
    }
    draw Ball at: (bx, by)

    // ── HUD: tick lives once per second; reset to 5 at zero. ──
    life_tick += 1
    if life_tick >= 60 {
        life_tick = 0
        if lives == 0 {
            lives = 5
        } else {
            lives -= 1
        }
    }

    // ── HUD: rewrite only the cells whose backing state changed.
    //        `nt_set` for the score digit, `nt_fill_h` for the
    //        lives bar (plus a second fill to erase the stale
    //        tail with the Bar tile so the display "shrinks"
    //        cleanly). The shadow-compare skips the write on the
    //        ~58 of 60 frames where nothing changed.
    if score != last_score {
        last_score = score
        nt_set(28, 1, DIGIT_BASE + score)
    }
    if lives != last_lives {
        last_lives = lives
        nt_fill_h(2, 1, lives, HEART_TILE)
        if lives < 5 {
            var blanks: u8 = 5 - lives
            nt_fill_h(2 + lives, 1, blanks, BAR_TILE)
        }
    }
}

start Main
