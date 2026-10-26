// VRAM update buffer demo — `nt_set`, `nt_attr`, and `nt_fill_h`
// append entries to a 256-byte ring at `$0400-$04FF` during
// `on frame`; the NMI handler drains them to PPU `$2007` during
// vblank. This is the idiom every nesdoug HUD / dialog box / score
// counter is built on — the user code never touches `$2006` or
// `$2007` directly, just appends record after record.
//
// This demo paints a "scoreboard" of three tiles in the top row
// each frame, then fills a 16-tile horizontal stripe a few rows
// down with a single tile pattern. Frame 180 captures the scene
// after the buffer has drained the same set of writes for ~3
// seconds — the visible output is stable.

game "VRAM Buffer Demo" {
    mapper: NROM
    mirroring: horizontal
}

palette Default {
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

background Empty {
    legend { ".": 0 }
    map: [
        "................................"
    ]
}

on frame {
    // Three single-tile writes for a tiny "score" digit row.
    // Each call appends a 4-byte buffer entry: [len=1][hi][lo][tile].
    nt_set(2, 1, 1)
    nt_set(3, 1, 2)
    nt_set(4, 1, 3)

    // A horizontal fill: 16 copies of the smiley starting at (8, 4).
    // Buffer entry is [len=16][hi][lo][tile × 16] = 19 bytes.
    nt_fill_h(8, 4, 16, 0)

    // Update the attribute byte for the metatile that contains the
    // score row so it picks up sub-palette 1 (red gradient) for
    // visual contrast against the rest of the screen. (x, y) here
    // are nametable cell coordinates; the codegen translates to
    // the attribute table address $23C0+.
    nt_attr(0, 0, 0b01010101)
}

start Main
