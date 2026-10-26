// Palette and Background Demo — shows the `palette` and
// `background` declarations plus runtime `set_palette` /
// `load_background` swaps.
//
// The program declares two palettes and two backgrounds. The
// *first* of each is loaded at reset time (before rendering is
// enabled) so the title screen comes up with the right colours
// and nametable on frame 0. A frame counter then toggles between
// the two palettes every 90 frames and between the two backgrounds
// every 180 frames, exercising the vblank-safe update path.
//
// Background tile 0 is the compiler's built-in smiley face (see
// the default CHR in `src/linker/mod.rs`). Tile indices 1+ would
// need matching `sprite` declarations with `chr:` data — we stick
// to tile 0 so the example is self-contained.
//
// Build:  cargo run -- build examples/palette_and_background.ne
// Output: examples/palette_and_background.nes

game "Palette + BG Demo" {
    mapper: NROM
    mirroring: horizontal
}

// ── Palettes ────────────────────────────────────────────────
//
// Both palettes are authored in grouped form: one shared
// `universal:` colour feeds every sub-palette's index-0 slot,
// which auto-fixes the `$3F10/$3F14/$3F18/$3F1C` PPU mirror
// trap (the parser handles the packing). Each `bgN` / `spN`
// field only needs three colours — the universal is prepended.
//
// Named NES colours resolve to master-palette indices via the
// curated name table; see `docs/language-guide.md` for the full
// list. Hex byte literals (`0x01`, `0x14`, …) still work if you
// need a colour that doesn't have a name.

palette CoolBlues {
    universal: black
    bg0: [dk_blue, blue, sky_blue]         // deep blue highlights
    bg1: [indigo, royal_blue, periwinkle]  // cool purples
    bg2: [dk_cyan, cyan, lt_cyan]          // aquas
    bg3: [dk_teal, teal, lt_teal]          // teal accents
    sp0: [dk_blue, blue, sky_blue]         // matches bg0
    sp1: [red, orange, white]              // warm accent sprites
    sp2: [magenta, lt_magenta, pale_pink]  // magenta sprites
    sp3: [dk_teal, teal, lt_teal]          // matches bg3
}

palette WarmReds {
    universal: black
    bg0: [dk_red, red, lt_red]             // fiery warm bg
    bg1: [brown, dk_orange, orange]        // autumnal
    bg2: [dk_olive, olive, yellow]         // muted yellows
    bg3: [dk_green, green, lt_green]       // greens for contrast
    sp0: [dk_red, red, lt_red]             // matches bg0
    sp1: [red, orange, white]              // highlight sprites
    sp2: [magenta, lt_magenta, pale_pink]  // pinks
    sp3: [dk_teal, teal, lt_teal]          // cool accent
}

// ── Backgrounds ─────────────────────────────────────────────
//
// A 32×30 nametable is 960 tile bytes + 64 attribute bytes. We
// only specify the first few tiles per background — the rest of
// the nametable is zero-padded by the asset pipeline, so
// undeclared cells render as tile 0 (the built-in smiley). The
// attribute table is left empty so every 16×16 metatile uses
// background sub-palette 0 (which is where CoolBlues / WarmReds
// put their headline colour).
//
// TitleScreen paints a short ribbon of tile 0 across row 14 (the
// middle of the screen). StageOne paints a diagonal stripe from
// top-left to bottom-right so the swap is visually obvious.

background TitleScreen {
    // Both backgrounds resolve to an all-zero nametable for this
    // demo — the visual difference between them comes from the
    // palette swap triggered alongside `load_background`. We still
    // author them with a `legend` + `map:` block here so the demo
    // exercises the pleasant syntax the same way a real game
    // would. The '.' legend entry alone is enough to fill an
    // all-tile-0 background; every row is padded to 32 columns
    // automatically by the parser.
    legend { ".": 0 }
    map: [
        "................................",   // row 0
        "................................",   // row 1
        "................................",   // row 2
        "................................",   // row 3
        "................................",   // row 4
        "................................",   // row 5
        "................................",   // row 6
        "................................",   // row 7
        "................................",   // row 8
        "................................",   // row 9
        "................................",   // row 10
        "................................",   // row 11
        "................................",   // row 12
        "................................",   // row 13
        "................................",   // row 14 (ribbon)
        "................................"    // row 15
    ]
}

background StageOne {
    // StageOne's visual difference comes from the palette swap —
    // the tile grid is still the built-in smiley everywhere. We
    // only declare 4 rows to prove the parser's zero-padding
    // still works with the new tilemap form.
    legend { ".": 0 }
    map: [
        "................................",
        "................................",
        "................................",
        "................................"
    ]
}

var tick: u8 = 0
var phase: u8 = 0

on frame {
    tick += 1

    // Every 90 frames toggle the palette between the two.
    if tick >= 90 {
        tick = 0
        phase += 1
        if phase == 4 {
            phase = 0
        }
    }

    // Phase 0: CoolBlues + TitleScreen
    // Phase 1: WarmReds + TitleScreen
    // Phase 2: CoolBlues + StageOne
    // Phase 3: WarmReds  + StageOne
    //
    // We reissue the set_palette / load_background call on every
    // phase transition (the single-frame condition also keeps the
    // golden stable — the jsnes test only renders a handful of
    // frames and the comparison runs without any controller input).
    if tick == 1 {
        if phase == 0 {
            set_palette CoolBlues
            load_background TitleScreen
        }
        if phase == 1 {
            set_palette WarmReds
            load_background TitleScreen
        }
        if phase == 2 {
            set_palette CoolBlues
            load_background StageOne
        }
        if phase == 3 {
            set_palette WarmReds
            load_background StageOne
        }
    }

    // Draw a single sprite tracking the tick so the sprite still
    // moves on screen and the golden diff tests spot regressions
    // in OAM DMA alongside the palette/background path.
    draw Smiley at: (tick + 60, 120)
}

start Main
