// Friendly Assets Demo — showcases NEScript's pleasant-to-author
// asset syntax. Every one of the "raw byte" art forms (palettes,
// CHR tiles, nametables, attribute tables, sfx envelopes, music
// note indices) has a friendlier alternative so you don't have to
// reach for a hex editor to make your game look and sound good.
//
// This demo uses every one of them at once:
//
//   1. Named NES colours (`black`, `sky_blue`, `dk_red`, …) inside
//      a grouped `palette` declaration with per-slot fields and a
//      shared `universal:` colour — auto-fixes the $3F10 mirror.
//   2. A `sprite` declared with ASCII pixel art rather than 16
//      bytes of 2-bitplane CHR.
//   3. A `background` laid out with a `legend` + `map:` tilemap
//      and a `palette_map:` grid that auto-packs the 64-byte
//      attribute table.
//   4. An `sfx` with a scalar `pitch:` (matching the v1 driver's
//      latch-once behaviour) and the friendlier `envelope:` alias.
//   5. A `music` track written with note names (`C4, E4 40, rest 10`)
//      plus a default `tempo:` so the common case stays concise.
//
// Build:  cargo run --release -- build examples/friendly_assets.ne
// Output: examples/friendly_assets.nes

game "Friendly Assets" {
    mapper: NROM
    mirroring: horizontal
}

// ── Palette ────────────────────────────────────────────────
//
// Grouped form: one `universal:` field feeds every sub-palette's
// shared index-0 byte (fixing the PPU mirror trap where the last
// four bytes of the 32-byte blob would otherwise clobber the
// background universal colour). Each `bgN` / `spN` field only
// needs three colours — `universal` supplies the fourth.
//
// Every colour here is a named constant; see docs/language-guide.md
// for the full list. Hex byte literals (`0x0F`, `0x21`, …) still
// work if you prefer them.

palette Sunset {
    universal: black                   // shared background colour
    bg0: [dk_blue,  blue,    sky_blue] // horizon
    bg1: [dk_red,   red,     peach]    // clouds
    bg2: [dk_olive, olive,   cream]    // ground highlights
    bg3: [dk_gray,  lt_gray, white]    // rocks
    sp0: [dk_blue,  blue,    sky_blue] // player body uses bg0 tones
    sp1: [dk_red,   red,     peach]    // enemies
    sp2: [dk_green, green,   mint]     // pickups
    sp3: [dk_gray,  lt_gray, white]    // UI / text
}

// ── Sprite ─────────────────────────────────────────────────
//
// ASCII pixel art. Characters map to 2-bit palette indices:
//
//   `.` or ` ` → 0 (transparent)
//   `#` or `1` → 1 (darker shade)
//   `%` or `2` → 2 (mid shade)
//   `@` or `3` → 3 (highlight)
//
// 8x8 for a plain tile; multiples of 8 in either dimension for
// multi-tile sprites (emitted in row-major reading order).

sprite Star {
    pixels: [
        "...@@...",
        "..@##@..",
        ".@####@.",
        "@######@",
        ".@####@.",
        "..@##@..",
        "...@@...",
        "........"
    ]
}

// ── Background ─────────────────────────────────────────────
//
// `legend { ... }` names each tile index with a single character;
// `map:` is the 32×30 nametable authored directly as one string
// per row. Short rows are right-padded with tile 0; fewer than 30
// rows pads the bottom with tile 0 as well.
//
// `palette_map:` is a 16×15 grid of sub-palette digits (`0`-`3`)
// where each cell covers one 16×16 metatile. The parser packs it
// into the awkward 8×8 attribute table automatically — no more
// hand-computing `(br<<6)|(bl<<4)|(tr<<2)|tl` by eye.

background Horizon {
    legend {
        ".": 0       // sky (built-in smiley tile as a stand-in)
        "S": 0       // star placeholder — same tile
    }
    // Sparse map: every cell in the first three rows is tile 0.
    // This is enough to exercise the tile + attribute pipeline
    // without depending on sprite CHR we haven't declared.
    map: [
        "................................",
        "................................",
        "................................"
    ]
    // Paint the top two metatile rows (rows 0-1) with sub-palette 1
    // so the sky uses the warm cloud colours. The next 13 rows use
    // sub-palette 0 (cool blues).
    palette_map: [
        "1111111111111111",
        "1111111111111111",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000",
        "0000000000000000"
    ]
}

// ── SFX ────────────────────────────────────────────────────
//
// Scalar `pitch:` + `envelope:` alias. The v1 audio driver only
// reads the first `pitch` byte (it latches the pulse period on
// trigger and never updates it) so a per-frame array was always
// redundant — a single byte makes the intent obvious.

sfx Chime {
    duty: 2
    pitch: 0x40                         // latched period byte
    envelope: [15, 14, 13, 12, 10, 8, 6, 4, 2, 1]
}

// ── Music ──────────────────────────────────────────────────
//
// `tempo:` sets the default frames-per-note; individual notes can
// override it by trailing the name with a frame count. Note names
// are C1..B5 with `Cs4`/`Db4` style accidentals (`#` and `♭` are
// not valid identifier characters so sharp/flat use a letter).

music Waltz {
    duty: 2
    volume: 10
    repeat: true
    tempo: 20
    notes: [
        C4, E4, G4, C5,                 // rising C major chord
        G4 40,                          // held chord tone
        rest 10,                        // brief pause
        E4, C4,                         // descent
        B4, D5, Fs5, B5,                // up a fifth with a sharp
        A4 30,                          // landing note
        rest 20                         // bar break
    ]
}

// ── Game state ─────────────────────────────────────────────

var px: u8 = 120
var py: u8 = 112
var tick: u8 = 0
var music_on: bool = false

on frame {
    tick += 1

    // Let the d-pad nudge the star around the screen.
    if button.right { px += 1 }
    if button.left  { px -= 1 }
    if button.down  { py += 1 }
    if button.up    { py -= 1 }

    // A / B ping the sfx so the envelope is audible under Mesen.
    if button.a { play Chime }
    if button.b { play Chime }

    // Auto-start the waltz once on the first frame so the jsnes
    // golden-capture run (which doesn't simulate input) still
    // hits the music driver's start path.
    if tick == 10 {
        if music_on {
            // Already playing — nothing to do.
        } else {
            start_music Waltz
            music_on = true
        }
    }

    // Keep a baseline sfx chirp so the audio golden is non-silent
    // even when the music is between notes.
    if tick == 120 {
        tick = 0
        play Chime
    }

    draw Star at: (px, py)
}

start Main
