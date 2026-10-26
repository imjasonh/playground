// sha256/render.ne — OAM shadow buffer helpers.
//
// The static screen (title, labels, keyboard grid) is baked into
// the `background Screen` nametable at reset time. Everything
// that changes frame-to-frame is drawn here as sprites on top:
// the keyboard cursor, the user's input buffer, and (after the
// compression phase finishes) the 64-character hex digest.
//
// Layouts are arranged to respect the NES's 8-sprites-per-
// scanline PPU limit. Input text is broken across 2 rows of 8,
// the digest across 8 rows of 8, and the cursor sits one tile
// to the left of the selected key so its scanlines don't
// intersect the keyboard row.

// ── Tile-index helpers ──────────────────────────────────────
//
// Map a character in the alphabet to its tile index inside
// Tileset. Covers the 26 uppercase letters, 10 digits, and the
// four punctuation glyphs used by the keyboard ('_', '.', '<',
// '>'). Any code not in the table maps to tile 44 (blank) so a
// stray byte never draws the built-in smiley.
fun tile_for_char(ch: u8) -> u8 {
    if ch >= 0x41 {
        if ch <= 0x5A {                // 'A'..'Z'
            return ch - 0x41 + 1       //   -> tile 1..26
        }
    }
    if ch >= 0x30 {
        if ch <= 0x39 {                // '0'..'9'
            return ch - 0x30 + 27      //   -> tile 27..36
        }
    }
    if ch == 0x20 {                    // space
        return 37                      //   -> underscore bar
    }
    if ch == 0x2E {                    // '.'
        return 38                      //   -> period glyph
    }
    if ch == KEY_BKSP {                // 0x08
        return 41
    }
    if ch == KEY_ENTER {               // 0x0A
        return 42
    }
    return 44                          // blank
}

// Return the tile index for a low nibble (0..15) rendered as a
// hexadecimal character glyph. 0..9 map to the digit tiles;
// 10..15 (A..F) to the letter tiles.
fun tile_for_nibble(n: u8) -> u8 {
    if n < 10 {
        return 27 + n                  // digits 0..9 → tiles 27..36
    }
    return 1 + (n - 10)                // A..F → tiles 1..6
}

// ── Cursor + input overlay (Entering / Computing states) ────

// Draw the keyboard cursor sprite. `blink` is a bit-flag: non-
// zero frames draw the arrow, zero frames hide it, producing a
// ~2 Hz flash that tells the player the keyboard is live.
fun draw_cursor(blink: u8) {
    if blink == 0 {
        return
    }
    // Compute pixel position of the *selected key* (kb_row,
    // kb_col), then shift 8 pixels left so the sprite lands one
    // tile column to the west — off the keyboard row, so the
    // cursor never eats into the 8-per-scanline budget.
    var cx: u8 = KB_BASE_X + (kb_col << 4) - 8
    var cy: u8 = KB_BASE_Y + (kb_row << 3)
    draw Tileset at: (cx, cy) frame: 43       // cursor glyph
}

// Draw the user's input buffer across two rows of 8 glyphs.
// Empty slots render as blank tiles. Row 0 is y=INPUT_BASE_Y,
// row 1 is y=INPUT_BASE_Y + INPUT_ROW_H. Both rows sit above
// the keyboard so their scanlines are distinct from any other
// sprite row — no `cycle_sprites` trick needed.
fun draw_input() {
    var i: u8 = 0
    while i < INPUT_MAX {
        var row: u8 = i >> 3                   // 0 or 1
        var col: u8 = i & 0x07                 // 0..7
        var sx: u8 = INPUT_BASE_X + (col << 3)
        var sy: u8 = INPUT_BASE_Y + (row << 3)     // INPUT_ROW_H = 8
        var ch: u8 = 0
        if i < msg_len {
            ch = msg[i]
        }
        draw Tileset at: (sx, sy) frame: tile_for_char(ch)
        i += 1
    }
}

// ── Digest overlay (Showing state) ──────────────────────────

// Draw the 64-nibble hexadecimal digest across 8 rows of 8
// glyphs. Reads h_state in its SHA-256-specified big-endian
// order: H_0 is the first u32, and inside each u32 the MSB is
// printed first. That makes the on-screen text match the hex
// digest most tools produce (e.g. shasum, Python's hexdigest).
fun draw_hash() {
    var word: u8 = 0
    while word < 8 {
        var base: u8 = word << 2                   // h_state byte index
        var nib_idx: u8 = 0
        while nib_idx < 8 {
            // Pick the byte of the word currently being printed.
            // nib_idx 0,1 -> byte 3 (MSB); 2,3 -> byte 2;
            // 4,5 -> byte 1; 6,7 -> byte 0 (LSB).
            var byte_off: u8 = 3 - (nib_idx >> 1)
            var byte_val: u8 = h_state[base + byte_off]
            var nibble: u8 = 0
            if (nib_idx & 1) == 0 {
                nibble = byte_val >> 4             // high nibble first
            } else {
                nibble = byte_val & 0x0F           // then low nibble
            }
            var char_idx: u8 = (word << 3) + nib_idx
            var row: u8 = char_idx >> 3            // 0..7
            var col: u8 = char_idx & 0x07          // 0..7
            var sx: u8 = HASH_BASE_X + (col << 3)
            var sy: u8 = HASH_BASE_Y + (row << 3)
            draw Tileset at: (sx, sy) frame: tile_for_nibble(nibble)
            nib_idx += 1
        }
        word += 1
    }
}
