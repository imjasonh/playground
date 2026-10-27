// The platform's track band: rows 10-17 of both nametables form a
// 64-column ring that the band scroll slides across. World column wc
// lives in ring column wc & 63. A train is six cars of 32 columns,
// world columns TRAIN_C0 to TRAIN_C1; everything else is empty track. Columns are streamed in at the right edge as the band scrolls.
//
// These functions live in the Gfx bank with the nametables they copy.

const BAND_ROW: u8 = 10
const BAND_ROWS: u8 = 8
const TRAIN_C0: u16 = 66
const TRAIN_C1: u16 = 258

// Nametable index of row BAND_ROW, column 0.
const BAND_NT_BASE: u16 = 320

// Band row of the LED side sign, and the car columns of its text
// (after the route bullet sprite).
const SIGN_ROW: u8 = 1
const SIGN_T0: u8 = SIGN_X + 2
const SIGN_T1: u8 = SIGN_X + SIGN_W

// Tile of band row r in world column wc. Every car's side sign shows
// sign_buf.
fun band_tile(wc: u16, r: u8) -> u8 {
    if wc < TRAIN_C0 or wc >= TRAIN_C1 {
        return NT_PLATFORM[BAND_NT_BASE + ((r as u16) << 5)]
    }
    var c: u8 = (wc - TRAIN_C0) as u8 & 31
    if r == SIGN_ROW and c >= SIGN_T0 and c < SIGN_T1 {
        var at: u8 = c - SIGN_T0
        if at < sign_len {
            return sign_buf[at] + FONT_BASE
        }
        return FONT_BASE
    }
    return NT_TRAIN[BAND_NT_BASE + c as u16 + ((r as u16) << 5)]
}

// Queue world column wc through the VRAM buffer.
fun band_col(wc: u16) {
    var ring: u8 = (wc as u8) & 63
    var x: u8 = ring & 31
    var y: u8 = BAND_ROW
    if ring >= 32 {
        y += 32
    }
    var r: u8 = 0
    while r < BAND_ROWS {
        nt_set(x, y, band_tile(wc, r))
        y += 1
        r += 1
    }
}

// Write world column wc straight to the PPU. Rendering must be off.
fun band_col_direct(wc: u16) {
    var ring: u8 = (wc as u8) & 63
    var hi: u8 = 0x21
    if ring >= 32 {
        hi = 0x25
    }
    var lo: u8 = 0x40 + (ring & 31)
    var r: u8 = 0
    while r < BAND_ROWS {
        vram_at(hi, lo)
        poke(0x2007, band_tile(wc, r))
        lo += 32
        if lo < 32 {
            hi += 1
        }
        r += 1
    }
}
