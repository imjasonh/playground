// PPU helpers. Screen loads run with rendering and NMI off, so they
// write $2006/$2007 directly instead of going through the VRAM buffer.

// Turn rendering and NMI off. Call at the start of a screen load.
fun screen_off() {
    mask = 0
    poke(0x2001, 0)
    poke(0x2000, 0)
}

// Turn NMI back on. The next frame handler turns rendering on.
fun screen_on() {
    poke(0x2000, CTRL_BASE)
    mask = 0x1E
}

fun vram_at(hi: u8, lo: u8) {
    var unused: u8 = peek(0x2002)
    poke(0x2006, hi)
    poke(0x2006, lo)
}

// Map one 4 KB CHR page as the background pattern table.
fun bg_page(p: u8) {
    poke(0x8000, 0)
    poke(0x8001, p << 2)
    poke(0x8000, 1)
    poke(0x8001, (p << 2) + 2)
}

// Write the eight colors of a background palette pair (4 + 4) at
// $3F00 + 4 * slot.
fun pal_set(slot: u8, c1: u8, c2: u8, c3: u8) {
    vram_at(0x3F, slot << 2)
    poke(0x2007, 0x0F)
    poke(0x2007, c1)
    poke(0x2007, c2)
    poke(0x2007, c3)
}

// Write text_buf[0..text_len] at the current VRAM address, then pad
// with blanks up to `width` cells.
fun vram_text(width: u8) {
    var i: u8 = 0
    while i < text_len {
        poke(0x2007, text_buf[i] + FONT_BASE)
        i += 1
    }
    while i < width {
        poke(0x2007, FONT_BASE)
        i += 1
    }
}

// Copy a run of text_buf into nametable row `y` through the VRAM
// buffer, while rendering. Writes `width` cells starting at `x`.
fun nt_text(x: u8, y: u8, width: u8) {
    var i: u8 = 0
    while i < width {
        var c: u8 = FONT_BASE
        if i < text_len {
            c = text_buf[i] + FONT_BASE
        }
        nt_set(x + i, y, c)
        i += 1
    }
}

// Put a short literal string into text_buf. Codes follow the font
// order in gen_gfx.py: space, A-Z, a-z, 0-9, then punctuation.
fun text_digit2(pos: u8, v: u8) {
    text_buf[pos] = 53 + v / 10
    text_buf[pos + 1] = 53 + v % 10
}

// Set the frame-top scroll and PPUCTRL. Call first thing in a frame
// handler, while the PPU is still in vblank.
fun frame_top() {
    scroll(top_x, top_y)
    poke(0x2000, CTRL_BASE)
    poke(0x2001, mask)
}
