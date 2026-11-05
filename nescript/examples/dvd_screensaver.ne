// DVD Screensaver — the DVD Video logo bouncing around a black screen
// and changing color every time it touches an edge.
//
// The logo is background tiles, not sprites, so it isn't held to the
// 8-sprites-per-scanline limit. `dvd_screensaver.png` holds the logo at
// the top-left of nametable 0, 96×43 pixels with anti-aliased edges in
// three shades of one color. Everything else on the plane is black, so
// moving the logo is just scrolling the background.
//
// The motion follows the screensaver's well-known rules: the same speed
// on both axes, so the logo always travels at 45 degrees, a perfect
// reflection off each edge, and a new color on each bounce. The logo
// steps one pixel on both axes every other frame, 30 pixels a second,
// so it takes about 8 seconds to cross the screen the way a DVD
// player's logo drifts, and it never moves in uneven steps.
//
// With those rules the logo is in a corner only when both axes hit a
// wall on the same step, which happens every lcm(W - w, H - h) steps.
// The logo moves inside the 240×224 picture a TV shows (8 pixels in
// from every edge), so W - w = 240 - 96 = 144 and H - h = 224 - 43 =
// 181. Those are coprime, so the corner hits do come, 144 × 181 =
// 26064 steps apart: one about every 14 minutes 29 seconds, with
// plenty of near misses in between. The corners come in pairs: the
// logo hits one corner, then the other corner on the same edge, and
// never the remaining two. From the starting position the first hit,
// the top-right corner, comes after 3528 steps, just under 2 minutes
// in, and the next is the top-left corner.
//
// Each bounce picks one of the seven colors the screensaver is known
// for, never the one the logo already has. A corner reverses both axes
// on one step and changes the color once.
//
// The logo art is rasterized from the DVD Video logo SVG in
// github.com/bemxio/dvd-screensaver (MIT).
//
// Build: cargo run -- build examples/dvd_screensaver.ne

game "DVD Screensaver" {
    mapper: NROM
    // Nametable 0 (the logo) sits beside nametable 1 (all black). The
    // vertical wrap repeats nametable 0, so any vertical scroll shows
    // the logo once.
    mirroring: vertical
}

// The picture a TV shows starts 8 pixels in from each edge.
const SAFE_LEFT: u8 = 8
const SAFE_TOP: u8 = 8
// How far the logo's top-left corner can travel inside that picture.
const RANGE_X: u8 = 144    // 240 - 96
const RANGE_Y: u8 = 181    // 224 - 43

// PPUCTRL: NMI on, and the scroll's nametable bit set. The scroll is
// 512 - X for a logo at screen X, which always lands in nametable 1.
const CTRL_SCROLL: u8 = 0x81
const MASK_ON: u8 = 0x1E

// Each color is three NES palette entries: the full color for the
// logo's solid pixels, and two darker shades of the same hue for its
// anti-aliased edges. Each shade is the NES entry closest to the full
// color at that coverage. The color id is the shared index.
const NUM_COLORS: u8 = 7
//                         red   blue  yellow cyan orange magenta green
const SHADE_FULL: u8[7] = [0x16, 0x12, 0x28, 0x2C, 0x17, 0x14, 0x1A]
const SHADE_MID: u8[7]  = [0x06, 0x01, 0x18, 0x1C, 0x07, 0x04, 0x09]
const SHADE_DARK: u8[7] = [0x07, 0x02, 0x08, 0x0C, 0x08, 0x04, 0x0B]
// Color 1 (blue) boots the screen.
const FIRST_COLOR: u8 = 1

// The importer picks each 16×16 area's sub-palette from its
// brightness, so all four background sub-palettes carry the logo's
// color.
palette Boot {
    universal: black
    bg0: [0x02, 0x01, 0x12]
    bg1: [0x02, 0x01, 0x12]
    bg2: [0x02, 0x01, 0x12]
    bg3: [0x02, 0x01, 0x12]
}

background Logo @nametable("dvd_screensaver.png")

// The logo's top-left corner inside the safe picture, 0..RANGE_X and
// 0..RANGE_Y. It starts near the middle, heading down and right.
var logo_x: u8 = 72
var logo_y: u8 = 92
var moving_right: bool = true
var moving_down: bool = true

// Written by `next_color`, applied by `frame_top` in vblank.
var color: u8 = FIRST_COLOR
var repaint: bool = true

// Flips every frame. The logo steps on the frames where it is true.
var step_frame: bool = false

// PPUMASK, applied by `frame_top`. The black fill turns it off.
var mask: u8 = 0

fun vram_at(hi: u8, lo: u8) {
    var unused: u8 = peek(0x2002)
    poke(0x2006, hi)
    poke(0x2006, lo)
}

// Fill nametable 1 with the black tile. The importer picks tile
// numbers, so read the black tile from a corner of nametable 0 that
// the logo doesn't cover. Rendering and NMI must be off.
fun fill_black() {
    vram_at(0x23, 0xBF)
    var stale: u8 = peek(0x2007)
    var blank: u8 = peek(0x2007)
    vram_at(0x24, 0x00)
    var i: u16 = 0
    while i < 960 {
        poke(0x2007, blank)
        i += 1
    }
    var j: u8 = 0
    while j < 64 {
        poke(0x2007, 0)
        j += 1
    }
}

// Write the current color into all four background sub-palettes.
fun paint_palette() {
    vram_at(0x3F, 0x00)
    var k: u8 = 0
    while k < 4 {
        poke(0x2007, 0x0F)
        poke(0x2007, SHADE_DARK[color])
        poke(0x2007, SHADE_MID[color])
        poke(0x2007, SHADE_FULL[color])
        k += 1
    }
}

// Apply the palette, scroll, and PPU registers for this frame. Call
// first thing in the frame handler, while the PPU is still in vblank.
fun frame_top() {
    if repaint {
        paint_palette()
        repaint = false
    }
    var unused: u8 = peek(0x2002)
    scroll(0 - (SAFE_LEFT + logo_x), 240 - (SAFE_TOP + logo_y))
    poke(0x2000, CTRL_SCROLL)
    poke(0x2001, mask)
}

// Pick a random color other than the current one.
fun next_color() {
    var skip: u8 = rand8() & 7
    while skip >= NUM_COLORS - 1 {
        skip = rand8() & 7
    }
    var next: u8 = color + 1 + skip
    if next >= NUM_COLORS {
        next -= NUM_COLORS
    }
    color = next
    repaint = true
}

// Move one pixel on each axis. Touching an edge reverses that axis
// on the same step, and a corner reverses both but changes the
// color once.
fun step() {
    var bounced: bool = false
    if moving_right {
        logo_x += 1
        if logo_x == RANGE_X {
            moving_right = false
            bounced = true
        }
    } else {
        logo_x -= 1
        if logo_x == 0 {
            moving_right = true
            bounced = true
        }
    }
    if moving_down {
        logo_y += 1
        if logo_y == RANGE_Y {
            moving_down = false
            bounced = true
        }
    } else {
        logo_y -= 1
        if logo_y == 0 {
            moving_down = true
            bounced = true
        }
    }
    if bounced {
        next_color()
    }
}

state Screensaver {
    on enter {
        poke(0x2001, 0)
        poke(0x2000, 0)
        fill_black()
        poke(0x2000, CTRL_SCROLL)
        mask = MASK_ON
        // The fill ran past at least one vblank with NMI off. Wait
        // for a fresh one so the first frame handler starts inside it
        // and turns rendering on before the frame begins.
        wait_frame
    }

    on frame {
        frame_top()
        step_frame = not step_frame
        if step_frame {
            step()
        }
    }
}

start Screensaver
