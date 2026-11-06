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
// Left alone, that is all it does. The controller changes it only when
// somebody picks one up:
//
// - Player 1 can fight the logo. Pressing the opposite of the logo's
//   direction on an axis holds it still on that axis, so a logo
//   heading up and right that is pushed down only moves right. Pushing
//   the way it already goes does nothing. Any button press counts as
//   input, and from then on a corner hit plays the coin sound. A miss
//   within 4 pixels counts: one axis meets its wall while the other is
//   that close and still heading for its own. The bounce itself does
//   not change, so a logo nobody has touched still reaches an exact
//   corner only every 26064 steps.
// - Player 2 presses START to launch a second logo, a 2/3-scale copy
//   built from sprites (a background can only be scrolled as one
//   piece). It bounces, changes color, and fights the d-pad on
//   controller 2 by the same rules. When the logos meet they bounce off
//   each other as they would off a wall, change color, and play a bump.
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

// Logo 0 is player 1's: the background logo, 96×43. Logo 1 is player 2's:
// the 64×28 sprite logo. Every table below is indexed by logo id.
const LOGO_W: u8[2] = [96, 64]
const LOGO_H: u8[2] = [43, 28]
// How far each logo's top-left corner can travel inside the picture:
// 240 - width and 224 - height.
const RANGE_X: u8[2] = [144, 176]
const RANGE_Y: u8[2] = [181, 196]

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

// What a step did on one axis.
const HIT_NONE: u8 = 0
const HIT_WALL: u8 = 1
const HIT_LOGO: u8 = 2

// After a player has pressed a button, the coin plays when the logo
// comes this close to a corner, not only on an exact one. An untouched
// logo ignores this and still bounces only on a real wall.
const CORNER_FORGIVE: u8 = 4

// Bits of `push`, the d-pad presses a logo has not yet acted on.
const PUSH_UP: u8 = 1
const PUSH_DOWN: u8 = 2
const PUSH_LEFT: u8 = 4
const PUSH_RIGHT: u8 = 8

// Player 2's logo launches at the top, or at the bottom when player 1's
// logo is within LAUNCH_CLEAR of the top, so the two never start
// overlapped. It starts LAUNCH_INSET pixels in from that edge, heading
// away from it.
const LAUNCH_X: u8 = 88
const LAUNCH_CLEAR: u8 = 40
const LAUNCH_INSET: u8 = 4

// The importer picks each 16×16 area's sub-palette from its
// brightness, so all four background sub-palettes carry the logo's
// color. Player 2's sprite palette starts the same way and is
// repainted when the logo launches.
palette Boot {
    universal: black
    bg0: [0x02, 0x01, 0x12]
    bg1: [0x02, 0x01, 0x12]
    bg2: [0x02, 0x01, 0x12]
    bg3: [0x02, 0x01, 0x12]
    sp0: [0x02, 0x01, 0x12]
}

background Logo @nametable("dvd_screensaver.png")

// An all-clear tile that nothing draws. The sprites take tiles from 1
// in declaration order, and tile 0 holds the built-in smiley because
// player 2's logo is drawn with a metasprite. A background tile is the
// same tile in the same pattern table, so this is the black that
// `fill_black` paints nametable 1 with.
const BLACK_TILE: u8 = 1
sprite Black {
    pixels: [
        "........",
        "........",
        "........",
        "........",
        "........",
        "........",
        "........",
        "........"
    ]
}

// Player 2's logo: `dvd_screensaver.png` scaled to 2/3 and cut into
// 8×8 tiles, 8 across and 4 down, one sprite per tile in reading order.
// Eight sprites in a row is exactly the per-scanline limit, and nothing
// else is a sprite. The art is inline, not `@chr`, because a metasprite
// can only place inline sprites. `.` is clear and `#`, `%`, and `@`
// are the dark, medium, and full shades.
sprite LogoArt {
    pixels: [
        ".....%@@@@@@@@@@@@@@@@@@@@@@@#..........@@@@@@@@@@@@@@@@%%##....",
        ".....@@@@@@@@@@@@@@@@@@@@@@@@#.........%@@@@@@@@@@@@@@@@@@@@%...",
        "....#@@@@@@@@@@@@@@@@@@@@@@@@%........%@@@@@@@@@@@@@@@@@@@@@@@#.",
        "....#%%%%%%%%%@@@@@@@@@@@@@@@@.......#@@@@@@%%%%%%%%%%@@@@@@@@%.",
        "....######......%@@@@@@@%@@@@@#.....#@@@@@%.######......%@@@@@@%",
        "....@@@@@@.......#@@@@@@%@@@@@%.....@@@@@@##@@@@@%.......%@@@@@@",
        "....@@@@@@........@@@@@@%%@@@@@....%@@@@@#.%@@@@@#.......#@@@@@@",
        "...#@@@@@%........@@@@@@##@@@@@#..%@@@@@#..%@@@@@#.......#@@@@@@",
        "...%@@@@@#........@@@@@@..@@@@@%.#@@@@@%...@@@@@@........#@@@@@%",
        "...%@@@@@#.......%@@@@@%..%@@@@@#@@@@@%...#@@@@@%........%@@@@@#",
        "..#@@@@@@.......#@@@@@%...#@@@@@@@@@@%....#@@@@@%.......%@@@@@%.",
        "..#@@@@@%......%@@@@@@#...#@@@@@@@@@%.....%@@@@@#.....#%@@@@@%..",
        "..%@@@@@%###%@@@@@@@%#.....%@@@@@@@@......@@@@@@####%@@@@@@@%...",
        "..%@@@@@@@@@@@@@@@@#.......#@@@@@@@#......@@@@@@@@@@@@@@@@@#....",
        "..@@@@@@@@@@@@@@%#..........@@@@@@#......#@@@@@@@@@@@@@@%#......",
        "..@@@@@@@@@@@%##............%@@@@%.......%@@@@@@@@@@%%##........",
        "............................#@@@#...............................",
        ".............................%@%................................",
        ".............................%%.................................",
        "................................................................",
        "............######%%%%%%%%%%%%%%%%%%%%%%%%######................",
        "......##%%%%@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@%%%%##..........",
        "..#%@@@@@@@@@#%@%#%@@%#@@@%###%@@@@###%@@@%####%@@@@@@@@%##.....",
        "%@@@@@@@@@@@@##@#.@@@%#@@@%.%%.%@@@##%@@@@.#%%#.@@@@@@@@@@@%....",
        "@@@@@@@@@@@@@@.#.%@@@%#@@@%.@@##@@@###%@@%.%@@%.@@@@@@@@@@@@....",
        "#@@@@@@@@@@@@@%.#@@@@%#@@@%.@%.%@@@##@@@@@.#@@#.@@@@@@@@@@@#....",
        "...#%%@@@@@@@@@#@@@@@@#@@@%###%@@@@%##%@@@@####@@@@@@@%%%#......",
        "......####%@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@%%###..........",
        "...............##%%%@@@@@@@@@@@@@@@@@@@@@%%##...................",
        "................................................................",
        "................................................................",
        "................................................................"
    ]
}

metasprite Logo2 {
    sprite: LogoArt
    dx:    [0, 8, 16, 24, 32, 40, 48, 56,
            0, 8, 16, 24, 32, 40, 48, 56,
            0, 8, 16, 24, 32, 40, 48, 56,
            0, 8, 16, 24, 32, 40, 48, 56]
    dy:    [0, 0, 0, 0, 0, 0, 0, 0,
            8, 8, 8, 8, 8, 8, 8, 8,
            16, 16, 16, 16, 16, 16, 16, 16,
            24, 24, 24, 24, 24, 24, 24, 24]
    frame: [0, 1, 2, 3, 4, 5, 6, 7,
            8, 9, 10, 11, 12, 13, 14, 15,
            16, 17, 18, 19, 20, 21, 22, 23,
            24, 25, 26, 27, 28, 29, 30, 31]
}

// Bounced off a wall or another logo: a sharp tick, then a noise thump.
sfx Bump {
    channel: noise
    pitch: 9
    volume: [15, 14, 12, 9, 6, 4, 2, 1]
}

// Each logo's top-left corner inside the safe picture. Logo 0 starts
// near the middle, heading down and right. Logo 1 is placed by `launch`.
var pos_x: u8[2] = [72, 0]
var pos_y: u8[2] = [92, 0]
// 1 when the logo's own direction on that axis is right or down.
var right: u8[2] = [1, 1]
var down: u8[2] = [1, 1]

// Written by `read_input` once a frame, spent by `step_logo`.
var push: u8[2] = [0, 0]
// 1 once that player has pressed anything (player 2's START counts).
var used: u8[2] = [0, 0]

// Written by `next_color`, applied by `frame_top` in vblank.
var color: u8[2] = [FIRST_COLOR, 0]
var repaint: u8[2] = [1, 0]

// 1 once player 2 has launched a logo.
var two_logos: u8 = 0

// Flips every frame. The logos step on the frames where it is true.
var step_frame: bool = false

// PPUMASK, applied by `frame_top`. The black fill turns it off.
var mask: u8 = 0

fun vram_at(hi: u8, lo: u8) {
    var unused: u8 = peek(0x2002)
    poke(0x2006, hi)
    poke(0x2006, lo)
}

// Fill nametable 1 with the black tile. Rendering and NMI must be off.
fun fill_black() {
    vram_at(0x24, 0x00)
    var i: u16 = 0
    while i < 960 {
        poke(0x2007, BLACK_TILE)
        i += 1
    }
    var j: u8 = 0
    while j < 64 {
        poke(0x2007, 0)
        j += 1
    }
}

// Write logo 0's color into all four background sub-palettes. Vblank
// is short, with the sprite DMA in it, so the shades are read once and
// the 16 writes are unrolled.
fun paint_background() {
    var dark: u8 = SHADE_DARK[color[0]]
    var mid: u8 = SHADE_MID[color[0]]
    var full: u8 = SHADE_FULL[color[0]]
    vram_at(0x3F, 0x00)
    poke(0x2007, 0x0F)
    poke(0x2007, dark)
    poke(0x2007, mid)
    poke(0x2007, full)
    poke(0x2007, 0x0F)
    poke(0x2007, dark)
    poke(0x2007, mid)
    poke(0x2007, full)
    poke(0x2007, 0x0F)
    poke(0x2007, dark)
    poke(0x2007, mid)
    poke(0x2007, full)
    poke(0x2007, 0x0F)
    poke(0x2007, dark)
    poke(0x2007, mid)
    poke(0x2007, full)
}

// Write logo 1's color into sprite sub-palette 0.
fun paint_sprites() {
    var dark: u8 = SHADE_DARK[color[1]]
    var mid: u8 = SHADE_MID[color[1]]
    var full: u8 = SHADE_FULL[color[1]]
    vram_at(0x3F, 0x11)
    poke(0x2007, dark)
    poke(0x2007, mid)
    poke(0x2007, full)
}

// Apply the palettes, scroll, and PPU registers for this frame. Call
// first thing in the frame handler, while the PPU is still in vblank.
fun frame_top() {
    if repaint[0] == 1 {
        paint_background()
        repaint[0] = 0
    }
    if repaint[1] == 1 {
        paint_sprites()
        repaint[1] = 0
    }
    var unused: u8 = peek(0x2002)
    scroll(0 - (SAFE_LEFT + pos_x[0]), 240 - (SAFE_TOP + pos_y[0]))
    poke(0x2000, CTRL_SCROLL)
    poke(0x2001, mask)
}

// Pick a random color other than `current`.
fun random_other(current: u8) -> u8 {
    var skip: u8 = rand8() & 7
    while skip >= NUM_COLORS - 1 {
        skip = rand8() & 7
    }
    var next: u8 = current + 1 + skip
    if next >= NUM_COLORS {
        next -= NUM_COLORS
    }
    return next
}

fun next_color(n: u8) {
    color[n] = random_other(color[n])
    repaint[n] = 1
}

// Collect the d-pad presses each controller made this frame. Steps
// come every other frame, so a press is kept until a step spends it.
fun read_input() {
    if p1.button.up    { push[0] |= PUSH_UP }
    if p1.button.down  { push[0] |= PUSH_DOWN }
    if p1.button.left  { push[0] |= PUSH_LEFT }
    if p1.button.right { push[0] |= PUSH_RIGHT }
    if p1.button.up or p1.button.down or p1.button.left or p1.button.right {
        used[0] = 1
    }
    if p1.button.a or p1.button.b or p1.button.start or p1.button.select {
        used[0] = 1
    }
    if two_logos == 1 {
        if p2.button.up    { push[1] |= PUSH_UP }
        if p2.button.down  { push[1] |= PUSH_DOWN }
        if p2.button.left  { push[1] |= PUSH_LEFT }
        if p2.button.right { push[1] |= PUSH_RIGHT }
    }
}

// Launch player 2's logo.
fun launch() {
    two_logos = 1
    used[1] = 1
    pos_x[1] = LAUNCH_X
    right[1] = 1
    if pos_y[0] >= LAUNCH_CLEAR {
        pos_y[1] = LAUNCH_INSET
        down[1] = 1
    } else {
        pos_y[1] = RANGE_Y[1] - LAUNCH_INSET
        down[1] = 0
    }
    color[1] = random_other(color[0])
    repaint[1] = 1
    play Confirm
}

// 1 when the two logos' rectangles overlap.
fun logos_overlap() -> u8 {
    if pos_x[0] >= pos_x[1] + LOGO_W[1] { return 0 }
    if pos_x[1] >= pos_x[0] + LOGO_W[0] { return 0 }
    if pos_y[0] >= pos_y[1] + LOGO_H[1] { return 0 }
    if pos_y[1] >= pos_y[0] + LOGO_H[0] { return 0 }
    return 1
}

// Move logo `n` one pixel along x. The player's push against the
// logo's direction holds it still. Running into the other logo undoes
// the move and reverses both logos, unless the other one is already
// heading away. Touching a wall reverses the logo on the same step.
fun step_x(n: u8) -> u8 {
    var other: u8 = 1 - n
    var against: u8 = PUSH_LEFT
    if right[n] == 0 {
        against = PUSH_RIGHT
    }
    if (push[n] & against) != 0 {
        return HIT_NONE
    }
    var old: u8 = pos_x[n]
    if right[n] == 1 {
        pos_x[n] = old + 1
    } else {
        pos_x[n] = old - 1
    }
    if two_logos == 1 {
        if logos_overlap() == 1 {
            pos_x[n] = old
            right[n] = 1 - right[n]
            if pos_x[other] > old {
                right[other] = 1
            } else {
                right[other] = 0
            }
            return HIT_LOGO
        }
    }
    if right[n] == 1 {
        if pos_x[n] == RANGE_X[n] {
            right[n] = 0
            return HIT_WALL
        }
    } else {
        if pos_x[n] == 0 {
            right[n] = 1
            return HIT_WALL
        }
    }
    return HIT_NONE
}

fun step_y(n: u8) -> u8 {
    var other: u8 = 1 - n
    var against: u8 = PUSH_UP
    if down[n] == 0 {
        against = PUSH_DOWN
    }
    if (push[n] & against) != 0 {
        return HIT_NONE
    }
    var old: u8 = pos_y[n]
    if down[n] == 1 {
        pos_y[n] = old + 1
    } else {
        pos_y[n] = old - 1
    }
    if two_logos == 1 {
        if logos_overlap() == 1 {
            pos_y[n] = old
            down[n] = 1 - down[n]
            if pos_y[other] > old {
                down[other] = 1
            } else {
                down[other] = 0
            }
            return HIT_LOGO
        }
    }
    if down[n] == 1 {
        if pos_y[n] == RANGE_Y[n] {
            down[n] = 0
            return HIT_WALL
        }
    } else {
        if pos_y[n] == 0 {
            down[n] = 1
            return HIT_WALL
        }
    }
    return HIT_NONE
}

// Pixels between this axis and the wall it is heading for. A wall hit
// this step is 0. Bouncing off the other logo is not a wall approach.
fun wall_gap(hit: u8, pos: u8, range: u8, toward_high: u8) -> u8 {
    if hit == HIT_WALL {
        return 0
    }
    if hit != HIT_NONE {
        return 255
    }
    if toward_high == 1 {
        return range - pos
    }
    return pos
}

// Move logo `n` one pixel on each axis. A bounce changes the color
// once, even in a corner, where both axes bounce on one step.
fun step_logo(n: u8) {
    var hit_x: u8 = step_x(n)
    var hit_y: u8 = step_y(n)
    push[n] = 0
    // The coin follows a real wall hit that lands within
    // CORNER_FORGIVE of the other wall. Both gaps are 0 on an exact
    // corner. Nothing here reverses an axis, so the logo still travels
    // the last few pixels and bounces when it actually arrives.
    if used[n] == 1 {
        if hit_x == HIT_WALL or hit_y == HIT_WALL {
            var gap_x: u8 = wall_gap(hit_x, pos_x[n], RANGE_X[n], right[n])
            var gap_y: u8 = wall_gap(hit_y, pos_y[n], RANGE_Y[n], down[n])
            if gap_x <= CORNER_FORGIVE and gap_y <= CORNER_FORGIVE {
                play coin
            }
        }
    }
    if hit_x == HIT_LOGO or hit_y == HIT_LOGO {
        play Bump
    }
    if hit_x != HIT_NONE or hit_y != HIT_NONE {
        next_color(n)
    }
}

state Screensaver {
    on enter {
        poke(0x2001, 0)
        poke(0x2000, 0)
        fill_black()
        poke(0x2000, CTRL_SCROLL)
        mask = MASK_ON
        // `play` of a noise effect loads the length counter before it
        // enables the channel, and the APU ignores a load while the
        // channel is off, so the first bump would be silent. Enable
        // the channel now. With no length loaded it makes no sound.
        poke(0x4015, 0x0F)
        // The fill ran past at least one vblank with NMI off. Wait
        // for a fresh one so the first frame handler starts inside it
        // and turns rendering on before the frame begins.
        wait_frame
    }

    on frame {
        frame_top()
        read_input()
        if two_logos == 0 {
            if p2.button.start {
                launch()
            }
        }
        step_frame = not step_frame
        if step_frame {
            step_logo(0)
            if two_logos == 1 {
                step_logo(1)
            }
        }
        if two_logos == 1 {
            draw Logo2 at: (SAFE_LEFT + pos_x[1], SAFE_TOP + pos_y[1] - 1)
        }
    }
}

start Screensaver
