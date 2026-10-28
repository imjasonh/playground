// Keep: a ray-cast corridor on the NES.
//
// The window is 16 tile columns. Each column is one ray marched
// across a 16 by 16 cell map. Walls, a door, and the exit gate are
// tiles; guards and the gun are sprites. The nametable update ring
// cannot take a full window in one vblank, so a turn paints a few
// columns of rays and then a few rows of tiles, and the pad waits
// until that picture is done.
//
// The source is split across examples/keep/*.ne:
//
//     constants.ne   layout, tile numbers, the map
//     tables.ne      angle steps and wall heights
//     assets.ne      tiles, glyphs, guards, gun
//     backgrounds.ne the frame around the window
//     state.ne       globals
//     audio.ne       the gunshot
//     cast.ne        the march
//     actors.ne      walking, guards, shots
//     render.ne      rows and sprites
//     title_state.ne
//     play_state.ne
//     end_state.ne
//
// Controls:
//     Title    Start or A begins. With no input, the view starts
//              turning on its own so a still capture is a corridor.
//     Play     Up and down walk. Left and right turn. Hold B and
//              left or right steps sideways. A fires at the center
//              of the window. Guards in view shoot back. Walk into
//              the gate to leave.
//     End      Start or A returns to the title.
//
// Build:  cargo run --release -- build examples/keep.ne

game "Keep" {
    mapper: NROM
    mirroring: horizontal
}

palette Main {
    universal: black
    // Window: brown floor, orange mortar, tan brick. The ceiling
    // is the black backdrop.
    bg0: [brown, orange, tan]
    // Frame. The brick tile, read with these colours, is gray.
    bg1: [dk_gray, gray, lt_gray]
    bg2: [dk_blue, blue, sky_blue]
    bg3: [dk_green, green, lt_green]
    // Guards.
    sp0: [peach, dk_red, white]
    // Gun, glyphs, ammo.
    sp1: [dk_gray, lt_gray, white]
    // Hearts and the muzzle flash.
    sp2: [red, white, yellow]
    sp3: [dk_blue, blue, sky_blue]
}

include "keep/constants.ne"
include "keep/tables.ne"
include "keep/assets.ne"
include "keep/backgrounds.ne"
include "keep/state.ne"
include "keep/audio.ne"
include "keep/cast.ne"
include "keep/actors.ne"
include "keep/render.ne"
include "keep/title_state.ne"
include "keep/play_state.ne"
include "keep/end_state.ne"

start Title
