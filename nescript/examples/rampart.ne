// Rampart: a 1v1 turn-based mech duel for the NES.
//
// Two mechs face off on a 12x12 board. Each turn both players lock
// a plan in secret (up to three points of actions), then the plans
// resolve in a fixed order: Snap, Step, Shield, Standard, Rush,
// Aimed, Charge. Shots aim at a cell of the enemy's 6x6 body plate
// and scatter by two d6 rolls; a hit that beats the save roll
// strips armor, and a location at zero armor is critical. Six
// critical locations wreck a mech.
//
// A critical location stops working. The gun and the right arm lose
// the weapons mounted there, the shield can't go up, the head caps
// plans at two points, and each leg costs a square of movement.
// With both legs gone the mech can't move.
//
// The body plate is the mech's portrait. Damage shows as sprites on
// the hit part: scuffs, then holes, then fire on the last point of
// armor, then a crater, with the part's tiles swapped for charred
// copies once it's critical. A revealed plan lists its actions as
// icons under the plate. The message line spells each action.
//
// Secret plans work like a two-player sports game's play call: the
// lock screen lists every plan with a two-button code, and each
// player taps a code on their own controller with nothing echoed
// on screen, then presses START.
//
// The source is split across examples/rampart/*.ne:
//
//     text.ne          string tables and plan tables (generated)
//     constants.ne     tiles, layout, and rules tables
//     assets.ne        the Tileset sprite (generated)
//     backgrounds.ne   Title, Board, and Card nametables (generated)
//     state.ne         globals
//     render.ne        text queue, panel painting, sprites
//     rules.ne         dice, geometry, legality, damage
//     result.ne        winner and game-over message
//     cpu.ne           Easy, Medium, and Hard CPU players
//     title_state.ne      match setup menu
//     customize_state.ne  name and weapon picks
//     battle_state.ne     turn sequencer
//     audio.ne            move and weapon effects, and the march
//
// scripts/gen_rampart.py writes the generated files.
//
// Controls:
//     Title       up/down pick a row, left/right change it, START
//                 begins. Idle for about seven seconds, the title
//                 starts a CPU-against-CPU demo.
//     Setup       each human names a mech and picks a gun weapon
//                 and an arm weapon, either one any of the five. On
//                 the name row, left/right move the lit letter and
//                 up/down rotate it. On the gun and arm rows,
//                 left/right cycle that row's weapon and up/down
//                 move to the next row. B clears the name, START
//                 confirms. Player 1 goes first, then player 2. A
//                 CPU keeps its frame's weapons and is named BLUE
//                 or RED, matching that player's color.
//     Lock        tap the two-button code, then START. A legal
//                 plan chimes, and READY shows in that player's
//                 color. An illegal one buzzes. A CPU shows
//                 CPU READY in its color. The d-pad buttons are
//                 arrows. A and B stay letters.
//     Move        d-pad moves the cursor within range, A confirms,
//                 B returns the cursor to the mech.
//     Aim         d-pad picks a plate cell, A fires.
//     Messages    A skips the wait.
//
// Build:  cargo run --release -- build examples/rampart.ne

game "Rampart" {
    mapper: UxROM
    mirroring: horizontal
}

palette Main {
    universal: black
    bg0: [dk_gray, gray, white]
    // Glyphs use colour 3. bg3's colour 3 is peach, which is lighter
    // than the mech, so red text uses this palette instead.
    bg1: [dk_gray, red, red]
    // Colour 1 is the floor's. The board's last tile column shares
    // an attribute cell with the panel, so bg2 and bg3 keep it gray.
    bg2: [dk_gray, blue, sky_blue]
    bg3: [dk_gray, red, peach]
    // Board mechs: sp0 for player 1, sp1 for player 2. sp2 is for
    // dents, holes, and craters; sp3 for fire, cursors, and flashes.
    sp0: [dk_gray, blue, sky_blue]
    sp1: [dk_gray, red, peach]
    sp2: [black, dk_gray, orange]
    sp3: [red, orange, yellow]
}

include "rampart/text.ne"
include "rampart/constants.ne"
include "rampart/assets.ne"
include "rampart/backgrounds.ne"
include "rampart/state.ne"
include "rampart/audio.ne"
include "rampart/render.ne"
include "rampart/cpu.ne"
include "rampart/title_state.ne"
include "rampart/battle_state.ne"
include "rampart/customize_state.ne"

start Title
