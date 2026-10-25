// Pong — a full NES port of the classic two-paddle game.
//
// Production-quality example: a title screen with a three-option
// menu (CPU VS CPU / 1 PLAYER / 2 PLAYERS), live gameplay with
// smooth ball physics and two paddles, powerups that bounce
// around the playfield and modify gameplay when caught
// (long paddle / fast ball / multi-ball), a victory screen with
// a fanfare, and a brisk title march. Every piece of the game
// (logic, art, sound, states) is authored in NEScript itself —
// no external assets, no external tooling.
//
// The source is split across examples/pong/*.ne files. This
// top-level file declares the hardware config, the reset-time
// palette and Tileset, the audio/state/logic includes, and the
// `start` declaration. Every include is processed by the parser
// before lexing, so it's exactly as if the whole game lived in
// one .ne file.
//
// The file layout mirrors how a real NES game would be organised:
//
//     examples/pong.ne               — this file, the top-level game
//     examples/pong/PLAN.md          — living implementation plan
//     examples/pong/constants.ne     — layout + gameplay constants
//     examples/pong/assets.ne        — Tileset sprite block
//     examples/pong/audio.ne         — sfx + music
//     examples/pong/state.ne         — global variables
//     examples/pong/rng.ne           — 8-bit Galois LFSR PRNG
//     examples/pong/render.ne        — draw helpers
//     examples/pong/input.ne         — paddle update (M2+)
//     examples/pong/ball.ne          — ball physics (M3+)
//     examples/pong/powerup.ne       — powerup entity (M8+)
//     examples/pong/title_state.ne   — state Title + menu
//     examples/pong/play_state.ne    — state Playing (inner SERVE/PLAY/POINT phase machine)
//     examples/pong/victory_state.ne — state Victory
//
// Controls (humans):
//     D-pad up/down  — move your paddle up/down
//     A / Start      — confirm a menu choice
//                      / return to title from the victory screen
//
// In CPU-vs-CPU mode both paddles are CPU and the game plays
// itself; in 1 PLAYER mode you are the left paddle and the CPU is
// the right; in 2 PLAYERS mode both sides are human (P1 left,
// P2 right). The headless jsnes golden harness boots straight
// into CPU VS CPU (title auto-commits after ~45 frames with no
// input) so the captured frame is always a scene from actual
// gameplay.
//
// Build:  cargo run --release -- build examples/pong.ne
// Output: examples/pong.nes

game "Pong" {
    mapper: NROM
    mirroring: horizontal
}

// ── Palette ─────────────────────────────────────────────────
//
// Classic Pong is a black field with white paddles and white
// ball. We add a yellow accent for powerup icons and the menu
// cursor so those read as distinct without growing the sprite
// sub-palette budget (sprites all share sp0 in NEScript's
// codegen).
//
// Sprite sub-palette 0 vocabulary:
//     0 = transparent
//     1 = white     (paddles, ball, letters, digits)
//     2 = lt_gray   (reserved for subtle secondary accents)
//     3 = yellow    (cursor, powerup icons)
palette Main {
    universal: black

    bg0: [dk_gray, lt_gray, white]      // center line + score gutters
    bg1: [dk_blue, blue,    sky_blue]   // reserved — P1 side accent
    bg2: [dk_red,  red,     peach]      // reserved — P2 side accent
    bg3: [dk_olive,olive,   yellow]     // reserved — powerup flash

    sp0: [white,   lt_gray, yellow]     // every sprite uses this
    sp1: [dk_blue, blue,    sky_blue]   // reserved
    sp2: [dk_red,  red,     peach]      // reserved
    sp3: [dk_gray, lt_gray, white]      // reserved
}

// Pull in everything else. Order matters only for symbol visibility:
// constants before the state variables that use them, state variables
// and helpers before state handlers.
include "pong/constants.ne"
include "pong/assets.ne"
include "pong/audio.ne"
include "pong/state.ne"
include "pong/rng.ne"
include "pong/render.ne"
include "pong/input.ne"
include "pong/ball.ne"
include "pong/powerup.ne"
include "pong/title_state.ne"
include "pong/play_state.ne"
include "pong/victory_state.ne"

start Title
