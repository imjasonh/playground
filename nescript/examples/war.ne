// War — a full NES port of the card game.
//
// This is a production-quality example: a title screen with a menu,
// an animated deal, cards that slide between two decks and a central
// play area with a running card count, a dedicated "WAR!" tie-break
// with buried cards, and a victory screen with a fanfare. Every
// piece of the game (logic, art, sound, states) is authored in
// NEScript itself — no external assets, no external tooling.
//
// The source is split across examples/war/*.ne files. This top-level
// file declares the hardware config, the reset-time palette and
// background, the one big Tileset sprite block that carries every
// custom CHR tile, the audio includes, the state includes, and the
// `start` declaration. Every include is processed by the parser's
// preprocess pass before lexing, so it's exactly as if the whole
// game lived in one .ne file.
//
// The file layout mirrors how a real NES game would be organised:
//
//     examples/war.ne              — this file, the top-level game
//     examples/war/PLAN.md         — living design doc
//     examples/war/constants.ne    — layout + gameplay constants
//     examples/war/audio.ne        — sfx + music declarations
//     examples/war/state.ne        — global variables
//     examples/war/rng.ne          — 8-bit LFSR PRNG
//     examples/war/deck.ne         — queue operations on the decks
//     examples/war/compare.ne      — card rank/suit extraction
//     examples/war/render.ne       — card + digit drawing helpers
//     examples/war/title_state.ne  — Title state + menu
//     examples/war/deal_state.ne   — Deal state + dealing animation
//     examples/war/play_state.ne   — Playing state + phase machine
//     examples/war/victory_state.ne — Victory state
//
// Controls (human players):
//     D-pad up/down  — move the title menu cursor
//     A / Start      — confirm a menu choice / draw the next card
//                      / return to the title from the victory screen
//
// In 0-player mode both players are CPU and the game plays itself;
// in 1-player mode you are player A and the CPU is player B; in
// 2-player mode both sides are human. The headless jsnes golden
// harness boots straight into 0-player mode (title auto-confirms
// after ~45 frames with no input) so the captured frame is always a
// scene from actual gameplay.
//
// Build:  cargo run --release -- build examples/war.ne
// Output: examples/war.nes

game "War" {
    mapper: NROM
    mirroring: horizontal
}

// ── Palette ─────────────────────────────────────────────────
//
// Grouped form with a shared `universal:` so the $3F10 mirror
// trap is handled automatically. The sprite sub-palette 0 is the
// one the NEScript codegen hardwires into the OAM attribute byte,
// so every sprite in the game renders through it. Four colours:
//
//     0 = transparent (universal — dk_green felt)
//     1 = red         (hearts, diamonds, accents)
//     2 = white       (card face, text)
//     3 = black       (outlines, spades, clubs)
//
// The three bg sub-palettes carry the felt, the cream banner, and
// a warm accent for the "WAR!" flash; bg3 stays reserved for
// future tweaks.
palette Main {
    universal: dk_green                    // green felt table colour

    bg0: [forest,    green,   mint]        // felt table base + subtle pattern
    bg1: [dk_red,    red,     white]       // cream / red banners
    bg2: [black,     lt_gray, white]       // card body on the nametable
    bg3: [dk_olive,  olive,   yellow]      // warm accent, "WAR!" flash

    sp0: [red,       white,   black]       // every sprite uses this
    sp1: [dk_red,    red,     peach]       // reserved
    sp2: [dk_blue,   blue,    sky_blue]    // reserved
    sp3: [dk_gray,   lt_gray, white]       // reserved
}

// Pull in everything else. Order matters only for symbol visibility:
// constants before the state variables that use them, state variables
// before helper functions, helper functions before state handlers.
include "war/constants.ne"
include "war/assets.ne"
include "war/background.ne"
include "war/audio.ne"
include "war/state.ne"
include "war/rng.ne"
include "war/deck.ne"
include "war/compare.ne"
include "war/render.ne"
include "war/title_state.ne"
include "war/deal_state.ne"
include "war/play_state.ne"
include "war/victory_state.ne"

start Title
