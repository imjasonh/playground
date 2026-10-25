// SHA-256 Hasher — a full interactive SHA-256 implementation for the NES.
//
// The user types a short ASCII message on an on-screen keyboard, hits
// the ENTER key, and the NES computes the SHA-256 hash of the input
// and displays the 64-character hex digest at the bottom of the screen.
//
// The hashing core is implemented in pure NEScript with inline
// assembly for the 32-bit primitives (copy, XOR, add, rotate-right,
// shift-right) — the whole algorithm fits in about 400 lines of
// source and compresses one 64-byte block in ~15 frames. Since the
// keyboard restricts input to 16 ASCII characters, every message
// fits in a single block, so the final hash appears well under a
// second after the user presses ENTER.
//
// The source is split across examples/sha256/*.ne:
//
//     examples/sha256.ne                   — this file, top-level
//     examples/sha256/constants.ne         — tile indices + layout
//     examples/sha256/assets.ne            — the Tileset sprite
//     examples/sha256/background.ne        — keyboard nametable
//     examples/sha256/state.ne             — globals
//     examples/sha256/sha_core.ne          — SHA-256 primitives +
//                                            block compression
//     examples/sha256/render.ne            — helpers that drive the
//                                            OAM shadow buffer
//     examples/sha256/keyboard.ne          — keyboard dispatch table
//     examples/sha256/entering_state.ne    — Entering state (typing)
//     examples/sha256/computing_state.ne   — Computing state
//                                            (runs the block
//                                            compression across
//                                            frames)
//     examples/sha256/showing_state.ne     — Showing state (renders
//                                            the 64-hex-char digest)
//
// Controls:
//     D-pad         — move the cursor on the keyboard.
//     A             — type the key under the cursor. The keys
//                     labelled ← and ↵ are backspace and enter;
//                     pressing A on ↵ starts the compression.
//     B             — backspace (same as moving to ← + A).
//     SELECT        — clear the input buffer (from any state).
//
// Autopilot: if the user doesn't press a key for ~1 second after
// reset the program auto-types "NES" and presses enter, so the
// headless jsnes golden captures a completed hash rather than an
// empty keyboard. The SHA-256 of "NES" is
// AE9145DB5CABC41FE34B54E34AF8881F462362EA20FD8F861B26532FFBB84E0D —
// the exact string that should appear at the bottom of the golden.
//
// Build:  cargo run --release -- build examples/sha256.ne
// Output: examples/sha256.nes

game "SHA-256 Hasher" {
    mapper: NROM
    mirroring: horizontal
}

// ── Palette ──────────────────────────────────────────────────
//
// A "terminal" look: dark slate background, cyan for the keyboard
// and labels, amber for the input text the user is typing, and
// bright white for the hash digest. Three of the four bg sub-
// palettes are populated so the attribute table can colour-code
// the INPUT, KEYBOARD, and HASH sections of the screen.
palette Main {
    universal: dk_blue                     // deep slate background

    bg0: [dk_gray,    lt_gray, white]      // default / labels / keyboard
    bg1: [dk_olive,   olive,   yellow]     // INPUT section (amber)
    bg2: [dk_teal,    teal,    aqua]       // HASH section (cyan)
    bg3: [dk_gray,    dk_red,  red]        // reserved accents

    sp0: [dk_red,     yellow,  white]      // cursor + dynamic text
    sp1: [dk_olive,   olive,   yellow]     // reserved (input overlay)
    sp2: [dk_teal,    teal,    aqua]       // reserved (hash overlay)
    sp3: [dk_gray,    lt_gray, white]      // reserved
}

// Pull in everything else. Order matters for symbol visibility:
// constants → assets → background → state → sha core → render →
// keyboard dispatch → each state handler.
include "sha256/constants.ne"
include "sha256/assets.ne"
include "sha256/background.ne"
include "sha256/state.ne"
include "sha256/sha_core.ne"
include "sha256/render.ne"
include "sha256/keyboard.ne"
include "sha256/entering_state.ne"
include "sha256/computing_state.ne"
include "sha256/showing_state.ne"

start Entering
