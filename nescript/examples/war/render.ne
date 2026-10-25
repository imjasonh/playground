// war/render.ne — card, digit, and text rendering helpers.
//
// Every function in this file is a thin wrapper around one or
// more `draw Tileset at: (x, y) frame: N` calls that writes to
// the runtime OAM cursor. Each `draw` takes one sprite slot, so
// a 16×24 card face burns 6 sprite slots, a single-character
// letter burns 1, and so on. The caller is responsible for
// sprite budgeting — see PLAN.md §3.

// ── Card face ──────────────────────────────────────────────
//
// Draws the 6-sprite face of a 16×24 card at (x, y) for the
// packed `rank<<4 | suit` byte. Layout (each cell is 8×8):
//
//     [ rank ][ssuit]    row 0: rank letter + small suit pip
//     [pipTL ][pipTR]    row 1: top half of the big 16×16 pip
//     [pipBL ][pipBR]    row 2: bottom half of the big pip
//
// Every tile in the card has a fully-opaque white background
// (palette index 2) so the felt green behind the card does not
// bleed through — see `assets.ne` for the art itself.
fun draw_card_face(x: u8, y: u8, card: u8) {
    var rank: u8 = card_rank(card)
    var suit: u8 = card_suit(card)
    var rank_tile:  u8 = TILE_RANK_BASE + rank - 1
    var small_tile: u8 = TILE_SUIT_SMALL_BASE + suit
    var pip_tl:     u8 = TILE_PIP_TL_BASE + suit
    var pip_tr:     u8 = TILE_PIP_TR_BASE + suit
    var pip_bl:     u8 = TILE_PIP_BL_BASE + suit
    var pip_br:     u8 = TILE_PIP_BR_BASE + suit
    // Row 0 — rank corner + small suit
    draw Tileset at: (x,     y)      frame: rank_tile
    draw Tileset at: (x + 8, y)      frame: small_tile
    // Row 1 — top half of the 16×16 big pip
    draw Tileset at: (x,     y + 8)  frame: pip_tl
    draw Tileset at: (x + 8, y + 8)  frame: pip_tr
    // Row 2 — bottom half of the 16×16 big pip
    draw Tileset at: (x,     y + 16) frame: pip_bl
    draw Tileset at: (x + 8, y + 16) frame: pip_br
}

// Draw the card-back checkerboard at (x, y). 6 sprites. The
// back tiles tile seamlessly so every cell of the 16×24 card
// body carries a 2-pixel square of the same black/white grid.
fun draw_card_back(x: u8, y: u8) {
    draw Tileset at: (x,     y)      frame: TILE_BACK_TL
    draw Tileset at: (x + 8, y)      frame: TILE_BACK_TR
    draw Tileset at: (x,     y + 8)  frame: TILE_BACK_BL
    draw Tileset at: (x + 8, y + 8)  frame: TILE_BACK_BR
    draw Tileset at: (x,     y + 16) frame: TILE_BACK_TL
    draw Tileset at: (x + 8, y + 16) frame: TILE_BACK_TR
}

// Dispatch between front and back based on the fly_face_up flag
// stamped by the phase handlers.
fun draw_flying_card(x: u8, y: u8) {
    if fly_face_up == 0 {
        draw_card_back(x, y)
    } else {
        draw_card_face(x, y, fly_card)
    }
}

// ── Digits + text ─────────────────────────────────────────

// Draw a single decimal digit 0..9 at (x, y).
fun draw_digit(x: u8, y: u8, d: u8) {
    draw Tileset at: (x, y) frame: TILE_DIGIT_BASE + d
}

// Draw a two-digit decimal count (0..99) at (x, y). Leading
// zero is preserved so the HUD always renders two glyphs wide,
// which keeps the layout stable as the counts change.
fun draw_count(x: u8, y: u8, v: u8) {
    var tens: u8 = 0
    var n: u8 = v
    // Divide by 10 without the software divide: repeatedly
    // subtract 10 until n < 10. For v ≤ 52 this loops at most
    // 5 times, cheaper than calling `/` and `%`.
    while n >= 10 {
        n -= 10
        tens += 1
    }
    draw_digit(x,     y, tens)
    draw_digit(x + 8, y, n)
}

// Draw a single letter 'A'..'Z' using the sprite font. `ch` is
// the letter index (0 = A, 25 = Z).
fun draw_letter(x: u8, y: u8, ch: u8) {
    draw Tileset at: (x, y) frame: TILE_LETTER_BASE + ch
}

// Short helper for drawing the word "PLAYER" at (x, y). 6 letters.
// Used by the HUD and the victory banner.
fun draw_word_player(x: u8, y: u8) {
    draw_letter(x,      y, 15)  // P
    draw_letter(x + 8,  y, 11)  // L
    draw_letter(x + 16, y, 0)   // A
    draw_letter(x + 24, y, 24)  // Y
    draw_letter(x + 32, y, 4)   // E
    draw_letter(x + 40, y, 17)  // R
}

// "WINS" — used on the victory screen.
fun draw_word_wins(x: u8, y: u8) {
    draw_letter(x,      y, 22)  // W
    draw_letter(x + 8,  y, 8)   // I
    draw_letter(x + 16, y, 13)  // N
    draw_letter(x + 24, y, 18)  // S
}

// "PRESS" — used on the title screen.
fun draw_word_press(x: u8, y: u8) {
    draw_letter(x,      y, 15)  // P
    draw_letter(x + 8,  y, 17)  // R
    draw_letter(x + 16, y, 4)   // E
    draw_letter(x + 24, y, 18)  // S
    draw_letter(x + 32, y, 18)  // S
}

// ── Fly animation driver ──────────────────────────────────
//
// Avoiding a software multiply: instead of computing
// `start + dx * t / FRAMES` we step the fly position by a
// fixed constant each frame. FLY_STEP is chosen so that
// FRAMES_FLY * FLY_STEP equals the deck-to-play distance on
// both axes:
//
//     FRAMES_FLY * FLY_STEP = 64 px   (16 * 4)
//
// The screen layout (DECK_*_X, PLAY_*_X, DECK_Y, PLAY_Y) is
// arranged so every animation traverses exactly 64 px on both
// axes, which keeps the per-frame step uniform.
const FLY_STEP: u8 = 4

// Step the global (fly_x, fly_y) by FLY_STEP in the directions
// stored in fly_dx_sign / fly_dy_sign. Sign 0 = positive (move
// right / down), 1 = negative (move left / up). Called once
// per frame inside the relevant fly-phase handler.
fun step_fly_pos() {
    if fly_dx_sign == 0 {
        fly_x += FLY_STEP
    } else {
        fly_x -= FLY_STEP
    }
    if fly_dy_sign == 0 {
        fly_y += FLY_STEP
    } else {
        fly_y -= FLY_STEP
    }
}

// Initialise the fly state for a card slide from (sx, sy) using
// the given direction signs, card byte, and face-up flag. The
// caller is responsible for picking signs so the end position
// lands where it should after FRAMES_FLY frames.
fun arm_fly(sx: u8, sy: u8, dxsign: u8, dysign: u8) {
    fly_x = sx
    fly_y = sy
    fly_dx_sign = dxsign
    fly_dy_sign = dysign
}
