// pong/render.ne — drawing helpers.
//
// Everything on-screen that isn't a static background tile goes
// through one of these functions. The idea is the same as war:
// the phase handlers stay readable and the sprite-budgeting math
// all lives in one file.

// ── Letters and digits ───────────────────────────────────

// Draw a single 'A'..'Z' glyph at (x, y). `ch` is the letter
// index (0 = A, 25 = Z).
fun draw_letter(x: u8, y: u8, ch: u8) {
    draw Tileset at: (x, y) frame: TILE_LETTER_BASE + ch
}

// Draw a single digit 0..9 at (x, y).
fun draw_digit(x: u8, y: u8, d: u8) {
    draw Tileset at: (x, y) frame: TILE_DIGIT_BASE + d
}

// Two-digit score display (0..99) at (x, y). Leading zero is
// preserved so the HUD never shifts as the score ticks up.
fun draw_count(x: u8, y: u8, v: u8) {
    var tens: u8 = 0
    var n: u8 = v
    while n >= 10 {
        n -= 10
        tens += 1
    }
    draw_digit(x,     y, tens)
    draw_digit(x + 8, y, n)
}

// ── Words ────────────────────────────────────────────────

// "PRESS" — used on the title's blinking prompt.
fun draw_word_press(x: u8, y: u8) {
    draw_letter(x,      y, 15)  // P
    draw_letter(x + 8,  y, 17)  // R
    draw_letter(x + 16, y, 4)   // E
    draw_letter(x + 24, y, 18)  // S
    draw_letter(x + 32, y, 18)  // S
}

// "PONG" — used on the title screen and the victory banner until
// we wire up the BIG PONG banner in the polish milestone.
fun draw_word_pong(x: u8, y: u8) {
    draw_letter(x,      y, 15)  // P
    draw_letter(x + 8,  y, 14)  // O
    draw_letter(x + 16, y, 13)  // N
    draw_letter(x + 24, y, 6)   // G
}

// "CPU" — used on the title menu options.
fun draw_word_cpu(x: u8, y: u8) {
    draw_letter(x,      y, 2)   // C
    draw_letter(x + 8,  y, 15)  // P
    draw_letter(x + 16, y, 20)  // U
}

// "VS" — used in the CPU-vs-CPU title line.
fun draw_word_vs(x: u8, y: u8) {
    draw_letter(x,     y, 21)   // V
    draw_letter(x + 8, y, 18)   // S
}

// "PLAYER" — used on the title menu and the victory banner.
fun draw_word_player(x: u8, y: u8) {
    draw_letter(x,      y, 15)  // P
    draw_letter(x + 8,  y, 11)  // L
    draw_letter(x + 16, y, 0)   // A
    draw_letter(x + 24, y, 24)  // Y
    draw_letter(x + 32, y, 4)   // E
    draw_letter(x + 40, y, 17)  // R
}

// "WINS" — used on the victory banner.
fun draw_word_wins(x: u8, y: u8) {
    draw_letter(x,      y, 22)  // W
    draw_letter(x + 8,  y, 8)   // I
    draw_letter(x + 16, y, 13)  // N
    draw_letter(x + 24, y, 18)  // S
}

// ── Center-line divider ──────────────────────────────────
//
// Classic dashed Pong divider at x = 124. We draw 7 dashes at
// y = 24, 56, 88, 120, 152, 184, 216 (every 32 px), which is
// always one sprite per scanline — safely under the per-scanline
// budget.
fun draw_center_line() {
    draw Tileset at: (124, 24)  frame: TILE_CENTER_DASH
    draw Tileset at: (124, 56)  frame: TILE_CENTER_DASH
    draw Tileset at: (124, 88)  frame: TILE_CENTER_DASH
    draw Tileset at: (124, 120) frame: TILE_CENTER_DASH
    draw Tileset at: (124, 152) frame: TILE_CENTER_DASH
    draw Tileset at: (124, 184) frame: TILE_CENTER_DASH
    draw Tileset at: (124, 216) frame: TILE_CENTER_DASH
}

// ── HUD scores ───────────────────────────────────────────
fun draw_scores() {
    draw_count(SCORE_LEFT_X,  SCORE_Y, score[0])
    draw_count(SCORE_RIGHT_X, SCORE_Y, score[1])
}

// ── Paddles ──────────────────────────────────────────────
//
// Draw the paddle on the given side at its current y. Side 0 =
// left (x = LEFT_PADDLE_X), side 1 = right (x = RIGHT_PADDLE_X).
// Normal paddles are 3 tiles tall (top, mid, bot). Long paddles
// are 5 tiles tall (top, mid, mid, mid, bot). The height choice
// is driven by `paddle_long[side]` — nonzero = extended.
fun draw_paddle(side: u8) {
    var px: u8 = LEFT_PADDLE_X
    if side == SIDE_RIGHT {
        px = RIGHT_PADDLE_X
    }
    var py: u8 = paddle_y[side]
    draw Tileset at: (px, py)      frame: TILE_PADDLE_TOP
    if paddle_long[side] > 0 {
        // 5-tile long paddle (40 px).
        draw Tileset at: (px, py + 8)  frame: TILE_PADDLE_MID
        draw Tileset at: (px, py + 16) frame: TILE_PADDLE_MID
        draw Tileset at: (px, py + 24) frame: TILE_PADDLE_MID
        draw Tileset at: (px, py + 32) frame: TILE_PADDLE_BOT
    } else {
        // 3-tile normal paddle (24 px).
        draw Tileset at: (px, py + 8)  frame: TILE_PADDLE_MID
        draw Tileset at: (px, py + 16) frame: TILE_PADDLE_BOT
    }
}

// Draw both paddles in one call. Used by every gameplay phase.
fun draw_paddles() {
    draw_paddle(SIDE_LEFT)
    draw_paddle(SIDE_RIGHT)
}

// ── Balls ────────────────────────────────────────────────
//
// Draw every active ball in the ball_* arrays. Inactive slots
// are skipped.
fun draw_balls() {
    var i: u8 = 0
    while i < MAX_BALLS {
        if ball_active[i] == 1 {
            draw Tileset at: (ball_x[i], ball_y[i]) frame: TILE_BALL
        }
        i += 1
    }
}

// ── Powerup ──────────────────────────────────────────────
//
// Draw the on-screen powerup iff one is active. Tile index picks
// up the right icon via TILE_POWERUP_BASE + (kind - 1).
fun draw_powerup() {
    if powerup_kind != PWR_NONE {
        draw Tileset at: (powerup_x, powerup_y) frame: (TILE_POWERUP_BASE - 1) + powerup_kind
    }
}
