// pong/input.ne — paddle update (human + CPU).
//
// `step_paddles()` is called every frame by the Playing state
// phase machine. Humans move their paddle up/down based on the
// D-pad on their controller; CPU paddles (is_cpu[side] == 1)
// are driven by `step_cpu_paddle(side)` which tracks the nearest
// active ball's y position with a one-frame lag and a small miss
// zone so the AI feels beatable.
//
// Clamping: paddles can never leave the playfield vertically.
// `move_paddle_up` / `move_paddle_down` handle the clamp so the
// caller just has to ask for motion in one direction at a time.

// Move a paddle upward by PADDLE_SPEED, clamped to PLAYFIELD_TOP.
fun move_paddle_up(side: u8) {
    if paddle_y[side] >= PLAYFIELD_TOP + PADDLE_SPEED {
        paddle_y[side] -= PADDLE_SPEED
    } else {
        paddle_y[side] = PLAYFIELD_TOP
    }
}

// Move a paddle downward by PADDLE_SPEED, clamped to
// (PLAYFIELD_BOTTOM - paddle_height). The paddle height depends
// on whether this side is currently in long-paddle mode.
fun move_paddle_down(side: u8) {
    var h: u8 = PADDLE_H
    if paddle_long[side] > 0 {
        h = PADDLE_H_LONG
    }
    var max_y: u8 = PLAYFIELD_BOTTOM - h
    if paddle_y[side] + PADDLE_SPEED <= max_y {
        paddle_y[side] += PADDLE_SPEED
    } else {
        paddle_y[side] = max_y
    }
}

// ── CPU AI ────────────────────────────────────────────────
//
// The CPU tracks the y-centre of the nearest active ball that
// is heading toward its side. It moves CPU_SPEED px per frame
// toward the ball's y, but only if the ball is more than 4 px
// away from the paddle centre (the "dead zone" that makes the
// AI imperfect and lets fast balls score occasionally).
//
// If no ball is heading toward this side, the CPU drifts toward
// the playfield center so it isn't caught flat-footed on the
// next serve.
fun step_cpu_paddle(side: u8) {
    // Find the nearest ball heading toward this side.
    var target_y: u8 = 112   // default: field centre
    var found: u8 = 0
    var j: u8 = 0
    while j < MAX_BALLS {
        if ball_active[j] == 1 {
            // Ball heading left → of interest to the left paddle
            // Ball heading right → of interest to the right paddle
            if side == SIDE_LEFT and ball_dx_sign[j] == 1 {
                target_y = ball_y[j] + (BALL_SIZE >> 1)
                found = 1
            }
            if side == SIDE_RIGHT and ball_dx_sign[j] == 0 {
                target_y = ball_y[j] + (BALL_SIZE >> 1)
                found = 1
            }
        }
        j += 1
    }

    // Aim the paddle centre at target_y.
    var ph: u8 = PADDLE_H
    if paddle_long[side] > 0 {
        ph = PADDLE_H_LONG
    }
    var centre: u8 = paddle_y[side] + (ph >> 1)

    // Dead zone: don't jitter if we're already close.
    if centre + 4 < target_y {
        // Need to move down.
        if paddle_y[side] + CPU_SPEED + ph <= PLAYFIELD_BOTTOM {
            paddle_y[side] += CPU_SPEED
        }
    }
    if centre > target_y + 4 {
        // Need to move up.
        if paddle_y[side] >= PLAYFIELD_TOP + CPU_SPEED {
            paddle_y[side] -= CPU_SPEED
        }
    }
}

// Drive both paddles from controller input (humans) or the CPU
// AI (bots) this frame. The per-player button reads are hand-
// rolled because `p1` / `p2` are compile-time syntactic prefixes.
fun step_paddles() {
    if is_cpu[SIDE_LEFT] == 0 {
        if button.up {
            move_paddle_up(SIDE_LEFT)
        }
        if button.down {
            move_paddle_down(SIDE_LEFT)
        }
    } else {
        step_cpu_paddle(SIDE_LEFT)
    }
    if is_cpu[SIDE_RIGHT] == 0 {
        if p2.button.up {
            move_paddle_up(SIDE_RIGHT)
        }
        if p2.button.down {
            move_paddle_down(SIDE_RIGHT)
        }
    } else {
        step_cpu_paddle(SIDE_RIGHT)
    }
}
