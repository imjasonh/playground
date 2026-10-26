// pong/ball.ne — multi-ball physics.
//
// Balls live in parallel arrays indexed by slot (ball_x[i], etc.)
// so swapping between single-ball M3 and multi-ball M4 is purely a
// matter of which slots are active — the physics code is the
// same. Velocity is stored as (magnitude, sign) per axis because
// NEScript's u8 arithmetic can't express negatives directly; sign
// 0 = positive (+x right / +y down), sign 1 = negative.
//
// Update order inside update_ball:
//   1. Move the ball by its velocity
//   2. Bounce off top / bottom walls
//   3. Test paddle collisions (left + right)
//   4. Test score-out on left / right exits
//
// The `i` parameter is the ball slot, 0..MAX_BALLS-1.

// ── Serve ────────────────────────────────────────────────
//
// Reset ball slot 0 to the centre of the playfield with a fresh
// random velocity, aimed toward the `target_side` that just lost
// a point (so the serve is into the loser's side, classic Pong).
// Every other ball slot is cleared. Called on game start and
// after every scored point.
fun serve_ball(target_side: u8) {
    // Wipe every slot first so M4's multi-ball leftovers never
    // carry through a score.
    var i: u8 = 0
    while i < MAX_BALLS {
        ball_active[i] = 0
        i += 1
    }

    // Centre the primary ball.
    ball_x[0] = 124
    ball_y[0] = 112
    ball_dx[0] = BALL_BASE_DX
    ball_dy[0] = BALL_BASE_DY

    // Horizontal direction is toward target_side. SIDE_LEFT = 0
    // means the ball travels left toward the left paddle, so x
    // sign = 1 (negative). Right paddle = sign 0.
    if target_side == SIDE_LEFT {
        ball_dx_sign[0] = 1
    } else {
        ball_dx_sign[0] = 0
    }

    // Vertical direction picked by a random bit to avoid the
    // same rally pattern every serve. RNG LSB = 0 → +y, 1 → -y.
    var r: u8 = rng_next()
    ball_dy_sign[0] = r & 1

    ball_active[0] = 1
}

// ── Score handling ───────────────────────────────────────
//
// Called when a ball exits the playfield past a paddle. The
// scoring side gets +1. With multi-ball, the round continues
// until ALL active balls are out. Only when the last ball exits
// does the phase machine drop into P_POINT for the serve pause.
fun on_score(scoring_side: u8) {
    score[scoring_side] += 1
    play Score

    // Count remaining active balls (the exiting ball has already
    // been marked inactive before this call).
    var remaining: u8 = 0
    var j: u8 = 0
    while j < MAX_BALLS {
        if ball_active[j] == 1 {
            remaining += 1
        }
        j += 1
    }
    if remaining == 0 {
        // Last ball out — enter the P_POINT pause. The
        // serving_side records the scorer; P_POINT flips it so
        // the serve aims at the loser.
        serving_side = scoring_side
        phase = P_POINT
        phase_timer = 0
        // Clear the powerup so it doesn't linger during the
        // inter-round pause.
        powerup_kind = PWR_NONE
        powerup_cooldown = 0
    }
}

// ── Multi-ball spawn on paddle hit ───────────────────────
//
// When paddle_multi[side] is set, a paddle hit spawns two extra
// balls at the hit point with mirrored y velocities. This
// function is called from within check_paddle_hit's hit branch.
// Returns immediately if no multi flag is set. The flag clears
// on use.
fun spawn_multi_balls(i: u8, side: u8) {
    if paddle_multi[side] == 0 {
        return
    }
    paddle_multi[side] = 0

    // Find two free slots.
    var slot1: u8 = 0
    var slot2: u8 = 0
    var found1: u8 = 0
    var found2: u8 = 0
    var k: u8 = 0
    while k < MAX_BALLS {
        if ball_active[k] == 0 {
            if found1 == 0 {
                slot1 = k
                found1 = 1
            } else {
                if found2 == 0 {
                    slot2 = k
                    found2 = 1
                }
            }
        }
        k += 1
    }

    // Spawn each extra ball as a copy of the hit ball with a
    // mirrored or offset y direction.
    if found1 == 1 {
        ball_active[slot1]  = 1
        ball_x[slot1]       = ball_x[i]
        ball_y[slot1]       = ball_y[i]
        ball_dx[slot1]      = ball_dx[i]
        ball_dy[slot1]      = ball_dy[i]
        ball_dx_sign[slot1] = ball_dx_sign[i]
        // Mirror y sign from the source ball.
        if ball_dy_sign[i] == 0 {
            ball_dy_sign[slot1] = 1
        } else {
            ball_dy_sign[slot1] = 0
        }
    }
    if found2 == 1 {
        ball_active[slot2]  = 1
        ball_x[slot2]       = ball_x[i]
        ball_y[slot2]       = ball_y[i]
        ball_dx[slot2]      = ball_dx[i]
        ball_dy[slot2]      = ball_dy[i]
        ball_dx_sign[slot2] = ball_dx_sign[i]
        // Same y direction as the source (so we have 3 distinct
        // trajectories: original, mirrored, and parallel).
        ball_dy_sign[slot2] = ball_dy_sign[i]
        // Offset the y slightly to avoid all three landing on
        // the same pixel.
        if ball_y[slot2] + 6 < PLAYFIELD_BOTTOM {
            ball_y[slot2] += 6
        }
    }
}

// ── Paddle collision ─────────────────────────────────────
//
// Classic AABB overlap test against the paddle on `side`. On a
// hit we flip the ball's x velocity sign, push the ball out of
// the paddle to avoid double-bounces, and play the hit sfx.
//
// Powerup effects consumed on hit:
//   - LONG:  paddle_long already decrements
//   - FAST:  paddle_fast → doubles ball_dx for the rest of this ball's life
//   - MULTI: paddle_multi → spawns 2 extra balls at the hit point
fun check_paddle_hit(i: u8, side: u8) {
    var px: u8 = LEFT_PADDLE_X
    if side == SIDE_RIGHT {
        px = RIGHT_PADDLE_X
    }
    var py: u8 = paddle_y[side]
    var ph: u8 = PADDLE_H
    if paddle_long[side] > 0 {
        ph = PADDLE_H_LONG
    }

    var bx: u8 = ball_x[i]
    var by: u8 = ball_y[i]

    // Four-way AABB overlap test. The operands are small u8
    // values so the additions can't overflow past 255.
    if bx + BALL_SIZE > px and bx < px + PADDLE_W and by + BALL_SIZE > py and by < py + ph {
        if side == SIDE_LEFT {
            ball_x[i] = px + PADDLE_W
            ball_dx_sign[i] = 0
        } else {
            ball_x[i] = px - BALL_SIZE
            ball_dx_sign[i] = 1
        }

        // ── Consume long-paddle hit ──────────────────
        if paddle_long[side] > 0 {
            paddle_long[side] -= 1
        }
        // ── Consume fast-ball flag ───────────────────
        if paddle_fast[side] > 0 {
            paddle_fast[side] = 0
            ball_dx[i] = BALL_FAST_DX
        }
        // ── Consume multi-ball flag ──────────────────
        spawn_multi_balls(i, side)

        play PaddleHit
    }
}

// ── Per-ball update ──────────────────────────────────────
fun update_ball(i: u8) {
    if ball_active[i] == 0 {
        return
    }

    // ── 1. Move ──────────────────────────────────────
    if ball_dx_sign[i] == 0 {
        ball_x[i] += ball_dx[i]
    } else {
        ball_x[i] -= ball_dx[i]
    }
    if ball_dy_sign[i] == 0 {
        ball_y[i] += ball_dy[i]
    } else {
        ball_y[i] -= ball_dy[i]
    }

    // ── 2. Wall bounce ───────────────────────────────
    //
    // Top: ball moving up and the top edge is now above the
    // playfield (u8 comparison, safe because PLAYFIELD_TOP = 16
    // and ball speeds are 1-2 so ball_y can't wrap around).
    if ball_dy_sign[i] == 1 {
        if ball_y[i] < PLAYFIELD_TOP {
            ball_y[i] = PLAYFIELD_TOP
            ball_dy_sign[i] = 0
            play WallBounce
        }
    }
    // Bottom: ball moving down and the bottom edge has crossed
    // PLAYFIELD_BOTTOM.
    if ball_dy_sign[i] == 0 {
        if ball_y[i] + BALL_SIZE > PLAYFIELD_BOTTOM {
            ball_y[i] = PLAYFIELD_BOTTOM - BALL_SIZE
            ball_dy_sign[i] = 1
            play WallBounce
        }
    }

    // ── 3. Paddle collision ──────────────────────────
    //
    // Only check the paddle the ball is travelling toward.
    // This is both faster and avoids the edge case of the
    // ball hitting a paddle moving away from it.
    if ball_dx_sign[i] == 1 {
        check_paddle_hit(i, SIDE_LEFT)
    } else {
        check_paddle_hit(i, SIDE_RIGHT)
    }

    // ── 4. Score-out ─────────────────────────────────
    //
    // "ball_x < 8" / "ball_x > 240" is safe because paddles
    // live at x = 16 and x = 232 — a ball that has moved past
    // the paddle edge with max speed 2 lands at ball_x ∈ [6, 14]
    // or [234, 242] before the next frame, never close enough
    // to 0 or 255 to wrap the u8.
    if ball_dx_sign[i] == 1 {
        if ball_x[i] < 8 {
            ball_active[i] = 0
            on_score(SIDE_RIGHT)
        }
    } else {
        if ball_x[i] > 240 {
            ball_active[i] = 0
            on_score(SIDE_LEFT)
        }
    }
}

// ── Sweep every active ball ──────────────────────────────
fun step_balls() {
    var i: u8 = 0
    while i < MAX_BALLS {
        update_ball(i)
        i += 1
    }
}
