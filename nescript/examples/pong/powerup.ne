// pong/powerup.ne — powerup entity spawn, bounce, catch, apply.
//
// One powerup is active at a time. When powerup_kind != PWR_NONE
// the entity is visible and bouncing around the playfield. Either
// paddle can catch it by overlapping its AABB. On catch, the
// catcher receives the effect (LONG / FAST / MULTI) and the
// powerup despawns. An uncaught powerup despawns automatically
// after POWERUP_LIFE_FRAMES. A new powerup spawns every
// POWERUP_SPAWN_FRAMES while no powerup is on-screen.

// ── Spawn ────────────────────────────────────────────────
//
// Place a new powerup at the playfield centre with a random
// kind (1..3) and random initial diagonal direction.
fun spawn_powerup() {
    var r: u8 = rng_next()
    // kind = 1, 2, or 3. We take `(r % 3) + 1` but the compiler
    // warns on non-power-of-two modulo so we do it manually:
    // (r & 3) gives 0..3; if 0, remap to 3.
    var k: u8 = r & 3
    if k == 0 {
        k = 3
    }
    powerup_kind = k
    powerup_x = 120
    powerup_y = 112

    var r2: u8 = rng_next()
    powerup_dx_sign = r2 & 1
    powerup_dy_sign = (r2 >> 1) & 1

    powerup_timer = 0
    play PowerSpawn
}

// ── Apply ────────────────────────────────────────────────
//
// Set the appropriate pending flag on the catching side's
// paddle. Called from the catch handler below.
fun apply_powerup(side: u8, kind: u8) {
    if kind == PWR_LONG {
        paddle_long[side] = LONG_PADDLE_HITS
    }
    if kind == PWR_FAST {
        paddle_fast[side] = 1
    }
    if kind == PWR_MULTI {
        paddle_multi[side] = 1
    }
    play PowerCatch
}

// ── Catch check ──────────────────────────────────────────
//
// AABB test of the powerup against a single paddle. Returns 1
// if the powerup was caught (and consumed), 0 otherwise.
fun check_powerup_vs_paddle(side: u8) -> u8 {
    var px: u8 = LEFT_PADDLE_X
    if side == SIDE_RIGHT {
        px = RIGHT_PADDLE_X
    }
    var py: u8 = paddle_y[side]
    var ph: u8 = PADDLE_H
    if paddle_long[side] > 0 {
        ph = PADDLE_H_LONG
    }
    if powerup_x + POWERUP_SIZE > px and powerup_x < px + PADDLE_W and powerup_y + POWERUP_SIZE > py and powerup_y < py + ph {
        apply_powerup(side, powerup_kind)
        powerup_kind = PWR_NONE
        return 1
    }
    return 0
}

// ── Step ─────────────────────────────────────────────────
//
// Called every frame during P_PLAY from the play state's main
// loop. Handles spawn cooldown, movement, wall bouncing, paddle
// catch checks, and lifetime despawn.
fun step_powerup() {
    if powerup_kind == PWR_NONE {
        // No powerup on screen — tick the spawn cooldown.
        powerup_cooldown += 1
        if powerup_cooldown >= POWERUP_SPAWN_FRAMES {
            powerup_cooldown = 0
            spawn_powerup()
        }
        return
    }

    // ── Lifetime check ───────────────────────────────
    powerup_timer += 1
    if powerup_timer >= POWERUP_LIFE_FRAMES {
        powerup_kind = PWR_NONE
        return
    }

    // ── Movement ─────────────────────────────────────
    if powerup_dx_sign == 0 {
        powerup_x += POWERUP_SPEED
    } else {
        powerup_x -= POWERUP_SPEED
    }
    if powerup_dy_sign == 0 {
        powerup_y += POWERUP_SPEED
    } else {
        powerup_y -= POWERUP_SPEED
    }

    // ── Wall bounces ─────────────────────────────────
    if powerup_dy_sign == 1 {
        if powerup_y < PLAYFIELD_TOP {
            powerup_y = PLAYFIELD_TOP
            powerup_dy_sign = 0
        }
    }
    if powerup_dy_sign == 0 {
        if powerup_y + POWERUP_SIZE > PLAYFIELD_BOTTOM {
            powerup_y = PLAYFIELD_BOTTOM - POWERUP_SIZE
            powerup_dy_sign = 1
        }
    }
    // Bounce off left/right back walls (not paddles — the
    // powerup flies past paddles and only bounces off the
    // absolute screen edges).
    if powerup_dx_sign == 1 {
        if powerup_x < 4 {
            powerup_x = 4
            powerup_dx_sign = 0
        }
    }
    if powerup_dx_sign == 0 {
        if powerup_x + POWERUP_SIZE > 252 {
            powerup_x = 252 - POWERUP_SIZE
            powerup_dx_sign = 1
        }
    }

    // ── Paddle catch ─────────────────────────────────
    var caught: u8 = check_powerup_vs_paddle(SIDE_LEFT)
    if caught == 0 {
        check_powerup_vs_paddle(SIDE_RIGHT)
    }
}
