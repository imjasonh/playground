// keep/actors.ne: walking, guards, and the shot.
//
// A shot is the center column of the last finished cast. The guard
// has to cover that column, plus one column either way, because a
// turn moves two angle steps and a far guard is only a couple of
// columns wide.

fun blocked(x: u8, y: u8) -> u8 {
    var c: u8 = cell_index(x, y)
    var t: u8 = LEVEL[c]
    if t != CELL_OPEN and t != CELL_EXIT {
        return 1
    }
    for i in 0..NUM_GUARDS {
        if ghp[i] != 0 and gcell[i] == c {
            return 1
        }
    }
    return 0
}

fun try_move(dir: u8) {
    var dx: u8 = MOVE_X[dir]
    var dy: u8 = MOVE_Y[dir]
    var nx: u8 = px + dx
    if blocked(nx, py) == 0 {
        px = nx
    }
    var ny: u8 = py + dy
    if blocked(px, ny) == 0 {
        py = ny
    }
}

fun hurt() {
    if phurt != 0 {
        return
    }
    if health == 0 {
        return
    }
    health = health - 1
    phurt = 40
    play damage
}

fun fire() {
    if ammo == 0 {
        play error
        return
    }
    ammo = ammo - 1
    flash = 6
    play Gun
    var best: u8 = 255
    var bestd: u8 = 255
    for i in 0..NUM_GUARDS {
        if gseen[i] != 0 and ghp[i] != 0 {
            if gcol0[i] <= 9 and gcol1[i] >= 7 {
                if gdist[i] < bestd {
                    bestd = gdist[i]
                    best = i
                }
            }
        }
    }
    if best != 255 {
        ghp[best] = ghp[best] - 1
        play hit
    } else {
        play shoot
    }
}

// axis_x 1 steps in x. neg 1 steps toward the origin. Returns 1
// when the guard actually moved.
fun try_guard(i: u8, neg: u8, axis_x: u8) -> u8 {
    var nx: u8 = gx[i]
    var ny: u8 = gy[i]
    if axis_x == 1 {
        if neg == 1 {
            if gx[i] < 8 {
                return 0
            }
            nx = gx[i] - 8
        } else {
            nx = gx[i] + 8
        }
    } else {
        if neg == 1 {
            if gy[i] < 8 {
                return 0
            }
            ny = gy[i] - 8
        } else {
            ny = gy[i] + 8
        }
    }
    var c: u8 = cell_index(nx, ny)
    var t: u8 = LEVEL[c]
    if t != CELL_OPEN and t != CELL_EXIT {
        return 0
    }
    for j in 0..NUM_GUARDS {
        if j != i and ghp[j] != 0 and gcell[j] == c {
            return 0
        }
    }
    // Don't walk onto the player. Bump them instead.
    if cell_index(px, py) == c {
        hurt()
        return 0
    }
    gx[i] = nx
    gy[i] = ny
    gcell[i] = c
    return 1
}

fun step_guard(i: u8) {
    var adx: u8 = 0
    var ady: u8 = 0
    var xneg: u8 = 0
    var yneg: u8 = 0
    if gx[i] > px {
        adx = gx[i] - px
        xneg = 1
    } else {
        adx = px - gx[i]
    }
    if gy[i] > py {
        ady = gy[i] - py
        yneg = 1
    } else {
        ady = py - gy[i]
    }
    if adx < 12 and ady < 12 {
        hurt()
        return
    }
    var moved: u8 = 0
    if adx > ady {
        moved = try_guard(i, xneg, 1)
        if moved == 0 {
            moved = try_guard(i, yneg, 0)
        }
    } else {
        moved = try_guard(i, yneg, 0)
        if moved == 0 {
            moved = try_guard(i, xneg, 1)
        }
    }
}

fun move_guards() {
    for i in 0..NUM_GUARDS {
        if ghp[i] != 0 {
            step_guard(i)
            if gcool[i] > 0 {
                gcool[i] = gcool[i] - 1
            } else {
                if gseen[i] != 0 and gdist[i] < 16 {
                    gcool[i] = 3
                    hurt()
                }
            }
        }
    }
}

fun reset_level() {
    px = START_X
    py = START_Y
    ang = START_ANG
    health = START_HP
    ammo = START_AMMO
    phurt = 0
    flash = 0
    gx[0] = G0X
    gy[0] = G0Y
    gx[1] = G1X
    gy[1] = G1Y
    gx[2] = G2X
    gy[2] = G2Y
    gx[3] = G3X
    gy[3] = G3Y
    for i in 0..NUM_GUARDS {
        ghp[i] = GUARD_HP
        gcool[i] = 0
        gcell[i] = 0
        gseen[i] = 0
        gnext[i] = 0
    }
    ai_timer = 0
    ai_due = 0
    rendered = 0
}

fun standing_on_exit() -> u8 {
    if LEVEL[cell_index(px, py)] == CELL_EXIT {
        return 1
    }
    return 0
}
