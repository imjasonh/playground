// rampart/rules.ne: dice, geometry, legality, and damage.

fun d6() -> u8 {
    loop {
        var r: u8 = rand8() & 7
        if r < 6 {
            return r + 1
        }
    }
}

fun absdiff(a: u8, b: u8) -> u8 {
    if a > b {
        return a - b
    }
    return b - a
}

fun cheb(ax: u8, ay: u8, bx: u8, by: u8) -> u8 {
    var dx: u8 = ax - bx
    if bx > ax {
        dx = bx - ax
    }
    var dy: u8 = ay - by
    if by > ay {
        dy = by - ay
    }
    if dx > dy {
        return dx
    }
    return dy
}

fun mech_dist() -> u8 {
    return cheb(mech_x[0], mech_y[0], mech_x[1], mech_y[1])
}

fun is_ruin(x: u8, y: u8) -> bool {
    var i: u8 = 0
    while i < NUM_RUINS {
        if RUIN_X[i] == x and RUIN_Y[i] == y {
            return true
        }
        i += 1
    }
    return false
}

// True when a ruin lies strictly between (ax, ay) and (bx, by):
// any square the straight line between them passes through,
// rounded to the nearest square at each of the n - 1 steps.
fun has_cover(ax: u8, ay: u8, bx: u8, by: u8) -> bool {
    var dx: u8 = ax - bx
    if bx > ax {
        dx = bx - ax
    }
    var dy: u8 = ay - by
    if by > ay {
        dy = by - ay
    }
    var n: u8 = dx
    if dy > n {
        n = dy
    }
    var n2: u8 = n * 2
    var i: u8 = 1
    while i < n {
        var qx: u8 = (dx * i * 2 + n) / n2
        var qy: u8 = (dy * i * 2 + n) / n2
        var x: u8 = ax + qx
        if bx < ax {
            x = ax - qx
        }
        var y: u8 = ay + qy
        if by < ay {
            y = ay - qy
        }
        if is_ruin(x, y) {
            return true
        }
        i += 1
    }
    return false
}

fun mech_cover() -> bool {
    return has_cover(mech_x[0], mech_y[0], mech_x[1], mech_y[1])
}

fun intact(p: u8, loc: u8) -> bool {
    return armor[p * 11 + loc] != 0
}

fun legs_down(p: u8) -> u8 {
    var n: u8 = 0
    if not intact(p, L_LEGL) {
        n += 1
    }
    if not intact(p, L_LEGR) {
        n += 1
    }
    return n
}

// Base range less one per wrecked leg. With both legs wrecked the
// mech can't move at all.
fun move_range(p: u8, base: u8) -> u8 {
    var l: u8 = legs_down(p)
    if l == 2 or l >= base {
        return 0
    }
    return base - l
}

fun plan_legal(p: u8, idx: u8) -> bool {
    var cap: u8 = 3
    if not intact(p, L_HEAD) {
        cap = 2
    }
    if PLAN_COST[idx] > cap {
        return false
    }
    if (PLAN_MASK[idx] & BIT[A_SHIELD]) != 0 {
        if not intact(p, L_SHIELD) {
            return false
        }
    }
    return true
}

fun weapon_ok(p: u8, slot: u8) -> bool {
    return intact(p, W_SLOT_LOC[slot])
}

// The ranged weapon p fires at distance d: the gun if it's intact
// and in range, else the left-arm weapon, else NO_WEAPON.
fun pick_ranged(p: u8, d: u8) -> u8 {
    var base: u8 = mech_frame[p] * 3
    if weapon_ok(p, 0) and d <= W_RANGE[base] {
        return base
    }
    if weapon_ok(p, 1) and d <= W_RANGE[base + 1] {
        return base + 1
    }
    return NO_WEAPON
}

// Longest range p can shoot at with its remaining weapons.
fun best_range(p: u8) -> u8 {
    var base: u8 = mech_frame[p] * 3
    var r: u8 = 1
    if weapon_ok(p, 0) {
        r = W_RANGE[base]
    }
    if weapon_ok(p, 1) and W_RANGE[base + 1] > r {
        r = W_RANGE[base + 1]
    }
    return r
}

// Save roll needed (d6 >= need saves). AP raises it; cover and an
// earlier shield lower it. Neither helps against melee, so callers
// pass cover = false for melee.
fun save_need(target: u8, w: u8, ranged: bool, cover: bool) -> u8 {
    var need: u8 = SAVE_TARGET + W_AP[w]
    if ranged {
        if cover {
            need -= 1
        }
        if shield_up[target] != 0 and armor[target * 11 + L_SHIELD] != 0 {
            need -= 1
        }
    }
    return need
}

// Square (x, y) is a legal end of a move for p.
fun square_open(p: u8, x: u8, y: u8) -> bool {
    if x >= BOARD_N or y >= BOARD_N {
        return false
    }
    if is_ruin(x, y) {
        return false
    }
    var o: u8 = 1 - p
    if mech_x[o] == x and mech_y[o] == y {
        return false
    }
    return true
}

// Apply d damage to loc. Returns true when it goes critical.
fun apply_damage(p: u8, loc: u8, d: u8) -> bool {
    var i: u8 = p * 11 + loc
    if armor[i] <= d {
        armor[i] = 0
        crits[p] += 1
        return true
    }
    armor[i] -= d
    return false
}

fun reset_mechs() {
    var p: u8 = 0
    while p < 2 {
        mech_x[p] = START_X[p]
        mech_y[p] = START_Y[p]
        var l: u8 = 0
        while l < NUM_LOCS {
            armor[p * 11 + l] = START_ARMOR[l]
            l += 1
        }
        crits[p] = 0
        shield_up[p] = 0
        p += 1
    }
    turn = 1
}

fun is_cpu(p: u8) -> bool {
    if mode == MODE_CPU2 {
        return true
    }
    if mode == MODE_1P and p == 1 {
        return true
    }
    return false
}
