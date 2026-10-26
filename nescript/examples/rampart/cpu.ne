// rampart/cpu.ne: CPU plan choice, move choice, and aim.
//
// Easy picks at random among legal choices. Medium follows a fixed
// priority list. Hard scores every legal plan, scores each square
// it can reach, and aims where the scatter spread expects the most
// damage. Move and aim searches run one row per frame so a frame
// never overruns.

var cpu_best: u8 = 0
var cpu_bx: u8 = 0
var cpu_by: u8 = 0
var cpu_row: u8 = 0
var cpu_row_end: u8 = 0
var cpu_col0: u8 = 0
var cpu_col1: u8 = 0
var cpu_ideal_d: u8 = 0
// Aim value per location for the shot being aimed.
var loc_value: u8[12]
// Cover between the mechs, computed once per plan choice.
var cpu_cover: bool = false

const MED_IN_RANGE: u8[4] = [14, 10, 3, 0]
const MED_CLOSING: u8[3] = [13, 4, 1]

// The CPU player lives in a switchable bank. Calls from the fixed
// bank go through trampolines; calls inside the bank and from it to
// the fixed bank are plain JSRs.
bank Brain {
    fun first_legal(p: u8) -> u8 {
        var i: u8 = 0
        while i < NUM_PLANS {
            if plan_legal(p, i) {
                return i
            }
            i += 1
        }
        return 0
    }

    // Preferred distance to the enemy. Outranging the enemy means
    // standing off at full range; otherwise close in.
    fun cpu_ideal(p: u8, act: u8) -> u8 {
        if act == A_CHARGE {
            return 1
        }
        var r: u8 = best_range(p)
        if r > best_range(1 - p) {
            return r
        }
        return 2
    }

    // Move from distance pd up to mv squares toward ideal.
    fun approach(pd: u8, mv: u8, ideal: u8) -> u8 {
        if pd > ideal {
            if pd - ideal > mv {
                return pd - mv
            }
            return ideal
        }
        if ideal - pd > mv {
            return pd + mv
        }
        return ideal
    }

    fun unsaved_faces(need: u8) -> u8 {
        if need > 7 {
            return 6
        }
        if need == 0 {
            return 0
        }
        return need - 1
    }

    fun shot_value(p: u8, a: u8, d: u8) -> u8 {
        var w: u8 = pick_ranged(p, d)
        if w == NO_WEAPON {
            return 0
        }
        var u: u8 = unsaved_faces(save_need(1 - p, w, true, cpu_cover))
        return HIT_W[SCATTER_OF[a]] * W_DMG[w] * u
    }

    fun hard_score(p: u8, idx: u8) -> u8 {
        var mask: u8 = PLAN_MASK[idx]
        var pd: u8 = mech_dist()
        var ideal: u8 = cpu_ideal(p, 0)
        var s: u8 = 0
        var a: u8 = 0
        while a < NUM_ACTIONS {
            if (mask & BIT[a]) != 0 {
                if a == A_SNAP or a == A_STANDARD or a == A_AIMED {
                    s += shot_value(p, a, pd)
                } else if a == A_SHIELD {
                    if pd <= best_range(1 - p) {
                        s += 12
                    }
                } else if a == A_CHARGE {
                    var mv: u8 = move_range(p, CHARGE_RANGE)
                    if pd - 1 <= mv and intact(p, L_ARMR) {
                        var w: u8 = mech_frame[p] * 3 + 2
                        s += HIT_W[2] * W_DMG[w] * unsaved_faces(save_need(1 - p, w, false, false))
                        pd = 1
                    } else {
                        var np: u8 = approach(pd, mv, 1)
                        s += (pd - np) * 2
                        pd = np
                    }
                } else {
                    var range: u8 = move_range(p, STEP_RANGE)
                    if a == A_RUSH {
                        range = move_range(p, 2)
                    }
                    var npd: u8 = approach(pd, range, ideal)
                    s += (absdiff(pd, ideal) - absdiff(npd, ideal)) * 4
                    pd = npd
                }
            }
            a += 1
        }
        return s
    }

    fun cpu_pick_plan(p: u8) -> u8 {
        cpu_cover = mech_cover()
        if cpu_level == LEVEL_EASY {
            loop {
                var r: u8 = rand8() & 31
                if r < NUM_PLANS {
                    if plan_legal(p, r) {
                        return r
                    }
                }
            }
        }
        if cpu_level == LEVEL_MED {
            var i: u8 = 0
            if pick_ranged(p, mech_dist()) != NO_WEAPON {
                while i < 4 {
                    if plan_legal(p, MED_IN_RANGE[i]) {
                        return MED_IN_RANGE[i]
                    }
                    i += 1
                }
            } else {
                while i < 3 {
                    if plan_legal(p, MED_CLOSING[i]) {
                        return MED_CLOSING[i]
                    }
                    i += 1
                }
            }
            return first_legal(p)
        }
        var best: u8 = first_legal(p)
        var best_s: u8 = 0
        var j: u8 = 0
        while j < NUM_PLANS {
            if plan_legal(p, j) {
                var s: u8 = hard_score(p, j)
                if s > best_s {
                    best_s = s
                    best = j
                }
            }
            j += 1
        }
        return best
    }

    // ── Move search ─────────────────────────────────────────────

    fun cpu_move_begin(p: u8, range: u8, act: u8) {
        var ox: u8 = mech_x[p]
        var oy: u8 = mech_y[p]
        cpu_bx = ox
        cpu_by = oy
        cpu_best = 0
        cpu_ideal_d = cpu_ideal(p, act)
        cpu_row = 0
        if oy > range {
            cpu_row = oy - range
        }
        cpu_row_end = oy + range
        if cpu_row_end >= BOARD_N {
            cpu_row_end = BOARD_N - 1
        }
        cpu_col0 = 0
        if ox > range {
            cpu_col0 = ox - range
        }
        cpu_col1 = ox + range
        if cpu_col1 >= BOARD_N {
            cpu_col1 = BOARD_N - 1
        }
        if cpu_level == LEVEL_EASY {
            // Random legal square in range; stays put after 24 misses.
            var tries: u8 = 0
            while tries < 24 {
                var x: u8 = cpu_col0 + (rand8() & 15)
                var y: u8 = cpu_row + (rand8() & 15)
                if x <= cpu_col1 and y <= cpu_row_end and square_open(p, x, y) {
                    cpu_bx = x
                    cpu_by = y
                    tries = 24
                }
                tries += 1
            }
            cpu_row = cpu_row_end + 1
        }
    }

    // Score one row of candidate squares. Returns true when done.
    fun cpu_move_step(p: u8) -> bool {
        if cpu_row > cpu_row_end {
            return true
        }
        var o: u8 = 1 - p
        var x: u8 = cpu_col0
        while x <= cpu_col1 {
            if square_open(p, x, cpu_row) or (x == mech_x[p] and cpu_row == mech_y[p]) {
                var d: u8 = cheb(x, cpu_row, mech_x[o], mech_y[o])
                var v: u8 = 40 - absdiff(d, cpu_ideal_d) * 3
                if cpu_level == LEVEL_HARD {
                    if has_cover(x, cpu_row, mech_x[o], mech_y[o]) {
                        v += 4
                    }
                }
                if v > cpu_best {
                    cpu_best = v
                    cpu_bx = x
                    cpu_by = cpu_row
                }
            }
            x += 1
        }
        cpu_row += 1
        return cpu_row > cpu_row_end
    }

    // ── Aim search ──────────────────────────────────────────────

    fun cpu_aim_begin(p: u8, w: u8) {
        var t: u8 = 1 - p
        cpu_best = 0
        cpu_row = 0
        if cpu_level == LEVEL_EASY {
            cpu_bx = rand8() % 6
            cpu_by = rand8() % 6
            cpu_row = 6
            return
        }
        // Medium aims at the hull.
        cpu_bx = 2
        cpu_by = 3
        if cpu_level == LEVEL_MED {
            cpu_row = 6
            return
        }
        var d: u8 = W_DMG[w]
        var l: u8 = 0
        while l < NUM_LOCS {
            var a: u8 = armor[t * 11 + l]
            var v: u8 = 1
            if a == 0 {
                v = 0
            } else if a <= d {
                v = 3
                if l == L_HEAD {
                    v = 4
                }
            }
            loc_value[l] = v
            l += 1
        }
        loc_value[L_NONE] = 0
    }

    // Expected value of aiming at one row of cells. Returns true when
    // the search is done.
    fun cpu_aim_step(scatter: u8) -> bool {
        if cpu_row >= 6 {
            return true
        }
        var base: u8 = scatter * 4
        var cx: u8 = 0
        while cx < 6 {
            var total: u8 = 0
            var j: u8 = 0
            while j < 4 {
                var wy: u8 = SPREAD_W[base + j]
                var ty: u8 = cpu_row + SPREAD_V[base + j]
                if wy != 0 and ty >= 2 and ty < 8 {
                    var i: u8 = 0
                    while i < 4 {
                        var wx: u8 = SPREAD_W[base + i]
                        var tx: u8 = cx + SPREAD_V[base + i]
                        if wx != 0 and tx >= 2 and tx < 8 {
                            var v: u8 = loc_value[PLATE[(ty - 2) * 6 + tx - 2]]
                            total += v * wx * wy
                        }
                        i += 1
                    }
                }
                j += 1
            }
            if total > cpu_best {
                cpu_best = total
                cpu_bx = cx
                cpu_by = cpu_row
            }
            cx += 1
        }
        cpu_row += 1
        return cpu_row >= 6
    }
}
