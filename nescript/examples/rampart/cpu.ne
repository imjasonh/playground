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

// The CPU and the rules live in a switchable bank. The fixed bank
// is full. Calls from the fixed bank go through trampolines.
bank Brain {
include "rules.ne"
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
                        var w: u8 = loadout[p * 2 + 1]
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

    // Naming and weapon picks. No locals: res_a and res_b are scratch.
    // A fourth nametable does not fit in the fixed bank, so this
    // wipes the title while the screen is off and paints over it.
    // cust_cursor 10 means the wipe is still running.

    // Index of the last non-space letter in p's name, or 0 when the
    // name is empty. The cursor starts here, the way a text field
    // places the caret after existing text.
    fun name_end(p: u8) -> u8 {
        var i: u8 = 5
        while i > 0 and name_ch[p * 6 + i] == T_SPACE {
            i -= 1
        }
        return i
    }

    fun paint_cust() {
        if cust_who == 0 {
            put_str(2, 1, S_P1)
            nt_attr(8, 4, 170)
            nt_attr(12, 4, 170)
            nt_attr(0, 8, 136)
            nt_attr(4, 8, 170)
            nt_attr(0, 12, 8)
            nt_attr(4, 12, 10)
        } else {
            put_str(2, 1, S_P2)
            nt_attr(8, 4, 255)
            nt_attr(12, 4, 255)
            nt_attr(0, 8, 204)
            nt_attr(4, 8, 255)
            nt_attr(0, 12, 12)
            nt_attr(4, 12, 15)
        }
        nt_attr(0, 20, 0)
        nt_attr(4, 20, 0)
        nt_attr(0, 24, 0)
        nt_attr(4, 24, 0)
        put_str(3, NAME_ROW, S_C_NAME)
        put_str(3, GUN_ROW, S_L_GUN)
        put_str(3, ARM_ROW, S_C_ARM)
        put_str(3, START_ROW, S_C_START)
        put_str(3, BACKSPACE_ROW, S_C_BACKSPACE)
        res_a = 0
        while res_a < 6 {
            put_tile(NAME_COL + res_a, NAME_ROW, name_ch[cust_who * 6 + res_a])
            res_a += 1
        }
        paint_portrait(2, 8, mech_frame[cust_who])
        res_b = loadout[cust_who * 2]
        put_clear(11, 16, WPN_NAME_W)
        put_str(11, 16, W_STR[res_b])
        res_b = loadout[cust_who * 2 + 1]
        put_clear(11, 18, WPN_NAME_W)
        put_str(11, 18, W_STR[res_b])
    }

    fun customize_begin() {
        cust_who = 0
        while cust_who < 2 and is_cpu(cust_who) {
            apply_stock(cust_who)
            cust_who += 1
        }
        if cust_who >= 2 {
            cust_cursor = 9
            transition Battle
            return
        }
        apply_stock(cust_who)
        cust_cursor = 10
        cust_tick = 0
        poke(0x2001, 0x00)
        unblank = 24
    }

    fun customize_tick() {
        tick_unblank()
        flush_text()
        if cust_cursor == 10 {
            res_a = 0
            while res_a < 4 and cust_tick < 30 {
                put_clear(0, cust_tick, 32)
                cust_tick += 1
                res_a += 1
            }
            if cust_tick >= 30 {
                paint_cust()
                cust_cursor = name_end(cust_who)
                cust_tick = 0
            }
            return
        }
        cust_tick += 1
        if cust_cursor < 6 and (cust_tick & 15) == 0 {
            if (cust_tick & 16) == 0 {
                put_tile(NAME_COL + cust_cursor, NAME_ROW, name_ch[cust_who * 6 + cust_cursor])
            } else {
                put_tile(NAME_COL + cust_cursor, NAME_ROW, T_SPACE)
            }
        }

        // On the name row, left/right move the lit letter and
        // up/down rotate it. On the gun and arm rows, left/right
        // cycle that row's weapon and up/down move to the next row,
        // so either weapon can be any of the five, gun and arm alike.
        res_b = pad_pressed(cust_who)
        if res_b == BTN_LEFT {
            if cust_cursor < 6 and cust_cursor > 0 {
                put_tile(NAME_COL + cust_cursor, NAME_ROW, name_ch[cust_who * 6 + cust_cursor])
                cust_cursor -= 1
                cust_tick = 0
            } else if cust_cursor == 6 {
                res_a = (loadout[cust_who * 2] + NUM_WEAPONS - 1) % NUM_WEAPONS
                loadout[cust_who * 2] = res_a
                put_clear(11, GUN_ROW, WPN_NAME_W)
                put_str(11, GUN_ROW, W_STR[res_a])
            } else if cust_cursor == 7 {
                res_a = (loadout[cust_who * 2 + 1] + NUM_WEAPONS - 1) % NUM_WEAPONS
                loadout[cust_who * 2 + 1] = res_a
                put_clear(11, ARM_ROW, WPN_NAME_W)
                put_str(11, ARM_ROW, W_STR[res_a])
            }
        }
        if res_b == BTN_RIGHT {
            if cust_cursor < 6 {
                put_tile(NAME_COL + cust_cursor, NAME_ROW, name_ch[cust_who * 6 + cust_cursor])
                cust_cursor += 1
                cust_tick = 0
            } else if cust_cursor == 6 {
                res_a = (loadout[cust_who * 2] + 1) % NUM_WEAPONS
                loadout[cust_who * 2] = res_a
                put_clear(11, GUN_ROW, WPN_NAME_W)
                put_str(11, GUN_ROW, W_STR[res_a])
            } else if cust_cursor == 7 {
                res_a = (loadout[cust_who * 2 + 1] + 1) % NUM_WEAPONS
                loadout[cust_who * 2 + 1] = res_a
                put_clear(11, ARM_ROW, WPN_NAME_W)
                put_str(11, ARM_ROW, W_STR[res_a])
            }
        }
        if res_b == BTN_UP or res_b == BTN_DOWN {
            if cust_cursor < 6 {
                res_a = name_ch[cust_who * 6 + cust_cursor]
                if res_b == BTN_DOWN {
                    if res_a == T_SPACE {
                        res_a = 90
                    } else if res_a == 65 {
                        res_a = T_SPACE
                    } else {
                        res_a -= 1
                    }
                } else if res_a == T_SPACE {
                    res_a = 65
                } else if res_a == 90 {
                    res_a = T_SPACE
                } else {
                    res_a += 1
                }
                name_ch[cust_who * 6 + cust_cursor] = res_a
                put_tile(NAME_COL + cust_cursor, NAME_ROW, res_a)
                cust_tick = 0
            } else if cust_cursor == 6 {
                cust_cursor = 7
                if res_b == BTN_UP {
                    cust_cursor = 5
                }
                cust_tick = 0
            } else if cust_cursor == 7 {
                cust_cursor = 8
                if res_b == BTN_UP {
                    cust_cursor = 6
                }
                cust_tick = 0
            } else if cust_cursor == 8 and res_b == BTN_UP {
                cust_cursor = 7
                cust_tick = 0
            }
        }
        // B backspaces: clear the lit letter and step left, so
        // repeated presses erase BLUE as BLU, BL, B, then nothing,
        // the way a text field's Backspace key does.
        if res_b == BTN_B and cust_cursor < 6 {
            name_ch[cust_who * 6 + cust_cursor] = T_SPACE
            put_tile(NAME_COL + cust_cursor, NAME_ROW, T_SPACE)
            if cust_cursor > 0 {
                cust_cursor -= 1
            }
            cust_tick = 0
        }
        if res_b == BTN_START or (res_b == BTN_A and cust_cursor == 8) {
            res_a = 0
            res_b = 1
            while res_a < 6 {
                if name_ch[cust_who * 6 + res_a] != T_SPACE {
                    res_b = 0
                }
                res_a += 1
            }
            if res_b == 1 {
                res_a = 0
                res_b = cust_who * 6
                while res_a < 6 {
                    name_ch[cust_who * 6 + res_a] = FRAME_NAME[res_b + res_a]
                    res_a += 1
                }
            }
            cust_who += 1
            while cust_who < 2 and is_cpu(cust_who) {
                apply_stock(cust_who)
                cust_who += 1
            }
            if cust_who >= 2 {
                cust_cursor = 9
                transition Battle
                return
            }
            apply_stock(cust_who)
            cust_cursor = name_end(cust_who)
            cust_tick = 0
            paint_cust()
        }
    }
}