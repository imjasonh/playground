// rampart/render.ne: text queue, panel painting, and sprites.
//
// Code never calls nt_set directly outside flush_text(). Callers
// queue print commands; flush_text() runs once per frame and turns
// at most RING_BUDGET bytes of them into VRAM ring entries, so a
// full panel repaint spreads over a few frames instead of
// overrunning vblank.

const K_STR: u8 = 0
const K_NUM: u8 = 1
const K_CLEAR: u8 = 2
const K_TILE: u8 = 3
const K_PLATE: u8 = 4
const RING_BUDGET: u8 = 160

fun str_byte(id: u8, i: u8) -> u8 {
    var c: u8 = STR_CHUNK[id]
    var o: u8 = STR_OFF[id] + i
    if c == 0 {
        return TXT0[o]
    }
    if c == 1 {
        return TXT1[o]
    }
    return TXT2[o]
}

fun push_cmd(kind: u8, x: u8, y: u8, arg: u8) {
    q_kind[q_tail] = kind
    q_x[q_tail] = x
    q_y[q_tail] = y
    q_arg[q_tail] = arg
    q_tail = (q_tail + 1) & 63
}

fun put_str(x: u8, y: u8, id: u8) {
    push_cmd(K_STR, x, y, id)
}

// Two digits, or one when n < 10.
fun put_num(x: u8, y: u8, n: u8) {
    push_cmd(K_NUM, x, y, n)
}

fun put_clear(x: u8, y: u8, len: u8) {
    push_cmd(K_CLEAR, x, y, len)
}

fun put_tile(x: u8, y: u8, t: u8) {
    push_cmd(K_TILE, x, y, t)
}

fun text_idle() -> bool {
    return q_head == q_tail
}

// Damage tier for a location: 0 once its armor hits zero, else how
// full its armor is out of its own max (START_ARMOR[loc]), rounded
// up into 1..4 so any remaining armor shows as more than empty and
// full armor always shows as tier 4 regardless of that max.
fun damage_tier(p: u8, loc: u8) -> u8 {
    var a: u8 = armor[p * 11 + loc]
    if a == 0 {
        return 0
    }
    var mx: u8 = START_ARMOR[loc]
    return (a * 4 + mx - 1) / mx
}

fun plate_tile(p: u8, cell: u8) -> u8 {
    var loc: u8 = PLATE[cell]
    if loc == L_NONE {
        return T_MISS
    }
    return T_DAMAGE0 + damage_tier(p, loc)
}

fun cmd_cost(kind: u8, arg: u8) -> u8 {
    if kind == K_STR {
        return STR_LEN[arg] * 4
    }
    if kind == K_NUM {
        return 8
    }
    if kind == K_CLEAR {
        return arg + 3
    }
    if kind == K_PLATE {
        return 24
    }
    return 4
}

fun flush_text() {
    var budget: u8 = RING_BUDGET
    while q_head != q_tail {
        var k: u8 = q_kind[q_head]
        var x: u8 = q_x[q_head]
        var y: u8 = q_y[q_head]
        var a: u8 = q_arg[q_head]
        var cost: u8 = cmd_cost(k, a)
        if cost > budget {
            return
        }
        budget -= cost
        if k == K_STR {
            var n: u8 = STR_LEN[a]
            var i: u8 = 0
            while i < n {
                nt_set(x + i, y, str_byte(a, i))
                i += 1
            }
        } else if k == K_NUM {
            if a >= 10 {
                nt_set(x, y, T_DIGIT0 + a / 10)
                nt_set(x + 1, y, T_DIGIT0 + a % 10)
            } else {
                nt_set(x, y, T_DIGIT0 + a)
            }
        } else if k == K_CLEAR {
            nt_fill_h(x, y, a, T_SPACE)
        } else if k == K_TILE {
            nt_set(x, y, a)
        } else {
            // K_PLATE: arg = player * 8 + row.
            var p: u8 = a >> 3
            var cell: u8 = (a & 7) * 6
            var c: u8 = 0
            while c < 6 {
                nt_set(x + c, y, plate_tile(p, cell + c))
                c += 1
            }
        }
        q_head = (q_head + 1) & 63
    }
}

// Blank rendering, queue a full nametable, and bring rendering back
// two frames later. The NMI copies the nametable while the screen
// is off; nametable writes don't fit in one vblank.
fun swap_background(which: u8) {
    poke(0x2001, 0x00)
    q_head = q_tail
    if which == 0 {
        load_background Title
    } else if which == 1 {
        load_background Board
    } else {
        load_background Card
    }
    unblank = 2
}

fun tick_unblank() {
    if unblank > 0 {
        unblank -= 1
        if unblank == 0 {
            poke(0x2001, 0x1E)
        }
    }
}

// ── Messages (rows 27 and 28) ───────────────────────────────

fun msg_line(row: u8) {
    put_clear(1, row, 30)
    msg_x = 1
    msg_y = row
}

fun msg_clear() {
    put_clear(1, MSG_ROW1, 30)
    put_clear(1, MSG_ROW2, 30)
}

fun msg_str(id: u8) {
    put_str(msg_x, msg_y, id)
    msg_x += STR_LEN[id] + 1
}

fun msg_num(n: u8) {
    put_num(msg_x, msg_y, n)
    if n >= 10 {
        msg_x += 3
    } else {
        msg_x += 2
    }
}

fun msg_who(p: u8) {
    if p == 0 {
        msg_str(S_P1)
    } else {
        msg_str(S_P2)
    }
}

// ── Panel ───────────────────────────────────────────────────

fun paint_plate(p: u8) {
    var base: u8 = P_BASE[p] + 2
    var r: u8 = 0
    while r < 6 {
        push_cmd(K_PLATE, PLATE_X, base + r, p * 8 + r)
        r += 1
    }
}

fun paint_crits(p: u8) {
    var row: u8 = P_BASE[p] + 8
    put_str(PANEL_X, row, S_CRIT)
    put_num(PANEL_X + 5, row, crits[p])
}

fun paint_shield(p: u8) {
    var row: u8 = P_BASE[p] + 1
    put_clear(PANEL_X, row, PANEL_W)
    if shield_up[p] != 0 {
        put_str(PANEL_X, row, S_SHIELD_UP)
    }
}

// Show the locked plan's actions, or nothing while it's secret.
fun paint_plan(p: u8, shown: bool) {
    var row: u8 = P_BASE[p] + 9
    put_clear(PANEL_X, row, PANEL_W)
    put_clear(PANEL_X, row + 1, PANEL_W)
    put_clear(PANEL_X, row + 2, PANEL_W)
    if not shown {
        return
    }
    var mask: u8 = PLAN_MASK[plan[p]]
    var a: u8 = 0
    while a < NUM_ACTIONS {
        if (mask & BIT[a]) != 0 {
            put_str(PANEL_X, row, ACTION_PANEL_STR[a])
            row += 1
        }
        a += 1
    }
}

fun paint_turn() {
    put_str(TURN_X, INFO_ROW, S_TURN)
    put_clear(TURN_X + 5, INFO_ROW, 2)
    put_num(TURN_X + 5, INFO_ROW, turn)
}

fun paint_range(d: u8, cover: bool) {
    put_clear(1, INFO_ROW, 16)
    put_str(1, INFO_ROW, S_RANGE)
    put_num(7, INFO_ROW, d)
    if cover {
        put_str(10, INFO_ROW, S_COVER)
    }
}

fun paint_panel_header(p: u8) {
    var row: u8 = P_BASE[p]
    put_num(PANEL_X, row, p + 1)
    put_str(PANEL_X + 2, row, FRAME_STR[mech_frame[p]])
}

// ── Sprites ─────────────────────────────────────────────────

fun draw_mech(p: u8) {
    var t: u8 = T_PIKE1
    if mech_frame[p] == 1 {
        t = T_MAUL1
    }
    if p == 1 {
        t += 4
    }
    var sx: u8 = mech_x[p] * 16 + BOARD_PX
    var sy: u8 = mech_y[p] * 16 + 15
    draw Tileset at: (sx, sy) frame: t
    draw Tileset at: (sx + 8, sy) frame: t + 1
    draw Tileset at: (sx, sy + 8) frame: t + 2
    draw Tileset at: (sx + 8, sy + 8) frame: t + 3
}

// Corner brackets around board square (x, y).
fun draw_square_cursor(x: u8, y: u8) {
    var sx: u8 = x * 16 + BOARD_PX
    var sy: u8 = y * 16 + 15
    draw Tileset at: (sx, sy) frame: T_CURSOR
    draw Tileset at: (sx + 8, sy) frame: T_CURSOR + 1
    draw Tileset at: (sx, sy + 8) frame: T_CURSOR + 2
    draw Tileset at: (sx + 8, sy + 8) frame: T_CURSOR + 3
}

// Box over cell (x, y) of player p's plate on the panel.
fun draw_plate_cursor(p: u8, x: u8, y: u8) {
    var sx: u8 = (PLATE_X + x) * 8
    var sy: u8 = (P_BASE[p] + 2 + y) * 8 - 1
    draw Tileset at: (sx, sy) frame: T_BOX
}
