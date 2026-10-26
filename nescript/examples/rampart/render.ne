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
const K_PORTRAIT: u8 = 5
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

// How beaten up a location looks: 0 untouched, 1 after its first
// hit, 2 after more, 3 on its last point of armor, 4 wrecked.
fun damage_level(p: u8, loc: u8) -> u8 {
    var a: u8 = armor[p * 11 + loc]
    var mx: u8 = START_ARMOR[loc]
    if a == 0 {
        return 4
    }
    if a == mx {
        return 0
    }
    if a == 1 {
        return 3
    }
    if mx - a == 1 {
        return 1
    }
    return 2
}

fun wpn_tile(id: u8, half: u8) -> u8 {
    return WPN_TILE[id * 2 + half]
}

// The portrait tile for one plate cell, charred once its location is
// wrecked. Cells off the plate still draw so the outline stays whole.
fun plate_tile(p: u8, cell: u8) -> u8 {
    var t: u8 = T_PLATE + cell
    if mech_frame[p] == 1 {
        t += 72
    }
    var loc: u8 = PLATE[cell]
    if loc != L_NONE {
        if armor[p * 11 + loc] == 0 {
            t += T_CHARRED
        }
    }
    return t
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
    if kind >= K_PLATE {
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
        } else if k == K_PLATE {
            // arg = player * 8 + row.
            var p: u8 = a >> 3
            var cell: u8 = (a & 7) * 6
            var c: u8 = 0
            while c < 6 {
                nt_set(x + c, y, plate_tile(p, cell + c))
                c += 1
            }
        } else {
            // K_PORTRAIT, an undamaged portrait row: arg = frame * 8 + row.
            var pt: u8 = T_PLATE + (a & 7) * 6
            if a >= 8 {
                pt += 72
            }
            var pc: u8 = 0
            while pc < 6 {
                nt_set(x + pc, y, pt + pc)
                pc += 1
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

// The name chosen at setup, without the trailing spaces, then the
// same gap msg_str leaves after a word.
fun msg_who(p: u8) {
    var end: u8 = 5
    while end > 0 and name_ch[p * 6 + end] == T_SPACE {
        end -= 1
    }
    var n: u8 = end + 1
    if name_ch[p * 6] == T_SPACE {
        n = 0
    }
    var i: u8 = 0
    while i < n {
        put_tile(msg_x, msg_y, name_ch[p * 6 + i])
        msg_x += 1
        i += 1
    }
    msg_x += 1
}

// ── Panel ───────────────────────────────────────────────────

fun paint_plate(p: u8) {
    rebuild_decals()
    var base: u8 = P_BASE[p] + 2
    var r: u8 = 0
    while r < 6 {
        push_cmd(K_PLATE, PLATE_X, base + r, p * 8 + r)
        r += 1
    }
}

// Frame f's undamaged portrait with its top-left cell at (x, y).
fun paint_portrait(x: u8, y: u8, f: u8) {
    var r: u8 = 0
    while r < 6 {
        push_cmd(K_PORTRAIT, x, y + r, f * 8 + r)
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

// The locked plan, one icon per action, or nothing while it's secret.
// The panel is six tiles wide, so the icons stand in for the names.
// The message line still spells the action.
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
            put_tile(PANEL_X, row, T_ACT + a)
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

// The panel color is the player. The first player's block is blue
// and the second player's is red. The six letters are the name
// chosen at setup.
fun paint_panel_header(p: u8) {
    var row: u8 = P_BASE[p]
    var i: u8 = 0
    while i < 6 {
        put_tile(PANEL_X + i, row, name_ch[p * 6 + i])
        i += 1
    }
}

// ── Sprites ─────────────────────────────────────────────────

// The board mech in its player's palette.
fun draw_mech(p: u8) {
    var t: u8 = T_PIKE
    if mech_frame[p] == 1 {
        t = T_MAUL
    }
    var sx: u8 = mech_x[p] * 16 + BOARD_PX
    var sy: u8 = mech_y[p] * 16 + 15
    draw Tileset at: (sx, sy) attr: p frame: t
    draw Tileset at: (sx + 8, sy) attr: p frame: t + 1
    draw Tileset at: (sx, sy + 8) attr: p frame: t + 2
    draw Tileset at: (sx + 8, sy + 8) attr: p frame: t + 3
}

// Corner brackets around board square (x, y): one corner tile,
// flipped into the other three.
fun draw_square_cursor(x: u8, y: u8) {
    var sx: u8 = x * 16 + BOARD_PX
    var sy: u8 = y * 16 + 15
    draw Tileset at: (sx, sy) attr: SP_FIRE frame: T_CORNER
    draw Tileset at: (sx + 8, sy) attr: SP_FIRE | FLIP_H frame: T_CORNER
    draw Tileset at: (sx, sy + 8) attr: SP_FIRE | FLIP_V frame: T_CORNER
    draw Tileset at: (sx + 8, sy + 8) attr: SP_FIRE | FLIP_H | FLIP_V frame: T_CORNER
}

// Brackets around cell (x, y) of player p's plate on the panel.
fun draw_plate_cursor(p: u8, x: u8, y: u8) {
    var sx: u8 = (PLATE_X + x) * 8
    var sy: u8 = (P_BASE[p] + 2 + y) * 8 - 1
    draw Tileset at: (sx, sy) attr: SP_FIRE frame: T_AIM
}

// Impact flash on cell (x, y) of player p's plate.
fun draw_plate_hit(p: u8, x: u8, y: u8) {
    var sx: u8 = (PLATE_X + x) * 8
    var sy: u8 = (P_BASE[p] + 2 + y) * 8 - 1
    draw Tileset at: (sx, sy) attr: SP_FIRE frame: T_BURST
}

// Scuffs, then holes, then fire, then a crater: each damage level
// moves the main decal one step along and leaves the previous step
// on the second anchor.
const DECAL_A: u8[5] = [0, T_SCUFF, T_HOLES, T_FIRE, T_CRATER]
const DECAL_B: u8[5] = [0, 0, T_SCUFF, T_HOLES, T_FIRE]

// Damage decals as ready-to-draw sprites. Working out damage levels
// for both plates every frame costs more than a frame has, so
// add_decals() rebuilds this list whenever a plate is repainted.
var dec_x: u8[44]
var dec_y: u8[44]
var dec_t: u8[44]
var dec_a: u8[44]
var dec_n: u8 = 0

// One decal at plate pixel (dx, dy). Fire never flips upside down.
fun push_decal(p: u8, dx: u8, dy: u8, kind: u8, flip: u8) {
    dec_x[dec_n] = PLATE_X * 8 + dx
    dec_y[dec_n] = (P_BASE[p] + 2) * 8 + dy - 1
    dec_t[dec_n] = kind
    if kind == T_FIRE {
        dec_a[dec_n] = SP_FIRE | (flip & FLIP_H)
    } else {
        dec_a[dec_n] = SP_DAMAGE | flip
    }
    dec_n += 1
}

fun add_decals(p: u8) {
    var loc: u8 = 0
    while loc < NUM_LOCS {
        var lvl: u8 = damage_level(p, loc)
        if lvl != 0 {
            var f: u8 = DEC_FLIP[loc]
            push_decal(p, DEC_AX[loc], DEC_AY[loc], DECAL_A[lvl], f)
            if lvl >= 2 {
                if DEC_BX[loc] != 255 {
                    push_decal(p, DEC_BX[loc], DEC_BY[loc], DECAL_B[lvl], f ^ FLIP_V)
                }
            }
        }
        loc += 1
    }
}

fun rebuild_decals() {
    dec_n = 0
    add_decals(0)
    add_decals(1)
}

// Fire flickers between its two frames.
fun draw_decals() {
    var flame: u8 = (anim >> 3) & 1
    var i: u8 = 0
    while i < dec_n {
        var t: u8 = dec_t[i]
        if t == T_FIRE {
            t += flame
        }
        draw Tileset at: (dec_x[i], dec_y[i]) attr: dec_a[i] frame: t
        i += 1
    }
}
