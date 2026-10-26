// rampart/battle_state.ne: one match, from first lock to result.
//
// Each turn: both players lock a plan in secret, the plans are
// revealed, then the seven actions resolve in order. When both
// plans hold the same action, a d6 roll-off (ties reroll) decides
// who goes first. A mech with six critical locations is lost.
//
// The sequencer is a phase machine. P_WAIT holds a message on
// screen for `timer` frames (A skips it) and then moves to `after`.

const P_WAIT: u8 = 0
const P_LOCK_START: u8 = 1
const P_LOCK: u8 = 2
const P_LOCK_DONE: u8 = 3
const P_REVEAL: u8 = 4
const P_NEXT_ACTION: u8 = 5
const P_DO: u8 = 6
const P_MOVE: u8 = 7
const P_MELEE: u8 = 8
const P_AIM: u8 = 9
const P_AFTER: u8 = 10
const P_OVER: u8 = 11

// Button codes from pad_pressed().
const BTN_UP: u8 = 0
const BTN_DOWN: u8 = 1
const BTN_LEFT: u8 = 2
const BTN_RIGHT: u8 = 3
const BTN_A: u8 = 4
const BTN_B: u8 = 5
const BTN_START: u8 = 6

const LOCK_STATUS_X: u8[2] = [1, 16]
const LOCK_STATUS_ROW: u8 = 27

// Edge-triggered press on player p's controller, as a BTN_ code.
fun pad_pressed(p: u8) -> u8 {
    if p == 0 {
        if p1.button.up.pressed {
            return BTN_UP
        }
        if p1.button.down.pressed {
            return BTN_DOWN
        }
        if p1.button.left.pressed {
            return BTN_LEFT
        }
        if p1.button.right.pressed {
            return BTN_RIGHT
        }
        if p1.button.a.pressed {
            return BTN_A
        }
        if p1.button.b.pressed {
            return BTN_B
        }
        if p1.button.start.pressed {
            return BTN_START
        }
        return B_NONE
    }
    if p2.button.up.pressed {
        return BTN_UP
    }
    if p2.button.down.pressed {
        return BTN_DOWN
    }
    if p2.button.left.pressed {
        return BTN_LEFT
    }
    if p2.button.right.pressed {
        return BTN_RIGHT
    }
    if p2.button.a.pressed {
        return BTN_A
    }
    if p2.button.b.pressed {
        return BTN_B
    }
    if p2.button.start.pressed {
        return BTN_START
    }
    return B_NONE
}

// Apply a d-pad code to (res_a, res_b), the cursor position.
// Returns false for non-direction codes.
fun nudge(b: u8, limit: u8) -> bool {
    if b == BTN_UP and res_b > 0 {
        res_b -= 1
        return true
    }
    if b == BTN_DOWN and res_b + 1 < limit {
        res_b += 1
        return true
    }
    if b == BTN_LEFT and res_a > 0 {
        res_a -= 1
        return true
    }
    if b == BTN_RIGHT and res_a + 1 < limit {
        res_a += 1
        return true
    }
    return false
}

// One step of (x, y) toward (tx, ty), left in res_a / res_b.
fun step_toward(x: u8, y: u8, tx: u8, ty: u8) {
    res_a = x
    res_b = y
    if tx > x {
        res_a = x + 1
    } else if tx < x {
        res_a = x - 1
    }
    if ty > y {
        res_b = y + 1
    } else if ty < y {
        res_b = y - 1
    }
}

fun paint_all() {
    paint_turn()
    paint_range(mech_dist(), mech_cover())
    var p: u8 = 0
    while p < 2 {
        paint_panel_header(p)
        paint_shield(p)
        paint_plate(p)
        paint_crits(p)
        paint_plan(p, false)
        p += 1
    }
}

fun paint_card() {
    var q: u8 = 0
    while q < 2 {
        var x: u8 = LOCK_STATUS_X[q]
        if q == 0 {
            put_str(x, LOCK_STATUS_ROW, S_P1)
        } else {
            put_str(x, LOCK_STATUS_ROW, S_P2)
        }
        if is_cpu(q) {
            put_str(x + 3, LOCK_STATUS_ROW, S_CPU)
            put_str(x + 7, LOCK_STATUS_ROW, S_READY)
        }
        q += 1
    }
}

fun total_armor(p: u8) -> u8 {
    var s: u8 = 0
    var l: u8 = 0
    while l < NUM_LOCS {
        s += armor[p * 11 + l]
        l += 1
    }
    return s
}

// 0 or 1 for a winner, 2 for a draw.
fun decide_winner() -> u8 {
    var lost0: bool = crits[0] >= LOSS_CRITS
    var lost1: bool = crits[1] >= LOSS_CRITS
    if lost0 and lost1 {
        return 2
    }
    if lost0 {
        return 1
    }
    if lost1 {
        return 0
    }
    if crits[0] < crits[1] {
        return 0
    }
    if crits[1] < crits[0] {
        return 1
    }
    var a0: u8 = total_armor(0)
    var a1: u8 = total_armor(1)
    if a0 > a1 {
        return 0
    }
    if a1 > a0 {
        return 1
    }
    return 2
}

// Sequencer state. Globals rather than state locals because
// the phase functions below read them.
var phase: u8 = P_WAIT
var after: u8 = P_LOCK_START
var timer: u8 = 40
var on_card: bool = false
var cur_act: u8 = 0
var first: u8 = 0
var count: u8 = 0
var step: u8 = 0
var actor: u8 = 0
// Lock: the last two presses and how many presses so far.
var lk_prev: u8[2]
var lk_last: u8[2]
var lk_n: u8[2]
var lk_ready: u8[2]
// Move: origin, cursor, and range.
var org_x: u8 = 0
var org_y: u8 = 0
var cur_x: u8 = 0
var cur_y: u8 = 0
var mrange: u8 = 0
// Aim: plate cursor, weapon, and whether the attack is ranged.
var aim_x: u8 = 0
var aim_y: u8 = 0
var wpn: u8 = 0
var aim_ranged: bool = true
var cpu_done: bool = false
var cpu_delay: u8 = 0
var show_hit: bool = false
var hit_x: u8 = 0
var hit_y: u8 = 0
var over_timer: u8 = 0
// Free-running frame counter for the fire decals' flicker.
var anim: u8 = 0

fun wait_then(t: u8, next: u8) {
    timer = t
    after = next
    phase = P_WAIT
}

fun run_wait() {
    if timer > 0 {
        timer -= 1
    }
    if p1.button.a.pressed or p2.button.a.pressed {
        timer = 0
    }
    if timer == 0 and text_idle() {
        show_hit = false
        phase = after
    }
}

fun draw_sprites() {
    draw_mech(0)
    draw_mech(1)
    if phase == P_MOVE {
        draw_square_cursor(cur_x, cur_y)
    }
    if phase == P_AIM {
        draw_plate_cursor(1 - actor, aim_x, aim_y)
    }
    if show_hit {
        draw_plate_hit(1 - actor, hit_x, hit_y)
    }
    draw_decals()
}

// ── Lock ────────────────────────────────────────────────

fun start_lock() {
    var any_human: bool = false
    var p: u8 = 0
    while p < 2 {
        lk_n[p] = 0
        lk_ready[p] = 0
        if is_cpu(p) {
            plan[p] = cpu_pick_plan(p)
            lk_ready[p] = 1
        } else {
            any_human = true
        }
        p += 1
    }
    if any_human {
        swap_background(2)
        on_card = true
        paint_card()
        phase = P_LOCK
    } else {
        msg_clear()
        msg_line(MSG_ROW1)
        msg_str(S_CPU_LOCK)
        wait_then(T_SHORT, P_REVEAL)
    }
}

fun run_lock() {
    var p: u8 = 0
    while p < 2 {
        if lk_ready[p] == 0 {
            var b: u8 = pad_pressed(p)
            var x: u8 = LOCK_STATUS_X[p] + 3
            if b == BTN_START {
                var code: u8 = lk_prev[p] * 6 + lk_last[p]
                if lk_n[p] >= 2 and code < NUM_PLANS and plan_legal(p, code) {
                    plan[p] = code
                    lk_ready[p] = 1
                    put_clear(x, LOCK_STATUS_ROW, 8)
                    put_str(x, LOCK_STATUS_ROW, S_READY)
                    play LockYes
                } else {
                    lk_n[p] = 0
                    put_tile(x, LOCK_STATUS_ROW, T_QUEST)
                    play LockNo
                }
            } else if b != B_NONE {
                lk_prev[p] = lk_last[p]
                lk_last[p] = b
                if lk_n[p] < 2 {
                    lk_n[p] += 1
                }
                if lk_n[p] == 1 {
                    put_tile(x, LOCK_STATUS_ROW, T_SPACE)
                }
            }
        }
        p += 1
    }
    if lk_ready[0] != 0 and lk_ready[1] != 0 {
        timer = 30
        phase = P_LOCK_DONE
    }
}

fun finish_lock() {
    if timer > 0 {
        timer -= 1
        return
    }
    swap_background(1)
    on_card = false
    paint_all()
    phase = P_REVEAL
}

fun reveal() {
    paint_plan(0, true)
    paint_plan(1, true)
    msg_clear()
    msg_line(MSG_ROW1)
    msg_str(S_REVEALED)
    cur_act = 0
    wait_then(T_LONG, P_NEXT_ACTION)
}

// ── Action order ────────────────────────────────────────

fun next_action() {
    while cur_act < NUM_ACTIONS {
        var bit: u8 = BIT[cur_act]
        var h0: bool = (PLAN_MASK[plan[0]] & bit) != 0
        var h1: bool = (PLAN_MASK[plan[1]] & bit) != 0
        if h0 and h1 {
            var r0: u8 = d6()
            var r1: u8 = d6()
            while r0 == r1 {
                r0 = d6()
                r1 = d6()
            }
            first = 0
            if r1 > r0 {
                first = 1
            }
            count = 2
            step = 0
            msg_clear()
            msg_line(MSG_ROW1)
            msg_str(ACTION_STR[cur_act])
            msg_who(first)
            msg_str(S_FIRST)
            msg_line(MSG_ROW2)
            msg_str(S_P1)
            msg_str(S_ROLL)
            msg_num(r0)
            msg_str(S_P2)
            msg_str(S_ROLL)
            msg_num(r1)
            wait_then(T_SHORT, P_DO)
            return
        }
        if h0 or h1 {
            first = 0
            if h1 {
                first = 1
            }
            count = 1
            step = 0
            phase = P_DO
            return
        }
        cur_act += 1
    }
    end_turn()
}

fun begin_action() {
    actor = first
    if step == 1 {
        actor = 1 - first
    }
    msg_clear()
    msg_line(MSG_ROW1)
    msg_who(actor)
    msg_str(ACTION_STR[cur_act])
    if cur_act == A_SHIELD {
        shield_up[actor] = 1
        paint_shield(actor)
        wait_then(T_SHORT, P_AFTER)
    } else if cur_act == A_STEP {
        begin_move(move_range(actor, STEP_RANGE))
    } else if cur_act == A_CHARGE {
        begin_move(move_range(actor, CHARGE_RANGE))
    } else if cur_act == A_RUSH {
        var r1: u8 = d6()
        var r2: u8 = d6()
        msg_str(S_ROLL)
        msg_num(r1)
        msg_num(r2)
        begin_move(move_range(actor, RUSH_TABLE[r1 + r2]))
    } else {
        var w: u8 = pick_ranged(actor, mech_dist())
        if w == NO_WEAPON {
            msg_line(MSG_ROW2)
            msg_str(S_NO_GUN)
            wait_then(T_SHORT, P_AFTER)
        } else {
            begin_aim(w, true)
        }
    }
}

// ── Movement ────────────────────────────────────────────

fun begin_move(range: u8) {
    org_x = mech_x[actor]
    org_y = mech_y[actor]
    cur_x = org_x
    cur_y = org_y
    mrange = range
    msg_line(MSG_ROW2)
    msg_str(S_RANGE)
    msg_num(range)
    if range == 0 {
        finish_move()
        return
    }
    if is_cpu(actor) {
        cpu_move_begin(actor, range, cur_act)
        cpu_done = false
        cpu_delay = 0
    } else {
        msg_str(S_PICK_SQ)
    }
    phase = P_MOVE
}

fun run_move() {
    if is_cpu(actor) {
        if not cpu_done {
            cpu_done = cpu_move_step(actor)
            return
        }
        cpu_delay += 1
        if cur_x == cpu_bx and cur_y == cpu_by {
            if cpu_delay >= 20 {
                finish_move()
            }
            return
        }
        if cpu_delay >= 8 {
            cpu_delay = 0
            step_toward(cur_x, cur_y, cpu_bx, cpu_by)
            cur_x = res_a
            cur_y = res_b
        }
        return
    }
    var b: u8 = pad_pressed(actor)
    if b == BTN_A {
        if (cur_x == org_x and cur_y == org_y) or square_open(actor, cur_x, cur_y) {
            finish_move()
        }
        return
    }
    if b == BTN_B {
        cur_x = org_x
        cur_y = org_y
        return
    }
    res_a = cur_x
    res_b = cur_y
    if nudge(b, BOARD_N) {
        if cheb(res_a, res_b, org_x, org_y) <= mrange {
            cur_x = res_a
            cur_y = res_b
        }
    }
}

// Step, Rush, and Charge each have their own effect. Anything
// else that reaches a square change stays silent.
fun play_move() {
    if cur_act == A_STEP {
        play MoveStep
    } else if cur_act == A_RUSH {
        play MoveRush
    } else if cur_act == A_CHARGE {
        play MoveCharge
    }
}

fun play_weapon(w: u8) {
    if w == W_LANCE {
        play Lance
    } else if w == W_CANNON {
        play Cannon
    } else if w == W_POD {
        play Missile
        play MissileWash
    } else if w == W_SWORD {
        play Sword
    } else if w == W_HAMMER {
        play Hammer
    }
}

fun finish_move() {
    msg_line(MSG_ROW2)
    if cur_x == org_x and cur_y == org_y {
        msg_who(actor)
        msg_str(S_STAY)
    } else {
        mech_x[actor] = cur_x
        mech_y[actor] = cur_y
        play_move()
        msg_who(actor)
        msg_str(S_MOVES)
        msg_num(cheb(cur_x, cur_y, org_x, org_y))
        msg_str(S_SQ)
    }
    paint_range(mech_dist(), mech_cover())
    if cur_act != A_CHARGE {
        wait_then(T_SHORT, P_AFTER)
        return
    }
    if mech_dist() != 1 {
        msg_str(S_NO_CONTACT)
        wait_then(T_SHORT, P_AFTER)
        return
    }
    if not intact(actor, L_ARMR) {
        msg_line(MSG_ROW2)
        msg_str(S_NO_ARM)
        wait_then(T_SHORT, P_AFTER)
        return
    }
    wait_then(T_SHORT, P_MELEE)
}

// ── Aim and resolve ─────────────────────────────────────

fun begin_aim(w: u8, is_ranged: bool) {
    wpn = w
    aim_ranged = is_ranged
    aim_x = 2
    aim_y = 3
    msg_clear()
    msg_line(MSG_ROW1)
    msg_who(actor)
    msg_str(ACTION_STR[cur_act])
    msg_str(W_STR[w])
    msg_line(MSG_ROW2)
    msg_str(S_AIM_AT)
    msg_who(1 - actor)
    if is_cpu(actor) {
        cpu_aim_begin(actor, w)
        cpu_done = false
        cpu_delay = 0
    }
    phase = P_AIM
}

fun run_aim() {
    if is_cpu(actor) {
        if not cpu_done {
            cpu_done = cpu_aim_step(SCATTER_OF[cur_act])
            return
        }
        cpu_delay += 1
        if aim_x == cpu_bx and aim_y == cpu_by {
            if cpu_delay >= 24 {
                resolve_shot()
            }
            return
        }
        if cpu_delay >= 6 {
            cpu_delay = 0
            step_toward(aim_x, aim_y, cpu_bx, cpu_by)
            aim_x = res_a
            aim_y = res_b
        }
        return
    }
    var b: u8 = pad_pressed(actor)
    if b == BTN_A {
        resolve_shot()
        return
    }
    res_a = aim_x
    res_b = aim_y
    if nudge(b, 6) {
        aim_x = res_a
        aim_y = res_b
    }
}

fun resolve_shot() {
    play_weapon(wpn)
    var target: u8 = 1 - actor
    var s: u8 = SCATTER_OF[cur_act] * 6
    var fx: u8 = d6()
    var fy: u8 = d6()
    var tx: u8 = aim_x + SCATTER[s + fx - 1]
    var ty: u8 = aim_y + SCATTER[s + fy - 1]
    var loc: u8 = L_NONE
    if tx >= 2 and tx < 8 and ty >= 2 and ty < 8 {
        hit_x = tx - 2
        hit_y = ty - 2
        loc = PLATE[hit_y * 6 + hit_x]
        show_hit = true
    }
    msg_clear()
    msg_line(MSG_ROW1)
    msg_str(S_DICE)
    msg_num(fx)
    msg_num(fy)
    msg_str(LOC_STR[loc])
    msg_line(MSG_ROW2)
    if loc == L_NONE {
        msg_str(S_MISS)
    } else if not intact(target, loc) {
        msg_str(S_ALREADY)
    } else {
        var need: u8 = save_need(target, wpn, aim_ranged, mech_cover())
        var r: u8 = d6()
        msg_str(S_SAVE)
        msg_num(r)
        msg_str(S_NEED)
        msg_num(need)
        if r >= need {
            msg_str(S_SAVED)
        } else {
            if apply_damage(target, loc, W_DMG[wpn]) {
                msg_str(S_CRITICAL)
            } else {
                msg_str(S_HIT)
            }
            paint_plate(target)
            paint_crits(target)
        }
    }
    wait_then(T_LONG, P_AFTER)
}

fun after_action() {
    if crits[0] >= LOSS_CRITS or crits[1] >= LOSS_CRITS {
        game_over()
        return
    }
    step += 1
    if step < count {
        phase = P_DO
        return
    }
    cur_act += 1
    phase = P_NEXT_ACTION
}

// ── Turn end and result ─────────────────────────────────

fun end_turn() {
    turn += 1
    var p: u8 = 0
    while p < 2 {
        shield_up[p] = 0
        paint_shield(p)
        paint_plan(p, false)
        p += 1
    }
    if turn > MAX_TURNS {
        game_over()
        return
    }
    paint_turn()
    msg_clear()
    wait_then(20, P_LOCK_START)
}

fun game_over() {
    stop_music
    var w: u8 = decide_winner()
    msg_clear()
    msg_line(MSG_ROW1)
    if crits[0] >= LOSS_CRITS or crits[1] >= LOSS_CRITS {
        if crits[0] >= LOSS_CRITS {
            msg_str(S_P1)
            msg_str(S_WRECKED)
        }
        if crits[1] >= LOSS_CRITS {
            msg_str(S_P2)
            msg_str(S_WRECKED)
        }
    } else {
        msg_str(S_TIME_UP)
    }
    msg_line(MSG_ROW2)
    if w == 2 {
        msg_str(S_DRAW)
    } else {
        msg_who(w)
        msg_str(S_WINS)
    }
    msg_str(S_PRESS_START)
    over_timer = 0
    phase = P_OVER
}

// True when the match should return to Title.
fun run_over() -> bool {
    if over_timer < 255 {
        over_timer += 1
    }
    if p1.button.start.pressed or p2.button.start.pressed {
        return true
    }
    return demo and over_timer == 255
}

state Battle {
    on enter {
        start_music March
        reset_mechs()
        phase = P_WAIT
        after = P_LOCK_START
        timer = 40
        on_card = false
        show_hit = false
        swap_background(1)
        paint_all()
        msg_clear()
    }

    on frame {
        tick_unblank()
        flush_text()
        anim += 1
        match phase {
            P_WAIT => { run_wait() }
            P_LOCK_START => { start_lock() }
            P_LOCK => { run_lock() }
            P_LOCK_DONE => { finish_lock() }
            P_REVEAL => { reveal() }
            P_NEXT_ACTION => { next_action() }
            P_DO => { begin_action() }
            P_MOVE => { run_move() }
            P_MELEE => { begin_aim(loadout[actor * 2 + 1], false) }
            P_AIM => { run_aim() }
            P_AFTER => { after_action() }
            P_OVER => {
                if run_over() {
                    transition Title
                }
            }
            _ => {}
        }
        if not on_card {
            draw_sprites()
        }
    }
}
