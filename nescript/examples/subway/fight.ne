// Fights in the River City Ransom style. B punches, A kicks, A and B
// together jump, and A or B in the air is a jump kick. Tapping a
// direction twice runs; an attack out of a run hits harder.
//
// A hit needs the attacker to face the target, the target to be in
// the move's reach and within DEPTH pixels of the attacker's floor
// line, and the move's height band to overlap the target's body, so
// a jump clears a kick. Three hits in a row, a jump kick, or a hit in
// the air knocks the target down; anything else staggers it. A hit
// from behind does half again as much damage.
//
// Each side of Alex holds one attacker at a time; the rest of the
// gang hangs back at HOVER until a side is free.

const M_PUNCH: u8 = 0
const M_KICK: u8 = 1
const M_JUMPKICK: u8 = 2
const MV_DMG: u8[3] = [4, 6, 8]
// Farthest x distance between the two fighters' sprites.
const MV_REACH: u8[3] = [20, 24, 22]
// Height band of the strike, in pixels up from the attacker's feet.
const MV_LO: u8[3] = [14, 4, 0]
const MV_HI: u8[3] = [26, 18, 14]
// Where the hit spark shows, down from the target's top.
const MV_SPARK: u8[3] = [8, 18, 12]

const PUNCH_LEN: u8 = 16
const PUNCH_HIT: u8 = 4
const KICK_LEN: u8 = 22
const KICK_HIT: u8 = 7
// Enemies take this much longer to recover from their own swings.
const EN_RECOVER: u8 = 8
const HURT_LEN: u8 = 16
const DOWN_LEN: u8 = 60
const KO_LEN: u8 = 48
const INV_LEN: u8 = 60
const JUMP_LEN: u8 = 30
const JUMP_Z: u8[30] = [0, 4, 7, 10, 13, 16, 18, 20, 22, 24, 25, 26, 27, 28, 28, 28, 28, 28, 27, 26, 25, 24, 22, 20, 18, 16, 13, 10, 7, 4]
const DEPTH: u8 = 5
const BODY_H: u8 = 30
const COMBO_FRAMES: u8 = 45
const TAP_FRAMES: u8 = 12
// An attacker closes to ENGAGE pixels from Alex; the others wait at
// HOVER, a little up or down the platform.
const ENGAGE: u8 = 18
const HOVER: u8 = 52
const HOVER_DY: u8 = 20

const PL_POW: u8 = 1
const PL_GUARD: u8 = 1
const DASH_POW: u8 = 2

// Gang members: a slow, weak one and a quick, tough one. Both wear
// Alex's palette; the route bullets hold every other sprite color.
const EK_HP: u8[2] = [20, 30]
const EK_POW: u8[2] = [0, 2]
const EK_GUARD: u8[2] = [0, 1]
// Walks only every other frame when 1.
const EK_SLOW: u8[2] = [1, 0]
const EK_COOL: u8[2] = [70, 45]
// Cents dropped.
const EK_CASH: u8[2] = [50, 95]

// End any fight: a new screen starts empty.
fun fight_clear() {
    var i: u8 = 0
    while i < MAX_EN {
        en_act[i] = A_GONE
        i += 1
    }
    pl_act = A_IDLE
    pl_t = 0
    pl_z = 0
    pl_kb = 0
    pl_run = false
    pl_combo = 0
    spark_t = 0
}

// Set the floor for a screen (0 platform, 1 car) and repaint the HUD
// row on that screen's tile page.
fun fight_enter(scene: u8) {
    if scene == 0 {
        fb_x0 = 0
        fb_y0 = PLAYER_MIN_Y
        fb_y1 = PLAYER_MAX_Y
        hud_bar0 = T_BAR0
    } else {
        fb_x0 = 8
        fb_y0 = RIDE_MIN_Y
        fb_y1 = RIDE_MAX_Y
        hud_bar0 = I_BAR0
    }
    fb_x1 = 232
    hud_hp = 255
    hud_cd = 255
    hud_cc = 255
}

// Five times in eight, two to four of the gang walk in from the ends
// of the screen, one after another.
fun fight_maybe() {
    if fight_safe {
        return
    }
    var r: u8 = rand8()
    if r >= 160 {
        return
    }
    var n: u8 = 2 + (r & 1) + ((r >> 1) & 1)
    var i: u8 = 0
    while i < n {
        var k: u8 = rand8() & 1
        en_act[i] = A_WAIT
        en_t[i] = 30 + (i << 5)
        en_kind[i] = k
        en_hp[i] = EK_HP[k]
        if (i & 1) == 0 {
            en_x[i] = fb_x0
        } else {
            en_x[i] = fb_x1
        }
        var y: u8 = fb_y0 + (rand8() & 63)
        if y > fb_y1 {
            y = fb_y1
        }
        en_y[i] = y
        en_cool[i] = 30
        en_combo[i] = 0
        en_ct[i] = 0
        en_kb[i] = 0
        en_walk[i] = 0
        en_tok[i] = 0
        i += 1
    }
}

fun fight_on() -> bool {
    var i: u8 = 0
    while i < MAX_EN {
        if en_act[i] != A_GONE {
            return true
        }
        i += 1
    }
    return false
}

fun tap(d: u8) {
    if tap_dir == d and tap_t > 0 and pl_act == A_IDLE {
        pl_run = true
    }
    tap_dir = d
    tap_t = TAP_FRAMES
}

fun start_jump() {
    pl_act = A_JUMP
    pl_t = 0
    pl_jk = false
    pl_hit = false
    pl_dash = pl_run
}

fun start_attack(a: u8) {
    pl_act = a
    pl_t = 0
    pl_hit = false
    pl_dash = pl_run
    pl_run = false
}

// Read the fight buttons and set pl_step for the states' walking code.
fun fight_input() {
    if tap_t > 0 {
        tap_t -= 1
    }
    if button.left.pressed {
        tap(1)
    }
    if button.right.pressed {
        tap(2)
    }
    if pl_run {
        if tap_dir == 1 and not button.left {
            pl_run = false
        }
        if tap_dir == 2 and not button.right {
            pl_run = false
        }
    }
    var both: bool = button.a and button.b
    var fresh: bool = button.a.pressed or button.b.pressed
    if pl_act == A_IDLE {
        if both and fresh {
            start_jump()
        } else if button.b.pressed {
            start_attack(A_PUNCH)
        } else if button.a.pressed {
            start_attack(A_KICK)
        }
    } else if pl_act == A_PUNCH or pl_act == A_KICK {
        // The other button a frame or two late still makes a jump.
        if pl_t < 3 and both {
            start_jump()
        }
    } else if pl_act == A_JUMP {
        if fresh and not pl_jk {
            pl_jk = true
            pl_hit = false
        }
    }
    pl_step = 0
    if pl_act == A_IDLE or pl_act == A_JUMP {
        pl_step = 1
        if pl_run or (pl_act == A_JUMP and pl_dash) {
            pl_step = 2
        }
    }
}

// Knockback: two pixels a frame, kept on the floor.
fun push_x(x: u8, right: bool) -> u8 {
    if right {
        if x < fb_x1 - 2 {
            return x + 2
        }
        return fb_x1
    }
    if x > fb_x0 + 2 {
        return x - 2
    }
    return fb_x0
}

fun absdiff(a: u8, b: u8) -> u8 {
    if a > b {
        return a - b
    }
    return b - a
}

// Does move mv from a fighter at (ax, ay), az up, facing right when
// aright, land on a fighter at (tx, ty), tz up?
fun connects(ax: u8, ay: u8, az: u8, aright: bool, mv: u8, tx: u8, ty: u8, tz: u8) -> bool {
    var dy: u8 = 0
    if ay > ty {
        dy = ay - ty
    } else {
        dy = ty - ay
    }
    if dy > DEPTH {
        return false
    }
    var d: u8 = 0
    if aright {
        if tx < ax + 4 {
            return false
        }
        d = tx - ax
    } else {
        if ax < tx + 4 {
            return false
        }
        d = ax - tx
    }
    if d > MV_REACH[mv] {
        return false
    }
    var lo: u8 = az + MV_LO[mv]
    var hi: u8 = az + MV_HI[mv]
    return lo <= tz + BODY_H and hi >= tz
}

// The target faces away from an attacker at ax.
fun from_behind(tright: bool, tx: u8, ax: u8) -> bool {
    if tright {
        return ax < tx
    }
    return ax > tx
}

fun damage(mv: u8, pow: u8, guard: u8, back: bool) -> u8 {
    var d: u8 = MV_DMG[mv] + pow
    if back {
        d += d >> 1
    }
    if d > guard {
        return d - guard
    }
    return 1
}

fun spark_at(x: u8, y: u8) {
    spark_x = x
    spark_y = y
    spark_t = 6
}

fun cash_add(c: u8) {
    cash_c += c
    if cash_c >= 100 {
        cash_c -= 100
        if cash_d < 99 {
            cash_d += 1
        } else {
            cash_c = 99
        }
    }
}

// Standing and able to fight back.
fun en_up(i: u8) -> bool {
    var a: u8 = en_act[i]
    return a == A_IDLE or a == A_PUNCH or a == A_KICK or a == A_HURT
}

fun player_open() -> bool {
    return pl_act != A_DOWN and pl_inv == 0
}

fun enemy_hurt(i: u8, d: u8, mv: u8, right: bool) {
    if en_hp[i] > d {
        en_hp[i] -= d
    } else {
        en_hp[i] = 0
    }
    en_combo[i] += 1
    en_ct[i] = COMBO_FRAMES
    en_t[i] = 0
    en_kbr[i] = 0
    if right {
        en_kbr[i] = 1
    }
    if en_hp[i] == 0 or en_combo[i] >= 3 or mv == M_JUMPKICK {
        en_act[i] = A_DOWN
        en_kb[i] = 12
        en_combo[i] = 0
        play Smack
    } else {
        en_act[i] = A_HURT
        en_kb[i] = 4
        play Punch
    }
    spark_at(en_x[i] + 4, en_y[i] + MV_SPARK[mv])
}

fun pl_attack(mv: u8) {
    var pow: u8 = PL_POW
    if pl_dash {
        pow += DASH_POW
    }
    var i: u8 = 0
    while i < MAX_EN {
        if en_up(i) {
            var ex: u8 = en_x[i]
            if connects(pl_x, pl_y, pl_z, pl_flip, mv, ex, en_y[i], 0) {
                var back: bool = from_behind(en_flip[i] == 1, ex, pl_x)
                enemy_hurt(i, damage(mv, pow, EK_GUARD[en_kind[i]], back), mv, pl_x < ex)
                pl_hit = true
            }
        }
        i += 1
    }
}

fun player_hurt(d: u8, mv: u8, right: bool) {
    if pl_hp > d {
        pl_hp -= d
    } else {
        pl_hp = 0
    }
    pl_combo += 1
    pl_ct = COMBO_FRAMES
    pl_run = false
    pl_t = 0
    pl_kbr = right
    var y: u8 = pl_y - pl_z
    if pl_hp == 0 or pl_combo >= 3 or pl_z > 0 {
        pl_act = A_DOWN
        pl_kb = 12
        pl_combo = 0
        pl_z = 0
        play Smack
    } else {
        pl_act = A_HURT
        pl_kb = 4
        play Punch
    }
    spark_at(pl_x + 4, y + MV_SPARK[mv])
}

fun en_attack(i: u8, mv: u8) {
    if not player_open() {
        return
    }
    var ex: u8 = en_x[i]
    if connects(ex, en_y[i], 0, en_flip[i] == 1, mv, pl_x, pl_y, pl_z) {
        var back: bool = from_behind(pl_flip, pl_x, ex)
        player_hurt(damage(mv, EK_POW[en_kind[i]], PL_GUARD, back), mv, ex < pl_x)
    }
}

// Back on his feet with full stamina and half his cash; the gang
// that beat him walks off.
fun player_revive() {
    pl_hp = PL_MAX_HP
    var c: u8 = cash_c >> 1
    if (cash_d & 1) != 0 {
        c += 50
    }
    cash_d = cash_d >> 1
    cash_c = c
    var i: u8 = 0
    while i < MAX_EN {
        en_act[i] = A_GONE
        i += 1
    }
}

fun player_tick() {
    if pl_inv > 0 {
        pl_inv -= 1
    }
    if pl_ct > 0 {
        pl_ct -= 1
    } else {
        pl_combo = 0
    }
    if pl_kb > 0 {
        pl_kb -= 1
        pl_x = push_x(pl_x, pl_kbr)
    }
    if pl_act == A_IDLE {
        pl_t = 0
        if pl_moving {
            pl_walk += 1
        } else {
            pl_walk = 0
        }
        return
    }
    pl_t += 1
    if pl_act == A_PUNCH {
        if pl_t == PUNCH_HIT {
            pl_attack(M_PUNCH)
        }
        if pl_t >= PUNCH_LEN {
            pl_act = A_IDLE
        }
    } else if pl_act == A_KICK {
        if pl_t == KICK_HIT {
            pl_attack(M_KICK)
        }
        if pl_t >= KICK_LEN {
            pl_act = A_IDLE
        }
    } else if pl_act == A_JUMP {
        if pl_t >= JUMP_LEN {
            pl_act = A_IDLE
            pl_z = 0
            pl_dash = false
        } else {
            pl_z = JUMP_Z[pl_t]
            if pl_jk and not pl_hit {
                pl_attack(M_JUMPKICK)
            }
        }
    } else if pl_act == A_HURT {
        if pl_t >= HURT_LEN {
            pl_act = A_IDLE
        }
    } else if pl_act == A_DOWN {
        if pl_t >= DOWN_LEN {
            if pl_hp == 0 {
                player_revive()
            }
            pl_act = A_IDLE
            pl_inv = INV_LEN
        }
    }
}

// Give each side of Alex to the first standing enemy on it, then any
// enemy left over takes a side nobody holds.
fun assign_tokens() {
    var l: u8 = 255
    var r: u8 = 255
    var i: u8 = 0
    while i < MAX_EN {
        en_tok[i] = 0
        if en_up(i) {
            if en_x[i] < pl_x {
                if l == 255 {
                    l = i
                }
            } else if r == 255 {
                r = i
            }
        }
        i += 1
    }
    i = 0
    while i < MAX_EN {
        if en_up(i) and i != l and i != r {
            if l == 255 {
                l = i
            } else if r == 255 {
                r = i
            }
        }
        i += 1
    }
    if l != 255 {
        en_tok[l] = 1
    }
    if r != 255 {
        en_tok[r] = 2
    }
}

fun enemy_move(i: u8) {
    var ex: u8 = en_x[i]
    var ey: u8 = en_y[i]
    if pl_x > ex {
        en_flip[i] = 1
    } else {
        en_flip[i] = 0
    }
    var tok: u8 = en_tok[i]
    var left: bool = ex < pl_x
    if tok == 1 {
        left = true
    } else if tok == 2 {
        left = false
    }
    var gap: u8 = HOVER
    var ty: u8 = pl_y
    if tok != 0 {
        gap = ENGAGE
    } else if (i & 1) == 0 {
        if ty > fb_y0 + HOVER_DY {
            ty -= HOVER_DY
        } else {
            ty = fb_y0
        }
    } else {
        if ty < fb_y1 - HOVER_DY {
            ty += HOVER_DY
        } else {
            ty = fb_y1
        }
    }
    var tx: u8 = 0
    if left {
        if pl_x > fb_x0 + gap {
            tx = pl_x - gap
        } else {
            tx = fb_x0
        }
    } else {
        if pl_x < fb_x1 - gap {
            tx = pl_x + gap
        } else {
            tx = fb_x1
        }
    }
    var moved: bool = false
    if (frame_count & EK_SLOW[en_kind[i]]) == 0 {
        if ex < tx {
            en_x[i] = ex + 1
            moved = true
        } else if ex > tx {
            en_x[i] = ex - 1
            moved = true
        }
        if ey < ty {
            en_y[i] = ey + 1
            moved = true
        } else if ey > ty {
            en_y[i] = ey - 1
            moved = true
        }
    }
    if moved {
        en_walk[i] += 1
    } else if (frame_count & EK_SLOW[en_kind[i]]) == 0 {
        en_walk[i] = 0
    }
    if tok == 0 or en_cool[i] > 0 or not player_open() {
        return
    }
    var dx: u8 = absdiff(en_x[i], pl_x)
    if dx >= 12 and dx <= 22 and absdiff(en_y[i], pl_y) <= 3 {
        if (rand8() & 1) == 0 {
            en_act[i] = A_PUNCH
        } else {
            en_act[i] = A_KICK
        }
        en_t[i] = 0
        en_cool[i] = EK_COOL[en_kind[i]]
    }
}

fun enemy_tick(i: u8) {
    var a: u8 = en_act[i]
    if a == A_WAIT {
        if en_t[i] > 0 {
            en_t[i] -= 1
        } else {
            en_act[i] = A_IDLE
        }
        return
    }
    if en_kb[i] > 0 {
        en_kb[i] -= 1
        en_x[i] = push_x(en_x[i], en_kbr[i] == 1)
    }
    if en_ct[i] > 0 {
        en_ct[i] -= 1
    } else {
        en_combo[i] = 0
    }
    if en_cool[i] > 0 {
        en_cool[i] -= 1
    }
    if a == A_IDLE {
        enemy_move(i)
        return
    }
    en_t[i] += 1
    var t: u8 = en_t[i]
    if a == A_PUNCH {
        if t == PUNCH_HIT {
            en_attack(i, M_PUNCH)
        }
        if t >= PUNCH_LEN + EN_RECOVER {
            en_act[i] = A_IDLE
        }
    } else if a == A_KICK {
        if t == KICK_HIT {
            en_attack(i, M_KICK)
        }
        if t >= KICK_LEN + EN_RECOVER {
            en_act[i] = A_IDLE
        }
    } else if a == A_HURT {
        if t >= HURT_LEN {
            en_act[i] = A_IDLE
            if en_cool[i] < 20 {
                en_cool[i] = 20
            }
        }
    } else if a == A_DOWN {
        if t >= DOWN_LEN {
            en_t[i] = 0
            if en_hp[i] == 0 {
                en_act[i] = A_KO
                cash_add(EK_CASH[en_kind[i]])
                play Coin
            } else {
                en_act[i] = A_IDLE
                en_cool[i] = 30
            }
        }
    } else if a == A_KO {
        if t >= KO_LEN {
            en_act[i] = A_GONE
        }
    }
}

// One frame of the fight, after the state has walked Alex.
fun fight_update() {
    player_tick()
    assign_tokens()
    var i: u8 = 0
    while i < MAX_EN {
        if en_act[i] != A_GONE {
            enemy_tick(i)
        }
        i += 1
    }
    if spark_t > 0 {
        spark_t -= 1
    }
}

// 16x32 in rows of two tiles; flipped, each row swaps its tiles.
fun draw_tall(x: u8, y: u8, t: u8, a: u8) {
    var l: u8 = 0
    var r: u8 = 1
    if (a & 0x40) != 0 {
        l = 1
        r = 0
    }
    var row: u8 = 0
    var tt: u8 = t
    var yy: u8 = y
    while row < 4 {
        draw SpriteTiles at: (x, yy) frame: tt + l attr: a
        draw SpriteTiles at: (x + 8, yy) frame: tt + r attr: a
        tt += 2
        yy += 8
        row += 1
    }
}

// 32x16 lying on the floor, centered on a standing sprite's footprint:
// the bottom 16 rows of it, 8 pixels wider each side.
fun draw_flat(x: u8, y: u8, t: u8, a: u8) {
    var lx: u8 = 0
    if x >= 8 {
        lx = x - 8
    }
    var flip: bool = (a & 0x40) != 0
    var c: u8 = 0
    while c < 4 {
        var cx: u8 = lx + (c << 3)
        if flip {
            cx = lx + ((3 - c) << 3)
        }
        draw SpriteTiles at: (cx, y + 16) frame: t + c attr: a
        draw SpriteTiles at: (cx, y + 24) frame: t + 4 + c attr: a
        c += 1
    }
}

fun draw_alex(off: u8) {
    if pl_inv > 0 and (frame_count & 2) != 0 {
        return
    }
    var x: u8 = pl_x - off
    var y: u8 = pl_y - pl_z
    var a: u8 = 0
    if pl_flip {
        a = 0x40
    }
    if pl_act == A_DOWN {
        draw_flat(x, y, S_P_DOWN, a)
        var jx: u8 = 0
        if x >= 8 {
            jx = x - 8
        }
        if pl_flip {
            jx += 24
        }
        draw SpriteTiles at: (jx, y + 16) frame: S_J_DOWN attr: a | 2
        draw SpriteTiles at: (jx, y + 24) frame: S_J_DOWN + 1 attr: a | 2
        return
    }
    var t: u8 = S_PLAYER0
    if pl_act == A_IDLE {
        var phase: u8 = (pl_walk >> 3) & 3
        if phase == 1 {
            t = S_PLAYER1
        } else if phase == 3 {
            t = S_PLAYER2
        }
    } else if pl_act == A_PUNCH {
        if pl_t >= 2 and pl_t < 10 {
            t = S_P_PUNCH
        }
    } else if pl_act == A_KICK {
        if pl_t >= 3 and pl_t < 15 {
            t = S_P_KICK
        }
    } else if pl_act == A_JUMP {
        t = S_P_JUMP
        if pl_jk {
            t = S_P_KICK
        }
    } else if pl_act == A_HURT {
        t = S_P_HURT
    }
    draw_tall(x, y, t, a)
    // The denim tiles always follow the body's 8 tiles.
    var l: u8 = 0
    var r: u8 = 1
    if pl_flip {
        l = 1
        r = 0
    }
    draw SpriteTiles at: (x, y + 24) frame: t + 8 + l attr: a | 2
    draw SpriteTiles at: (x + 8, y + 24) frame: t + 8 + r attr: a | 2
}

fun draw_enemy(i: u8, off: u8) {
    var act: u8 = en_act[i]
    if act == A_KO and (frame_count & 4) != 0 {
        return
    }
    var x: u8 = en_x[i] - off
    var y: u8 = en_y[i]
    var a: u8 = 0
    if en_flip[i] == 1 {
        a = 0x40
    }
    if act == A_DOWN or act == A_KO {
        draw_flat(x, y, S_E_DOWN, a)
        return
    }
    var t: u8 = S_E_STAND
    var et: u8 = en_t[i]
    if act == A_IDLE {
        var phase: u8 = (en_walk[i] >> 3) & 3
        if phase == 1 {
            t = S_E_WALK1
        } else if phase == 3 {
            t = S_E_WALK2
        }
    } else if act == A_PUNCH {
        if et >= 2 and et < 10 {
            t = S_E_PUNCH
        }
    } else if act == A_KICK {
        if et >= 3 and et < 15 {
            t = S_E_KICK
        }
    } else if act == A_HURT {
        t = S_E_HURT
    }
    draw_tall(x, y, t, a)
}

// Draw the fighters nearest first, so they cover the ones behind. With
// four or more on screen, or one lying down across the width of two,
// a scanline can hold more than 8 sprites, and the PPU drops whatever
// comes last; starting the order one fighter later each frame makes
// the drop a flicker shared by everyone. off is the car's sway.
fun fight_draw(off: u8) {
    var n: u8 = 1
    var crowd: bool = pl_act == A_DOWN
    fd_id[0] = 0
    fd_key[0] = pl_y
    var i: u8 = 0
    while i < MAX_EN {
        var a: u8 = en_act[i]
        if a != A_GONE and a != A_WAIT {
            if a == A_DOWN or a == A_KO {
                crowd = true
            }
            // Insertion by floor line, largest (nearest) first.
            var k: u8 = n
            var y: u8 = en_y[i]
            while k > 0 and fd_key[k - 1] < y {
                fd_id[k] = fd_id[k - 1]
                fd_key[k] = fd_key[k - 1]
                k -= 1
            }
            fd_id[k] = i + 1
            fd_key[k] = y
            n += 1
        }
        i += 1
    }
    var s: u8 = 0
    if n >= 4 or (crowd and n >= 2) {
        fd_rot += 1
        if fd_rot >= n {
            fd_rot = 0
        }
        s = fd_rot
    }
    var j: u8 = 0
    while j < n {
        var id: u8 = fd_id[s]
        if id == 0 {
            draw_alex(off)
        } else {
            draw_enemy(id - 1, off)
        }
        s += 1
        if s >= n {
            s = 0
        }
        j += 1
    }
    if spark_t > 0 {
        draw SpriteTiles at: (spark_x - off, spark_y) frame: S_SPARK attr: 0
    }
}

// Repaint what changed on HUD row 4: the stamina bar (8 cells), or
// else the cash, never both in one frame.
fun fight_hud() {
    if pl_hp != hud_hp {
        hud_hp = pl_hp
        var left: u8 = pl_hp
        var c: u8 = 0
        while c < 8 {
            var f: u8 = 8
            if left < 8 {
                f = left
            }
            nt_set(HUD_BAR_X + c, HUD_ROW, hud_bar0 + f)
            left -= f
            c += 1
        }
        return
    }
    if cash_d == hud_cd and cash_c == hud_cc {
        return
    }
    hud_cd = cash_d
    hud_cc = cash_c
    nt_set(HUD_CASH_X, HUD_ROW, hud_bar0 + 9)
    var tens: u8 = 0
    var v: u8 = cash_d
    while v >= 10 {
        v -= 10
        tens += 1
    }
    var tt: u8 = FONT_BASE
    if tens > 0 {
        tt = FONT_BASE + 53 + tens
    }
    nt_set(HUD_CASH_X + 1, HUD_ROW, tt)
    nt_set(HUD_CASH_X + 2, HUD_ROW, FONT_BASE + 53 + v)
    nt_set(HUD_CASH_X + 3, HUD_ROW, FONT_BASE + 64)
    tens = 0
    v = cash_c
    while v >= 10 {
        v -= 10
        tens += 1
    }
    nt_set(HUD_CASH_X + 4, HUD_ROW, FONT_BASE + 53 + tens)
    nt_set(HUD_CASH_X + 5, HUD_ROW, FONT_BASE + 53 + v)
}
