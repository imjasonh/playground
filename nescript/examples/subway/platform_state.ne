// The platform: a side view across the track. Trains arrive, dwell,
// and leave on the schedule, sliding through the track band (rows
// 10-17) while the wall, HUD, and platform stay put. See band.ne for
// how the band scrolls.
//
// Controls: left and right walk, up and down step toward or away from
// the edge. Up at an open door boards the train. A on the stairs at
// the right crosses to the other platform. Walking off the left end
// takes the passage to the next station in the complex. Hold B to
// wait faster while no train is in.

const BAND_TOP: u8 = 80
const BAND_BOTTOM: u8 = 144

// Camera positions in band pixels. A train stops with its third car
// exactly on screen.
const CAM_STOP: u16 = 1040
const DEPART_DIST: u16 = 1024

// Ring column of screen column 0 when the train is stopped, minus 32
// (CAM_STOP / 8 = 130, 130 & 63 = 2): every door and sign cell of the
// stopped car is in nametable 0 at screen column + 2.
const STOP_RING: u8 = 2

// Train presence on this platform.
const TP_NONE: u8 = 0
const TP_ARRIVING: u8 = 1
const TP_STOPPED: u8 = 2
const TP_LEAVING: u8 = 3

// Doors open DOOR_OPEN frames into the dwell tick and close when
// DOOR_CLOSE frames are left.
const DOOR_OPEN: u8 = 210
const DOOR_CLOSE: u8 = 36

const PLAYER_MIN_Y: u8 = 128
const PLAYER_MAX_Y: u8 = 198
const STAIRS_X: u8 = 206

var cam: u16 = 0
var stream_col: u16 = 32
var tp: u8 = TP_NONE
var tp_p: u8 = 0
var tp_k: u8 = 0
var tp_mul: u8 = 1
var tp_dist: u16 = 0
var doors_open: bool = false
var doors_want: bool = false
var restore_col: u8 = 64
var hud_chunk: u8 = 0
var arr_n: u8 = 0
var arr_route: u8[3]
var arr_slot: u8[3]

// Per-frame scratch for the train lookup.
var best_w: u8 = 0
var best_i: u8 = 0

var patterns_ready: bool = false
var a_held: bool = false

state Platform {
    var px: u8 = 120
    var py: u8 = 160
    var flip: bool = false
    var walk: u8 = 0

    on enter {
        top_y = 0
        if not patterns_ready {
            reset_patterns()
            patterns_ready = true
        }
        if resume {
            resume = false
            px = save_px
            py = save_py
            flip = save_flip
        } else if on_train {
            // Stepping off: stand at the door the player used.
            px = door_px
            py = PLAYER_MIN_Y
        }
        on_train = false
        platform_setup()
    }

    on frame {
        frame_top()
        frame_count += 1
        if button.start.pressed {
            save_px = px
            save_py = py
            save_flip = flip
            pause_from = 0
            transition PauseMap
        }

        var speed: u8 = 1
        if button.b and tp == TP_NONE {
            speed = 8
        }
        clock_step(speed)
        if ticked {
            hud_chunk = 1
        }

        find_train()
        if hud_chunk == 0 {
            cache_sign()
        }
        update_cam()
        band_x = cam as u8
        band_ctrl = CTRL_BASE | ((cam >> 8) as u8 & 1)

        var budget: u8 = stream_band()
        if budget > 0 {
            run_jobs()
        }
        if hud_chunk > 0 {
            hud_arrivals()
        }

        // Walk.
        var moving: bool = false
        if button.right and px < 232 {
            px += 1
            flip = false
            moving = true
        }
        if button.left {
            if px > 0 {
                px -= 1
            } else if take_passage() {
                return
            }
            flip = true
            moving = true
        }
        if not button.up {
            up_lock = false
        }
        if button.up {
            if py > PLAYER_MIN_Y {
                py -= 1
                moving = true
            } else if not up_lock and can_board(px) {
                up_lock = true
                ride_p = tp_p
                ride_k = tp_k
                door_px = px
                transition Riding
            }
        }
        if button.down and py < PLAYER_MAX_Y {
            py += 1
            moving = true
        }
        var a_new: bool = button.a and not a_held
        a_held = button.a
        if a_new and px >= STAIRS_X and py >= 150 {
            cur_dir = cur_dir ^ 1
            px = STAIRS_X - 8
            platform_setup()
            return
        }
        var f: u8 = S_PLAYER0
        if moving {
            walk += 1
            var phase: u8 = (walk >> 3) & 3
            if phase == 1 {
                f = S_PLAYER1
            } else if phase == 3 {
                f = S_PLAYER2
            }
        } else {
            walk = 0
        }
        draw_player(px, py, f, flip)
        draw_hud_bullets()
        draw_sign_bullets()
    }

    on scanline(80) {
        asm {
            LDA {band_x}
            STA $2005
            LDA #0
            STA $2005
            LDA {band_ctrl}
            STA $2000
        }
    }

    on scanline(144) {
        asm {
            LDA #0
            STA $2005
            STA $2005
            LDA #$88
            STA $2000
        }
    }
}

// Load the platform for cur_st / cur_dir with rendering off.
fun platform_setup() {
    screen_off()
    bg_page(0)
    load_platform_nt()
    load_platform(cur_st, cur_dir)
    load_routes(cur_st)
    assign_sp3()
    pal_set(0, 0x00, 0x10, 0x30)
    pal_set(1, 0x10, 0x30, 0x27)
    pal_set(2, mosaic_color(), 0x10, 0x30)
    pal_set(3, 0x00, 0x28, 0x10)
    pal_set(4, 0x00, 0x37, 0x16)
    pal_set(5, 0x16, 0x1A, 0x30)
    pal_set(6, 0x12, 0x27, 0x30)
    pal_set(7, sp3_c1, sp3_c2, 0x30)

    load_name(cur_st)
    vram_at(0x20, 0x21)
    vram_text(30)
    load_label(cur_st, cur_dir)
    if text_len > 21 {
        text_len = 21
    }
    vram_at(0x20, 0x41)
    vram_text(21)
    text_len = 0
    text_clock(0)
    text_len = 8
    vram_at(0x20, 0x57)
    vram_text(8)
    tablet_names()

    // Put the band where the schedule says the train is, and write
    // every ring column for that position.
    find_train()
    sign_p = 255
    cache_sign()
    update_cam()
    var wc: u16 = (cam >> 3) + 33
    var i: u8 = 0
    while i < 64 {
        wc -= 1
        band_col_direct(wc)
        i += 1
    }
    stream_col = (cam >> 3) + 33
    restore_col = 64
    doors_open = false
    if tp == TP_STOPPED and tick_frames <= DOOR_OPEN and tick_frames > DOOR_CLOSE {
        doors_direct()
        doors_open = true
    }
    band_x = cam as u8
    band_ctrl = CTRL_BASE | ((cam >> 8) as u8 & 1)
    hud_chunk = 0
    arrivals_text()
    vram_at(0x20, 0x61)
    vram_text(30)
    screen_on()
}

fun mosaic_color() -> u8 {
    return mosaic_of(cur_st)
}

// Station mosaics come in a handful of colors; pick one per station.
fun mosaic_of(st: u16) -> u8 {
    var c: u8 = (st as u8) & 7
    if c == 0 { return 0x16 }
    if c == 1 { return 0x1A }
    if c == 2 { return 0x12 }
    if c == 3 { return 0x27 }
    if c == 4 { return 0x17 }
    if c == 5 { return 0x14 }
    if c == 6 { return 0x2B }
    return 0x08
}

// Write the station name into the two wall tablets (rows 6-7 are
// mosaic; the tablets' text row is 7, 8 cells wide).
fun tablet_names() {
    load_name(cur_st)
    short_name()
    vram_at(0x20, 0xE3)
    tablet_text()
    vram_at(0x20, 0xF5)
    tablet_text()
}

// Cut text_buf at the first '-' so tablets show "Times Sq", not
// "Times Sq-42 St", and at 8 cells.
fun short_name() {
    var i: u8 = 0
    while i < text_len {
        if text_buf[i] == C_DASH {
            text_len = i
        }
        i += 1
    }
    if text_len > 8 {
        text_len = 8
    }
}

fun tablet_text() {
    var pad: u8 = (8 - text_len) >> 1
    var i: u8 = 0
    while i < pad {
        poke(0x2007, T_TABLET)
        i += 1
    }
    i = 0
    while i < text_len {
        poke(0x2007, text_buf[i] + TABLET_FONT)
        i += 1
    }
    i = pad + text_len
    while i < 8 {
        poke(0x2007, T_TABLET)
        i += 1
    }
}

// Find the train that is in, coming in, or going out on this
// platform, and how far it is from its stop (tp_dist). The schedule
// can put two trains on the track in one tick; then they share it:
// a train that dwells after one that left gets the first quarter to
// clear the band and the second to pull in, at four times the speed,
// and a train that arrives as one leaves gets half each, at twice.
fun find_train() {
    tp = TP_NONE
    tp_mul = 1
    var stopped: u8 = 255
    var arriving: u8 = 255
    var leaving: u8 = 255
    var i: u8 = 0
    while i < plat_n {
        var p: u8 = plat_p[i]
        var w: u8 = wait_at(p, plat_k[i])
        if w == 0 and stopped == 255 {
            stopped = i
        }
        if w == 1 and arriving == 255 {
            arriving = i
        }
        if w == pat_head(p) - 1 and leaving == 255 {
            leaving = i
        }
        i += 1
    }
    var f: u8 = FRAMES_PER_TICK - tick_frames
    if stopped != 255 {
        if leaving != 255 and f < FRAMES_PER_TICK >> 1 {
            tp_mul = 4
            if f < FRAMES_PER_TICK >> 2 {
                use_train(TP_LEAVING, leaving, move_dist(f << 2))
            } else {
                use_train(TP_ARRIVING, stopped, move_dist(((FRAMES_PER_TICK >> 1) - f) << 2))
            }
            return
        }
        use_train(TP_STOPPED, stopped, 0)
        return
    }
    if leaving != 255 {
        if arriving != 255 {
            tp_mul = 2
            if f < FRAMES_PER_TICK >> 1 {
                use_train(TP_LEAVING, leaving, move_dist(f << 1))
            } else {
                use_train(TP_ARRIVING, arriving, move_dist(tick_frames << 1))
            }
            return
        }
        var d: u16 = move_dist(f)
        if d < DEPART_DIST {
            use_train(TP_LEAVING, leaving, d)
            return
        }
    }
    if arriving != 255 {
        use_train(TP_ARRIVING, arriving, move_dist(tick_frames))
    }
}

fun use_train(t: u8, i: u8, d: u16) {
    tp = t
    tp_p = plat_p[i]
    tp_k = plat_k[i]
    tp_dist = d
}

// Pixels moved f frames after a start (or f frames before a stop).
fun move_dist(f: u8) -> u16 {
    if f <= ACCEL_FRAMES {
        return accel_dist(f)
    }
    return ACCEL_DIST + (((f - ACCEL_FRAMES) as u16) << 3)
}

fun update_cam() {
    if tp == TP_ARRIVING {
        cam = CAM_STOP - tp_dist
        restore_col = 64
    } else if tp == TP_STOPPED {
        cam = CAM_STOP
    } else if tp == TP_LEAVING {
        cam = CAM_STOP + tp_dist
    } else if cam != 0 and restore_col == 64 {
        // The train just left: blank the whole ring, then jump back.
        restore_col = 0
    }
    if tp != TP_STOPPED {
        doors_want = false
    } else {
        doors_want = tick_frames <= DOOR_OPEN and tick_frames > DOOR_CLOSE
    }
}

// Queue the columns that scrolled in at the right edge. Returns
// nonzero when there is room left this frame for another job.
fun stream_band() -> u8 {
    var target: u16 = (cam >> 3) + 33
    if stream_col > target + 40 or target > stream_col + 40 {
        // A departure handed the band to the next arrival. The old
        // view ended at TRAIN_C1, so only the two ring columns left of
        // it can still show the last car.
        band_col(cam >> 3)
        band_col((cam >> 3) + 1)
        stream_col = target
        return 0
    }
    var n: u8 = 0
    // Four times speed moves four columns a frame.
    var cap: u8 = 3
    if tp_mul == 4 {
        cap = 4
    }
    while stream_col < target and n < cap {
        band_col(stream_col)
        stream_col += 1
        n += 1
    }
    if n > 0 {
        return 0
    }
    return 1
}

// One VRAM job per frame: doors or blanking the ring.
fun run_jobs() {
    if doors_want != doors_open {
        doors_open = doors_want
        doors_queue()
        if doors_open {
            play DoorChime
        }
        return
    }
    if restore_col < 64 {
        var i: u8 = 0
        while i < 4 {
            band_col(restore_col as u16)
            restore_col += 1
            i += 1
        }
        if restore_col == 64 {
            cam = 0
            stream_col = 33
            restore_col = 64
        }
    }
}

// Door cells of the stopped car: two columns at screen columns d+1
// and d+2 for each door d, rows 11-16.
fun doors_queue() {
    door_queue(DOOR0_COL + 1 + STOP_RING)
    door_queue(DOOR1_COL + 1 + STOP_RING)
}

fun door_queue(x: u8) {
    if doors_open {
        nt_fill_h(x, 11, 2, T_OPEN1)
        nt_fill_h(x, 12, 2, T_OPEN_M)
        nt_fill_h(x, 13, 2, T_OPEN_M)
        nt_fill_h(x, 14, 2, T_OPEN_M)
        nt_fill_h(x, 15, 2, T_OPEN_M)
        nt_fill_h(x, 16, 2, T_OPEN_FLOOR)
    } else {
        nt_set(x, 11, T_DOOR_TOP_L1)
        nt_set(x + 1, 11, T_DOOR_TOP_R1)
        nt_set(x, 12, T_DOOR_L)
        nt_set(x + 1, 12, T_DOOR_R)
        nt_set(x, 13, T_DOOR_LB)
        nt_set(x + 1, 13, T_DOOR_RB)
        nt_fill_h(x, 14, 1, T_DOOR_LP)
        nt_fill_h(x + 1, 14, 1, T_DOOR_RP)
        nt_fill_h(x, 15, 1, T_DOOR_LP)
        nt_fill_h(x + 1, 15, 1, T_DOOR_RP)
        nt_set(x, 16, T_DOOR_L2)
        nt_set(x + 1, 16, T_DOOR_R2)
    }
}

fun doors_direct() {
    door_direct(DOOR0_COL + 1 + STOP_RING)
    door_direct(DOOR1_COL + 1 + STOP_RING)
}

fun door_direct(x: u8) {
    vram_at(0x21, 0x60 + x)
    poke(0x2007, T_OPEN1)
    poke(0x2007, T_OPEN1)
    var lo: u8 = 0x80 + x
    var r: u8 = 0
    while r < 4 {
        if r == 3 {
            vram_at(0x22, 0x00 + x)
        } else {
            vram_at(0x21, lo)
        }
        poke(0x2007, T_OPEN_M)
        poke(0x2007, T_OPEN_M)
        lo += 32
        r += 1
    }
    vram_at(0x22, 0x00 + x + 32)
    poke(0x2007, T_OPEN_FLOOR)
    poke(0x2007, T_OPEN_FLOOR)
}

// Load the side-sign destination of the train in the band into
// sign_buf. Cut at the first '-' like the real signs: "Coney Island",
// not "Coney Island-Stillwell Av". Uses text_buf, so call it only
// while no HUD update is in flight.
fun cache_sign() {
    if tp == TP_NONE or tp_p == sign_p {
        return
    }
    sign_p = tp_p
    load_name(pat_dest(tp_p))
    sign_len = 0
    while sign_len < text_len and sign_len < SIGN_W - 2 {
        if text_buf[sign_len] == C_DASH {
            break
        }
        sign_buf[sign_len] = text_buf[sign_len]
        sign_len += 1
    }
    text_len = 0
}

// The route bullet at the left of each car's side sign that is on
// screen.
fun draw_sign_bullets() {
    if tp == TP_NONE {
        return
    }
    var x: u16 = ((TRAIN_C0 + SIGN_X as u16) << 3) + 2
    var r: u8 = pat_route(tp_p)
    var car: u8 = 0
    while car < 6 {
        if x >= cam and x < cam + 248 {
            draw_bullet((x - cam) as u8, 87, r)
        }
        x += 256
        car += 1
    }
}

// Can the player, standing at the edge at x, step into an open door?
fun can_board(x: u8) -> bool {
    if not doors_open {
        return false
    }
    var c: u8 = x + 8
    if door_at(c, DOOR0_COL) or door_at(c, DOOR1_COL) {
        return true
    }
    return false
}

fun door_at(c: u8, d: u8) -> bool {
    var left: u8 = (d + 1) << 3
    return c >= left and c < left + 16
}

// Walk the passage to the next station in the complex, if any.
fun take_passage() -> bool {
    var n: u16 = next_in_complex(cur_st)
    if n == cur_st {
        return false
    }
    cur_st = n
    platform_setup()
    return true
}

// The arrivals line (row 3): up to three trains, soonest first.
fun arrivals_text() {
    arr_n = 0
    var used: u8 = 0
    var pos: u8 = 0
    while arr_n < 3 {
        best_w = 255
        best_i = 255
        var i: u8 = 0
        while i < plat_n {
            if (used & (1 << i)) == 0 {
                var w: u8 = wait_at(plat_p[i], plat_k[i])
                if w < best_w {
                    best_w = w
                    best_i = i
                }
            }
            i += 1
        }
        if best_i == 255 {
            break
        }
        used = used | (1 << best_i)
        arr_route[arr_n] = pat_route(plat_p[best_i])
        text_buf[pos] = C_SPACE
        text_buf[pos + 1] = C_SPACE
        pos += 2
        pos += text_wait(pos, best_w)
        text_buf[pos] = C_SPACE
        pos += 1
        arr_slot[arr_n] = pos
        arr_n += 1
    }
    text_len = pos
}

// Queue the arrivals line a few cells per frame, after a tick.
fun hud_arrivals() {
    if hud_chunk == 1 {
        arrivals_text()
    }
    var x: u8 = (hud_chunk - 1) * 8
    var i: u8 = 0
    while i < 8 {
        var c: u8 = FONT_BASE
        var at: u8 = x + i
        if at < text_len {
            c = text_buf[at] + FONT_BASE
        }
        nt_set(at + 1, 3, c)
        i += 1
    }
    hud_chunk += 1
    if hud_chunk == 5 {
        hud_chunk = 0
        text_len = 0
        text_clock(0)
        text_len = 8
        nt_text(23, 2, 8)
    }
}

fun draw_hud_bullets() {
    var i: u8 = 0
    var x: u8 = 8
    while i < arr_n {
        draw_bullet(x, 23, arr_route[i])
        x = (arr_slot[i] + 1) << 3
        i += 1
    }
}

// The player: 16x32, two tiles wide. Facing left mirrors each row.
fun draw_player(x: u8, y: u8, f: u8, flip: bool) {
    var a: u8 = 0
    var l: u8 = 0
    var r: u8 = 1
    if flip {
        a = 0x40
        l = 1
        r = 0
    }
    var row: u8 = 0
    var t: u8 = f
    var yy: u8 = y
    while row < 4 {
        draw SpriteTiles at: (x, yy) frame: t + l attr: a
        draw SpriteTiles at: (x + 8, yy) frame: t + r attr: a
        t += 2
        yy += 8
        row += 1
    }
}
