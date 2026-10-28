// Transfer hints sit in the bottom corners, under the part of the
// floor where Alex walks and fights. Each side that has a passage
// stacks its route bullets in one column, bottom-aligned so a short
// list stays on the floor, with the arrow beside the top bullet and
// the "UP"/"DN" tag on the row above that. Column 0 and column 31
// are cropped, so the column is one tile in from the edge. The
// lowest bullet is the last fully visible row. Both columns are
// clear of the benches (columns 9-12 and 20-23).
const XFER_BULLET_BOTTOM: u8 = 224
const XFER_L_ARROW_X: u8 = 8
const XFER_L_BULLET_X: u8 = 16
const XFER_L_TAG_COL: u8 = 1
const XFER_R_ARROW_X: u8 = 240
const XFER_R_BULLET_X: u8 = 232
const XFER_R_TAG_COL: u8 = 29
const XFER_FLIP: u8 = 0x40

// Load the platform for cur_st / cur_dir with rendering off.
fun platform_setup() {
    screen_off()
    bg_page(0)
    load_platform_nt()
    load_platform(cur_st, cur_dir)
    load_routes(cur_st)
    assign_sp3()
    compute_transfers()
    pal_set(0, 0x00, 0x10, 0x30)
    pal_set(1, 0x10, 0x30, 0x27)
    pal_set(2, mosaic_color(), 0x10, 0x30)
    pal_set(3, 0x00, 0x28, 0x10)
    // Alex: black hair, skin, white shirt. The denim is sprite
    // palette 2's blue, set below.
    pal_set(4, 0x0F, 0x37, 0x30)
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
    if l_has {
        write_dir_tag(XFER_L_TAG_COL, l_n)
    }
    if r_has {
        write_dir_tag(XFER_R_TAG_COL, r_n)
    }
    text_len = 0
    screen_on()
}

// The complex members off the left (next_in_complex) and right
// (prev_in_complex) edge of this platform, with up to 4 routes each.
// Reserves a sprite palette 3 slot for any that need one, same as
// load_xfers does for the in-train transfer HUD. Runs after
// load_routes(cur_st) / assign_sp3(), and overwrites st_routes:
// nothing after this reads the current platform's copy again.
fun compute_transfers() {
    var l: u16 = next_in_complex(cur_st)
    l_has = l != cur_st
    if l_has {
        load_routes(l)
        l_n = st_nroutes
        if l_n > 4 {
            l_n = 4
        }
        var i: u8 = 0
        while i < l_n {
            l_routes[i] = st_routes[i]
            claim_sp3(st_routes[i])
            i += 1
        }
    }
    var r: u16 = prev_in_complex(cur_st)
    r_has = r != cur_st
    if r_has {
        load_routes(r)
        r_n = st_nroutes
        if r_n > 4 {
            r_n = 4
        }
        var j: u8 = 0
        while j < r_n {
            r_routes[j] = st_routes[j]
            claim_sp3(st_routes[j])
            j += 1
        }
    }
}

// Y of the top route bullet. The column grows upward from
// XFER_BULLET_BOTTOM, so one route sits on the floor and four
// reach the row just under a standing Alex.
fun xfer_bullet_y(n: u8) -> u8 {
    if n < 2 {
        return XFER_BULLET_BOTTOM
    }
    return XFER_BULLET_BOTTOM - ((n - 1) << 3)
}

// "UP" when cur_dir faces north, "DN" when it faces south. Passages
// keep cur_dir, so both the adjacent platforms this hints at face the
// same way. The tag sits on the nametable row above the top bullet.
fun write_dir_tag(col: u8, n: u8) {
    if cur_dir == 0 {
        text_buf[0] = 21 // U
        text_buf[1] = 16 // P
    } else {
        text_buf[0] = 4 // D
        text_buf[1] = 14 // N
    }
    text_len = 2
    var row: u8 = xfer_bullet_y(n) >> 3
    row -= 1
    var addr: u16 = 0x2000 + ((row as u16) << 5) + (col as u16)
    vram_at((addr >> 8) as u8, addr as u8)
    vram_text(2)
}

// The transfer arrow and route bullets at each edge that has one.
// Bullets stack downward from the arrow. Call only while no fight
// has the sprite budget those bullets need.
fun draw_transfer_hints() {
    if l_has {
        var ly: u8 = xfer_bullet_y(l_n)
        draw SpriteTiles at: (XFER_L_ARROW_X, ly) frame: S_ARROW attr: XFER_FLIP
        var i: u8 = 0
        while i < l_n {
            draw_bullet(XFER_L_BULLET_X, ly, l_routes[i])
            ly += 8
            i += 1
        }
    }
    if r_has {
        var ry: u8 = xfer_bullet_y(r_n)
        draw SpriteTiles at: (XFER_R_ARROW_X, ry) frame: S_ARROW attr: 0
        var j: u8 = 0
        while j < r_n {
            draw_bullet(XFER_R_BULLET_X, ry, r_routes[j])
            ry += 8
            j += 1
        }
    }
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
        } else {
            play_dpcm StandClear
        }
        return
    }
    if restore_col < 64 {
        // 2 columns/frame, not 4: each queues 8 `nt_set` calls, and
        // this job already competes with `hud_arrivals()` and the
        // bullet draws for the same frame's VRAM buffer entries.
        // The NMI drain has a real but tight vblank cycle budget
        // (see `gen_vram_buf_drain`'s "~50 single-tile writes"
        // comment); stacking a 4-column (32-entry) burst on top of
        // that other per-frame work occasionally overran it by a
        // scanline or two, right as a departing train hands the
        // band back for restoration. Halving the burst halves this
        // job's share and keeps every departure inside budget.
        var i: u8 = 0
        while i < 2 {
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