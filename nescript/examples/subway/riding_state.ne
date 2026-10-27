// Riding: inside the car, facing the far wall. The windows show the
// tunnel, the stations, and the elevated skyline sliding by; the car
// sways and bumps over rail joints while it moves. The ride follows the
// schedule: the train leaves when the platform view would show it
// leaving and reaches the next stop after that stop's running time.
//
// Controls: left and right walk, up and down move between the seats
// and the aisle. Up at an open door steps off. Hold B between stations
// to ride faster.
//
// See scenery.ne for the window band.

const Z_TUNNEL: u8 = 0
const Z_A: u8 = 1
const Z_B: u8 = 2
const Z_SKY: u8 = 3

// Station columns reach this far past a stop, both ways.
const ST_REACH: u16 = 96
// Columns are compared with this bias added, so columns behind the
// last stop stay positive.
const BIAS: u16 = 256

// Scenery state read by scenery.ne.
var seg_c0: u16 = 0
var b_c0: u16 = 0x3000
var mid_c: u16 = 0x3000
var out_a: bool = false
var out_b: bool = false
var name_a: u8[8]
var len_a: u8 = 0
var name_b: u8[8]
var len_b: u8 = 0
var col_buf: u8[5]

const RIDE_MIN_Y: u8 = 132
const RIDE_MAX_Y: u8 = 200
// First scanline of the window band (the splits at 40 and 112 put the
// car back after the HUD and after the band).
const SPLIT_BAND: u8 = 72

// Where the ride is: 0 standing at stop ride_k, 1 running to it.
var rphase: u8 = 0
var at_end: bool = false
// Band scroll in pixels, and the scroll at the last stop.
var rx: u16 = 0
var seg_x0: u16 = 0
// Pixels and frames of motion from the last stop to the next.
var seg_d: u16 = 0
var seg_t: u16 = 0
var half_passed: bool = false
var rstream: u16 = 33

var rdoors: bool = false
var rdoor_job: u8 = 0
var pal_job: bool = false
var mos_b: u8 = 0

// LED sign: what it is showing, and which half still needs writing.
var led_mode: u8 = 255
var led_page: u8 = 0
var led_timer: u8 = 0
var led_job: u8 = 0
var led_buf: u8[28]
var hud_job: bool = false
var clock_job: bool = false

// Transfers at the station the HUD lists.
var xfer_n: u8 = 0
var xfer: u8[12]

// Sway: interior scroll offsets (ix moves the car, iy jolts the whole
// screen), and the counters that drive them.
var ix: u8 = 0
var iy: u8 = 0
var sway_t: u8 = 0
var bump_t: u8 = 0
var joint: u8 = 0

const LED_PAGE_FRAMES: u8 = 150

state Riding {
    var rpx: u8 = 120
    var rpy: u8 = 132
    var rflip: bool = false
    var rwalk: u8 = 0

    on enter {
        rpx = door_px
        rpy = RIDE_MIN_Y
        on_train = true
        rphase = 0
        at_end = false
        rx = 0
        seg_x0 = 0
        seg_c0 = 0
        b_c0 = 0x3000
        mid_c = 0x3000
        seg_d = 0
        seg_t = 0
        set_station_a(stop_station(ride_p, ride_k))
        ride_setup()
    }

    on frame {
        frame_top()
        frame_count += 1

        var speed: u8 = 1
        if button.b and rphase == 1 {
            speed = 3
        }
        clock_step(speed)
        if ticked {
            clock_job = true
        }
        ride_update()
        sway_update()
        set_splits()

        var n: u8 = ride_stream()
        if n < 2 {
            ride_jobs()
        }

        var moving: bool = false
        if button.right and rpx < 232 {
            rpx += 1
            rflip = false
            moving = true
        }
        if button.left and rpx > 8 {
            rpx -= 1
            rflip = true
            moving = true
        }
        if not button.up {
            up_lock = false
        }
        if button.up {
            if rpy > RIDE_MIN_Y {
                rpy -= 1
                moving = true
            } else if not up_lock and rdoors and at_door(rpx) {
                up_lock = true
                cur_st = stop_station(ride_p, ride_k)
                cur_dir = pat_dir(ride_p)
                door_px = rpx
                transition Platform
            }
        }
        if button.down and rpy < RIDE_MAX_Y {
            rpy += 1
            moving = true
        }
        var f: u8 = S_PLAYER0
        if moving {
            rwalk += 1
            var phase: u8 = (rwalk >> 3) & 3
            if phase == 1 {
                f = S_PLAYER1
            } else if phase == 3 {
                f = S_PLAYER2
            }
        } else {
            rwalk = 0
        }
        draw_player(rpx - ix, rpy, f, rflip)
        draw_bullet(8, 7, pat_route(ride_p))
        draw_xfers()
        draw_band_sprites()
    }

    on scanline(40) {
        asm {
            LDA {ix}
            STA $2005
            LDA #0
            STA $2005
            LDA #$88
            STA $2000
        }
    }

    on scanline(72) {
        asm {
            LDA {band_x}
            STA $2005
            LDA #0
            STA $2005
            LDA {band_ctrl}
            STA $2000
        }
    }

    on scanline(112) {
        asm {
            LDA {ix}
            STA $2005
            LDA #0
            STA $2005
            LDA #$88
            STA $2000
        }
    }
}

// Load the car with rendering off.
fun ride_setup() {
    screen_off()
    bg_page(2)
    load_interior_nt()
    pal_set(0, 0x00, 0x10, 0x30)
    pal_set(1, 0x07, 0x27, 0x37)
    pal_set(2, mosaic_of(stop_station(ride_p, ride_k)), 0x00, 0x37)
    pal_set(3, 0x21, 0x00, 0x37)
    pal_set(4, 0x00, 0x37, 0x16)

    rstream = (rx >> 3) + 33
    var c: u16 = rstream
    var i: u8 = 0
    while i < 64 {
        c -= 1
        ride_col_direct(c)
        i += 1
    }
    rdoors = false
    rdoor_job = 0
    if doors_wanted() {
        rdoors = true
        door_direct_i(IN_DOOR0_COL)
        door_direct_i(IN_DOOR1_COL)
    }

    load_xfers()
    claim_sp3(pat_route(ride_p))
    pal_set(7, sp3_c1, sp3_c2, 0x30)

    hud_dest_text()
    vram_at(0x20, 0x23)
    vram_text(19)
    text_len = 0
    text_clock(0)
    text_len = 8
    vram_at(0x20, 0x37)
    vram_text(8)
    hud_stop_text()
    vram_at(0x20, 0x41)
    vram_text(30)

    led_mode = led_mode_now()
    led_page = 0
    led_timer = LED_PAGE_FRAMES
    led_compose()
    vram_at(0x20, 0xA0 + IN_LED_X)
    var j: u8 = 0
    while j < IN_LED_W {
        poke(0x2007, led_buf[j] + FONT_BASE)
        j += 1
    }
    led_job = 0
    hud_job = false
    clock_job = false
    pal_job = false

    ix = 0
    iy = 0
    set_splits()
    screen_on()
}

fun set_station_a(st: u16) {
    out_a = (station_flags(st) & 1) != 0
    load_name(st)
    short_name()
    len_a = text_len
    var i: u8 = 0
    while i < len_a {
        name_a[i] = text_buf[i]
        i += 1
    }
}

fun set_station_b(st: u16) {
    out_b = (station_flags(st) & 1) != 0
    load_name(st)
    short_name()
    len_b = text_len
    var i: u8 = 0
    while i < len_b {
        name_b[i] = text_buf[i]
        i += 1
    }
    mos_b = mosaic_of(st)
}

// Pixels covered e frames into a run of seg_t frames.
fun run_dist(e: u16) -> u16 {
    var f: u16 = seg_t - e
    if e <= f {
        return long_dist(e)
    }
    return seg_d - long_dist(f)
}

// move_dist for any number of frames: past the table, cruise.
fun long_dist(f: u16) -> u16 {
    if f <= 240 {
        return move_dist(f as u8)
    }
    return move_dist(240) + ((f - 240) << 3)
}

// Follow the schedule: leave the stop, run, and arrive.
fun ride_update() {
    if rphase == 0 {
        if at_end {
            return
        }
        if wait_at(ride_p, ride_k) == 0 {
            return
        }
        if ride_k + 1 >= pat_len(ride_p) {
            at_end = true
            return
        }
        start_run()
        return
    }
    var w: u8 = wait_at(ride_p, ride_k)
    if w == 0 {
        rphase = 0
        rx = seg_x0 + seg_d
        if ride_k + 1 >= pat_len(ride_p) {
            at_end = true
        }
        hud_job = true
        return
    }
    var f: u16 = (((w - 1) as u16) * 240) + (tick_frames as u16)
    if f > seg_t {
        f = seg_t
    }
    var e: u16 = seg_t - f
    rx = seg_x0 + run_dist(e)
    if not half_passed and e >= (seg_t >> 1) {
        half_passed = true
        pal_job = true
    }
}

// The train just left stop ride_k: set up the run to the next stop.
fun start_run() {
    var g: u8 = stop_gap(ride_p, ride_k)
    seg_t = ((g - 1) as u16) * 240
    seg_d = long_dist(seg_t >> 1) << 1
    seg_x0 = rx
    seg_c0 = seg_x0 >> 3
    b_c0 = (seg_x0 + seg_d) >> 3
    mid_c = (seg_x0 + (seg_d >> 1)) >> 3
    mid_c += 16
    ride_k += 1
    set_station_b(stop_station(ride_p, ride_k))
    half_passed = false
    rphase = 1
    hud_job = true
}

// The car rocks side to side at speed and drops a pixel at each rail
// joint, every 39 feet of track (64 pixels here).
fun sway_update() {
    if rphase == 0 {
        ix = 0
        iy = 0
        return
    }
    var j: u8 = (rx >> 6) as u8
    if j != joint {
        joint = j
        bump_t = 3
    }
    iy = 0
    if bump_t > 0 {
        bump_t -= 1
        iy = 1
    }
    if sway_t > 0 {
        sway_t -= 1
    } else {
        ix = ix ^ 1
        sway_t = 18 + (frame_count & 15)
    }
}

// Scroll for the window band, and the whole-screen jolt of a rail
// joint (the frame-top scroll; the splits only set X).
fun set_splits() {
    band_x = rx as u8
    band_ctrl = CTRL_BASE | ((rx >> 8) as u8 & 1)
    top_y = iy
}

// Queue the window columns that scrolled in. Returns how many.
fun ride_stream() -> u8 {
    var target: u16 = (rx >> 3) + 33
    if rstream > target + 40 or target > rstream + 40 {
        rstream = target
    }
    var n: u8 = 0
    while rstream < target and n < 4 {
        ride_col(rstream)
        rstream += 1
        n += 1
    }
    return n
}

fun doors_wanted() -> bool {
    if rphase != 0 {
        return false
    }
    if at_end {
        return true
    }
    return tick_frames <= DOOR_OPEN and tick_frames > DOOR_CLOSE
}

// One VRAM job per frame, most urgent first.
fun ride_jobs() {
    var want: bool = doors_wanted()
    if want != rdoors and rdoor_job == 0 {
        rdoors = want
        rdoor_job = 2
        if rdoors {
            play DoorChime
        }
    }
    if rdoor_job == 2 {
        door_queue_i(IN_DOOR0_COL)
        rdoor_job = 1
        return
    }
    if rdoor_job == 1 {
        door_queue_i(IN_DOOR1_COL)
        rdoor_job = 0
        return
    }
    if pal_job {
        pal_job = false
        nt_set(9, 248, mos_b)
        return
    }
    var mode: u8 = led_mode_now()
    if mode != led_mode {
        led_mode = mode
        led_page = 0
        led_timer = LED_PAGE_FRAMES
        led_compose()
        led_job = 2
    } else if led_job == 0 {
        if led_timer > 0 {
            led_timer -= 1
        } else {
            led_timer = LED_PAGE_FRAMES
            led_page += 1
            led_compose()
            led_job = 2
        }
    }
    if led_job > 0 {
        var half: u8 = (2 - led_job) * 14
        var i: u8 = 0
        while i < 14 {
            nt_set(IN_LED_X + half + i, 5, led_buf[half + i] + FONT_BASE)
            i += 1
        }
        led_job -= 1
        return
    }
    if hud_job {
        hud_job = false
        load_xfers()
        claim_sp3(pat_route(ride_p))
        sp3_update()
        hud_stop_text()
        nt_text(1, 2, 30)
        return
    }
    if clock_job {
        clock_job = false
        text_len = 0
        text_clock(0)
        text_len = 8
        nt_text(23, 1, 8)
    }
}

// LED sign modes: 0 standing, 1 doors closing, 2 running, 3 last stop.
fun led_mode_now() -> u8 {
    if rphase == 1 {
        return 2
    }
    if at_end {
        return 3
    }
    if tick_frames <= DOOR_CLOSE + 40 {
        return 1
    }
    return 0
}

// Put page led_page of the current mode, centered, in led_buf.
fun led_compose() {
    text_len = 0
    var st: u16 = stop_station(ride_p, ride_k)
    if led_mode == 0 {
        if (led_page & 1) == 0 {
            msg(MSG_THIS)
        } else {
            load_name(st)
        }
    } else if led_mode == 1 {
        if (led_page & 1) == 0 {
            msg(MSG_CLEAR1)
        } else {
            msg(MSG_CLEAR2)
        }
    } else if led_mode == 3 {
        if (led_page & 1) == 0 {
            msg(MSG_LAST)
        } else {
            msg(MSG_LEAVE)
        }
    } else {
        var p: u8 = led_page & 3
        if p == 3 and xfer_n == 0 {
            p = 0
            led_page = 0
        }
        if p == 0 {
            msg(MSG_NEXT)
        } else if p == 1 {
            load_name(st)
        } else if p == 2 {
            msg(MSG_GOING)
            load_name(pat_dest(ride_p))
            cut_at_dash()
        } else {
            msg(MSG_XFER)
        }
    }
    if text_len > IN_LED_W {
        text_len = IN_LED_W
    }
    var pad: u8 = (IN_LED_W - text_len) >> 1
    var i: u8 = 0
    while i < IN_LED_W {
        led_buf[i] = 0
        if i >= pad and i < pad + text_len {
            led_buf[i] = text_buf[i - pad]
        }
        i += 1
    }
}

// Cut text_buf at the first '-', as the car signs do: "Coney Island",
// not "Coney Island-Stillwell Av".
fun cut_at_dash() {
    var i: u8 = 0
    while i < text_len {
        if text_buf[i] == C_DASH {
            text_len = i
        }
        i += 1
    }
}

// Append fixed message m to text_buf.
fun msg(m: u8) {
    var off: u8 = MSG_OFF[m]
    var n: u8 = MSG_LEN[m]
    var i: u8 = 0
    while i < n {
        text_buf[text_len] = MSG_TEXT[off + i]
        text_len += 1
        i += 1
    }
}

// HUD row 1: "to Bay Ridge-95 St".
fun hud_dest_text() {
    load_name(pat_dest(ride_p))
    cut_at_dash()
    prefix(MSG_TO, 19)
}

// HUD row 2: "Next: 34 St-Herald Sq" or "At: Times Sq-42 St".
fun hud_stop_text() {
    load_name(stop_station(ride_p, ride_k))
    if rphase == 1 {
        prefix(MSG_HUD_NEXT, 30)
    } else {
        prefix(MSG_HUD_AT, 30)
    }
}

// Put message m in front of text_buf, then cut it to max cells.
fun prefix(m: u8, max: u8) {
    var shift: u8 = MSG_LEN[m]
    var i: u8 = text_len
    while i > 0 {
        i -= 1
        text_buf[i + shift] = text_buf[i]
    }
    var n: u8 = text_len
    text_len = 0
    msg(m)
    text_len += n
    if text_len > max {
        text_len = max
    }
}

// The other routes at the stop the HUD names, across every station of
// its complex (34 St-Herald Sq is two stations: N Q R W and B D F M).
fun load_xfers() {
    var own: u8 = pat_route(ride_p)
    var first: u16 = stop_station(ride_p, ride_k)
    var st: u16 = first
    xfer_n = 0
    var hops: u8 = 0
    while hops < 8 {
        load_routes(st)
        var i: u8 = 0
        while i < st_nroutes {
            var r: u8 = st_routes[i]
            if r != own and not has_xfer(r) and xfer_n < 12 {
                xfer[xfer_n] = r
                xfer_n += 1
            }
            i += 1
        }
        st = next_in_complex(st)
        if st == first {
            break
        }
        hops += 1
    }
    var j: u8 = 0
    while j < xfer_n {
        st_routes[j] = xfer[j]
        j += 1
    }
    st_nroutes = xfer_n
    assign_sp3()
}

fun has_xfer(r: u8) -> bool {
    var i: u8 = 0
    while i < xfer_n {
        if xfer[i] == r {
            return true
        }
        i += 1
    }
    return false
}

// Transfer bullets: seven to a line, two lines.
fun draw_xfers() {
    var i: u8 = 0
    var x: u8 = 8
    var y: u8 = 23
    while i < xfer_n {
        if i == 7 {
            x = 8
            y = 33
        }
        draw_bullet(x, y, xfer[i])
        x += 12
        i += 1
    }
}

// Door frames, door seams, and the window post over the band.
fun draw_band_sprites() {
    var y: u8 = SPLIT_BAND - 1
    var r: u8 = 0
    while r < IN_BAND_ROWS {
        band_door(IN_DOOR0_COL << 3, y)
        draw SpriteTiles at: (IN_POST0_X - ix, y) frame: S_WPOST attr: 0
        band_door(IN_DOOR1_COL << 3, y)
        y += 8
        r += 1
    }
}

fun band_door(x: u8, y: u8) {
    draw SpriteTiles at: (x - ix, y) frame: S_DEDGE_L attr: 0
    if not rdoors {
        draw SpriteTiles at: (x + 20 - ix, y) frame: S_DCENTER attr: 0
    }
    draw SpriteTiles at: (x + 40 - ix, y) frame: S_DEDGE_R attr: 0
}

// Can the player, standing at the back at x, step out of a door?
fun at_door(x: u8) -> bool {
    var c: u8 = x + 8
    var d0: u8 = (IN_DOOR0_COL + 1) << 3
    var d1: u8 = (IN_DOOR1_COL + 1) << 3
    if c >= d0 and c < d0 + 32 {
        return true
    }
    return c >= d1 and c < d1 + 32
}

// Door d's lower leaves (rows 14-19), open or shut, through the VRAM
// buffer.
fun door_queue_i(d: u8) {
    var x: u8 = d + 1
    var y: u8 = 14
    while y < 20 {
        if rdoors {
            var t: u8 = I_OUT_FLOOR
            if y == 14 {
                t = I_OUT_EDGE
            } else if y == 19 {
                t = I_OUT_FLOOR_LO
            }
            nt_fill_h(x, y, 4, t)
        } else if y == 19 {
            nt_fill_h(x, y, 4, I_THRESHOLD)
        } else if y == 18 {
            nt_set(x, y, I_LEAF_KICK)
            nt_set(x + 1, y, I_LEAF_KICK_L)
            nt_set(x + 2, y, I_LEAF_KICK_R)
            nt_set(x + 3, y, I_LEAF_KICK)
        } else {
            nt_set(x, y, I_LEAF)
            nt_set(x + 1, y, I_LEAF_SEAM_L)
            nt_set(x + 2, y, I_LEAF_SEAM_R)
            nt_set(x + 3, y, I_LEAF)
        }
        y += 1
    }
}

// Open door d straight through the PPU. Rendering must be off.
fun door_direct_i(d: u8) {
    var lo: u8 = 0xC0 + d + 1
    var hi: u8 = 0x21
    var y: u8 = 14
    while y < 20 {
        vram_at(hi, lo)
        var t: u8 = I_OUT_FLOOR
        if y == 14 {
            t = I_OUT_EDGE
        } else if y == 19 {
            t = I_OUT_FLOOR_LO
        }
        poke(0x2007, t)
        poke(0x2007, t)
        poke(0x2007, t)
        poke(0x2007, t)
        lo += 32
        if lo < 32 {
            hi += 1
        }
        y += 1
    }
}
