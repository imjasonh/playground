// Pause map setup: one-time screen writes for the map and its side panel.
// It runs with rendering off, so it lives in the Map bank with the tiles.

fun pause_setup() {
    screen_off()
    top_x = 0
    top_y = 0
    bg_page(3)
    load_map_nt()
    map_c1 = 0
    map_c2 = 0
    pm_n = 0
    text_len = 0
    text_clock(0)
    panel_put(PANEL_COL, 2, 0, 8, PANEL_W)
    if pause_from == 0 {
        pause_platform()
    } else {
        pause_riding()
    }
    pal_set(0, 0x00, 0x10, 0x10)
    pal_set(1, map_c1, 0x10, 0x10)
    pal_set(2, map_c2, 0x10, 0x10)
    pal_set(3, 0x10, 0x27, 0x30)
    pal_set(4, 0x00, 0x30, 0x16)
    pal_set(5, 0x16, 0x1A, 0x30)
    pal_set(6, 0x12, 0x27, 0x30)
    pal_set(7, sp3_c1, sp3_c2, 0x30)
    vram_at(0x23, 0xC0)
    var j: u8 = 0
    while j < 64 {
        poke(0x2007, map_attr[j])
        j += 1
    }
    screen_on()
}

// The platform: its station and direction, and each route that stops
// here with its destination and next train. The routes are lit from
// this stop on.
fun pause_platform() {
    here_x = map_x(cur_st)
    here_y = map_y(cur_st)
    load_name(cur_st)
    panel_wrap(PANEL_COL, 4, PANEL_W)
    load_label(cur_st, cur_dir)
    panel_wrap(PANEL_COL, 7, PANEL_W)
    text_len = 0
    msg(MSG_TRAINS)
    panel_put(PANEL_COL, 10, 0, text_len, PANEL_W)
    var row: u8 = 11
    var i: u8 = 0
    while i < plat_n and i < LIST_MAX and row < 28 {
        var p: u8 = plat_p[i]
        var k: u8 = plat_k[i]
        light_ahead(p, k)
        pm_route[i] = pat_route(p)
        pm_y[i] = (row << 3) - 1
        load_name(pat_dest(p))
        cut_at_dash()
        panel_wrap(PANEL_COL + 2, row, BULLET_W)
        if text_len > BULLET_W {
            row += 1
        }
        text_len = text_wait(0, wait_at(p, k))
        panel_put(PANEL_COL + 2, row + 1, 0, text_len, BULLET_W)
        row += 2
        i += 1
    }
    pm_n = i
}

// The train: its route and destination, and the stops ahead with the
// time to each. The route is lit from the last stop on.
fun pause_riding() {
    var st: u16 = stop_station(ride_p, ride_k)
    here_x = map_x(st)
    here_y = map_y(st)
    var k0: u8 = ride_k
    if rphase == 1 and ride_k > 0 {
        k0 = ride_k - 1
        train_between(stop_station(ride_p, k0))
    }
    light_ahead(ride_p, k0)
    load_name(pat_dest(ride_p))
    cut_at_dash()
    panel_wrap(PANEL_COL + 2, 4, BULLET_W)
    text_len = 0
    msg(MSG_STOPS)
    panel_put(PANEL_COL, 7, 0, text_len, PANEL_W)

    // Trains of a pattern keep their order, so this train is the next
    // one at every stop ahead: its time there is the wait for stop
    // ride_k plus the running time from ride_k.
    var base: u8 = wait_at(ride_p, ride_k)
    var c0: u8 = stop_cum(ride_p, ride_k)
    var n: u8 = pat_len(ride_p)
    var k: u8 = ride_k
    var row: u8 = 8
    pm_n = 0
    while k < n and pm_n < LIST_MAX {
        st = stop_station(ride_p, k)
        pm_x[pm_n] = map_x(st)
        pm_y[pm_n] = map_y(st)
        load_name(st)
        fit_text(PANEL_W)
        panel_put(PANEL_COL, row, 0, text_len, PANEL_W)
        text_buf[0] = C_SPACE
        text_buf[1] = C_SPACE
        text_len = 2 + text_wait(2, base + stop_cum(ride_p, k) - c0)
        panel_put(PANEL_COL, row + 1, 0, text_len, PANEL_W)
        row += 2
        k += 1
        pm_n += 1
    }
}

// Move the marker from stop ride_k toward the last stop, prev, by how
// far the run has gone, in eighths.
fun train_between(prev: u16) {
    var step: u16 = seg_d >> 3
    var done: u16 = rx - seg_x0
    var acc: u16 = step
    var t: u8 = 0
    while t < 8 and acc <= done {
        t += 1
        acc += step
    }
    here_x = lerp8(map_x(prev), here_x, t)
    here_y = lerp8(map_y(prev), here_y, t)
}

// a + (b - a) * t / 8, for t from 0 to 8.
fun lerp8(a: u8, b: u8, t: u8) -> u8 {
    var s: u16 = (a as u16) << 3
    var i: u8 = 0
    while i < t {
        s = s + (b as u16) - (a as u16)
        i += 1
    }
    return (s >> 3) as u8
}

// Light pattern p from its stop k0 to the end: every attribute cell the
// line passes through gets the palette of the pattern's color. Up to
// two colors; a third color stays unlit.
fun light_ahead(p: u8, k0: u8) {
    var c: u8 = ROUTE_MAP[pat_route(p)]
    var pal: u8 = 1
    if map_c1 == 0 or map_c1 == c {
        map_c1 = c
    } else if map_c2 == 0 or map_c2 == c {
        map_c2 = c
        pal = 2
    } else {
        return
    }
    var n: u8 = pat_len(p)
    var st: u16 = stop_station(p, k0)
    var x0: u8 = map_x(st)
    var y0: u8 = map_y(st)
    map_mark(x0, y0, pal)
    var k: u8 = k0 + 1
    while k < n {
        st = stop_station(p, k)
        var x1: u8 = map_x(st)
        var y1: u8 = map_y(st)
        // Eight points along the segment; no segment is long enough to
        // skip a 16-pixel cell.
        var ax: u16 = (x0 as u16) << 3
        var ay: u16 = (y0 as u16) << 3
        var t: u8 = 0
        while t < 8 {
            ax = ax + (x1 as u16) - (x0 as u16)
            ay = ay + (y1 as u16) - (y0 as u16)
            map_mark((ax >> 3) as u8, (ay >> 3) as u8, pal)
            t += 1
        }
        x0 = x1
        y0 = y1
        k += 1
    }
}

fun map_mark(x: u8, y: u8, pal: u8) {
    var i: u8 = ((y >> 5) << 3) + (x >> 5)
    var sh: u8 = (((y >> 4) & 1) << 2) + (((x >> 4) & 1) << 1)
    map_attr[i] = (map_attr[i] & (0xFF ^ (3 << sh))) | (pal << sh)
}

// Write text_buf[from, from + n) at (col, row), padded to w cells.
// Rendering must be off.
fun panel_put(col: u8, row: u8, from: u8, n: u8, w: u8) {
    var a: u16 = ((row as u16) << 5) + (col as u16)
    vram_at(0x20 + (a >> 8) as u8, a as u8)
    var i: u8 = 0
    while i < w {
        var c: u8 = FONT_BASE
        if i < n {
            c = text_buf[from + i] + FONT_BASE
        }
        poke(0x2007, c)
        i += 1
    }
}

// Write text_buf over rows row and row + 1, w cells each, breaking at
// the last space or dash that fits.
fun panel_wrap(col: u8, row: u8, w: u8) {
    if text_len <= w {
        panel_put(col, row, 0, text_len, w)
        return
    }
    var cut: u8 = w
    var next: u8 = w
    var i: u8 = w
    while i > 0 {
        if text_buf[i] == C_SPACE {
            cut = i
            next = i + 1
            break
        }
        if text_buf[i - 1] == C_DASH {
            cut = i
            next = i
            break
        }
        i -= 1
    }
    panel_put(col, row, 0, cut, w)
    var n2: u8 = text_len - next
    if n2 > w {
        n2 = w
    }
    panel_put(col, row + 1, next, n2, w)
}

// Shorten text_buf to w cells. A complex name that doesn't fit keeps
// its first part, so 34 St-Herald Sq reads 34 St; anything else breaks
// at the last space that fits.
fun fit_text(w: u8) {
    if text_len <= w {
        return
    }
    cut_at_dash()
    if text_len <= w {
        return
    }
    var i: u8 = w
    while i > 0 {
        if text_buf[i] == C_SPACE {
            text_len = i
            return
        }
        i -= 1
    }
    text_len = w
}
