// What the car's windows show: tunnel, station platforms, and the
// elevated skyline. Rows 9-13 of both nametables form a 64-column ring
// like the platform's track band; world column c lives in ring column
// c & 63.
//
// Positions are band columns counted from the start of the ride. The
// last stop (A) is at seg_c0 and the next stop (B) at b_c0: those are
// the columns at the left edge of the screen while the train stands
// there. A station is drawn from its stop column with a 32-column
// period, so a tablet with the station name sits in the left window.
//
// These functions live in the Gfx bank with the interior nametable.

fun zone_of(c: u16) -> u8 {
    var rel: u16 = c + BIAS - seg_c0
    var b_rel: u16 = b_c0 + BIAS - seg_c0
    var m_rel: u16 = mid_c + BIAS - seg_c0
    if rel < BIAS + ST_REACH and rel < m_rel {
        return Z_A
    }
    if rel + ST_REACH >= b_rel and rel >= m_rel {
        return Z_B
    }
    var out: bool = out_a
    if rel >= m_rel {
        out = out_b
    }
    if out {
        return Z_SKY
    }
    return Z_TUNNEL
}

// Palette of the window band at column c.
fun zone_pal(c: u16) -> u8 {
    var z: u8 = zone_of(c)
    if z == Z_SKY {
        return 3
    }
    if z == Z_A and out_a {
        return 3
    }
    if z == Z_B and out_b {
        return 3
    }
    return 2
}

// Fill col_buf with the five window rows of column c.
fun scene_col(c: u16) {
    var z: u8 = zone_of(c)
    if z == Z_A {
        station_col(((c + 256 - seg_c0) as u8) & 31, out_a, 0)
    } else if z == Z_B {
        station_col(((c + 256 - b_c0) as u8) & 31, out_b, 1)
    } else if z == Z_SKY {
        skyline_col(c)
    } else {
        tunnel_col(c as u8)
    }
}

fun tunnel_col(c: u8) {
    if (c & 7) == 0 {
        col_buf[0] = I_TN_BEAM_TOP
        col_buf[1] = I_TN_BEAM
        col_buf[2] = I_TN_BEAM
        col_buf[3] = I_TN_BEAM
        col_buf[4] = I_TN_BEAM
        return
    }
    col_buf[0] = I_TN_CABLE
    col_buf[1] = I_TN_DARK
    if (c & 31) == 12 {
        col_buf[1] = I_TN_LAMP
    }
    col_buf[2] = I_BLACK
    col_buf[3] = I_TN_DARK
    col_buf[4] = I_TN_BENCH
}

// A cheap hash of a column pair, for rooftops and riders.
fun col_hash(c: u16) -> u8 {
    var h: u8 = (c >> 1) as u8
    h = h ^ (h >> 3)
    h = h * 13 + 7
    return h ^ (h >> 4)
}

fun skyline_col(c: u16) {
    var h: u8 = col_hash(c >> 1)
    var top: u8 = (h & 3) + 1
    var r: u8 = 0
    while r < 4 {
        if r < top {
            col_buf[r] = I_SKY
        } else if r == top {
            if (h & 4) == 0 {
                col_buf[r] = I_BLD_TOP
            } else {
                col_buf[r] = I_BLD_TOP2
            }
        } else {
            col_buf[r] = I_BLD
        }
        r += 1
    }
    col_buf[4] = I_EL_GIRDER
}

// t is the column within the station's 32-column period, counted from
// the screen's left edge while the train stands there.
fun station_col(t: u8, out: bool, which: u8) {
    if out {
        el_station_col(t, which)
        return
    }
    col_buf[3] = I_ST_WALL
    col_buf[4] = I_ST_EDGE
    if t >= 7 and t <= 16 {
        if t == 7 {
            col_buf[0] = I_TABF_TL
            col_buf[1] = I_TABF_L
            col_buf[2] = I_TABF_BL
        } else if t == 16 {
            col_buf[0] = I_TABF_TR
            col_buf[1] = I_TABF_R
            col_buf[2] = I_TABF_BR
        } else {
            col_buf[0] = I_TABF_T
            col_buf[1] = I_TAB_FONT + name_char(t - 8, which)
            col_buf[2] = I_TABF_B
        }
        return
    }
    if t == 2 or t == 21 or t == 27 {
        col_buf[0] = I_ST_COL
        col_buf[1] = I_ST_COL
        col_buf[2] = I_ST_COL
        col_buf[3] = I_ST_COL
        col_buf[4] = I_ST_COL_EDGE
        return
    }
    col_buf[0] = I_MOS_T
    col_buf[1] = I_MOS_B
    col_buf[2] = I_ST_WALL
    if t == 4 or t == 19 or t == 24 or t == 30 {
        col_buf[3] = I_ST_HEAD
        col_buf[4] = I_ST_BODY
    }
}

// An elevated platform: canopy, a black name sign, rooftops beyond.
fun el_station_col(t: u8, which: u8) {
    col_buf[0] = I_CANOPY
    col_buf[1] = I_SKY
    col_buf[2] = I_SKY
    col_buf[3] = I_BLD
    col_buf[4] = I_OP_EDGE_M
    if (t & 7) == 3 {
        col_buf[0] = I_CANOPY_POST
        col_buf[1] = I_OP_POST
        col_buf[2] = I_OP_POST
        col_buf[3] = I_OP_POST
        col_buf[4] = I_OP_EDGE
    }
    if t >= 7 and t <= 16 {
        if t == 7 {
            col_buf[1] = I_SIGN_L
        } else if t == 16 {
            col_buf[1] = I_SIGN_R
        } else {
            col_buf[1] = FONT_BASE + name_char(t - 8, which)
        }
    }
    if (t & 3) == 1 {
        col_buf[2] = I_BLD_TOP
    }
}

// Character i of the 8-cell tablet text of station A or B, centered.
fun name_char(i: u8, which: u8) -> u8 {
    var n: u8 = len_a
    if which == 1 {
        n = len_b
    }
    var pad: u8 = (8 - n) >> 1
    if i < pad or i >= pad + n {
        return 0
    }
    if which == 1 {
        return name_b[i - pad]
    }
    return name_a[i - pad]
}

// Attribute byte for the four ring columns starting at c (c & 3 == 0).
fun scene_attr(c: u16) -> u8 {
    var l: u8 = zone_pal(c)
    var r: u8 = zone_pal(c + 2)
    return l | (r << 2) | (l << 4) | (r << 6)
}

// Queue world column c through the VRAM buffer.
fun ride_col(c: u16) {
    var ring: u8 = (c as u8) & 63
    var x: u8 = ring & 31
    var y: u8 = IN_BAND_ROW
    var ay: u8 = 30
    if ring >= 32 {
        y += 32
        ay = 62
    }
    scene_col(c)
    var r: u8 = 0
    while r < IN_BAND_ROWS {
        nt_set(x, y, col_buf[r])
        y += 1
        r += 1
    }
    if (ring & 3) == 0 {
        var v: u8 = scene_attr(c)
        nt_set(16 + (x >> 2), ay, v)
        nt_set(24 + (x >> 2), ay, v)
    }
}

// Write world column c straight to the PPU. Rendering must be off.
fun ride_col_direct(c: u16) {
    var ring: u8 = (c as u8) & 63
    var hi: u8 = 0x21
    var ahi: u8 = 0x23
    if ring >= 32 {
        hi = 0x25
        ahi = 0x27
    }
    var x: u8 = ring & 31
    scene_col(c)
    var lo: u8 = 0x20 + x
    var r: u8 = 0
    while r < IN_BAND_ROWS {
        vram_at(hi, lo)
        poke(0x2007, col_buf[r])
        lo += 32
        if lo < 32 {
            hi += 1
        }
        r += 1
    }
    if (ring & 3) == 0 {
        var v: u8 = scene_attr(c)
        vram_at(ahi, 0xD0 + (x >> 2))
        poke(0x2007, v)
        vram_at(ahi, 0xD8 + (x >> 2))
        poke(0x2007, v)
    }
}

// Both nametables get the interior; the window rows are then
// overwritten by the scenery ring.
fun load_interior_nt() {
    vram_at(0x20, 0)
    var i: u16 = 0
    while i < 1024 {
        poke(0x2007, NT_INTERIOR[i])
        i += 1
    }
    vram_at(0x24, 0)
    i = 0
    while i < 1024 {
        poke(0x2007, NT_INTERIOR[i])
        i += 1
    }
}
