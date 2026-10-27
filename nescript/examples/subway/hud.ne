// Clock, route bullets, and text formatting shared by every screen.

// Font codes for the characters the code writes itself.
const C_SPACE: u8 = 0
const C_COLON: u8 = 70
const C_DASH: u8 = 63
const C_GT: u8 = 73
const C_0: u8 = 53

// Advance the clock one frame. Sets `ticked` on the frame a new tick
// starts. `speed` frames pass at once while fast-forwarding.
fun clock_step(speed: u8) {
    ticked = false
    if tick_frames > speed {
        tick_frames -= speed
        return
    }
    tick_frames = FRAMES_PER_TICK
    ticked = true
    advance_patterns()
    clock_half += 1
    if clock_half == 2 {
        clock_half = 0
        clock_min += 1
        if clock_min == 60 {
            clock_min = 0
            clock_hr += 1
            if clock_hr == 24 {
                clock_hr = 0
            }
        }
    }
}

// Write "12:05 PM" into text_buf at pos.
fun text_clock(pos: u8) {
    var h: u8 = clock_hr
    var pm: bool = h >= 12
    if h > 12 {
        h -= 12
    }
    if h == 0 {
        h = 12
    }
    if h < 10 {
        text_buf[pos] = C_SPACE
        text_buf[pos + 1] = C_0 + h
    } else {
        text_digit2(pos, h)
    }
    text_buf[pos + 2] = C_COLON
    text_digit2(pos + 3, clock_min)
    text_buf[pos + 5] = C_SPACE
    if pm {
        text_buf[pos + 6] = 16
    } else {
        text_buf[pos + 6] = 1
    }
    text_buf[pos + 7] = 13
}

// Write a wait of `w` ticks as "3 min" (or "now") into text_buf at
// pos. Returns the number of cells written.
fun text_wait(pos: u8, w: u8) -> u8 {
    if w == 0 {
        text_buf[pos] = 40
        text_buf[pos + 1] = 41
        text_buf[pos + 2] = 49
        return 3
    }
    var m: u8 = (w + 1) >> 1
    var n: u8 = 0
    if m >= 10 {
        text_digit2(pos, m)
        n = 2
    } else {
        text_buf[pos] = C_0 + m
        n = 1
    }
    text_buf[pos + n] = C_SPACE
    text_buf[pos + n + 1] = 39
    text_buf[pos + n + 2] = 35
    text_buf[pos + n + 3] = 40
    return n + 4
}

// Give each route in st_routes that needs sprite palette 3 one of its
// two slots, and remember the two colors.
fun assign_sp3() {
    sp3_c1 = 0
    sp3_c2 = 0
    var i: u8 = 0
    while i < st_nroutes {
        var r: u8 = st_routes[i]
        var c: u8 = ROUTE_SP3[r]
        if c != 0 {
            if c == sp3_c1 {
                route_slot[r] = 1
            } else if c == sp3_c2 {
                route_slot[r] = 2
            } else if sp3_c1 == 0 {
                sp3_c1 = c
                route_slot[r] = 1
            } else if sp3_c2 == 0 {
                sp3_c2 = c
                route_slot[r] = 2
            } else {
                route_slot[r] = 3
            }
        }
        i += 1
    }
    if sp3_c1 == 0 {
        sp3_c1 = 0x14
    }
    if sp3_c2 == 0 {
        sp3_c2 = 0x28
        if sp3_c1 == 0x28 {
            sp3_c2 = 0x14
        }
    }
}

// Make sure route r has a sprite palette 3 slot, taking slot 2 if it
// has none. For the train's own route when it isn't in st_routes.
fun claim_sp3(r: u8) {
    var c: u8 = ROUTE_SP3[r]
    if c == 0 or c == sp3_c1 or c == sp3_c2 {
        if c == sp3_c1 {
            route_slot[r] = 1
        } else if c == sp3_c2 {
            route_slot[r] = 2
        }
        return
    }
    sp3_c2 = c
    route_slot[r] = 2
}

// Draw route r's bullet with its top-left corner at (x, y).
fun draw_bullet(x: u8, y: u8, r: u8) {
    var t: u8 = ROUTE_TILE[r]
    var a: u8 = ROUTE_PAL[r]
    if a == 3 and route_slot[r] == 2 {
        t += S_BULLET2 - S_BULLET1
    }
    draw SpriteTiles at: (x, y) frame: t attr: a
}

// Sprite palette 3 through the VRAM buffer, while rendering.
fun sp3_update() {
    nt_set(29, 248, sp3_c1)
    nt_set(30, 248, sp3_c2)
}
