// Station lookups. These live in the Stations bank with the tables
// they read, and return results through globals.

// Copy station `st`'s name into text_buf.
fun load_name(st: u16) {
    var off: u16 = (ST_NAME_HI[st] as u16) << 8
    off = off + (ST_NAME_LO[st] as u16)
    text_len = ST_NAME_LEN[st]
    var i: u8 = 0
    while i < text_len {
        text_buf[i] = NAME_TEXT[off]
        off += 1
        i += 1
    }
}

// Copy the platform direction label of station `st` into text_buf.
fun load_label(st: u16, dir: u8) {
    var lab: u8 = ST_LAB_N[st]
    if dir == 1 {
        lab = ST_LAB_S[st]
    }
    var off: u16 = (LAB_HI[lab] as u16) << 8
    off = off + (LAB_LO[lab] as u16)
    text_len = LAB_LEN[lab]
    var i: u8 = 0
    while i < text_len {
        text_buf[i] = LAB_TEXT[off]
        off += 1
        i += 1
    }
}

// Copy the routes that stop at station st into st_routes.
fun load_routes(st: u16) {
    var off: u16 = (ST_RTE_HI[st] as u16) << 8
    off = off + (ST_RTE_LO[st] as u16)
    var n: u8 = ST_RTE_LEN[st]
    if n > 12 {
        n = 12
    }
    st_nroutes = n
    var i: u8 = 0
    while i < n {
        st_routes[i] = RTE_LIST[off]
        off += 1
        i += 1
    }
}

// The next station in st's complex, or st itself.
fun next_in_complex(st: u16) -> u16 {
    var n: u16 = (ST_NEXT_HI[st] as u16) << 8
    return n + (ST_NEXT_LO[st] as u16)
}

// The previous station in st's complex. The tables store the ring
// in one direction, so walk it until it comes back around.
fun prev_in_complex(st: u16) -> u16 {
    var prev: u16 = st
    var n: u16 = next_in_complex(st)
    while n != st {
        prev = n
        n = next_in_complex(n)
    }
    return prev
}

// Leave this station for the next one in the complex, or the
// previous one when forward is false. A one-station complex stays.
// The caller reloads the platform. platform_setup switches the
// $8000 bank, and this function is still running from that window.
fun take_passage(forward: bool) -> bool {
    var n: u16 = cur_st
    if forward {
        n = next_in_complex(cur_st)
    } else {
        n = prev_in_complex(cur_st)
    }
    if n == cur_st {
        return false
    }
    cur_st = n
    return true
}

fun station_flags(st: u16) -> u8 {
    return ST_FLAGS[st]
}

// Station st's position on the pause map.
fun map_x(st: u16) -> u8 {
    return ST_MAP_X[st]
}

fun map_y(st: u16) -> u8 {
    return ST_MAP_Y[st]
}
