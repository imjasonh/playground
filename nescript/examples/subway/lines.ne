// Schedule lookups. These live in the Lines bank with the pattern
// tables they read.
//
// A stop pattern is one route's sequence of stops in one direction.
// pc[p] counts ticks since pattern p's last departure from its first
// stop, wrapped at the headway, so a train is at stop k whenever
// pc[p] equals PS_MOD at that stop.

// Advance every pattern's phase counter by one tick.
fun advance_patterns() {
    var p: u8 = 0
    while p < NUM_PATTERNS {
        var c: u8 = pc[p] + 1
        if c >= PAT_HEAD[p] {
            c = 0
        }
        pc[p] = c
        p += 1
    }
}

// Set every phase counter to its value at the start time.
fun reset_patterns() {
    var p: u8 = 0
    while p < NUM_PATTERNS {
        pc[p] = PAT_PC0[p]
        p += 1
    }
}

fun stop_offset(p: u8, k: u8) -> u16 {
    var off: u16 = (PAT_OFF_HI[p] as u16) << 8
    off = off + (PAT_OFF_LO[p] as u16)
    return off + (k as u16)
}

// Ticks until the next train of pattern p is at its stop k. 0 means
// a train is there now.
fun wait_at(p: u8, k: u8) -> u8 {
    var off: u16 = stop_offset(p, k)
    var m: u8 = PS_MOD[off]
    var c: u8 = pc[p]
    if c == m {
        return 0
    }
    if m > c {
        return m - c
    }
    return PAT_HEAD[p] - (c - m)
}

// Station of pattern p's stop k.
fun stop_station(p: u8, k: u8) -> u16 {
    var off: u16 = stop_offset(p, k)
    var st: u16 = (PS_ST_HI[off] as u16) << 8
    return st + (PS_ST_LO[off] as u16)
}

// Ticks from pattern p's stop k to stop k + 1.
fun stop_gap(p: u8, k: u8) -> u8 {
    var off: u16 = stop_offset(p, k)
    return PS_CUM[off + 1] - PS_CUM[off]
}

fun pat_route(p: u8) -> u8 {
    return PAT_ROUTE[p]
}

fun pat_head(p: u8) -> u8 {
    return PAT_HEAD[p]
}

fun pat_len(p: u8) -> u8 {
    return PAT_LEN[p]
}

fun pat_dir(p: u8) -> u8 {
    return PAT_DIR[p]
}

fun pat_dest(p: u8) -> u16 {
    var st: u16 = (PAT_DEST_HI[p] as u16) << 8
    return st + (PAT_DEST_LO[p] as u16)
}

// Pixels covered f frames after leaving a stop (or f frames before
// reaching one), for f up to ACCEL_FRAMES.
fun accel_dist(f: u8) -> u16 {
    var d: u16 = (ACC_HI[f] as u16) << 8
    return d + (ACC_LO[f] as u16)
}

// Fill the platform service list for station st, direction dir:
// plat_n entries of (pattern, stop index).
fun load_platform(st: u16, dir: u8) {
    var off: u16 = (ST_SRV_HI[st] as u16) << 8
    off = off + (ST_SRV_LO[st] as u16)
    var n: u8 = ST_SRV_N[st]
    if dir == 1 {
        off = off + (n as u16)
        n = ST_SRV_S[st]
    }
    plat_n = n
    var i: u8 = 0
    while i < n {
        plat_p[i] = SRV_PAT[off]
        plat_k[i] = SRV_IDX[off]
        off += 1
        i += 1
    }
}
