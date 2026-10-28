// keep/cast.ne: one ray per view column.
//
// The march adds a precomputed step, at most half a cell, and
// samples the cell it lands in. A step that crosses both a
// vertical and a horizontal grid line also samples the vertical
// side cell, so a ray cannot slip through a convex corner.

fun cell_index(x: u8, y: u8) -> u8 {
    return (y & 0xF0) | (x >> 4)
}

fun note_guard(who: u8, col: u8, steps: u8) {
    var i: u8 = who - 1
    if gnext[i] == 0 {
        gnext[i] = 1
        gn0[i] = col
        gn1[i] = col
        gnd[i] = steps
    } else {
        gn1[i] = col
        if steps < gnd[i] {
            gnd[i] = steps
        }
    }
}

fun cast_column(col: u8) {
    var a: u8 = (ang + COL_OFF[col]) & ANG_MASK
    var x: u8 = px
    var y: u8 = py
    var dx: u8 = STEP_X[a]
    var dy: u8 = STEP_Y[a]
    var steps: u8 = 0
    var hit: u8 = CELL_BRICK
    var side: u8 = 0
    while steps < MAX_STEPS {
        var pcx: u8 = x >> 4
        var pcy: u8 = y >> 4
        x = x + dx
        y = y + dy
        steps = steps + 1
        var cx: u8 = x >> 4
        var cy: u8 = y >> 4
        if cx != pcx {
            side = 1
        } else {
            side = 0
        }
        if cx != pcx and cy != pcy {
            var w1: u8 = LEVEL[(pcy << 4) | cx]
            if w1 != CELL_OPEN {
                hit = w1
                side = 1
                break
            }
        }
        var here: u8 = (cy << 4) | cx
        var t: u8 = LEVEL[here]
        if t != CELL_OPEN {
            hit = t
            break
        }
        var who: u8 = occ[here]
        if who != 0 {
            note_guard(who, col, steps)
        }
    }
    col_h[col] = WALL_H[steps]
    col_type[col] = hit
    col_side[col] = side
}

// Drop the previous guard claims, then mark the living guards.
// Two passes so one guard cannot clear a cell another just claimed.
fun rebuild_occ() {
    for i in 0..NUM_GUARDS {
        occ[gcell[i]] = 0
    }
    for i in 0..NUM_GUARDS {
        var c: u8 = cell_index(gx[i], gy[i])
        gcell[i] = c
        if ghp[i] != 0 {
            occ[c] = i + 1
        }
    }
}

fun begin_cast() {
    cast_i = 0
    phase = PH_CAST
    for i in 0..NUM_GUARDS {
        gnext[i] = 0
    }
    rebuild_occ()
}

fun finish_cast() {
    for i in 0..NUM_GUARDS {
        gseen[i] = gnext[i]
        gcol0[i] = gn0[i]
        gcol1[i] = gn1[i]
        gdist[i] = gnd[i]
    }
    phase = PH_PAINT
    paint_row = 0
}
