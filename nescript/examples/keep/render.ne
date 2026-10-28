// keep/render.ne: publish the window, then the sprites.
//
// A horizontal run of one tile becomes one nt_fill_h. A row of 16
// distinct tiles is 16 entries, 64 bytes. Two rows fit in the ring
// with room to spare. Shaded walls (the ones whose ray crossed a
// horizontal grid line) use the dark tile of that material.

fun wall_chr(kind: u8, side: u8) -> u8 {
    if kind == CELL_EXIT {
        return CHR_EXIT
    }
    if kind == CELL_DOOR {
        return CHR_DOOR
    }
    if kind == CELL_STONE {
        if side == 0 {
            return CHR_STONE_DARK
        }
        return CHR_STONE
    }
    if side == 0 {
        return CHR_BRICK_DARK
    }
    return CHR_BRICK
}

fun tile_at(col: u8, row: u8) -> u8 {
    var h: u8 = col_h[col]
    var top: u8 = 8 - h
    var bot: u8 = 8 + h
    if row < top {
        return CHR_BLANK
    }
    if row >= bot {
        return CHR_FLOOR
    }
    return wall_chr(col_type[col], col_side[col])
}

fun emit_row(row: u8) {
    var c: u8 = 0
    while c < VIEW_W {
        var tile: u8 = tile_at(c, row)
        var n: u8 = 1
        while (c + n) < VIEW_W {
            if tile_at(c + n, row) != tile {
                break
            }
            n = n + 1
        }
        nt_fill_h(VIEW_X + c, VIEW_Y + row, n, tile)
        c = c + n
    }
}

fun glyph(x: u8, y: u8, g: u8) {
    draw Glyph at: (x, y) frame: g attr: SP_HUD
}

fun draw_guards() {
    for i in 0..NUM_GUARDS {
        if gseen[i] != 0 and ghp[i] != 0 {
            var mid: u8 = (gcol0[i] + gcol1[i]) >> 1
            var h: u8 = WALL_H[gdist[i]]
            var feet: u8 = (VIEW_Y + 8 + h) << 3
            var sx: u8 = (VIEW_X << 3) + (mid << 3)
            if h >= 5 {
                draw GuardNear at: (sx - 8, feet - 48) attr: SP_ACTOR
            } else {
                if h >= 3 {
                    draw Guard at: (sx - 4, feet - 16) attr: SP_ACTOR
                } else {
                    draw Head at: (sx, feet - 8) attr: SP_ACTOR
                }
            }
        }
    }
}

fun draw_hud() {
    var i: u8 = 0
    while i < START_HP {
        var hx: u8 = 16 + (i << 3)
        if i < health {
            draw Heart at: (hx, 184) attr: SP_HUD
        } else {
            draw HeartEmpty at: (hx, 184) attr: SP_HUD
        }
        i = i + 1
    }
    var tens: u8 = 0
    var n: u8 = ammo
    if n >= 10 {
        tens = 1
        n = n - 10
    }
    draw Glyph at: (200, 184) frame: G_0 + tens attr: SP_ACTOR
    draw Glyph at: (208, 184) frame: G_0 + n attr: SP_ACTOR
}

fun draw_play() {
    draw Gun at: (116, 144) attr: SP_GUN
    if flash != 0 {
        draw Flash at: (120, 128) attr: SP_HUD
    }
    draw_guards()
    draw_hud()
}
