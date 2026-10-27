// The pause map (Start): the whole system, with the routes ahead lit in
// their colors, a marker where the player is, and a side panel with the
// clock, the station, and the trains or stops ahead. The clock stops
// while the map is up. Start again goes back.

// Side panel text: columns PANEL_COL to PANEL_COL + PANEL_W - 1, with
// route bullets in the first two columns of a line that has one.
const PANEL_COL: u8 = 19
const PANEL_W: u8 = 13
const BULLET_W: u8 = 11
const LIST_MAX: u8 = 6

// Attribute bytes of the map, with the lit routes' cells set to
// palette 1 or 2 (map_c1, map_c2 are their line colors).
var map_attr: u8[64]
var map_c1: u8 = 0
var map_c2: u8 = 0

// Platform: the routes listed, one bullet each. Riding: the stops
// listed, one dot each on the map.
var pm_n: u8 = 0
var pm_route: u8[6]
var pm_x: u8[6]
var pm_y: u8[6]
var here_x: u8 = 0
var here_y: u8 = 0

state PauseMap {
    on enter {
        pause_setup()
    }

    on frame {
        frame_top()
        frame_count += 1
        if button.start.pressed {
            resume = true
            if pause_from == 0 {
                transition Platform
            } else {
                transition Riding
            }
        }
        draw_pause_sprites()
    }
}

fun draw_pause_sprites() {
    if (frame_count & 0x10) == 0 {
        draw SpriteTiles at: (here_x - 3, here_y - 4) frame: S_HERE attr: 0
    }
    var i: u8 = 0
    if pause_from == 1 {
        var r: u8 = pat_route(ride_p)
        draw_bullet(PANEL_COL << 3, 31, r)
        while i < pm_n {
            draw_dot(pm_x[i] - 3, pm_y[i] - 4, r)
            i += 1
        }
        return
    }
    while i < pm_n {
        draw_bullet(PANEL_COL << 3, pm_y[i], pm_route[i])
        i += 1
    }
}

// Route r's map dot with its top-left corner at (x, y).
fun draw_dot(x: u8, y: u8, r: u8) {
    var t: u8 = ROUTE_DOT[r]
    var a: u8 = ROUTE_PAL[r]
    if a == 3 and route_slot[r] == 2 {
        t = S_DOT2
    }
    draw SpriteTiles at: (x, y) frame: t attr: a
}
