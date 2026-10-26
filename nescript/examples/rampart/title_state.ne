// rampart/title_state.ne: match setup menu.
//
// Up and down pick a row; left and right change it; START (or A on
// the START row) begins the match. Left alone for about seven
// seconds, the title starts a CPU-against-CPU demo match.

const MENU_ROWS: u8[5] = [13, 15, 17, 19, 21]
// Top-left cells of the P1 and P2 portraits.
const PORTRAIT_X: u8[2] = [2, 24]
const PORTRAIT_Y: u8 = 23
const MENU_VALUE_X: u8 = 16
const DEMO_IDLE: u8 = 200

fun paint_menu_value(row: u8) {
    var y: u8 = MENU_ROWS[row]
    put_clear(MENU_VALUE_X, y, 12)
    if row == 0 {
        put_str(MENU_VALUE_X, y, MODE_STR[mode])
    } else if row == 1 {
        put_str(MENU_VALUE_X, y, LEVEL_STR[cpu_level])
    } else if row >= 2 {
        var p: u8 = row - 2
        put_str(MENU_VALUE_X, y, FRAME_STR[mech_frame[p]])
        paint_portrait(PORTRAIT_X[p], PORTRAIT_Y, mech_frame[p])
    }
}

state Title {
    var sel: u8 = 4
    var idle: u8 = 0
    var ticks: u8 = 0
    var seed: u16 = 0x2B1D

    on enter {
        swap_background(0)
        if demo {
            demo = false
            mode = MODE_1P
        }
        var r: u8 = 0
        while r < 4 {
            paint_menu_value(r)
            r += 1
        }
        put_str(10, 25, S_PRESS_START)
    }

    on frame {
        tick_unblank()
        flush_text()
        ticks += 1
        seed += 1
        if (ticks & 1) == 0 {
            idle += 1
        }

        var changed: bool = false
        var delta: u8 = 0
        if p1.button.up.pressed and sel > 0 {
            sel -= 1
            changed = true
        }
        if p1.button.down.pressed and sel < 4 {
            sel += 1
            changed = true
        }
        if p1.button.right.pressed {
            delta = 1
        }
        if p1.button.left.pressed {
            delta = 2
        }
        if delta != 0 {
            changed = true
            if sel == 0 {
                mode = (mode + delta) % 3
            } else if sel == 1 {
                cpu_level = (cpu_level + delta) % 3
            } else if sel == 2 {
                mech_frame[0] = mech_frame[0] ^ 1
            } else if sel == 3 {
                mech_frame[1] = mech_frame[1] ^ 1
            }
            if sel < 4 {
                paint_menu_value(sel)
            }
        }
        if changed {
            idle = 0
        }

        var go: bool = false
        if p1.button.start.pressed {
            go = true
        }
        if p1.button.a.pressed and sel == 4 {
            go = true
        }
        if idle >= DEMO_IDLE {
            demo = true
            mode = MODE_CPU2
            cpu_level = LEVEL_HARD
            go = true
        }

        draw Tileset at: (16, MENU_ROWS[sel] * 8 - 1) attr: SP_FIRE frame: T_ARROW
        if go {
            seed_rand(seed)
            if mode == MODE_CPU2 {
                apply_stock(0)
                apply_stock(1)
                transition Battle
            } else {
                transition Customize
            }
        }
    }
}
