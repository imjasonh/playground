// The platform: a side view across the track. Trains arrive, dwell,
// and leave on the schedule, sliding through the track band (rows
// 10-17) while the wall, HUD, and platform stay put. See band.ne for
// how the band scrolls.
//
// Controls: left and right walk, up and down step toward or away from
// the edge. Up at an open door boards the train. Walking off the left
// end takes the passage to the next station in the complex, and
// walking off the right end takes it to the previous one. Select
// switches to the other direction on this station. B punches, A
// kicks, and fight.ne has the rest. Holding B with no train in and no
// fight on waits faster.

const BAND_TOP: u8 = 80
const BAND_BOTTOM: u8 = 144

// Camera positions in band pixels. A train stops with its third car
// exactly on screen.
const CAM_STOP: u16 = 1040
const DEPART_DIST: u16 = 1024

// Ring column of screen column 0 when the train is stopped, minus 32
// (CAM_STOP / 8 = 130, 130 & 63 = 2): every door and sign cell of the
// stopped car is in nametable 0 at screen column + 2.
const STOP_RING: u8 = 2

// Train presence on this platform.
const TP_NONE: u8 = 0
const TP_ARRIVING: u8 = 1
const TP_STOPPED: u8 = 2
const TP_LEAVING: u8 = 3

// Doors open DOOR_OPEN frames into the dwell tick and close when
// DOOR_CLOSE frames are left.
const DOOR_OPEN: u8 = 210
const DOOR_CLOSE: u8 = 36

const PLAYER_MIN_Y: u8 = 128
const PLAYER_MAX_Y: u8 = 198

var cam: u16 = 0
var stream_col: u16 = 32
var tp: u8 = TP_NONE
var tp_p: u8 = 0
var tp_k: u8 = 0
var tp_mul: u8 = 1
var tp_dist: u16 = 0
var doors_open: bool = false
var doors_want: bool = false
var restore_col: u8 = 64
var hud_chunk: u8 = 0
var arr_n: u8 = 0
var arr_route: u8[3]
var arr_slot: u8[3]

// Per-frame scratch for the train lookup.
var best_w: u8 = 0
var best_i: u8 = 0

var patterns_ready: bool = false

state Platform {
    on enter {
        top_y = 0
        if not patterns_ready {
            reset_patterns()
            patterns_ready = true
        }
        var fresh: bool = not resume
        resume = false
        if fresh {
            if on_train {
                // Stepping off: stand at the door the player used.
                pl_x = door_px
                pl_y = PLAYER_MIN_Y
            }
            fight_clear()
        }
        on_train = false
        platform_setup()
        fight_enter(0)
        if fresh {
            fight_maybe()
        }
    }

    on frame {
        frame_top()
        frame_count += 1
        if button.start.pressed {
            pause_from = 0
            transition PauseMap
        }

        var speed: u8 = 1
        if button.b and tp == TP_NONE and not fight_on() {
            speed = 8
        }
        clock_step(speed)
        if ticked {
            hud_chunk = 1
        }

        find_train()
        if hud_chunk == 0 {
            cache_sign()
        }
        update_cam()
        band_x = cam as u8
        band_ctrl = CTRL_BASE | ((cam >> 8) as u8 & 1)

        var budget: u8 = stream_band()
        if budget > 0 {
            run_jobs()
        }
        if hud_chunk > 0 {
            hud_arrivals()
        } else if budget > 0 {
            fight_hud()
        }

        // Walk. Off the left end is the next station in the complex,
        // and you come out at its right end. Off the right end is the
        // previous station, and you come out at its left end. Only a
        // standing Alex turns, takes a passage, or boards.
        fight_input()
        var st: u8 = pl_step
        var ready: bool = pl_act == A_IDLE
        pl_moving = false
        var changed: bool = false
        if button.right and st > 0 {
            if pl_x < 232 {
                pl_x += st
                if pl_x > 232 {
                    pl_x = 232
                }
            } else if ready and take_passage(false) {
                pl_x = 8
                changed = true
            }
            if ready {
                pl_flip = true
            }
            pl_moving = true
        }
        if button.left and st > 0 {
            if pl_x > st {
                pl_x -= st
            } else if pl_x > 0 {
                pl_x = 0
            } else if ready and take_passage(true) {
                pl_x = 224
                changed = true
            }
            if ready {
                pl_flip = false
            }
            pl_moving = true
        }
        if changed {
            fight_safe = false
            fight_clear()
            platform_setup()
            fight_enter(0)
            fight_maybe()
            return
        }
        if not button.up {
            up_lock = false
        }
        if button.up and st > 0 {
            if pl_y > PLAYER_MIN_Y {
                pl_y -= 1
                pl_moving = true
            } else if ready and not up_lock and can_board(pl_x) {
                up_lock = true
                fight_safe = false
                ride_p = tp_p
                ride_k = tp_k
                door_px = pl_x
                transition Riding
            }
        }
        if button.down and st > 0 and pl_y < PLAYER_MAX_Y {
            pl_y += 1
            pl_moving = true
        }
        if button.select.pressed {
            cur_dir = cur_dir ^ 1
            platform_setup()
            fight_enter(0)
            return
        }
        fight_update()
        fight_draw(0)
        draw_hud_bullets()
        draw_sign_bullets()
        // The transfer hints at the edges would compete with the
        // gang's sprites; hide them for the same reason riding hides
        // its in-train transfer bullets during a fight.
        if not fight_on() {
            draw_transfer_hints()
        }
    }

    on scanline(80) {
        asm {
            LDA {band_x}
            STA $2005
            LDA #0
            STA $2005
            LDA {band_ctrl}
            STA $2000
        }
    }

    on scanline(144) {
        asm {
            LDA #0
            STA $2005
            STA $2005
            LDA #$88
            STA $2000
        }
    }
}

