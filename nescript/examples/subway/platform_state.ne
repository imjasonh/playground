// The platform: a side view across the track. Trains arrive, dwell,
// and leave on the schedule, sliding through the track band (rows
// 10-17) while the wall, HUD, and platform stay put. See band.ne for
// how the band scrolls.
//
// Controls: left and right walk, up and down step toward or away from
// the edge. Up at an open door boards the train. Walking off the left
// end takes the passage to the next station in the complex, and
// walking off the right end takes it to the previous one. A switches
// to the other direction on this station. Hold B to wait faster while
// no train is in.

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
    var px: u8 = 120
    var py: u8 = 160
    var flip: bool = false
    var walk: u8 = 0

    on enter {
        top_y = 0
        if not patterns_ready {
            reset_patterns()
            patterns_ready = true
        }
        if resume {
            resume = false
            px = save_px
            py = save_py
            flip = save_flip
        } else if on_train {
            // Stepping off: stand at the door the player used.
            px = door_px
            py = PLAYER_MIN_Y
        }
        on_train = false
        platform_setup()
    }

    on frame {
        frame_top()
        frame_count += 1
        if button.start.pressed {
            save_px = px
            save_py = py
            save_flip = flip
            pause_from = 0
            transition PauseMap
        }

        var speed: u8 = 1
        if button.b and tp == TP_NONE {
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
        }

        // Walk. Off the left end is the next station in the complex,
        // and you come out at its right end. Off the right end is the
        // previous station, and you come out at its left end.
        var moving: bool = false
        var changed: bool = false
        if button.right {
            if px < 232 {
                px += 1
            } else if take_passage(false) {
                px = 8
                changed = true
            }
            flip = true
            moving = true
        }
        if button.left {
            if px > 0 {
                px -= 1
            } else if take_passage(true) {
                px = 224
                changed = true
            }
            flip = false
            moving = true
        }
        if changed {
            platform_setup()
            return
        }
        if not button.up {
            up_lock = false
        }
        if button.up {
            if py > PLAYER_MIN_Y {
                py -= 1
                moving = true
            } else if not up_lock and can_board(px) {
                up_lock = true
                ride_p = tp_p
                ride_k = tp_k
                door_px = px
                transition Riding
            }
        }
        if button.down and py < PLAYER_MAX_Y {
            py += 1
            moving = true
        }
        if button.a.pressed {
            cur_dir = cur_dir ^ 1
            platform_setup()
            return
        }
        var f: u8 = S_PLAYER0
        if moving {
            walk += 1
            var phase: u8 = (walk >> 3) & 3
            if phase == 1 {
                f = S_PLAYER1
            } else if phase == 3 {
                f = S_PLAYER2
            }
        } else {
            walk = 0
        }
        draw_player(px, py, f, flip)
        draw_hud_bullets()
        draw_sign_bullets()
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

