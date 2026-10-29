// Riding: inside the car, facing the far wall. The windows show the
// tunnel, the stations, and the elevated skyline sliding by; the car
// sways and bumps over rail joints while it moves. The ride follows the
// schedule: the train leaves when the platform view would show it
// leaving and reaches the next stop after that stop's running time.
//
// Controls: left and right walk, up and down move between the seats
// and the aisle. Up at an open door steps off. B punches, A kicks, and
// fight.ne has the rest. Holding B between stations with no fight on
// rides faster. A fight can start as the train leaves a stop.
//
// See scenery.ne for the window band.

const Z_TUNNEL: u8 = 0
const Z_A: u8 = 1
const Z_B: u8 = 2
const Z_SKY: u8 = 3

// Station columns reach this far past a stop, both ways.
const ST_REACH: u16 = 96
// Columns are compared with this bias added, so columns behind the
// last stop stay positive.
const BIAS: u16 = 256

// Scenery state read by scenery.ne.
var seg_c0: u16 = 0
var b_c0: u16 = 0x3000
var mid_c: u16 = 0x3000
var out_a: bool = false
var out_b: bool = false
var name_a: u8[8]
var len_a: u8 = 0
var name_b: u8[8]
var len_b: u8 = 0
var col_buf: u8[5]

const RIDE_MIN_Y: u8 = 132
const RIDE_MAX_Y: u8 = 200
// First scanline of the window band (the splits at 40 and 112 put the
// car back after the HUD and after the band).
const SPLIT_BAND: u8 = 72

// Where the ride is: 0 standing at stop ride_k, 1 running to it.
var rphase: u8 = 0
var at_end: bool = false
// Band scroll in pixels, and the scroll at the last stop.
var rx: u16 = 0
var seg_x0: u16 = 0
// Pixels and frames of motion from the last stop to the next.
var seg_d: u16 = 0
var seg_t: u16 = 0
var half_passed: bool = false
var rstream: u16 = 33

var rdoors: bool = false
var rdoor_job: u8 = 0
var pal_job: bool = false
var mos_b: u8 = 0

// LED sign: what it is showing, and which half still needs writing.
var led_mode: u8 = 255
var led_page: u8 = 0
var led_timer: u8 = 0
var led_job: u8 = 0
var led_buf: u8[28]
var hud_job: bool = false
var clock_job: bool = false

// Transfers at the station the HUD lists.
var xfer_n: u8 = 0
var xfer: u8[12]

// Sway: interior scroll offsets (ix moves the car, iy jolts the whole
// screen), and the counters that drive them.
var ix: u8 = 0
var iy: u8 = 0
var sway_t: u8 = 0
var bump_t: u8 = 0
var joint: u8 = 0

const LED_PAGE_FRAMES: u8 = 150

state Riding {
    on enter {
        on_train = true
        if resume {
            resume = false
            ride_setup()
            fight_enter(1)
            return
        }
        pl_x = door_px
        pl_y = RIDE_MIN_Y
        fight_clear()
        rphase = 0
        at_end = false
        rx = 0
        seg_x0 = 0
        seg_c0 = 0
        b_c0 = 0x3000
        mid_c = 0x3000
        seg_d = 0
        seg_t = 0
        set_station_a(stop_station(ride_p, ride_k))
        ride_setup()
        fight_enter(1)
    }

    on frame {
        frame_top()
        frame_count += 1
        if button.start.pressed {
            pause_from = 1
            transition PauseMap
        }

        var fighting: bool = fight_on()
        var speed: u8 = 1
        if button.b and rphase == 1 and not fighting {
            speed = 3
        }
        clock_step(speed)
        if ticked {
            clock_job = true
        }
        var was: u8 = rphase
        ride_update()
        if was == 0 and rphase == 1 {
            fight_maybe()
        }
        sway_update()
        set_splits()

        var n: u8 = ride_stream()
        if n < 2 {
            ride_jobs()
        }
        if n == 0 {
            fight_hud()
        }

        fight_input()
        var st: u8 = pl_step
        var ready: bool = pl_act == A_IDLE
        pl_moving = false
        if button.right and st > 0 and pl_x < 232 {
            pl_x += st
            if pl_x > 232 {
                pl_x = 232
            }
            if ready {
                pl_flip = true
            }
            pl_moving = true
        }
        if button.left and st > 0 and pl_x > 8 {
            pl_x -= st
            if pl_x < 8 {
                pl_x = 8
            }
            if ready {
                pl_flip = false
            }
            pl_moving = true
        }
        if not button.up {
            up_lock = false
        }
        if button.up and st > 0 {
            if pl_y > RIDE_MIN_Y {
                pl_y -= 1
                pl_moving = true
            } else if ready and not up_lock and rdoors and at_door(pl_x) {
                up_lock = true
                cur_st = stop_station(ride_p, ride_k)
                cur_dir = pat_dir(ride_p)
                door_px = pl_x
                transition Platform
            }
        }
        if button.down and st > 0 and pl_y < RIDE_MAX_Y {
            pl_y += 1
            pl_moving = true
        }
        fight_update()
        fight_draw(ix)
        draw_bullet(8, 7, pat_route(ride_p))
        // Four of the gang fill the sprites the transfer bullets use.
        if not fighting {
            draw_xfers()
        }
        draw_band_sprites()
    }

    on scanline(40) {
        asm {
            LDA {ix}
            STA $2005
            LDA #0
            STA $2005
            LDA #$88
            STA $2000
        }
    }

    on scanline(72) {
        asm {
            LDA {band_x}
            STA $2005
            LDA #0
            STA $2005
            LDA {band_ctrl}
            STA $2000
        }
    }

    on scanline(112) {
        asm {
            LDA {ix}
            STA $2005
            LDA #0
            STA $2005
            LDA #$88
            STA $2000
        }
    }
}

