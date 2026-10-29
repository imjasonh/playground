// Street fights, on the platforms and in the cars. fight.ne (bank
// Fight) runs them; the Platform and Riding states walk Alex, then
// hand the rest of the frame to it.

// What a fighter is doing. A_GONE is 0 so the zeroed enemy slots
// start out empty.
const A_GONE: u8 = 0
const A_IDLE: u8 = 1
const A_PUNCH: u8 = 2
const A_KICK: u8 = 3
const A_JUMP: u8 = 4
const A_HURT: u8 = 5
const A_DOWN: u8 = 6
// Beaten: lies blinking, then leaves.
const A_KO: u8 = 7
// Off screen, en_t frames from walking in.
const A_WAIT: u8 = 8

const MAX_EN: u8 = 4
// One point per pixel of the stamina bar.
const PL_MAX_HP: u8 = 64

// HUD row 4: the stamina bar and the cash.
const HUD_ROW: u8 = 4
const HUD_BAR_X: u8 = 14
const HUD_CASH_X: u8 = 24

// Alex. pl_y is the top of his standing sprite on the floor, and pl_z
// how far a jump has lifted him off it. The art faces left, so
// pl_flip means he faces right.
var pl_x: u8 = 120
var pl_y: u8 = 160
var pl_z: u8 = 0
var pl_flip: bool = false
var pl_act: u8 = A_IDLE
var pl_t: u8 = 0
var pl_walk: u8 = 0
// Set by the states when Alex walked this frame.
var pl_moving: bool = false
// Pixels a frame Alex may walk, from fight_input: 0 while he punches,
// kicks, or is hurt, 2 while he runs.
var pl_step: u8 = 1
var pl_hp: u8 = PL_MAX_HP
var pl_inv: u8 = 0
var pl_run: bool = false
// The attack in progress started from a run.
var pl_dash: bool = false
var pl_jk: bool = false
var pl_hit: bool = false
var pl_combo: u8 = 0
var pl_ct: u8 = 0
var pl_kb: u8 = 0
var pl_kbr: bool = false
// Double-tap detection: the last direction pressed (1 left, 2 right)
// and the frames left to press it again.
var tap_dir: u8 = 0
var tap_t: u8 = 0
// Cash as dollars and cents, so the HUD needs no division.
var cash_d: u8 = 0
var cash_c: u8 = 0

// The gang, one entry per slot. en_flip is 1 facing right; en_kbr is 1
// knocked to the right; en_tok is the side of Alex an attacker holds
// (1 left, 2 right, 0 waiting its turn).
var en_act: u8[4]
var en_kind: u8[4]
var en_x: u8[4]
var en_y: u8[4]
var en_t: u8[4]
var en_hp: u8[4]
var en_flip: u8[4]
var en_cool: u8[4]
var en_walk: u8[4]
var en_combo: u8[4]
var en_ct: u8[4]
var en_kb: u8[4]
var en_kbr: u8[4]
var en_tok: u8[4]

// The floor fighters can stand on, for the current screen.
var fb_x0: u8 = 0
var fb_x1: u8 = 232
var fb_y0: u8 = 128
var fb_y1: u8 = 198
// No fight on the platform Alex starts on.
var fight_safe: bool = true

var spark_t: u8 = 0
var spark_x: u8 = 0
var spark_y: u8 = 0

// Draw order: fighter ids (0 Alex, 1-4 enemy slots), nearest first,
// and the rotation that takes turns dropping fighters off a crowded
// scanline.
var fd_id: u8[5]
var fd_key: u8[5]
var fd_rot: u8 = 0

// What HUD row 4 shows now (255: repaint), and its tile page.
var hud_bar0: u8 = 0
var hud_hp: u8 = 255
var hud_cd: u8 = 255
var hud_cc: u8 = 255
