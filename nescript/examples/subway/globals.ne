// Global state that survives state changes: where the player is, the
// clock, the train they ride, and scratch space for text.

// PPUCTRL: NMI on, sprites from pattern table 1, background from 0.
const CTRL_BASE: u8 = 0x88

// Clock: game ticks of 30 seconds. FRAMES_PER_TICK real frames make
// one tick, so the game runs 7.5 times faster than real time.
const FRAMES_PER_TICK: u8 = 240
var tick_frames: u8 = FRAMES_PER_TICK
var ticked: bool = false
var clock_hr: u8 = 12
var clock_min: u8 = 0
var clock_half: u8 = 0

// Where the player is: a station and a platform direction (0 north,
// 1 south).
var cur_st: u16 = 10
var cur_dir: u8 = 1

// Phase counters, one per stop pattern: ticks since the pattern's
// last departure from its first stop, wrapped at the headway.
var pc: u8[56]

// The patterns that stop at the current platform: plat_n entries of
// (pattern, stop index), from load_platform.
var plat_n: u8 = 0
var plat_p: u8[6]
var plat_k: u8[6]

// The train the player is on, or just left: pattern and stop index.
var ride_p: u8 = 0
var ride_k: u8 = 0
var on_train: bool = false
// The player's x at the door they used to board or leave.
var door_px: u8 = 32
// Set when Up boards or leaves a train; Up must be let go before it
// boards or leaves again, so holding it through the doors doesn't
// step straight back on.
var up_lock: bool = false

// The pause map: which state it came from (0 platform, 1 riding).
// resume tells that state to pick up where it left off.
var pause_from: u8 = 0
var resume: bool = false

// Routes that stop at a station, from load_routes, and which slot of
// sprite palette 3 each route's bullet uses.
var st_routes: u8[12]
var st_nroutes: u8 = 0
var route_slot: u8[25]
var sp3_c1: u8 = 0
var sp3_c2: u8 = 0

// Text scratch: station names and labels are copied here from the
// Stations bank, as font codes.
var text_buf: u8[32]
var text_len: u8 = 0

// The destination on the LED side signs of the train in the band, as
// font codes, for pattern sign_p (255: none).
var sign_buf: u8[12]
var sign_len: u8 = 0
var sign_p: u8 = 255

// Background scroll for the frame top and the scrolled band.
var band_x: u8 = 0
var band_ctrl: u8 = CTRL_BASE
var top_y: u8 = 0
var top_x: u8 = 0
var mask: u8 = 0

var frame_count: u8 = 0
