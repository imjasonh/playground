// rampart/state.ne: globals that outlive a single state.

// ── Match setup (Title writes, Battle reads) ────────────────
var mode: u8 = MODE_1P
var cpu_level: u8 = LEVEL_MED
var mech_frame: u8[2] = [0, 1]
// Two weapon ids per player, gun mount then right-arm mount.
var loadout: u8[4]
// Six name letters per player, as tile numbers. 32 is a space.
var name_ch: u8[12]
// Customize screen cursor. The handlers live in the Brain bank,
// so these are globals rather than state locals.
var cust_who: u8 = 0
var cust_cursor: u8 = 0
var cust_tick: u8 = 0
// Set by the title autopilot so the demo match returns to Title.
var demo: bool = false

// ── Mechs ───────────────────────────────────────────────────
var mech_x: u8[2]
var mech_y: u8[2]
// Armor per location, at player * 11 + location. Zero is critical.
var armor: u8[22]
var crits: u8[2]
var shield_up: u8[2]
// Locked plan index per player.
var plan: u8[2]
var turn: u8 = 1

// ── Rendering ───────────────────────────────────────────────
// Frames left before rendering comes back on after a background
// swap; see swap_background in render.ne.
var unblank: u8 = 0

// Text queue: print commands that flush_text() turns into VRAM
// ring writes, a bounded number of tiles per frame.
var q_kind: u8[64]
var q_x: u8[64]
var q_y: u8[64]
var q_arg: u8[64]
var q_head: u8 = 0
var q_tail: u8 = 0

// Message cursor for msg_* helpers.
var msg_x: u8 = 0
var msg_y: u8 = 0

// Scratch results from rules helpers that compute two values.
var res_a: u8 = 0
var res_b: u8 = 0
