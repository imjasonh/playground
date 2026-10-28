// keep/state.ne: globals shared by the fixed-bank frame handlers
// and the raycast. Each comment names the writer.

// Play writes these from input. reset_level reloads the start.
var px: u8 = 40
var py: u8 = 48
var ang: u8 = 0
var health: u8 = 5
var ammo: u8 = 12
// Frames left in the hurt lock. Play counts it down.
var phurt: u8 = 0
// Muzzle flash frames. Play counts it down.
var flash: u8 = 0

// 0 until the player presses something. Title and Play write it.
// While it stays 0, Play turns in place so the title demo has a view.
var human: u8 = 0

// Cast / paint / idle. Play writes it.
var phase: u8 = 2
// Next column or row to publish. Play writes them.
var cast_i: u8 = 0
var paint_row: u8 = 0
// Completed views. Play increments it. The probe waits on it.
var rendered: u8 = 0
// Demo pause between turns. Play writes it.
var attract_wait: u8 = 0
// Guard think clock. Play writes both.
var ai_timer: u8 = 0
var ai_due: u8 = 0

// End writes this. 0 is escaped, 1 is dead.
var outcome: u8 = 0
// Rows of the window End has blanked.
var end_row: u8 = 0

// Title writes the blink.
var title_timer: u8 = 0
var title_blink: u8 = 0

// Guard bodies. reset_level and the guard step write positions.
// Fire writes health. 0 health is a downed guard.
var gx: u8[4] = [104, 72, 184, 136]
var gy: u8[4] = [48, 136, 184, 216]
var ghp: u8[4] = [2, 2, 2, 2]
// Shots the guard skips after firing. move_guards writes it.
var gcool: u8[4] = [0, 0, 0, 0]
// Cell index currently claimed in occ. rebuild_occ writes it.
var gcell: u8[4] = [0, 0, 0, 0]

// What the last finished cast saw. Copied from gnext when the cast
// ends, and read by the sprite draw and by fire.
var gseen: u8[4] = [0, 0, 0, 0]
var gcol0: u8[4] = [0, 0, 0, 0]
var gcol1: u8[4] = [0, 0, 0, 0]
var gdist: u8[4] = [0, 0, 0, 0]

// The cast in progress. begin_cast clears it, cast_column fills it.
var gnext: u8[4] = [0, 0, 0, 0]
var gn0: u8[4] = [0, 0, 0, 0]
var gn1: u8[4] = [0, 0, 0, 0]
var gnd: u8[4] = [0, 0, 0, 0]

// One byte per map cell. 0 is empty, otherwise guard index + 1.
// rebuild_occ is the only writer.
var occ: u8[256]

// Finished column record. cast_column writes it, the painter reads it.
var col_h: u8[16]
var col_type: u8[16]
var col_side: u8[16]
