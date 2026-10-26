// rampart/constants.ne: tile numbers, layout, and rules tables.

// ── Tiles (see scripts/gen_rampart.py) ──────────────────────
const T_SPACE: u8 = 32
const T_MISS: u8 = 10
const T_DIGIT0: u8 = 48
const T_X: u8 = 88
const T_PLUS: u8 = 43
const T_MINUS: u8 = 45
const T_QUEST: u8 = 63
const T_PIKE1: u8 = 96
const T_PIKE2: u8 = 100
const T_MAUL1: u8 = 104
const T_MAUL2: u8 = 108
const T_CURSOR: u8 = 112
const T_BOX: u8 = 116
const T_ARROW: u8 = 118

// ── Screen layout (nametable cells) ─────────────────────────
// Columns 0 and 31 are left blank: TVs and most emulators crop them.
const BOARD_PX: u8 = 8
const PANEL_X: u8 = 25
const PANEL_W: u8 = 6
const PLATE_X: u8 = 25
const TURN_X: u8 = 23
const MSG_ROW1: u8 = 27
const MSG_ROW2: u8 = 28
const INFO_ROW: u8 = 1
// Panel block top rows for P1 and P2.
const P_BASE: u8[2] = [2, 14]

// ── Board ───────────────────────────────────────────────────
const BOARD_N: u8 = 12
const NUM_RUINS: u8 = 6
const RUIN_X: u8[6] = [4, 4, 5, 7, 7, 6]
const RUIN_Y: u8[6] = [4, 5, 4, 7, 6, 7]
const START_X: u8[2] = [1, 10]
const START_Y: u8[2] = [10, 1]

// ── Actions, in resolve order ───────────────────────────────
const A_SNAP: u8 = 0
const A_STEP: u8 = 1
const A_SHIELD: u8 = 2
const A_STANDARD: u8 = 3
const A_RUSH: u8 = 4
const A_AIMED: u8 = 5
const A_CHARGE: u8 = 6
const NUM_ACTIONS: u8 = 7
const NUM_PLANS: u8 = 17
const BIT: u8[8] = [1, 2, 4, 8, 16, 32, 64, 128]
const ACTION_STR: u8[7] = [S_A_SNAP, S_A_STEP, S_A_SHIELD, S_A_STANDARD, S_A_RUSH, S_A_AIMED, S_A_CHARGE]
// The panel is PANEL_W columns wide.
const ACTION_PANEL_STR: u8[7] = [S_A_SNAP, S_A_STEP, S_A_SHIELD, S_A_STANDARD_SHORT, S_A_RUSH, S_A_AIMED, S_A_CHARGE]

// Scatter type per shot action (0 snap, 1 standard, 2 aimed).
// Melee uses the aimed spread.
const SCATTER_OF: u8[7] = [0, 2, 2, 1, 2, 2, 2]

// Shift per die face 1..6, stored +2 so it fits a u8.
//   snap      -2 -2 -1 +1 +2 +2
//   standard  -1 -1  0  0 +1 +1
//   aimed     -1  0  0  0  0 +1
const SCATTER: u8[18] = [0, 0, 1, 3, 4, 4, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2, 3]

// The same spreads as distinct shifts with their face counts, for
// the hard CPU's expected-value aim. Four slots per type; a zero
// weight ends the list.
const SPREAD_V: u8[12] = [0, 1, 3, 4, 1, 2, 3, 0, 1, 2, 3, 0]
const SPREAD_W: u8[12] = [2, 1, 1, 2, 2, 2, 2, 0, 1, 4, 1, 0]

// ── Body plate ──────────────────────────────────────────────
const L_HEAD: u8 = 0
const L_GUN: u8 = 1
const L_SHIELD: u8 = 2
const L_ARML: u8 = 3
const L_ARMR: u8 = 4
const L_MAST: u8 = 5
const L_PAULL: u8 = 6
const L_PAULR: u8 = 7
const L_HULL: u8 = 8
const L_LEGL: u8 = 9
const L_LEGR: u8 = 10
const L_NONE: u8 = 11
const NUM_LOCS: u8 = 11
const LOSS_CRITS: u8 = 6

const PLATE: u8[36] = [
    11, 5, 5, 11, 11, 11,
    6, 6, 0, 0, 7, 7,
    3, 3, 8, 1, 4, 4,
    3, 2, 8, 1, 4, 4,
    9, 9, 8, 8, 10, 10,
    9, 9, 11, 11, 10, 10
]
const START_ARMOR: u8[11] = [2, 3, 3, 4, 4, 2, 3, 3, 4, 4, 4]
const LOC_STR: u8[12] = [S_L_HEAD, S_L_GUN, S_L_SHIELD, S_L_ARML, S_L_ARMR, S_L_MAST, S_L_PAULL, S_L_PAULR, S_L_HULL, S_L_LEGL, S_L_LEGR, S_L_MISS]

// ── Mechs and weapons ───────────────────────────────────────
// Frame 0 is the Pike, frame 1 the Maul. Each has three weapons
// at FRAME*3 + slot: slot 0 is the gun, slot 1 the left-arm
// weapon, slot 2 the right-arm melee weapon.
const FRAME_STR: u8[2] = [S_PIKE, S_MAUL]
const W_SLOT_LOC: u8[3] = [1, 3, 4]
const W_RANGE: u8[6] = [8, 6, 1, 6, 10, 1]
const W_AP: u8[6] = [1, 0, 2, 0, 0, 3]
const W_DMG: u8[6] = [3, 1, 3, 2, 2, 4]
const W_STR: u8[6] = [S_W_LANCE, S_W_STUB, S_W_BLADE, S_W_CANNON, S_W_POD, S_W_HAMMER]
const NO_WEAPON: u8 = 255

const SAVE_TARGET: u8 = 5
const STEP_RANGE: u8 = 3
const CHARGE_RANGE: u8 = 2
// floor(2d6 / 3) for sums 0..12.
const RUSH_TABLE: u8[13] = [0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4]
const MAX_TURNS: u8 = 30

// ── Match setup ─────────────────────────────────────────────
const MODE_CPU2: u8 = 0
const MODE_1P: u8 = 1
const MODE_2P: u8 = 2
const MODE_STR: u8[3] = [S_M_CPU2, S_M_1P, S_M_2P]
const LEVEL_EASY: u8 = 0
const LEVEL_MED: u8 = 1
const LEVEL_HARD: u8 = 2
const LEVEL_STR: u8[3] = [S_D_EASY, S_D_MED, S_D_HARD]

// Two-press code buttons, in card order.
const B_NONE: u8 = 255

// Hard CPU: hit weight per scatter type, out of six.
const HIT_W: u8[3] = [2, 3, 4]

// ── Message timing (frames) ─────────────────────────────────
const T_SHORT: u8 = 50
const T_LONG: u8 = 90
