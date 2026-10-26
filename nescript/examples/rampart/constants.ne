// rampart/constants.ne: tile numbers, layout, and rules tables.

// ── Tiles (see scripts/gen_rampart.py) ──────────────────────
const T_SPACE: u8 = 32
const T_DIGIT0: u8 = 48
const T_PLUS: u8 = 43
const T_MINUS: u8 = 45
const T_QUEST: u8 = 63
const T_CORNER: u8 = 13
const T_AIM: u8 = 14
const T_BURST: u8 = 15
const T_SCUFF: u8 = 16
const T_HOLES: u8 = 17
const T_FIRE: u8 = 18
const T_CRATER: u8 = 20
const T_ARROW: u8 = 21
// Plan icons, in action order: Snap, Step, Shield, Standard, Rush,
// Aimed, Charge.
const T_ACT: u8 = 22
const T_PIKE: u8 = 96
const T_MAUL: u8 = 100
// Weapon pictures, two tiles each, in weapon-id order. Keep this in
// step with WPN_AT in scripts/gen_rampart.py.
const WPN_TILE: u8[10] = [104, 105, 110, 111, 9, 10, 108, 109, 11, 29]
// Frame f's portrait cell c is T_PLATE + f * 72 + c; the charred
// copy shown once a location is wrecked is T_CHARRED tiles later.
const T_PLATE: u8 = 112
const T_CHARRED: u8 = 36

// Sprite attribute bytes: palette in bits 0-1, flips in bits 6-7.
const SP_DAMAGE: u8 = 2
const SP_FIRE: u8 = 3
const FLIP_H: u8 = 0x40
const FLIP_V: u8 = 0x80

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

// ── Setup screen rows and columns ───────────────────────────
// A sprite drawn at row r sits at pixel r * 8 - 1, one pixel above
// the row's top, which centers it against the text baseline.
const NAME_ROW: u8 = 3
const NAME_COL: u8 = 8
const GUN_ROW: u8 = 16
const ARM_ROW: u8 = 18
const START_ROW: u8 = 22
const BACKSPACE_ROW: u8 = 24

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

// The plate is the mech's portrait cut into 6x6 cells; this maps
// each cell to the location it shows.
const PLATE: u8[36] = [
    5, 5, 0, 0, 1, 1,
    6, 6, 8, 8, 7, 7,
    3, 3, 8, 8, 4, 4,
    2, 3, 8, 8, 4, 4,
    11, 9, 9, 10, 10, 11,
    11, 9, 9, 10, 10, 11
]
const START_ARMOR: u8[11] = [2, 3, 3, 4, 4, 2, 3, 3, 4, 4, 4]
// Damage decals: up to two per location, at these pixel offsets
// from the plate's top-left corner. DEC_BX is 255 where a location
// has room for one decal only. DEC_FLIP mirrors the decals on the
// mech's right side.
const DEC_AX: u8[11] = [20, 36, 0, 5, 35, 4, 4, 36, 20, 11, 28]
const DEC_AY: u8[11] = [0, 0, 24, 16, 17, 1, 7, 7, 10, 33, 33]
const DEC_BX: u8[11] = [255, 255, 255, 8, 37, 255, 255, 255, 20, 12, 27]
const DEC_BY: u8[11] = [0, 0, 0, 24, 25, 0, 0, 0, 21, 41, 41]
const DEC_FLIP: u8[11] = [0, 0x40, 0, 0, 0x40, 0, 0, 0x40, 0, 0, 0x40]
const LOC_STR: u8[12] = [S_L_HEAD, S_L_GUN, S_L_SHIELD, S_L_ARML, S_L_ARMR, S_L_MAST, S_L_PAULL, S_L_PAULR, S_L_HULL, S_L_LEGL, S_L_LEGR, S_L_MISS]

// ── Mechs and weapons ───────────────────────────────────────
// Frame 0 is the Pike, frame 1 the Maul. A player brings two
// weapons, stored in loadout at p * 2 + slot. Slot 0 is mounted
// on the gun. Slot 1 is mounted on the right arm. Charge uses the
// arm weapon, and a shot uses it when the gun weapon can't reach.
// The ids index the tables below.
//   0 thermal lance   1 gatling cannon   2 missile pod
//   3 sword           4 hammer
const NUM_WEAPONS: u8 = 5
// Longest weapon name, in tiles. Setup clears this many cells
// before printing the name.
const WPN_NAME_W: u8 = 14
const FRAME_STR: u8[2] = [S_PIKE, S_MAUL]
const W_RANGE: u8[5] = [8, 6, 10, 1, 1]
const W_AP: u8[5] = [1, 0, 0, 2, 3]
const W_DMG: u8[5] = [3, 2, 2, 3, 4]
const W_STR: u8[5] = [S_W_LANCE, S_W_CANNON, S_W_POD, S_W_SWORD, S_W_HAMMER]
const NO_WEAPON: u8 = 255
// Stock pair for each frame: Pike thermal lance and sword, Maul
// gatling cannon and hammer.
const STOCK_WPN: u8[4] = [0, 3, 1, 4]
// Each player's default name, six letters, space-padded. A human
// starts editing it, a CPU keeps it, and confirming a blank name
// restores it.
const FRAME_NAME: u8[12] = [
    66, 76, 85, 69, 32, 32, // BLUE
    82, 69, 68, 32, 32, 32 // RED
]

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
