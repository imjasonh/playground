// keep/constants.ne: screen layout, tile numbers, and the level.
//
// The view is 16 nametable columns by 16 rows, which is the whole
// ray budget. Each column is one ray. A cell on the map is 16
// position units, and position fits in a byte, so the level is
// exactly 16 by 16 cells.

const VIEW_X: u8 = 8
const VIEW_Y: u8 = 4
const VIEW_W: u8 = 16
const VIEW_H: u8 = 16
const VIEW_MID: u8 = 8

// How much of a new view is published per frame. The VRAM ring is
// 256 bytes and a paint frame has to finish before the next NMI,
// so these stay small.
const COLS_PER_FRAME: u8 = 4
const ROWS_PER_FRAME: u8 = 2

const NUM_GUARDS: u8 = 4
const GUARD_HP: u8 = 2
const START_HP: u8 = 5
const START_AMMO: u8 = 12
const MAX_STEPS: u8 = 40

// Angle 0 faces +x (east). 64 steps is a full turn. A ray step is
// at most 8 units, half a cell, so a march cannot skip a grid line
// on one axis.
const ANG_MASK: u8 = 63
const TURN_STEP: u8 = 2
const ATTRACT_TURN: u8 = 4
const TITLE_AUTO: u8 = 45
const ATTRACT_WAIT: u8 = 18
const AI_PERIOD: u8 = 45

const PH_CAST: u8 = 0
const PH_PAINT: u8 = 1
const PH_IDLE: u8 = 2

const START_X: u8 = 40
const START_Y: u8 = 48
const START_ANG: u8 = 0

// Guard anchors, in the same 16-units-per-cell space as the player.
// Guard 0 stands in the opening hall, east of the start.
const G0X: u8 = 104
const G0Y: u8 = 48
const G1X: u8 = 72
const G1Y: u8 = 136
const G2X: u8 = 184
const G2Y: u8 = 184
const G3X: u8 = 136
const G3Y: u8 = 216

// Pattern-table indices. Tileset is the first sprite, so its first
// tile is CHR 1 (tile 0 is the built-in smiley).
const CHR_BLANK: u8 = 1
const CHR_FLOOR: u8 = 2
const CHR_BRICK: u8 = 3
const CHR_BRICK_DARK: u8 = 4
const CHR_STONE: u8 = 5
const CHR_STONE_DARK: u8 = 6
const CHR_DOOR: u8 = 7
const CHR_EXIT: u8 = 8

// Absolute CHR indices. `draw Glyph frame:` takes a tile number,
// not an index into Glyph. Tile 0 is the built-in smiley and
// Tileset owns the next 8 tiles, so Glyph's A is tile 9.
const G_A: u8 = 9
const G_D: u8 = 10
const G_E: u8 = 11
const G_I: u8 = 12
const G_K: u8 = 13
const G_N: u8 = 14
const G_O: u8 = 15
const G_P: u8 = 16
const G_R: u8 = 17
const G_S: u8 = 18
const G_T: u8 = 19
const G_U: u8 = 20
const G_W: u8 = 21
const G_Y: u8 = 22
const G_0: u8 = 23

// Sprite palettes.
const SP_ACTOR: u8 = 0
const SP_GUN: u8 = 1
const SP_HUD: u8 = 2

// Map cell values. 0 is open. 4 is the exit: the ray draws it as a
// gate, and walking into the cell wins.
const CELL_OPEN: u8 = 0
const CELL_BRICK: u8 = 1
const CELL_STONE: u8 = 2
const CELL_DOOR: u8 = 3
const CELL_EXIT: u8 = 4

// Row-major, 16 by 16. The picture matches the bytes below.
//
//   ################
//   #.............D#
//   #.............D#
//   #.............D#
//   #.............D#
//   ####.######.####
//   #SS............#
//   #SS###....###..#
//   #S.#........#..#
//   #S.#.#####.#.E.#
//   #S.#......#....#
//   #..#..##..#....#
//   #..####..##....#
//   #..............#
//   #..............#
//   ################
//
// # brick, S stone, D door, E exit, . open.
const LEVEL: u8[256] = [
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1,
    1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1,
    1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    1, 2, 2, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1,
    1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1,
    1, 2, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 4, 0, 1,
    1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1,
    1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1,
    1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1
]
