// pong/constants.ne — layout, gameplay, powerup, and phase constants.
//
// Everything that feeds Pong's positional layout, animation timing,
// powerup machine, or score tracking lives here so one central edit
// can retune the whole game. No code, just `const` entries.

// ── Playfield layout ──────────────────────────────────────
//
// The NES screen is 256×240. We leave the top 16 px for the HUD
// score strip and the bottom 24 px as a buffer, giving a 200 px
// tall playfield from y = 16 to y = 216.
const PLAYFIELD_TOP:    u8 = 16
const PLAYFIELD_BOTTOM: u8 = 216
const PLAYFIELD_LEFT:   u8 = 0
const PLAYFIELD_RIGHT:  u8 = 248

// ── Paddles ──────────────────────────────────────────────
//
// Paddles are 8 px wide. Normal height is 24 px (3 tiles), long
// mode bumps to 40 px (5 tiles). Paddle y is the top edge.
const PADDLE_W:     u8 = 8
const PADDLE_H:     u8 = 24
const PADDLE_H_LONG:u8 = 40

const LEFT_PADDLE_X:  u8 = 16   // fixed x for the left paddle
const RIGHT_PADDLE_X: u8 = 232  // fixed x for the right paddle

// Human paddle speed and CPU tracking speed.
const PADDLE_SPEED:   u8 = 2
const CPU_SPEED:      u8 = 1

// When a powerup is caught by a paddle, the catching paddle gets
// LONG_PADDLE_HITS worth of extended-height paddle.
const LONG_PADDLE_HITS: u8 = 5

// ── Ball ─────────────────────────────────────────────────
//
// 8×8 sprite. Position is the top-left corner. Velocity is a
// per-axis (magnitude, sign) pair — u8 magnitude + u8 sign bit
// (0 = positive / +x right / +y down, 1 = negative).
const BALL_SIZE:      u8 = 8
const BALL_BASE_DX:   u8 = 1
const BALL_BASE_DY:   u8 = 1
const BALL_FAST_DX:   u8 = 2

const MAX_BALLS:      u8 = 3

// ── Powerup ──────────────────────────────────────────────
//
// One powerup active at a time. Spawns periodically, bounces
// around for a while, despawns if nobody catches it.
const POWERUP_SIZE:         u8 = 8
const POWERUP_SPEED:        u8 = 1
const POWERUP_SPAWN_FRAMES: u16 = 240  // ~4 s at 60 Hz
const POWERUP_LIFE_FRAMES:  u16 = 480  // ~8 s before despawn

const PWR_NONE:  u8 = 0
const PWR_LONG:  u8 = 1
const PWR_FAST:  u8 = 2
const PWR_MULTI: u8 = 3
const PWR_KINDS: u8 = 3  // number of real kinds (LONG / FAST / MULTI)

// ── Sides ────────────────────────────────────────────────
//
// Side indexing for the two paddles. Used by input, AI,
// collision, powerup apply, and victory.
const SIDE_LEFT:  u8 = 0
const SIDE_RIGHT: u8 = 1

// ── Scoring ──────────────────────────────────────────────
const WIN_SCORE: u8 = 7

// ── HUD ──────────────────────────────────────────────────
//
// Score digits at the top of the screen, 2 digits per side.
const SCORE_LEFT_X:  u8 = 88
const SCORE_RIGHT_X: u8 = 152
const SCORE_Y:       u8 = 16

// ── Title menu ───────────────────────────────────────────
const MODE_CPU_VS_CPU:   u8 = 0
const MODE_HUMAN_VS_CPU: u8 = 1
const MODE_HUMAN_VS_HUMAN:u8 = 2

// Title autopilot: if no input for this many frames, the menu
// commits to CPU VS CPU so the headless golden harness always
// reaches gameplay.
const TITLE_AUTO_FRAMES: u8 = 45

// ── Phase machine (state Playing) ────────────────────────
//
// Explicit constants instead of an enum to keep names from
// colliding with state names.
const P_SERVE:  u8 = 0
const P_PLAY:   u8 = 1
const P_POINT:  u8 = 2

// Frames spent in each non-PLAY phase.
const FRAMES_SERVE: u8 = 60   // 1 s countdown before the ball launches
const FRAMES_POINT: u8 = 40   // 0.67 s pause after a point
const VICTORY_LINGER_FRAMES: u16 = 240  // 4 s on the victory screen

// ── Tile indices into the Tileset sprite ─────────────────
//
// Every `draw Tileset frame: N` call in render.ne uses a constant
// from this block. If you add or remove a tile in assets.ne, move
// the constants too.

// Tile 0 is the builtin smiley that the linker reserves; every
// custom tile starts at 1.

// Alphabet A-Z at indices 1..26 (A = 1, Z = 26).
const TILE_LETTER_BASE: u8 = 1

// Digits 0-9 at indices 27..36 (0 = 27).
const TILE_DIGIT_BASE:  u8 = 27

// Paddle body — top cap / mid / bottom cap.
const TILE_PADDLE_TOP:  u8 = 37
const TILE_PADDLE_MID:  u8 = 38
const TILE_PADDLE_BOT:  u8 = 39

// Ball (8×8 filled circle).
const TILE_BALL:        u8 = 40

// Cursor (▶) for the title menu.
const TILE_CURSOR:      u8 = 41

// Center-line dash (8×8 vertical bar).
const TILE_CENTER_DASH: u8 = 42

// Powerup icons — one tile per powerup kind. Indexed as
// TILE_POWERUP_BASE + (kind - 1), so LONG = +0, FAST = +1,
// MULTI = +2.
const TILE_POWERUP_BASE: u8 = 43
