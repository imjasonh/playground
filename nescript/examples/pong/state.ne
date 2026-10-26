// pong/state.ne — every mutable variable the game touches.
//
// As in the war example, keeping these as globals means helper
// functions can read and write without taking parameters and
// returning values — the 6502's 8-register ABI makes every extra
// parameter an extra LDA/STA pair, so the shorter call signatures
// pay for themselves in the hot loop.

// ── Paddles ──────────────────────────────────────────────
//
// Two parallel u8 arrays indexed by `side` (SIDE_LEFT = 0, SIDE_RIGHT = 1).
// `paddle_y[i]`        — top-edge y of paddle i
// `paddle_long[i]`     — remaining LONG-paddle hits (0 = normal)
// `paddle_fast[i]`     — 1 if catcher's next hit doubles ball x velocity
// `paddle_multi[i]`    — 1 if catcher's next hit spawns two extra balls
// `score[i]`           — current score (0..WIN_SCORE)
// `is_cpu[i]`          — 1 if this side is CPU-controlled
var paddle_y:     u8[2] = [96, 96]
var paddle_long:  u8[2] = [0, 0]
var paddle_fast:  u8[2] = [0, 0]
var paddle_multi: u8[2] = [0, 0]
var score:        u8[2] = [0, 0]
var is_cpu:       u8[2] = [1, 1]

// ── Balls ────────────────────────────────────────────────
//
// Parallel u8 arrays, one slot per ball up to MAX_BALLS. Each
// ball's velocity is stored as a (magnitude, sign) pair so the
// existing u8-only arithmetic suffices — sign 0 means +x right
// / +y down, sign 1 means -x left / -y up.
//
// `ball_active[i]`  — 1 if this slot is in play, 0 if free
// `ball_x[i]`       — top-left x in px
// `ball_y[i]`       — top-left y in px
// `ball_dx[i]`      — x speed in px/frame
// `ball_dy[i]`      — y speed in px/frame
// `ball_dx_sign[i]` — 0 = moving right, 1 = moving left
// `ball_dy_sign[i]` — 0 = moving down,  1 = moving up
var ball_active:  u8[3] = [0, 0, 0]
var ball_x:       u8[3] = [0, 0, 0]
var ball_y:       u8[3] = [0, 0, 0]
var ball_dx:      u8[3] = [0, 0, 0]
var ball_dy:      u8[3] = [0, 0, 0]
var ball_dx_sign: u8[3] = [0, 0, 0]
var ball_dy_sign: u8[3] = [0, 0, 0]

// ── Powerup ──────────────────────────────────────────────
//
// Single-slot powerup entity. `powerup_kind == PWR_NONE` means
// nothing is on screen; any other value is the current kind plus
// its position and velocity. `powerup_timer` counts frames since
// spawn so we can despawn after POWERUP_LIFE_FRAMES.
var powerup_kind:    u8 = 0
var powerup_x:       u8 = 0
var powerup_y:       u8 = 0
var powerup_dx_sign: u8 = 0
var powerup_dy_sign: u8 = 0
var powerup_timer:   u16 = 0
var powerup_cooldown:u16 = 0  // counts down to the next spawn

// ── Game mode + phase machine ────────────────────────────
var mode:        u8 = 0   // 0/1/2 — CPU vs CPU / human vs CPU / human vs human
var phase:       u8 = 0   // one of the P_* constants
var phase_timer: u8 = 0   // frames spent in the current phase
var serving_side:u8 = 0   // which side serves next (alternates)

// ── Title menu ────────────────────────────────────────────
var title_cursor:   u8 = 0
var title_timer:    u8 = 0
var title_blink:    u8 = 0
var title_debounce: u8 = 0

// ── Victory state ─────────────────────────────────────────
var winner:         u8 = 0
var victory_timer:  u16 = 0

// ── RNG ──────────────────────────────────────────────────
//
// 8-bit Galois LFSR state. Seeded from the title frame counter at
// the moment the title transitions to gameplay so the shuffle of
// the first serve direction and powerup kinds is deterministic
// once a user commits. The jsnes headless harness always hits the
// title autopilot at the same frame, so the seed is stable there
// too.
var rng_state: u8 = 0xA7

// ── Global free-running frame counter ────────────────────
var global_tick: u16 = 0
