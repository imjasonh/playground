// sha256/state.ne — global variables.
//
// Every piece of cross-handler state lives here so Entering,
// Computing, and Showing can share buffers (and, crucially, so
// the message buffer survives the state transition from
// Entering → Computing without being reinitialised).

// ── Cursor position on the keyboard ─────────────────────────
var kb_row: u8 = 0                         // 0..KB_ROWS-1
var kb_col: u8 = 0                         // 0..KB_COLS-1

// ── Input buffer + length ───────────────────────────────────
var msg: u8[16]                            // INPUT_MAX ASCII bytes
var msg_len: u8 = 0                        // 0..INPUT_MAX

// ── SHA-256 working memory ──────────────────────────────────
//
// `h_state` holds the running hash (8 u32 words, little-endian);
// it's initialised from H_INIT on every new compression so users
// can run more than one hash per power-on. `w` is the 64-entry
// message schedule (256 bytes). `wk` is the scratch area that
// hosts the a..h registers plus T1/T2/Σ/tmp — see
// constants.ne for the byte offsets.
var h_state: u8[32]
var w: u8[256]
var wk: u8[64]

// ── Compression driver state ────────────────────────────────
//
// The compression is split across frames so the main loop never
// overruns vblank. `cp_phase` selects which block of work runs
// this frame; see computing_state.ne for the phase table.
var cp_phase: u8 = 0

// ── Input-idle timer ────────────────────────────────────────
//
// Incremented every frame while Entering sees no button presses.
// When it reaches AUTO_DELAY the state auto-types DEMO_TEXT and
// transitions to Computing, so the headless jsnes golden always
// captures a populated hash screen.
var idle_timer: u8 = 0

// Debounces repeat-fire for the face and special keys so one
// press is registered as one key press rather than one per frame
// held.
var debounce: u8 = 0

// ── Cursor blink ────────────────────────────────────────────
//
// The cursor sprite on the keyboard pulses at ~2 Hz. Also used
// by Showing to mark "PRESS B TO RESET".
var blink_timer: u8 = 0
