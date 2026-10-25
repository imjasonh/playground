// sha256/constants.ne — layout and algorithm constants.
//
// All pixel/tile positions live here so the rest of the code can
// read as coordinate expressions rather than magic numbers. The
// screen budget is tight: only 64 OAM sprites are available, and
// the hash display alone wants 64 of them (8 rows × 8 digits), so
// the Entering / Computing phases keep their overlays small and
// the Showing phase reuses the OAM slots for the digest.

// ── Keyboard layout ──────────────────────────────────────────
//
// 5 rows × 8 columns = 40 keys, laid out on the nametable and
// mirrored by a compile-time character table so `key_char[i]`
// returns the ASCII code a given cell produces. The cursor is
// one sprite that moves over the grid; its background tile is
// not touched.
//
// The bottom row holds five special keys instead of glyphs:
//     `_` produces a space character.
//     `.` produces a period.
//     `<` is backspace — deletes the last input character.
//     `>` is enter — starts the SHA-256 compression.
//     (positions 0..3 on that row are just digits 6-9)
const KB_ROWS: u8 = 5
const KB_COLS: u8 = 8
const KB_KEYS: u8 = 40                     // KB_ROWS * KB_COLS

// Origin of the keyboard on screen, in pixels.
const KB_BASE_X: u8 = 88                   // tile col 11
const KB_BASE_Y: u8 = 96                   // tile row 12
const KB_CELL_W: u8 = 16                   // 2 tiles wide per cell
const KB_CELL_H: u8 = 8                    // 1 tile tall per cell

// Special-key ASCII bytes (all < 32 so they can't collide with
// printable input characters). The keyboard dispatch table stores
// one of these in the bottom row's last two slots.
const KEY_BKSP: u8 = 0x08                  // ASCII BS
const KEY_ENTER: u8 = 0x0A                 // ASCII LF
const KEY_SPACE: u8 = 0x20                 // ASCII SP
const KEY_PERIOD: u8 = 0x2E                // ASCII .

// ── Input buffer ─────────────────────────────────────────────
//
// Maximum 16 ASCII characters. After padding (one 0x80 byte,
// zeros, and an 8-byte big-endian length field) the message is
// exactly 64 bytes — a single SHA-256 block. Keeping to one block
// simplifies the compression driver and bounds the wall-clock
// latency of the Computing phase to a fraction of a second.
const INPUT_MAX: u8 = 16
const INPUT_ROW_LEN: u8 = 8                // 8 chars per on-screen row
const INPUT_BASE_X: u8 = 16                // tile col 2
const INPUT_BASE_Y: u8 = 32                // tile row 4
const INPUT_ROW_H: u8 = 8

// ── Hash output ──────────────────────────────────────────────
//
// 64 hex characters laid out as 8 rows × 8 glyphs at the bottom
// of the screen. The grid exactly fills the OAM budget.
const HASH_NIBBLES: u8 = 64                // 8 bytes × 2 * 4 words
const HASH_ROW_LEN: u8 = 8
const HASH_ROWS: u8 = 8
const HASH_BASE_X: u8 = 32                 // tile col 4
const HASH_BASE_Y: u8 = 168                // tile row 21 — 8 rows fit at
                                           //   y=168..231 with margin
const HASH_ROW_H: u8 = 8

// ── Sprite cursor ────────────────────────────────────────────
//
// The cursor sits just to the left of the selected key, so it
// never shares a scanline with the keyboard cell itself.
const CURSOR_OFS_X: i8 = -8                // 8 px left of cell
const CURSOR_OFS_Y: u8 = 0

// ── Auto-demo ────────────────────────────────────────────────
//
// The headless golden harness drives the ROM without touching
// the controller. After AUTO_DELAY frames in Entering with no
// input, the state handler auto-fills the buffer with DEMO_TEXT
// and transitions to Computing, so the captured frame 180 shows
// an actual hash rather than an empty form. DEMO_TEXT is "NES"
// and its SHA-256 digest is
// AE9145DB5CABC41FE34B54E34AF8881F462362EA20FD8F861B26532FFBB84E0D.
const AUTO_DELAY: u8 = 60                  // 1 s at 60 fps
const AUTO_DEMO_LEN: u8 = 3                // length of "NES"

// ── SHA-256 algorithm constants ──────────────────────────────
//
// K[64] round constants and H[8] initial hash values, both stored
// little-endian (LSB first) so the byte-level primitives in
// sha_core.ne can load and add them four bytes at a time.
//
// Derived from the fractional parts of the cube roots of the
// first 64 primes (K) and square roots of the first 8 primes
// (H) per FIPS 180-4 §4.2.
//
// Declared as `var` with an array initialiser rather than `const`
// because the v0.1 compiler only stores scalar constants in its
// const-fold table; array constants would be accepted by the
// grammar but silently dropped. The initialiser costs ~256 bytes
// of reset-time "write each byte" code and 256 bytes of RAM, but
// avoids adding a new const-data pathway just for this program.
//
// The leading underscore on `_K_BYTES` silences the W0103 unused-
// variable warning: the analyzer doesn't look inside inline-asm
// bodies, and every use of this table happens through
// `LDA {_K_BYTES},Y` inside `add_k_to_wk`.
var _K_BYTES: u8[256] = [
    0x98, 0x2F, 0x8A, 0x42,    0x91, 0x44, 0x37, 0x71,    // K[ 0..1]
    0xCF, 0xFB, 0xC0, 0xB5,    0xA5, 0xDB, 0xB5, 0xE9,    // K[ 2..3]
    0x5B, 0xC2, 0x56, 0x39,    0xF1, 0x11, 0xF1, 0x59,    // K[ 4..5]
    0xA4, 0x82, 0x3F, 0x92,    0xD5, 0x5E, 0x1C, 0xAB,    // K[ 6..7]
    0x98, 0xAA, 0x07, 0xD8,    0x01, 0x5B, 0x83, 0x12,    // K[ 8..9]
    0xBE, 0x85, 0x31, 0x24,    0xC3, 0x7D, 0x0C, 0x55,    // K[10..11]
    0x74, 0x5D, 0xBE, 0x72,    0xFE, 0xB1, 0xDE, 0x80,    // K[12..13]
    0xA7, 0x06, 0xDC, 0x9B,    0x74, 0xF1, 0x9B, 0xC1,    // K[14..15]
    0xC1, 0x69, 0x9B, 0xE4,    0x86, 0x47, 0xBE, 0xEF,    // K[16..17]
    0xC6, 0x9D, 0xC1, 0x0F,    0xCC, 0xA1, 0x0C, 0x24,    // K[18..19]
    0x6F, 0x2C, 0xE9, 0x2D,    0xAA, 0x84, 0x74, 0x4A,    // K[20..21]
    0xDC, 0xA9, 0xB0, 0x5C,    0xDA, 0x88, 0xF9, 0x76,    // K[22..23]
    0x52, 0x51, 0x3E, 0x98,    0x6D, 0xC6, 0x31, 0xA8,    // K[24..25]
    0xC8, 0x27, 0x03, 0xB0,    0xC7, 0x7F, 0x59, 0xBF,    // K[26..27]
    0xF3, 0x0B, 0xE0, 0xC6,    0x47, 0x91, 0xA7, 0xD5,    // K[28..29]
    0x51, 0x63, 0xCA, 0x06,    0x67, 0x29, 0x29, 0x14,    // K[30..31]
    0x85, 0x0A, 0xB7, 0x27,    0x38, 0x21, 0x1B, 0x2E,    // K[32..33]
    0xFC, 0x6D, 0x2C, 0x4D,    0x13, 0x0D, 0x38, 0x53,    // K[34..35]
    0x54, 0x73, 0x0A, 0x65,    0xBB, 0x0A, 0x6A, 0x76,    // K[36..37]
    0x2E, 0xC9, 0xC2, 0x81,    0x85, 0x2C, 0x72, 0x92,    // K[38..39]
    0xA1, 0xE8, 0xBF, 0xA2,    0x4B, 0x66, 0x1A, 0xA8,    // K[40..41]
    0x70, 0x8B, 0x4B, 0xC2,    0xA3, 0x51, 0x6C, 0xC7,    // K[42..43]
    0x19, 0xE8, 0x92, 0xD1,    0x24, 0x06, 0x99, 0xD6,    // K[44..45]
    0x85, 0x35, 0x0E, 0xF4,    0x70, 0xA0, 0x6A, 0x10,    // K[46..47]
    0x16, 0xC1, 0xA4, 0x19,    0x08, 0x6C, 0x37, 0x1E,    // K[48..49]
    0x4C, 0x77, 0x48, 0x27,    0xB5, 0xBC, 0xB0, 0x34,    // K[50..51]
    0xB3, 0x0C, 0x1C, 0x39,    0x4A, 0xAA, 0xD8, 0x4E,    // K[52..53]
    0x4F, 0xCA, 0x9C, 0x5B,    0xF3, 0x6F, 0x2E, 0x68,    // K[54..55]
    0xEE, 0x82, 0x8F, 0x74,    0x6F, 0x63, 0xA5, 0x78,    // K[56..57]
    0x14, 0x78, 0xC8, 0x84,    0x08, 0x02, 0xC7, 0x8C,    // K[58..59]
    0xFA, 0xFF, 0xBE, 0x90,    0xEB, 0x6C, 0x50, 0xA4,    // K[60..61]
    0xF7, 0xA3, 0xF9, 0xBE,    0xF2, 0x78, 0x71, 0xC6     // K[62..63]
]

var H_INIT: u8[32] = [
    0x67, 0xE6, 0x09, 0x6A,    // H[0] = 0x6A09E667
    0x85, 0xAE, 0x67, 0xBB,    // H[1] = 0xBB67AE85
    0x72, 0xF3, 0x6E, 0x3C,    // H[2] = 0x3C6EF372
    0x3A, 0xF5, 0x4F, 0xA5,    // H[3] = 0xA54FF53A
    0x7F, 0x52, 0x0E, 0x51,    // H[4] = 0x510E527F
    0x8C, 0x68, 0x05, 0x9B,    // H[5] = 0x9B05688C
    0xAB, 0xD9, 0x83, 0x1F,    // H[6] = 0x1F83D9AB
    0x19, 0xCD, 0xE0, 0x5B     // H[7] = 0x5BE0CD19
]

// ── wk[] layout ──────────────────────────────────────────────
//
// Every SHA-256 primitive takes byte offsets into the `wk`
// working array. Values are little-endian 32-bit: wk[A+0] is
// the LSB of `a`, wk[A+3] is its MSB.
const OFS_A:   u8 =  0
const OFS_B:   u8 =  4
const OFS_C:   u8 =  8
const OFS_D:   u8 = 12
const OFS_E:   u8 = 16
const OFS_F:   u8 = 20
const OFS_G:   u8 = 24
const OFS_H:   u8 = 28
const OFS_T1:  u8 = 32
const OFS_T2:  u8 = 36
const OFS_SIG: u8 = 40                     // Σ / σ accumulator
const OFS_TMP: u8 = 44                     // rotation / shift scratch

// ── Computing phase budget ───────────────────────────────────
//
// The compression driver splits work over multiple frames. We
// advance one of the following phases per `on frame` tick:
//
//     Phase 0  schedule W[16..31]   (16 iterations)
//     Phase 1  schedule W[32..47]   (16 iterations)
//     Phase 2  schedule W[48..63]   (16 iterations)
//     Phase 3  rounds 0..15         (16 rounds)
//     Phase 4  rounds 16..31        (16 rounds)
//     Phase 5  rounds 32..47        (16 rounds)
//     Phase 6  rounds 48..63        (16 rounds)
//     Phase 7  fold a..h into H,
//              render the digest,
//              transition to Showing
//
// Each of phases 0..6 does 16 iterations. On a release build one
// round or one schedule step runs in well under a vblank-free
// NES frame, so the user-visible latency is ~8 frames.
const CP_PHASES: u8 = 8
