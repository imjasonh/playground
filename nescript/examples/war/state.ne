// war/state.ne — every mutable variable the game touches.
//
// NEScript allocates top-level `var` declarations in general RAM
// (the analyzer places them starting at $10 / $18 depending on
// whether the program declares background/palette updates). We
// keep everything global so helper functions can read and write
// without having to take parameters and return values — the
// 6502's 8-register ABI makes every extra parameter an extra
// LDA/STA pair.

// ── Decks + pot ───────────────────────────────────────────
// Each deck is a circular buffer backed by a 52-byte array.
// `*_front` is the index of the next card to draw; `*_count` is
// the number of cards currently in the buffer. Both fields wrap
// mod 52 — there's a helper for that in war/deck.ne.
var deck_a: u8[52]
var deck_a_front: u8 = 0
var deck_a_count: u8 = 0

var deck_b: u8[52]
var deck_b_front: u8 = 0
var deck_b_count: u8 = 0

// Pot holds every card currently in play (the normal-round draws
// and, during a war, the face-down buries too). Drained into the
// winner's deck after each round resolves.
var pot: u8[52]
var pot_count: u8 = 0

// ── The two cards showing face-up this round ─────────────
// These are the packed rank/suit bytes drawn from each deck at
// the start of a round. During a war, the old face-up cards get
// pushed into the pot and new values land in these slots.
var card_a: u8 = 0
var card_b: u8 = 0

// ── Game mode + phase machine ─────────────────────────────
var mode: u8 = 0                  // 0/1/2 players
var a_is_cpu: u8 = 1              // bool-ish
var b_is_cpu: u8 = 1
var phase: u8 = 0                 // one of the P_* constants
var phase_timer: u8 = 0           // counts up during each phase

// ── Animation state ───────────────────────────────────────
// Shared by every card-fly phase. We step (fly_x, fly_y) by a
// constant FLY_STEP per frame in the directions encoded in
// fly_dx_sign / fly_dy_sign. The screen layout is arranged so
// that FRAMES_FLY * FLY_STEP exactly matches the deck-to-play
// distance on both axes — see render.ne for the math.
var fly_x: u8 = 0
var fly_y: u8 = 0
var fly_dx_sign: u8 = 0           // 0 = +FLY_STEP / 1 = -FLY_STEP
var fly_dy_sign: u8 = 0
var fly_card:    u8 = 0           // packed rank/suit to show during the fly
var fly_face_up: u8 = 1           // 0 = show card back, 1 = show face

// ── Title menu ────────────────────────────────────────────
var title_cursor: u8 = 1          // menu index (0/1/2) — default "1 PLAYER"
var title_timer:  u8 = 0          // auto-advance counter
var title_debounce: u8 = 0        // menu input debounce
var title_blink:  u8 = 0          // "PRESS A" blink counter

// ── Deal state ────────────────────────────────────────────
var deal_next:    u8 = 0          // next card index to deal
var deal_timer:   u8 = 0

// ── Victory state ─────────────────────────────────────────
var winner: u8 = 0                // 0 = A wins, 1 = B wins
var victory_timer: u8 = 0

// ── RNG ──────────────────────────────────────────────────
// 8-bit Galois LFSR state. Seeded from the free-running title
// frame counter at the moment the title screen transitions to
// Deal, so the shuffle is deterministic once the user commits
// to starting a game. The jsnes headless harness always starts
// at frame 45, so the seed is stable there too.
var rng_state: u8 = 0xA7

// ── Global free-running frame counter ────────────────────
// Used by any state that needs a coarse "which frame are we
// on" read without installing its own counter.
var global_tick: u16 = 0
