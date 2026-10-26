// war/constants.ne — gameplay and layout constants.
//
// Everything that feeds the game's positional layout, animation
// timing, phase machine, or card encoding lives here so one central
// edit can retune the whole game. No code, just `const` entries.

// ── Card encoding ─────────────────────────────────────────
//
// Each card in a deck is packed into one u8:
//
//     high nibble = rank, 1..13     (A=1, 2..10, J=11, Q=12, K=13)
//     low  nibble = suit, 0..3      (0=♠, 1=♥, 2=♦, 3=♣)
//
// Rank nibble lives in bits 7..4 and extracts cleanly via >>4;
// suit nibble lives in bits 3..0 and extracts via &0x0F. No
// division, no multiplication.
const SUIT_SPADE:   u8 = 0
const SUIT_HEART:   u8 = 1
const SUIT_DIAMOND: u8 = 2
const SUIT_CLUB:    u8 = 3

const RANK_ACE:   u8 = 1
const RANK_JACK:  u8 = 11
const RANK_QUEEN: u8 = 12
const RANK_KING:  u8 = 13

const DECK_SIZE:   u8 = 52     // standard 52-card deck
const HALF_DECK:   u8 = 26     // starting count per player

// ── Tile index base pointers into the Tileset sprite ─────
//
// The Tileset sprite (declared in war/assets.ne) stacks every
// custom tile vertically in reading order, so tile index N in a
// `draw Tileset frame: N` call picks the N'th 8×8 block.
//
// Tile 0 is reserved by the linker for the builtin smiley, so
// every custom tile starts at 1. The ranges below must match the
// order the Tileset body lists them in — if you move a tile,
// move its constant too.

// Card frame (shared across every face-up card)
const TILE_FRAME_TL:  u8 = 1       // top-left corner with inset
const TILE_FRAME_TR:  u8 = 2       // top-right corner
const TILE_FRAME_BL:  u8 = 3       // bottom-left corner
const TILE_FRAME_BR:  u8 = 4       // bottom-right corner
const TILE_FRAME_BLANK_L: u8 = 5   // left-half blank cell (white body)
const TILE_FRAME_BLANK_R: u8 = 6   // right-half blank cell

// Card back — 4 tiles arranged as a 2x2 repeating diamond lattice
const TILE_BACK_TL: u8 = 7
const TILE_BACK_TR: u8 = 8
const TILE_BACK_BL: u8 = 9
const TILE_BACK_BR: u8 = 10

// Rank glyphs: one tile per rank, indexed by RANK_TILE_BASE + rank - 1
// so rank 1 (Ace) lands at RANK_TILE_BASE + 0.
const TILE_RANK_BASE: u8 = 11      // 13 tiles: A, 2..10, J, Q, K

// Small suit glyphs for the card corner, one per suit.
const TILE_SUIT_SMALL_BASE: u8 = 24  // 4 tiles: ♠ ♥ ♦ ♣

// Big centre-pip, authored as a 16×16 shape split into four 8×8
// quadrants per suit. Each `_BASE + suit` picks the tile for that
// suit's quadrant. The TL/TR quadrants are contiguous at 28-35;
// the BL/BR quadrants live at 88-95 because they were added
// after the alphabet / digit / BIG WAR tiles and putting them in
// the middle would have shifted every later tile's index.
const TILE_PIP_TL_BASE: u8 = 28      // spade/heart/diamond/club TL
const TILE_PIP_TR_BASE: u8 = 32      // spade/heart/diamond/club TR
const TILE_PIP_BL_BASE: u8 = 88      // spade/heart/diamond/club BL
const TILE_PIP_BR_BASE: u8 = 92      // spade/heart/diamond/club BR

// Alphanumerics (8×8) used for all on-screen text that lives on the
// sprite layer. Letters A-Z then digits 0-9, contiguous.
const TILE_LETTER_BASE: u8 = 36      // 26 letters: A=+0, Z=+25
const TILE_DIGIT_BASE:  u8 = 62      // 10 digits: 0=+0, 9=+9

// UI bits
const TILE_CURSOR:      u8 = 72      // right-pointing arrow for menus
const TILE_HEART_TINY:  u8 = 73      // tiny pip used as a victory marker
const TILE_DOT:         u8 = 74      // single 8x8 card stack marker
const TILE_FELT_BG:     u8 = 75      // subtle felt cross-hatch (bg fill)

// Big WAR title letters — each letter is a 2x2 block of tiles
// addressed by its quadrant.
const TILE_BIG_W_TL: u8 = 76
const TILE_BIG_W_TR: u8 = 77
const TILE_BIG_W_BL: u8 = 78
const TILE_BIG_W_BR: u8 = 79
const TILE_BIG_A_TL: u8 = 80
const TILE_BIG_A_TR: u8 = 81
const TILE_BIG_A_BL: u8 = 82
const TILE_BIG_A_BR: u8 = 83
const TILE_BIG_R_TL: u8 = 84
const TILE_BIG_R_TR: u8 = 85
const TILE_BIG_R_BL: u8 = 86
const TILE_BIG_R_BR: u8 = 87

// ── Screen-space layout ──────────────────────────────────
//
// Positions are in pixels. The screen is 256×240.
// Cards are 16 wide × 24 tall (2 cols × 3 rows of 8×8 tiles).
const CARD_W: u8 = 16
const CARD_H: u8 = 24

// Decks sit on the upper half of the play area; face-up cards sit
// on the lower half so the two bands never share scanlines.
//
// The X and Y deltas are deliberately exactly 64 px so the
// per-frame step animation (FLY_STEP * FRAMES_FLY = 4 * 16 = 64)
// lands a flying card exactly on its destination — no rounding,
// no overshoot, no need to clamp at the end.
//
//     DECK_A_X -> PLAY_A_X = 32 -> 96     (Δ = +64)
//     DECK_B_X -> PLAY_B_X = 208 -> 144   (Δ = -64)
//     DECK_Y   -> PLAY_Y   = 64 -> 128    (Δ = +64)
const DECK_Y:     u8 = 64            // top edge of deck card-back sprite
const PLAY_Y:     u8 = 128           // top edge of face-up card sprite

const DECK_A_X:   u8 = 32            // left deck
const DECK_B_X:   u8 = 208           // right deck
const PLAY_A_X:   u8 = 96            // centre-left face-up slot
const PLAY_B_X:   u8 = 144           // centre-right face-up slot

// War banner is centred horizontally in the middle of the screen.
// Coordinates are the top-left of the first banner sprite.
const BANNER_X:   u8 = 104
const BANNER_Y:   u8 = 96

// HUD card counts sit above each deck.
const COUNT_A_X:  u8 = 32
const COUNT_B_X:  u8 = 208
const COUNT_Y:    u8 = 56

// ── Animation timing ─────────────────────────────────────
//
// Every animation uses a power-of-two frame count so the lerp
// (delta * t / FRAMES) can be compiled into a shift-right by the
// optimizer, avoiding the software multiply/divide warning.
const FRAMES_FLY:   u8 = 16          // card-draw and win-return slides
const FRAMES_BURY:  u8 = 8           // faster bury animation during a war
const FRAMES_REVEAL:u8 = 32          // held pause after both cards are up
const FRAMES_BANNER:u8 = 48          // "WAR!" banner dwell
const FRAMES_DEAL_STEP: u8 = 4       // one dealt card every N frames

// Title auto-advance for the headless jsnes harness: the menu
// confirms "0 PLAYERS" automatically after this many frames of no
// input so the golden capture at frame 180 always lands in
// gameplay.
const TITLE_AUTO_FRAMES: u8 = 45

// CPU "thinking" delay before it draws a card.
const CPU_THINK_FRAMES: u8 = 20

// Victory auto-return timer.
const VICTORY_LINGER_FRAMES: u8 = 180

// ── Phase values for the Playing state's inner machine ───
//
// A plain `enum` would collide with other `Title` / `Victory` /
// etc identifiers, so we use explicit constants instead.
const P_WAIT_A:    u8 = 0
const P_FLY_A:     u8 = 1
const P_WAIT_B:    u8 = 2
const P_FLY_B:     u8 = 3
const P_REVEAL:    u8 = 4
const P_RESOLVE:   u8 = 5
const P_WIN_A:     u8 = 6
const P_WIN_B:     u8 = 7
const P_WAR_BANNER:u8 = 8
const P_WAR_BURY:  u8 = 9
const P_CHECK:     u8 = 10

// Game-mode bookkeeping: 0 / 1 / 2 players selected from the title.
const MODE_CPU_VS_CPU: u8 = 0
const MODE_HUMAN_VS_CPU: u8 = 1
const MODE_HUMAN_VS_HUMAN: u8 = 2
