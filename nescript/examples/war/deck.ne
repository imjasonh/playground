// war/deck.ne — queue operations on the three u8[52] buffers.
//
// Each of deck_a, deck_b, and pot is a 52-entry circular buffer
// storing packed rank/suit bytes. The front index is the next
// card to draw; the count is the number of cards currently in
// the buffer. Everything wraps mod 52 — since 52 isn't a power
// of two, we use `if idx >= 52 { idx -= 52 }` instead of `%` to
// avoid the expensive software mod routine.

// ── Helpers shared by every deck ──────────────────────────
//
// Wrap a (front + count) sum back into the 0..51 range. Only
// needed inside push_back because `front` and `count` are both
// ≤ 51 by construction, so the sum is at most 102 and one
// subtraction is enough.
//
// Not marked `inline`: the conditional early return is one of
// the body shapes the inliner declines (W0110), and living
// with the JSR is cheaper than rewriting this as `v % DECK_SIZE`
// (which would pull in the software modulo routine).
fun wrap52(v: u8) -> u8 {
    if v >= DECK_SIZE {
        return v - DECK_SIZE
    }
    return v
}

// ── deck_a ────────────────────────────────────────────────

fun deck_a_empty() -> u8 {
    if deck_a_count == 0 {
        return 1
    }
    return 0
}

fun draw_front_a() -> u8 {
    var card: u8 = deck_a[deck_a_front]
    deck_a_front = wrap52(deck_a_front + 1)
    deck_a_count -= 1
    return card
}

fun push_back_a(card: u8) {
    var slot: u8 = wrap52(deck_a_front + deck_a_count)
    deck_a[slot] = card
    deck_a_count += 1
}

// ── deck_b ────────────────────────────────────────────────

fun deck_b_empty() -> u8 {
    if deck_b_count == 0 {
        return 1
    }
    return 0
}

fun draw_front_b() -> u8 {
    var card: u8 = deck_b[deck_b_front]
    deck_b_front = wrap52(deck_b_front + 1)
    deck_b_count -= 1
    return card
}

fun push_back_b(card: u8) {
    var slot: u8 = wrap52(deck_b_front + deck_b_count)
    deck_b[slot] = card
    deck_b_count += 1
}

// ── pot ───────────────────────────────────────────────────

fun push_back_pot(card: u8) {
    pot[pot_count] = card
    pot_count += 1
}

fun clear_pot() {
    pot_count = 0
}

// Transfer every card currently in the pot into deck_a, in FIFO
// order (so the face-up and face-down cards layer naturally).
fun pot_to_a() {
    var i: u8 = 0
    while i < pot_count {
        push_back_a(pot[i])
        i += 1
    }
    pot_count = 0
}

fun pot_to_b() {
    var i: u8 = 0
    while i < pot_count {
        push_back_b(pot[i])
        i += 1
    }
    pot_count = 0
}

// ── Init + shuffle ────────────────────────────────────────
//
// Build a 52-card "master deck" in deck_a's backing array using
// a rank-major loop: for each rank 1..13, each suit 0..3, write
// the packed byte (rank << 4) | suit into deck_a[i]. Then
// bounded-random-swap-shuffle it. Finally, split the first 26
// into deck_b (copied), leaving the second 26 in deck_a's first
// half, and reset both queues' cursors.
//
// The random-swap shuffle is a bounded alternative to
// Fisher-Yates: it does 200 swaps between two random indices,
// where each index is rand() & 0x3F (0..63) and the swap is
// only done when both indices are < 52. Uses only bitwise ops
// (no multiply, no divide).

fun build_master_deck() {
    var r: u8 = 1
    var i: u8 = 0
    while r <= RANK_KING {
        var s: u8 = 0
        while s < 4 {
            // Pack rank into the high nibble, suit into the low.
            // rank fits in 4 bits (max 13) and suit fits in 2
            // bits, so the shift-and-or is exact.
            var packed: u8 = r << 4
            deck_a[i] = packed | s
            i += 1
            s += 1
        }
        r += 1
    }
}

fun shuffle_deck_a() {
    var k: u8 = 0
    while k < 200 {
        var i: u8 = rand_u8() & 0x3F
        var j: u8 = rand_u8() & 0x3F
        if i < DECK_SIZE {
            if j < DECK_SIZE {
                var tmp: u8 = deck_a[i]
                deck_a[i] = deck_a[j]
                deck_a[j] = tmp
            }
        }
        k += 1
    }
}

// After shuffle, split deck_a's 52 cards into two halves: the
// first 26 stay in deck_a, the second 26 move into deck_b.
// Reset both queues' front/count cursors in the process.
fun split_decks() {
    var i: u8 = 0
    while i < HALF_DECK {
        deck_b[i] = deck_a[HALF_DECK + i]
        i += 1
    }
    deck_a_front = 0
    deck_a_count = HALF_DECK
    deck_b_front = 0
    deck_b_count = HALF_DECK
    pot_count = 0
}

fun init_and_shuffle_decks() {
    build_master_deck()
    shuffle_deck_a()
    split_decks()
}
