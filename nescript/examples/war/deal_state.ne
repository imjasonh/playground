// war/deal_state.ne — the Deal state.
//
// Shuffles the deck on entry, then runs a brief dealing animation
// before transitioning into Playing. The animation shows a single
// face-down "in flight" card sprite alternating between A's deck
// and B's deck while a FlipCard sfx clicks on each dealt step.
// The deck counts tick up alongside so it looks like the stacks
// are actually growing.
//
// Pace: one dealt card every 2 frames → 104 frames for the full
// 52-card deal. Combined with the title's 45-frame autopilot,
// Playing starts at roughly frame 150, leaving ~30 frames before
// the jsnes harness captures at frame 180 — enough for the
// CPU-think delay and the start of A's first fly.

state Deal {
    on enter {
        init_and_shuffle_decks()
        // Visually pretend both decks start empty and grow during
        // the animation — we animate a `visible_count` counter
        // on each side. The underlying deck_*_count starts at
        // HALF_DECK after init_and_shuffle_decks; we override the
        // on-screen count via deal_next.
        deal_next = 0
        deal_timer = 0
    }

    on frame {
        global_tick += 1
        deal_timer += 1

        // ── Dealing tick ─────────────────────────────────
        // Deal one card every 2 frames until we've laid down
        // all 52. Play a FlipCard sfx on each dealt step for
        // the rhythmic click.
        if deal_timer >= 2 {
            deal_timer = 0
            if deal_next < DECK_SIZE {
                deal_next += 1
                play FlipCard
            }
        }

        // ── Rendering ────────────────────────────────────
        // Draw the "table" furniture: two deck stacks in their
        // resting position and the running card counts. The
        // deal_next counter controls how many of the 52 have
        // "landed", so the first half goes to A and the second
        // half to B — matching the actual split_decks() logic.
        var dealt_a: u8 = deal_next
        var dealt_b: u8 = 0
        if dealt_a > HALF_DECK {
            dealt_b = dealt_a - HALF_DECK
            dealt_a = HALF_DECK
        }

        // Both decks drawn as card backs whenever they have at
        // least one card. Before that, skip the draw so the slot
        // is empty.
        if dealt_a > 0 {
            draw_card_back(DECK_A_X, DECK_Y)
        }
        if dealt_b > 0 {
            draw_card_back(DECK_B_X, DECK_Y)
        }

        draw_count(COUNT_A_X, COUNT_Y, dealt_a)
        draw_count(COUNT_B_X, COUNT_Y, dealt_b)

        // ── Flying card ──────────────────────────────────
        // A single face-down card bouncing between the centre
        // and each deck. The x position alternates based on the
        // low bit of deal_next (even → going to A, odd → B).
        if deal_next < DECK_SIZE {
            var fly_x_pos: u8 = DECK_A_X + 32
            if (deal_next & 1) != 0 {
                fly_x_pos = DECK_B_X - 32
            }
            draw_card_back(fly_x_pos, 96)
        }

        // ── Transition ───────────────────────────────────
        if deal_next >= DECK_SIZE {
            transition Playing
        }
    }
}
