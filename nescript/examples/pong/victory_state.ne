// pong/victory_state.ne — the Victory state.
//
// Shows "PLAYER N WINS" centred on screen, plays the builtin
// fanfare, and auto-returns to the Title after
// VICTORY_LINGER_FRAMES. Pressing A / Start skips the wait.

state Victory {
    on enter {
        victory_timer = 0
        start_music fanfare
    }

    on frame {
        victory_timer += 1

        // ── Banner: "PLAYER N WINS" ──────────────────────
        //
        // Two rows so the per-scanline sprite limit is comfortable.
        // Row 1: "PLAYER N" (7 sprites at y = 96).
        // Row 2: "WINS"     (4 sprites at y = 116).
        draw_word_player(80, 96)
        // Winner digit: 0 → "1", 1 → "2".
        draw_digit(136, 96, winner + 1)

        draw_word_wins(104, 116)

        // ── Input: skip linger ───────────────────────────
        if button.a or button.start {
            transition Title
        }

        // ── Auto-return ──────────────────────────────────
        if victory_timer >= VICTORY_LINGER_FRAMES {
            transition Title
        }
    }

    on exit {
        stop_music
    }
}
