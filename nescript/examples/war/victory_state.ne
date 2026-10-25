// war/victory_state.ne — the Victory state.
//
// Big "PLAYER A WINS" or "PLAYER B WINS" banner, the builtin
// `fanfare` music, an auto-return to Title after
// VICTORY_LINGER_FRAMES frames, and a manual "press A to skip"
// path.

state Victory {
    on enter {
        victory_timer = 0
        start_music fanfare
    }

    on frame {
        global_tick += 1
        victory_timer += 1

        // ── Banner ──────────────────────────────────────
        // "PLAYER X" on row 1, "WINS" on row 2. Splitting the
        // banner across two y rows keeps each scanline under the
        // NES's 8-sprite-per-scanline limit (the "PLAYER X WINS"
        // single-line version was 11 sprites tall and dropped
        // letters past the 8th).
        draw_word_player(64, 80)
        if winner == 0 {
            draw_letter(120, 80, 0)   // A
        } else {
            draw_letter(120, 80, 1)   // B
        }
        draw_word_wins(96, 96)

        // Flourish: draw the winning deck's top card in the
        // middle of the screen as a victory showcase. If the
        // deck is empty (shouldn't happen — we only arrive
        // here because the *loser* is empty) fall back to a
        // card back so the layout is stable.
        // Pull the winner's top card into a single local. Only
        // one `var top` declaration per on-frame body — NEScript
        // scopes locals per function body, not per if-block.
        var top: u8 = 0
        if winner == 0 {
            if deck_a_count > 0 {
                top = deck_a[deck_a_front]
                draw_card_face(120, 128, top)
            } else {
                draw_card_back(120, 128)
            }
        } else {
            if deck_b_count > 0 {
                top = deck_b[deck_b_front]
                draw_card_face(120, 128, top)
            } else {
                draw_card_back(120, 128)
            }
        }

        // Row of tiny hearts under the banner.
        draw Tileset at: (80,  168) frame: TILE_HEART_TINY
        draw Tileset at: (96,  168) frame: TILE_HEART_TINY
        draw Tileset at: (112, 168) frame: TILE_HEART_TINY
        draw Tileset at: (128, 168) frame: TILE_HEART_TINY
        draw Tileset at: (144, 168) frame: TILE_HEART_TINY
        draw Tileset at: (160, 168) frame: TILE_HEART_TINY

        // ── Input + auto-return ─────────────────────────
        if button.a or button.start {
            transition Title
        }
        if victory_timer >= VICTORY_LINGER_FRAMES {
            transition Title
        }
    }

    on exit {
        stop_music
    }
}
