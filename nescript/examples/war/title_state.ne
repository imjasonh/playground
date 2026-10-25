// war/title_state.ne — the Title state.
//
// Draws a big "WAR" banner, a 3-option menu with a cursor, and a
// blinking "PRESS A" prompt. Autopilot: if the player doesn't
// press anything for TITLE_AUTO_FRAMES frames the menu auto-
// commits to "0 PLAYERS" so the jsnes golden capture reaches
// gameplay by frame 180.
//
// The cursor navigates with D-pad up/down; A or Start confirms.
// Debouncing is done via title_debounce — one key press per
// press rather than per frame held.

state Title {
    on enter {
        title_cursor = 1
        title_timer = 0
        title_blink = 0
        title_debounce = 0
        start_music TitleTheme
    }

    on frame {
        global_tick += 1
        title_timer += 1
        title_blink += 1
        if title_blink >= 60 {
            title_blink = 0
        }
        if title_debounce > 0 {
            title_debounce -= 1
        }

        // ── Big "WAR" title banner ───────────────────────
        // Three 16×16 metasprite letters (BIG W, A, R), drawn
        // via the same helper the in-game tie-break uses. Each
        // letter is 8px wide (BIG_*_TL / BIG_*_TR side-by-side);
        // letters land at x = 100, 120, 140 with the helper's
        // internal 20-px stride.
        draw_big_war_banner(100, 32)

        // Subtitle "CARD GAME" in 8x8 font under the banner.
        // 8 letter sprites at y=64 — exactly at the per-scanline
        // limit. The space between "CARD" and "GAME" is just a
        // skipped tile column, so it doesn't burn an OAM slot.
        draw_letter(96,  64, 2)    // C
        draw_letter(104, 64, 0)    // A
        draw_letter(112, 64, 17)   // R
        draw_letter(120, 64, 3)    // D
        draw_letter(136, 64, 6)    // G
        draw_letter(144, 64, 0)    // A
        draw_letter(152, 64, 12)   // M
        draw_letter(160, 64, 4)    // E

        // ── Menu options ─────────────────────────────────
        // Three lines vertically stacked. Each row is "X PLAYER"
        // (no S — plural is implied) so the row never exceeds 7
        // sprites and stays under the per-scanline limit even
        // when the cursor sprite shares the same row.
        draw_digit(88, 104, 0)
        draw_word_player(104, 104)
        draw_digit(88, 120, 1)
        draw_word_player(104, 120)
        draw_digit(88, 136, 2)
        draw_word_player(104, 136)

        // Cursor sits to the left of the selected option.
        var cursor_y: u8 = 104 + (title_cursor << 4)  // 104, 120, 136
        draw Tileset at: (72, cursor_y) frame: TILE_CURSOR

        // ── Blinking "PRESS A" prompt ────────────────────
        if title_blink < 30 {
            draw_word_press(96, 184)
            draw_letter(144, 184, 0)   // A
        }


        // ── Input handling ───────────────────────────────
        if title_debounce == 0 {
            if button.up {
                if title_cursor > 0 {
                    title_cursor -= 1
                }
                title_debounce = 10
                title_timer = 0
                play FlipCard
            }
            if button.down {
                if title_cursor < 2 {
                    title_cursor += 1
                }
                title_debounce = 10
                title_timer = 0
                play FlipCard
            }
            if button.a or button.start {
                // Commit the selection and seed the RNG from the
                // current global tick so each user-visible start
                // produces a different shuffle.
                mode = title_cursor
                rng_seed((global_tick & 0xFF) as u8)
                transition Deal
            }
        }

        // ── Autopilot for the headless harness ───────────
        if title_timer >= TITLE_AUTO_FRAMES {
            mode = 0
            rng_seed((global_tick & 0xFF) as u8)
            transition Deal
        }
    }

    on exit {
        stop_music
        // Translate the menu selection into the two a_is_cpu /
        // b_is_cpu flags the play state reads each frame.
        if mode == MODE_CPU_VS_CPU {
            a_is_cpu = 1
            b_is_cpu = 1
        }
        if mode == MODE_HUMAN_VS_CPU {
            a_is_cpu = 0
            b_is_cpu = 1
        }
        if mode == MODE_HUMAN_VS_HUMAN {
            a_is_cpu = 0
            b_is_cpu = 0
        }
    }
}
