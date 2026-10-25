// pong/title_state.ne — the Title state.
//
// Draws "PONG" at the top of the screen, a 3-option menu (CPU VS
// CPU / 1 PLAYER / 2 PLAYERS) with a cursor, and a blinking
// "PRESS A" prompt below. If nothing happens for TITLE_AUTO_FRAMES
// the menu auto-commits to CPU VS CPU so the headless jsnes
// golden capture always reaches gameplay by frame 180.

state Title {
    on enter {
        title_cursor = 0      // default: CPU VS CPU (autopilot pick)
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

        // ── "PONG" banner ─────────────────────────────────
        //
        // Until the BIG PONG banner lands in the polish
        // milestone, we draw the name in the 8×8 font at
        // roughly 2× scale by spacing letters 16 px apart. That
        // reads as a title without eating a dozen extra tiles.
        draw_letter(88,  40, 15)  // P
        draw_letter(104, 40, 14)  // O
        draw_letter(120, 40, 13)  // N
        draw_letter(136, 40, 6)   // G

        // ── Menu options ──────────────────────────────────
        //
        // Three vertically-stacked rows. Row 0 = CPU VS CPU,
        // row 1 = 1 PLAYER, row 2 = 2 PLAYER (no S — plural is
        // implied, and dropping the S keeps each row short
        // enough that the cursor sprite + row fits under the
        // sprites-per-scanline budget).
        //
        // Row 0: "CPU VS CPU"
        draw_word_cpu(80,  96)
        draw_word_vs (112, 96)
        draw_word_cpu(136, 96)
        // Row 1: "1 PLAYER"
        draw_digit(88, 120, 1)
        draw_word_player(104, 120)
        // Row 2: "2 PLAYER"
        draw_digit(88, 144, 2)
        draw_word_player(104, 144)

        // Cursor sits to the left of the selected option, at
        // y = 96 / 120 / 144 depending on title_cursor.
        var cursor_y: u8 = 96 + (title_cursor << 3) + (title_cursor << 4)  // +24 per row
        draw Tileset at: (64, cursor_y) frame: TILE_CURSOR

        // ── Blinking "PRESS A" prompt ─────────────────────
        if title_blink < 30 {
            draw_word_press(96, 184)
            draw_letter(144, 184, 0)  // A
        }

        // ── Input handling ────────────────────────────────
        if title_debounce == 0 {
            if button.up {
                if title_cursor > 0 {
                    title_cursor -= 1
                }
                title_debounce = 10
                title_timer = 0
                play PaddleHit
            }
            if button.down {
                if title_cursor < 2 {
                    title_cursor += 1
                }
                title_debounce = 10
                title_timer = 0
                play PaddleHit
            }
            if button.a or button.start {
                mode = title_cursor
                rng_seed((global_tick & 0xFF) as u8)
                transition Playing
            }
        }

        // ── Autopilot for the headless harness ────────────
        if title_timer >= TITLE_AUTO_FRAMES {
            mode = MODE_CPU_VS_CPU
            title_cursor = 0
            rng_seed((global_tick & 0xFF) as u8)
            transition Playing
        }
    }

    on exit {
        stop_music
        // Translate the menu selection into per-side is_cpu flags
        // the playing state reads each frame.
        if mode == MODE_CPU_VS_CPU {
            is_cpu[0] = 1
            is_cpu[1] = 1
        }
        if mode == MODE_HUMAN_VS_CPU {
            is_cpu[0] = 0
            is_cpu[1] = 1
        }
        if mode == MODE_HUMAN_VS_HUMAN {
            is_cpu[0] = 0
            is_cpu[1] = 0
        }
    }
}
