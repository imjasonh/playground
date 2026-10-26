// sha256/entering_state.ne — the interactive typing state.
//
// Reads controller 1 each frame, moves the keyboard cursor on
// D-pad presses, types a character on A, deletes a character on
// B, and starts compression on START (or when the cursor is
// over the ↵ key and A is pressed). SELECT clears the buffer at
// any time so the user can start over.
//
// If the user doesn't press anything in the first AUTO_DELAY
// frames, the handler auto-types DEMO_TEXT ("NES") and
// transitions to Computing so the jsnes golden always captures
// a fully-rendered hash.

state Entering {
    on enter {
        kb_row = 0
        kb_col = 0
        idle_timer = 0
        debounce = 0
        blink_timer = 0
    }

    on frame {
        // ── Debounce + blink tick ───────────────────────
        if debounce > 0 {
            debounce -= 1
        }
        blink_timer += 1
        if blink_timer >= 40 {
            blink_timer = 0
        }

        // ── D-pad navigation ────────────────────────────
        var pressed: u8 = 0
        if debounce == 0 {
            if button.left {
                if kb_col > 0 {
                    kb_col -= 1
                } else {
                    kb_col = KB_COLS - 1
                }
                debounce = 8
                pressed = 1
            } else if button.right {
                kb_col += 1
                if kb_col >= KB_COLS {
                    kb_col = 0
                }
                debounce = 8
                pressed = 1
            } else if button.up {
                if kb_row > 0 {
                    kb_row -= 1
                } else {
                    kb_row = KB_ROWS - 1
                }
                debounce = 8
                pressed = 1
            } else if button.down {
                kb_row += 1
                if kb_row >= KB_ROWS {
                    kb_row = 0
                }
                debounce = 8
                pressed = 1
            } else if button.a {
                // Press the key under the cursor. Backspace
                // and enter dispatch to their actions; any
                // other character is appended to `msg`.
                var ch: u8 = current_key()
                if ch == KEY_BKSP {
                    input_backspace()
                } else if ch == KEY_ENTER {
                    if msg_len > 0 {
                        transition Computing
                    }
                } else {
                    input_append(ch)
                }
                debounce = 10
                pressed = 1
            } else if button.b {
                input_backspace()
                debounce = 10
                pressed = 1
            } else if button.start {
                if msg_len > 0 {
                    transition Computing
                }
                debounce = 10
                pressed = 1
            } else if button.select {
                input_clear()
                debounce = 10
                pressed = 1
            }
        }

        // ── Idle / auto-demo ────────────────────────────
        if pressed == 1 {
            idle_timer = 0
        } else {
            if idle_timer < 255 {
                idle_timer += 1
            }
            if idle_timer == AUTO_DELAY {
                if msg_len == 0 {
                    // Auto-type "NES" → SHA-256 digest visible
                    // in the headless jsnes golden.
                    input_append(0x4E)           // N
                    input_append(0x45)           // E
                    input_append(0x53)           // S
                    transition Computing
                }
            }
        }

        // ── Render ──────────────────────────────────────
        // Input buffer takes 16 sprites, cursor 1 (when on).
        // Well under the 64-sprite OAM budget.
        draw_input()
        if blink_timer < 25 {
            draw_cursor(1)
        }
    }
}
