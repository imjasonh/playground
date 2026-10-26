// sha256/showing_state.ne — renders the final digest.
//
// Draws the 64-character hexadecimal digest across 8 rows of 8
// glyphs at the bottom of the screen (see HASH_BASE_Y /
// HASH_BASE_X in constants.ne). The digest display alone fills
// the OAM budget, so this state does not draw the input buffer
// or the keyboard cursor.
//
// Pressing B or SELECT clears the buffer and returns to the
// Entering state so the user can hash another message.

state Showing {
    on enter {
        blink_timer = 0
        debounce = 20                        // swallow the press that
                                             //   brought us here
    }

    on frame {
        blink_timer += 1
        if blink_timer >= 60 {
            blink_timer = 0
        }
        if debounce > 0 {
            debounce -= 1
        }

        // ── Input ────────────────────────────────────────
        if debounce == 0 {
            if button.b or button.select or button.start {
                input_clear()
                transition Entering
            }
        }

        // ── Render the 256-bit digest ───────────────────
        draw_hash()
    }
}
