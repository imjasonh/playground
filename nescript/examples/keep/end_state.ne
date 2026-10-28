// keep/end_state.ne: escaped, or dead.
//
// The window blanks one row per frame so the words sit on black.
// Start returns to the title.

state End {
    on enter {
        end_row = 0
        stop_music
        if outcome == 0 {
            start_music win
        } else {
            start_music gameover
        }
    }

    on frame {
        if end_row < VIEW_H {
            nt_fill_h(VIEW_X, VIEW_Y + end_row, VIEW_W, CHR_BLANK)
            end_row = end_row + 1
        }

        glyph(112, 48, G_Y)
        glyph(120, 48, G_O)
        glyph(128, 48, G_U)
        if outcome == 0 {
            glyph(112, 64, G_W)
            glyph(120, 64, G_I)
            glyph(128, 64, G_N)
        } else {
            glyph(104, 64, G_D)
            glyph(112, 64, G_I)
            glyph(120, 64, G_E)
            glyph(128, 64, G_D)
        }

        if button.start.pressed or button.a.pressed {
            transition Title
        }
    }
}
