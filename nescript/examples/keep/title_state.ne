// keep/title_state.ne: the title, then the demo.
//
// With no input, Play starts on its own and turns in place. That is
// what the frame-180 golden sees. Pressing Start or A before then
// sets human, and Play keeps the view still until you move.

state Title {
    on enter {
        human = 0
        title_timer = 0
        title_blink = 0
        start_music title
    }

    on frame {
        title_timer = title_timer + 1
        title_blink = title_blink + 1
        if title_blink >= 40 {
            title_blink = 0
        }

        // KEEP
        glyph(112, 64, G_K)
        glyph(120, 64, G_E)
        glyph(128, 64, G_E)
        glyph(136, 64, G_P)

        if title_blink < 24 {
            // PRESS
            glyph(104, 96, G_P)
            glyph(112, 96, G_R)
            glyph(120, 96, G_E)
            glyph(128, 96, G_S)
            glyph(136, 96, G_S)
            // START
            glyph(104, 112, G_S)
            glyph(112, 112, G_T)
            glyph(120, 112, G_A)
            glyph(128, 112, G_R)
            glyph(136, 112, G_T)
        }

        if button.start.pressed or button.a.pressed {
            human = 1
            transition Playing
        } else {
            if title_timer >= TITLE_AUTO {
                transition Playing
            }
        }
    }
}
