// rampart/customize_state.ne: name and weapons, one human at a time.
//
// The screen logic runs in the Brain bank. This state draws the
// weapon sprites, which have to stay in the fixed bank. The cursor
// starts on the last letter of the name (its NAME_ROW cell), the
// way a text field places the caret after existing text. Left and
// right move the lit letter and up and down rotate it, the rotary
// dial pattern arcade high-score entry uses. On the gun and arm
// rows, left and right cycle that row's weapon and up and down
// move to the next row. Either weapon can be any of the five, so a
// mech can carry two guns or two close-combat weapons. B
// backspaces the name a letter at a time. START confirms from any
// row. A confirms on START. Player 1 finishes, then player 2. A
// CPU skips this screen.
//
// The weapon sprites use the player's palette. The portrait behind
// them is the chassis chosen on the title.

state Customize {
    on enter {
        customize_begin()
    }

    on frame {
        customize_tick()
        if cust_cursor < 9 {
            res_a = 64
            res_b = GUN_ROW * 8 - 1
            draw Tileset at: (res_a, res_b) attr: cust_who frame: wpn_tile(loadout[cust_who * 2], 0)
            draw Tileset at: (res_a + 8, res_b) attr: cust_who frame: wpn_tile(loadout[cust_who * 2], 1)
            res_b = ARM_ROW * 8 - 1
            draw Tileset at: (res_a, res_b) attr: cust_who frame: wpn_tile(loadout[cust_who * 2 + 1], 0)
            draw Tileset at: (res_a + 8, res_b) attr: cust_who frame: wpn_tile(loadout[cust_who * 2 + 1], 1)
            res_b = NAME_ROW * 8 - 1
            if cust_cursor == 6 {
                res_b = GUN_ROW * 8 - 1
            } else if cust_cursor == 7 {
                res_b = ARM_ROW * 8 - 1
            } else if cust_cursor == 8 {
                res_b = START_ROW * 8 - 1
            }
            // The arrow marks the row, just after its label. On the
            // name row the blinking letter marks the cursor, so the
            // arrow stays put instead of covering a letter.
            res_a = 8
            if cust_cursor < 6 {
                res_a = (NAME_COL - 1) * 8
                res_b = NAME_ROW * 8 - 1
            } else if cust_cursor < 8 {
                res_a = 48
            }
            draw Tileset at: (res_a, res_b) attr: SP_FIRE frame: T_ARROW
        }
    }
}
