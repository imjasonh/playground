// rampart/customize_state.ne: name and weapons, one human at a time.
//
// The screen logic runs in the Brain bank. This state draws the
// weapon sprites, which have to stay in the fixed bank. On the
// name row, left and right move the lit letter and up and down
// rotate it. On the gun and arm rows, left and right cycle that
// row's weapon and up and down move to the next row. Either
// weapon can be any of the six, so a mech can carry two guns or
// two close-combat weapons. B clears the name. START confirms
// from any row. A confirms on START. Player 1 finishes, then
// player 2. A CPU skips this screen.
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
            res_b = 127
            draw Tileset at: (res_a, res_b) attr: cust_who frame: wpn_tile(loadout[cust_who * 2], 0)
            draw Tileset at: (res_a + 8, res_b) attr: cust_who frame: wpn_tile(loadout[cust_who * 2], 1)
            res_b = 143
            draw Tileset at: (res_a, res_b) attr: cust_who frame: wpn_tile(loadout[cust_who * 2 + 1], 0)
            draw Tileset at: (res_a + 8, res_b) attr: cust_who frame: wpn_tile(loadout[cust_who * 2 + 1], 1)
            res_b = 39
            if cust_cursor == 6 {
                res_b = 127
            } else if cust_cursor == 7 {
                res_b = 143
            } else if cust_cursor == 8 {
                res_b = 175
            }
            res_a = 8
            if cust_cursor < 6 {
                res_a = (8 + cust_cursor) * 8 - 8
                res_b = 39
            } else if cust_cursor < 8 {
                res_a = 48
            }
            draw Tileset at: (res_a, res_b) attr: SP_FIRE frame: T_ARROW
        }
    }
}
