// war/play_state.ne — the Playing state and its inner phase machine.
//
// `phase` cycles through the P_* constants defined in
// war/constants.ne. `phase_timer` counts frames inside the
// current phase and is reset to 0 whenever the phase changes.

// Set the current phase and zero the timer in one shot. Inlined
// so each call site is just two stores.
inline fun set_phase(p: u8) {
    phase = p
    phase_timer = 0
}

// Draw the steady-state table furniture: the two deck card backs
// (if non-empty) and the running card counts. Used as the base
// layer every frame; phase-specific sprites are layered on top.
fun draw_table() {
    if deck_a_count > 0 {
        draw_card_back(DECK_A_X, DECK_Y)
    }
    if deck_b_count > 0 {
        draw_card_back(DECK_B_X, DECK_Y)
    }
    draw_count(COUNT_A_X, COUNT_Y, deck_a_count)
    draw_count(COUNT_B_X, COUNT_Y, deck_b_count)
}

// Bury helper for a war: move one card from the deck into the
// pot (face-down). Must be called with a non-empty deck.
fun bury_from_a() {
    var c: u8 = draw_front_a()
    push_back_pot(c)
}
fun bury_from_b() {
    var c: u8 = draw_front_b()
    push_back_pot(c)
}

// Draw the BIG WAR banner — three 16×16 metasprite letters at
// the centre of the screen. 12 sprites total, drawn in the
// centre row so they don't conflict with the deck stacks (rows
// 64-87) or the face-up cards (rows 128-151).
fun draw_big_war_banner(x: u8, y: u8) {
    // BIG W
    draw Tileset at: (x,      y)     frame: TILE_BIG_W_TL
    draw Tileset at: (x + 8,  y)     frame: TILE_BIG_W_TR
    draw Tileset at: (x,      y + 8) frame: TILE_BIG_W_BL
    draw Tileset at: (x + 8,  y + 8) frame: TILE_BIG_W_BR
    // BIG A
    draw Tileset at: (x + 20, y)     frame: TILE_BIG_A_TL
    draw Tileset at: (x + 28, y)     frame: TILE_BIG_A_TR
    draw Tileset at: (x + 20, y + 8) frame: TILE_BIG_A_BL
    draw Tileset at: (x + 28, y + 8) frame: TILE_BIG_A_BR
    // BIG R
    draw Tileset at: (x + 40, y)     frame: TILE_BIG_R_TL
    draw Tileset at: (x + 48, y)     frame: TILE_BIG_R_TR
    draw Tileset at: (x + 40, y + 8) frame: TILE_BIG_R_BL
    draw Tileset at: (x + 48, y + 8) frame: TILE_BIG_R_BR
}

// Begin the A-side draw animation: pull the top card off deck_a,
// stash it as the face-up `card_a`, arm the fly state for the
// deck → play slide, and play the click sfx.
//
// fly_card / fly_face_up are written directly to globals
// instead of being passed to arm_fly, because arm_fly already
// takes 4 parameters and the v0.1 ABI caps function signatures
// at 4 parameters (E0506).
fun begin_draw_a() {
    if deck_a_count > 0 {
        card_a = draw_front_a()
        fly_card = card_a
        fly_face_up = 1
        // dx_sign 0 = move right (DECK_A_X = 32 → PLAY_A_X = 96).
        // dy_sign 0 = move down  (DECK_Y = 64 → PLAY_Y = 128).
        arm_fly(DECK_A_X, DECK_Y, 0, 0)
        play FlipCard
        set_phase(P_FLY_A)
    }
}

// Begin the B-side draw. dx_sign 1 = move left
// (DECK_B_X = 208 → PLAY_B_X = 144). dy_sign 0 = move down.
fun begin_draw_b() {
    if deck_b_count > 0 {
        card_b = draw_front_b()
        fly_card = card_b
        fly_face_up = 1
        arm_fly(DECK_B_X, DECK_Y, 1, 0)
        play FlipCard
        set_phase(P_FLY_B)
    }
}

state Playing {
    on enter {
        set_phase(P_WAIT_A)
        card_a = 0
        card_b = 0
        pot_count = 0
    }

    on frame {
        global_tick += 1
        phase_timer += 1
        draw_table()

        // ── Phase dispatch ───────────────────────────────
        // We use `match` instead of a flat if-chain so each
        // frame only runs the FIRST matching arm. A naive
        // chain like `if phase == X { ... } if phase == Y {...}`
        // would let one phase transition into another (via
        // `set_phase`) and then run the next phase's body in
        // the same frame, which advances animation timers twice
        // and made the card-fly overshoot its endpoint by
        // FLY_STEP every time.
        match phase {
            P_WAIT_A => {
                // Human prompt: hint blink above the deck.
                if a_is_cpu == 0 {
                    if (phase_timer & 32) == 0 {
                        draw_word_press(8, 200)
                    }
                    if button.a or button.start {
                        begin_draw_a()
                    }
                } else {
                    // CPU draws after a short delay.
                    if phase_timer >= CPU_THINK_FRAMES {
                        begin_draw_a()
                    }
                }
            }
            P_FLY_A => {
                step_fly_pos()
                draw_flying_card(fly_x, fly_y)
                if phase_timer >= FRAMES_FLY {
                    set_phase(P_WAIT_B)
                }
            }
            P_WAIT_B => {
                // A's card is now parked in its play slot.
                draw_card_face(PLAY_A_X, PLAY_Y, card_a)
                if b_is_cpu == 0 {
                    if (phase_timer & 32) == 0 {
                        draw_word_press(208, 200)
                    }
                    if p2.button.a or p2.button.start or button.a or button.start {
                        begin_draw_b()
                    }
                } else {
                    if phase_timer >= CPU_THINK_FRAMES {
                        begin_draw_b()
                    }
                }
            }
            P_FLY_B => {
                // A is in place; B is flying.
                draw_card_face(PLAY_A_X, PLAY_Y, card_a)
                step_fly_pos()
                draw_flying_card(fly_x, fly_y)
                if phase_timer >= FRAMES_FLY {
                    set_phase(P_REVEAL)
                }
            }
            P_REVEAL => {
                draw_card_face(PLAY_A_X, PLAY_Y, card_a)
                draw_card_face(PLAY_B_X, PLAY_Y, card_b)
                if phase_timer >= FRAMES_REVEAL {
                    set_phase(P_RESOLVE)
                }
            }
            P_RESOLVE => {
                // Both cards go into the pot regardless of outcome.
                push_back_pot(card_a)
                push_back_pot(card_b)
                var result: u8 = compare_cards(card_a, card_b)
                if result == 1 {
                    play CheerA
                    set_phase(P_WIN_A)
                }
                if result == 2 {
                    play CheerB
                    set_phase(P_WIN_B)
                }
                if result == 0 {
                    // It's a tie — but only enter the war flow if both
                    // sides actually have cards left to bury. If a
                    // player ran out of cards on this very tie, the
                    // OTHER player wins by default and takes the pot.
                    if deck_a_count == 0 {
                        pot_to_b()
                        winner = 1
                        transition Victory
                    }
                    if deck_b_count == 0 {
                        pot_to_a()
                        winner = 0
                        transition Victory
                    }
                    play WarFlash
                    set_phase(P_WAR_BANNER)
                }
            }
            P_WIN_A => {
                draw_card_face(PLAY_A_X, PLAY_Y, card_a)
                draw_card_face(PLAY_B_X, PLAY_Y, card_b)
                if phase_timer >= FRAMES_FLY {
                    pot_to_a()
                    set_phase(P_CHECK)
                }
            }
            P_WIN_B => {
                draw_card_face(PLAY_A_X, PLAY_Y, card_a)
                draw_card_face(PLAY_B_X, PLAY_Y, card_b)
                if phase_timer >= FRAMES_FLY {
                    pot_to_b()
                    set_phase(P_CHECK)
                }
            }
            P_WAR_BANNER => {
                draw_card_face(PLAY_A_X, PLAY_Y, card_a)
                draw_card_face(PLAY_B_X, PLAY_Y, card_b)
                // Flashing big "WAR" banner — only drawn on alternate
                // 8-frame windows so the title strobes for emphasis.
                if (phase_timer & 8) != 0 {
                    draw_big_war_banner(96, 80)
                }
                if phase_timer >= FRAMES_BANNER {
                    set_phase(P_WAR_BURY)
                }
            }
            P_WAR_BURY => {
                // Keep the previous round's face-up pair on the
                // table while the buries thump in — visually the
                // tied cards stay lit until the new pair lands.
                draw_card_face(PLAY_A_X, PLAY_Y, card_a)
                draw_card_face(PLAY_B_X, PLAY_Y, card_b)
                // Bury up to 3 face-down cards from each deck, then
                // draw a new face-up pair. We don't animate each
                // individual buried card; just play a noise thump
                // per buried card and advance the counters.
                if phase_timer == 1 {
                    if deck_a_count > 0 { bury_from_a() }
                    if deck_b_count > 0 { bury_from_b() }
                    play ThudDown
                }
                if phase_timer == 4 {
                    if deck_a_count > 0 { bury_from_a() }
                    if deck_b_count > 0 { bury_from_b() }
                    play ThudDown
                }
                if phase_timer == 7 {
                    if deck_a_count > 0 { bury_from_a() }
                    if deck_b_count > 0 { bury_from_b() }
                    play ThudDown
                }
                if phase_timer == 10 {
                    // Draw new face-ups for the comparison. If either
                    // side has run out of cards, the OTHER side wins
                    // and takes the entire pot — we transition straight
                    // to Victory.
                    if deck_a_count == 0 {
                        pot_to_b()
                        winner = 1
                        transition Victory
                    }
                    if deck_b_count == 0 {
                        pot_to_a()
                        winner = 0
                        transition Victory
                    }
                    card_a = draw_front_a()
                    card_b = draw_front_b()
                }
                if phase_timer >= FRAMES_BURY + 16 {
                    set_phase(P_REVEAL)
                }
            }
            P_CHECK => {
                if deck_a_count == 0 {
                    winner = 1
                    transition Victory
                }
                if deck_b_count == 0 {
                    winner = 0
                    transition Victory
                }
                // No winner yet — start the next round.
                card_a = 0
                card_b = 0
                set_phase(P_WAIT_A)
            }
            _ => {}
        }
    }
}
