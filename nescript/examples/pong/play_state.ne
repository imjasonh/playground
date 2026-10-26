// pong/play_state.ne — the Playing state and its inner phase machine.
//
// The phase machine cycles through P_SERVE → P_PLAY → P_POINT:
//
//   P_SERVE  — brief countdown, then serve_ball() and switch to P_PLAY
//   P_PLAY   — normal gameplay: update paddles, balls, powerups, draw
//   P_POINT  — a side just scored; short pause then re-serve (or Victory)

// Inline helper to set the phase and zero the timer atomically.
inline fun set_phase(p: u8) {
    phase = p
    phase_timer = 0
}

state Playing {
    on enter {
        // Reset scores and paddle state on a fresh game.
        score[0] = 0
        score[1] = 0
        paddle_y[0] = 96
        paddle_y[1] = 96
        paddle_long[0] = 0
        paddle_long[1] = 0
        paddle_fast[0] = 0
        paddle_fast[1] = 0
        paddle_multi[0] = 0
        paddle_multi[1] = 0
        serving_side = SIDE_RIGHT   // first serve goes toward the right paddle
        set_phase(P_SERVE)
    }

    on frame {
        global_tick += 1
        phase_timer += 1

        // ── Phase dispatch ───────────────────────────────
        // Using `match` so at most one arm executes per frame
        // (prevents one phase from advancing into the next in
        // the same frame — the same rationale as war's phase
        // machine).
        match phase {
            P_SERVE => {
                // Draw the static table while the serve countdown
                // ticks. After FRAMES_SERVE frames, launch the ball
                // and start play.
                draw_center_line()
                draw_scores()
                draw_paddles()

                if phase_timer >= FRAMES_SERVE {
                    serve_ball(serving_side)
                    set_phase(P_PLAY)
                }
            }
            P_PLAY => {
                // Core gameplay loop.
                step_paddles()
                step_balls()
                step_powerup()

                draw_center_line()
                draw_scores()
                draw_paddles()
                draw_balls()
                draw_powerup()
            }
            P_POINT => {
                // Short pause after a score before re-serving.
                // Keep drawing the table and scores so the new
                // score reads on-screen.
                draw_center_line()
                draw_scores()
                draw_paddles()

                if phase_timer >= FRAMES_POINT {
                    // Check for match win.
                    if score[SIDE_LEFT] >= WIN_SCORE {
                        winner = 0
                        transition Victory
                    }
                    if score[SIDE_RIGHT] >= WIN_SCORE {
                        winner = 1
                        transition Victory
                    }
                    // Not over yet — serve again. The serving_side
                    // was set in on_score() to the scoring side, so
                    // the ball is served TOWARD the side that lost
                    // the point.
                    if serving_side == SIDE_LEFT {
                        serving_side = SIDE_RIGHT
                    } else {
                        serving_side = SIDE_LEFT
                    }
                    set_phase(P_SERVE)
                }
            }
            _ => {}
        }
    }
}
