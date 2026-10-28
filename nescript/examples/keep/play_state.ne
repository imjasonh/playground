// keep/play_state.ne: cast, paint, then read the pad.
//
// A view is not one frame. Cast publishes four columns at a time,
// then paint publishes two rows at a time. Input waits until the
// window is finished, so the picture does not tear.

state Playing {
    on enter {
        reset_level()
        begin_cast()
        start_music battle
    }

    on frame {
        if phurt > 0 {
            phurt = phurt - 1
        }
        if flash > 0 {
            flash = flash - 1
        }
        if human == 1 {
            ai_timer = ai_timer + 1
            if ai_timer >= AI_PERIOD {
                ai_timer = 0
                ai_due = 1
            }
        }

        // show stays 1 unless this frame leaves for End.
        var show: u8 = 1

        if phase == PH_CAST {
            var cast_n: u8 = 0
            while cast_n < COLS_PER_FRAME {
                if cast_i >= VIEW_W {
                    break
                }
                cast_column(cast_i)
                cast_i = cast_i + 1
                cast_n = cast_n + 1
            }
            if cast_i >= VIEW_W {
                finish_cast()
            }
        } else {
            if phase == PH_PAINT {
                var paint_n: u8 = 0
                while paint_n < ROWS_PER_FRAME {
                    if paint_row >= VIEW_H {
                        break
                    }
                    emit_row(paint_row)
                    paint_row = paint_row + 1
                    paint_n = paint_n + 1
                }
                if paint_row >= VIEW_H {
                    phase = PH_IDLE
                    rendered = rendered + 1
                    if human == 0 {
                        attract_wait = ATTRACT_WAIT
                    }
                }
            } else {
                if phase != PH_IDLE {
                    // A phase this state does not know about. Recast
                    // so the window cannot sit there looking finished.
                    begin_cast()
                } else {
                    if health == 0 {
                        outcome = 1
                        show = 0
                        transition End
                    } else {
                        if standing_on_exit() == 1 {
                            outcome = 0
                            show = 0
                            transition End
                        } else {
                            if button.up or button.down or button.left or button.right or button.a.pressed or button.b {
                                human = 1
                            }
                            if human == 0 {
                                if attract_wait > 0 {
                                    attract_wait = attract_wait - 1
                                } else {
                                    ang = (ang + ATTRACT_TURN) & ANG_MASK
                                    begin_cast()
                                }
                            } else {
                                var acted: u8 = 0
                                if button.b {
                                    if button.left {
                                        try_move((ang + 48) & ANG_MASK)
                                        acted = 1
                                    }
                                    if button.right {
                                        try_move((ang + 16) & ANG_MASK)
                                        acted = 1
                                    }
                                } else {
                                    if button.left {
                                        ang = (ang - TURN_STEP) & ANG_MASK
                                        acted = 1
                                    }
                                    if button.right {
                                        ang = (ang + TURN_STEP) & ANG_MASK
                                        acted = 1
                                    }
                                }
                                if button.up {
                                    try_move(ang)
                                    acted = 1
                                }
                                if button.down {
                                    try_move((ang + 32) & ANG_MASK)
                                    acted = 1
                                }
                                if button.a.pressed {
                                    fire()
                                }
                                if ai_due == 1 {
                                    ai_due = 0
                                    move_guards()
                                    acted = 1
                                }
                                if health == 0 {
                                    outcome = 1
                                    show = 0
                                    transition End
                                } else {
                                    if standing_on_exit() == 1 {
                                        outcome = 0
                                        show = 0
                                        transition End
                                    } else {
                                        if acted == 1 {
                                            begin_cast()
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        if show == 1 {
            draw_play()
        }
    }
}
