// Logic Ops — demonstrates keyword-based boolean operators
// (`and`, `or`, `not`) along with comparison operators.
//
// The player sprite is drawn only when it's "alive AND unpaused",
// the score counter freezes when paused OR dead, and movement is
// allowed when NOT paused.
//
// Build: cargo run -- build examples/logic_ops.ne

game "Logic Ops" {
    mapper: NROM
}

var alive:  bool = true
var paused: bool = false
var px:     u8 = 100
var py:     u8 = 120
var score:  u8 = 0
var tick:   u8 = 0
var debounce: u8 = 0

on frame {
    if debounce > 0 {
        debounce -= 1
    }

    // Start toggles pause; B kills the player (both with debounce).
    if button.start and debounce == 0 {
        if paused {
            paused = false
        } else {
            paused = true
        }
        debounce = 20
    }
    if button.b and debounce == 0 {
        alive = false
        debounce = 20
    }
    if button.a and debounce == 0 {
        alive = true
        debounce = 20
    }

    // Movement is only allowed when alive AND not paused.
    if alive and (not paused) {
        if button.right { px += 1 }
        if button.left  { px -= 1 }
        if button.up    { py -= 1 }
        if button.down  { py += 1 }
    }

    // Score ticks up 1/frame unless paused or dead. Using OR to
    // short-circuit when either flag blocks scoring.
    tick += 1
    if paused or (not alive) {
        // frozen
    } else {
        if tick >= 30 {
            tick = 0
            if score < 240 {
                score += 1
            }
        }
    }

    // Only draw the player when alive and unpaused.
    if alive and (not paused) {
        draw Player at: (px, py)
    }

    // A simple score bar: draw one marker per 30 score points so the
    // effect of the pause/dead gating is visible without text.
    if score >= 30  { draw Pip at: (20, 20) }
    if score >= 60  { draw Pip at: (30, 20) }
    if score >= 90  { draw Pip at: (40, 20) }
    if score >= 120 { draw Pip at: (50, 20) }
}

start Main
