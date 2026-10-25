// State Machine — demonstrates multi-state game flow.
//
// Shows: multiple states with on enter/exit/frame handlers,
// transitions, state-local variables, button input.
//
// Build: cargo run -- build examples/state_machine.ne

game "State Demo" {
    mapper: NROM
}

var global_score: u8 = 0

// ── Title Screen ──
state Title {
    var blink_timer: u8 = 0

    on enter {
        blink_timer = 0
    }

    on frame {
        blink_timer += 1

        // Draw title logo
        draw Logo at: (100, 80)

        // Blink "press start" indicator
        if blink_timer < 30 {
            draw Arrow at: (100, 140)
        }
        if blink_timer > 60 {
            blink_timer = 0
        }

        if button.start {
            transition Playing
        }
    }
}

// ── Gameplay ──
state Playing {
    var px: u8 = 128
    var py: u8 = 200
    var timer: u8 = 0

    on enter {
        px = 128
        py = 200
        timer = 0
    }

    on frame {
        // Movement
        if button.right { px += 2 }
        if button.left  { px -= 2 }
        if button.up    { py -= 2 }
        if button.down  { py += 2 }

        // Timer counts up
        timer += 1

        // After 180 frames (~3 seconds), end the level
        if timer > 180 {
            global_score += 10
            transition Victory
        }

        // Press select to quit
        if button.select {
            transition Title
        }

        draw Player at: (px, py)
    }

    on exit {
        // Could save state here
        wait_frame
    }
}

// ── Victory Screen ──
state Victory {
    var celebrate_timer: u8 = 0

    on enter {
        celebrate_timer = 0
    }

    on frame {
        celebrate_timer += 1

        draw Trophy at: (120, 100)

        // Return to title after a delay
        if celebrate_timer > 120 {
            transition Title
        }

        if button.start {
            transition Playing
        }
    }
}

start Title
