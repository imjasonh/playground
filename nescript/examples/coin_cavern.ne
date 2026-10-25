// Coin Cavern — a multi-state game demo for Milestone 2.
//
// Demonstrates: state machine, functions, if/else, while loops,
// constants, button input, transitions between states.
//
// Build:  cargo run -- build examples/coin_cavern.ne
// Output: examples/coin_cavern.nes
//
// Note: In M2 sprites use the built-in CHR tile. Custom tile data
// and proper graphics come in M3 with the asset pipeline.

game "Coin Cavern" {
    mapper: NROM
}

// Constants
const SPEED: u8 = 2
const GRAVITY: u8 = 1
const JUMP_FORCE: u8 = 4
const SCREEN_RIGHT: u8 = 240
const SCREEN_BOTTOM: u8 = 220
const COIN_X: u8 = 180
const COIN_Y: u8 = 100

// Global variables
var score: u8 = 0

// Helper function: clamp a value to screen bounds
fun clamp_x(val: u8) -> u8 {
    if val > SCREEN_RIGHT {
        return 0
    }
    return val
}

// Title screen state
state Title {
    on frame {
        // Draw title sprite at center of screen
        draw Logo at: (100, 100)

        // Press start to play
        if button.start {
            transition Playing
        }
    }
}

// Main gameplay state
state Playing {
    // Physics and position live with the state: they're only
    // meaningful while Playing is active, and the analyzer
    // overlays them with the locals of the Title and GameOver
    // states so the idle scenes don't reserve bytes they never
    // touch. Initializers re-run on every entry, so dying and
    // retrying starts the player back on the ground.
    var player_x: u8 = 40
    var player_y: u8 = 200
    var player_vy: u8 = 0
    var on_ground: u8 = 1
    var coins_left: u8 = 3

    on enter {
        score = 0
    }

    on frame {
        // Horizontal movement
        if button.right {
            player_x += SPEED
            if player_x > SCREEN_RIGHT {
                player_x = SCREEN_RIGHT
            }
        }
        if button.left {
            if player_x >= SPEED {
                player_x -= SPEED
            } else {
                player_x = 0
            }
        }

        // Simple gravity
        if on_ground == 0 {
            player_y += player_vy
            player_vy += GRAVITY
            if player_y >= SCREEN_BOTTOM {
                player_y = SCREEN_BOTTOM
                on_ground = 1
                player_vy = 0
            }
        }

        // Jump
        if button.a {
            if on_ground == 1 {
                on_ground = 0
                player_vy = JUMP_FORCE
            }
        }

        // Check coin collection (simple distance check)
        if player_x >= COIN_X {
            if player_y >= COIN_Y {
                score += 1
                coins_left -= 1
                if coins_left == 0 {
                    transition GameOver
                }
            }
        }

        // Draw player and coin
        draw Player at: (player_x, player_y)
        draw Coin at: (COIN_X, COIN_Y)
    }
}

// Game over state
state GameOver {
    on frame {
        draw Trophy at: (120, 100)

        // Press start to restart
        if button.start {
            transition Title
        }
    }
}

start Title
