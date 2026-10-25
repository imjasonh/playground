// Arrays and Functions — demonstrates M2 features.
//
// Shows: arrays, functions with parameters and return values,
// while loops, constants, inline functions.
//
// Build: cargo run -- build examples/arrays_and_functions.ne

game "Arrays Demo" {
    mapper: NROM
}

const NUM_ENEMIES: u8 = 4
const SPEED: u8 = 1

var player_x: u8 = 128
var player_y: u8 = 200

// Enemy positions stored in arrays
var enemy_x: u8[4] = [30, 80, 130, 200]
var enemy_y: u8[4] = [40, 80, 120, 60]

// Function: clamp value to screen bounds
fun clamp(val: u8, max: u8) -> u8 {
    if val > max {
        return max
    }
    return val
}

// Inline function: absolute difference
// Not marked `inline`: the conditional early return is one of
// the shapes the inliner declines (W0110). Living with the JSR
// is the correct call here since rewriting as a branchless max
// wouldn't fit in a single-return expression.
fun abs_diff(a: u8, b: u8) -> u8 {
    if a > b {
        return a - b
    }
    return b - a
}

// Function: check collision between two points
fun check_collision(x1: u8, y1: u8, x2: u8, y2: u8) -> u8 {
    var dx: u8 = abs_diff(x1, x2)
    var dy: u8 = abs_diff(y1, y2)
    if dx < 8 {
        if dy < 8 {
            return 1
        }
    }
    return 0
}

on frame {
    // Player movement
    if button.right { player_x += SPEED }
    if button.left  { player_x -= SPEED }
    if button.down  { player_y += SPEED }
    if button.up    { player_y -= SPEED }

    player_x = clamp(player_x, 240)
    player_y = clamp(player_y, 224)

    // Update and draw enemies
    var i: u8 = 0
    while i < NUM_ENEMIES {
        // Move enemies down slowly
        enemy_y[i] += 1
        if enemy_y[i] > 224 {
            enemy_y[i] = 0
        }

        // Check collision with player
        var hit: u8 = check_collision(player_x, player_y, enemy_x[i], enemy_y[i])
        if hit == 1 {
            // Reset enemy position on collision
            enemy_y[i] = 0
        }

        draw Enemy at: (enemy_x[i], enemy_y[i])
        i += 1
    }

    draw Player at: (player_x, player_y)
}

start Main
