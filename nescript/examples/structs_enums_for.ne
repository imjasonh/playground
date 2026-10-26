// Demonstrates struct types, enums, and for loops.
//
// A small "platformer" scaffold: the player has a position, velocity,
// and animation state held in a struct, enums describe directions and
// animation phases, and a for loop iterates over an array of stationary
// enemies each frame.
//
// Compile with the default IR codegen:
//   nescript build examples/structs_enums_for.ne

game "StructsDemo" { mapper: NROM }

// Named constants for the four cardinal directions. Each variant is
// a u8 value equal to its declaration order (Up=0, Down=1, etc.).
enum Direction { Up, Down, Left, Right }

enum AnimFrame { Idle, Run1, Run2 }

// A struct bundles related state into a single variable.
// See examples/nested_structs.ne for nested-struct and array-field
// fields; this example sticks to flat scalar fields for simplicity.
struct Player {
    x: u8,
    y: u8,
    vx: u8,
    vy: u8,
    facing: u8,   // Direction enum value
    frame: u8,   // AnimFrame enum value
    alive: bool,
}

// Struct literal initializer in declaration.
var player: Player = Player {
    x: 120,
    y: 112,
    vx: 0,
    vy: 0,
    facing: Down,
    frame: Idle,
    alive: true,
}

// A small fixed-size array of enemy x-positions. In a real game this
// would be an array of structs once those are supported.
var enemies_x: u8[4] = [32, 80, 160, 208]
var enemy_y: u8 = 100

const SPEED: u8 = 1

on frame {
    // Read controls and update position. Velocities are u8 so we
    // treat them as signed by adding/subtracting SPEED.
    if button.left {
        player.x -= SPEED
        player.facing = Left
    }
    if button.right {
        player.x += SPEED
        player.facing = Right
    }
    if button.up {
        player.y -= SPEED
        player.facing = Up
    }
    if button.down {
        player.y += SPEED
        player.facing = Down
    }

    // Draw the player — the IR codegen allocates the OAM slot.
    draw Smiley at: (player.x, player.y)

    // And each enemy, using a for loop over the array.
    for i in 0..4 {
        draw Smiley at: (enemies_x[i], enemy_y)
    }

    wait_frame
}

start Main
