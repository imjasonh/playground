// MMC1 Banked — demonstrates M5 mapper and bank features.
//
// Shows: MMC1 mapper selection, bank declarations,
// vertical mirroring, software multiply.
//
// Build: cargo run -- build examples/mmc1_banked.ne

game "Banked Game" {
    mapper: MMC1
    mirroring: vertical
}

// Declare PRG banks for organizing code/data
bank Level1Data: prg
bank Level2Data: prg
bank TileBank: chr

const GRAVITY: u8 = 1
const JUMP_VEL: u8 = 5
const GROUND_Y: u8 = 200

var px: u8 = 64
var py: u8 = 200
var vy: u8 = 0
var airborne: u8 = 0
var level: u8 = 1

// Multiplication via the language (uses software multiply runtime)
fun scale_speed(base: u8, factor: u8) -> u8 {
    return base * factor
}

fun apply_gravity() {
    if airborne == 1 {
        vy += GRAVITY
        py += vy
        if py >= GROUND_Y {
            py = GROUND_Y
            airborne = 0
            vy = 0
        }
    }
}

state Level1 {
    on enter {
        px = 64
        py = GROUND_Y
        level = 1
    }

    on frame {
        // Horizontal movement with scaled speed
        if button.right {
            var spd: u8 = scale_speed(2, level)
            px += spd
        }
        if button.left {
            if px > 2 {
                px -= 2
            }
        }

        // Jump
        if button.a {
            if airborne == 0 {
                airborne = 1
                vy = JUMP_VEL
            }
        }

        apply_gravity()

        // Advance to level 2
        if px > 230 {
            transition Level2
        }

        draw Player at: (px, py)
    }
}

state Level2 {
    on enter {
        px = 10
        py = GROUND_Y
        level = 2
    }

    on frame {
        if button.right { px += 3 }
        if button.left  { px -= 3 }

        if button.a {
            if airborne == 0 {
                airborne = 1
                vy = JUMP_VEL
            }
        }

        apply_gravity()

        // Loop back
        if button.select {
            transition Level1
        }

        draw Player at: (px, py)
    }
}

start Level1
