// Bitwise Ops — demonstrates shift and mask operators on a packed
// "status" byte that holds several small flags.
//
// The byte layout:
//   bit 7 — alive
//   bit 6 — shield
//   bit 5 — powered
//   bit 4 — invulnerable
//   bits 0..3 — health (0..15)
//
// The player toggles each high-bit flag with the face buttons and
// heals/damages the low nibble with the d-pad. The drawing code
// reads each flag with an `and` mask after shifting the status byte
// into place — a typical pattern on the 6502.
//
// Build: cargo run -- build examples/bitwise_ops.ne

game "Bitwise Ops" {
    mapper: NROM
}

const ALIVE:     u8 = 0x80
const SHIELD:    u8 = 0x40
const POWERED:   u8 = 0x20
const INVULN:    u8 = 0x10
const HEALTH_MASK: u8 = 0x0F

var status: u8 = 0x8F     // alive + full health
var debounce: u8 = 0

on frame {
    if debounce > 0 {
        debounce -= 1
    }

    // Toggle each flag on a different face button. `^` is XOR,
    // which flips exactly the masked bit.
    if button.a and debounce == 0 {
        status = status ^ SHIELD
        debounce = 15
    }
    if button.b and debounce == 0 {
        status = status ^ POWERED
        debounce = 15
    }
    if button.start and debounce == 0 {
        status = status ^ INVULN
        debounce = 15
    }
    if button.select and debounce == 0 {
        status = status ^ ALIVE
        debounce = 15
    }

    // D-pad tweaks the low-nibble health counter. Clear the low
    // nibble, compute new health, then OR it back in — the
    // canonical "update a bitfield" pattern.
    var health: u8 = status & HEALTH_MASK
    if button.right and debounce == 0 {
        if health < 15 {
            health += 1
        }
        debounce = 8
    }
    if button.left and debounce == 0 {
        if health > 0 {
            health -= 1
        }
        debounce = 8
    }
    status = (status & 0xF0) | health

    // Read back each flag with a mask + nonzero test.
    if (status & ALIVE) != 0 {
        draw Player at: (120, 120)
    }
    if (status & SHIELD) != 0 {
        draw Ring at: (120, 120)
    }
    if (status & POWERED) != 0 {
        draw Spark at: (136, 120)
    }
    if (status & INVULN) != 0 {
        draw Spark at: (104, 120)
    }

    // Draw a health bar by shifting the low nibble into a loop
    // counter. `>>` divides by 2^n on the 6502 with a shift, which
    // the optimizer also emits for `/ 2`.
    var bars: u8 = health >> 1   // 0..7 bars
    var i: u8 = 0
    while i < bars {
        draw Pip at: (40 + i * 10, 200)
        i += 1
    }
}

start Main
