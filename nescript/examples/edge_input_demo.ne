// Edge-triggered input demo — the A / B buttons toggle a pair
// of sprites using `.pressed` / `.released` rather than the
// level-state `p1.button.a`. Held buttons only fire once per
// press, which is the canonical menu / one-shot action pattern.

game "Edge Input Demo" {
    mapper: NROM
}

var ax: u8 = 64
var bx: u8 = 120
var toggle_a: u8 = 0
var toggle_b: u8 = 0

on frame {
    // Each press moves the A-sprite 8 pixels right. Because
    // `.pressed` fires once per press transition, holding the
    // button down does not accelerate movement.
    if p1.button.a.pressed {
        ax += 8
        toggle_a = toggle_a ^ 1
    }

    // Release moves the B-sprite 4 pixels right on letting go.
    if p1.button.b.released {
        bx += 4
        toggle_b = toggle_b ^ 1
    }

    // Drive the frame colours off the toggles so the output is
    // observable in the emulator golden.
    draw Ball at: (ax, 80)
    draw Ball at: (bx, 120)

    // A tiny visual beacon for "toggle_a" / "toggle_b" so the
    // golden captures the state even before the user presses
    // anything.
    if toggle_a == 1 { draw Ball at: (ax, 90) }
    if toggle_b == 1 { draw Ball at: (bx, 130) }
}

start Main
