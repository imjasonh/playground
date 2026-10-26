// Fade demo — blocking fade_out / fade_in builtins cycle between
// normal and black every few seconds. Exercises the runtime fade
// helper that walks 5 brightness levels with a user-controlled
// step delay between each.

game "Fade Demo" {
    mapper: NROM
}

var frame: u8 = 0

on frame {
    frame += 1

    // Every 120 frames (~2 sec), fade out and back in. Each fade
    // takes 5 steps × 6 frames = 30 frames.
    if frame == 30 {
        fade_out(6)
    }
    if frame == 120 {
        fade_in(6)
        frame = 0
    }

    draw Ball at: (120, 100)
}

start Main
