// Noise / Triangle SFX Demo
//
// Showcases the newer `channel:` property on `sfx` blocks. The audio
// driver's per-frame tick gains a noise channel (writes to $400C) and
// a triangle channel (writes to $4008) whenever the program declares
// at least one sfx targeting those channels. Programs that stick to
// pulse 1 still emit the exact same driver code as before.
//
// Every 30 frames we trigger one of the two effects and move a small
// smiley back and forth so it's obvious the program is still running.
// The emulator harness sees the registers get poked and hashes the
// APU output, so the golden locks in both the pixels *and* the sound.
//
// Build: cargo run -- build examples/noise_triangle_sfx.ne
// Output: examples/noise_triangle_sfx.nes

game "Noise Triangle SFX" {
    mapper: NROM
}

// A short, sharp noise burst — perfect for explosions / footsteps.
// `pitch: 4` indexes the APU's 16-entry noise period table; lower
// values are higher-pitched. `volume` is a per-frame amplitude ramp,
// exactly like a pulse sfx.
sfx Crash {
    channel: noise
    pitch: 4
    volume: [15, 13, 11, 9, 7, 5, 3, 1]
}

// A sustained triangle "bass" note. Triangle has no volume register,
// so `volume:` entries are just "hold" flags — nonzero means sustain,
// zero means silence. The numeric value doesn't matter.
// `pitch: 60` picks a period-table entry; triangle shares the pulse
// period table, and 60 is the lowest note in it (C1).
sfx Bass {
    channel: triangle
    pitch: 60
    volume: [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
}

var px: u8 = 120
var timer: u8 = 0
var bounce: u8 = 0

on frame {
    // Bounce the smiley between x=110 and x=140 so frame 180 is
    // not a still frame — the golden image diff would otherwise
    // miss the "program is running" signal.
    timer += 1
    if bounce == 0 {
        px += 1
        if px == 140 { bounce = 1 }
    } else {
        px -= 1
        if px == 110 { bounce = 0 }
    }

    // Cycle through the two sfx every 30 frames so each channel
    // retriggers at least twice inside the 180-frame capture window.
    if timer == 30 { play Crash }
    if timer == 60 {
        timer = 0
        play Bass
    }

    draw Smiley at: (px, 120)
}

start Main
