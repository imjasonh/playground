// Per-frame pitch envelope on a pulse SFX. The user authors the
// `pitch:` array as one byte per frame (matching the per-frame
// `volume:` array) and the runtime audio tick walks both pointers
// in lockstep, writing pitch to `$4002` and volume to `$4000` on
// every NMI. The result is a frequency-sweeping "siren" tone — the
// classic latch-once pulse SFX driver couldn't model this at all.
//
// Per-frame pitch is opt-in: if the `pitch:` array has a single
// value (or repeats one byte) the compiler emits the byte-identical
// pre-pitch-envelope sequence and no extra blob, so existing
// programs that just want a static pitch keep working unchanged.
// See `runtime/gen_audio_tick` for the gated extension.
//
// Build: cargo run -- build examples/sfx_pitch_envelope.ne

game "SFX Pitch Envelope" {
    mapper: NROM
}

// 16-frame pitch sweep from $40 down to $20 paired with a slow
// volume ramp. Both arrays are the same length so the runtime's
// lockstep walker handles the simplest possible case.
sfx Siren {
    duty: 2
    pitch:  [0x40, 0x3D, 0x3A, 0x37, 0x34, 0x31, 0x2E, 0x2B, 0x28, 0x26, 0x24, 0x22, 0x21, 0x20, 0x20, 0x20]
    volume: [15,   14,   13,   12,   11,   10,   9,    8,    7,    6,    5,    4,    3,    2,    1,    0]
}

var tick: u8 = 0

on frame {
    // Re-trigger the sfx every 60 frames so the siren restarts
    // whenever the previous pass mutes itself, giving the
    // emulator harness a stable pattern to capture.
    tick += 1
    if tick == 60 {
        tick = 0
        play Siren
    }
}

start Main
