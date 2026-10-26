// rampart/audio.ne: move and weapon effects, and the march.
//
// Channel budget. Pulse 1 is sound effects. Pulse 2 is the march.
// Noise is footsteps, the gatling cannon, and impacts. A second
// `play` on the same channel restarts that channel, so two effects
// that share a channel must not start on the same frame. Pulse and
// noise can start together. Triangle stays unused: an effect's
// period high byte is fixed at 0, so the lowest triangle note is
// about A4, too high for a thud.

// ── Movement ───────────────────────────────────────────────
// One effect per move action, played when the mech actually
// changes squares. Step is one thud. Rush is two quicker ones.
// Charge is a heavier stomp, before the arm weapon swings.

sfx MoveStep {
    channel: noise
    pitch: 10
    volume: [13, 10, 6, 3, 1]
}

sfx MoveRush {
    channel: noise
    pitch: 7
    volume: [14, 8, 3, 0, 13, 7, 2]
}

sfx MoveCharge {
    channel: noise
    pitch: 14
    volume: [15, 14, 12, 9, 6, 4, 2, 1]
}

// ── Weapons ────────────────────────────────────────────────
// Played when the shot resolves, hit or miss. The ids match
// W_LANCE and the rest in constants.ne.

// Rising beam.
sfx Lance {
    duty: 2
    pitch: [0x58, 0x50, 0x48, 0x40, 0x3A, 0x34, 0x30, 0x2C, 0x28, 0x26, 0x24, 0x22, 0x20, 0x1E, 0x1C, 0x1A, 0x18, 0x18, 0x18, 0x18]
    volume: [12, 13, 14, 15, 15, 15, 14, 14, 13, 12, 11, 10, 8, 6, 5, 4, 3, 2, 1, 0]
}

// Short bursts on the noise channel.
sfx Cannon {
    channel: noise
    pitch: 3
    volume: [15, 8, 15, 6, 15, 8, 15, 6, 14, 5, 12, 4, 8, 2]
}

// Falling tone plus a noise wash, started on the same frame.
sfx Missile {
    duty: 1
    pitch: [0x30, 0x38, 0x40, 0x48, 0x50, 0x58, 0x60, 0x70, 0x80, 0x90, 0xA0, 0xB0, 0xB0, 0xB0]
    volume: [10, 12, 14, 14, 13, 12, 10, 8, 6, 5, 4, 3, 2, 1]
}

sfx MissileWash {
    channel: noise
    pitch: 8
    volume: [8, 12, 11, 9, 7, 5, 3, 1]
}

// A bright tick that drops, shorter than the lance.
sfx Sword {
    duty: 2
    pitch: [0x1C, 0x1C, 0x28, 0x28, 0x30, 0x38, 0x40, 0x48]
    volume: [15, 12, 14, 10, 8, 5, 3, 1]
}

// Short-mode noise, lower and metallic.
sfx Hammer {
    channel: noise
    pitch: 0x8A
    volume: [15, 13, 10, 6, 3, 1]
}

// ── March ──────────────────────────────────────────────────
// Sixteen bars of 4/4 in D minor, eighth notes at 150 BPM
// (12 frames each). Duty 1 is the narrow pulse. The flat 2
// (Eb) is the grind in the low riff. Bars 9 to 12 answer an
// octave up, then the riff returns. The last note is D3 and
// the first note is D3, so the loop does not jump.

music March {
    duty: 1
    volume: 9
    repeat: true
    tempo: 12
    notes: [
        D3, D3, D3, F3, Eb3, D3, C3, D3,
        D3, D3, Bb2, C3, D3, F3, E3, D3,
        D3, D3, D3, F3, Eb3, D3, C3, D3,
        A2, C3, D3, F3, E3, D3, C3, A2,

        A3, A3, A3, C4, Bb3, A3, G3, A3,
        A3, A3, F3, G3, A3, C4, Bb3, A3,
        G3, G3, G3, Bb3, A3, G3, F3, G3,
        E3, F3, G3, A3, G3, F3, E3, D3,

        D4, F4, E4, D4, C4, D4, F4, E4,
        D4, C4, Bb3, A3, Bb3, A3, G3, F3,
        G3, Bb3, A3, G3, F3, G3, A3, C4,
        D4, C4, A3, F3, E3, D3, C3, D3,

        D3, D3, D3, F3, Eb3, D3, C3, D3,
        D3, D3, Bb2, C3, D3, F3, E3, D3,
        F3, E3, D3, C3, Bb2, C3, D3, E3,
        A2, D3, F3, E3, D3, C3, A2, D3
    ]
}
