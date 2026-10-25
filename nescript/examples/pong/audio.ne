// pong/audio.ne — sfx + music declarations.
//
// Channel budget (same as war):
//     pulse 1  — every `play Name` sfx
//     pulse 2  — music (TitleTheme + builtin fanfare)
//     triangle — reserved
//     noise    — reserved for a later low-thud on paddle hit
//
// The audio tick is linked in only because the title state uses
// `start_music`, so everything below ends up in PRG ROM.

// ── Sound effects ──────────────────────────────────────────

// Quick high click when the ball bounces off a top/bottom wall.
sfx WallBounce {
    duty: 1
    pitch: 0x30
    envelope: [10, 6, 2]
}

// Brighter click with a slight descent when the ball hits a paddle.
sfx PaddleHit {
    duty: 2
    pitch: [0x28, 0x2C, 0x30]
    volume: [14, 10, 5]
}

// Short descending beep when a side scores a point.
sfx Score {
    duty: 2
    pitch: [0x40, 0x50, 0x60, 0x70]
    volume: [14, 12, 9, 4]
}

// Rising chirp when a powerup spawns in the middle of the field.
sfx PowerSpawn {
    duty: 3
    pitch: [0x80, 0x70, 0x60, 0x50, 0x40, 0x30]
    volume: [12, 12, 12, 12, 12, 8]
}

// Bright ascending blip when a paddle catches a powerup.
sfx PowerCatch {
    duty: 2
    pitch: [0x60, 0x50, 0x40, 0x30, 0x28, 0x20]
    volume: [15, 13, 11, 9, 7, 4]
}

// ── Music ──────────────────────────────────────────────────

// Brisk 4/4 title march on pulse 2. Four bars of a rising C-major
// phrase with punchy staccato notes so the menu feels energetic.
music TitleTheme {
    duty: 2
    volume: 10
    repeat: true
    tempo: 8
    notes: [
        // bar 1
        C4 4, E4 4, G4 8, E4 8, C4 8, rest 4,
        // bar 2
        G4 4, G4 4, C5 8, G4 8, E4 8, rest 4,
        // bar 3
        E4 4, G4 4, C5 8, E5 8, C5 8, rest 4,
        // bar 4 — resolution
        G4 4, G4 4, C5 16, rest 8
    ]
}
