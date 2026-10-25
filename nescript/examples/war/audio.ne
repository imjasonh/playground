// war/audio.ne — every sfx + music declaration in the game.
//
// The NEScript audio driver is only linked in when user code
// contains at least one `play` / `start_music` / `stop_music`
// statement. That's always true for this game, so everything
// declared here ends up in PRG ROM.
//
// Channel budget:
//     pulse 1 — sfx (FlipCard, CheerA, CheerB, WarFlash)
//     pulse 2 — music (TitleTheme and the builtin fanfare)
//     triangle — unused (reserved for later)
//     noise   — ThudDown bury sfx

// ── Sound effects ──────────────────────────────────────────

// Sharp descending click for a card flip / draw. Kept short so
// repeated clicks during the deal animation don't overlap.
sfx FlipCard {
    duty: 1
    pitch: 0x28
    envelope: [12, 9, 5, 2]
}

// Cheerful ascending arpeggio when player A wins a round. The
// per-frame pitch envelope sweeps through three notes so the
// effect actually sounds like a melody rather than a beep.
sfx CheerA {
    duty: 2
    pitch:  [0x50, 0x50, 0x50, 0x40, 0x40, 0x40, 0x30, 0x30, 0x30, 0x28]
    volume: [14,   13,   12,   14,   13,   12,   14,   13,   12,   10]
}

// Same shape but descending for player B — immediately
// distinguishable from CheerA without reading the screen.
sfx CheerB {
    duty: 2
    pitch:  [0x30, 0x30, 0x30, 0x40, 0x40, 0x40, 0x50, 0x50, 0x50, 0x60]
    volume: [14,   13,   12,   14,   13,   12,   14,   13,   12,   10]
}

// Exciting two-part pitch sweep for the "WAR!" tie-break. A
// rising trill followed by a descending burst. The volume ramps
// loud-soft-loud to really stand out from the calmer round sfx.
sfx WarFlash {
    duty: 3
    pitch:  [0x80, 0x60, 0x40, 0x30, 0x20, 0x20, 0x30, 0x40, 0x60, 0x80, 0x60, 0x40, 0x20, 0x20, 0x20, 0x20]
    volume: [15,   13,   11,   9,    8,    10,   12,   14,   15,   13,   11,   9,    7,    5,    3,    1]
}

// Low noise thump for each card buried during a war.
sfx ThudDown {
    channel: noise
    pitch: 8
    volume: [15, 11, 7, 3]
}

// ── Music ──────────────────────────────────────────────────

// Brisk 4/4 march on pulse 2 for the title screen. The pattern is
// a military-style tonic-dominant alternation (C - G - C - G) with
// a quick triplet pickup into each down-beat, evoking the rolling
// snare of a war drum. Every note is short and staccato so the
// melody feels like it's being played on a single high-pitched
// fife over an implied drum line.
//
// Four bars (two repeats of a two-bar phrase) that loop
// seamlessly.
music TitleTheme {
    duty: 2
    volume: 10
    repeat: true
    tempo: 8
    notes: [
        // bar 1 — C major down-beat with pickup triplet
        G4 4, G4 4, C5 8, G4 8, E4 8, C4 8,
        // bar 2 — dominant with rising triplet
        G4 4, G4 4, G4 8, C5 8, E5 8, G4 8,
        // bar 3 — tonic inversion, military flourish
        C5 4, G4 4, E5 8, C5 8, G4 8, E4 8,
        // bar 4 — resolution back to tonic
        G4 4, G4 4, C5 8, G4 8, C4 16,
        rest 8
    ]
}
