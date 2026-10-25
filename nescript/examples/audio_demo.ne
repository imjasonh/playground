// Audio Demo — showcases the full audio subsystem.
//
// NEScript has three audio statements:
//     play Name        — trigger an SFX on pulse 1 (one-shot)
//     start_music Name — play a background music track on pulse 2
//     stop_music       — silence the music channel
//
// SFX and music tracks are compiled into PRG ROM data tables and
// walked one byte per NMI by the builtin audio driver. You can
// either use the builtin names (coin, jump, theme, ...) or declare
// your own via `sfx Name { ... }` / `music Name { ... }` blocks.
//
// Builtin SFX names:
//     coin, pickup, collect      — high ascending blip
//     jump, hop                  — descending arc
//     hit, damage, explode       — low blast
//     click, select, confirm     — sharp beep
//     cancel, back, error        — low longer tone
//     shoot, laser, fire         — very high pulse
//     step, footstep             — low thud
//
// Builtin music names:
//     title, theme, main         — major arpeggio (looping)
//     battle, boss               — driving pulse (looping)
//     win, victory, fanfare      — ascending burst (one-shot)
//     gameover, lose, fail       — descending dirge (looping)
//
// Build:  cargo run -- build examples/audio_demo.ne
// Output: examples/audio_demo.nes

game "Audio Demo" {
    mapper: NROM
}

// ── User-declared sound effects ──
//
// An `sfx` block is a frame-accurate envelope for pulse 1. `pitch`
// is latched into `$4002` once on trigger — the v1 audio driver
// never updates the pulse period mid-effect — so a single scalar
// byte is the natural form for the current pipeline. `envelope:`
// is a friendlier alias for `volume:`: both describe the per-frame
// volume ramp that shapes the effect. `duty` (0-3) picks the pulse
// waveform (2 = 50% square).

// A gentle rising chirp, longer than the builtin coin.
sfx LongCoin {
    duty: 2
    pitch: 0x50
    envelope: [15, 14, 13, 12, 11, 9, 7, 5, 3, 1]
}

// A sharp two-part zap — quick high spike into silence.
sfx Zap {
    duty: 3
    pitch: 0x20
    envelope: [15, 12, 8, 4, 1]
}

// ── User-declared music tracks ──
//
// Notes are written in note-name form (`C4`, `E4`, `G4`, …) with a
// default frames-per-note set by `tempo:`. Any note can override
// the default by trailing the name with an explicit duration
// (e.g. `G4 40` holds twice as long). `rest` (or the alias `_`) is
// a silent beat. Use the legacy `37, 20, 41, 20, ...` pair form by
// leaving `tempo:` out if you'd rather pick pitches by index.

// A cheerful four-note looping theme — every note is one-third of
// a second long, and the whole loop is 120 frames = 2 seconds.
music Theme {
    duty: 2
    volume: 10
    repeat: true
    tempo: 20
    notes: [
        C4, E4, G4, C5, G4, E4
    ]
}

// ── Game state ──

var px: u8 = 128
var py: u8 = 120
var timer: u8 = 0
var music_on: bool = false

on frame {
    // Move the smiley so you can see the game is running.
    if button.right { px += 1 }
    if button.left  { px -= 1 }
    if button.down  { py += 1 }
    if button.up    { py -= 1 }

    // Input-triggered SFX.
    if button.a { play LongCoin }
    if button.b { play Zap }

    // Start/stop the user-declared theme.
    if button.start  { start_music Theme }
    if button.select { stop_music }

    // Auto-play a builtin coin SFX every 60 frames so the e2e
    // harness (which runs headless without simulated input) can
    // capture a non-silent audio hash. Also toggles the music
    // every 120 frames to exercise start/stop paths.
    timer += 1
    if timer == 30 {
        play coin
    }
    if timer == 120 {
        timer = 0
        if music_on {
            stop_music
            music_on = false
        } else {
            start_music Theme
            music_on = true
        }
    }

    draw Smiley at: (px, py)
}

start Main
