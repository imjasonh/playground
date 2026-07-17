# 2A03 — NES sequencer / looper

A browser MIDI sequencer and looper aimed at **faithful NES/2A03 music**, not
generic “8-bit flavored” softsynth tones. Audio is produced by a cycle-driven
RP2A03 APU emulator (pulse ×2, triangle, noise) running in an AudioWorklet when
available.

## Features (v1)

- **Four hardware channels** — Pulse 1, Pulse 2, Triangle, Noise
- **Step sequencer / looper** — 8 / 16 / 32 / 64 steps, per-channel overdub
- **Instrument macros** — duty, volume sequences, arpeggios (FamiTracker-style)
- **Web MIDI** — USB/Bluetooth controllers on Chrome, Edge, and Firefox
- **QWERTY piano** — `Z`–`/` and `Q`–`P`, with octave shift
- **WAV export** — offline render of the same APU engine
- **Local save** — pattern + instruments persist in `localStorage`

Safari can compose with the computer keyboard; it does not expose Web MIDI.

## Run locally

```bash
cd nes-seq
npm start          # http://localhost:3000
npm test
```

No build step — static ES modules, same as other playground browser apps.
`package-lock.json` is committed so CI’s `npm ci` succeeds even though there
are no runtime dependencies.

## Authoring model

The NES is not a polyphonic softsynth. Each channel is monophonic; expression
comes from **duty cycle**, **4-bit volume**, **arpeggio macros**, and **noise
mode** — the same constraints composers used on hardware.

| Channel  | Role                         | Knobs                          |
|----------|------------------------------|--------------------------------|
| Pulse 1/2 | Leads, harmony, arps        | Duty, volume macro, arp        |
| Triangle | Bass / sustained tones       | Pitch (no volume envelope)     |
| Noise    | Hats, snares, textures       | Period (via MIDI note), short LFSR |

### Workflow

1. Select a channel.
2. Click a step (or just start playing — entry advances the selected step).
3. Play notes via MIDI or the computer keyboard.
4. Hit **Rec** while playing to overdub into the live playhead.
5. Tweak the instrument macros; they expand while notes are held.
6. **Export WAV** for a bounce of the current loop.

## Architecture

```
src/apu/           cycle-driven 2A03 + note/period tables
src/instruments/   duty / volume / arp macros
src/sequencer/     pattern, transport, NesPlayer
src/audio/         AudioWorklet engine (+ main-thread fallback)
src/input/         Web MIDI + QWERTY
src/export/        offline render → 16-bit WAV
```

Unit tests exercise the APU, macros, sequencer, player, song I/O, and WAV path
with Node’s built-in test runner — no browser required.

## Limits / next

- DMC / DPCM samples not yet exposed
- No NSF or FamiTracker export yet (WAV is the v1 deliverable)
- Expansion audio (VRC6, N163, …) out of scope for v1
- Browser MIDI latency is fine for sketching; not Core Audio–class
