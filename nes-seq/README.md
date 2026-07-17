# 2A03 — NES sequencer / looper

A browser MIDI sequencer and looper aimed at **faithful NES/2A03 music**, not
generic “8-bit flavored” softsynth tones. Audio is produced by a cycle-driven
RP2A03 APU emulator (pulse ×2, triangle, noise) running in an AudioWorklet when
available.

## Features

- **Four hardware channels** — Pulse 1, Pulse 2, Triangle, Noise
- **Multi-pattern songs** — up to 16 patterns with an order list (verse/chorus)
- **Step sequencer / looper** — 8 / 16 / 32 / 64 steps, per-channel overdub
- **Note effects** — length, gate, slide-to, and note cuts
- **Instrument macros** — duty, volume, arpeggio, pitch envelope, vibrato, delay
- **Preset library** — per-channel instrument presets
- **Web MIDI** — USB/Bluetooth controllers on Chrome, Edge, and Firefox
- **QWERTY piano** — `Z`–`/` and `Q`–`P`, with octave shift (`Shift+X` = cut)
- **WAV + NSF export** — full order list, same register stream as authoring
- **Local save** — song v2 persists in `localStorage` (v1 songs migrate)

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
6. **Export WAV** for a bounce, or **Export NSF** for emulator playback.

## NSF export

`Export NSF` compiles the current loop into a non-bankswitched NTSC NSF:

1. The authoring `NesPlayer` runs once, recording APU register writes.
2. Writes are delta-encoded into ~60 Hz PLAY frames.
3. A tiny 6502 player (INIT / PLAY) is assembled at `$8000` and packed with a
   standard NSF header.

Open the `.nsf` in any NSF-capable player (VirtuaNSF, Nestopia NSF mode,
Game_Music_Emu front-ends, etc.). JSNES does **not** load NSF files directly;
CI wraps the NSF in a Mapper-0 iNES ROM (`src/export/nesRom.js`) and plays that
through `jsnes` to verify the bytes are readable and audible.

## Architecture

```
src/apu/           cycle-driven 2A03 + note/period tables
src/instruments/   duty / volume / arp macros
src/sequencer/     pattern, transport, NesPlayer
src/audio/         AudioWorklet engine (+ main-thread fallback)
src/input/         Web MIDI + QWERTY
src/export/        WAV, NSF, iNES ROM wrapper (for JSNES tests)
```

Unit tests exercise the APU, macros, sequencer, player, song I/O, WAV/NSF
export, and JSNES ROM playback with Node’s built-in test runner.

## Limits / next

- DMC / DPCM samples not yet exposed
- No hardware sweep unit UI (pitch macros approximate slides/drops)
- No FamiTracker `.ftm` export yet
- Expansion audio (VRC6, N163, …) out of scope
- Browser MIDI latency is fine for sketching; not Core Audio–class
