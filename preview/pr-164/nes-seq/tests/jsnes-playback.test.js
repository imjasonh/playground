import test from "node:test";
import assert from "node:assert/strict";
import { createRequire } from "node:module";

import { songToNsf } from "../src/export/nsf.js";
import { nsfToInesRom } from "../src/export/nesRom.js";
import { createDemoSong, createSong } from "../src/song.js";
import { overdubNote } from "../src/sequencer/pattern.js";
import { renderSongToSamples } from "../src/export/wav.js";

const require = createRequire(import.meta.url);

/**
 * JSNES does not play NSF files directly. We wrap our NSF in a Mapper-0 ROM
 * (RESET→INIT, NMI→PLAY) and drive jsnes.NES to verify the bytes are readable
 * and the APU produces audible energy similar to our offline render.
 */
function loadJsnes() {
  try {
    return require("jsnes");
  } catch {
    return null;
  }
}

/**
 * @param {Uint8Array} rom
 * @param {{ frames?: number, sampleRate?: number, warmupFrames?: number }} [opts]
 */
function playRomWithJsnes(
  rom,
  { frames = 120, sampleRate = 44100, warmupFrames = 0 } = {},
) {
  const jsnes = loadJsnes();
  assert.ok(jsnes, "jsnes must be installed as a devDependency");

  /** @type {number[]} */
  const samples = [];
  /** @type {number[]} */
  const measureSamples = [];
  const nes = new jsnes.NES({
    emulateSound: true,
    sampleRate,
    onFrame() {},
    onAudioSample(left, right) {
      samples.push((left + right) * 0.5);
    },
  });

  // jsnes historically wants a binary string.
  const asBinary = Buffer.from(rom).toString("binary");
  nes.loadROM(asBinary);

  for (let i = 0; i < frames; i += 1) {
    const start = samples.length;
    nes.frame();
    if (i >= warmupFrames) {
      for (let j = start; j < samples.length; j += 1) {
        measureSamples.push(samples[j]);
      }
    }
  }

  let peak = 0;
  let sumSq = 0;
  for (const s of measureSamples) {
    if (!Number.isFinite(s)) continue;
    peak = Math.max(peak, Math.abs(s));
    sumSq += s * s;
  }
  const rms = measureSamples.length
    ? Math.sqrt(sumSq / measureSamples.length)
    : 0;
  return { samples: measureSamples, peak, rms, frames };
}

test("JSNES loads NSF-wrapped demo ROM without crashing", () => {
  const nsf = songToNsf(createDemoSong(), { loops: 1 });
  const rom = nsfToInesRom(nsf);
  const { peak, rms, samples } = playRomWithJsnes(rom, { frames: 90 });
  assert.ok(samples.length > 1000, `sample count ${samples.length}`);
  assert.ok(peak > 0.02, `JSNES peak ${peak}`);
  assert.ok(rms > 0.001, `JSNES rms ${rms}`);
});

test("JSNES audio energy is in the same ballpark as offline WAV render", () => {
  let song = createSong({ title: "Pulse", bpm: 140, length: 8 });
  song.patterns[0] = overdubNote(song.patterns[0], "pulse1", 0, 60, {
    length: 4,
  });
  song.patterns[0] = overdubNote(song.patterns[0], "pulse1", 4, 67, {
    length: 4,
  });

  const offline = renderSongToSamples(song, {
    sampleRate: 44100,
    loops: 1,
    tailSeconds: 0,
  });
  let offlinePeak = 0;
  for (const s of offline) offlinePeak = Math.max(offlinePeak, Math.abs(s));

  const rom = nsfToInesRom(songToNsf(song, { loops: 1 }));
  const { peak } = playRomWithJsnes(rom, { frames: 100, sampleRate: 44100 });

  assert.ok(offlinePeak > 0.05, `offline peak ${offlinePeak}`);
  assert.ok(peak > 0.02, `jsnes peak ${peak}`);
  // Different APU implementations → allow a wide ratio, but both must be audible.
  const ratio = peak / offlinePeak;
  assert.ok(ratio > 0.05 && ratio < 20, `peak ratio ${ratio}`);
});

test("silent NSF-wrapped ROM stays quiet in JSNES after warmup", () => {
  const song = createSong({ title: "Quiet", bpm: 120, length: 8 });
  const rom = nsfToInesRom(songToNsf(song, { loops: 1 }));
  // JSNES emits a short APU init transient; measure after it decays.
  const { peak } = playRomWithJsnes(rom, { frames: 90, warmupFrames: 20 });
  assert.ok(peak < 0.02, `silent peak ${peak}`);
});
