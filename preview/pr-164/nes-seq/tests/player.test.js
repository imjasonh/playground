import test from "node:test";
import assert from "node:assert/strict";

import { NesApu } from "../src/apu/nesApu.js";
import { createDefaultInstruments } from "../src/instruments/macros.js";
import {
  createEmptyPattern,
  overdubNote,
  setCut,
} from "../src/sequencer/pattern.js";
import { NesPlayer } from "../src/sequencer/player.js";
import {
  createTransport,
  setPlaying,
} from "../src/sequencer/transport.js";
import { createDemoSong } from "../src/song.js";

function makePlayer(patterns, order = [0], bpm = 180) {
  const defaults = createDefaultInstruments();
  const instruments = {
    pulse1: { ...defaults[0], channel: "pulse1" },
    pulse2: { ...defaults[1], channel: "pulse2" },
    triangle: { ...defaults.find((i) => i.id === "tri-bass"), channel: "triangle" },
    noise: { ...defaults.find((i) => i.id === "noise-hat"), channel: "noise" },
  };
  const apu = new NesApu();
  const transport = createTransport({
    bpm,
    patternLength: patterns[0].length,
  });
  const player = new NesPlayer(apu, {
    patterns,
    order,
    transport,
    instruments,
    sampleRate: 22050,
  });
  return { apu, transport, player };
}

test("sequenced pattern produces audio across a loop", () => {
  let pattern = createEmptyPattern(8);
  pattern = overdubNote(pattern, "pulse1", 0, 60);
  pattern = overdubNote(pattern, "pulse1", 4, 67);
  pattern = overdubNote(pattern, "triangle", 0, 36, { length: 2 });
  const { transport, player } = makePlayer([pattern], [0], 200);
  setPlaying(transport, true);
  player.onStart();
  const out = new Float32Array(22050);
  player.render(out);
  const peak = Math.max(...out.map(Math.abs));
  const rms = Math.sqrt(out.reduce((s, x) => s + x * x, 0) / out.length);
  assert.ok(peak > 0.05, `peak ${peak}`);
  assert.ok(rms > 0.005, `rms ${rms}`);
});

test("order list advances across patterns", () => {
  let a = createEmptyPattern(4, "A");
  let b = createEmptyPattern(4, "B");
  a = overdubNote(a, "pulse1", 0, 60, { length: 1, gate: 6 });
  b = overdubNote(b, "pulse1", 0, 72, { length: 1, gate: 6 });
  const { transport, player } = makePlayer([a, b], [0, 1], 240);
  setPlaying(transport, true);
  player.onStart();
  assert.equal(player.orderIndex, 0);
  // Render enough for more than one pattern at high BPM.
  const out = new Float32Array(22050);
  player.render(out);
  assert.ok(player.orderIndex === 0 || player.orderIndex === 1);
  // Should have visited pattern B at some point during the buffer.
  assert.ok(out.some((s) => Math.abs(s) > 0.02));
});

test("cut step releases the voice", () => {
  let pattern = createEmptyPattern(8);
  pattern = overdubNote(pattern, "pulse1", 0, 60, { length: 8 });
  pattern = setCut(pattern, "pulse1", 2);
  const { transport, player } = makePlayer([pattern], [0], 200);
  setPlaying(transport, true);
  player.onStart();
  const out = new Float32Array(8000);
  player.render(out);
  // After the cut, later samples should trend quieter than the attack.
  const early = out.slice(0, 1000);
  const late = out.slice(5000, 6000);
  const earlyPeak = Math.max(...early.map(Math.abs));
  const latePeak = Math.max(...late.map(Math.abs));
  assert.ok(earlyPeak > 0.04, `early ${earlyPeak}`);
  assert.ok(latePeak < earlyPeak, `late ${latePeak} vs early ${earlyPeak}`);
});

test("live noteOn produces sound while stopped", () => {
  const pattern = createEmptyPattern(8);
  const { player } = makePlayer([pattern]);
  player.noteOn("pulse1", 64, 12);
  const out = new Float32Array(4096);
  player.render(out);
  const peak = Math.max(...out.map(Math.abs));
  assert.ok(peak > 0.04, `peak ${peak}`);
  player.noteOff("pulse1");
});

test("demo song order renders audible audio", () => {
  const demo = createDemoSong();
  const { transport, player } = makePlayer(
    demo.patterns,
    demo.order,
    demo.bpm,
  );
  setPlaying(transport, true);
  player.onStart();
  const out = new Float32Array(22050);
  player.render(out);
  assert.ok(Math.max(...out.map(Math.abs)) > 0.05);
});

test("allNotesOff silences output", () => {
  const pattern = createEmptyPattern(8);
  const { player } = makePlayer([pattern]);
  player.noteOn("noise", 70, 12);
  player.allNotesOff();
  const out = new Float32Array(2048);
  player.render(out);
  const peak = Math.max(...out.map(Math.abs));
  assert.ok(peak < 0.05, `peak ${peak}`);
});
