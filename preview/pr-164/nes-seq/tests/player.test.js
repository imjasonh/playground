import test from "node:test";
import assert from "node:assert/strict";

import { NesApu } from "../src/apu/nesApu.js";
import { createDefaultInstruments } from "../src/instruments/macros.js";
import { createEmptyPattern, overdubNote } from "../src/sequencer/pattern.js";
import { NesPlayer } from "../src/sequencer/player.js";
import {
  createTransport,
  setPlaying,
} from "../src/sequencer/transport.js";

function makePlayer(pattern, bpm = 180) {
  const defaults = createDefaultInstruments();
  const instruments = {
    pulse1: { ...defaults[0], channel: "pulse1" },
    pulse2: { ...defaults[1], channel: "pulse2" },
    triangle: { ...defaults[3], channel: "triangle" },
    noise: { ...defaults[4], channel: "noise" },
  };
  const apu = new NesApu();
  const transport = createTransport({
    bpm,
    patternLength: pattern.length,
  });
  const player = new NesPlayer(apu, {
    pattern,
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
  const { transport, player } = makePlayer(pattern, 200);
  setPlaying(transport, true);
  player.onStart();
  const out = new Float32Array(22050); // ~1s
  player.render(out);
  const peak = Math.max(...out.map(Math.abs));
  const rms = Math.sqrt(out.reduce((s, x) => s + x * x, 0) / out.length);
  assert.ok(peak > 0.05, `peak ${peak}`);
  assert.ok(rms > 0.005, `rms ${rms}`);
});

test("live noteOn produces sound while stopped", () => {
  const pattern = createEmptyPattern(8);
  const { player } = makePlayer(pattern);
  player.noteOn("pulse1", 64, 12);
  const out = new Float32Array(4096);
  player.render(out);
  const peak = Math.max(...out.map(Math.abs));
  assert.ok(peak > 0.04, `peak ${peak}`);
  player.noteOff("pulse1");
});

test("live voice overrides sequencer on same channel", () => {
  let pattern = createEmptyPattern(8);
  pattern = overdubNote(pattern, "pulse1", 0, 48);
  const { transport, player } = makePlayer(pattern, 160);
  setPlaying(transport, true);
  player.onStart();
  player.noteOn("pulse1", 72, 12);
  assert.ok(player.liveVoices.pulse1);
  const out = new Float32Array(2048);
  player.render(out);
  assert.ok(player.liveVoices.pulse1);
});

test("allNotesOff silences output", () => {
  const pattern = createEmptyPattern(8);
  const { player } = makePlayer(pattern);
  player.noteOn("noise", 70, 12);
  player.allNotesOff();
  const out = new Float32Array(2048);
  player.render(out);
  const peak = Math.max(...out.map(Math.abs));
  assert.ok(peak < 0.05, `peak ${peak}`);
});
