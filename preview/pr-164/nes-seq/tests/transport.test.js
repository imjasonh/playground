import test from "node:test";
import assert from "node:assert/strict";

import {
  advanceTransport,
  createTransport,
  playheadStep,
  quantizeStep,
  samplesPerTick,
  secondsPerStep,
  setBpm,
  setPlaying,
  setRecording,
  TICKS_PER_STEP,
} from "../src/sequencer/transport.js";

test("secondsPerStep follows BPM", () => {
  assert.ok(Math.abs(secondsPerStep(120) - 0.125) < 1e-9);
  assert.ok(secondsPerStep(60) > secondsPerStep(180));
});

test("advanceTransport emits step boundaries", () => {
  const t = createTransport({ bpm: 120, patternLength: 4 });
  setPlaying(t, true);
  const spt = samplesPerTick(120, 44100);
  const samplesForOneStep = Math.ceil(spt * TICKS_PER_STEP);
  const { steps, ticks } = advanceTransport(t, samplesForOneStep, 44100);
  assert.ok(ticks >= TICKS_PER_STEP);
  assert.ok(steps.includes(1));
  assert.equal(t.step, 1);
});

test("transport wraps pattern length", () => {
  const t = createTransport({ bpm: 240, patternLength: 4 });
  setPlaying(t, true);
  const spt = samplesPerTick(240, 22050);
  const need = Math.ceil(spt * TICKS_PER_STEP * 4) + 10;
  advanceTransport(t, need, 22050);
  assert.ok(t.step >= 0 && t.step < 4);
});

test("stop resets playhead", () => {
  const t = createTransport({ bpm: 100, patternLength: 8 });
  setPlaying(t, true);
  advanceTransport(t, 20000, 44100);
  setPlaying(t, false);
  assert.equal(t.step, 0);
  assert.equal(t.playing, false);
});

test("recording implies playing", () => {
  const t = createTransport();
  setRecording(t, true);
  assert.equal(t.recording, true);
  assert.equal(t.playing, true);
});

test("setBpm clamps", () => {
  const t = createTransport();
  setBpm(t, 10);
  assert.equal(t.bpm, 40);
  setBpm(t, 900);
  assert.equal(t.bpm, 280);
});

test("quantizeStep and playheadStep", () => {
  assert.equal(quantizeStep(3.6, 16), 4);
  assert.equal(quantizeStep(-1, 16), 15);
  const t = createTransport({ bpm: 120, patternLength: 16 });
  setPlaying(t, true);
  t.step = 2;
  t.tickInStep = TICKS_PER_STEP / 2;
  const ph = playheadStep(t, 44100);
  assert.ok(ph > 2 && ph < 3);
});
