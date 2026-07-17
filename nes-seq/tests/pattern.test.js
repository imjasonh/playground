import test from "node:test";
import assert from "node:assert/strict";

import {
  clearStep,
  clonePattern,
  countNotes,
  createEmptyPattern,
  getStep,
  noteHoldTicks,
  overdubNote,
  patternFromJSON,
  patternToJSON,
  resizePattern,
  setCut,
  setStep,
} from "../src/sequencer/pattern.js";
import { TICKS_PER_STEP } from "../src/sequencer/transport.js";

test("createEmptyPattern initializes all channels", () => {
  const p = createEmptyPattern(16);
  assert.equal(p.length, 16);
  assert.equal(p.tracks.pulse1.length, 16);
  assert.equal(p.tracks.noise.length, 16);
  assert.equal(countNotes(p), 0);
});

test("setStep / getStep / clearStep round-trip", () => {
  let p = createEmptyPattern(8);
  p = setStep(p, "pulse1", 3, {
    midi: 60,
    velocity: 10,
    length: 2,
    gate: 4,
    slideTo: 64,
  });
  assert.deepEqual(getStep(p, "pulse1", 3), {
    midi: 60,
    velocity: 10,
    length: 2,
    gate: 4,
    slideTo: 64,
  });
  p = clearStep(p, "pulse1", 3);
  assert.equal(getStep(p, "pulse1", 3), null);
});

test("cut notes serialize", () => {
  let p = createEmptyPattern(8);
  p = setCut(p, "triangle", 2);
  assert.deepEqual(getStep(p, "triangle", 2), { cut: true });
  const restored = patternFromJSON(patternToJSON(p));
  assert.deepEqual(getStep(restored, "triangle", 2), { cut: true });
});

test("noteHoldTicks respects gate", () => {
  assert.equal(noteHoldTicks({ midi: 60 }), TICKS_PER_STEP);
  assert.equal(noteHoldTicks({ midi: 60, length: 2, gate: 3 }), TICKS_PER_STEP + 3);
  assert.equal(noteHoldTicks({ cut: true }), 0);
});

test("overdubNote replaces existing content", () => {
  let p = createEmptyPattern(8);
  p = overdubNote(p, "triangle", 0, 36);
  p = overdubNote(p, "triangle", 0, 40, { velocity: 15, gate: 2 });
  assert.equal(getStep(p, "triangle", 0).midi, 40);
  assert.equal(getStep(p, "triangle", 0).velocity, 15);
  assert.equal(getStep(p, "triangle", 0).gate, 2);
});

test("resizePattern pads and truncates", () => {
  let p = createEmptyPattern(8);
  p = overdubNote(p, "pulse2", 7, 55);
  p = resizePattern(p, 16);
  assert.equal(p.length, 16);
  assert.equal(getStep(p, "pulse2", 7).midi, 55);
  assert.equal(getStep(p, "pulse2", 15), null);
  p = resizePattern(p, 4);
  assert.equal(p.length, 4);
});

test("JSON serialization preserves notes", () => {
  let p = createEmptyPattern(16);
  p = overdubNote(p, "noise", 4, 72, { velocity: 9 });
  const json = patternToJSON(p);
  const restored = patternFromJSON(json);
  assert.deepEqual(getStep(restored, "noise", 4), getStep(p, "noise", 4));
  assert.equal(countNotes(restored), 1);
});

test("clonePattern is deep", () => {
  let p = createEmptyPattern(8);
  p = overdubNote(p, "pulse1", 1, 60);
  const c = clonePattern(p);
  c.tracks.pulse1[1].midi = 1;
  assert.equal(getStep(p, "pulse1", 1).midi, 60);
});

test("unknown channel throws", () => {
  const p = createEmptyPattern(8);
  assert.throws(() => setStep(p, "dmc", 0, { midi: 1 }));
});
