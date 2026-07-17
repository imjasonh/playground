import test from "node:test";
import assert from "node:assert/strict";

import {
  buildPeriodTable,
  formatNoteName,
  isPulsePeriodMuted,
  midiToHz,
  midiToNoisePeriodIndex,
  midiToTimerPeriod,
  timerPeriodToMidi,
} from "../src/apu/notes.js";

test("midiToHz: A4 is 440", () => {
  assert.equal(midiToHz(69), 440);
});

test("midiToTimerPeriod: A4 lands near classic NES period", () => {
  // NTSC: CPU/(16*440) - 1 ≈ 253.3 → 253
  const period = midiToTimerPeriod(69);
  assert.ok(period >= 250 && period <= 256, `got ${period}`);
  assert.equal(isPulsePeriodMuted(period), false);
});

test("midiToTimerPeriod clamps to 11-bit range", () => {
  assert.ok(midiToTimerPeriod(0) <= 0x7ff);
  assert.ok(midiToTimerPeriod(127) >= 0);
});

test("pulse mute zone is period < 8", () => {
  assert.equal(isPulsePeriodMuted(7), true);
  assert.equal(isPulsePeriodMuted(8), false);
  // Top MIDI notes sit at the edge of the hardware range on NTSC.
  assert.ok(midiToTimerPeriod(127) <= 8);
});

test("timerPeriodToMidi round-trips near A4", () => {
  const period = midiToTimerPeriod(69);
  assert.equal(timerPeriodToMidi(period), 69);
});

test("noise period index maps high MIDI to bright noise", () => {
  assert.ok(midiToNoisePeriodIndex(84) < midiToNoisePeriodIndex(36));
  assert.equal(midiToNoisePeriodIndex(36), 15);
  assert.equal(midiToNoisePeriodIndex(84), 0);
});

test("formatNoteName", () => {
  assert.equal(formatNoteName(60), "C-4");
  assert.equal(formatNoteName(61), "C#4");
  assert.equal(formatNoteName(null), "---");
});

test("buildPeriodTable covers MIDI range", () => {
  const table = buildPeriodTable();
  assert.equal(table.length, 128);
  assert.equal(table[69], midiToTimerPeriod(69));
});
