import test from "node:test";
import assert from "node:assert/strict";

import {
  createDefaultInstruments,
  instrumentFromJSON,
  macroValue,
  releaseVoice,
  startVoice,
  tickVoice,
} from "../src/instruments/macros.js";

test("default instruments cover all channels", () => {
  const list = createDefaultInstruments();
  assert.ok(list.length >= 4);
  assert.ok(list.some((i) => i.channel === "pulse1"));
  assert.ok(list.some((i) => i.channel === "triangle"));
  assert.ok(list.some((i) => i.channel === "noise"));
});

test("macroValue holds last element past end", () => {
  assert.equal(macroValue([1, 2, 3], 0, 9), 1);
  assert.equal(macroValue([1, 2, 3], 10, 9), 3);
  assert.equal(macroValue([], 0, 9), 9);
});

test("arp macro walks chord tones", () => {
  const inst = createDefaultInstruments().find((i) => i.id === "pulse-arp");
  const voice = startVoice(inst, 60);
  const midis = [];
  for (let i = 0; i < 12; i += 1) {
    midis.push(tickVoice(voice).midi);
  }
  assert.ok(midis.includes(60));
  assert.ok(midis.includes(64));
  assert.ok(midis.includes(67));
});

test("volume macro decay can end a drum voice", () => {
  const hat = createDefaultInstruments().find((i) => i.id === "noise-hat");
  const voice = startVoice(hat, 72);
  let last = null;
  for (let i = 0; i < 20; i += 1) {
    last = tickVoice(voice);
  }
  assert.equal(last.active, false);
  assert.equal(last.volume, 0);
});

test("releaseVoice fades then deactivates", () => {
  const inst = createDefaultInstruments()[0];
  const voice = startVoice({ ...inst, volumeMacro: [] }, 60);
  tickVoice(voice);
  releaseVoice(voice, 3);
  const a = tickVoice(voice);
  assert.equal(a.active, true);
  tickVoice(voice);
  const c = tickVoice(voice);
  assert.equal(c.active, false);
});

test("instrumentFromJSON clamps and fills defaults", () => {
  const inst = instrumentFromJSON({
    channel: "pulse2",
    duty: 99,
    volume: -3,
    arpMacro: [0, 100],
    pitchMacro: [0, 99],
    macroSpeed: 0,
    vibratoDepth: 99,
    delay: 100,
  });
  assert.equal(inst.channel, "pulse2");
  assert.equal(inst.duty, 3);
  assert.equal(inst.volume, 0);
  assert.equal(inst.arpMacro[1], 24);
  assert.equal(inst.pitchMacro[1], 64);
  assert.equal(inst.macroSpeed, 1);
  assert.equal(inst.vibratoDepth, 16);
  assert.equal(inst.delay, 48);
});

test("pitch macro accumulates period offset", () => {
  const inst = createDefaultInstruments().find((i) => i.id === "pulse-bend");
  const voice = startVoice(inst, 60);
  const offsets = [];
  for (let i = 0; i < 8; i += 1) {
    offsets.push(tickVoice(voice).periodOffset);
  }
  assert.ok(offsets[offsets.length - 1] > offsets[0]);
});

test("vibrato modulates period offset", () => {
  const inst = createDefaultInstruments().find((i) => i.id === "pulse-vib");
  const voice = startVoice(inst, 60);
  const offsets = new Set();
  for (let i = 0; i < 16; i += 1) {
    offsets.add(tickVoice(voice).periodOffset);
  }
  assert.ok(offsets.size > 1);
});

test("delay keeps note silent then opens", () => {
  const base = createDefaultInstruments()[0];
  const voice = startVoice({ ...base, delay: 2, volumeMacro: [] }, 60);
  const a = tickVoice(voice);
  const b = tickVoice(voice);
  const c = tickVoice(voice);
  assert.equal(a.volume, 0);
  assert.equal(b.volume, 0);
  assert.ok(c.volume > 0);
});

test("slide interpolates midi toward target", () => {
  const inst = createDefaultInstruments()[0];
  const voice = startVoice(
    { ...inst, volumeMacro: [], arpMacro: [] },
    60,
    { slideTo: 72, slideTicks: 4 },
  );
  const midis = [];
  for (let i = 0; i < 5; i += 1) midis.push(tickVoice(voice).midi);
  assert.equal(midis[0], 60);
  assert.ok(midis[midis.length - 1] >= 70);
});
