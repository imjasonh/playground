import test from "node:test";
import assert from "node:assert/strict";

import { NesApu, enableToneChannels, startPulseNote, mixSample } from "../src/apu/nesApu.js";
import { midiToTimerPeriod } from "../src/apu/notes.js";

test("silent APU produces near-zero output", () => {
  const apu = new NesApu();
  const out = new Float32Array(256);
  apu.render(out, 44100);
  const peak = Math.max(...out.map(Math.abs));
  assert.ok(peak < 0.05, `peak ${peak}`);
});

test("pulse note produces audible energy", () => {
  const apu = new NesApu();
  enableToneChannels(apu);
  startPulseNote(apu, "pulse1", {
    duty: 2,
    volume: 12,
    period: midiToTimerPeriod(60),
  });
  const out = new Float32Array(4096);
  apu.render(out, 44100);
  const peak = Math.max(...out.map(Math.abs));
  const rms = Math.sqrt(out.reduce((s, x) => s + x * x, 0) / out.length);
  assert.ok(peak > 0.05, `peak ${peak}`);
  assert.ok(rms > 0.01, `rms ${rms}`);
});

test("register writes update pulse period and duty", () => {
  const apu = new NesApu();
  enableToneChannels(apu);
  apu.writeRegister(0x4000, 0xb0 | 10); // duty 2, halt, const, vol 10
  apu.writeRegister(0x4002, 0xfd);
  apu.writeRegister(0x4003, 0x00);
  assert.equal(apu.pulse1.timerPeriod & 0xff, 0xfd);
  assert.equal(apu.pulse1.duty, 2);
  assert.equal(apu.pulse1.volumeOrDecay, 10);
});

test("disabling channel in $4015 clears length counter", () => {
  const apu = new NesApu();
  enableToneChannels(apu);
  startPulseNote(apu, "pulse1", {
    duty: 2,
    volume: 8,
    period: 200,
  });
  assert.ok(apu.pulse1.lengthCounter > 0);
  apu.writeRegister(0x4015, 0x0e); // disable pulse1
  assert.equal(apu.pulse1.lengthCounter, 0);
});

test("noise LFSR advances and can produce output", () => {
  const apu = new NesApu();
  enableToneChannels(apu);
  apu.writeRegister(0x400c, 0x3f);
  apu.writeRegister(0x400e, 0x00); // shortest period
  apu.writeRegister(0x400f, 0x08);
  const out = new Float32Array(8000);
  apu.render(out, 44100);
  const peak = Math.max(...out.map(Math.abs));
  assert.ok(peak > 0.02, `peak ${peak}`);
});

test("triangle note produces output", () => {
  const apu = new NesApu();
  enableToneChannels(apu);
  apu.writeRegister(0x4008, 0xff);
  const period = midiToTimerPeriod(36);
  apu.writeRegister(0x400a, period & 0xff);
  apu.writeRegister(0x400b, 0x08 | ((period >> 8) & 7));
  const out = new Float32Array(4096);
  apu.render(out, 44100);
  const peak = Math.max(...out.map(Math.abs));
  assert.ok(peak > 0.02, `peak ${peak}`);
});

test("mixSample is quiet when all channels silent", () => {
  const apu = new NesApu();
  const s = mixSample(apu.pulse1, apu.pulse2, apu.triangle, apu.noise);
  assert.ok(Math.abs(s) < 0.3);
});

test("readStatus reflects length counters", () => {
  const apu = new NesApu();
  enableToneChannels(apu);
  startPulseNote(apu, "pulse2", { duty: 1, volume: 8, period: 180 });
  assert.equal(apu.readStatus() & 0x02, 0x02);
});
