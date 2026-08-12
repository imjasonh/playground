import test from "node:test";
import assert from "node:assert/strict";

import {
  configureAudioSession,
  createAudioContext,
  frequencyForPitch,
  playbackTickForElapsed,
  unlockAudioContext,
} from "../audio-engine.js";

test("creates Web Audio through the iOS-prefixed fallback", () => {
  class PrefixedAudioContext {}
  const context = createAudioContext({ webkitAudioContext: PrefixedAudioContext });
  assert.ok(context instanceof PrefixedAudioContext);
});

test("configures a mobile browser audio session for playback", () => {
  const navigatorObject = { audioSession: { type: "auto" } };
  configureAudioSession(navigatorObject);
  assert.equal(navigatorObject.audioSession.type, "playback");
});

test("starts an unlock source synchronously before awaiting resume", async () => {
  const calls = [];
  const context = {
    state: "suspended",
    sampleRate: 48_000,
    destination: {},
    createBuffer: () => ({}),
    createBufferSource: () => ({
      connect: () => calls.push("connect"),
      start: () => calls.push("start"),
    }),
    resume: async () => {
      calls.push("resume");
      context.state = "running";
    },
  };

  await unlockAudioContext(context);
  assert.deepEqual(calls, ["connect", "start", "resume"]);
});

test("reports when a browser refuses to activate audio", async () => {
  const context = {
    state: "suspended",
    sampleRate: 48_000,
    destination: {},
    createBuffer: () => ({}),
    createBufferSource: () => ({ connect() {}, start() {} }),
    resume: async () => {},
  };

  await assert.rejects(unlockAudioContext(context), /Audio output is suspended/);
});

test("maps the encoded infinite loop back to measure 9", () => {
  const tickSeconds = 60 / 180 / 4;
  assert.equal(playbackTickForElapsed(511 * tickSeconds, 512, 128), 511);
  assert.equal(playbackTickForElapsed(512 * tickSeconds, 512, 128), 128);
  assert.equal(playbackTickForElapsed(896 * tickSeconds, 512, 128), 128);
  assert.equal(playbackTickForElapsed(900 * tickSeconds, 512, 128), 132);
});

test("matches the opening notes to their NTSC APU timer frequencies", () => {
  const ntscCpuHz = 1_789_773;
  const timerFrequency = (timer, divider) =>
    ntscCpuHz / (divider * (timer + 1));

  // Opening Pulse 1: the disassembly calls timer $023B “G2,” but the
  // pulse divider makes it sound at 195.6 Hz, concert G3.
  assert.ok(
    Math.abs(frequencyForPitch("G2", 12) - timerFrequency(0x023b, 16)) < 0.5,
  );
  // Opening Pulse 2 and triangle both sound D#3. The triangle stream starts
  // from the next table octave because its hardware divider is twice as large.
  assert.ok(
    Math.abs(frequencyForPitch("D#2", 12) - timerFrequency(0x02cf, 16)) < 0.5,
  );
  assert.ok(
    Math.abs(frequencyForPitch("D#3") - timerFrequency(0x0167, 32)) < 0.5,
  );
});
