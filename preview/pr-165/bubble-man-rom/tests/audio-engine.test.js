import test from "node:test";
import assert from "node:assert/strict";

import {
  configureAudioSession,
  createAudioContext,
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
