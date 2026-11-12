import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { runInNewContext } from "node:vm";

import { makeRom } from "./rom-fixture.js";

const bundle = readFileSync(new URL("../vendor/jsnes.min.js", import.meta.url), "utf8");

// Runs the bundle the way a classic <script> tag does: no module or exports
// in scope, so it attaches itself to globalThis.
function loadJsnes() {
  const context = {};
  context.globalThis = context;
  runInNewContext(bundle, context);
  return context.jsnes;
}

test("the vendored bundle defines window.jsnes.NES", () => {
  const jsnes = loadJsnes();
  assert.equal(typeof jsnes?.NES, "function");
});

test("the vendored bundle runs a ROM and makes a sample rate's worth of audio", () => {
  const { NES } = loadJsnes();
  const sampleRate = 48000;
  let frames = 0;
  let samples = 0;
  let size = 0;
  const nes = new NES({
    sampleRate,
    onFrame: (buf) => {
      frames++;
      size = buf.length;
    },
    onAudioSample: () => samples++,
  });
  nes.loadROM(makeRom());
  for (let i = 0; i < 60; i++) nes.frame();
  assert.equal(frames, 60);
  assert.equal(size, 256 * 240);
  const perSecond = (samples / 60) * 60.0988;
  assert.ok(Math.abs(perSecond - sampleRate) < sampleRate * 0.01, `${perSecond} samples per second`);
});
