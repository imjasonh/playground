import test from "node:test";
import assert from "node:assert/strict";

import { encodeWav, renderSongToSamples } from "../src/export/wav.js";
import { createDemoSong } from "../src/song.js";

test("encodeWav writes valid RIFF header", () => {
  const samples = new Float32Array([0, 0.5, -0.5, 1, -1]);
  const buf = encodeWav(samples, 44100);
  const view = new DataView(buf);
  const tag = (o) =>
    String.fromCharCode(
      view.getUint8(o),
      view.getUint8(o + 1),
      view.getUint8(o + 2),
      view.getUint8(o + 3),
    );
  assert.equal(tag(0), "RIFF");
  assert.equal(tag(8), "WAVE");
  assert.equal(tag(12), "fmt ");
  assert.equal(tag(36), "data");
  assert.equal(view.getUint16(20, true), 1); // PCM
  assert.equal(view.getUint16(22, true), 1); // mono
  assert.equal(view.getUint32(24, true), 44100);
  assert.equal(buf.byteLength, 44 + samples.length * 2);
});

test("renderSongToSamples of demo is audible and finite", () => {
  const song = createDemoSong();
  const samples = renderSongToSamples(song, {
    sampleRate: 22050,
    loops: 1,
    tailSeconds: 0,
  });
  assert.ok(samples.length > 1000);
  let peak = 0;
  let bad = 0;
  for (const s of samples) {
    if (!Number.isFinite(s)) bad += 1;
    peak = Math.max(peak, Math.abs(s));
  }
  assert.equal(bad, 0);
  assert.ok(peak > 0.05, `peak ${peak}`);
});
