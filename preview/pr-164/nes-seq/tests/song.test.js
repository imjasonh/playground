import test from "node:test";
import assert from "node:assert/strict";

import {
  createDemoSong,
  createSong,
  deserializeSong,
  serializeSong,
  songFromJSON,
  songToJSON,
} from "../src/song.js";
import { countNotes } from "../src/sequencer/pattern.js";

test("createSong wires instruments to channels", () => {
  const song = createSong();
  assert.equal(song.instruments.pulse1.channel, "pulse1");
  assert.equal(song.instruments.noise.channel, "noise");
  assert.equal(song.pattern.length, 16);
});

test("demo song has notes on multiple channels", () => {
  const demo = createDemoSong();
  assert.ok(countNotes(demo.pattern) > 10);
  assert.ok(demo.pattern.tracks.triangle.some(Boolean));
  assert.ok(demo.pattern.tracks.pulse1.some(Boolean));
  assert.ok(demo.pattern.tracks.noise.some(Boolean));
});

test("serialize / deserialize round-trip", () => {
  const demo = createDemoSong();
  const text = serializeSong(demo);
  const restored = deserializeSong(text);
  assert.equal(restored.title, demo.title);
  assert.equal(restored.bpm, demo.bpm);
  assert.equal(countNotes(restored.pattern), countNotes(demo.pattern));
  assert.deepEqual(
    songToJSON(restored).pattern,
    songToJSON(demo).pattern,
  );
});

test("songFromJSON tolerates empty input", () => {
  const song = songFromJSON(null);
  assert.equal(song.version, 1);
  assert.ok(song.pattern.length >= 4);
});
