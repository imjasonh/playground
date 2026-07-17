import test from "node:test";
import assert from "node:assert/strict";

import {
  addPattern,
  appendOrder,
  createDemoSong,
  createSong,
  deletePattern,
  deserializeSong,
  getEditPattern,
  orderStepCount,
  selectEditPattern,
  serializeSong,
  setEditPatternData,
  songFromJSON,
  songToJSON,
} from "../src/song.js";
import { countNotes, overdubNote } from "../src/sequencer/pattern.js";

test("createSong wires instruments and a single pattern", () => {
  const song = createSong();
  assert.equal(song.version, 2);
  assert.equal(song.instruments.pulse1.channel, "pulse1");
  assert.equal(song.patterns.length, 1);
  assert.deepEqual(song.order, [0]);
  assert.equal(getEditPattern(song).length, 16);
});

test("demo song has multiple patterns and a multi-entry order", () => {
  const demo = createDemoSong();
  assert.ok(demo.patterns.length >= 2);
  assert.ok(demo.order.length >= 2);
  assert.ok(countNotes(demo.patterns[0]) > 10);
  assert.ok(orderStepCount(demo) > demo.patterns[0].length);
});

test("serialize / deserialize round-trip preserves order", () => {
  const demo = createDemoSong();
  const restored = deserializeSong(serializeSong(demo));
  assert.equal(restored.title, demo.title);
  assert.deepEqual(restored.order, demo.order);
  assert.equal(restored.patterns.length, demo.patterns.length);
  assert.equal(
    countNotes(restored.patterns[0]),
    countNotes(demo.patterns[0]),
  );
});

test("v1 song JSON migrates to patterns/order", () => {
  const v1 = {
    version: 1,
    title: "Old",
    bpm: 100,
    pattern: {
      length: 8,
      tracks: {
        pulse1: [{ midi: 60 }, null, null, null, null, null, null, null],
        pulse2: [null, null, null, null, null, null, null, null],
        triangle: [null, null, null, null, null, null, null, null],
        noise: [null, null, null, null, null, null, null, null],
      },
    },
    instruments: {},
  };
  const song = songFromJSON(v1);
  assert.equal(song.patterns.length, 1);
  assert.deepEqual(song.order, [0]);
  assert.equal(getEditPattern(song).tracks.pulse1[0].midi, 60);
});

test("add/select/delete patterns updates order", () => {
  let song = createSong();
  song = addPattern(song, "B");
  assert.equal(song.patterns.length, 2);
  assert.equal(song.editPattern, 1);
  song = appendOrder(song, 1);
  assert.deepEqual(song.order, [0, 1]);
  song = selectEditPattern(song, 0);
  song = deletePattern(song, 1);
  assert.equal(song.patterns.length, 1);
  assert.deepEqual(song.order, [0]);
});

test("setEditPatternData writes into the selected pattern", () => {
  let song = createDemoSong();
  song = selectEditPattern(song, 1);
  const nextPat = overdubNote(getEditPattern(song), "pulse1", 3, 64);
  song = setEditPatternData(song, nextPat);
  assert.equal(song.patterns[1].tracks.pulse1[3].midi, 64);
});

test("songFromJSON tolerates empty input", () => {
  const song = songFromJSON(null);
  assert.equal(song.version, 2);
  assert.ok(song.patterns[0].length >= 4);
});

test("songToJSON includes legacy pattern field", () => {
  const song = createSong();
  const json = songToJSON(song);
  assert.ok(json.pattern);
  assert.equal(json.pattern.length, song.patterns[0].length);
});
