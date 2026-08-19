import test from "node:test";
import assert from "node:assert/strict";

import {
  BPM,
  TICKS_PER_BEAT,
  formatTime,
  getSection,
  midiToPitch,
  pitchToMidi,
  sections,
} from "../music-data.js";
import {
  exactTrackChannels,
  LOOP_START_TICK,
  TRACK_LENGTH_TICKS,
} from "../exact-track-data.js";

test("walkthrough exposes the full form and four complete sections", () => {
  assert.deepEqual(
    sections.map(({ id }) => id),
    ["full", "intro", "ostinato", "lead", "turnaround"],
  );
  assert.equal(BPM, 180);
  assert.equal(TICKS_PER_BEAT, 4);
  assert.equal(sections[0].durationTicks, 512);
  assert.equal(sections[0].loopStartTick, 128);
  assert.ok(sections.slice(1).every((section) => section.durationTicks === 128));
});

test("every playable event fits within its passage", () => {
  for (const section of sections) {
    assert.ok(section.durationTicks > 0);
    assert.ok(section.code.length > 0);
    assert.equal(section.channels.length, 4);

    for (const channel of section.channels) {
      for (const event of channel.events) {
        assert.ok(event.start >= 0, `${section.id}/${channel.id} starts before zero`);
        assert.ok(event.duration > 0, `${section.id}/${channel.id} has an empty event`);
        assert.ok(
          event.start + event.duration <= section.durationTicks,
          `${section.id}/${channel.id} exceeds the passage`,
        );
      }
    }
  }
});

test("exact channel streams cover all 32 bars without truncation", () => {
  assert.equal(TRACK_LENGTH_TICKS, 512);
  assert.equal(LOOP_START_TICK, 128);
  assert.deepEqual(
    exactTrackChannels.map((channel) => channel.events.length),
    [177, 254, 256, 257],
  );

  for (const channel of exactTrackChannels) {
    let cursor = 0;
    for (const event of channel.events) {
      assert.equal(event.start, cursor, `${channel.id} has a gap or overlap at ${cursor}`);
      cursor += event.duration;
    }
    assert.equal(cursor, TRACK_LENGTH_TICKS, `${channel.id} is cut off`);
  }
});

test("pitch parser handles flats, sharps, rests and reference pitch", () => {
  assert.equal(pitchToMidi("A4"), 69);
  assert.equal(pitchToMidi("Bb3"), 58);
  assert.equal(pitchToMidi("F#4"), 66);
  assert.equal(midiToPitch(68), "Ab4");
  assert.equal(pitchToMidi(null), null);
  assert.equal(pitchToMidi("noise"), null);
});

test("only pulse streams need the timer-table octave correction", () => {
  assert.deepEqual(
    exactTrackChannels.map(({ id, transpose }) => [id, transpose]),
    [
      ["pulse1", 12],
      ["pulse2", 12],
      ["triangle", 0],
      ["noise", 0],
    ],
  );
});

test("section lookup and display helpers have safe fallbacks", () => {
  assert.equal(getSection("lead").id, "lead");
  assert.equal(getSection("missing").id, "full");
  assert.equal(formatTime(42.7), "0:42");
});
