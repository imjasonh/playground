import test from "node:test";
import assert from "node:assert/strict";

import {
  BPM,
  TICKS_PER_BEAT,
  formatTime,
  getSection,
  pitchToMidi,
  sections,
} from "../music-data.js";

test("walkthrough exposes the four narrative passages", () => {
  assert.deepEqual(
    sections.map(({ id }) => id),
    ["intro", "ostinato", "lead", "turnaround"],
  );
  assert.equal(BPM, 180);
  assert.equal(TICKS_PER_BEAT, 4);
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

test("pitch parser handles flats, sharps, rests and reference pitch", () => {
  assert.equal(pitchToMidi("A4"), 69);
  assert.equal(pitchToMidi("Bb3"), 58);
  assert.equal(pitchToMidi("F#4"), 66);
  assert.equal(pitchToMidi(null), null);
  assert.equal(pitchToMidi("noise"), null);
});

test("section lookup and display helpers have safe fallbacks", () => {
  assert.equal(getSection("lead").id, "lead");
  assert.equal(getSection("missing").id, "intro");
  assert.equal(formatTime(42.7), "0:42");
});
