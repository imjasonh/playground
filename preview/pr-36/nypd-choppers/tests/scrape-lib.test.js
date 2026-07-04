import test from "node:test";
import assert from "node:assert/strict";

import {
  buildSnapshot,
  localDateString,
  mergeDay,
  normalizeAircraft,
  updateIndex,
} from "../src/scrape-lib.js";

test("normalizeAircraft maps adsb.lol fields to a compact sample", () => {
  const s = normalizeAircraft(
    { hex: "acb1f5", r: "N917PD", flight: "PD1 ", lat: 40.7, lon: -74, alt_baro: 1200, gs: 95, track: 180, seen_pos: 10 },
    1_700_000_000,
  );
  assert.deepEqual(s, {
    hex: "ACB1F5",
    r: "N917PD",
    flight: "PD1",
    t: 1_699_999_990,
    lat: 40.7,
    lon: -74,
    alt: 1200,
    gs: 95,
    track: 180,
    ground: false,
  });
});

test("normalizeAircraft flags ground state and drops positionless records", () => {
  const g = normalizeAircraft({ hex: "abc", lat: 40, lon: -74, alt_baro: "ground" }, 1000);
  assert.equal(g.ground, true);
  assert.equal(g.alt, null);
  assert.equal(normalizeAircraft({ hex: "abc" }, 1000), null);
  assert.equal(normalizeAircraft(null, 1000), null);
});

test("buildSnapshot uses the API's clock and filters aircraft", () => {
  const snap = buildSnapshot({
    now: 1_700_000_000_000,
    ac: [
      { hex: "a", lat: 40, lon: -74, alt_baro: 900, seen_pos: 0 },
      { hex: "b" }, // no position -> dropped
    ],
  });
  assert.equal(snap.t, 1_700_000_000);
  assert.equal(snap.samples.length, 1);
});

test("localDateString formats US Eastern civil date", () => {
  // 2026-01-01T02:00:00Z is still 2025-12-31 in New York.
  assert.equal(localDateString(Date.parse("2026-01-01T02:00:00Z")), "2025-12-31");
  assert.equal(localDateString(Date.parse("2026-07-04T18:00:00Z")), "2026-07-04");
});

test("mergeDay de-duplicates on hex+time and keeps sorted order", () => {
  const first = mergeDay(null, [
    { hex: "B", t: 20 },
    { hex: "A", t: 10 },
  ], "2026-07-04");
  assert.equal(first.added, 2);
  assert.deepEqual(first.day.samples.map((s) => s.hex), ["A", "B"]);

  const second = mergeDay(first.day, [
    { hex: "A", t: 10 }, // duplicate
    { hex: "A", t: 30 }, // new
  ], "2026-07-04");
  assert.equal(second.added, 1);
  assert.equal(second.day.samples.length, 3);
});

test("updateIndex replaces the entry for a day and sorts", () => {
  let idx = updateIndex(null, "2026-07-04", 5);
  idx = updateIndex(idx, "2026-07-03", 2);
  idx = updateIndex(idx, "2026-07-04", 7); // update, not duplicate
  assert.deepEqual(idx.days, [
    { date: "2026-07-03", samples: 2 },
    { date: "2026-07-04", samples: 7 },
  ]);
});
