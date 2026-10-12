import test from "node:test";
import assert from "node:assert/strict";

import { parseTrace, traceFullPath, traceShard } from "../src/trace.js";

const BASE = 1_700_000_000;

function trace(entries, extra = {}) {
  return { icao: "acb1f5", r: "N917PD", t: "B429", timestamp: BASE, trace: entries, ...extra };
}

test("parseTrace expands offsets to absolute timestamps and maps fields", () => {
  const samples = parseTrace(
    trace([
      [0, 40.7, -74.0, 1200, 90, 180, 0, 64, null, "adsb_icao", 1320],
      [30, 40.71, -74.01, 1300, 95, 182, 0, 64],
    ]),
  );
  assert.equal(samples.length, 2);
  assert.deepEqual(
    { ...samples[0] },
    { hex: "ACB1F5", r: "N917PD", flight: null, t: BASE, lat: 40.7, lon: -74.0, alt: 1200, gs: 90, track: 180, ground: false, leg: false },
  );
  assert.equal(samples[1].t, BASE + 30);
});

test("parseTrace flags ground state and the new-leg (takeoff/landing) bit", () => {
  const samples = parseTrace(
    trace([
      [0, 40.6, -73.9, "ground", 0, 90, 0, 0],
      [60, 40.61, -73.9, 500, 60, 90, 2, 500], // flags bit 2 => new leg
    ]),
  );
  assert.equal(samples[0].ground, true);
  assert.equal(samples[0].alt, null);
  assert.equal(samples[1].leg, true);
  assert.equal(samples[0].leg, false);
});

test("parseTrace skips entries without a position and tolerates junk", () => {
  const samples = parseTrace(
    trace([
      [0, null, null, 1000, 90, 180, 0],
      [10, 40.7, -74.0, 1000, 90, 180, 0],
      "nonsense",
    ]),
  );
  assert.equal(samples.length, 1);
  assert.equal(parseTrace(null).length, 0);
  assert.equal(parseTrace({ timestamp: "bad", trace: [] }).length, 0);
});

test("parseTrace falls back to registration from the per-point details object", () => {
  const samples = parseTrace({
    icao: "abcdef",
    timestamp: BASE,
    trace: [[0, 40, -74, 1000, 90, 180, 0, 0, { r: "N999ZZ", flight: "TEST1 " }]],
  });
  assert.equal(samples[0].r, "N999ZZ");
  assert.equal(samples[0].flight, "TEST1");
});

test("trace path helpers use the last two hex characters, lowercased", () => {
  assert.equal(traceShard("ACB1F5"), "f5");
  assert.equal(traceFullPath("ACB1F5"), "data/traces/f5/trace_full_acb1f5.json");
});
