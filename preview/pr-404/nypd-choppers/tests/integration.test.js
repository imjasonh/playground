import test from "node:test";
import assert from "node:assert/strict";

import { buildSnapshot, mergeDay } from "../src/scrape-lib.js";
import { FLEET, FLEET_BY_HEX } from "../src/fleet.js";
import { analyzeDay, kmToMiles } from "../src/analysis.js";

// A realistic adsb.lol / ADSBExchange-compatible /v2/hex response. Field names
// and shapes (trailing-padded `flight`, string "ground" alt, `seen_pos`) mirror
// what the live scraper actually receives.
function response(nowMs, aircraft) {
  return { ac: aircraft, total: aircraft.length, now: nowMs, ctime: nowMs, ptime: 1 };
}

const HOUR = 3600_000;

test("real-shape adsb.lol responses flow through to sensible daily estimates", () => {
  const start = Date.parse("2026-07-04T14:00:00Z"); // 10:00 America/New_York

  // Six hourly snapshots. N917PD airborne for four of them along a track;
  // N922PD airborne for two; N919PD parked on the ramp the whole time.
  const snapshots = [
    response(start + 0 * HOUR, [
      { hex: "acb1f5", r: "N917PD", flight: "PD1     ", t: "B429", lat: 40.706, lon: -74.01, alt_baro: 1200, gs: 85.3, track: 180.2, seen_pos: 1.2 },
      { hex: "acb963", r: "N919PD", flight: "", t: "B429", lat: 40.5905, lon: -73.884, alt_baro: "ground", gs: 0, track: 0, seen_pos: 3.0 },
    ]),
    response(start + 1 * HOUR, [
      { hex: "acb1f5", r: "N917PD", flight: "PD1     ", lat: 40.758, lon: -73.985, alt_baro: 1500, gs: 95.1, track: 20.0, seen_pos: 0.8 },
      { hex: "acb963", r: "N919PD", lat: 40.5905, lon: -73.884, alt_baro: "ground", gs: 0, seen_pos: 2.0 },
    ]),
    response(start + 2 * HOUR, [
      { hex: "acb1f5", r: "N917PD", lat: 40.82, lon: -73.93, alt_baro: 1400, gs: 90.0, track: 300, seen_pos: 5.5 },
    ]),
    response(start + 3 * HOUR, [
      { hex: "acb1f5", r: "N917PD", lat: 40.78, lon: -73.96, alt_baro: 1300, gs: 80.0, track: 210, seen_pos: 2.1 },
    ]),
    response(start + 6 * HOUR, [
      { hex: "acc6e1", r: "N922PD", t: "B412", lat: 40.689, lon: -74.045, alt_baro: 900, gs: 80.0, track: 120, seen_pos: 4.0 },
    ]),
    response(start + 7 * HOUR, [
      { hex: "acc6e1", r: "N922PD", lat: 40.65, lon: -73.98, alt_baro: 1100, gs: 90.0, track: 90, seen_pos: 1.0 },
    ]),
  ];

  // Accumulate exactly as the hourly scraper would.
  let day = null;
  for (const body of snapshots) {
    const snap = buildSnapshot(body);
    ({ day } = mergeDay(day, snap.samples, "2026-07-04"));
  }

  // The grounded N919PD samples are stored but must not inflate flight time.
  assert.equal(day.samples.length, 8);

  const { perAircraft, totals } = analyzeDay(
    day.samples,
    { fleet: FLEET, fleetByHex: FLEET_BY_HEX },
    { pricePerGallon: 6.5 },
  );

  const tails = perAircraft.map((a) => a.tail).sort();
  assert.deepEqual(tails, ["N917PD", "N922PD"], "only airborne aircraft counted");
  assert.equal(totals.activeAircraft, 2);

  // Timestamps are back-dated by each record's `seen_pos`, so spans land a few
  // seconds under the round hour; assert approximately.
  const near = (actual, expected, tol = 60) =>
    assert.ok(Math.abs(actual - expected) <= tol, `${actual} ~= ${expected}`);

  const pd917 = perAircraft.find((a) => a.tail === "N917PD");
  // Span ~3h + 1h interval = ~4h estimated, one flight, Bell 429 @ 50 gph.
  assert.equal(pd917.flightCount, 1);
  near(pd917.estimatedSeconds, 4 * 3600);
  near(pd917.estimatedGallons, 200, 1);
  assert.ok(pd917.distanceKm > 0);

  const pd922 = perAircraft.find((a) => a.tail === "N922PD");
  // Span ~1h + 1h interval = ~2h, Bell 412 @ 100 gph.
  near(pd922.estimatedGallons, 200, 1);

  // Totals are finite, positive, and cost = gallons * price.
  assert.ok(totals.estimatedHours > 0);
  assert.ok(kmToMiles(totals.distanceKm) > 0);
  assert.ok(Math.abs(totals.estimatedCost - totals.estimatedGallons * 6.5) < 1e-6);
});
