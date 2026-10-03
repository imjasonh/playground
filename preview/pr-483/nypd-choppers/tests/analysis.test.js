import test from "node:test";
import assert from "node:assert/strict";

import {
  DEFAULTS,
  aggregateDays,
  analyzeAircraft,
  analyzeDay,
  estimateSampleInterval,
  formatDuration,
  haversineKm,
  isAirborne,
  segmentFlights,
} from "../src/analysis.js";

const HOUR = 3600;
const T0 = 1_700_000_000; // arbitrary base epoch (seconds)

function airborneSample(hexTOverrides) {
  return { hex: "ACB1F5", lat: 40.7, lon: -74.0, alt: 1000, gs: 90, ground: false, ...hexTOverrides };
}

test("isAirborne distinguishes flying from parked/taxiing", () => {
  assert.equal(isAirborne(airborneSample({ t: T0 })), true);
  assert.equal(isAirborne(airborneSample({ t: T0, ground: true })), false);
  assert.equal(isAirborne(airborneSample({ t: T0, alt: 50 })), false);
  // No altitude but moving fast => airborne; slow => not.
  assert.equal(isAirborne({ lat: 40, lon: -74, alt: null, gs: 80 }), true);
  assert.equal(isAirborne({ lat: 40, lon: -74, alt: null, gs: 5 }), false);
  assert.equal(isAirborne({ lat: null, lon: null }), false);
});

test("haversineKm computes a sane distance", () => {
  // ~ Manhattan to JFK is roughly 20 km.
  const d = haversineKm({ lat: 40.7128, lon: -74.006 }, { lat: 40.6413, lon: -73.7781 });
  assert.ok(d > 18 && d < 24, `expected ~20km, got ${d}`);
  assert.equal(haversineKm({ lat: 40, lon: -74 }, { lat: 40, lon: -74 }), 0);
});

test("segmentFlights splits on large time gaps", () => {
  const samples = [
    airborneSample({ t: T0 }),
    airborneSample({ t: T0 + HOUR }),
    airborneSample({ t: T0 + 2 * HOUR }),
    // gap of 4h -> new flight
    airborneSample({ t: T0 + 6 * HOUR }),
  ];
  const flights = segmentFlights(samples);
  assert.equal(flights.length, 2);
  assert.equal(flights[0].sampleCount, 3);
  assert.equal(flights[1].sampleCount, 1);
});

test("segmentFlights sorts unordered input and ignores grounded samples", () => {
  const samples = [
    airborneSample({ t: T0 + HOUR }),
    airborneSample({ t: T0, ground: true }),
    airborneSample({ t: T0 }),
  ];
  const flights = segmentFlights(samples);
  assert.equal(flights.length, 1);
  assert.equal(flights[0].sampleCount, 2);
  assert.equal(flights[0].startT, T0);
});

test("segmentFlights splits on the readsb new-leg flag even without a time gap", () => {
  const samples = [
    airborneSample({ t: T0 }),
    airborneSample({ t: T0 + 60 }),
    airborneSample({ t: T0 + 300, leg: true }), // takeoff after a brief landing
    airborneSample({ t: T0 + 360 }),
  ];
  const flights = segmentFlights(samples);
  assert.equal(flights.length, 2);
  assert.equal(flights[0].sampleCount, 2);
  assert.equal(flights[1].sampleCount, 2);
});

test("estimateSampleInterval returns the clamped median observation gap", () => {
  // Dense ~30s trace data.
  const dense = [0, 30, 60, 90, 120].map((dt) => airborneSample({ t: T0 + dt }));
  assert.equal(estimateSampleInterval(dense), 30);
  // Sparse hourly data clamps to the max.
  const sparse = [0, HOUR, 2 * HOUR].map((dt) => airborneSample({ t: T0 + dt }));
  assert.equal(estimateSampleInterval(sparse), DEFAULTS.maxSampleIntervalSec);
  // No gaps -> fallback default.
  assert.equal(estimateSampleInterval([airborneSample({ t: T0 })]), DEFAULTS.sampleIntervalSec);
});

test("analyzeDay adapts credited time to dense trace data", () => {
  const fleet = [{ hex: "ACB1F5", tail: "N917PD", model: "Bell 429", fuelGph: 50, color: "#1" }];
  // 30 minutes of 30s-spaced points => ~30 min estimated, not ~1.5h.
  const samples = [];
  for (let dt = 0; dt <= 1800; dt += 30) {
    samples.push({ hex: "ACB1F5", lat: 40.7 + dt / 100000, lon: -74, alt: 1000, gs: 90, ground: false, t: T0 + dt });
  }
  const { totals } = analyzeDay(samples, { fleet });
  // span 1800s + one 30s interval = 1830s.
  assert.ok(Math.abs(totals.estimatedSeconds - 1830) <= 5, `${totals.estimatedSeconds}`);
});

test("a single-sample flight is credited about one sampling interval", () => {
  const flights = segmentFlights([airborneSample({ t: T0 })]);
  assert.equal(flights.length, 1);
  assert.equal(flights[0].spanSeconds, 0);
  assert.equal(flights[0].estimatedSeconds, DEFAULTS.sampleIntervalSec);
});

test("analyzeAircraft rolls up fuel and cost from estimated hours", () => {
  const member = { hex: "ACB1F5", tail: "N917PD", model: "Bell 429", fuelGph: 50, color: "#000" };
  const samples = [
    airborneSample({ t: T0 }),
    airborneSample({ t: T0 + HOUR }),
  ];
  const result = analyzeAircraft(member, samples, { pricePerGallon: 6 });
  // span 1h + 1h interval = 2h estimated.
  assert.equal(result.estimatedSeconds, 2 * HOUR);
  assert.equal(result.estimatedGallons, 100); // 2h * 50 gph
  assert.equal(result.estimatedCost, 600); // 100 gal * $6
  assert.equal(result.detections, 2);
});

test("analyzeDay groups the fleet, sorts, and totals", () => {
  const fleet = [
    { hex: "ACB1F5", tail: "N917PD", model: "Bell 429", fuelGph: 50, color: "#1" },
    { hex: "ACC6E1", tail: "N922PD", model: "Bell 412EPX", fuelGph: 100, color: "#2" },
    { hex: "A4C7E5", tail: "N407NY", model: "Bell 407", fuelGph: 40, color: "#3" },
  ];
  const samples = [
    { hex: "ACB1F5", lat: 40.7, lon: -74, alt: 1000, gs: 90, ground: false, t: T0 },
    { hex: "ACB1F5", lat: 40.8, lon: -74, alt: 1000, gs: 90, ground: false, t: T0 + HOUR },
    { hex: "ACC6E1", lat: 40.6, lon: -73.9, alt: 800, gs: 80, ground: false, t: T0 },
    // N407NY only ever seen on the ground -> not active.
    { hex: "A4C7E5", lat: 40.5, lon: -73.8, alt: null, gs: 0, ground: true, t: T0 },
  ];
  const { perAircraft, totals } = analyzeDay(samples, { fleet }, { pricePerGallon: 6 });
  assert.equal(perAircraft.length, 2);
  assert.equal(perAircraft[0].tail, "N917PD"); // most airborne time first
  assert.equal(totals.activeAircraft, 2);
  assert.equal(totals.flightCount, 2);
  assert.equal(totals.estimatedHours, 3); // 2h + 1h
});

test("analyzeDay includes tracked aircraft outside the known roster", () => {
  const fleet = [];
  const samples = [
    { hex: "ABCDEF", r: "N999XX", lat: 40.7, lon: -74, alt: 900, gs: 90, ground: false, t: T0 },
  ];
  const { perAircraft } = analyzeDay(samples, { fleet });
  assert.equal(perAircraft.length, 1);
  assert.equal(perAircraft[0].tail, "N999XX");
});

test("aggregateDays sums per-aircraft across days", () => {
  const fleet = [
    { hex: "ACB1F5", tail: "N917PD", model: "Bell 429", fuelGph: 50, color: "#1" },
  ];
  const mk = (t) => analyzeDay(
    [
      { hex: "ACB1F5", lat: 40.7, lon: -74, alt: 1000, gs: 90, ground: false, t },
      { hex: "ACB1F5", lat: 40.8, lon: -74, alt: 1000, gs: 90, ground: false, t: t + HOUR },
    ],
    { fleet },
    { pricePerGallon: 6 },
  );
  const agg = aggregateDays([mk(T0), mk(T0 + 86400)]);
  assert.equal(agg.totals.days, 2);
  assert.equal(agg.perAircraft.length, 1);
  assert.equal(agg.perAircraft[0].activeDays, 2);
  assert.equal(agg.perAircraft[0].estimatedSeconds, 4 * HOUR);
});

test("formatDuration renders hours and minutes", () => {
  assert.equal(formatDuration(0), "0m");
  assert.equal(formatDuration(90 * 60), "1h 30m");
  assert.equal(formatDuration(45 * 60), "45m");
});
