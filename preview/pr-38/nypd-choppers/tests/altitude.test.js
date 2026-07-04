import test from "node:test";
import assert from "node:assert/strict";

import {
  altitudeColor,
  altitudeColorForFraction,
  altitudeFraction,
  altitudeLegendStops,
  altitudeRange,
  clamp01,
} from "../src/altitude.js";

test("clamp01 keeps values within [0, 1] and rejects junk", () => {
  assert.equal(clamp01(0.5), 0.5);
  assert.equal(clamp01(-2), 0);
  assert.equal(clamp01(4), 1);
  assert.equal(clamp01(NaN), 0);
});

test("altitudeRange finds min/max over airborne samples with altitude", () => {
  const samples = [
    { alt: 1200 },
    { alt: 900 },
    { alt: null },
    { alt: 1500 },
    { alt: undefined },
    {},
  ];
  assert.deepEqual(altitudeRange(samples), { min: 900, max: 1500 });
});

test("altitudeRange returns null when no sample has an altitude", () => {
  assert.equal(altitudeRange([{ alt: null }, {}, { alt: "x" }]), null);
  assert.equal(altitudeRange([]), null);
  assert.equal(altitudeRange(null), null);
});

test("altitudeFraction maps an altitude into [0, 1] across the range", () => {
  assert.equal(altitudeFraction(1000, 1000, 2000), 0);
  assert.equal(altitudeFraction(1500, 1000, 2000), 0.5);
  assert.equal(altitudeFraction(2000, 1000, 2000), 1);
  // Out-of-range values clamp.
  assert.equal(altitudeFraction(500, 1000, 2000), 0);
  assert.equal(altitudeFraction(3000, 1000, 2000), 1);
});

test("altitudeFraction defaults to the mid-point for degenerate input", () => {
  assert.equal(altitudeFraction(1000, 1000, 1000), 0.5); // flat range
  assert.equal(altitudeFraction(null, 0, 1000), 0.5); // missing altitude
});

test("altitudeColorForFraction runs blue (low) to red (high)", () => {
  assert.equal(altitudeColorForFraction(0), "hsl(240, 80%, 52%)");
  assert.equal(altitudeColorForFraction(1), "hsl(0, 80%, 52%)");
  assert.equal(altitudeColorForFraction(0.5), "hsl(120, 80%, 52%)");
  // Fractions are clamped before mapping.
  assert.equal(altitudeColorForFraction(-1), "hsl(240, 80%, 52%)");
  assert.equal(altitudeColorForFraction(2), "hsl(0, 80%, 52%)");
});

test("altitudeColor composes range normalisation with the colour ramp", () => {
  assert.equal(altitudeColor(1000, 1000, 2000), "hsl(240, 80%, 52%)");
  assert.equal(altitudeColor(2000, 1000, 2000), "hsl(0, 80%, 52%)");
});

test("altitudeLegendStops returns evenly spaced, coloured stops", () => {
  const stops = altitudeLegendStops(1000, 2000, 5);
  assert.equal(stops.length, 5);
  assert.deepEqual(
    stops.map((s) => s.alt),
    [1000, 1250, 1500, 1750, 2000],
  );
  assert.equal(stops[0].color, "hsl(240, 80%, 52%)");
  assert.equal(stops[4].color, "hsl(0, 80%, 52%)");
  // Invalid input yields no stops.
  assert.deepEqual(altitudeLegendStops(NaN, 2000), []);
  assert.deepEqual(altitudeLegendStops(1000, 2000, 1), []);
});
