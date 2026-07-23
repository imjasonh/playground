import test from "node:test";
import assert from "node:assert/strict";
import {
  bearingLabel,
  destination,
  feetToMeters,
  formatPeople,
  metersPerDegree,
  milesToMeters,
} from "../src/geo.js";

test("feetToMeters converts 100 feet", () => {
  assert.ok(Math.abs(feetToMeters(100) - 30.48) < 1e-9);
});

test("destination due east from equator advances longitude", () => {
  const p = destination(0, 0, 90, 111_320);
  assert.ok(Math.abs(p.lat) < 0.05);
  assert.ok(p.lon > 0.9 && p.lon < 1.1);
});

test("metersPerDegree shrinks longitude meters near poles", () => {
  const eq = metersPerDegree(0);
  const high = metersPerDegree(60);
  assert.ok(eq.lon > high.lon);
  assert.ok(eq.lat > 110_000 && eq.lat < 112_000);
});

test("milesToMeters is exact for statute miles", () => {
  assert.equal(milesToMeters(1), 1609.344);
});

test("formatPeople uses compact suffixes", () => {
  assert.equal(formatPeople(1_250_000), "1.25M");
  assert.equal(formatPeople(12_400), "12.4k");
});

test("bearingLabel maps compass octants", () => {
  assert.equal(bearingLabel(0), "N");
  assert.equal(bearingLabel(135), "SE");
  assert.equal(bearingLabel(270), "W");
});
