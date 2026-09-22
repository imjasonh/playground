import test from "node:test";
import assert from "node:assert/strict";
import { bearingDeg, haversineNm, headingErrorDeg, offsetNm, wrap180, wrap360 } from "../src/geo.js";

test("wrap helpers", () => {
  assert.equal(wrap360(-10), 350);
  assert.equal(wrap180(190), -170);
  assert.equal(headingErrorDeg(10, 350), -20);
  assert.equal(headingErrorDeg(350, 10), 20);
});

test("offset and haversine agree on a short east leg", () => {
  const origin = { lat: 37.55, lon: -122.65 };
  const east = offsetNm(origin, 90, 2);
  assert.ok(haversineNm(origin, east) > 1.95 && haversineNm(origin, east) < 2.05);
  const brg = bearingDeg(origin, east);
  assert.ok(Math.abs(headingErrorDeg(90, brg)) < 2);
});
