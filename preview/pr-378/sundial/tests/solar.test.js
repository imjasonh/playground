import test from "node:test";
import assert from "node:assert/strict";

import {
  DEFAULT_LATITUDE,
  castLayers,
  gnomonShadow,
  isNight,
  julianDate,
  longitudeFromTimezoneOffset,
  parseLocation,
  parsePinnedTime,
  sceneFromSun,
  shadowStrength,
  sunPosition,
  wrapDegrees,
} from "../src/solar.js";

const NYC = { latitude: 40.7128, longitude: -74.006 };

test("julianDate matches J2000 at 2000-01-01 12:00 UTC", () => {
  const jd = julianDate(new Date("2000-01-01T12:00:00Z"));
  assert.ok(Math.abs(jd - 2451545) < 1e-8);
});

test("longitudeFromTimezoneOffset maps offset to degrees east", () => {
  assert.equal(longitudeFromTimezoneOffset(300), -75);
  assert.equal(longitudeFromTimezoneOffset(0), 0);
  assert.equal(longitudeFromTimezoneOffset(-540), 135);
});

test("parseLocation reads lat and lon, and falls back to the timezone", () => {
  const date = new Date("2026-06-21T16:00:00Z");
  const fallback = parseLocation("", date);
  assert.equal(fallback.latitude, DEFAULT_LATITUDE);
  assert.equal(
    fallback.longitude,
    longitudeFromTimezoneOffset(date.getTimezoneOffset()),
  );

  const pinned = parseLocation("lat=-33.87&lon=151.21", date);
  assert.equal(pinned.latitude, -33.87);
  assert.equal(pinned.longitude, 151.21);
});

test("parsePinnedTime accepts an ISO instant and rejects junk", () => {
  const pinned = parsePinnedTime("at=2026-06-21T16:56:00Z");
  assert.equal(pinned.toISOString(), "2026-06-21T16:56:00.000Z");
  assert.equal(parsePinnedTime(""), null);
  assert.equal(parsePinnedTime("at=not-a-date"), null);
});

test("solar noon in New York in June is high and nearly south", () => {
  const sun = sunPosition(
    new Date("2026-06-21T16:56:00Z"),
    NYC.latitude,
    NYC.longitude,
  );
  assert.ok(sun.altitude > 70);
  assert.ok(sun.azimuth > 160 && sun.azimuth < 200);
  assert.equal(isNight(sun.altitude), false);
});

test("a New York morning sun sits in the east, so the shadow points west", () => {
  const sun = sunPosition(
    new Date("2026-06-21T13:00:00Z"),
    NYC.latitude,
    NYC.longitude,
  );
  assert.ok(sun.altitude > 0);
  assert.ok(sun.azimuth > 60 && sun.azimuth < 130);
  const shadow = gnomonShadow(sun, 200);
  assert.equal(shadow.visible, true);
  assert.ok(shadow.offsetX < 0);
});

test("a New York afternoon sun sits in the west, so the shadow points east", () => {
  const sun = sunPosition(
    new Date("2026-06-21T20:00:00Z"),
    NYC.latitude,
    NYC.longitude,
  );
  assert.ok(sun.altitude > 0);
  assert.ok(sun.azimuth > 230 && sun.azimuth < 300);
  const shadow = gnomonShadow(sun, 200);
  assert.equal(shadow.visible, true);
  assert.ok(shadow.offsetX > 0);
});

test("New York solar noon casts a shadow toward the top of the page", () => {
  const sun = sunPosition(
    new Date("2026-06-21T16:56:00Z"),
    NYC.latitude,
    NYC.longitude,
  );
  const shadow = gnomonShadow(sun, 200);
  assert.ok(shadow.offsetY < 0);
  assert.ok(Math.abs(shadow.offsetX) < Math.abs(shadow.offsetY));
});

test("night leaves no shadow", () => {
  const sun = sunPosition(
    new Date("2026-01-15T08:00:00Z"),
    NYC.latitude,
    NYC.longitude,
  );
  assert.ok(sun.altitude < 0);
  assert.equal(isNight(sun.altitude), true);
  assert.equal(shadowStrength(sun.altitude), 0);

  const shadow = gnomonShadow(sun, 200);
  assert.equal(shadow.visible, false);
  assert.equal(shadow.strength, 0);
  assert.equal(shadow.length, 0);
  assert.deepEqual(castLayers(shadow, { r: 0, g: 0, b: 0, a: 0.4 }), []);
  assert.equal(sceneFromSun(sun).night, true);
});

test("daytime casts are a soft umbra and a longer penumbra", () => {
  const shadow = gnomonShadow(
    { altitude: 40, azimuth: 180, declination: 20, hourAngle: 0 },
    200,
  );
  const layers = castLayers(shadow, { r: 40, g: 38, b: 36, a: 0.42 });
  assert.equal(layers.length, 2);
  assert.ok(layers[0].blur > 0);
  assert.ok(layers[1].blur > layers[0].blur);
  assert.ok(Math.abs(layers[1].x) >= Math.abs(layers[0].x));
  assert.ok(Math.abs(layers[1].y) >= Math.abs(layers[0].y));
  assert.ok(layers[0].opacity > layers[1].opacity);
});

test("equinox sunrise at the equator is nearly due east", () => {
  const sun = sunPosition(new Date("2026-03-20T06:05:00Z"), 0, 0);
  assert.ok(Math.abs(sun.altitude) < 3);
  assert.ok(sun.azimuth > 80 && sun.azimuth < 100);
});

test("Sydney in December noon puts the sun in the north, shadow south", () => {
  const sun = sunPosition(new Date("2026-12-21T02:00:00Z"), -33.87, 151.21);
  assert.ok(sun.altitude > 50);
  assert.ok(sun.azimuth < 40 || sun.azimuth > 320);
  const shadow = gnomonShadow(sun, 200);
  assert.ok(shadow.offsetY > 0);
});

test("shadow azimuth is opposite the sun", () => {
  const sun = {
    altitude: 40,
    azimuth: 90,
    declination: 0,
    hourAngle: -45,
  };
  const shadow = gnomonShadow(sun, 100);
  assert.ok(Math.abs(wrapDegrees(shadow.azimuth - 270)) < 1e-9);
});

test("scene keeps night paper dark and day paper light", () => {
  const night = sceneFromSun({
    altitude: -20,
    azimuth: 10,
    declination: -20,
    hourAngle: 160,
  });
  const day = sceneFromSun({
    altitude: 45,
    azimuth: 180,
    declination: 20,
    hourAngle: 0,
  });
  assert.ok(night.paper.r + night.paper.g + night.paper.b < 80);
  assert.ok(day.paper.r + day.paper.g + day.paper.b > 600);
  assert.equal(night.colorScheme, "dark");
  assert.equal(day.colorScheme, "light");
});
