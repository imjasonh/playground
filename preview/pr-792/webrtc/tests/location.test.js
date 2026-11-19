import test from "node:test";
import assert from "node:assert/strict";

import {
  LOCATION_KIND,
  LOCATION_STOP_KIND,
  createLocationMessage,
  createLocationStop,
  parseLocationMessage,
  isValidLat,
  isValidLon,
  formatCoords,
  formatAccuracy,
  mapsLink,
} from "../src/location.js";

const samplePosition = {
  coords: { latitude: 40.7128, longitude: -74.006, accuracy: 12, heading: 90, speed: 1.5 },
  timestamp: 1_700_000_000_000,
};

test("createLocationMessage extracts the useful fields", () => {
  const msg = createLocationMessage(samplePosition);
  assert.equal(msg.kind, LOCATION_KIND);
  assert.equal(msg.lat, 40.7128);
  assert.equal(msg.lon, -74.006);
  assert.equal(msg.accuracy, 12);
  assert.equal(msg.heading, 90);
  assert.equal(msg.speed, 1.5);
  assert.equal(msg.live, false);
  assert.equal(msg.ts, 1_700_000_000_000);
});

test("createLocationMessage marks live shares and defaults the timestamp", () => {
  const msg = createLocationMessage({ coords: { latitude: 1, longitude: 2 } }, { live: true });
  assert.equal(msg.live, true);
  assert.equal(typeof msg.ts, "number");
  assert.ok(!("accuracy" in msg));
});

test("createLocationMessage rejects positions without numeric coords", () => {
  assert.throws(() => createLocationMessage(null));
  assert.throws(() => createLocationMessage({ coords: {} }));
  assert.throws(() => createLocationMessage({ coords: { latitude: "x", longitude: 2 } }));
});

test("createLocationStop carries the stop kind", () => {
  assert.deepEqual(createLocationStop(), { kind: LOCATION_STOP_KIND });
});

test("parseLocationMessage validates and normalizes incoming payloads", () => {
  const parsed = parseLocationMessage(createLocationMessage(samplePosition));
  assert.equal(parsed.lat, 40.7128);
  assert.equal(parsed.lon, -74.006);
  assert.equal(parsed.accuracy, 12);

  assert.equal(parseLocationMessage(null), null);
  assert.equal(parseLocationMessage({ kind: "chat" }), null);
  assert.equal(parseLocationMessage({ kind: LOCATION_KIND, lat: 999, lon: 0 }), null);
  assert.equal(parseLocationMessage({ kind: LOCATION_KIND, lat: 0, lon: 999 }), null);
});

test("lat/lon validators enforce ranges", () => {
  assert.equal(isValidLat(90), true);
  assert.equal(isValidLat(-90), true);
  assert.equal(isValidLat(90.1), false);
  assert.equal(isValidLon(180), true);
  assert.equal(isValidLon(-181), false);
  assert.equal(isValidLat("40"), false);
});

test("formatCoords renders fixed precision or empty for invalid input", () => {
  assert.equal(formatCoords(40.7128, -74.006), "40.71280, -74.00600");
  assert.equal(formatCoords(40.7128, -74.006, 2), "40.71, -74.01");
  assert.equal(formatCoords(999, 0), "");
});

test("formatAccuracy scales meters to km and rejects junk", () => {
  assert.equal(formatAccuracy(12), "±12 m");
  assert.equal(formatAccuracy(0), "±0 m");
  assert.equal(formatAccuracy(1500), "±1.5 km");
  assert.equal(formatAccuracy(-1), "");
  assert.equal(formatAccuracy("x"), "");
});

test("mapsLink builds an OpenStreetMap URL and rejects invalid coords", () => {
  const link = mapsLink(40.7128, -74.006);
  assert.ok(link.startsWith("https://www.openstreetmap.org/?mlat=40.7128&mlon=-74.006"));
  assert.ok(link.includes("#map=16/40.7128/-74.006"));
  assert.equal(mapsLink(999, 0), "");
});
