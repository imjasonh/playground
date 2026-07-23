import test from "node:test";
import assert from "node:assert/strict";
import {
  CONUS_BOUNDS,
  inConusBounds,
  parseNominatimResults,
  searchUsPlaces,
  zoomForNominatimType,
} from "../src/geocode.js";

test("inConusBounds accepts Austin and rejects London", () => {
  assert.equal(inConusBounds(30.27, -97.74), true);
  assert.equal(inConusBounds(51.5, -0.12), false);
  assert.equal(inConusBounds(61.2, -149.9), false); // Anchorage — outside CONUS grid
});

test("zoomForNominatimType is tighter for addresses than cities", () => {
  assert.ok(zoomForNominatimType("house") > zoomForNominatimType("city"));
  assert.equal(zoomForNominatimType("city"), 10);
});

test("parseNominatimResults keeps CONUS hits and drops others", () => {
  const hits = parseNominatimResults(
    [
      {
        lat: "30.2711286",
        lon: "-97.7436995",
        display_name: "Austin, Travis County, Texas, United States",
        type: "city",
      },
      {
        lat: "21.3099",
        lon: "-157.8581",
        display_name: "Honolulu, Hawaii, United States",
        type: "city",
      },
      { lat: "bad", lon: "-97", display_name: "junk" },
    ],
    CONUS_BOUNDS,
  );
  assert.equal(hits.length, 1);
  assert.equal(hits[0].lat, 30.2711286);
  assert.match(hits[0].label, /Austin/);
  assert.equal(hits[0].zoom, 10);
});

test("searchUsPlaces calls Nominatim with US + viewbox params", async () => {
  /** @type {string | undefined} */
  let calledUrl;
  const fetchImpl = async (url) => {
    calledUrl = String(url);
    return {
      ok: true,
      async json() {
        return [
          {
            lat: "30.27",
            lon: "-97.74",
            display_name: "Austin, TX, USA",
            type: "city",
          },
        ];
      },
    };
  };
  const hits = await searchUsPlaces("Austin TX", { fetchImpl, limit: 3 });
  assert.equal(hits.length, 1);
  assert.ok(calledUrl.includes("nominatim.openstreetmap.org/search"));
  assert.ok(calledUrl.includes("countrycodes=us"));
  assert.ok(calledUrl.includes("viewbox="));
  assert.ok(calledUrl.includes("Austin"));
});

test("searchUsPlaces returns empty for short queries without fetching", async () => {
  let calls = 0;
  const fetchImpl = async () => {
    calls += 1;
    throw new Error("should not fetch");
  };
  assert.deepEqual(await searchUsPlaces("A", { fetchImpl }), []);
  assert.equal(calls, 0);
});
