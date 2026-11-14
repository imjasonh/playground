import test from "node:test";
import assert from "node:assert/strict";

import {
  PLAYABLE,
  filterRoms,
  listingUrl,
  parseListing,
  romUrl,
  selectPlayable,
  sourceUrl,
} from "../src/catalog.js";

test("URLs point at nescript/examples on main", () => {
  assert.equal(
    listingUrl(),
    "https://api.github.com/repos/imjasonh/playground/contents/nescript/examples?ref=main",
  );
  assert.equal(
    romUrl("dvd_screensaver"),
    "https://raw.githubusercontent.com/imjasonh/playground/main/nescript/examples/dvd_screensaver.nes",
  );
  assert.equal(
    sourceUrl("pong"),
    "https://github.com/imjasonh/playground/blob/main/nescript/examples/pong.ne",
  );
});

test("parseListing keeps the playable games and drops the smoke tests", () => {
  const roms = parseListing([
    { type: "file", name: "hello_sprite.nes", size: 4096 },
    { type: "file", name: "sha256.nes", size: 65536 },
    { type: "file", name: "pong.ne", size: 900 },
    { type: "file", name: "pong.nes", size: 24592 },
    { type: "file", name: "feature_canary.nes", size: 8192 },
    { type: "dir", name: "rampart" },
    null,
  ]);
  assert.deepEqual(
    roms.map((r) => r.name),
    ["pong", "sha256"],
  );
  assert.deepEqual(roms[0], { name: "pong", title: "Pong", size: 24592 });
});

test("selectPlayable uses the showcase order and retitles a cached list", () => {
  const roms = selectPlayable([
    { name: "coin_cavern", size: 1 },
    { name: "arrays_and_functions", size: 2 },
    { name: "dvd_screensaver", size: 3 },
  ]);
  assert.deepEqual(
    roms.map((r) => r.title),
    ["DVD screensaver", "Coin Cavern"],
  );
  assert.deepEqual(
    PLAYABLE.map((g) => g.name),
    [
      "platformer",
      "war",
      "pong",
      "subway",
      "rampart",
      "dvd_screensaver",
      "sha256",
      "coin_cavern",
    ],
  );
});

test("parseListing rejects an error body", () => {
  assert.throws(() => parseListing({ message: "API rate limit exceeded" }));
});

test("filterRoms matches the title and treats spaces like underscores", () => {
  const roms = selectPlayable([
    { name: "dvd_screensaver", size: 1 },
    { name: "pong", size: 1 },
  ]);
  assert.deepEqual(
    filterRoms(roms, "DVD screen").map((r) => r.name),
    ["dvd_screensaver"],
  );
  assert.equal(filterRoms(roms, "  ").length, 2);
  assert.deepEqual(filterRoms(roms, "zelda"), []);
});
