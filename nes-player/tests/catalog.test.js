import test from "node:test";
import assert from "node:assert/strict";

import {
  filterRoms,
  listingUrl,
  parseListing,
  romUrl,
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

test("parseListing keeps .nes files, strips the extension, and sorts", () => {
  const roms = parseListing([
    { type: "file", name: "pong.ne", size: 900 },
    { type: "file", name: "pong.nes", size: 24592 },
    { type: "file", name: "README.md", size: 10 },
    { type: "dir", name: "rampart.nes" },
    { type: "file", name: "Arcade.NES", size: "40976" },
    null,
  ]);
  assert.deepEqual(roms, [
    { name: "Arcade", size: 40976 },
    { name: "pong", size: 24592 },
  ]);
});

test("parseListing rejects an error body", () => {
  assert.throws(() => parseListing({ message: "API rate limit exceeded" }));
});

test("filterRoms treats spaces, underscores, and hyphens alike", () => {
  const roms = [{ name: "dvd_screensaver" }, { name: "pong" }];
  assert.deepEqual(filterRoms(roms, "DVD screen"), [{ name: "dvd_screensaver" }]);
  assert.deepEqual(filterRoms(roms, "  "), roms);
  assert.deepEqual(filterRoms(roms, "zelda"), []);
});
