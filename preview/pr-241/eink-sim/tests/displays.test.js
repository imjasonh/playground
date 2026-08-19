import test from "node:test";
import assert from "node:assert/strict";

import {
  DISPLAYS,
  PALETTES,
  RESPONSE,
  getDisplay,
  getPalette,
  getResponse,
  displayCategories,
} from "../src/displays.js";
import { paletteColorCount } from "../src/dither.js";

test("catalog is non-empty and every id is unique", () => {
  assert.ok(DISPLAYS.length >= 10);
  const ids = new Set(DISPLAYS.map((d) => d.id));
  assert.equal(ids.size, DISPLAYS.length);
});

test("every display references a known palette and response", () => {
  for (const d of DISPLAYS) {
    assert.ok(PALETTES[d.palette], `${d.id} palette ${d.palette} missing`);
    assert.ok(RESPONSE[d.response], `${d.id} response ${d.response} missing`);
  }
});

test("every display has sane physical specs", () => {
  for (const d of DISPLAYS) {
    assert.ok(d.width > 0 && d.height > 0, `${d.id} bad resolution`);
    assert.ok(d.ppi > 0 && d.ppi <= 400, `${d.id} bad ppi`);
    assert.ok(d.inches > 0, `${d.id} bad size`);
    assert.equal(typeof d.name, "string");
    assert.equal(typeof d.note, "string");
    assert.equal(typeof d.refresh, "string");
  }
});

test("resolution roughly matches diagonal and ppi", () => {
  // diagonal(px) / ppi should be within ~20% of the advertised inches.
  for (const d of DISPLAYS) {
    const diagPx = Math.hypot(d.width, d.height);
    const computedInches = diagPx / d.ppi;
    const ratio = computedInches / d.inches;
    assert.ok(
      ratio > 0.8 && ratio < 1.2,
      `${d.id}: computed ${computedInches.toFixed(2)}" vs ${d.inches}"`,
    );
  }
});

test("list palettes use canonical primaries", () => {
  // ACeP 7-color must contain orange (255,128,0) — the signature ink.
  const acep = PALETTES.acep7.colors;
  assert.ok(acep.some((c) => c[0] === 255 && c[1] === 128 && c[2] === 0));
  // Spectra 6 must contain all four chromatic primaries.
  const spectra = PALETTES.spectra6.colors;
  for (const c of [
    [255, 0, 0],
    [255, 255, 0],
    [0, 255, 0],
    [0, 0, 255],
  ]) {
    assert.ok(spectra.some((x) => x[0] === c[0] && x[1] === c[1] && x[2] === c[2]));
  }
});

test("palette color counts are as expected", () => {
  assert.equal(paletteColorCount(PALETTES.mono1), 2);
  assert.equal(paletteColorCount(PALETTES.gray16), 16);
  assert.equal(paletteColorCount(PALETTES.spectra6), 6);
  assert.equal(paletteColorCount(PALETTES.acep7), 7);
  assert.equal(paletteColorCount(PALETTES.bwr), 3);
  assert.equal(paletteColorCount(PALETTES.bwry), 4);
});

test("responses are muted and low-contrast (white < ideal, black > ideal)", () => {
  for (const [name, r] of Object.entries(RESPONSE)) {
    assert.ok(r.white.every((v) => v <= 255 && v >= 150), `${name} white`);
    assert.ok(r.black.every((v) => v >= 20 && v <= 90), `${name} black`);
    assert.ok(r.saturation > 0 && r.saturation <= 1, `${name} saturation`);
    // white must be brighter than black on every channel
    for (let i = 0; i < 3; i++) {
      assert.ok(r.white[i] > r.black[i], `${name} channel ${i}`);
    }
  }
});

test("color technologies mute chroma; grayscale panels keep saturation 1", () => {
  assert.equal(RESPONSE.carta.saturation, 1);
  assert.ok(RESPONSE.kaleido3.saturation < 0.6);
  assert.ok(RESPONSE.acep7.saturation < 1);
  assert.ok(RESPONSE.spectra6.saturation < 1);
});

test("helpers resolve displays, palettes, responses", () => {
  const d = DISPLAYS[0];
  assert.equal(getDisplay(d.id), d);
  assert.equal(getDisplay("does-not-exist"), null);
  assert.equal(getPalette(d), PALETTES[d.palette]);
  assert.equal(getResponse(d), RESPONSE[d.response]);
});

test("displayCategories returns unique categories covering all displays", () => {
  const cats = displayCategories();
  assert.equal(new Set(cats).size, cats.length);
  for (const d of DISPLAYS) assert.ok(cats.includes(d.category));
});
