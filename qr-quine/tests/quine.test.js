import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import { createRequire } from "node:module";

import { Q } from "../src/encode.js";
import { quine } from "../src/quine.js";
import { minify, quineUrl } from "../build.js";

const require = createRequire(import.meta.url);
const QRCode = require("qrcode");
const jsQR = require("jsqr");

const SIZE = 177;

function textOf(length) {
  let text = "";
  for (let i = 0; i < length; i++) {
    text += String.fromCharCode(32 + ((i * 17) % 95));
  }
  return text;
}

function countDiffs(text) {
  const mine = Q(text);
  const symbol = QRCode.create([{ data: text, mode: "byte" }], {
    errorCorrectionLevel: "L",
    version: 40,
    maskPattern: 0,
  });
  let diffs = 0;
  for (let row = 0; row < SIZE; row++) {
    for (let col = 0; col < SIZE; col++) {
      const mineBit = mine[row * SIZE + col] & 1;
      const libraryBit = symbol.modules.get(row, col) ? 1 : 0;
      if (mineBit !== libraryBit) {
        diffs++;
      }
    }
  }
  return diffs;
}

test("version 40 byte symbols match the reference encoder", () => {
  for (const length of [1, 2, 8, 9, 17, 100, 500, 2000, 2952, 2953]) {
    assert.equal(countDiffs(textOf(length)), 0, "length " + length);
  }
});

test("the data URL is the script and fits in the symbol", () => {
  const src = fs.readFileSync(new URL("../src/encode.js", import.meta.url), "utf8");
  const built = quineUrl(src);
  assert.equal(quine, built);
  assert.ok(quine.length <= 2953, quine.length);
  const payload = built.slice("data:text/html,".length);
  assert.equal(payload.includes("?"), false);
  assert.equal(payload.includes("#"), false);
  const decoded = decodeURIComponent(payload);
  assert.equal(decoded, "<script>" + minify(src) + "D(location.href)</script>");
  assert.equal(quine.indexOf("\n"), -1);
  assert.equal(countDiffs(quine), 0);
});

function scan(text) {
  const modules = Q(text);
  const scale = 4;
  const quiet = 4;
  const side = (SIZE + quiet * 2) * scale;
  const data = new Uint8ClampedArray(side * side * 4);
  data.fill(255);
  for (let row = 0; row < SIZE; row++) {
    for (let col = 0; col < SIZE; col++) {
      if ((modules[row * SIZE + col] & 1) === 0) {
        continue;
      }
      for (let y = 0; y < scale; y++) {
        for (let x = 0; x < scale; x++) {
          const px = ((row + quiet) * scale + y) * side + ((col + quiet) * scale + x);
          data[px * 4] = 0;
          data[px * 4 + 1] = 0;
          data[px * 4 + 2] = 0;
        }
      }
    }
  }
  const code = jsQR(data, side, side);
  assert.ok(code, "decoder found no symbol");
  return code.data;
}

test("a page address scans back as that address", () => {
  const page = "https://imjasonh.github.io/playground/qr-quine/";
  assert.equal(countDiffs(page), 0);
  assert.equal(scan(page), page);
});

test("a scan of the painted symbol returns the data URL", () => {
  assert.equal(scan(quine), quine);
});
