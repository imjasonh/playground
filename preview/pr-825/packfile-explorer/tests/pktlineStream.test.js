import test from "node:test";
import assert from "node:assert/strict";

import { createUploadPackReader, encodePktLine } from "../src/pktline.js";
import { concatBytes, encodeUtf8 } from "../src/hex.js";

function band(n, payload) {
  const body = typeof payload === "string" ? encodeUtf8(payload) : payload;
  return encodePktLine(concatBytes([Uint8Array.from([n]), body]));
}

test("createUploadPackReader demuxes control, pack, and live progress", () => {
  const packA = Uint8Array.from([0x50, 0x41, 0x43, 0x4b]); // "PACK"
  const packB = Uint8Array.from([1, 2, 3, 4]);
  const stream = concatBytes([
    encodePktLine("NAK\n"),
    band(2, "Enumerating objects: 100%\n"),
    band(1, packA),
    band(1, packB),
    band(2, "Total 3\n"),
  ]);

  const progress = [];
  const reader = createUploadPackReader({ onProgress: (t) => progress.push(t) });
  // Feed one byte at a time to exercise partial-line buffering.
  for (let i = 0; i < stream.length; i += 1) reader.push(stream.subarray(i, i + 1));
  const result = reader.finish();

  assert.deepEqual([...result.pack], [...concatBytes([packA, packB])]);
  assert.deepEqual(result.control, ["NAK"]);
  assert.equal(result.error, "");
  assert.equal(progress.join(""), "Enumerating objects: 100%\nTotal 3\n");
});

test("createUploadPackReader collects a side-band error", () => {
  const stream = concatBytes([encodePktLine("NAK\n"), band(3, "fatal: no such ref\n")]);
  const reader = createUploadPackReader();
  reader.push(stream);
  const result = reader.finish();
  assert.match(result.error, /no such ref/);
  assert.equal(result.pack.length, 0);
});
