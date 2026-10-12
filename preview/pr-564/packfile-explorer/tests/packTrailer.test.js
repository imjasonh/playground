import test from "node:test";
import assert from "node:assert/strict";
import { webcrypto } from "node:crypto";

import { verifyPackTrailer } from "../src/packTrailer.js";
import { subtleSha1Hex } from "../src/oid.js";
import { bytesToHex } from "../src/hex.js";

const sha1Hex = subtleSha1Hex(webcrypto.subtle);

test("verifyPackTrailer accepts a matching checksum", async () => {
  const body = Uint8Array.from([1, 2, 3, 4, 5]);
  const digest = new Uint8Array(await webcrypto.subtle.digest("SHA-1", body));
  const trailerHex = bytesToHex(digest);
  const packBytes = new Uint8Array(body.length + 20);
  packBytes.set(body, 0);
  packBytes.set(digest, body.length);
  const parsed = { version: 2, count: 3, trailer: trailerHex, trailerOffset: body.length };

  const result = await verifyPackTrailer(packBytes, parsed, sha1Hex);
  assert.equal(result.valid, true);
  assert.equal(result.computedTrailer, trailerHex);
  assert.equal(result.bodyBytes, body.length);
});

test("verifyPackTrailer flags a corrupted body", async () => {
  const body = Uint8Array.from([1, 2, 3, 4, 5]);
  const digest = new Uint8Array(await webcrypto.subtle.digest("SHA-1", body));
  const packBytes = new Uint8Array(body.length + 20);
  packBytes.set(body, 0);
  packBytes.set(digest, body.length);
  packBytes[0] = 99; // corrupt the body after recording the trailer
  const parsed = { version: 2, count: 3, trailer: bytesToHex(digest), trailerOffset: body.length };

  const result = await verifyPackTrailer(packBytes, parsed, sha1Hex);
  assert.equal(result.valid, false);
});
