import test from "node:test";
import assert from "node:assert/strict";

import { deflateToBase64Url, inflateFromBase64Url } from "../src/codec.js";

test("deflate/inflate round-trips text", async () => {
  const text = "hello world " + "x".repeat(500);
  const token = await deflateToBase64Url(text);
  assert.equal(typeof token, "string");
  assert.equal(await inflateFromBase64Url(token), text);
});

test("compressed token is URL-safe", async () => {
  const token = await deflateToBase64Url("a".repeat(1000) + "??//++");
  assert.match(token, /^[A-Za-z0-9_-]+$/);
});

test("compression meaningfully shrinks repetitive SDP-like text", async () => {
  // Simulate the repetitive structure of a real SDP.
  const sdp = Array.from({ length: 120 }, (_, i) =>
    `a=rtpmap:${i} OPUS/48000/2\r\na=rtcp-fb:${i} transport-cc\r\n`,
  ).join("");
  const token = await deflateToBase64Url(sdp);
  assert.ok(
    token.length < sdp.length / 2,
    `expected >2x shrink, got ${sdp.length} -> ${token.length}`,
  );
  assert.equal(await inflateFromBase64Url(token), sdp);
});

test("inflate rejects empty / garbage input", async () => {
  await assert.rejects(() => inflateFromBase64Url(""));
  await assert.rejects(() => inflateFromBase64Url("!!!!not-deflate!!!!"));
});

test("preserves unicode through the round-trip", async () => {
  const text = "café ✓ 🚀 — naïve";
  assert.equal(await inflateFromBase64Url(await deflateToBase64Url(text)), text);
});
