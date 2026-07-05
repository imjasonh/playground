import test from "node:test";
import assert from "node:assert/strict";

import {
  SIGNAL_VERSION,
  LINK_KEY,
  encodeSignal,
  decodeSignal,
  safeDecodeSignal,
  buildLink,
  tokenFromUrl,
  extractToken,
} from "../src/signaling.js";

const sampleOffer = {
  type: "offer",
  sdp: "v=0\r\no=- 42 2 IN IP4 127.0.0.1\r\ns=-\r\nt=0 0\r\na=group:BUNDLE 0\r\n",
};

test("encode/decode round-trips a session description", () => {
  const token = encodeSignal(sampleOffer);
  assert.equal(typeof token, "string");
  const decoded = decodeSignal(token);
  assert.deepEqual(decoded, { type: "offer", sdp: sampleOffer.sdp });
});

test("tokens are URL-safe (no +, /, = or whitespace)", () => {
  // Use content likely to produce padding and non-url-safe base64 chars.
  const token = encodeSignal({ type: "answer", sdp: "a".repeat(101) + "??>>" });
  assert.match(token, /^[A-Za-z0-9_-]+$/);
});

test("decodeSignal preserves exact SDP bytes including CRLF and unicode", () => {
  const sdp = "v=0\r\na=note:café ✓\r\n";
  const decoded = decodeSignal(encodeSignal({ type: "answer", sdp }));
  assert.equal(decoded.sdp, sdp);
  assert.equal(decoded.type, "answer");
});

test("encodeSignal rejects bad input", () => {
  assert.throws(() => encodeSignal(null));
  assert.throws(() => encodeSignal({ type: "bogus", sdp: "x" }));
  assert.throws(() => encodeSignal({ type: "offer", sdp: "" }));
});

test("decodeSignal throws on garbage and unsupported versions", () => {
  assert.throws(() => decodeSignal(""));
  assert.throws(() => decodeSignal("!!!not base64!!!"));
  const wrongVersion = Buffer.from(
    JSON.stringify({ v: SIGNAL_VERSION + 99, t: "offer", s: "x" }),
  ).toString("base64url");
  assert.throws(() => decodeSignal(wrongVersion));
});

test("safeDecodeSignal returns null instead of throwing", () => {
  assert.equal(safeDecodeSignal("nonsense%%%"), null);
  assert.deepEqual(safeDecodeSignal(encodeSignal(sampleOffer)), {
    type: "offer",
    sdp: sampleOffer.sdp,
  });
});

test("buildLink puts the token in the hash under LINK_KEY", () => {
  const token = encodeSignal(sampleOffer);
  const link = buildLink("https://example.com/linkchat/", token);
  assert.equal(link, `https://example.com/linkchat/#${LINK_KEY}=${token}`);
});

test("buildLink replaces an existing hash rather than appending", () => {
  const token = encodeSignal(sampleOffer);
  const link = buildLink("https://example.com/app/#old=1", token);
  assert.equal(link, `https://example.com/app/#${LINK_KEY}=${token}`);
});

test("tokenFromUrl reads the token back out of a link", () => {
  const token = encodeSignal(sampleOffer);
  const link = buildLink("https://example.com/linkchat/", token);
  assert.equal(tokenFromUrl(link), token);
  assert.equal(tokenFromUrl("https://example.com/linkchat/"), null);
});

test("extractToken accepts either a full link or a bare token", () => {
  const token = encodeSignal(sampleOffer);
  const link = buildLink("https://example.com/linkchat/", token);
  assert.equal(extractToken(link), token);
  assert.equal(extractToken(`  ${token}  `), token);
  assert.equal(extractToken(""), null);
  assert.equal(extractToken(null), null);
});
