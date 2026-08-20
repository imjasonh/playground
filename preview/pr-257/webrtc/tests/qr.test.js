import test from "node:test";
import assert from "node:assert/strict";

import { buildMatrix, QrCapacityError } from "../src/qr.js";

test("buildMatrix produces a valid module grid", () => {
  const { count, isDark } = buildMatrix("https://example.com/#z=abc123");
  // Module count is 17 + 4*version, always odd and >= 21 (version 1).
  assert.ok(count >= 21);
  assert.equal(count % 2, 1);
  // Top-left finder pattern corner is always dark.
  assert.equal(isDark(0, 0), true);
});

test("larger payloads need a bigger grid", () => {
  const small = buildMatrix("hi").count;
  const big = buildMatrix("x".repeat(800)).count;
  assert.ok(big > small);
});

test("a typical compressed token fits within QR capacity", () => {
  // ~2.3k base64 chars is the ballpark for a compressed SDP; must not throw.
  const token = "A".repeat(2300);
  const { count } = buildMatrix(token);
  assert.ok(count <= 177); // version 40 is 177x177
});

test("throws QrCapacityError when data exceeds the largest QR", () => {
  assert.throws(() => buildMatrix("Z".repeat(3200)), QrCapacityError);
});
