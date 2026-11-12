import test from "node:test";
import assert from "node:assert/strict";

import { applyDelta, parseDelta } from "../src/delta.js";
import { buildAppendDelta } from "./synthPack.js";
import { decodeUtf8 } from "../src/hex.js";

test("parseDelta reports base size, result size, and ops", () => {
  const base = "abcdef";
  const delta = buildAppendDelta(base, "GH");
  const parsed = parseDelta(delta);
  assert.equal(parsed.baseSize, 6);
  assert.equal(parsed.resultSize, 8);
  assert.equal(parsed.ops[0].type, "copy");
  assert.equal(parsed.ops[0].size, 6);
  assert.equal(parsed.ops[1].type, "insert");
  assert.equal(decodeUtf8(parsed.ops[1].data), "GH");
});

test("applyDelta reconstructs the target", () => {
  const base = new TextEncoder().encode("the quick brown fox");
  const delta = buildAppendDelta("the quick brown fox", " jumps");
  const out = applyDelta(base, delta);
  assert.equal(decodeUtf8(out), "the quick brown fox jumps");
});

test("applyDelta rejects a base of the wrong size", () => {
  const delta = buildAppendDelta("abc", "d");
  assert.throws(() => applyDelta(new TextEncoder().encode("ab"), delta));
});
