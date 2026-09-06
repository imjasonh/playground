import test from "node:test";
import assert from "node:assert/strict";

import { parseDelta, buildResolvedSegments, applyDelta } from "../src/delta.js";
import { buildAppendDelta } from "./synthPack.js";
import { decodeUtf8, encodeUtf8 } from "../src/hex.js";

test("parseDelta annotates header and instruction byte spans", () => {
  const base = "abcdef";
  const delta = buildAppendDelta(base, "GH");
  const parsed = parseDelta(delta);
  assert.equal(parsed.regions.length >= 4, true);
  assert.equal(parsed.ops[0].copyIndex, 0);
  assert.equal(parsed.ops[0].span.start < parsed.ops[0].span.end, true);
  assert.ok(parsed.regions.some((r) => r.role === "header" && r.field === "baseSize"));
  assert.ok(parsed.regions.some((r) => r.role === "insert-data"));
});

test("buildResolvedSegments maps output bytes to copy and insert ranges", () => {
  const base = "line one\nline two\n";
  const suffix = "line three\n";
  const target = `${base}${suffix}`;
  const delta = buildAppendDelta(base, suffix);
  const parsed = parseDelta(delta);
  const out = applyDelta(encodeUtf8(base), delta);
  const segments = buildResolvedSegments(parsed, "a".repeat(40));
  assert.equal(decodeUtf8(out), target);
  let covered = 0;
  for (const seg of segments) {
    covered += seg.end - seg.start;
    if (seg.kind === "copy") {
      assert.equal(seg.copyIndex, 0);
      assert.equal(seg.baseOffset, 0);
      assert.equal(seg.end - seg.start, base.length);
    } else {
      assert.equal(decodeUtf8(out.subarray(seg.start, seg.end)), suffix);
    }
  }
  assert.equal(covered, out.length);
});
