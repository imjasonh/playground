import test from "node:test";
import assert from "node:assert/strict";

import { byteRoles, renderHexEditor, renderSegmentedText } from "../src/hexView.js";
import { parseDelta, buildResolvedSegments } from "../src/delta.js";
import { buildAppendDelta } from "./synthPack.js";
import { encodeUtf8 } from "../src/hex.js";

test("byteRoles assigns the last overlapping region per byte", () => {
  const roles = byteRoles(4, [
    { start: 0, end: 4, role: "header", label: "all" },
    { start: 2, end: 3, role: "insert-data", label: "one" },
  ]);
  assert.equal(roles[0].role, "header");
  assert.equal(roles[2].role, "insert-data");
});

test("renderHexEditor includes offset column and highlighted bytes", () => {
  const html = renderHexEditor(Uint8Array.from([0x48, 0x69]), [
    { start: 0, end: 2, role: "insert-data", label: "Hi" },
  ]);
  assert.match(html, /hex-offset/);
  assert.match(html, /hex-byte hx-insert/);
  assert.match(html, /48/);
});

test("renderSegmentedText colors insert bytes white and copy bytes by index", () => {
  const base = "abc";
  const delta = buildAppendDelta(base, "Z");
  const parsed = parseDelta(delta);
  const segments = buildResolvedSegments(parsed, "c".repeat(40));
  const out = encodeUtf8("abcZ");
  const html = renderSegmentedText(out, segments);
  assert.match(html, /seg-insert/);
  assert.match(html, /seg-copy seg-copy-0/);
  assert.match(html, /Z/);
});
