import test from "node:test";
import assert from "node:assert/strict";

import * as pako from "pako";
import { parsePack, OBJ_OFS_DELTA } from "../src/pack.js";
import { makePakoInflate } from "../src/inflate.js";
import { annotatePackEntry, annotatePackEntrySlice } from "../src/packVisual.js";
import { buildAppendDelta, buildPack } from "./synthPack.js";

const inflate = makePakoInflate(pako);

test("annotatePackEntry marks header, zlib, and ofs-delta base offset", () => {
  const base = "hello\n";
  const delta = buildAppendDelta(base, "world\n");
  const { pack } = buildPack([
    { type: "blob", content: base },
    { type: "ofs-delta", delta, baseIndex: 0 },
  ]);
  const parsed = parsePack(pack, inflate);
  const entry = parsed.objects[1];
  assert.equal(entry.type, OBJ_OFS_DELTA);
  const ann = annotatePackEntry(pack, entry);
  assert.equal(ann.bytes.length, entry.packedSize);
  assert.ok(ann.regions.some((r) => r.role === "pack-header"));
  assert.ok(ann.regions.some((r) => r.role === "base-offset"));
  assert.ok(ann.regions.some((r) => r.role === "zlib"));
});

test("annotatePackEntrySlice rebases the same regions to a slice starting at the entry", () => {
  const base = "hello\n";
  const delta = buildAppendDelta(base, "world\n");
  const { pack } = buildPack([
    { type: "blob", content: base },
    { type: "ofs-delta", delta, baseIndex: 0 },
  ]);
  const parsed = parsePack(pack, inflate);
  const entry = parsed.objects[1];
  const whole = annotatePackEntry(pack, entry);
  const slice = pack.subarray(entry.offset, entry.offset + entry.packedSize);
  const rebased = annotatePackEntrySlice(slice, entry);

  assert.deepEqual([...rebased.bytes], [...whole.bytes]);
  assert.equal(rebased.regions.length, whole.regions.length);
  for (let i = 0; i < rebased.regions.length; i += 1) {
    assert.equal(rebased.regions[i].role, whole.regions[i].role);
    assert.equal(rebased.regions[i].start, whole.regions[i].start - entry.offset);
    assert.equal(rebased.regions[i].end, whole.regions[i].end - entry.offset);
  }
  // Slice-relative regions index into the slice bytes directly.
  assert.ok(rebased.regions.every((r) => r.start >= 0 && r.end <= slice.length));
});
