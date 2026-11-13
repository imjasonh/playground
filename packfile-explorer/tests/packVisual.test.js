import test from "node:test";
import assert from "node:assert/strict";

import * as pako from "pako";
import { parsePack, OBJ_OFS_DELTA } from "../src/pack.js";
import { makePakoInflate } from "../src/inflate.js";
import { annotatePackEntrySlice } from "../src/packVisual.js";
import { buildAppendDelta, buildPack } from "./synthPack.js";

const inflate = makePakoInflate(pako);

test("annotatePackEntrySlice marks header, base offset, and zlib relative to the entry", () => {
  const base = "hello\n";
  const delta = buildAppendDelta(base, "world\n");
  const { pack } = buildPack([
    { type: "blob", content: base },
    { type: "ofs-delta", delta, baseIndex: 0 },
  ]);
  const parsed = parsePack(pack, inflate);
  const entry = parsed.objects[1];
  assert.equal(entry.type, OBJ_OFS_DELTA);
  const slice = pack.subarray(entry.offset, entry.offset + entry.packedSize);
  const ann = annotatePackEntrySlice(slice, entry);

  assert.equal(ann.bytes.length, entry.packedSize);
  assert.deepEqual(
    ann.regions.map((r) => r.role),
    ["pack-header", "base-offset", "zlib"],
  );
  assert.equal(ann.regions[0].start, 0);
  const zlib = ann.regions[2];
  assert.equal(zlib.start, entry.dataOffset - entry.offset);
  assert.equal(zlib.end, entry.packedSize);
  assert.equal(ann.regions[1].end, zlib.start);
});
