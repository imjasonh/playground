import test from "node:test";
import assert from "node:assert/strict";

import pako from "pako";
import { parsePack, OBJ_OFS_DELTA } from "../src/pack.js";
import { makePakoInflate } from "../src/inflate.js";
import { annotatePackEntry } from "../src/packVisual.js";
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
