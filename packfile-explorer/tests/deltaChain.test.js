import test from "node:test";
import assert from "node:assert/strict";

import { buildDeltaChain, indexByOffset } from "../src/deltaChain.js";
import { buildBaseSegments, parseDelta } from "../src/delta.js";

test("buildDeltaChain returns root-first through ofs and ref links", () => {
  const root = { oid: "r".repeat(40), offset: 0, deltaType: "none" };
  const mid = { oid: "m".repeat(40), offset: 50, deltaType: "ofs", baseOffset: 0 };
  const leaf = { oid: "l".repeat(40), offset: 120, deltaType: "ref", baseOid: "m".repeat(40) };
  const objects = [root, mid, leaf];
  const byOffset = indexByOffset(objects);
  const byOid = new Map(objects.map((o) => [o.oid, o]));

  const chain = buildDeltaChain(leaf, { byOid, byOffset });
  assert.deepEqual(chain.map((o) => o.oid), [root.oid, mid.oid, leaf.oid]);
});

test("buildDeltaChain stops at a base missing from the pack", () => {
  const leaf = { oid: "l".repeat(40), offset: 10, deltaType: "ref", baseOid: "x".repeat(40) };
  const byOffset = indexByOffset([leaf]);
  const byOid = new Map([[leaf.oid, leaf]]);
  const chain = buildDeltaChain(leaf, { byOid, byOffset });
  assert.deepEqual(chain.map((o) => o.oid), [leaf.oid]);
});

test("buildBaseSegments marks the base ranges a delta copies", () => {
  // copy base[0..4], insert "XY", copy base[8..10].
  const delta = Uint8Array.from([
    10, // base size
    8, // result size
    0x90, 0x04, // copy offset=0 size=4
    0x02, 0x58, 0x59, // insert "XY"
    0x91, 0x08, 0x02, // copy offset=8 size=2
  ]);
  const parsed = parseDelta(delta);
  const segs = buildBaseSegments(parsed);
  assert.deepEqual(
    segs.map((s) => [s.start, s.end, s.copyIndex]),
    [
      [0, 4, 0],
      [8, 10, 1],
    ],
  );
});
