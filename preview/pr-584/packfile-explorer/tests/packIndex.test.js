import test from "node:test";
import assert from "node:assert/strict";

import { computeStats, queryObjects } from "../src/packIndex.js";

const OBJECTS = [
  { oid: "aa11", typeName: "commit", offset: 12, packedSize: 100, size: 200, deltaType: "none", depth: 0 },
  { oid: "bb22", typeName: "tree", offset: 120, packedSize: 40, size: 80, deltaType: "none", depth: 0 },
  { oid: "bc33", typeName: "blob", offset: 170, packedSize: 30, size: 300, deltaType: "ofs", depth: 2 },
  { oid: "cc44", typeName: "blob", offset: 210, packedSize: 500, size: 500, deltaType: "none", depth: 0 },
];

test("computeStats aggregates counts, sizes, deltas, and depth", () => {
  const stats = computeStats(OBJECTS);
  assert.equal(stats.count, 4);
  assert.equal(stats.totalPacked, 670);
  assert.equal(stats.totalInflated, 1080);
  assert.equal(stats.deltaCounts.ofs, 1);
  assert.equal(stats.deltaCounts.none, 3);
  assert.equal(stats.maxDepth, 2);
  // Blobs dominate packed size, so they sort first.
  assert.equal(stats.byType[0].type, "blob");
  assert.equal(stats.byType[0].packed, 530);
});

test("queryObjects filters by type and delta, and sorts", () => {
  const blobs = queryObjects(OBJECTS, { type: "blob", sort: "packed" });
  assert.deepEqual(blobs.map((o) => o.oid), ["cc44", "bc33"]);

  const deltas = queryObjects(OBJECTS, { deltaType: "ofs" });
  assert.deepEqual(deltas.map((o) => o.oid), ["bc33"]);

  const byPrefix = queryObjects(OBJECTS, { search: "bb" });
  assert.deepEqual(byPrefix.map((o) => o.oid), ["bb22"]);
});
