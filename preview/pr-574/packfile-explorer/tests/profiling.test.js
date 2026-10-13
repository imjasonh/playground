import test from "node:test";
import assert from "node:assert/strict";

import { deltaSavings, queryObjects, topObjects } from "../src/packIndex.js";

function obj(over) {
  return {
    oid: "0".repeat(40),
    typeName: "blob",
    deltaType: "none",
    offset: 0,
    size: 100,
    packedSize: 40,
    depth: 0,
    ...over,
  };
}

test("deltaSavings is inflated minus packed, floored at zero", () => {
  assert.equal(deltaSavings(obj({ size: 100, packedSize: 30 })), 70);
  assert.equal(deltaSavings(obj({ size: 20, packedSize: 40 })), 0);
});

test("topObjects ranks by the chosen metric, largest first", () => {
  const objects = [
    obj({ oid: "a".repeat(40), packedSize: 10, size: 200 }),
    obj({ oid: "b".repeat(40), packedSize: 90, size: 100 }),
    obj({ oid: "c".repeat(40), packedSize: 50, size: 300 }),
  ];
  const byPacked = topObjects(objects, { metric: "packed", limit: 2 });
  assert.deepEqual(byPacked.map((r) => r.obj.oid), ["b".repeat(40), "c".repeat(40)]);
  const bySavings = topObjects(objects, { metric: "savings", limit: 1 });
  assert.equal(bySavings[0].obj.oid, "c".repeat(40));
  assert.equal(bySavings[0].value, 250);
});

test("queryObjects filters by reachability and an oid set", () => {
  const objects = [
    obj({ oid: "a".repeat(40) }),
    obj({ oid: "b".repeat(40) }),
    obj({ oid: "c".repeat(40) }),
  ];
  const reachable = new Set(["a".repeat(40), "c".repeat(40)]);
  const onlyReachable = queryObjects(objects, { reachability: "reachable", reachable });
  assert.deepEqual(onlyReachable.map((o) => o.oid).sort(), ["a".repeat(40), "c".repeat(40)]);
  const onlyUnreachable = queryObjects(objects, { reachability: "unreachable", reachable });
  assert.deepEqual(onlyUnreachable.map((o) => o.oid), ["b".repeat(40)]);
  const restricted = queryObjects(objects, { oids: new Set(["b".repeat(40)]) });
  assert.deepEqual(restricted.map((o) => o.oid), ["b".repeat(40)]);
});
