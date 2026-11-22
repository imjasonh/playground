import test from "node:test";
import assert from "node:assert/strict";

import { diffPacks } from "../src/diffPacks.js";

const oid = (c) => c.repeat(40);

test("diffPacks reports added, removed, common, and deltas", () => {
  const a = [
    { oid: oid("a"), typeName: "blob", packedSize: 10, size: 20 },
    { oid: oid("b"), typeName: "blob", packedSize: 30, size: 60 },
  ];
  const b = [
    { oid: oid("b"), typeName: "blob", packedSize: 30, size: 60 },
    { oid: oid("c"), typeName: "commit", packedSize: 50, size: 90 },
  ];
  const d = diffPacks(a, b);
  assert.deepEqual(d.added.map((x) => x.oid), [oid("c")]);
  assert.deepEqual(d.removed.map((x) => x.oid), [oid("a")]);
  assert.equal(d.common, 1);
  assert.equal(d.countDelta, 0);
  assert.equal(d.packedDelta, 40); // (30+50) - (10+30)
  assert.equal(d.inflatedDelta, 70); // (60+90) - (20+60)
});
