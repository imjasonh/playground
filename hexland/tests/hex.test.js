import test from "node:test";
import assert from "node:assert/strict";

import {
  HEX_DIRS,
  axialToWorld,
  edgeNeighbor,
  hexAdd,
  hexCornerWorld,
  hexCountInRadius,
  hexDistance,
  hexKey,
  hexLine,
  hexRound,
  hexesInRadius,
  mod6,
  vertexId,
} from "../src/hex.js";

test("hexCountInRadius matches the hex-number formula", () => {
  assert.equal(hexCountInRadius(0), 1);
  assert.equal(hexCountInRadius(1), 7);
  assert.equal(hexCountInRadius(2), 19);
  assert.equal(hexCountInRadius(10), 331);
  assert.equal(hexesInRadius(5).length, hexCountInRadius(5));
});

test("hexDistance is cube-equivalent and symmetric", () => {
  assert.equal(hexDistance({ q: 0, r: 0 }, { q: 0, r: 0 }), 0);
  assert.equal(hexDistance({ q: 1, r: 0 }, { q: 0, r: 0 }), 1);
  assert.equal(hexDistance({ q: 2, r: -1 }, { q: 0, r: 0 }), 2);
  assert.equal(
    hexDistance({ q: -3, r: 4 }, { q: 1, r: -2 }),
    hexDistance({ q: 1, r: -2 }, { q: -3, r: 4 }),
  );
});

test("every neighbor sits at distance 1", () => {
  const origin = { q: 0, r: 0 };
  for (const dir of HEX_DIRS) {
    assert.equal(hexDistance(origin, hexAdd(origin, dir)), 1);
  }
});

test("vertex ids are shared by the three hexes that meet there", () => {
  const origin = { q: 0, r: 0 };
  for (let i = 0; i < 6; i += 1) {
    const id = vertexId(origin.q, origin.r, i);
    const n0 = hexAdd(origin, HEX_DIRS[i]);
    const n1 = hexAdd(origin, HEX_DIRS[(i + 1) % 6]);
    const fromNeighbors = [n0, n1].map((hex) => {
      for (let v = 0; v < 6; v += 1) {
        if (vertexId(hex.q, hex.r, v) === id) {
          return v;
        }
      }
      return -1;
    });
    assert.notEqual(fromNeighbors[0], -1, `neighbor ${hexKey(n0.q, n0.r)} missing ${id}`);
    assert.notEqual(fromNeighbors[1], -1, `neighbor ${hexKey(n1.q, n1.r)} missing ${id}`);
    assert.equal(vertexId(n0.q, n0.r, fromNeighbors[0]), id);
    assert.equal(vertexId(n1.q, n1.r, fromNeighbors[1]), id);
  }
});

test("hexLine walks inclusive axial steps", () => {
  const line = hexLine({ q: 0, r: 0 }, { q: 3, r: 0 });
  assert.equal(line.length, 4);
  assert.deepEqual(line[0], { q: 0, r: 0 });
  assert.deepEqual(line[3], { q: 3, r: 0 });
  assert.deepEqual(hexRound(2, -1), { q: 2, r: -1 });
});

test("edgeNeighbor is the hex across that side", () => {
  const origin = { q: 0, r: 0 };
  for (let i = 0; i < 6; i += 1) {
    const next = edgeNeighbor(origin.q, origin.r, i);
    assert.equal(hexDistance(origin, next), 1);
  }
});

test("vertex index wraps and matches the geometric corner", () => {
  assert.equal(mod6(-1), 5);
  assert.equal(mod6(6), 0);
  assert.equal(vertexId(2, -1, 8), vertexId(2, -1, 2));

  const size = 10;
  const corner = hexCornerWorld(0, 0, 0, size);
  const center = axialToWorld(0, 0, size);
  const dx = corner.x - center.x;
  const dz = corner.z - center.z;
  assert.ok(Math.abs(Math.hypot(dx, dz) - size) < 1e-9);
  assert.ok(dx > 0);
  assert.ok(dz < 0);
});
