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
  vertexNeighborDirs,
  worldToAxial,
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
  const size = 10;
  for (let i = 0; i < 6; i += 1) {
    const id = vertexId(origin.q, origin.r, i);
    const corner = hexCornerWorld(origin.q, origin.r, i, size);
    const dirs = vertexNeighborDirs(i);
    for (const dir of dirs) {
      const hex = hexAdd(origin, dir);
      let match = -1;
      for (let v = 0; v < 6; v += 1) {
        if (vertexId(hex.q, hex.r, v) === id) {
          match = v;
          break;
        }
      }
      assert.notEqual(match, -1, `neighbor ${hexKey(hex.q, hex.r)} missing ${id}`);
      const other = hexCornerWorld(hex.q, hex.r, match, size);
      assert.ok(
        Math.hypot(corner.x - other.x, corner.z - other.z) < 1e-9,
        `corner ${i} of 0,0 should sit on neighbor ${hexKey(hex.q, hex.r)}`,
      );
    }
  }
});

test("every hex corner is welded to both adjacent neighbors", () => {
  const size = 8;
  for (let i = 0; i < 6; i += 1) {
    const corner = hexCornerWorld(0, 0, i, size);
    const near = [];
    for (let d = 0; d < 6; d += 1) {
      const center = axialToWorld(HEX_DIRS[d].q, HEX_DIRS[d].r, size);
      if (Math.abs(Math.hypot(corner.x - center.x, corner.z - center.z) - size) < 1e-6) {
        near.push(d);
      }
    }
    assert.deepEqual(near.slice().sort(), vertexNeighborDirs(i).map((dir) => HEX_DIRS.indexOf(dir)).sort());
    const edge = edgeNeighbor(0, 0, i);
    const mid = {
      x: (hexCornerWorld(0, 0, i, size).x + hexCornerWorld(0, 0, i + 1, size).x) / 2,
      z: (hexCornerWorld(0, 0, i, size).z + hexCornerWorld(0, 0, i + 1, size).z) / 2,
    };
    const edgeCenter = axialToWorld(edge.q, edge.r, size);
    const originCenter = axialToWorld(0, 0, size);
    const toEdge = Math.hypot(mid.x - edgeCenter.x, mid.z - edgeCenter.z);
    const toOrigin = Math.hypot(mid.x - originCenter.x, mid.z - originCenter.z);
    assert.ok(Math.abs(toEdge - toOrigin) < 1e-6);
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

test("worldToAxial inverts axialToWorld", () => {
  const size = 10;
  const world = axialToWorld(3, -2, size);
  assert.deepEqual(worldToAxial(world.x, world.z, size), { q: 3, r: -2 });
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
