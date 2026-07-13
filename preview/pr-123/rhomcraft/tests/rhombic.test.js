import test from "node:test";
import assert from "node:assert/strict";

import {
  FACE_NEIGHBORS,
  RHOMBIC_FACES,
  RHOMBIC_VERTICES,
  cellCenter,
  isFccCell,
  nearestFcc,
  pointInRhombic,
  rhombicSignedDistance,
  validateFaceWindings,
  unitMeshVertices,
  MESH_SCALE,
} from "../src/rhombic.js";

test("FCC parity helper", () => {
  assert.equal(isFccCell(0, 0, 0), true);
  assert.equal(isFccCell(1, 0, 0), false);
  assert.equal(isFccCell(1, 1, 0), true);
  assert.equal(isFccCell(-1, -1, 0), true);
});

test("rhombic dodecahedron has 14 vertices and 12 quad faces", () => {
  assert.equal(RHOMBIC_VERTICES.length, 14);
  assert.equal(RHOMBIC_FACES.length, 12);
  assert.equal(FACE_NEIGHBORS.length, 12);
  for (const face of RHOMBIC_FACES) {
    assert.equal(face.length, 4);
    for (const i of face) assert.ok(i >= 0 && i < 14);
  }
});

test("face windings are outward", () => {
  assert.deepEqual(validateFaceWindings(), []);
});

test("neighbors stay on the FCC lattice", () => {
  for (const [dx, dy, dz] of FACE_NEIGHBORS) {
    assert.equal(isFccCell(dx, dy, dz), true);
    assert.equal(Math.hypot(dx, dy, dz), Math.SQRT2);
  }
});

test("nearestFcc snaps to even-sum lattice", () => {
  assert.deepEqual(nearestFcc(0.1, 0.1, 0.1), [0, 0, 0]);
  assert.deepEqual(nearestFcc(0.9, 0.9, 0.1), [1, 1, 0]);
  const [x, y, z] = nearestFcc(2.4, -1.2, 0.3);
  assert.equal(isFccCell(x, y, z), true);
});

test("unit cell contains its center and rejects a neighbor center", () => {
  assert.ok(pointInRhombic(0, 0, 0, 0, 0, 0));
  assert.ok(rhombicSignedDistance(0, 0, 0) < 0);
  // Neighbor center at (1,1,0) should be outside (or on boundary of) this cell
  assert.ok(!pointInRhombic(1, 1, 0, 0, 0, 0));
});

test("neighboring meshes kiss along a shared face plane", () => {
  // Face plane distance from center equals half neighbor spacing
  const halfGap = Math.SQRT2 / 2;
  const inRadius = MESH_SCALE * Math.SQRT2;
  assert.ok(Math.abs(inRadius - halfGap) < 1e-9);
  const [cx, cy, cz] = cellCenter(1, 1, 0);
  assert.deepEqual([cx, cy, cz], [1, 1, 0]);
});

test("scaled mesh vertices stay finite", () => {
  const verts = unitMeshVertices();
  assert.equal(verts.length, 14);
  assert.ok(verts.every(([x, y, z]) => Number.isFinite(x + y + z)));
});
