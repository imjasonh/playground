import test from "node:test";
import assert from "node:assert/strict";

import { createTerrain, raiseHex } from "../src/terrain.js";
import {
  cellGroundDepth,
  clamp,
  createCamera,
  hexTopPoints,
  nearestVertex,
  pickCell,
  pointInPolygon,
  project,
  rotateY,
  viewOrigin,
} from "../src/render.js";

test("clamp and rotateY keep simple invariants", () => {
  assert.equal(clamp(4, 0, 3), 3);
  assert.equal(clamp(-2, 0, 3), 0);
  const rotated = rotateY(1, 0, Math.PI / 2);
  assert.ok(Math.abs(rotated.x) < 1e-9);
  assert.ok(Math.abs(rotated.z - 1) < 1e-9);
});

test("project lifts higher world Y toward the top of the screen", () => {
  const camera = createCamera();
  camera.zoom = 1;
  camera.panX = 0;
  camera.panY = 0;
  const origin = { x: 200, y: 200 };
  const low = project(0, 0, 0, camera, origin);
  const high = project(0, 40, 0, camera, origin);
  assert.ok(high.y < low.y);
});

test("pointInPolygon detects a hex and rejects the outside", () => {
  const hex = [
    { x: 10, y: 0 },
    { x: 20, y: 6 },
    { x: 20, y: 18 },
    { x: 10, y: 24 },
    { x: 0, y: 18 },
    { x: 0, y: 6 },
  ];
  assert.equal(pointInPolygon(10, 12, hex), true);
  assert.equal(pointInPolygon(40, 12, hex), false);
});

test("pickCell hits the center hex of a flat map", () => {
  const terrain = createTerrain({ radius: 2, base: 3 });
  const camera = createCamera();
  camera.yaw = 0;
  camera.zoom = 1;
  camera.panX = 0;
  camera.panY = 0;
  const view = { width: 640, height: 480 };
  const origin = viewOrigin(view.width, view.height);
  const top = hexTopPoints(terrain, 0, 0, camera, origin);
  const cx = top.reduce((sum, p) => sum + p.x, 0) / top.length;
  const cy = top.reduce((sum, p) => sum + p.y, 0) / top.length;
  const hit = pickCell(terrain, camera, cx, cy, view);
  assert.ok(hit);
  assert.equal(hit.q, 0);
  assert.equal(hit.r, 0);
});

test("raising a hex moves its top toward the camera", () => {
  const terrain = createTerrain({ radius: 1, base: 2 });
  const camera = createCamera();
  const view = { width: 400, height: 400 };
  const origin = viewOrigin(view.width, view.height);
  const before = hexTopPoints(terrain, 0, 0, camera, origin)[0].y;
  raiseHex(terrain, 0, 0, 4);
  const after = hexTopPoints(terrain, 0, 0, camera, origin)[0].y;
  assert.ok(after < before);
});

test("nearestVertex picks the closest projected corner", () => {
  const terrain = createTerrain({ radius: 1, base: 3 });
  const camera = createCamera();
  const view = { width: 500, height: 400 };
  const origin = viewOrigin(view.width, view.height);
  const top = hexTopPoints(terrain, 0, 0, camera, origin);
  assert.equal(nearestVertex(terrain, camera, 0, 0, top[3].x, top[3].y, view), 3);
});

test("farther cells have a smaller ground depth in the default yaw", () => {
  const camera = createCamera();
  camera.yaw = 0;
  assert.ok(cellGroundDepth(0, -3, camera) < cellGroundDepth(0, 3, camera));
});
