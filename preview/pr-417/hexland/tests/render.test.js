import test from "node:test";
import assert from "node:assert/strict";

import { hexCornerWorld } from "../src/hex.js";
import { MIN_HEIGHT, createTerrain, raiseHex } from "../src/terrain.js";
import {
  cellGroundDepth,
  clamp,
  collectVisibleCells,
  createCamera,
  fitZoom,
  hexBasePoints,
  hexTopPoints,
  nearestVertex,
  pickCell,
  pointInPolygon,
  project,
  rotateY,
  screenToWorld,
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

test("a raised neighbor projects as a sloped top, not a flat step", () => {
  const terrain = createTerrain({ radius: 1, base: 3 });
  const camera = createCamera();
  camera.yaw = 0;
  camera.zoom = 1;
  camera.panX = 0;
  camera.panY = 0;
  const origin = { x: 200, y: 200 };
  raiseHex(terrain, 0, 0, 2);
  const top = hexTopPoints(terrain, 1, 0, camera, origin);
  const ys = top.map((point) => point.y);
  assert.ok(Math.max(...ys) - Math.min(...ys) > 8);
});

test("collectVisibleCells keeps the opening view much smaller than the map", () => {
  const terrain = createTerrain({ radius: 40 });
  const camera = createCamera();
  camera.yaw = 0;
  camera.panX = 0;
  camera.panY = 0;
  const view = { width: 800, height: 600 };
  fitZoom(terrain, camera, view);
  const { cells } = collectVisibleCells(terrain, camera, view);
  assert.ok(cells.length < terrain.cells.length / 4);
  assert.ok(cells.length > 40);
  assert.ok(cells.some((cell) => cell.q === 0 && cell.r === 0));
});

test("fitZoom keeps hexes large enough to paint on a big map", () => {
  const terrain = createTerrain({ radius: 22 });
  const camera = createCamera();
  camera.zoom = 2;
  fitZoom(terrain, camera, { width: 800, height: 600 });
  assert.ok(camera.zoom >= 0.55);
  assert.ok(camera.zoom <= 1.4);
  assert.ok(camera.zoom < 2);
});

test("hex bases sit at the underwater floor", () => {
  const camera = createCamera();
  camera.yaw = 0;
  camera.zoom = 1;
  camera.panX = 0;
  camera.panY = 0;
  const origin = { x: 200, y: 200 };
  const base = hexBasePoints(0, 0, camera, origin);
  for (let i = 0; i < 6; i += 1) {
    const corner = hexCornerWorld(0, 0, i, camera.hexSize);
    const expected = project(
      corner.x,
      MIN_HEIGHT * camera.heightScale,
      corner.z,
      camera,
      origin,
    );
    assert.ok(Math.abs(base[i].x - expected.x) < 1e-6);
    assert.ok(Math.abs(base[i].y - expected.y) < 1e-6);
  }
  const floor = project(0, MIN_HEIGHT * camera.heightScale, 0, camera, origin);
  const ground = project(0, 0, 0, camera, origin);
  assert.ok(floor.y > ground.y);
});

test("screenToWorld inverts project on the ground plane", () => {
  const camera = createCamera();
  camera.yaw = 0.2;
  camera.elevation = 0.5;
  camera.zoom = 1;
  camera.panX = 0;
  camera.panY = 0;
  const view = { width: 800, height: 600 };
  const origin = viewOrigin(view.width, view.height);
  const screen = project(40, 0, -20, camera, origin);
  const world = screenToWorld(camera, screen.x, screen.y, view, 0);
  assert.ok(Math.abs(world.x - 40) < 1e-6);
  assert.ok(Math.abs(world.z + 20) < 1e-6);
});
