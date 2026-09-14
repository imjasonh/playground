import test from "node:test";
import assert from "node:assert/strict";

import { HEX_DIRS, hexAdd, hexCornerWorld, hexDistance, vertexId, vertexNeighborDirs } from "../src/hex.js";
import {
  DEFAULT_BASE,
  DEFAULT_WATER,
  MAX_HEIGHT,
  MIN_HEIGHT,
  applyHeights,
  cellsInBrush,
  cloneHeights,
  createHistory,
  createTerrain,
  flattenTerrain,
  generateHills,
  getVertexHeight,
  hasCell,
  hasRoad,
  heightsEqual,
  hexIsShore,
  hexIsUnderwater,
  hexMaxHeight,
  hexMeanHeight,
  hexMinHeight,
  hexVertexHeights,
  isSkirtEdge,
  levelHex,
  mulberry32,
  pushUndo,
  raiseBrush,
  raiseHex,
  raiseVertex,
  redo,
  sculptPreview,
  setRoad,
  setRoadBrush,
  setWaterLevel,
  smoothSlopes,
  terrainFingerprint,
  undo,
} from "../src/terrain.js";

function allHeights(terrain) {
  return [...terrain.heights.values()];
}

test("createTerrain fills every on-map vertex at the base height", () => {
  const terrain = createTerrain({ radius: 2, base: 4, waterLevel: 1 });
  assert.equal(terrain.cells.length, 19);
  assert.equal(hasCell(terrain, 0, 0), true);
  assert.equal(hasCell(terrain, 3, 0), false);
  assert.ok(allHeights(terrain).every((value) => value === 4));
  assert.equal(terrain.waterLevel, 1);
  assert.deepEqual(hexVertexHeights(terrain, 0, 0), [4, 4, 4, 4, 4, 4]);
});

test("raising a hex lifts its six vertices and two on each neighbor", () => {
  const terrain = createTerrain({ radius: 2, base: 3 });
  assert.equal(raiseHex(terrain, 0, 0, 1), true);
  assert.ok(hexVertexHeights(terrain, 0, 0).every((value) => value === 4));

  for (const dir of HEX_DIRS) {
    const neighbor = hexAdd({ q: 0, r: 0 }, dir);
    const heights = hexVertexHeights(terrain, neighbor.q, neighbor.r);
    const lifted = heights.filter((value) => value === 4).length;
    const stayed = heights.filter((value) => value === 3).length;
    assert.equal(lifted, 2);
    assert.equal(stayed, 4);
  }
});

test("a shared vertex raised from one hex is visible from the others", () => {
  const terrain = createTerrain({ radius: 1, base: 2 });
  assert.equal(raiseVertex(terrain, 0, 0, 0, 3), true);
  const id = vertexId(0, 0, 0);
  const n0 = hexAdd({ q: 0, r: 0 }, HEX_DIRS[0]);
  const n1 = hexAdd({ q: 0, r: 0 }, HEX_DIRS[1]);
  assert.equal(terrain.heights.get(id), 5);
  assert.equal(hexMaxHeight(terrain, n0.q, n0.r), 5);
  assert.equal(hexMaxHeight(terrain, n1.q, n1.r), 5);
  assert.equal(getVertexHeight(terrain, 0, 0, 0), 5);
});

test("raise and lower clamp to the height range", () => {
  const terrain = createTerrain({ radius: 1, base: 0 });
  assert.equal(raiseHex(terrain, 0, 0, -4), false);
  assert.equal(hexMinHeight(terrain, 0, 0), MIN_HEIGHT);

  flattenTerrain(terrain, MAX_HEIGHT);
  assert.equal(raiseHex(terrain, 0, 0, 2), false);
  assert.equal(hexMaxHeight(terrain, 0, 0), MAX_HEIGHT);
});

test("levelHex flattens a tile to one height", () => {
  const terrain = createTerrain({ radius: 1, base: 3 });
  raiseVertex(terrain, 0, 0, 2, 2);
  raiseVertex(terrain, 0, 0, 4, -1);
  assert.ok(hexMaxHeight(terrain, 0, 0) > hexMinHeight(terrain, 0, 0));
  assert.equal(levelHex(terrain, 0, 0, 6), true);
  assert.ok(hexVertexHeights(terrain, 0, 0).every((value) => value === 6));
  assert.equal(Math.round(hexMeanHeight(terrain, 0, 0)), 6);
});

test("brush radius 0 is the tile, radius 1 includes neighbors", () => {
  const terrain = createTerrain({ radius: 2, base: 2 });
  const tile = cellsInBrush(terrain, { q: 0, r: 0 }, 0);
  const patch = cellsInBrush(terrain, { q: 0, r: 0 }, 1);
  assert.equal(tile.length, 1);
  assert.equal(patch.length, 7);
  assert.ok(patch.every((cell) => hexDistance(cell, { q: 0, r: 0 }) <= 1));

  raiseBrush(terrain, 0, 0, 1, 1);
  for (const cell of patch) {
    assert.ok(hexMeanHeight(terrain, cell.q, cell.r) > 2);
  }
});

function maxEdgeStep(terrain, q, r) {
  const heights = hexVertexHeights(terrain, q, r);
  let max = 0;
  for (let i = 0; i < 6; i += 1) {
    max = Math.max(max, Math.abs(heights[i] - heights[(i + 1) % 6]));
  }
  return max;
}

test("smoothSlopes after a double raise pulls the next ring up", () => {
  const terrain = createTerrain({ radius: 3, base: 3 });
  raiseHex(terrain, 0, 0, 2);
  assert.equal(maxEdgeStep(terrain, 1, 0) >= 2, true);
  smoothSlopes(terrain, true);
  assert.ok(maxEdgeStep(terrain, 1, 0) <= 1);
  assert.ok(hexMaxHeight(terrain, 1, 0) >= 4);
});

test("smoothSlopes after a lower pulls highs down", () => {
  const terrain = createTerrain({ radius: 2, base: 6 });
  raiseHex(terrain, 0, 0, -2);
  smoothSlopes(terrain, false);
  assert.ok(maxEdgeStep(terrain, 1, 0) <= 1);
  assert.ok(hexMinHeight(terrain, 1, 0) <= 5);
});

test("water classification follows min and max vertex heights", () => {
  const terrain = createTerrain({ radius: 1, base: 3, waterLevel: 2 });
  assert.equal(hexIsUnderwater(terrain, 0, 0), false);
  raiseHex(terrain, 0, 0, -2);
  assert.equal(hexIsUnderwater(terrain, 0, 0), true);
  raiseVertex(terrain, 0, 0, 1, 3);
  assert.equal(hexIsShore(terrain, 0, 0), true);
  setWaterLevel(terrain, 0);
  assert.equal(hexIsUnderwater(terrain, 0, 0), false);
});

test("undo and redo restore vertex heights", () => {
  const terrain = createTerrain({ radius: 1, base: 3 });
  const history = createHistory();
  pushUndo(history, terrain);
  raiseHex(terrain, 0, 0, 2);
  const afterRaise = cloneHeights(terrain);
  assert.equal(undo(history, terrain), true);
  assert.ok(hexVertexHeights(terrain, 0, 0).every((value) => value === 3));
  assert.equal(redo(history, terrain), true);
  assert.ok(heightsEqual(terrain.heights, afterRaise));
});

test("sculptPreview and generateHills stay in range and are seeded", () => {
  const preview = createTerrain({ radius: 6, base: 3 });
  sculptPreview(preview);
  assert.ok(allHeights(preview).every((value) => value >= MIN_HEIGHT && value <= MAX_HEIGHT));
  assert.notEqual(terrainFingerprint(preview), terrainFingerprint(createTerrain({ radius: 6 })));

  const a = createTerrain({ radius: 5 });
  const b = createTerrain({ radius: 5 });
  const c = createTerrain({ radius: 5 });
  generateHills(a, mulberry32(11));
  generateHills(b, mulberry32(11));
  generateHills(c, mulberry32(29));
  assert.equal(terrainFingerprint(a), terrainFingerprint(b));
  assert.notEqual(terrainFingerprint(a), terrainFingerprint(c));
  assert.equal(a.cells.length, 91);
});

test("applyHeights replaces the live map", () => {
  const terrain = createTerrain({ radius: 1, base: 2 });
  const snap = cloneHeights(terrain);
  raiseHex(terrain, 0, 0, 3);
  applyHeights(terrain, snap);
  assert.ok(heightsEqual(terrain.heights, snap));
});

test("off-map edits are no-ops", () => {
  const terrain = createTerrain({ radius: 1, base: 3 });
  assert.equal(raiseHex(terrain, 8, 8, 1), false);
  assert.equal(raiseVertex(terrain, 8, 8, 0, 1), false);
  assert.equal(levelHex(terrain, 8, 8, 1), false);
  assert.equal(setRoad(terrain, 8, 8, true), false);
  assert.equal(DEFAULT_BASE, 3);
  assert.equal(DEFAULT_WATER, 2);
});

test("raising a hex lifts the corners it shares with each neighbor", () => {
  const terrain = createTerrain({ radius: 1, base: 3 });
  raiseHex(terrain, 0, 0, 1);
  const size = 10;
  for (let i = 0; i < 6; i += 1) {
    const corner = hexCornerWorld(0, 0, i, size);
    assert.equal(getVertexHeight(terrain, 0, 0, i), 4);
    for (const dir of vertexNeighborDirs(i)) {
      const hex = hexAdd({ q: 0, r: 0 }, dir);
      let welded = false;
      for (let v = 0; v < 6; v += 1) {
        const other = hexCornerWorld(hex.q, hex.r, v, size);
        if (Math.hypot(corner.x - other.x, corner.z - other.z) >= 1e-6) {
          continue;
        }
        welded = true;
        assert.equal(getVertexHeight(terrain, hex.q, hex.r, v), 4);
      }
      assert.equal(welded, true);
    }
  }
});

test("raising a hex tilts neighbors instead of leaving a cliff step", () => {
  const terrain = createTerrain({ radius: 1, base: 3 });
  raiseHex(terrain, 0, 0, 1);
  const neighbor = hexVertexHeights(terrain, 1, 0);
  assert.ok(new Set(neighbor).size >= 2);
  assert.ok(neighbor.some((value) => value === 4));
  assert.ok(neighbor.some((value) => value === 3));
});

test("interior hex edges are not skirt edges", () => {
  const terrain = createTerrain({ radius: 1, base: 3 });
  for (let i = 0; i < 6; i += 1) {
    assert.equal(isSkirtEdge(terrain, 0, 0, i), false);
  }
  let skirts = 0;
  for (let i = 0; i < 6; i += 1) {
    if (isSkirtEdge(terrain, 1, 0, i)) {
      skirts += 1;
    }
  }
  assert.ok(skirts >= 3);
});

test("roads paint, clear, and undo", () => {
  const terrain = createTerrain({ radius: 2, base: 3 });
  const history = createHistory();
  assert.equal(hasRoad(terrain, 0, 0), false);
  pushUndo(history, terrain);
  assert.equal(setRoad(terrain, 0, 0, true), true);
  assert.equal(setRoadBrush(terrain, 1, 0, 0, true), true);
  assert.equal(hasRoad(terrain, 0, 0), true);
  assert.equal(hasRoad(terrain, 1, 0), true);
  assert.equal(setRoad(terrain, 0, 0, true), false);
  assert.equal(setRoad(terrain, 0, 0, false), true);
  assert.equal(hasRoad(terrain, 0, 0), false);
  assert.equal(undo(history, terrain), true);
  assert.equal(hasRoad(terrain, 0, 0), false);
  assert.equal(hasRoad(terrain, 1, 0), false);
});
