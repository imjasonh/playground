import test from "node:test";
import assert from "node:assert/strict";
import { createGrid, pickGrid } from "../src/grid.js";
import {
  centerlineCellWeights,
  computeRose,
  distanceToPeople,
  peopleInCorridor,
  rosePolygon,
} from "../src/rays.js";
import { feetToMeters, milesToMeters } from "../src/geo.js";

function makeAsymmetricGrid() {
  const width = 60;
  const height = 40;
  const cellDeg = 0.01;
  const west = -74.3;
  const north = 40.9;
  const south = north - height * cellDeg;
  const data = new Float32Array(width * height);
  for (let r = 0; r < height; r++) {
    for (let c = 0; c < width; c++) {
      data[r * width + c] = c >= 40 ? 20_000 : 20;
    }
  }
  return createGrid(
    { west, south, north, east: west + width * cellDeg, cellDeg, width, height },
    data,
  );
}

const ORIGIN = { lat: 40.7, lon: -74.2 };
const WIDTH = feetToMeters(500);

test("peopleInCorridor finds more people toward the dense side", () => {
  const grid = makeAsymmetricGrid();
  const lengthM = milesToMeters(25);
  const east = peopleInCorridor(grid, ORIGIN, 90, lengthM, WIDTH);
  const west = peopleInCorridor(grid, ORIGIN, 270, lengthM, WIDTH);
  assert.ok(east > west * 3, `east ${east} should dwarf west ${west}`);
});

test("wider corridor collects at least as many people", () => {
  const grid = makeAsymmetricGrid();
  const lengthM = milesToMeters(20);
  // Width only pulls neighboring cells once it approaches cell size (~0.7 mi here).
  const narrow = peopleInCorridor(grid, ORIGIN, 90, lengthM, feetToMeters(200));
  const wide = peopleInCorridor(grid, ORIGIN, 90, lengthM, milesToMeters(3));
  assert.ok(wide > narrow, `wide ${wide} should beat narrow ${narrow}`);
});

test("wider corridor reaches a target sooner", () => {
  const grid = makeAsymmetricGrid();
  const maxLengthM = milesToMeters(40);
  const target = 100_000;
  const thin = distanceToPeople(
    grid,
    ORIGIN,
    90,
    target,
    feetToMeters(200),
    maxLengthM,
  );
  const fat = distanceToPeople(
    grid,
    ORIGIN,
    90,
    target,
    milesToMeters(3),
    maxLengthM,
  );
  assert.ok(Number.isFinite(thin) && Number.isFinite(fat));
  assert.ok(fat < thin, `fat ${fat} should be shorter than thin ${thin}`);
});

test("distanceToPeople is shorter toward dense cells", () => {
  const grid = makeAsymmetricGrid();
  const maxLengthM = milesToMeters(40);
  const target = 100_000;
  const east = distanceToPeople(grid, ORIGIN, 90, target, WIDTH, maxLengthM);
  const west = distanceToPeople(grid, ORIGIN, 270, target, WIDTH, maxLengthM);
  assert.ok(Number.isFinite(east), `east distance ${east}`);
  assert.ok(east < west, `east ${east} should be < west ${west}`);
});

test("computeRose marks east reached sooner than west", () => {
  const grid = makeAsymmetricGrid();
  const rays = computeRose(grid, ORIGIN, {
    widthM: WIDTH,
    targetPeople: 80_000,
    maxLengthM: milesToMeters(40),
    rayCount: 36,
  });
  assert.equal(rays.length, 36);
  const east = rays.find((r) => r.bearingDeg === 90);
  const west = rays.find((r) => r.bearingDeg === 270);
  assert.ok(east.reached, "east should reach target");
  assert.ok(east.lengthM < west.lengthM);
});

test("rosePolygon closes the ring", () => {
  const origin = { lat: 40, lon: -74 };
  const rays = [
    { bearingDeg: 0 },
    { bearingDeg: 120 },
    { bearingDeg: 240 },
  ];
  const ring = rosePolygon(origin, rays, () => 1000);
  assert.equal(ring.length, 4);
  assert.deepEqual(ring[0], ring[3]);
});

test("centerlineCellWeights averages the two cells on a grid edge", () => {
  const vert = centerlineCellWeights(10, 5.4, 100, 100);
  assert.equal(vert.length, 2);
  assert.deepEqual(
    vert.map((c) => [c.col, c.weight]).sort((a, b) => a[0] - b[0]),
    [
      [9, 0.5],
      [10, 0.5],
    ],
  );

  const horiz = centerlineCellWeights(5.4, 10, 100, 100);
  assert.equal(horiz.length, 2);
  assert.deepEqual(
    horiz.map((c) => [c.row, c.weight]).sort((a, b) => a[0] - b[0]),
    [
      [9, 0.5],
      [10, 0.5],
    ],
  );

  // Cell interior → full credit for that cell only.
  const interior = centerlineCellWeights(5.4, 7.4, 100, 100);
  assert.deepEqual(interior, [{ row: 7, col: 5, weight: 1 }]);

  // Slightly off a vertical line still splits left/right (geodesic drift).
  const drifted = centerlineCellWeights(10.0003, 5.4, 100, 100);
  assert.equal(drifted.length, 2);
  const total = drifted.reduce((s, c) => s + c.weight, 0);
  assert.ok(Math.abs(total - 1) < 1e-9);
});

test("rosePolygon collapses unreached tips to the origin", () => {
  const origin = { lat: 40, lon: -74 };
  const rays = [
    { bearingDeg: 0, reached: true, lengthM: 1000 },
    { bearingDeg: 90, reached: false, lengthM: 1e7 },
    { bearingDeg: 180, reached: true, lengthM: 1000 },
    { bearingDeg: 270, reached: false, lengthM: 1e7 },
  ];
  const ring = rosePolygon(origin, rays, (ray) =>
    ray.reached ? ray.lengthM : 0,
  );
  // Unreached bearings sit on the pin — no floating tip-only polygon.
  assert.deepEqual(ring[1], [origin.lat, origin.lon]);
  assert.deepEqual(ring[3], [origin.lat, origin.lon]);
  assert.notDeepEqual(ring[0], [origin.lat, origin.lon]);
});

test("pickGrid prefers finer cell size", () => {
  const coarse = createGrid(
    {
      west: -75,
      south: 40,
      north: 41,
      east: -74,
      cellDeg: 0.02,
      width: 50,
      height: 50,
    },
    new Float32Array(50 * 50),
  );
  const fine = createGrid(
    {
      west: -75,
      south: 40,
      north: 41,
      east: -74,
      cellDeg: 0.005,
      width: 200,
      height: 200,
    },
    new Float32Array(200 * 200),
  );
  const picked = pickGrid([coarse, fine], 40.5, -74.5);
  assert.equal(picked.meta.cellDeg, 0.005);
});
