import test from "node:test";
import assert from "node:assert/strict";
import { createGrid, pickGrid } from "../src/grid.js";
import {
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
