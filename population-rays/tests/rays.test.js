import test from "node:test";
import assert from "node:assert/strict";
import { createGrid, pickGrid } from "../src/grid.js";
import {
  bearingBetween,
  cellsInSector,
  computeRose,
  deltaBearingDeg,
  distanceToPeople,
  peopleInSlice,
  probeRay,
  rosePolygon,
} from "../src/rays.js";
import { milesToMeters } from "../src/geo.js";

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
const SLICE = 2;

test("peopleInSlice finds more people toward the dense side", () => {
  const grid = makeAsymmetricGrid();
  const lengthM = milesToMeters(25);
  const east = peopleInSlice(grid, ORIGIN, 90, lengthM, SLICE);
  const west = peopleInSlice(grid, ORIGIN, 270, lengthM, SLICE);
  assert.ok(east > west * 3, `east ${east} should dwarf west ${west}`);
});

test("wider slice collects at least as many people", () => {
  const grid = makeAsymmetricGrid();
  const lengthM = milesToMeters(20);
  const narrow = peopleInSlice(grid, ORIGIN, 90, lengthM, 2);
  const wide = peopleInSlice(grid, ORIGIN, 90, lengthM, 15);
  assert.ok(wide > narrow, `wide ${wide} should beat narrow ${narrow}`);
});

test("wider slice reaches a target sooner", () => {
  const grid = makeAsymmetricGrid();
  const maxLengthM = milesToMeters(40);
  const target = 100_000;
  const thin = distanceToPeople(grid, ORIGIN, 90, target, 2, maxLengthM);
  const fat = distanceToPeople(grid, ORIGIN, 90, target, 15, maxLengthM);
  assert.ok(Number.isFinite(thin) && Number.isFinite(fat));
  assert.ok(fat < thin, `fat ${fat} should be shorter than thin ${thin}`);
});

test("distanceToPeople is shorter toward dense cells", () => {
  const grid = makeAsymmetricGrid();
  const maxLengthM = milesToMeters(40);
  const target = 100_000;
  const east = distanceToPeople(grid, ORIGIN, 90, target, SLICE, maxLengthM);
  const west = distanceToPeople(grid, ORIGIN, 270, target, SLICE, maxLengthM);
  assert.ok(Number.isFinite(east), `east distance ${east}`);
  assert.ok(east < west, `east ${east} should be < west ${west}`);
});

test("computeRose marks east reached sooner than west", () => {
  const grid = makeAsymmetricGrid();
  const rays = computeRose(grid, ORIGIN, {
    sliceDeg: SLICE,
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

test("probeRay reports people when unreached", () => {
  const grid = makeAsymmetricGrid();
  const ray = probeRay(
    grid,
    ORIGIN,
    270,
    50_000_000,
    SLICE,
    milesToMeters(25),
  );
  assert.equal(ray.reached, false);
  assert.ok(ray.people > 0, "should count people in the short slice");
  assert.ok(ray.people < 50_000_000);
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
  assert.deepEqual(ring[1], [origin.lat, origin.lon]);
  assert.deepEqual(ring[3], [origin.lat, origin.lon]);
  assert.notDeepEqual(ring[0], [origin.lat, origin.lon]);
});

test("deltaBearingDeg wraps across 0°", () => {
  assert.ok(Math.abs(deltaBearingDeg(10, 350) - 20) < 1e-9);
  assert.ok(Math.abs(deltaBearingDeg(350, 10) - -20) < 1e-9);
});

test("bearingBetween NYC toward Chicago is ~281°", () => {
  const o = { lat: 40.758, lon: -73.9855 };
  const br = bearingBetween(o, 41.8781, -87.6298);
  assert.ok(br > 275 && br < 285, `got ${br}`);
});

test("cellsInSector includes a cell on the bearing and skips off-slice", () => {
  const grid = makeAsymmetricGrid();
  const on = cellsInSector(grid, ORIGIN, 90, 5, milesToMeters(10));
  const off = cellsInSector(grid, ORIGIN, 0, 5, milesToMeters(10));
  assert.ok(on.length > 0);
  // Due-north slice from this origin stays over sparse western cells.
  const onPop = on.reduce((s, h) => s + h.pop, 0);
  const offPop = off.reduce((s, h) => s + h.pop, 0);
  assert.ok(onPop > offPop);
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
