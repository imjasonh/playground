import test from "node:test";
import assert from "node:assert/strict";
import { createGrid, pickGrid } from "../src/grid.js";
import {
  computeRose,
  distanceToPeople,
  peopleInCorridor,
  rosePolygon,
  scaledLengths,
} from "../src/rays.js";
import { feetToMeters, milesToMeters } from "../src/geo.js";

/** Build a tiny synthetic grid: dense east band, sparse west. */
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
      // Dense only well into the eastern third.
      data[r * width + c] = c >= 40 ? 20_000 : 20;
    }
  }
  return createGrid(
    { west, south, north, east: west + width * cellDeg, cellDeg, width, height },
    data,
  );
}

/** Origin in the sparse west, clearly left of the dense band. */
const ORIGIN = { lat: 40.7, lon: -74.2 };

test("peopleInCorridor finds more people toward the dense side", () => {
  const grid = makeAsymmetricGrid();
  assert.ok(grid.contains(ORIGIN.lat, ORIGIN.lon));
  const widthM = feetToMeters(100);
  const lengthM = milesToMeters(25);
  const east = peopleInCorridor(grid, ORIGIN, 90, lengthM, widthM, { stepM: 100 });
  const west = peopleInCorridor(grid, ORIGIN, 270, lengthM, widthM, { stepM: 100 });
  assert.ok(east > west * 3, `east ${east} should dwarf west ${west}`);
});

test("peopleInCorridor is roughly linear in width", () => {
  const grid = makeAsymmetricGrid();
  const lengthM = milesToMeters(12);
  const a = peopleInCorridor(grid, ORIGIN, 90, lengthM, 30, { stepM: 100 });
  const b = peopleInCorridor(grid, ORIGIN, 90, lengthM, 60, { stepM: 100 });
  assert.ok(Math.abs(b / a - 2) < 0.08, `ratio ${b / a}`);
});

test("distanceToPeople is shorter toward dense cells", () => {
  const grid = makeAsymmetricGrid();
  const widthM = feetToMeters(100);
  const maxLengthM = milesToMeters(40);
  const target = 2_000;
  const east = distanceToPeople(grid, ORIGIN, 90, target, widthM, maxLengthM, {
    stepM: 100,
  });
  const west = distanceToPeople(grid, ORIGIN, 270, target, widthM, maxLengthM, {
    stepM: 100,
  });
  assert.ok(Number.isFinite(east), `east distance ${east}`);
  assert.ok(east < west, `east ${east} should be < west ${west}`);
});

test("computeRose fixedLength marks east stronger than west", () => {
  const grid = makeAsymmetricGrid();
  const rays = computeRose(grid, ORIGIN, {
    mode: "fixedLength",
    widthM: feetToMeters(100),
    lengthM: milesToMeters(25),
    rayCount: 36,
    stepM: 150,
  });
  assert.equal(rays.length, 36);
  const east = rays.find((r) => r.bearingDeg === 90);
  const west = rays.find((r) => r.bearingDeg === 270);
  assert.ok(east && west);
  assert.ok(
    east.people > west.people * 3,
    `east ${east.people} vs west ${west.people}`,
  );
});

test("scaledLengths normalizes peak to maxLength", () => {
  const lengths = scaledLengths(
    [
      { people: 10 },
      { people: 50 },
      { people: 0 },
    ],
    1000,
  );
  assert.equal(lengths[1], 1000);
  assert.equal(lengths[0], 200);
  assert.equal(lengths[2], 0);
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
