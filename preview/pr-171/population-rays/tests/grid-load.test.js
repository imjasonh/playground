import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";
import { loadGridFromGzip, gridsForRose, pickGridForTarget } from "../src/grid.js";
import {
  bearingBetween,
  computeRose,
  distanceToPeople,
  peopleInSlice,
} from "../src/rays.js";
import { formatDistance, milesToMeters } from "../src/geo.js";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const SLICE = 2;

test("loads packaged CONUS grid and samples Times Square", async () => {
  const meta = JSON.parse(
    readFileSync(join(root, "data/conus-0p02.json"), "utf8"),
  );
  const gz = readFileSync(join(root, "data/conus-0p02.f32.gz"));
  const grid = await loadGridFromGzip(meta, gz);
  assert.equal(grid.meta.width, 2950);
  const midtown = grid.sample(40.758, -73.985);
  assert.ok(midtown > 10_000, `expected dense midtown cell, got ${midtown}`);
});

test("Times Square landward slice beats due west over water", async () => {
  const meta = JSON.parse(
    readFileSync(join(root, "data/northeast-0p005.json"), "utf8"),
  );
  const grid = await loadGridFromGzip(
    meta,
    readFileSync(join(root, "data/northeast-0p005.f32.gz")),
  );
  const origin = { lat: 40.758, lon: -73.9855 };
  const lengthM = milesToMeters(20);
  const west = peopleInSlice(grid, origin, 270, lengthM, SLICE);
  const nne = peopleInSlice(grid, origin, 30, lengthM, SLICE);
  assert.ok(
    nne > west,
    `expected NNE (${nne}) > W (${west}) from Times Square`,
  );
});

test("rose grids list fine Northeast then CONUS in NYC", async () => {
  const conus = await loadGridFromGzip(
    JSON.parse(readFileSync(join(root, "data/conus-0p02.json"), "utf8")),
    readFileSync(join(root, "data/conus-0p02.f32.gz")),
  );
  const ne = await loadGridFromGzip(
    JSON.parse(readFileSync(join(root, "data/northeast-0p005.json"), "utf8")),
    readFileSync(join(root, "data/northeast-0p005.f32.gz")),
  );
  const o = { lat: 40.706, lon: -74.012 };
  const grids = gridsForRose([conus, ne], o.lat, o.lon);
  assert.deepEqual(
    grids.map((g) => g.meta.key),
    ["northeast-0p005", "conus-0p02"],
  );
  assert.equal(
    pickGridForTarget([conus, ne], o.lat, o.lon, 100_000).meta.key,
    "northeast-0p005",
  );
});

test("Manhattan 2° slice toward Chicago reaches 350k before the Pacific", async () => {
  const conus = await loadGridFromGzip(
    JSON.parse(readFileSync(join(root, "data/conus-0p02.json"), "utf8")),
    readFileSync(join(root, "data/conus-0p02.f32.gz")),
  );
  const ne = await loadGridFromGzip(
    JSON.parse(readFileSync(join(root, "data/northeast-0p005.json"), "utf8")),
    readFileSync(join(root, "data/northeast-0p005.f32.gz")),
  );
  const o = { lat: 40.758, lon: -73.9855 };
  const chicagoBearing = bearingBetween(o, 41.8781, -87.6298);
  const rayBearing = Math.round(chicagoBearing / 2) * 2;
  const dist = distanceToPeople(
    [ne, conus],
    o,
    rayBearing,
    350_000,
    SLICE,
    milesToMeters(3000),
  );
  assert.ok(Number.isFinite(dist), `should reach 350k toward Chicago, got ${dist}`);
  // Chicago is ~711 mi away; a 2° slice should still hit 350k before that.
  assert.ok(
    dist < milesToMeters(711),
    `expected under Chicago distance, got ${formatDistance(dist)}`,
  );
});

test("Manhattan rose with 2° slices reaches most bearings at 100k", async () => {
  const conus = await loadGridFromGzip(
    JSON.parse(readFileSync(join(root, "data/conus-0p02.json"), "utf8")),
    readFileSync(join(root, "data/conus-0p02.f32.gz")),
  );
  const ne = await loadGridFromGzip(
    JSON.parse(readFileSync(join(root, "data/northeast-0p005.json"), "utf8")),
    readFileSync(join(root, "data/northeast-0p005.f32.gz")),
  );
  const o = { lat: 40.758, lon: -73.9855 };
  const rose = computeRose([ne, conus], o, {
    sliceDeg: SLICE,
    targetPeople: 100_000,
    maxLengthM: milesToMeters(3000),
    rayCount: 180,
  });
  const reached = rose.filter((r) => r.reached);
  assert.ok(
    reached.length >= 140,
    `expected most slices to hit 100k, got ${reached.length}/180`,
  );
});

test("Manhattan reaches 500k much sooner than Wyoming", async () => {
  const conus = await loadGridFromGzip(
    JSON.parse(readFileSync(join(root, "data/conus-0p02.json"), "utf8")),
    readFileSync(join(root, "data/conus-0p02.f32.gz")),
  );
  const target = 500_000;
  const maxM = milesToMeters(3000);
  const manhattan = { lat: 40.758, lon: -73.9855 };
  const wyoming = { lat: 43.076, lon: -107.2903 };

  // Due east through Queens/Long Island — dense near-field.
  const nycDist = distanceToPeople(conus, manhattan, 90, target, SLICE, maxM);
  const wyDist = distanceToPeople(conus, wyoming, 225, target, SLICE, maxM);

  assert.ok(Number.isFinite(nycDist), `NYC should reach 500k, got ${nycDist}`);
  assert.ok(
    nycDist < milesToMeters(80),
    `NYC 500k distance should be under 80 mi, got ${formatDistance(nycDist)}`,
  );
  assert.ok(
    !Number.isFinite(wyDist) || wyDist > milesToMeters(200),
    `Wyoming should need hundreds of miles or go unreached, got ${formatDistance(wyDist)}`,
  );
});

test("Wyoming southwest slice through LA reaches 500k", async () => {
  const conus = await loadGridFromGzip(
    JSON.parse(readFileSync(join(root, "data/conus-0p02.json"), "utf8")),
    readFileSync(join(root, "data/conus-0p02.f32.gz")),
  );
  const wyoming = { lat: 43.076, lon: -107.2903 };
  const dist = distanceToPeople(
    conus,
    wyoming,
    225,
    500_000,
    SLICE,
    milesToMeters(3000),
  );
  assert.ok(Number.isFinite(dist), "expected to reach 500k toward LA");
  assert.ok(
    dist < milesToMeters(1000),
    `LA-ward distance should be under 1000 mi, got ${formatDistance(dist)}`,
  );
});

test("wider slice shortens Wyoming distance to 200k", async () => {
  const conus = await loadGridFromGzip(
    JSON.parse(readFileSync(join(root, "data/conus-0p02.json"), "utf8")),
    readFileSync(join(root, "data/conus-0p02.f32.gz")),
  );
  // Sparse origin: angular width matters more than near a metro core.
  const origin = { lat: 43.076, lon: -107.2903 };
  const maxM = milesToMeters(3000);
  const thin = distanceToPeople(conus, origin, 225, 200_000, 2, maxM);
  const fat = distanceToPeople(conus, origin, 225, 200_000, 15, maxM);
  assert.ok(Number.isFinite(thin) && Number.isFinite(fat));
  assert.ok(
    fat < thin * 0.85,
    `15° (${formatDistance(fat)}) should beat 2° (${formatDistance(thin)})`,
  );
});
