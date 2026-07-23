import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";
import { loadGridFromGzip, pickGridForTarget } from "../src/grid.js";
import { distanceToPeople, peopleInCorridor } from "../src/rays.js";
import { feetToMeters, formatDistance, milesToMeters } from "../src/geo.js";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const WIDTH = feetToMeters(500);

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

test("Times Square landward corridor beats due west over water", async () => {
  const meta = JSON.parse(
    readFileSync(join(root, "data/northeast-0p005.json"), "utf8"),
  );
  const grid = await loadGridFromGzip(
    meta,
    readFileSync(join(root, "data/northeast-0p005.f32.gz")),
  );
  const origin = { lat: 40.758, lon: -73.9855 };
  const lengthM = milesToMeters(20);
  const west = peopleInCorridor(grid, origin, 270, lengthM, WIDTH);
  // NNE stays over dense boroughs; due west hits the Hudson quickly.
  const nne = peopleInCorridor(grid, origin, 30, lengthM, WIDTH);
  assert.ok(
    nne > west,
    `expected NNE (${nne}) > W (${west}) from Times Square`,
  );
});

test("100k target uses fine Northeast grid in NYC", async () => {
  const conus = await loadGridFromGzip(
    JSON.parse(readFileSync(join(root, "data/conus-0p02.json"), "utf8")),
    readFileSync(join(root, "data/conus-0p02.f32.gz")),
  );
  const ne = await loadGridFromGzip(
    JSON.parse(readFileSync(join(root, "data/northeast-0p005.json"), "utf8")),
    readFileSync(join(root, "data/northeast-0p005.f32.gz")),
  );
  const o = { lat: 40.706, lon: -74.012 };
  assert.equal(
    pickGridForTarget([conus, ne], o.lat, o.lon, 100_000).meta.key,
    "northeast-0p005",
  );
  assert.equal(
    pickGridForTarget([conus, ne], o.lat, o.lon, 1_000_000).meta.key,
    "conus-0p02",
  );
});

test("Manhattan reaches 1M much sooner than Wyoming", async () => {
  const conus = await loadGridFromGzip(
    JSON.parse(readFileSync(join(root, "data/conus-0p02.json"), "utf8")),
    readFileSync(join(root, "data/conus-0p02.f32.gz")),
  );
  const target = 1_000_000;
  const maxM = milesToMeters(3000);
  const manhattan = { lat: 40.758, lon: -73.9855 };
  const wyoming = { lat: 43.076, lon: -107.2903 };

  const nycDist = distanceToPeople(conus, manhattan, 28, target, WIDTH, maxM);
  const wyDist = distanceToPeople(conus, wyoming, 84, target, WIDTH, maxM);

  assert.ok(Number.isFinite(nycDist), `NYC should reach 1M, got ${nycDist}`);
  assert.ok(
    nycDist < milesToMeters(50),
    `NYC 1M distance should be under 50 mi, got ${formatDistance(nycDist)}`,
  );
  // Sparse corridors often never hit 1M within CONUS (Infinity). That still
  // counts as "much farther" than Manhattan's few miles.
  assert.ok(
    !Number.isFinite(wyDist) || wyDist > milesToMeters(500),
    `Wyoming should need hundreds of miles or go unreached, got ${formatDistance(wyDist)}`,
  );
  if (Number.isFinite(wyDist)) {
    assert.ok(wyDist > nycDist * 20);
  }
});

test("wider corridor shortens Manhattan distance to 1M", async () => {
  const conus = await loadGridFromGzip(
    JSON.parse(readFileSync(join(root, "data/conus-0p02.json"), "utf8")),
    readFileSync(join(root, "data/conus-0p02.f32.gz")),
  );
  const origin = { lat: 40.758, lon: -73.9855 };
  const maxM = milesToMeters(3000);
  const thin = distanceToPeople(
    conus,
    origin,
    28,
    1_000_000,
    feetToMeters(500),
    maxM,
  );
  const fat = distanceToPeople(
    conus,
    origin,
    28,
    1_000_000,
    milesToMeters(5),
    maxM,
  );
  assert.ok(Number.isFinite(thin) && Number.isFinite(fat));
  assert.ok(
    fat < thin * 0.6,
    `5 mi wide (${formatDistance(fat)}) should beat 500 ft (${formatDistance(thin)})`,
  );
});
