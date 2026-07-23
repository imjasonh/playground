import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";
import { loadGridFromGzip } from "../src/grid.js";
import { distanceToPeople, peopleAlongLine } from "../src/rays.js";
import { formatDistance, milesToMeters } from "../src/geo.js";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");

test("loads packaged CONUS grid and samples Times Square", async () => {
  const meta = JSON.parse(
    readFileSync(join(root, "data/conus-0p02.json"), "utf8"),
  );
  const gz = readFileSync(join(root, "data/conus-0p02.f32.gz"));
  const grid = await loadGridFromGzip(meta, gz);
  assert.equal(grid.meta.width, 2950);
  assert.equal(grid.meta.height, 1300);
  const midtown = grid.sample(40.758, -73.985);
  assert.ok(midtown > 10_000, `expected dense midtown cell, got ${midtown}`);
  const ocean = grid.sample(40.75, -74.5);
  assert.ok(ocean < midtown / 10);
});

test("Times Square SE crosses more people than due west", async () => {
  const meta = JSON.parse(
    readFileSync(join(root, "data/northeast-0p005.json"), "utf8"),
  );
  const gz = readFileSync(join(root, "data/northeast-0p005.f32.gz"));
  const grid = await loadGridFromGzip(meta, gz);
  const origin = { lat: 40.758, lon: -73.9855 };
  const lengthM = milesToMeters(20);
  const west = peopleAlongLine(grid, origin, 270, lengthM, { stepM: 200 });
  const southeast = peopleAlongLine(grid, origin, 135, lengthM, {
    stepM: 200,
  });
  assert.ok(
    southeast > west,
    `expected SE (${southeast}) > W (${west}) from Times Square`,
  );
});

test("Manhattan reaches 1M much sooner than Wyoming", async () => {
  const conusMeta = JSON.parse(
    readFileSync(join(root, "data/conus-0p02.json"), "utf8"),
  );
  const conus = await loadGridFromGzip(
    conusMeta,
    readFileSync(join(root, "data/conus-0p02.f32.gz")),
  );

  const target = 1_000_000;
  const maxM = milesToMeters(3000);
  const manhattan = { lat: 40.758, lon: -73.9855 };
  const wyoming = { lat: 43.076, lon: -107.2903 };

  // NNE from Midtown stays over dense land; due-east Wyoming is sparse.
  const nycDist = distanceToPeople(conus, manhattan, 28, target, 0, maxM, {
    stepM: 1000,
  });
  const wyDist = distanceToPeople(conus, wyoming, 84, target, 0, maxM, {
    stepM: 1000,
  });

  assert.ok(Number.isFinite(nycDist), `NYC should reach 1M, got ${nycDist}`);
  assert.ok(
    nycDist < milesToMeters(50),
    `NYC 1M distance should be under 50 mi, got ${formatDistance(nycDist)}`,
  );
  assert.ok(
    Number.isFinite(wyDist) && wyDist > milesToMeters(500),
    `Wyoming should need hundreds of miles (${formatDistance(wyDist)})`,
  );
  assert.ok(
    wyDist > nycDist * 20,
    `Wyoming (${formatDistance(wyDist)}) should dwarf NYC (${formatDistance(nycDist)})`,
  );
});
