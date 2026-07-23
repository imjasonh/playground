import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";
import { loadGridFromGzip } from "../src/grid.js";
import { peopleInCorridor } from "../src/rays.js";
import { feetToMeters, milesToMeters } from "../src/geo.js";

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

test("Times Square SE corridor beats due west (Manhattan story)", async () => {
  const meta = JSON.parse(
    readFileSync(join(root, "data/northeast-0p005.json"), "utf8"),
  );
  const gz = readFileSync(join(root, "data/northeast-0p005.f32.gz"));
  const grid = await loadGridFromGzip(meta, gz);
  const origin = { lat: 40.758, lon: -73.9855 };
  const widthM = feetToMeters(100);
  const lengthM = milesToMeters(20);
  const west = peopleInCorridor(grid, origin, 270, lengthM, widthM, {
    stepM: 200,
  });
  const southeast = peopleInCorridor(grid, origin, 135, lengthM, widthM, {
    stepM: 200,
  });
  assert.ok(
    southeast > west,
    `expected SE (${southeast}) > W (${west}) from Times Square`,
  );
});
