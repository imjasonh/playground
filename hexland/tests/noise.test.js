import test from "node:test";
import assert from "node:assert/strict";

import { mulberry32 } from "../src/terrain.js";
import { createPerlin2D, fbm2D } from "../src/noise.js";

test("createPerlin2D is deterministic for a seed", () => {
  const a = createPerlin2D(mulberry32(42));
  const b = createPerlin2D(mulberry32(42));
  const c = createPerlin2D(mulberry32(43));
  assert.equal(a(1.25, 3.5), b(1.25, 3.5));
  assert.notEqual(a(1.25, 3.5), c(1.25, 3.5));
});

test("Perlin and fbm stay finite across a grid", () => {
  const noise = createPerlin2D(mulberry32(7));
  let min = Infinity;
  let max = -Infinity;
  for (let x = 0; x < 8; x += 0.5) {
    for (let y = 0; y < 8; y += 0.5) {
      const n = noise(x, y);
      const f = fbm2D(noise, x * 0.1, y * 0.1);
      assert.equal(Number.isFinite(n), true);
      assert.equal(Number.isFinite(f), true);
      min = Math.min(min, n, f);
      max = Math.max(max, n, f);
    }
  }
  assert.ok(max > min);
  assert.ok(min >= -2 && max <= 2);
});
