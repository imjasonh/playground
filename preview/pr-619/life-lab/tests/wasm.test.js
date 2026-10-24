// Tests against the real wasm module (same artifact the browser loads).
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

import init, { simulate, export_stl, export_3mf, pattern_cells } from '../vendor/life_stl/life_stl.js';

const wasmBytes = readFileSync(
  fileURLToPath(new URL('../vendor/life_stl/life_stl_bg.wasm', import.meta.url)),
);
await init({ module_or_path: wasmBytes });

function gliderCells(w, h) {
  const cells = new Uint8Array(w * h);
  // Glider at (1,1): .O. / ..O / OOO
  for (const [x, y] of [[2, 1], [3, 2], [1, 3], [2, 3], [3, 3]]) cells[y * w + x] = 1;
  return cells;
}

test('pattern_cells returns catalogued seeds', () => {
  const acorn = pattern_cells('acorn', 44, 44, 1, 0);
  assert.equal(acorn.length, 44 * 44);
  assert.equal(acorn.reduce((a, b) => a + b, 0), 7, 'acorn has 7 cells');

  const glider = pattern_cells('glider', 16, 16, 1, 0);
  assert.equal(glider.reduce((a, b) => a + b, 0), 5, 'glider has 5 cells');

  const soupA = pattern_cells('soup', 24, 24, 42, 0.2);
  const soupB = pattern_cells('soup', 24, 24, 42, 0.2);
  assert.deepEqual(soupA, soupB, 'soups are seed-deterministic');
  assert.ok(soupA.reduce((a, b) => a + b, 0) > 40, 'soup is populated');

  assert.throws(() => pattern_cells('nonsense', 10, 10, 1, 0));
});

test('simulate: glider stays interesting and one piece', () => {
  const w = 16, h = 16, depth = 24;
  const result = simulate(gliderCells(w, h), w, h, depth);

  assert.ok(result.interesting, 'glider never settles inside the stack');
  assert.equal(result.period, 0);
  assert.ok(result.one_piece, 'causality braces make one piece');
  assert.ok(result.life_voxels >= depth * 4, 'roughly 5 cells per generation');
  assert.ok(result.brace_count > 0, 'moving pattern needs braces');

  const voxels = result.voxels;
  assert.equal(voxels.length, result.life_voxels * 3);
  // Base layer occupies z=0; life starts at z=1.
  const zs = [];
  for (let i = 2; i < voxels.length; i += 3) zs.push(voxels[i]);
  assert.equal(Math.min(...zs), 1);
  assert.equal(Math.max(...zs), depth);

  const base = result.base;
  assert.equal(base.length, 5, 'base bbox (x0,y0,x1,y1,layers)');
  assert.equal(base[4], 1, 'one base layer');

  assert.equal(result.braces.length, result.brace_count * 6);
});

test('simulate: block is boring (settles immediately)', () => {
  const w = 12, h = 12, depth = 16;
  const cells = new Uint8Array(w * h);
  for (const [x, y] of [[5, 5], [6, 5], [5, 6], [6, 6]]) cells[y * w + x] = 1;
  const result = simulate(cells, w, h, depth);
  assert.ok(!result.interesting);
  assert.equal(result.period, 1, 'still life');
  assert.equal(result.quiescent_generation, 0);
});

test('export_stl produces a valid binary STL', () => {
  const w = 16, h = 16, depth = 20;
  const bytes = export_stl(gliderCells(w, h), w, h, depth, 4.0);
  assert.ok(bytes.length > 84);
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const triangles = view.getUint32(80, true);
  assert.equal(bytes.length, 84 + triangles * 50, 'length matches header count');
  assert.ok(triangles > 100);
});

test('export_3mf produces a Bambu project zip', () => {
  const w = 16, h = 16, depth = 20;
  const bytes = export_3mf(gliderCells(w, h), w, h, depth, 4.0, 'test-glider');
  // ZIP local-file-header magic.
  assert.deepEqual([...bytes.slice(0, 4)], [0x50, 0x4b, 0x03, 0x04]);
  const text = Buffer.from(bytes).toString('latin1');
  assert.ok(text.includes('3D/3dmodel.model'));
  assert.ok(text.includes('Metadata/project_settings.config'));
  assert.ok(text.includes('Metadata/slice_info.config'));
});

test('simulate rejects mismatched input', () => {
  assert.throws(() => simulate(new Uint8Array(10), 16, 16, 8));
  assert.throws(() => export_stl(new Uint8Array(16 * 16), 16, 16, 8, 0.5), /cell size/);
});
