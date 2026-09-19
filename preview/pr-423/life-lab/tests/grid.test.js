import { test } from 'node:test';
import assert from 'node:assert/strict';

import { makeCells, resizeCells, setCell, getCell, pointToCell, liveCount } from '../src/grid.js';

test('makeCells starts empty', () => {
  const cells = makeCells(8, 4);
  assert.equal(cells.length, 32);
  assert.equal(liveCount(cells), 0);
});

test('set/get round-trip', () => {
  const cells = makeCells(8, 8);
  setCell(cells, 8, 3, 2, true);
  assert.ok(getCell(cells, 8, 3, 2));
  assert.ok(!getCell(cells, 8, 2, 3));
  setCell(cells, 8, 3, 2, false);
  assert.equal(liveCount(cells), 0);
});

test('resize preserves top-left content', () => {
  const cells = makeCells(4, 4);
  setCell(cells, 4, 1, 1, true);
  setCell(cells, 4, 3, 3, true);

  const grown = resizeCells(cells, 4, 4, 6, 6);
  assert.ok(getCell(grown, 6, 1, 1));
  assert.ok(getCell(grown, 6, 3, 3));
  assert.equal(liveCount(grown), 2);

  const shrunk = resizeCells(grown, 6, 6, 2, 2);
  assert.ok(getCell(shrunk, 2, 1, 1));
  assert.equal(liveCount(shrunk), 1, 'cell at (3,3) cropped away');
});

test('pointToCell maps canvas coords to cells', () => {
  assert.deepEqual(pointToCell(0, 0, 240, 240, 24, 24), { x: 0, y: 0 });
  assert.deepEqual(pointToCell(239, 239, 240, 240, 24, 24), { x: 23, y: 23 });
  assert.deepEqual(pointToCell(125, 5, 240, 240, 24, 24), { x: 12, y: 0 });
  assert.equal(pointToCell(-1, 0, 240, 240, 24, 24), null);
  assert.equal(pointToCell(0, 300, 240, 240, 24, 24), null);
});
