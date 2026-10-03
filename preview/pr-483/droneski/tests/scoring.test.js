import { test } from 'node:test';
import assert from 'node:assert/strict';
import {
  createScoreState,
  updateScoreState,
  getRatingColor,
} from '../src/scoring.js';
import { clamp, lerp } from '../src/utils.js';

test('clamp restricts to [min, max]', () => {
  assert.equal(clamp(5, 0, 10), 5);
  assert.equal(clamp(-1, 0, 10), 0);
  assert.equal(clamp(11, 0, 10), 10);
});

test('lerp interpolates linearly', () => {
  assert.equal(lerp(0, 10, 0), 0);
  assert.equal(lerp(0, 10, 1), 10);
  assert.equal(lerp(0, 10, 0.5), 5);
});

test('createScoreState starts at zero', () => {
  const s = createScoreState();
  assert.equal(s.total, 0);
  assert.equal(s.frameCount, 0);
  assert.equal(s.centeringSum, 0);
});

test('updateScoreState accumulates weighted totals', () => {
  const s = createScoreState();
  updateScoreState(s, {
    centering: 1,
    visibility: 1,
    distance: 1,
    smoothness: 1,
    frameTotal: 1,
  });
  assert.equal(s.frameCount, 1);
  assert.equal(s.centeringSum, 1);
  assert.equal(s.total, 10);
});

test('getRatingColor thresholds', () => {
  assert.equal(getRatingColor(0.9), '#ffdd00');
  assert.equal(getRatingColor(0.75), '#44ff44');
  assert.equal(getRatingColor(0.55), '#88ccff');
  assert.equal(getRatingColor(0.35), '#ffaa44');
  assert.equal(getRatingColor(0.1), '#ff4444');
});
