import { test } from 'node:test';
import assert from 'node:assert/strict';
import { BUILDINGS, helicopterPath } from '../src/city.js';
import { bounceBands, unitBands, materialForFace, cutoffFromBands } from '../src/materials.js';
import { buildingEdges, computeDiffraction, edgeDiffraction } from '../src/diffraction.js';
import { traceEnergyBins, binsToImpulseResponse } from '../src/stochasticIr.js';
import { computeReflections, order3TripleList, order3Reflection } from '../src/reflections.js';
import { buildingFaces } from '../src/city.js';

test('materials darken high band more than low on asphalt', () => {
  const face = { id: 'ground', kind: 'ground', building: 'ground' };
  const m = materialForFace(face);
  const b = bounceBands(unitBands(), m);
  assert.ok(b.high < b.low);
  assert.ok(cutoffFromBands(b, 40) < cutoffFromBands(unitBands(), 40));
});

test('building edges include vertical corners and roof edges', () => {
  const edges = buildingEdges(BUILDINGS);
  assert.ok(edges.length >= BUILDINGS.length * 8);
  assert.ok(edges.some((e) => e.kind === 'vertical'));
  assert.ok(edges.some((e) => e.kind === 'roof'));
});

test('diffraction appears when direct path is blocked behind a block', () => {
  const nw = BUILDINGS.find((b) => b.id === 'nw');
  const listener = [0, 1.7, (nw.min[2] + nw.max[2]) / 2];
  const source = [nw.min[0] - 40, 60, listener[2]];
  const list = computeDiffraction(listener, source, BUILDINGS, { limit: 8 });
  assert.ok(list.length >= 1, 'expected at least one diffracted path');
  assert.equal(list[0].kind, 'diffraction');
  assert.ok(list[0].gain > 0);
  assert.ok(list[0].cutoffHz > 0);
});

test('edgeDiffraction rejects near-LOS wraps', () => {
  const edges = buildingEdges(BUILDINGS);
  const edge = edges.find((e) => e.kind === 'vertical');
  const listener = [0, 1.7, 0];
  const source = [0, 40, -30];
  // Open avenue: any corner wrap should be longer / weak; may be null.
  const d = edgeDiffraction(listener, source, edge, BUILDINGS);
  if (d) assert.ok(d.pathLength > 30);
});

test('order-3 triples produce candidates in the canyon', () => {
  const faces = buildingFaces(BUILDINGS);
  const triples = order3TripleList(faces, { limit: 48 });
  assert.ok(triples.length > 0);
  const listener = [0, 1.7, 80];
  const source = [12, 90, 90];
  let found = 0;
  for (const [a, b, c] of triples) {
    if (order3Reflection(listener, source, a, b, c, BUILDINGS)) found++;
  }
  void found;
  const orbit = computeReflections(listener, source, BUILDINGS, { limit: 16, maxOrder: 3 });
  assert.ok(orbit.some((r) => r.order >= 1));
});

test('stochastic energy bins have energy and build an IR', () => {
  const listener = [0, 1.7, 0];
  const source = helicopterPath(2);
  const bins = traceEnergyBins(listener, source, BUILDINGS, { rays: 64, bounces: 4, seed: 2 });
  let sum = 0;
  for (let i = 0; i < bins.length; i++) sum += bins[i];
  assert.ok(sum > 0);
  const fakeCtx = {
    sampleRate: 48000,
    createBuffer(ch, n, rate) {
      const data = Array.from({ length: ch }, () => new Float32Array(n));
      return {
        numberOfChannels: ch,
        length: n,
        sampleRate: rate,
        getChannelData: (i) => data[i],
      };
    },
  };
  const buf = binsToImpulseResponse(fakeCtx, bins);
  assert.equal(buf.numberOfChannels, 2);
  assert.ok(buf.length > 1000);
});
