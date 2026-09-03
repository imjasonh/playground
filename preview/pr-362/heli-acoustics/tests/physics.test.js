import { test } from 'node:test';
import assert from 'node:assert/strict';
import {
  airAbsorptionDbPerMeter,
  airGain,
  applyAirToBands,
} from '../src/airAbsorption.js';
import { fresnelNumber, maekawaInsertionLossDb, maekawaAmplitude } from '../src/maekawa.js';
import {
  pressureReflection,
  bounceBands,
  MATERIALS,
  sphericalPressureGain,
  unitBands,
} from '../src/materials.js';
import { occlusionAmount, isOccluded } from '../src/occlusion.js';
import { BUILDINGS } from '../src/city.js';

test('ISO 9613-1 air absorption rises with frequency', () => {
  const a250 = airAbsorptionDbPerMeter(250);
  const a1k = airAbsorptionDbPerMeter(1000);
  const a4k = airAbsorptionDbPerMeter(4000);
  assert.ok(a1k > a250, `1 kHz ${a1k} vs 250 Hz ${a250}`);
  assert.ok(a4k > a1k, `4 kHz ${a4k} vs 1 kHz ${a1k}`);
  // ~5 dB/km at 1 kHz, 20 °C, 50 % RH (ISO 9613-1 table order of magnitude).
  const dbPerKm = a1k * 1000;
  assert.ok(dbPerKm > 2 && dbPerKm < 12, `1 kHz α=${dbPerKm.toFixed(2)} dB/km`);
});

test('air gain attenuates long paths more at high frequency', () => {
  const g = applyAirToBands(unitBands(), 200);
  assert.ok(g.high < g.low);
  assert.ok(airGain(200, 4000) < airGain(200, 250));
});

test('Maekawa IL is 0 in illuminated zone and rises in shadow', () => {
  assert.equal(maekawaInsertionLossDb(-1), 0);
  assert.equal(maekawaInsertionLossDb(0), 0);
  const il = maekawaInsertionLossDb(fresnelNumber(2, 1000));
  assert.ok(il > 5 && il <= 25);
  assert.ok(maekawaAmplitude(2, 1000) < 1);
});

test('Allen-Berkley β = √(1−α); bounce does not double-count R', () => {
  const a = MATERIALS.asphalt.absorb.mid;
  assert.ok(Math.abs(pressureReflection(a) - Math.sqrt(1 - a)) < 1e-12);
  const b = bounceBands(unitBands(), MATERIALS.asphalt);
  assert.ok(b.high < b.low);
  assert.ok(b.mid < 1);
});

test('spherical pressure gain is 1/R', () => {
  assert.equal(sphericalPressureGain(10), 0.1);
  assert.equal(sphericalPressureGain(0), 1);
});

test('soft occlusion is continuous in shadow and zero in open air', () => {
  const open = occlusionAmount([0, 1.7, 0], [0, 80, -90], BUILDINGS);
  assert.equal(open, 0);
  const nw = BUILDINGS.find((b) => b.id === 'nw');
  const listener = [0, 1.7, (nw.min[2] + nw.max[2]) / 2];
  const source = [nw.min[0] - 40, 60, listener[2]];
  assert.equal(isOccluded(listener, source, BUILDINGS), true);
  const soft = occlusionAmount(listener, source, BUILDINGS);
  assert.ok(soft > 0.2 && soft <= 1, `soft occlusion=${soft}`);
});
