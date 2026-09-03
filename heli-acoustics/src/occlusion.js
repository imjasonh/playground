// Soft occlusion via Maekawa barrier IL on the best wrapping edge.
// Binary isOccluded remains for specular visibility tests.

import { length, sub, add, scale } from './geometry.js';
import { buildingEdges, diffractionPoint } from './edges.js';
import { maekawaAmplitude, maekawaInsertionLossDb, fresnelNumber } from './maekawa.js';
import { BAND_HZ } from './airAbsorption.js';

export function rayAabb(origin, dir, box) {
  let tmin = 0;
  let tmax = Infinity;
  for (let i = 0; i < 3; i++) {
    const o = origin[i];
    const d = dir[i];
    const min = box.min[i];
    const max = box.max[i];
    if (Math.abs(d) < 1e-12) {
      if (o < min || o > max) return null;
      continue;
    }
    let t1 = (min - o) / d;
    let t2 = (max - o) / d;
    if (t1 > t2) {
      const tmp = t1;
      t1 = t2;
      t2 = tmp;
    }
    tmin = Math.max(tmin, t1);
    tmax = Math.min(tmax, t2);
    if (tmin > tmax) return null;
  }
  if (tmax < 0) return null;
  const t = tmin >= 0 ? tmin : tmax;
  return t >= 0 ? t : null;
}

export function isOccluded(listener, source, buildings) {
  const delta = sub(source, listener);
  const dist = length(delta);
  if (dist < 1e-6) return false;
  const dir = scale(delta, 1 / dist);
  const eps = 0.05;
  for (const b of buildings) {
    const t = rayAabb(listener, dir, b);
    if (t !== null && t > eps && t < dist - eps) return true;
  }
  return false;
}

/**
 * Best-edge path difference δ = R_edge − R_direct for Maekawa (m).
 * Returns 0 when LOS is clear.
 */
export function bestPathDifference(listener, source, buildings) {
  if (!isOccluded(listener, source, buildings)) return 0;
  const direct = length(sub(source, listener));
  const edges = buildingEdges(buildings);
  let bestDelta = Infinity;
  for (const edge of edges) {
    const p = diffractionPoint(source, listener, edge.a, edge.b);
    // Skip if either leg still punches through a different building.
    if (isOccluded(source, p, buildings) || isOccluded(p, listener, buildings)) continue;
    const pathLen = length(sub(p, source)) + length(sub(listener, p));
    const delta = pathLen - direct;
    if (delta > 0 && delta < bestDelta) bestDelta = delta;
  }
  if (!Number.isFinite(bestDelta)) {
    // Deeply enclosed: treat as large δ so Maekawa saturates.
    return 8;
  }
  return bestDelta;
}

/**
 * Occlusion amount in [0,1] from continuous Maekawa mid-band IL.
 * 0 = clear LOS, ~1 = deep shadow (IL ≈ 25 dB).
 */
export function occlusionAmount(listener, source, buildings) {
  const delta = bestPathDifference(listener, source, buildings);
  if (delta <= 0) return 0;
  const amp = maekawaAmplitude(delta, BAND_HZ.mid);
  return Math.max(0, Math.min(1, 1 - amp));
}

/** Mid-band Maekawa IL (dB) for HUD / debug. */
export function occlusionInsertionLossDb(listener, source, buildings) {
  const delta = bestPathDifference(listener, source, buildings);
  if (delta <= 0) return 0;
  return maekawaInsertionLossDb(fresnelNumber(delta, BAND_HZ.mid));
}

export function hitPoint(origin, dir, t) {
  return add(origin, scale(dir, t));
}
