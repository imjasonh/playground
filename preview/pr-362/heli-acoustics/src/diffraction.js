// Geometric edge diffraction for AABB buildings. When the direct path is
// blocked (or grazing), sound wraps around vertical corners and roof edges.
// This is a lightweight UTD-style path: source → closest edge point → listener,
// with legs checked for secondary occlusion.

import { add, sub, scale, length, dot, normalize } from './geometry.js';
import { isOccluded } from './occlusion.js';
import { SPEED_OF_SOUND } from './city.js';
import { MATERIALS, cutoffFromBands, gainFromBands } from './materials.js';

/**
 * Vertical corners + roof horizontal edges for each AABB.
 * @returns {Array<{ id: string, a: number[], b: number[], kind: string }>}
 */
export function buildingEdges(buildings) {
  const edges = [];
  for (const b of buildings) {
    const [x0, y0, z0] = b.min;
    const [x1, y1, z1] = b.max;
    const corners = [
      [x0, z0],
      [x0, z1],
      [x1, z0],
      [x1, z1],
    ];
    for (let i = 0; i < corners.length; i++) {
      const [x, z] = corners[i];
      edges.push({
        id: `${b.id}-v${i}`,
        kind: 'vertical',
        a: [x, y0, z],
        b: [x, y1, z],
      });
    }
    // Roof edges (horizontal).
    edges.push(
      { id: `${b.id}-rn`, kind: 'roof', a: [x0, y1, z0], b: [x1, y1, z0] },
      { id: `${b.id}-rs`, kind: 'roof', a: [x0, y1, z1], b: [x1, y1, z1] },
      { id: `${b.id}-rw`, kind: 'roof', a: [x0, y1, z0], b: [x0, y1, z1] },
      { id: `${b.id}-re`, kind: 'roof', a: [x1, y1, z0], b: [x1, y1, z1] },
    );
  }
  return edges;
}

/** Point on segment a→b that minimizes |source-P|+|P-listener| (clamped). */
export function diffractionPoint(source, listener, a, b) {
  const ab = sub(b, a);
  const abLen2 = dot(ab, ab);
  if (abLen2 < 1e-8) return a.slice();
  // Seed with projection of the midpoint of source/listener onto the line.
  const mid = scale(add(source, listener), 0.5);
  let t = dot(sub(mid, a), ab) / abLen2;
  // One Newton-ish refinement: sample a few t values (segment is short).
  let bestT = Math.max(0, Math.min(1, t));
  let best = Infinity;
  for (let i = 0; i <= 8; i++) {
    const ti = i / 8;
    const p = add(a, scale(ab, ti));
    const cost = length(sub(source, p)) + length(sub(listener, p));
    if (cost < best) {
      best = cost;
      bestT = ti;
    }
  }
  // Local refine around bestT.
  for (const d of [-0.05, -0.02, 0.02, 0.05]) {
    const ti = Math.max(0, Math.min(1, bestT + d));
    const p = add(a, scale(ab, ti));
    const cost = length(sub(source, p)) + length(sub(listener, p));
    if (cost < best) {
      best = cost;
      bestT = ti;
    }
  }
  return add(a, scale(ab, bestT));
}

/**
 * Diffraction path for one edge. Returns null when legs are blocked, the bend
 * is negligible, or the path is barely longer than the direct path.
 */
export function edgeDiffraction(listener, source, edge, buildings) {
  const p = diffractionPoint(source, listener, edge.a, edge.b);
  const d1 = length(sub(p, source));
  const d2 = length(sub(listener, p));
  const pathLen = d1 + d2;
  if (pathLen < 1e-3) return null;

  const direct = length(sub(source, listener));
  // Must be a real wrap (extra path), not a fake LOS.
  if (pathLen < direct + 0.4) return null;

  if (isOccluded(source, p, buildings) || isOccluded(p, listener, buildings)) return null;

  const u = normalize(sub(p, source));
  const v = normalize(sub(listener, p));
  const bend = Math.acos(Math.max(-1, Math.min(1, dot(u, v))));
  // Near-straight paths are specular-ish; skip weak bends.
  if (bend < 0.2) return null;

  // Darker, quieter than specular; high frequencies die faster around edges.
  const atten = 0.22 / (1 + 2.2 * bend);
  const bands = {
    low: atten / Math.max(pathLen, 1),
    mid: (atten * 0.75) / Math.max(pathLen, 1),
    high: (atten * 0.35) / Math.max(pathLen, 1),
  };
  // Edge "material" leans concrete (corners) with extra HF loss already in bands.
  void MATERIALS;
  return {
    kind: 'diffraction',
    order: 0,
    faceId: edge.id,
    hit: p,
    hits: [p],
    image: p,
    pathLength: pathLen,
    delaySec: pathLen / SPEED_OF_SOUND,
    gain: gainFromBands(bands),
    bands,
    cutoffHz: cutoffFromBands(bands, pathLen),
  };
}

/**
 * Strongest diffraction paths, usually useful when direct LOS is blocked.
 */
export function computeDiffraction(listener, source, buildings, { limit = 6, edges = null } = {}) {
  const list = edges || buildingEdges(buildings);
  const out = [];
  for (const edge of list) {
    const d = edgeDiffraction(listener, source, edge, buildings);
    if (d) out.push(d);
  }
  out.sort((a, b) => b.gain - a.gain);
  return out.slice(0, limit);
}
