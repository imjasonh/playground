// Building edge geometry for diffraction / soft occlusion (AABB corners + roofs).

import { add, sub, scale, length, dot } from './geometry.js';

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
  const mid = scale(add(source, listener), 0.5);
  let t = dot(sub(mid, a), ab) / abLen2;
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
