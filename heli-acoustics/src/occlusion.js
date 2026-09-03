import { length, sub, add, scale, normalize, dot } from './geometry.js';

// Ray vs AABB. Returns distance t along the ray to the first hit, or null.
// Ray is origin + t * dir with dir not necessarily unit; t is in the same
// units as dir's scale (if dir is unit, t is meters).
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

// True when a building AABB sits between listener and source (exclusive of
// endpoints, so standing inside a block still reports clear if the source is
// outside through an open face is not expected in this scene).
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

// Occlusion amount in [0,1]: 0 clear, 1 fully blocked. Softens near grazing
// hits by counting how much of the path is buried in an AABB (simple for M1).
export function occlusionAmount(listener, source, buildings) {
  return isOccluded(listener, source, buildings) ? 1 : 0;
}

export function hitPoint(origin, dir, t) {
  return add(origin, scale(dir, t));
}
