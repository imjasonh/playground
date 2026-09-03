// Street-canyon enclosure estimate for late reverb. Casts horizontal rays from
// the listener and maps mean wall distance to an enclosure amount in [0, 1].
// Open plaza → near 0; standing between close facades → near 1.

import { rayAabb } from './occlusion.js';

const DEFAULT_RAYS = 12;
const DEFAULT_MAX_DIST = 100;

/**
 * @param {number[]} listener
 * @param {Array<{min:number[],max:number[]}>} buildings
 * @param {{ rays?: number, maxDist?: number }} [opts]
 * @returns {{ amount: number, meanWallDist: number, nearestWall: number, rt60Sec: number }}
 */
export function enclosureAt(listener, buildings, { rays = DEFAULT_RAYS, maxDist = DEFAULT_MAX_DIST } = {}) {
  let sumInv = 0;
  let sumDist = 0;
  let nearest = maxDist;
  for (let i = 0; i < rays; i++) {
    const a = (i / rays) * Math.PI * 2;
    const dir = [Math.cos(a), 0, Math.sin(a)];
    let hit = maxDist;
    for (const b of buildings) {
      const t = rayAabb(listener, dir, b);
      if (t !== null && t > 0.05 && t < hit) hit = t;
    }
    nearest = Math.min(nearest, hit);
    sumDist += hit;
    // Close walls contribute more enclosure than distant ones.
    sumInv += 1 - Math.min(1, hit / maxDist);
  }
  const amount = clamp01(sumInv / rays);
  const meanWallDist = sumDist / rays;
  // Sabine-ish: tighter canyon → longer audible tail. Open → short.
  const rt60Sec = 0.25 + amount * 1.6;
  return { amount, meanWallDist, nearestWall: nearest, rt60Sec };
}

function clamp01(x) {
  return Math.max(0, Math.min(1, x));
}
