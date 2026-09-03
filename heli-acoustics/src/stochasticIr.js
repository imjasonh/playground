// Stochastic late-field energy: bounce rays in the AABB city, bin arrivals by
// delay, and turn the histogram into a stereo impulse response for ConvolverNode.

import { add, sub, scale, length, normalize, dot } from './geometry.js';
import { rayAabb } from './occlusion.js';
import { SPEED_OF_SOUND, GROUND } from './city.js';
import { MATERIALS } from './materials.js';
import { buildImpulseResponse } from './impulseResponse.js';

const BIN_COUNT = 256;
const IR_DURATION = 1.6;

function hash(i, seed) {
  let x = (i * 1664525 + seed * 1013904223) >>> 0;
  x ^= x << 13;
  x ^= x >>> 17;
  x ^= x << 5;
  return (x >>> 0) / 0xffffffff;
}

function randomDir(i, seed) {
  const u = hash(i, seed);
  const v = hash(i + 19, seed + 7);
  const theta = u * Math.PI * 2;
  const z = v * 2 - 1;
  const r = Math.sqrt(Math.max(0, 1 - z * z));
  return [r * Math.cos(theta), z, r * Math.sin(theta)];
}

function nearestHit(origin, dir, buildings) {
  let best = null;
  let bestT = Infinity;
  for (const b of buildings) {
    const t = rayAabb(origin, dir, b);
    if (t !== null && t > 0.05 && t < bestT) {
      bestT = t;
      best = b;
    }
  }
  // Ground plane y=0.
  if (dir[1] < -1e-6) {
    const tG = (GROUND.y - origin[1]) / dir[1];
    if (tG > 0.05 && tG < bestT) {
      bestT = tG;
      best = { id: 'ground', ground: true };
    }
  }
  if (!best) return null;
  const point = add(origin, scale(dir, bestT));
  let normal;
  let material;
  if (best.ground) {
    normal = [0, 1, 0];
    material = MATERIALS.asphalt;
  } else {
    // Face normal from which slab was hit.
    const eps = 0.02;
    if (Math.abs(point[0] - best.min[0]) < eps) normal = [-1, 0, 0];
    else if (Math.abs(point[0] - best.max[0]) < eps) normal = [1, 0, 0];
    else if (Math.abs(point[2] - best.min[2]) < eps) normal = [0, 0, -1];
    else if (Math.abs(point[2] - best.max[2]) < eps) normal = [0, 0, 1];
    else if (Math.abs(point[1] - best.max[1]) < eps) normal = [0, 1, 0];
    else normal = [0, -1, 0];
    material = /ne-low|se/.test(best.id) ? MATERIALS.glass : MATERIALS.concrete;
  }
  return { t: bestT, point, normal, material };
}

function reflectDir(dir, normal) {
  const d = dot(dir, normal);
  return normalize(sub(dir, scale(normal, 2 * d)));
}

/**
 * Trace rays and return delay-bin energies (length BIN_COUNT over IR_DURATION).
 */
export function traceEnergyBins(
  listener,
  source,
  buildings,
  { rays = 192, bounces = 5, seed = 1 } = {},
) {
  const bins = new Float32Array(BIN_COUNT);
  const maxDist = SPEED_OF_SOUND * IR_DURATION;

  for (let i = 0; i < rays; i++) {
    let origin = source.slice();
    let dir = randomDir(i, seed);
    let energy = 1;
    let dist = 0;
    for (let b = 0; b < bounces; b++) {
      const hit = nearestHit(origin, dir, buildings);
      if (!hit) break;
      dist += hit.t;
      if (dist > maxDist) break;
      energy *=
        Math.sqrt(1 - hit.material.absorb.mid) *
        Math.sqrt(Math.max(0, 1 - (hit.material.scatter || 0)));
      // Deposit at this bounce as if heard from the listener direction of arrival
      // approximated by path length (diffuse late field; not image-source accurate).
      const toListener = length(sub(listener, hit.point));
      const total = dist + toListener;
      if (total < maxDist && energy > 1e-5) {
        const bin = Math.min(BIN_COUNT - 1, Math.floor((total / maxDist) * BIN_COUNT));
        // Extra HF loss baked as mid-band deposit; listener proximity falloff.
        bins[bin] += energy / Math.max(toListener, 1);
      }
      // Scatter mix from material s (Kang-style diffuse fraction).
      const s = hit.material.scatter ?? 0.15;
      const spec = reflectDir(dir, hit.normal);
      const rnd = randomDir(i * 17 + b, seed + 3);
      dir = normalize(add(scale(spec, 1 - s), scale(rnd, s)));
      // Nudge off the surface.
      origin = add(hit.point, scale(hit.normal, 0.08));
      if (dot(dir, hit.normal) < 0) dir = reflectDir(dir, hit.normal);
    }
  }
  return bins;
}

/**
 * Build a stereo AudioBuffer whose amplitude envelope follows energy bins.
 * Falls back to enclosure procedural IR when bins are empty.
 */
export function binsToImpulseResponse(ctx, bins, { durationSec = IR_DURATION } = {}) {
  let peak = 0;
  for (let i = 0; i < bins.length; i++) peak = Math.max(peak, bins[i]);
  if (peak < 1e-8) {
    return buildImpulseResponse(ctx, { durationSec, decay: 3.5, damping: 2.8 });
  }
  const n = Math.max(1, Math.floor(ctx.sampleRate * durationSec));
  const buf = ctx.createBuffer(2, n, ctx.sampleRate);
  for (let ch = 0; ch < 2; ch++) {
    const data = buf.getChannelData(ch);
    let state = (ch + 3) * 1664525 + 2246822519;
    for (let i = 0; i < n; i++) {
      const t = i / (n - 1);
      const fBin = t * (bins.length - 1);
      const i0 = Math.floor(fBin);
      const i1 = Math.min(bins.length - 1, i0 + 1);
      const frac = fBin - i0;
      const env = (bins[i0] * (1 - frac) + bins[i1] * frac) / peak;
      state = (state * 1664525 + 1013904223) >>> 0;
      const noise = state / 0xffffffff * 2 - 1;
      // Mild HF damping over time.
      const damp = Math.exp(-1.8 * t);
      data[i] = noise * Math.sqrt(Math.max(0, env)) * damp;
    }
  }
  return buf;
}

export { BIN_COUNT, IR_DURATION };
