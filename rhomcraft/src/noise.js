/** Deterministic 3D value noise + fBm helpers (no deps). */

function fade(t) {
  return t * t * t * (t * (t * 6 - 15) + 10);
}

function lerp(a, b, t) {
  return a + (b - a) * t;
}

function hash3(x, y, z, seed) {
  let n = Math.imul(x, 374761393) + Math.imul(y, 668265263) + Math.imul(z, 2147483647);
  n = Math.imul(n ^ seed, 2246822519);
  n ^= n >>> 13;
  n = Math.imul(n, 3266489917);
  n ^= n >>> 16;
  return (n >>> 0) / 4294967296;
}

/** Value noise in [0, 1). */
export function valueNoise3(x, y, z, seed = 1) {
  const x0 = Math.floor(x);
  const y0 = Math.floor(y);
  const z0 = Math.floor(z);
  const fx = fade(x - x0);
  const fy = fade(y - y0);
  const fz = fade(z - z0);

  const n000 = hash3(x0, y0, z0, seed);
  const n100 = hash3(x0 + 1, y0, z0, seed);
  const n010 = hash3(x0, y0 + 1, z0, seed);
  const n110 = hash3(x0 + 1, y0 + 1, z0, seed);
  const n001 = hash3(x0, y0, z0 + 1, seed);
  const n101 = hash3(x0 + 1, y0, z0 + 1, seed);
  const n011 = hash3(x0, y0 + 1, z0 + 1, seed);
  const n111 = hash3(x0 + 1, y0 + 1, z0 + 1, seed);

  const x00 = lerp(n000, n100, fx);
  const x10 = lerp(n010, n110, fx);
  const x01 = lerp(n001, n101, fx);
  const x11 = lerp(n011, n111, fx);
  const y0l = lerp(x00, x10, fy);
  const y1l = lerp(x01, x11, fy);
  return lerp(y0l, y1l, fz);
}

export function fbm2(x, z, seed = 1, octaves = 4) {
  let amp = 1;
  let freq = 1;
  let sum = 0;
  let norm = 0;
  for (let i = 0; i < octaves; i++) {
    sum += amp * valueNoise3(x * freq, 0, z * freq, seed + i * 101);
    norm += amp;
    amp *= 0.5;
    freq *= 2;
  }
  return sum / norm;
}
