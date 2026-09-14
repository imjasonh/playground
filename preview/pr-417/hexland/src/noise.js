function fade(t) {
  return t * t * t * (t * (t * 6 - 15) + 10);
}

function lerp(a, b, t) {
  return a + t * (b - a);
}

const GRAD2 = [
  [1, 1],
  [-1, 1],
  [1, -1],
  [-1, -1],
  [1, 0],
  [-1, 0],
  [0, 1],
  [0, -1],
];

function grad(hash, x, y) {
  const g = GRAD2[hash & 7];
  return g[0] * x + g[1] * y;
}

/**
 * Returns a 2D Perlin sampler. `rng` must return values in [0, 1).
 * The same `rng` sequence produces the same field.
 */
export function createPerlin2D(rng) {
  const source = new Uint8Array(256);
  for (let i = 0; i < 256; i += 1) {
    source[i] = i;
  }
  for (let i = 255; i > 0; i -= 1) {
    const j = Math.floor(rng() * (i + 1));
    const tmp = source[i];
    source[i] = source[j];
    source[j] = tmp;
  }
  const perm = new Uint16Array(512);
  for (let i = 0; i < 512; i += 1) {
    perm[i] = source[i & 255];
  }

  return (x, y) => {
    const x0 = Math.floor(x);
    const y0 = Math.floor(y);
    const xf = x - x0;
    const yf = y - y0;
    const u = fade(xf);
    const v = fade(yf);
    const X = x0 & 255;
    const Y = y0 & 255;
    const n00 = grad(perm[X + perm[Y]], xf, yf);
    const n10 = grad(perm[X + 1 + perm[Y]], xf - 1, yf);
    const n01 = grad(perm[X + perm[Y + 1]], xf, yf - 1);
    const n11 = grad(perm[X + 1 + perm[Y + 1]], xf - 1, yf - 1);
    return lerp(lerp(n00, n10, u), lerp(n01, n11, u), v);
  };
}

/**
 * Fractal Brownian motion: summed Perlin octaves, normalized to about [-1, 1].
 */
export function fbm2D(noise, x, y, octaves = 4, lacunarity = 2, gain = 0.5) {
  let sum = 0;
  let amp = 1;
  let freq = 1;
  let norm = 0;
  for (let i = 0; i < octaves; i += 1) {
    sum += amp * noise(x * freq, y * freq);
    norm += amp;
    amp *= gain;
    freq *= lacunarity;
  }
  return sum / (norm || 1);
}
