// Pure image-processing engine for the e-ink simulator.
//
// Images are represented the same way the browser's ImageData is:
//   { width, height, data: Uint8ClampedArray }  // RGBA, 4 bytes per pixel
// so the same functions run in the browser (on a real ImageData) and under
// `node --test` (on a plain object). No DOM APIs are used here.

import {
  clamp255,
  clamp01,
  luma,
  toGray,
  srgbToLinear,
  linearToSrgb,
  makeColorMatcher,
} from "./color.js";
import { BLUE_NOISE_SIZE, getBlueNoiseMatrix } from "./bluenoise.js";
import { OSTROMOUKHOV_WEIGHTS } from "./ostromoukhov.js";

export function createImage(width, height) {
  return { width, height, data: new Uint8ClampedArray(width * height * 4) };
}

export function cloneImage(img) {
  return {
    width: img.width,
    height: img.height,
    data: new Uint8ClampedArray(img.data),
  };
}

// ---------------------------------------------------------------------------
// Pre-processing adjustments
// ---------------------------------------------------------------------------
//
// Real e-paper converters almost always push saturation/contrast/sharpness up
// before quantizing, because reflective inks are muted and lower-DPI panels
// soften detail. Order is chosen to feel predictable: optional auto-levels,
// gamma, brightness, contrast, saturation, then optional unsharp-mask sharpen.
// All parameters default to "identity".

const DEFAULT_ADJUST = Object.freeze({
  brightness: 1,
  contrast: 1,
  saturation: 1,
  gamma: 1,
  sharpen: 0,
  autoLevels: false,
});

function computeAutoLevelsRange(data) {
  const hist = new Uint32Array(256);
  const pixelCount = data.length >>> 2;
  for (let i = 0; i < data.length; i += 4) {
    const l = clamp255(Math.round(luma(data[i], data[i + 1], data[i + 2])));
    hist[l]++;
  }
  const clip = Math.floor(pixelCount * 0.01);
  let acc = 0;
  let lo = 0;
  for (let i = 0; i < 256; i++) {
    acc += hist[i];
    if (acc > clip) {
      lo = i;
      break;
    }
  }
  acc = 0;
  let hi = 255;
  for (let i = 255; i >= 0; i--) {
    acc += hist[i];
    if (acc > clip) {
      hi = i;
      break;
    }
  }
  return [lo, hi];
}

function applyUnsharpMask(img, amount) {
  const { width, height, data } = img;
  const copy = new Uint8ClampedArray(data);
  for (let y = 0; y < height; y++) {
    const ym = y > 0 ? y - 1 : 0;
    const yp = y + 1 < height ? y + 1 : height - 1;
    for (let x = 0; x < width; x++) {
      const xm = x > 0 ? x - 1 : 0;
      const xp = x + 1 < width ? x + 1 : width - 1;
      const i00 = (ym * width + xm) * 4;
      const i01 = (ym * width + x) * 4;
      const i02 = (ym * width + xp) * 4;
      const i10 = (y * width + xm) * 4;
      const i11 = (y * width + x) * 4;
      const i12 = (y * width + xp) * 4;
      const i20 = (yp * width + xm) * 4;
      const i21 = (yp * width + x) * 4;
      const i22 = (yp * width + xp) * 4;

      for (let c = 0; c < 3; c++) {
        // 3x3 Gaussian blur [1 2 1; 2 4 2; 1 2 1] / 16
        const blur =
          (copy[i00 + c] +
            2 * copy[i01 + c] +
            copy[i02 + c] +
            2 * copy[i10 + c] +
            4 * copy[i11 + c] +
            2 * copy[i12 + c] +
            copy[i20 + c] +
            2 * copy[i21 + c] +
            copy[i22 + c]) *
          0.0625;
        const orig = copy[i11 + c];
        data[i11 + c] = clamp255(orig + amount * (orig - blur));
      }
    }
  }
}

export function adjustImage(img, options = {}) {
  const { brightness, contrast, saturation, gamma, sharpen, autoLevels } = {
    ...DEFAULT_ADJUST,
    ...options,
  };
  const out = cloneImage(img);
  const d = out.data;

  let levelLo = 0;
  let levelScale = 1;
  let applyLevels = false;
  if (autoLevels) {
    const [lo, hi] = computeAutoLevelsRange(d);
    if (hi > lo + 4) {
      levelLo = lo;
      levelScale = 255 / (hi - lo);
      applyLevels = true;
    }
  }

  const invGamma = gamma > 0 ? 1 / gamma : 1;
  const applyGamma = gamma !== 1;

  for (let i = 0; i < d.length; i += 4) {
    let r = d[i];
    let g = d[i + 1];
    let b = d[i + 2];

    if (applyLevels) {
      r = clamp255((r - levelLo) * levelScale);
      g = clamp255((g - levelLo) * levelScale);
      b = clamp255((b - levelLo) * levelScale);
    }

    if (applyGamma) {
      r = 255 * Math.pow(r / 255, invGamma);
      g = 255 * Math.pow(g / 255, invGamma);
      b = 255 * Math.pow(b / 255, invGamma);
    }

    if (brightness !== 1) {
      r *= brightness;
      g *= brightness;
      b *= brightness;
    }

    if (contrast !== 1) {
      r = (r - 128) * contrast + 128;
      g = (g - 128) * contrast + 128;
      b = (b - 128) * contrast + 128;
    }

    if (saturation !== 1) {
      const l = luma(r, g, b);
      r = l + (r - l) * saturation;
      g = l + (g - l) * saturation;
      b = l + (b - l) * saturation;
    }

    d[i] = clamp255(r);
    d[i + 1] = clamp255(g);
    d[i + 2] = clamp255(b);
    // alpha (d[i + 3]) is preserved
  }

  if (sharpen > 0) {
    applyUnsharpMask(out, sharpen);
  }

  return out;
}

// ---------------------------------------------------------------------------
// Palette model
// ---------------------------------------------------------------------------
//
// A palette is either:
//   { kind: "list",    colors: [[r,g,b], ...], grayscale?: bool }
//   { kind: "channel", levels: N, grayscale?: bool }
//
// "list" palettes snap each pixel to the nearest color in a fixed set (used for
// Spectra 6, ACeP 7-color, tri/four-color ESL panels...). "channel" palettes
// quantize each RGB channel to N evenly spaced levels (used for grayscale Carta
// panels and continuous-color CFA/ACeP panels like Kaleido 3 / Gallery 3).

function quantizeChannel(value, levels) {
  const step = levels - 1;
  const level = Math.round(clamp01(value / 255) * step);
  return Math.round((level / step) * 255);
}

// Clamp an error-diffusion accumulator to the representable range while keeping
// its fractional part (so dithering stays smooth).
function clampWork(value) {
  if (value < 0) return 0;
  if (value > 255) return 255;
  return value;
}

// Returns the number of distinct colors a palette can render (for UI display).
export function paletteColorCount(palette) {
  if (palette.kind === "list") return palette.colors.length;
  if (palette.grayscale) return palette.levels;
  return palette.levels * palette.levels * palette.levels;
}

function buildChannelLevels(levels) {
  const srgb = new Uint8Array(levels);
  const lin = new Float32Array(levels);
  const step = levels - 1;
  for (let k = 0; k < levels; k++) {
    srgb[k] = Math.round((k / step) * 255);
    lin[k] = srgbToLinear(srgb[k]) * 255;
  }
  return { srgb, lin };
}

function nearestLinearLevelIndex(linVal, linLevels) {
  let best = 0;
  let bestDist = Math.abs(linVal - linLevels[0]);
  for (let i = 1; i < linLevels.length; i++) {
    const d = Math.abs(linVal - linLevels[i]);
    if (d < bestDist) {
      bestDist = d;
      best = i;
    }
  }
  return best;
}

// Build a closure that maps a working triple (r, g, b) to:
//   - `outSrgb`: the chosen palette color in sRGB (written to destination)
//   - `outWork`: the chosen palette color in working space (for error diffusion)
// In sRGB mode (`linearLight === false`), outWork === outSrgb.
function makeMapper(palette, colorMetric = "redmean", linearLight = false) {
  if (palette.kind === "list") {
    const colors = palette.colors;
    const match = makeColorMatcher(colors, colorMetric);
    if (!linearLight) {
      return (r, g, b, outSrgb, outWork) => {
        const idx = match(r, g, b);
        const c = colors[idx];
        outSrgb[0] = outWork[0] = c[0];
        outSrgb[1] = outWork[1] = c[1];
        outSrgb[2] = outWork[2] = c[2];
      };
    }
    const linColors = colors.map((c) => [
      srgbToLinear(c[0]) * 255,
      srgbToLinear(c[1]) * 255,
      srgbToLinear(c[2]) * 255,
    ]);
    return (lr, lg, lb, outSrgb, outWork) => {
      const sr = linearToSrgb(lr / 255);
      const sg = linearToSrgb(lg / 255);
      const sb = linearToSrgb(lb / 255);
      const idx = match(sr, sg, sb);
      const c = colors[idx];
      const lc = linColors[idx];
      outSrgb[0] = c[0];
      outSrgb[1] = c[1];
      outSrgb[2] = c[2];
      outWork[0] = lc[0];
      outWork[1] = lc[1];
      outWork[2] = lc[2];
    };
  }

  const levels = palette.levels;
  if (!linearLight) {
    if (palette.grayscale) {
      return (r, g, b, outSrgb, outWork) => {
        const q = quantizeChannel(luma(r, g, b), levels);
        outSrgb[0] = outWork[0] = q;
        outSrgb[1] = outWork[1] = q;
        outSrgb[2] = outWork[2] = q;
      };
    }
    return (r, g, b, outSrgb, outWork) => {
      outSrgb[0] = outWork[0] = quantizeChannel(r, levels);
      outSrgb[1] = outWork[1] = quantizeChannel(g, levels);
      outSrgb[2] = outWork[2] = quantizeChannel(b, levels);
    };
  }

  const { srgb, lin } = buildChannelLevels(levels);
  if (palette.grayscale) {
    return (lr, lg, lb, outSrgb, outWork) => {
      const idx = nearestLinearLevelIndex(lr, lin);
      const sv = srgb[idx];
      const lv = lin[idx];
      outSrgb[0] = sv;
      outSrgb[1] = sv;
      outSrgb[2] = sv;
      outWork[0] = lv;
      outWork[1] = lv;
      outWork[2] = lv;
    };
  }
  return (lr, lg, lb, outSrgb, outWork) => {
    const ir = nearestLinearLevelIndex(lr, lin);
    const ig = nearestLinearLevelIndex(lg, lin);
    const ib = nearestLinearLevelIndex(lb, lin);
    outSrgb[0] = srgb[ir];
    outSrgb[1] = srgb[ig];
    outSrgb[2] = srgb[ib];
    outWork[0] = lin[ir];
    outWork[1] = lin[ig];
    outWork[2] = lin[ib];
  };
}

// ---------------------------------------------------------------------------
// Dithering strategies
// ---------------------------------------------------------------------------

// Error-diffusion kernels. Each entry is [dx, dy, weight]; weights are divided
// by `divisor`. Only forward neighbors (relative to the scan) are listed.
export const DIFFUSION_KERNELS = {
  "floyd-steinberg": {
    divisor: 16,
    cells: [
      [1, 0, 7],
      [-1, 1, 3],
      [0, 1, 5],
      [1, 1, 1],
    ],
  },
  atkinson: {
    // Atkinson only propagates 6/8 of the error, giving crisp, contrasty
    // results that look a lot like classic 1-bit Mac dithering.
    divisor: 8,
    cells: [
      [1, 0, 1],
      [2, 0, 1],
      [-1, 1, 1],
      [0, 1, 1],
      [1, 1, 1],
      [0, 2, 1],
    ],
  },
  burkes: {
    divisor: 32,
    cells: [
      [1, 0, 8],
      [2, 0, 4],
      [-2, 1, 2],
      [-1, 1, 4],
      [0, 1, 8],
      [1, 1, 4],
      [2, 1, 2],
    ],
  },
  "jarvis-judice-ninke": {
    divisor: 48,
    cells: [
      [1, 0, 7],
      [2, 0, 5],
      [-2, 1, 3],
      [-1, 1, 5],
      [0, 1, 7],
      [1, 1, 5],
      [2, 1, 3],
      [-2, 2, 1],
      [-1, 2, 3],
      [0, 2, 5],
      [1, 2, 3],
      [2, 2, 1],
    ],
  },
  stucki: {
    divisor: 42,
    cells: [
      [1, 0, 8],
      [2, 0, 4],
      [-2, 1, 2],
      [-1, 1, 4],
      [0, 1, 8],
      [1, 1, 4],
      [2, 1, 2],
      [-2, 2, 1],
      [-1, 2, 2],
      [0, 2, 4],
      [1, 2, 2],
      [2, 2, 1],
    ],
  },
  sierra: {
    divisor: 32,
    cells: [
      [1, 0, 5],
      [2, 0, 3],
      [-2, 1, 2],
      [-1, 1, 4],
      [0, 1, 5],
      [1, 1, 4],
      [2, 1, 2],
      [-1, 2, 2],
      [0, 2, 3],
      [1, 2, 2],
    ],
  },
  "sierra-lite": {
    divisor: 4,
    cells: [
      [1, 0, 2],
      [-1, 1, 1],
      [0, 1, 1],
    ],
  },
};

// Normalized Bayer threshold matrices (values in 0..n*n-1, centered later).
export const BAYER_MATRICES = {
  "bayer-2": [
    [0, 2],
    [3, 1],
  ],
  "bayer-4": [
    [0, 8, 2, 10],
    [12, 4, 14, 6],
    [3, 11, 1, 9],
    [15, 7, 13, 5],
  ],
  "bayer-8": buildBayer8(),
};

function buildBayer8() {
  // Recursively expand the 4x4 into 8x8.
  const base = [
    [0, 8, 2, 10],
    [12, 4, 14, 6],
    [3, 11, 1, 9],
    [15, 7, 13, 5],
  ];
  const size = 8;
  const m = Array.from({ length: size }, () => new Array(size).fill(0));
  for (let y = 0; y < size; y++) {
    for (let x = 0; x < size; x++) {
      const q = base[y % 4][x % 4];
      const quadrant = (y < 4 ? 0 : 2) + (x < 4 ? 0 : 1);
      m[y][x] = q * 4 + quadrant;
    }
  }
  return m;
}

export const DITHER_METHODS = [
  "none",
  "floyd-steinberg",
  "ostromoukhov",
  "atkinson",
  "riemersma",
  "burkes",
  "jarvis-judice-ninke",
  "stucki",
  "sierra",
  "sierra-lite",
  "blue-noise",
  "yliluoma",
  "bayer-2",
  "bayer-4",
  "bayer-8",
];

// Approximate the palette's quantization step, used to scale ordered-dither
// thresholds so the pattern strength matches the color spacing.
function paletteSpread(palette) {
  if (palette.kind === "channel") {
    return 255 / palette.levels;
  }
  // For small list palettes a fixed, fairly strong spread reads well.
  return 96;
}

// Exact fractional ordered-dither for a single channel (supports both sRGB and
// linear-light spaces). `t01` is a threshold in (0, 1).
function orderedQuantizeChannel(val, srgbLevels, linLevels, linearLight, t01) {
  const n = srgbLevels.length;
  if (!linearLight) {
    const scaled = clamp01(val / 255) * (n - 1);
    const lo = Math.min(n - 1, Math.floor(scaled));
    const hi = Math.min(n - 1, lo + 1);
    const frac = scaled - lo;
    return frac > t01 ? srgbLevels[hi] : srgbLevels[lo];
  }
  const lv = clampWork(val);
  // Find bracketing levels in linLevels (monotonically increasing 0..255).
  let lo = 0;
  while (lo + 1 < n && linLevels[lo + 1] <= lv) lo++;
  const hi = Math.min(n - 1, lo + 1);
  if (hi === lo) return srgbLevels[lo];
  const frac = (lv - linLevels[lo]) / (linLevels[hi] - linLevels[lo]);
  return frac > t01 ? srgbLevels[hi] : srgbLevels[lo];
}

// ---------------------------------------------------------------------------
// Ostromoukhov (2001) variable-coefficient error diffusion
// ---------------------------------------------------------------------------

function runOstromoukhov(
  img,
  working,
  dst,
  map,
  serpentine,
  grayscale,
) {
  const { width, height } = img;
  const chosenSrgb = [0, 0, 0];
  const chosenWork = [0, 0, 0];

  for (let y = 0; y < height; y++) {
    const leftToRight = !serpentine || y % 2 === 0;
    const xStart = leftToRight ? 0 : width - 1;
    const xEnd = leftToRight ? width : -1;
    const xStep = leftToRight ? 1 : -1;

    for (let x = xStart; x !== xEnd; x += xStep) {
      const p = (y * width + x) * 3;
      const or = clampWork(working[p]);
      const og = clampWork(working[p + 1]);
      const ob = clampWork(working[p + 2]);
      map(or, og, ob, chosenSrgb, chosenWork);
      writePixel(dst, img, x, y, chosenSrgb);

      const er = or - chosenWork[0];
      const eg = og - chosenWork[1];
      const eb = ob - chosenWork[2];

      // Select Ostromoukhov's tone-dependent coefficients by input intensity.
      const tone = grayscale
        ? clamp255(Math.round(or))
        : clamp255(Math.round(luma(or, og, ob)));
      const wIdx = tone * 3;
      const w1 = OSTROMOUKHOV_WEIGHTS[wIdx];
      const w2 = OSTROMOUKHOV_WEIGHTS[wIdx + 1];
      const w3 = OSTROMOUKHOV_WEIGHTS[wIdx + 2];

      const nx1 = x + xStep;
      if (nx1 >= 0 && nx1 < width) {
        const np = (y * width + nx1) * 3;
        working[np] += er * w1;
        working[np + 1] += eg * w1;
        working[np + 2] += eb * w1;
      }
      if (y + 1 < height) {
        const nx2 = x - xStep;
        if (nx2 >= 0 && nx2 < width) {
          const np = ((y + 1) * width + nx2) * 3;
          working[np] += er * w2;
          working[np + 1] += eg * w2;
          working[np + 2] += eb * w2;
        }
        const np3 = ((y + 1) * width + x) * 3;
        working[np3] += er * w3;
        working[np3 + 1] += eg * w3;
        working[np3 + 2] += eb * w3;
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Riemersma (Hilbert space-filling curve) error diffusion
// ---------------------------------------------------------------------------

const RIEMERSMA_LEN = 16;
const RIEMERSMA_WEIGHTS = (() => {
  const w = new Float32Array(RIEMERSMA_LEN);
  const ratio = 1 / 16;
  const logRatio = Math.log(ratio);
  let sum = 0;
  for (let i = 0; i < RIEMERSMA_LEN; i++) {
    // Index 0 is oldest (smallest weight), index 15 is newest (largest weight).
    w[i] = Math.exp(((RIEMERSMA_LEN - 1 - i) * logRatio) / (RIEMERSMA_LEN - 1));
    sum += w[i];
  }
  for (let i = 0; i < RIEMERSMA_LEN; i++) w[i] /= sum;
  return w;
})();

// Convert 1D Hilbert index `d` in [0, n*n) to 2D coordinates (n = power of 2).
function hilbertD2XY(n, d, out) {
  let x = 0;
  let y = 0;
  let t = d;
  for (let s = 1; s < n; s <<= 1) {
    const rx = 1 & (t >> 1);
    const ry = 1 & (t ^ rx);
    if (ry === 0) {
      if (rx === 1) {
        x = s - 1 - x;
        y = s - 1 - y;
      }
      const tmp = x;
      x = y;
      y = tmp;
    }
    x += s * rx;
    y += s * ry;
    t >>= 2;
  }
  out[0] = x;
  out[1] = y;
}

function runRiemersma(img, working, dst, map) {
  const { width, height } = img;
  let n = 1;
  const maxDim = Math.max(width, height);
  while (n < maxDim) n <<= 1;

  const errR = new Float32Array(RIEMERSMA_LEN);
  const errG = new Float32Array(RIEMERSMA_LEN);
  const errB = new Float32Array(RIEMERSMA_LEN);
  let head = 0;

  const coord = [0, 0];
  const chosenSrgb = [0, 0, 0];
  const chosenWork = [0, 0, 0];
  const total = n * n;

  for (let d = 0; d < total; d++) {
    hilbertD2XY(n, d, coord);
    const x = coord[0];
    const y = coord[1];
    if (x >= width || y >= height) continue;

    let ar = 0;
    let ag = 0;
    let ab = 0;
    for (let k = 0; k < RIEMERSMA_LEN; k++) {
      const idx = (head + k) & (RIEMERSMA_LEN - 1);
      const w = RIEMERSMA_WEIGHTS[k];
      ar += errR[idx] * w;
      ag += errG[idx] * w;
      ab += errB[idx] * w;
    }

    const p = (y * width + x) * 3;
    const or = clampWork(working[p] + ar);
    const og = clampWork(working[p + 1] + ag);
    const ob = clampWork(working[p + 2] + ab);
    map(or, og, ob, chosenSrgb, chosenWork);
    writePixel(dst, img, x, y, chosenSrgb);

    // Push new error into circular queue (overwriting the oldest slot at `head`).
    errR[head] = or - chosenWork[0];
    errG[head] = og - chosenWork[1];
    errB[head] = ob - chosenWork[2];
    head = (head + 1) & (RIEMERSMA_LEN - 1);
  }
}

// ---------------------------------------------------------------------------
// Blue-noise ordered dithering (64x64 Void-and-Cluster)
// ---------------------------------------------------------------------------

function runBlueNoise(img, working, dst, palette, map, linearLight) {
  const { width, height } = img;
  const mask = getBlueNoiseMatrix();
  const maskMask = BLUE_NOISE_SIZE - 1; // 63
  const chosenSrgb = [0, 0, 0];
  const chosenWork = [0, 0, 0];

  if (palette.kind === "channel") {
    const { srgb, lin } = buildChannelLevels(palette.levels);
    const grayscale = !!palette.grayscale;
    for (let y = 0; y < height; y++) {
      const rowOff = (y & maskMask) * BLUE_NOISE_SIZE;
      for (let x = 0; x < width; x++) {
        const t01 = (mask[rowOff + (x & maskMask)] + 0.5) / 256;
        const p = (y * width + x) * 3;
        if (grayscale) {
          const q = orderedQuantizeChannel(
            working[p],
            srgb,
            lin,
            linearLight,
            t01,
          );
          chosenSrgb[0] = chosenSrgb[1] = chosenSrgb[2] = q;
        } else {
          chosenSrgb[0] = orderedQuantizeChannel(
            working[p],
            srgb,
            lin,
            linearLight,
            t01,
          );
          chosenSrgb[1] = orderedQuantizeChannel(
            working[p + 1],
            srgb,
            lin,
            linearLight,
            t01,
          );
          chosenSrgb[2] = orderedQuantizeChannel(
            working[p + 2],
            srgb,
            lin,
            linearLight,
            t01,
          );
        }
        writePixel(dst, img, x, y, chosenSrgb);
      }
    }
    return;
  }

  const spread = paletteSpread(palette);
  for (let y = 0; y < height; y++) {
    const rowOff = (y & maskMask) * BLUE_NOISE_SIZE;
    for (let x = 0; x < width; x++) {
      const t = (mask[rowOff + (x & maskMask)] + 0.5) / 256 - 0.5;
      const bias = t * spread;
      const p = (y * width + x) * 3;
      map(
        working[p] + bias,
        working[p + 1] + bias,
        working[p + 2] + bias,
        chosenSrgb,
        chosenWork,
      );
      writePixel(dst, img, x, y, chosenSrgb);
    }
  }
}

// ---------------------------------------------------------------------------
// Joel Yliluoma's Algorithm 2 (arbitrary-palette positional dithering)
// ---------------------------------------------------------------------------

function runYliluoma(img, working, dst, palette, colorMetric, linearLight) {
  const { width, height } = img;
  const bayer = BAYER_MATRICES["bayer-8"];
  const chosenSrgb = [0, 0, 0];

  // For channel palettes, exact bracketing-level ordered dithering is optimal.
  if (palette.kind === "channel") {
    const { srgb, lin } = buildChannelLevels(palette.levels);
    const grayscale = !!palette.grayscale;
    for (let y = 0; y < height; y++) {
      const brow = bayer[y & 7];
      for (let x = 0; x < width; x++) {
        const t01 = (brow[x & 7] + 0.5) / 64;
        const p = (y * width + x) * 3;
        if (grayscale) {
          const q = orderedQuantizeChannel(
            working[p],
            srgb,
            lin,
            linearLight,
            t01,
          );
          chosenSrgb[0] = chosenSrgb[1] = chosenSrgb[2] = q;
        } else {
          chosenSrgb[0] = orderedQuantizeChannel(
            working[p],
            srgb,
            lin,
            linearLight,
            t01,
          );
          chosenSrgb[1] = orderedQuantizeChannel(
            working[p + 1],
            srgb,
            lin,
            linearLight,
            t01,
          );
          chosenSrgb[2] = orderedQuantizeChannel(
            working[p + 2],
            srgb,
            lin,
            linearLight,
            t01,
          );
        }
        writePixel(dst, img, x, y, chosenSrgb);
      }
    }
    return;
  }

  // Arbitrary discrete ink palette: build an 8-slot mixing plan per pixel
  // greedily minimizing error against the target color, sort the plan by luma,
  // and index with the 8x8 Bayer matrix.
  const colors = palette.colors;
  const match = makeColorMatcher(colors, colorMetric);
  const palLuma = colors.map((c) => luma(c[0], c[1], c[2]));
  const planSize = 8;
  const plan = new Int32Array(planSize);

  for (let y = 0; y < height; y++) {
    const brow = bayer[y & 7];
    for (let x = 0; x < width; x++) {
      const p = (y * width + x) * 3;
      const tr = linearLight ? linearToSrgb(working[p] / 255) : working[p];
      const tg = linearLight
        ? linearToSrgb(working[p + 1] / 255)
        : working[p + 1];
      const tb = linearLight
        ? linearToSrgb(working[p + 2] / 255)
        : working[p + 2];

      let sumR = 0;
      let sumG = 0;
      let sumB = 0;
      for (let step = 0; step < planSize; step++) {
        // Desired color for this slot so the running average hits (tr, tg, tb).
        const wantR = clampWork(tr * (step + 1) - sumR);
        const wantG = clampWork(tg * (step + 1) - sumG);
        const wantB = clampWork(tb * (step + 1) - sumB);
        const idx = match(wantR, wantG, wantB);
        plan[step] = idx;
        const c = colors[idx];
        sumR += c[0];
        sumG += c[1];
        sumB += c[2];
      }

      // Insertion-sort the 8-element plan by luma so Bayer thresholds produce
      // smooth tonal transitions without high-frequency flicker.
      for (let i = 1; i < planSize; i++) {
        const key = plan[i];
        const keyL = palLuma[key];
        let j = i - 1;
        while (j >= 0 && palLuma[plan[j]] > keyL) {
          plan[j + 1] = plan[j];
          j--;
        }
        plan[j + 1] = key;
      }

      const slot = (brow[x & 7] * planSize) >> 6;
      const picked = colors[plan[slot]];
      writePixel(dst, img, x, y, picked);
    }
  }
}

// Main entry point. Returns a NEW image quantized to `palette` using `method`.
// Options:
//   method:      one of DITHER_METHODS (default "floyd-steinberg")
//   serpentine:  alternate scan direction for error diffusion (default true)
//   colorMetric: one of COLOR_METRICS for list palettes (default "redmean")
//   grayMode:    one of GRAY_MODES for grayscale palettes (default "luma")
//   linearLight: dither in linear-light reflectance space (default false)
export function quantizeImage(img, palette, options = {}) {
  const method = options.method ?? "floyd-steinberg";
  const serpentine = options.serpentine ?? true;
  const colorMetric = options.colorMetric ?? "redmean";
  const grayMode = options.grayMode ?? "luma";
  const linearLight = Boolean(options.linearLight);
  const map = makeMapper(palette, colorMetric, linearLight);
  const { width, height } = img;
  const src = img.data;

  // Build working float buffer. If the palette is grayscale, collapse to a
  // single tone axis first (using the selected B&W channel filter) so error
  // diffusion produces neutral gray dithering.
  const working = new Float32Array(width * height * 3);
  const grayscale = !!palette.grayscale;
  for (let p = 0, s = 0; s < src.length; p += 3, s += 4) {
    if (grayscale) {
      const g = toGray(src[s], src[s + 1], src[s + 2], grayMode);
      const v = linearLight ? srgbToLinear(g) * 255 : g;
      working[p] = v;
      working[p + 1] = v;
      working[p + 2] = v;
    } else if (linearLight) {
      working[p] = srgbToLinear(src[s]) * 255;
      working[p + 1] = srgbToLinear(src[s + 1]) * 255;
      working[p + 2] = srgbToLinear(src[s + 2]) * 255;
    } else {
      working[p] = src[s];
      working[p + 1] = src[s + 1];
      working[p + 2] = src[s + 2];
    }
  }

  const out = createImage(width, height);
  const dst = out.data;
  const chosenSrgb = [0, 0, 0];
  const chosenWork = [0, 0, 0];

  if (method === "none") {
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const p = (y * width + x) * 3;
        map(working[p], working[p + 1], working[p + 2], chosenSrgb, chosenWork);
        writePixel(dst, img, x, y, chosenSrgb);
      }
    }
    return out;
  }

  if (method === "blue-noise") {
    runBlueNoise(img, working, dst, palette, map, linearLight);
    return out;
  }

  if (method === "yliluoma") {
    runYliluoma(img, working, dst, palette, colorMetric, linearLight);
    return out;
  }

  if (method === "ostromoukhov") {
    runOstromoukhov(img, working, dst, map, serpentine, grayscale);
    return out;
  }

  if (method === "riemersma") {
    runRiemersma(img, working, dst, map);
    return out;
  }

  if (method.startsWith("bayer")) {
    const matrix = BAYER_MATRICES[method];
    const n = matrix.length;
    const denom = n * n;
    const spread = paletteSpread(palette);
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const p = (y * width + x) * 3;
        // Centered threshold in [-0.5, 0.5) scaled by the palette spread.
        const t = (matrix[y % n][x % n] + 0.5) / denom - 0.5;
        const bias = t * spread;
        map(
          working[p] + bias,
          working[p + 1] + bias,
          working[p + 2] + bias,
          chosenSrgb,
          chosenWork,
        );
        writePixel(dst, img, x, y, chosenSrgb);
      }
    }
    return out;
  }

  // Standard fixed-kernel error diffusion.
  const kernel = DIFFUSION_KERNELS[method];
  if (!kernel) {
    throw new Error(`Unknown dither method: ${method}`);
  }
  const { cells, divisor } = kernel;

  for (let y = 0; y < height; y++) {
    const leftToRight = !serpentine || y % 2 === 0;
    const xStart = leftToRight ? 0 : width - 1;
    const xEnd = leftToRight ? width : -1;
    const xStep = leftToRight ? 1 : -1;

    for (let x = xStart; x !== xEnd; x += xStep) {
      const p = (y * width + x) * 3;
      // Clamp the accumulated value into the representable [0,255] range before
      // quantizing. Without this, near a high-contrast edge (e.g. a vivid image
      // against white paper) the diffused error grows unbounded and smears
      // saturated ink into regions that should stay clean, producing comet-tail
      // streaks. Clamping bounds the error the way real converters do.
      const or = clampWork(working[p]);
      const og = clampWork(working[p + 1]);
      const ob = clampWork(working[p + 2]);
      map(or, og, ob, chosenSrgb, chosenWork);
      writePixel(dst, img, x, y, chosenSrgb);

      const er = or - chosenWork[0];
      const eg = og - chosenWork[1];
      const eb = ob - chosenWork[2];

      for (let c = 0; c < cells.length; c++) {
        const [dx, dy, w] = cells[c];
        // Mirror the horizontal offset when scanning right-to-left.
        const nx = x + (leftToRight ? dx : -dx);
        const ny = y + dy;
        if (nx < 0 || nx >= width || ny < 0 || ny >= height) continue;
        const np = (ny * width + nx) * 3;
        const f = w / divisor;
        working[np] += er * f;
        working[np + 1] += eg * f;
        working[np + 2] += eb * f;
      }
    }
  }
  return out;
}

function writePixel(dst, srcImg, x, y, rgb) {
  const i = (y * srcImg.width + x) * 4;
  dst[i] = rgb[0];
  dst[i + 1] = rgb[1];
  dst[i + 2] = rgb[2];
  dst[i + 3] = srcImg.data[i + 3]; // preserve alpha
}

// ---------------------------------------------------------------------------
// Physical panel response (realism pass)
// ---------------------------------------------------------------------------
//
// Quantization above targets *ideal* ink colors (pure primaries, pure black &
// white) so the dithering makes crisp decisions. Real reflective e-paper never
// shows those ideals: whites are a dim off-white substrate, blacks are lifted
// dark gray (low contrast ratio), and colored inks are muted. This pass maps an
// ideal image into that measured, reflective appearance.
//
//   response = {
//     white: [r,g,b],   // reflective white point of the substrate
//     black: [r,g,b],   // darkest achievable "black"
//     saturation: 0..1, // chroma retained by the inks (1 = none lost)
//   }

export function applyPanelResponse(img, response) {
  if (!response) return cloneImage(img);
  const white = response.white ?? [255, 255, 255];
  const black = response.black ?? [0, 0, 0];
  const sat = response.saturation ?? 1;
  const out = cloneImage(img);
  const d = out.data;
  for (let i = 0; i < d.length; i += 4) {
    let r = d[i];
    let g = d[i + 1];
    let b = d[i + 2];

    if (sat !== 1) {
      const l = luma(r, g, b);
      r = l + (r - l) * sat;
      g = l + (g - l) * sat;
      b = l + (b - l) * sat;
    }

    // Remap each channel from the ideal [0,255] range into the panel's
    // reflective [black, white] envelope.
    d[i] = clamp255(black[0] + ((white[0] - black[0]) * r) / 255);
    d[i + 1] = clamp255(black[1] + ((white[1] - black[1]) * g) / 255);
    d[i + 2] = clamp255(black[2] + ((white[2] - black[2]) * b) / 255);
  }
  return out;
}

// Convenience: run the full pipeline (adjust -> quantize -> optional response).
export function renderPipeline(img, palette, options = {}) {
  const adjusted = adjustImage(img, options.adjust);
  const quantized = quantizeImage(adjusted, palette, options.dither);
  if (options.response && options.realism !== false) {
    return applyPanelResponse(quantized, options.response);
  }
  return quantized;
}
