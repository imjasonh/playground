// Pure image-processing engine for the e-ink simulator.
//
// Images are represented the same way the browser's ImageData is:
//   { width, height, data: Uint8ClampedArray }  // RGBA, 4 bytes per pixel
// so the same functions run in the browser (on a real ImageData) and under
// `node --test` (on a plain object). No DOM APIs are used here.

import { clamp255, clamp01, luma, nearestColorIndex } from "./color.js";

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
// Real e-paper converters almost always push saturation/contrast up before
// quantizing, because the reflective inks are muted. These knobs let the user
// compensate. Order is chosen to feel predictable: gamma, brightness, contrast,
// then saturation. All parameters default to "identity".

const DEFAULT_ADJUST = Object.freeze({
  brightness: 1,
  contrast: 1,
  saturation: 1,
  gamma: 1,
});

export function adjustImage(img, options = {}) {
  const { brightness, contrast, saturation, gamma } = {
    ...DEFAULT_ADJUST,
    ...options,
  };
  const out = cloneImage(img);
  const d = out.data;
  const invGamma = gamma > 0 ? 1 / gamma : 1;
  const applyGamma = gamma !== 1;

  for (let i = 0; i < d.length; i += 4) {
    let r = d[i];
    let g = d[i + 1];
    let b = d[i + 2];

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

// Build a closure that maps a working RGB triple to its nearest palette color.
// Writes the chosen color into `outRgb` (length-3 array) to avoid allocations.
function makeMapper(palette) {
  if (palette.kind === "list") {
    const colors = palette.colors;
    return (r, g, b, outRgb) => {
      const idx = nearestColorIndex(r, g, b, colors);
      const c = colors[idx];
      outRgb[0] = c[0];
      outRgb[1] = c[1];
      outRgb[2] = c[2];
    };
  }
  const levels = palette.levels;
  if (palette.grayscale) {
    return (r, g, b, outRgb) => {
      const q = quantizeChannel(luma(r, g, b), levels);
      outRgb[0] = q;
      outRgb[1] = q;
      outRgb[2] = q;
    };
  }
  return (r, g, b, outRgb) => {
    outRgb[0] = quantizeChannel(r, levels);
    outRgb[1] = quantizeChannel(g, levels);
    outRgb[2] = quantizeChannel(b, levels);
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

// Normalized Bayer threshold matrices (values in 0..1, centered later).
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
  "atkinson",
  "jarvis-judice-ninke",
  "stucki",
  "sierra",
  "sierra-lite",
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

// Main entry point. Returns a NEW image quantized to `palette` using `method`.
// `serpentine` (default true) alternates scan direction for error diffusion to
// reduce directional worming artifacts.
export function quantizeImage(img, palette, options = {}) {
  const method = options.method ?? "floyd-steinberg";
  const serpentine = options.serpentine ?? true;
  const map = makeMapper(palette);
  const { width, height } = img;
  const src = img.data;

  // If the palette is grayscale, collapse to luma first so error diffusion runs
  // on a single tone axis and produces neutral gray dithering.
  const working = new Float32Array(width * height * 3);
  const grayscale = !!palette.grayscale;
  for (let p = 0, s = 0; s < src.length; p += 3, s += 4) {
    if (grayscale) {
      const l = luma(src[s], src[s + 1], src[s + 2]);
      working[p] = l;
      working[p + 1] = l;
      working[p + 2] = l;
    } else {
      working[p] = src[s];
      working[p + 1] = src[s + 1];
      working[p + 2] = src[s + 2];
    }
  }

  const out = createImage(width, height);
  const dst = out.data;
  const chosen = [0, 0, 0];

  if (method === "none") {
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const p = (y * width + x) * 3;
        map(working[p], working[p + 1], working[p + 2], chosen);
        writePixel(dst, img, x, y, chosen);
      }
    }
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
          chosen,
        );
        writePixel(dst, img, x, y, chosen);
      }
    }
    return out;
  }

  // Error diffusion.
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
      map(or, og, ob, chosen);
      writePixel(dst, img, x, y, chosen);

      const er = or - chosen[0];
      const eg = og - chosen[1];
      const eb = ob - chosen[2];

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
