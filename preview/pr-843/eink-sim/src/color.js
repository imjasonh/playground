// Small, dependency-free color helpers shared by the processing engine and the
// display/palette definitions. Everything here is pure so it can be unit tested
// under `node --test` without a DOM.

export function clamp255(value) {
  if (value < 0) return 0;
  if (value > 255) return 255;
  return value | 0;
}

export function clamp01(value) {
  if (value < 0) return 0;
  if (value > 1) return 1;
  return value;
}

// Rec. 709 luma. Kept in 0..255 space to match the rest of the pipeline.
export function luma(r, g, b) {
  return 0.2126 * r + 0.7152 * g + 0.0722 * b;
}

// B&W channel-mixer presets for monochrome displays (classic color-filter
// photography: e.g. a red/orange filter darkens blue skies and lifts skin).
export const GRAY_MODES = ["luma", "red", "orange", "green", "blue"];

const GRAY_WEIGHTS = {
  luma: [0.2126, 0.7152, 0.0722],
  red: [0.72, 0.23, 0.05],
  orange: [0.55, 0.38, 0.07],
  green: [0.2, 0.68, 0.12],
  blue: [0.1, 0.25, 0.65],
};

export function toGray(r, g, b, mode = "luma") {
  const w = GRAY_WEIGHTS[mode];
  if (!w) {
    throw new Error(`Unknown gray mode: ${mode}`);
  }
  return w[0] * r + w[1] * g + w[2] * b;
}

export function hexToRgb(hex) {
  const normalized = hex.replace("#", "").trim();
  const value =
    normalized.length === 3
      ? normalized
          .split("")
          .map((c) => c + c)
          .join("")
      : normalized;
  const int = Number.parseInt(value, 16);
  return [(int >> 16) & 255, (int >> 8) & 255, int & 255];
}

export function rgbToHex(r, g, b) {
  const to = (v) => clamp255(v).toString(16).padStart(2, "0");
  return `#${to(r)}${to(g)}${to(b)}`;
}

export function mix(a, b, t) {
  return a + (b - a) * t;
}

export function mixRgb(a, b, t) {
  return [mix(a[0], b[0], t), mix(a[1], b[1], t), mix(a[2], b[2], t)];
}

// ---------------------------------------------------------------------------
// sRGB <-> Linear light
// ---------------------------------------------------------------------------

const SRGB_TO_LINEAR_LUT = new Float32Array(256);
for (let i = 0; i < 256; i++) {
  const s = i / 255;
  SRGB_TO_LINEAR_LUT[i] =
    s <= 0.04045 ? s / 12.92 : Math.pow((s + 0.055) / 1.055, 2.4);
}

// Convert sRGB channel in [0, 255] to linear light in [0, 1].
export function srgbToLinear(v) {
  if (v <= 0) return 0;
  if (v >= 255) return 1;
  const i = v | 0;
  if (i === v) return SRGB_TO_LINEAR_LUT[i];
  // Linear interpolation in the 256-entry LUT is accurate to < 1e-5 and fast.
  const f = v - i;
  return SRGB_TO_LINEAR_LUT[i] * (1 - f) + SRGB_TO_LINEAR_LUT[i + 1] * f;
}

// Convert linear light in [0, 1] to sRGB in [0, 255].
export function linearToSrgb(lin) {
  if (lin <= 0) return 0;
  if (lin >= 1) return 255;
  const s =
    lin <= 0.0031308 ? 12.92 * lin : 1.055 * Math.pow(lin, 1 / 2.4) - 0.055;
  return s * 255;
}

// ---------------------------------------------------------------------------
// Perceptual color spaces: Oklab & CIELAB (D65)
// ---------------------------------------------------------------------------

// Convert sRGB [0..255] to Björn Ottosson's Oklab [L, a, b].
// Oklab has excellent hue linearity (unlike CIELAB, blues do not drift purple)
// and is cheap enough to run per pixel in JS.
export function rgbToOklab(r, g, b) {
  const lr = srgbToLinear(r);
  const lg = srgbToLinear(g);
  const lb = srgbToLinear(b);

  const l = Math.cbrt(0.4122214708 * lr + 0.5363325363 * lg + 0.0514459929 * lb);
  const m = Math.cbrt(0.2119034982 * lr + 0.6806995451 * lg + 0.1073969566 * lb);
  const s = Math.cbrt(0.0883024619 * lr + 0.2817188376 * lg + 0.6299787005 * lb);

  return [
    0.2104542553 * l + 0.793617785 * m - 0.0040720468 * s,
    1.9779984951 * l - 2.428592205 * m + 0.4505937099 * s,
    0.0259040371 * l + 0.7827717662 * m - 0.808675766 * s,
  ];
}

function labF(t) {
  return t > 0.008856451679 ? Math.cbrt(t) : 7.787037037 * t + 16 / 116;
}

// Convert sRGB [0..255] to CIE L*a*b* (D65 reference white).
export function rgbToLab(r, g, b) {
  const lr = srgbToLinear(r);
  const lg = srgbToLinear(g);
  const lb = srgbToLinear(b);

  const x = (0.4124564 * lr + 0.3575761 * lg + 0.1804375 * lb) / 0.95047;
  const y = 0.2126729 * lr + 0.7151522 * lg + 0.072175 * lb;
  const z = (0.0193339 * lr + 0.119192 * lg + 0.9503041 * lb) / 1.08883;

  const fx = labF(x);
  const fy = labF(y);
  const fz = labF(z);

  return [116 * fy - 16, 500 * (fx - fy), 200 * (fy - fz)];
}

// ---------------------------------------------------------------------------
// Color distance metrics (for discrete ink palettes)
// ---------------------------------------------------------------------------

export const COLOR_METRICS = [
  "oklab",
  "photopainter",
  "cielab",
  "redmean",
  "rgb",
];

// Perceptual "redmean" distance (squared). Cheap and noticeably better than a
// flat RGB Euclidean distance when snapping photos to a handful of ink colors.
// https://www.compuphase.com/cmetric.htm
export function colorDistanceSq(r1, g1, b1, r2, g2, b2) {
  const rmean = (r1 + r2) / 2;
  const dr = r1 - r2;
  const dg = g1 - g2;
  const db = b1 - b2;
  return (
    (((512 + rmean) * dr * dr) >> 8) +
    4 * dg * dg +
    (((767 - rmean) * db * db) >> 8)
  );
}

// Build a fast nearest-color matcher for `colors` (array of [r,g,b]) using the
// requested `metric`. Precomputes palette coordinates in the target space once.
export function makeColorMatcher(colors, metric = "redmean") {
  const n = colors.length;

  if (metric === "redmean") {
    return (r, g, b) => {
      let best = 0;
      let bestDist = Infinity;
      for (let i = 0; i < n; i++) {
        const c = colors[i];
        const d = colorDistanceSq(r, g, b, c[0], c[1], c[2]);
        if (d < bestDist) {
          bestDist = d;
          best = i;
          if (d === 0) break;
        }
      }
      return best;
    };
  }

  if (metric === "rgb") {
    return (r, g, b) => {
      let best = 0;
      let bestDist = Infinity;
      for (let i = 0; i < n; i++) {
        const c = colors[i];
        const dr = r - c[0];
        const dg = g - c[1];
        const db = b - c[2];
        const d = dr * dr + dg * dg + db * db;
        if (d < bestDist) {
          bestDist = d;
          best = i;
          if (d === 0) break;
        }
      }
      return best;
    };
  }

  if (metric === "photopainter") {
    // Spectra 6 / PhotoPainter RGB + Luma distance metric from
    // Toon-nooT/PhotoPainter-E-Ink-Spectra-6-image-converter:
    // boosts blue/green weights and prioritizes hue fidelity over luma so
    // muted e-ink primaries hold their color on photos.
    const palLuma = new Float32Array(n);
    const invLumaScale = 1 / (255 * 1000);
    const inv255Sq = 0.75 / (255 * 255);
    for (let i = 0; i < n; i++) {
      const c = colors[i];
      palLuma[i] = (c[0] * 250 + c[1] * 350 + c[2] * 400) * invLumaScale;
    }
    return (r, g, b) => {
      const luma1 = (r * 250 + g * 350 + b * 400) * invLumaScale;
      let best = 0;
      let bestDist = Infinity;
      for (let i = 0; i < n; i++) {
        const c = colors[i];
        const dr = r - c[0];
        const dg = g - c[1];
        const db = b - c[2];
        const rgbDist =
          (dr * dr * 0.25 + dg * dg * 0.35 + db * db * 0.4) * inv255Sq;
        const dl = luma1 - palLuma[i];
        const d = 1.5 * rgbDist + 0.6 * dl * dl;
        if (d < bestDist) {
          bestDist = d;
          best = i;
          if (d === 0) break;
        }
      }
      return best;
    };
  }

  if (metric === "oklab") {
    const pL = new Float32Array(n);
    const pA = new Float32Array(n);
    const pB = new Float32Array(n);
    for (let i = 0; i < n; i++) {
      const [L, a, b] = rgbToOklab(colors[i][0], colors[i][1], colors[i][2]);
      pL[i] = L;
      pA[i] = a;
      pB[i] = b;
    }
    return (r, g, b) => {
      const lr = srgbToLinear(r);
      const lg = srgbToLinear(g);
      const lb = srgbToLinear(b);
      const l = Math.cbrt(
        0.4122214708 * lr + 0.5363325363 * lg + 0.0514459929 * lb,
      );
      const m = Math.cbrt(
        0.2119034982 * lr + 0.6806995451 * lg + 0.1073969566 * lb,
      );
      const s = Math.cbrt(
        0.0883024619 * lr + 0.2817188376 * lg + 0.6299787005 * lb,
      );
      const c0 = 0.2104542553 * l + 0.793617785 * m - 0.0040720468 * s;
      const c1 = 1.9779984951 * l - 2.428592205 * m + 0.4505937099 * s;
      const c2 = 0.0259040371 * l + 0.7827717662 * m - 0.808675766 * s;

      let best = 0;
      let bestDist = Infinity;
      for (let i = 0; i < n; i++) {
        const d0 = c0 - pL[i];
        const d1 = c1 - pA[i];
        const d2 = c2 - pB[i];
        const d = d0 * d0 + d1 * d1 + d2 * d2;
        if (d < bestDist) {
          bestDist = d;
          best = i;
          if (d === 0) break;
        }
      }
      return best;
    };
  }

  if (metric === "cielab") {
    const pL = new Float32Array(n);
    const pA = new Float32Array(n);
    const pB = new Float32Array(n);
    for (let i = 0; i < n; i++) {
      const [L, a, b] = rgbToLab(colors[i][0], colors[i][1], colors[i][2]);
      pL[i] = L;
      pA[i] = a;
      pB[i] = b;
    }
    return (r, g, b) => {
      const lr = srgbToLinear(r);
      const lg = srgbToLinear(g);
      const lb = srgbToLinear(b);
      const fx = labF(
        (0.4124564 * lr + 0.3575761 * lg + 0.1804375 * lb) / 0.95047,
      );
      const fy = labF(0.2126729 * lr + 0.7151522 * lg + 0.072175 * lb);
      const fz = labF(
        (0.0193339 * lr + 0.119192 * lg + 0.9503041 * lb) / 1.08883,
      );
      const c0 = 116 * fy - 16;
      const c1 = 500 * (fx - fy);
      const c2 = 200 * (fy - fz);

      let best = 0;
      let bestDist = Infinity;
      for (let i = 0; i < n; i++) {
        const d0 = c0 - pL[i];
        const d1 = c1 - pA[i];
        const d2 = c2 - pB[i];
        const d = d0 * d0 + d1 * d1 + d2 * d2;
        if (d < bestDist) {
          bestDist = d;
          best = i;
          if (d === 0) break;
        }
      }
      return best;
    };
  }

  throw new Error(`Unknown color metric: ${metric}`);
}

// Index of the nearest color in `colors` (array of [r,g,b]) to (r,g,b).
export function nearestColorIndex(r, g, b, colors, metric = "redmean") {
  if (metric === "redmean") {
    let best = 0;
    let bestDist = Infinity;
    for (let i = 0; i < colors.length; i++) {
      const c = colors[i];
      const d = colorDistanceSq(r, g, b, c[0], c[1], c[2]);
      if (d < bestDist) {
        bestDist = d;
        best = i;
        if (d === 0) break;
      }
    }
    return best;
  }
  return makeColorMatcher(colors, metric)(r, g, b);
}
