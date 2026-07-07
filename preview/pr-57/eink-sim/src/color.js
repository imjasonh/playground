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

// Index of the nearest color in `colors` (array of [r,g,b]) to (r,g,b).
export function nearestColorIndex(r, g, b, colors) {
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
