// Pure, DOM-free helpers for colouring flight paths by altitude.
//
// The map can shade each trace segment by the aircraft's barometric altitude so
// climbs and descents are visible at a glance. NYPD helicopters mostly fly low
// (a few hundred to a few thousand feet), so we normalise the colour ramp to the
// altitude range actually present in the data being drawn rather than to a fixed
// scale — otherwise every low-and-level track would look the same colour.

/** Clamp a number to the inclusive [0, 1] range. */
export function clamp01(x) {
  if (!Number.isFinite(x)) return 0;
  return Math.max(0, Math.min(1, x));
}

/** Min/max airborne altitude (feet) across samples, or null if none have one. */
export function altitudeRange(samples) {
  let min = Infinity;
  let max = -Infinity;
  for (const s of samples || []) {
    const alt = s && s.alt;
    if (!Number.isFinite(alt)) continue;
    if (alt < min) min = alt;
    if (alt > max) max = alt;
  }
  if (min === Infinity) return null;
  return { min, max };
}

/**
 * Position of an altitude within a range, as a fraction in [0, 1]. A degenerate
 * range (single altitude, or missing/invalid altitude) maps to the mid-point so
 * the track still gets a stable, sensible colour.
 */
export function altitudeFraction(alt, min, max) {
  if (!Number.isFinite(alt) || !Number.isFinite(min) || !Number.isFinite(max)) {
    return 0.5;
  }
  if (max <= min) return 0.5;
  return clamp01((alt - min) / (max - min));
}

/**
 * Colour for a normalised altitude fraction: low altitudes are cool (deep blue),
 * high altitudes are warm (red), passing through cyan/green/yellow in between.
 * Returns an `hsl(...)` string, accepted anywhere Leaflet takes a colour.
 */
export function altitudeColorForFraction(fraction) {
  const t = clamp01(fraction);
  const hue = Math.round(240 - 240 * t); // 240° blue (low) -> 0° red (high)
  return `hsl(${hue}, 80%, 52%)`;
}

/** Colour for an absolute altitude given the range being displayed. */
export function altitudeColor(alt, min, max) {
  return altitudeColorForFraction(altitudeFraction(alt, min, max));
}

/**
 * Even stops from `min` to `max` (inclusive), each with its altitude and colour,
 * for drawing a gradient legend. Returns an empty array for an invalid range.
 */
export function altitudeLegendStops(min, max, count = 5) {
  if (!Number.isFinite(min) || !Number.isFinite(max) || count < 2) return [];
  const stops = [];
  for (let i = 0; i < count; i++) {
    const t = i / (count - 1);
    stops.push({ alt: min + (max - min) * t, color: altitudeColorForFraction(t) });
  }
  return stops;
}
