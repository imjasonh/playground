/**
 * Map cell indices (0..size-1) onto an Archimedean spiral winding
 * counter-clockwise from the outside toward the center.
 *
 * Cell 0 (number 1) sits at the top of the outer ring.
 *
 * @param {number} size
 * @param {{ turns?: number, innerRatio?: number }} [options]
 * @returns {{ x: number, y: number, angle: number, radius: number }[]}
 *   Coordinates in a unit square centered at (0.5, 0.5).
 */
export function spiralLayout(size, options = {}) {
  // Enough turns to space rings, but not so many that cells collide.
  const turns = options.turns ?? Math.max(2.2, Math.min(4.2, size / 26));
  const innerRatio = options.innerRatio ?? 0.14;
  const points = [];

  for (let i = 0; i < size; i += 1) {
    const t = size === 1 ? 0 : i / (size - 1);
    // Start at top (-PI/2); increase angle for counter-clockwise in math coords.
    const angle = -Math.PI / 2 + t * turns * 2 * Math.PI;
    const radius = 0.46 * (1 - t * (1 - innerRatio));
    const x = 0.5 + Math.cos(angle) * radius;
    const y = 0.5 + Math.sin(angle) * radius;
    points.push({ x, y, angle, radius });
  }
  return points;
}

/**
 * Estimate a font size (as a fraction of the viewBox) that fits nearby cells.
 * @param {number} size
 */
export function cellFontScale(size) {
  if (size <= 36) return 0.028;
  if (size <= 48) return 0.024;
  if (size <= 64) return 0.02;
  return 0.016;
}

/**
 * Estimate cell radius as a fraction of the viewBox.
 * @param {number} size
 */
export function cellRadiusScale(size) {
  if (size <= 36) return 0.038;
  if (size <= 48) return 0.032;
  if (size <= 64) return 0.027;
  return 0.022;
}
