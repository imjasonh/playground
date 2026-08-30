/**
 * Magazine-style spiral track: a constant-width ribbon winding
 * counter-clockwise from the outside toward the center, divided into cells.
 *
 * Cell 0 (number 1) starts near 12–1 o'clock on the outer rim.
 */

/**
 * @typedef {{
 *   index: number,
 *   cx: number,
 *   cy: number,
 *   numX: number,
 *   numY: number,
 *   path: string
 * }} SpiralCell
 */

/**
 * @param {number} size
 * @param {{ turns?: number }} [options]
 * @returns {{ cells: SpiralCell[], outerPath: string, turns: number }}
 *   Coordinates in a unit square centered at (0.5, 0.5).
 */
export function spiralLayout(size, options = {}) {
  const turns = options.turns ?? Math.max(2.6, Math.min(3.8, size / 30));
  const rim = 0.48;
  // Track width ≈ radial pitch between successive turns.
  const pitch = (rim - 0.08) / turns;
  const half = pitch * 0.46;
  // Keep the outer edge of the track inside the circular rim.
  const rMax = rim - half;
  const rMin = 0.08 + half;
  const startAngle = -Math.PI / 2 + 0.35;
  const sweep = turns * 2 * Math.PI;

  function radiusAt(t) {
    return rMax - t * (rMax - rMin);
  }

  function point(t, radialOffset) {
    // Negative sweep so the path reads counter-clockwise on screen
    // (SVG y grows downward, so positive math angles appear clockwise).
    const angle = startAngle - t * sweep;
    const r = radiusAt(t) + radialOffset;
    return {
      x: 0.5 + Math.cos(angle) * r,
      y: 0.5 + Math.sin(angle) * r,
      angle,
      r,
    };
  }

  function sampleEdge(t0, t1, radialOffset, steps) {
    const pts = [];
    for (let s = 0; s <= steps; s += 1) {
      const t = t0 + ((t1 - t0) * s) / steps;
      pts.push(point(t, radialOffset));
    }
    return pts;
  }

  function pathFrom(outerPts, innerPts) {
    const parts = [];
    outerPts.forEach((p, i) => {
      parts.push(`${i === 0 ? "M" : "L"} ${p.x.toFixed(4)} ${p.y.toFixed(4)}`);
    });
    for (let i = innerPts.length - 1; i >= 0; i -= 1) {
      const p = innerPts[i];
      parts.push(`L ${p.x.toFixed(4)} ${p.y.toFixed(4)}`);
    }
    parts.push("Z");
    return parts.join(" ");
  }

  /** @type {SpiralCell[]} */
  const cells = [];
  const steps = 4;

  for (let i = 0; i < size; i += 1) {
    const t0 = i / size;
    const t1 = (i + 1) / size;
    const outerPts = sampleEdge(t0, t1, half, steps);
    const innerPts = sampleEdge(t0, t1, -half, steps);
    const mid = point((t0 + t1) / 2, 0);
    // Number sits toward the outer-leading corner of the cell.
    const num = point(t0 + (t1 - t0) * 0.18, half * 0.55);

    cells.push({
      index: i,
      cx: mid.x,
      cy: mid.y,
      numX: num.x,
      numY: num.y,
      path: pathFrom(outerPts, innerPts),
    });
  }

  // Outer rim guide: the outer edge of the whole track.
  const rim = sampleEdge(0, 1, half, Math.max(48, size * 2));
  const outerPath = rim
    .map((p, i) => `${i === 0 ? "M" : "L"} ${p.x.toFixed(4)} ${p.y.toFixed(4)}`)
    .join(" ");

  return { cells, outerPath, turns };
}

/**
 * Letter font size as a fraction of the viewBox.
 * @param {number} size
 */
export function cellFontScale(size) {
  if (size <= 36) return 0.028;
  if (size <= 48) return 0.024;
  if (size <= 64) return 0.02;
  return 0.016;
}

/**
 * Cell number font size as a fraction of the viewBox.
 * @param {number} size
 */
export function cellNumberScale(size) {
  if (size <= 36) return 0.014;
  if (size <= 48) return 0.012;
  if (size <= 64) return 0.01;
  return 0.009;
}
