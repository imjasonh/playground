/**
 * Magazine-style spiral track: constant-width ribbon, cells of equal arc
 * length. Dividers are perpendicular to the path, so they do not line up
 * from one turn to the next — same idea as the printed Games spiral.
 *
 * Cell 0 (number 1) starts near 1 o'clock on the outer rim and winds
 * counter-clockwise into the center.
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
 * @returns {{ cells: SpiralCell[], turns: number, trackWidth: number }}
 */
export function spiralLayout(size, options = {}) {
  // Printed 100-cell spirals use about 4.5–5 turns so inner cells stay chunky.
  const turns = options.turns ?? Math.max(3.2, Math.min(5.2, 2.2 + size / 36));
  const rim = 0.485;
  const pitch = (rim - 0.055) / turns;
  const half = pitch * 0.5;
  const trackWidth = pitch;
  const rMax = rim - half;
  const rMin = Math.max(half * 1.05, 0.055);
  const startAngle = -Math.PI / 2 + 0.45;
  const thetaMax = turns * 2 * Math.PI;
  // Archimedean: r = rMax - b * θ
  const b = (rMax - rMin) / thetaMax;

  const samples = Math.max(800, size * 24);
  /** @type {{ θ: number, s: number, x: number, y: number, nx: number, ny: number }[]} */
  const spine = [];
  let s = 0;
  let prev = null;

  for (let i = 0; i <= samples; i += 1) {
    const θ = (i / samples) * thetaMax;
    const r = rMax - b * θ;
    // Screen counter-clockwise: decreasing polar angle.
    const φ = startAngle - θ;
    const cos = Math.cos(φ);
    const sin = Math.sin(φ);
    const x = 0.5 + r * cos;
    const y = 0.5 + r * sin;

    // dr/dθ = -b, dφ/dθ = -1
    // dx/dθ = -b cos(φ) + r sin(φ)
    // dy/dθ = -b sin(φ) - r cos(φ)
    const dx = -b * cos + r * sin;
    const dy = -b * sin - r * cos;
    const len = Math.hypot(dx, dy) || 1;
    const tx = dx / len;
    const ty = dy / len;
    // Normal: rotate tangent 90°. Pick the side that points roughly outward.
    let nx = -ty;
    let ny = tx;
    if (nx * cos + ny * sin < 0) {
      nx = -nx;
      ny = -ny;
    }

    if (prev) {
      s += Math.hypot(x - prev.x, y - prev.y);
    }
    spine.push({ θ, s, x, y, nx, ny });
    prev = { x, y };
  }

  const totalS = spine[spine.length - 1].s;

  function atArc(targetS) {
    const clamped = Math.max(0, Math.min(totalS, targetS));
    let lo = 0;
    let hi = spine.length - 1;
    while (lo < hi) {
      const mid = (lo + hi) >> 1;
      if (spine[mid].s < clamped) lo = mid + 1;
      else hi = mid;
    }
    const i = Math.max(1, lo);
    const a = spine[i - 1];
    const c = spine[i];
    const span = c.s - a.s || 1;
    const u = (clamped - a.s) / span;
    return {
      x: a.x + (c.x - a.x) * u,
      y: a.y + (c.y - a.y) * u,
      nx: a.nx + (c.nx - a.nx) * u,
      ny: a.ny + (c.ny - a.ny) * u,
      s: clamped,
    };
  }

  function offset(p, alongNormal) {
    return {
      x: p.x + p.nx * alongNormal,
      y: p.y + p.ny * alongNormal,
    };
  }

  function sampleSide(s0, s1, alongNormal, steps) {
    const pts = [];
    for (let i = 0; i <= steps; i += 1) {
      const t = i / steps;
      pts.push(offset(atArc(s0 + (s1 - s0) * t), alongNormal));
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
  const cellLen = totalS / size;
  const steps = 5;

  for (let i = 0; i < size; i += 1) {
    const s0 = i * cellLen;
    const s1 = (i + 1) * cellLen;
    const outerPts = sampleSide(s0, s1, half, steps);
    const innerPts = sampleSide(s0, s1, -half, steps);
    const mid = atArc((s0 + s1) / 2);
    const num = atArc(s0 + cellLen * 0.18);
    const numPt = offset(num, half * 0.45);

    cells.push({
      index: i,
      cx: mid.x,
      cy: mid.y,
      numX: numPt.x,
      numY: numPt.y,
      path: pathFrom(outerPts, innerPts),
    });
  }

  return { cells, turns, trackWidth };
}

/**
 * Letter font size as a fraction of the viewBox.
 * Sized from track width so inner cells stay as readable as outer ones.
 * @param {number} size
 * @param {number} [trackWidth]
 */
export function cellFontScale(size, trackWidth) {
  if (trackWidth) return Math.min(0.032, trackWidth * 0.58);
  if (size <= 36) return 0.028;
  if (size <= 48) return 0.024;
  if (size <= 64) return 0.02;
  return 0.016;
}

/**
 * Cell number font size as a fraction of the viewBox.
 * @param {number} size
 * @param {number} [trackWidth]
 */
export function cellNumberScale(size, trackWidth) {
  if (trackWidth) return Math.min(0.014, trackWidth * 0.28);
  if (size <= 36) return 0.014;
  if (size <= 48) return 0.012;
  if (size <= 64) return 0.01;
  return 0.009;
}
