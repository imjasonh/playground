// Geometry for a spin-draw disc.
//
// A picture is a list of polylines. The disc stores each piece rotated
// about the pin. You align a number with a fixed dot, then trace the
// line whose number is upright. Turning the disc by that piece's angle
// puts the line back where it belongs on the paper.

export const REFERENCE_ANGLE = Math.PI / 2;

export function rotatePoint(point, theta) {
  const c = Math.cos(theta);
  const s = Math.sin(theta);
  return {
    x: point.x * c - point.y * s,
    y: point.x * s + point.y * c,
  };
}

export function polylineLength(points) {
  let total = 0;
  for (let i = 1; i < points.length; i += 1) {
    total += Math.hypot(points[i].x - points[i - 1].x, points[i].y - points[i - 1].y);
  }
  return total;
}

export function totalLength(strokes) {
  let total = 0;
  for (const stroke of strokes) {
    total += polylineLength(stroke);
  }
  return total;
}

export function normalizeStrokes(strokes) {
  const out = [];
  for (const stroke of strokes || []) {
    const pts = [];
    for (const point of stroke) {
      if (!point || !Number.isFinite(point.x) || !Number.isFinite(point.y)) {
        continue;
      }
      const last = pts[pts.length - 1];
      if (!last || last.x !== point.x || last.y !== point.y) {
        pts.push({ x: point.x, y: point.y });
      }
    }
    if (pts.length >= 2) {
      out.push(pts);
    }
  }
  return out;
}

function clampInt(value, min, max) {
  const n = Math.round(Number(value));
  if (!Number.isFinite(n)) {
    return min;
  }
  return Math.min(max, Math.max(min, n));
}

// Length-weighted center, so a densely sampled curve does not pull the picture.
function centroid(strokes) {
  let weight = 0;
  let sx = 0;
  let sy = 0;
  for (const stroke of strokes) {
    for (let i = 1; i < stroke.length; i += 1) {
      const a = stroke[i - 1];
      const b = stroke[i];
      const len = Math.hypot(b.x - a.x, b.y - a.y);
      sx += ((a.x + b.x) / 2) * len;
      sy += ((a.y + b.y) / 2) * len;
      weight += len;
    }
  }
  return { x: sx / weight, y: sy / weight };
}

// Pack the picture into the ring between `inner` and `outer`, below the pin.
// Pieces then swing around the pin instead of stacking on top of each other.
export function fitStrokes(strokes, inner, outer) {
  const center = centroid(strokes);
  let maxR = 0;
  for (const stroke of strokes) {
    for (const point of stroke) {
      maxR = Math.max(maxR, Math.hypot(point.x - center.x, point.y - center.y));
    }
  }
  const band = (outer - inner) / 2;
  const scale = maxR > 1e-9 ? band / maxR : 1;
  const orbit = inner + band;
  return strokes.map((stroke) =>
    stroke.map((point) => ({
      x: (point.x - center.x) * scale,
      y: (point.y - center.y) * scale - orbit,
    })),
  );
}

function pointAlong(poly, distance) {
  let left = distance;
  for (let i = 1; i < poly.length; i += 1) {
    const a = poly[i - 1];
    const b = poly[i];
    const seg = Math.hypot(b.x - a.x, b.y - a.y);
    if (left <= seg || i === poly.length - 1) {
      const t = seg === 0 ? 0 : Math.min(1, left / seg);
      return { x: a.x + (b.x - a.x) * t, y: a.y + (b.y - a.y) * t };
    }
    left -= seg;
  }
  return { x: poly[0].x, y: poly[0].y };
}

function labelAnchor(polylines, maxRadius) {
  let best = polylines[0];
  let bestLen = -1;
  for (const poly of polylines) {
    const len = polylineLength(poly);
    if (len > bestLen) {
      best = poly;
      bestLen = len;
    }
  }
  const mid = pointAlong(best, bestLen / 2);
  const prev = pointAlong(best, Math.max(0, bestLen / 2 - 0.75));
  let tx = mid.x - prev.x;
  let ty = mid.y - prev.y;
  const tlen = Math.hypot(tx, ty) || 1;
  tx /= tlen;
  ty /= tlen;
  let nx = -ty;
  let ny = tx;
  if (nx * mid.x + ny * mid.y < 0) {
    nx = -nx;
    ny = -ny;
  }
  let x = mid.x + nx * 5;
  let y = mid.y + ny * 5;
  const r = Math.hypot(x, y);
  if (r > maxRadius) {
    x *= maxRadius / r;
    y *= maxRadius / r;
  }
  return { x, y };
}

// Split strokes into `count` pieces of nearly equal length.
// A piece can hold several polylines. Strokes are not joined.
export function splitStrokes(strokes, count) {
  const total = totalLength(strokes);
  const steps = clampInt(count, 1, 80);
  if (!(total > 0)) {
    return [];
  }
  const target = total / steps;
  const pieces = [];
  let piece = [];
  let poly = null;
  let filled = 0;

  function closePiece(cut) {
    if (poly && poly.length >= 2) {
      piece.push(poly);
    }
    if (piece.length > 0) {
      pieces.push(piece);
    }
    piece = [];
    poly = [{ x: cut.x, y: cut.y }];
    filled = 0;
  }

  for (const stroke of strokes) {
    poly = [{ x: stroke[0].x, y: stroke[0].y }];
    for (let i = 1; i < stroke.length; i += 1) {
      let ax = poly[poly.length - 1].x;
      let ay = poly[poly.length - 1].y;
      const bx = stroke[i].x;
      const by = stroke[i].y;
      let remain = Math.hypot(bx - ax, by - ay);
      let guard = 0;
      const guardLimit = steps + 2;
      while (remain > 1e-8 && pieces.length < steps - 1 && guard < guardLimit) {
        guard += 1;
        const room = target - filled;
        if (room <= 1e-8) {
          closePiece({ x: ax, y: ay });
        } else if (remain > room + 1e-8) {
          const t = room / remain;
          const cut = { x: ax + (bx - ax) * t, y: ay + (by - ay) * t };
          poly.push(cut);
          filled = target;
          closePiece(cut);
          ax = cut.x;
          ay = cut.y;
          remain = Math.hypot(bx - ax, by - ay);
        } else {
          guard = guardLimit;
        }
      }
      const prev = poly[poly.length - 1];
      const seg = Math.hypot(bx - prev.x, by - prev.y);
      if (seg > 1e-9) {
        poly.push({ x: bx, y: by });
        filled += seg;
      }
    }
    if (poly && poly.length >= 2) {
      piece.push(poly);
    }
    poly = null;
  }
  if (piece.length > 0) {
    pieces.push(piece);
  }
  return pieces;
}

export function buildDisc(strokes, options = {}) {
  const requested = clampInt(options.steps ?? 16, 1, 80);
  const radius = options.radius ?? 100;
  const hole = options.hole ?? 2.4;
  const outer = radius - 24;
  const inner = hole + 8;
  const clean = normalizeStrokes(strokes);
  if (!(totalLength(clean) > 0)) {
    return {
      radius,
      hole,
      inner,
      outer,
      rim: radius - 11,
      steps: [],
      fitted: [],
    };
  }
  const fitted = fitStrokes(clean, inner, outer);
  const pieces = splitStrokes(fitted, requested);
  const count = pieces.length;
  const steps = pieces.map((paper, index) => {
    const theta = (Math.PI * 2 * index) / count;
    const local = paper.map((poly) => poly.map((point) => rotatePoint(point, -theta)));
    return {
      index,
      number: index + 1,
      theta,
      labelAngle: REFERENCE_ANGLE - theta,
      paper,
      local,
      label: labelAnchor(local, outer - 1),
    };
  });
  return {
    radius,
    hole,
    inner,
    outer,
    rim: radius - 11,
    steps,
    fitted,
  };
}

export function paperPolylines(step) {
  return step.local.map((poly) => poly.map((point) => rotatePoint(point, step.theta)));
}
