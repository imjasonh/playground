// Turn a dark-on-light bitmap into polylines the disc can split.
// Coordinates stay in pixel space, y down. The page flips y when it
// commits a picture.

import { polylineLength } from "./rotadraw.js";

const NX = [1, 1, 0, -1, -1, -1, 0, 1];
const NY = [0, 1, 1, 1, 0, -1, -1, -1];

export function maskFromRgba(data, width, height, threshold) {
  const mask = new Uint8Array(width * height);
  const limit = Number(threshold);
  for (let i = 0; i < mask.length; i += 1) {
    const o = i * 4;
    const alpha = data[o + 3] / 255;
    const lum =
      (0.2126 * data[o] + 0.7152 * data[o + 1] + 0.0722 * data[o + 2]) * alpha +
      255 * (1 - alpha);
    if (lum < limit) {
      mask[i] = 1;
    }
  }
  return mask;
}

function traceBlob(mask, width, height, sx, sy) {
  const contour = [];
  let cx = sx;
  let cy = sy;
  let back = 4;
  const limit = width * height * 4;
  for (let guard = 0; guard < limit; guard += 1) {
    contour.push({ x: cx, y: cy });
    let found = -1;
    for (let k = 0; k < 8; k += 1) {
      const dir = (back + 1 + k) % 8;
      const nx = cx + NX[dir];
      const ny = cy + NY[dir];
      if (nx >= 0 && ny >= 0 && nx < width && ny < height && mask[ny * width + nx] === 1) {
        found = dir;
        break;
      }
    }
    if (found < 0) {
      break;
    }
    cx += NX[found];
    cy += NY[found];
    back = (found + 4) % 8;
    if (cx === sx && cy === sy) {
      break;
    }
  }
  return contour;
}

export function traceContours(mask, width, height) {
  const seen = new Uint8Array(width * height);
  const contours = [];
  for (let y = 0; y < height; y += 1) {
    for (let x = 0; x < width; x += 1) {
      const start = y * width + x;
      const leftIsInk = x > 0 && mask[start - 1] === 1;
      if (mask[start] === 1 && seen[start] === 0 && !leftIsInk) {
        const contour = traceBlob(mask, width, height, x, y);
        for (const point of contour) {
          const px = Math.round(point.x);
          const py = Math.round(point.y);
          if (px >= 0 && py >= 0 && px < width && py < height) {
            seen[py * width + px] = 1;
          }
        }
        if (contour.length >= 4) {
          contours.push(contour);
        }
      }
    }
  }
  return contours;
}

function pointLineDistance(point, a, b) {
  const dx = b.x - a.x;
  const dy = b.y - a.y;
  const len = Math.hypot(dx, dy);
  if (len === 0) {
    return Math.hypot(point.x - a.x, point.y - a.y);
  }
  const t = ((point.x - a.x) * dx + (point.y - a.y) * dy) / (len * len);
  const clamped = Math.min(1, Math.max(0, t));
  return Math.hypot(point.x - (a.x + clamped * dx), point.y - (a.y + clamped * dy));
}

export function simplifyPolyline(points, epsilon) {
  if (points.length < 3) {
    return points.map((point) => ({ x: point.x, y: point.y }));
  }
  return rdp(points, epsilon);
}

function rdp(points, epsilon) {
  let max = 0;
  let index = 0;
  const a = points[0];
  const b = points[points.length - 1];
  for (let i = 1; i < points.length - 1; i += 1) {
    const d = pointLineDistance(points[i], a, b);
    if (d > max) {
      max = d;
      index = i;
    }
  }
  if (max > epsilon) {
    const left = rdp(points.slice(0, index + 1), epsilon);
    const right = rdp(points.slice(index), epsilon);
    return left.slice(0, -1).concat(right);
  }
  return [
    { x: a.x, y: a.y },
    { x: b.x, y: b.y },
  ];
}

export function strokesFromMask(mask, width, height, options = {}) {
  const minLength = options.minLength ?? 12;
  const epsilon = options.epsilon ?? 1.25;
  const maxStrokes = options.maxStrokes ?? 24;
  const contours = traceContours(mask, width, height);
  const simplified = [];
  for (const contour of contours) {
    const simple = simplifyPolyline(contour, epsilon);
    if (simple.length >= 2 && polylineLength(simple) >= minLength) {
      simplified.push(simple);
    }
  }
  simplified.sort((a, b) => polylineLength(b) - polylineLength(a));
  return simplified.slice(0, maxStrokes);
}
