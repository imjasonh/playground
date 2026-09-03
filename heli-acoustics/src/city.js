// Axis-aligned city blocks. Coordinates match the Web Audio / three.js frame:
// +x right, +y up, +z toward the viewer (south if the player faces -z / "north").
// Main N–S avenue along x≈0; E–W cross streets between block rows.

export const SPEED_OF_SOUND = 343; // m/s

// Large street-canyon grid (~600 m across). Heights are meters above the street.
export const BUILDINGS = [
  // Inner four corners of the main intersection.
  { id: 'sw', min: [-160, 0, -160], max: [-30, 156, -30] },
  { id: 'se', min: [30, 0, -160], max: [160, 236, -30] },
  { id: 'nw', min: [-160, 0, 30], max: [-30, 280, 160] },
  { id: 'ne-low', min: [30, 0, 30], max: [160, 128, 95] },
  { id: 'ne-tall', min: [30, 0, 110], max: [160, 210, 200] },
  // Outer ring so the city reads as a real district, not five boxes.
  { id: 'far-sw', min: [-160, 0, -320], max: [-30, 120, -180] },
  { id: 'far-se', min: [30, 0, -320], max: [160, 180, -180] },
  { id: 'far-w', min: [-320, 0, 30], max: [-180, 200, 160] },
  { id: 'far-e', min: [180, 0, 30], max: [320, 165, 160] },
  { id: 'far-nw', min: [-160, 0, 220], max: [-30, 175, 360] },
  { id: 'far-ne', min: [30, 0, 220], max: [160, 195, 360] },
];

export const GROUND = { y: 0 };

/** City extents for ground plane / camera / flight legs. */
export function cityBounds(buildings = BUILDINGS) {
  let x0 = Infinity;
  let x1 = -Infinity;
  let z0 = Infinity;
  let z1 = -Infinity;
  let yMax = 0;
  for (const b of buildings) {
    x0 = Math.min(x0, b.min[0]);
    x1 = Math.max(x1, b.max[0]);
    z0 = Math.min(z0, b.min[2]);
    z1 = Math.max(z1, b.max[2]);
    yMax = Math.max(yMax, b.max[1]);
  }
  return { x0, x1, z0, z1, yMax, spanX: x1 - x0, spanZ: z1 - z0 };
}

// Vertical facade rectangles used for image-source reflections.
export function buildingFaces(buildings = BUILDINGS) {
  const faces = [];
  for (const b of buildings) {
    const [x0, y0, z0] = b.min;
    const [x1, y1, z1] = b.max;
    faces.push(
      { id: `${b.id}-w`, building: b.id, axis: 'x', value: x0, outward: -1, u0: z0, u1: z1, v0: y0, v1: y1 },
      { id: `${b.id}-e`, building: b.id, axis: 'x', value: x1, outward: +1, u0: z0, u1: z1, v0: y0, v1: y1 },
      { id: `${b.id}-n`, building: b.id, axis: 'z', value: z0, outward: -1, u0: x0, u1: x1, v0: y0, v1: y1 },
      { id: `${b.id}-s`, building: b.id, axis: 'z', value: z1, outward: +1, u0: x0, u1: x1, v0: y0, v1: y1 },
    );
  }
  return faces;
}

/**
 * Helicopter flight modes.
 * - orbit: elliptical lap mid-canyon (legacy demo path)
 * - traverse: straight lanes across the city, pause, then reverse on another lane
 */
export const FLIGHT_MODES = Object.freeze(['orbit', 'traverse']);

const TRAVERSE_CRUISE = 22; // m/s
const TRAVERSE_HEIGHT = 95;
const TRAVERSE_PAUSE = 4; // seconds between legs

function traverseLegs(bounds) {
  const pad = 40;
  const xL = bounds.x0 - pad;
  const xR = bounds.x1 + pad;
  const zS = bounds.z0 - pad;
  const zN = bounds.z1 + pad;
  const y = TRAVERSE_HEIGHT;
  // Alternate E–W and W–E on different latitudes, then N–S / S–N.
  return [
    { from: [xL, y, -90], to: [xR, y, -90] },
    { from: [xR, y, 90], to: [xL, y, 90] },
    { from: [xL, y, 240], to: [xR, y, 240] },
    { from: [0, y, zS], to: [0, y, zN] },
    { from: [90, y, zN], to: [90, y, zS] },
    { from: [-90, y, zS], to: [-90, y, zN] },
  ];
}

function lerp3(a, b, u) {
  return [
    a[0] + (b[0] - a[0]) * u,
    a[1] + (b[1] - a[1]) * u,
    a[2] + (b[2] - a[2]) * u,
  ];
}

function legDuration(leg, speed = TRAVERSE_CRUISE) {
  const dx = leg.to[0] - leg.from[0];
  const dy = leg.to[1] - leg.from[1];
  const dz = leg.to[2] - leg.from[2];
  return Math.hypot(dx, dy, dz) / speed;
}

function traverseSchedule(bounds = cityBounds()) {
  const legs = traverseLegs(bounds);
  const schedule = [];
  let t0 = 0;
  for (const leg of legs) {
    const dur = legDuration(leg);
    schedule.push({ kind: 'fly', leg, t0, t1: t0 + dur });
    t0 += dur;
    schedule.push({ kind: 'pause', at: leg.to.slice(), t0, t1: t0 + TRAVERSE_PAUSE });
    t0 += TRAVERSE_PAUSE;
  }
  return { schedule, period: t0 };
}

let _traverseCache = null;
function getTraverse() {
  if (!_traverseCache) _traverseCache = traverseSchedule();
  return _traverseCache;
}

function traverseSample(t) {
  const { schedule, period } = getTraverse();
  const tau = ((t % period) + period) % period;
  for (const seg of schedule) {
    if (tau < seg.t1) {
      if (seg.kind === 'pause') {
        return { position: seg.at.slice(), velocity: [0, 0, 0] };
      }
      const u = (tau - seg.t0) / Math.max(1e-6, seg.t1 - seg.t0);
      const position = lerp3(seg.leg.from, seg.leg.to, u);
      const dur = seg.t1 - seg.t0;
      const velocity = [
        (seg.leg.to[0] - seg.leg.from[0]) / dur,
        (seg.leg.to[1] - seg.leg.from[1]) / dur,
        (seg.leg.to[2] - seg.leg.from[2]) / dur,
      ];
      return { position, velocity };
    }
  }
  const last = schedule[schedule.length - 1];
  return { position: (last.at || last.leg.to).slice(), velocity: [0, 0, 0] };
}

export function helicopterPath(t, { mode = 'orbit', radius = 110, height = 95, period = 28, center = [0, 0, 40] } = {}) {
  if (mode === 'traverse') return traverseSample(t).position;
  const a = (t / period) * Math.PI * 2;
  return [
    center[0] + radius * 0.55 * Math.sin(a),
    height + 14 * Math.sin(a * 2),
    center[2] + radius * Math.cos(a),
  ];
}

/** Analytic velocity (m/s) for the active flight mode. */
export function helicopterVelocity(t, opts = {}) {
  const mode = opts.mode || 'orbit';
  if (mode === 'traverse') return traverseSample(t).velocity;
  const { radius = 110, period = 28 } = opts;
  const a = (t / period) * Math.PI * 2;
  const w = (Math.PI * 2) / period;
  return [
    radius * 0.55 * Math.cos(a) * w,
    14 * Math.cos(a * 2) * 2 * w,
    -radius * Math.sin(a) * w,
  ];
}
