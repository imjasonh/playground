// Axis-aligned city blocks. Coordinates match the Web Audio / three.js frame:
// +x right, +y up, +z toward the viewer (south if the player faces -z / "north").
// The main avenue runs along z through x=0.

export const SPEED_OF_SOUND = 343; // m/s

// Tall street-canyon blocks so the heli is usually behind or bouncing off
// facades rather than clear-sky. Heights are meters above the street.
export const BUILDINGS = [
  { id: 'sw', min: [-80, 0, -80], max: [-20, 78, -20] },
  { id: 'se', min: [20, 0, -80], max: [80, 118, -20] },
  { id: 'nw', min: [-80, 0, 20], max: [-20, 140, 80] },
  { id: 'ne-low', min: [20, 0, 20], max: [80, 64, 55] },
  { id: 'ne-tall', min: [20, 0, 60], max: [80, 105, 100] },
];

export const GROUND = { y: 0 };

// Vertical facade rectangles used for image-source reflections.
// Each face is a finite rectangle in a constant-x or constant-z plane.
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

// Flight path sits mid-canyon so rooftops and facades block the direct path
// for much of the orbit, and order-1/2 facade hits stay common.
export function helicopterPath(t, { radius = 55, height = 52, period = 18, center = [0, 0, 10] } = {}) {
  const a = (t / period) * Math.PI * 2;
  return [
    center[0] + radius * 0.55 * Math.sin(a),
    height + 10 * Math.sin(a * 2),
    center[2] + radius * Math.cos(a),
  ];
}

/** Analytic velocity (m/s) of `helicopterPath` at time t. */
export function helicopterVelocity(t, opts = {}) {
  const { radius = 55, period = 18 } = opts;
  const a = (t / period) * Math.PI * 2;
  const w = (Math.PI * 2) / period;
  return [
    radius * 0.55 * Math.cos(a) * w,
    10 * Math.cos(a * 2) * 2 * w,
    -radius * Math.sin(a) * w,
  ];
}
