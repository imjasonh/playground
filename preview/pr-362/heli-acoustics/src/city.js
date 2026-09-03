// Axis-aligned city blocks for the M1/M2 urban scene. Coordinates match the
// Web Audio / three.js frame: +x right, +y up, +z toward the viewer (south if
// the player faces -z / "north"). The main avenue runs along z through x=0.

export const SPEED_OF_SOUND = 343; // m/s

// Each building is an AABB: min/max corners. Heights vary so the skyline is
// not a flat wall; the street canyon is ~40m wide.
export const BUILDINGS = [
  { id: 'sw', min: [-80, 0, -80], max: [-20, 32, -20] },
  { id: 'se', min: [20, 0, -80], max: [80, 48, -20] },
  { id: 'nw', min: [-80, 0, 20], max: [-20, 56, 80] },
  { id: 'ne-low', min: [20, 0, 20], max: [80, 24, 55] },
  { id: 'ne-tall', min: [20, 0, 60], max: [80, 44, 100] },
];

export const GROUND = { y: 0 };

// Vertical facade rectangles used for order-1 image-source reflections.
// Each face is a finite rectangle in a constant-x or constant-z plane.
export function buildingFaces(buildings = BUILDINGS) {
  const faces = [];
  for (const b of buildings) {
    const [x0, y0, z0] = b.min;
    const [x1, y1, z1] = b.max;
    // -x face (west), +x face (east), -z face (north in our map), +z face (south)
    faces.push(
      { id: `${b.id}-w`, building: b.id, axis: 'x', value: x0, outward: -1, u0: z0, u1: z1, v0: y0, v1: y1 },
      { id: `${b.id}-e`, building: b.id, axis: 'x', value: x1, outward: +1, u0: z0, u1: z1, v0: y0, v1: y1 },
      { id: `${b.id}-n`, building: b.id, axis: 'z', value: z0, outward: -1, u0: x0, u1: x1, v0: y0, v1: y1 },
      { id: `${b.id}-s`, building: b.id, axis: 'z', value: z1, outward: +1, u0: x0, u1: x1, v0: y0, v1: y1 },
    );
  }
  return faces;
}

export function helicopterPath(t, { radius = 55, height = 38, period = 18, center = [0, 0, 10] } = {}) {
  const a = (t / period) * Math.PI * 2;
  // Elongated oval along the avenue so the heli spends time over the street
  // and also ducks behind the taller NW / SE blocks.
  return [
    center[0] + radius * 0.55 * Math.sin(a),
    height + 6 * Math.sin(a * 2),
    center[2] + radius * Math.cos(a),
  ];
}
