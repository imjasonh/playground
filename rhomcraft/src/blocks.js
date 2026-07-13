/** Block palette for Rhomcraft. */

export const AIR = 0;

export const BLOCKS = Object.freeze({
  0: { id: 0, name: "Air", solid: false, color: null },
  1: { id: 1, name: "Grass", solid: true, color: [0.34, 0.62, 0.28] },
  2: { id: 2, name: "Dirt", solid: true, color: [0.45, 0.3, 0.18] },
  3: { id: 3, name: "Stone", solid: true, color: [0.48, 0.5, 0.54] },
  4: { id: 4, name: "Sand", solid: true, color: [0.82, 0.74, 0.52] },
  5: { id: 5, name: "Log", solid: true, color: [0.4, 0.26, 0.14] },
  6: { id: 6, name: "Leaves", solid: true, color: [0.22, 0.48, 0.3] },
  7: { id: 7, name: "Crystal", solid: true, color: [0.2, 0.72, 0.78] },
  8: { id: 8, name: "Basalt", solid: true, color: [0.18, 0.2, 0.24] },
  9: { id: 9, name: "Clay", solid: true, color: [0.62, 0.42, 0.36] },
});

export const PLACEABLE = Object.freeze([1, 2, 3, 4, 5, 6, 7, 8, 9]);

export function isSolid(id) {
  return id > 0 && BLOCKS[id]?.solid === true;
}

export function blockColor(id) {
  return BLOCKS[id]?.color ?? [1, 0, 1];
}

/** Slight per-face shade so the 12-gon reads clearly. */
export function shadedColor(id, faceIndex) {
  const [r, g, b] = blockColor(id);
  // Alternate shade by face axis family
  const family = faceIndex % 3;
  const shade = 0.78 + family * 0.08 + (faceIndex % 2) * 0.04;
  return [r * shade, g * shade, b * shade];
}
