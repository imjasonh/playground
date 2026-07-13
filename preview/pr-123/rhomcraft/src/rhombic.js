/**
 * Rhombic dodecahedron voxel geometry on an FCC lattice.
 *
 * Cells live at integer (x, y, z) where x+y+z is even. Adjacent cells share a
 * face along the 12 directions (±1,±1,0) and permutations. World units match
 * lattice units; the mesh is scaled by 1/2 so neighboring cells kiss.
 */

export const LATTICE_SCALE = 1;
export const MESH_SCALE = 0.5;

/** 14 vertices of the canonical rhombic dodecahedron (before MESH_SCALE). */
export const RHOMBIC_VERTICES = Object.freeze([
  [1, 1, 1],
  [1, 1, -1],
  [1, -1, 1],
  [1, -1, -1],
  [-1, 1, 1],
  [-1, 1, -1],
  [-1, -1, 1],
  [-1, -1, -1],
  [2, 0, 0],
  [-2, 0, 0],
  [0, 2, 0],
  [0, -2, 0],
  [0, 0, 2],
  [0, 0, -2],
]);

/** 12 face-neighbor offsets (also face normals before normalization). */
export const FACE_NEIGHBORS = Object.freeze([
  [1, 1, 0],
  [1, -1, 0],
  [-1, 1, 0],
  [-1, -1, 0],
  [1, 0, 1],
  [1, 0, -1],
  [-1, 0, 1],
  [-1, 0, -1],
  [0, 1, 1],
  [0, 1, -1],
  [0, -1, 1],
  [0, -1, -1],
]);

/**
 * Quad index lists (CCW, outward) into RHOMBIC_VERTICES, one per FACE_NEIGHBORS.
 * Derived by taking the four vertices maximizing n·v for each neighbor normal.
 */
export const RHOMBIC_FACES = Object.freeze([
  [10, 0, 8, 1], // +x+y
  [11, 3, 8, 2], // +x-y
  [10, 5, 9, 4], // -x+y
  [11, 6, 9, 7], // -x-y
  [12, 2, 8, 0], // +x+z
  [13, 1, 8, 3], // +x-z
  [12, 4, 9, 6], // -x+z
  [13, 7, 9, 5], // -x-z
  [12, 0, 10, 4], // +y+z
  [13, 5, 10, 1], // +y-z
  [12, 6, 11, 2], // -y+z
  [13, 3, 11, 7], // -y-z
]);

export function isFccCell(x, y, z) {
  return ((x + y + z) & 1) === 0;
}

export function cellKey(x, y, z) {
  return `${x},${y},${z}`;
}

export function parseCellKey(key) {
  const [x, y, z] = key.split(",").map(Number);
  return [x, y, z];
}

/** World-space center of lattice cell (x,y,z). */
export function cellCenter(x, y, z, scale = LATTICE_SCALE) {
  return [x * scale, y * scale, z * scale];
}

/** Scaled mesh vertex positions for a cell centered at the origin. */
export function unitMeshVertices(scale = MESH_SCALE) {
  return RHOMBIC_VERTICES.map(([x, y, z]) => [x * scale, y * scale, z * scale]);
}

export function faceNormal(faceIndex) {
  const [nx, ny, nz] = FACE_NEIGHBORS[faceIndex];
  const len = Math.hypot(nx, ny, nz);
  return [nx / len, ny / len, nz / len];
}

/**
 * Nearest FCC lattice point to a world-space position (lattice units).
 * Standard even-sum cubic rounding.
 */
export function nearestFcc(px, py, pz) {
  let x = Math.round(px);
  let y = Math.round(py);
  let z = Math.round(pz);
  if (((x + y + z) & 1) === 0) return [x, y, z];

  const fx = px - x;
  const fy = py - y;
  const fz = pz - z;
  const ax = Math.abs(fx);
  const ay = Math.abs(fy);
  const az = Math.abs(fz);

  if (ax >= ay && ax >= az) x += fx >= 0 ? 1 : -1;
  else if (ay >= az) y += fy >= 0 ? 1 : -1;
  else z += fz >= 0 ? 1 : -1;

  return [x, y, z];
}

/**
 * Approximate signed distance to a unit rhombic dodecahedron centered at origin
 * (mesh-scaled). Negative = inside. Uses the 12 half-spaces n·p <= MESH_SCALE * √2.
 */
export function rhombicSignedDistance(px, py, pz, scale = MESH_SCALE) {
  // Unscaled face planes are n·v = 2 with ||n_unnormalized||; after *scale,
  // plane distance from center is scale * √2.
  const limit = scale * Math.SQRT2;
  let maxProj = -Infinity;
  for (const [nx, ny, nz] of FACE_NEIGHBORS) {
    const len = Math.SQRT2; // ||(±1,±1,0)||
    const proj = (nx * px + ny * py + nz * pz) / len;
    if (proj > maxProj) maxProj = proj;
  }
  return maxProj - limit;
}

export function pointInRhombic(px, py, pz, cx, cy, cz, scale = MESH_SCALE) {
  return rhombicSignedDistance(px - cx, py - cy, pz - cz, scale) <= 1e-6;
}

/** Insphere radius (distance to face) and circumsphere (distance to vertex). */
export function rhombicRadii(scale = MESH_SCALE) {
  return {
    inRadius: scale * Math.SQRT2,
    circumRadius: scale * 2, // axis vertex (±2,0,0) * scale
  };
}

/**
 * Build triangle lists for exposed faces of one cell.
 * @returns {{ positions: number[], normals: number[], uvs: number[] }}
 */
export function appendRhombicCellMesh(
  out,
  cx,
  cy,
  cz,
  exposedFaceMask,
  scale = MESH_SCALE,
) {
  const verts = RHOMBIC_VERTICES;
  for (let f = 0; f < 12; f++) {
    if (((exposedFaceMask >> f) & 1) === 0) continue;
    const [n0, n1, n2, n3] = RHOMBIC_FACES[f];
    const [nx, ny, nz] = faceNormal(f);
    const quad = [n0, n1, n2, n3];
    // two triangles: 0-1-2 and 0-2-3
    const tris = [
      [0, 1, 2],
      [0, 2, 3],
    ];
    for (const [a, b, c] of tris) {
      for (const corner of [quad[a], quad[b], quad[c]]) {
        const [vx, vy, vz] = verts[corner];
        out.positions.push(cx + vx * scale, cy + vy * scale, cz + vz * scale);
        out.normals.push(nx, ny, nz);
      }
    }
  }
  return out;
}

export function emptyMeshBuffers() {
  return { positions: [], normals: [], colors: [] };
}

/** Verify face windings produce outward normals matching FACE_NEIGHBORS. */
export function validateFaceWindings(epsilon = 1e-6) {
  const issues = [];
  for (let f = 0; f < 12; f++) {
    const [i0, i1, i2] = RHOMBIC_FACES[f];
    const a = RHOMBIC_VERTICES[i0];
    const b = RHOMBIC_VERTICES[i1];
    const c = RHOMBIC_VERTICES[i2];
    const e1 = [b[0] - a[0], b[1] - a[1], b[2] - a[2]];
    const e2 = [c[0] - a[0], c[1] - a[1], c[2] - a[2]];
    const cross = [
      e1[1] * e2[2] - e1[2] * e2[1],
      e1[2] * e2[0] - e1[0] * e2[2],
      e1[0] * e2[1] - e1[1] * e2[0],
    ];
    const [nx, ny, nz] = FACE_NEIGHBORS[f];
    const dot = cross[0] * nx + cross[1] * ny + cross[2] * nz;
    if (dot <= epsilon) {
      issues.push({ face: f, neighbor: [nx, ny, nz], dot });
    }
  }
  return issues;
}
