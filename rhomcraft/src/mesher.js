import { shadedColor } from "./blocks.js";
import { RHOMBIC_FACES, RHOMBIC_VERTICES, FACE_NEIGHBORS, MESH_SCALE } from "./rhombic.js";
import { isSolid } from "./blocks.js";

/**
 * Build a flat mesh of all exposed rhombic faces in the world.
 * Returns TypedArrays ready for Three.js BufferGeometry.
 */
export function meshWorld(world, scale = MESH_SCALE) {
  const positions = [];
  const normals = [];
  const colors = [];

  for (const [key, id] of world.cells) {
    if (!isSolid(id)) continue;
    const [cx, cy, cz] = key.split(",").map(Number);
    const mask = world.exposedMask(cx, cy, cz);
    if (mask === 0) continue;

    for (let f = 0; f < 12; f++) {
      if (((mask >> f) & 1) === 0) continue;
      const [i0, i1, i2, i3] = RHOMBIC_FACES[f];
      const [nnx, nny, nnz] = FACE_NEIGHBORS[f];
      const inv = Math.SQRT2;
      const nx = nnx / inv;
      const ny = nny / inv;
      const nz = nnz / inv;
      const [cr, cg, cb] = shadedColor(id, f);
      const quad = [i0, i1, i2, i3];
      for (const [a, b, c] of [
        [0, 1, 2],
        [0, 2, 3],
      ]) {
        for (const vi of [quad[a], quad[b], quad[c]]) {
          const [vx, vy, vz] = RHOMBIC_VERTICES[vi];
          positions.push(cx + vx * scale, cy + vy * scale, cz + vz * scale);
          normals.push(nx, ny, nz);
          colors.push(cr, cg, cb);
        }
      }
    }
  }

  return {
    positions: new Float32Array(positions),
    normals: new Float32Array(normals),
    colors: new Float32Array(colors),
    vertexCount: positions.length / 3,
  };
}

/** Count triangles that would be emitted (for tests). */
export function countExposedFaces(world) {
  let faces = 0;
  for (const [key, id] of world.cells) {
    if (!isSolid(id)) continue;
    const [x, y, z] = key.split(",").map(Number);
    const mask = world.exposedMask(x, y, z);
    for (let f = 0; f < 12; f++) if ((mask >> f) & 1) faces += 1;
  }
  return faces;
}
