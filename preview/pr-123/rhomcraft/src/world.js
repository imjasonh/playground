import { AIR, isSolid, PLACEABLE } from "./blocks.js";
import { fbm2, valueNoise3 } from "./noise.js";
import {
  FACE_NEIGHBORS,
  cellKey,
  isFccCell,
  nearestFcc,
  pointInRhombic,
} from "./rhombic.js";

/**
 * Sparse FCC voxel world. Keys are "x,y,z" for even-sum lattice cells.
 */
export class World {
  constructor({ seed = 42, radius = 28, height = 18 } = {}) {
    this.seed = seed;
    this.radius = radius;
    this.height = height;
    /** @type {Map<string, number>} */
    this.cells = new Map();
    this.version = 0;
  }

  get(x, y, z) {
    return this.cells.get(cellKey(x, y, z)) ?? AIR;
  }

  set(x, y, z, id) {
    if (!isFccCell(x, y, z)) return false;
    const key = cellKey(x, y, z);
    if (id === AIR) {
      if (!this.cells.has(key)) return false;
      this.cells.delete(key);
    } else {
      this.cells.set(key, id);
    }
    this.version += 1;
    return true;
  }

  hasSolid(x, y, z) {
    return isSolid(this.get(x, y, z));
  }

  neighborsOf(x, y, z) {
    return FACE_NEIGHBORS.map(([dx, dy, dz]) => [x + dx, y + dy, z + dz]);
  }

  /** Bitmask of faces that are exposed (neighbor empty/non-solid). */
  exposedMask(x, y, z) {
    let mask = 0;
    for (let f = 0; f < 12; f++) {
      const [dx, dy, dz] = FACE_NEIGHBORS[f];
      if (!this.hasSolid(x + dx, y + dy, z + dz)) mask |= 1 << f;
    }
    return mask;
  }

  surfaceHeight(x, z) {
    const n = fbm2(x * 0.045, z * 0.045, this.seed, 5);
    const ridge = fbm2(x * 0.02 + 40, z * 0.02 - 10, this.seed + 7, 3);
    const h = 3 + n * 9 + ridge * ridge * 5;
    return Math.floor(h);
  }

  generate() {
    this.cells.clear();
    const r = this.radius;
    for (let x = -r; x <= r; x++) {
      for (let z = -r; z <= r; z++) {
        if ((x + z) * (x + z) > r * r * 1.15) continue;
        const surface = this.surfaceHeight(x, z);
        for (let y = 0; y <= Math.min(surface, this.height); y++) {
          if (!isFccCell(x, y, z)) continue;
          let id;
          if (y === surface) {
            id = surface <= 4 ? 4 : 1; // sand near "sea level", else grass
          } else if (y >= surface - 2) {
            id = surface <= 4 ? 4 : 2; // dirt
          } else if (y >= surface - 5) {
            id = 3; // stone
          } else {
            id = valueNoise3(x * 0.2, y * 0.2, z * 0.2, this.seed + 3) > 0.78 ? 8 : 3;
          }
          // crystal veins
          if (
            y < surface - 2 &&
            valueNoise3(x * 0.15, y * 0.15, z * 0.15, this.seed + 99) > 0.92
          ) {
            id = 7;
          }
          this.cells.set(cellKey(x, y, z), id);
        }

        // occasional trees on grass
        if (
          surface > 5 &&
          isFccCell(x, surface, z) &&
          valueNoise3(x, 0, z, this.seed + 55) > 0.965
        ) {
          this.plantTree(x, surface + 1, z);
        }
      }
    }
    this.version += 1;
    return this;
  }

  plantTree(x, y, z) {
    const trunk = 3 + Math.floor(valueNoise3(x, y, z, this.seed + 12) * 3);
    for (let i = 0; i < trunk; i++) {
      const ty = y + i;
      if (!isFccCell(x, ty, z)) continue;
      this.cells.set(cellKey(x, ty, z), 5);
    }
    const top = y + trunk - 1;
    for (const [dx, dy, dz] of [
      [0, 1, 0],
      [1, 1, 1],
      [1, 1, -1],
      [-1, 1, 1],
      [-1, 1, -1],
      [2, 0, 0],
      [-2, 0, 0],
      [0, 0, 2],
      [0, 0, -2],
      [0, 2, 0],
    ]) {
      const lx = x + dx;
      const ly = top + dy;
      const lz = z + dz;
      if (!isFccCell(lx, ly, lz)) continue;
      if (this.get(lx, ly, lz) === AIR) this.cells.set(cellKey(lx, ly, lz), 6);
    }
  }

  /** Find a safe spawn on the +Y surface near origin. */
  findSpawn() {
    for (let r = 0; r < this.radius; r++) {
      for (let x = -r; x <= r; x++) {
        for (let z = -r; z <= r; z++) {
          if (Math.max(Math.abs(x), Math.abs(z)) !== r) continue;
          for (let y = this.height; y >= 0; y--) {
            if (!isFccCell(x, y, z)) continue;
            if (this.hasSolid(x, y, z) && !this.hasSolid(x, y + 1, z) && !this.hasSolid(x, y + 2, z)) {
              return { x: x + 0.0, y: y + 1.6, z: z + 0.0 };
            }
          }
        }
      }
    }
    return { x: 0, y: 12, z: 0 };
  }

  /**
   * Raycast through the FCC lattice.
   * @returns {{ hit: boolean, x?: number, y?: number, z?: number, px?: number, py?: number, pz?: number, face?: number, distance?: number }}
   */
  raycast(ox, oy, oz, dx, dy, dz, maxDist = 8) {
    const len = Math.hypot(dx, dy, dz) || 1;
    const vx = dx / len;
    const vy = dy / len;
    const vz = dz / len;
    const step = 0.05;
    let prev = null;
    let prevEmpty = nearestFcc(ox, oy, oz);

    for (let t = 0; t <= maxDist; t += step) {
      const px = ox + vx * t;
      const py = oy + vy * t;
      const pz = oz + vz * t;
      const [cx, cy, cz] = nearestFcc(px, py, pz);
      if (prev && prev[0] === cx && prev[1] === cy && prev[2] === cz) continue;
      prev = [cx, cy, cz];

      if (!this.hasSolid(cx, cy, cz)) {
        prevEmpty = [cx, cy, cz];
        continue;
      }
      if (!pointInRhombic(px, py, pz, cx, cy, cz)) continue;

      // which face did we enter from?
      let face = 0;
      let best = -Infinity;
      for (let f = 0; f < 12; f++) {
        const [nx, ny, nz] = FACE_NEIGHBORS[f];
        // prefer face whose outward normal opposes the ray
        const score = -(nx * vx + ny * vy + nz * vz);
        if (score > best) {
          best = score;
          face = f;
        }
      }
      // place cell: step back one neighbor along that face if empty, else prevEmpty
      const [nx, ny, nz] = FACE_NEIGHBORS[face];
      let [pxCell, pyCell, pzCell] = [cx - nx, cy - ny, cz - nz];
      if (this.hasSolid(pxCell, pyCell, pzCell)) {
        [pxCell, pyCell, pzCell] = prevEmpty;
      }

      return {
        hit: true,
        x: cx,
        y: cy,
        z: cz,
        px: pxCell,
        py: pyCell,
        pz: pzCell,
        face,
        distance: t,
      };
    }
    return { hit: false };
  }

  breakBlock(x, y, z) {
    if (!this.hasSolid(x, y, z)) return AIR;
    const id = this.get(x, y, z);
    this.set(x, y, z, AIR);
    return id;
  }

  placeBlock(x, y, z, id) {
    if (!PLACEABLE.includes(id)) return false;
    if (!isFccCell(x, y, z)) return false;
    if (this.hasSolid(x, y, z)) return false;
    return this.set(x, y, z, id);
  }
}
