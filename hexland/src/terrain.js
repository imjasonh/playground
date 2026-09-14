import {
  hexDistance,
  hexKey,
  hexesInRadius,
  vertexId,
} from "./hex.js";

export const MIN_HEIGHT = 0;
export const MAX_HEIGHT = 12;
export const DEFAULT_RADIUS = 10;
export const DEFAULT_BASE = 3;
export const DEFAULT_WATER = 2;

export function clampHeight(value) {
  return Math.max(MIN_HEIGHT, Math.min(MAX_HEIGHT, value));
}

export function mulberry32(seed) {
  let state = seed >>> 0;
  return () => {
    state = (state + 0x6d2b79f5) >>> 0;
    let value = state;
    value = Math.imul(value ^ (value >>> 15), value | 1);
    value ^= value + Math.imul(value ^ (value >>> 7), value | 61);
    return ((value ^ (value >>> 14)) >>> 0) / 4294967296;
  };
}

export function createTerrain({
  radius = DEFAULT_RADIUS,
  base = DEFAULT_BASE,
  waterLevel = DEFAULT_WATER,
} = {}) {
  const cells = hexesInRadius(radius);
  const cellSet = new Set(cells.map((cell) => hexKey(cell.q, cell.r)));
  const heights = new Map();
  for (const cell of cells) {
    for (let i = 0; i < 6; i += 1) {
      const id = vertexId(cell.q, cell.r, i);
      if (!heights.has(id)) {
        heights.set(id, base);
      }
    }
  }
  return {
    radius,
    cells,
    cellSet,
    heights,
    waterLevel: clampHeight(waterLevel),
  };
}

export function hasCell(terrain, q, r) {
  return terrain.cellSet.has(hexKey(q, r));
}

export function getVertexHeight(terrain, q, r, vertexIndex) {
  const value = terrain.heights.get(vertexId(q, r, vertexIndex));
  if (value === null || value === undefined) {
    return MIN_HEIGHT;
  }
  return value;
}

export function hexVertexHeights(terrain, q, r) {
  return [0, 1, 2, 3, 4, 5].map((i) => getVertexHeight(terrain, q, r, i));
}

export function hexMeanHeight(terrain, q, r) {
  const heights = hexVertexHeights(terrain, q, r);
  return heights.reduce((sum, value) => sum + value, 0) / heights.length;
}

export function hexMinHeight(terrain, q, r) {
  return Math.min(...hexVertexHeights(terrain, q, r));
}

export function hexMaxHeight(terrain, q, r) {
  return Math.max(...hexVertexHeights(terrain, q, r));
}

export function hexSlope(terrain, q, r) {
  return hexMaxHeight(terrain, q, r) - hexMinHeight(terrain, q, r);
}

export function hexIsUnderwater(terrain, q, r) {
  return hexMinHeight(terrain, q, r) < terrain.waterLevel;
}

export function hexIsShore(terrain, q, r) {
  const min = hexMinHeight(terrain, q, r);
  const max = hexMaxHeight(terrain, q, r);
  return min < terrain.waterLevel && max >= terrain.waterLevel;
}

export function setWaterLevel(terrain, level) {
  terrain.waterLevel = clampHeight(level);
}

function setVertex(terrain, id, value) {
  const next = clampHeight(value);
  if (terrain.heights.get(id) === next) {
    return false;
  }
  terrain.heights.set(id, next);
  return true;
}

export function raiseHex(terrain, q, r, delta = 1) {
  if (!hasCell(terrain, q, r)) {
    return false;
  }
  let changed = false;
  for (let i = 0; i < 6; i += 1) {
    const id = vertexId(q, r, i);
    const current = terrain.heights.get(id) ?? MIN_HEIGHT;
    if (setVertex(terrain, id, current + delta)) {
      changed = true;
    }
  }
  return changed;
}

export function raiseVertex(terrain, q, r, vertexIndex, delta = 1) {
  if (!hasCell(terrain, q, r)) {
    return false;
  }
  const id = vertexId(q, r, vertexIndex);
  const current = terrain.heights.get(id) ?? MIN_HEIGHT;
  return setVertex(terrain, id, current + delta);
}

export function levelHex(terrain, q, r, height) {
  if (!hasCell(terrain, q, r)) {
    return false;
  }
  const target = clampHeight(height);
  let changed = false;
  for (let i = 0; i < 6; i += 1) {
    if (setVertex(terrain, vertexId(q, r, i), target)) {
      changed = true;
    }
  }
  return changed;
}

export function flattenTerrain(terrain, height = DEFAULT_BASE) {
  const target = clampHeight(height);
  for (const id of terrain.heights.keys()) {
    terrain.heights.set(id, target);
  }
}

export function cellsInBrush(terrain, origin, radius) {
  if (radius <= 0) {
    if (hasCell(terrain, origin.q, origin.r)) {
      return [{ q: origin.q, r: origin.r }];
    }
    return [];
  }
  return terrain.cells.filter((cell) => hexDistance(cell, origin) <= radius);
}

export function raiseBrush(terrain, q, r, radius, delta) {
  let changed = false;
  for (const cell of cellsInBrush(terrain, { q, r }, radius)) {
    if (raiseHex(terrain, cell.q, cell.r, delta)) {
      changed = true;
    }
  }
  return changed;
}

/**
 * Pull adjacent vertices so no hex edge differs by more than one step.
 * After a raise, lows move up. After a lower, highs move down.
 * That is the RCT "land follows" cascade.
 */
export function smoothSlopes(terrain, preferRaise) {
  let any = false;
  for (let guard = 0; guard < 500; guard += 1) {
    let changed = false;
    for (const cell of terrain.cells) {
      for (let i = 0; i < 6; i += 1) {
        const a = vertexId(cell.q, cell.r, i);
        const b = vertexId(cell.q, cell.r, (i + 1) % 6);
        const ha = terrain.heights.get(a);
        const hb = terrain.heights.get(b);
        if (Math.abs(ha - hb) <= 1) {
          continue;
        }
        if (preferRaise) {
          if (ha < hb) {
            changed = setVertex(terrain, a, hb - 1) || changed;
          } else {
            changed = setVertex(terrain, b, ha - 1) || changed;
          }
        } else if (ha > hb) {
          changed = setVertex(terrain, a, hb + 1) || changed;
        } else {
          changed = setVertex(terrain, b, ha + 1) || changed;
        }
      }
    }
    if (!changed) {
      break;
    }
    any = true;
  }
  return any;
}

export function cloneHeights(terrain) {
  return new Map(terrain.heights);
}

export function applyHeights(terrain, snapshot) {
  terrain.heights = new Map(snapshot);
}

export function createHistory(limit = 48) {
  return { past: [], future: [], limit };
}

export function pushUndo(history, terrain) {
  history.past.push(cloneHeights(terrain));
  if (history.past.length > history.limit) {
    history.past.shift();
  }
  history.future.length = 0;
}

export function undo(history, terrain) {
  if (history.past.length === 0) {
    return false;
  }
  history.future.push(cloneHeights(terrain));
  applyHeights(terrain, history.past.pop());
  return true;
}

export function redo(history, terrain) {
  if (history.future.length === 0) {
    return false;
  }
  history.past.push(cloneHeights(terrain));
  applyHeights(terrain, history.future.pop());
  return true;
}

export function sculptPreview(terrain) {
  flattenTerrain(terrain, DEFAULT_BASE);
  terrain.waterLevel = DEFAULT_WATER;
  for (const cell of terrain.cells) {
    const lake = hexDistance(cell, { q: 1, r: 3 });
    if (lake <= 3) {
      raiseHex(terrain, cell.q, cell.r, lake <= 1 ? -2 : -1);
    }
    const ridge = hexDistance(cell, { q: -4, r: -2 });
    if (ridge <= 4) {
      raiseHex(terrain, cell.q, cell.r, 4 - ridge);
    }
    const mesa = hexDistance(cell, { q: 5, r: -4 });
    if (mesa <= 2) {
      raiseHex(terrain, cell.q, cell.r, 3);
    }
  }
  smoothSlopes(terrain, true);
}

export function generateHills(terrain, rng = Math.random) {
  flattenTerrain(terrain, DEFAULT_BASE);
  const peakCount = 3 + Math.floor(rng() * 4);
  for (let p = 0; p < peakCount; p += 1) {
    const center = terrain.cells[Math.floor(rng() * terrain.cells.length)];
    const reach = 2 + Math.floor(rng() * 4);
    const lift = 2 + Math.floor(rng() * 4);
    for (const cell of terrain.cells) {
      const distance = hexDistance(cell, center);
      if (distance > reach) {
        continue;
      }
      raiseHex(terrain, cell.q, cell.r, Math.max(1, lift - distance));
    }
  }
  const basin = terrain.cells[Math.floor(rng() * terrain.cells.length)];
  const basinReach = 2 + Math.floor(rng() * 2);
  for (const cell of terrain.cells) {
    if (hexDistance(cell, basin) <= basinReach) {
      raiseHex(terrain, cell.q, cell.r, -2);
    }
  }
  smoothSlopes(terrain, true);
}

export function heightsEqual(a, b) {
  if (a.size !== b.size) {
    return false;
  }
  for (const [id, value] of a) {
    if (b.get(id) !== value) {
      return false;
    }
  }
  return true;
}

export function terrainFingerprint(terrain) {
  const parts = [];
  for (const [id, value] of [...terrain.heights.entries()].sort((left, right) => {
    if (left[0] < right[0]) {
      return -1;
    }
    if (left[0] > right[0]) {
      return 1;
    }
    return 0;
  })) {
    parts.push(`${id}:${value}`);
  }
  return parts.join(";");
}

