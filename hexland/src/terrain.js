import {
  HEX_CORNER_X,
  HEX_CORNER_Z,
  HEX_DIRS,
  axialToWorld,
  edgeNeighbor,
  hexAdd,
  hexDistance,
  hexKey,
  hexesInRadius,
  vertexId,
} from "./hex.js";
import { createPerlin2D, fbm2D } from "./noise.js";

export const MIN_HEIGHT = -10;
export const MAX_HEIGHT = 30;
export const SNOW_HEIGHT = MAX_HEIGHT - 4;
export const DEEP_WATER_HEIGHT = MIN_HEIGHT + 4;
export const DEFAULT_RADIUS = 66;
export const DEFAULT_BASE = 3;
export const DEFAULT_WATER = 2;

export function clampHeight(value) {
  return Math.max(MIN_HEIGHT, Math.min(MAX_HEIGHT, value));
}

export function isSnowHeight(height) {
  return height >= SNOW_HEIGHT;
}

export function isDeepWaterHeight(height) {
  return height <= DEEP_WATER_HEIGHT;
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
  const cellSet = new Set();
  const cellMap = new Map();
  const heights = new Map();
  for (const cell of cells) {
    const key = hexKey(cell.q, cell.r);
    cellSet.add(key);
    cellMap.set(key, cell);
    const world = axialToWorld(cell.q, cell.r, 1);
    cell.ux = world.x;
    cell.uz = world.z;
    cell.corners = [];
    for (let i = 0; i < 6; i += 1) {
      const id = vertexId(cell.q, cell.r, i);
      cell.corners.push(id);
      if (!heights.has(id)) {
        heights.set(id, base);
      }
    }
  }
  for (const cell of cells) {
    cell.skirts = [0, 1, 2, 3, 4, 5].map((i) => {
      const next = edgeNeighbor(cell.q, cell.r, i);
      return !cellSet.has(hexKey(next.q, next.r));
    });
  }
  return {
    radius,
    cells,
    cellSet,
    cellMap,
    heights,
    roads: new Set(),
    waterLevel: clampHeight(waterLevel),
  };
}

export function hasCell(terrain, q, r) {
  return terrain.cellMap.has(hexKey(q, r));
}

export function getCell(terrain, q, r) {
  return terrain.cellMap.get(hexKey(q, r)) ?? null;
}

function heightFromId(terrain, id) {
  const value = terrain.heights.get(id);
  if (value === null || value === undefined) {
    return MIN_HEIGHT;
  }
  return value;
}

export function getVertexHeight(terrain, q, r, vertexIndex) {
  const cell = getCell(terrain, q, r);
  if (!cell) {
    return MIN_HEIGHT;
  }
  return heightFromId(terrain, cell.corners[vertexIndex]);
}

export function hexVertexHeights(terrain, q, r) {
  const cell = getCell(terrain, q, r);
  if (!cell) {
    return [MIN_HEIGHT, MIN_HEIGHT, MIN_HEIGHT, MIN_HEIGHT, MIN_HEIGHT, MIN_HEIGHT];
  }
  return cell.corners.map((id) => heightFromId(terrain, id));
}

export function hexHeightStats(terrain, q, r) {
  const heights = hexVertexHeights(terrain, q, r);
  let min = heights[0];
  let max = heights[0];
  let sum = 0;
  for (const value of heights) {
    min = Math.min(min, value);
    max = Math.max(max, value);
    sum += value;
  }
  return { heights, min, max, mean: sum / heights.length, slope: max - min };
}

export function hexMeanHeight(terrain, q, r) {
  return hexHeightStats(terrain, q, r).mean;
}

export function hexMinHeight(terrain, q, r) {
  return hexHeightStats(terrain, q, r).min;
}

export function hexMaxHeight(terrain, q, r) {
  return hexHeightStats(terrain, q, r).max;
}

export function hexSlope(terrain, q, r) {
  return hexHeightStats(terrain, q, r).slope;
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
  const cell = getCell(terrain, q, r);
  if (!cell) {
    return false;
  }
  let changed = false;
  for (const id of cell.corners) {
    const current = terrain.heights.get(id) ?? MIN_HEIGHT;
    if (setVertex(terrain, id, current + delta)) {
      changed = true;
    }
  }
  return changed;
}

export function raiseVertex(terrain, q, r, vertexIndex, delta = 1) {
  const cell = getCell(terrain, q, r);
  if (!cell) {
    return false;
  }
  const id = cell.corners[vertexIndex];
  const current = terrain.heights.get(id) ?? MIN_HEIGHT;
  return setVertex(terrain, id, current + delta);
}

export function levelHex(terrain, q, r, height) {
  const cell = getCell(terrain, q, r);
  if (!cell) {
    return false;
  }
  const target = clampHeight(height);
  let changed = false;
  for (const id of cell.corners) {
    if (setVertex(terrain, id, target)) {
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

export function hasRoad(terrain, q, r) {
  return terrain.roads.has(hexKey(q, r));
}

export function setRoad(terrain, q, r, on) {
  if (!hasCell(terrain, q, r)) {
    return false;
  }
  const key = hexKey(q, r);
  if (on) {
    if (terrain.roads.has(key)) {
      return false;
    }
    terrain.roads.add(key);
    return true;
  }
  if (!terrain.roads.has(key)) {
    return false;
  }
  terrain.roads.delete(key);
  return true;
}

export function roadNeighbors(terrain, q, r) {
  const links = [];
  for (const dir of HEX_DIRS) {
    const next = hexAdd({ q, r }, dir);
    if (hasRoad(terrain, next.q, next.r)) {
      links.push(next);
    }
  }
  return links;
}

export function isSkirtEdge(terrain, q, r, edgeIndex) {
  const cell = getCell(terrain, q, r);
  if (!cell) {
    return false;
  }
  return cell.skirts[edgeIndex];
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

export function setRoadBrush(terrain, q, r, radius, on) {
  let changed = false;
  for (const cell of cellsInBrush(terrain, { q, r }, radius)) {
    if (setRoad(terrain, cell.q, cell.r, on)) {
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
        const a = cell.corners[i];
        const b = cell.corners[(i + 1) % 6];
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

export function cloneState(terrain) {
  return {
    heights: new Map(terrain.heights),
    roads: new Set(terrain.roads),
    waterLevel: terrain.waterLevel,
  };
}

export function applyState(terrain, snapshot) {
  terrain.heights = new Map(snapshot.heights);
  terrain.roads = new Set(snapshot.roads);
  terrain.waterLevel = snapshot.waterLevel;
}

export function statesEqual(a, b) {
  if (a.waterLevel !== b.waterLevel || a.heights.size !== b.heights.size || a.roads.size !== b.roads.size) {
    return false;
  }
  for (const [id, value] of a.heights) {
    if (b.heights.get(id) !== value) {
      return false;
    }
  }
  for (const key of a.roads) {
    if (!b.roads.has(key)) {
      return false;
    }
  }
  return true;
}

export function createHistory(limit = 48) {
  return { past: [], future: [], limit };
}

export function pushUndo(history, terrain) {
  history.past.push(cloneState(terrain));
  if (history.past.length > history.limit) {
    history.past.shift();
  }
  history.future.length = 0;
}

export function undo(history, terrain) {
  if (history.past.length === 0) {
    return false;
  }
  history.future.push(cloneState(terrain));
  applyState(terrain, history.past.pop());
  return true;
}

export function redo(history, terrain) {
  if (history.future.length === 0) {
    return false;
  }
  history.past.push(cloneState(terrain));
  applyState(terrain, history.future.pop());
  return true;
}

/**
 * Largest |height| gap between adjacent corners of one hex.
 * Generated maps keep this at most 1 so interior faces stay planar enough
 * to draw without a cliff wall.
 */
export function maxHeightStep(terrain) {
  let max = 0;
  for (const cell of terrain.cells) {
    for (let i = 0; i < 6; i += 1) {
      const ha = terrain.heights.get(cell.corners[i]);
      const hb = terrain.heights.get(cell.corners[(i + 1) % 6]);
      max = Math.max(max, Math.abs(ha - hb));
    }
  }
  return max;
}

/**
 * Pull neighboring vertices together until every hex edge differs by at most
 * one step. Unlike `smoothSlopes`, this does not prefer raising or lowering.
 */
export function relaxSlopes(terrain) {
  let any = false;
  for (let guard = 0; guard < 500; guard += 1) {
    let changed = false;
    for (const cell of terrain.cells) {
      for (let i = 0; i < 6; i += 1) {
        const a = cell.corners[i];
        const b = cell.corners[(i + 1) % 6];
        const ha = terrain.heights.get(a);
        const hb = terrain.heights.get(b);
        const gap = ha - hb;
        if (gap > 1) {
          changed = setVertex(terrain, a, ha - 1) || changed;
          changed = setVertex(terrain, b, hb + 1) || changed;
        } else if (gap < -1) {
          changed = setVertex(terrain, a, ha + 1) || changed;
          changed = setVertex(terrain, b, hb - 1) || changed;
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

function heightSpanForRadius(radius) {
  return Math.min(MAX_HEIGHT - MIN_HEIGHT, Math.max(0, 2 * radius));
}

function vertexWorld(cell, cornerIndex) {
  return {
    x: cell.ux + HEX_CORNER_X[cornerIndex],
    z: cell.uz + HEX_CORNER_Z[cornerIndex],
  };
}

/**
 * Sample Perlin noise at each unique vertex, stretch to the height range the
 * hex radius can support, then relax edges so no step is steeper than 1.
 */
export function generateNoiseTerrain(terrain, rng) {
  terrain.roads.clear();
  terrain.waterLevel = DEFAULT_WATER;
  const noise = createPerlin2D(rng);
  const originX = rng() * 256;
  const originZ = rng() * 256;
  const freq = 1 / Math.max(10, terrain.radius * 1.15);
  const samples = [];
  let minN = Infinity;
  let maxN = -Infinity;
  const seen = new Set();
  for (const cell of terrain.cells) {
    for (let i = 0; i < 6; i += 1) {
      const id = cell.corners[i];
      if (seen.has(id)) {
        continue;
      }
      seen.add(id);
      const world = vertexWorld(cell, i);
      const x = world.x * freq + originX;
      const z = world.z * freq + originZ;
      const n = fbm2D(noise, x, z, 4, 2, 0.35);
      samples.push([id, n]);
      if (n < minN) {
        minN = n;
      }
      if (n > maxN) {
        maxN = n;
      }
    }
  }
  const span = heightSpanForRadius(terrain.radius);
  const lo = Math.round((MIN_HEIGHT + MAX_HEIGHT - span) / 2);
  const hi = lo + span;
  const range = maxN - minN;
  for (const [id, n] of samples) {
    const t = range === 0 ? 0.5 : (n - minN) / range;
    terrain.heights.set(id, clampHeight(Math.round(lo + t * (hi - lo))));
  }
  relaxSlopes(terrain);
}

export function sculptPreview(terrain, rng = mulberry32(Date.now())) {
  generateNoiseTerrain(terrain, rng);
}

export function generateHills(terrain, rng = Math.random) {
  generateNoiseTerrain(terrain, rng);
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
  const roadParts = [...terrain.roads].sort();
  return `${parts.join(";")}#${roadParts.join(",")}#${terrain.waterLevel}`;
}
