import {
  HEX_DIRS,
  axialToWorld,
  edgeNeighbor,
  hexAdd,
  hexDistance,
  hexKey,
  hexLine,
  hexesInRadius,
  vertexId,
} from "./hex.js";

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

function liftCone(terrain, center, reach, lift) {
  for (const cell of cellsInBrush(terrain, center, reach)) {
    const distance = hexDistance(cell, center);
    raiseHex(terrain, cell.q, cell.r, Math.max(1, lift - distance));
  }
}

export function sculptPreview(terrain) {
  flattenTerrain(terrain, DEFAULT_BASE);
  terrain.roads.clear();
  terrain.waterLevel = DEFAULT_WATER;
  liftCone(terrain, { q: -3, r: -2 }, 7, 10);
  liftCone(terrain, { q: 5, r: -4 }, 5, 8);
  liftCone(terrain, { q: 2, r: 4 }, 4, 6);
  if (terrain.radius >= 20) {
    liftCone(
      terrain,
      { q: -Math.round(terrain.radius * 0.48), r: Math.round(terrain.radius * 0.12) },
      10,
      9,
    );
    liftCone(
      terrain,
      { q: Math.round(terrain.radius * 0.42), r: Math.round(terrain.radius * 0.22) },
      11,
      10,
    );
  }
  const lake = { q: 1, r: 2 };
  const lakeReach = 4;
  const lakeCore = 1;
  smoothSlopes(terrain, true);
  for (const cell of cellsInBrush(terrain, lake, lakeReach)) {
    const distance = hexDistance(cell, lake);
    if (distance <= lakeCore) {
      levelHex(terrain, cell.q, cell.r, MIN_HEIGHT);
    } else {
      const current = Math.round(hexMeanHeight(terrain, cell.q, cell.r));
      levelHex(terrain, cell.q, cell.r, Math.max(MIN_HEIGHT, current - 8));
    }
  }
  for (const cell of [...hexLine({ q: -6, r: 2 }, { q: 1, r: -1 }), ...hexLine({ q: 1, r: -1 }, { q: 7, r: -5 })]) {
    setRoad(terrain, cell.q, cell.r, true);
  }
}

export function generateHills(terrain, rng = Math.random) {
  flattenTerrain(terrain, DEFAULT_BASE);
  terrain.roads.clear();
  const peakCount = 6 + Math.floor(rng() * 7) + Math.floor(terrain.radius / 8);
  for (let p = 0; p < peakCount; p += 1) {
    const center = terrain.cells[Math.floor(rng() * terrain.cells.length)];
    liftCone(
      terrain,
      center,
      3 + Math.floor(rng() * Math.max(4, Math.floor(terrain.radius / 4))),
      8 + Math.floor(rng() * 10),
    );
  }
  smoothSlopes(terrain, true);
  const basin = terrain.cells[Math.floor(rng() * terrain.cells.length)];
  const basinReach = 3 + Math.floor(rng() * 3);
  for (const cell of cellsInBrush(terrain, basin, basinReach)) {
    const current = Math.round(hexMeanHeight(terrain, cell.q, cell.r));
    levelHex(terrain, cell.q, cell.r, Math.max(MIN_HEIGHT, current - 10));
  }
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
