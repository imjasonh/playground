/**
 * Directional corridor population.
 *
 * From an origin, extend a corridor of width W along bearing D. Count people
 * in population cells the corridor covers. Ask: how long must the corridor be
 * before it has hit N people?
 *
 * At packaged resolutions (~0.5–2 km), a 100 ft corridor is thinner than a
 * cell. Centerline samples get full credit for the cell they’re in. When a
 * sample lies on a grid line (common for exact N/S/E/W walks), credit is the
 * average of the two adjacent cells instead of picking one side. A catch band
 * still pulls in nearby cells so thin rose rays don’t miss metro cores like LA.
 */

import { destination, metersPerDegree } from "./geo.js";

/**
 * @typedef {object} RayResult
 * @property {number} bearingDeg
 * @property {number} people
 * @property {number} lengthM
 * @property {number} widthM
 * @property {boolean} reached
 */

/** Catch radius so a thin corridor still grazes nearby cells. */
function catchRadiusM(grid, origin, widthM) {
  const halfW = Math.max(0, widthM) / 2;
  // Use the larger cell side so both row- and col-neighbors stay in range
  // (cellSizeM is the min side and can exclude the other axis).
  const { lat: mLat, lon: mLon } = metersPerDegree(origin.lat);
  const cellM = Math.max(
    Math.abs(mLat * grid.meta.cellDeg),
    Math.abs(mLon * grid.meta.cellDeg),
  );
  // Slightly more than one cell so 5° rose rays still clip metro cores (LA).
  return Math.max(halfW, cellM * 1.25);
}

/**
 * 1D sample along a grid axis. Interior of a cell → that cell at weight 1.
 * On (or within a few % of) a grid line → 50/50 average of the two adjacent
 * cells. A narrow band covers geodesic drift off exact N/S/E/W without
 * turning every sample into a bilinear under-count.
 *
 * @returns {{index:number, weight:number}[]}
 */
export function edgeBlend1D(f) {
  const i0 = Math.floor(f);
  const t = f - i0; // 0..1 inside cell i0
  // ~5% of a cell ≈ geodesic drift over a few miles on cardinal walks.
  const EDGE = 0.05;

  if (t <= EDGE) {
    // Lower edge shared with i0-1: 50/50 on the line → full i0 by EDGE.
    const u = t / EDGE;
    const wOther = 0.5 * (1 - u);
    return [
      { index: i0 - 1, weight: wOther },
      { index: i0, weight: 1 - wOther },
    ];
  }
  if (t >= 1 - EDGE) {
    const u = (1 - t) / EDGE;
    const wOther = 0.5 * (1 - u);
    return [
      { index: i0, weight: 1 - wOther },
      { index: i0 + 1, weight: wOther },
    ];
  }
  return [{ index: i0, weight: 1 }];
}

/**
 * Cells under a sample point. Near a grid line, split weight across both
 * adjacent cells (their average on the line). Near a corner, the two 1D
 * blends multiply (bilinear).
 *
 * @returns {{row:number, col:number, weight:number}[]}
 */
export function centerlineCellWeights(colF, rowF, width, height) {
  const cols = edgeBlend1D(colF);
  const rows = edgeBlend1D(rowF);
  /** @type {{row:number, col:number, weight:number}[]} */
  const out = [];
  for (const r of rows) {
    for (const c of cols) {
      const weight = r.weight * c.weight;
      if (!(weight > 0)) continue;
      if (r.index < 0 || r.index >= height || c.index < 0 || c.index >= width) {
        continue;
      }
      out.push({ row: r.index, col: c.index, weight });
    }
  }
  return out;
}

/**
 * Walk the geodesic centerline; collect cells near the strip.
 *
 * @param {import('./grid.js').PopulationGrid} grid
 * @param {{lat:number, lon:number}} origin
 * @param {number} bearingDeg
 * @param {number} lengthM
 * @param {number} widthM
 * @returns {{idx:number, pop:number, along:number}[]}
 */
function cellsInCorridor(grid, origin, bearingDeg, lengthM, widthM) {
  if (lengthM <= 0) return [];

  const cellDeg = grid.meta.cellDeg;
  const catchM = catchRadiusM(grid, origin, widthM);
  const cellM = grid.cellSizeM(origin.lat);
  const step = Math.max(Math.min(cellM * 0.2, 150), 25);
  const rad = (bearingDeg * Math.PI) / 180;
  const dirX = Math.sin(rad);
  const dirY = Math.cos(rad);

  /** @type {Map<number, {idx:number, pop:number, along:number}>} */
  const seen = new Map();

  function add(idx, along, weight) {
    if (!(weight > 0)) return;
    const raw = grid.data[idx];
    if (!(raw > 0)) return;
    const credit = raw * weight;
    const prev = seen.get(idx);
    const a = Math.max(0, along);
    if (
      prev == null ||
      a < prev.along - 1e-6 ||
      (Math.abs(a - prev.along) <= 1e-6 && credit > prev.pop)
    ) {
      seen.set(idx, { idx, pop: credit, along: a });
    }
  }

  const nSteps = Math.max(1, Math.ceil(lengthM / step));
  const neighbor = Math.max(1, Math.ceil(catchM / Math.max(cellM, 1)) + 1);
  // Rectangular tiles: once a ray leaves after having been inside, it won't
  // re-enter. Stop instead of stepping empty ocean/Canada for thousands of miles
  // (that freeze was the main "nothing on mobile" failure mode).
  let outsideStreak = 0;
  let everInside = false;

  for (let i = 0; i <= nSteps; i++) {
    const along = Math.min(lengthM, i * step);
    const p = destination(origin.lat, origin.lon, bearingDeg, along);
    if (!grid.contains(p.lat, p.lon)) {
      outsideStreak++;
      if (everInside && outsideStreak >= 3) break;
      if (!everInside && outsideStreak >= 8) break;
      continue;
    }
    outsideStreak = 0;
    everInside = true;

    const colF = (p.lon - grid.meta.west) / cellDeg;
    const rowF = (grid.meta.north - p.lat) / cellDeg;
    if (
      colF < 0 ||
      colF >= grid.meta.width ||
      rowF < 0 ||
      rowF >= grid.meta.height
    ) {
      continue;
    }

    const primary = centerlineCellWeights(
      colF,
      rowF,
      grid.meta.width,
      grid.meta.height,
    );
    /** @type {Set<number>} */
    const primaryIdx = new Set();
    for (const cell of primary) {
      const idx = cell.row * grid.meta.width + cell.col;
      primaryIdx.add(idx);
      add(idx, along, cell.weight);
    }

    // Catch band for cells beside the strip. Skip primary cells so a boundary
    // average (0.5+0.5) is not overwritten by a full-credit catch hit.
    const anchorRow = Math.min(
      grid.meta.height - 1,
      Math.max(0, Math.floor(rowF)),
    );
    const anchorCol = Math.min(
      grid.meta.width - 1,
      Math.max(0, Math.floor(colF)),
    );
    const { lat: mLat, lon: mLon } = metersPerDegree(p.lat);
    for (let dr = -neighbor; dr <= neighbor; dr++) {
      for (let dc = -neighbor; dc <= neighbor; dc++) {
        const r = anchorRow + dr;
        const c = anchorCol + dc;
        if (r < 0 || r >= grid.meta.height || c < 0 || c >= grid.meta.width) {
          continue;
        }
        const idx = r * grid.meta.width + c;
        if (primaryIdx.has(idx)) continue;
        const clat = grid.meta.north - (r + 0.5) * cellDeg;
        const clon = grid.meta.west + (c + 0.5) * cellDeg;
        const dx = (clon - p.lon) * mLon;
        const dy = (clat - p.lat) * mLat;
        const cross = Math.abs(dx * dirY - dy * dirX);
        if (cross > catchM) continue;
        const alongOffset = dx * dirX + dy * dirY;
        const cellAlong = along + alongOffset;
        if (cellAlong < -catchM || cellAlong > lengthM) continue;
        add(idx, cellAlong, 1);
      }
    }
  }

  return [...seen.values()];
}

function asGridList(gridOrGrids) {
  const list = Array.isArray(gridOrGrids) ? gridOrGrids : [gridOrGrids];
  return list.filter(Boolean);
}

/** Grids containing origin, finest cell size first. */
function orderedGrids(gridOrGrids, origin) {
  return asGridList(gridOrGrids)
    .filter((g) => g.contains(origin.lat, origin.lon))
    .sort((a, b) => a.meta.cellDeg - b.meta.cellDeg);
}

function cellCenter(grid, idx) {
  const col = idx % grid.meta.width;
  const row = (idx / grid.meta.width) | 0;
  return {
    lat: grid.meta.north - (row + 0.5) * grid.meta.cellDeg,
    lon: grid.meta.west + (col + 0.5) * grid.meta.cellDeg,
  };
}

/**
 * Corridor hits across one or more grids. Finer tiles win where they overlap
 * so long rays can leave a metro tile and keep counting on CONUS.
 */
function corridorHitsOnGrids(gridOrGrids, origin, bearingDeg, lengthM, widthM) {
  const grids = orderedGrids(gridOrGrids, origin);
  /** @type {{along:number, pop:number}[]} */
  const merged = [];
  for (let gi = 0; gi < grids.length; gi++) {
    const grid = grids[gi];
    const finer = grids.slice(0, gi);
    const hits = cellsInCorridor(grid, origin, bearingDeg, lengthM, widthM || 0);
    for (const h of hits) {
      if (finer.length) {
        const { lat, lon } = cellCenter(grid, h.idx);
        if (finer.some((f) => f.contains(lat, lon))) continue;
      }
      merged.push({ along: h.along, pop: h.pop });
    }
  }
  merged.sort((a, b) => a.along - b.along);
  return merged;
}

/** People inside a corridor of length lengthM and width widthM. */
export function peopleInCorridor(
  gridOrGrids,
  origin,
  bearingDeg,
  lengthM,
  widthM,
) {
  const hits = corridorHitsOnGrids(
    gridOrGrids,
    origin,
    bearingDeg,
    lengthM,
    widthM || 0,
  );
  let people = 0;
  for (const h of hits) people += h.pop;
  return people;
}

/** @deprecated alias */
export function peopleAlongLine(grid, origin, bearingDeg, lengthM, opts = {}) {
  const widthM = opts.widthM ?? 0;
  return peopleInCorridor(grid, origin, bearingDeg, lengthM, widthM);
}

/** Growing length caps so nearby targets don't force a full maxLength walk. */
function searchCaps(maxLengthM) {
  /** @type {number[]} */
  const caps = [];
  let cap = Math.min(maxLengthM, 40_000); // ~25 mi
  while (cap < maxLengthM - 1) {
    caps.push(cap);
    cap = Math.min(maxLengthM, cap * 2.5);
  }
  caps.push(maxLengthM);
  return caps;
}

/**
 * One bearing: shortest corridor to N people, plus people counted if unreached.
 * Uses expanding length caps (cheap when N is nearby) and never re-walks for
 * the unreached population total.
 */
export function probeRay(
  gridOrGrids,
  origin,
  bearingDeg,
  targetPeople,
  widthM,
  maxLengthM,
) {
  if (targetPeople <= 0) {
    return {
      bearingDeg,
      people: 0,
      lengthM: 0,
      widthM,
      reached: true,
    };
  }
  if (maxLengthM <= 0) {
    return {
      bearingDeg,
      people: 0,
      lengthM: 0,
      widthM,
      reached: false,
    };
  }

  let people = 0;
  for (const cap of searchCaps(maxLengthM)) {
    const hits = corridorHitsOnGrids(
      gridOrGrids,
      origin,
      bearingDeg,
      cap,
      widthM || 0,
    );
    people = 0;
    for (const h of hits) {
      people += h.pop;
      if (people >= targetPeople) {
        return {
          bearingDeg,
          people: targetPeople,
          lengthM: h.along,
          widthM,
          reached: true,
        };
      }
    }
  }
  return {
    bearingDeg,
    people,
    lengthM: maxLengthM,
    widthM,
    reached: false,
  };
}

/**
 * Shortest corridor length to accumulate targetPeople (meters), or Infinity.
 * Accepts one grid or several (finest-first cascade).
 */
export function distanceToPeople(
  gridOrGrids,
  origin,
  bearingDeg,
  targetPeople,
  widthM,
  maxLengthM,
) {
  const ray = probeRay(
    gridOrGrids,
    origin,
    bearingDeg,
    targetPeople,
    widthM,
    maxLengthM,
  );
  return ray.reached ? ray.lengthM : Infinity;
}

/**
 * Directional rose: distance to N people in each direction.
 * @param {import('./grid.js').PopulationGrid | import('./grid.js').PopulationGrid[]} gridOrGrids
 * @param {{lat:number, lon:number}} origin
 * @param {object} options
 * @param {number} options.widthM
 * @param {number} options.targetPeople
 * @param {number} options.maxLengthM
 * @param {number} [options.rayCount=72]
 */
export function computeRose(gridOrGrids, origin, options) {
  const {
    widthM,
    targetPeople,
    maxLengthM,
    rayCount = 72,
  } = options;
  const grids = orderedGrids(gridOrGrids, origin);
  if (!grids.length) {
    throw new Error("origin is outside the population grid");
  }
  const rays = [];
  for (let i = 0; i < rayCount; i++) {
    const bearingDeg = (360 * i) / rayCount;
    rays.push(
      probeRay(grids, origin, bearingDeg, targetPeople, widthM, maxLengthM),
    );
  }
  return rays;
}

/**
 * Same as computeRose, but yields to the event loop so mobile Safari can paint
 * the map (and status) instead of freezing on a multi-second sync walk.
 * @param {(done:number, total:number) => void} [onProgress]
 */
export async function computeRoseAsync(
  gridOrGrids,
  origin,
  options,
  onProgress,
) {
  const {
    widthM,
    targetPeople,
    maxLengthM,
    rayCount = 72,
  } = options;
  const grids = orderedGrids(gridOrGrids, origin);
  if (!grids.length) {
    throw new Error("origin is outside the population grid");
  }
  const rays = [];
  for (let i = 0; i < rayCount; i++) {
    const bearingDeg = (360 * i) / rayCount;
    rays.push(
      probeRay(grids, origin, bearingDeg, targetPeople, widthM, maxLengthM),
    );
    if (i % 6 === 5 || i === rayCount - 1) {
      onProgress?.(i + 1, rayCount);
      await new Promise((r) => setTimeout(r, 0));
    }
  }
  return rays;
}

/** Build a closed ring of [lat, lon] tips for drawing a rose polygon. */
export function rosePolygon(origin, rays, lengthForRay) {
  const ring = [];
  for (const ray of rays) {
    const len = lengthForRay(ray);
    if (!(len > 0) || !Number.isFinite(len)) {
      ring.push([origin.lat, origin.lon]);
      continue;
    }
    const tip = destination(origin.lat, origin.lon, ray.bearingDeg, len);
    ring.push([tip.lat, tip.lon]);
  }
  if (ring.length) ring.push(ring[0]);
  return ring;
}
