/**
 * Directional corridor population.
 *
 * From an origin, extend a corridor of width W along bearing D. Count people
 * in population cells the corridor covers. Ask: how long must the corridor be
 * before it has hit N people?
 *
 * At packaged resolutions (~0.5–2 km), a 100 ft corridor is thinner than a
 * cell. We treat that as ~one cell wide: cells the centerline crosses, plus
 * cells whose centers lie within one cell of the line. Wider W expands the
 * catch radius further.
 *
 * Axis-aligned grid walks can notch N/S/E/W; computeRose applies a light
 * angular median so the drawn rose stays closer to the oval you’d expect.
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

/** Catch radius so a thin corridor still hits cells it grazes. */
function catchRadiusM(grid, origin, widthM) {
  const halfW = Math.max(0, widthM) / 2;
  // One cell: otherwise a 5° rose ray can thread past LA and miss 500k.
  const cellM = grid.cellSizeM(origin.lat);
  return Math.max(halfW, cellM);
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
  // Fine enough to not skip a cell on diagonal geodesics.
  const step = Math.max(Math.min(cellM * 0.2, 150), 25);
  const rad = (bearingDeg * Math.PI) / 180;
  const dirX = Math.sin(rad);
  const dirY = Math.cos(rad);

  /** @type {Map<number, {idx:number, pop:number, along:number}>} */
  const seen = new Map();

  function add(idx, along) {
    const pop = grid.data[idx];
    if (!(pop > 0)) return;
    const prev = seen.get(idx);
    const a = Math.max(0, along);
    if (prev == null || a < prev.along) seen.set(idx, { idx, pop, along: a });
  }

  const nSteps = Math.max(1, Math.ceil(lengthM / step));
  for (let i = 0; i <= nSteps; i++) {
    const along = Math.min(lengthM, i * step);
    const p = destination(origin.lat, origin.lon, bearingDeg, along);
    if (!grid.contains(p.lat, p.lon)) continue;

    const col = Math.floor((p.lon - grid.meta.west) / cellDeg);
    const row = Math.floor((grid.meta.north - p.lat) / cellDeg);
    if (col < 0 || col >= grid.meta.width || row < 0 || row >= grid.meta.height) {
      continue;
    }

    // Always count the cell the centerline is in (don’t require the sample
    // to sit near the cell center — corner samples would fail that test).
    add(row * grid.meta.width + col, along);

    const { lat: mLat, lon: mLon } = metersPerDegree(p.lat);
    const neighbor = Math.max(1, Math.ceil(catchM / Math.max(cellM, 1)) + 1);
    for (let dr = -neighbor; dr <= neighbor; dr++) {
      for (let dc = -neighbor; dc <= neighbor; dc++) {
        if (dr === 0 && dc === 0) continue;
        const r = row + dr;
        const c = col + dc;
        if (r < 0 || r >= grid.meta.height || c < 0 || c >= grid.meta.width) {
          continue;
        }
        const idx = r * grid.meta.width + c;
        const clat = grid.meta.north - (r + 0.5) * cellDeg;
        const clon = grid.meta.west + (c + 0.5) * cellDeg;
        const dx = (clon - p.lon) * mLon;
        const dy = (clat - p.lat) * mLat;
        const cross = Math.abs(dx * dirY - dy * dirX);
        if (cross > catchM) continue;
        const alongOffset = dx * dirX + dy * dirY;
        const cellAlong = along + alongOffset;
        if (cellAlong < -catchM || cellAlong > lengthM) continue;
        add(idx, cellAlong);
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
  if (targetPeople <= 0) return 0;
  if (maxLengthM <= 0) return Infinity;

  const hits = corridorHitsOnGrids(
    gridOrGrids,
    origin,
    bearingDeg,
    maxLengthM,
    widthM || 0,
  );

  let people = 0;
  for (const h of hits) {
    people += h.pop;
    if (people >= targetPeople) return h.along;
  }
  return Infinity;
}

/**
 * Angular median on reached lengths. Lat/lon grids over-count on exact
 * N/S/E/W walks; this lifts single-bearing inward notches for the rose.
 * @param {RayResult[]} rays
 * @param {number} [halfWindow=2]  neighbors on each side (2 ⇒ 5-tap)
 */
export function smoothRoseLengths(rays, halfWindow = 2) {
  const n = rays.length;
  if (n < 3) return rays;
  const raw = rays.map((r) => (r.reached ? r.lengthM : null));
  return rays.map((ray, i) => {
    if (!ray.reached) return ray;
    const samples = [];
    for (let d = -halfWindow; d <= halfWindow; d++) {
      const v = raw[(i + d + n) % n];
      if (v != null) samples.push(v);
    }
    if (samples.length < 2) return ray;
    samples.sort((a, b) => a - b);
    const mid = samples[Math.floor(samples.length / 2)];
    return { ...ray, lengthM: mid };
  });
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
 * @param {boolean} [options.smooth=true]
 */
export function computeRose(gridOrGrids, origin, options) {
  const {
    widthM,
    targetPeople,
    maxLengthM,
    rayCount = 72,
    smooth = true,
  } = options;
  const grids = orderedGrids(gridOrGrids, origin);
  if (!grids.length) {
    throw new Error("origin is outside the population grid");
  }
  const rays = [];
  for (let i = 0; i < rayCount; i++) {
    const bearingDeg = (360 * i) / rayCount;
    const dist = distanceToPeople(
      grids,
      origin,
      bearingDeg,
      targetPeople,
      widthM,
      maxLengthM,
    );
    const reached = Number.isFinite(dist);
    rays.push({
      bearingDeg,
      people: reached
        ? targetPeople
        : peopleInCorridor(grids, origin, bearingDeg, maxLengthM, widthM),
      lengthM: reached ? dist : maxLengthM,
      widthM,
      reached,
    });
  }
  return smooth ? smoothRoseLengths(rays) : rays;
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
