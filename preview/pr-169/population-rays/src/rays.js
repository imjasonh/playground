/**
 * Directional corridor population.
 *
 * From an origin, extend a corridor of width W along bearing D. Count people
 * in population cells the corridor covers. Ask: how long must the corridor be
 * before it has hit N people?
 *
 * Model:
 *  1. Cells the centerline crosses (so a thin corridor still works), plus
 *  2. Cells whose centers lie within W/2 of the centerline (wider → more).
 *
 * Below roughly one grid cell of width, (2) adds little — the map resolution
 * is the limit. Widen into miles and petals shrink.
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

/**
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
  const cellM = grid.cellSizeM(origin.lat);
  const halfW = Math.max(0, widthM) / 2;
  const { lat: mLat, lon: mLon } = metersPerDegree(origin.lat);
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

  // 1) Centerline walk — thin corridors still hit cells they cross.
  const step = Math.max(cellM * 0.35, 1);
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
    add(row * grid.meta.width + col, along);
  }

  // 2) Width band — pull in neighbors as W grows past ~one cell.
  if (halfW > 0) {
    const pad = halfW + cellM;
    const reach = lengthM + pad;
    const west = origin.lon - reach / mLon;
    const east = origin.lon + reach / mLon;
    const south = origin.lat - reach / mLat;
    const north = origin.lat + reach / mLat;

    const c0 = Math.max(0, Math.floor((west - grid.meta.west) / cellDeg));
    const c1 = Math.min(
      grid.meta.width - 1,
      Math.floor((east - grid.meta.west) / cellDeg),
    );
    const r0 = Math.max(
      0,
      Math.floor((grid.meta.north - north) / cellDeg),
    );
    const r1 = Math.min(
      grid.meta.height - 1,
      Math.floor((grid.meta.north - south) / cellDeg),
    );

    for (let r = r0; r <= r1; r++) {
      for (let c = c0; c <= c1; c++) {
        const idx = r * grid.meta.width + c;
        const pop = grid.data[idx];
        if (!(pop > 0)) continue;
        const clat = grid.meta.north - (r + 0.5) * cellDeg;
        const clon = grid.meta.west + (c + 0.5) * cellDeg;
        const dx = (clon - origin.lon) * mLon;
        const dy = (clat - origin.lat) * mLat;
        const along = dx * dirX + dy * dirY;
        if (along < -halfW || along > lengthM) continue;
        const cross = Math.abs(dx * dirY - dy * dirX);
        if (cross > halfW) continue;
        add(idx, along);
      }
    }
  }

  return [...seen.values()];
}

/** People inside a corridor of length lengthM and width widthM. */
export function peopleInCorridor(grid, origin, bearingDeg, lengthM, widthM) {
  const hits = cellsInCorridor(grid, origin, bearingDeg, lengthM, widthM || 0);
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
 */
export function distanceToPeople(
  grid,
  origin,
  bearingDeg,
  targetPeople,
  widthM,
  maxLengthM,
) {
  if (targetPeople <= 0) return 0;
  if (maxLengthM <= 0) return Infinity;

  const hits = cellsInCorridor(
    grid,
    origin,
    bearingDeg,
    maxLengthM,
    widthM || 0,
  );
  hits.sort((a, b) => a.along - b.along);

  let people = 0;
  for (const h of hits) {
    people += h.pop;
    if (people >= targetPeople) return h.along;
  }
  return Infinity;
}

/**
 * Directional rose: distance to N people in each direction.
 * @param {import('./grid.js').PopulationGrid} grid
 * @param {{lat:number, lon:number}} origin
 * @param {object} options
 * @param {number} options.widthM
 * @param {number} options.targetPeople
 * @param {number} options.maxLengthM
 * @param {number} [options.rayCount=72]
 */
export function computeRose(grid, origin, options) {
  const {
    widthM,
    targetPeople,
    maxLengthM,
    rayCount = 72,
  } = options;
  if (!grid?.contains(origin.lat, origin.lon)) {
    throw new Error("origin is outside the population grid");
  }
  const rays = [];
  for (let i = 0; i < rayCount; i++) {
    const bearingDeg = (360 * i) / rayCount;
    const dist = distanceToPeople(
      grid,
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
        : peopleInCorridor(grid, origin, bearingDeg, maxLengthM, widthM),
      lengthM: reached ? dist : maxLengthM,
      widthM,
      reached,
    });
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
