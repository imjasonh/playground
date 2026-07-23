/**
 * Directional corridor population.
 *
 * From an origin, extend a corridor of width W along bearing D. Count people
 * in population cells whose centers fall inside that corridor. Ask: how long
 * must the corridor be before it has hit N people?
 *
 * At packaged resolutions (~0.5–2 km), a corridor thinner than a cell behaves
 * like “cells the centerline crosses.” Wider corridors pull in neighboring
 * cells.
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
 * Corridor width used for queries. Never thinner than two cell widths so a
 * cell center up to ~1 cell off the centerline (pin near a cell corner) still
 * counts — otherwise thin corridors miss the grid entirely.
 */
export function effectiveCorridorWidthM(grid, origin, widthM) {
  const cellM = grid.cellSizeM(origin.lat);
  return Math.max(widthM || 0, cellM * 2);
}

/**
 * Collect unique cell indices whose centers lie in the corridor
 * [0, lengthM] × widthM centered on the ray.
 */
function cellsInCorridor(grid, origin, bearingDeg, lengthM, widthM) {
  if (lengthM <= 0 || widthM <= 0) return [];
  const halfW = widthM / 2;
  const { lat: mLat, lon: mLon } = metersPerDegree(origin.lat);
  const rad = (bearingDeg * Math.PI) / 180;
  const dirX = Math.sin(rad); // east
  const dirY = Math.cos(rad); // north

  const pad = halfW + grid.cellSizeM(origin.lat);
  const reach = lengthM + pad;
  const west = origin.lon - reach / mLon;
  const east = origin.lon + reach / mLon;
  const south = origin.lat - reach / mLat;
  const north = origin.lat + reach / mLat;

  const c0 = Math.max(0, Math.floor((west - grid.meta.west) / grid.meta.cellDeg));
  const c1 = Math.min(
    grid.meta.width - 1,
    Math.floor((east - grid.meta.west) / grid.meta.cellDeg),
  );
  const r0 = Math.max(
    0,
    Math.floor((grid.meta.north - north) / grid.meta.cellDeg),
  );
  const r1 = Math.min(
    grid.meta.height - 1,
    Math.floor((grid.meta.north - south) / grid.meta.cellDeg),
  );

  const hits = [];
  for (let r = r0; r <= r1; r++) {
    for (let c = c0; c <= c1; c++) {
      const idx = r * grid.meta.width + c;
      const pop = grid.data[idx];
      if (!(pop > 0)) continue;
      const clat = grid.meta.north - (r + 0.5) * grid.meta.cellDeg;
      const clon = grid.meta.west + (c + 0.5) * grid.meta.cellDeg;
      const dx = (clon - origin.lon) * mLon;
      const dy = (clat - origin.lat) * mLat;
      const along = dx * dirX + dy * dirY;
      // Include the origin cell (along ≈ 0); only drop cells behind the pin.
      if (along < -halfW || along > lengthM) continue;
      const cross = Math.abs(dx * dirY - dy * dirX);
      if (cross > halfW) continue;
      hits.push({ idx, pop, along: Math.max(0, along) });
    }
  }
  return hits;
}

/** People inside a corridor of length lengthM and width widthM. */
export function peopleInCorridor(grid, origin, bearingDeg, lengthM, widthM) {
  const w = effectiveCorridorWidthM(grid, origin, widthM);
  const hits = cellsInCorridor(grid, origin, bearingDeg, lengthM, w);
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

  const w = effectiveCorridorWidthM(grid, origin, widthM);
  const hits = cellsInCorridor(grid, origin, bearingDeg, maxLengthM, w);
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
