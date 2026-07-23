/**
 * Directional population along a thin line.
 *
 * From an origin, walk a bearing and sum the population of each distinct grid
 * cell the line first enters. That answers: “how many people’s home cells does
 * this line cross?” — and, conversely, how far until it has crossed N people.
 *
 * At the packaged resolutions (~0.5–2 km cells), a 100′ corridor is thinner
 * than a cell, so “cells the centerline crosses” is the right discrete model
 * for “homes along a thin line.” In Midtown that reaches 1M in tens of miles;
 * in rural Wyoming it can take thousands.
 */

import { destination } from "./geo.js";

/**
 * @typedef {object} RayResult
 * @property {number} bearingDeg
 * @property {number} people
 * @property {number} lengthM
 * @property {number} widthM
 * @property {boolean} reached
 */

/**
 * Sum unique cell populations crossed by a line of length `lengthM`.
 * @param {import('./grid.js').PopulationGrid} grid
 * @param {{lat:number, lon:number}} origin
 * @param {number} bearingDeg
 * @param {number} lengthM
 * @param {{ stepM?: number }} [opts]
 */
export function peopleAlongLine(grid, origin, bearingDeg, lengthM, opts = {}) {
  if (lengthM <= 0) return 0;
  const cellM = grid.cellSizeM(origin.lat);
  const stepM = opts.stepM ?? Math.min(Math.max(cellM * 0.45, 50), 500);
  const seen = new Set();
  let people = 0;

  // Include the origin cell.
  const originIdx = grid.indexAt(origin.lat, origin.lon);
  if (originIdx >= 0) {
    seen.add(originIdx);
    people += grid.data[originIdx];
  }

  for (let s = stepM; s <= lengthM; s += stepM) {
    const pt = destination(origin.lat, origin.lon, bearingDeg, s);
    const idx = grid.indexAt(pt.lat, pt.lon);
    if (idx < 0 || seen.has(idx)) continue;
    seen.add(idx);
    people += grid.data[idx];
  }
  return people;
}

/** @deprecated alias — older tests/docs referred to a corridor integral */
export function peopleInCorridor(grid, origin, bearingDeg, lengthM, _widthM, opts) {
  return peopleAlongLine(grid, origin, bearingDeg, lengthM, opts);
}

/**
 * Walk outward until unique crossed-cell population reaches `targetPeople`.
 * Returns distance in meters, or Infinity if not reached within maxLengthM.
 */
export function distanceToPeople(
  grid,
  origin,
  bearingDeg,
  targetPeople,
  _widthM,
  maxLengthM,
  opts = {},
) {
  if (targetPeople <= 0) return 0;
  if (maxLengthM <= 0) return Infinity;
  const cellM = grid.cellSizeM(origin.lat);
  const stepM = opts.stepM ?? Math.min(Math.max(cellM * 0.45, 50), 500);
  const seen = new Set();
  let people = 0;

  const originIdx = grid.indexAt(origin.lat, origin.lon);
  if (originIdx >= 0) {
    seen.add(originIdx);
    people += grid.data[originIdx];
    if (people >= targetPeople) return 0;
  }

  for (let s = stepM; s <= maxLengthM; s += stepM) {
    const pt = destination(origin.lat, origin.lon, bearingDeg, s);
    const idx = grid.indexAt(pt.lat, pt.lon);
    if (idx >= 0 && !seen.has(idx)) {
      seen.add(idx);
      people += grid.data[idx];
    }
    if (people >= targetPeople) return s;
  }
  return Infinity;
}

/**
 * Compute a directional rose around an origin.
 *
 * @param {import('./grid.js').PopulationGrid} grid
 * @param {{lat:number, lon:number}} origin
 * @param {object} options
 * @param {'fixedLength'|'fixedPeople'} options.mode
 * @param {number} [options.widthM] kept for API compat / future strip tests
 * @param {number} [options.lengthM] used in fixedLength mode
 * @param {number} [options.targetPeople] used in fixedPeople mode
 * @param {number} [options.maxLengthM] cap for fixedPeople search
 * @param {number} [options.rayCount=180]
 * @param {number} [options.stepM]
 * @returns {RayResult[]}
 */
export function computeRose(grid, origin, options) {
  const {
    mode,
    widthM = 0,
    lengthM = 0,
    targetPeople = 0,
    maxLengthM = lengthM || 0,
    rayCount = 180,
    stepM,
  } = options;
  if (!grid?.contains(origin.lat, origin.lon)) {
    throw new Error("origin is outside the population grid");
  }
  const rays = [];
  for (let i = 0; i < rayCount; i++) {
    const bearingDeg = (360 * i) / rayCount;
    if (mode === "fixedPeople") {
      const dist = distanceToPeople(
        grid,
        origin,
        bearingDeg,
        targetPeople,
        widthM,
        maxLengthM,
        { stepM },
      );
      const reached = Number.isFinite(dist);
      rays.push({
        bearingDeg,
        people: reached
          ? targetPeople
          : peopleAlongLine(grid, origin, bearingDeg, maxLengthM, { stepM }),
        lengthM: reached ? dist : maxLengthM,
        widthM,
        reached,
      });
    } else {
      const people = peopleAlongLine(grid, origin, bearingDeg, lengthM, {
        stepM,
      });
      rays.push({
        bearingDeg,
        people,
        lengthM,
        widthM,
        reached: true,
      });
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

/** Scale lengths for fixedLength mode so the longest petal reaches maxLengthM. */
export function scaledLengths(rays, maxLengthM) {
  let maxPeople = 0;
  for (const r of rays) maxPeople = Math.max(maxPeople, r.people);
  if (maxPeople <= 0) return rays.map(() => 0);
  return rays.map((r) => (r.people / maxPeople) * maxLengthM);
}
