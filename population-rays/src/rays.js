/**
 * Directional corridor population.
 *
 * Model: a corridor is a thin strip of width W and length L from an origin in
 * bearing D. Homes are represented by a gridded population density field ρ.
 * People intersecting the corridor ≈ ∫ ρ(s) · W ds along the centerline.
 *
 * This is the right continuous limit when W is much smaller than a cell
 * (e.g. a 100′ strip over ~0.5–2 km cells): we count the share of each cell’s
 * population that the strip covers, not whether a cell centroid falls inside.
 */

import { destination } from "./geo.js";

/**
 * @typedef {object} RayResult
 * @property {number} bearingDeg
 * @property {number} people
 * @property {number} lengthM
 * @property {number} widthM
 */

/**
 * Integrate population along one corridor.
 * @param {import('./grid.js').PopulationGrid} grid
 * @param {{lat:number, lon:number}} origin
 * @param {number} bearingDeg
 * @param {number} lengthM
 * @param {number} widthM
 * @param {{ stepM?: number }} [opts]
 */
export function peopleInCorridor(grid, origin, bearingDeg, lengthM, widthM, opts = {}) {
  if (lengthM <= 0 || widthM <= 0) return 0;
  const cellM = grid.cellSizeM(origin.lat);
  const stepM = opts.stepM ?? Math.min(Math.max(cellM * 0.5, 50), 400);
  let people = 0;
  for (let s = stepM * 0.5; s <= lengthM; s += stepM) {
    const pt = destination(origin.lat, origin.lon, bearingDeg, s);
    const pop = grid.sample(pt.lat, pt.lon);
    if (pop <= 0) continue;
    const area = grid.cellAreaM2At(pt.lat);
    if (area <= 0) continue;
    people += (pop / area) * widthM * stepM;
  }
  return people;
}

/**
 * Walk outward until cumulative people reach `targetPeople` (or maxLengthM).
 * Returns the distance in meters; Infinity if never reached within max.
 */
export function distanceToPeople(
  grid,
  origin,
  bearingDeg,
  targetPeople,
  widthM,
  maxLengthM,
  opts = {},
) {
  if (targetPeople <= 0) return 0;
  if (widthM <= 0 || maxLengthM <= 0) return Infinity;
  const cellM = grid.cellSizeM(origin.lat);
  const stepM = opts.stepM ?? Math.min(Math.max(cellM * 0.5, 50), 400);
  let people = 0;
  for (let s = stepM * 0.5; s <= maxLengthM; s += stepM) {
    const pt = destination(origin.lat, origin.lon, bearingDeg, s);
    const pop = grid.sample(pt.lat, pt.lon);
    if (pop > 0) {
      const area = grid.cellAreaM2At(pt.lat);
      if (area > 0) people += (pop / area) * widthM * stepM;
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
 * @param {number} options.widthM corridor width
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
    widthM,
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
      rays.push({
        bearingDeg,
        people: Number.isFinite(dist) ? targetPeople : peopleInCorridor(
          grid,
          origin,
          bearingDeg,
          maxLengthM,
          widthM,
          { stepM },
        ),
        lengthM: dist,
        widthM,
      });
    } else {
      const people = peopleInCorridor(
        grid,
        origin,
        bearingDeg,
        lengthM,
        widthM,
        { stepM },
      );
      rays.push({ bearingDeg, people, lengthM, widthM });
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
