/**
 * Directional population slices.
 *
 * From an origin, take a filled pie slice of angular width S (default 2°,
 * matching a 180-ray rose). Count people in population cells whose centers
 * fall in the slice. Petal length = how far the slice must extend to hit N
 * people.
 *
 * When several grids cover the origin, finer tiles win where they overlap so
 * a metro tile can hand off to CONUS for long slices (e.g. NYC → Chicago).
 */

import { destination, metersPerDegree } from "./geo.js";

/**
 * @typedef {object} RayResult
 * @property {number} bearingDeg
 * @property {number} people
 * @property {number} lengthM
 * @property {number} sliceDeg
 * @property {boolean} reached
 */

export const DEFAULT_SLICE_DEG = 2;

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

/** Smallest signed degree difference in (-180, 180]. */
export function deltaBearingDeg(a, b) {
  let d = ((((a - b) % 360) + 360) % 360);
  if (d > 180) d -= 360;
  return d;
}

/** Forward azimuth from origin to a point (degrees, 0 = north). */
export function bearingBetween(origin, lat, lon) {
  const φ1 = (origin.lat * Math.PI) / 180;
  const φ2 = (lat * Math.PI) / 180;
  const Δλ = ((lon - origin.lon) * Math.PI) / 180;
  const y = Math.sin(Δλ) * Math.cos(φ2);
  const x =
    Math.cos(φ1) * Math.sin(φ2) -
    Math.sin(φ1) * Math.cos(φ2) * Math.cos(Δλ);
  return ((Math.atan2(y, x) * 180) / Math.PI + 360) % 360;
}

/** Great-circle distance in meters. */
export function distanceM(origin, lat, lon) {
  const R = 6_371_000;
  const φ1 = (origin.lat * Math.PI) / 180;
  const φ2 = (lat * Math.PI) / 180;
  const Δφ = ((lat - origin.lat) * Math.PI) / 180;
  const Δλ = ((lon - origin.lon) * Math.PI) / 180;
  const s =
    Math.sin(Δφ / 2) ** 2 +
    Math.cos(φ1) * Math.cos(φ2) * Math.sin(Δλ / 2) ** 2;
  return 2 * R * Math.asin(Math.min(1, Math.sqrt(s)));
}

/**
 * Axis-aligned bbox covering a circular sector (origin + arc tips).
 * @returns {{south:number, north:number, west:number, east:number}}
 */
function sectorBBox(origin, bearingDeg, sliceDeg, lengthM) {
  const half = sliceDeg / 2;
  const bearings = [
    bearingDeg - half,
    bearingDeg,
    bearingDeg + half,
    bearingDeg - half / 2,
    bearingDeg + half / 2,
  ];
  let south = origin.lat;
  let north = origin.lat;
  let west = origin.lon;
  let east = origin.lon;
  for (const b of bearings) {
    const p = destination(origin.lat, origin.lon, b, lengthM);
    if (p.lat < south) south = p.lat;
    if (p.lat > north) north = p.lat;
    if (p.lon < west) west = p.lon;
    if (p.lon > east) east = p.lon;
  }
  // Pad by ~one cell so edge cells aren’t clipped by geodesic vs bbox.
  const pad = 0.05;
  return {
    south: south - pad,
    north: north + pad,
    west: west - pad,
    east: east + pad,
  };
}

/**
 * Population cells that intersect the filled slice out to lengthM.
 * A cell counts when its center is within the slice, or close enough that the
 * cell’s footprint overlaps the wedge (important near the pin, where a 2°
 * slice is narrower than a coarse grid cell).
 * @returns {{idx:number, pop:number, along:number}[]}
 */
export function cellsInSector(grid, origin, bearingDeg, sliceDeg, lengthM) {
  if (!(lengthM > 0) || !(sliceDeg > 0)) return [];

  const half = sliceDeg / 2;
  const bbox = sectorBBox(origin, bearingDeg, sliceDeg, lengthM);
  const { west, south, north, cellDeg, width, height } = grid.meta;
  const { lat: mLat0, lon: mLon0 } = metersPerDegree(origin.lat);
  const cellRM = 0.5 * Math.hypot(Math.abs(mLat0 * cellDeg), Math.abs(mLon0 * cellDeg));

  const col0 = Math.max(0, Math.floor((bbox.west - west) / cellDeg) - 1);
  const col1 = Math.min(width - 1, Math.floor((bbox.east - west) / cellDeg) + 1);
  const row0 = Math.max(0, Math.floor((north - bbox.north) / cellDeg) - 1);
  const row1 = Math.min(height - 1, Math.floor((north - bbox.south) / cellDeg) + 1);
  if (col0 > col1 || row0 > row1) return [];

  // Also include every cell that contains the origin (bearing is unstable).
  const originCol = Math.floor((origin.lon - west) / cellDeg);
  const originRow = Math.floor((north - origin.lat) / cellDeg);

  /** @type {Map<number, {idx:number, pop:number, along:number}>} */
  const seen = new Map();

  function consider(row, col) {
    if (row < 0 || row >= height || col < 0 || col >= width) return;
    const idx = row * width + col;
    if (seen.has(idx)) return;
    const pop = grid.data[idx];
    if (!(pop > 0)) return;
    const lat = north - (row + 0.5) * cellDeg;
    const lon = west + (col + 0.5) * cellDeg;
    const along = distanceM(origin, lat, lon);
    // Allow the origin cell even when the pin sits near a corner (along ≈ cellR).
    const isOriginCell = row === originRow && col === originCol;
    if (!isOriginCell && along > lengthM + cellRM) return;
    if (isOriginCell) {
      seen.set(idx, { idx, pop, along: 0 });
      return;
    }
    if (along > lengthM) return;
    const br = bearingBetween(origin, lat, lon);
    // Inflate the half-angle by the cell’s angular radius so coarse cells that
    // straddle the wedge still count.
    const inflateDeg =
      (Math.atan2(cellRM, Math.max(along, cellRM * 0.25)) * 180) / Math.PI;
    if (Math.abs(deltaBearingDeg(br, bearingDeg)) > half + inflateDeg) return;
    seen.set(idx, { idx, pop, along });
  }

  consider(originRow, originCol);
  for (let row = row0; row <= row1; row++) {
    for (let col = col0; col <= col1; col++) {
      consider(row, col);
    }
  }
  return [...seen.values()];
}

/**
 * Slice hits across one or more grids. Finer tiles win where they overlap.
 */
function sectorHitsOnGrids(
  gridOrGrids,
  origin,
  bearingDeg,
  sliceDeg,
  lengthM,
) {
  const grids = orderedGrids(gridOrGrids, origin);
  /** @type {{along:number, pop:number}[]} */
  const merged = [];
  for (let gi = 0; gi < grids.length; gi++) {
    const grid = grids[gi];
    const finer = grids.slice(0, gi);
    const hits = cellsInSector(
      grid,
      origin,
      bearingDeg,
      sliceDeg,
      lengthM,
    );
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

/** People inside a filled slice of length lengthM and angular width sliceDeg. */
export function peopleInSlice(
  gridOrGrids,
  origin,
  bearingDeg,
  lengthM,
  sliceDeg = DEFAULT_SLICE_DEG,
) {
  const hits = sectorHitsOnGrids(
    gridOrGrids,
    origin,
    bearingDeg,
    sliceDeg,
    lengthM,
  );
  let people = 0;
  for (const h of hits) people += h.pop;
  return people;
}

/** @deprecated Use peopleInSlice. */
export function peopleInCorridor(
  gridOrGrids,
  origin,
  bearingDeg,
  lengthM,
  _widthM,
  sliceDeg = DEFAULT_SLICE_DEG,
) {
  return peopleInSlice(gridOrGrids, origin, bearingDeg, lengthM, sliceDeg);
}

/**
 * Resolve grid row/col for a lat/lon, or null if outside.
 * @returns {{row:number, col:number, idx:number}|null}
 */
function cellIndexAt(grid, lat, lon) {
  if (!grid.contains(lat, lon)) return null;
  const { west, north, cellDeg, width, height } = grid.meta;
  const col = Math.floor((lon - west) / cellDeg);
  const row = Math.floor((north - lat) / cellDeg);
  if (col < 0 || col >= width || row < 0 || row >= height) return null;
  return { row, col, idx: row * width + col };
}

/**
 * Fast distance-to-N for one slice.
 * 1) Exact near-field AABB (cheap while the wedge is small)
 * 2) Coarse radial march beyond that (avoids 10k+ fine rings out to 3000 mi)
 * @returns {RayResult}
 */
function probeRayRadial(
  grids,
  origin,
  bearingDeg,
  targetPeople,
  sliceDeg,
  maxLengthM,
) {
  const half = sliceDeg / 2;
  const fineM = Math.min(...grids.map((g) => g.cellSizeM(origin.lat)));
  const coarseM = Math.max(...grids.map((g) => g.cellSizeM(origin.lat)));
  const cellRM = coarseM * 0.65;
  const nearM = Math.min(maxLengthM, Math.max(60_000, fineM * 40));

  /** @type {Set<string>} */
  const seen = new Set();
  let people = 0;

  /**
   * @param {number} gi
   * @param {number} idx
   * @param {number} pop
   * @param {number} along
   */
  function credit(gi, idx, pop, along) {
    const key = `${gi}:${idx}`;
    if (seen.has(key)) return null;
    const grid = grids[gi];
    const { lat, lon } = cellCenter(grid, idx);
    for (let fj = 0; fj < gi; fj++) {
      if (grids[fj].contains(lat, lon)) return null;
    }
    seen.add(key);
    if (!(pop > 0)) return null;
    return { along, pop };
  }

  // Near field: full cell enumeration in a small sector (accurate + cheap).
  {
    const nearHits = sectorHitsOnGrids(
      grids,
      origin,
      bearingDeg,
      sliceDeg,
      nearM,
    );
    for (const h of nearHits) {
      people += h.pop;
      if (people >= targetPeople) {
        return {
          bearingDeg,
          people: targetPeople,
          lengthM: h.along,
          sliceDeg,
          reached: true,
        };
      }
    }
  }

  if (nearM >= maxLengthM) {
    return {
      bearingDeg,
      people,
      lengthM: maxLengthM,
      sliceDeg,
      reached: false,
    };
  }

  // Far field: radial samples stepped by the coarsest cell size.
  const dRad = Math.max(coarseM * 0.55, 400);
  for (let r = nearM + dRad; r < maxLengthM + dRad; r += dRad) {
    const rUse = Math.min(r, maxLengthM);
    const angleStep = Math.min(
      half * 0.5,
      Math.max(0.1, ((dRad * 0.95) / Math.max(rUse, dRad)) * (180 / Math.PI)),
    );
    /** @type {{along:number, pop:number}[]} */
    const batch = [];
    for (
      let a = bearingDeg - half;
      a <= bearingDeg + half + 1e-9;
      a += angleStep
    ) {
      const p = destination(origin.lat, origin.lon, a, rUse);
      for (let gi = 0; gi < grids.length; gi++) {
        const grid = grids[gi];
        const at = cellIndexAt(grid, p.lat, p.lon);
        if (!at) continue;
        const { lat, lon } = cellCenter(grid, at.idx);
        const along = distanceM(origin, lat, lon);
        if (along <= nearM || along > maxLengthM + cellRM) continue;
        const br = bearingBetween(origin, lat, lon);
        const inflate =
          (Math.atan2(cellRM, Math.max(along, cellRM * 0.25)) * 180) / Math.PI;
        if (Math.abs(deltaBearingDeg(br, bearingDeg)) > half + inflate) {
          continue;
        }
        const hit = credit(gi, at.idx, grid.data[at.idx], along);
        if (hit) batch.push(hit);
      }
    }
    batch.sort((a, b) => a.along - b.along);
    for (const h of batch) {
      people += h.pop;
      if (people >= targetPeople) {
        return {
          bearingDeg,
          people: targetPeople,
          lengthM: h.along,
          sliceDeg,
          reached: true,
        };
      }
    }
    if (rUse >= maxLengthM) break;
  }

  return {
    bearingDeg,
    people,
    lengthM: maxLengthM,
    sliceDeg,
    reached: false,
  };
}

/**
 * One bearing: shortest slice length to N people.
 * @returns {RayResult}
 */
export function probeRay(
  gridOrGrids,
  origin,
  bearingDeg,
  targetPeople,
  sliceDeg,
  maxLengthM,
) {
  const slice = sliceDeg > 0 ? sliceDeg : DEFAULT_SLICE_DEG;
  if (targetPeople <= 0) {
    return {
      bearingDeg,
      people: 0,
      lengthM: 0,
      sliceDeg: slice,
      reached: true,
    };
  }
  if (maxLengthM <= 0) {
    return {
      bearingDeg,
      people: 0,
      lengthM: 0,
      sliceDeg: slice,
      reached: false,
    };
  }

  const grids = orderedGrids(gridOrGrids, origin);
  if (!grids.length) {
    return {
      bearingDeg,
      people: 0,
      lengthM: maxLengthM,
      sliceDeg: slice,
      reached: false,
    };
  }

  return probeRayRadial(
    grids,
    origin,
    bearingDeg,
    targetPeople,
    slice,
    maxLengthM,
  );
}

/**
 * Shortest slice length to accumulate targetPeople (meters), or Infinity.
 * `sliceOrWidth` accepts slice degrees (preferred) or a legacy width_m ignored
 * when `sliceDeg` is passed via options — kept as positional sliceDeg.
 */
export function distanceToPeople(
  gridOrGrids,
  origin,
  bearingDeg,
  targetPeople,
  sliceDeg,
  maxLengthM,
) {
  const ray = probeRay(
    gridOrGrids,
    origin,
    bearingDeg,
    targetPeople,
    sliceDeg,
    maxLengthM,
  );
  return ray.reached ? ray.lengthM : Infinity;
}

/**
 * Directional rose: distance to N people in each slice.
 * @param {import('./grid.js').PopulationGrid | import('./grid.js').PopulationGrid[]} gridOrGrids
 * @param {{lat:number, lon:number}} origin
 * @param {object} options
 * @param {number} options.targetPeople
 * @param {number} options.maxLengthM
 * @param {number} [options.rayCount=180]
 * @param {number} [options.sliceDeg=2] — angular width; defaults to 360/rayCount
 */
export function computeRose(gridOrGrids, origin, options) {
  const {
    targetPeople,
    maxLengthM,
    rayCount = 180,
    sliceDeg = 360 / rayCount,
  } = options;
  const grids = orderedGrids(gridOrGrids, origin);
  if (!grids.length) {
    throw new Error("origin is outside the population grid");
  }
  const rays = [];
  for (let i = 0; i < rayCount; i++) {
    const bearingDeg = (360 * i) / rayCount;
    rays.push(
      probeRay(grids, origin, bearingDeg, targetPeople, sliceDeg, maxLengthM),
    );
  }
  return rays;
}

/**
 * Same as computeRose, but yields to the event loop so mobile Safari can paint.
 * @param {(done:number, total:number) => void} [onProgress]
 */
export async function computeRoseAsync(
  gridOrGrids,
  origin,
  options,
  onProgress,
) {
  const {
    targetPeople,
    maxLengthM,
    rayCount = 180,
    sliceDeg = 360 / rayCount,
  } = options;
  const grids = orderedGrids(gridOrGrids, origin);
  if (!grids.length) {
    throw new Error("origin is outside the population grid");
  }
  const rays = [];
  for (let i = 0; i < rayCount; i++) {
    const bearingDeg = (360 * i) / rayCount;
    rays.push(
      probeRay(grids, origin, bearingDeg, targetPeople, sliceDeg, maxLengthM),
    );
    if (i % 12 === 11 || i === rayCount - 1) {
      onProgress?.(i + 1, rayCount);
      await new Promise((r) => setTimeout(r, 0));
    }
  }
  return rays;
}

/** @deprecated Rose always uses every covering grid (finest-first cascade). */
export function selectRoseGrid(gridOrGrids, origin, _options) {
  return orderedGrids(gridOrGrids, origin)[0] || null;
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

// --- legacy exports kept for older tests (thin-corridor helpers removed) ---

/** @deprecated Thin-corridor helper; unused by the slice model. */
export function edgeBlend1D(f) {
  const i0 = Math.floor(f);
  const t = f - i0;
  const EDGE = 0.05;
  if (t <= EDGE) {
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

/** @deprecated Thin-corridor helper; unused by the slice model. */
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
