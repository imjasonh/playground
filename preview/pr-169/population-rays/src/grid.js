/** In-memory population grid: people per rectangular lat/lon cell. */

import { cellAreaM2, metersPerDegree } from "./geo.js";

/**
 * @typedef {object} GridMeta
 * @property {number} west
 * @property {number} south
 * @property {number} north
 * @property {number} east
 * @property {number} cellDeg
 * @property {number} width
 * @property {number} height
 * @property {string} [key]
 * @property {string} [note]
 */

/**
 * @typedef {object} PopulationGrid
 * @property {GridMeta} meta
 * @property {Float32Array} data
 * @property {(lat:number, lon:number) => number} sample
 * @property {(lat:number) => number} cellAreaM2At
 * @property {(lat:number) => number} cellSizeM
 * @property {(lat:number, lon:number) => boolean} contains
 */

export function createGrid(meta, data) {
  if (!(data instanceof Float32Array)) {
    throw new Error("grid data must be Float32Array");
  }
  if (data.length !== meta.width * meta.height) {
    throw new Error(
      `grid size mismatch: data ${data.length} vs ${meta.width}×${meta.height}`,
    );
  }

  const { west, south, north, cellDeg, width, height } = meta;

  function contains(lat, lon) {
    return lon >= west && lon < west + width * cellDeg && lat >= south && lat < north;
  }

  function indexAt(lat, lon) {
    if (!contains(lat, lon)) return -1;
    const col = Math.floor((lon - west) / cellDeg);
    const row = Math.floor((north - lat) / cellDeg);
    if (col < 0 || col >= width || row < 0 || row >= height) return -1;
    return row * width + col;
  }

  function sample(lat, lon) {
    const i = indexAt(lat, lon);
    return i < 0 ? 0 : data[i];
  }

  function cellAreaM2At(lat) {
    return cellAreaM2(lat, cellDeg);
  }

  function cellSizeM(lat) {
    const { lat: mLat, lon: mLon } = metersPerDegree(lat);
    return Math.min(Math.abs(mLat * cellDeg), Math.abs(mLon * cellDeg));
  }

  return {
    meta,
    data,
    sample,
    cellAreaM2At,
    cellSizeM,
    contains,
    indexAt,
  };
}

/**
 * Choose a loaded grid that contains the point.
 * @param {'finest'|'broadest'} [prefer='finest']
 *   finest — smallest cell size (local detail)
 *   broadest — largest geographic extent (long rays / distance-to-N)
 */
export function pickGrid(grids, lat, lon, prefer = "finest") {
  const hits = grids.filter((g) => g.contains(lat, lon));
  if (!hits.length) return null;
  if (prefer === "broadest") {
    return hits.reduce((a, b) => {
      const ea = (a.meta.east - a.meta.west) * (a.meta.north - a.meta.south);
      const eb = (b.meta.east - b.meta.west) * (b.meta.north - b.meta.south);
      return eb > ea ? b : a;
    });
  }
  return hits.reduce((a, b) => (a.meta.cellDeg <= b.meta.cellDeg ? a : b));
}

/**
 * Choose a grid for a distance-to-N query.
 * Smaller targets use the finest local tile (better metro shape).
 * Large targets need the continental grid so rays aren't clipped.
 */
export function pickGridForTarget(grids, lat, lon, targetPeople) {
  const fine = pickGrid(grids, lat, lon, "finest");
  const broad = pickGrid(grids, lat, lon, "broadest");
  if (!fine) return broad;
  if (!broad) return fine;
  // ~250k fits in the Northeast tile for dense urban walks; 1M often needs CONUS.
  if (targetPeople <= 250_000 && fine.meta.cellDeg < broad.meta.cellDeg) {
    return fine;
  }
  return broad;
}

/**
 * Decode a little-endian float32 gzip payload into a PopulationGrid.
 * Uses DecompressionStream in browsers; Node can pass pre-decompressed bytes.
 */
export async function loadGridFromGzip(meta, gzipBytes) {
  const raw = await gunzipBytes(gzipBytes);
  if (raw.byteLength !== meta.width * meta.height * 4) {
    throw new Error(
      `unexpected grid byte length ${raw.byteLength}, expected ${meta.width * meta.height * 4}`,
    );
  }
  const data = new Float32Array(raw.buffer, raw.byteOffset, meta.width * meta.height);
  return createGrid(meta, data);
}

async function gunzipBytes(gzipBytes) {
  const bytes =
    gzipBytes instanceof Uint8Array ? gzipBytes : new Uint8Array(gzipBytes);
  if (typeof DecompressionStream === "function") {
    const stream = new Blob([bytes]).stream().pipeThrough(new DecompressionStream("gzip"));
    const buf = await new Response(stream).arrayBuffer();
    return new Uint8Array(buf);
  }
  // Node 20+: zlib
  const { gunzipSync } = await import("node:zlib");
  return gunzipSync(bytes);
}
