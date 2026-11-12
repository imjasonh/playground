/**
 * US place search via OpenStreetMap Nominatim, clipped to the CONUS population grid.
 */

/** Contiguous US bounds matching `data/conus-0p02`. */
export const CONUS_BOUNDS = {
  west: -125,
  south: 24,
  north: 50,
  east: -66,
};

const NOMINATIM_URL = "https://nominatim.openstreetmap.org/search";

/**
 * @typedef {object} GeocodeHit
 * @property {string} label
 * @property {number} lat
 * @property {number} lon
 * @property {number} zoom
 * @property {string} [type]
 */

export function inConusBounds(lat, lon, bounds = CONUS_BOUNDS) {
  return (
    lat >= bounds.south &&
    lat <= bounds.north &&
    lon >= bounds.west &&
    lon <= bounds.east
  );
}

/** Map zoom for a Nominatim result type. */
export function zoomForNominatimType(type) {
  const t = String(type || "").toLowerCase();
  if (
    t === "house" ||
    t === "building" ||
    t === "yes" ||
    t === "residential" ||
    t === "commercial"
  ) {
    return 15;
  }
  if (t === "road" || t === "highway" || t === "neighbourhood" || t === "suburb") {
    return 13;
  }
  if (t === "city" || t === "town" || t === "municipality") return 10;
  if (t === "county" || t === "state") return 7;
  return 11;
}

/**
 * Normalize Nominatim JSON into hits inside CONUS.
 * @param {unknown} payload
 * @param {{west:number,south:number,north:number,east:number}} [bounds]
 * @returns {GeocodeHit[]}
 */
export function parseNominatimResults(payload, bounds = CONUS_BOUNDS) {
  if (!Array.isArray(payload)) return [];
  const hits = [];
  for (const row of payload) {
    const lat = Number(row?.lat);
    const lon = Number(row?.lon);
    if (!Number.isFinite(lat) || !Number.isFinite(lon)) continue;
    if (!inConusBounds(lat, lon, bounds)) continue;
    const label = String(row?.display_name || "").trim();
    if (!label) continue;
    hits.push({
      label,
      lat,
      lon,
      zoom: zoomForNominatimType(row?.type || row?.addresstype),
      type: row?.type ? String(row.type) : undefined,
    });
  }
  return hits;
}

/**
 * Search US places / addresses. Results are limited to CONUS (our data coverage).
 * @param {string} query
 * @param {object} [opts]
 * @param {typeof fetch} [opts.fetchImpl]
 * @param {AbortSignal} [opts.signal]
 * @param {number} [opts.limit=5]
 * @param {typeof CONUS_BOUNDS} [opts.bounds]
 * @returns {Promise<GeocodeHit[]>}
 */
export async function searchUsPlaces(query, opts = {}) {
  const q = String(query || "").trim();
  if (q.length < 2) return [];

  const {
    fetchImpl = globalThis.fetch,
    signal,
    limit = 5,
    bounds = CONUS_BOUNDS,
  } = opts;
  if (typeof fetchImpl !== "function") {
    throw new Error("fetch is not available");
  }

  const url = new URL(NOMINATIM_URL);
  url.searchParams.set("q", q);
  url.searchParams.set("format", "jsonv2");
  url.searchParams.set("countrycodes", "us");
  url.searchParams.set("limit", String(Math.min(Math.max(limit, 1), 10)));
  // Prefer the contiguous US; still filter client-side for Alaska/Hawaii/etc.
  url.searchParams.set(
    "viewbox",
    `${bounds.west},${bounds.north},${bounds.east},${bounds.south}`,
  );
  url.searchParams.set("addressdetails", "0");

  const res = await fetchImpl(url.toString(), {
    signal,
    headers: {
      Accept: "application/json",
    },
  });
  if (!res.ok) {
    throw new Error(`Geocode failed (${res.status})`);
  }
  const payload = await res.json();
  return parseNominatimResults(payload, bounds);
}
