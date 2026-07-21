// Client for the life-print Worker (Slant 3D quote backend).

export const STORAGE_KEY = 'life-lab.printApi';
export const SLANT_BED_MM = 220;

/** Resolve the Worker base URL from ?printApi=, localStorage, or a fallback. */
export function resolvePrintApiBase({ search = '', storage = null, fallback = '' } = {}) {
  const params = new URLSearchParams(search.startsWith('?') ? search.slice(1) : search);
  const fromQuery = (params.get('printApi') || '').trim().replace(/\/$/, '');
  if (fromQuery) {
    try {
      storage?.setItem(STORAGE_KEY, fromQuery);
    } catch {
      /* ignore quota / private mode */
    }
    return fromQuery;
  }
  try {
    const stored = (storage?.getItem(STORAGE_KEY) || '').trim().replace(/\/$/, '');
    if (stored) return stored;
  } catch {
    /* ignore */
  }
  return (fallback || '').trim().replace(/\/$/, '');
}

export function savePrintApiBase(base, storage = null) {
  const cleaned = (base || '').trim().replace(/\/$/, '');
  if (!cleaned) {
    try {
      storage?.removeItem(STORAGE_KEY);
    } catch {
      /* ignore */
    }
    return '';
  }
  try {
    storage?.setItem(STORAGE_KEY, cleaned);
  } catch {
    /* ignore */
  }
  return cleaned;
}

/** Axis lengths in mm for the current sculpture (Z includes the base layer). */
export function sculptureSizeMm({ width, height, depth, cellMm }) {
  return {
    x: width * cellMm,
    y: height * cellMm,
    z: (depth + 1) * cellMm,
  };
}

/** True when the sculpture fits Slant's 220³ mm build volume. */
export function fitsSlantBed(sizeMm, bedMm = SLANT_BED_MM) {
  return sizeMm.x <= bedMm && sizeMm.y <= bedMm && sizeMm.z <= bedMm;
}

/**
 * POST a binary STL to the life-print Worker and return the parsed quote.
 * @param {string} base Worker origin
 * @param {Uint8Array|ArrayBuffer} stlBytes
 * @param {typeof fetch} [fetchImpl]
 */
export async function requestQuote(base, stlBytes, fetchImpl = fetch) {
  const root = (base || '').trim().replace(/\/$/, '');
  if (!root) {
    throw new Error('Set the life-print Worker URL first (e.g. https://life-print.example.workers.dev).');
  }
  const body = stlBytes instanceof ArrayBuffer ? new Uint8Array(stlBytes) : stlBytes;
  const res = await fetchImpl(`${root}/quote`, {
    method: 'POST',
    headers: { 'Content-Type': 'model/stl' },
    body,
  });
  let payload = null;
  const text = await res.text();
  try {
    payload = text ? JSON.parse(text) : null;
  } catch {
    payload = null;
  }
  if (!res.ok) {
    const msg = payload?.error || text || `HTTP ${res.status}`;
    throw new Error(msg);
  }
  if (typeof payload?.price !== 'number') {
    throw new Error('Quote response missing price');
  }
  return payload;
}

/** Format a USD price for the UI. */
export function formatPrice(price, currency = 'USD') {
  try {
    return new Intl.NumberFormat(undefined, { style: 'currency', currency }).format(price);
  } catch {
    return `$${Number(price).toFixed(2)}`;
  }
}
