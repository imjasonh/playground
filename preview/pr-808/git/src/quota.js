/**
 * Storage-quota helpers around the StorageManager API (`navigator.storage`).
 *
 * Cloning writes the whole repository into IndexedDB (via lightning-fs), which
 * is subject to the origin's storage quota. These helpers surface usage and let
 * the UI warn before a clone is likely to fail and explain a QuotaExceededError
 * after one does. Pure except for the single `navigator` read, which is
 * injectable so the logic is unit-testable without a browser.
 */
import { formatBytes } from './format.js';

/** Warn when fewer than this many free bytes remain before a clone (~50 MB). */
export const LOW_STORAGE_BYTES = 50 * 1024 * 1024;

/**
 * @typedef {Object} StorageEstimate
 * @property {number} usage      bytes currently used by this origin
 * @property {number} quota      total bytes available to this origin
 * @property {number} available  quota - usage (never negative)
 * @property {number} ratio      usage / quota in [0, 1] (0 when quota unknown)
 */

/**
 * Best-effort storage estimate, or null when the API is unavailable or fails.
 *
 * @param {{storage?: {estimate: Function}}} [nav]
 * @returns {Promise<StorageEstimate|null>}
 */
export async function storageEstimate(nav = globalThis.navigator) {
  if (!nav || !nav.storage || typeof nav.storage.estimate !== 'function') return null;
  try {
    const { usage = 0, quota = 0 } = (await nav.storage.estimate()) || {};
    const available = Math.max(0, quota - usage);
    const ratio = quota > 0 ? usage / quota : 0;
    return { usage, quota, available, ratio };
  } catch {
    return null;
  }
}

/** Short human label for a usage meter, or '' when there's nothing to show. */
export function describeStorage(est) {
  if (!est || !est.quota) return '';
  const pct = Math.round(est.ratio * 100);
  return `${formatBytes(est.usage)} of ${formatBytes(est.quota)} used (${pct}%)`;
}

/** True when free space is below `threshold` (and a quota is actually known). */
export function isLowOnStorage(est, threshold = LOW_STORAGE_BYTES) {
  return Boolean(est && est.quota && est.available < threshold);
}
