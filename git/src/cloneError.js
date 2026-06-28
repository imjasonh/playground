/**
 * Map a raw clone/fetch failure to a friendly, actionable message.
 *
 * Pure and exported so the mapping is unit-testable in isolation. (A richer
 * typed taxonomy is noted as future work; this stays a small string sniff.)
 */

/** @param {unknown} err  @param {string} [corsProxy]  @returns {string} */
export function cloneErrorMessage(err, corsProxy) {
  const message = (err && err.message) || String(err);
  const name = (err && err.name) || '';

  // Out of IndexedDB quota: the actionable fix is to free space or shrink the
  // clone, so say that rather than the generic "clone failed".
  if (
    name === 'QuotaExceededError' ||
    /quota.?exceeded|exceeded the quota|out of (?:disk )?space|insufficient storage/i.test(message)
  ) {
    return (
      'Out of browser storage while cloning. Remove a stored repository below, ' +
      `or clone with a smaller depth, then try again. (${message})`
    );
  }

  // Authentication: a private repo (or a bad/expired token). isomorphic-git
  // surfaces these as 401/403 or an explicit auth message.
  if (
    name === 'UserCanceledError' ||
    /\b401\b|\b403\b|Unauthorized|Forbidden|authentication|HTTP Basic: Access denied/i.test(message)
  ) {
    return (
      'Authentication required or failed. If this repository is private, add a read-only ' +
      `access token in Advanced options and try again. (${message})`
    );
  }

  if (/Failed to fetch|NetworkError|CORS|ENOTFOUND/i.test(message)) {
    return corsProxy
      ? `Could not reach the repository. The CORS proxy may be down or the URL may be wrong. (${message})`
      : `Could not reach the repository. Most hosts need a CORS proxy — set one in Advanced options. (${message})`;
  }

  if (/404|not found|Could not find/i.test(message)) {
    return `Repository or ref not found. Check the URL and branch. (${message})`;
  }

  return `Clone failed: ${message}`;
}
