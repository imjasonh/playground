/**
 * Turn a raw clone/fetch failure into a typed classification and a friendly,
 * actionable message.
 *
 * The mapping is split in two so each half is small and independently testable:
 *
 *   classifyCloneError(err) -> { kind, name, message }
 *   cloneErrorMessage(err, corsProxy) -> string
 *
 * `classifyCloneError` is the structured taxonomy: it sniffs the error's name
 * and message once and reduces it to a stable `kind`, so callers can branch on
 * a small enum instead of re-matching error strings. `cloneErrorMessage` builds
 * the user-facing copy from that classification. Everything here is pure and
 * dependency-free.
 */

/**
 * @typedef {'quota'|'auth'|'network'|'not-found'|'unknown'} CloneErrorKind
 *
 * @typedef {Object} CloneErrorInfo
 * @property {CloneErrorKind} kind  the stable category
 * @property {string} name          the original error name (may be '')
 * @property {string} message       the original error message
 */

/**
 * Ordered rules mapping an error to a {@link CloneErrorKind}. Each rule matches
 * on the error name (exact) and/or the message (regex); the first match wins, so
 * more specific categories are listed before broader ones. Kept as data so the
 * taxonomy is easy to read, extend, and test.
 */
const RULES = [
  {
    // Out of IndexedDB quota: the actionable fix is to free space or shrink the
    // clone, so this is its own category rather than a generic failure.
    kind: 'quota',
    names: ['QuotaExceededError'],
    test: /quota.?exceeded|exceeded the quota|out of (?:disk )?space|insufficient storage/i,
  },
  {
    // Authentication: a private repo, or a bad/expired token. isomorphic-git
    // surfaces these as 401/403, an explicit auth message, or a user-cancel.
    kind: 'auth',
    names: ['UserCanceledError'],
    test: /\b401\b|\b403\b|Unauthorized|Forbidden|authentication|HTTP Basic: Access denied/i,
  },
  {
    // Transport: DNS, offline, or a CORS rejection (often a missing/dead proxy).
    kind: 'network',
    names: [],
    test: /Failed to fetch|NetworkError|CORS|ENOTFOUND|ECONNREFUSED|ETIMEDOUT|network/i,
  },
  {
    // The repository or the requested ref doesn't exist.
    kind: 'not-found',
    names: [],
    test: /\b404\b|not found|Could not find/i,
  },
];

/**
 * Reduce any thrown value to a stable {@link CloneErrorInfo}.
 *
 * @param {unknown} err
 * @returns {CloneErrorInfo}
 */
export function classifyCloneError(err) {
  const message = (err && err.message) || String(err);
  const name = (err && err.name) || '';
  for (const rule of RULES) {
    if (rule.names.includes(name) || rule.test.test(message)) {
      return { kind: rule.kind, name, message };
    }
  }
  return { kind: 'unknown', name, message };
}

/**
 * Build a friendly, actionable message for a clone/fetch failure.
 *
 * @param {unknown} err
 * @param {string} [corsProxy]  the proxy in use, to tailor the network hint
 * @returns {string}
 */
export function cloneErrorMessage(err, corsProxy) {
  const { kind, message } = classifyCloneError(err);
  switch (kind) {
    case 'quota':
      return (
        'Out of browser storage while cloning. Remove a stored repository below, ' +
        `or clone with a smaller depth, then try again. (${message})`
      );
    case 'auth':
      return (
        'Authentication required or failed. If this repository is private, add a read-only ' +
        `access token in Advanced options and try again. (${message})`
      );
    case 'network':
      return corsProxy
        ? `Could not reach the repository. The CORS proxy may be down or the URL may be wrong. (${message})`
        : `Could not reach the repository. Most hosts need a CORS proxy — set one in Advanced options. (${message})`;
    case 'not-found':
      return `Repository or ref not found. Check the URL and branch. (${message})`;
    default:
      return `Clone failed: ${message}`;
  }
}
