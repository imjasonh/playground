/**
 * Deep-linkable view state encoded in the URL hash, so a repo + ref + file
 * (+ a line range) is shareable, bookmarkable, and survives a reload.
 *
 * The encoding is a small, readable `key=value&…` form after the `#`:
 *
 *   #repo=https://github.com/owner/repo&ref=branch:main&file=src/app.js&lines=10-20
 *
 * `repo` is either the clone URL or the literal `demo`. `ref` reuses the
 * `type:name` form from repoSource (`refValue`). Slashes and colons are kept
 * literal (both are legal in a fragment) so the hash stays human-readable; only
 * the genuinely unsafe characters are percent-encoded.
 *
 * The bare legacy `#demo` is still understood (it predates this module and the
 * mobile e2e suite links to it).
 *
 * Everything here is pure and dependency-free so it can be unit-tested without a
 * DOM.
 *
 * @typedef {Object} LineRange
 * @property {number} start  1-based first line (inclusive)
 * @property {number} end    1-based last line (inclusive; === start for one line)
 *
 * @typedef {Object} HashState
 * @property {string} repo            clone URL, or 'demo'
 * @property {string} [ref]           refValue, e.g. 'branch:main' / 'tag:v1' / 'commit:<oid>'
 * @property {string} [file]          repo-relative file path
 * @property {LineRange} [lines]      selected line range
 */

const KEYS = ['repo', 'ref', 'file', 'lines'];

/** Keep `/` and `:` readable; escape only what would break the key=value form. */
function encodeValue(value) {
  return encodeURIComponent(value).replace(/%2F/gi, '/').replace(/%3A/gi, ':');
}

/** Parse a "10" or "10-20" line spec into a normalized range, or null. */
export function parseLines(spec) {
  if (!spec) return null;
  const match = /^(\d+)(?:-(\d+))?$/.exec(String(spec).trim());
  if (!match) return null;
  const start = parseInt(match[1], 10);
  if (!start) return null; // line numbers are 1-based; 0 is meaningless
  const end = match[2] ? parseInt(match[2], 10) : start;
  if (!end) return null;
  return start <= end ? { start, end } : { start: end, end: start };
}

/** Format a line range back into "10" or "10-20". */
export function formatLines(range) {
  if (!range || !range.start) return '';
  return range.end && range.end !== range.start
    ? `${range.start}-${range.end}`
    : `${range.start}`;
}

/**
 * Parse a location hash into a {@link HashState}, or null when there's nothing
 * actionable. Accepts the value with or without a leading '#'.
 *
 * @param {string} hash
 * @returns {?HashState}
 */
export function parseHash(hash) {
  let raw = String(hash || '');
  if (raw.startsWith('#')) raw = raw.slice(1);
  if (!raw) return null;
  // Legacy bare "#demo".
  if (raw === 'demo') return { repo: 'demo' };

  const params = new URLSearchParams(raw);
  const repo = params.get('repo');
  if (!repo) return null;

  const state = { repo };
  const ref = params.get('ref');
  if (ref) state.ref = ref;
  const file = params.get('file');
  if (file) state.file = file;
  const lines = parseLines(params.get('lines'));
  if (lines) state.lines = lines;
  return state;
}

/**
 * Encode a {@link HashState} into a hash string *without* the leading '#'.
 * Returns '' for an empty/invalid state. Demo with nothing else collapses to
 * the short, legacy-compatible `demo`.
 *
 * @param {?HashState} state
 * @returns {string}
 */
export function encodeHashState(state) {
  if (!state || !state.repo) return '';
  if (state.repo === 'demo' && !state.ref && !state.file) return 'demo';

  const parts = [`repo=${encodeValue(state.repo)}`];
  if (state.ref) parts.push(`ref=${encodeValue(state.ref)}`);
  if (state.file) parts.push(`file=${encodeValue(state.file)}`);
  if (state.lines) {
    const lines = formatLines(state.lines);
    if (lines) parts.push(`lines=${lines}`);
  }
  return parts.join('&');
}

/** True when two hash states describe the same view (ignoring key order). */
export function sameHashState(a, b) {
  return encodeHashState(a) === encodeHashState(b);
}

// Re-export the key list so callers/tests can introspect the schema.
export const HASH_KEYS = KEYS;
