/**
 * Lightweight fuzzy subsequence matcher for the file finder. No dependencies.
 *
 * Scoring favors (higher is better):
 *   - contiguous runs of matched characters
 *   - matches at word boundaries (start, after a separator, camelCase humps)
 *   - matches close to the start of the string
 * A query that is not a subsequence of the target does not match.
 */

const SEPARATORS = new Set(['/', '\\', '_', '-', '.', ' ']);

const BASE = 1;
const CONTIGUOUS_BONUS = 18;
const BOUNDARY_BONUS = 14;
const LEADING_PENALTY = 2; // per char before the first match (capped)
const MAX_LEADING_PENALTY = 12;

function isBoundary(target, index) {
  if (index === 0) return true;
  const prev = target[index - 1];
  if (SEPARATORS.has(prev)) return true;
  const cur = target[index];
  // camelCase hump: lower/digit followed by upper
  if (cur >= 'A' && cur <= 'Z' && !(prev >= 'A' && prev <= 'Z')) return true;
  return false;
}

/**
 * Score a single target against a non-empty, already-lowercased query.
 *
 * Both the lowercased query (`ql`) and the lowercased target (`tl`) are passed in
 * so the hot path never re-lowercases — the index precomputes `tl` once (see
 * {@link buildIndex}) and reuses it across every keystroke. The original-case
 * `target` is still needed for word-boundary detection (camelCase humps).
 *
 * @param {string} ql      lowercased, trimmed, non-empty query
 * @param {string} target  original-case target
 * @param {string} tl      lowercased target (must equal target.toLowerCase())
 * @returns {{matched: boolean, score: number, positions: number[]}}
 */
function scorePrepared(ql, target, tl) {
  const positions = [];
  let score = 0;
  let ti = 0;
  let prevMatchIndex = -2;

  for (let qi = 0; qi < ql.length; qi += 1) {
    const qc = ql[qi];
    let found = false;
    while (ti < tl.length) {
      if (tl[ti] === qc) {
        positions.push(ti);
        score += BASE;
        if (isBoundary(target, ti)) score += BOUNDARY_BONUS;
        if (ti === prevMatchIndex + 1) score += CONTIGUOUS_BONUS;
        prevMatchIndex = ti;
        ti += 1;
        found = true;
        break;
      }
      ti += 1;
    }
    if (!found) return { matched: false, score: 0, positions: [] };
  }

  score -= Math.min(positions[0] * LEADING_PENALTY, MAX_LEADING_PENALTY);
  return { matched: true, score, positions };
}

/**
 * @param {string} query
 * @param {string} target
 * @returns {{matched: boolean, score: number, positions: number[]}}
 */
export function fuzzyMatch(query, target) {
  const q = (query || '').trim();
  if (q === '') return { matched: true, score: 0, positions: [] };
  if (!target) return { matched: false, score: 0, positions: [] };
  return scorePrepared(q.toLowerCase(), target, target.toLowerCase());
}

/**
 * Build a reusable search index from a list of items. This is the work that can
 * be hoisted off the per-keystroke path (and off the main thread — see
 * `searchWorker.js`): every target is lowercased exactly once here instead of on
 * every query.
 *
 * @template T
 * @param {T[]} items
 * @param {(item: T) => string} [key]
 * @returns {{items: T[], targets: string[], lowers: string[]}}
 */
export function buildIndex(items, key = (x) => x) {
  const list = items || [];
  const targets = new Array(list.length);
  const lowers = new Array(list.length);
  for (let i = 0; i < list.length; i += 1) {
    const target = key(list[i]) || '';
    targets[i] = target;
    lowers[i] = target.toLowerCase();
  }
  return { items: list, targets, lowers };
}

/** Stable ranking: score desc, then shorter target, then lexicographic. */
function compareResults(a, b) {
  if (b.score !== a.score) return b.score - a.score;
  if (a.target.length !== b.target.length) return a.target.length - b.target.length;
  return a.target < b.target ? -1 : a.target > b.target ? 1 : 0;
}

/**
 * Filter and rank a precomputed {@link buildIndex} by a query. Identical output
 * to {@link fuzzyFilter}, but reuses the index's lowercased targets so it can run
 * cheaply on every keystroke (and inside a worker).
 *
 * @template T
 * @param {string} query
 * @param {{items: T[], targets: string[], lowers: string[]}} index
 * @param {{limit?: number}} [opts]
 * @returns {{item: T, score: number, positions: number[], target: string}[]}
 */
export function fuzzyFilterIndex(query, index, opts = {}) {
  const { items, targets, lowers } = index;
  const q = (query || '').trim();

  const results = [];
  if (q === '') {
    // Empty query keeps original order, mirroring fuzzyMatch('', …).
    for (let i = 0; i < items.length; i += 1) {
      results.push({ item: items[i], score: 0, positions: [], target: targets[i] });
    }
  } else {
    const ql = q.toLowerCase();
    for (let i = 0; i < items.length; i += 1) {
      const target = targets[i];
      if (!target) continue;
      const { matched, score, positions } = scorePrepared(ql, target, lowers[i]);
      if (matched) results.push({ item: items[i], score, positions, target });
    }
    results.sort(compareResults);
  }

  return typeof opts.limit === 'number' ? results.slice(0, opts.limit) : results;
}

/**
 * Filter and rank a list of items by a query.
 *
 * @template T
 * @param {string} query
 * @param {T[]} items
 * @param {{key?: (item: T) => string, limit?: number}} [opts]
 * @returns {{item: T, score: number, positions: number[], target: string}[]}
 */
export function fuzzyFilter(query, items, opts = {}) {
  const key = opts.key || ((x) => x);
  return fuzzyFilterIndex(query, buildIndex(items, key), opts);
}

/**
 * Split a target string into alternating {text, match} segments based on the
 * matched positions, for highlight rendering.
 *
 * @param {string} target
 * @param {number[]} positions  sorted ascending
 * @returns {{text: string, match: boolean}[]}
 */
export function highlightSegments(target, positions) {
  if (!positions || positions.length === 0) {
    return target ? [{ text: target, match: false }] : [];
  }
  const set = new Set(positions);
  const segments = [];
  let buffer = '';
  let bufferMatch = set.has(0);
  for (let i = 0; i < target.length; i += 1) {
    const match = set.has(i);
    if (match !== bufferMatch && buffer) {
      segments.push({ text: buffer, match: bufferMatch });
      buffer = '';
    }
    bufferMatch = match;
    buffer += target[i];
  }
  if (buffer) segments.push({ text: buffer, match: bufferMatch });
  return segments;
}
