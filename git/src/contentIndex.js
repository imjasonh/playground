/**
 * Trigram content-search index: the persisted, reusable structure that lets a
 * content (grep) search narrow to a handful of *candidate* files instead of
 * reading and scanning every file on every keystroke.
 *
 * The idea is the one used by code-search engines (Google Code Search, ripgrep
 * with `--pre`/indexed backends): a file is represented by the *set of distinct
 * 3-character substrings* (trigrams) it contains. A literal query of length ≥ 3
 * can only appear in a file that contains *all* of the query's trigrams, so
 * intersecting those trigrams' posting lists yields a small candidate set. The
 * candidates are then scanned (see contentSearch.js) to confirm real matches and
 * collect line/column info — a trigram hit is only a *possible* match, so the
 * scan is what makes results exact.
 *
 * Everything here is pure, dependency-free, and DOM-free so it runs unchanged on
 * the main thread and inside a worker, is unit-testable in isolation, and can be
 * serialized to IndexedDB (see contentIndexStore.js) and reloaded next session.
 *
 * Trigrams are lowercased so one index serves both case-insensitive and
 * case-sensitive searches: lowercasing only *widens* the candidate set (a
 * superset), and the exact-case decision is made later by the scan.
 *
 * @typedef {Object} ContentIndex
 * @property {string[]} paths                 file paths, index = numeric file id
 * @property {Map<string, number[]>} postings trigram -> ascending file ids
 */

/** Trigram length. Threes are the sweet spot: selective without exploding size. */
export const TRIGRAM_LENGTH = 3;

/** Current on-disk format version; bump to invalidate stale serialized indexes. */
export const INDEX_FORMAT_VERSION = 1;

/**
 * Add every distinct (lowercased) trigram of `text` to `out`.
 *
 * @param {string} text
 * @param {Set<string>} [out]  reuse a set to avoid per-file allocation churn
 * @returns {Set<string>}
 */
export function extractTrigrams(text, out = new Set()) {
  if (!text) return out;
  const lower = text.toLowerCase();
  const end = lower.length - TRIGRAM_LENGTH;
  for (let i = 0; i <= end; i += 1) {
    out.add(lower.slice(i, i + TRIGRAM_LENGTH));
  }
  return out;
}

/**
 * The trigrams a literal query needs. Empty when the query is shorter than a
 * trigram — such a query can't be narrowed, so callers fall back to "every
 * indexed file is a candidate".
 *
 * @param {string} query
 * @returns {string[]}
 */
export function queryTrigrams(query) {
  return [...extractTrigrams(query || '')];
}

/**
 * Build a trigram index from decoded text entries. Callers are expected to have
 * already dropped binary/oversize files, so an index only ever holds searchable
 * text files.
 *
 * @param {Array<{path: string, text: string}>} entries
 * @returns {ContentIndex}
 */
export function buildTrigramIndex(entries) {
  const paths = [];
  /** @type {Map<string, number[]>} */
  const postings = new Map();
  const grams = new Set();
  for (const entry of entries || []) {
    if (!entry || typeof entry.path !== 'string') continue;
    const id = paths.length;
    paths.push(entry.path);
    grams.clear();
    extractTrigrams(entry.text || '', grams);
    for (const gram of grams) {
      // Ids are handed out in ascending order, so simply pushing keeps every
      // posting list sorted — which the intersection below relies on.
      let list = postings.get(gram);
      if (list === undefined) {
        list = [];
        postings.set(gram, list);
      }
      list.push(id);
    }
  }
  return { paths, postings };
}

/** Intersect two ascending id lists into a new ascending list. */
function intersectSorted(a, b) {
  const out = [];
  let i = 0;
  let j = 0;
  while (i < a.length && j < b.length) {
    const x = a[i];
    const y = b[j];
    if (x === y) {
      out.push(x);
      i += 1;
      j += 1;
    } else if (x < y) {
      i += 1;
    } else {
      j += 1;
    }
  }
  return out;
}

/**
 * Candidate paths that *may* contain the literal `query`, found by intersecting
 * the posting lists of the query's trigrams (rarest first, so the running
 * intersection stays small). A candidate is not a guaranteed match — the caller
 * scans it to confirm.
 *
 * Special cases:
 *   - A query too short to yield a trigram can't be narrowed → every indexed
 *     path is a candidate.
 *   - A required trigram absent from the index → no file can match → `[]`.
 *
 * @param {ContentIndex} index
 * @param {string} query
 * @returns {string[]}
 */
export function candidatePaths(index, query) {
  if (!index || !Array.isArray(index.paths)) return [];
  const grams = queryTrigrams(query);
  if (grams.length === 0) return index.paths.slice();

  const lists = [];
  for (const gram of grams) {
    const list = index.postings.get(gram);
    if (!list || list.length === 0) return []; // a needed trigram is missing
    lists.push(list);
  }
  lists.sort((a, b) => a.length - b.length);

  let acc = lists[0];
  for (let i = 1; i < lists.length && acc.length > 0; i += 1) {
    acc = intersectSorted(acc, lists[i]);
  }
  return acc.map((id) => index.paths[id]);
}

/**
 * Flatten an index into a plain, JSON/structured-clone-friendly object for
 * persistence. Posting lists are kept as plain arrays (a `Map` doesn't survive
 * `JSON`, and arrays clone faster into IndexedDB than a `Map` would).
 *
 * @param {ContentIndex} index
 * @returns {{version: number, paths: string[], trigrams: Record<string, number[]>}}
 */
export function serializeIndex(index) {
  const trigrams = Object.create(null);
  if (index && index.postings) {
    for (const [gram, list] of index.postings) trigrams[gram] = list;
  }
  return {
    version: INDEX_FORMAT_VERSION,
    paths: index && Array.isArray(index.paths) ? index.paths : [],
    trigrams,
  };
}

/**
 * Rebuild an index from its serialized form, or `null` when the payload is
 * missing/corrupt or from an incompatible version (so the caller rebuilds).
 *
 * @param {*} obj
 * @returns {ContentIndex|null}
 */
export function deserializeIndex(obj) {
  if (!obj || obj.version !== INDEX_FORMAT_VERSION) return null;
  if (!Array.isArray(obj.paths) || !obj.trigrams || typeof obj.trigrams !== 'object') return null;
  const postings = new Map();
  for (const gram of Object.keys(obj.trigrams)) {
    const list = obj.trigrams[gram];
    if (Array.isArray(list)) postings.set(gram, list);
  }
  return { paths: obj.paths, postings };
}
