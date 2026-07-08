/**
 * Trigram content-search index: the persisted, reusable structure that lets a
 * content (grep) search narrow to a handful of *candidate* files instead of
 * reading and scanning every file on every keystroke.
 *
 * The idea is the one used by code-search engines (Google Code Search, ripgrep
 * with indexed backends): a file is represented by the *set of distinct
 * 3-character substrings* (trigrams) it contains. A literal query of length ≥ 3
 * can only appear in a file that contains *all* of the query's trigrams, so
 * intersecting those trigrams' posting lists yields a small candidate set. The
 * candidates are then scanned (see contentSearch.js) to confirm real matches and
 * collect line/column info — a trigram hit is only a *possible* match, so the
 * scan is what makes results exact.
 *
 * The index is mutable at the granularity of a single file (`indexFile` /
 * `removeFile`), which is what lets an update reindex only the files that changed
 * between two commits instead of rebuilding from scratch. Its in-memory shape is:
 *
 *   postings:     Map<trigram, Set<path>>   // for candidate lookup
 *   fileTrigrams: Map<path, string[]>       // a file's trigrams, for removal
 *
 * Keeping each file's trigram list lets us drop a file from every posting set
 * without re-reading its (now-gone) old content.
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
 * @property {Map<string, Set<string>>} postings      trigram -> set of paths
 * @property {Map<string, string[]>}    fileTrigrams  path -> its distinct trigrams
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

/** A new, empty index. */
export function createIndex() {
  return { postings: new Map(), fileTrigrams: new Map() };
}

/**
 * Add or replace a single file in the index. Idempotent: re-indexing a path
 * first drops its previous trigrams, so this doubles as the "modified" case.
 *
 * @param {ContentIndex} index
 * @param {string} path
 * @param {string} text
 */
export function indexFile(index, path, text) {
  if (typeof path !== 'string') return;
  if (index.fileTrigrams.has(path)) removeFile(index, path);
  const list = [...extractTrigrams(text || '')];
  index.fileTrigrams.set(path, list);
  for (const gram of list) {
    let set = index.postings.get(gram);
    if (set === undefined) {
      set = new Set();
      index.postings.set(gram, set);
    }
    set.add(path);
  }
}

/**
 * Drop a single file from the index (every posting set it appears in, and its
 * trigram list). A no-op for a path that isn't indexed.
 *
 * @param {ContentIndex} index
 * @param {string} path
 */
export function removeFile(index, path) {
  const list = index.fileTrigrams.get(path);
  if (list === undefined) return;
  for (const gram of list) {
    const set = index.postings.get(gram);
    if (!set) continue;
    set.delete(path);
    if (set.size === 0) index.postings.delete(gram);
  }
  index.fileTrigrams.delete(path);
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
  const index = createIndex();
  for (const entry of entries || []) {
    if (!entry || typeof entry.path !== 'string') continue;
    indexFile(index, entry.path, entry.text || '');
  }
  return index;
}

/** Every path currently in the index (indexing order not guaranteed). */
export function indexedPaths(index) {
  return index && index.fileTrigrams ? [...index.fileTrigrams.keys()] : [];
}

/**
 * Candidate paths that *may* contain the literal `query`, found by intersecting
 * the posting sets of the query's trigrams (walking the smallest set and probing
 * the rest, so the work scales with the rarest trigram). A candidate is not a
 * guaranteed match — the caller scans it to confirm.
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
  if (!index || !index.postings) return [];
  const grams = queryTrigrams(query);
  if (grams.length === 0) return indexedPaths(index);

  const sets = [];
  for (const gram of grams) {
    const set = index.postings.get(gram);
    if (!set || set.size === 0) return []; // a needed trigram is missing
    sets.push(set);
  }
  sets.sort((a, b) => a.size - b.size);

  const [smallest, ...rest] = sets;
  const out = [];
  for (const path of smallest) {
    let inAll = true;
    for (const set of rest) {
      if (!set.has(path)) {
        inAll = false;
        break;
      }
    }
    if (inAll) out.push(path);
  }
  return out;
}

/**
 * Flatten an index into a plain, JSON/structured-clone-friendly object for
 * persistence. Files are numbered so posting lists can reference small integer
 * ids instead of repeating path strings (compact, and stable to reload).
 *
 * @param {ContentIndex} index
 * @returns {{version: number, paths: string[], trigrams: Record<string, number[]>}}
 */
export function serializeIndex(index) {
  const paths = indexedPaths(index);
  const idOf = new Map(paths.map((path, i) => [path, i]));
  const trigrams = Object.create(null);
  if (index && index.postings) {
    for (const [gram, set] of index.postings) {
      const ids = [];
      for (const path of set) {
        const id = idOf.get(path);
        if (id !== undefined) ids.push(id);
      }
      ids.sort((a, b) => a - b);
      trigrams[gram] = ids;
    }
  }
  return { version: INDEX_FORMAT_VERSION, paths, trigrams };
}

/**
 * Rebuild an index from its serialized form, or `null` when the payload is
 * missing/corrupt or from an incompatible version (so the caller rebuilds). The
 * per-file trigram lists are reconstructed by inverting the posting lists.
 *
 * @param {*} obj
 * @returns {ContentIndex|null}
 */
export function deserializeIndex(obj) {
  if (!obj || obj.version !== INDEX_FORMAT_VERSION) return null;
  if (!Array.isArray(obj.paths) || !obj.trigrams || typeof obj.trigrams !== 'object') return null;

  const index = createIndex();
  // Seed every path so an empty file (no trigrams) still counts as indexed.
  for (const path of obj.paths) index.fileTrigrams.set(path, []);

  for (const gram of Object.keys(obj.trigrams)) {
    const ids = obj.trigrams[gram];
    if (!Array.isArray(ids)) continue;
    const set = new Set();
    for (const id of ids) {
      const path = obj.paths[id];
      if (path === undefined) continue;
      set.add(path);
      const list = index.fileTrigrams.get(path);
      if (list) list.push(gram);
    }
    if (set.size > 0) index.postings.set(gram, set);
  }
  return index;
}
