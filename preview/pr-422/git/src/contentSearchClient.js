/**
 * Drives a content (grep) search backed by a reusable trigram index.
 *
 * The old flow read and scanned *every* file on every keystroke. Now the client
 * builds a trigram index once per repository content state (see contentIndex.js),
 * persists it to IndexedDB (contentIndexStore.js), and reuses it across
 * keystrokes, reopens, and reloads. A literal query is answered by intersecting
 * the query's trigrams to a small set of *candidate* files; only those are read
 * and scanned to confirm real matches and collect line/column info. Building is
 * the one-time cost; typing is cheap.
 *
 * Building reads all files with bounded concurrency (a huge repo doesn't open
 * thousands of IndexedDB reads at once) and skips binaries/oversize files so the
 * index only holds searchable text. Scanning candidates keeps the same
 * streaming, worker-offloaded model as before: the main thread only does I/O and
 * the CPU-heavy decode+scan happens in `contentSearchWorker.js` (with a
 * synchronous fallback when Workers are unavailable or fail). Results stream back
 * per file via `onResult`, are capped so a pathological query can't blow up
 * memory/DOM, and a new search (or an explicit signal) supersedes the previous.
 *
 * Regex queries and queries shorter than a trigram can't be trigram-narrowed, so
 * they scan every indexed (text) file — still off the main thread, and still
 * skipping binaries, just without candidate pruning.
 *
 * @typedef {Object} FileResult
 * @property {string} path
 * @property {import('./contentSearch.js').LineMatch[]} matches
 *
 * @typedef {Object} SearchSummary
 * @property {number} files       files with at least one match
 * @property {number} matches     total matching lines emitted
 * @property {number} scanned     files read+scanned (excludes skipped binaries)
 * @property {boolean} truncated  stopped early because the result cap was hit
 * @property {boolean} cancelled  superseded by a newer search or aborted
 * @property {string} [error]     a bad regex message (nothing was scanned)
 */
import { buildPattern, searchContent } from './contentSearch.js';
import {
  buildTrigramIndex,
  candidatePaths,
  indexedPaths,
  indexFile,
  removeFile,
  serializeIndex,
  deserializeIndex,
} from './contentIndex.js';
import { createIndexStore } from './contentIndexStore.js';
import { isBinaryExtension, looksBinary } from './language.js';

const WORKER_URL = new URL('./contentSearchWorker.js', import.meta.url);
const decoder = new TextDecoder('utf-8', { fatal: false });
const WORKER_FAILED = Symbol('worker-failed');

const DEFAULTS = {
  concurrency: 8,
  maxFileBytes: 2_000_000, // skip very large files (likely generated/minified)
  maxMatchesPerFile: 200,
  maxTotalMatches: 1000, // hard cap across the whole search
  maxCachedIndexes: 3, // in-memory indexes kept hot (e.g. toggling branches)
};

/** In-memory cache key for a repo at a specific content state (commit oid). */
function cacheKey(repoId, oid) {
  return `${repoId}\u0000${oid == null ? '' : oid}`;
}

/**
 * @param {{
 *   createWorker?: () => Worker,
 *   useWorker?: boolean,
 *   concurrency?: number,
 *   maxFileBytes?: number,
 *   maxMatchesPerFile?: number,
 *   maxTotalMatches?: number,
 *   maxCachedIndexes?: number,
 *   store?: object,          // injectable index persistence (tests)
 *   indexedDB?: IDBFactory,  // injectable IndexedDB factory (tests)
 * }} [options]
 */
export function createContentSearchClient(options = {}) {
  const cfg = { ...DEFAULTS, ...options };
  const store = options.store || createIndexStore({ indexedDB: options.indexedDB });

  let worker = null;
  let disposed = false;
  let searchSeq = 0; // identifies the active search; a new one supersedes
  let reqSeq = 0; // per-file request id (worker correlation)
  const pending = new Map(); // reqId -> resolve

  // Built indexes kept hot. Persisted (repoId+oid) indexes live in `indexCache`
  // as an insertion-ordered LRU; keyless callers (no repoId) get an ephemeral
  // index keyed by the file-list array identity so repeated searches reuse it.
  const indexCache = new Map(); // cacheKey -> ContentIndex
  const ephemeral = new WeakMap(); // files[] -> ContentIndex
  const builds = new Map(); // dedupe concurrent builds: key -> Promise

  function startWorker() {
    if (options.useWorker === false) return;
    const make = options.createWorker
      ? options.createWorker
      : typeof Worker !== 'undefined'
        ? () => new Worker(WORKER_URL, { type: 'module' })
        : null;
    if (!make) return;
    try {
      worker = make();
      worker.onmessage = onMessage;
      worker.onerror = onWorkerFailure;
      worker.onmessageerror = onWorkerFailure;
    } catch {
      // Don't leak a worker that was created before a later step threw.
      if (worker) {
        try {
          worker.terminate();
        } catch {
          /* already gone */
        }
      }
      worker = null;
    }
  }

  function onMessage(event) {
    const msg = event.data || {};
    if (msg.type !== 'matches') return;
    const resolve = pending.get(msg.reqId);
    if (!resolve) return;
    pending.delete(msg.reqId);
    resolve(msg.matches);
  }

  function onWorkerFailure() {
    if (!worker) return;
    try {
      worker.terminate();
    } catch {
      /* already gone */
    }
    worker = null;
    // Unblock everything in flight; the awaiting lane recomputes synchronously.
    for (const resolve of pending.values()) resolve(WORKER_FAILED);
    pending.clear();
  }

  function matchInWorker(searchId, path, bytes, limits) {
    const reqId = (reqSeq += 1);
    return new Promise((resolve) => {
      pending.set(reqId, resolve);
      // Structured clone copies `bytes` (no transfer/detach), so the caller's
      // buffer stays valid for the synchronous fallback if the worker dies.
      worker.postMessage({ type: 'file', id: searchId, reqId, path, bytes, limits });
    });
  }

  /* ---------------------------------------------------------------- */
  /* Index build / cache                                              */
  /* ---------------------------------------------------------------- */

  function cacheIndex(key, index) {
    indexCache.delete(key); // re-insert to move to the MRU end
    indexCache.set(key, index);
    while (indexCache.size > cfg.maxCachedIndexes) {
      const oldest = indexCache.keys().next().value;
      indexCache.delete(oldest);
    }
  }

  /**
   * Read a single file and decode it to text, or null when it isn't indexable
   * searchable text (binary by extension/content, over the byte cap, or
   * unreadable). Shared by the full build and the incremental update.
   */
  async function readIndexableText(path, readFile) {
    if (isBinaryExtension(path)) return null;
    let bytes;
    try {
      bytes = await readFile(path);
    } catch {
      return null; // unreadable — treat as absent
    }
    if (!bytes || bytes.length > cfg.maxFileBytes || looksBinary(bytes)) return null;
    return decoder.decode(bytes);
  }

  /**
   * Read + decode every text file once and build a trigram index. Returns null
   * if the client is disposed before it finishes (so a stale/partial index is
   * never cached). Ignores per-search aborts on purpose: the build is a
   * repo-level, one-time cost that outlives the keystroke that triggered it.
   */
  async function buildIndex(files, readFile, onStatus) {
    const list = files || [];
    const entries = new Array(list.length); // keep original order (id stability)
    let processed = 0;
    let cursor = 0;

    async function lane() {
      while (!disposed) {
        const i = cursor;
        if (i >= list.length) return;
        cursor += 1;
        const path = list[i];
        const text = await readIndexableText(path, readFile);
        if (text != null) entries[i] = { path, text };
        processed += 1;
        if (onStatus) onStatus({ phase: 'building', processed, total: list.length });
      }
    }

    const laneCount = Math.max(1, Math.min(cfg.concurrency, list.length || 1));
    await Promise.all(Array.from({ length: laneCount }, lane));
    if (disposed) return null;
    return buildTrigramIndex(entries.filter(Boolean));
  }

  /**
   * Ensure an index exists for the given corpus, building it at most once and
   * reusing it (from memory, then from IndexedDB) thereafter. Concurrent callers
   * share a single in-flight build.
   *
   * @returns {Promise<import('./contentIndex.js').ContentIndex|null>}
   */
  function ensureIndex({ files, readFile, repoId, oid, onStatus }) {
    const persistKey = repoId ? cacheKey(repoId, oid) : null;

    if (persistKey && indexCache.has(persistKey)) {
      const hit = indexCache.get(persistKey);
      cacheIndex(persistKey, hit); // mark MRU
      return Promise.resolve(hit);
    }
    if (!persistKey && files && ephemeral.has(files)) {
      return Promise.resolve(ephemeral.get(files));
    }

    const dedupeKey = persistKey || files;
    if (dedupeKey && builds.has(dedupeKey)) return builds.get(dedupeKey);

    const work = (async () => {
      // Reuse a persisted index when its oid still matches the repo's state.
      if (persistKey) {
        const raw = await store.load(repoId, oid).catch(() => null);
        const restored = raw ? deserializeIndex(raw) : null;
        if (restored) {
          cacheIndex(persistKey, restored);
          return restored;
        }
      }

      if (onStatus) onStatus({ phase: 'building', processed: 0, total: (files || []).length });
      const index = await buildIndex(files, readFile, onStatus);
      if (!index) return null; // disposed mid-build

      if (persistKey) {
        cacheIndex(persistKey, index);
        // Best-effort persistence; failure just means we rebuild next session.
        store.save(repoId, oid, serializeIndex(index)).catch(() => {});
      } else if (files) {
        ephemeral.set(files, index);
      }
      return index;
    })();

    if (dedupeKey) {
      builds.set(dedupeKey, work);
      work.finally(() => builds.delete(dedupeKey)).catch(() => {});
    }
    return work;
  }

  /**
   * Build (or load) the index for a corpus without running a query — used to
   * warm the index when the search overlay opens so the first keystroke is fast.
   *
   * @returns {Promise<boolean>} whether an index is ready
   */
  async function prepareIndex(handlers = {}) {
    const index = await ensureIndex(handlers);
    return Boolean(index);
  }

  /** Whether an index for this repo state is already hot in memory. */
  function hasIndex(repoId, oid) {
    return Boolean(repoId) && indexCache.has(cacheKey(repoId, oid));
  }

  /**
   * Incrementally advance an existing index from `prevOid` to `oid` by applying
   * only the files that changed between those commits, instead of rebuilding.
   * A no-op that returns false when there is no base index to advance (the next
   * search then lazily builds a fresh one for `oid`).
   *
   * @param {{
   *   repoId: string,
   *   prevOid: string,
   *   oid: string,
   *   changes: Array<{path: string, status: 'added'|'removed'|'modified'}>,
   *   readFile: (path: string) => Promise<Uint8Array>,
   * }} args
   * @returns {Promise<boolean>} whether an index was updated
   */
  async function updateIndex({ repoId, prevOid, oid, changes, readFile }) {
    if (!repoId || prevOid === oid) return false;
    const prevKey = cacheKey(repoId, prevOid);

    // Find the base index (at prevOid): memory first, then persistence.
    let index = indexCache.get(prevKey);
    if (!index) {
      const raw = await store.load(repoId, prevOid).catch(() => null);
      index = raw ? deserializeIndex(raw) : null;
    }
    if (!index) return false; // nothing to advance — leave the lazy rebuild path

    for (const change of changes || []) {
      if (!change || typeof change.path !== 'string') continue;
      if (change.status === 'removed') {
        removeFile(index, change.path);
        continue;
      }
      // added / modified: re-read the new content and (re)index it, or drop it if
      // it's no longer indexable text (deleted, became binary, or grew too big).
      const text = await readIndexableText(change.path, readFile);
      if (text == null) removeFile(index, change.path);
      else indexFile(index, change.path, text);
    }

    // Re-key to the new content state and re-persist the advanced index.
    indexCache.delete(prevKey);
    cacheIndex(cacheKey(repoId, oid), index);
    store.save(repoId, oid, serializeIndex(index)).catch(() => {});
    return true;
  }

  /**
   * Forget a repository's index — both the in-memory copies and the persisted
   * record — so clearing a repo from browser storage doesn't leave its index
   * behind.
   *
   * @param {string} repoId
   */
  async function removeIndex(repoId) {
    if (!repoId) return;
    const prefix = `${repoId}\u0000`;
    for (const key of [...indexCache.keys()]) {
      if (key.startsWith(prefix)) indexCache.delete(key);
    }
    await store.remove(repoId).catch(() => {});
  }

  /* ---------------------------------------------------------------- */
  /* Search                                                           */
  /* ---------------------------------------------------------------- */

  /**
   * Run a content search.
   *
   * @param {string[]} files
   * @param {string} query
   * @param {{regex?: boolean, caseSensitive?: boolean}} queryOpts
   * @param {{
   *   readFile: (path: string) => Promise<Uint8Array>,
   *   onResult?: (r: FileResult) => void,
   *   onProgress?: (processed: number, total: number) => void,
   *   onStatus?: (info: {phase: string, processed: number, total: number}) => void,
   *   signal?: { aborted: boolean },
   *   repoId?: string,   // enables persistence + cross-session reuse
   *   oid?: string,      // repo content state (index invalidates when it moves)
   * }} handlers
   * @returns {Promise<SearchSummary>}
   */
  async function search(files, query, queryOpts = {}, handlers = {}) {
    const { readFile, onResult, onProgress, onStatus, signal, repoId, oid } = handlers;
    const { re, error } = buildPattern(query, queryOpts);
    const empty = { files: 0, matches: 0, scanned: 0, truncated: false, cancelled: false };
    // Validate the pattern before touching any file, so a bad regex reads nothing.
    if (error) return { ...empty, error };
    if (!re) return empty;

    const searchId = (searchSeq += 1);
    const superseded = () => searchId !== searchSeq;
    // A disposed client is deliberately *not* treated as aborted here: dispose
    // kills the worker but its in-flight lanes must still finish synchronously
    // (that's the "degrade, don't hang" contract), so only a newer search or an
    // explicit signal cancels a scan.
    const aborted = () => (signal && signal.aborted) || superseded();

    // Build once, reuse forever: the index is what turns per-keystroke full scans
    // into a candidate lookup.
    const index = await ensureIndex({ files, readFile, repoId, oid, onStatus });
    if (aborted()) return { ...empty, cancelled: true };

    // Pick the files to scan. A trigram-narrowable literal query hits only its
    // candidates; regex / too-short queries (and a missing index) fall back to
    // scanning the whole (text) corpus.
    let list;
    if (!index) list = (files || []).filter((path) => !isBinaryExtension(path));
    else if (queryOpts.regex) list = indexedPaths(index);
    else list = candidatePaths(index, query);

    const limits = { maxMatches: cfg.maxMatchesPerFile };
    if (worker) worker.postMessage({ type: 'begin', id: searchId, query, options: queryOpts });

    let fileHits = 0;
    let totalHits = 0;
    let scanned = 0; // files actually decoded+scanned (excludes skips)
    let processed = 0; // files considered, including skips — drives progress
    let cursor = 0;
    let stopped = false; // hit the total cap
    const scanAborted = () => stopped || aborted();

    async function lane() {
      while (!scanAborted()) {
        const i = cursor;
        if (i >= list.length) return;
        cursor += 1;
        const path = list[i];
        // `finally` guarantees every file (matched, scanned, or skipped) advances
        // progress, so the status can always reach total/total.
        try {
          if (isBinaryExtension(path)) continue; // cheap guard for the fallback path

          let bytes;
          try {
            bytes = await readFile(path);
          } catch {
            continue; // unreadable file — skip, keep going
          }
          if (scanAborted()) return;
          if (!bytes || bytes.length > cfg.maxFileBytes || looksBinary(bytes)) continue;

          let matches;
          if (worker) {
            matches = await matchInWorker(searchId, path, bytes, limits);
            if (matches === WORKER_FAILED) matches = searchContent(decoder.decode(bytes), re, limits);
          } else {
            matches = searchContent(decoder.decode(bytes), re, limits);
          }
          if (scanAborted()) return;

          scanned += 1;
          if (matches && matches.length) {
            fileHits += 1;
            totalHits += matches.length;
            if (onResult) onResult({ path, matches });
            if (totalHits >= cfg.maxTotalMatches) stopped = true;
          }
        } finally {
          processed += 1;
          if (onProgress) onProgress(processed, list.length);
        }
      }
    }

    const laneCount = Math.max(1, Math.min(cfg.concurrency, list.length));
    await Promise.all(Array.from({ length: laneCount }, lane));

    return {
      files: fileHits,
      matches: totalHits,
      scanned,
      truncated: stopped,
      cancelled: Boolean((signal && signal.aborted) || superseded()),
    };
  }

  function dispose() {
    disposed = true;
    if (worker) {
      try {
        worker.terminate();
      } catch {
        /* already gone */
      }
      worker = null;
    }
    // Unblock any awaiting lane (it will fall back to a synchronous scan) so a
    // dispose mid-search can't leave a search() promise pending forever.
    for (const resolve of pending.values()) resolve(WORKER_FAILED);
    pending.clear();
  }

  startWorker();

  return {
    search,
    prepareIndex,
    hasIndex,
    updateIndex,
    removeIndex,
    dispose,
    get usingWorker() {
      return Boolean(worker);
    },
  };
}
