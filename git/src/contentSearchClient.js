/**
 * Drives a content (grep) search: walks the file list, reads each file's bytes
 * (the RepoSource lives on the main thread), and scans them — in a Web Worker
 * when available, synchronously otherwise. Results stream back per file via an
 * `onResult` callback so the UI fills in as the scan proceeds.
 *
 * The main thread only does I/O (reads) and skips binaries/oversize files; the
 * CPU-heavy decode+scan happens in the worker (`contentSearchWorker.js`), which
 * is the work the future-work note wanted off the main thread. Both paths share
 * the same pure logic (contentSearch.js), so results are identical.
 *
 * Reads run with bounded concurrency so a huge repo doesn't open thousands of
 * IndexedDB reads at once; results are capped so a pathological query can't blow
 * up memory/DOM. A new search (or an explicit signal) supersedes the previous.
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
import { isBinaryExtension, looksBinary } from './language.js';

const WORKER_URL = new URL('./contentSearchWorker.js', import.meta.url);
const decoder = new TextDecoder('utf-8', { fatal: false });
const WORKER_FAILED = Symbol('worker-failed');

const DEFAULTS = {
  concurrency: 8,
  maxFileBytes: 2_000_000, // skip very large files (likely generated/minified)
  maxMatchesPerFile: 200,
  maxTotalMatches: 1000, // hard cap across the whole search
};

/**
 * @param {{
 *   createWorker?: () => Worker,
 *   useWorker?: boolean,
 *   concurrency?: number,
 *   maxFileBytes?: number,
 *   maxMatchesPerFile?: number,
 *   maxTotalMatches?: number,
 * }} [options]
 */
export function createContentSearchClient(options = {}) {
  const cfg = { ...DEFAULTS, ...options };
  let worker = null;
  let searchSeq = 0; // identifies the active search; a new one supersedes
  let reqSeq = 0; // per-file request id (worker correlation)
  const pending = new Map(); // reqId -> resolve

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
   *   signal?: { aborted: boolean },
   * }} handlers
   * @returns {Promise<SearchSummary>}
   */
  async function search(files, query, queryOpts = {}, handlers = {}) {
    const { readFile, onResult, onProgress, signal } = handlers;
    const { re, error } = buildPattern(query, queryOpts);
    const empty = { files: 0, matches: 0, scanned: 0, truncated: false, cancelled: false };
    if (error) return { ...empty, error };
    if (!re) return empty;

    const searchId = (searchSeq += 1);
    const list = files || [];
    const limits = { maxMatches: cfg.maxMatchesPerFile };
    if (worker) worker.postMessage({ type: 'begin', id: searchId, query, options: queryOpts });

    let fileHits = 0;
    let totalHits = 0;
    let scanned = 0; // files actually decoded+scanned (excludes skips)
    let processed = 0; // files considered, including skips — drives progress
    let cursor = 0;
    let stopped = false; // hit the total cap
    const aborted = () => stopped || (signal && signal.aborted) || searchId !== searchSeq;

    async function lane() {
      while (!aborted()) {
        const i = cursor;
        if (i >= list.length) return;
        cursor += 1;
        const path = list[i];
        // `finally` guarantees every file (matched, scanned, or skipped) advances
        // progress, so the status can always reach total/total instead of stalling
        // below it when binaries/oversize files are skipped.
        try {
          if (isBinaryExtension(path)) continue; // skip without an I/O read

          let bytes;
          try {
            bytes = await readFile(path);
          } catch {
            continue; // unreadable file — skip, keep going
          }
          if (aborted()) return;
          if (!bytes || bytes.length > cfg.maxFileBytes || looksBinary(bytes)) continue;

          let matches;
          if (worker) {
            matches = await matchInWorker(searchId, path, bytes, limits);
            if (matches === WORKER_FAILED) matches = searchContent(decoder.decode(bytes), re, limits);
          } else {
            matches = searchContent(decoder.decode(bytes), re, limits);
          }
          if (aborted()) return;

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
      cancelled: Boolean((signal && signal.aborted) || searchId !== searchSeq),
    };
  }

  function dispose() {
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
    dispose,
    get usingWorker() {
      return Boolean(worker);
    },
  };
}
