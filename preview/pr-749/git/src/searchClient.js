/**
 * Front-end for the fuzzy file search. It hides whether matching runs in a Web
 * Worker (the fast path on large repos — indexing and scanning stay off the main
 * thread) or synchronously on the main thread (the fallback when Workers are
 * unavailable or fail to spawn, e.g. older browsers or a CSP that blocks them).
 *
 * Both paths share the same pure logic (fuzzy.js), so results are identical; only
 * *where* the work happens differs. The async contract is the same either way:
 * {@link createSearchClient}().search returns a Promise.
 *
 * Concurrency model:
 *   - `setFiles` replaces the corpus and bumps an epoch. A result from an older
 *     epoch (a query that was in flight when the corpus changed) resolves to
 *     `null`, which callers treat as "ignore".
 *   - Each `search` is correlated to its worker reply by a unique id, so two
 *     callers (the palette and the tree filter) sharing one client never steal
 *     each other's results. "Latest keystroke wins" is the *caller's* job (a
 *     small token), keeping this layer a plain request/response correlator.
 */
import { buildIndex, fuzzyFilterIndex } from './fuzzy.js';

const WORKER_URL = new URL('./searchWorker.js', import.meta.url);

/**
 * @param {{
 *   createWorker?: () => Worker,   // injectable for tests
 *   useWorker?: boolean,           // force-disable the worker (defaults to true)
 * }} [options]
 */
export function createSearchClient(options = {}) {
  let files = [];
  let epoch = 0;
  // Lazily-built main-thread index, only used by the synchronous fallback so the
  // happy path never pays the indexing cost on the main thread.
  let syncIndex = null;
  let syncIndexEpoch = -1;
  let seq = 0;
  const pending = new Map(); // id -> { resolve, epoch, query, limit }
  let worker = null;

  function ensureSyncIndex() {
    if (!syncIndex || syncIndexEpoch !== epoch) {
      syncIndex = buildIndex(files);
      syncIndexEpoch = epoch;
    }
    return syncIndex;
  }

  function startWorker() {
    if (options.useWorker === false) return;
    // An injected factory wins outright (used by tests); otherwise only spawn a
    // worker where the platform actually provides one.
    const make = options.createWorker
      ? options.createWorker
      : typeof Worker !== 'undefined'
        ? () => new Worker(WORKER_URL, { type: 'module' })
        : null;
    if (!make) return;
    try {
      worker = make();
      worker.onmessage = onMessage;
      // A worker that throws at runtime (or fails its initial module fetch)
      // shouldn't break search: fall back to synchronous matching.
      worker.onerror = onWorkerFailure;
      worker.onmessageerror = onWorkerFailure;
      worker.postMessage({ type: 'setFiles', epoch, files });
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
    if (msg.type !== 'result') return;
    const entry = pending.get(msg.id);
    if (!entry) return;
    pending.delete(msg.id);
    // Drop a reply computed against a corpus we've since replaced.
    entry.resolve(msg.epoch === epoch ? msg.results : null);
  }

  function onWorkerFailure() {
    if (!worker) return;
    try {
      worker.terminate();
    } catch {
      /* already gone */
    }
    worker = null;
    // Resolve whatever was in flight from the synchronous index so callers that
    // are awaiting a reply aren't left hanging.
    const index = ensureSyncIndex();
    for (const entry of pending.values()) {
      entry.resolve(
        entry.epoch === epoch ? fuzzyFilterIndex(entry.query, index, { limit: entry.limit }) : null,
      );
    }
    pending.clear();
  }

  /** Replace the corpus searched against. Cheap on the main thread (no scan). */
  function setFiles(next) {
    files = Array.isArray(next) ? next : [];
    epoch += 1;
    syncIndex = null;
    if (worker) worker.postMessage({ type: 'setFiles', epoch, files });
  }

  /**
   * Rank `files` by `query`.
   *
   * @param {string} query
   * @param {{limit?: number}} [opts]
   * @returns {Promise<?{item:string, score:number, positions:number[], target:string}[]>}
   *   resolves to results, or `null` if the corpus changed before it completed
   */
  function search(query, opts = {}) {
    const limit = typeof opts.limit === 'number' ? opts.limit : undefined;
    if (worker) {
      const id = (seq += 1);
      return new Promise((resolve) => {
        // The entry's `epoch` (not the message) is what the result is later
        // checked against; the worker stamps its reply with its own epoch.
        pending.set(id, { resolve, epoch, query, limit });
        worker.postMessage({ type: 'query', id, query, limit });
      });
    }
    return Promise.resolve(fuzzyFilterIndex(query, ensureSyncIndex(), { limit }));
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
    // Resolve (don't drop) anything in flight so awaiters can't hang forever.
    for (const entry of pending.values()) entry.resolve(null);
    pending.clear();
  }

  startWorker();

  return {
    setFiles,
    search,
    dispose,
    /** True while the worker is the active backend (false once we've degraded). */
    get usingWorker() {
      return Boolean(worker);
    },
  };
}
