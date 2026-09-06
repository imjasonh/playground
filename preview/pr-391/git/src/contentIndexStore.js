/**
 * IndexedDB persistence for the content-search trigram index (contentIndex.js).
 *
 * Building the index reads and decodes every text file in the repo, so it should
 * happen once per repository *content state* and be reused afterwards — across
 * reopens and page reloads, not just across keystrokes. This store keeps exactly
 * one serialized index per repository, tagged with the commit oid it was built
 * from: a `load` only returns it when the oid still matches, so new commits (or
 * switching to a ref with different content) transparently invalidate it, and a
 * fresh `save` overwrites the previous one (bounded storage — no accumulation of
 * stale indexes).
 *
 * Everything is best-effort: a browser without IndexedDB, a blocked/again-failing
 * open, or any transaction error degrades to "no persistence" rather than
 * throwing, so search still works (it just rebuilds the in-memory index each
 * session). The `indexedDB` factory is injectable so the logic is testable
 * against a fake without a real browser.
 */

const DB_NAME = 'git-content-index';
const STORE_NAME = 'indexes';
const DB_VERSION = 1;

/** A no-op store used when IndexedDB is unavailable; keeps callers branch-free. */
function createNullStore() {
  return {
    available: false,
    async load() {
      return null;
    },
    async save() {
      return false;
    },
    async remove() {
      return false;
    },
  };
}

/**
 * @param {{ indexedDB?: IDBFactory }} [options]
 * @returns {{
 *   available: boolean,
 *   load: (repoId: string, oid: string) => Promise<*|null>,
 *   save: (repoId: string, oid: string, data: *) => Promise<boolean>,
 *   remove: (repoId: string) => Promise<boolean>,
 * }}
 */
export function createIndexStore(options = {}) {
  const idb =
    options.indexedDB !== undefined
      ? options.indexedDB
      : typeof indexedDB !== 'undefined'
        ? indexedDB
        : null;
  if (!idb) return createNullStore();

  let dbPromise = null;

  function openDB() {
    if (dbPromise) return dbPromise;
    dbPromise = new Promise((resolve, reject) => {
      let req;
      try {
        req = idb.open(DB_NAME, DB_VERSION);
      } catch (err) {
        reject(err);
        return;
      }
      req.onupgradeneeded = () => {
        const db = req.result;
        if (!db.objectStoreNames.contains(STORE_NAME)) {
          // Keyed by repoId: one record per repo, so a rebuild for a new oid
          // simply overwrites the old one.
          db.createObjectStore(STORE_NAME, { keyPath: 'repoId' });
        }
      };
      req.onsuccess = () => resolve(req.result);
      req.onerror = () => reject(req.error);
      req.onblocked = () => reject(new Error('IndexedDB open blocked'));
    }).catch((err) => {
      // Reset so a later call can retry a transient failure.
      dbPromise = null;
      throw err;
    });
    return dbPromise;
  }

  /** Run `fn(store)` in a transaction, resolving with `result` on commit. */
  function withStore(mode, fn) {
    return openDB().then(
      (db) =>
        new Promise((resolve, reject) => {
          let tx;
          try {
            tx = db.transaction(STORE_NAME, mode);
          } catch (err) {
            reject(err);
            return;
          }
          const store = tx.objectStore(STORE_NAME);
          let result;
          tx.oncomplete = () => resolve(result);
          tx.onerror = () => reject(tx.error);
          tx.onabort = () => reject(tx.error || new Error('IndexedDB transaction aborted'));
          try {
            result = fn(store);
          } catch (err) {
            try {
              tx.abort();
            } catch {
              /* already aborting */
            }
            reject(err);
          }
        }),
    );
  }

  async function load(repoId, oid) {
    if (!repoId) return null;
    try {
      let record;
      await withStore('readonly', (store) => {
        const req = store.get(repoId);
        req.onsuccess = () => {
          record = req.result;
        };
      });
      if (!record || record.oid !== oid) return null;
      return record.data ?? null;
    } catch {
      return null;
    }
  }

  async function save(repoId, oid, data) {
    if (!repoId) return false;
    try {
      await withStore('readwrite', (store) => {
        store.put({ repoId, oid, data, savedAt: Date.now() });
      });
      return true;
    } catch {
      return false;
    }
  }

  async function remove(repoId) {
    if (!repoId) return false;
    try {
      await withStore('readwrite', (store) => {
        store.delete(repoId);
      });
      return true;
    } catch {
      return false;
    }
  }

  return { available: true, load, save, remove };
}

export { DB_NAME as INDEX_DB_NAME, STORE_NAME as INDEX_STORE_NAME };
