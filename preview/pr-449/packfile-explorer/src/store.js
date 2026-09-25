// Persist fetched packs in IndexedDB so a repo can be re-explored offline.
//
// The original ask was "index it in WebSQL"; WebSQL has been removed from
// every current browser, so this uses IndexedDB — the supported local
// structured store — keyed by the repository's base URL. The raw pack is small
// for a shallow clone, so it's stored verbatim and re-parsed on load rather
// than persisting the resolved object graph.

const DB_NAME = "packfile-explorer";
const STORE = "packs";
const VERSION = 1;

function openDb() {
  return new Promise((resolve, reject) => {
    const req = indexedDB.open(DB_NAME, VERSION);
    req.onupgradeneeded = () => {
      const db = req.result;
      if (!db.objectStoreNames.contains(STORE)) {
        db.createObjectStore(STORE, { keyPath: "key" });
      }
    };
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(req.error);
  });
}

function tx(db, mode, fn) {
  return new Promise((resolve, reject) => {
    const t = db.transaction(STORE, mode);
    const store = t.objectStore(STORE);
    const result = fn(store);
    t.oncomplete = () => resolve(result && result.value !== undefined ? result.value : result);
    t.onerror = () => reject(t.error);
    t.onabort = () => reject(t.error);
  });
}

/** Save a fetched pack record. `pack` is a Uint8Array. */
export async function saveRepo(record) {
  const db = await openDb();
  const value = {
    key: record.base,
    base: record.base,
    savedAt: Date.now(),
    refs: record.refs,
    head: record.head,
    wants: record.wants,
    progress: record.progress || "",
    pack: record.pack.buffer.slice(
      record.pack.byteOffset,
      record.pack.byteOffset + record.pack.byteLength,
    ),
  };
  await tx(db, "readwrite", (store) => store.put(value));
  db.close();
}

/** List saved repos (metadata only, newest first). */
export async function listRepos() {
  const db = await openDb();
  const rows = await new Promise((resolve, reject) => {
    const out = [];
    const req = db.transaction(STORE, "readonly").objectStore(STORE).openCursor();
    req.onsuccess = () => {
      const cursor = req.result;
      if (!cursor) {
        resolve(out);
        return;
      }
      const v = cursor.value;
      out.push({
        key: v.key,
        base: v.base,
        savedAt: v.savedAt,
        head: v.head,
        refCount: v.refs ? v.refs.length : 0,
        packBytes: v.pack ? v.pack.byteLength : 0,
      });
      cursor.continue();
    };
    req.onerror = () => reject(req.error);
  });
  db.close();
  rows.sort((a, b) => b.savedAt - a.savedAt);
  return rows;
}

/** Load a saved repo, returning `{ ...meta, pack: Uint8Array }` or null. */
export async function loadRepo(key) {
  const db = await openDb();
  const value = await new Promise((resolve, reject) => {
    const req = db.transaction(STORE, "readonly").objectStore(STORE).get(key);
    req.onsuccess = () => resolve(req.result || null);
    req.onerror = () => reject(req.error);
  });
  db.close();
  if (!value) return null;
  return { ...value, pack: new Uint8Array(value.pack) };
}

/** Delete a saved repo. */
export async function deleteRepo(key) {
  const db = await openDb();
  await tx(db, "readwrite", (store) => store.delete(key));
  db.close();
}
