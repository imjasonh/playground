import { createIndexStore } from '../src/contentIndexStore.js';

/**
 * A tiny in-memory fake of the slice of IndexedDB the store uses (open +
 * upgrade, a single keyPath object store, get/put/delete, and transaction
 * completion). It is intentionally minimal: enough to exercise the store's
 * keying (one record per repoId) and oid-validated reuse without a real browser.
 */
function fakeIndexedDB() {
  const databases = new Map(); // name -> { version, stores: Map<storeName, Map> }

  function makeRequest() {
    return { onsuccess: null, onerror: null, onupgradeneeded: null, onblocked: null, result: undefined, error: null };
  }

  function makeObjectStore(map, keyPath) {
    const ops = [];
    const store = {
      keyPath,
      _ops: ops,
      get(key) {
        const req = makeRequest();
        ops.push(() => {
          req.result = map.has(key) ? structuredClone(map.get(key)) : undefined;
          req.onsuccess && req.onsuccess();
        });
        return req;
      },
      put(value) {
        const req = makeRequest();
        ops.push(() => {
          map.set(value[keyPath], structuredClone(value));
          req.onsuccess && req.onsuccess();
        });
        return req;
      },
      delete(key) {
        const req = makeRequest();
        ops.push(() => {
          map.delete(key);
          req.onsuccess && req.onsuccess();
        });
        return req;
      },
    };
    return store;
  }

  return {
    open(name, version) {
      const req = makeRequest();
      queueMicrotask(() => {
        let db = databases.get(name);
        const isNew = !db || db.version < version;
        if (!db) {
          db = { version, stores: new Map() };
          databases.set(name, db);
        }
        const handle = {
          objectStoreNames: {
            contains: (n) => db.stores.has(n),
          },
          createObjectStore: (n, opts) => {
            db.stores.set(n, new Map());
            return { keyPath: opts.keyPath };
          },
          transaction: (storeName) => {
            const map = db.stores.get(storeName);
            const os = makeObjectStore(map, 'repoId');
            const tx = { oncomplete: null, onerror: null, onabort: null, error: null, objectStore: () => os, abort() {} };
            queueMicrotask(() => {
              for (const op of os._ops) op();
              tx.oncomplete && tx.oncomplete();
            });
            return tx;
          },
        };
        req.result = handle;
        if (isNew) {
          db.version = version;
          req.onupgradeneeded && req.onupgradeneeded();
        }
        req.onsuccess && req.onsuccess();
      });
      return req;
    },
  };
}

describe('createIndexStore — no IndexedDB available', () => {
  const store = createIndexStore({ indexedDB: null });

  test('degrades to a no-op store', async () => {
    expect(store.available).toBe(false);
    expect(await store.load('r', '1')).toBeNull();
    expect(await store.save('r', '1', { a: 1 })).toBe(false);
    expect(await store.remove('r')).toBe(false);
  });
});

describe('createIndexStore — with a fake IndexedDB', () => {
  test('saves and loads a record for a matching oid', async () => {
    const store = createIndexStore({ indexedDB: fakeIndexedDB() });
    expect(store.available).toBe(true);
    expect(await store.save('repo', 'oid-1', { paths: ['a'] })).toBe(true);
    expect(await store.load('repo', 'oid-1')).toEqual({ paths: ['a'] });
  });

  test('returns null when the oid no longer matches (stale index)', async () => {
    const store = createIndexStore({ indexedDB: fakeIndexedDB() });
    await store.save('repo', 'oid-1', { paths: ['a'] });
    expect(await store.load('repo', 'oid-2')).toBeNull();
  });

  test('keeps one record per repo — a new save overwrites the old', async () => {
    const idb = fakeIndexedDB();
    const store = createIndexStore({ indexedDB: idb });
    await store.save('repo', 'oid-1', { v: 1 });
    await store.save('repo', 'oid-2', { v: 2 });
    expect(await store.load('repo', 'oid-1')).toBeNull(); // superseded
    expect(await store.load('repo', 'oid-2')).toEqual({ v: 2 });
  });

  test('remove deletes the record', async () => {
    const store = createIndexStore({ indexedDB: fakeIndexedDB() });
    await store.save('repo', 'oid-1', { v: 1 });
    expect(await store.remove('repo')).toBe(true);
    expect(await store.load('repo', 'oid-1')).toBeNull();
  });

  test('missing repoId is a no-op', async () => {
    const store = createIndexStore({ indexedDB: fakeIndexedDB() });
    expect(await store.load('', '1')).toBeNull();
    expect(await store.save('', '1', {})).toBe(false);
  });
});
