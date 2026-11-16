import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {describe, test} from 'node:test';
import vm from 'node:vm';

const ROOT = new URL('../', import.meta.url);

async function loadWorker({network}) {
  const source = await readFile(new URL('sw.js', ROOT), 'utf8');
  const handlers = {};
  const stores = new Map();
  const bucket = (name) => {
    if (!stores.has(name)) {
      stores.set(name, new Map());
    }
    return stores.get(name);
  };
  const keyOf = (request) => new URL(
    typeof request === 'string' ? request : request.url,
    'https://example.com/zip/').pathname;
  const caches = {
    open: async (name) => {
      const store = bucket(name);
      return {
        addAll: async (urls) => {
          for (const url of urls) {
            store.set(keyOf(url), 'precached');
          }
        },
        match: async (request) => store.get(keyOf(request)),
        put: async (request, response) => {
          store.set(keyOf(request), response);
        },
      };
    },
    keys: async () => [...stores.keys()],
    delete: async (name) => stores.delete(name),
  };
  const self = {
    location: new URL('https://example.com/zip/sw.js'),
    addEventListener: (type, handler) => {
      handlers[type] = handler;
    },
    skipWaiting: async () => {},
    clients: {claim: async () => {}},
  };
  vm.runInNewContext(source, {
    self, caches, URL, fetch: network, Promise,
  });
  return {handlers, stores, bucket};
}

function dispatch(handler, extra = {}) {
  const event = {
    ...extra,
    waitUntil: (promise) => {
      event.waited = promise;
    },
    respondWith: (promise) => {
      event.responded = promise;
    },
  };
  handler(event);
  return event;
}

function request(url, init = {}) {
  return {url, method: 'GET', mode: 'cors', ...init};
}

describe('service worker', () => {
  test('precaches every module the app imports', async () => {
    const {handlers, stores} = await loadWorker({network: async () => {
      throw new Error('offline');
    }});
    await dispatch(handlers.install).waited;
    const cached = [...stores.get('zip-v1').keys()];
    for (const name of ['app', 'game', 'zip', 'worker']) {
      assert.ok(cached.includes(`/zip/src/${name}.js`), name);
    }
    assert.ok(cached.includes('/zip/'));
    assert.ok(cached.includes('/zip/index.html'));
  });

  test('drops older caches of its own app on activate', async () => {
    const {handlers, stores, bucket} = await loadWorker({
      network: async () => {},
    });
    bucket('zip-v0');
    bucket('zip-v1');
    bucket('other');
    await dispatch(handlers.activate).waited;
    assert.deepEqual([...stores.keys()].sort(), ['other', 'zip-v1']);
  });

  test('serves a cached file while offline, ignoring the query string',
    async () => {
      const {handlers} = await loadWorker({network: async () => {
        throw new Error('offline');
      }});
      await dispatch(handlers.install).waited;
      const event = dispatch(handlers.fetch, {
        request: request('https://example.com/zip/?game=zip&seed=ab'),
      });
      assert.equal(await event.responded, 'precached');
    });

  test('refreshes the cache from the network', async () => {
    const fresh = {ok: true, clone: () => 'clone'};
    const {handlers, stores} = await loadWorker({network: async () => fresh});
    await dispatch(handlers.install).waited;
    const event = dispatch(handlers.fetch, {
      request: request('https://example.com/zip/styles.css'),
    });
    assert.equal(await event.responded, 'precached');
    await new Promise((resolve) => setImmediate(resolve));
    assert.equal(stores.get('zip-v1').get('/zip/styles.css'), 'clone');
  });

  test('falls back to the app page for an uncached navigation offline',
    async () => {
      const {handlers} = await loadWorker({network: async () => {
        throw new Error('offline');
      }});
      await dispatch(handlers.install).waited;
      const event = dispatch(handlers.fetch, {
        request: request('https://example.com/zip/unknown', {
          mode: 'navigate',
        }),
      });
      assert.equal(await event.responded, 'precached');
    });

  test('ignores other origins and non-GET requests', async () => {
    const {handlers} = await loadWorker({network: async () => {}});
    for (const req of [
      request('https://other.example/x.js'),
      request('https://example.com/zip/', {method: 'POST'}),
    ]) {
      assert.equal(dispatch(handlers.fetch, {request: req}).responded,
        undefined);
    }
  });
});
