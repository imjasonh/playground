const CACHE = 'queens-v1';
const PREFIX = 'queens-';
const SHELL = [
  './',
  'index.html',
  'styles.css',
  'favicon.svg',
  'src/app.js',
  'src/game.js',
  'src/puzzle.js',
  'src/worker.js',
];

self.addEventListener('install', (event) => {
  event.waitUntil(
    caches.open(CACHE).then((cache) => cache.addAll(SHELL))
      .then(() => self.skipWaiting()));
});

self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches.keys()
      .then((keys) => Promise.all(
        keys.filter((key) => key.startsWith(PREFIX) && key !== CACHE)
          .map((key) => caches.delete(key))))
      .then(() => self.clients.claim()));
});

// Serve from the cache and refresh the entry in the background, so a visit
// with a connection updates the app for the next load. Shared links carry the
// puzzle in the query string, so lookups ignore it.
self.addEventListener('fetch', (event) => {
  const {request} = event;
  if (request.method !== 'GET' ||
      new URL(request.url).origin !== self.location.origin) {
    return;
  }
  event.respondWith(respond(request));
});

async function respond(request) {
  const cache = await caches.open(CACHE);
  const cached = await cache.match(request, {ignoreSearch: true});
  const refresh = fetch(request).then((response) => {
    if (response.ok) {
      cache.put(new URL(request.url).pathname, response.clone());
    }
    return response;
  });
  if (cached) {
    refresh.catch(() => {});
    return cached;
  }
  try {
    return await refresh;
  } catch (error) {
    if (request.mode === 'navigate') {
      const shell = await cache.match('index.html');
      if (shell) {
        return shell;
      }
    }
    throw error;
  }
}
