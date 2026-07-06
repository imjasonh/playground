/*
 * Service worker for the Web Push demo.
 *
 * Responsibilities:
 *   - Receive the `push` event, decode the (already-decrypted-by-the-browser)
 *     payload, and show a system notification.
 *   - Relay the payload to any open demo tabs so the page can log it live.
 *   - Focus/open a tab when a notification is clicked.
 *   - Best-effort re-subscribe when the browser rotates the subscription
 *     (`pushsubscriptionchange`), using config the page stashed in Cache Storage.
 *
 * The push payload is whatever JSON the application server sent to `/notify`,
 * e.g. `{ "title": "...", "body": "...", "url": "...", "icon": "..." }`.
 */

const CONFIG_CACHE = "web-push-demo-config";
// Synthetic, never-fetched URL used purely as a Cache Storage key.
const CONFIG_KEY = "https://web-push-demo.local/config.json";

self.addEventListener("install", () => {
  // Activate this worker immediately instead of waiting for old tabs to close.
  self.skipWaiting();
});

self.addEventListener("activate", (event) => {
  // Take control of already-open clients so messaging works right away.
  event.waitUntil(self.clients.claim());
});

// The page sends `{ type: "config", apiBase, vapidPublicKey }` so the worker can
// re-subscribe on its own if the browser rotates the subscription later.
self.addEventListener("message", (event) => {
  const data = event.data || {};
  if (data.type === "config") {
    event.waitUntil(writeConfig({ apiBase: data.apiBase, vapidPublicKey: data.vapidPublicKey }));
  }
});

self.addEventListener("push", (event) => {
  const payload = parsePayload(event);
  const title = payload.title || "Web Push";
  const options = {
    body: payload.body || "",
    icon: payload.icon || "./icon.svg",
    badge: payload.badge || "./icon.svg",
    tag: payload.tag,
    data: { url: payload.url || "./", payload },
    timestamp: Date.now(),
  };

  event.waitUntil(
    (async () => {
      // Chrome requires a user-visible notification for every push when the
      // subscription used `userVisibleOnly: true`.
      let error = null;
      try {
        await self.registration.showNotification(title, options);
      } catch (err) {
        error = String(err);
      }
      // Report how many notifications the browser now has for this
      // registration. showNotification can resolve while the OS still shows
      // nothing (Do Not Disturb / Focus, or per-app notification settings), so
      // a non-zero count tells the page the push worked and the issue is an OS
      // display setting rather than the web app.
      let active = null;
      try {
        active = (await self.registration.getNotifications()).length;
      } catch (_e) {
        /* getNotifications may be unavailable; leave active null */
      }
      await broadcast({ type: "push", payload, at: Date.now(), shown: error === null, active, error });
    })(),
  );
});

self.addEventListener("notificationclick", (event) => {
  event.notification.close();
  const target = (event.notification.data && event.notification.data.url) || "./";
  event.waitUntil(
    (async () => {
      const all = await self.clients.matchAll({ type: "window", includeUncontrolled: true });
      for (const client of all) {
        // Focus an existing demo tab if one is open.
        if ("focus" in client) {
          await client.focus();
          return;
        }
      }
      if (self.clients.openWindow) {
        await self.clients.openWindow(target);
      }
    })(),
  );
});

// Browsers may rotate a subscription's keys without warning. When that happens
// we try to re-subscribe and re-register with the application server so pushes
// keep arriving. This is best-effort: it only works if the page previously sent
// us the API base + VAPID key, and if the browser supports re-subscription here.
self.addEventListener("pushsubscriptionchange", (event) => {
  event.waitUntil(
    (async () => {
      const config = await readConfig();
      if (!config || !config.apiBase || !config.vapidPublicKey) {
        return;
      }
      try {
        const applicationServerKey = urlBase64ToUint8Array(config.vapidPublicKey);
        const fresh = await self.registration.pushManager.subscribe({
          userVisibleOnly: true,
          applicationServerKey,
        });
        const base = config.apiBase.replace(/\/+$/, "");
        await fetch(base + "/subscribe", {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify(fresh),
        });
        const old = event.oldSubscription;
        if (old && old.endpoint && old.endpoint !== fresh.endpoint) {
          await fetch(base + "/unsubscribe", {
            method: "POST",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify({ endpoint: old.endpoint }),
          });
        }
        await broadcast({ type: "resubscribed", at: Date.now() });
      } catch (err) {
        await broadcast({ type: "error", message: "Re-subscribe failed: " + String(err), at: Date.now() });
      }
    })(),
  );
});

function parsePayload(event) {
  if (!event.data) {
    return { title: "Web Push", body: "(no payload)" };
  }
  try {
    return event.data.json();
  } catch (_e) {
    return { title: "Web Push", body: event.data.text() };
  }
}

async function broadcast(message) {
  const clients = await self.clients.matchAll({ type: "window", includeUncontrolled: true });
  for (const client of clients) {
    client.postMessage(message);
  }
}

async function readConfig() {
  try {
    const cache = await caches.open(CONFIG_CACHE);
    const res = await cache.match(CONFIG_KEY);
    return res ? await res.json() : null;
  } catch (_e) {
    return null;
  }
}

async function writeConfig(config) {
  try {
    const cache = await caches.open(CONFIG_CACHE);
    await cache.put(
      CONFIG_KEY,
      new Response(JSON.stringify(config), { headers: { "Content-Type": "application/json" } }),
    );
  } catch (_e) {
    /* Cache Storage may be unavailable in private modes; ignore. */
  }
}

// base64url (unpadded) -> Uint8Array, matching what the Worker emits for the
// VAPID public key. Duplicated here because the worker can't import app.js.
function urlBase64ToUint8Array(base64String) {
  const padding = "=".repeat((4 - (base64String.length % 4)) % 4);
  const base64 = (base64String + padding).replace(/-/g, "+").replace(/_/g, "/");
  const raw = atob(base64);
  const output = new Uint8Array(raw.length);
  for (let i = 0; i < raw.length; i += 1) {
    output[i] = raw.charCodeAt(i);
  }
  return output;
}
