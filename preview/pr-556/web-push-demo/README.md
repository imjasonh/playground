# web-push-demo — browser front-end for the Web Push Worker

A tiny static page that drives the [`web-push`](../web-push/) Cloudflare Worker
**end to end** from a real browser: grant permission, subscribe, send a test
notification, and watch it arrive.

It is a plain static app (HTML + CSS + JS, no build step) so the repository's
GitHub Pages workflows deploy it automatically — both to production and to a
per-PR preview URL.

```
web-push-demo/
├── index.html          # the UI
├── app.js              # config, feature detection, subscribe/notify, logging
├── sw.js               # service worker: push + notificationclick handlers
├── styles.css
├── manifest.webmanifest
└── icon.svg            # favicon + notification icon
```

## How it fits together

The page and its service worker are served from **this** origin (GitHub Pages).
All API calls go **cross-origin** to your deployed Worker, which sends permissive
CORS headers (`Access-Control-Allow-Origin: *`), so the two can live on
different origins.

```
 GitHub Pages (this page + sw.js)            Cloudflare Worker (../web-push)
 ───────────────────────────────             ──────────────────────────────
  subscribe ──fetch /vapidPublicKey──────────▶ returns VAPID public key
            ──pushManager.subscribe()
            ──fetch POST /subscribe ──────────▶ stores subscription (KV)
  notify    ──fetch POST /notify  ───────────▶ encrypts + sends to push service
                                                          │
  service worker  ◀───────── push (encrypted) ────────────┘   (via the browser's
   push event → showNotification + postMessage to the page         push service)
```

## Use it (deployed)

1. **Deploy the Worker** from [`../web-push`](../web-push/README.md#deploying)
   and note its URL, e.g. `https://web-push-worker.your-name.workers.dev`.
2. Open the demo:
   - Production: `https://<owner>.github.io/<repo>/web-push-demo/`
   - PR preview: the URL the preview bot comments on your PR, then `…/web-push-demo/`
3. Paste the Worker URL into **Worker API base URL** and click **Check
   connection** (you should see `reachable` and the VAPID public key).
4. Click **Subscribe** and allow notifications when prompted.
5. Click **Send notification** — a system notification appears and the push
   payload is echoed in the activity log.

Tip: you can deep-link the Worker URL with a query param, e.g.
`…/web-push-demo/?api=https://web-push-worker.your-name.workers.dev`. The value
is also remembered in `localStorage`.

## Use it (locally)

Service workers and the Push API require a **secure context** — HTTPS or
`http://localhost`. Serve over `localhost` (not `file://`):

```bash
cd web-push-demo
npx serve .          # or: python3 -m http.server 8080
```

Then open `http://localhost:8080/` and point it at a Worker you can reach (for
example `wrangler dev`'s URL).

## Requirements & notes

- **HTTPS / localhost** — enforced by the browser for service workers + push.
  When the demo is served over HTTPS, the Worker URL must be `https://` too — an
  `http://` URL is blocked as mixed content (the page warns you).
- **Notification permission** — you must allow notifications; if you deny it,
  reset it in the browser's site settings.
- **iOS Safari** — add the page to the **Home Screen** and open it from there;
  Web Push only works for installed web apps on iOS 16.4+.
- **"Only notify this device"** (checked by default) targets just your
  subscription using its id (`base64url(SHA-256(endpoint))`, computed locally to
  match the Worker). Unchecking it broadcasts to every stored subscription.
- The service worker always calls `showNotification` on a push, because the
  subscription is created with `userVisibleOnly: true`.

## Tests

Like `hello/`, this is a static demo with **no build or unit tests**: its
behavior is browser-only (service workers, the Push API, real push delivery) and
can't be meaningfully exercised in headless CI without a live push service. The
protocol/crypto correctness is covered by the Rust test suite in
[`../web-push`](../web-push/README.md#local-development--tests).
