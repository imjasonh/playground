# cors-proxy-demo — browser front-end for the CORS proxy Worker

A tiny static page that drives the [`cors-proxy`](../cors-proxy/) Cloudflare
Worker from a real browser: point it at your deployed proxy, build a request to
any public API, send it through the proxy, and inspect the CORS-enabled
response (status, headers, and body).

It is a plain static app (HTML + CSS + JS, no build step) so the repository's
GitHub Pages workflows deploy it automatically — both to production and to a
per-PR preview URL.

```
cors-proxy-demo/
├── index.html          # the UI
├── app.js              # config, request builder, response viewer, logging
├── styles.css
└── icon.svg            # favicon
```

## How it fits together

The page is served from **this** origin (GitHub Pages). It makes a cross-origin
`fetch` to your deployed proxy, which adds `Access-Control-Allow-Origin`, so the
browser lets this page read the upstream response it would otherwise block.

```
 GitHub Pages (this page)            Cloudflare Worker (../cors-proxy)        upstream API
 ────────────────────────           ────────────────────────────────        ────────────
  fetch  /?url=<target> ───────────▶ validate (SSRF guard) ───────────────▶  GET <target>
        ◀── body + ACAO:* ─────────  relay body + CORS headers  ◀──────────  body
```

## Use it (deployed)

1. **Deploy the Worker** from [`../cors-proxy`](../cors-proxy/README.md#deploy)
   and note its URL, e.g. `https://cors-proxy-worker.your-name.workers.dev`.
2. Open the demo:
   - Production: `https://<owner>.github.io/<repo>/cors-proxy-demo/`
   - PR preview: the URL the preview bot comments on your PR, then `…/cors-proxy-demo/`
3. Paste the proxy URL into **Proxy base URL** and click **Check connection**
   (you should see `reachable` and the proxy's limits).
4. Enter a **Target URL** (or click a preset chip) and click **Send request**.
5. Inspect the response. Try the "metadata (blocked)" chip to see the SSRF guard
   refuse a request to `169.254.169.254` with a `403`.

Tip: you can deep-link the proxy URL with a query param, e.g.
`…/cors-proxy-demo/?proxy=https://cors-proxy-worker.your-name.workers.dev`. The
value is also remembered in `localStorage`.

## Use it (locally)

Serve over `localhost` (not `file://`) so relative assets and `fetch` behave:

```bash
cd cors-proxy-demo
npx serve .          # or: python3 -m http.server 8080
```

Then open `http://localhost:8080/` and point it at a proxy you can reach (for
example `wrangler dev`'s URL). If this page is served over HTTPS, the proxy URL
must be `https://` too, or the browser blocks it as mixed content.

## Safety reminder

A CORS proxy can read and modify everything that passes through it. This demo is
for **public, read-only** data. Never send secrets, cookies, or authenticated
requests through a shared proxy, and never execute content fetched through one.

## Tests

Like `hello/` and `web-push-demo/`, this is a static demo with **no build or
unit tests**: its behavior is browser-only. The proxy's security logic (SSRF
guard, header sanitization, CORS decisions) is covered by the Rust test suite in
[`../cors-proxy`](../cors-proxy/README.md#develop-and-test).
