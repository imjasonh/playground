# web-push — Web Push backend on Cloudflare Workers (Rust)

The application-server half of the [Web Push][webpush] stack, implemented in
Rust and compiled to a Cloudflare Worker (`wasm32-unknown-unknown`). It stores
browser push subscriptions and sends encrypted, VAPID-authenticated push
messages to any standards-compliant push service (FCM, Mozilla autopush, Apple,
etc.).

> **Not a Pages app.** Unlike most directories here, this is a Cloudflare
> Worker, not a GitHub Pages app (it has no `index.html`), so the Pages
> deploy/preview workflows skip it. Instead, `deploy-workers.yml` deploys it to
> Cloudflare with `wrangler` on every push to `main`. The only setup needed is
> the repo secrets `CLOUDFLARE_API_TOKEN` and `CLOUDFLARE_ACCOUNT_ID`; the
> deploy provisions the rest (the KV namespace and the `VAPID_PRIVATE_KEY`
> secret) automatically. See [Deploying](#deploying).

> **Learning the protocol?** Read **[docs/how-it-works.md](docs/how-it-works.md)** —
> a thorough, diagram-driven walkthrough of Web Push, VAPID, and the encryption,
> mapped to this code. This README is the quick reference.

## What it implements

| RFC | Title | Where |
|-----|-------|-------|
| [8030] | Generic Event Delivery Using HTTP Push (TTL/Urgency/Topic) | `src/push.rs` |
| [8188] | Encrypted Content-Encoding for HTTP (`aes128gcm`) | `src/ece.rs` |
| [8291] | Message Encryption for Web Push (ECDH + HKDF schedule) | `src/ece.rs` |
| [8292] | VAPID — application-server identification (ES256 JWT) | `src/vapid.rs` |

All cryptography is pure Rust ([RustCrypto]): P-256 ECDH/ECDSA, HKDF-SHA256, and
AES-128-GCM. The same code runs natively under `cargo test` and in the wasm
Worker, so the test suite exercises the exact production crypto.

## Architecture

The HTTP API is written against two traits so it can be tested without the
Workers runtime or a network:

- `SubscriptionStore` — CRUD for subscriptions. Backed by **Workers KV** in
  production (`src/worker_entry.rs`) and an in-memory map in tests
  (`InMemoryStore`).
- `PushSender` — delivers an assembled request. Backed by the **`fetch`** API in
  production and a recording sender in tests.

```
browser ──subscribe──▶ Worker (fetch) ──▶ api::handle ──▶ SubscriptionStore (KV)
                                              │
admin ────notify─────▶ Worker (fetch) ──▶ api::handle ──▶ encrypt (RFC 8291)
                                              │            + VAPID (RFC 8292)
                                              └──────────▶ PushSender (fetch) ──▶ push service
```

| File | Responsibility |
|------|----------------|
| `src/b64.rs` | base64url encode/decode (tolerant) |
| `src/subscription.rs` | parse/validate the browser `PushSubscription` |
| `src/ece.rs` | `aes128gcm` content encoding + Web Push encrypt/decrypt |
| `src/vapid.rs` | VAPID key, ES256 JWT, `Authorization` header |
| `src/push.rs` | assemble the HTTP push request (headers + encrypted body) |
| `src/store.rs` | `SubscriptionStore` trait + in-memory store |
| `src/sender.rs` | `PushSender` trait + response classification |
| `src/api.rs` | routing + request/response handling |
| `src/worker_entry.rs` | Cloudflare Worker glue (KV + fetch), wasm only |

## HTTP API

An optional `/api` prefix and trailing slash are accepted. All responses are
JSON with permissive CORS headers.

| Method | Path | Body | Description |
|--------|------|------|-------------|
| `GET` | `/health` | – | Liveness + subscription count |
| `GET` | `/vapidPublicKey` | – | `{ "publicKey": "<base64url>" }` for `applicationServerKey` |
| `POST` | `/subscribe` | `PushSubscription` | Store a subscription → `{ "id" }` |
| `POST` | `/unsubscribe` | `{ "id" }` or `{ "endpoint" }` | Remove a subscription |
| `GET` | `/subscriptions` | – | List stored subscriptions |
| `POST` | `/notify` | see below | Encrypt + send to one or all subscriptions |

`POST /notify` body:

```json
{
  "payload": { "title": "Hello", "body": "World" },
  "ttl": 86400,
  "urgency": "normal",
  "topic": "optional-topic",
  "id": "optional-single-subscription-id"
}
```

`payload` (required) is delivered, encrypted, to the service worker's `push`
event. If `id` is omitted the message is broadcast to every subscription;
subscriptions the push service reports as `404`/`410` are pruned automatically.

## Local development & tests

```bash
cd web-push
cargo test                                  # unit + integration tests
cargo clippy --all-targets                  # lints
cargo build --target wasm32-unknown-unknown # build the Worker (wasm)
cargo run --example genvapid                # print a fresh VAPID key pair
```

The integration tests (`tests/integration.rs`) drive the real API, then act as
the user agent — decrypting the captured push body with the subscription's
private key and verifying the VAPID JWT — so correctness is checked end-to-end
without any deployment. `src/ece.rs` also includes the **RFC 8188 Appendix A.1**
known-answer test.

### Minimum supported Rust

The crate targets Rust **1.83**, pinned in `rust-toolchain.toml` so local builds
and CI use the same toolchain (and the `wasm32-unknown-unknown` target). A few
transitive dependencies raised their MSRV in later patch releases and are pinned
in `Cargo.toml` (`zeroize`, `idna_adapter`); `Cargo.lock` is committed for
reproducible builds.

## Deploying

Pushes to `main` deploy this Worker automatically via `deploy-workers.yml`,
which runs `wrangler deploy` with the repo secrets `CLOUDFLARE_API_TOKEN` and
`CLOUDFLARE_ACCOUNT_ID`. **Those two secrets are the only setup required** — the
workflow provisions the Worker's Cloudflare-side config for you:

- **KV namespace** — before deploy, `.github/scripts/provision-worker-kv.py`
  create-or-gets the `SUBSCRIPTIONS` namespace (and its `_preview` sibling) and
  rewrites the `REPLACE_WITH_…` placeholder ids in `wrangler.toml` with the real
  ids. It's idempotent: existing namespaces are reused, so the committed
  placeholders are fine to leave in place.
- **VAPID key** — after deploy, `.github/scripts/ensure-worker-vapid.sh`
  checks whether the Worker already has a `VAPID_PRIVATE_KEY` secret. If not, it
  generates a fresh key pair (via the `genvapid` example) and stores the private
  key as the secret. It only generates when the secret is **absent**, so the
  VAPID identity — and every browser subscription bound to it — stays stable
  across deploys. `VAPID_SUBJECT` is a plain var in `wrangler.toml [vars]`.

The API token must have permission to manage Workers, Workers KV, and Worker
secrets on the account.

To deploy or iterate manually (equivalent steps, done by hand):

```bash
# Install tooling
cargo install worker-build
npm install -g wrangler

# Provision KV + VAPID once, then deploy
wrangler kv namespace create SUBSCRIPTIONS          # paste id into wrangler.toml
wrangler kv namespace create SUBSCRIPTIONS --preview # paste preview_id
cargo run --example genvapid                        # generate a VAPID key pair
wrangler secret put VAPID_PRIVATE_KEY               # paste the private key

wrangler dev      # local
wrangler deploy   # production
```

## Browser integration

A ready-to-use browser front-end lives in [`../web-push-demo`](../web-push-demo/) —
a static page (deployed to GitHub Pages by this repo) that subscribes,
unsubscribes, and sends notifications against a deployed Worker so you can see
the whole round-trip. The essentials it performs:

```js
// 1. Fetch the server's VAPID public key and subscribe.
const { publicKey } = await (await fetch(`${API}/vapidPublicKey`)).json();
const reg = await navigator.serviceWorker.register("sw.js");
const sub = await reg.pushManager.subscribe({
  userVisibleOnly: true,
  applicationServerKey: urlBase64ToUint8Array(publicKey), // base64url → bytes
});
await fetch(`${API}/subscribe`, {
  method: "POST",
  headers: { "Content-Type": "application/json" },
  body: JSON.stringify(sub),
});

// 2. In sw.js, show the decrypted payload.
self.addEventListener("push", (event) => {
  const data = event.data.json();
  event.waitUntil(self.registration.showNotification(data.title, { body: data.body }));
});
```

[webpush]: https://developer.mozilla.org/en-US/docs/Web/API/Push_API
[8030]: https://www.rfc-editor.org/rfc/rfc8030
[8188]: https://www.rfc-editor.org/rfc/rfc8188
[8291]: https://www.rfc-editor.org/rfc/rfc8291
[8292]: https://www.rfc-editor.org/rfc/rfc8292
[RustCrypto]: https://github.com/RustCrypto
