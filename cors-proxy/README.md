# cors-proxy

A self-hostable **CORS proxy** for Cloudflare Workers, written in Rust. It
fetches a URL you name and returns the response with permissive
`Access-Control-*` headers, so browser code can read APIs that don't send CORS
headers of their own — the same job [corsproxy.io](https://corsproxy.io) does,
but as a small Worker you run yourself.

The interesting part is not the proxying, it's the hardening: "fetch any URL the
caller names" is textbook **Server-Side Request Forgery (SSRF)**, so most of
this crate is about *refusing* the dangerous requests.

> ⚠️ **A CORS proxy can read and modify everything that passes through it.**
> Never send secrets, cookies, or authenticated requests through a shared proxy.
> Treat this as a tool for **public, read-only** data. See
> [Security](#security).

## Usage

Once deployed at `https://cors-proxy-worker.<you>.workers.dev`:

```js
// Query form (recommended; matches corsproxy.io):
const url = "https://cors-proxy-worker.you.workers.dev/?url=" +
  encodeURIComponent("https://api.github.com/users/octocat");
const res = await fetch(url);

// Path form (best-effort):
// https://cors-proxy-worker.you.workers.dev/https://api.github.com/users/octocat
```

`GET /` with no target returns a small JSON help/limits document.

## Why Cloudflare Workers?

Hosted CORS proxies look expensive for what they do (corsproxy.io's paid tiers
are gated on **requests, RPM, bandwidth, and max file size**). The reason is
that a proxy re-emits the upstream body to the client, so on most clouds you pay
**egress bandwidth on ~100% of proxied traffic**, and an abuser can amplify that
by looping large downloads.

Workers changes the economics:

- **No egress bandwidth billing.** Workers bills requests + CPU time, not bytes
  out.
- **Waiting on the upstream `fetch` is not billable CPU time** — only actual
  compute is. A proxy that mostly streams bytes uses very little CPU.

So the real cost of running this is requests/CPU plus whatever **abuse
mitigation** you enable (rate-limit rules, WAF, Turnstile). That is the opposite
of the bandwidth trap that makes self-hosting a proxy on a VM pricey.

## Security

This is an open URL fetcher, so it is hardened against SSRF and abuse. See
[`docs/how-it-works.md`](docs/how-it-works.md) for the full rationale.

| Control | What it does |
|---------|--------------|
| Scheme allow-list | Only `http`/`https`; `file:`, `gopher:`, `data:`, etc. are rejected. |
| IP range blocking | Refuses loopback, private (RFC1918), link-local (incl. `169.254.169.254`), CGNAT, benchmarking, documentation, and reserved ranges — IPv4 and IPv6, including IPv4-mapped/compatible IPv6 and alternate numeric encodings (`2130706433`, `0x7f.0.0.1`). |
| Hostname blocking | Refuses `localhost`, `*.localhost`, `*.local`, `*.internal`, `*.home.arpa`, and cloud-metadata names. |
| Redirect re-validation | Redirects are followed **manually** and every `Location` hop is re-validated (defeats redirect-to-internal). Max 5 hops. |
| Cross-origin credential stripping | `Authorization`, `Proxy-Authorization`, `Cookie`, and `X-Api-Key` are dropped when a redirect crosses to a different origin, so a redirect can't harvest a caller's secrets. |
| Request header hygiene | Strips `Cookie`, `Origin`, `Referer`, forwarding headers (`X-Forwarded-*`, `CF-*`, `X-Real-IP`, `Via`), and hop-by-hop headers before calling the upstream. |
| Response header hygiene | Strips `Set-Cookie`/`Set-Cookie2` and upstream `Access-Control-*`; sets its own CORS headers. |
| Response size cap | Rejects responses larger than `MAX_RESPONSE_BYTES` (default 25 MiB), enforced **while streaming** so a chunked body can't be buffered unbounded. |
| Request size cap | Rejects inbound bodies larger than `MAX_REQUEST_BYTES` (default 10 MiB). |
| Origin allow-list | `ALLOWED_ORIGINS` restricts which browser origins may use the proxy (default `*`). |

### Known limitation: DNS rebinding

The Workers runtime does not expose DNS resolution to user code, so the guard
cannot resolve a hostname, check the resulting IP, and pin the connection to it.
A hostname that resolves to a private address (e.g. `localtest.me` →
`127.0.0.1`, or a TOCTOU rebind between check and connect) is therefore **not**
caught by the IP range checks. In practice, Cloudflare's edge does not route
`fetch` to RFC1918/loopback space, and redirects are re-validated hop by hop. If
you deploy somewhere that *can* reach a private network, add a resolve-and-pin
step before the fetch.

## Configuration

Set in `wrangler.toml` under `[vars]` (or with `wrangler secret`/dashboard):

| Var | Default | Meaning |
|-----|---------|---------|
| `ALLOWED_ORIGINS` | `*` | `*` to allow any browser origin, or a comma-separated list of exact origins (`https://a.example,https://b.example`). |
| `MAX_RESPONSE_BYTES` | `26214400` | Reject upstream responses larger than this (streamed). |
| `MAX_REQUEST_BYTES` | `10485760` | Reject inbound request bodies larger than this. |

## Develop and test

This is an isolated Rust crate pinned to the toolchain in `rust-toolchain.toml`
(Rust 1.88 + the `wasm32-unknown-unknown` target). All security logic is
transport-agnostic and unit-tested on the host — no deployment needed:

```bash
cd cors-proxy
cargo fmt --check
cargo clippy --all-targets -- -D warnings
cargo test

# What CI additionally runs for a Worker app:
cargo clippy --target wasm32-unknown-unknown -- -D warnings
cargo build --release --target wasm32-unknown-unknown
```

## Deploy

Pushes to `main` deploy this Worker automatically via `deploy-workers.yml`
(`wrangler deploy`), using the `CLOUDFLARE_API_TOKEN` and `CLOUDFLARE_ACCOUNT_ID`
repo secrets — no per-app secrets or KV namespaces are needed. To deploy by hand
you need a Cloudflare account and [`wrangler`](https://developers.cloudflare.com/workers/wrangler/):

```bash
cd cors-proxy
cargo +stable install worker-build@0.8.5   # tool build; see wrangler.toml note
npx wrangler deploy                          # builds the wasm Worker and publishes
```

`wrangler.toml`'s `[build]` command installs `worker-build` and compiles the
crate to wasm. This app has no `index.html`, so the repo's GitHub Pages
workflows do **not** serve it; the companion browser playground lives in
[`../cors-proxy-demo`](../cors-proxy-demo).
