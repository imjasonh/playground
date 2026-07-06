# How the CORS proxy works

This document explains what the proxy does, why each security control exists,
and where the sharp edges are. If you only read one section, read
[§2 SSRF](#2-ssrf-the-main-threat).

## 1. What a CORS proxy is

Browsers block a page on origin `A` from reading a response from origin `B`
unless `B` opts in with `Access-Control-Allow-Origin`. Many public APIs don't,
so the browser refuses to hand the bytes to your JavaScript even though the
request succeeded.

A CORS proxy sidesteps this: your page calls the proxy (same-origin or a proxy
that *does* send CORS headers), the proxy makes the request server-side where
CORS doesn't apply, and returns the body with `Access-Control-Allow-Origin: *`.
From the browser's point of view it's just talking to a CORS-friendly server.

```
browser ──(CORS-friendly)──▶ cors-proxy ──(server-side, no CORS)──▶ upstream API
        ◀──body + ACAO:* ───            ◀──── body ────────────────
```

## 2. SSRF: the main threat

The proxy fetches a URL chosen by the caller. That is **Server-Side Request
Forgery** by construction: an attacker can ask the proxy to fetch things they
could never reach themselves, from the proxy's network vantage point:

- `http://127.0.0.1/...` or `http://[::1]/...` — services bound to loopback.
- `http://10.x`, `http://192.168.x`, `http://172.16-31.x` — internal network.
- `http://169.254.169.254/latest/meta-data/` — cloud instance metadata
  (credentials on many platforms).
- `http://metadata.google.internal/` — the same, by name.

`src/url_guard.rs` rejects these before any fetch happens. It:

1. **Allow-lists the scheme** (`http`/`https` only). `file:`, `gopher:`,
   `data:`, `ftp:` are all rejected — they're SSRF/LFI vectors or nonsense for a
   web proxy.
2. **Parses with a real WHATWG URL parser** (the `url` crate) so it sees the
   same host the runtime will connect to. This matters because
   `http://2130706433/`, `http://0x7f.0.0.1/`, and `http://0177.0.0.1/` all mean
   `127.0.0.1`; a string denylist misses them, but the parser normalizes them to
   an `Ipv4Addr` the range check catches.
3. **Blocks non-public IP ranges** for both IPv4 and IPv6: unspecified,
   loopback, private, link-local, CGNAT (`100.64/10`), benchmarking
   (`198.18/15`), documentation, and reserved (`240/4`) ranges, plus multicast
   and broadcast. IPv6 unwraps IPv4-mapped (`::ffff:a.b.c.d`) and
   IPv4-compatible forms and applies the IPv4 rules, and blocks `fe80::/10`,
   `fc00::/7`, and `2001:db8::/32`.
4. **Blocks local/internal hostnames**: `localhost`, `*.localhost`, `*.local`,
   `*.internal`, `*.home.arpa`, and known metadata names.

### Redirects re-open the hole

An upstream that returns `302 → http://169.254.169.254/` would walk you straight
past the initial check if you followed redirects automatically. So the Worker
sets `redirect: manual` and, for each `Location`, resolves it against the current
URL and runs the **full guard again** before making the next request (max 5
hops). `301`/`302`/`303` collapse to a bodyless `GET`; `307`/`308` preserve the
method and body.

### The DNS-rebinding gap (be honest about it)

The classic hardening is "resolve the hostname once, validate that IP, then pin
the socket to it so DNS can't change under you." The Cloudflare Workers runtime
**does not expose DNS resolution** — `fetch` resolves internally — so we can't do
the resolve-and-pin dance. That means:

- A name like `localtest.me` that resolves to `127.0.0.1` **passes** the guard
  (there's a test pinning this behavior).
- A TOCTOU rebind (public at check time, private at connect time) is not caught
  by IP checks.

Two things keep this acceptable for a Workers deployment: Cloudflare's edge does
not route `fetch` to RFC1918/loopback space in the first place, and every
redirect hop is re-validated. **If you port this to a runtime that can reach a
private network (a VM, a container in a VPC), you must add a resolve-and-pin
step — the IP checks alone are not enough there.**

## 3. Abuse and resource limits

An open proxy is attractive to scrapers and as an IP launderer, so:

- **Size cap.** `MAX_RESPONSE_BYTES` (default 25 MiB) is checked against the
  upstream `Content-Length` and again against the actual body length.
- **Redirect cap.** At most 5 hops.
- **Header hygiene.** Inbound `X-Forwarded-*`, `CF-*`, `X-Real-IP`, `Via`,
  `Forwarded` are stripped so the proxy can't be used to spoof identity headers
  to the upstream; `Cookie` is not forwarded.
- **Origin allow-list.** `ALLOWED_ORIGINS` lets you restrict the proxy to your
  own front-ends instead of running it fully open.

Rate limiting and bot defense are best handled at the platform edge:
Cloudflare **Rate Limiting Rules**, **WAF**, and **Turnstile** are the right
tools at scale, rather than counting requests inside the isolate.

## 4. Privacy: what the operator can see

Because the proxy terminates the request, **whoever runs it can read and modify
everything passing through** — URLs, request bodies, response bodies. This is
unavoidable for any proxy. Consequences:

- Never send `Authorization`, cookies, or other secrets through a shared proxy.
- Don't trust responses you can't otherwise verify.
- **Never `eval`/execute content fetched through a proxy** (JS, JSONP, HTML you
  inline): a malicious upstream or operator could run script in your origin.

This proxy does not persist request or response bodies. It sets no cookies and
strips `Set-Cookie` from upstream responses.

## 5. Cost model on Workers

A proxy is almost pure I/O, and Workers is priced well for that:

- **No egress bandwidth charge.** The dominant cost of a proxy on AWS/GCP/Azure
  (you pay to send the upstream bytes back to the client) simply isn't billed on
  Workers.
- **Blocking on the upstream `fetch` isn't billable CPU time.** Only real
  compute counts, and a byte-relay does very little.

So the marginal cost is requests + a little CPU. The costs that *do* scale are
the abuse-mitigation add-ons (WAF/rate limiting/Turnstile) if you run the proxy
open to the world.

## 6. Code map

| File | Responsibility |
|------|----------------|
| `src/url_guard.rs` | SSRF guard: scheme + IP/host validation. Native tests. |
| `src/proxy.rs` | Target extraction, header sanitization, CORS decisions, size limits. Native tests. |
| `src/error.rs` | `GuardError` and its HTTP status mapping. |
| `src/worker_entry.rs` | wasm-only glue: `fetch`, manual re-validated redirects, response relay. |
| `tests/integration.rs` | End-to-end tests of the extract → validate → sanitize pipeline. |
