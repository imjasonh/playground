# life-print

Cloudflare Worker that quotes [life-lab](../life-lab) sculptures through the
[Slant 3D](https://www.slant3d.com/api) print API.

life-lab builds a binary STL in the browser (via the `life-stl` wasm module).
This Worker parks that STL briefly in R2, asks Slant to slice the public
`/files/{id}` URL, and returns the print price. The Slant API key never leaves
the Worker.

> **Not a Pages app.** No `index.html` — `deploy-workers.yml` deploys it to
> Cloudflare on pushes to `main`. Pair it with the quote UI in `life-lab/`.

## HTTP API

| Method | Path | Body | Description |
|--------|------|------|-------------|
| `GET` | `/` or `/health` | – | Liveness + whether `SLANT_API_KEY` is set |
| `POST` | `/quote` | binary STL | `{ price, currency, triangles, id, provider }` |
| `GET` | `/files/{id}` | – | Temporary public STL (fetched by Slant during quote) |

CORS is permissive by default (`ALLOWED_ORIGINS = "*"`). Slant's slicer call is
synchronous, so the R2 blob is deleted as soon as the quote returns.

## Local development & tests

```bash
cd life-print
cargo test
cargo fmt --check
cargo clippy --locked --all-targets -- -D warnings
cargo clippy --locked --target wasm32-unknown-unknown -- -D warnings
```

The crate targets Rust **1.88**, pinned in `rust-toolchain.toml`.

## Deploying

Pushes to `main` that touch `life-print/` deploy via `deploy-workers.yml` (R2
bucket `life-print-stls` is created automatically). After the first deploy, set
the Slant key once:

```bash
cd life-print
wrangler secret put SLANT_API_KEY   # paste key from https://www.slant3dapi.com/
```

Optional vars in `wrangler.toml`:

| Var | Default | Purpose |
|-----|---------|---------|
| `SLANT_API_BASE` | `https://www.slant3dapi.com` | Slant REST root |
| `MAX_STL_BYTES` | `15728640` (15 MiB) | Inbound STL size cap |
| `ALLOWED_ORIGINS` | `*` | Browser Origin allow-list |

Point life-lab at the deployed Worker with `?printApi=https://life-print.<account>.workers.dev`
(or the in-page field; value is saved in `localStorage`).

## Ordering / payment (not implemented)

**Quote is free of payment plumbing. Checkout is not.**

| Approach | Who pays Slant? | Are you in the money path? |
|----------|-----------------|----------------------------|
| `POST /api/order` with *your* API key | **You** (card on the Slant account) | Yes — you eat the cost or must charge the user yourself (Stripe/Shopify/etc.) |
| Slant **Portals** (hosted product link, $0 markup) | **The buyer**, at Slant's checkout | No — closest to "pay Slant at cost, leave me out" |
| User pastes their own Slant API key | The user | No, but terrible UX |

There is no Order API mode where an anonymous life-lab visitor pays Slant
directly while your key is only used for quoting. Stripe Connect on Slant's
platform is for marketplace markups, not for stepping out of the transaction.
A future "Buy print" button should open/create a Portal (or similar hosted
checkout) rather than calling `/api/order` with the playground's key.
