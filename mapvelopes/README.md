# mapvelopes

A US #10 envelope PDF with the driving route from sender to recipient as the
background. Nick Johnson published this in 2010 as
[Mapvelopes](http://blog.notdot.net/2010/04/Generating-PDFs-on-App-Engine-Python-and-introducing-Mapvelopes).
[Yanko Design](https://www.yankodesign.com/2010/03/30/google-envelopes-beta-of-course/)
wrote it up as Google Envelopes. This is that envelope, as a Rust Cloudflare
Worker.

I wanted a PDF I could print: two addresses, a blue line between them.

> **Not a Pages app.** This directory has no `index.html`. GitHub Pages
> deploy and preview skip it. `deploy-workers.yml` publishes it to Cloudflare
> on push to `main` when the `CLOUDFLARE_API_TOKEN` and
> `CLOUDFLARE_ACCOUNT_ID` repo secrets are set.

## What you get

One page, 9.5 × 4.125 in (US #10). Return address, delivery address, stamp
box. With a Google Maps Platform key, the Worker (and the CLI) call Geocoding,
Directions, and Maps Static, and print the route as the background JPEG.
Without a key, or with `--stub`, you get the addresses on a blank page. Print
at 100% scale. "Fit to page" shrinks a #10 onto letter paper.

## Run it on your machine

From `mapvelopes/`:

```bash
cargo run --example envelope
```

That writes `envelope.pdf` in the current directory (Mountain View to New
York, no map). Override the addresses:

```bash
cargo run --example envelope -- \
  --from $'Ada Example\n1600 Amphitheatre Parkway\nMountain View, CA 94043' \
  --to $'Bob Example\n350 Fifth Avenue\nNew York, NY 10118' \
  -o /tmp/envelope.pdf
```

To hit Google, export a key or pass `--key`:

```bash
export GOOGLE_MAPS_API_KEY='…'
cargo run --example envelope -- -o /tmp/envelope.pdf
```

`--help` lists the flags.

The key needs **Geocoding**, **Directions**, and **Maps Static**. Do not
restrict it by HTTP referrer; neither the CLI nor the Worker send a Referer
Google will accept. Restricting by API is enough.

## HTTP API

Once deployed (or under `wrangler dev`):

| Method | Path | Result |
|--------|------|--------|
| `GET` | `/` | HTML form |
| `GET` | `/health` | `{"ok":true,"maps":"none"}` or `"google"` |
| `GET` | `/envelope?from=…&to=…` | PDF |
| `POST` | `/envelope` | PDF (`application/x-www-form-urlencoded` or JSON `{"from","to"}`) |

Addresses are freeform, one line per envelope line. The first line is bold on
the delivery block.

## Develop and test

Pinned in `rust-toolchain.toml` (Rust 1.88 + `wasm32-unknown-unknown`):

```bash
cd mapvelopes
cargo fmt --check
cargo clippy --all-targets -- -D warnings
cargo test

# What CI additionally runs for a Worker app:
cargo clippy --target wasm32-unknown-unknown -- -D warnings
cargo build --release --target wasm32-unknown-unknown
```

PDF drawing, polyline encode/decode, and Maps JSON parsing run on the host.
Nothing in `cargo test` calls Google.

## Deploy

Pushes to `main` deploy this Worker via `deploy-workers.yml`. To deploy by
hand:

```bash
cd mapvelopes
cargo +stable install worker-build@0.8.5
npx wrangler deploy
npx wrangler secret put GOOGLE_MAPS_API_KEY
```

For `wrangler dev`, copy `.dev.vars.example` to `.dev.vars` and put the key
there if you want live maps locally. An empty value skips Google.

The crate name is `mapvelopes-worker`; the Worker script name is
`mapvelopes-worker`.
