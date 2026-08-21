# mapvelopes

A US envelope PDF with the driving route from sender to recipient as the
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

One page in a US envelope size you pick: #10 (9.5 × 4.125 in, default), #9
(8.875 × 3.875), Monarch (7.5 × 3.875), #6¾ (6.5 × 3.625), or A7 (7.25 ×
5.25). Return address, delivery address, stamp box, and a Maps Static JPEG
of the driving route as the background. The map is washed toward cream so
the addresses stay readable (hybrid more than the others). Short addresses
are expanded to USPS-style lines before printing: `98 16th st brooklyn`
becomes `98 16th St` / `Brooklyn, NY 11215`. The form offers Google, paper,
terrain, muted, and hybrid looks, plus Places Autocomplete as you type.
The Worker and CLI both require a Google Maps Platform key. If the key is
missing or Google rejects it, they return an error instead of a blank
envelope. Print at 100% scale. "Fit to page" shrinks the PDF onto letter
paper.

## Run it on your machine

From `mapvelopes/`, with a key:

```bash
export GOOGLE_MAPS_API_KEY='…'
cargo run --example envelope
```

That writes `envelope.pdf` in the current directory (Mountain View to New
York). Override the addresses:

```bash
cargo run --example envelope -- \
  --from $'Ada Example\n1600 Amphitheatre Parkway\nMountain View, CA 94043' \
  --to $'Bob Example\n350 Fifth Avenue\nNew York, NY 10118' \
  -o /tmp/envelope.pdf
```

`--help` lists the flags, including `--style` (`google`, `paper`,
`terrain`, `muted`, `hybrid`) and `--size` (`10`, `9`, `monarch`,
`6-3/4`, `a7`).

The key needs **Geocoding**, **Directions**, **Maps Static**, and **Places**
(Autocomplete + Place Details). Do not restrict it by HTTP referrer; neither
the CLI nor the Worker send a Referer Google will accept. Restricting by
API is enough. The form never sees the key: typeahead goes through
`/suggest` and `/place` on this Worker.

## HTTP API

Once deployed (or under `wrangler dev`):

| Method | Path | Result |
|--------|------|--------|
| `GET` | `/` | HTML form |
| `GET` | `/form.js` | Typeahead script for the form |
| `GET` | `/health` | `{"ok":true,"maps":"google"}` or 503 `{"ok":false,"maps":"none"}` |
| `GET` | `/suggest?q=…` | `{ "suggestions": [{ "label", "place_id" }] }` |
| `GET` | `/place?id=…` | `{ "lines": ["98 16th St", "Brooklyn, NY 11215"] }` |
| `GET` | `/envelope?from=…&to=…` | PDF (optional `style=`, `size=`) |
| `POST` | `/envelope` | PDF (`application/x-www-form-urlencoded` or JSON `{"from","to","style","size"}`) |

Addresses are freeform, one line per envelope line. A name on the first
line is kept; the rest is expanded from Geocoding (street, city, state,
ZIP). The first line is bold on the delivery block when it looks like a
name. `style` is `google` (default), `paper`, `terrain`, `muted`, or
`hybrid`. `size` is `10` (default, #10), `9`, `monarch`, `6-3/4`, or
`a7`.

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

For `wrangler dev`, copy `.dev.vars.example` to `.dev.vars` and put a real
key there. An empty value fails the same way as a missing secret.

The crate name is `mapvelopes-worker`; the Worker script name is
`mapvelopes-worker`. Invocation logs go to the Cloudflare dashboard under
Workers & Pages → mapvelopes-worker → Logs. They record whether the key
binding is present (length only) and any Google error body. They do not
record the key.
