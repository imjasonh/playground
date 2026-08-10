# inkbot

E-ink desk frame: a Cloudflare Worker that hosts a **library** of 800×480
black-and-white frames, plus ESP32 firmware that rotates through them.
Mention `@inkbot` in Slack with an image to add one; `list` / `delete` manage
the rotation.

Companion firmware (Rust / ESP-IDF): [`../inkbot-esp32/`](../inkbot-esp32/).

## Shape

```
Slack @inkbot + image ──► Worker (dither) ──► R2 frames/{name}.{png,bin}
curl POST /foo.bin    ──► Worker (validate) ──┘
                                                         ▲
ESP32 ──GET / every 60s; GET /{name}.bin on change/rotate─┘
```

## Worker API

| Method | Path | Auth | Purpose |
|--------|------|------|---------|
| `GET` | `/` | none | Catalog JSON: `{ revision, latest, images }` |
| `GET` | `/health` | none | Liveness |
| `GET` | `/{name}.bin` | none | Packed 48 000-byte framebuffer (`ETag` / `304`) |
| `GET` | `/{name}.png` | none | PNG preview |
| `POST` | `/{name}.bin` | `Authorization: Bearer <UPLOAD_SECRET>` | Create/replace (panel PNG or any photo) |
| `DELETE` | `/{name}.bin` | Bearer | Remove from rotation |
| `POST` | `/slack/events` | Slack signing secret | Events API |

```bash
wrangler secret put UPLOAD_SECRET
wrangler secret put SLACK_BOT_TOKEN
wrangler secret put SLACK_SIGNING_SECRET
```

## Slack

| Mention | Effect |
|---------|--------|
| `@inkbot` + image attachment | Dither and add (name from filename) |
| `@inkbot list` | List images in the rotation |
| `@inkbot delete <name>` | Delete from rotation |

## Device behaviour

- Every `poll_secs` (default 60s): fetch catalog; if `latest` changed, display it.
- Every `rotate_secs` (default 1800s): pick a random other image and display it.
- Boot always paints `latest`.

## Local development

```bash
cd inkbot
cargo test
cargo clippy --all-targets -- -D warnings
npx wrangler dev
```

Upload:

```bash
curl -X POST \
  -H "Authorization: Bearer $UPLOAD_SECRET" \
  --data-binary @frame.png \
  https://inkbot.<account>.workers.dev/sgt-pepper.bin

curl https://inkbot.<account>.workers.dev/
```

## Tests

```bash
cargo test --locked
```
