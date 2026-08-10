# inkbot

E-ink desk frame: a Cloudflare Worker that hosts a single 800×480 black-and-white
PNG, plus a tiny ESP32 sketch that polls it once a minute. Mention `@inkbot` in
Slack with an image attached and the Worker cover-crops, Floyd–Steinberg
dithers, and publishes the frame.

Companion firmware (Rust / ESP-IDF): [`../inkbot-esp32/`](../inkbot-esp32/).

## Why this shape

The earlier ESP32 e-ink work ([PR #188](https://github.com/imjasonh/playground/pull/188))
targeted the same Waveshare 7.5″ 800×480 panel + ESP32 driver board, but bundled
SSH, signed OTA, and Rekor trust. This pair keeps only the useful hardware
assumptions and the “show a picture” loop.

```
Slack @inkbot + image ──► Worker (transform) ──► R2 image.png
curl POST /image.png  ──► Worker (validate)  ──┘
                                                   ▲
ESP32 ──GET /image.png every 60s (If-None-Match)───┘
```

## Worker API

| Method | Path | Auth | Purpose |
|--------|------|------|---------|
| `GET` | `/image.png` | none | Current frame. Sends `ETag`; honors `If-None-Match` → `304`. |
| `POST` | `/image.png` | `Authorization: Bearer <UPLOAD_SECRET>` | Replace frame. Body must already be an 800×480 strictly B/W PNG. |
| `POST` | `/slack/events` | Slack signing secret | Events API (`url_verification`, `app_mention`). |
| `GET` | `/health` | none | Liveness. |

On deploy, if `UPLOAD_SECRET` is unset, CI generates one (see
`.github/scripts/ensure-worker-upload-secret.sh`). Slack secrets are manual:

```bash
wrangler secret put SLACK_BOT_TOKEN        # xoxb-…
wrangler secret put SLACK_SIGNING_SECRET   # from Slack app Basic Information
```

## Slack app setup

1. Create a Slack app → **OAuth & Permissions** bot scopes:
   `app_mentions:read`, `files:read`, `chat:write`.
2. **Event Subscriptions** → Request URL
   `https://inkbot.<account>.workers.dev/slack/events`
   (URL verification is handled automatically).
3. Subscribe to bot event `app_mention`.
4. Install to the workspace; put the bot token + signing secret into Worker secrets.
5. Invite `@inkbot` to a channel, attach an image, mention it.

## Local development

```bash
cd inkbot
cargo test
cargo clippy --all-targets -- -D warnings

# Optional: run under wrangler (needs CLOUDFLARE_* + R2 binding)
cp .dev.vars.example .dev.vars   # if present; or create with UPLOAD_SECRET=…
npx wrangler dev
```

Upload a panel-ready PNG:

```bash
curl -X POST \
  -H "Authorization: Bearer $UPLOAD_SECRET" \
  --data-binary @frame.png \
  https://inkbot.<account>.workers.dev/image.png
```

## Tests

Pure logic (PNG validate/transform, Bearer auth, Slack signature + event parse,
HTTP routing) runs on the host — no Workers runtime needed:

```bash
cargo test --locked
```

## Layout

```
inkbot/
├── src/
│   ├── panel.rs         # 800×480 B/W validate + Slack dither/encode
│   ├── auth.rs          # Bearer + Slack HMAC
│   ├── slack.rs         # Events API parse
│   ├── api.rs           # transport-agnostic router
│   └── worker_entry.rs  # R2 + fetch glue (wasm only)
├── examples/gensecret.rs
└── wrangler.toml        # R2 bucket inkbot-images
```
