# How inkbot works

## Storage

R2 holds a small catalog plus per-image objects:

- `catalog.json` — `{ revision, latest, images: [...] }`
- `frames/{name}.png` — browser-friendly packed 1-bit PNG
- `frames/{name}.bin` — raw 48 000-byte MSB-first framebuffer (ESP32)
- `device.json` — last ESP32 telemetry (`{ received_at, report }`)

`revision` bumps on every add/replace/delete. `latest` is the name most
recently written so the device can show new uploads immediately.

Legacy single-image keys (`image.png` / `image.bin` / `image.etag`) are
imported once as the name `image` when no catalog exists yet.

## HTTP API

| Method | Path | Auth | Purpose |
|--------|------|------|---------|
| `GET` | `/` | none | Catalog JSON |
| `GET` | `/health` | none | Liveness |
| `GET` | `/latest.bin` | none | Packed framebuffer for `catalog.latest` (ESP32 boot) |
| `GET` | `/{name}.bin` | none | Packed framebuffer (`ETag` / `304`) |
| `GET` | `/{name}.png` | none | PNG preview |
| `GET` | `/device` | Bearer | Last ESP32 telemetry report |
| `POST` | `/{name}.bin` | Bearer | Create/replace (PNG or photo body) |
| `POST` | `/device` | Bearer | ESP32 status report (JSON object, ≤8 KiB) |
| `DELETE` | `/{name}.bin` | Bearer | Remove from rotation |
| `POST` | `/slack/events` | Slack sig | Events API |

Names are `[A-Za-z0-9][A-Za-z0-9_-]{0,62}` (`health`, `slack`, `events`, `latest`, `device` reserved).

## Slack

`POST /slack/events` (Slack Events API):

1. Verify `X-Slack-Signature`.
2. Answer `url_verification` challenges.
3. On `app_mention`:
   - attach an image → dither, add as sanitized filename
   - `list` → reply with names
   - `delete <name>` → remove from rotation
   - `status` → last ESP32 telemetry (`POST /device`)

## Device poll

Every `poll_secs` (default 60):

1. `GET /` for the catalog.
2. If `latest` changed since last seen → `GET /{latest}.bin` and display.
3. Else if `rotate_secs` (default 1800) elapsed → pick a random other name and display.

Boot always paints `latest` (no `If-None-Match`) so a power cycle restores the
current frame.

The device also `POST /device` with Bearer `UPLOAD_SECRET` after boot, whenever
its error text changes, and every `status_secs` (default 900). The Worker stores
the last report in `device.json` (`GET /device`, or Slack `@inkbot status`).
