# How inkbot works

## Storage

R2 keeps three siblings for the current frame:

- `image.png` — canonical packed 1-bit PNG (browsers / Slack preview)
- `image.bin` — raw 48 000-byte MSB-first framebuffer (ESP32; no zlib)
- `image.etag` — SHA-256 ETag of the PNG so `GET` can answer `304`

Legacy buckets that only have `image.png` recover `image.bin` on first load.

## Direct upload

`POST /image.png` with `Authorization: Bearer <UPLOAD_SECRET>`:

1. Reject empty / unauthorized bodies.
2. Decode the PNG; require exact panel size.
3. Require every opaque pixel to be pure black or pure white (no gray, no color).
4. Re-encode as a packed 1-bit grayscale PNG and the matching raw framebuffer.

## Slack mention

`POST /slack/events` (Slack Events API):

1. Verify `X-Slack-Signature` (HMAC-SHA256 over `v0:{ts}:{body}`, 5-minute skew).
2. Answer `url_verification` challenges.
3. On `app_mention`, download the first image file with the bot token.
4. Cover-crop to 800×480, Floyd–Steinberg dither to 1-bit, store, reply in-thread.

## Device poll

The ESP32 polls `GET /image.bin` with `If-None-Match` for the last ETag it
displayed. Unchanged frames cost one cheap `304` and no panel refresh (e-ink
full refreshes are slow and flash). The device never inflates PNG/zlib —
HTTPS already fragments the classic ESP32 heap enough that a 32 KB inflate
window often fails.
