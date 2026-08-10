# How inkbot works

## Storage

One R2 object, `image.png`, holds the canonical packed 1-bit PNG for the
Waveshare 7.5″ panel (800×480). A sibling `image.etag` object stores the
SHA-256 ETag so `GET` can answer `304` without hashing on every poll.

## Direct upload

`POST /image.png` with `Authorization: Bearer <UPLOAD_SECRET>`:

1. Reject empty / unauthorized bodies.
2. Decode the PNG; require exact panel size.
3. Require every opaque pixel to be pure black or pure white (no gray, no color).
4. Re-encode as a packed 1-bit grayscale PNG and store.

## Slack mention

`POST /slack/events` (Slack Events API):

1. Verify `X-Slack-Signature` (HMAC-SHA256 over `v0:{ts}:{body}`, 5-minute skew).
2. Answer `url_verification` challenges.
3. On `app_mention`, download the first image file with the bot token.
4. Cover-crop to 800×480, Floyd–Steinberg dither to 1-bit, store, reply in-thread.

## Device poll

The ESP32 sends `If-None-Match` with the last ETag it displayed. Unchanged
frames cost one cheap `304` and no panel refresh (e-ink full refreshes are
slow and flash).
