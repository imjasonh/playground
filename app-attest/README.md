# app-attest

Cloudflare Worker that checks one Apple App Attest handshake from the Playground
iOS app, then issues a short-lived JWT. Later calls send that JWT.
`GET /v1/whoami` returns the attested `userId` and `deviceId`.

This directory has no `index.html`, so GitHub Pages skips it.
`deploy-workers.yml` deploys it on pushes to `main`.

The iOS UI lives in [`ios/Sources/Experiments/AppAttest/`](../ios/Sources/Experiments/AppAttest/).

## Handshake

1. `POST /v1/challenge` returns a one-time nonce (5-minute KV TTL).
2. The iOS app builds `{"challenge","userId","deviceId"}`, hashes those exact
   JSON bytes, and calls `DCAppAttestService.attestKey`.
3. `POST /v1/token` sends `keyId`, the CBOR `attestationObject`, and the raw
   client JSON. The Worker checks the Apple certificate chain, the nonce
   extension, the App ID hash, and the bound identifiers, then stores the
   public key (`counter` starts at 0) and returns an HS256 JWT.
4. `GET /v1/whoami` with `Authorization: Bearer <jwt>` returns
   `{ userId, deviceId, keyId, unattested }`.

App Attest is not available in the iOS Simulator. When
`ALLOW_UNATTESTED=1`, `POST /v1/unattested-token` issues a JWT with
`unattested: true` after consuming a challenge. Leave that flag off in
production.

## HTTP API

An optional `/api` prefix and trailing slash are accepted.

| Method | Path | Auth | Description |
|--------|------|------|-------------|
| `GET` | `/health` | – | Service name, configured App ID |
| `POST` | `/v1/challenge` | – | `{ challenge, expiresAt }` |
| `POST` | `/v1/token` | – | Attestation → JWT |
| `POST` | `/v1/unattested-token` | – | Simulator path; disabled unless `ALLOW_UNATTESTED=1` |
| `GET` | `/v1/whoami` | Bearer JWT | Attested `userId` and `deviceId` |

`POST /v1/token` body:

```json
{
  "keyId": "<base64 key id from generateKey>",
  "attestationObject": "<base64 CBOR>",
  "clientData": "{\"challenge\":\"…\",\"userId\":\"…\",\"deviceId\":\"…\"}"
}
```

`clientData` must be the exact JSON string the app hashed. Sending it as a
string keeps those bytes intact.

The JWT `sub` is `userId`. Custom claims are `device_id` and `key_id`.

## Configuration

| Binding | Kind | Purpose |
|---------|------|---------|
| `STORE` | KV | Challenges and attested device rows |
| `APP_ID` | var | `<Team ID>.<Bundle ID>` for the Playground host app |
| `TOKEN_TTL_SECONDS` | var | JWT lifetime (default 3600) |
| `ALLOW_UNATTESTED` | var | `1` to allow the Simulator path |
| `JWT_SECRET` | secret | HS256 key. Generate with `cargo run --example gensecret` |

Replace the `XXXXXXXXXX` Team ID in `wrangler.toml` with the 10-character
`APPLE_TEAM_ID` before a real device can attest. The App ID hash in
authenticator data is `SHA-256(APP_ID)`.

`deploy-workers.yml` generates `JWT_SECRET` on first deploy when
`examples/gensecret.rs` is present, and leaves an existing secret alone.

```bash
cd app-attest
cargo test
echo -n "$(cargo run --quiet --example gensecret)" | wrangler secret put JWT_SECRET
```

## Tests

Native `cargo test` covers JWT mint/verify, challenge replay, the unattested
path, and a generated App Attest chain (test CA, Apple nonce OID, CBOR
object). The wasm Worker entry is compiled only for `wasm32`.
