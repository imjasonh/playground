# app-attest

Cloudflare Worker that checks one Apple App Attest handshake from the Playground
iOS app, then requires a fresh `generateAssertion` on each later call.
`POST /v1/whoami` returns the attested `userId` and `deviceId`.

This directory has no `index.html`, so GitHub Pages skips it.
`deploy-workers.yml` deploys it on pushes to `main`.

The iOS UI lives in [`ios/Sources/Experiments/AppAttest/`](../ios/Sources/Experiments/AppAttest/).

## Handshake

1. `POST /v1/challenge` returns a one-time nonce (5-minute KV TTL).
2. The iOS app signs in with Apple, then builds `{"challenge","userId","deviceId"}`
   using that Apple user identifier, hashes those exact JSON bytes, and calls
   `DCAppAttestService.attestKey`.
3. `POST /v1/token` sends `keyId`, the CBOR `attestationObject`, and the raw
   client JSON. The Worker checks the Apple certificate chain, the nonce
   extension, the App ID hash, and the bound identifiers, then stores the
   public key (`counter` starts at 0) and the attestation receipt.
4. Each later `POST /v1/whoami` spends a new challenge. The app hashes
   `{"action":"whoami","challenge"}`, calls `generateAssertion`, and posts the
   CBOR assertion. The Worker verifies the signature with the stored public
   key and requires the authenticator counter to increase, then returns
   `{ userId, deviceId, keyId, unattested, counter, riskMetric }`.

A reused JWT is not enough to call `whoami`. A stolen assertion also fails:
the challenge is one-shot, and the counter must be strictly greater than the
value stored from the previous assertion.

App Attest is not available in the iOS Simulator. When
`ALLOW_UNATTESTED=1`, `POST /v1/unattested-token` stores an unattested device
row after consuming a challenge, and later `whoami` calls for that key skip
the assertion. Leave that flag off in production.

## Fraud metric

A compromised genuine iPhone can attest many keys and then sign assertions
for patched app copies running on other devices. Apple's App Attest data
server returns an approximate count of unique attested keys for your app on
that device over the past 30 days. The Worker stores the receipt from
`attStmt` and, when DeviceCheck secrets are set, POSTs it to
`https://data.appattest.apple.com/v1/attestationData` (or the development
host) for a refreshed receipt that includes that count.

The metric is a risk signal, not a hard proof. Reinstalls and device restores
also rotate keys and raise the number. Apple's guidance is to watch for
spikes, not to lock people out on a single high value. Set `MAX_RISK_METRIC`
only if you want this Worker to return HTTP 403 when the stored count is
above that number. Without DeviceCheck secrets the Worker still attests and
verifies assertions; `riskMetric` stays null.

## HTTP API

An optional `/api` prefix and trailing slash are accepted.

| Method | Path | Description |
|--------|------|-------------|
| `GET` | `/health` | Service name, configured App ID |
| `POST` | `/v1/challenge` | `{ challenge, expiresAt }` |
| `POST` | `/v1/token` | Attestation. Stores the key and returns the bound ids |
| `POST` | `/v1/unattested-token` | Simulator path; disabled unless `ALLOW_UNATTESTED=1` |
| `POST` | `/v1/whoami` | Assertion (or unattested challenge) → attested ids |

`POST /v1/token` body:

```json
{
  "keyId": "<base64 key id from generateKey>",
  "attestationObject": "<base64 CBOR>",
  "clientData": "{\"challenge\":\"…\",\"userId\":\"…\",\"deviceId\":\"…\"}"
}
```

`POST /v1/whoami` body:

```json
{
  "keyId": "<base64 key id>",
  "assertionObject": "<base64 CBOR>",
  "clientData": "{\"action\":\"whoami\",\"challenge\":\"…\"}"
}
```

`clientData` must be the exact JSON string the app hashed. Sending it as a
string keeps those bytes intact. Omit `assertionObject` only on the
unattested Simulator path.

## Configuration

| Binding | Kind | Purpose |
|---------|------|---------|
| `STORE` | KV | Challenges and attested device rows |
| `APP_ID` | var | `<Team ID>.<Bundle ID>` for the Playground host app |
| `ALLOW_UNATTESTED` | var | `1` to allow the Simulator path |
| `MAX_RISK_METRIC` | var | Optional. `whoami` returns 403 when the stored Apple count is above this |
| `DEVICECHECK_KEY_ID` | secret | Optional. DeviceCheck key id for receipt refresh |
| `DEVICECHECK_PRIVATE_KEY` | secret | Optional. PKCS #8 PEM for that DeviceCheck key |

`APP_ID` in `wrangler.toml` is `W5LPA2QM2W.io.github.imjasonh.playground`.
The App ID hash in authenticator data is `SHA-256(APP_ID)`. The Team ID is
public; it is in every signed Playground build. Receipt refresh uses that
same Team ID as the DeviceCheck JWT `iss`.

```bash
cd app-attest
cargo test
```

## Tests

Native `cargo test` covers challenge replay, the unattested path, assertion
signature and counter checks, a generated App Attest chain (test CA, Apple
nonce OID, CBOR object), and a scripted fraud-metric refresh. The wasm
Worker entry is compiled only for `wasm32`.
