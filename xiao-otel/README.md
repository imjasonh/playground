# xiao-otel

Go service for Cloud Run that authorizes `POST /v1/metrics` requests from the
Playground iOS **XIAO ESP32C3** experiment using Apple **App Attest** and writes
the incoming OTLP/HTTP v1 metrics to **Google Cloud Monitoring**
(`custom.googleapis.com/xiao_esp32c3/*`).

The iOS app holds no GCP credentials. Instead:

1. On first export, the iOS app requests a one-time challenge from
   `POST /v1/challenge`, attests a Secure Enclave key with
   `DCAppAttestService.attestKey`, and registers that key via `POST /v1/token`
   (or `POST /v1/unattested-token` in the iOS Simulator when
   `ALLOW_UNATTESTED=true`).
2. On every metric export, the iOS app fetches a fresh challenge, hashes
   `{"action":"metrics","challenge":"…"}`, signs a hardware assertion with
   `DCAppAttestService.generateAssertion`, and sends the OTLP/HTTP v1 JSON
   payload to `POST /v1/metrics` with the `X-Apple-App-Attest-*` headers.
3. `xiao-otel` verifies the ECDSA P-256 assertion against the stored public key
   and requires the authenticator counter to increase, then writes the gauge
   points to `monitoring.googleapis.com/v3/projects/{project}/timeSeries` using
   the Cloud Run service account's ambient `roles/monitoring.metricWriter`
   credentials.

## HTTP API

| Method | Path | Description |
|--------|------|-------------|
| `GET` | `/health` | Service status, configured `appId`, and `allowUnattested` flag |
| `POST` | `/v1/challenge` | Issue a one-time 32-byte hex challenge (5-minute TTL) |
| `POST` | `/v1/token` | Verify Apple App Attest `attestationObject` and register the device's P-256 public key |
| `POST` | `/v1/unattested-token` | Simulator fallback when `ALLOW_UNATTESTED=true` |
| `POST` | `/v1/whoami` | Verify a `whoami` assertion and return the bound `userId` and `deviceId` |
| `POST` | `/v1/metrics` | Verify a `metrics` assertion (if headers or envelope are present) and forward OTLP/HTTP JSON metrics to Cloud Monitoring |

## Local development and tests

```bash
cd xiao-otel
bash ../.github/scripts/check-gofmt.sh .
go build ./...
go test -race ./...
```

## Deploying to Cloud Run

1. Apply [`gcp/terraform`](../gcp/README.md) once so the `xiao-otel` runtime
   service account exists in your GCP project.
2. Push to `main`. `.github/workflows/deploy-gcp.yml` builds the container image
   with `ko` and applies `xiao-otel/terraform` over GitHub OIDC.
