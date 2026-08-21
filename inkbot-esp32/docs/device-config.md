# Device config (NVS)

Wi-Fi, Worker URL, poll/rotate/status cadence, upload secret, and Sigstore OTA
pins are **not** compiled into the ELF. They live in the NVS partition and are
flashed separately with the same binary on every board.

## Flash

```bash
cp nvs/device.csv.example nvs/device.csv
# edit ssid / pass / base_url (and optional cadence / Sigstore pins)
make build                   # once, so ESP-IDF (and nvs_partition_gen) exist
make flash PORT=/dev/cu.usbserial-XXXX
make nvs PORT=/dev/cu.usbserial-XXXX
```

`make nvs` runs ESP-IDF’s `nvs_partition_gen.py` and writes the blob at the
default NVS offset (`0x9000`, size `0x6000` on the stock single-app table).
That **replaces the whole NVS partition**, so catalog bookmarks (`name` /
`etag` / …) are cleared. Re-flash `nvs/device.csv` whenever you change
credentials or cadence; you do not need to rebuild the app.

If `ssid` or `base_url` is missing, the panel shows `config: …` and retries
every few seconds until you provision NVS.

## Namespaces and keys

ESP-IDF NVS keys are at most **15** characters.

| Namespace | Key | Type | Required | Meaning |
|-----------|-----|------|----------|---------|
| `wifi` | `ssid` | string | yes | STA SSID |
| `wifi` | `pass` | string | no | STA password (empty = open) |
| `inkbot` | `base_url` | string | yes | Worker base URL (no trailing slash) |
| `inkbot` | `poll_secs` | u32 | no | Catalog poll interval (default 60) |
| `inkbot` | `rotate_secs` | u32 | no | Library rotate interval (default 1800) |
| `inkbot` | `upload_sec` | string | no | Bearer for `POST /device` (empty = off) |
| `inkbot` | `status_secs` | u32 | no | Status post interval (default 900) |
| `inkbot` | `dhcp_renew` | u32 | no | DHCP renew interval (default 21600) |
| `sigstore` | `oidc_iss` | string | for OTA | Fulcio OIDC issuer |
| `sigstore` | `cert_id` | string | for OTA | Fulcio certificate identity |

The `inkbot` namespace also holds runtime catalog keys (`name`, `etag`,
`latest`, `op`, `inc`). Do not reuse those names in the CSV.

## Code

| Piece | Role |
|-------|------|
| [`src/device_config.rs`](../src/device_config.rs) | Host-tested parse + defaults |
| [`nvs/device.csv.example`](../nvs/device.csv.example) | Flash-time template |
| [`docs/sigstore-ota.md`](sigstore-ota.md) | Why Sigstore stays in the app + NVS pins |
