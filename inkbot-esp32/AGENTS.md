# Agent guide: inkbot-esp32

Rust / ESP-IDF firmware for the Waveshare e-Paper ESP32 Driver Board +
7.5″ 800×480 panel. Two binaries share the panel geometry: `inkbot-esp32`
(Wi-Fi + Worker + OTA) and `maze-esp32` (offline USB-only maze).

Read [`README.md`](README.md) for hardware and the day-to-day flash
loop, and [`docs/ota.md`](docs/ota.md) for NVS, OTA, and GCP.

## Contracts

- **Secrets stay in NVS.** Do not bake Wi-Fi, Worker URLs, upload secrets,
  or service-account keys into the ELF (`config.toml` / `build.rs`
  codegen is gone). `make provision` writes `provisioning.toml` into the
  `nvs` partition. An OTA image must boot on a device that was
  provisioned once over USB.
- **Required NVS or the panel loops `NOT PROVISIONED`:** `wifi/ssid`,
  `wifi/pass`, `inkbot/base_url` (must be `https://`), `trust/identities`,
  `trust/fulcio_root`, `trust/fulcio_inter`. Optional: `gcp/*`,
  `ota/repo|tag|poll_secs`. `ota.poll_secs = 0` disables GHCR polling.
- **NVS keys are at most 15 characters.** The DHCP interval is stored as
  `dhcp_renew`, not `dhcp_renew_secs`. GCP's interval is `metric_intvl`.
- **OTA is signed GHCR, not a raw URL.** Layer media type
  `application/vnd.esp32.firmware.bin`. Require OCI config
  `app=inkbot-esp32` and `target_chip=esp32`, and reject a layer larger
  than the `0x1F0000` slot. Verify the Cosign Sigstore bundle (Fulcio +
  DSSE + in-toto subject = manifest SHA) before writing the inactive
  slot. Identity allowlist comes from NVS, not the image.
- **Pending-verify:** after an OTA reboot, mark the slot valid only when
  the Worker boot fetch succeeds (`Displayed` or empty catalog). On fetch
  error, call `esp_ota_mark_app_invalid_rollback_and_reboot()` and store
  the digest as `last_digest` so the next poll does not re-flash it.
- **No extra stacks for OTA or GCP.** Both run on the main loop
  (`CONFIG_ESP_MAIN_TASK_STACK_SIZE=49152`). Set
  `OTA_DOWNLOAD_IN_PROGRESS` while the blob streams so frame GETs and GCP
  POSTs do not open a second TLS session.
- **Custom CA bundle only.** Roots live in `certs/`. Do not turn the full
  Mozilla bundle back on; DRAM is already tight next to the 48 KB
  framebuffer.
- **Slim GCP, not the Google crates.** JWT RS256 through mbedTLS FFI, one
  cached access token, Cloud Logging + Monitoring POSTs. A 64-entry
  `ForkLogger` queue tees `log` lines. No `rsa` / `tracing` / `time`
  crate on the device.
- **Maze stays USB-only.** Do not add Wi-Fi or OTA to `maze-esp32`.
- **First install is USB erase.** Boards that still have the factory
  partition table cannot OTA into this layout. Document
  `make bootstrap`; do not invent a migration path from the old image.
- **Host tools** live under `tools/provision` and `tools/publisher`
  (separate crates, not the firmware package). `make test` runs
  `cargo test --lib` plus `provision --dry-run` against
  `provisioning.toml.example`.
- **CI:** `inkbot-esp32.yml` hosts tests + Xtensa `make build`.
  `inkbot-esp32-publish.yml` (push to `main`, or dispatch from `main`)
  pushes and Cosign-signs `ghcr.io/imjasonh/playground/inkbot-esp32`, then
  `make pull-verify`. The example trust identity is that workflow
  `@refs/heads/main`. The GHCR package must stay public; the device pulls
  anonymously.
- **`FIRMWARE_ID`** in `src/status.rs` is the HTTP `User-Agent` and
  telemetry `firmware` field. Bump it when the on-wire or OTA contract
  changes.

## Local commands

```bash
cd inkbot-esp32
make test          # host lib + provision dry-run
make build         # both ELFs (needs espup)
make bootstrap     # erase + flash-all + provision
make publish       # OCI push + cosign (needs GH_TOKEN / gh.env)
```
