# Agent guide: inkbot-esp32

Rust / ESP-IDF firmware for the Waveshare e-Paper ESP32 Driver Board +
7.5″ 800×480 panel. Two binaries share the panel geometry: `inkbot-esp32`
(Wi-Fi + Worker + OTA pull) and `maze-esp32` (offline maze). Cargo features
are per-package, so each image is a separate `cargo +esp build` with its
own sdkconfig and `CARGO_TARGET_DIR` (`make build`).

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
  `ota/app|repo|tag|poll_secs`. `ota.app` is `inkbot-esp32` (default) or
  `maze-esp32`. `ota.poll_secs = 0` disables GHCR polling. The default
  repo is `ghcr.io/imjasonh/playground/{app}` when `ota/repo` is unset.
- **NVS keys are at most 15 characters.** The DHCP interval is stored as
  `dhcp_renew`, not `dhcp_renew_secs`. GCP's interval is `metric_intvl`.
  The selected image is `ota/app` (the key is `app`).
- **OTA is signed GHCR, not a raw URL.** Layer media type
  `application/vnd.esp32.firmware.bin`. Require OCI config `app` to match
  the **requested** `ota/app` (not the running binary) and
  `target_chip=esp32`, and reject a layer larger than the `0x1F0000`
  slot. Verify the Cosign Sigstore bundle (Fulcio + DSSE + in-toto
  subject = manifest SHA) before writing the inactive slot. Identity
  allowlist comes from NVS, not the image.
- **Pending-verify:** after an OTA reboot, mark the slot valid only when
  the health check succeeds. inkbot: Worker boot fetch (`Displayed` or
  empty catalog). maze: first successful panel paint. On that check
  failing (inkbot fetch error, or maze mark-valid error), call
  `esp_ota_mark_app_invalid_rollback_and_reboot()` and store the digest
  as `last_digest` so the next poll does not re-flash it.
- **No extra stacks for OTA or GCP.** Both run on the inkbot main loop
  (`CONFIG_ESP_MAIN_TASK_STACK_SIZE=49152`). Set
  `OTA_DOWNLOAD_IN_PROGRESS` while the blob streams so frame GETs and GCP
  POSTs do not open a second TLS session. Maze uses a smaller main stack
  (`sdkconfig.defaults.maze.in`).
- **Custom CA bundle only (inkbot).** Roots live in `certs/`. Do not turn
  the full Mozilla bundle back on; DRAM is already tight next to the 48 KB
  framebuffer. Maze sdkconfig leaves the CA bundle off.
- **Slim GCP, not the Google crates.** JWT RS256 through mbedTLS FFI, one
  cached access token, Cloud Logging + Monitoring POSTs. A 64-entry
  `ForkLogger` queue tees `log` lines. No `rsa` / `tracing` / `time`
  crate on the device. Compile GCP out with `make build GCP=0` (`gcp`
  Cargo feature). Runtime `[gcp]` omitted still means serial-only on an
  image that includes the feature.
- **Maze does not poll GHCR.** Do not add Wi-Fi or an OTA client to
  `maze-esp32`. inkbot can pull the maze image when `ota/app=maze-esp32`.
  That switch is one-way until a USB `make flash` (without `APP=maze`)
  restores inkbot.
- **First install is USB erase.** Boards that still have the factory
  partition table cannot OTA into this layout. Document
  `make bootstrap`; do not invent a migration path from the old image.
  Bootstrap flashes **inkbot** (the puller). Maze is a later OTA or
  `make flash APP=maze`.
- **Host tools** live under `tools/provision` and `tools/publisher`
  (separate crates, not the firmware package). `make test` runs
  `cargo test --lib` plus `provision --dry-run` against
  `provisioning.toml.example`.
- **CI:** `inkbot-esp32.yml` hosts tests + Xtensa `make build` (both
  apps, separate IDF trees). `inkbot-esp32-publish.yml` (push to `main`,
  or dispatch from `main`) pushes and Cosign-signs
  `ghcr.io/imjasonh/playground/inkbot-esp32` and
  `ghcr.io/imjasonh/playground/maze-esp32`, then `make pull-verify`. The
  example trust identity is that workflow `@refs/heads/main`. GHCR
  packages must stay public; the device pulls anonymously.
- **`FIRMWARE_ID`** in `src/status.rs` is the HTTP `User-Agent` and
  telemetry `firmware` field. Bump it when the on-wire or OTA contract
  changes.

## Local commands

```bash
cd inkbot-esp32
make test          # host lib + provision dry-run
make build         # both ELFs, separate target dirs (needs espup)
make build GCP=0   # inkbot without the gcp module
make bootstrap     # erase + flash-all + provision (APP=inkbot)
make publish       # OCI push + cosign of both apps (needs GH_TOKEN / gh.env)
```
