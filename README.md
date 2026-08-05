# ESP32 Rust

[![CI](https://github.com/imjasonh/esp32/actions/workflows/ci.yml/badge.svg)](https://github.com/imjasonh/esp32/actions/workflows/ci.yml)
[![Publish OTA](https://github.com/imjasonh/esp32/actions/workflows/publish.yml/badge.svg)](https://github.com/imjasonh/esp32/actions/workflows/publish.yml)

Std Rust on an Inland ESP-WROOM-32 dev board with end-to-end OTA over
GHCR + cosign keyless signing. Optional Cloud Logging + Cloud
Monitoring shipped from the device. E-ink display work coming next.

## What it does today

- Polls `ghcr.io/imjasonh/esp32:latest` every ~60 s for new firmware.
- For each new digest: fetches the cosign Sigstore Bundle, verifies
  the signature + cert chain to the Sigstore root + that the signer's
  identity matches the allowlist provisioned into the device's NVS.
- On verify-pass, streams the layer to the inactive OTA partition,
  reboots, marks the new image valid only after Wi-Fi + registry
  bringup checks pass. Any post-OTA failure auto-rolls back via the
  bootloader.
- Optionally ships structured `tracing` events to **Cloud Logging**
  and chip-health metrics (heap, stack, wifi, cpu, …) to **Cloud
  Monitoring**. Opt-in per device via the `[gcp]` block in
  `provisioning.toml`.

Push to `main` → CI builds → publish workflow pushes a signed image
to GHCR → device picks it up on its next poll.

## Docs

- [`docs/setup.md`](docs/setup.md) — prerequisites, first flash,
  day-to-day commands, GCP setup
- [`docs/ota.md`](docs/ota.md) — OTA + provisioning + signing design
- [`docs/observability.md`](docs/observability.md) — Cloud Logging +
  Cloud Monitoring design (current state)
- [`docs/eink-plan.md`](docs/eink-plan.md) — planned e-ink display work

## Quick start

```bash
cargo install espup espflash ldproxy
brew install cmake ninja dfu-util cosign jq
espup install --targets esp32
curl -LsSf https://astral.sh/uv/install.sh | sh

make provisioning.toml             # creates from template
$EDITOR provisioning.toml          # fill in wifi creds + trust identities
make bootstrap                     # build, flash everything, write NVS
make monitor                       # watch it boot and connect
```

See [`docs/setup.md`](docs/setup.md) for full details, including
optional GCP Logging + Monitoring setup.
