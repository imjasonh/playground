# ESP32 Rust firmware

[![ESP32](https://github.com/imjasonh/playground/actions/workflows/esp32.yml/badge.svg)](https://github.com/imjasonh/playground/actions/workflows/esp32.yml)
[![Publish OTA](https://github.com/imjasonh/playground/actions/workflows/esp32-publish.yml/badge.svg)](https://github.com/imjasonh/playground/actions/workflows/esp32-publish.yml)

Std Rust on an Inland ESP-WROOM-32 dev board with end-to-end OTA over
GHCR + cosign keyless signing. Optional Cloud Logging + Cloud
Monitoring ships from the original firmware. The `eink/` firmware turns a
Waveshare ESP32 driver board and 800×480 panel into an SSH display client.

This code was imported from
[`github.com/imjasonh/esp32`](https://github.com/imjasonh/esp32) and retains its
Apache-2.0 license.

## Firmware applications

- `esp32-blinky` (workspace root): the original OTA + observability firmware.
- `esp32-eink` (`eink/`): connects over WiFi, generates and persists an
  Ed25519 key, verifies a provisioned Ed25519 server host key, requests an
  SSH exec channel, displays the command's output in an 80×25 buffer, and
  disconnects. Its signed OTA stream is `ghcr.io/imjasonh/esp32-eink:latest`.

Both applications share the same OTA verifier and trust implementation from
`src/lib.rs`.

Monthly maintenance updates the ESP32 lockfiles and a compiled trust epoch,
cross-builds both applications, and triggers a signed Rekor-v2 OTA only after
all checks pass.

## Secure OTA

- Polls its application-specific GHCR repository every ~60 s for new firmware.
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
- [`docs/eink-ssh.md`](docs/eink-ssh.md) — e-ink hardware, provisioning, and
  first SSH flow

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

For the Waveshare device, use `APP=eink`:

```bash
make provisioning.toml
$EDITOR provisioning.toml
make APP=eink bootstrap
make APP=eink monitor
```

See [`docs/setup.md`](docs/setup.md) for host prerequisites and
[`docs/eink-ssh.md`](docs/eink-ssh.md) for SSH enrollment.
