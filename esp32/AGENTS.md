# ESP32 firmware agent guide

`esp32/` is a Rust/ESP-IDF workspace for classic Xtensa ESP32 boards. It was
imported from `github.com/imjasonh/esp32`; the original firmware remains at the
workspace root and the Waveshare e-ink SSH client lives in `eink/`.

## Commands

Use the Makefile so app-specific target directories, sdkconfig, partition table,
Python shim, and OCI package stay aligned:

```bash
make APP=blinky build
make APP=eink build
make APP=eink bootstrap
make APP=eink monitor
make APP=eink publish
```

Do not invoke `espflash flash` without `--partition-table partitions.csv`; doing
so replaces the rollback-safe OTA layout with espflash's factory layout.

Host-only checks:

```bash
cargo test --manifest-path eink/Cargo.toml --lib --target "$(rustc -vV | sed -n 's/^host: //p')"
cargo test --manifest-path tools/bundle-verifier/Cargo.toml --target "$(rustc -vV | sed -n 's/^host: //p')"
cargo test --manifest-path tools/provision/Cargo.toml --target "$(rustc -vV | sed -n 's/^host: //p')"
```

## Security contracts

- Firmware artifacts contain no WiFi credentials, SSH endpoints, host keys,
  client keys, or signer policy. Per-device values live in NVS.
- Never weaken Sigstore verification or server host-key pinning to make a demo
  connect.
- OTA verification must remain offline and bind Rekor's SET, checkpoint,
  inclusion proof, canonicalized body, DSSE signature, and Fulcio certificate.
  Rekor-key rotation is a USB re-provisioning event.
- The e-ink client supports Ed25519 server and client keys only. Adding another
  algorithm requires equivalent host-key verification and resource testing.
- The client key is generated on-device after WiFi starts and stored in plain
  NVS for the prototype. Re-provisioning the full NVS partition rotates it.
- Keep the original and e-ink firmware in separate GHCR repositories.
- OTA images must fit the `0x1F0000` app slot.

## E-ink hardware

Expected board wiring is fixed by Waveshare SKU 15823:

| Signal | GPIO |
|---|---:|
| SCLK | 13 |
| MOSI | 14 |
| CS | 15 |
| DC | 27 |
| RST | 26 |
| BUSY | 25 |

The Amazon listing does not guarantee the panel revision. Keep initialization
inside `eink/src/display.rs`; do not add partial refresh until the rear sticker
and flex markings identify the exact 800×480 panel and full refresh works on
hardware. The current implementation targets the modern V2/UC8179 sequence and
performs full refresh followed by panel deep sleep.
