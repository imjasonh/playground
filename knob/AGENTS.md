# Agent guide: knob

Rust / ESP-IDF firmware for the Waveshare ESP32-S3-Knob-Touch-LCD-1.8.
Two binaries share one library. `knob-s3` is the panel, sensors, and BLE
peripheral. `knob-esp32` is the Classic Bluetooth audio chip and the I2S
master for the 3.5 mm jack.

Read [`README.md`](README.md) for the flash loop. Pin facts are in
[`docs/hardware.md`](docs/hardware.md). The GATT contract for the later
iOS app is in [`docs/ble.md`](docs/ble.md).

## Contracts

- **Host tests stay off the Xtensa toolchain.** `cargo test --lib` compiles
  `src/lib.rs` only. Device code lives in `src/s3_main.rs` and
  `src/esp32_main.rs`, behind `firmware-s3` and `firmware-esp32`.
- **Do not add this crate to `test.yml`.** Stable Linux Cargo cannot build
  `xtensa-esp32s3-espidf` or `xtensa-esp32-espidf`. `knob.yml` owns the
  host tests and both cross-builds.
- **The S3 does not drive the PCM5100A.** GPIO0 stays low so the companion
  I2S path stays selected. Tone and A2DP audio leave this chip as UART
  `Msg::Tone` or as A2DP samples on the companion.
- **Example apps are Cargo features.** `app-dial` through `app-remote`.
  `make build APPS=clock,tone` is `--no-default-features` plus those
  features. Do not hide an app behind a runtime flag.
- **BLE UUIDs and the text protocol live in `src/ble.rs`.** Bump
  `FIRMWARE_ID_S3` or `FIRMWARE_ID_ESP32` when that chip's on-wire contract
  changes. The iOS app is not in this crate yet.
- **An API-shaped change to the UART frame belongs in `src/link.rs` with a
  round-trip test.** Both binaries use that codec.
- **CI.** `knob.yml` always runs discover, then no-ops the host and
  firmware jobs when `knob/` is unchanged.

## Local commands

```bash
cd knob
make test
make build
make flash-s3
make flash-esp32
make monitor
```
