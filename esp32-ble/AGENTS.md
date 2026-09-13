# Agent guide: esp32-ble

Rust / ESP-IDF firmware that exposes a small GATT server for the Playground
**ESP32 BLE** iOS experiment. The iPhone writes LED commands; the board
notifies a status line and blinks GPIO 2.

Read [`README.md`](README.md) for the flash loop and the on-wire format.

## Contracts

- **Host tests stay off the Xtensa toolchain.** `cargo test --lib` and
  `cargo clippy --lib` compile `src/protocol.rs` only. Device code lives in
  `src/main.rs` behind the `firmware` feature and `required-features` on the
  `esp32-ble` binary.
- **Do not add this crate to `test.yml`.** Stable Linux Cargo cannot build
  `xtensa-esp32-espidf`. `esp32-ble.yml` owns host tests and the Xtensa
  cross-build, same split as `inkbot-esp32`.
- **GATT UUIDs and the text protocol are shared with iOS.** Keep
  `src/protocol.rs` and `ios/Sources/Experiments/ESP32BLE/ESP32BLEProtocol.swift`
  in lockstep. Bump `FIRMWARE_ID` when the on-wire contract changes.
- **No Wi-Fi, NVS secrets, or OTA.** This image is USB-flash only. Do not
  copy inkbot's provision / GHCR publish path here unless the product changes.
- **LED pin is GPIO 2, active-high.** That matches most ESP32-DevKitC boards.
  Change `LED_GPIO_LABEL` / `gpio2` / `LED_ACTIVE_HIGH` in `src/main.rs` if
  the board you have is different.
- **CI:** `esp32-ble.yml` always runs discover + host/firmware jobs (so they
  can be required checks) and no-ops when `esp32-ble/` is unchanged.

## Local commands

```bash
cd esp32-ble
make test          # host protocol tests
make build         # Xtensa ELF (needs espup)
make flash         # build + flash
make monitor       # serial log
```
