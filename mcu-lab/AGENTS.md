# Agent guide: mcu-lab

Multi-MCU Rust / ESP-IDF firmware lab (`riscv32imc-esp-espidf` for Seeed Studio
XIAO ESP32-C3 and `xtensa-esp32-espidf` for Waveshare 7.5″ e-Paper ESP32) with
shared BLE telemetry, BLE GATT OTA, and 1 kHz PC hotspot profiling for the
Playground **MCU Lab** iOS experiment.

Read [`README.md`](README.md) for the wire layout and build commands.

## Contracts

- **Host tests stay off the ESP-IDF C toolchain.** `cargo test --lib` and
  `cargo clippy --lib` compile the host-safe modules (`src/protocol.rs`,
  `src/panel.rs`, `src/maze/`, `src/grayscale/`, `src/gzip_bench.rs`) only.
  Device code lives behind the `firmware` feature and `required-features` on
  the board+app binaries.
- **Do not add this crate to the generic Rust job.** `discover-esp32-apps.sh`
  matches `[target.riscv32*-esp-espidf]` / `[target.xtensa-*-espidf]` in
  `.cargo/config.toml` so the ESP32 jobs in `test.yml` run host tests and the
  firmware cross-builds.
- **Binary packet layout and OTLP metric names are shared with iOS.** Keep
  `src/protocol.rs` and
  `ios/Sources/Experiments/MCULab/MCULabProtocol.swift` in lockstep.
- **Logic probe is GPIO 2 (`D0`) on `xiao-esp32c3`.** Keep `GPIO2` dedicated to
  phase-boundary toggling so external power profilers (Nordic PPK2) correlate
  current spikes with firmware phases.

## Local commands

```bash
cd mcu-lab
make test                                  # host protocol and maze tests
make build                                 # cross-compile xiao-esp32c3 + epd-maze
make flash-all APP=epd-maze PROFILING=1    # one-time USB flash for Waveshare EPD-75
make flash-all APP=xiao-esp32c3 PROFILING=1
make monitor                               # USB Serial/JTAG log
```
