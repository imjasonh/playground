# Agent guide: xiao-esp32c3

Rust / ESP-IDF firmware (`riscv32imc-esp-espidf`) for the Seeed Studio XIAO
ESP32C3 that instruments wake-cycle phases (`sensor`, `compute`, `epd_refresh`,
and `radio`), toggles a GPIO logic marker (`GPIO2` / `D0`), and broadcasts a
24-byte telemetry packet in BLE Manufacturer Specific Data (`0xFFFF`) for the
Playground **XIAO ESP32C3** iOS experiment.

Read [`README.md`](README.md) for the wire layout and build commands.

## Contracts

- **Host tests stay off the ESP-IDF C toolchain.** `cargo test --lib` and
  `cargo clippy --lib` compile `src/protocol.rs` only. Device code lives in
  `src/main.rs` behind the `firmware` feature and `required-features` on the
  `xiao-esp32c3` binary.
- **Do not add this crate to the generic Rust job.** `discover-esp32-apps.sh`
  matches `[target.riscv32*-esp-espidf]` in `.cargo/config.toml` so the ESP32
  jobs in `test.yml` run host tests and the firmware cross-build.
- **Binary packet layout and OTLP metric names are shared with iOS.** Keep
  `src/protocol.rs` and
  `ios/Sources/Experiments/XIAOESP32C3/XIAOESP32C3Protocol.swift` in lockstep.
  Bump `FIRMWARE_ID` when the on-wire contract changes.
- **Logic probe is GPIO 2 (`D0`).** Keep `GPIO2` dedicated to phase-boundary
  toggling so external power profilers (Nordic PPK2) correlate current spikes
  with firmware phases.

## Local commands

```bash
cd xiao-esp32c3
make test          # host protocol and OTLP tests
make build         # RISC-V ESP-IDF ELF
make flash         # build + flash
make monitor       # USB Serial/JTAG log
```
