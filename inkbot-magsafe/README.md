# inkbot-magsafe

Firmware and hardware design for a 4-inch mono e-ink tile that snaps to an
iPhone's MagSafe ring and takes frames from an iOS app over Bluetooth Low
Energy (BLE). It is the battery-first, phone-first sibling of the tethered
[`inkbot-esp32/`](../inkbot-esp32/) panel.

The full product design, circuit, power budget, and pricing are in
[`docs/inkbot-magsafe-design.md`](../docs/inkbot-magsafe-design.md); the bill of
materials is [`docs/inkbot-magsafe-bom.csv`](../docs/inkbot-magsafe-bom.csv).
Hardware notes (netlist, pin map, board stack-up) are in
[`hardware/`](hardware/).

Status: scaffold. The pure logic (frame protocol, panel geometry, power gating)
is implemented and unit-tested; the nRF52832 bring-up (SPI panel driver, SAADC,
SoftDevice BLE) is stubbed. The iOS app is deferred until the firmware and
hardware settle.

## What runs today

- `src/protocol.rs`: the resumable, idempotent BLE frame-transfer state machine
  with a table-free streaming CRC-32. Host-tested.
- `src/panel.rs`: geometry and the SSD1683-class command set for the 400x300
  panel, including partial-refresh window math. Host-tested.
- `src/power.rs`: battery state-of-charge estimate and the voltage and
  temperature gates for refresh and charge. Host-tested.
- `src/main.rs`: the bare-metal entry point. A do-nothing WFI loop today, with
  the bring-up sequence written out as the next steps.

## Target

- MCU: Nordic nRF52832 (Cortex-M4F), target `thumbv7em-none-eabihf`.
- Pre-certified module for early boards: Raytac MDBT42Q.
- Flashing: SWD test pads (there is no USB port); the cargo runner is
  `probe-rs`.

## Build and test

The library is `no_std` on the target but builds with `std` under `cargo test`,
so the logic runs on the host without a cross toolchain. Bare-metal-only crates
are gated on `cfg(target_os = "none")`, so host commands never pull the ARM
runtime.

```bash
cd inkbot-magsafe

# Host: logic tests, lints, formatting.
cargo test
cargo clippy --all-targets -- -D warnings
cargo fmt --all --check

# Firmware: cross-build and lint for the nRF52832.
cargo build --release --target thumbv7em-none-eabihf
cargo clippy --target thumbv7em-none-eabihf -- -D warnings

# Flash over SWD (needs a probe and probe-rs installed).
cargo run --release --target thumbv7em-none-eabihf
```

CI runs the same checks in [`.github/workflows/inkbot-magsafe.yml`](../.github/workflows/inkbot-magsafe.yml).
Like `inkbot-esp32`, this crate is excluded from the shared Rust job in
`test.yml` because it cross-compiles to a bare-metal target.
