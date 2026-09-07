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

Status: EVT design. Host-tested code covers the frame protocol, panel geometry,
refresh policy, charger status, and fail-closed REGOUT0 policy. The nRF52833
SPI, SAADC, watchdog, S140 BLE, flash store, and signed DFU integrations are not
implemented. Do not treat a successful cross-build as working device firmware.

## What runs today

- `src/boot.rs`: one-time UICR REGOUT0 policy. An erased device is programmed
  for a 3.0 V VDD rail and reset; a conflicting persistent setting fails closed.
- `src/protocol.rs`: the versioned, resumable BLE frame-transfer state machine
  with exact bounds, byte alignment, length, CRC-32, conflicting-ID, durable
  commit, and replay checks.
- `src/panel.rs`: geometry and the SSD1677 command set for the 480 x 800
  portrait GDEM0397T81P panel, including byte-aligned partial-refresh windows.
  Host-tested.
- `src/power.rs`: battery-only state-of-charge estimate, BQ25185 status
  decoding, connection interval selection, and refresh safety gates.
- `src/main.rs`: the bare-metal entry point and REGOUT0 programming path. It
  enters WFI after the early power check until the peripheral drivers land.
  Target builds require the explicit `bringup-stub` feature so this inert image
  cannot be mistaken for release firmware.

## Target

- MCU: Nordic nRF52833 (Cortex-M4F, 128 KiB RAM), target `thumbv7em-none-eabihf`,
  shipped as a pre-certified Raytac MDBT50Q-512K module. The 48 KiB mono
  framebuffer for the 480x800 panel needs the 52833's RAM.
- BLE stack: S140 7.3.0. The linker reserves 156 KiB for S140, two 160 KiB
  application slots, 32 KiB for the planned signed bootloader, and one 4 KiB
  state page. It reserves 31 KiB of RAM for S140. Recalculate both reservations
  after final GATT, L2CAP, MTU, DLE, update, and connection settings.
- Flashing: SWD test pads. There is no USB port; the cargo runner is `probe-rs`.

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

# Inert bring-up image: cross-build and lint for CI only.
cargo build --release --target thumbv7em-none-eabihf --features bringup-stub
cargo clippy --target thumbv7em-none-eabihf --features bringup-stub -- -D warnings

# Provision REGOUT0 on a blank module over SWD. This image starts at address 0
# and must not be combined with S140.
cargo run --release --target thumbv7em-none-eabihf --features factory-bringup
```

The `bringup-stub` image starts at S140's application origin, `0x27000`. To run
it, first flash the exact S140 7.3.0 image and then flash the application. CI
checks every file-backed ELF segment against its assigned flash interval. The
`--nmagic` linker flag prevents ELF page alignment from creating a loadable
segment inside the SoftDevice region.

CI runs the same checks in [`.github/workflows/inkbot-magsafe.yml`](../.github/workflows/inkbot-magsafe.yml).
Like `inkbot-esp32`, this crate is excluded from the shared Rust job in
`test.yml` because it cross-compiles to a bare-metal target.
