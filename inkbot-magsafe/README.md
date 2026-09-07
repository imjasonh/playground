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
refresh policy, charger configuration, and SYS conversion. The nRF52833
SPI, SAADC, watchdog, S113 BLE, flash store, and signed DFU integrations are not
implemented. Do not treat a successful cross-build as working device firmware.

## What runs today

- `src/charger.rs`: ordered BQ25186 safety-register writes and exact readback
  checks that must pass before hardware can enable charging.
- `src/protocol.rs`: the versioned, resumable BLE frame-transfer state machine
  with exact bounds, byte alignment, length, CRC-32, conflicting-ID, durable
  commit, and replay checks.
- `src/panel.rs`: geometry and the SSD1677 command set for the 480 x 800
  portrait GDEY0397T81P panel, including byte-aligned partial-refresh windows.
  Host-tested.
- `src/power.rs`: battery-only state-of-charge estimate, BQ25186 configuration,
  SYS-divider conversion, connection parameters, and refresh safety gates.
- `src/main.rs`: the bare-metal entry point. It enters WFI until the peripheral
  drivers land.
  Target builds require the explicit `bringup-stub` feature so this inert image
  cannot be mistaken for release firmware.

## Target

- MCU: Nordic nRF52833 (Cortex-M4F, 128 KiB RAM), target `thumbv7em-none-eabihf`,
  shipped as a pre-certified Raytac MDBT50Q-512K module. The 48 KiB mono
  framebuffer for the 480x800 panel needs the 52833's RAM.
- BLE stack: S113 7.3.0. The linker reserves 112 KiB for S113, a 176 KiB
  application slot, a 180 KiB update slot, an 8 KiB settings journal, 32 KiB
  for the planned signed bootloader, and one 4 KiB state page. It provisionally
  reserves 32 KiB of RAM for S113. Recalculate RAM after final GATT, L2CAP, MTU,
  DLE, and connection settings.
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

```

The `bringup-stub` image starts at S113's application origin, `0x1c000`. To run
it, first flash the exact S113 7.3.0 image and then flash the application. CI
checks every file-backed ELF segment against its assigned flash interval. The
`--nmagic` linker flag prevents ELF page alignment from creating a loadable
segment inside the SoftDevice region.

CI runs the same checks in [`.github/workflows/inkbot-magsafe.yml`](../.github/workflows/inkbot-magsafe.yml).
Like `inkbot-esp32`, this crate is excluded from the shared Rust job in
`test.yml` because it cross-compiles to a bare-metal target.
