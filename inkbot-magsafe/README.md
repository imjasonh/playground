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
refresh policy, charger configuration, and sensor conversions. The nRF52840
SPI, SAADC, watchdog, S113 BLE, flash store, and signed DFU integrations are not
implemented. Do not treat a successful cross-build as working device firmware.

## What runs today

- `src/charger.rs`: ordered BQ25186 safety-register writes and exact readback
  checks that must pass before hardware can enable charging. Bus, register, and
  live-fault failures drop the external gate. The detached factory flow also
  disables charging before it requests ship mode.
- `src/protocol.rs`: the versioned, resumable BLE frame-transfer state machine
  with exact bounds, byte alignment, length, CRC-32, conflicting-ID, durable
  commit, and replay checks.
- `src/panel.rs`: geometry and the SSD1677 command set for the 480 x 800
  portrait GDEY0397T81P panel. Wire frames use the controller's native
  800 x 480 order, including byte-aligned partial-refresh windows, reversed
  gate addressing, and exact full, fast, partial, power-off, and sleep values.
  Host-tested.
- `src/power.rs`: battery-only state-of-charge estimate, BQ25186 configuration,
  SYS-divider conversion, connection parameters, and refresh safety gates.
- `src/memory.rs` and `src/storage.rs`: nonoverlapping 1 MiB flash regions and
  CRC-protected metadata for alternating 48 KiB frame slots.
- `src/recovery.rs`: the bounce- and timeout-checked physical owner-reset
  gesture for the sealed enclosure.
- `src/main.rs`: the bare-metal entry point. It enters WFI until the peripheral
  drivers land.
  Target builds require the explicit `bringup-stub` feature so this inert image
  cannot be mistaken for release firmware. CI permits that feature only while
  `production-gates.json` classifies the device below `PRODUCTION`; a production
  release must build the target without it.

## Target

- MCU: Nordic nRF52840 (Cortex-M4F, 256 KiB RAM), target
  `thumbv7em-none-eabihf`, shipped as a pre-certified Raytac MDBT50Q-1MV2
  module. Its 1 MiB flash holds equal 256 KiB application and update slots,
  two 48 KiB frame slots, journals, and the signed bootloader region.
- BLE stack: S113 7.3.0. The linker reserves 112 KiB for the MBR and S113 and
  provisionally reserves 32 KiB of RAM for S113. Recalculate RAM after final
  GATT, L2CAP, MTU, DLE, and connection settings.
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
