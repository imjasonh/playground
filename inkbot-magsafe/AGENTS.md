# Agent guide: inkbot-magsafe

Firmware and hardware for a MagSafe-attached 4-inch BLE e-ink tile, phone-first
and battery-first. Read [`README.md`](README.md) for the build loop and
[`../docs/inkbot-magsafe-design.md`](../docs/inkbot-magsafe-design.md) for the
product and circuit design. This is a scaffold: pure logic is implemented and
tested; nRF52833 bring-up and BLE are stubbed.

## Contracts

- **The library is host-testable.** `src/lib.rs` is `#![cfg_attr(not(test),
  no_std)]`, so keep the interesting logic in plain modules (`protocol`,
  `panel`, `power`) that build and test on the host. Do not reach for hardware
  in the library.
- **Bare-metal deps are target-gated.** ARM-only crates (`cortex-m`,
  `cortex-m-rt`, `panic-halt`) live under `[target.'cfg(target_os = "none")'
  .dependencies]`. Do not move them to the plain `[dependencies]` table or the
  host build pulls the ARM runtime and breaks.
- **The binary compiles on host and target.** `src/main.rs` gates the firmware
  module on `cfg(target_os = "none")` and provides an empty host `main`. Keep
  both paths building.
- **No connector.** Charging is wireless (Qi RX); updates are BLE DFU; recovery
  is SWD test pads. Do not add a USB port to the design; it was considered and
  dropped (see the design doc).
- **`[lints.rust] unused = "deny"`.** Unused code fails the build. Do not
  `#[allow(dead_code)]` to keep dead methods; delete them.
- **Toolchain is pinned.** `rust-toolchain.toml` sets stable plus the
  `thumbv7em-none-eabihf` target. The nRF52833 uses S140 for BLE. Keep the
  application flash and RAM origins synchronized with the exact S140 build and
  enabled BLE features.

## CI

`inkbot-magsafe` is excluded from `discover-rust-apps.sh` (same reason as
`inkbot-esp32`: it cross-compiles to a bare-metal target that the shared stable
Rust job cannot build). The dedicated
[`inkbot-magsafe.yml`](../.github/workflows/inkbot-magsafe.yml) workflow runs
host tests plus the ARM cross-build on changes under `inkbot-magsafe/`.

## Local commands

```bash
cd inkbot-magsafe
cargo test                                          # host logic tests
cargo clippy --all-targets -- -D warnings           # host lints
cargo build --release --target thumbv7em-none-eabihf # firmware
```
