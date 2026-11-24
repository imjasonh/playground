# c3-boot

c3-boot is the over-the-air (OTA) update verifier for an ESP32-C3 bootloader,
written so that its compiled RISC-V machine code can be proved correct in
Lean. The design, the theorems, and the phases are in
[`docs/esp32c3-verified-ota-plan.md`](../docs/esp32c3-verified-ota-plan.md).
Every byte the bootloader reads is defined in
[`docs/formats.md`](docs/formats.md), and phase 0 measurements are in
[`docs/measurements.md`](docs/measurements.md).

## Crates

| Crate | Contents |
| --- | --- |
| `verify` (`c3-verify`) | Every slot check, composed by `accept::accept_slot`: the slot manifest, image header and segment rules, boot-state record, key-set chain, trust-root blob, security-level rules, bundle container, leaf certificate, timestamp token, checkpoint, Merkle inclusion proof, and Rekor entry. Pure `no_std` functions with no heap, no `unsafe`, and checked arithmetic and indexing. The `tuf` feature adds the checks that `TODO.md` plans to anchor trust with: strict and canonical JSON, Sigstore's TUF root chain and targets, the keys in `trusted_root.json`, and `tuf_slot::accept_slot`. The bootloader doesn't turn it on |
| `crypto` (`c3-crypto`) | SHA-256, SHA-384, ECDSA P-256 and P-384 verification, and strict Ed25519 verification. The rules are enforced explicitly on top of provisional backends (`sha2`, `p256`, `p384`, `ed25519-dalek`), until phase 0 picks the implementation that phase 7 proves |
| `bootloader` (`c3-bootloader`) | The second-stage bootloader for `riscv32imc-unknown-none-elf`: ROM flash and cache hooks, image hashing, boot-state writes, the security-level burn, RAM loading, MMU mapping, and the jump |
| `ota` (`c3-ota`) | The host tool: packs images, converts Sigstore bundles, builds and signs chain links and blobs from a `trusted_root.json`, assembles slots and flash images, and checks a slot with `verify`. `tuf-root`, `tuf-package`, `tuf-verify`, and `tuf-accept` pin a TUF root, package Sigstore's TUF metadata (`testdata/tuf/fetch.sh` downloads it), and check it with the device's code |
| `demo-app` (`c3-demo-app`) | An untrusted demo application that prints its slot, reads a flash-mapped message, and confirms its slot |
| `rvtest` (`c3-rvtest`) | Firmware for the lockstep test of the Lean RV32 model: runs generated instruction sequences in QEMU and prints the registers and memory they end with (`qemu/rv-lockstep.sh`) |

`fakestore/` is a Go program, not a crate: a test-only Sigstore that signs
files with the same bundle profile that Sigstore issues to GitHub Actions.
See [`fakestore/README.md`](fakestore/README.md).

`ota/tests/conformance.rs` runs the Sigstore conformance bundles in
`testdata/conformance/` through the device's checks, and check that a
change to any identity-policy field or to a Fulcio, log, or timestamp
window rejects the real bundle. `ota/tests/mutation.rs`
flips one bit in each byte of a valid slot's manifest, image, bundle, chain,
and blob, and checks that every change is rejected, except in the timestamp
authority's embedded certificate, which nothing reads.

Not done yet:

- The eFuse lock is a no-op. Which protection unit can lock the eFuse
  controller is a phase 0 hardware question, and the lock is a release
  blocker. Until it exists, a signed application can burn any eFuse.
- eFuse programming timing at 160 MHz is unchecked. The bootloader
  programs `SECURE_VERSION` with whatever timing the eFuse controller's
  registers hold at boot, and the timing depends on the bus clock. At
  160 MHz the bus clock is 80 MHz, not the ROM's 20 MHz, so a raise might
  program out of specification. Either
  raise the level before switching clocks, switch back to the crystal for
  the raise, or set the timing registers for 80 MHz as ESP-IDF's
  `efuse_hal_set_timing` does. Test the choice on a board set aside for
  eFuse tests.
- **Demo builds are valid releases, on purpose for now.** `c3-release.yml`
  signs the demo application under the release identity on every push to
  `main`, so each demo build is a valid image at security version 0. Once a
  simple demo has been tested on hardware, this tightens so that devices
  accept only released images.
- Retired trust-root key sets keep the power to sign blobs at or above the
  current level, because the device keeps no record of key sets. **Retired
  keys are destroyed**, the genesis keys included after the first rotation;
  see the plan's "Rotating trust-root keys".
- eFuse programming timing, the ROM's initial state, and the memory layout
  are from Espressif's documentation and have run only in QEMU, not on
  silicon.
- The production genesis keys. The bootloader build requires `C3_GENESIS`,
  set to a key file or to `dev` for the public development keys in
  `testdata/keys/`. A `dev` build warns on every boot.
- Offline tooling for signing chain links and trust-root blobs with
  hardware-held keys. `c3-ota link` and `c3-ota blob` take seed files.

## Testing on boards

Burning an eFuse can't be undone, and nothing a test does should stop a
board from taking updates. The bootloader never enables Secure Boot or
flash encryption and never disables USB download mode, so a board can
always be reflashed over USB. Its only permanent action is raising
`SECURE_VERSION`, which two build settings control:

- `C3_EFUSE_BURN` is `off` by default. An `off` build has no eFuse
  programming code: it logs `eFuse burns off; not raising security level
  to N` and boots the slot. Build with `C3_EFUSE_BURN=on` only for a board
  set aside for eFuse tests, because each raise uses one of its 16 levels
  for good and stops every lower image from booting.
- A build with `C3_GENESIS=dev` and `C3_EFUSE_BURN=on` doesn't halt when a
  raise fails. It logs `raise failed; booting without it` and boots the
  slot, so a board whose `SECURE_VERSION` field was damaged or
  write-disabled still updates.

A build with production genesis keys fails unless `C3_EFUSE_BURN=on`, and
it halts on a failed raise, as the plan and the proofs assume. The QEMU
scenarios build both ways and test both settings.

## Build and test

```bash
cd c3-boot
cargo fmt --check
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked
C3_GENESIS=dev cargo build --locked --release --target riscv32imc-unknown-none-elf \
  -p c3-verify -p c3-crypto -p c3-bootloader -p c3-demo-app
```

The default test build of the bootloader image (development keys, no eFuse
burns) is reproducible on x86-64 Linux, where CI builds it: it gives the
digest in `bootloader/dev-image.sha256`, and `bootloader/check-digest.sh`
checks it in CI. Builds on macOS and on arm64 Linux give other digests, so
regenerate the pin in an x86-64 Linux container. A change to the bootloader, `c3-verify`, `c3-crypto`, a dependency, or
the toolchain changes the digest; run `bootloader/check-digest.sh --update`
to pin the new one.

`rust-toolchain.toml` pins Rust 1.99.1 and the RISC-V target. The proofs cover
the machine code that this exact compiler produces, so change the pin only
together with the pinned image digest.

## Fuzz

`fuzz/` has five [cargo-fuzz](https://github.com/rust-fuzz/cargo-fuzz)
targets: the format decoders, the key-set chain and trust-root blob, the
Sigstore bundle checks against a fixed trust root, whole slots through
the bootloader's checks, and the TUF checks (JSON, the TUF part from
Sigstore's root 5, and `trusted_root.json`). Fuzz builds turn on overflow checks, so an
arithmetic slip that the lints missed shows up as a crash. `fuzz/seed.sh`
builds seed inputs from the mutation test's fixtures, and `fuzz/run.sh`
fuzzes each target for `FUZZ_SECONDS` seconds (30 by default) with a pinned
nightly toolchain. The `c3-boot` workflow runs it on every change.

```bash
rustup toolchain install nightly-2026-11-09 --profile minimal
cargo +nightly-2026-11-09 install cargo-fuzz --locked
bash fuzz/run.sh
```

## Boot in QEMU

`qemu/scenarios.sh` builds the bootloader and three versions of the demo
application, signs each with a new fakestore instance, and boots them in
[Espressif's QEMU](https://github.com/espressif/qemu) through these
scenarios, keeping one flash file and one eFuse file across boots:

1. First boot of slot A, which the application confirms.
1. A slot with one changed image byte, rejected for a bad signature.
1. A trial update to slot B at security level 1, confirmed by the
   application, with no eFuse burn during the trial.
1. The next boot raises the eFuse level to 1, and the level stays 1.
1. Slot A at level 0 is rejected for its level, and slot B boots.
1. A failed trial of a changed slot falls back to slot B.
1. A level 2 slot whose trust root is signed by the retired genesis keys
   is rejected.
1. A level 2 slot from a rotated key set boots on trial, gets confirmed,
   and raises the level to 2.
1. Power cuts (QEMU killed at seeded random points) during trial boots of a
   level 3 update and during a raise from level 3 to 6. A clean boot works
   afterward, and the level never goes down across any boot.
1. A raise from 3 to 6 interrupted after one bit, and one that left a gap
   in the bits, set up by editing the eFuse file. Both finish at 6.
1. A trial that the application never confirms boots three times, then
   the bootloader ends it and boots the preferred slot.
1. A bootloader built without `C3_EFUSE_BURN=on` boots a confirmed level 6
   slot on a level 3 board and leaves the eFuses unchanged.
1. With `SECURE_VERSION` write-disabled, a raise fails, and a development
   build boots the slot anyway.

To run it, install Go and Espressif's QEMU, then run:

```bash
QEMU=/path/to/qemu-system-riscv32 bash qemu/scenarios.sh
```

The serial log of each boot is saved in the work directory, which the script
prints. The `c3-boot` workflow runs the same script, and `qemu/boot.sh` runs
a single boot.

## Releases

`c3-release.yml` signs the demo application with production Sigstore and
boots the signed slot in QEMU. See [`release/README.md`](release/README.md).

## Hardware

Constants that come from Espressif's documentation are marked
**(hardware)** in `docs/formats.md`, and the plan lists how each one gets
checked on a real board.

On an ESP32-C3 v0.4 board, the development build boots a fakestore-signed
slot, maps flash, and jumps to the demo application, which confirms its
slot. The ROM leaves the CPU at 20 MHz and arms timer group 0's and 1's
watchdogs for 1.3 s, and a boot at that speed takes 9.3 s, so the bootloader
first sets its own watchdog budget and switches the CPU to 160 MHz. Then a
boot that checks one slot takes 1.2 s. See `docs/measurements.md`.

Flash a board over USB with `espflash write-bin 0x0 flash.bin`, using a
`flash.bin` from `c3-ota flash` as `qemu/scenarios.sh` builds it. The
console is the board's USB serial port.
