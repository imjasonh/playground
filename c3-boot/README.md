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
| `verify` (`c3-verify`) | Every slot check, composed by `accept::accept_slot`: the slot manifest, image header and segment rules, boot-state record, key-set chain, trust-root blob, security-level rules, bundle container, leaf certificate, timestamp token, checkpoint, Merkle inclusion proof, and Rekor entry. Pure `no_std` functions with no heap, no `unsafe`, and checked arithmetic and indexing |
| `crypto` (`c3-crypto`) | SHA-256, SHA-384, ECDSA P-256 and P-384 verification, and strict Ed25519 verification. The rules are enforced explicitly on top of provisional backends (`sha2`, `p256`, `p384`, `ed25519-dalek`), until phase 0 picks the implementation that phase 7 proves |
| `bootloader` (`c3-bootloader`) | The second-stage bootloader for `riscv32imc-unknown-none-elf`: ROM flash and cache hooks, image hashing, boot-state writes, the security-level burn, RAM loading, MMU mapping, and the jump |
| `ota` (`c3-ota`) | The host tool: packs images, converts Sigstore bundles, builds and signs chain links and blobs from a `trusted_root.json`, assembles slots and flash images, and checks a slot with `verify` |
| `demo-app` (`c3-demo-app`) | An untrusted demo application that prints its slot, reads a flash-mapped message, and confirms its slot |

`ota/tests/conformance.rs` runs the Sigstore conformance bundles in
`testdata/conformance/` through the device's checks.

Not done yet:

- The eFuse lock is a no-op. Which protection unit can lock the eFuse
  controller is a phase 0 hardware question, and the lock is a release
  blocker.
- eFuse programming timing, the ROM's initial state, and the memory layout
  are from Espressif's documentation and haven't run on silicon.
- The production genesis keys. The bootloader build requires `C3_GENESIS`,
  set to a key file or to `dev` for the public development keys in
  `testdata/keys/`. A `dev` build warns on every boot.
- The release and trust-root rotation workflows, and the QEMU scenario
  runner.

## Build and test

```bash
cd c3-boot
cargo fmt --check
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked
C3_GENESIS=dev cargo build --locked --release --target riscv32imc-unknown-none-elf \
  -p c3-verify -p c3-crypto -p c3-bootloader -p c3-demo-app
```

To boot the bootloader in Espressif's QEMU fork, build a flash image with
`c3-ota bootloader-image` and `c3-ota flash`, then run
`qemu-system-riscv32 -nographic -machine esp32c3` with the flash image as an
`mtd` drive and a 1 KiB eFuse file.

`rust-toolchain.toml` pins Rust 1.99.1 and the RISC-V target. The proofs cover
the machine code that this exact compiler produces, so change the pin only
together with the pinned image digest.

## Hardware

No board is needed yet. Constants that come from Espressif's documentation
are marked **(hardware)** in `docs/formats.md`, and the plan lists how each
one gets checked on a real board.
