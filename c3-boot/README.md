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
| `verify` (`c3-verify`) | The slot manifest, image header and segment rules, boot-state record, key-set chain, trust-root blob, and security-level rules. Pure `no_std` functions with no heap, no `unsafe`, and checked arithmetic and indexing. It isn't a complete slot verifier yet |
| `crypto` (`c3-crypto`) | Signature checks. Ed25519 enforces the plan's strict rules on top of a provisional `ed25519-dalek` backend, until phase 0 picks the implementation that phase 7 proves |

Not done yet:

- The Sigstore checks: the bundle container, the Rekor checkpoint, inclusion
  proof, and canonical JSON entry, the X.509 and CMS subsets, and ECDSA
  P-256 and P-384.
- The function that composes every check into one slot decision, the
  plan's `accept`.
- The bootloader crate, including the four genesis trust-root keys, which
  only exist as test seeds today.
- The `c3-ota` host tool.

These come in later phases. Until
the P-384 code lands, the blob parser checks only that each P-384 key starts
with the uncompressed-point prefix. Nothing uses those keys yet, and the
on-curve check that `docs/formats.md` requires arrives with the code that
uses them.

## Build and test

```bash
cd c3-boot
cargo fmt --check
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked
cargo build --locked --release --target riscv32imc-unknown-none-elf -p c3-verify -p c3-crypto
```

`rust-toolchain.toml` pins Rust 1.99.1 and the RISC-V target. The proofs cover
the machine code that this exact compiler produces, so change the pin only
together with the pinned image digest.

## Hardware

No board is needed yet. Constants that come from Espressif's documentation
are marked **(hardware)** in `docs/formats.md`, and the plan lists how each
one gets checked on a real board.
