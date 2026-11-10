# Phase 0 measurements

This page records the phase 0 measurements from
[the verification plan](../../docs/esp32c3-verified-ota-plan.md) and the
decisions they support. Rows marked **(hardware)** wait for a development
board. Until then, the plan proceeds on the assumption that the hardware
behaves as Espressif documents it.

## Toolchain

- Rust 1.99.1, target `riscv32imc-unknown-none-elf`, pinned in
  `rust-toolchain.toml`.
- Espressif's QEMU fork, release `esp-develop-9.2.2-20261109`, which has an
  `esp32c3` machine. It stands in for a board until one is available.

## Code size of candidate cryptography crates

Each figure is the size of a `no_std` RV32IMC binary that verifies one
signature or computes the listed digests on data the compiler can't see,
built with `lto = true`, `codegen-units = 1`, and `panic = "abort"`. The
empty binary is 20 bytes of `.text`, so the figures are the cost of each
crate. Measured on 2026-11-10.

| Crate and version | Operation | `.text` at `opt-level = "s"` | `.text` at `opt-level = "z"` | `.rodata` |
| --- | --- | --- | --- | --- |
| `p256` 0.14.0 | ECDSA verification from a SEC1 key | 22,602 | 21,006 | about 700 |
| `p384` 0.14.0 | ECDSA verification from a SEC1 key | 20,762 | 17,656 | about 1,200 |
| `ed25519-dalek` 3.0.0 | `verify_strict` | 56,632 | 56,420 | about 1,100 |
| `ed25519-compact` 2.6.1 | Verification | 841,628 | Not measured | about 1,700 |
| `sha2` 0.11.1 | SHA-256 and SHA-384 | 48,494 | 48,620 | about 1,000 |
| `p256`, `p384`, `ed25519-dalek`, and `sha2` together | All of the above | 110,222 | 104,448 | about 3,500 |

Findings:

- `ed25519-compact` is ruled out by size.
- The audited crates together need about 104 to 110 KB of code before any
  parser or bootloader code.
- `sha2` unrolls its compression loops, which accounts for most of its size.
  A loop-based SHA-2 is typically a few kilobytes.
- `ed25519-dalek` is about half the total, and much of it is generic code
  that a proof would have to cover.

The phase 0 comparison against a minimal implementation, built from
fiat-crypto field arithmetic, complete formulas, and loop-based SHA-2, is
still open. The minimal design is expected to be smaller and easier to
prove, and the decision waits for its measurement.

## Bootloader memory budget

ESP-IDF's ESP32-C3 bootloader linker script gives its bootloader about 58 KB
of SRAM: 10 KB of code, 28 KB of loader code, and 20 KB of data, all below
`0x3FCDC710`, with an 8 KB stack margin. That is a convention, not a limit
of the chip. The ROM uses memory above `0x3FCDC710` while it runs, and the
application's RAM segments are loaded below the bootloader.

c3-boot uses a different split, defined in [formats.md](formats.md):

| Region (data-bus addresses) | Size | Use |
| --- | --- | --- |
| `0x3FC80000` through `0x3FCA0000` | 128 KiB | Application RAM segments that the bootloader loads |
| `0x3FCA0000` through `0x3FCDC710` | About 241 KiB | Bootloader code, data, stack, and buffers |

The application runs mostly from flash through the cache, so its loaded RAM
segments are small. After the jump, the application can reuse all of SRAM.

The flash layout reserves 160 KiB for the bootloader image. The first
complete prototype, built on 2026-11-10 with the provisional crypto crates at
`opt-level = "z"`, has 128,904 bytes of code and 4,544 bytes of read-only
data, and keeps its slot buffers on a 95 KiB stack.

| Item | Status |
| --- | --- |
| The ROM loads a bootloader image of this size into this region **(hardware)** | Assumed from the technical reference manual and ESP-IDF |
| The ROM doesn't use memory below `0x3FCDC710` after it jumps to the bootloader **(hardware)** | Assumed from ESP-IDF's linker script |
| Boot time for two slot checks with 16-link chains **(hardware)** | Not measured. QEMU instruction counts come first |
| Software SHA-256 over a full 1,920 KiB slot **(hardware)** | Not measured |
| eFuse controller lock against machine-mode writes **(hardware)** | Not tested. A release blocker |

## Findings from QEMU

Booting in Espressif's QEMU (`esp-develop-9.2.2-20261109`) found two bugs
that would also have failed on silicon:

- The ROM flash functions refuse addresses past the flash size the ROM
  holds, which doesn't cover slot B at `0x210000`. The bootloader now sets
  that size to 4 MiB at startup, as ESP-IDF's bootloader does.
- `SECURE_VERSION` was read from `RD_REPEAT_DATA4`. It is block 0 word 4,
  which reads through `RD_REPEAT_DATA3`. The device would have seen level 0
  forever, and the first level raise would have halted every boot.

QEMU models the eFuse controller and the ROM, but not their timing or
failure modes, so both fixes still need checking on a board. (hardware)
