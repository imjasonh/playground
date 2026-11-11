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
| Boot time for two slot checks with 16-link chains **(hardware)** | Not measured on a board. The RV32 model counts about 135 million instructions for one full slot check; see [Boot cost on the RV32 model](#boot-cost-on-the-rv32-model) |
| Software SHA-256 over a full 1,920 KiB slot **(hardware)** | Not measured |
| eFuse controller lock against machine-mode writes **(hardware)** | Not tested. A release blocker |

## Boot cost on the RV32 model

The machine-code proofs are about the compiled image, so they don't change
how fast it runs. A proof only makes a difference to speed when it moves
the code to a version that is easier to prove and slower. This section
tracks the image's size and speed so that such a trade shows up.

The Lean RV32 model (`c3-boot-proofs`' `boot-sim`) runs the burns-off
bootloader image on the scenarios that `qemu/boot-lockstep.sh` checks, and
counts the instructions each boot runs. Measured on 2026-11-11 with the
image pinned in `bootloader/dev-image.sha256` before the proof-friendly
build settings below (SHA-256
`4b0fe03668079f6a6bf085aae436104cc27d8d057f53a9e37ab4f02ef6f04cf0`):

| Boot | Instructions | At 160 MHz, one cycle each |
| --- | --- | --- |
| Slot signed by another workflow, rejected | 68,413,457 | 428 ms |
| Slot with a stale timestamp, rejected | 134,326,927 | 840 ms |
| Trial boot of a valid slot, then the jump | 134,646,260 | 842 ms |

One cycle per instruction is a lower bound. The bootloader runs from SRAM,
so instruction fetches don't miss a cache, but loads, taken branches,
multiplies, and flash reads through the ROM add cycles. A board has to
measure the real time. **(hardware)**

With `BOOT_SIM_PROFILE` set, `boot-sim` writes how many instructions ran at
each address, and `c3-boot-proofs/scripts/boot-profile.py` groups them by
function and crate. For the trial boot, by the crate that each function's
symbol names first:

| Crate | Code (bytes) | Instructions run | Share |
| --- | --- | --- | --- |
| `crypto_bigint` | 9,544 | 87,062,408 | 64.7% |
| `compiler_builtins` (`memcpy`, `memset`) | 534 | 13,636,050 | 10.1% |
| `curve25519_dalek` | 12,804 | 11,176,686 | 8.3% |
| `sha2` | 47,680 | 8,673,530 | 6.4% |
| Outlined helpers | 2,366 | 4,230,372 | 3.1% |
| `p256` | 4,790 | 3,684,725 | 2.7% |
| `c3_bootloader` | 5,646 | 2,325,761 | 1.7% |
| `p384` | 528 | 2,270,922 | 1.7% |
| Everything else | 44,668 | 1,585,806 | 1.2% |
| **Total** | **128,560** | **134,646,260** | |

Findings:

- **P-384 dominates.** `crypto_bigint`'s 12-word Montgomery multiplication
  and squaring (`mul_montgomery_form::<12>`, `square_montgomery_form::<12>`)
  run 58.5 million instructions, 43 percent of the boot, for the P-384
  signatures of the timestamp authority. A faster P-384 field
  multiplication is the main lever on boot time.
- **SHA-2 is large but cheap at run time.** `sha2` is 37 percent of the
  code and 6 percent of the instructions. SHA-512's unrolled compression
  function alone is 35.7 KB for Ed25519's hashes.
- **`memcpy` and `memset` run 10 percent of the instructions**, mostly
  moving and zeroing big-number temporaries.

### After the proof-friendly build settings

`.cargo/config.toml` builds the bootloader without LLVM's machine outliner
and with `sha2`'s compact backend, and `root_from_inclusion` is kept out of
line, so that the machine-code proofs have fewer and smaller functions (see
`c3-boot-proofs/docs/throughput.md`). The image shrank from 133,392 to
89,296 bytes, and its code from 42,490 to 28,526 instructions. The trial
boot of a valid slot runs 136,797,349 instructions, 2.2 percent more, at
least 855 ms at 160 MHz:

| Crate | Code (bytes) | Instructions run | Share |
| --- | --- | --- | --- |
| `crypto_bigint` | 10,326 | 88,869,532 | 65.0% |
| `compiler_builtins` (`memcpy`, `memset`) | 534 | 13,780,156 | 10.1% |
| `sha2` | 2,610 | 12,681,985 | 9.3% |
| `curve25519_dalek` | 12,958 | 11,333,429 | 8.3% |
| `p256` | 4,856 | 3,866,865 | 2.8% |
| `p384` | 542 | 2,328,079 | 1.7% |
| `c3_bootloader` | 6,188 | 2,325,911 | 1.7% |
| Everything else | 47,066 | 1,610,768 | 1.2% |
| **Total** | **84,470** | **136,797,349** | |

The compact `sha2` runs about 4 million more instructions than the
unrolled one, and code that the outliner had moved into helpers runs about
1.3 million fewer.

To reproduce, build the scenarios and run the lockstep check, then profile
one boot:

```bash
bash qemu/scenarios.sh /tmp/scen
bash qemu/boot-lockstep.sh /tmp/scen /tmp/boot
nm="$(rustc --print sysroot)/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-nm"
elf=target/riscv32imc-unknown-none-elf/release/c3-bootloader
halt="$("${nm}" -C "${elf}" | awk '$3 == "c3_bootloader::halt" { print $1 }')"
BOOT_SIM_PROFILE=/tmp/trial.prof ../c3-boot-proofs/.lake/build/bin/boot-sim \
  /tmp/boot/trial.flash /tmp/boot/trial.efuse "${halt}" >/dev/null
python3 ../c3-boot-proofs/scripts/boot-profile.py /tmp/trial.prof "${elf}" "${nm}"
```

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
