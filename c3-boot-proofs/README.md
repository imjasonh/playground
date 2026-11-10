# c3-boot-proofs

c3-boot-proofs holds the Lean proofs for c3-boot, the verified OTA
bootloader that [`docs/esp32c3-verified-ota-plan.md`](../docs/esp32c3-verified-ota-plan.md)
describes. This first part needs no machine model: it specifies the
bootloader's decision logic in Lean and proves the plan's boot-safety
theorems about it, over traces with power loss.

## What's proved

`C3BootProofs/Spec/` is the executable specification. Each definition
follows the Rust code it names:

- `Level.lean`: the security level, eFuse burns, the bit-by-bit raise, the
  burn target, and the level rules (`c3_verify::level`,
  `efuse::raise_level`).
- `BootState.lean`: the boot-state record's transitions and the trial plan
  (`c3_verify::bootstate`).
- `Boot.lean`: `decideBoot`, the boot decision (`c3_verify::boot::decide`).
- `TrustRoot.lean`: key-set chains and trust-root blobs: each link signed by
  two distinct keys of the set before it at a strictly higher level, and the
  blob signed the same way by the chain's last set (`c3_verify::chain`,
  `keys`, and `trustroot`). Signature verification is a parameter; the
  Ed25519 proofs are the plan's cryptography phase.
- `Formats.lean`: decoders for the boot-state record (including CRC-32 and
  the newer-copy rule), the slot manifest, and the image header and segment
  table (`c3_verify::bootstate`, `manifest`, and `image`).

`C3BootProofs/Model/RV32.lean` is an executable model of RV32IMC, the
ESP32-C3's instruction set: registers, the program counter, byte memory, a
decoder for every RV32I, M, and 16-bit C instruction, and a step function.
Encodings that would trap make `step` return `none`; it doesn't model CSRs,
interrupts, or misaligned accesses yet. This is the plan's compact
semantics, which the machine-code proofs will run the bootloader image on.

`C3BootProofs/Theorems/Trace.lean` models a device as its eFuse field, its
boot-state record, and the result of checking each slot. A trace mixes
arbitrary flash and record writes by an attacker, boots that lose power and
burn arbitrary eFuse bits, and boots that run to the jump. Over every such
trace, it proves the following:

| Theorem | Statement |
| --- | --- |
| `efuse_monotone` | No step lowers the security level |
| `rollback` | If a step ends with the level at L, every jump in that step or a later one goes to a slot whose level is at least L |
| `boots_safe` | Every jump goes to a slot accepted at the level the bootloader read, after the level reached that slot's burn target |
| `availability` | When some slot is accepted, a boot can run to a jump |
| `mapped_pages_signed` | For an accepted image header, every 64 KiB page the cache maps for a flash segment ends inside the signed image |
| `trust_root_monotone` | When the slot results come from the trust-root checks, every jump goes to a slot whose chain is authorized from the genesis keys, whose blob the chain's last key set signed, whose chain level is at most the blob's level, whose image security version equals the blob's level, and whose blob level is at least the eFuse level |

A boot that halts, including the bootloader's halt when an eFuse bit fails
to program, is an `interrupted` step, which may leave any bits and any
record. So `availability` assumes the eFuses program and the boot isn't cut
short; the other theorems hold either way. Where the Rust code writes the
record relative to the slot checks is outside this model, because an
interrupted boot may leave any record. `c3-verify`'s `boot::tests` pin that
order.

`C3BootProofs/Audit.lean` pins each theorem's axioms (`propext` and
`Quot.sound`) and proves that admissible traces with a jump exist, including
one whose slot results come from the trust-root checks.

The model is the production bootloader configuration, which burns eFuses
(`C3_EFUSE_BURN=on`) and halts when a burn fails. A test build that doesn't
burn, or that boots after a failed burn, can jump before the level reaches
the target, so `boots_safe`'s second half doesn't hold for it; `rollback`
and `efuse_monotone` still do.

These theorems cover the decision logic only. The slot checks
(signatures, the key-set chain, and the Sigstore bundle) are abstracted as
the `slots` function, which an attacker's flash writes may set to anything,
so nothing here shows that an accepted slot is authentic. That, and
connecting these theorems to the RISC-V binary, is the plan's machine-code
and cryptography work.

## Differential test

`lake exe spec-vectors` prints the specification's answers for 171,235
inputs: every `SECURE_VERSION` value, every level-rule input, every burn
target, and the boot decision for 216 records, 4 eFuse levels, and 25 pairs
of slot results. `c3-boot/verify/examples/spec_vectors.rs` prints the Rust
code's answers in the same format, and CI requires the two to be identical.

`c3-boot/ota/examples/trust_vectors.rs` builds 20,000 key-set chains and
trust-root blobs with real Ed25519 signatures. Each signature list starts
honest, and about a third get one fault: a corrupted signature, a wrong
signer or message, a repeated or out-of-range index, too few signatures, or
the wrong order. Key sets, levels, and security versions vary too. It prints
each case with `c3-verify`'s verdict. `lake exe trust-check` reads those
lines and evaluates `acceptContents`, counting a signature valid exactly
when it is uncorrupted and made by that key over that message. CI requires
the verdicts to match; about a third of the cases are accepted. The
Sigstore checks and the trust-root blob's byte format are outside this
comparison; `c3-boot`'s conformance and mutation tests cover them.

`c3-boot/verify/examples/decode_vectors.rs` builds 20,000 boot-state
records, 5,000 pairs of records, 20,000 manifests, and 20,000 image headers.
About half are valid; the rest have one change: a field set to a boundary
value or nearby number, a flipped bit, or a truncation, with the record's
CRC often recomputed so the field rules are reached. It prints each input
with `c3-verify`'s result, and `lake exe decode-check` must print the same
results.

`c3-boot/qemu/rv-lockstep.sh` tests the RV32 model against Espressif's
QEMU. `c3-ota`'s `rv_cases` example generates random sequences of 28
instructions or groups each, mixing 16- and 32-bit encodings, with ALU and
multiply-divide operations on edge-case values, aligned loads and stores
into a fixed buffer, and forward branches, jumps, and `auipc`/`jalr` pairs.
The `c3-rvtest` firmware runs each in QEMU from a known register and memory
state and prints what it ends with, and `lake exe rv-check` must get the
same registers and buffer from the same start. CI runs 3,000 cases.

`c3-boot/qemu/boot-lockstep.sh` runs the bootloader image itself on the
model. `lake exe boot-sim` loads the image from a flash file the way the ROM
does and runs it, with the ROM functions it calls (flash read, write, and
erase, cache control, and `ets_printf`) as hooks and eFuse reads from an
eFuse file. `c3-boot/qemu/rsp-trace.py` runs the same flash in QEMU through
its GDB server. Both print each ROM call with its arguments and how the
boot ended, and the flash the model leaves must match QEMU's byte for byte.
CI boots three scenarios: two rejected slots, and a trial boot that
rewrites the boot state and jumps to the new slot. That's about 336 million
instructions on the model, through SHA-256, ECDSA, Ed25519, and the
parsers as compiled. The bootloader uses no CSR or system instructions.

`scripts/decode-vs-llvm.py` checks which encodings the decoder accepts
against LLVM's RISC-V disassembler (RV32IMC, from the pinned Rust
toolchain's `llvm-tools`): all 49,152 16-bit encodings and 200,000 32-bit
ones weighted toward the modeled opcodes. An encoding the model accepts and
LLVM rejects fails the check, because the model would run an instruction
the hardware traps on. The model leaves out the SYSTEM opcode, `fence.i`,
and `c.ebreak`, and accepts only the FENCE encodings compilers emit.

## Build and test

Install [elan](https://github.com/leanprover/elan), then run:

```bash
cd c3-boot-proofs
lake build
lake exe spec-vectors > /tmp/lean.txt
(cd ../c3-boot && cargo run --release -q -p c3-verify --example spec_vectors) > /tmp/rust.txt
diff /tmp/lean.txt /tmp/rust.txt
(cd ../c3-boot && cargo run -q -p c3-ota --example trust_vectors) > /tmp/rust-trust.txt
lake exe trust-check < /tmp/rust-trust.txt | diff - /tmp/rust-trust.txt
(cd ../c3-boot && cargo run -q -p c3-verify --example decode_vectors) > /tmp/rust-decode.txt
lake exe decode-check < /tmp/rust-decode.txt | diff - /tmp/rust-decode.txt
(cd ../c3-boot && QEMU=/path/to/qemu-system-riscv32 bash qemu/rv-lockstep.sh)
python3 scripts/decode-vs-llvm.py .lake/build/bin/rv-decode \
  "$(cd ../c3-boot && rustc --print sysroot)/lib/rustlib/x86_64-unknown-linux-gnu/bin"
```

`lean-toolchain` pins Lean 4.34.0, the version that
[`google-deepmind/code-verification`](https://github.com/google-deepmind/code-verification)
uses. The project has no dependencies.
