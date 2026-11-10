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

## Machine-code proofs

`C3BootProofs/Proofs/Crc32.lean` proves `crc32_correct` about the compiled
`c3_verify::bootstate::crc32`, the boot-state record's checksum, as it is in
the bootloader image: 23 instructions with two nested loops, which the
compiler specialized to the record's 28-byte body. With the function's bytes
in memory at any address and the program counter at its first byte, the RV32
model runs it to the return address, memory and every register outside `a0`
through `a6` are unchanged, and `a0` holds the CRC-32 of the 28 bytes at
`a0`. `crc32_spec` restates the result as `C3.crc32`, the byte-format
specification that `decode-check` tests against `c3-verify`.
`exists_crc32_machine` in `Audit.lean` shows the hypotheses can all hold.
`Steps` says some execution gets there; the proof follows the function's
path through both loops to its `ret`.

The proofs are about the pinned image: the default test build with the
development genesis keys. A build with other keys has its own image, and
its functions are covered only if their bytes are the same, which
`extract-functions.py` would show against that image.

`C3BootProofs/Proofs/Reader.lean` proves `readerBytes_correct` about the
compiled `Reader::bytes`, which takes `n` bytes from a bounds-checked
reader. It loads the reader's three words, writes its `Result` through a
pointer, and updates the reader's position. The theorem gives the exact
memory afterward (`bytesMem`) for every input, success and both failures,
with only `a3` through `a5` changed among the registers. Its hypotheses are
that the result and the reader are 4-byte aligned, the return address is
even, and the bytes it stores (the result's 8 bytes and the reader's
position) don't overlap its code. Callers in the image keep both on the
stack or in data memory, which the proofs of those callers will have to
show. `bytesResult_eq`
restates the specification in plain arithmetic: the call succeeds exactly
when `pos + n ≤ len` as natural numbers, so a sum that wraps past 2^32
fails.

`mapped_pages_signed` in `Theorems/Formats.lean` proves that, for an
accepted image header, every 64 KiB page the cache maps for a flash segment
ends inside the signed image.

| Machine-code theorem | Statement, on the RV32 model, about the pinned image's bytes |
| --- | --- |
| `crc32_correct`, `crc32_spec` | The compiled `crc32` returns the CRC-32 of the 28 bytes at `a0` |
| `readerBytes_correct` | The compiled `Reader::bytes` leaves memory exactly as `bytesMem` says, for every input |
| `readerArray4_correct` | The compiled `Reader::array::<4>`, through its call to `Reader::bytes`, restores its frame and leaves memory outside the frame exactly as `array4Mem` says |
| `readerU32_correct` | The compiled `Reader::u32`, through `Reader::array::<4>` and `Reader::bytes`, leaves memory outside its 48 bytes of stack exactly as `u32Mem` says: on success, tag 0 and the 4 bytes at the slice's position as a little-endian word through `out` |
| `save_run`, `restore_run` | Any machine-outlined helper that stores (or loads) a list of registers at offsets from `sp` and returns with `jr t0` does exactly that: memory `saveMem`, or registers `restoreRegs`. `decide` checks each helper's bytes against its list |
| `manifestPart_correct` | The compiled `manifest::part`, through both `Reader::u32` calls and both helpers, restores `sp` and every register but `a0` through `a5` and `t0`, and leaves memory outside its 80 bytes of stack exactly as `partMem` says: the offset, the length, and tag 0 when both reads succeed and `min ≤ length ≤ max`; otherwise tag 1 and `Truncated` or `OutOfRange` |
| `readerMagic_correct` | The compiled `Reader::magic`, through `Reader::array::<4>` and an outlined load helper, returns 0xFFFFFFFF in `a0` when the next 4 bytes equal the magic, `BadMagic` (2) when they don't, and `Truncated` (0) when fewer remain. LLVM passes the magic as its little-endian word `k` in `a1`, so `parse`'s proof shows `k` is "C3SL". The position advances whenever 4 bytes were read |
| `readerU16_correct`, `readerVersion1_correct` | The compiled `Reader::u16` returns its `Result` packed in `a0` (error flag in bit 0, error in bits 8 to 15, value in bits 16 to 31). `Reader::version_1`, through it, returns 0xFFFFFFFF when the version is 1, `BadVersion` (3) when it isn't, and `Truncated` (0) when fewer than 2 bytes remain |
| `reserved_loop`, `readerReserved_correct` | The compiled `Reader::reserved(n)`, for `n` other than 0, through `Reader::bytes` and a loop proved by induction on the bytes left, returns 0xFF when the `n` bytes are zero, `NonzeroReserved` (4) when one isn't, and `Truncated` (0) when fewer than `n` remain |
| `manifestParse_correct` | The compiled `manifest::parse`, through `magic`, `version_1`, `reserved(2)`, four calls to `part`, and its outlined helpers, returns to its caller with `sp` and every register but `a0` through `a5` and `t0` restored, and leaves memory outside its 144 bytes of stack as `parseMem` says: tag 1 and the error that `parseErr` gives, or tag 0 and the four parts |
| `decodeManifest_parse` | `parseErr`, which states the compiled checks in the code's own word arithmetic, accepts the 40 bytes exactly when the Lean decoder `decodeManifest` does, and the parts are the decoder's |
| `manifestParse_decodes` | The two joined: the compiled `parse` returns `Err` when `decodeManifest` rejects the manifest, and `Ok` with the decoder's manifest at `out + 4` when it accepts |
| `readerU8_correct` | The compiled `Reader::u8`, through `Reader::bytes`, returns the error flag in `a0` and the byte or `Truncated` (0) in `a1`, and advances the position by 1 when a byte was left |
| `segmentPhysical_correct` | The compiled `Segment::physical` writes a segment's address space and start, or `BadSegment` (9) when the address is below its region's base, as `physResult` says |
| `memcpy_aligned` | The compiled `memcpy`, called with 4-byte-aligned buffers that don't overlap and a length of at least 16 bytes that is a multiple of 4, copies the words through its word loop (`copyWords`), proved by induction |

`C3BootProofs/Proofs/ReaderArray.lean` proves `readerArray4_correct` about
the compiled `Reader::array::<4>`, the first proof that composes a call. It
saves `ra`, `s0`, and `s1` in a 32-byte stack frame, calls `Reader::bytes`
with its result slot in the frame, checks the slice it gets back, and
writes a `Result<&[u8; 4], Error>` through `a0`. The proof runs the call
through `readerBytes_correct` instead of the callee's instructions. Its
hypotheses add the slice invariant Rust guarantees (the reader's slice is
not null and doesn't wrap past 2^32, so a returned slice is never null) and
keep the frame, the result, and the reader's position apart from each other
and from both functions' code. The conclusion restores `sp`, `ra`, `s0`,
and `s1`, changes only `a0` through `a5` among the other registers, and
gives every byte of memory outside the frame. `C3BootProofs/Proof/Mem.lean`
has the load-after-store lemmas.

`C3BootProofs/Proofs/ReaderU32.lean` proves `readerU32_correct`, two calls
deep: `Reader::u32` calls `Reader::array::<4>` through its theorem, which
calls `Reader::bytes` through its own. It then loads the 4 bytes at the
returned address and joins them with shifts and ORs, which `or_assemble`
shows is the little-endian word. The bytes it loads are the original ones
because its hypotheses keep the reader's buffer apart from the stack and
from the reader's position. Rust's layout makes that true at every call
site, and the proof of each caller, such as `manifest::part`, has to show
it.

`C3BootProofs/Proofs/Part.lean` proves `manifestPart_correct`. LLVM's
machine outliner moved `part`'s register saves and restores into helper
functions, which `part` enters with `auipc t0; jalr t0` and which return
with `jr t0`. The outliner numbers them (`OUTLINED_FUNCTION_N`) differently
on each rebuild, so `scripts/extract-functions.py` finds each helper by
decoding the call that reaches it. `C3BootProofs/Proofs/Outlined.lean`
proves every helper of that shape at once, by induction on the list of
registers it saves or restores, and gives the caller a lemma that runs the
entry pair and the whole helper as one step. The proof
follows five paths: the offset is truncated, the length is truncated, the
length is below `min`, the length is above `max`, and success. On every
path it shows that the saved slots survive both calls and the stores
through `out`, so the restore gives back the caller's registers. Its code
hypothesis is one window, from `Reader::bytes` to the end of the save helper,
that the stack, the result, and the reader's position stay out of, instead
of a hypothesis for each function. `sep_of_le` turns address order into
`Sep`, so the audit's witness machine checks that window without comparing
every pair of bytes.

`C3BootProofs/Proofs/Parse.lean` proves `manifestParse_correct`. LLVM
specialized `parse` to its only caller, which passes the 40-byte manifest,
so the compiled function reads the bytes at `a1` and builds its reader with
length 40 without reading `a2`. The function's facts are in two structures.
`PCode` says memory holds all 14 functions `parse` runs where the image puts
them. `PEnv` keeps the 144 bytes of stack below `sp` apart from the code
window, the result, and the manifest, and the result apart from the code
window. It also requires a non-null manifest pointer whose 40 bytes don't
wrap past 2^32, and a 4-byte-aligned result and frame. The manifest may
overlap the result, because the code reads all 40 bytes before it stores
any. The proof of `check_slot` will have to show these, and that no address
in the stack region or the result reaches the code through the data-bus
alias described below. The theorem ends at the return address after some
number of steps, so a caller composes it with `Steps.trans`. Each call goes
through a lemma that applies the
callee's theorem at that call site. `PEnv.advance` and its `part` variants
carry the reader, the saved registers, and memory outside the stack across
each call. Every error path ends at the same store of the error byte, so one
lemma finishes all 16 of them; the trailing-bytes check can't fail, because
the four parts end at byte 40, and the proof shows that branch isn't taken.
`parseErr` lists the checks in the order the
code makes them, so the error `parse` returns is the first check that fails.

`C3BootProofs/Proofs/ParseSpec.lean` proves `decodeManifest_parse` by
flattening `decodeManifest` on 40 symbolic bytes into one condition on
natural numbers (`decodeManifest_bytes`) and translating each of `parse`'s
word comparisons into it. A sum that wraps past 2^32 is how the compiled
code detects overflow, and the translation turns each wrap test into the
decoder's `endOf < 2^32`. `omega`'s proof of a conjunction or an `↔`
depends on `Classical.choice`, so those goals are split before `omega` sees
them. The result's fields are at the offsets the compiled code stores them;
Rust's default layout chose those, and the pinned image fixes them.

The bytes come from `C3BootProofs/Image/Bootloader.lean`, which
`scripts/extract-functions.py` generates from the bootloader image whose
digest `c3-boot/bootloader/dev-image.sha256` pins; CI regenerates it and
fails on any difference, and `c3-boot/bootloader/check-digest.sh --update`
rewrites both. `C3BootProofs/Proof/Code.lean` has the proof tools: `CodeAt`
(memory holds a function's bytes), `fetch_code` (a fetch decodes from those
bytes, so the kernel computes each instruction), and `Steps`.
`C3BootProofs/Proof/Step.lean` runs one instruction at a time on a
symbolic state (`St`), with loads, stores, and `Sep`, which says two byte
ranges don't overlap, so a store leaves the code in place.

The model treats the instruction-bus and data-bus addresses of the same
SRAM as different memory, while the ESP32-C3 aliases them. A proof is
sound for the chip as long as no store reaches the code through its
data-bus alias, which holds when the code's preconditions keep stores in
the data region. The platform model will make that a stated obligation.

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
one whose slot results come from the trust-root checks. Some core lemmas
pull in `Classical.choice`: `beq_self_eq_true` does for `BitVec`, so the
proofs use `beq_iff_eq.mpr rfl` instead. The audit catches any that slip
in.

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
CI boots four scenarios: two rejected slots, and a trial boot that
rewrites the boot state and jumps to the new slot, at eFuse level 0 and at
level 1. That's about 470 million instructions on the model, through SHA-256, ECDSA, Ed25519, and the
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
