# Phase 5 throughput report

This report measures the machine-code proofs written so far against the
bootloader image they were written for (SHA-256
`4b0fe03668079f6a6bf085aae436104cc27d8d057f53a9e37ab4f02ef6f04cf0`, now
`Image/BootloaderV0.lean`), as
[the plan](../../docs/esp32c3-verified-ota-plan.md#phase-5-pilot-proofs-and-code-freeze)
asks: proof lines per instruction, agent time per function, and Lean build
time and memory. It then projects the cost of proving the whole image.
Measured on 2026-11-11, with SHA-256 added the same day.

## Coverage

On 2026-11-11 the build changed (see
[Code changes](#code-changes-that-would-make-proofs-easier)), and the
current image (SHA-256
`c005c412f2faf2f1807ed68dae8bee9b111b5d63e1974f71fdbdba2d1b0d20da`) has
28,526 instructions. The proofs are being redone for it. Twelve functions
have the same bytes in both images, because RISC-V code that calls nothing
doesn't depend on where it is, so their proofs now name the current image.
P-384's Montgomery multiplication and squaring, `Uint<12>::select`, and
the P-256 field and point functions are redone: their code moved by fixed
offsets, the register saves and restores that the outliner had moved into
helpers are now straight-line blocks, and calls reach their callees at new
offsets. Proofs about the current image cover 5.7 percent of its
instructions and 71.0 percent of the instructions a boot runs. The
figures below are for the earlier image, before the change.

`scripts/coverage.py` counts the instructions in proved functions, in the
image and in one boot. A function counts once a correctness theorem covers
it; the theorem's hypotheses, such as a stack layout, are still for its
callers' proofs to discharge. The boot is the trial boot of a valid slot
that `c3-boot/docs/measurements.md` profiles. Measured on 2026-11-11, after
P-384's `mul_montgomery_form::<12>`, `Uint<12>::select`, and
`square_montgomery_form::<12>`:

| Measure | Proved | Total | Share |
| --- | --- | --- | --- |
| Instructions in the image | 6,160 | 42,490 | 14.5% |
| Instructions one boot runs | 106,531,322 | 133,867,420 | 79.6% |

`mul_montgomery_form::<12>` alone ran 36.2 percent of the boot, so proving
its 206 instructions raised boot coverage from 31.8 to 72.4 percent; the
squaring added 7.1 percent more. The unproved functions that run the most,
as a share of that boot:

| Function | Share of the boot |
| --- | --- |
| `curve25519_dalek`'s field multiplication, squaring, and reduction | 7.5% |
| `ConstMontyForm` operations on P-384 field elements | 6.0% |
| `c3_bootloader::flash::read` | 1.7% |
| `p384`'s `FieldElement::double` | 1.7% |

### What the coverage figures mean

On 2026-11-13, for the current image:

| Measure | Proved | Total | Share |
| --- | --- | --- | --- |
| Instructions in the image | 9,361 | 28,526 | 32.8% |
| Instructions one boot runs | 135,846,873 | 136,797,349 | 99.3% |
| Instructions in the 229 functions `c3_verify::sigstore::verify` reaches | 9,069 | 24,870 | 36.5% |
| Instructions in the 263 functions `boot_main` reaches | 9,361 | 28,513 | 32.8% |

The trial boot runs the whole Sigstore check of the update: 98.3 percent
of its instructions run in `sigstore::verify` and its callees. Boot
coverage weighs each function by how long it runs, and nearly all of that
time is field arithmetic, so it was 99.3 percent while the functions that
decide whether an update is accepted had no proofs: `sigstore::verify`
(4,098 instructions), `ed25519_verify` (2,099), `p384_verify_prehash`
(1,445), and `boot_main`'s main closure (1,531). The last 0.7 percent of
the boot is about 950,000 instructions in 156 unproved functions, which
hold about 17,800 instructions of code: most of the verifier's own logic.

The reach rows count each function that `sigstore::verify` or `boot_main`
can call, through any chain of calls, by its size, so the deciding code
counts as much as the hot code. They are the figures to watch.

No percentage is the goal. The goal is a theorem that the compiled
`sigstore::verify` returns `Ok` exactly when a Lean specification of the
Sigstore check accepts the bundle, and then the same for `boot_main` and
the slot check around it. That needs, besides the remaining callees'
proofs:

1. The Lean specification of the Sigstore check: decoders for the X.509,
   CMS, and Rekor checkpoint parts and the checks over them, tested against
   `c3-verify` the way the manifest and image-header decoders are. Without
   it, a proof of `sigstore::verify` could say only that the machine code
   computes what the Rust source computes. Done on 2026-11-13:
   `Spec/Sigstore.lean`'s `sigstoreVerify`, with ECDSA, Ed25519, and
   SHA-384 specified on naturals, matches `c3-verify` on the conformance
   cases and 32,000 mutations (see the README's differential test).
2. Proofs of the deciding functions against that specification:
   `p384_verify_prehash`, `ed25519_verify`, `sigstore::verify`, and
   `boot_main`.
3. Later, proofs that the crypto functions' specifications, which follow
   the Rust source's arithmetic, are ECDSA and Ed25519 verification
   (phase 7 of the plan).

To reproduce, profile the trial boot as `measurements.md` shows, then:

```bash
bin="$(rustc --print sysroot)/lib/rustlib/x86_64-unknown-linux-gnu/bin"
python3 ../c3-boot-proofs/scripts/coverage.py /tmp/trial.prof "${elf}" "${bin}/llvm-nm" "${bin}/llvm-objdump"
```

## Method

- **Instructions** are counted by decoding each extracted function's bytes
  in `C3BootProofs/Image/Bootloader.lean`, 16-bit and 32-bit encodings
  alike. The image's `.text` holds 42,490 instructions in 128,606 bytes.
- **Proof lines** are the lines of each group's files under
  `C3BootProofs/Proofs/`, including the generated `fetchRel` lemmas, the
  generated straight-line proofs, and the files that tie the parsers to
  their Lean decoders. The shared tools in `C3BootProofs/Proof/` (534 lines)
  aren't counted.
- **Build time and memory** are each file's `lake env lean` wall time and
  peak resident memory, four files at a time on an 8-core VM, with every
  import already built.
- **Agent time** is the wall-clock time between one agent's commits that
  finished each group. It includes builds, failed attempts, and the
  security review before each push. It is a rough measure: one agent, one
  attempt per function.

## Results

| Group | Instructions | Proof lines | Lines per instruction | Build time (s) | Peak memory (GB) | Agent time |
| --- | --- | --- | --- | --- | --- | --- |
| `crc32` | 22 | 373 | 17.0 | 1.5 | 0.5 | Not measured |
| `manifest::parse` and the `Reader` functions under it | 356 | 6,512 | 18.3 | 61 | 1.3 | 2 h 10 min |
| `image::parse` with `Reader::u8`, `Segment::physical`, and `memcpy` | 548 | 8,043 | 14.7 | 90 | 0.7 | 1 h 58 min |
| `FieldElement::multiply` with `memset`, `borrowing_sub`, `sub_inner`, and `widening_mul_fixed` | 555 | 5,047 | 9.1 | 365 | 2.2 | 2 h 38 min |
| `field_impl::add`, `field_impl::sub`, and `FieldElement::double` | 173 | 1,489 | 8.6 | 322 | 3.6 | 50 min |
| Complete point addition | 253 | 2,419 | 9.6 | 97 | 2.0 | 1 h 41 min |
| `sha2::sha256::compress256` with its outlined helpers | 3,685 | 25,809 | 7.0 | 392 | 1.8 | About 12 h 20 min |
| P-384's `mul_montgomery_form::<12>` with its outlined helpers and `Uint<12>::select` | 206 | 2,969 | 14.4 | 30 | 0.8 | 1 h 15 min |
| P-384's `square_montgomery_form::<12>` | 126 | 1,679 | 13.3 | 25 | 0.8 | 25 min |
| **Total** | **5,924** | **54,340** | **9.2** | **1,387** | **3.6** | **About 23 h 20 min** |

The 5,924 instructions are 14 percent of the image. The full build of the
Lean project, with the specification, the RV32 model, and the audit, takes
10 to 13 minutes on the same VM.

Findings:

- **Lines per instruction are a third of libsignal's.** The libsignal proof
  averages about 38 lines per AArch64 instruction. The pilot averages 12.5
  lines per RV32 instruction: 15 to 18 for the hand-written parser proofs,
  and 7 to 10 for the field, point, and SHA-256 code.
- **Generated straight-line proofs are cheapest.** The Montgomery reduction
  (`FieldMontRed.lean`, 199 instructions, 573 lines) and the point
  addition's body (`PointAdd.lean`, 253 instructions, 1,013 lines) take 3 to
  4 lines per instruction, because a script writes them from the decoded
  instructions and Lean checks every step.
- **SHA-256's generated rounds cost 6.6 lines per instruction, not 3 to 4.**
  The 3,587 round instructions take 23,502 generated lines in 51 chunks.
  Each chunk restates the registers and stack slots it starts from, names
  every new value with its own equation, and folds the compiler's
  rotations, `Ch`, and `Maj` into the specification's forms before
  `ac_rfl` closes it. The earlier straight-line proofs had no such
  bookkeeping. The projection below uses the measured rate.
- **Covering every call costs more than covering the first caller's.**
  `memset_correct` (35 instructions, 616 lines) and `memcpy_correct`
  (123 instructions, 2,465 lines) replace proofs that covered word-aligned
  buffers only. They add no instructions to the table, because each
  function was counted with its first caller, but every byte-buffer caller
  needs them. `memcpy`'s misaligned path costs 20 lines per instruction, the
  most of any code so far: it builds partial words in its stack frame with
  byte and halfword stores, so the proof tracks the frame's bytes one by
  one, and it needed its own sign-extension lemma because the library's
  use `Classical.choice`.
- **Build time grows faster than proof length.** The point addition's
  proof steps through its 46 calls with an invariant and one lemma per
  callee, so each step is small. Its first version closed the final
  equation inside the main theorem, where `subst_vars` worked through
  hundreds of hypotheses, and ran past 40 minutes. The same equation as a
  lemma of its own takes a second, and the file builds in 72 seconds.
  `fieldAdd_correct`, a single theorem over 107 instructions with one
  hypothesis per instruction, takes 249 seconds and 3.6 GB, the most of any
  file, and is the first candidate for the same split.
- **A loop proved once serves both P-384 multiplications.** The Montgomery
  loop body (`mmBody` in `MontMul12.lean`) is stated over its registers, so
  `square_montgomery_form::<12>`, which compiles the same loop with other
  registers, reused its arithmetic and its loop proofs, whose copies differ
  only in register numbers and offsets: the squaring took 13.3 lines per
  instruction and 25 minutes. The multiplication's
  2,969 lines are mostly calls and frames: the prologue, the final
  subtraction, and the call to `Uint<12>::select` take 1,225 lines for 60
  instructions, against 938 lines for the 81 instructions of both loops.
- **About 200 to 300 instructions an hour.** One agent proved about 1,900
  instructions in about 9 hours 20 minutes of wall-clock time, about 200
  an hour. SHA-256 took about 12 hours 20 minutes for 3,685 instructions,
  about 300 an hour, but most of that went to the generator, the RV32
  decoder in Python, and removing proof steps that depended on
  `Classical.choice`. Those are one-time costs: the generator's next
  straight-line function should go faster. The rate for hand-written
  proofs of branching code is still the 200 an hour measured above.

## Projection

| Part of the image | Code | Instructions (about) | Lines per instruction | Proof lines (about) |
| --- | --- | --- | --- | --- |
| Checks, bootloader, and helpers (`c3_verify`, `c3_bootloader`, outlined helpers, `core`, `memcpy`, `memset`) | 31.5 KB | 10,400 | 15 | 156,000 |
| `sha2`'s compression functions, unrolled straight-line code (SHA-256's 3,685 instructions done) | 47.7 KB | 15,700 | 7 | 110,000 |
| The rest of the cryptography (`curve25519_dalek`, `crypto_bigint`, `primeorder`, `p256`, `p384`, `ecdsa`, `c3_crypto`) | 49.4 KB | 16,300 | 9.5 | 155,000 |
| **Whole image** | **128.6 KB** | **42,500** | | **About 420,000** |

At the pilot's hand-written rate of 12.5 lines per instruction throughout,
the whole image would take about 530,000 lines. Either figure is about a
tenth of libsignal's 5.3 million lines. That is well inside phase 5's exit
criterion of three times libsignal, and below the plan's estimate of 0.5 to 2
million lines. At about 200 instructions an hour, one agent would need about
210 hours for the whole image. The work splits by function, so agents can run
in parallel.

The projection leaves out work that the instruction count doesn't capture:

- The algebra that turns the cryptographic contracts into the group law.
  `pointAdd_correct` proves that the compiled point addition computes the
  Renes, Costello, and Batina formula, not yet that the formula adds points.
- The computational security games in VCVio.
- The proofs that tie the boot path's theorems to the binary through
  `check_slot`, which must establish the stack and memory layout that every
  function proof assumes.

## Code changes that would make proofs easier

Phase 5 also asks for a list of code changes. Each one changes the pinned
image and every function's bytes and offsets after it, so the proofs
written by then have to be redone for the new image. That cost grows with
every proved function, so the three changes below landed together, as one
image change, on 2026-11-11, right after P-384's squaring was proved.
`sha2`'s compact backend covers SHA-256 as well as SHA-512, which retires
the proof of the unrolled `compress256`; the compact one is a loop.

Scratch builds of the pinned image's sources measured the options on
2026-11-11, with the trial boot that `c3-boot/docs/measurements.md`
profiles. Every variant booted the slot the same way:

| Build | Image (bytes) | Instructions one boot runs | Change |
| --- | --- | --- | --- |
| Pinned image | 133,392 | 133,867,420 | |
| Machine outliner off | 134,736 | 132,583,063 | −1.0% |
| `sha2`'s compact software backend | 88,016 | 138,060,641 | +3.1% |
| Both | 89,264 | 136,797,324 | +2.2% |

All fit the 160 KiB (163,840-byte) partition. `sha2` 0.11.1 chooses its
compact backend with one setting, `--cfg sha2_backend_soft="compact"`, for
SHA-256 and SHA-512 together, so a compact SHA-512 alone needs a patched
copy of the crate. Each change is checked
the way the image is today: the digest pin, the QEMU scenarios, and the
Lean-versus-Rust differential tests, plus NIST's SHA-512 vectors for the new
compression function.

- **Give `root_from_inclusion` its own symbol** with `#[inline(never)]`.
  The pinned image inlines it into `sigstore::verify`, a 12.5 KB function,
  so the Merkle inclusion pilot can't be proved on its own.
- **Use a loop-based SHA-512.** `sha2::sha512::compress512` is 35.7 KB of
  unrolled code, more than a quarter of the image, for Ed25519's one hash
  per signature. A loop-based compression function would be a few
  kilobytes and could be proved by induction, like `crc32`. It runs about
  330,000 instructions in a boot, 0.2 percent; a compact version 1.5 to 3
  times slower stays under 1 percent. Prefer the `sha2` crate's own compact
  software backend over new code in `c3-crypto`, if the pinned version has
  one. SHA-256 keeps its unrolled compression function, which is proved.
- **Turn off LLVM's machine outliner** (`-C llvm-args=-enable-machine-outliner=never`)
  if the size allows. It moves short instruction runs into helpers such as
  `OUTLINED_FUNCTION_97`, which the SHA-256 compression function calls in
  the middle of its rounds, and renumbers them on every rebuild.
