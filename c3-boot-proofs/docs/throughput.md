# Phase 5 throughput report

This report measures the machine-code proofs written so far against the
pinned bootloader image (SHA-256
`4b0fe03668079f6a6bf085aae436104cc27d8d057f53a9e37ab4f02ef6f04cf0`), as
[the plan](../../docs/esp32c3-verified-ota-plan.md#phase-5-pilot-proofs-and-code-freeze)
asks: proof lines per instruction, agent time per function, and Lean build
time and memory. It then projects the cost of proving the whole image.
Measured on 2026-11-11, with SHA-256 added the same day.

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
| **Total** | **5,592** | **49,692** | **8.9** | **1,332** | **3.6** | **About 21 h 40 min** |

The 5,592 instructions are 13 percent of the image. The full build of the
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
- **Build time grows faster than proof length.** The point addition's
  proof steps through its 46 calls with an invariant and one lemma per
  callee, so each step is small. Its first version closed the final
  equation inside the main theorem, where `subst_vars` worked through
  hundreds of hypotheses, and ran past 40 minutes. The same equation as a
  lemma of its own takes a second, and the file builds in 72 seconds.
  `fieldAdd_correct`, a single theorem over 107 instructions with one
  hypothesis per instruction, takes 249 seconds and 3.6 GB, the most of any
  file, and is the first candidate for the same split.
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

Phase 5 also asks for a list of code changes. None is made yet, because
each one changes the pinned image and every function's bytes and offsets
after it, so the proofs would need to be rebased at once at the code
freeze.

- **Give `root_from_inclusion` its own symbol** with `#[inline(never)]`.
  The pinned image inlines it into `sigstore::verify`, a 12.5 KB function,
  so the Merkle inclusion pilot can't be proved on its own.
- **Use a loop-based SHA-512.** `sha2::sha512::compress512` is 35.7 KB of
  unrolled code, more than a quarter of the image, for Ed25519's one hash
  per signature. A loop-based compression function would be a few
  kilobytes and could be proved by induction, like `crc32`.
- **Turn off LLVM's machine outliner** (`-C llvm-args=-enable-machine-outliner=never`)
  if the size allows. It moves short instruction runs into helpers such as
  `OUTLINED_FUNCTION_97`, which the SHA-256 compression function calls in
  the middle of its rounds, and renumbers them on every rebuild.
