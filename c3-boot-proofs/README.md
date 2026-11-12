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
- `Sha256.lean`: SHA-256 as FIPS 180-4 defines it, on 32-bit words of the
  type the machine model's registers hold, with the standard's examples as
  build-time checks.
- `Merkle.lean`: RFC 6962 leaf and node hashes, and `rootFromInclusion`, the
  RFC 9162 algorithm that computes the root an inclusion proof implies, as
  `c3_verify::merkle::root_from_inclusion` takes it.

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

On 2026-11-11 the build changed to make the image easier to prove: no LLVM
machine outliner, `sha2`'s compact backend, and `root_from_inclusion` out of
line (`c3-boot/.cargo/config.toml`). `Image/Bootloader.lean` holds the
current image's functions, and CI checks them against it.
`Image/BootloaderV0.lean` keeps the earlier image's functions, which every
proof below was written against; each theorem still holds for those bytes,
and is being redone for the current image. `scripts/coverage.py` counts
only proofs about the current image.

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
| `imageParse_correct` | The compiled `image::parse`, through `magic`, `version_1`, `u16`, `u8`, `reserved`, `u32`, `Segment::physical`, `memcpy`, and its outlined helpers, returns to its caller with `sp` and the callee-saved registers restored, and leaves memory outside its 0x190-byte stack region and the 0x110-byte result unchanged. The result holds the error byte that `imgW` gives and the `Err` marker 0xFF at offset 0xC, or the segments, entry point, image length, segment count, and security version that `imgW` gives |
| `imgW_rel` | `imgW`, which states the compiled checks in the code's own word arithmetic and order, accepts the bytes exactly when the Lean decoder `decodeImageHeader` does, and then returns the decoder's header |
| `imageParse_decodes` | The two joined: the compiled `image::parse` returns `Err` when `decodeImageHeader` rejects the header, and `Ok` with the decoder's segments and fields in the result when it accepts |
| `memset_aligned` | The compiled `memset`, called with a 4-byte-aligned buffer and a length of at least 16 bytes that is a multiple of 4, stores the fill byte's word at each word through its word loop (`fillWords`), proved by induction. The P-256 field multiplication's Karatsuba step zeroes its accumulator with it |
| `memset_correct` | The compiled `memset` for any buffer: called with `dst`, a fill value, and a length `n` that doesn't run past the top of memory or into `memset`'s own code, it sets the `n` bytes from `dst` to the fill value's low byte and leaves every other byte as it was (`fillBytes`). The proof covers both of the compiled paths: one byte at a time below 16 bytes, and otherwise bytes up to a 4-byte boundary, then words, then the rest. One lemma (`fill_loop`) covers both byte loops. It changes only `a2` through `a6` and uses no stack |
| `memcpy_correct` | The compiled `compiler_builtins` `memcpy` for any buffers that don't overlap each other, `memcpy`'s code, or its 16-byte stack frame: it copies the `N` bytes at `src` to `dst` and leaves every other byte outside the frame as it was (`copyBytes`), returns `dst`, restores `sp`, and changes only `a1` through `a7` and `t0` through `t5`. The proof covers all four compiled paths: bytes one at a time below 16 bytes; otherwise bytes up to the destination's first 4-byte boundary (`copy_loop`), then words, then the rest (`memcpy_tail`). The words go through `lw` and `sw` when the source is aligned too (`copyw_loop`). When the source is 1, 2, or 3 bytes past a boundary, the code splices pairs of aligned source words with shifts (`splice_loop`, `splice_byte`) and builds the partial words at either end in its stack frame with `sb`, `sh`, and `lbu` (`mis_head1` to `mis_head3`, `mis_tail1` to `mis_tail3`). `signExtend_byte` proves the halfword copy's sign extension harmless without the library's `signExtend` lemmas, which use `Classical.choice` |
| `borrowingSub_correct`, `bsubB_eq` | The compiled `crypto_bigint::primitives::borrowing_sub` returns `l - r - c` and the borrow out as a mask, all ones exactly when `l < r + c`. Its Hacker's Delight borrow formula is proved from bit 31 of each operand (`hd_borrow`) |
| `subInner_correct` | The compiled `p256` `sub_inner`, called with a 9-limb number `L` and the modulus `p`, stores `L - p` when `L` is at least `p` and `L` otherwise, in 256 bits (`subRes`), and the borrow mask, all ones exactly when `L < p`. It runs nine `borrowing_sub` calls through that function's theorem (`si_round`), then the masked add-back in the compiled code's order (`addBack_val`, `bchain_val`, `sub_fin`). It restores every register but `a0` through `a5` and `t0`, and changes no memory outside 0x34 bytes of stack and the result |
| `wideMul_correct` | The compiled `crypto_bigint` `widening_mul_fixed::<8, 8>`, called with two 8-limb numbers, stores their 512-bit product in the 16 words at `out`. It zeroes a 16-word accumulator on its stack with two `memset` calls, adds each row of partial products into it with a carry chain (`wm_row`, `wm_inner`, `wm_step`), and copies it out with two `memcpy` calls, through those functions' theorems. It restores every register but `a0` through `a7` and `t0` through `t3`, and changes no memory outside 0x60 bytes of stack and the result |
| `fm_red` | The compiled Montgomery reduction, the 199-instruction straight-line block in `FieldElement::multiply`: the nine words it leaves for `sub_inner`, times 2^256, are the 16-word product plus `q · p` for some `q < 2^256`. Each `carrying_add` and `carrying_mul_add` of `montgomery_reduce` maps to one of three instruction idioms with a carry lemma (`fmP1`, `fmP3`, `fmP4`), and `mont_round` and `mont_tele` sum the eight rounds. `scripts/gen-mont-red.py` writes the proof from the decoded instructions, and CI checks that the committed file matches |
| `fieldMul_correct` | The compiled `p256` `FieldElement::multiply`, through `widening_mul_fixed::<8, 8>`, the reduction, and `sub_inner`, returns the Montgomery product: the 8 words it stores at the result, times 2^256, equal the operands' product modulo `p`, and are below `p` when that product is below `p · 2^256`, as it is for operands below `p`. It restores every register but `a0` through `a7` and `t0` through `t6`, and changes no memory outside 0x130 bytes of stack and the result |
| `fieldSub_correct`, `subInner_gen` | The compiled `p256` `field_impl::sub` copies its operands into 9-limb numbers and calls `sub_inner` with the subtrahend as the second operand, which `subInner_gen` covers for any second operand: it stores `A - B` with `p` added back when it borrows (`subGen`), which is `(A + p - B) mod p` for operands below `p` (`subGen_field`) |
| `fieldAdd_correct` | The compiled `p256` `field_impl::add` adds its operands with a carry chain into 9 limbs and calls `sub_inner` with the modulus: it stores `subRes (A + B)`, which is `(A + B) mod p` for operands below `p` (`subRes_add`) |
| `fieldDouble_correct` | The compiled `FieldElement::double` tail-calls `field_impl::add` with its operand twice, through `fieldAdd_correct` |
| `mont_fm`, `ptAddSpec` | The field operations as functions on numbers below `p` in Montgomery form (`fm a b = a · b · 2^-256 mod p`, `fa`, `fs`, `fd`), and `primeorder`'s complete point addition for `a = -3` (Renes, Costello, and Batina 2015, algorithm 4) in them, in the order of its Rust source. `mont_fm` turns `fieldMul_correct`'s congruence into `fm`. That `ptAddSpec` computes the curve's group law is not yet proved |
| `pointAdd_correct` | The compiled `primeorder` `add_assign` for P-256, called with `lhs` and `rhs` pointing at points whose six coordinates are below `p`, stores `ptAddSpec` of them over `lhs`. It makes 46 calls with 17 field elements in a 0x240-byte frame, each through its callee's theorem (`pa_mul`, `pa_add`, `pa_sub`, `pa_dbl`, `pa_cpy` in `PointEnv.lean`), and reads `b` in Montgomery form from `0x3FCC4368`, where the image's data segment puts it (`PAEnv` assumes those bytes, and the extraction checks them). It writes `lhs` only after its last read of either point, so the points may overlap. It restores every register but `a0` through `a7` and `t0` through `t6`, and changes no memory outside 0x370 bytes of stack and the 96 bytes at `lhs`. `scripts/gen-point-add.py` writes the proof, and CI checks that the committed file matches |
| `sha_rounds` | The 64 rounds of the compiled `sha2::sha256::compress256`, 3,587 straight-line instructions with the message schedule interleaved, turn the 8 working variables and the 16 block words on the stack into FIPS 180-4's rounds of them (`rnd`, `vs`). `scripts/gen-sha256.py` runs the instructions in Python on random inputs to name every value, cuts them into 51 chunks where every live register and stack slot holds a named value, and writes one theorem per chunk in `Sha256Rounds0.lean` through `Sha256Rounds6.lean`. Each chunk folds the compiler's rotations, `Ch`, and `Maj` into the specification's forms (`ShaSupport.lean`) and closes each value with `ac_rfl`. CI checks that the committed files match |
| `sha256Compress_correct` | The compiled `compress256`, called with the 8-word state at `stp` and `n` 64-byte blocks at `bp`, all disjoint from its 0xE0-byte frame and each other, updates the state to `Sha256.compress` folded over the blocks (`blockList`). It loads each block big-endian (`sha_load_iter`), runs the rounds through `sha_rounds`, and adds the result into the state (`sha_block_iter`), by induction on the blocks left. It reads the round constants from the image's table at `0x3FCC4EBC` (`SCEnv` assumes those bytes, and the extraction checks them). It restores `ra`, `sp`, `tp`, and `s0` through `s11`, and changes no memory outside its frame and the 32 bytes at `stp`. The theorem doesn't claim `gp` is preserved, though the function never writes it |
| `kcCompress_correct` | The current image's `compress256`, which `sha2`'s compact backend compiles to a 64-round loop with the message schedule in a 16-word window on the stack. Called with the 8-word state at `stp` and `n` 64-byte blocks at `bp`, all disjoint from its 0xE0-byte frame and each other, it updates the state to `Sha256.compress` folded over the blocks (`blockList`). Each block's words come in big-endian through 16 calls to `RangeFrom::index` (`kc_load_from`) and go into the window through `memcpy`. The rounds run by induction on the round (`kc_rounds_from`): rounds 16 through 63 first compute `W[t]` over `W[t - 16]`'s slot (`kcSched_run`), and each round's 47 instructions are one block (`kcRound_run`). The feed-forward adds the result into the state (`kc_block`). It restores `ra`, `sp`, and `s0` through `s11`, keeps `gp` and `tp`, and changes no memory outside its frame and the state |
| `shaUpdate_correct` | The compiled `<sha2::Sha256 as digest::Update>::update`, with its block loop and its `memcpy` calls, called with the hasher at `S` holding `msg` and `n` bytes at `D`, leaves the hasher holding `msg` followed by those bytes. `HasherAt` says what the hasher's 0x68 bytes hold for a message: the bytes after its full blocks in the buffer, their count, the hash value of the full blocks, and the block count. The proof covers the three compiled paths: the bytes fit in the buffer; the buffer is empty; or the buffer holds some bytes, which the code fills to a block from the input and compresses first (`fullBlocks_fill`). The whole blocks left go to `compress256` straight from the input and the rest to the buffer (`upd_join`). It restores `sp` and the callee-saved registers, and changes no memory outside the hasher and 0x100 bytes of stack. `n` is below 2^31, as Rust's slice lengths are, and the message stays below 2^32 bytes |
| `shaFinalize_correct` | The compiled `<sha2::Sha256 as digest::Digest>::finalize`, called with the hasher at `S` holding `msg` and a 32-byte output at `out`, writes FIPS 180-4's SHA-256 digest of `msg` to `out` (`sha256`). It pads the buffer with 0x80 and zeros through `memset`, then compresses one block, or two when the buffer holds 56 bytes or more (`padTail_short`, `padTail_long`). It writes the length in bits big-endian: the code byte-swaps two words with shifts and masks, and `lenLo_eq`, `lenHi_eq`, and `len_bytes` prove the swap bit by bit. It stores the hash words big-endian through an outlined helper in a loop (`St.callStoreBe`, `fin_loop`) and copies them out with two `memcpy` calls. Its callees are proved too: `shaZero32_correct` for `hybrid_array`'s zeroing `from_fn`, and `shaFinBlock_correct` for the closure that copies a block to the stack and compresses it. It restores `ra`, `sp`, and `s0` through `s11`, and changes no memory outside the hasher, the output, and 0x190 bytes of stack |
| `sha256Fn_correct` | The compiled `c3_crypto::sha::sha256`, called with `n` bytes at `D` and a 32-byte output at `out`, writes `sha256` of those bytes to `out`: FIPS 180-4's digest. It builds a fresh hasher in its frame (an outlined helper sets up `memcpy` of the image's initial hash value, which `iv_words` shows is `H(0)`, and three stores clear the buffer count and the block count), absorbs the input through `shaUpdate_correct`, moves the hasher with `memcpy` (`HasherAt.copy`), and calls `finalize` through `shaFinalize_correct`. It restores `ra`, `sp`, and `s0` through `s11`, and changes no memory outside the output and 0x270 bytes of stack. `n` is below 2^31 |
| `mulMont12_correct` | The compiled `crypto_bigint` `mul_montgomery_form::<12>`, P-384's field multiplication, called with 12-limb operands `x` and `y`, a modulus `n` with `y < n`, and `k` with `k · n₀ ≡ -1 (mod 2^32)`, writes to `out` the number `r < n` with `r · 2^384 ≡ x · y (mod n)`. Each of the outer loop's 12 passes adds a limb of `x` times `y` and the multiple of `n` that clears the low limb, then shifts the sum down a limb (`mm_pass`, through the inner loop `mm_inner`, which states the loop body once over its registers as `mmBody`). After pass `i` the accumulator and its top carry hold `T` with `2^(32 i) T = X_i Y + U N` and `T < 2N` (`mm_outer`). The final subtraction (`sub_loop`, 12 calls to `borrowing_sub`) and `Uint<12>::select` pick `T mod N` (`mm_final_arith`). It restores `ra`, `sp`, and `s0` through `s11`, and changes no memory outside `out` and 0xF0 bytes of stack |
| `sqrMont12_correct` | The compiled `crypto_bigint` `square_montgomery_form::<12>`, called with a 12-limb operand `x` below the modulus `n` and `k` with `k · n₀ ≡ -1 (mod 2^32)`, writes to `out` the number `r < n` with `r · 2^384 ≡ x · x (mod n)`. It compiles the multiplication's loop with both operands the same, in other registers, so its proof runs the same loop body (`mmBody`) and arithmetic lemmas; the final subtraction and `Uint<12>::select` are the multiplication's at other offsets. It restores `ra`, `sp`, and `s0` through `s11`, and changes no memory outside `out` and 0xF0 bytes of stack |
| `uintSelect12_correct` | The compiled `crypto_bigint` `Uint<12>::select`, called with `choice` 0 or 1, writes `b`'s 12 limbs to `out` when `choice` is 1 and `a`'s when it is 0. It masks one limb per call to an outlined helper into a zeroed buffer on its stack, then copies the buffer out with `memcpy`. It restores its callee-saved registers and changes no memory outside `out` and its 0x50-byte frame |
| `p384Add_correct`, `p3AddRes_mod` | The current image's `crypto_bigint` `ConstMontyForm<p384::FieldParams, 12>::add`, called with 12-limb operands `A` and `B`, stores `p3AddRes A B`, which is `(A + B) mod p` for operands below `p`. It adds the limbs with carries into its frame (`p3_add_loop`), subtracts the modulus, which it reads from the image's data, with 12 `borrowing_sub` calls (`p3_sub_loop`), and copies out the sum or the difference with a constant-time select through a byte of the frame (`p3_sel_loop`). It restores `ra`, `sp`, and the callee-saved registers, and changes no memory outside the 0xB4 bytes of stack below `sp` and the result |
| `p384Double_correct` | The current image's `<p384::arithmetic::field::FieldElement as ff::Field>::double`, called with a 12-limb operand `A`, stores `p3AddRes A A`, which is `2 A mod p` for an operand below `p`. It copies the operand to its frame with `memcpy`, shifts it left a bit in place, limb by limb (`pd_dbl_loop`), subtracts the modulus with 12 `borrowing_sub` calls (`pd_sub_loop`), and has `Uint<12>::select` write the doubled value or the difference to the result, through its theorem. It restores `ra`, `sp`, and the callee-saved registers, and changes no memory outside the 0xD0 bytes of stack below `sp` and the result |
| `p384Sub_correct`, `p3SubRes_mod` | The current image's `crypto_bigint` `ConstMontyForm<p384::FieldParams, 12>::sub`, called with 12-limb operands `A` and `B`, stores `p3SubRes A B`, which is `(A - B) mod p` for operands below `p`. It subtracts the limbs with 12 `borrowing_sub` calls into its frame (`ps_sub_loop`), masks the modulus, which it reads from the image's data, with the borrow (`ps_mask_loop`), adds the two with carries (`ps_add_loop`), and copies the sum out. It restores `ra`, `sp`, and the callee-saved registers, and changes no memory outside the 0xB4 bytes of stack below `sp` and the result |
| `feReduce_correct`, `fr_body` | The current image's `curve25519_dalek` `FieldElement2625::reduce`, called with ten `u64` limbs, stores `feReduceSpec` of them: the Rust source's carry chain on naturals, each `+=` modulo 2^64, then each limb's low 32 bits. `scripts/gen-fe25519.py` writes the body's proof (`FeReduceBody.lean`): it names each instruction's result, turns it into a natural-number fact, finds by running the code and the Rust source side by side which words hold each Rust value, and proves each Rust step with one small `omega` lemma over the instructions between. CI checks that the file is current. It saves and restores `s0` through `s4`, and changes no memory outside its 0x20 bytes of stack and the result |
| `feMul_correct`, `fmu_body` | The current image's `curve25519_dalek` `<&FieldElement2625 as Mul>::mul` stores `feMulSpec` of its operands' limbs: the Rust source's ten `u64` sums of products (each `19 * y[j]` and `2 * x[i]` a wrapping `u32`, each sum modulo 2^64), then `reduce`. `gen-fe25519.py` writes `FeMulBody.lean`: a theorem for each 40 instructions (the body has 777, with spills to the stack), one lemma for each of the 100 products, and one for each partial sum that the compiled code keeps whole. A sum's lemma states the exact integer identity, with an unnamed quotient for each 32-bit wrap, so `omega` solves only equations. It saves and restores `ra` and `s0` through `s11` and changes no memory outside its 0x140 bytes of stack and the result |
| `feSqInner_correct`, `fsq_body` | The current image's `curve25519_dalek` `FieldElement2625::square_inner` stores `feSqZ` of its operand's limbs as ten `u64`s: the Rust source's sums of products, with `2 * x[i]` and `19 * x[i]` as wrapping `u32`s and each `(...) * 2` group doubled modulo 2^64. `gen-fe25519.py` writes `FeSqBody.lean` the same way as `mul`'s body, with a lemma for each doubled group (a shift of the group's sum by one bit). It saves and restores `ra` and `s0` through `s11`, and changes no memory outside its 0x50 bytes of stack and the result |
| `feSquare_correct` | The current image's `FieldElement2625::square` stores `feSquareSpec` of its operand's limbs: `square_inner` into a buffer in its frame, then `reduce` into the result, each through its theorem. It saves and restores `ra` and `s0`, and changes no memory outside 0xB0 bytes of stack (its frame and its callees') and the result |
| `romFlashReadWords_correct`, `RomRead` | The current image's `rom::flash_read_words`, given `RomRead` (what the proofs assume the ROM's `esp_rom_spiflash_read` at 0x40000130 does when the ROM's code is in memory): it returns 1 or 0, and when it returns 1 the `4 w` bytes at the destination hold the flash's bytes from the source. It keeps `sp` and the callee-saved registers, and changes no memory outside its stack and the destination. `romStub_read` shows a ROM that always fails meets `RomRead`, so the assumption is satisfiable |
| `flashRead_correct`, `frd_outer`, `frd_inner` | The current image's `flash::read`, called with a flash address and an output slice of `len` bytes, returns 1 or 0, and when it returns 1 the slice holds `len` bytes of flash from the address. It clears its 256-byte bounce buffer through `memset_correct`, reads each chunk through `romFlashReadWords_correct`, and copies the chunk's bytes out of the buffer. It keeps `sp` and the callee-saved registers, and changes no memory outside its stack (its 0x140-byte frame, `flash_read_words`'s 16 bytes, and the ROM's) and the slice |
| `feAdd_correct`, `fad_loop` | The current image's `curve25519_dalek` `<&FieldElement2625 as Add>::add` stores, in each of the result's ten limbs, the sum of the operands' limbs modulo 2^32, as the Rust source's `+=` on `u32` in a release build. It copies the left operand into its frame and the sum out through `memcpy_correct` |
| `selectI64_correct` | The current image's `ctutils` `Choice::select_i64` returns `a`'s two words when the choice byte is 0 and `b`'s when it is 1. It writes the choice byte to the stack and reads it back (the optimization barrier), and changes no other memory |
| `feSub_correct` | The current image's `curve25519_dalek` `<&FieldElement2625 as Sub>::sub` stores `feSubSpec` of its operands' limbs: each `(x[i] + 16 p[i]) - y[i]` in `u32` arithmetic, widened to `u64` and reduced through `feReduce_correct` |
| `wideMul12x2_correct`, `wideMul8x2_correct`, `km_row_arith` | The current image's `crypto_bigint` `karatsuba::widening_mul_fixed::<12, 2>` and `::<8, 2>`, called with an `N`-limb and a 2-limb operand, store the `N + 2`-limb product: `accV out (N + 2) = accV x N * accV y 2`. They clear the product buffer through `memset_correct`, run the schoolbook rows (one theorem per step, one per row by induction), and copy the low `N` words out through `memcpy_correct` |
| `edDouble_correct`, `edd_loop` | The current image's `curve25519_dalek` `ProjectivePoint::double`, called with a point's `X`, `Y`, and `Z` at `sf`, stores `edDoubleSpec` of their limbs as the result's `X`, `Y`, `Z`, and `T`: the Rust source's `square`, `square2`, `add`, and `sub` steps in its order. It runs 12 calls through their callees' theorems (`square` three times, `square_inner` and `reduce` for `square2` with the doubling loop between them, `add` twice, `sub` three times, and `memcpy` twice), and changes no memory outside 0x210 bytes of stack and the result |
| `imgW_pages_signed` | `mapped_pages_signed` for the compiled parser: when it accepts, each 64 KiB page the cache maps for a flash segment ends inside the image |

[`docs/throughput.md`](docs/throughput.md) measures these proofs (lines per
instruction, build time and memory, agent time) and projects the cost of the
whole image.
[`docs/future-work.md`](docs/future-work.md) lists cleanup for later, including
the classical-free workarounds to remove once the audit allows `Classical.choice`.

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

`C3BootProofs/Proofs/Part.lean` proves `manifestPart_correct`. In the
earlier image, LLVM's machine outliner moved `part`'s register saves and restores into helper
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

`C3BootProofs/Proofs/ImageTop.lean` proves `imageParse_correct`, which
composes one theorem for each stage of the compiled function. `ImageHeader`
covers the prologue and the header checks, `ImageSegs` the loop that zeroes
the 16 segment slots, `ImageSegLoop` the segment loop (by induction on the
segments left), `ImageOverlap` the end check and the two overlap loops, and
`ImageFinal` the entry-point loop and the copy out. `imgW`, in
`ImageParse.lean`, states the compiled checks in the code's own word
arithmetic and order, so the error `parse` returns is the first check that
fails. `IEnv` keeps the stack region, the result, the input, the code
window, and the region tables apart, and requires that the stack region not
wrap past 2^32. `exists_imageParse_machine` in the audit shows those
hypotheses can hold.

`C3BootProofs/Proofs/ImageSpec.lean` and `ImageSpecSegs.lean` prove
`imgW_rel`. `Rel` relates an `Except` result of the compiled checks to the
decoder's `Option` result, and `Rel.bind` composes it through both monads'
binds, so each reader and each layer of the header check relates to the
decoder's at the same byte position. The decoder reads every segment and then
checks them, while the compiled code reads and checks each in turn; both
reject when any read or check fails, so `segs_rel` relates them by induction
on the segments left. `check_rel` turns each wrapped-sum test into the
decoder's `< 2^32` bound, and `align_rel` turns each mask into a remainder.
The mask lemma is proved from `Nat.testBit`, because the library's
`Nat.and_two_pow_sub_one_eq_mod` depends on `Classical.choice`.
`imageParse_decodes` joins `imgW_rel` to `imageParse_correct`, the way
`manifestParse_decodes` does for the manifest.

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
CRC often recomputed so the field rules are reached. It also hashes a
random message of every length from 0 to 300 bytes with `c3_crypto::sha256`,
which crosses each padding boundary, and builds 5,000 inclusion proofs for
trees of up to 40 leaves. About half of the proofs are valid; the rest have a
wrong index or size, a dropped, added, or flipped hash, a length that isn't a
multiple of 32, or 64 or 65 hashes for a tree near 2^64 leaves. It prints
each input with `c3-verify`'s or `c3-crypto`'s result, and
`lake exe decode-check` must print the same results.

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
