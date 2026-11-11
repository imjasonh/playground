# Future work and cleanup

This page lists cleanup that would simplify the proofs without changing
what they prove. None of it blocks progress. Each item says what to change
and where. Add to it when a proof takes a workaround that a later change
could remove.

## Allow `Classical.choice`

The axiom audit allows only `propext` and `Quot.sound`
(`axiom-audit-allow` in `.github/workflows/c3-boot-proofs.yml`, and the
`#guard_msgs` checks in `C3BootProofs/Audit.lean`). The audit's real job is
to reject `sorryAx` (an unfinished proof) and `Lean.ofReduceBool` (what
`native_decide` and `bv_decide` use, which trusts the compiled evaluator
along with the kernel). Rejecting `Classical.choice` as well keeps the
proofs constructive, but it isn't needed for soundness: `Classical.choice`
is one of Lean's three standard axioms and is consistent with its logic.
The AlphaProof Code work on libsignal, which the plan follows, accepted all
of Lean's standard axioms.

Many library lemmas depend on `Classical.choice`, so each time a proof
needs one, it gets a classical-free replacement. At a later milestone,
after the boot path's function proofs are done, allow `Classical.choice`
and remove the replacements:

1. Add `Classical.choice` to `axiom-audit-allow` and to the expected
   output of every `#guard_msgs in #print axioms` in `Audit.lean`. Keep
   rejecting `sorryAx` and `Lean.ofReduceBool`.
2. Replace each workaround in the catalog below with the library lemma or
   tactic it stands in for, and delete the workaround.
3. Rebuild and rerun the audit.

### Catalog of classical-free replacements

| File | Workaround | Stands in for |
| --- | --- | --- |
| `Spec/Formats.lean` | The magic numbers spelled out as byte lists (`magicRecord`, `magicManifest`, `magicImage`) | `String` functions such as `String.toUTF8` |
| `Proofs/ParseSpec.lean` and other parser proofs | Goals that are conjunctions or `↔` split by hand before `omega` | `omega` on the whole goal |
| `Proofs/ShaSpec.lean` | `mod_mul_two` | `Nat.mod_mul` |
| `Proofs/ShaSpec.lean` | `bits_lt`, `carry_disj`, `add_disj` | `BitVec.carry_of_and_eq_zero`, `BitVec.add_eq_or_of_and_eq_zero` |
| `Proofs/ShaSpec.lean` | `not_eq_xor`, `ch_add`, `maj_alt` proved bit by bit with `bitw` | `BitVec.getLsbD_not`, `BitVec.toNat_not` |
| `Proofs/Sha256Compress.lean` | `k7_flags`, `k18_flags`, and the other register-flag lemmas, by `decide` over `Fin 32` | `simp [Bool.or_eq_false_iff]` on the hypothesis |
| `Proofs/MemsetAny.lean` | `and255_small`, `and255` | `Nat.and_two_pow_sub_one_eq_mod` |
| `Proofs/MemsetAny.lean` | `ult_ofNat` splits its `↔` before `omega` | `omega` on the `↔` |
| `Proofs/MemsetAny.lean` | `fillw_loop` closes branch conditions with `decide_eq_true (by omega)` | `simpa using hlt` |
| `Proofs/MemcpyAny.lean` | `signExtend_byte`, `ext0_append`, `ext8_append`, `signExtend_lo`, `signExtend_hi` (through `ofInt` and `toInt`) | `BitVec.getLsbD_signExtend`, `BitVec.toNat_signExtend` |
| `Proofs/MemcpyAny.lean` | `and1_small`, `and1_val`, `and3_word_val` | `Nat.and_two_pow_sub_one_eq_mod` |
| `Proofs/ShaStream.lean` | `drop_take'` | `List.drop_take` |
| `Proofs/ShaUpdate.lean` | `and63_small`, `and63` | `Nat.and_two_pow_sub_one_eq_mod` |
| `Proofs/ShaUpdate.lean` | `mask64_val`, proved bit by bit through `m64_bits` and `Sha256.add_disj` | `Nat.and_two_pow_sub_one_eq_mod` on the value and its complement |
| `Proofs/ShaUpdate.lean` | Branch conditions closed with `beq_eq_false_iff_ne` and `ofNat_inj` | `simp` on the condition |

## Other cleanup

- **Retire the aligned-only `memset` and `memcpy` proofs.** `memset_correct`
  and `memcpy_correct` cover every call that `memset_aligned`
  (`Proofs/Memset.lean`, with `fillWords`) and `memcpy_aligned`
  (`Proofs/ImageHelpers.lean`, with `copyWords`) cover. Move their callers
  (`wideMul_correct`, `imageParse_correct`) to the general theorems and
  delete the aligned ones.
- **Move general step lemmas into `Proof/`.** `St.lh`, `St.sh`,
  `St.upd_eq`, and `St.upd_ne` (`Proofs/MemcpyAny.lean`,
  `Proofs/MemsetAny.lean`) belong in `Proof/Step.lean`, beside the other
  step lemmas.
- **Rename colliding decode lemmas.** `ms_at_0` and `ms_at_4` decode the
  `memcpy` stub (`Proofs/ImageHelpers.lean`), while `ms_at_14` through
  `ms_at_64` decode `memset` (`Proofs/MemsetAny.lean`).
- **State that `compress256` preserves `gp`.** `sha256Compress_correct`
  leaves `gp` out of the registers it restores, though the function never
  writes it.
- **Split `fieldAdd_correct`.** It takes 249 seconds and 3.6 GB, the most of
  any file, because one theorem steps through 107 instructions. A lemma for
  the closing equation, as `PointAdd.lean` does with `pa_spec_eq`, should
  cut both.
- **Write a bit-blasting tactic.** `lenLo_eq`, `lenHi_eq`, `bswap32_byte`,
  and `lenLo_toNat` (`Proofs/ShaFinal.lean`) split a 32-bit identity into
  one goal per bit index with `lt32_cases` and close each with `simp`, given
  the bits of `0xFF00` as lemmas. `bv_decide` would do it in one line, but
  the audit rejects it because it trusts the compiled evaluator
  (`Lean.ofReduceBool`). A tactic that does the case split and the `simp`
  call would shorten the next proof that needs it.
- **Revisit the dependency-update skip for `c3-boot`.** The daily update
  skips `c3-boot` because a bump changes the pinned image. An alternative is
  to let it bump `c3-boot` and make the proofs workflow a required check, so
  a bump lands only after the proofs are redone.
