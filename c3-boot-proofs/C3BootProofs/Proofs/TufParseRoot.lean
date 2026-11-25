import C3BootProofs.Proofs.TufParseMetadataHead
import C3BootProofs.Proofs.JsonU64
import C3BootProofs.Proofs.AllAsciiDigit

/-!
# `tuf::parse_root`, as compiled

`parse_root(doc)` runs `parse_metadata(doc, "root")`, reads the `version`
member of `signed` with `field` and `u64`, and rejects version 0. The
compiler passes the document's slice in `a1` and `a2` and the result's
address in `a0`. A `Result<Root, TufError>` keeps the `signed` and
`signatures` slices in its first 16 bytes and the version's low and high
words at `out + 0x10` and `out + 0x14`. An error keeps the zero word at
`out` and the error byte at `out + 4`.

The function saves seven registers in a 64-byte frame, and
`parse_metadata` uses 532 more bytes below it, so the stack region is the
596 bytes below `sp`. `prModel` gives the result on the document's bytes,
and `tufParseRoot_correct` is the machine-level contract.
-/

namespace C3.Json

/-- `tuf::parse_root` on the document `d`: the positions in `d` of `signed`
and `signatures`, and the version, or the error byte (`0x21` for a missing,
malformed, or zero `version`). -/
def prModel (d : Bytes) : Except Nat (Nat × Nat × Nat × Nat × Nat) :=
  match pmModel d (ascii!"root") with
  | .error e => .error e
  | .ok (gp, gl, sp, sl) =>
    match objField (slice d gp gl) (ascii!"version") with
    | .error e => .error e
    | .ok (vp, vl) =>
      match u64Val (slice (slice d gp gl) vp vl) with
      | none => .error 0x21
      | some v => if v = 0 then .error 0x21 else .ok (gp, gl, sp, sl, v)

/-- The values `pmObj` returns lie inside the object. -/
theorem pmObj_bnd {t kind : Bytes} {a b c e : Nat} (h : pmObj t kind = .ok (a, b, c, e)) :
    a + b ≤ t.length ∧ c + e ≤ t.length := by
  unfold pmObj pmMembers at h
  split at h
  · cases h
  split at h
  · cases h
  · cases h
  rename_i h1
  unfold pmTwo at h
  split at h
  · cases h
  · cases h
  rename_i h2
  split at h
  · unfold pmThen at h
    split at h
    · cases h
    · cases h
      exact ⟨(nextMember_lt h2).2.2.2.2.2, (nextMember_lt h1).2.2.2.2.2⟩
  · cases h

/-- The values `pmModel` returns lie inside the document. -/
theorem pmModel_bnd {d kind : Bytes} {a b c e : Nat} (h : pmModel d kind = .ok (a, b, c, e)) :
    a + b ≤ d.length ∧ c + e ≤ d.length := by
  unfold pmModel at h
  split at h
  · cases h
  rename_i tp tl hp
  obtain ⟨rfl, rfl⟩ := parseModel_ok_canon hp
  split at h
  · cases h
  rename_i a' b' c' e' ho
  cases h
  have hs : slice d 0 d.length = d := by
    show (d.drop 0).take d.length = d
    rw [List.drop_zero, List.take_length]
  rw [hs] at ho
  have := pmObj_bnd ho
  exact ⟨by omega, by omega⟩

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

abbrev TPR : Word := BitVec.ofNat 32 tufParseRootAddress
abbrev TPR_JU : Word := BitVec.ofNat 32 jsonU64Address
abbrev TPR_KR : Word := BitVec.ofNat 32 tufRootKindAddress
abbrev TPR_KV : Word := BitVec.ofNat 32 tufVersionKeyAddress

theorem pr_at_0 : fetchRel tufParseRootCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem pr_at_2 : fetchRel tufParseRootCode 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem pr_at_4 : fetchRel tufParseRootCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem pr_at_6 : fetchRel tufParseRootCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem pr_at_8 : fetchRel tufParseRootCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem pr_at_a : fetchRel tufParseRootCode 0xA = some (.store .sw sp (19 : Fin 32) 0x2C, 2) := by decide
theorem pr_at_c : fetchRel tufParseRootCode 0xC = some (.store .sw sp (20 : Fin 32) 0x28, 2) := by decide
theorem pr_at_e : fetchRel tufParseRootCode 0xE = some (.store .sw sp (21 : Fin 32) 0x24, 2) := by decide
theorem pr_at_10 : fetchRel tufParseRootCode 0x10 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem pr_at_12 : fetchRel tufParseRootCode 0x12 = some (.lui a3 0x3FCC4000, 4) := by decide
theorem pr_at_16 : fetchRel tufParseRootCode 0x16 = some (.aluImm .add a3 a3 0x76E, 4) := by decide
theorem pr_at_1a : fetchRel tufParseRootCode 0x1A = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem pr_at_1c : fetchRel tufParseRootCode 0x1C = some (.aluImm .add a4 x0 0x4, 2) := by decide
theorem pr_at_1e : fetchRel tufParseRootCode 0x1E = some (.auipc ra 0x0, 4) := by decide
theorem pr_at_22 : fetchRel tufParseRootCode 0x22 = some (.jalr ra ra 0xC4, 4) := by decide
theorem pr_at_26 : fetchRel tufParseRootCode 0x26 = some (.load .lw (9 : Fin 32) sp 0x8, 2) := by decide
theorem pr_at_28 : fetchRel tufParseRootCode 0x28 = some (.load .lbu (18 : Fin 32) sp 0xC, 4) := by decide
theorem pr_at_2c : fetchRel tufParseRootCode 0x2C = some (.branch .beq (9 : Fin 32) x0 0x56, 2) := by decide
theorem pr_at_2e : fetchRel tufParseRootCode 0x2E = some (.load .lbu a0 sp 0xE, 4) := by decide
theorem pr_at_32 : fetchRel tufParseRootCode 0x32 = some (.load .lbu a1 sp 0xD, 4) := by decide
theorem pr_at_36 : fetchRel tufParseRootCode 0x36 = some (.load .lbu a2 sp 0xF, 4) := by decide
theorem pr_at_3a : fetchRel tufParseRootCode 0x3A = some (.load .lw (19 : Fin 32) sp 0x10, 2) := by decide
theorem pr_at_3c : fetchRel tufParseRootCode 0x3C = some (.aluImm .sll a0 a0 0x8, 2) := by decide
theorem pr_at_3e : fetchRel tufParseRootCode 0x3E = some (.alu .or a0 a0 a1, 2) := by decide
theorem pr_at_40 : fetchRel tufParseRootCode 0x40 = some (.aluImm .sll a2 a2 0x10, 2) := by decide
theorem pr_at_42 : fetchRel tufParseRootCode 0x42 = some (.load .lw (20 : Fin 32) sp 0x14, 2) := by decide
theorem pr_at_44 : fetchRel tufParseRootCode 0x44 = some (.alu .or (21 : Fin 32) a0 a2, 4) := by decide
theorem pr_at_48 : fetchRel tufParseRootCode 0x48 = some (.aluImm .sll a0 (21 : Fin 32) 0x8, 4) := by decide
theorem pr_at_4c : fetchRel tufParseRootCode 0x4C = some (.alu .or a2 a0 (18 : Fin 32), 4) := by decide
theorem pr_at_50 : fetchRel tufParseRootCode 0x50 = some (.lui a3 0x3FCC5000, 4) := by decide
theorem pr_at_54 : fetchRel tufParseRootCode 0x54 = some (.aluImm .add a3 a3 0xFFFFF8A1, 4) := by decide
theorem pr_at_58 : fetchRel tufParseRootCode 0x58 = some (.aluImm .add a0 sp 0x1C, 2) := by decide
theorem pr_at_5a : fetchRel tufParseRootCode 0x5A = some (.aluImm .add a4 x0 0x7, 2) := by decide
theorem pr_at_5c : fetchRel tufParseRootCode 0x5C = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem pr_at_5e : fetchRel tufParseRootCode 0x5E = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem pr_at_62 : fetchRel tufParseRootCode 0x62 = some (.jalr ra ra 0xFFFFFDDA, 4) := by decide
theorem pr_at_66 : fetchRel tufParseRootCode 0x66 = some (.load .lw a1 sp 0x1C, 2) := by decide
theorem pr_at_68 : fetchRel tufParseRootCode 0x68 = some (.branch .beq a1 x0 0x24, 2) := by decide
theorem pr_at_6a : fetchRel tufParseRootCode 0x6A = some (.load .lw a2 sp 0x20, 2) := by decide
theorem pr_at_6c : fetchRel tufParseRootCode 0x6C = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem pr_at_6e : fetchRel tufParseRootCode 0x6E = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pr_at_72 : fetchRel tufParseRootCode 0x72 = some (.jalr ra ra 0xFFFFF98C, 4) := by decide
theorem pr_at_76 : fetchRel tufParseRootCode 0x76 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem pr_at_7a : fetchRel tufParseRootCode 0x7A = some (.branch .beq a0 x0 0x18, 2) := by decide
theorem pr_at_7c : fetchRel tufParseRootCode 0x7C = some (.load .lbu a0 sp 0x9, 4) := by decide
theorem pr_at_80 : fetchRel tufParseRootCode 0x80 = some (.jal x0 0x48, 2) := by decide
theorem pr_at_82 : fetchRel tufParseRootCode 0x82 = some (.store .sw (8 : Fin 32) x0 0x0, 4) := by decide
theorem pr_at_86 : fetchRel tufParseRootCode 0x86 = some (.store .sb (8 : Fin 32) (18 : Fin 32) 0x4, 4) := by decide
theorem pr_at_8a : fetchRel tufParseRootCode 0x8A = some (.jal x0 0x46, 2) := by decide
theorem pr_at_8c : fetchRel tufParseRootCode 0x8C = some (.load .lbu a0 sp 0x20, 4) := by decide
theorem pr_at_90 : fetchRel tufParseRootCode 0x90 = some (.jal x0 0x38, 2) := by decide
theorem pr_at_92 : fetchRel tufParseRootCode 0x92 = some (.load .lw a0 sp 0x10, 2) := by decide
theorem pr_at_94 : fetchRel tufParseRootCode 0x94 = some (.load .lw a1 sp 0x14, 2) := by decide
theorem pr_at_96 : fetchRel tufParseRootCode 0x96 = some (.alu .or a2 a0 a1, 4) := by decide
theorem pr_at_9a : fetchRel tufParseRootCode 0x9A = some (.branch .beq a2 x0 0x2A, 2) := by decide
theorem pr_at_9c : fetchRel tufParseRootCode 0x9C = some (.aluImm .srl a2 (21 : Fin 32) 0x8, 4) := by decide
theorem pr_at_a0 : fetchRel tufParseRootCode 0xA0 = some (.aluImm .srl a3 (21 : Fin 32) 0x10, 4) := by decide
theorem pr_at_a4 : fetchRel tufParseRootCode 0xA4 = some (.store .sw (8 : Fin 32) (9 : Fin 32) 0x0, 2) := by decide
theorem pr_at_a6 : fetchRel tufParseRootCode 0xA6 = some (.store .sb (8 : Fin 32) (18 : Fin 32) 0x4, 4) := by decide
theorem pr_at_aa : fetchRel tufParseRootCode 0xAA = some (.store .sb (8 : Fin 32) (21 : Fin 32) 0x5, 4) := by decide
theorem pr_at_ae : fetchRel tufParseRootCode 0xAE = some (.store .sb (8 : Fin 32) a2 0x6, 4) := by decide
theorem pr_at_b2 : fetchRel tufParseRootCode 0xB2 = some (.store .sb (8 : Fin 32) a3 0x7, 4) := by decide
theorem pr_at_b6 : fetchRel tufParseRootCode 0xB6 = some (.store .sw (8 : Fin 32) (19 : Fin 32) 0x8, 4) := by decide
theorem pr_at_ba : fetchRel tufParseRootCode 0xBA = some (.store .sw (8 : Fin 32) (20 : Fin 32) 0xC, 4) := by decide
theorem pr_at_be : fetchRel tufParseRootCode 0xBE = some (.store .sw (8 : Fin 32) a0 0x10, 2) := by decide
theorem pr_at_c0 : fetchRel tufParseRootCode 0xC0 = some (.store .sw (8 : Fin 32) a1 0x14, 2) := by decide
theorem pr_at_c2 : fetchRel tufParseRootCode 0xC2 = some (.jal x0 0xE, 2) := by decide
theorem pr_at_c4 : fetchRel tufParseRootCode 0xC4 = some (.aluImm .add a0 x0 0x21, 4) := by decide
theorem pr_at_c8 : fetchRel tufParseRootCode 0xC8 = some (.store .sw (8 : Fin 32) x0 0x0, 4) := by decide
theorem pr_at_cc : fetchRel tufParseRootCode 0xCC = some (.store .sb (8 : Fin 32) a0 0x4, 4) := by decide
theorem pr_at_d0 : fetchRel tufParseRootCode 0xD0 = some (.load .lw ra sp 0x3C, 2) := by decide
theorem pr_at_d2 : fetchRel tufParseRootCode 0xD2 = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem pr_at_d4 : fetchRel tufParseRootCode 0xD4 = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem pr_at_d6 : fetchRel tufParseRootCode 0xD6 = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem pr_at_d8 : fetchRel tufParseRootCode 0xD8 = some (.load .lw (19 : Fin 32) sp 0x2C, 2) := by decide
theorem pr_at_da : fetchRel tufParseRootCode 0xDA = some (.load .lw (20 : Fin 32) sp 0x28, 2) := by decide
theorem pr_at_dc : fetchRel tufParseRootCode 0xDC = some (.load .lw (21 : Fin 32) sp 0x24, 2) := by decide
theorem pr_at_de : fetchRel tufParseRootCode 0xDE = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem pr_at_e0 : fetchRel tufParseRootCode 0xE0 = some (.jalr x0 ra 0x0, 2) := by decide

/-! The bytes of the `signed` slice's length, which the function loads one
at a time and stores back one at a time. -/

theorem pr_s5 (b13 b14 b15 : BitVec 8) :
    ((b14.zeroExtend 32 <<< 8 ||| b13.zeroExtend 32) ||| b15.zeroExtend 32 <<< 16 : Word) =
      0#8 ++ b15 ++ b14 ++ b13 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_zero]
  iterate 32 (rcases i with _ | i; · simp)
  omega

theorem pr_w (b12 b13 b14 b15 : BitVec 8) :
    ((0#8 ++ b15 ++ b14 ++ b13) <<< 8 ||| b12.zeroExtend 32 : Word) = b15 ++ b14 ++ b13 ++ b12 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_zero]
  iterate 32 (rcases i with _ | i; · simp)
  omega

theorem pr_e0 (b13 b14 b15 : BitVec 8) : (0#8 ++ b15 ++ b14 ++ b13 : Word).extractLsb' 0 8 = b13 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_zero]
  iterate 8 (rcases i with _ | i; · simp)
  omega

theorem pr_e1 (b13 b14 b15 : BitVec 8) : ((0#8 ++ b15 ++ b14 ++ b13 : Word) >>> 8).extractLsb' 0 8 = b14 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  iterate 8 (rcases i with _ | i; · simp)
  omega

theorem pr_e2 (b13 b14 b15 : BitVec 8) : ((0#8 ++ b15 ++ b14 ++ b13 : Word) >>> 16).extractLsb' 0 8 = b15 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  iterate 8 (rcases i with _ | i; · simp)
  omega

theorem pr_x (b12 b13 b14 b15 : BitVec 8) :
    (b15 ++ b14 ++ b13 ++ b12 : Word).extractLsb' 0 8 = b12 ∧ (b15 ++ b14 ++ b13 ++ b12 : Word).extractLsb' 8 8 = b13 ∧
      (b15 ++ b14 ++ b13 ++ b12 : Word).extractLsb' 16 8 = b14 ∧
      (b15 ++ b14 ++ b13 ++ b12 : Word).extractLsb' 24 8 = b15 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb'] <;>
    (iterate 8 (rcases i with _ | i; · simp)) <;> omega

/-- The code `parse_root` runs, and the keys it passes. -/
structure PrCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M TPR tufParseRootCode
  pm : PmCode M
  u64 : CodeIn M TPR_JU jsonU64Code
  aad : CodeIn M AAD allAsciiDigitCode
  kr : CodeIn M TPR_KR tufRootKindData
  kv : CodeIn M TPR_KV tufVersionKeyData

theorem PrCode.of_out {M M' : Word → BitVec 8} {s : Word} {k : Nat} (h : PrCode M) (hO : Out M M' s k)
    (hs : s.toNat + k ≤ 0x40000000) (hro : Sep s k (BitVec.ofNat 32 roWindowAddress) roWindowSize) :
    PrCode M' :=
  ⟨tpm_codeIn h.self hO hs (by decide) (by decide), h.pm.of_out hO hs hro,
    tpm_codeIn h.u64 hO hs (by decide) (by decide), tpm_codeIn h.aad hO hs (by decide) (by decide),
    hO.codeIn h.kr (tuf_sep_ro hro (by decide) (by decide)), hO.codeIn h.kv (tuf_sep_ro hro (by decide) (by decide))⟩

theorem tpr_kr {M : Word → BitVec 8} (h : PrCode M) : memBytes M TPR_KR 4 = ascii!"root" :=
  tuf_codeIn_memBytes h.kr (by decide)

theorem tpr_kv {M : Word → BitVec 8} (h : PrCode M) : memBytes M TPR_KV 7 = ascii!"version" :=
  tuf_codeIn_memBytes h.kv (by decide)

theorem PmRes.frame {M M' : Word → BitVec 8} {s out : Word} {r : Except Nat (Word × Nat × Word × Nat)}
    (h : PmRes M M' s out r) : ∀ x, Sep x 1 s 532 → Sep x 1 out 16 → M' x = M x := by
  rcases r with _ | ⟨_, _, _, _⟩
  · exact h.1
  · exact h.1

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- A call to `parse_metadata(doc, kind)` on the `n` bytes at `p`, with the
type the `kl` bytes at `kq`. -/
theorem WP.callPm {hi lo out s p kq : Word} {n kl : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = TPM) (hev : (off + 8) % 2 = 0)
    (hc : PmCode M) (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n) (ha3 : f a3 = kq)
    (ha4 : f a4 = BitVec.ofNat 32 kl) (hsp : f sp = s + BitVec.ofNat 32 532)
    (hal : s.toNat % 4 = 0) (hsw : s.toNat + 532 ≤ 0x40000000)
    (hro : Sep s 532 (BitVec.ofNat 32 roWindowAddress) roWindowSize) (halo : out.toNat % 4 = 0)
    (how : out.toNat + 16 ≤ 0x40000000) (hso : Sep out 16 s 532) (hn : n < 2 ^ 31) (hp0 : p.toNat ≠ 0)
    (hpn : p.toNat + n < 2 ^ 32) (hSp : Sep s 532 p n) (hKL : kl < 2 ^ 32) (hSK : Sep s 532 kq kl)
    (hSb : Sep s 532 base code.length) (hsb : Sep out 16 base code.length)
    (k : ∀ m2 : Machine, PmRes M m2.mem s out (pmRes p (pmModel (memBytes M p n) (memBytes M kq kl))) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := TPM) (cl := jClob)
    (P := fun m2 => PmRes M m2.mem s out (pmRes p (pmModel (memBytes M p n) (memBytes M kq kl))))
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc' i hi => by
      rw [hP.frame _ (hSb.symm.sub (c := i) (l := 1) hi) (hsb.symm.sub (c := i) (l := 1) hi)]
      exact hc' i hi) k
  obtain ⟨m2, c2, pc2, hR, hfr⟩ := tufParseMetadata_correct m1 (retAddr := base + BitVec.ofNat 32 (off + 8))
    (by rw [hmem1]; exact hc) hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1)
    (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp; exact ha3) (by rw [hreg1]; rsimp; exact ha4)
    (by rw [hreg1]; rsimp; exact hsp) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
    hal hsw hro halo how hso hn hp0 hpn hSp hKL hSK
  rw [hmem1] at hR
  exact ⟨m2, c2, pc2, hR, hfr⟩

/-- A call to `Value::u64` on the `n` bytes at `p`. -/
theorem WP.callU64 {hi lo out s p : Word} {n : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = TPR_JU) (hev : (off + 8) % 2 = 0)
    (hcu : CodeIn M TPR_JU jsonU64Code) (hca : CodeIn M AAD allAsciiDigitCode)
    (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n) (hsp : f sp = s + BitVec.ofNat 32 32)
    (hn : n < 2 ^ 32) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hsw : s.toNat + 32 ≤ 0x40000000)
    (hSp : Sep s 32 p n) (hso : Sep out 16 s 32) (how : out.toNat + 16 ≤ 0x40000000)
    (hSb : Sep s 32 base code.length) (hsb : Sep out 16 base code.length)
    (k : ∀ m2 : Machine, U64ResF M m2.mem out s 32 (u64Val (memBytes M p n)) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  have hA : TPR_JU + 0x158 = AAD := by decide
  refine WP.callGen (tb := TPR_JU) (cl := jClob)
    (P := fun m2 => U64ResF M m2.mem out s 32 (u64Val (memBytes M p n)))
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => by
      obtain ⟨M1, hO, hU⟩ := hP
      exact hU.outside.codeIn (hO.codeIn hc hSb) hsb) k
  obtain ⟨m2, c2, pc2, hR, hfr⟩ := jsonU64_correct m1 (base := TPR_JU) (out := out) (s := s) (p := p) (n := n)
    (by decide) (by rw [hmem1]; exact hcu) (by rw [hmem1, hA]; exact hca) hpc1
    (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2)
    (by rw [hreg1]; rsimp; exact hsp) hn hal halo
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
    (lowSep hsw (by decide) (by decide)) (by rw [hA]; exact lowSep hsw (by decide) (by decide)) hSp hso
    (lowSep how (by decide) (by decide))
  rw [hmem1] at hR
  exact ⟨m2, c2, pc2, hR, hfr⟩

end

/-- What `parse_root` leaves: memory outside the 596 bytes at `s` and the
24 bytes at `out` as before, and `r` at `out`. -/
def PrRes (M M' : Word → BitVec 8) (s out : Word) : Except Nat (Word × Nat × Word × Nat × Nat) → Prop
  | .error e => (∀ x, Sep x 1 s 596 → Sep x 1 out 24 → M' x = M x) ∧ memLoad32 M' out = 0 ∧
      M' (out + 4) = BitVec.ofNat 8 e
  | .ok (q1, l1, q2, l2, v) => (∀ x, Sep x 1 s 596 → Sep x 1 out 24 → M' x = M x) ∧ memLoad32 M' out = q1 ∧
      memLoad32 M' (out + 4) = BitVec.ofNat 32 l1 ∧ memLoad32 M' (out + 8) = q2 ∧
      memLoad32 M' (out + 0xC) = BitVec.ofNat 32 l2 ∧
      (memLoad32 M' (out + 0x14)).toNat * 2 ^ 32 + (memLoad32 M' (out + 0x10)).toNat = v

/-- The word-level result of `parse_root` on the document at `p`. -/
def prRes (p : Word) (r : Except Nat (Nat × Nat × Nat × Nat × Nat)) : Except Nat (Word × Nat × Word × Nat × Nat) :=
  r.map fun x => (p + BitVec.ofNat 32 x.1, x.2.1, p + BitVec.ofNat 32 x.2.2.1, x.2.2.2.1, x.2.2.2.2)

/-- The registers `parse_root` changes before its epilogue restores the
saved ones. -/
abbrev prE : List (Fin 32) := jClob ++ [ra, sp, 8, 9, 18, 19, 20, 21]

/-- The saved registers in the frame at `F`. -/
def PrSaved (F : Word) (g0 : Fin 32 → Word) (M1 : Word → BitVec 8) : Prop :=
  memLoad32 M1 (F + BitVec.ofNat 32 0x3C) = g0 ra ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x38) = g0 8 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x34) = g0 9 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x30) = g0 18 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x2C) = g0 19 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x28) = g0 20 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x24) = g0 21

/-- Memory after the prologue. -/
def prM1 (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (F + 0x3C) (g0 ra))
    (F + 0x38) (g0 8))
    (F + 0x34) (g0 9))
    (F + 0x30) (g0 18))
    (F + 0x2C) (g0 19))
    (F + 0x28) (g0 20))
    (F + 0x24) (g0 21)

theorem tpr_pro (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) :
    Out M (prM1 M F g0) F 64 ∧ PrSaved F g0 (prM1 M F g0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((((out_store32 _ _ _).widen (d := 0x3C) (by decide)).trans
      ((out_store32 _ _ _).widen (d := 0x38) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x34) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x30) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x2C) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x28) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x24) (by decide))
  · exact pa_ld 0x3C (by decide) [0x38, 0x34, 0x30, 0x2C, 0x28, 0x24] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 8, g0 9, g0 18, g0 19, g0 20, g0 21]
  · exact pa_ld 0x38 (by decide) [0x34, 0x30, 0x2C, 0x28, 0x24] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 9, g0 18, g0 19, g0 20, g0 21]
  · exact pa_ld 0x34 (by decide) [0x30, 0x2C, 0x28, 0x24] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 18, g0 19, g0 20, g0 21]
  · exact pa_ld 0x30 (by decide) [0x2C, 0x28, 0x24] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 19, g0 20, g0 21]
  · exact pa_ld 0x2C (by decide) [0x28, 0x24] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 20, g0 21]
  · exact pa_ld 0x28 (by decide) [0x24] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 21]
  · exact memLoad32_store32_same _ _ _

/-- What the function's body may assume after the prologue: the frame at
`F = s + 532`, the saved registers in `M1`, and the bounds on the stack and
`out`. -/
structure PrEnv (M0 M1 : Word → BitVec 8) (s out F : Word) (g0 : Fin 32 → Word) : Prop where
  hF : s + BitVec.ofNat 32 532 = F
  hal : s.toNat % 4 = 0
  hsw : s.toNat + 596 ≤ 0x40000000
  halo : out.toNat % 4 = 0
  how : out.toNat + 24 ≤ 0x40000000
  hso : Sep out 24 s 596
  hro : Sep s 596 (BitVec.ofNat 32 roWindowAddress) roWindowSize
  hc : PrCode M0
  hO1 : Out M0 M1 s 596
  hv : PrSaved F g0 M1
  hsp0 : g0 sp = F + BitVec.ofNat 32 0x40
  hret : g0 ra &&& ~~~1 = g0 ra
  hz0 : g0 0 = 0

section
variable {M0 M1 Mk : Word → BitVec 8} {s out F : Word} {g0 : Fin 32 → Word}

theorem PrEnv.Fc (E : PrEnv M0 M1 s out F g0) (c : Nat) :
    F + BitVec.ofNat 32 c = s + BitVec.ofNat 32 (532 + c) := by
  rw [← E.hF, add_ofNat_assoc]

theorem PrEnv.FN (E : PrEnv M0 M1 s out F g0) {c : Nat} (hc : c ≤ 64) :
    (F + BitVec.ofNat 32 c).toNat = s.toNat + 532 + c := by
  rw [E.Fc, tex_toNat (by have := E.hsw; omega)]; omega

theorem PrEnv.halF (E : PrEnv M0 M1 s out F g0) : F.toNat % 4 = 0 := by
  have := E.FN (c := 0) (by decide); rw [add_ofNat_zero] at this; have := E.hal; omega

/-- A word of the frame at or above the saved registers is apart from the
568 bytes below them. -/
theorem PrEnv.sepHi (E : PrEnv M0 M1 s out F g0) {c : Nat} (hc : 36 ≤ c) (hc' : c + 4 ≤ 64) :
    Sep s 568 (F + BitVec.ofNat 32 c) 4 := by
  rw [E.Fc]; exact tex_sepS (by omega) (by have := E.hsw; omega)

theorem PrEnv.code (E : PrEnv M0 M1 s out F g0) (hO : Out M1 Mk s 568) : PrCode Mk :=
  E.hc.of_out (E.hO1.trans (hO.mono (by decide))) E.hsw E.hro

theorem PrEnv.saved (E : PrEnv M0 M1 s out F g0) (hO : Out M1 Mk s 568) : PrSaved F g0 Mk := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := E.hv
  exact ⟨(hO.load32 (E.sepHi (by decide) (by decide))).trans v0, (hO.load32 (E.sepHi (by decide) (by decide))).trans v1,
    (hO.load32 (E.sepHi (by decide) (by decide))).trans v2, (hO.load32 (E.sepHi (by decide) (by decide))).trans v3,
    (hO.load32 (E.sepHi (by decide) (by decide))).trans v4, (hO.load32 (E.sepHi (by decide) (by decide))).trans v5,
    (hO.load32 (E.sepHi (by decide) (by decide))).trans v6⟩

/-- `out` is apart from each saved register. -/
theorem PrEnv.outHi (E : PrEnv M0 M1 s out F g0) {c : Nat} (hc' : c + 4 ≤ 64) :
    Sep out 24 (F + BitVec.ofNat 32 c) 4 := by
  rw [E.Fc]; exact E.hso.subR (by omega)

theorem PrEnv.outT (E : PrEnv M0 M1 s out F g0) : Sep out 24 TPR tufParseRootCode.length :=
  lowSep E.how (by decide) (by decide)

theorem PrEnv.savedOut {Mf Mf' : Word → BitVec 8} (E : PrEnv M0 M1 s out F g0) (hv : PrSaved F g0 Mf)
    (hO : Out Mf Mf' out 24) : PrSaved F g0 Mf' := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := hv
  exact ⟨(hO.load32 (E.outHi (by decide))).trans v0, (hO.load32 (E.outHi (by decide))).trans v1,
    (hO.load32 (E.outHi (by decide))).trans v2, (hO.load32 (E.outHi (by decide))).trans v3,
    (hO.load32 (E.outHi (by decide))).trans v4, (hO.load32 (E.outHi (by decide))).trans v5,
    (hO.load32 (E.outHi (by decide))).trans v6⟩

/-- Memory that agrees with `M1` outside the 568 bytes at `s` agrees with
`M0` outside the 596. -/
theorem PrEnv.agree (E : PrEnv M0 M1 s out F g0) (hO : Out M1 Mk s 568) : ∀ x, Sep x 1 s 596 → Mk x = M0 x :=
  fun x hx => (hO x (by have := hx.subR (c := 0) (l := 568) (by decide); rwa [add_ofNat_zero] at this)).trans
    (E.hO1 x hx)

end

section
variable {M0 M1 Mf : Word → BitVec 8} {s out F : Word} {g g0 : Fin 32 → Word}

theorem pr_epi {R : (Word → BitVec 8) → Prop} (hsp : g sp = F) (hv : PrSaved F g0 Mf)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0x40) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0)
    (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ prE → g x = g0 x) (hR : R Mf) :
    WP tufParseRootCode TPR (RPost (g0 ra) R g0) Mf 0xD0 g := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := hv
  refine WP.lw pr_at_d0 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x3C) (by decide)) ?_; wn
  refine WP.lw pr_at_d2 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x38) (by decide)) ?_; wn
  refine WP.lw pr_at_d4 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x34) (by decide)) ?_; wn
  refine WP.lw pr_at_d6 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x30) (by decide)) ?_; wn
  refine WP.lw pr_at_d8 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x2C) (by decide)) ?_; wn
  refine WP.lw pr_at_da (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x28) (by decide)) ?_; wn
  refine WP.lw pr_at_dc (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x24) (by decide)) ?_; wn
  refine WP.aluImm pr_at_de ?_; wn
  refine WP.ret pr_at_e0 ⟨?_, hR, ?_⟩
  · rsimp; rw [hsp]; erw [e0]; rw [add_lit_zero, hret]
  refine frame_of (L2 := [ra, sp, 8, 9, 18, 19, 20, 21]) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp <;> rw [hsp]
  · exact e0
  · rw [hsp0]; rfl
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5
  · exact e6

end

/-- The postcondition: return to the caller with `r` at `out`. -/
abbrev prQ (M0 : Word → BitVec 8) (s out : Word) (g0 : Fin 32 → Word)
    (r : Except Nat (Word × Nat × Word × Nat × Nat)) : Post :=
  RPost (g0 ra) (fun M' => PrRes M0 M' s out r) g0

section
variable {M0 M1 Mf : Word → BitVec 8} {s out F : Word} {g g0 : Fin 32 → Word} {e : Nat}

theorem pr_errRes (E : PrEnv M0 M1 s out F g0) (hO : Out M1 Mf s 568) :
    PrRes M0 (memStore8 (memStore32 Mf out 0) (out + 4) (BitVec.ofNat 8 e)) s out (.error e) ∧
      Out Mf (memStore8 (memStore32 Mf out 0) (out + 4) (BitVec.ofNat 8 e)) out 24 := by
  have hR := pa_err_res Mf out _ e rfl
  exact ⟨⟨fun x hx ho => (hR.1 x (ho.subR (c := 0) (l := 8) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)).trans
      (E.agree hO x hx), hR.2.1, hR.2.2⟩, hR.out.mono (by decide)⟩

/-- The error tail at 0xC8: the zero word at `out`, the error byte from
`a0` at `out + 4`, and the epilogue. -/
theorem pr_c8 (E : PrEnv M0 M1 s out F g0) (hO : Out M1 Mf s 568) (h8 : g 8 = out) (hsp : g sp = F)
    (ha0 : (g a0).extractLsb' 0 8 = BitVec.ofNat 8 e) (hz : g 0 = 0) (hfr : ∀ x, x ∉ prE → g x = g0 x) :
    WP tufParseRootCode TPR (prQ M0 s out g0 (.error e)) Mf 0xC8 g := by
  refine WP.sw pr_at_c8 (by (try rsimp); rw [h8, add_lit_zero]; exact E.halo)
    (by (try rsimp); rw [h8, add_lit_zero]; exact tex_sepL E.outT (by decide)) ?_; wn
  refine WP.sb pr_at_cc (by (try rsimp); rw [h8]; exact E.outT.sub (c := 4) (l := 1) (by decide)) ?_; wn
  (try rsimp)
  rw [h8, add_lit_zero, hz, ha0]
  obtain ⟨hR, hOo⟩ := pr_errRes (e := e) E hO
  exact pr_epi hsp (E.savedOut (E.saved hO) hOo) E.hsp0 E.hret E.halF E.hz0 hfr hR

/-- The error tail at 0x82, with the error byte in `s2`. -/
theorem pr_82 (E : PrEnv M0 M1 s out F g0) (hO : Out M1 Mf s 568) (h8 : g 8 = out) (hsp : g sp = F)
    (h18 : (g 18).extractLsb' 0 8 = BitVec.ofNat 8 e) (hz : g 0 = 0) (hfr : ∀ x, x ∉ prE → g x = g0 x) :
    WP tufParseRootCode TPR (prQ M0 s out g0 (.error e)) Mf 0x82 g := by
  refine WP.sw pr_at_82 (by (try rsimp); rw [h8, add_lit_zero]; exact E.halo)
    (by (try rsimp); rw [h8, add_lit_zero]; exact tex_sepL E.outT (by decide)) ?_; wn
  refine WP.sb pr_at_86 (by (try rsimp); rw [h8]; exact E.outT.sub (c := 4) (l := 1) (by decide)) ?_; wn
  refine WP.jal pr_at_8a (by decide) ?_; wn
  (try rsimp)
  rw [h8, add_lit_zero, hz, h18]
  obtain ⟨hR, hOo⟩ := pr_errRes (e := e) E hO
  exact pr_epi hsp (E.savedOut (E.saved hO) hOo) E.hsp0 E.hret E.halF E.hz0 hfr hR

end

theorem pr_st6 {M Mf : Word → BitVec 8} {o a b c d e w : Word}
    (hM : memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M o a) (o + 4) b) (o + 8) c)
      (o + 0xC) d) (o + 0x10) e) (o + 0x14) w = Mf) :
    Out M Mf o 24 ∧ memLoad32 Mf o = a ∧ memLoad32 Mf (o + 4) = b ∧ memLoad32 Mf (o + 8) = c ∧
      memLoad32 Mf (o + 0xC) = d ∧ memLoad32 Mf (o + 0x10) = e ∧ memLoad32 Mf (o + 0x14) = w := by
  subst hM
  refine ⟨(((((out_store32 _ _ _).mono (by decide)).trans (Out.widen (d := 4) (out_store32 _ _ _) (by decide))).trans
      (Out.widen (d := 8) (out_store32 _ _ _) (by decide))).trans (Out.widen (d := 0xC) (out_store32 _ _ _)
      (by decide))).trans (Out.widen (d := 0x10) (out_store32 _ _ _) (by decide)) |>.trans
      (Out.widen (d := 0x14) (out_store32 _ _ _) (by decide)), ?_, ?_, ?_, ?_, ?_, memLoad32_store32_same _ _ _⟩
  · have := ld_skip (s := o) (v := w) 0 0x14 (Or.inl (by decide)) (by decide) (by decide)
      (ld_skip (v := e) 0 0x10 (Or.inl (by decide)) (by decide) (by decide)
      (ld_skip (v := d) 0 0xC (Or.inl (by decide)) (by decide) (by decide)
      (ld_skip (v := c) 0 8 (Or.inl (by decide)) (by decide) (by decide)
        (ld_skip (v := b) 0 4 (Or.inl (by decide)) (by decide) (by decide)
          (show memLoad32 (memStore32 M o a) (o + BitVec.ofNat 32 0) = a by
            rw [add_ofNat_zero]; exact memLoad32_store32_same _ _ _)))))
    rwa [add_ofNat_zero] at this
  · exact ld_skip 4 0x14 (Or.inl (by decide)) (by decide) (by decide)
      (ld_skip 4 0x10 (Or.inl (by decide)) (by decide) (by decide)
      (ld_skip 4 0xC (Or.inl (by decide)) (by decide) (by decide)
      (ld_skip 4 8 (Or.inl (by decide)) (by decide) (by decide) (memLoad32_store32_same _ _ _))))
  · exact ld_skip 8 0x14 (Or.inl (by decide)) (by decide) (by decide)
      (ld_skip 8 0x10 (Or.inl (by decide)) (by decide) (by decide)
      (ld_skip 8 0xC (Or.inl (by decide)) (by decide) (by decide) (memLoad32_store32_same _ _ _)))
  · exact ld_skip 0xC 0x14 (Or.inl (by decide)) (by decide) (by decide)
      (ld_skip 0xC 0x10 (Or.inl (by decide)) (by decide) (by decide) (memLoad32_store32_same _ _ _))
  · exact ld_skip 0x10 0x14 (Or.inl (by decide)) (by decide) (by decide) (memLoad32_store32_same _ _ _)

theorem pr_st8 (M : Word → BitVec 8) (a w : Word) :
    memStore8 (memStore8 (memStore8 (memStore8 M a (w.extractLsb' 0 8)) (a + 1) (w.extractLsb' 8 8)) (a + 2)
      (w.extractLsb' 16 8)) (a + 3) (w.extractLsb' 24 8) = memStore32 M a w := rfl

theorem pr_srl8 (x : Word) : aluEval .srl x 8 = x >>> 8 := rfl

theorem pr_srl16 (x : Word) : aluEval .srl x 16 = x >>> 16 := rfl

section
variable {M0 M1 Mf : Word → BitVec 8} {s out F : Word} {g g0 : Fin 32 → Word}

/-- The success tail at 0x9C: `signed`, `signatures`, and the version at
`out`, and the epilogue. The length of `signed` is in `s2` (its low byte)
and `s5` (its other three bytes). -/
theorem pr_9c {q1 q2 lo hi : Word} {l1 l2 v : Nat} {b12 b13 b14 b15 : BitVec 8}
    (E : PrEnv M0 M1 s out F g0) (hO : Out M1 Mf s 568) (h8 : g 8 = out) (hsp : g sp = F) (h9 : g 9 = q1)
    (h18 : g 18 = b12.zeroExtend 32) (h21 : g 21 = 0#8 ++ b15 ++ b14 ++ b13) (h19 : g 19 = q2)
    (h20 : g 20 = BitVec.ofNat 32 l2) (h10 : g a0 = lo) (h11 : g a1 = hi)
    (hW : (b15 ++ b14 ++ b13 ++ b12 : Word) = BitVec.ofNat 32 l1) (hv : hi.toNat * 2 ^ 32 + lo.toNat = v)
    (hfr : ∀ x, x ∉ prE → g x = g0 x) :
    WP tufParseRootCode TPR (prQ M0 s out g0 (.ok (q1, l1, q2, l2, v))) Mf 0x9C g := by
  have hoT := E.outT
  refine WP.aluImm pr_at_9c ?_; wn
  refine WP.aluImm pr_at_a0 ?_; wn
  refine WP.sw pr_at_a4 (by (try rsimp); rw [h8, add_lit_zero]; exact E.halo)
    (by (try rsimp); rw [h8, add_lit_zero]; exact tex_sepL hoT (by decide)) ?_; wn
  refine WP.sb pr_at_a6 (by (try rsimp); rw [h8]; exact hoT.sub (c := 4) (l := 1) (by decide)) ?_; wn
  refine WP.sb pr_at_aa (by (try rsimp); rw [h8]; exact hoT.sub (c := 5) (l := 1) (by decide)) ?_; wn
  refine WP.sb pr_at_ae (by (try rsimp); rw [h8]; exact hoT.sub (c := 6) (l := 1) (by decide)) ?_; wn
  refine WP.sb pr_at_b2 (by (try rsimp); rw [h8]; exact hoT.sub (c := 7) (l := 1) (by decide)) ?_; wn
  refine WP.sw pr_at_b6 (by (try rsimp); rw [h8]; exact aligned_add E.halo (k := 8) (by decide))
    (by (try rsimp); rw [h8]; exact hoT.sub (c := 8) (l := 4) (by decide)) ?_; wn
  refine WP.sw pr_at_ba (by (try rsimp); rw [h8]; exact aligned_add E.halo (k := 0xC) (by decide))
    (by (try rsimp); rw [h8]; exact hoT.sub (c := 0xC) (l := 4) (by decide)) ?_; wn
  refine WP.sw pr_at_be (by (try rsimp); rw [h8]; exact aligned_add E.halo (k := 0x10) (by decide))
    (by (try rsimp); rw [h8]; exact hoT.sub (c := 0x10) (l := 4) (by decide)) ?_; wn
  refine WP.sw pr_at_c0 (by (try rsimp); rw [h8]; exact aligned_add E.halo (k := 0x14) (by decide))
    (by (try rsimp); rw [h8]; exact hoT.sub (c := 0x14) (l := 4) (by decide)) ?_; wn
  refine WP.jal pr_at_c2 (by decide) ?_; wn
  (try rsimp)
  obtain ⟨x0, x1, x2, x3⟩ := pr_x b12 b13 b14 b15
  generalize hWd : b15 ++ b14 ++ b13 ++ b12 = W at x0 x1 x2 x3 hW
  rw [h8, h9, h18, h21, h19, h20, h10, h11, add_lit_zero, pr_srl8, pr_srl16, ri_ze,
    pr_e0, pr_e1, pr_e2, ← x0, ← x1, ← x2, ← x3, show out + 5 = out + 4 + 1 by rw [BitVec.add_assoc]; rfl,
    show out + 6 = out + 4 + 2 by rw [BitVec.add_assoc]; rfl, show out + 7 = out + 4 + 3 by rw [BitVec.add_assoc]; rfl,
    pr_st8, hW]
  obtain ⟨hOs, r0, r1, r2, r3, r4, r5⟩ := pr_st6 (M := Mf) (o := out) (a := q1) (b := BitVec.ofNat 32 l1)
    (c := q2) (d := BitVec.ofNat 32 l2) (e := lo) (w := hi) rfl
  exact pr_epi (by (try rsimp); exact hsp) (E.savedOut (E.saved hO) hOs) E.hsp0 E.hret E.halF E.hz0 (by keepz E.hz0)
    ⟨fun x hx ho => (hOs x ho).trans (E.agree hO x hx), r0, r1, r2, r3, by rw [r4, r5]; exact hv⟩

end

section
variable {M0 M1 Mk : Word → BitVec 8} {s out F : Word} {g0 : Fin 32 → Word}

theorem PrEnv.lowS (E : PrEnv M0 M1 s out F g0) {c w : Nat} (h : c + w ≤ 596) {b : Word} {l : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + l ≤ 2 ^ 32) : Sep (s + BitVec.ofNat 32 c) w b l :=
  lowSep (by have := E.hsw; rw [tex_toNat (by omega)]; omega) hb hbl

theorem PrEnv.lowF (E : PrEnv M0 M1 s out F g0) {c w : Nat} (h : c + w ≤ 64) {b : Word} {l : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + l ≤ 2 ^ 32) : Sep (F + BitVec.ofNat 32 c) w b l := by
  rw [E.Fc]; exact E.lowS (by omega) hb hbl

theorem PrEnv.fs (E : PrEnv M0 M1 s out F g0) {c n d k : Nat} (h : 532 + c + n ≤ d ∨ d + k ≤ 532 + c)
    (hc : c + n ≤ 64) (hd : d + k ≤ 596) : Sep (F + BitVec.ofNat 32 c) n (s + BitVec.ofNat 32 d) k := by
  rw [E.Fc]; exact sep_offsets s h (by omega) (by omega)

theorem PrEnv.bytes (E : PrEnv M0 M1 s out F g0) (hO : Out M1 Mk s 568) {q : Word} {l : Nat}
    (hS : Sep s 596 q l) : memBytes Mk q l = memBytes M0 q l :=
  memBytes_congr fun _ hi => E.agree hO _ (sep_pt hS hi)

theorem PrEnv.sp (E : PrEnv M0 M1 s out F g0) (d : Nat) (hd : d ≤ 532) :
    s + BitVec.ofNat 32 d + BitVec.ofNat 32 (532 - d) = F := by
  rw [add_ofNat_assoc, ← E.hF]; congr 2; omega

theorem PrEnv.wS (E : PrEnv M0 M1 s out F g0) {d k : Nat} (hd : d + k ≤ 596) :
    (s + BitVec.ofNat 32 d).toNat + k ≤ 0x40000000 := by
  have := E.hsw; rw [tex_toNat (by omega)]; omega

/-- What `parse_metadata` leaves outside its stack and its result is
outside the 568 bytes at `s`. -/
theorem PrEnv.pmOut (E : PrEnv M0 M1 s out F g0) {Ma Mb : Word → BitVec 8}
    (h : ∀ x, Sep x 1 s 532 → Sep x 1 (F + BitVec.ofNat 32 8) 16 → Mb x = Ma x) : Out Ma Mb s 568 :=
  fun x hx => h x (tex_sepR hx (by decide)) (by rw [E.Fc]; exact hx.subR (by decide))

end

theorem pr_or (a b : Word) : aluEval .or a b = a ||| b := rfl
theorem pr_sll8 (x : Word) : aluEval .sll x 8 = x <<< 8 := rfl
theorem pr_sll16 (x : Word) : aluEval .sll x 16 = x <<< 16 := rfl

theorem pr_add (F : Word) (a b : Nat) : F + BitVec.ofNat 32 a + BitVec.ofNat 32 b = F + BitVec.ofNat 32 (a + b) :=
  add_ofNat_assoc F a b

/-- `parse_root` after its prologue. -/
theorem pr_body {M0 : Word → BitVec 8} {s out p F : Word} {n : Nat} {g0 g : Fin 32 → Word}
    (E : PrEnv M0 (prM1 M0 F g0) s out F g0) (hsp : g sp = F) (h10 : g a0 = out) (h11 : g a1 = p)
    (h12 : g a2 = BitVec.ofNat 32 n) (hz : g 0 = 0) (hfr : ∀ x, x ∉ prE → g x = g0 x) (hn : n < 2 ^ 31)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n < 2 ^ 32) (hSp : Sep s 596 p n) :
    WP tufParseRootCode TPR (prQ M0 s out g0 (prRes p (prModel (memBytes M0 p n)))) (prM1 M0 F g0) 0x10 g := by
  generalize hM1 : prM1 M0 F g0 = M1 at E
  have hc1 := E.code (Mk := M1) (fun _ _ => rfl)
  refine WP.alu pr_at_10 ?_; wn
  refine WP.lui pr_at_12 ?_; wn
  refine WP.aluImm pr_at_16 ?_; wn
  refine WP.aluImm pr_at_1a ?_; wn
  refine WP.aluImm pr_at_1c ?_; wn
  refine WP.callPm (out := F + 8) (s := s) (p := p) (kq := TPR_KR) (n := n) (kl := 4)
    pr_at_1e pr_at_22 (by decide) (by decide) hc1.pm
    (by (try rsimp); rw [ev_add, hsp]) (by (try rsimp); exact h11) (by (try rsimp); exact h12)
    (by (try rsimp); (try rfl); (try decide)) (by (try rsimp); (try rw [hz]); (try rfl); (try decide))
    (by (try rsimp); rw [hsp]; exact E.hF.symm) E.hal (by have := E.hsw; omega) (tex_sepL E.hro (by decide))
    (aligned_add E.halF (k := 8) (by decide))
    (by have := E.FN (c := 8) (by decide); have := E.hsw; exact (by omega : (F + BitVec.ofNat 32 8).toNat + 16 ≤ 0x40000000))
    (show Sep (F + BitVec.ofNat 32 8) 16 s 532 by rw [E.Fc]; exact (tex_sepS (by decide) (by decide)).symm)
    hn hp0 hpn (tex_sepL hSp (by decide))
    (by decide) (tuf_sep_ro (tex_sepL E.hro (by decide)) (by decide) (by decide))
    (lowSep (by have := E.hsw; omega) (by decide) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) fun m2 hR => ?_
  rw [E.bytes (Mk := M1) (fun _ _ => rfl) hSp, tpr_kr hc1] at hR
  generalize m2.mem = M2 at hR
  have hO2 : Out M1 M2 s 568 := E.pmOut hR.frame
  refine WP.zero fun hz2 => ?_
  refine WP.lw pr_at_26 (by (try rsimp); rw [hsp]; exact aligned_add E.halF (k := 8) (by decide)) ?_; wn
  refine WP.lbu pr_at_28 ?_; wn
  simp only [prModel]
  rcases hpm : pmModel (memBytes M0 p n) (ascii!"root") with e | ⟨gp, gl, sq, sl⟩ <;> rw [hpm] at hR <;>
    simp only [pmRes, Except.map] at hR <;> (try dsimp only)
  · obtain ⟨-, t1, t2⟩ := hR
    refine WP.branch pr_at_2c (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hsp, t1] at eb; exact absurd eb (by decide)
    exact pr_82 E hO2 (by (try rsimp); (try rw [ev_mv hz]); exact h10) (by (try rsimp); exact hsp)
      (by (try rsimp); rw [hsp, ri_ze, show F + 0xC = F + BitVec.ofNat 32 8 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2)
      (by (try rsimp); (try exact hz)) (by keepz E.hz0)
  · obtain ⟨-, t1, t2, t3, t4⟩ := hR
    have hb := pmModel_bnd hpm
    rw [memBytes_length] at hb
    have htp : (p + BitVec.ofNat 32 gp).toNat = p.toNat + gp := tex_toNat (by omega)
    have hq0 := nx_q0 hp0 (n := gp + 1) (pos := gp) (by omega) (by omega)
    have a12 : F + 8 + 4 = F + 12 := by rw [BitVec.add_assoc]; rfl
    rw [a12] at t2
    have hW : M2 (F + 15) ++ M2 (F + 14) ++ M2 (F + 13) ++ M2 (F + 12) = BitVec.ofNat 32 gl := by
      rw [← t2]; unfold memLoad32
      rw [show F + 12 + 3 = F + 15 by rw [BitVec.add_assoc]; rfl, show F + 12 + 2 = F + 14 by rw [BitVec.add_assoc]; rfl,
        show F + 12 + 1 = F + 13 by rw [BitVec.add_assoc]; rfl]
    refine WP.branch pr_at_2c (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hsp, t1, hq0] at eb; exact absurd eb (by decide)
    refine WP.lbu pr_at_2e ?_; wn
    refine WP.lbu pr_at_32 ?_; wn
    refine WP.lbu pr_at_36 ?_; wn
    refine WP.lw pr_at_3a (by (try rsimp); rw [hsp]; exact aligned_add E.halF (k := 0x10) (by decide)) ?_; wn
    refine WP.aluImm pr_at_3c ?_; wn
    refine WP.alu pr_at_3e ?_; wn
    refine WP.aluImm pr_at_40 ?_; wn
    refine WP.lw pr_at_42 (by (try rsimp); rw [hsp]; exact aligned_add E.halF (k := 0x14) (by decide)) ?_; wn
    refine WP.alu pr_at_44 ?_; wn
    refine WP.aluImm pr_at_48 ?_; wn
    refine WP.alu pr_at_4c ?_; wn
    refine WP.lui pr_at_50 ?_; wn
    refine WP.aluImm pr_at_54 ?_; wn
    refine WP.aluImm pr_at_58 ?_; wn
    refine WP.aluImm pr_at_5a ?_; wn
    refine WP.alu pr_at_5c ?_; wn
    have hSg : Sep s 596 (p + BitVec.ofNat 32 gp) gl := hSp.subR (by omega)
    refine WP.callField (tb := TPM_JF) (out := F + 0x1C) (s := s + BitVec.ofNat 32 272)
      (p := p + BitVec.ofNat 32 gp) (kq := TPR_KV) (n := gl) (kl := 7)
      pr_at_5e pr_at_62 (by decide) (by decide) (by decide) (E.code hO2).pm.fieldC
      (by (try rsimp); rw [ev_add, hsp]) (by (try rsimp); (try simp only [ev0]); rw [hsp]; exact t1)
      (by (try rsimp); simp only [hsp, pr_or, pr_sll8, pr_sll16]; rw [pr_s5, pr_w]; exact hW)
      (by (try rsimp); (try rfl); (try decide)) (by (try rsimp); (try simp only [ev0]); (try rfl))
      (by (try rsimp); rw [hsp]; exact (E.sp 272 (by decide)).symm)
      (aligned_add E.hal (k := 272) (by decide)) (aligned_add E.halF (k := 0x1C) (by decide))
      (by have := E.wS (d := 272) (k := 260) (by decide); omega) (by decide)
      (by rw [htp]; omega) (by rw [htp]; omega)
      (tuf_fieldSep (E.wS (by decide)) (E.hro.sub (by decide))) ((hSp.sub (by decide)).subR (by omega))
      (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) (E.fs (Or.inr (by decide)) (by decide) (by decide))
      (E.lowF (by decide) (by decide) (by decide)) (E.lowS (by decide) (by decide) (by decide))
      (E.lowF (by decide) (by decide) (by decide)) fun m3 hR3 => ?_
    have hsl : slice (memBytes M0 p n) gp gl = memBytes M0 (p + BitVec.ofNat 32 gp) gl :=
      tuf_memBytes_drop_take (by omega)
    rw [E.bytes hO2 hSg, tpr_kv (E.code hO2)] at hR3
    rw [hsl]
    generalize m3.mem = M3 at hR3
    obtain ⟨Mb, hOb, hFR⟩ := hR3
    have hO3 : Out M1 M3 s 568 :=
      hO2.trans ((Out.upK rfl hOb (by decide)).trans (Out.upK (c := 560) (E.Fc 0x1C).symm hFR.out (by decide)))
    refine WP.zero fun hz3 => ?_
    refine WP.lw pr_at_66 (by (try rsimp); rw [hsp]; exact aligned_add E.halF (k := 0x1C) (by decide)) ?_; wn
    rcases hof : objField (memBytes M0 (p + BitVec.ofNat 32 gp) gl) (ascii!"version") with e | ⟨vp, vl⟩ <;>
      rw [hof] at hFR <;> simp only [fieldRes, Except.map] at hFR <;> (try dsimp only)
    · obtain ⟨-, t5, t6⟩ := hFR
      refine WP.branch pr_at_68 (fun _ => ?_) (fun eb => ?_) <;> wn
      rotate_left
      · exfalso; (try rsimp at eb); rw [hsp, t5] at eb; exact absurd eb (by decide)
      refine WP.lbu pr_at_8c ?_; wn
      refine WP.jal pr_at_90 (by decide) ?_; wn
      exact pr_c8 E hO3 (by (try rsimp); (try rw [ev_mv hz]); exact h10) (by (try rsimp); exact hsp)
        (by (try rsimp); rw [hsp, ri_ze, show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t6)
        (by (try rsimp); (try exact hz)) (by keepz E.hz0)
    · obtain ⟨-, t5, t6⟩ := hFR
      have hv := objField_val hof
      rw [memBytes_length] at hv
      have t6' : memLoad32 M3 (F + 0x20) = BitVec.ofNat 32 vl := by
        rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t6
      have hq1 := nx_q0 (p := p + BitVec.ofNat 32 gp) (by rw [htp]; omega) (n := gl) (pos := vp) (by rw [htp]; omega)
        hv.1
      refine WP.branch pr_at_68 (fun eb => ?_) (fun _ => ?_) <;> wn
      · exfalso; (try rsimp at eb); rw [hsp, t5, hq1] at eb; exact absurd eb (by decide)
      refine WP.lw pr_at_6a (by (try rsimp); rw [hsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
      refine WP.aluImm pr_at_6c ?_; wn
      have hSv : Sep s 596 (p + BitVec.ofNat 32 gp + BitVec.ofNat 32 vp) vl := by
        rw [add_ofNat_assoc]; exact hSp.subR (by omega)
      refine WP.callU64 (out := F + 8) (s := s + BitVec.ofNat 32 500) (p := p + BitVec.ofNat 32 gp + BitVec.ofNat 32 vp)
        (n := vl) pr_at_6e pr_at_72 (by decide) (by decide) (E.code hO3).u64 (E.code hO3).aad
        (by (try rsimp); rw [ev_add, hsp]) (by (try rsimp); rw [hsp]; exact t5) (by (try rsimp); rw [hsp]; exact t6')
        (by (try rsimp); rw [hsp]; exact (E.sp 500 (by decide)).symm) (by omega)
        (aligned_add E.hal (k := 500) (by decide)) (aligned_add E.halF (k := 8) (by decide)) (E.wS (by decide))
        (by rw [add_ofNat_assoc]; exact (hSp.sub (by decide)).subR (by omega))
        (E.fs (c := 8) (Or.inr (by decide)) (by decide) (by decide))
        (by have := E.FN (c := 8) (by decide); have := E.hsw;
            exact (by omega : (F + BitVec.ofNat 32 8).toNat + 16 ≤ 0x40000000))
        (E.lowS (by decide) (by decide) (by decide)) (E.lowF (c := 8) (by decide) (by decide) (by decide))
        fun m4 hR4 => ?_
      rw [E.bytes hO3 hSv] at hR4
      have hsl2 : slice (memBytes M0 (p + BitVec.ofNat 32 gp) gl) vp vl =
          memBytes M0 (p + BitVec.ofNat 32 gp + BitVec.ofNat 32 vp) vl := tuf_memBytes_drop_take (by omega)
      rw [hsl2]
      generalize m4.mem = M4 at hR4
      obtain ⟨Mc, hOc, hU⟩ := hR4
      have hO4 : Out M1 M4 s 568 :=
        hO3.trans ((Out.upK rfl hOc (by decide)).trans (Out.upK (c := 540) (E.Fc 8).symm hU.outside (by decide)))
      refine WP.zero fun hz4 => ?_
      refine WP.lbu pr_at_76 ?_; wn
      rcases hu : u64Val (memBytes M0 (p + BitVec.ofNat 32 gp + BitVec.ofNat 32 vp) vl) with _ | v <;>
        rw [hu] at hU <;> (try dsimp only)
      · obtain ⟨-, u1, u2⟩ := hU
        refine WP.branch pr_at_7a (fun eb => ?_) (fun _ => ?_) <;> wn
        · exfalso; (try rsimp at eb); rw [hsp, u1] at eb; exact absurd eb (by decide)
        refine WP.lbu pr_at_7c ?_; wn
        refine WP.jal pr_at_80 (by decide) ?_; wn
        simp only [prRes, Except.map]
        exact pr_c8 E hO4 (by (try rsimp); (try rw [ev_mv hz]); exact h10) (by (try rsimp); exact hsp)
          (by (try rsimp); rw [hsp, ri_ze, show F + 9 = F + 8 + 1 by rw [BitVec.add_assoc]; rfl]; exact u2)
          (by (try rsimp); (try exact hz)) (by keepz E.hz0)
      · obtain ⟨-, u1, u2⟩ := hU
        refine WP.branch pr_at_7a (fun _ => ?_) (fun eb => ?_) <;> wn
        rotate_left
        · exfalso; (try rsimp at eb); rw [hsp, u1] at eb; exact absurd eb (by decide)
        refine WP.lw pr_at_92 (by (try rsimp); rw [hsp]; exact aligned_add E.halF (k := 0x10) (by decide)) ?_; wn
        refine WP.lw pr_at_94 (by (try rsimp); rw [hsp]; exact aligned_add E.halF (k := 0x14) (by decide)) ?_; wn
        refine WP.alu pr_at_96 ?_; wn
        have u2' : (memLoad32 M4 (F + 20)).toNat * 2 ^ 32 + (memLoad32 M4 (F + 16)).toNat = v := by
          rw [show F + 20 = F + 8 + 12 by rw [BitVec.add_assoc]; rfl, show F + 16 = F + 8 + 8 by rw [BitVec.add_assoc]; rfl]
          exact u2
        by_cases hv0 : v = 0
        · subst hv0
          simp only [↓reduceIte, prRes, Except.map]
          have e1 : (memLoad32 M4 (F + 16)).toNat = 0 := by omega
          have e2 : (memLoad32 M4 (F + 20)).toNat = 0 := by omega
          have l1 : memLoad32 M4 (F + 16) = 0 := BitVec.eq_of_toNat_eq (by rw [e1]; rfl)
          have l2 : memLoad32 M4 (F + 20) = 0 := BitVec.eq_of_toNat_eq (by rw [e2]; rfl)
          refine WP.branch pr_at_9a (fun _ => ?_) (fun eb => ?_) <;> wn
          rotate_left
          · exfalso; (try rsimp at eb); (try simp only [pr_or] at eb); rw [hsp, l1, l2] at eb
            exact absurd eb (by decide)
          refine WP.aluImm pr_at_c4 ?_; wn
          exact pr_c8 E hO4 (by (try rsimp); (try rw [ev_mv hz]); exact h10) (by (try rsimp); exact hsp)
            (by (try rsimp); (try simp only [ev0]); (try rfl); (try decide))
            (by (try rsimp); (try exact hz)) (by keepz E.hz0)
        · simp only [hv0, ↓reduceIte, prRes, Except.map]
          refine WP.branch pr_at_9a (fun eb => ?_) (fun _ => ?_) <;> wn
          · exfalso; (try rsimp at eb); (try simp only [pr_or] at eb); rw [hsp] at eb
            have h0 := BitVec.or_eq_zero_iff.mp (beq_iff_eq.mp eb)
            exact hv0 (by rw [← u2', h0.1, h0.2]; rfl)
          exact pr_9c E hO4 (by (try rsimp); (try rw [ev_mv hz]); exact h10) (by (try rsimp); exact hsp)
            (by (try rsimp); rw [hsp]; exact t1) (by (try rsimp); rw [hsp])
            (by (try rsimp); simp only [hsp, pr_or, pr_sll8, pr_sll16]; exact pr_s5 _ _ _)
            (by (try rsimp); rw [hsp, show F + 16 = F + 8 + 8 by rw [BitVec.add_assoc]; rfl]; exact t3)
            (by (try rsimp); rw [hsp, show F + 20 = F + 8 + 12 by rw [BitVec.add_assoc]; rfl]; exact t4)
            (by (try rsimp); rw [hsp]) (by (try rsimp); rw [hsp]) hW u2' (by keepz E.hz0)

end C3.RV32
