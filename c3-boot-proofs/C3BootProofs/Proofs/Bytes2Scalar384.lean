import C3BootProofs.Proofs.FromBeSliceTrunc
import C3BootProofs.Proofs.Norm12
import C3BootProofs.Proofs.P384Scalar
import C3BootProofs.Proofs.LeadingZeros
import C3BootProofs.Proofs.Panic
import C3BootProofs.Proofs.CtEq
import C3BootProofs.Proofs.CtAssign

/-!
# `ecdsa::hazmat::bytes2scalar::<NistP384>`, as compiled

`bytes2scalar` reads the leftmost bytes of a message digest, up to the
order's 48, as a big-endian number `x`, subtracts the order `n` once when
`x ≥ n`, and converts the result to Montgomery form with
`ConstMontyForm::new`. The scalar it returns is `x · 2^384 mod n`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem bz_at_0 : fetchRel bytes2scalar384Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF40, 2) := by decide
theorem bz_at_2 : fetchRel bytes2scalar384Code 0x2 = some (.store .sw sp ra 0xBC, 2) := by decide
theorem bz_at_4 : fetchRel bytes2scalar384Code 0x4 = some (.store .sw sp (8 : Fin 32) 0xB8, 2) := by decide
theorem bz_at_6 : fetchRel bytes2scalar384Code 0x6 = some (.store .sw sp (9 : Fin 32) 0xB4, 2) := by decide
theorem bz_at_8 : fetchRel bytes2scalar384Code 0x8 = some (.store .sw sp (18 : Fin 32) 0xB0, 2) := by decide
theorem bz_at_a : fetchRel bytes2scalar384Code 0xA = some (.store .sw sp (19 : Fin 32) 0xAC, 2) := by decide
theorem bz_at_c : fetchRel bytes2scalar384Code 0xC = some (.store .sw sp (20 : Fin 32) 0xA8, 2) := by decide
theorem bz_at_e : fetchRel bytes2scalar384Code 0xE = some (.store .sw sp (21 : Fin 32) 0xA4, 2) := by decide
theorem bz_at_10 : fetchRel bytes2scalar384Code 0x10 = some (.store .sw sp (22 : Fin 32) 0xA0, 2) := by decide
theorem bz_at_12 : fetchRel bytes2scalar384Code 0x12 = some (.store .sw sp (23 : Fin 32) 0x9C, 2) := by decide
theorem bz_at_14 : fetchRel bytes2scalar384Code 0x14 = some (.alu .add (20 : Fin 32) x0 a2, 2) := by decide
theorem bz_at_16 : fetchRel bytes2scalar384Code 0x16 = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem bz_at_18 : fetchRel bytes2scalar384Code 0x18 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem bz_at_1a : fetchRel bytes2scalar384Code 0x1A = some (.lui (22 : Fin 32) 0x3FCC5000, 4) := by decide
theorem bz_at_1e : fetchRel bytes2scalar384Code 0x1E = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0xFFFFFDC4, 4) := by decide
theorem bz_at_22 : fetchRel bytes2scalar384Code 0x22 = some (.aluImm .add a1 x0 0xC, 2) := by decide
theorem bz_at_24 : fetchRel bytes2scalar384Code 0x24 = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem bz_at_26 : fetchRel bytes2scalar384Code 0x26 = some (.aluImm .add (23 : Fin 32) x0 0xC, 2) := by decide
theorem bz_at_28 : fetchRel bytes2scalar384Code 0x28 = some (.auipc ra 0xA000, 4) := by decide
theorem bz_at_2c : fetchRel bytes2scalar384Code 0x2C = some (.jalr ra ra 0x3E8, 4) := by decide
theorem bz_at_30 : fetchRel bytes2scalar384Code 0x30 = some (.aluImm .add a1 x0 0x180, 4) := by decide
theorem bz_at_34 : fetchRel bytes2scalar384Code 0x34 = some (.alu .sub (21 : Fin 32) a1 a0, 4) := by decide
theorem bz_at_38 : fetchRel bytes2scalar384Code 0x38 = some (.aluImm .and a0 (21 : Fin 32) 0x7, 4) := by decide
theorem bz_at_3c : fetchRel bytes2scalar384Code 0x3C = some (.aluImm .srl a1 (21 : Fin 32) 0x3, 4) := by decide
theorem bz_at_40 : fetchRel bytes2scalar384Code 0x40 = some (.alu .sltu a0 x0 a0, 4) := by decide
theorem bz_at_44 : fetchRel bytes2scalar384Code 0x44 = some (.alu .add a0 a0 a1, 2) := by decide
theorem bz_at_46 : fetchRel bytes2scalar384Code 0x46 = some (.store .sb sp x0 0x4, 4) := by decide
theorem bz_at_4a : fetchRel bytes2scalar384Code 0x4A = some (.store .sw sp a0 0x8, 2) := by decide
theorem bz_at_4c : fetchRel bytes2scalar384Code 0x4C = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem bz_at_4e : fetchRel bytes2scalar384Code 0x4E = some (.auipc ra 0x0, 4) := by decide
theorem bz_at_52 : fetchRel bytes2scalar384Code 0x52 = some (.jalr ra ra 0xFFFFFBBC, 4) := by decide
theorem bz_at_56 : fetchRel bytes2scalar384Code 0x56 = some (.branch .bltu (20 : Fin 32) a0 0x6, 4) := by decide
theorem bz_at_5a : fetchRel bytes2scalar384Code 0x5A = some (.alu .add (20 : Fin 32) x0 a0, 2) := by decide
theorem bz_at_5c : fetchRel bytes2scalar384Code 0x5C = some (.aluImm .add a0 sp 0x3C, 2) := by decide
theorem bz_at_5e : fetchRel bytes2scalar384Code 0x5E = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem bz_at_60 : fetchRel bytes2scalar384Code 0x60 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem bz_at_62 : fetchRel bytes2scalar384Code 0x62 = some (.alu .add a3 x0 (21 : Fin 32), 2) := by decide
theorem bz_at_64 : fetchRel bytes2scalar384Code 0x64 = some (.aluImm .add (9 : Fin 32) sp 0x3C, 2) := by decide
theorem bz_at_66 : fetchRel bytes2scalar384Code 0x66 = some (.auipc ra 0x0, 4) := by decide
theorem bz_at_6a : fetchRel bytes2scalar384Code 0x6A = some (.jalr ra ra 0xFFFFFD34, 4) := by decide
theorem bz_at_6e : fetchRel bytes2scalar384Code 0x6E = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem bz_at_70 : fetchRel bytes2scalar384Code 0x70 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem bz_at_74 : fetchRel bytes2scalar384Code 0x74 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem bz_at_76 : fetchRel bytes2scalar384Code 0x76 = some (.aluImm .add (8 : Fin 32) sp 0xC, 2) := by decide
theorem bz_at_78 : fetchRel bytes2scalar384Code 0x78 = some (.auipc ra 0x12000, 4) := by decide
theorem bz_at_7c : fetchRel bytes2scalar384Code 0x7C = some (.jalr ra ra 0xFFFFF87E, 4) := by decide
theorem bz_at_80 : fetchRel bytes2scalar384Code 0x80 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem bz_at_82 : fetchRel bytes2scalar384Code 0x82 = some (.branch .beq (23 : Fin 32) x0 0x22, 4) := by decide
theorem bz_at_86 : fetchRel bytes2scalar384Code 0x86 = some (.load .lw a0 (9 : Fin 32) 0x0, 2) := by decide
theorem bz_at_88 : fetchRel bytes2scalar384Code 0x88 = some (.load .lw a1 (22 : Fin 32) 0x0, 4) := by decide
theorem bz_at_8c : fetchRel bytes2scalar384Code 0x8C = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem bz_at_90 : fetchRel bytes2scalar384Code 0x90 = some (.jalr ra ra 0x3A4, 4) := by decide
theorem bz_at_94 : fetchRel bytes2scalar384Code 0x94 = some (.alu .add a2 x0 a1, 2) := by decide
theorem bz_at_96 : fetchRel bytes2scalar384Code 0x96 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem bz_at_98 : fetchRel bytes2scalar384Code 0x98 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem bz_at_9a : fetchRel bytes2scalar384Code 0x9A = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0x4, 2) := by decide
theorem bz_at_9c : fetchRel bytes2scalar384Code 0x9C = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem bz_at_9e : fetchRel bytes2scalar384Code 0x9E = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem bz_at_a0 : fetchRel bytes2scalar384Code 0xA0 = some (.branch .bne (23 : Fin 32) x0 0xFFFFFFE6, 4) := by decide
theorem bz_at_a4 : fetchRel bytes2scalar384Code 0xA4 = some (.aluImm .srl a0 a2 0x1F, 4) := by decide
theorem bz_at_a8 : fetchRel bytes2scalar384Code 0xA8 = some (.auipc ra 0xA000, 4) := by decide
theorem bz_at_ac : fetchRel bytes2scalar384Code 0xAC = some (.jalr ra ra 0x7AC, 4) := by decide
theorem bz_at_b0 : fetchRel bytes2scalar384Code 0xB0 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem bz_at_b4 : fetchRel bytes2scalar384Code 0xB4 = some (.auipc ra 0xF000, 4) := by decide
theorem bz_at_b8 : fetchRel bytes2scalar384Code 0xB8 = some (.jalr ra ra 0xFFFFF9B2, 4) := by decide
theorem bz_at_bc : fetchRel bytes2scalar384Code 0xBC = some (.aluImm .and a4 a0 0xFF, 4) := by decide
theorem bz_at_c0 : fetchRel bytes2scalar384Code 0xC0 = some (.aluImm .add a0 sp 0x3C, 2) := by decide
theorem bz_at_c2 : fetchRel bytes2scalar384Code 0xC2 = some (.aluImm .add a1 x0 0xC, 2) := by decide
theorem bz_at_c4 : fetchRel bytes2scalar384Code 0xC4 = some (.aluImm .add a2 sp 0xC, 2) := by decide
theorem bz_at_c6 : fetchRel bytes2scalar384Code 0xC6 = some (.aluImm .add a3 x0 0xC, 2) := by decide
theorem bz_at_c8 : fetchRel bytes2scalar384Code 0xC8 = some (.aluImm .add (19 : Fin 32) sp 0x3C, 4) := by decide
theorem bz_at_cc : fetchRel bytes2scalar384Code 0xCC = some (.aluImm .add (9 : Fin 32) x0 0xC, 2) := by decide
theorem bz_at_ce : fetchRel bytes2scalar384Code 0xCE = some (.auipc ra 0xA000, 4) := by decide
theorem bz_at_d2 : fetchRel bytes2scalar384Code 0xD2 = some (.jalr ra ra 0x6C8, 4) := by decide
theorem bz_at_d6 : fetchRel bytes2scalar384Code 0xD6 = some (.aluImm .add a0 sp 0x6C, 2) := by decide
theorem bz_at_d8 : fetchRel bytes2scalar384Code 0xD8 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem bz_at_dc : fetchRel bytes2scalar384Code 0xDC = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem bz_at_de : fetchRel bytes2scalar384Code 0xDE = some (.aluImm .add (8 : Fin 32) sp 0x6C, 2) := by decide
theorem bz_at_e0 : fetchRel bytes2scalar384Code 0xE0 = some (.auipc ra 0x12000, 4) := by decide
theorem bz_at_e4 : fetchRel bytes2scalar384Code 0xE4 = some (.jalr ra ra 0xFFFFF816, 4) := by decide
theorem bz_at_e8 : fetchRel bytes2scalar384Code 0xE8 = some (.branch .beq (9 : Fin 32) x0 0x10, 2) := by decide
theorem bz_at_ea : fetchRel bytes2scalar384Code 0xEA = some (.load .lw a0 (19 : Fin 32) 0x0, 4) := by decide
theorem bz_at_ee : fetchRel bytes2scalar384Code 0xEE = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x4, 2) := by decide
theorem bz_at_f0 : fetchRel bytes2scalar384Code 0xF0 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem bz_at_f2 : fetchRel bytes2scalar384Code 0xF2 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem bz_at_f4 : fetchRel bytes2scalar384Code 0xF4 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem bz_at_f6 : fetchRel bytes2scalar384Code 0xF6 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFF4, 2) := by decide
theorem bz_at_f8 : fetchRel bytes2scalar384Code 0xF8 = some (.aluImm .add a1 sp 0x6C, 2) := by decide
theorem bz_at_fa : fetchRel bytes2scalar384Code 0xFA = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem bz_at_fc : fetchRel bytes2scalar384Code 0xFC = some (.auipc ra 0x11000, 4) := by decide
theorem bz_at_100 : fetchRel bytes2scalar384Code 0x100 = some (.jalr ra ra 0xFFFFFE8A, 4) := by decide
theorem bz_at_104 : fetchRel bytes2scalar384Code 0x104 = some (.load .lw ra sp 0xBC, 2) := by decide
theorem bz_at_106 : fetchRel bytes2scalar384Code 0x106 = some (.load .lw (8 : Fin 32) sp 0xB8, 2) := by decide
theorem bz_at_108 : fetchRel bytes2scalar384Code 0x108 = some (.load .lw (9 : Fin 32) sp 0xB4, 2) := by decide
theorem bz_at_10a : fetchRel bytes2scalar384Code 0x10A = some (.load .lw (18 : Fin 32) sp 0xB0, 2) := by decide
theorem bz_at_10c : fetchRel bytes2scalar384Code 0x10C = some (.load .lw (19 : Fin 32) sp 0xAC, 2) := by decide
theorem bz_at_10e : fetchRel bytes2scalar384Code 0x10E = some (.load .lw (20 : Fin 32) sp 0xA8, 2) := by decide
theorem bz_at_110 : fetchRel bytes2scalar384Code 0x110 = some (.load .lw (21 : Fin 32) sp 0xA4, 2) := by decide
theorem bz_at_112 : fetchRel bytes2scalar384Code 0x112 = some (.load .lw (22 : Fin 32) sp 0xA0, 2) := by decide
theorem bz_at_114 : fetchRel bytes2scalar384Code 0x114 = some (.load .lw (23 : Fin 32) sp 0x9C, 2) := by decide
theorem bz_at_116 : fetchRel bytes2scalar384Code 0x116 = some (.aluImm .add sp sp 0xC0, 2) := by decide
theorem bz_at_118 : fetchRel bytes2scalar384Code 0x118 = some (.jalr x0 ra 0x0, 2) := by decide
end

abbrev BS : Word := BitVec.ofNat 32 bytes2scalar384Address

/-- Where `bytes2scalar` calls `borrowing_sub`, from its start `P`. -/
abbrev bzBsub (P : Word) : Word := P + 0xFFFFF430

/-- The end of a subtraction round, from 0x94: keep the borrow, store the
difference, and advance the pointers and the count. -/
def bzSubTail : List BInstr :=
  [.alu .add a2 x0 a1, .aluImm .add (9 : Fin 32) (9 : Fin 32) 4, .sw (8 : Fin 32) a0 0,
   .aluImm .add (22 : Fin 32) (22 : Fin 32) 4, .aluImm .add (8 : Fin 32) (8 : Fin 32) 4,
   .aluImm .add (23 : Fin 32) (23 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem bzSubTail_end : blockEnd bytes2scalar384Code 0x94 bzSubTail = some 0xA0 := by decide
end

set_option maxRecDepth 20000 in
theorem bzSubTail_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock bzSubTail (M, f)).1 = memStore32 M (f (8 : Fin 32) + 0) (f a0) ∧
    (runBlock bzSubTail (M, f)).2 a2 = f a1 ∧
    (runBlock bzSubTail (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 4 ∧
    (runBlock bzSubTail (M, f)).2 (22 : Fin 32) = f (22 : Fin 32) + 4 ∧
    (runBlock bzSubTail (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 4 ∧
    (runBlock bzSubTail (M, f)).2 (23 : Fin 32) = f (23 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ a2 → q ≠ (9 : Fin 32) → q ≠ (22 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (23 : Fin 32) →
      (runBlock bzSubTail (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, bzSubTail]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q q2 qnp qxp qd qc => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte, hz]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, qnp, qxp, qd, qc]

theorem bzSubTail_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f (8 : Fin 32) + 0).toNat % 4 = 0) (hs : Sep (f (8 : Fin 32) + 0) 4 base len) :
    BlockOk base len bzSubTail (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, bzSubTail, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h, hs⟩

set_option maxRecDepth 20000 in
/-- **One round of the subtraction**, from 0x86: subtract limb `i` of the
order at `xp` and the borrow from limb `i` of the number at `np`, and store
the difference at limb `i` of the buffer at `D`. `borrowing_sub` also
writes the word below `sp`. -/
theorem bz_sub_iter {M : Word → BitVec 8} {P F np xp D b : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x86 (reg n)) (hc : CodeIn M P bytes2scalar384Code) (hb : CodeIn M (bzBsub P) borrowingSubCode)
    (hP : P.toNat % 2 = 0) (hi : i < 12) (hF : F.toNat % 4 = 0) (hnp : np.toNat % 4 = 0)
    (hxp : xp.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (bzBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P bytes2scalar384Code.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P bytes2scalar384Code.length)
    (rsp : reg n sp = F) (rnp : reg n (9 : Fin 32) = np + BitVec.ofNat 32 (4 * i))
    (rxp : reg n (22 : Fin 32) = xp + BitVec.ofNat 32 (4 * i)) (rd : reg n (8 : Fin 32) = D + BitVec.ofNat 32 (4 * i))
    (rc : reg n (23 : Fin 32) = BitVec.ofNat 32 (12 - i)) (ra2 : reg n a2 = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < 12 then 0x86 else 0xA4) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' a2 = bsubB (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' (9 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (22 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (23 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (22 : Fin 32) →
        q ≠ (8 : Fin 32) → q ≠ (23 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc bz_at_86 (off' := 0x88) (by decide)
    (by rw [rnp, add_lit_zero]; exact aligned_add hnp (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.lw hc bz_at_88 (off' := 0x8C) (by decide)
    (by rw [upd_ne (by decide) (by decide), rxp, add_lit_zero]; exact aligned_add hxp (by omega))
  rw [rnp, add_lit_zero] at u2
  have f0 : upd (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (22 : Fin 32) + 0)) a0 =
      memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by simp +decide [upd]
  have f1 : upd (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (22 : Fin 32) + 0)) a1 =
      memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) := by
    simp +decide only [upd, ↓reduceIte]; rw [rxp, add_lit_zero]
  have u2' := u2.self
  have g2a0 : reg n2 a0 = memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f0]
  have g2a1 : reg n2 a1 = memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f1]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q q0 q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1]
  obtain ⟨n3, c3, u3, a03, a13, sp3, fr3, mem3⟩ := u2'.bsubCall hc hb (even_at P hP 0xFFFFF430 (by decide))
    bz_at_8c bz_at_90 (by rw [BitVec.add_assoc, BitVec.add_assoc,
      show BitVec.ofNat 32 0x8C + ((0xFFFFF000 : Word) + 0x3A4) = 0xFFFFF430 by decide]) (even_at P hP (0x8C + 8) (by decide))
    (by rw [k2 sp (by decide) (by decide), rsp]) hF sFB
  rw [g2a0, g2a1, k2 a2 (by decide) (by decide), ra2] at a03 a13
  have hc3 : CodeIn n3.mem P bytes2scalar384Code := fun j hj => by
    rw [mem3 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n3 q = reg n q := fun q q0 q1 q2 q3 q4 qr =>
    by rw [fr3 q q0 q1 q2 q3 q4 qr, k2 q q0 q1]
  have ed : reg n3 (8 : Fin 32) + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rd, add_lit_zero]
  obtain ⟨n4, c4, u4⟩ := St.block bzSubTail u3 hc3 bzSubTail_end
    (bzSubTail_ok (by rw [ed]; exact aligned_add hD (by omega)) (by rw [ed]; exact sDC))
  obtain ⟨em4, t2, tnp, txp, td, tc, tk⟩ := bzSubTail_run (M := n3.mem) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [em4, ed, a03] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock bzSubTail (n3.mem, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) hc3 sDC
  have ec : reg n4 (23 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) := by
    rw [g4, tc, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rc, cnt12_dec i hi]
  have hb4 : branchTaken .bne (reg n4 (23 : Fin 32)) (reg n4 x0) = decide (i + 1 < 12) := by
    rw [ec, u4'.zero]; exact cnt12_ne i hi
  have post : ∀ n5 : Machine, (∀ q, reg n5 q = reg n4 q) →
      reg n5 a2 = bsubB (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n5 sp = F ∧ reg n5 (9 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (22 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (8 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (23 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (22 : Fin 32) →
        q ≠ (8 : Fin 32) → q ≠ (23 : Fin 32) → reg n5 q = reg n q := fun n5 h5 => by
    refine ⟨by rw [h5, g4, t2, a13], by rw [h5, g4, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3],
      ?_, ?_, ?_, by rw [h5, ec], fun q q0 q1 q2 q3 q4 qr qnp qxp qd qc => ?_⟩
    · rw [h5, g4, tnp, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rnp, ptr4]
    · rw [h5, g4, txp, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rxp, ptr4]
    · rw [h5, g4, td, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rd, ptr4]
    · rw [h5, g4, tk q q2 qnp qxp qd qc, k3 q q0 q1 q2 q3 q4 qr]
  by_cases hl : i + 1 < 12
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x86 bz_at_a0 (by decide) (by rw [hb4]; exact decide_eq_true hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      mem3, post n5 u5.regs⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0xA4 bz_at_a0 (by decide) (by rw [hb4]; exact decide_eq_false hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      mem3, post n5 u5.regs⟩

set_option exponentiation.threshold 400 in
/-- **The subtraction**, from round `i` to its end at 0xA4: the buffer at
`D` gets the number at `np` minus the order at `xp`, and `a2` the borrow out
as a mask. -/
theorem bz_sub_loop {P F np xp D : Word} {M0 : Word → BitVec 8} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hnp : np.toNat % 4 = 0) (hxp : xp.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 48 ≤ 2 ^ 32)
    (sFN : Sep (F + 0xFFFFFFFC) 4 np 48) (sFX : Sep (F + 0xFFFFFFFC) 4 xp 48) (sFD : Sep (F + 0xFFFFFFFC) 4 D 48)
    (sDN : Sep D 48 np 48) (sDX : Sep D 48 xp 48)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (bzBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P bytes2scalar384Code.length)
    (sDB : Sep D 48 (bzBsub P) borrowingSubCode.length) (sDC : Sep D 48 P bytes2scalar384Code.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x86 (reg n) → CodeIn M P bytes2scalar384Code → CodeIn M (bzBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 np i + 2 ^ (32 * i) * maskBit b = accV M0 xp i + accV M D i →
      reg n sp = F → reg n (9 : Fin 32) = np + BitVec.ofNat 32 (4 * i) →
      reg n (22 : Fin 32) = xp + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (23 : Fin 32) = BitVec.ofNat 32 (12 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0xA4 (reg n') ∧ CodeIn M' P bytes2scalar384Code ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 np 12 + 2 ^ (32 * 12) * maskBit (reg n' a2) = accV M0 xp 12 + accV M' D 12 ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (22 : Fin 32) →
          q ≠ (8 : Fin 32) → q ≠ (23 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x86 (reg n) → CodeIn M P bytes2scalar384Code → CodeIn M (bzBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 np i + 2 ^ (32 * i) * maskBit b = accV M0 xp i + accV M D i →
      reg n sp = F → reg n (9 : Fin 32) = np + BitVec.ofNat 32 (4 * i) →
      reg n (22 : Fin 32) = xp + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (23 : Fin 32) = BitVec.ofNat 32 (12 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0x86 else 0xA4) (reg n') ∧
        CodeIn M' P bytes2scalar384Code ∧ CodeIn M' (bzBsub P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 np (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' a2) = accV M0 xp (i + 1) + accV M' D (i + 1) ∧
        reg n' sp = F ∧ reg n' (9 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (22 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (23 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (22 : Fin 32) →
          q ≠ (8 : Fin 32) → q ≠ (23 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    obtain ⟨n1, Mb, c1, u1, hMb, e2, esp, enp, exp, ed, ec, fr⟩ := bz_sub_iter (i := i) s hc hb hP hi hF hnp hxp hD
      sFB sFC (sDC.sub (by omega)) rsp rnp rxp rd rc ra2
    have eA : memLoad32 M (np + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    have eN : memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFX.subR (by omega)) (sDX.subR (by omega))
    rw [eA, eN] at u1 e2
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb (bzBsub P) borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb P bytes2scalar384Code := fun j hj => by
      rw [hMb _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    refine ⟨n1, _, c1, u1, CodeIn.store32 hCb (sDC.sub (by omega)), CodeIn.store32 hDb (sDB.sub (by omega)),
      fun x hx hd => ?_, by rw [e2]; exact bm, ?_, esp, enp, exp, ed, ec, fr⟩
    · rw [memStore32_get_sep (hd.sub (c := 4 * i) (l := 4) (by omega)), hMb x hx, hfr x hx hd]
    · have hA : accV (memStore32 Mb (D + BitVec.ofNat 32 (4 * i)) (bsubD (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)))
          (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))) b)) D (i + 1) = accV M D i +
          (bsubD (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))) b).toNat *
            2 ^ (32 * i) := by
        rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same]
        congr 1
        exact accV_congr i fun j hj => memLoad32_congr fun q hq =>
          hMb _ ((sFD.subR (c := 4 * j) (l := 4) (by omega)).subR (c := q) (l := 1) (by omega))
      rw [hA, accV_succ1, accV_succ1, pow32_succ, e2]
      exact sub_arith hv bv
  intro m
  induction m with
  | zero =>
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, _, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step 11 (by decide) s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    exact ⟨n1, M1, c1, u1, hc1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, enp, exp, ed, ec, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 hv1 sp1 enp exp ed ec rfl
    exact ⟨n', M', c1.trans c', u', hc', hf', hm', hv', sp', fun q q0 q1 q2 q3 q4 qr qnp qxp qd qc => by
      rw [fr' q q0 q1 q2 q3 q4 qr qnp qxp qd qc, fr q q0 q1 q2 q3 q4 qr qnp qxp qd qc]⟩

/-- One round of the copy, from 0xEA to the branch at 0xF6: copy the word at
`s3` to `s0`, and advance both and the count. -/
def bzCp : List BInstr :=
  [.lw a0 (19 : Fin 32) 0, .aluImm .add (19 : Fin 32) (19 : Fin 32) 4, .sw (8 : Fin 32) a0 0,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 4, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem bzCp_end : blockEnd bytes2scalar384Code 0xEA bzCp = some 0xF6 := by decide
end

set_option maxRecDepth 20000 in
/-- **The copy**, from round `i` to its end at 0xF8: the 12 words at `X` go
to the 12 at `Y`. -/
theorem bz_copy_loop {P X Y : Word} {M0 : Word → BitVec 8} (hX : X.toNat % 4 = 0) (hY : Y.toNat % 4 = 0)
    (sYX : Sep Y 48 X 48)
    (sYC : Sep Y 48 P bytes2scalar384Code.length) (hc : CodeIn M0 P bytes2scalar384Code) :
    ∀ m i, i + m + 1 = 12 → ∀ {n : Machine}, St (copyWords M0 Y X i) P n 0xEA (reg n) →
      reg n (19 : Fin 32) = X + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = Y + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = BitVec.ofNat 32 (12 - i) →
      ∃ n', Steps n n' ∧ St (copyWords M0 Y X 12) P n' 0xF8 (reg n') ∧
        ∀ q, q ≠ a0 → q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  have hcw : ∀ i, i ≤ 12 → CodeIn (copyWords M0 Y X i) P bytes2scalar384Code := fun i hi j hj => by
    have h := (sYC.subR (c := j) (l := 1) (by omega)).sub (c := 0) (l := 4 * i) (by omega)
    rw [add_ofNat_zero] at h
    rw [copyWords_outside i h]; exact hc j hj
  have step : ∀ i, i < 12 → ∀ {n : Machine}, St (copyWords M0 Y X i) P n 0xEA (reg n) →
      reg n (19 : Fin 32) = X + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = Y + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = BitVec.ofNat 32 (12 - i) →
      ∃ n', Steps n n' ∧ St (copyWords M0 Y X (i + 1)) P n' (if i + 1 < 12 then 0xEA else 0xF8) (reg n') ∧
        reg n' (19 : Fin 32) = X + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = Y + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
    intro i hi n s r19 r8 r9
    have hz := s.zero
    obtain ⟨n1, c1, u1⟩ := St.block bzCp s (hcw i (by omega)) bzCp_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, bzCp, upd, ↓reduceIte, and_true, true_and]
      rw [r19, r8, add_lit_zero, add_lit_zero]
      exact ⟨aligned_add hX (by omega), aligned_add hY (by omega), sYC.sub (c := 4 * i) (l := 4) (by omega)⟩)
    have sYi : Sep Y (4 * i) (X + BitVec.ofNat 32 (4 * i)) 4 := by
      have h := (sYX.subR (c := 4 * i) (l := 4) (by omega)).sub (c := 0) (l := 4 * i) (by omega)
      rwa [add_ofNat_zero] at h
    have e1 : (runBlock bzCp (copyWords M0 Y X i, reg n)).1 = copyWords M0 Y X (i + 1) := by
      simp +decide only [runBlock, BInstr.run, bzCp, upd, ↓reduceIte]
      rw [r19, r8, add_lit_zero, add_lit_zero, copyWords_load_sep sYi]; rfl
    have R : ∀ q, reg n1 q = (runBlock bzCp (copyWords M0 Y X i, reg n)).2 q := u1.regs
    have v19 : reg n1 (19 : Fin 32) = X + BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [R]; simp +decide only [runBlock, BInstr.run, bzCp, upd_app, ↓reduceIte]
      rw [r19, ev_add, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc, Nat.mul_succ]
    have v8 : reg n1 (8 : Fin 32) = Y + BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [R]; simp +decide only [runBlock, BInstr.run, bzCp, upd_app, ↓reduceIte]
      rw [r8, ev_add, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc, Nat.mul_succ]
    have v9 : reg n1 (9 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) := by
      rw [R]; simp +decide only [runBlock, BInstr.run, bzCp, upd_app, ↓reduceIte]
      rw [r9, ev_add, cnt12_dec i hi]
    have K : ∀ q, q ≠ a0 → q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n1 q = reg n q :=
      fun q h0 h19 h8 h9 => by
        rw [R]; refine runBlock_reg _ _ _ q hz ?_
        simp only [bzCp, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h19, h8, h9]
    have u1' : St (copyWords M0 Y X (i + 1)) P n1 0xF6 (reg n1) := ⟨u1.pc, by rw [u1.mem, e1], fun _ => rfl⟩
    have hb : branchTaken .bne (reg n1 (9 : Fin 32)) (reg n1 x0) = decide (i + 1 < 12) := by
      rw [v9, u1'.zero]; exact cnt12_ne i hi
    by_cases hl : i + 1 < 12
    · obtain ⟨n2, d2, u2⟩ := u1'.taken (hcw (i + 1) (by omega)) 0xEA bz_at_f6 (by decide)
        (by rw [hb]; exact decide_eq_true hl)
      exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, by rw [u2.regs, v19],
        by rw [u2.regs, v8], by rw [u2.regs, v9], fun q h0 h19 h8 h9 => by rw [u2.regs, K q h0 h19 h8 h9]⟩
    · obtain ⟨n2, d2, u2⟩ := u1'.notTaken (hcw (i + 1) (by omega)) 0xF8 bz_at_f6 (by decide)
        (by rw [hb]; exact decide_eq_false hl)
      exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, by rw [u2.regs, v19],
        by rw [u2.regs, v8], by rw [u2.regs, v9], fun q h0 h19 h8 h9 => by rw [u2.regs, K q h0 h19 h8 h9]⟩
  intro m
  induction m with
  | zero =>
    intro i hi n s r19 r8 r9
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, c1, u1, _, _, _, K⟩ := step 11 (by decide) s r19 r8 r9
    exact ⟨n1, c1, u1, K⟩
  | succ m ih =>
    intro i hi n s r19 r8 r9
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, c1, u1, v19, v8, v9, K⟩ := step i (by omega) s r19 r8 r9
    rw [ite_eq_left hl] at u1
    obtain ⟨n', c', u', K'⟩ := ih (i + 1) (sel_succ hi) u1 v19 v8 v9
    exact ⟨n', c1.trans c', u', fun q h0 h19 h8 h9 => by rw [K' q h0 h19 h8 h9, K q h0 h19 h8 h9]⟩

abbrev BZO : Word := BitVec.ofNat 32 b2sOrder384Address

/-- The code `bytes2scalar::<NistP384>` runs, its callees', the constants
`ConstMontyForm::new` reads, and the copy of the order that `bytes2scalar`
compares against, with that copy's value and leading zero bits. -/
structure BZEnv (M : Word → BitVec 8) : Prop where
  cod : CodeIn M BS bytes2scalar384Code
  lz : CodeIn M (BitVec.ofNat 32 leadingZerosAddress) leadingZerosCode
  pan : PanicCode M
  exu : CodeIn M (BitVec.ofNat 32 expectUsizeAddress) expectUsizeCode
  fb : FBEnv M
  bsb : CodeIn M (BitVec.ofNat 32 borrowingSubAddress) borrowingSubCode
  bb : CodeIn M (BitVec.ofNat 32 blackBoxU8Address) blackBoxU8Code
  cn : CodeIn M (BitVec.ofNat 32 choiceNotAddress) choiceNotCode
  sca : CodeIn M (BitVec.ofNat 32 sliceCtAssignAddress) sliceCtAssignCode
  nw : CodeIn M (BitVec.ofNat 32 p384ScalarNewAddress) p384ScalarNewCode
  mm : CodeIn M (BitVec.ofNat 32 mulMont12Address) mulMont12Code
  sel : CodeIn M (BitVec.ofNat 32 uintSelect12Address) uintSelect12Code
  nmod : CodeIn M n3M p384OrderData
  r2 : CodeIn M n3R2A p384ScalarR2Data
  ord : accV M BZO 12 = n384
  ordLz : lzLimbs M BZO 12 = 0

abbrev bzPs : List (Fin 32 × Word) :=
  [(ra, 0xBC), ((8 : Fin 32), 0xB8), ((9 : Fin 32), 0xB4), ((18 : Fin 32), 0xB0), ((19 : Fin 32), 0xAC),
   ((20 : Fin 32), 0xA8), ((21 : Fin 32), 0xA4), ((22 : Fin 32), 0xA0), ((23 : Fin 32), 0x9C)]

def bzA : List BInstr :=
  [.alu .add (20 : Fin 32) x0 a2, .alu .add (19 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0,
   .lui (22 : Fin 32) 0x3FCC5000, .aluImm .add (22 : Fin 32) (22 : Fin 32) 0xFFFFFDC4, .aluImm .add a1 x0 0xC,
   .alu .add a0 x0 (22 : Fin 32), .aluImm .add (23 : Fin 32) x0 0xC]
def bzB : List BInstr :=
  [.aluImm .add a1 x0 0x180, .alu .sub (21 : Fin 32) a1 a0, .aluImm .and a0 (21 : Fin 32) 0x7,
   .aluImm .srl a1 (21 : Fin 32) 0x3, .alu .sltu a0 x0 a0, .alu .add a0 a0 a1]
def bzC : List BInstr := [.sb sp x0 0x4, .sw sp a0 0x8, .aluImm .add a0 sp 0x4]
def bzD : List BInstr :=
  [.aluImm .add a0 sp 0x3C, .alu .add a1 x0 (19 : Fin 32), .alu .add a2 x0 (20 : Fin 32),
   .alu .add a3 x0 (21 : Fin 32), .aluImm .add (9 : Fin 32) sp 0x3C]
def bzE : List BInstr :=
  [.aluImm .add a0 sp 0xC, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0, .aluImm .add (8 : Fin 32) sp 0xC]
def bzF : List BInstr :=
  [.aluImm .add a0 sp 0x3C, .aluImm .add a1 x0 0xC, .aluImm .add a2 sp 0xC, .aluImm .add a3 x0 0xC,
   .aluImm .add (19 : Fin 32) sp 0x3C, .aluImm .add (9 : Fin 32) x0 0xC]
def bzG : List BInstr :=
  [.aluImm .add a0 sp 0x6C, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0, .aluImm .add (8 : Fin 32) sp 0x6C]
def bzH : List BInstr := [.aluImm .add a1 sp 0x6C, .alu .add a0 x0 (18 : Fin 32)]

section
set_option maxRecDepth 20000
theorem bzSave_end : blockEnd bytes2scalar384Code 2 (saveBlock bzPs) = some 0x14 := by decide
theorem bzA_end : blockEnd bytes2scalar384Code 0x14 bzA = some 0x28 := by decide
theorem bzB_end : blockEnd bytes2scalar384Code 0x30 bzB = some 0x46 := by decide
theorem bzC_end : blockEnd bytes2scalar384Code 0x46 bzC = some 0x4E := by decide
theorem bzD_end : blockEnd bytes2scalar384Code 0x5C bzD = some 0x66 := by decide
theorem bzE_end : blockEnd bytes2scalar384Code 0x6E bzE = some 0x78 := by decide
theorem bzF_end : blockEnd bytes2scalar384Code 0xC0 bzF = some 0xCE := by decide
theorem bzG_end : blockEnd bytes2scalar384Code 0xD6 bzG = some 0xE0 := by decide
theorem bzH_end : blockEnd bytes2scalar384Code 0xF8 bzH = some 0xFC := by decide
theorem bzRestore_end : blockEnd bytes2scalar384Code 0x104 (restoreBlock bzPs) = some 0x116 := by decide
end

theorem lz_congr {M M' : Word → BitVec 8} {p : Word} :
    ∀ k, (∀ i, i < k → memLoad32 M' (p + BitVec.ofNat 32 (4 * i)) = memLoad32 M (p + BitVec.ofNat 32 (4 * i))) →
      lzLimbs M' p k = lzLimbs M p k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [lzLimbs]; rw [h k (by omega), lz_congr k fun i hi => h i (by omega)]

theorem bz_srl31 {b : Word} (hb : b = 0 ∨ b = 0xFFFFFFFF) :
    aluEval .srl b 0x1F = BitVec.ofNat 32 (maskBit b) := by
  rcases hb with rfl | rfl <;> decide

/-- Bytes 4 to 7 of the `Result` slot: the tag byte 0 and the 48 that
`expect` returns. -/
theorem bz_res {M : Word → BitVec 8} {F : Word} :
    (memStore32 (memStore8 M (F + 0x4) 0) (F + 0x8) 0x30) (F + 0x4) = 0 ∧
      memLoad32 (memStore32 (memStore8 M (F + 0x4) 0) (F + 0x8) 0x30) (F + 0x4 + 4) = 0x30 := by
  have e : F + 0x4 + 4 = F + 0x8 := by rw [BitVec.add_assoc]; rfl
  refine ⟨?_, by rw [e, memLoad32_store32_same]⟩
  rw [memStore32_get_sep (by
    have := sep_offsets F (c := 8) (n := 4) (d := 4) (k := 1) (by omega) (by omega) (by omega)
    exact this), memStore8_same]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
set_option exponentiation.threshold 400 in
/-- **The compiled `bytes2scalar::<NistP384>`**: for the `n` bytes at `b`,
it returns at `out` the scalar whose limbs are `x · 2^384 mod n`, with `x`
the big-endian value of the first `min n 48` bytes, so the scalar is `x mod
n` in Montgomery form. It returns with `sp` and the callee-saved registers
restored and writes only `out` and the 0x1B0 bytes of stack below `sp`. -/
theorem bytes2scalar384_correct (m : Machine) {sp0 out b retAddr : Word} {n : Nat} (E : BZEnv m.mem)
    (hpc : m.pc = BS) (ha0 : reg m a0 = out) (ha1 : reg m a1 = b) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hsa : sp0.toNat % 16 = 0) (hsl : 0x3FC80000 + 0x200 ≤ sp0.toNat) (hsw : sp0.toNat ≤ dramEnd)
    (how : out.toNat + 48 ≤ dramEnd) (hoa : out.toNat % 4 = 0) (hbn : b.toNat + n < 2 ^ 32)
    (sBG : Sep b n (sp0 + 0xFFFFFE50) 0x1B0) (sOG : Sep out 48 (sp0 + 0xFFFFFE50) 0x1B0)
    (sGO : Sep (sp0 + 0xFFFFFE50) 0x1B0 BZO 48) (sGN : Sep (sp0 + 0xFFFFFE50) 0x1B0 n3M 48)
    (sGR : Sep (sp0 + 0xFFFFFE50) 0x1B0 n3R2A 48) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      accV m'.mem out 12 = beNat (memBytes m.mem b (min n 48)) * 2 ^ 384 % n384 ∧
      ∀ x, Sep (sp0 + 0xFFFFFE50) 0x1B0 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFE50 = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFF40 = F := ⟨_, rfl⟩
  rw [hG] at sBG sOG sGO sGN sGR ⊢
  have hGn : G.toNat = sp0.toNat - 0x1B0 := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFE50 : Word).toNat = 2 ^ 32 - 0x1B0 from rfl]; have := sp0.isLt; omega
  have hGF : G + BitVec.ofNat 32 0xF0 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGc : ∀ c, c ≤ 0x1B0 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold dramEnd at hsw; omega
  have hFn : F.toNat = G.toNat + 0xF0 := by rw [← hGF]; exact hGc _ (by decide)
  have hFa : F.toNat % 4 = 0 := by omega
  have hGw : ∀ c, c ≤ 0x1B0 → (G + BitVec.ofNat 32 c).toNat + 4 * 12 < 2 ^ 32 := fun c hc => by
    rw [hGc c hc]; unfold dramEnd at hsw; omega
  have hOw : out.toNat + 48 < 2 ^ 32 := by unfold dramEnd at how; omega
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0xF0 + k) := fun k => by
    rw [← hGF, add_ofNat_assoc]
  have eFS : F + 0xC0 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x1B0 → d + k ≤ 0x1B0 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have inG : ∀ {c l : Nat} {x : Word}, Sep G 0x1B0 x 1 → c + l ≤ 0x1B0 → Sep (G + BitVec.ofNat 32 c) l x 1 :=
    fun hx h => (hx.symm.subR h).symm
  have hiG : ∀ x : Word, dramEnd ≤ x.toNat → Sep G 0x1B0 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hiO : ∀ x : Word, dramEnd ≤ x.toNat → Sep out 48 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have sGcode : ∀ {a : Word} {len : Nat}, dramEnd ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 → Sep G 0xF0 a len :=
    fun h1 h2 => sep_of_le (by omega) h2
  have sOcode : ∀ {a : Word} {len : Nat}, dramEnd ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 → Sep out 48 a len :=
    fun h1 h2 => sep_of_le (by omega) h2
  have cd : ∀ {M' : Word → BitVec 8} {c : Word} {code : List Nat}, CodeIn m.mem c code → dramEnd ≤ c.toNat →
      c.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep G 0x1B0 x 1 → M' x = m.mem x) → CodeIn M' c code :=
    fun hc h1 h2 hM i hi' => by
      rw [hM _ (hiG _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]; exact hc i hi'
  have pcd : ∀ {M' : Word → BitVec 8}, (∀ x, Sep G 0x1B0 x 1 → M' x = m.mem x) → PanicCode M' :=
    fun hM p hp => by
      have hb := panicFns_hi p hp
      exact cd (E.pan p hp) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hb.1)
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) hM
  have hBSn : BS.toNat = (img% bytes2scalar384Address) := by decide
  have hc := E.cod
  have st0 : St m.mem BS m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hc bz_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF40) sp = F := by
    simp +decide only [upd, ↓reduceIte]; rw [hsp]; exact hF
  have slotO : ∀ o : Word, F + o = F + BitVec.ofNat 32 o.toNat := fun o => by rw [ofNat_toNat_self]
  have slotC : ∀ o : Word, o.toNat ≤ 0xBC → Sep (F + o) 4 BS bytes2scalar384Code.length := fun o ho =>
    sep_of_le (by rw [BitVec.toNat_add, hBSn]; have := Nat.mod_le (F.toNat + o.toNat) (2 ^ 32); unfold dramEnd at hsw
                  omega) (by rw [hBSn]; decide)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock bzPs) u1 hc bzSave_end (saveBlock_ok _ bzPs _ fun q hq => by
      rw [sp1]
      simp only [bzPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add hFa (by decide), slotC _ (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF40)) bzPs = Ms :=
    ⟨_, rfl⟩
  rw [hMs] at u2
  have IMs : ∀ x, Sep G 0x1B0 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside bzPs fun q hq => by
      simp only [bzPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (rw [slotO, eFk]; exact inG hx (by decide))
  have slots : ∀ r o, (r, o) ∈ bzPs → memLoad32 Ms (F + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [bzPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot bzPs _ hm (by
      simp only [bzPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide), upd_ne (by
        simp only [bzPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hr]
  have hc2 : CodeIn Ms BS bytes2scalar384Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IMs
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  obtain ⟨m3, c3, u3⟩ := St.block bzA u2.self hc2 bzA_end (by simp only [BlockOk, BInstr.ok, bzA, and_self])
  have R3 : ∀ q, reg m3 q = (runBlock bzA (Ms, reg m2)).2 q := u3.regs
  have u3' : St Ms BS m3 0x28 (reg m3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  have K3 : ∀ q, q.val ∉ [10, 11, 18, 19, 20, 22, 23] → reg m3 q = reg m2 q := fun q hq => by
    rw [R3]; refine runBlock_reg _ _ _ q u2.self.zero ?_
    simp only [bzA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have v3 : reg m3 (20 : Fin 32) = BitVec.ofNat 32 n ∧ reg m3 (19 : Fin 32) = b ∧ reg m3 (18 : Fin 32) = out ∧
      reg m3 (22 : Fin 32) = BZO ∧ reg m3 a1 = BitVec.ofNat 32 12 ∧ reg m3 a0 = BZO ∧
      reg m3 (23 : Fin 32) = BitVec.ofNat 32 12 := by
    simp +decide only [R3, runBlock, BInstr.run, bzA, upd_app, ↓reduceIte]
    rw [r2 a2 (by decide), r2 a1 (by decide), r2 a0 (by decide), ha0, ha1, ha2, u2.self.zero]
    exact ⟨zw _, zw _, zw _, trivial⟩
  obtain ⟨v320, v319, v318, v322, v3a1, v3a0, v323⟩ := v3
  have hLZn : (BitVec.ofNat 32 leadingZerosAddress : Word).toNat = leadingZerosAddress := by decide
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3'.callRa hc2 bz_at_28 bz_at_2c (cb := BitVec.ofNat 32 leadingZerosAddress)
    (by decide) (by decide)
  have r4 := PEnv.reg1 regs4 u3'.zero
  have eFm : F + 0xFFFFFFE0 = G + BitVec.ofNat 32 0xD0 := by rw [← hGF, BitVec.add_assoc]; rfl
  have sp3 : reg m3 sp = F := by rw [K3 sp (by decide), sp2]
  have sLZ : Sep (G + BitVec.ofNat 32 0xD0) 0x20 (BitVec.ofNat 32 leadingZerosAddress) leadingZerosCode.length :=
    sep_of_le (by rw [hGc _ (by decide), hLZn]; unfold dramEnd at hsw; unfold leadingZerosAddress; omega)
      (by rw [hLZn]; decide)
  obtain ⟨m5, c5, pc5, sp5, a05, K5, fr5⟩ := leadingZeros_correct m4 (P := BitVec.ofNat 32 leadingZerosAddress)
    (sp0 := F) (p := BZO) (n := 12) (retAddr := BS + BitVec.ofNat 32 (0x28 + 8))
    (by rw [mem4]; exact cd E.lz (by rw [hLZn]; decide) (by rw [hLZn]; decide) IMs) pc4
    (by rw [r4 sp (by decide), sp3]) (by rw [r4 a0 (by decide), v3a0]) (by rw [r4 a1 (by decide), v3a1]) (by decide)
    (by decide) (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at BS (by decide) _ (by decide))) hFa
    (by rw [eFm]; exact sLZ)
    (by rw [eFm]; exact (sGO.sub (c := 0xD0) (l := 0x20) (by decide)).symm)
  have IM5 : ∀ x, Sep G 0x1B0 x 1 → m5.mem x = m.mem x := fun x hx => by
    rw [fr5 x (by rw [eFm]; exact inG hx (by decide)), mem4, IMs x hx]
  have hz0 : lzLimbs m4.mem BZO 12 = 0 := by
    rw [mem4, lz_congr (M := m.mem) (M' := Ms) 12 fun i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact IMs _ (sGO.subR (c := 4 * i + j) (l := 1) (by omega))]
    exact E.ordLz
  rw [hz0] at a05
  have hc5 : CodeIn m5.mem BS bytes2scalar384Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IM5
  have u5 : St m5.mem BS m5 0x30 (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have K5' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m5 q = reg m3 q := fun q hq => by
    rw [K5 q (by revert hq; revert q; decide), r4 q (by revert hq; revert q; decide)]
  obtain ⟨m6, c6, u6⟩ := St.block bzB u5 hc5 bzB_end (by simp only [BlockOk, BInstr.ok, bzB, and_self])
  have R6 : ∀ q, reg m6 q = (runBlock bzB (m5.mem, reg m5)).2 q := u6.regs
  have u6' : St m5.mem BS m6 0x46 (reg m6) := ⟨u6.pc, by rw [u6.mem]; rfl, fun _ => rfl⟩
  have K6 : ∀ q, q.val ∉ [10, 11, 21] → reg m6 q = reg m5 q := fun q hq => by
    rw [R6]; refine runBlock_reg _ _ _ q u5.zero ?_
    simp only [bzB, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have v6 : reg m6 (21 : Fin 32) = 0x180 ∧ reg m6 a0 = 0x30 := by
    simp +decide only [R6, runBlock, BInstr.run, bzB, upd_app, ↓reduceIte]
    rw [a05, u5.zero]; decide
  obtain ⟨v621, v6a0⟩ := v6
  have sp6 : reg m6 sp = F := by rw [K6 sp (by decide), sp5]
  obtain ⟨m7, c7, u7⟩ := St.block bzC u6' hc5 bzC_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, bzC, and_true]
    rw [sp6]
    have h4 := (slotC 4 (by decide)).sub (c := 0) (l := 1) (by decide)
    rw [add_ofNat_zero] at h4
    exact ⟨h4, aligned_add hFa (by decide), slotC _ (by decide)⟩)
  obtain ⟨Mr, hMr⟩ : ∃ Mr, memStore32 (memStore8 m5.mem (F + 0x4) 0) (F + 0x8) 0x30 = Mr := ⟨_, rfl⟩
  have e7 : (runBlock bzC (m5.mem, reg m6)).1 = Mr := by
    simp +decide only [runBlock, BInstr.run, bzC]
    rw [sp6, v6a0, u6'.zero, ← hMr]; rfl
  have R7 : ∀ q, reg m7 q = (runBlock bzC (m5.mem, reg m6)).2 q := u7.regs
  have u7' : St Mr BS m7 0x4E (reg m7) := ⟨u7.pc, by rw [u7.mem, e7], fun _ => rfl⟩
  have K7 : ∀ q, q ≠ a0 → reg m7 q = reg m6 q := fun q h0 => by
    rw [R7]; refine runBlock_reg _ _ _ q u6.zero ?_
    simp only [bzC, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0]
  have v7 : reg m7 a0 = F + 0x4 := by
    simp +decide only [R7, runBlock, BInstr.run, bzC, upd_app, ↓reduceIte]; rw [sp6, ev_add]
  have IMr : ∀ x, Sep G 0x1B0 x 1 → Mr x = m.mem x := fun x hx => by
    have h8 : Sep (F + 0x8) 4 x 1 := by
      rw [show (0x8 : Word) = BitVec.ofNat 32 8 from rfl, eFk]; exact inG hx (by decide)
    have h4 : x ≠ F + 0x4 := fun e => by
      have h := inG (c := 0xF0 + 4) (l := 1) hx (by decide)
      rw [← eFk] at h
      exact h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e]; rfl)
    rw [← hMr, memStore32_get_sep h8, memStore8_ne h4, IM5 x hx]
  have hc7 : CodeIn Mr BS bytes2scalar384Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IMr
  have hEXn : (BitVec.ofNat 32 expectUsizeAddress : Word).toNat = expectUsizeAddress := by decide
  obtain ⟨m8, c8, pc8, mem8, regs8⟩ := u7'.callRa hc7 bz_at_4e bz_at_52 (cb := BitVec.ofNat 32 expectUsizeAddress)
    (by decide) (by decide)
  have r8 := PEnv.reg1 regs8 u7'.zero
  have sp7 : reg m7 sp = F := by rw [K7 sp (by decide), sp6]
  obtain ⟨m9, c9, pc9, a09, mem9, K9⟩ := (expectUsize_correct m8 (p := F + 0x4)
    (retAddr := BS + BitVec.ofNat 32 (0x4E + 8)) (by rw [mem8]; exact pcd IMr)
    (by rw [mem8]; exact cd E.exu (by rw [hEXn]; decide) (by rw [hEXn]; decide) IMr) pc8
    (by rw [r8 a0 (by decide), v7]) (aligned_add hFa (k := 4) (by decide))
    (by rw [regs8]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at BS (by decide) _ (by decide)))
    (by rw [r8 sp (by decide), sp7]; exact ⟨hFa, by omega, by omega⟩)).1 (by rw [mem8, ← hMr]; exact bz_res.1)
  rw [mem8] at a09 mem9
  have a09' : reg m9 a0 = 0x30 := by rw [a09, ← hMr]; exact bz_res.2
  have u9 : St Mr BS m9 0x56 (reg m9) := ⟨by rw [pc9], mem9, fun _ => rfl⟩
  have K9' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ ra → reg m9 q = reg m7 q := fun q h0 h1 hr => by
    rw [K9 q h0 h1, r8 q hr]
  have v920 : reg m9 (20 : Fin 32) = BitVec.ofNat 32 n := by
    rw [K9' _ (by decide) (by decide) (by decide), K7 _ (by decide), K6 _ (by decide),
      K5' _ (by decide), v320]
  have hn32 : n < 2 ^ 32 := by omega
  have pre10 : ∃ m10, Steps m9 m10 ∧ St Mr BS m10 0x5C (reg m10) ∧
      reg m10 (20 : Fin 32) = BitVec.ofNat 32 (min n 48) ∧ ∀ q, q ≠ (20 : Fin 32) → reg m10 q = reg m9 q := by
    by_cases hb : n < 48
    · obtain ⟨m10, d10, u10⟩ := u9.taken hc7 0x5C bz_at_56 (by decide) (by
        simp only [branchTaken]; rw [v920, a09']
        simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq, Nat.mod_eq_of_lt hn32]
        exact hb)
      exact ⟨m10, .single d10, u10.self, by rw [u10.regs, v920, Nat.min_eq_left (by omega)],
        fun q _ => by rw [u10.regs]⟩
    · obtain ⟨m10, d10, u10⟩ := u9.notTaken hc7 0x5A bz_at_56 (by decide) (by
        simp only [branchTaken]; rw [v920, a09']
        simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.mod_eq_of_lt hn32]
        exact hb)
      obtain ⟨m11, d11, u11⟩ := u10.alu hc7 bz_at_5a (off' := 0x5C) (by decide)
      refine ⟨m11, .cons d10 (.single d11), u11.self, ?_, fun q hq => ?_⟩
      · rw [u11.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u9.zero, a09', Nat.min_eq_right (by omega)]
        rfl
      · rw [u11.regs, updz u10.zero hq]
  obtain ⟨m10, c10, u10, v1020, K10⟩ := pre10
  obtain ⟨X, hX⟩ : ∃ X, G + BitVec.ofNat 32 0x12C = X := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, G + BitVec.ofNat 32 0xFC = D := ⟨_, rfl⟩
  have eFX : F + 0x3C = X := by rw [← hX, show (0x3C : Word) = BitVec.ofNat 32 0x3C from rfl, eFk]
  have eFD : F + 0xC = D := by rw [← hD, show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, eFk]
  have hXn : X.toNat = G.toNat + 0x12C := by rw [← hX]; exact hGc _ (by decide)
  have hDn : D.toNat = G.toNat + 0xFC := by rw [← hD]; exact hGc _ (by decide)
  obtain ⟨m11, c11, u11⟩ := St.block bzD u10 hc7 bzD_end (by simp only [BlockOk, BInstr.ok, bzD, and_self])
  have R11 : ∀ q, reg m11 q = (runBlock bzD (Mr, reg m10)).2 q := u11.regs
  have u11' : St Mr BS m11 0x66 (reg m11) := ⟨u11.pc, by rw [u11.mem]; rfl, fun _ => rfl⟩
  have K11 : ∀ q, q.val ∉ [9, 10, 11, 12, 13] → reg m11 q = reg m10 q := fun q hq => by
    rw [R11]; refine runBlock_reg _ _ _ q u10.zero ?_
    simp only [bzD, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  -- registers from `m3` that the calls so far keep
  have K10' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ (20 : Fin 32) →
      q ≠ (21 : Fin 32) → reg m10 q = reg m3 q := fun q hq h20 h21 => by
    rw [K10 q h20, K9' q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), K7 q (by revert hq; revert q; decide),
      K6 q (by intro h; revert h; revert hq h20 h21; revert q; decide), K5' q hq]
  have sp10 : reg m10 sp = F := by
    rw [K10 sp (by decide), K9' sp (by decide) (by decide) (by decide), sp7]
  have v11 : reg m11 a0 = X ∧ reg m11 a1 = b ∧ reg m11 a2 = BitVec.ofNat 32 (min n 48) ∧
      reg m11 a3 = BitVec.ofNat 32 384 ∧ reg m11 (9 : Fin 32) = X := by
    simp +decide only [R11, runBlock, BInstr.run, bzD, upd_app, ↓reduceIte]
    rw [sp10, v1020, K10' 19 (by decide) (by decide) (by decide), v319,
      K10 21 (by decide), K9' 21 (by decide) (by decide) (by decide), K7 21 (by decide), v621]
    simp only [ev_add, eFX, zw, true_and, and_true]
    rfl
  obtain ⟨v11a0, v11a1, v11a2, v11a3, v119⟩ := v11
  obtain ⟨m12, c12, pc12, mem12, regs12⟩ := u11'.callRa hc7 bz_at_66 bz_at_6a (cb := FB) (by decide) (by decide)
  have r12 := PEnv.reg1 regs12 u11'.zero
  have hFBn : FB.toNat = fromBeSliceTrunc12Address := by decide
  have eF70 : F + 0xFFFFFF90 = G + BitVec.ofNat 32 0x80 := by rw [← hGF, BitVec.add_assoc]; rfl
  have hn48 : min n 48 ≤ n := Nat.min_le_left _ _
  have EF : FBEnv m12.mem := by
    rw [mem12]
    exact ⟨cd E.fb.cod (by rw [hFBn]; decide) (by rw [hFBn]; decide) IMr,
      cd E.fb.ms (by decide) (by decide) IMr, cd E.fb.fl (by decide) (by decide) IMr,
      cd E.fb.cs (by decide) (by decide) IMr, cd E.fb.cb (by decide) (by decide) IMr⟩
  have sBF : Sep b (min n 48) (F + 0xFFFFFF90) 0x70 := by
    rw [eF70]; have h := (sBG.subR (c := 0x80) (l := 0x70) (by decide)).sub (c := 0) (l := min n 48) (by omega)
    rwa [add_ofNat_zero] at h
  have sXF : Sep X 48 (F + 0xFFFFFF90) 0x70 := by
    rw [eF70, ← hX]; exact offs (by omega) (by omega) (by omega)
  have sp11 : reg m11 sp = F := by rw [K11 sp (by decide), sp10]
  obtain ⟨m13, c13, pc13, sp13, K13, val13, fr13⟩ := fromBeSliceTrunc12_correct m12 (sp0 := F) (out := X) (b := b)
    (n := min n 48) (bits := 384) (retAddr := BS + BitVec.ofNat 32 (0x66 + 8)) EF pc12
    (by rw [r12 a0 (by decide), v11a0]) (by rw [r12 a1 (by decide), v11a1]) (by rw [r12 a2 (by decide), v11a2])
    (by rw [r12 a3 (by decide), v11a3]) (by rw [regs12]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at BS (by decide) _ (by decide))) (by rw [r12 sp (by decide), sp11]) (by decide)
    (Nat.le_refl _) (by omega) hFa (by omega) (by unfold dramEnd at hsw; omega) (by unfold dramEnd at hsw; omega)
    (by omega) sBF sXF
  rw [show (384 : Nat) / 8 = 48 from rfl, Nat.min_eq_left (Nat.min_le_right n 48), BitVec.add_sub_cancel, mem12]
    at val13
  have xval : accV m13.mem X 12 = beNat (memBytes m.mem b (min n 48)) := by
    rw [val13]
    exact congrArg beNat (memBytes_congr fun i hi =>
      IMr _ (by have h := (sBG.sub (c := i) (l := 1) (by omega)).symm; exact h))
  have IM13 : ∀ x, Sep G 0x1B0 x 1 → m13.mem x = m.mem x := fun x hx => by
    rw [fr13 x (by rw [eF70]; exact inG hx (by decide)) (by rw [← hX]; exact inG hx (by decide)), mem12, IMr x hx]
  have hc13 : CodeIn m13.mem BS bytes2scalar384Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IM13
  have u13 : St m13.mem BS m13 0x6E (reg m13) := ⟨by rw [pc13], rfl, fun _ => rfl⟩
  have K13' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m13 q = reg m11 q :=
    fun q hq => by rw [K13 q (by revert hq; revert q; decide), r12 q (by revert hq; revert q; decide)]
  obtain ⟨m14, c14, u14⟩ := St.block bzE u13 hc13 bzE_end (by simp only [BlockOk, BInstr.ok, bzE, and_self])
  have R14 : ∀ q, reg m14 q = (runBlock bzE (m13.mem, reg m13)).2 q := u14.regs
  have u14' : St m13.mem BS m14 0x78 (reg m14) := ⟨u14.pc, by rw [u14.mem]; rfl, fun _ => rfl⟩
  have K14 : ∀ q, q.val ∉ [8, 10, 11, 12] → reg m14 q = reg m13 q := fun q hq => by
    rw [R14]; refine runBlock_reg _ _ _ q u13.zero ?_
    simp only [bzE, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have v14 : reg m14 a0 = D ∧ reg m14 a2 = BitVec.ofNat 32 (4 * 12) ∧ reg m14 a1 = 0 ∧ reg m14 (8 : Fin 32) = D := by
    simp +decide only [R14, runBlock, BInstr.run, bzE, upd_app, ↓reduceIte]
    rw [sp13]; simp only [ev_add, eFD, and_true]
  obtain ⟨v14a0, v14a2, v14a1, v148⟩ := v14
  have hMSn : (BitVec.ofNat 32 memsetAddress : Word).toNat = memsetAddress := by decide
  obtain ⟨m15, c15, u15, _, k15⟩ := u14'.memsetW (B := BitVec.ofNat 32 memsetAddress) (w := 12) (dst := D)
    (by decide) hc13 (cd E.fb.ms (by rw [hMSn]; decide) (by rw [hMSn]; decide) IM13) bz_at_78 bz_at_7c (by decide)
    (by decide) (by decide) (by omega) (by decide) (by omega)
    (sep_of_le (by rw [hMSn]; unfold dramEnd at hsw; unfold memsetAddress; omega) (by decide)) v14a0 v14a1 v14a2
  obtain ⟨Mz, hMz⟩ : ∃ Mz, fillWords m13.mem D 0 12 = Mz := ⟨_, rfl⟩
  rw [hMz] at u15
  have IMz : ∀ x, Sep G 0x1B0 x 1 → Mz x = m.mem x := fun x hx => by
    rw [← hMz, fillWords_outside 12 (by rw [← hD]; exact inG hx (by decide)), IM13 x hx]
  have hcz : CodeIn Mz BS bytes2scalar384Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IMz
  obtain ⟨m16, d16, u16⟩ := u15.aluImm hcz bz_at_80 (off' := 0x82) (by decide)
  -- registers kept from `m11` through `memset`
  have K15 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m15 q = reg m11 q := fun q hq => by
    rw [k15 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      K14 q (by intro h; revert h; revert hq; revert q; decide), K13' q (by revert hq; revert q; decide)]
  have v1523 : reg m15 (23 : Fin 32) = BitVec.ofNat 32 12 := by
    rw [K15 _ (by decide), K11 _ (by decide), K10' _ (by decide) (by decide) (by decide), v323]
  have v1522 : reg m15 (22 : Fin 32) = BZO := by
    rw [K15 _ (by decide), K11 _ (by decide), K10' _ (by decide) (by decide) (by decide), v322]
  have v159 : reg m15 (9 : Fin 32) = X := by rw [K15 _ (by decide), v119]
  have v158 : reg m15 (8 : Fin 32) = D := by
    rw [k15 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v148]
  have sp15 : reg m15 sp = F := by
    rw [k15 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), K14 sp (by decide), sp13]
  have K16 : ∀ q, q ≠ a2 → reg m16 q = reg m15 q := fun q h => by rw [u16.regs, updz u15.zero h]
  obtain ⟨m17, d17, u17⟩ := u16.self.notTaken hcz 0x86 bz_at_82 (by decide) (by
    simp only [branchTaken]; rw [K16 _ (by decide), v1523, u16.self.zero]; decide)
  have hBBn : bzBsub BS = BitVec.ofNat 32 borrowingSubAddress := by decide
  have eFm4 : F + 0xFFFFFFFC = G + BitVec.ofNat 32 0xEC := by rw [← hGF, BitVec.add_assoc]; rfl
  have hBSb : (BitVec.ofNat 32 borrowingSubAddress : Word).toNat = borrowingSubAddress := by decide
  have hiC : ∀ {c l : Nat} {a : Word} {len : Nat}, c + l ≤ 0x1B0 → dramEnd ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 →
      Sep (G + BitVec.ofNat 32 c) l a len := fun h h1 h2 => sep_of_le (by rw [hGc _ (by omega)]; omega) h2
  obtain ⟨n18, M18, c18, u18, hc18, fr18, hm18, hv18, sp18, K18⟩ := bz_sub_loop (P := BS) (F := F) (np := X)
    (xp := BZO) (D := D) (M0 := Mz) (by decide) hFa (by omega) (by decide) (by omega) (by omega)
    (by rw [eFm4, ← hX]; exact offs (by omega) (by omega) (by omega))
    (by rw [eFm4]; exact sGO.sub (by decide))
    (by rw [eFm4, ← hD]; exact offs (by omega) (by omega) (by omega))
    (by rw [← hD, ← hX]; exact offs (by omega) (by omega) (by omega))
    (by rw [← hD]; exact sGO.sub (by decide))
    (by rw [eFm4, hBBn]; exact hiC (by decide) (by rw [hBSb]; decide) (by rw [hBSb]; decide))
    (by rw [eFm4]; exact hiC (by decide) (by rw [hBSn]; decide) (by rw [hBSn]; decide))
    (by rw [← hD, hBBn]; exact hiC (by decide) (by rw [hBSb]; decide) (by rw [hBSb]; decide))
    (by rw [← hD]; exact hiC (by decide) (by rw [hBSn]; decide) (by rw [hBSn]; decide))
    11 0 rfl u17.self hcz (by rw [hBBn]; exact cd E.bsb (by rw [hBSb]; decide) (by rw [hBSb]; decide) IMz)
    (fun _ _ _ => rfl) (.inl rfl) rfl
    (by rw [u17.regs, K16 _ (by decide), sp15]) (by rw [u17.regs, K16 _ (by decide), v159, add_ofNat_zero])
    (by rw [u17.regs, K16 _ (by decide), v1522, add_ofNat_zero]) (by rw [u17.regs, K16 _ (by decide), v158, add_ofNat_zero])
    (by rw [u17.regs, K16 _ (by decide), v1523]) (by rw [u17.regs, u16.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u15.zero]; rfl)
  have IM18 : ∀ x, Sep G 0x1B0 x 1 → M18 x = m.mem x := fun x hx => by
    rw [fr18 x (by rw [eFm4]; exact inG hx (by decide)) (by rw [← hD]; exact inG hx (by decide)), IMz x hx]
  have hc18' : CodeIn M18 BS bytes2scalar384Code := hc18
  -- the borrow as 0 or 1
  obtain ⟨mb, hmb⟩ : ∃ mb, maskBit (reg n18 a2) = mb := ⟨_, rfl⟩
  have hmb01 : mb = 0 ∨ mb = 1 := by
    rw [← hmb]; unfold maskBit; by_cases h : reg n18 a2 = 0
    · rw [ite_eq_left h]; exact .inl rfl
    · rw [ite_eq_right h]; exact .inr rfl
  have hmbW : BitVec.ofNat 32 mb = 0 ∨ BitVec.ofNat 32 mb = 1 := by rcases hmb01 with rfl | rfl <;> decide
  obtain ⟨m19, d19, u19⟩ := u18.aluImm hc18' bz_at_a4 (off' := 0xA8) (by decide)
  have v19 : reg m19 a0 = BitVec.ofNat 32 mb := by
    rw [u19.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [bz_srl31 hm18, hmb]
  have K19 : ∀ q, q ≠ a0 → reg m19 q = reg n18 q := fun q h => by rw [u19.regs, updz u18.zero h]
  have hBBa : (BitVec.ofNat 32 blackBoxU8Address : Word).toNat = blackBoxU8Address := by decide
  obtain ⟨m20, c20, pc20, mem20, regs20⟩ := u19.self.callRa hc18' bz_at_a8 bz_at_ac
    (cb := BitVec.ofNat 32 blackBoxU8Address) (by decide) (by decide)
  have r20 := PEnv.reg1 regs20 u19.self.zero
  have sp20 : reg m20 sp = F := by rw [r20 sp (by decide), K19 sp (by decide), sp18]
  have eFm1 : F + 0xFFFFFFFF = G + BitVec.ofNat 32 0xEF := by rw [← hGF, BitVec.add_assoc]; rfl
  obtain ⟨m21, c21, pc21, a021, K21, fr21⟩ := blackBoxU8_correct m20 (base := BitVec.ofNat 32 blackBoxU8Address)
    (retAddr := BS + BitVec.ofNat 32 (0xA8 + 8))
    (by rw [mem20]; exact cd E.bb (by rw [hBBa]; decide) (by rw [hBBa]; decide) IM18) pc20
    (by rw [regs20]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at BS (by decide) _ (by decide)))
    (by rw [sp20, eFm1]; exact hiC (by decide) (by rw [hBBa]; decide) (by rw [hBBa]; decide))
  rw [r20 a0 (by decide), v19, frp_c8 hmbW] at a021
  rw [sp20, eFm1, mem20] at fr21
  have IM21 : ∀ x, Sep G 0x1B0 x 1 → m21.mem x = m.mem x := fun x hx => by
    rw [fr21 x (inG hx (by decide)), IM18 x hx]
  have hc21 : CodeIn m21.mem BS bytes2scalar384Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IM21
  have u21 : St m21.mem BS m21 0xB0 (reg m21) := ⟨by rw [pc21], rfl, fun _ => rfl⟩
  obtain ⟨m22, d22, u22⟩ := u21.aluImm hc21 bz_at_b0 (off' := 0xB4) (by decide)
  have v22 : reg m22 a0 = BitVec.ofNat 32 mb := by
    rw [u22.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [a021]; rcases hmbW with h | h <;> rw [h] <;> decide
  have K22 : ∀ q, q ≠ a0 → reg m22 q = reg m21 q := fun q h => by rw [u22.regs, updz u21.zero h]
  have hCNa : (BitVec.ofNat 32 choiceNotAddress : Word).toNat = choiceNotAddress := by decide
  obtain ⟨m23, c23, pc23, mem23, regs23⟩ := u22.self.callRa hc21 bz_at_b4 bz_at_b8
    (cb := BitVec.ofNat 32 choiceNotAddress) (by decide) (by decide)
  have r23 := PEnv.reg1 regs23 u22.self.zero
  have sp22 : reg m22 sp = F := by
    rw [K22 sp (by decide), K21 sp (by decide), r20 sp (by decide), K19 sp (by decide), sp18]
  have hmbv : (BitVec.ofNat 32 mb).toNat ≤ 1 := by rcases hmb01 with rfl | rfl <;> decide
  obtain ⟨m24, c24, pc24, a024, K24, fr24⟩ := choiceNot_correct m23 (P := BitVec.ofNat 32 choiceNotAddress)
    (retAddr := BS + BitVec.ofNat 32 (0xB4 + 8)) (c := BitVec.ofNat 32 mb) (by decide)
    (by rw [mem23]; exact cd E.cn (by rw [hCNa]; decide) (by rw [hCNa]; decide) IM21)
    (by rw [mem23, show BitVec.ofNat 32 choiceNotAddress + 0xFFFFBDEE = BitVec.ofNat 32 blackBoxU8Address by decide]
        exact cd E.bb (by rw [hBBa]; decide) (by rw [hBBa]; decide) IM21) pc23
    (by rw [r23 a0 (by decide), v22]) hmbv (by rw [regs23]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at BS (by decide) _ (by decide)))
    (by rw [r23 sp (by decide), sp22, eFm1,
          show BitVec.ofNat 32 choiceNotAddress + 0xFFFFBDEE = BitVec.ofNat 32 blackBoxU8Address by decide]
        exact hiC (by decide) (by rw [hBBa]; decide) (by rw [hBBa]; decide))
  rw [r23 sp (by decide), sp22, eFm1, mem23] at fr24
  have IM24 : ∀ x, Sep G 0x1B0 x 1 → m24.mem x = m.mem x := fun x hx => by
    rw [fr24 x (inG hx (by decide)), IM21 x hx]
  have hc24 : CodeIn m24.mem BS bytes2scalar384Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IM24
  have u24 : St m24.mem BS m24 0xBC (reg m24) := ⟨by rw [pc24], rfl, fun _ => rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc : Word, BitVec.ofNat 32 (1 - (BitVec.ofNat 32 mb).toNat) = cc := ⟨_, rfl⟩
  have hcc01 : cc = 0 ∨ cc = 1 := by rw [← hcc]; rcases hmb01 with rfl | rfl <;> decide
  have hccmb : cc = 1 ↔ mb = 0 := by rw [← hcc]; rcases hmb01 with rfl | rfl <;> decide
  rw [hcc] at a024
  obtain ⟨m25, d25, u25⟩ := u24.aluImm hc24 bz_at_bc (off' := 0xC0) (by decide)
  have v25 : reg m25 a4 = cc := by
    rw [u25.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [a024]; rcases hcc01 with h | h <;> rw [h] <;> decide
  have K25 : ∀ q, q ≠ a4 → reg m25 q = reg m24 q := fun q h => by rw [u25.regs, updz u24.zero h]
  -- registers from `n18` that `black_box` and `Choice::not` keep
  have K25' : ∀ q, q ≠ a0 → q ≠ a4 → q ≠ t1 → q ≠ ra → reg m25 q = reg n18 q := fun q h0 h4 ht hr => by
    rw [K25 q h4, K24 q h0 ht, r23 q hr, K22 q h0, K21 q h0, r20 q hr, K19 q h0]
  have sp25 : reg m25 sp = F := by
    rw [K25' sp (by decide) (by decide) (by decide) (by decide), sp18]
  obtain ⟨m26, c26, u26⟩ := St.block bzF u25.self hc24 bzF_end (by simp only [BlockOk, BInstr.ok, bzF, and_self])
  have R26 : ∀ q, reg m26 q = (runBlock bzF (m24.mem, reg m25)).2 q := u26.regs
  have u26' : St m24.mem BS m26 0xCE (reg m26) := ⟨u26.pc, by rw [u26.mem]; rfl, fun _ => rfl⟩
  have K26 : ∀ q, q.val ∉ [9, 10, 11, 12, 13, 19] → reg m26 q = reg m25 q := fun q hq => by
    rw [R26]; refine runBlock_reg _ _ _ q u25.zero ?_
    simp only [bzF, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have v26 : reg m26 a0 = X ∧ reg m26 a1 = BitVec.ofNat 32 12 ∧ reg m26 a2 = D ∧ reg m26 a3 = BitVec.ofNat 32 12 ∧
      reg m26 (19 : Fin 32) = X ∧ reg m26 (9 : Fin 32) = BitVec.ofNat 32 12 := by
    simp +decide only [R26, runBlock, BInstr.run, bzF, upd_app, ↓reduceIte]
    rw [sp25]; simp only [ev_add, eFX, eFD, and_true]
  obtain ⟨v26a0, v26a1, v26a2, v26a3, v2619, v269⟩ := v26
  have hSCa : (BitVec.ofNat 32 sliceCtAssignAddress : Word).toNat = sliceCtAssignAddress := by decide
  obtain ⟨m27, c27, pc27, mem27, regs27⟩ := u26'.callRa hc24 bz_at_ce bz_at_d2
    (cb := BitVec.ofNat 32 sliceCtAssignAddress) (by decide) (by decide)
  have r27 := PEnv.reg1 regs27 u26'.zero
  have sp26 : reg m26 sp = F := by rw [K26 sp (by decide), sp25]
  obtain ⟨m28, c28, pc28, sp28, lim28, fr28, K28⟩ := sliceCtAssign_correct m27
    (B := BitVec.ofNat 32 sliceCtAssignAddress) (sp0 := F) (dst := X) (src := D) (c := cc) (n := 12)
    (retAddr := BS + BitVec.ofNat 32 (0xCE + 8))
    (by rw [mem27]; exact cd E.sca (by rw [hSCa]; decide) (by rw [hSCa]; decide) IM24) pc27
    (by rw [r27 sp (by decide), sp26]) hFa (by omega) (by rw [r27 a0 (by decide), v26a0])
    (by rw [r27 a1 (by decide), v26a1]) (by rw [r27 a2 (by decide), v26a2]) (by rw [r27 a3 (by decide), v26a3])
    (by rw [r27 a4 (by decide), K26 a4 (by decide), v25]) hcc01
    (by rw [regs27]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at BS (by decide) _ (by decide)))
    (by omega) (by omega) (by rw [← hX]; exact Nat.le_of_lt (hGw _ (by decide)))
    (by rw [eFm]; exact hiC (by decide) (by rw [hSCa]; decide) (by rw [hSCa]; decide))
    (by rw [← hX]; exact hiC (by decide) (by rw [hSCa]; decide) (by rw [hSCa]; decide))
    (by rw [eFm, ← hX]; exact offs (by omega) (by omega) (by omega))
    (by rw [eFm, ← hD]; exact offs (by omega) (by omega) (by omega))
    (by rw [← hX, ← hD]; exact offs (by omega) (by omega) (by omega))
  rw [mem27, eFm] at fr28
  rw [mem27] at lim28
  -- the values
  have P24X : ∀ j, j < 48 → m24.mem (X + BitVec.ofNat 32 j) = m13.mem (X + BitVec.ofNat 32 j) := fun j hj => by
    rw [← hX, add_ofNat_assoc]
    have h1 : Sep (G + BitVec.ofNat 32 0xEF) 1 (G + BitVec.ofNat 32 (0x12C + j)) 1 := offs (by omega) (by omega) (by omega)
    rw [fr24 _ h1, fr21 _ h1, fr18 _ (by rw [eFm4]; exact offs (by omega) (by omega) (by omega))
      (by rw [← hD]; exact offs (by omega) (by omega) (by omega)), ← hMz,
      fillWords_outside 12 (by rw [← hD]; exact offs (by omega) (by omega) (by omega))]
  have P24D : ∀ j, j < 48 → m24.mem (D + BitVec.ofNat 32 j) = M18 (D + BitVec.ofNat 32 j) := fun j hj => by
    rw [← hD, add_ofNat_assoc]
    have h1 : Sep (G + BitVec.ofNat 32 0xEF) 1 (G + BitVec.ofNat 32 (0xFC + j)) 1 := offs (by omega) (by omega) (by omega)
    rw [fr24 _ h1, fr21 _ h1]
  have PzX : ∀ j, j < 48 → Mz (X + BitVec.ofNat 32 j) = m13.mem (X + BitVec.ofNat 32 j) := fun j hj => by
    rw [← hX, add_ofNat_assoc, ← hMz, fillWords_outside 12 (by rw [← hD]; exact offs (by omega) (by omega) (by omega))]
  have accEq : ∀ {M M' : Word → BitVec 8} {p : Word}, (∀ j, j < 48 → M' (p + BitVec.ofNat 32 j) = M (p + BitVec.ofNat 32 j)) →
      accV M' p 12 = accV M p 12 := fun h =>
    accV_congr 12 fun i hi => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega)
  have xz : accV Mz X 12 = beNat (memBytes m.mem b (min n 48)) := by rw [accEq PzX, xval]
  have nz : accV Mz BZO 12 = n384 := by
    rw [accEq (M := m.mem) fun j hj => IMz _ (sGO.subR (c := j) (l := 1) (by omega)), E.ord]
  rw [xz, nz, hmb] at hv18
  have dz : accV m24.mem D 12 = accV M18 D 12 := accEq P24D
  have x28 : accV m28.mem X 12 = if cc = 1 then accV M18 D 12 else beNat (memBytes m.mem b (min n 48)) := by
    by_cases h1 : cc = 1
    · rw [ite_eq_left h1, ← dz]
      exact accV_congr2 12 fun i hi => by rw [lim28 i hi, ite_eq_left h1]
    · rw [ite_eq_right h1, ← xval, ← accEq P24X]
      exact accV_congr 12 fun i hi => by rw [lim28 i hi, ite_eq_right h1]
  have xmod : (if cc = 1 then accV M18 D 12 else beNat (memBytes m.mem b (min n 48))) * 2 ^ 384 % n384 =
      beNat (memBytes m.mem b (min n 48)) * 2 ^ 384 % n384 := by
    by_cases h1 : cc = 1
    · rw [ite_eq_left h1]
      have h0 := hccmb.mp h1
      rw [h0, Nat.mul_zero, Nat.add_zero] at hv18
      rw [hv18, Nat.add_mul, Nat.add_comm (n384 * _), Nat.add_mul_mod_self_left]
    · rw [ite_eq_right h1]
  rw [← x28] at xmod
  -- zero `Y` and copy the limbs there
  have IM28 : ∀ x, Sep G 0x1B0 x 1 → m28.mem x = m.mem x := fun x hx => by
    rw [fr28 x (inG hx (by decide)) (by rw [← hX]; exact inG hx (by decide)), IM24 x hx]
  have hc28 : CodeIn m28.mem BS bytes2scalar384Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IM28
  have u28 : St m28.mem BS m28 0xD6 (reg m28) := ⟨by rw [pc28], rfl, fun _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, G + BitVec.ofNat 32 0x15C = Y := ⟨_, rfl⟩
  have eFY : F + 0x6C = Y := by rw [← hY, show (0x6C : Word) = BitVec.ofNat 32 0x6C from rfl, eFk]
  have hYn : Y.toNat = G.toNat + 0x15C := by rw [← hY]; exact hGc _ (by decide)
  obtain ⟨m29, c29, u29⟩ := St.block bzG u28 hc28 bzG_end (by simp only [BlockOk, BInstr.ok, bzG, and_self])
  have R29 : ∀ q, reg m29 q = (runBlock bzG (m28.mem, reg m28)).2 q := u29.regs
  have u29' : St m28.mem BS m29 0xE0 (reg m29) := ⟨u29.pc, by rw [u29.mem]; rfl, fun _ => rfl⟩
  have K29 : ∀ q, q.val ∉ [8, 10, 11, 12] → reg m29 q = reg m28 q := fun q hq => by
    rw [R29]; refine runBlock_reg _ _ _ q u28.zero ?_
    simp only [bzG, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have v29 : reg m29 a0 = Y ∧ reg m29 a2 = BitVec.ofNat 32 (4 * 12) ∧ reg m29 a1 = 0 ∧ reg m29 (8 : Fin 32) = Y := by
    simp +decide only [R29, runBlock, BInstr.run, bzG, upd_app, ↓reduceIte]
    rw [sp28]; simp only [ev_add, eFY, and_true]
  obtain ⟨v29a0, v29a2, v29a1, v298⟩ := v29
  obtain ⟨m30, c30, u30, _, k30⟩ := u29'.memsetW (B := BitVec.ofNat 32 memsetAddress) (w := 12) (dst := Y)
    (by decide) hc28 (cd E.fb.ms (by rw [hMSn]; decide) (by rw [hMSn]; decide) IM28) bz_at_e0 bz_at_e4 (by decide)
    (by decide) (by decide) (by rw [← hY]; exact hGw _ (by decide)) (by decide) (by omega)
    (by rw [← hY]; exact hiC (by decide) (by rw [hMSn]; decide) (by rw [hMSn]; decide)) v29a0 v29a1 v29a2
  obtain ⟨My, hMy⟩ : ∃ My, fillWords m28.mem Y 0 12 = My := ⟨_, rfl⟩
  rw [hMy] at u30
  have IMy : ∀ x, Sep G 0x1B0 x 1 → My x = m.mem x := fun x hx => by
    rw [← hMy, fillWords_outside 12 (by rw [← hY]; exact inG hx (by decide)), IM28 x hx]
  have hcy : CodeIn My BS bytes2scalar384Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IMy
  have K30 : ∀ q, q.val ∉ [1, 8, 10, 11, 12, 13, 14, 15, 16] → reg m30 q = reg m28 q := fun q hq => by
    rw [k30 q (by intro h; apply hq; rw [h]; decide) (by intro h; apply hq; rw [h]; decide)
      (by intro h; apply hq; rw [h]; decide) (by intro h; apply hq; rw [h]; decide)
      (by intro h; apply hq; rw [h]; decide) (by intro h; apply hq; rw [h]; decide),
      K29 q (by intro h; apply hq; revert h; revert q; decide)]
  have K28' : ∀ q, q.val ∉ [1, 10, 11, 12, 13, 14, 15, 16] → reg m28 q = reg m26 q := fun q hq => by
    rw [K28 q (by intro h; apply hq; revert h; revert q; decide), r27 q (by intro h; apply hq; rw [h]; decide)]
  have v309 : reg m30 (9 : Fin 32) = BitVec.ofNat 32 12 := by rw [K30 _ (by decide), K28' _ (by decide), v269]
  have v3019 : reg m30 (19 : Fin 32) = X := by rw [K30 _ (by decide), K28' _ (by decide), v2619]
  have v308 : reg m30 (8 : Fin 32) = Y := by
    rw [k30 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v298]
  obtain ⟨m31, d31, u31⟩ := u30.notTaken hcy 0xEA bz_at_e8 (by decide) (by
    simp only [branchTaken]; rw [v309, u30.zero]; decide)
  have sYX : Sep Y 48 X 48 := by rw [← hY, ← hX]; exact offs (by omega) (by omega) (by omega)
  obtain ⟨m32, c32, u32, K32⟩ := bz_copy_loop (P := BS) (X := X) (Y := Y) (M0 := My) (by omega) (by omega) sYX
    (by rw [← hY]; exact hiC (by decide) (by rw [hBSn]; decide) (by rw [hBSn]; decide)) hcy 11 0 rfl u31.self
    (by rw [u31.regs, v3019, add_ofNat_zero]) (by rw [u31.regs, v308, add_ofNat_zero]) (by rw [u31.regs, v309])
  obtain ⟨Mc, hMc⟩ : ∃ Mc, copyWords My Y X 12 = Mc := ⟨_, rfl⟩
  rw [hMc] at u32
  have IMc : ∀ x, Sep G 0x1B0 x 1 → Mc x = m.mem x := fun x hx => by
    rw [← hMc, copyWords_outside 12 (by rw [← hY]; exact inG hx (by decide)), IMy x hx]
  have hcc' : CodeIn Mc BS bytes2scalar384Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IMc
  have accY : accV Mc Y 12 = accV m28.mem X 12 := accV_congr2 12 fun i hi => by
    rw [← hMc, copyWords_load 12 i hi (by rw [← hY]; exact Nat.le_of_lt (hGw _ (by decide))), ← hMy, fillWords_load_sep
      ((sYX.subR (c := 4 * i) (l := 4) (by omega)))]
  -- registers the calls since `m3` keep
  have Kall : ∀ q, q.val ∈ [3, 4, 18, 24, 25, 26, 27] → reg m32 q = reg m3 q := fun q hq => by
    rw [K32 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide), u31.regs,
      K30 q (by intro h; revert h; revert hq; revert q; decide), K28' q (by intro h; revert h; revert hq; revert q; decide),
      K26 q (by intro h; revert h; revert hq; revert q; decide),
      K25' q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide),
      K18 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide),
      u17.regs, K16 q (by revert hq; revert q; decide), K15 q (by revert hq; revert q; decide),
      K11 q (by intro h; revert h; revert hq; revert q; decide),
      K10' q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  have sp32 : reg m32 sp = F := by
    rw [K32 sp (by decide) (by decide) (by decide) (by decide), u31.regs, K30 sp (by decide), K28' sp (by decide), sp26]
  obtain ⟨m33, c33, u33⟩ := St.block bzH u32 hcc' bzH_end (by simp only [BlockOk, BInstr.ok, bzH, and_self])
  have R33 : ∀ q, reg m33 q = (runBlock bzH (Mc, reg m32)).2 q := u33.regs
  have u33' : St Mc BS m33 0xFC (reg m33) := ⟨u33.pc, by rw [u33.mem]; rfl, fun _ => rfl⟩
  have K33 : ∀ q, q ≠ a0 → q ≠ a1 → reg m33 q = reg m32 q := fun q h0 h1 => by
    rw [R33]; refine runBlock_reg _ _ _ q u32.zero ?_
    simp only [bzH, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1]
  have v33 : reg m33 a1 = Y ∧ reg m33 a0 = out := by
    simp +decide only [R33, runBlock, BInstr.run, bzH, upd_app, ↓reduceIte]
    rw [sp32, Kall 18 (by decide), v318]; simp only [ev_add, eFY, true_and]; exact zw _
  obtain ⟨v33a1, v33a0⟩ := v33
  have hNWa : (BitVec.ofNat 32 p384ScalarNewAddress : Word).toNat = p384ScalarNewAddress := by decide
  obtain ⟨m34, c34, pc34, mem34, regs34⟩ := u33'.callRa hcc' bz_at_fc bz_at_100
    (cb := BitVec.ofNat 32 p384ScalarNewAddress) (by decide) (by decide)
  have r34 := PEnv.reg1 regs34 u33'.zero
  have eFG0 : F + 0xFFFFFF10 = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
  have lowG : ∀ {a : Word} {k : Nat}, Sep G 0x1B0 a k → Sep a k G 0xF0 := fun h => by
    have := h.symm.subR (c := 0) (l := 0xF0) (by decide); rwa [add_ofNat_zero] at this
  have hlo : p384OrderData.length = 48 := by decide
  have hlr : p384ScalarR2Data.length = 48 := by decide
  have EN : N3NEnv m34.mem (BitVec.ofNat 32 p384ScalarNewAddress) F out Y := by
    rw [mem34]
    refine ⟨by decide, cd E.nw (by rw [hNWa]; decide) (by rw [hNWa]; decide) IMc,
      fun i hi => by rw [IMc _ (sGN.subR (c := i) (l := 1) (by omega))]; exact E.nmod i hi,
      fun i hi => by rw [IMc _ (sGR.subR (c := i) (l := 1) (by omega))]; exact E.r2 i hi, ?_⟩
    refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, hFa, by omega, hoa, by omega, by decide, by decide, hOw,
      ?_, ?_, ?_, ?_, ?_, ?_, by rw [eFG0]; exact lowG sOG.symm, ?_, ?_, ?_,
      by rw [eFG0, ← hY]; have := offs (c := 0x15C) (n := 48) (d := 0) (k := 0xF0) (by omega) (by omega) (by omega)
         rwa [add_ofNat_zero] at this,
      by rw [eFG0]; exact lowG sGR, by rw [eFG0]; exact lowG sGN⟩
    · rw [show BitVec.ofNat 32 p384ScalarNewAddress + 0xFFFFEE64 = BitVec.ofNat 32 mulMont12Address by decide]
      exact cd E.mm (by decide) (by decide) IMc
    · rw [show BitVec.ofNat 32 p384ScalarNewAddress + 0xFFFFEE64 + 0x1B0C = BitVec.ofNat 32 memsetAddress by decide]
      exact cd E.fb.ms (by decide) (by decide) IMc
    · rw [show mmBsub (BitVec.ofNat 32 p384ScalarNewAddress + 0xFFFFEE64) = BitVec.ofNat 32 borrowingSubAddress by
        decide]
      exact cd E.bsb (by decide) (by decide) IMc
    · rw [show BitVec.ofNat 32 p384ScalarNewAddress + 0xFFFFEE64 + 0x18E = BitVec.ofNat 32 uintSelect12Address by
        decide]
      exact cd E.sel (by decide) (by decide) IMc
    · rw [show BitVec.ofNat 32 p384ScalarNewAddress + 0xFFFFEE64 + 0x1B74 = BitVec.ofNat 32 memcpyStubAddress by
        decide]
      exact cd E.fb.cs (by decide) (by decide) IMc
    · rw [show BitVec.ofNat 32 p384ScalarNewAddress + 0xFFFFEE64 + 0x1B7C = BitVec.ofNat 32 memcpyStubAddress + 8 by
        decide]
      exact cd E.fb.cb (by decide) (by decide) IMc
    all_goals first
      | (rw [eFG0]; exact sGcode (by decide) (by decide))
      | exact sOcode (by decide) (by decide)
  have sp33 : reg m33 sp = F := by rw [K33 sp (by decide) (by decide), sp32]
  obtain ⟨m35, c35, pc35, sp35, K35, val35, fr35⟩ := p384ScalarNew_correct m34 (P := BitVec.ofNat 32 p384ScalarNewAddress)
    (sp0 := F) (out := out) (xp := Y) (retAddr := BS + BitVec.ofNat 32 (0xFC + 8)) EN pc34
    (by rw [r34 a0 (by decide), v33a0]) (by rw [r34 a1 (by decide), v33a1])
    (by rw [regs34]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at BS (by decide) _ (by decide)))
    (by rw [r34 sp (by decide), sp33])
  rw [mem34, accY] at val35
  rw [mem34, eFG0] at fr35
  have hc35 : CodeIn m35.mem BS bytes2scalar384Code := fun i hi => by
    have hx := code_hi (b := BS) (by rw [hBSn]; decide) (by rw [hBSn]; decide) hi
    have hx' : dramEnd ≤ (BS + BitVec.ofNat 32 i).toNat := by unfold dramEnd; omega
    rw [fr35 _ (lowG (hiG _ hx')).symm (hiO _ hx'), IMc _ (hiG _ hx')]; exact hc i hi
  have u35 : St m35.mem BS m35 0x104 (reg m35) := ⟨by rw [pc35], rfl, fun _ => rfl⟩
  -- the saved registers' slots, at `G + 0x18C` to `G + 0x1B0`, are untouched since the prologue
  have lowS : ∀ {a l c : Nat}, a + l ≤ c → c < 0x1B0 → Sep (G + BitVec.ofNat 32 a) l (G + BitVec.ofNat 32 c) 1 :=
    fun h1 h2 => offs (by omega) (by omega) (by omega)
  have slotM : ∀ c, 0x18C ≤ c → c < 0x1B0 → m35.mem (G + BitVec.ofNat 32 c) = Ms (G + BitVec.ofNat 32 c) :=
    fun c h1 h2 => by
      have hG0 : Sep G 0xF0 (G + BitVec.ofNat 32 c) 1 := by
        have := lowS (a := 0) (l := 0xF0) (c := c) (by omega) h2; rwa [add_ofNat_zero] at this
      have h4 : G + BitVec.ofNat 32 c ≠ F + 0x4 := fun e => by
        have h := lowS (a := 0xF0 + 4) (l := 1) (c := c) (by omega) h2
        rw [← eFk] at h
        exact h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e]; rfl)
      rw [fr35 _ hG0 (sOG.subR (c := c) (l := 1) (by omega)), ← hMc,
        copyWords_outside 12 (by rw [← hY]; exact lowS (by omega) h2), ← hMy,
        fillWords_outside 12 (by rw [← hY]; exact lowS (by omega) h2),
        fr28 _ (lowS (by omega) h2) (by rw [← hX]; exact lowS (by omega) h2),
        fr24 _ (lowS (by omega) h2), fr21 _ (lowS (by omega) h2),
        fr18 _ (by rw [eFm4]; exact lowS (by omega) h2) (by rw [← hD]; exact lowS (by omega) h2), ← hMz,
        fillWords_outside 12 (by rw [← hD]; exact lowS (by omega) h2),
        fr13 _ (by rw [eF70]; exact lowS (by omega) h2) (by rw [← hX]; exact lowS (by omega) h2), mem12, ← hMr,
        memStore32_get_sep (by rw [show (0x8 : Word) = BitVec.ofNat 32 8 from rfl, eFk]; exact lowS (by omega) h2),
        memStore8_ne h4, fr5 _ (by rw [eFm]; exact lowS (by omega) h2), mem4]
  have slot : ∀ o : Word, 0x9C ≤ o.toNat → o.toNat + 4 ≤ 0xC0 → memLoad32 m35.mem (F + o) = memLoad32 Ms (F + o) :=
    fun o h1 h2 => by
      rw [slotO]
      apply memLoad32_congr; intro j hj
      rw [add_ofNat_assoc, eFk]; exact slotM _ (by omega) (by omega)
  have hpsp : ∀ p ∈ bzPs, p.1 ≠ sp := by decide
  obtain ⟨n1, c36, u36⟩ := St.block (restoreBlock bzPs) u35 hc35 bzRestore_end
    (restoreBlock_ok m35.mem F bzPs (reg m35) sp35 hpsp fun q hq => by
      simp only [bzPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run m35.mem F bzPs (reg m35) sp35 hpsp] at u36
  have rsp : restoreRegs m35.mem F (reg m35) bzPs sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp35
  obtain ⟨n2, d37, u37⟩ := u36.aluImm hc35 bz_at_116 (off' := 0x118) (by decide)
  obtain ⟨n3, d38, pc38, mem38, regs38⟩ := u37.jalr hc35 bz_at_118
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs m35.mem F f ps q = f q := by
    intro f ps q hq0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
  have hslot : ∀ r o, (r, o) ∈ bzPs → reg n3 r = reg m r := fun r o hm => by
    rw [regs38]
    simp only [bzPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
      rw [slot _ (by decide) (by decide)]; exact slots _ _ (by decide)
  refine ⟨n3, (.cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans (c11.trans (c12.trans (c13.trans (c14.trans (c15.trans (.cons d16 (.cons d17 (c18.trans (.cons d19 (c20.trans (c21.trans (.cons d22 (c23.trans (c24.trans (.cons d25 (c26.trans (c27.trans (c28.trans (c29.trans (c30.trans (.cons d31 (c32.trans (c33.trans (c34.trans (c35.trans (c36.trans (.cons d37 (.single d38)))))))))))))))))))))))))))))))))))))),
    ?_, ?_, fun q hq => ?_, ?_, fun x hx hl => ?_⟩
  · rw [pc38, ← regs38, hslot ra 0xBC (by decide), hra, add_lit_zero, hret]
  · rw [regs38]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [rsp, eFS]
  · rcases (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨
        q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q = (23 : Fin 32) ∨ q.val ∈ [3, 4, 24, 25, 26, 27]) q hq with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hL
    · exact hslot _ 0xBC (by decide)
    · exact hslot _ 0xB8 (by decide)
    · exact hslot _ 0xB4 (by decide)
    · exact hslot _ 0xB0 (by decide)
    · exact hslot _ 0xAC (by decide)
    · exact hslot _ 0xA8 (by decide)
    · exact hslot _ 0xA4 (by decide)
    · exact hslot _ 0xA0 (by decide)
    · exact hslot _ 0x9C (by decide)
    · obtain ⟨hv, hs, hps, hr, h0, h1⟩ : q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ bzPs, p.1 ≠ q) ∧ q ≠ ra ∧ q ≠ a0 ∧ q ≠ a1 := by
        revert hL; revert q; decide
      rw [regs38, upd_ne hv hs, rr _ _ q hv hps,
        K35 q ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 24, 25, 26, 27] →
          q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) q hL), r34 q hr, K33 q h0 h1,
        Kall q ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 24, 25, 26, 27] → q.val ∈ [3, 4, 18, 24, 25, 26, 27]) q hL),
        K3 q ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 24, 25, 26, 27] → q.val ∉ [10, 11, 18, 19, 20, 22, 23]) q hL),
        r2 q hs]
  · rw [mem38]; rw [val35]; exact xmod
  · rw [mem38, fr35 x (lowG hx).symm hl, IMc x hx]


end C3.RV32
