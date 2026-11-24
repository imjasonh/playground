import C3BootProofs.Proofs.MontRetrieve12

/-!
# Montgomery reduction out of P-256's field Montgomery form

`ConstMontyForm<p256 FieldParams, 8>::retrieve` is `montgomery_retrieve::<8>`
specialized to P-256's field modulus and inlined. Because the modulus's low
limb is `2^32 - 1`, `-n⁻¹ mod 2^32` is 1, so each pass's factor `u` is the
low word itself, and the code forms `u · (2^32 - 1)` from `mulhu` and a
nonzero test. The modulus's other limbs are read from the image at
`p256ModulusAddress + 0x4`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem pr_at_0 : fetchRel p256FieldRetrieveCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem pr_at_2 : fetchRel p256FieldRetrieveCode 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem pr_at_4 : fetchRel p256FieldRetrieveCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem pr_at_6 : fetchRel p256FieldRetrieveCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem pr_at_8 : fetchRel p256FieldRetrieveCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem pr_at_a : fetchRel p256FieldRetrieveCode 0xA = some (.store .sw sp (19 : Fin 32) 0x2C, 2) := by decide
theorem pr_at_c : fetchRel p256FieldRetrieveCode 0xC = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem pr_at_e : fetchRel p256FieldRetrieveCode 0xE = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem pr_at_10 : fetchRel p256FieldRetrieveCode 0x10 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem pr_at_12 : fetchRel p256FieldRetrieveCode 0x12 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem pr_at_16 : fetchRel p256FieldRetrieveCode 0x16 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem pr_at_18 : fetchRel p256FieldRetrieveCode 0x18 = some (.auipc ra 0x2000, 4) := by decide
theorem pr_at_1c : fetchRel p256FieldRetrieveCode 0x1C = some (.jalr ra ra 0x796, 4) := by decide
theorem pr_at_20 : fetchRel p256FieldRetrieveCode 0x20 = some (.aluImm .add (7 : Fin 32) x0 0x0, 2) := by decide
theorem pr_at_22 : fetchRel p256FieldRetrieveCode 0x22 = some (.aluImm .add a6 sp 0x10, 4) := by decide
theorem pr_at_26 : fetchRel p256FieldRetrieveCode 0x26 = some (.aluImm .add (5 : Fin 32) x0 0x8, 2) := by decide
theorem pr_at_28 : fetchRel p256FieldRetrieveCode 0x28 = some (.aluImm .add (17 : Fin 32) x0 0xFFFFFFFF, 2) := by decide
theorem pr_at_2a : fetchRel p256FieldRetrieveCode 0x2A = some (.lui (6 : Fin 32) 0x3FCC5000, 4) := by decide
theorem pr_at_2e : fetchRel p256FieldRetrieveCode 0x2E = some (.aluImm .add (6 : Fin 32) (6 : Fin 32) 0xFFFFFB3C, 4) := by decide
theorem pr_at_32 : fetchRel p256FieldRetrieveCode 0x32 = some (.branch .beq (5 : Fin 32) x0 0x5E, 4) := by decide
theorem pr_at_36 : fetchRel p256FieldRetrieveCode 0x36 = some (.aluImm .sll a1 (7 : Fin 32) 0x2, 4) := by decide
theorem pr_at_3a : fetchRel p256FieldRetrieveCode 0x3A = some (.alu .add a1 a1 (19 : Fin 32), 2) := by decide
theorem pr_at_3c : fetchRel p256FieldRetrieveCode 0x3C = some (.load .lw a4 sp 0xC, 2) := by decide
theorem pr_at_3e : fetchRel p256FieldRetrieveCode 0x3E = some (.load .lw a5 a1 0x0, 2) := by decide
theorem pr_at_40 : fetchRel p256FieldRetrieveCode 0x40 = some (.alu .add a5 a5 a4, 2) := by decide
theorem pr_at_42 : fetchRel p256FieldRetrieveCode 0x42 = some (.alu .mulhu a1 a5 (17 : Fin 32), 4) := by decide
theorem pr_at_46 : fetchRel p256FieldRetrieveCode 0x46 = some (.alu .sltu a4 a5 a4, 4) := by decide
theorem pr_at_4a : fetchRel p256FieldRetrieveCode 0x4A = some (.alu .sltu (8 : Fin 32) x0 a5, 4) := by decide
theorem pr_at_4e : fetchRel p256FieldRetrieveCode 0x4E = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem pr_at_50 : fetchRel p256FieldRetrieveCode 0x50 = some (.alu .add a1 a1 a4, 2) := by decide
theorem pr_at_52 : fetchRel p256FieldRetrieveCode 0x52 = some (.aluImm .add (8 : Fin 32) x0 0x7, 2) := by decide
theorem pr_at_54 : fetchRel p256FieldRetrieveCode 0x54 = some (.store .sw sp a1 0xC, 2) := by decide
theorem pr_at_56 : fetchRel p256FieldRetrieveCode 0x56 = some (.alu .add a1 x0 a6, 2) := by decide
theorem pr_at_58 : fetchRel p256FieldRetrieveCode 0x58 = some (.alu .add a4 x0 (6 : Fin 32), 2) := by decide
theorem pr_at_5a : fetchRel p256FieldRetrieveCode 0x5A = some (.branch .beq (8 : Fin 32) x0 0x30, 2) := by decide
theorem pr_at_5c : fetchRel p256FieldRetrieveCode 0x5C = some (.load .lw a2 a4 0x0, 2) := by decide
theorem pr_at_5e : fetchRel p256FieldRetrieveCode 0x5E = some (.alu .mul a3 a2 a5, 4) := by decide
theorem pr_at_62 : fetchRel p256FieldRetrieveCode 0x62 = some (.alu .mulhu a2 a2 a5, 4) := by decide
theorem pr_at_66 : fetchRel p256FieldRetrieveCode 0x66 = some (.load .lw (9 : Fin 32) a1 0x0, 2) := by decide
theorem pr_at_68 : fetchRel p256FieldRetrieveCode 0x68 = some (.load .lw a0 a1 0xFFFFFFFC, 4) := by decide
theorem pr_at_6c : fetchRel p256FieldRetrieveCode 0x6C = some (.alu .add (9 : Fin 32) (9 : Fin 32) a3, 2) := by decide
theorem pr_at_6e : fetchRel p256FieldRetrieveCode 0x6E = some (.alu .sltu a3 (9 : Fin 32) a3, 4) := by decide
theorem pr_at_72 : fetchRel p256FieldRetrieveCode 0x72 = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem pr_at_74 : fetchRel p256FieldRetrieveCode 0x74 = some (.alu .add a2 a2 a3, 2) := by decide
theorem pr_at_76 : fetchRel p256FieldRetrieveCode 0x76 = some (.alu .sltu a3 a0 (9 : Fin 32), 4) := by decide
theorem pr_at_7a : fetchRel p256FieldRetrieveCode 0x7A = some (.aluImm .add a4 a4 0x4, 2) := by decide
theorem pr_at_7c : fetchRel p256FieldRetrieveCode 0x7C = some (.alu .add a2 a2 a3, 2) := by decide
theorem pr_at_7e : fetchRel p256FieldRetrieveCode 0x7E = some (.store .sw a1 a0 0xFFFFFFFC, 4) := by decide
theorem pr_at_82 : fetchRel p256FieldRetrieveCode 0x82 = some (.store .sw a1 a2 0x0, 2) := by decide
theorem pr_at_84 : fetchRel p256FieldRetrieveCode 0x84 = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem pr_at_86 : fetchRel p256FieldRetrieveCode 0x86 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem pr_at_88 : fetchRel p256FieldRetrieveCode 0x88 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFD4, 2) := by decide
theorem pr_at_8a : fetchRel p256FieldRetrieveCode 0x8A = some (.aluImm .add (7 : Fin 32) (7 : Fin 32) 0x1, 2) := by decide
theorem pr_at_8c : fetchRel p256FieldRetrieveCode 0x8C = some (.branch .bne (7 : Fin 32) (5 : Fin 32) 0xFFFFFFAA, 4) := by decide
theorem pr_at_90 : fetchRel p256FieldRetrieveCode 0x90 = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem pr_at_92 : fetchRel p256FieldRetrieveCode 0x92 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem pr_at_96 : fetchRel p256FieldRetrieveCode 0x96 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem pr_at_98 : fetchRel p256FieldRetrieveCode 0x98 = some (.auipc ra 0x2000, 4) := by decide
theorem pr_at_9c : fetchRel p256FieldRetrieveCode 0x9C = some (.jalr ra ra 0x77E, 4) := by decide
theorem pr_at_a0 : fetchRel p256FieldRetrieveCode 0xA0 = some (.load .lw ra sp 0x3C, 2) := by decide
theorem pr_at_a2 : fetchRel p256FieldRetrieveCode 0xA2 = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem pr_at_a4 : fetchRel p256FieldRetrieveCode 0xA4 = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem pr_at_a6 : fetchRel p256FieldRetrieveCode 0xA6 = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem pr_at_a8 : fetchRel p256FieldRetrieveCode 0xA8 = some (.load .lw (19 : Fin 32) sp 0x2C, 2) := by decide
theorem pr_at_aa : fetchRel p256FieldRetrieveCode 0xAA = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem pr_at_ac : fetchRel p256FieldRetrieveCode 0xAC = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- One column as the specialized code computes it: the same word and carry
as `mrCols`, with the carry's three parts added in another order. -/
def prCols (N U Cin O : Word) : Word × Word :=
  let lo := aluEval .mul N U
  let hi := aluEval .mulhu N U
  let s := aluEval .add O lo
  let c1 := aluEval .sltu s lo
  let a0 := aluEval .add Cin s
  let t := aluEval .add hi c1
  let c2 := aluEval .sltu a0 s
  (a0, aluEval .add t c2)

theorem prCols_eq (N U Cin O : Word) : prCols N U Cin O = mrCols N U Cin O := by
  unfold prCols mrCols
  simp only [Prod.mk.injEq, true_and]
  show aluEval .mulhu N U + aluEval .sltu (O + aluEval .mul N U) (aluEval .mul N U) +
      aluEval .sltu (Cin + (O + aluEval .mul N U)) (O + aluEval .mul N U) =
    aluEval .sltu (Cin + (O + aluEval .mul N U)) (O + aluEval .mul N U) +
      (aluEval .sltu (O + aluEval .mul N U) (aluEval .mul N U) + aluEval .mulhu N U)
  rw [BitVec.add_comm _ (aluEval .sltu (Cin + _) _), BitVec.add_comm (aluEval .mulhu N U)]

/-- The inner loop's body, from 0x5C to its branch at 0x88. -/
def prBody : List BInstr :=
  [.lw a2 a4 0, .alu .mul a3 a2 a5, .alu .mulhu a2 a2 a5, .lw (9 : Fin 32) a1 0, .lw a0 a1 0xFFFFFFFC,
   .alu .add (9 : Fin 32) (9 : Fin 32) a3, .alu .sltu a3 (9 : Fin 32) a3, .alu .add a0 a0 (9 : Fin 32),
   .alu .add a2 a2 a3, .alu .sltu a3 a0 (9 : Fin 32), .aluImm .add a4 a4 4, .alu .add a2 a2 a3,
   .sw a1 a0 0xFFFFFFFC, .sw a1 a2 0, .aluImm .add a1 a1 4, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem prBody_end : blockEnd p256FieldRetrieveCode 0x5C prBody = some 0x88 := by decide
end

set_option maxRecDepth 20000 in
theorem prBody_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock prBody (M, f)).1 = memStore32 (memStore32 M (f a1 + 0xFFFFFFFC)
        (prCols (memLoad32 M (f a4 + 0)) (f a5) (memLoad32 M (f a1 + 0xFFFFFFFC)) (memLoad32 M (f a1 + 0))).1)
        (f a1 + 0)
        (prCols (memLoad32 M (f a4 + 0)) (f a5) (memLoad32 M (f a1 + 0xFFFFFFFC)) (memLoad32 M (f a1 + 0))).2 ∧
    (runBlock prBody (M, f)).2 a4 = f a4 + 4 ∧
    (runBlock prBody (M, f)).2 a1 = f a1 + 4 ∧
    (runBlock prBody (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 →
      (runBlock prBody (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, prBody]
  refine ⟨?_, ?_, ?_, ?_, fun q q8 q9 q10 q11 q12 q13 q14 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, hz]
    · simp [upd, hq, q8, q9, q10, q11, q12, q13, q14]

theorem prBody_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hn : (f a4 + 0).toNat % 4 = 0) (ho : (f a1 + 0).toNat % 4 = 0)
    (hc : (f a1 + 0xFFFFFFFC).toNat % 4 = 0)
    (hs1 : Sep (f a1 + 0xFFFFFFFC) 4 base len) (hs2 : Sep (f a1 + 0) 4 base len) :
    BlockOk base len prBody (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, prBody, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hn, ho, hc, ⟨hc, hs1⟩, ho, hs2⟩

theorem cnt7_dec : ∀ k : Nat, k < 7 → BitVec.ofNat 32 (7 - k) + 0xFFFFFFFF = BitVec.ofNat 32 (7 - (k + 1)) := by
  decide

theorem cnt7_ne : ∀ k : Nat, k < 7 → (BitVec.ofNat 32 (7 - (k + 1)) != 0) = decide (k + 1 < 7) := by decide

/-- The registers the inner loop's body leaves alone. -/
def prKeep (q : Fin 32) : Bool := q.val ∉ [8, 9, 10, 11, 12, 13, 14]

/-- **One pass of the inner loop**, from 0x5C: column `k + 1` of a pass. -/
theorem pr_iter {M : Word → BitVec 8} {B np acc U lo hi : Word} {n : Machine} {k : Nat}
    (s : St M B n 0x5C (reg n)) (hc : CodeIn M B p256FieldRetrieveCode) (hk : k < 7)
    (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hS1 : Sep (acc + BitVec.ofNat 32 (4 * k)) 4 B p256FieldRetrieveCode.length)
    (hS2 : Sep (acc + BitVec.ofNat 32 (4 * (k + 1))) 4 B p256FieldRetrieveCode.length)
    (ra4 : reg n a4 = np + BitVec.ofNat 32 (4 * (k + 1)))
    (ra1 : reg n a1 = acc + BitVec.ofNat 32 (4 * (k + 1)))
    (ra5 : reg n a5 = U) (rs0 : reg n (8 : Fin 32) = BitVec.ofNat 32 (7 - k))
    (hcol : mrCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1)))) U (memLoad32 M (acc + BitVec.ofNat 32 (4 * k)))
      (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1)))) = (lo, hi)) :
    ∃ n', Steps n n' ∧
      St (memStore32 (memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo) (acc + BitVec.ofNat 32 (4 * (k + 1))) hi)
        B n' (if k + 1 < 7 then 0x5C else 0x8A) (reg n') ∧
      reg n' a4 = np + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' a1 = acc + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' (8 : Fin 32) = BitVec.ofNat 32 (7 - (k + 1)) ∧
      ∀ q, prKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have ok := prBody_ok (M := M) (f := reg n) (base := B) (len := p256FieldRetrieveCode.length)
    (by rw [ra4, add_lit_zero]; exact aligned_add hnp (by omega))
    (by rw [ra1, add_lit_zero]; exact aligned_add hacc (by omega))
    (by rw [ra1, back4 acc k]; exact aligned_add hacc (by omega))
    (by rw [ra1, back4 acc k]; exact hS1)
    (by rw [ra1, add_lit_zero]; exact hS2)
  obtain ⟨n1, c1, u1⟩ := St.block prBody s hc prBody_end ok
  obtain ⟨em, e4, e1, e8, fr⟩ := prBody_run (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [em, ra4, ra1, ra5, add_lit_zero, add_lit_zero, back4 acc k, prCols_eq, hcol] at u1'
  have g : ∀ q, reg n1 q = (runBlock prBody (M, reg n)).2 q := u1.regs
  have hb : branchTaken .bne (reg n1 (8 : Fin 32)) (reg n1 x0) = decide (k + 1 < 7) := by
    rw [g, e8, rs0, cnt7_dec k hk, u1'.zero]; exact cnt7_ne k hk
  have hc1 := CodeIn.store32 (v := hi) (CodeIn.store32 (v := lo) hc hS1) hS2
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a4 = np + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n2 a1 = acc + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n2 (8 : Fin 32) = BitVec.ofNat 32 (7 - (k + 1)) ∧
      ∀ q, prKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨?_, ?_, ?_, fun q hq => ?_⟩
    · rw [h2, g, e4, ra4, ptr4]
    · rw [h2, g, e1, ra1, ptr4]
    · rw [h2, g, e8, rs0, cnt7_dec k hk]
    · rw [h2, g]
      exact fr q (pkeep_ne (r := 8) hq rfl) (pkeep_ne (r := 9) hq rfl) (pkeep_ne (r := a0) hq rfl)
        (pkeep_ne (r := a1) hq rfl) (pkeep_ne (r := a2) hq rfl) (pkeep_ne (r := a3) hq rfl)
        (pkeep_ne (r := a4) hq rfl)
  by_cases hl : k + 1 < 7
  · obtain ⟨n2, d2, u2⟩ := u1'.taken hc1 0x5C pr_at_88 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc1 0x8A pr_at_88 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- What one column does to a pass's sum, for 8 limbs. -/
theorem pr_inv_step {M M0 : Word → BitVec 8} {acc np U lo hi : Word} {X k : Nat} (hk : k < 7)
    (hw : acc.toNat + 32 ≤ 2 ^ 32) (hAN : Sep acc 32 np 32)
    (hfr : ∀ a, Sep acc 32 a 1 → M a = M0 a)
    (hab : ∀ i, k + 1 ≤ i → i < 8 →
      memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)))
    (hinv : 2 ^ 32 * accV M acc (k + 1) = accV M0 acc (k + 1) + X + U.toNat * accV M0 np (k + 1))
    (hcol : mrCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1)))) U (memLoad32 M (acc + BitVec.ofNat 32 (4 * k)))
      (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1)))) = (lo, hi)) :
    2 ^ 32 * accV (memStore32 (memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo) (acc + BitVec.ofNat 32 (4 * (k + 1)))
        hi) acc (k + 2) = accV M0 acc (k + 2) + X + U.toNat * accV M0 np (k + 2) ∧
    (∀ a, Sep acc 32 a 1 → memStore32 (memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo)
      (acc + BitVec.ofNat 32 (4 * (k + 1))) hi a = M0 a) ∧
    (∀ i, k + 2 ≤ i → i < 8 → memLoad32 (memStore32 (memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo)
      (acc + BitVec.ofNat 32 (4 * (k + 1))) hi) (acc + BitVec.ofNat 32 (4 * i)) =
        memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) := by
  have st := mr_col (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1)))) U (memLoad32 M (acc + BitVec.ofNat 32 (4 * k)))
    (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
  rw [hcol] at st
  simp only at st
  rw [load_frame hfr (hAN.subR (by omega)), hab (k + 1) (by omega) (by omega)] at st
  refine ⟨?_, fun a ha => ?_, fun i hi1 hi2 => ?_⟩
  · have hA : accV (memStore32 (memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo) (acc + BitVec.ofNat 32 (4 * (k + 1)))
        hi) acc (k + 2) = accV M acc k + lo.toNat * 2 ^ (32 * k) + hi.toNat * 2 ^ (32 * (k + 1)) := by
      show accV _ acc (k + 1) + _ = _
      rw [accV_store_above (by omega) (k + 1) (Nat.le_refl _), memLoad32_store32_same, accV_succ1,
        accV_store_above (by omega) k (Nat.le_refl k), memLoad32_store32_same]
    rw [hA, show k + 2 = (k + 1) + 1 from rfl, accV_succ1 M0 acc (k + 1), accV_succ1 M0 np (k + 1), pow32_succ k]
    rw [accV_succ1] at hinv
    exact mr_inner_arith hinv (by omega)
  · rw [memStore32_ne fun j hj e => (ha.point (i := 4 * (k + 1) + j) (j := 0) (by omega) (by decide)) (by
      rw [add_ofNat_zero, ← add_ofNat_assoc]; exact e.symm),
      memStore32_ne fun j hj e => (ha.point (i := 4 * k + j) (j := 0) (by omega) (by decide)) (by
      rw [add_ofNat_zero, ← add_ofNat_assoc]; exact e.symm), hfr a ha]
  · rw [memLoad32_store32_sep (sep_offsets acc (.inl (by omega)) (by omega) (by omega)),
      memLoad32_store32_sep (sep_offsets acc (.inl (by omega)) (by omega) (by omega)), hab i (by omega) hi2]

/-- **The inner loop**, from column `k + 1` of a pass to its end at 0x8A. -/
theorem pr_inner {B acc np U : Word} {X : Nat} {M0 : Word → BitVec 8}
    (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0) (hw : acc.toNat + 32 ≤ 2 ^ 32)
    (hAN : Sep acc 32 np 32) (hAC : Sep acc 32 B p256FieldRetrieveCode.length) :
    ∀ m k, k + m + 1 = 7 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M B n 0x5C (reg n) → CodeIn M B p256FieldRetrieveCode →
      (∀ a, Sep acc 32 a 1 → M a = M0 a) →
      (∀ i, k + 1 ≤ i → i < 8 →
        memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) →
      2 ^ 32 * accV M acc (k + 1) = accV M0 acc (k + 1) + X + U.toNat * accV M0 np (k + 1) →
      reg n a4 = np + BitVec.ofNat 32 (4 * (k + 1)) → reg n a1 = acc + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n a5 = U → reg n (8 : Fin 32) = BitVec.ofNat 32 (7 - k) →
      ∃ n' M', Steps n n' ∧ St M' B n' 0x8A (reg n') ∧ CodeIn M' B p256FieldRetrieveCode ∧
        2 ^ 32 * accV M' acc 8 = accV M0 acc 8 + X + U.toNat * accV M0 np 8 ∧
        (∀ a, Sep acc 32 a 1 → M' a = M0 a) ∧
        ∀ q, prKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro k hk M n s hc hfr hab hinv ra4 ra1 ra5 rs0
    have k6 : k = 6 := by omega
    subst k6
    obtain ⟨lo, hi, hcol⟩ : ∃ lo hi, mrCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (6 + 1)))) U
        (memLoad32 M (acc + BitVec.ofNat 32 (4 * 6))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (6 + 1)))) =
        (lo, hi) := ⟨_, _, rfl⟩
    obtain ⟨n1, c1, u1, _, _, _, fr⟩ := pr_iter (k := 6) s hc (by decide) hnp hacc
      (hAC.sub (by omega)) (hAC.sub (by omega)) ra4 ra1 ra5 rs0 hcol
    obtain ⟨i1, i2, _⟩ := pr_inv_step (k := 6) (by decide) hw hAN hfr hab hinv hcol
    exact ⟨n1, _, c1, u1, CodeIn.store32 (CodeIn.store32 hc (hAC.sub (by omega))) (hAC.sub (by omega)), i1, i2, fr⟩
  | succ m ih =>
    intro k hk M n s hc hfr hab hinv ra4 ra1 ra5 rs0
    have hl : k + 1 < 7 := by omega
    obtain ⟨lo, hi, hcol⟩ : ∃ lo hi, mrCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1)))) U
        (memLoad32 M (acc + BitVec.ofNat 32 (4 * k))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1)))) =
        (lo, hi) := ⟨_, _, rfl⟩
    obtain ⟨n1, c1, u1, e4, e1, e8, fr⟩ := pr_iter (k := k) s hc (by omega) hnp hacc
      (hAC.sub (by omega)) (hAC.sub (by omega)) ra4 ra1 ra5 rs0 hcol
    rw [ite_eq_left hl] at u1
    obtain ⟨i1, i2, i3⟩ := pr_inv_step (k := k) (by omega) hw hAN hfr hab hinv hcol
    have k5 : reg n1 a5 = U := by rw [fr _ rfl, ra5]
    obtain ⟨n', M', c', u', hc', f1, f2, fr'⟩ :=
      ih (k + 1) (by omega) u1 (CodeIn.store32 (CodeIn.store32 hc (hAC.sub (by omega))) (hAC.sub (by omega)))
        i2 i3 i1 e4 e1 k5 e8
    exact ⟨n', M', c1.trans c', u', hc', f1, f2, fun q hq => by rw [fr' q hq, fr q hq]⟩

/-- The start of a pass, as the specialized code computes it: the factor `u`,
which is the low word `X + B0` itself, and the first column's carry. -/
def prHead (X B0 : Word) : Word × Word :=
  let s := aluEval .add X B0
  let hi := aluEval .mulhu s 0xFFFFFFFF
  let c0 := aluEval .sltu s B0
  let nz := aluEval .sltu 0 s
  (s, aluEval .add hi (aluEval .add c0 nz))

set_option maxHeartbeats 2000000 in
theorem pr_head (X B0 : Word) :
    X.toNat + B0.toNat + (prHead X B0).1.toNat * 0xFFFFFFFF = 2 ^ 32 * (prHead X B0).2.toNat := by
  unfold prHead
  simp only
  have e1 := add_carry X B0
  have em := mul_mulhu (aluEval .add X B0) 0xFFFFFFFF
  generalize aluEval .add X B0 = s at e1 em ⊢
  generalize aluEval .sltu s B0 = c0 at e1 ⊢
  generalize hlo : aluEval .mul s 0xFFFFFFFF = lo at em
  generalize hhi : aluEval .mulhu s 0xFFFFFFFF = hi at em ⊢
  have hnz : (aluEval .sltu 0 s).toNat = if s.toNat = 0 then 0 else 1 := by
    show (if (0 : Word).ult s then (1 : Word) else 0).toNat = _
    by_cases h : s.toNat = 0
    · rw [ite_eq_left h, ite_eq_right (by simp only [BitVec.ult, decide_eq_true_eq]; show ¬ 0 < s.toNat; omega)]; rfl
    · rw [ite_eq_right h, ite_eq_left (by simp only [BitVec.ult, decide_eq_true_eq]; show 0 < s.toNat; omega)]; rfl
  have b1 := add_toNat c0 (aluEval .sltu 0 s)
  generalize aluEval .sltu 0 s = nz at hnz b1 ⊢
  generalize aluEval .add c0 nz = t at b1 ⊢
  have b2 := add_toNat hi t
  generalize aluEval .add hi t = c at b2 ⊢
  have := s.isLt; have := lo.isLt; have := hi.isLt; have := c0.isLt; have := t.isLt; have := c.isLt
  have := X.isLt; have := B0.isLt
  rw [show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl] at em
  have hc0 : c0.toNat ≤ 1 := by omega
  by_cases h0 : s.toNat = 0
  · rw [ite_eq_left h0] at hnz
    have ht : t.toNat = c0.toNat := by rw [b1, hnz]; omega
    have hh : hi.toNat = 0 := by rw [h0] at em; omega
    rw [b2, ht, hh, h0]; omega
  · rw [ite_eq_right h0] at hnz
    have ht : t.toNat = c0.toNat + 1 := by rw [b1, hnz]; omega
    have hh : hi.toNat = s.toNat - 1 := by
      have : s.toNat * 4294967295 = (s.toNat - 1) * 2 ^ 32 + (2 ^ 32 - s.toNat) := by omega
      omega
    have hs : s.toNat - 1 + (c0.toNat + 1) < 2 ^ 32 := by omega
    rw [b2, ht, hh, Nat.mod_eq_of_lt hs]
    omega

/-- The start of a pass, from 0x36: load the input's limb and the
accumulator's low word, compute `u` and the first column's carry, store the
carry over the low word, and set up the inner loop. -/
def prHeadBlock : List BInstr :=
  [.aluImm .sll a1 (7 : Fin 32) 2, .alu .add a1 a1 (19 : Fin 32), .lw a4 sp 0xC, .lw a5 a1 0, .alu .add a5 a5 a4,
   .alu .mulhu a1 a5 (17 : Fin 32), .alu .sltu a4 a5 a4, .alu .sltu (8 : Fin 32) x0 a5, .alu .add a4 a4 (8 : Fin 32),
   .alu .add a1 a1 a4, .aluImm .add (8 : Fin 32) x0 7, .sw sp a1 0xC, .alu .add a1 x0 a6,
   .alu .add a4 x0 (6 : Fin 32)]

section
set_option maxRecDepth 20000
theorem prHeadBlock_end : blockEnd p256FieldRetrieveCode 0x36 prHeadBlock = some 0x5A := by decide
end

/-- The registers the start of a pass leaves alone. -/
def phKeep (q : Fin 32) : Bool := q.val ∉ [8, 11, 14, 15]

set_option maxRecDepth 20000 in
theorem prHeadBlock_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) (h17 : f (17 : Fin 32) = 0xFFFFFFFF) :
    (runBlock prHeadBlock (M, f)).1 = memStore32 M (f sp + 0xC)
      (prHead (memLoad32 M (aluEval .add (aluEval .sll (f (7 : Fin 32)) 2) (f (19 : Fin 32)) + 0))
        (memLoad32 M (f sp + 0xC))).2 ∧
    (runBlock prHeadBlock (M, f)).2 a5 =
      (prHead (memLoad32 M (aluEval .add (aluEval .sll (f (7 : Fin 32)) 2) (f (19 : Fin 32)) + 0))
        (memLoad32 M (f sp + 0xC))).1 ∧
    (runBlock prHeadBlock (M, f)).2 (8 : Fin 32) = BitVec.ofNat 32 (7 - 0) ∧
    (runBlock prHeadBlock (M, f)).2 a1 = f a6 ∧
    (runBlock prHeadBlock (M, f)).2 a4 = f (6 : Fin 32) ∧
    ∀ q, phKeep q = true → (runBlock prHeadBlock (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, prHeadBlock]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; try simp only [h17]
    rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, pkeep_ne (r := 8) hq rfl, pkeep_ne (r := a1) hq rfl,
        pkeep_ne (r := a4) hq rfl, pkeep_ne (r := a5) hq rfl]

theorem prHeadBlock_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hx : (aluEval .add (aluEval .sll (f (7 : Fin 32)) 2) (f (19 : Fin 32)) + 0).toNat % 4 = 0)
    (hs : (f sp + 0xC).toNat % 4 = 0) (hsep : Sep (f sp + 0xC) 4 base len) :
    BlockOk base len prHeadBlock (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, prHeadBlock, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hs, hx, hs, hsep⟩

theorem sll8 : ∀ i : Nat, i < 8 → aluEval .sll (BitVec.ofNat 32 i) 2 = BitVec.ofNat 32 (4 * i) := by decide

theorem pass_ne8' : ∀ i : Nat, i < 8 → (BitVec.ofNat 32 (i + 1) != 8) = decide (i + 1 < 8) := by decide

/-- The registers a pass leaves alone. -/
def ppKeep (q : Fin 32) : Bool := q.val ∉ [7, 8, 9, 10, 11, 12, 13, 14, 15]

theorem ppKeep_head : ∀ q, ppKeep q = true → phKeep q = true := by decide
theorem ppKeep_body : ∀ q, ppKeep q = true → prKeep q = true := by decide

set_option exponentiation.threshold 400 in
set_option maxHeartbeats 4000000 in
/-- **One pass of the outer loop**, from 0x36: add limb `i` of the input,
and `u` times the modulus, to the accumulator, and shift the sum down a
word. -/
theorem pr_pass {B acc xp np : Word} {MB : Word → BitVec 8} {i : Nat} (hi : i < 8)
    (hxp : xp.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 32 ≤ 2 ^ 32) (hAX : Sep acc 32 xp 32) (hAN : Sep acc 32 np 32)
    (hAC : Sep acc 32 B p256FieldRetrieveCode.length) (hN0 : memLoad32 MB np = 0xFFFFFFFF)
    {M : Word → BitVec 8} {n : Machine} (s : St M B n 0x36 (reg n)) (hc : CodeIn M B p256FieldRetrieveCode)
    (hfr : ∀ a, Sep acc 32 a 1 → M a = MB a)
    (r7 : reg n (7 : Fin 32) = BitVec.ofNat 32 i) (r19 : reg n (19 : Fin 32) = xp)
    (r17 : reg n (17 : Fin 32) = 0xFFFFFFFF) (rsp : reg n sp + 0xC = acc)
    (r6 : reg n (6 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)))
    (r16 : reg n a6 = acc + BitVec.ofNat 32 (4 * (0 + 1))) (r5 : reg n (5 : Fin 32) = 8) :
    ∃ n' M', Steps n n' ∧ St M' B n' (if i + 1 < 8 then 0x36 else 0x90) (reg n') ∧
      CodeIn M' B p256FieldRetrieveCode ∧ (∀ a, Sep acc 32 a 1 → M' a = MB a) ∧
      (∃ u : Nat, u < 2 ^ 32 ∧ 2 ^ 32 * accV M' acc 8 =
        accV M acc 8 + (memLoad32 MB (xp + BitVec.ofNat 32 (4 * i))).toNat + u * accV MB np 8) ∧
      reg n' (7 : Fin 32) = BitVec.ofNat 32 (i + 1) ∧ ∀ q, ppKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hX : aluEval .add (aluEval .sll (reg n (7 : Fin 32)) 2) (reg n (19 : Fin 32)) + 0 =
      xp + BitVec.ofNat 32 (4 * i) := by
    rw [r7, r19, sll8 i hi, add_lit_zero]; exact BitVec.add_comm _ _
  have hS0 : Sep acc 4 B p256FieldRetrieveCode.length :=
    (hAC.sub (c := 0) (l := 4) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h
  have ok1 := prHeadBlock_ok (M := M) (f := reg n) (base := B) (len := p256FieldRetrieveCode.length)
    (by rw [hX]; exact aligned_add hxp (by omega)) (by rw [rsp]; exact hacc) (by rw [rsp]; exact hS0)
  obtain ⟨n1, c1, u1⟩ := St.block prHeadBlock s hc prHeadBlock_end ok1
  obtain ⟨hm1, h5, h8, h1, h4, hfr1⟩ := prHeadBlock_run (M := M) (f := reg n) hz r17
  rw [hX, rsp] at hm1 h5
  have eX : memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) = memLoad32 MB (xp + BitVec.ofNat 32 (4 * i)) :=
    load_frame hfr (hAX.subR (by omega))
  obtain ⟨u, c, hH⟩ : ∃ u c, prHead (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) (memLoad32 M acc) = (u, c) :=
    ⟨_, _, rfl⟩
  have hd := pr_head (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) (memLoad32 M acc)
  rw [hH] at hd hm1 h5
  simp only at hd hm1 h5
  have u1' := u1.self
  rw [hm1] at u1'
  have g1 : ∀ q, reg n1 q = (runBlock prHeadBlock (M, reg n)).2 q := u1.regs
  have hb : branchTaken .beq (reg n1 (8 : Fin 32)) (reg n1 x0) = false := by
    rw [g1, h8, u1'.zero]; decide
  have hc1 := CodeIn.store32 (v := c) hc hS0
  obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc1 0x5C pr_at_5a (by decide) hb
  have g2 : ∀ q, reg n2 q = (runBlock prHeadBlock (M, reg n)).2 q := fun q => by rw [u2.regs, g1]
  have frH : ∀ a, Sep acc 32 a 1 → memStore32 M acc c a = M a := fun a ha => memStore32_get_sep
    ((ha.sub (c := 0) (l := 4) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h)
  have abH : ∀ j, 0 + 1 ≤ j → j < 8 →
      memLoad32 (memStore32 M acc c) (acc + BitVec.ofNat 32 (4 * j)) = memLoad32 M (acc + BitVec.ofNat 32 (4 * j)) :=
    fun j h1 h2 => memLoad32_store32_sep (by
      have := sep_offsets acc (c := 0) (n := 4) (d := 4 * j) (k := 4) (.inl (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this)
  have eN0 : memLoad32 M np = memLoad32 MB np :=
    load_frame hfr ((hAN.subR (c := 0) (l := 4) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h)
  have inv0 : 2 ^ 32 * accV (memStore32 M acc c) acc (0 + 1) =
      accV M acc (0 + 1) + (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))).toNat + u.toNat * accV M np (0 + 1) := by
    show 2 ^ 32 * (0 + (memLoad32 (memStore32 M acc c) (acc + BitVec.ofNat 32 (4 * 0))).toNat * 1) =
      (0 + (memLoad32 M (acc + BitVec.ofNat 32 (4 * 0))).toNat * 1) + _ +
        _ * (0 + (memLoad32 M (np + BitVec.ofNat 32 (4 * 0))).toNat * 1)
    rw [Nat.mul_zero, add_ofNat_zero, add_ofNat_zero, memLoad32_store32_same, eN0, hN0]
    simp only [Nat.zero_add, Nat.mul_one]
    rw [show (0xFFFFFFFF : Word).toNat = 0xFFFFFFFF from rfl]
    omega
  obtain ⟨n3, M1, c3, u3, hc3, I1, I2, fr3⟩ :=
    pr_inner (M0 := M) (U := u) (X := (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))).toNat) hnp hacc hw hAN hAC
      6 0 (by decide) u2.self hc1 frH abH inv0
      (by rw [g2, h4, r6]) (by rw [g2, h1, r16]) (by rw [g2, h5]) (by rw [g2, h8])
  have k3 : ∀ q, ppKeep q = true → reg n3 q = reg n q := fun q hq => by
    rw [fr3 q (ppKeep_body q hq), g2, hfr1 q (ppKeep_head q hq)]
  obtain ⟨n4, d4, u4⟩ := u3.aluImm hc3 pr_at_8a (off' := 0x8C) (by decide)
  have v7 : upd (reg n3) (7 : Fin 32) (aluEval .add (reg n3 (7 : Fin 32)) 1) (7 : Fin 32) =
      BitVec.ofNat 32 (i + 1) := by
    simp +decide only [upd, ↓reduceIte]
    rw [fr3 _ rfl, g2, hfr1 _ rfl, r7]; exact ofNat_succ i
  have v5 : upd (reg n3) (7 : Fin 32) (aluEval .add (reg n3 (7 : Fin 32)) 1) (5 : Fin 32) = 8 := by
    simp +decide only [upd, ↓reduceIte]
    rw [k3 _ rfl, r5]
  have hb4 : branchTaken .bne (upd (reg n3) (7 : Fin 32) (aluEval .add (reg n3 (7 : Fin 32)) 1) (7 : Fin 32))
      (upd (reg n3) (7 : Fin 32) (aluEval .add (reg n3 (7 : Fin 32)) 1) (5 : Fin 32)) = decide (i + 1 < 8) := by
    rw [v7, v5]; exact pass_ne8' i hi
  have fr4 : ∀ a, Sep acc 32 a 1 → M1 a = MB a := fun a ha => by rw [I2 a ha, hfr a ha]
  have arith : 2 ^ 32 * accV M1 acc 8 =
      accV M acc 8 + (memLoad32 MB (xp + BitVec.ofNat 32 (4 * i))).toNat + u.toNat * accV MB np 8 := by
    rw [I1, eX]
    congr 2
    exact accV_congr 8 fun l hl => load_frame hfr (hAN.subR (by omega))
  have k4 : ∀ q, q ≠ (7 : Fin 32) → upd (reg n3) (7 : Fin 32) (aluEval .add (reg n3 (7 : Fin 32)) 1) q = reg n3 q :=
    fun q hq => by
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd, u3.zero]
      · simp [upd, h0, hq]
  by_cases hl : i + 1 < 8
  · obtain ⟨n5, d5, u5⟩ := u4.taken hc3 0x36 pr_at_8c (by decide) (by rw [hb4]; exact decide_eq_true hl)
    have g5 := u5.regs
    refine ⟨n5, M1, Steps.trans c1 (.cons d2 (c3.trans (.cons d4 (.single d5)))), by
      rw [ite_eq_left hl]; exact u5.self, hc3, fr4, ⟨u.toNat, u.isLt, arith⟩, by rw [g5, v7], fun q hq => ?_⟩
    rw [g5, k4 q (pkeep_ne (r := 7) hq rfl), k3 q hq]
  · obtain ⟨n5, d5, u5⟩ := u4.notTaken hc3 0x90 pr_at_8c (by decide) (by rw [hb4]; exact decide_eq_false hl)
    have g5 := u5.regs
    refine ⟨n5, M1, Steps.trans c1 (.cons d2 (c3.trans (.cons d4 (.single d5)))), by
      rw [ite_eq_right hl]; exact u5.self, hc3, fr4, ⟨u.toNat, u.isLt, arith⟩, by rw [g5, v7], fun q hq => ?_⟩
    rw [g5, k4 q (pkeep_ne (r := 7) hq rfl), k3 q hq]

set_option exponentiation.threshold 400 in
/-- **The outer loop**, from pass `i` to its end at 0x90. -/
theorem pr_outer {B acc xp np : Word} {MB : Word → BitVec 8}
    (hxp : xp.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 32 ≤ 2 ^ 32) (hAX : Sep acc 32 xp 32) (hAN : Sep acc 32 np 32)
    (hAC : Sep acc 32 B p256FieldRetrieveCode.length) (hN0 : memLoad32 MB np = 0xFFFFFFFF) :
    ∀ m i, i + m + 1 = 8 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M B n 0x36 (reg n) → CodeIn M B p256FieldRetrieveCode → (∀ a, Sep acc 32 a 1 → M a = MB a) →
      (∃ U, U < 2 ^ (32 * i) ∧ 2 ^ (32 * i) * accV M acc 8 = accV MB xp i + U * accV MB np 8) →
      reg n (7 : Fin 32) = BitVec.ofNat 32 i → reg n (19 : Fin 32) = xp → reg n (17 : Fin 32) = 0xFFFFFFFF →
      reg n sp + 0xC = acc → reg n (6 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n a6 = acc + BitVec.ofNat 32 (4 * (0 + 1)) → reg n (5 : Fin 32) = 8 →
      ∃ n' M', Steps n n' ∧ St M' B n' 0x90 (reg n') ∧ CodeIn M' B p256FieldRetrieveCode ∧
        (∀ a, Sep acc 32 a 1 → M' a = MB a) ∧
        (∃ U, U < 2 ^ (32 * 8) ∧ 2 ^ (32 * 8) * accV M' acc 8 = accV MB xp 8 + U * accV MB np 8) ∧
        ∀ q, ppKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro i hi M n s hc hfr hinv r7 r19 r17 rsp r6 r16 r5
    have i7 : i = 7 := Nat.succ.inj hi
    subst i7
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, _, k1⟩ := pr_pass (i := 7) (by decide) hxp hnp hacc
      hw hAX hAN hAC hN0 s hc hfr r7 r19 r17 rsp r6 r16 r5
    obtain ⟨U, hU, hUv⟩ := hinv
    obtain ⟨a1, a2⟩ := mr_outer_arith hp hUv hU hu
    refine ⟨n1, M1, c1, u1, hc1, hf1, ⟨U + 2 ^ (32 * 7) * u, by rw [pow32_succ 7]; exact a2, ?_⟩, k1⟩
    rw [pow32_succ 7, a1, accV_succ1 MB xp 7]
  | succ m ih =>
    intro i hi M n s hc hfr hinv r7 r19 r17 rsp r6 r16 r5
    have hl : i + 1 < 8 := idx_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, e7, k1⟩ := pr_pass (i := i)
      (Nat.lt_trans (Nat.lt_succ_self i) hl) hxp hnp hacc hw hAX hAN hAC hN0 s hc hfr r7 r19 r17 rsp r6 r16 r5
    rw [ite_eq_left hl] at u1
    obtain ⟨U, hU, hUv⟩ := hinv
    obtain ⟨a1, a2⟩ := mr_outer_arith hp hUv hU hu
    have inv1 : ∃ U, U < 2 ^ (32 * (i + 1)) ∧
        2 ^ (32 * (i + 1)) * accV M1 acc 8 = accV MB xp (i + 1) + U * accV MB np 8 :=
      ⟨U + 2 ^ (32 * i) * u, by rw [pow32_succ i]; exact a2, by rw [pow32_succ i, a1, accV_succ1 MB xp i]⟩
    obtain ⟨n', M', c', u', hc', hf', hv', k'⟩ := ih (i + 1) (idx_succ hi) u1 hc1 hf1 inv1 e7
      (by rw [k1 _ rfl, r19]) (by rw [k1 _ rfl, r17]) (by rw [k1 _ rfl, rsp])
      (by rw [k1 _ rfl, r6]) (by rw [k1 _ rfl, r16]) (by rw [k1 _ rfl, r5])
    exact ⟨n', M', c1.trans c', u', hc', hf', hv', fun q hq => by rw [k' q hq, k1 q hq]⟩

/-- What the specialized retrieve saves in its frame, at offsets from its
`sp`. -/
abbrev prPs : List (Fin 32 × Word) :=
  [(ra, 0x3C), ((8 : Fin 32), 0x38), ((9 : Fin 32), 0x34), ((18 : Fin 32), 0x30), ((19 : Fin 32), 0x2C)]

/-- From 0xC: keep the arguments, and set up the call to `memset`. -/
def prPro : List BInstr :=
  [.alu .add (19 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0xC, .aluImm .add a2 x0 0x20,
   .aluImm .add a1 x0 0]

/-- From 0x20: zero the pass count, and set up the accumulator pointer, the
pass bound, `2^32 - 1`, and the pointer to the modulus's limb 1. -/
def prSetup : List BInstr :=
  [.aluImm .add (7 : Fin 32) x0 0, .aluImm .add a6 sp 0x10, .aluImm .add (5 : Fin 32) x0 8,
   .aluImm .add (17 : Fin 32) x0 0xFFFFFFFF, .lui (6 : Fin 32) 0x3FCC5000,
   .aluImm .add (6 : Fin 32) (6 : Fin 32) 0xFFFFFB3C]

/-- From 0x90: set up the call to `memcpy`. -/
def prArgs : List BInstr :=
  [.aluImm .add a1 sp 0xC, .aluImm .add a2 x0 0x20, .alu .add a0 x0 (18 : Fin 32)]

section
set_option maxRecDepth 20000
theorem prSave_end : blockEnd p256FieldRetrieveCode 2 (saveBlock prPs) = some 0xC := by decide
theorem prPro_end : blockEnd p256FieldRetrieveCode 0xC prPro = some 0x18 := by decide
theorem prSetup_end : blockEnd p256FieldRetrieveCode 0x20 prSetup = some 0x32 := by decide
theorem prArgs_end : blockEnd p256FieldRetrieveCode 0x90 prArgs = some 0x98 := by decide
theorem prRestore_end : blockEnd p256FieldRetrieveCode 0xA0 (restoreBlock prPs) = some 0xAA := by decide
end

/-- The P-256 field modulus's limbs, where the image keeps them. -/
abbrev p256Np : Word := (img% p256ModulusAddress)

/-- Where the specialized retrieve runs: its code and its callees', the 0x40
bytes of stack below `sp0`, and the result and input, aligned and apart from
what each must not touch. -/
structure PREnv (M : Word → BitVec 8) (P sp0 out xp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P p256FieldRetrieveCode
  mset : CodeIn M (P + 0x27AE) memsetCode
  stub : CodeIn M (P + 0x2816) memcpyStubCode
  body : CodeIn M (P + 0x281E) memcpyBodyCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x40 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hxp : xp.toNat % 4 = 0
  hwo : out.toNat + 32 < 2 ^ 32
  hN0 : memLoad32 M p256Np = 0xFFFFFFFF
  sGC : Sep (sp0 + 0xFFFFFFC0) 0x40 P p256FieldRetrieveCode.length
  sGM : Sep (sp0 + 0xFFFFFFC0) 0x40 (P + 0x27AE) memsetCode.length
  sGU : Sep (sp0 + 0xFFFFFFC0) 0x40 (P + 0x2816) memcpyStubCode.length
  sGY : Sep (sp0 + 0xFFFFFFC0) 0x40 (P + 0x281E) memcpyBodyCode.length
  sOG : Sep out 32 (sp0 + 0xFFFFFFC0) 0x40
  sOC : Sep out 32 P p256FieldRetrieveCode.length
  sOY : Sep out 32 (P + 0x281E) memcpyBodyCode.length
  sXG : Sep xp 32 (sp0 + 0xFFFFFFC0) 0x40
  sNG : Sep p256Np 32 (sp0 + 0xFFFFFFC0) 0x40

theorem prFrame (sp0 : Word) (h : 0x40 ≤ sp0.toNat) : (sp0 + 0xFFFFFFC0).toNat + 0x40 = sp0.toNat := by
  rw [BitVec.toNat_add]; have : (0xFFFFFFC0 : Word).toNat = 0xFFFFFFC0 := rfl; rw [this]; have := sp0.isLt; omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The prologue**, from 0 to the outer loop at 0x36: open the frame at
`G`, save registers, zero the accumulator at `G + 0xC`, and set up the first
pass. -/
theorem pr_pro (m : Machine) {P sp0 out xp : Word} (E : PREnv m.mem P sp0 out xp) (hpc : m.pc = P)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp) (hsp : reg m sp = sp0) :
    ∃ n M, Steps m n ∧ St M P n 0x36 (reg n) ∧
      (∀ x, Sep (sp0 + 0xFFFFFFC0) 0x40 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ prPs → memLoad32 M (sp0 + 0xFFFFFFC0 + o) = reg m r) ∧
      accV M (sp0 + 0xFFFFFFC0 + 0xC) 8 = 0 ∧
      reg n sp = sp0 + 0xFFFFFFC0 ∧ reg n (7 : Fin 32) = BitVec.ofNat 32 0 ∧
      reg n (19 : Fin 32) = xp ∧ reg n (17 : Fin 32) = 0xFFFFFFFF ∧
      reg n (6 : Fin 32) = p256Np + BitVec.ofNat 32 (4 * (0 + 1)) ∧
      reg n a6 = sp0 + 0xFFFFFFC0 + 0xC + BitVec.ofNat 32 (4 * (0 + 1)) ∧
      reg n (5 : Fin 32) = 8 ∧ reg n (18 : Fin 32) = out ∧
      ∀ q, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] → reg n q = reg m q := by
  have hG := prFrame sp0 E.hS
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hGa : (sp0 + 0xFFFFFFC0).toNat % 4 = 0 := aligned_add E.hsp (k := 0xFFFFFFC0) (by decide)
  obtain ⟨m1, d1, u1⟩ := s0.aluImm E.code pr_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0) sp = sp0 + 0xFFFFFFC0 := by
    simp +decide [upd, hsp]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock prPs) u1 E.code prSave_end (saveBlock_ok _ prPs _ fun q hq => by
      rw [sp1]
      simp only [prPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add hGa (by decide), E.sGC.sub (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  have codeS : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFFC0) 0x40 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFFC0) 0x40 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have I2 : ∀ x, Sep (sp0 + 0xFFFFFFC0) 0x40 x 1 →
      saveMem m.mem (sp0 + 0xFFFFFFC0) (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0)) prPs x = m.mem x :=
    fun x hx => saveMem_outside prPs fun q hq => by
      simp only [prPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> exact hx.sub (by decide)
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q1]
  have sp2 : reg m2 sp = sp0 + 0xFFFFFFC0 := by rw [u2.regs]; exact sp1
  have hc2 := codeS E.code E.sGC I2
  obtain ⟨m3, c3, u3⟩ := St.block prPro u2.self hc2 prPro_end (by
    simp only [BlockOk, BInstr.ok, prPro]; exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩)
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem (sp0 + 0xFFFFFFC0) (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0))
      prPs = Ms := ⟨_, rfl⟩
  rw [hMs] at u3 I2 hc2
  have g3 : ∀ q, reg m3 q = (runBlock prPro (Ms, reg m2)).2 q := u3.regs
  have em3 : (runBlock prPro (Ms, reg m2)).1 = Ms := by simp only [runBlock, BInstr.run, prPro]
  have u3' : St Ms P m3 0x18 (reg m3) := ⟨u3.pc, by rw [u3.mem, em3], fun _ => rfl⟩
  have pa0 : reg m3 a0 = sp0 + 0xFFFFFFC0 + 0xC := by
    rw [g3]; simp +decide only [runBlock, BInstr.run, prPro, upd, ↓reduceIte]; rw [sp2]; rfl
  have pa1 : reg m3 a1 = 0 := by rw [g3]; simp +decide only [runBlock, BInstr.run, prPro, upd, ↓reduceIte]
  have pa2 : reg m3 a2 = BitVec.ofNat 32 (4 * 8) := by
    rw [g3]; simp +decide only [runBlock, BInstr.run, prPro, upd, ↓reduceIte]
  have p19 : reg m3 (19 : Fin 32) = xp := by
    rw [g3]; simp +decide only [runBlock, BInstr.run, prPro, upd, ↓reduceIte]
    rw [r2 a1 (by decide), ha1]; exact BitVec.zero_add _
  have p18 : reg m3 (18 : Fin 32) = out := by
    rw [g3]; simp +decide only [runBlock, BInstr.run, prPro, upd, ↓reduceIte]
    rw [r2 a0 (by decide), ha0]; exact BitVec.zero_add _
  have pk : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (18 : Fin 32) → q ≠ (19 : Fin 32) → reg m3 q = reg m2 q :=
    fun q q0 q1 q2 q18 q19 => by
      rw [g3]; refine runBlock_reg _ _ _ q u2.self.zero ?_
      simp only [prPro, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      simp [q0, q1, q2, q18, q19]
  obtain ⟨m4, c4, u4, a04, fr4⟩ := u3'.memsetW (B := P + 0x27AE) (w := 8) (dst := sp0 + 0xFFFFFFC0 + 0xC)
    (even_at P E.hP 0x27AE (by decide)) hc2 (codeS E.mset E.sGM I2) pr_at_18 pr_at_1c
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P E.hP (0x18 + 8) (by decide)) (by decide)
    (by rw [BitVec.toNat_add]; have : (0xC : Word).toNat = 0xC := rfl; rw [this]; omega) (by decide)
    (aligned_add hGa (k := 0xC) (by decide)) (E.sGM.sub (c := 0xC) (l := 32) (by decide))
    pa0 pa1 pa2
  obtain ⟨M4, hM4⟩ : ∃ M4, fillWords Ms (sp0 + 0xFFFFFFC0 + 0xC) 0 8 = M4 := ⟨_, rfl⟩
  rw [hM4] at u4
  have I4 : ∀ x, Sep (sp0 + 0xFFFFFFC0) 0x40 x 1 → M4 x = m.mem x := fun x hx => by
    rw [← hM4, fillWords_outside (dst := sp0 + 0xFFFFFFC0 + 0xC) 8 (hx.sub (c := 0xC) (l := 32) (by decide)), I2 x hx]
  have k4 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg m4 q = reg m3 q := fr4
  have sp4 : reg m4 sp = sp0 + 0xFFFFFFC0 := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      pk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp2]
  have hc4 := codeS E.code E.sGC I4
  obtain ⟨m5, c5, u5⟩ := St.block prSetup u4 hc4 prSetup_end (by
    simp only [BlockOk, BInstr.ok, prSetup]; exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩)
  have g5 : ∀ q, reg m5 q = (runBlock prSetup (M4, reg m4)).2 q := u5.regs
  have em5 : (runBlock prSetup (M4, reg m4)).1 = M4 := by simp only [runBlock, BInstr.run, prSetup]
  have u5' : St M4 P m5 0x32 (reg m5) := ⟨u5.pc, by rw [u5.mem, em5], fun _ => rfl⟩
  have s5 : reg m5 (5 : Fin 32) = 8 := by
    rw [g5]; simp +decide only [runBlock, BInstr.run, prSetup, upd, ↓reduceIte]
  obtain ⟨m6, d6, u6⟩ := u5'.notTaken hc4 0x36 pr_at_32 (by decide) (by
    simp only [branchTaken]; rw [s5, u5'.zero]; decide)
  have g6 : ∀ q, reg m6 q = reg m5 q := u6.regs
  have sk : ∀ q, q ≠ (5 : Fin 32) → q ≠ (6 : Fin 32) → q ≠ (7 : Fin 32) → q ≠ a6 → q ≠ (17 : Fin 32) →
      reg m6 q = reg m4 q := fun q h5 h6 h7 h16 h17 => by
    rw [g6, g5]; refine runBlock_reg _ _ _ q u4.zero ?_
    simp only [prSetup, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    simp [h5, h6, h7, h16, h17]
  have hnF : Sep (sp0 + 0xFFFFFFC0) 0x40 p256Np 4 := E.sNG.symm.subR (c := 0) (l := 4) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h
  refine ⟨m6, M4, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.single d6))))), u6.self, I4,
    fun r o hm => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · have slot : ∀ (r : Fin 32) (o : Word), (r, o) ∈ prPs → 0x2C ≤ o.toNat → o.toNat + 4 ≤ 0x40 →
        (∀ p ∈ prPs, p = (r, o) ∨ ((p.2.toNat + 4 ≤ o.toNat ∨ o.toNat + 4 ≤ p.2.toNat) ∧
          p.2.toNat + 4 ≤ 2 ^ 32 ∧ o.toNat + 4 ≤ 2 ^ 32)) → r ≠ sp →
        memLoad32 M4 (sp0 + 0xFFFFFFC0 + o) = reg m r := fun r o hm h1 h2 hp hr => by
      have hFo : sp0 + 0xFFFFFFC0 + BitVec.ofNat 32 o.toNat = sp0 + 0xFFFFFFC0 + o := by rw [ofNat_toNat_self]
      rw [← hM4, ← hFo, fillWords_load_sep (dst := sp0 + 0xFFFFFFC0 + 0xC) (by
        have := sep_offsets (sp0 + 0xFFFFFFC0) (c := 0xC) (n := 32) (d := o.toNat) (k := 4) (.inl (by omega))
          (by omega) (by omega)
        exact this), hFo, ← hMs, saveMem_slot prPs _ hm hp, upd_ne (by
          intro h; apply hr; exact Fin.ext (by
            simp only [prPs, List.mem_cons, List.mem_nil_iff, or_false] at hm
            rcases hm with h' | h' | h' | h' | h' <;>
              (rw [Prod.mk.injEq] at h'; rw [h'.1] at h; exact absurd h (by decide)))) hr]
    simp only [prPs, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with h' | h' | h' | h' | h' <;>
      (rw [Prod.mk.injEq] at h'; obtain ⟨rfl, rfl⟩ := h'; exact slot _ _ (by decide) (by decide) (by decide)
        (by decide) (by decide))
  · have hacw : (sp0 + 0xFFFFFFC0 + 0xC).toNat + 4 * 8 ≤ 2 ^ 32 := by
      rw [BitVec.toNat_add]; have : (0xC : Word).toNat = 0xC := rfl; rw [this]; omega
    rw [← hM4]
    exact accV_zero 8 fun i hi => fillWords_load 8 i hi hacw
  · rw [sk sp (by decide) (by decide) (by decide) (by decide) (by decide), sp4]
  · rw [g6, g5]; simp +decide only [runBlock, BInstr.run, prSetup, upd, ↓reduceIte]; rfl
  · rw [sk _ (by decide) (by decide) (by decide) (by decide) (by decide),
      k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p19]
  · rw [g6, g5]; simp +decide only [runBlock, BInstr.run, prSetup, upd, ↓reduceIte]
  · rw [g6, g5]; simp +decide only [runBlock, BInstr.run, prSetup, upd, ↓reduceIte]
  · rw [g6, g5]; simp +decide only [runBlock, BInstr.run, prSetup, upd, ↓reduceIte]; rw [sp4]
    show sp0 + 0xFFFFFFC0 + 0x10 = sp0 + 0xFFFFFFC0 + 0xC + BitVec.ofNat 32 4
    rw [BitVec.add_assoc (sp0 + 0xFFFFFFC0)]; rfl
  · exact s5.trans rfl |> fun h => by rw [g6]; exact s5
  · rw [sk _ (by decide) (by decide) (by decide) (by decide) (by decide),
      k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p18]
  · obtain ⟨h5, h6, h7, h16, h17, h2, h3, h4', h5', h6', hr, h0, h1, h18, h19, hsp'⟩ :=
      (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ (5 : Fin 32) ∧ q ≠ (6 : Fin 32) ∧
        q ≠ (7 : Fin 32) ∧ q ≠ a6 ∧ q ≠ (17 : Fin 32) ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ ra ∧
        q ≠ a0 ∧ q ≠ a1 ∧ q ≠ (18 : Fin 32) ∧ q ≠ (19 : Fin 32) ∧ q ≠ sp) q hq
    rw [sk q h5 h6 h7 h16 h17, k4 q h2 h3 h4' h5' h6' hr, pk q h0 h1 h2 h18 h19, r2 q hsp']

set_option exponentiation.threshold 400 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The compiled `ConstMontyForm<p256 FieldParams, 8>::retrieve`.** For an
input `x` of 8 limbs at `xp`, it writes to `out` a number `r` with
`r · 2^256 ≡ x (mod n)`, for the modulus `n` whose limbs the image keeps at
`p256Np`, and `r < n` when `x < n`. It returns with `sp` and the
callee-saved registers restored, and writes only `out` and the 0x40 bytes of
stack below `sp`. -/
theorem p256FieldRetrieve_correct (m : Machine) {P sp0 out xp retAddr : Word}
    (E : PREnv m.mem P sp0 out xp) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      accV m'.mem out 8 * 2 ^ 256 % accV m.mem p256Np 8 = accV m.mem xp 8 % accV m.mem p256Np 8 ∧
      (accV m.mem xp 8 < accV m.mem p256Np 8 → accV m'.mem out 8 < accV m.mem p256Np 8) ∧
      (∀ x, Sep (sp0 + 0xFFFFFFC0) 0x40 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x) ∧
      ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q := by
  have hG := prFrame sp0 E.hS
  have hGa : (sp0 + 0xFFFFFFC0).toNat % 4 = 0 := aligned_add E.hsp (k := 0xFFFFFFC0) (by decide)
  obtain ⟨n1, M1, c1, u1, hf1, hsl1, hacc0, sp1, r7, r19, r17, r6, ra6, r5, r18, rk⟩ :=
    pr_pro m E hpc ha0 ha1 hsp
  have hAw : (sp0 + 0xFFFFFFC0 + 0xC).toNat + 32 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add]; have : (0xC : Word).toNat = 0xC := rfl; rw [this]; omega
  have hAa : (sp0 + 0xFFFFFFC0 + 0xC).toNat % 4 = 0 := aligned_add hGa (k := 0xC) (by decide)
  have codeG : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFFC0) 0x40 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFFC0) 0x40 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hc1 := codeG E.code E.sGC hf1
  have en0 : memLoad32 M1 p256Np = memLoad32 m.mem p256Np :=
    load_frame hf1 (E.sNG.symm.subR (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
  have hAX : Sep (sp0 + 0xFFFFFFC0 + 0xC) 32 xp 32 := E.sXG.symm.sub (c := 0xC) (l := 32) (by decide)
  have hAN : Sep (sp0 + 0xFFFFFFC0 + 0xC) 32 p256Np 32 := E.sNG.symm.sub (c := 0xC) (l := 32) (by decide)
  have hAC : Sep (sp0 + 0xFFFFFFC0 + 0xC) 32 P p256FieldRetrieveCode.length := E.sGC.sub (c := 0xC) (l := 32) (by decide)
  obtain ⟨n2, M2, c2, u2, hc2, hf2, ⟨U, hU, hUv⟩, k2⟩ := pr_outer (MB := M1) (by exact E.hxp) (by decide) hAa hAw
    hAX hAN hAC (by rw [en0]; exact E.hN0) 7 0 (by decide) u1 hc1 (fun _ _ => rfl)
    ⟨0, by decide, by rw [hacc0, Nat.mul_zero, Nat.zero_mul]; rfl⟩
    r7 r19 r17 (by rw [sp1]) r6 ra6 r5
  have fS : ∀ {b : Word}, Sep (sp0 + 0xFFFFFFC0) 0x40 b 32 → accV M1 b 8 = accV m.mem b 8 := fun {b} hs =>
    accV_congr 8 fun i hi => load_frame hf1 (hs.subR (by omega))
  rw [fS E.sXG.symm, fS E.sNG.symm] at hUv
  have hf2G : ∀ x, Sep (sp0 + 0xFFFFFFC0) 0x40 x 1 → M2 x = m.mem x := fun x hx => by
    rw [hf2 x (hx.sub (c := 0xC) (l := 32) (by decide)), hf1 x hx]
  have sp2 : reg n2 sp = sp0 + 0xFFFFFFC0 := by rw [k2 _ rfl, sp1]
  have hc2' := codeG E.code E.sGC hf2G
  obtain ⟨n3, c3, u3⟩ := St.block prArgs u2 hc2' prArgs_end (by
    simp only [BlockOk, BInstr.ok, prArgs]; exact ⟨trivial, trivial, trivial, trivial⟩)
  have g3 : ∀ q, reg n3 q = (runBlock prArgs (M2, reg n2)).2 q := u3.regs
  have em3 : (runBlock prArgs (M2, reg n2)).1 = M2 := by simp only [runBlock, BInstr.run, prArgs]
  have u3' : St M2 P n3 0x98 (reg n3) := ⟨u3.pc, by rw [u3.mem, em3], fun _ => rfl⟩
  have eY : P + 0x2816 + 8 = P + 0x281E := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n4, c4, u4, _, fr4⟩ := u3'.memcpyW (B := P + 0x2816) (w := 8) (dst := out)
    (src := sp0 + 0xFFFFFFC0 + 0xC) (even_at P E.hP 0x2816 (by decide)) hc2' (codeG E.stub E.sGU hf2G)
    (by rw [eY]; exact codeG E.body E.sGY hf2G) pr_at_98 pr_at_9c (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (even_at P E.hP (0x98 + 8) (by decide)) (by decide) (by have := E.hwo; omega) (by decide) E.hout hAa
    (E.sOG.subR (c := 0xC) (l := 32) (by decide)) (by rw [eY]; exact E.sOY)
    (by rw [g3]; simp +decide only [runBlock, BInstr.run, prArgs, upd, ↓reduceIte]; rw [k2 _ rfl, r18]
        exact BitVec.zero_add _)
    (by rw [g3]; simp +decide only [runBlock, BInstr.run, prArgs, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [g3]; simp +decide only [runBlock, BInstr.run, prArgs, upd, ↓reduceIte])
  obtain ⟨M4, hM4⟩ : ∃ M4, copyWords M2 out (sp0 + 0xFFFFFFC0 + 0xC) 8 = M4 := ⟨_, rfl⟩
  rw [hM4] at u4
  have I4 : ∀ x, Sep out 32 x 1 → M4 x = M2 x := fun x hx => by rw [← hM4, copyWords_outside 8 hx]
  have hc4 : CodeIn M4 P p256FieldRetrieveCode := fun i hi => by
    rw [I4 _ (E.sOC.subR (c := i) (l := 1) (by omega))]; exact hc2' i hi
  have k4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ ra → reg n4 q = reg n2 q := fun q q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qr => by
    rw [fr4 q q1 q2 q3 q4 q5 q6 q7 q8 q9 qr, g3]
    refine runBlock_reg _ _ _ q u2.zero ?_
    simp only [prArgs, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    simp [q0, q1, q2]
  have sp4 : reg n4 sp = sp0 + 0xFFFFFFC0 := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), sp2]
  have slot : ∀ r o, (r, o) ∈ prPs → memLoad32 M4 (sp0 + 0xFFFFFFC0 + o) = reg m r := fun r o hm => by
    have hb : 0x2C ≤ o.toNat ∧ o.toNat + 4 ≤ 0x40 := by
      simp only [prPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    have hFo : sp0 + 0xFFFFFFC0 + BitVec.ofNat 32 o.toNat = sp0 + 0xFFFFFFC0 + o := by rw [ofNat_toNat_self]
    have h1 : Sep out (4 * 8) (sp0 + 0xFFFFFFC0 + o) 4 := by
      rw [← hFo]; exact E.sOG.subR (c := o.toNat) (l := 4) (by omega)
    have h2 : Sep (sp0 + 0xFFFFFFC0 + 0xC) 32 (sp0 + 0xFFFFFFC0 + o) 4 := by
      rw [← hFo]; exact sep_offsets _ (c := 0xC) (.inl (by omega)) (by omega) (by omega)
    rw [← hM4, copyWords_load_sep h1, load_frame hf2 h2]
    exact hsl1 r o hm
  have hpsp : ∀ p ∈ prPs, p.1 ≠ sp := by decide
  obtain ⟨n6, c6, u6⟩ := St.block (restoreBlock prPs) u4 hc4 prRestore_end
    (restoreBlock_ok M4 (sp0 + 0xFFFFFFC0) prPs (reg n4) sp4 hpsp fun q hq => by
      simp only [prPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hGa (by decide))
  simp only [restoreBlock_run M4 (sp0 + 0xFFFFFFC0) prPs (reg n4) sp4 hpsp] at u6
  have rsp6 : restoreRegs M4 (sp0 + 0xFFFFFFC0) (reg n4) prPs sp = sp0 + 0xFFFFFFC0 := by
    rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp4
  obtain ⟨n7, d7, u7⟩ := u6.aluImm hc4 pr_at_aa (off' := 0xAC) (by decide)
  obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.jalr hc4 pr_at_ac
  have rra : restoreRegs M4 (sp0 + 0xFFFFFFC0) (reg n4) prPs ra = reg m ra := by
    simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
    exact slot ra _ (by decide)
  have hout : accV n8.mem out 8 = accV M2 (sp0 + 0xFFFFFFC0 + 0xC) 8 := by
    rw [mem8, ← hM4]
    exact accV_congr2 8 fun i hi => copyWords_load 8 i hi (by have := E.hwo; omega)
  obtain ⟨f1, f2⟩ := mr_final hUv hU
  refine ⟨n8, c1.trans (c2.trans (c3.trans (c4.trans (c6.trans (.cons d7 (.single d8)))))), ?_, ?_,
    by rw [hout]; exact f1, fun h => by rw [hout]; exact f2 h, fun x hx ho => ?_, fun q hq => ?_⟩
  · rw [pc8]; simp +decide only [upd, ↓reduceIte]; rw [rra, add_lit_zero, hra, hret]
  · rw [regs8]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [rsp6, BitVec.add_assoc]; exact BitVec.add_zero _
  · rw [mem8, I4 x ho, hf2G x hx]
  · have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
        restoreRegs M4 (sp0 + 0xFFFFFFC0) f ps q = f q := by
      intro f ps q hq0
      induction ps generalizing f with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro h
        simp only [restoreRegs]
        rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
        (q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] ∧ ppKeep q = true ∧ q.val ≠ 0 ∧ q ≠ sp ∧
          q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ ra ∧
          (∀ p ∈ prPs, p.1 ≠ q)) := by decide
    have hreg : ∀ r o, (r, o) ∈ prPs → reg n8 r = reg m r := fun r o hm => by
      rw [regs8]
      simp only [prPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
        exact slot _ _ (by decide)
    rcases key q hq with rfl | rfl | rfl | rfl | rfl |
      ⟨h1, hp, h0, hsp', q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, qr, hps⟩
    · exact hreg _ 0x3C (by decide)
    · exact hreg _ 0x38 (by decide)
    · exact hreg _ 0x34 (by decide)
    · exact hreg _ 0x30 (by decide)
    · exact hreg _ 0x2C (by decide)
    · rw [regs8, upd_ne h0 hsp', rr _ _ q h0 hps, k4 q q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qr, k2 q hp, rk q h1]

end C3.RV32
