import C3BootProofs.Proofs.Memset
import C3BootProofs.Proofs.Block

/-!
# `borrowing_sub` and `sub_inner`, as compiled

`crypto_bigint::primitives::borrowing_sub` subtracts one 32-bit limb and a
borrow from another and returns the difference and the borrow out as a mask,
which it computes with Hacker's Delight's formula (`hd_borrow`).
`p256::arithmetic::field::field_impl::sub_inner` subtracts the P-256 modulus
from a 9-limb number with nine calls to it, then adds the modulus back under
the final borrow's mask.
-/

namespace C3.RV32

open C3.Image

theorem bit31 (x : Word) : x.toNat.testBit 31 = decide (2 ^ 31 ≤ x.toNat) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have := x.isLt
  by_cases h : 2 ^ 31 ≤ x.toNat
  · rw [decide_eq_true h, decide_eq_true (by omega)]
  · rw [decide_eq_false h, decide_eq_false (by omega)]

theorem srl31 (x : Word) : x >>> 31 = if 2 ^ 31 ≤ x.toNat then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  by_cases h : 2 ^ 31 ≤ x.toNat
  · rw [ite_eq_left h]; show _ = 1; omega
  · rw [ite_eq_right h]; show _ = 0; omega

/-- Hacker's Delight's borrow out of `l - r - c`, as `borrowing_sub` computes it. -/
theorem hd_borrow (l r d : Word) (c : Nat) (hc : c ≤ 1)
    (hd : d.toNat = (l.toNat + (2 ^ 32 - r.toNat) + (2 ^ 32 - c)) % 2 ^ 32) :
    ((r &&& (l ^^^ 0xFFFFFFFF)) ||| ((r ||| (l ^^^ 0xFFFFFFFF)) &&& d)) >>> 31 =
      if l.toNat < r.toNat + c then 1 else 0 := by
  rw [srl31]
  have hl := l.isLt
  have hr := r.isLt
  have hdl := d.isLt
  have bx : ∀ x : Word, ((x ^^^ 0xFFFFFFFF).toNat.testBit 31) = !x.toNat.testBit 31 := fun x => by
    rw [BitVec.toNat_xor, Nat.testBit_xor]
    show (_ ^^ true) = _
    cases x.toNat.testBit 31 <;> rfl
  have hX : decide (2 ^ 31 ≤ ((r &&& (l ^^^ 0xFFFFFFFF)) ||| ((r ||| (l ^^^ 0xFFFFFFFF)) &&& d)).toNat) =
      ((decide (2 ^ 31 ≤ r.toNat) && !decide (2 ^ 31 ≤ l.toNat)) ||
        ((decide (2 ^ 31 ≤ r.toNat) || !decide (2 ^ 31 ≤ l.toNat)) && decide (2 ^ 31 ≤ d.toNat))) := by
    rw [← bit31, BitVec.toNat_or, Nat.testBit_or, BitVec.toNat_and, Nat.testBit_and,
      BitVec.toNat_and, Nat.testBit_and, BitVec.toNat_or, Nat.testBit_or, bx, bit31, bit31, bit31]
  revert hX
  cases h1 : decide (2 ^ 31 ≤ l.toNat) <;> cases h2 : decide (2 ^ 31 ≤ r.toNat) <;>
    cases h3 : decide (2 ^ 31 ≤ d.toNat) <;> intro hX <;>
    simp only [Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false,
      Bool.or_true, Bool.or_false] at hX <;>
    have p1 := h1 <;> have p2 := h2 <;> have p3 := h3 <;>
    first
    | (have q1 := of_decide_eq_true p1; first
        | (have q2 := of_decide_eq_true p2; first
            | (have q3 := of_decide_eq_true p3; first
                | (rw [ite_eq_left (of_decide_eq_true hX)]; rw [ite_eq_left (by omega)])
                | (rw [ite_eq_right (of_decide_eq_false hX)]; rw [ite_eq_right (by omega)]))
            | (have q3 := of_decide_eq_false p3; first
                | (rw [ite_eq_left (of_decide_eq_true hX)]; rw [ite_eq_left (by omega)])
                | (rw [ite_eq_right (of_decide_eq_false hX)]; rw [ite_eq_right (by omega)])))
        | (have q2 := of_decide_eq_false p2; first
            | (have q3 := of_decide_eq_true p3; first
                | (rw [ite_eq_left (of_decide_eq_true hX)]; rw [ite_eq_left (by omega)])
                | (rw [ite_eq_right (of_decide_eq_false hX)]; rw [ite_eq_right (by omega)]))
            | (have q3 := of_decide_eq_false p3; first
                | (rw [ite_eq_left (of_decide_eq_true hX)]; rw [ite_eq_left (by omega)])
                | (rw [ite_eq_right (of_decide_eq_false hX)]; rw [ite_eq_right (by omega)]))))
    | (have q1 := of_decide_eq_false p1; first
        | (have q2 := of_decide_eq_true p2; first
            | (have q3 := of_decide_eq_true p3; first
                | (rw [ite_eq_left (of_decide_eq_true hX)]; rw [ite_eq_left (by omega)])
                | (rw [ite_eq_right (of_decide_eq_false hX)]; rw [ite_eq_right (by omega)]))
            | (have q3 := of_decide_eq_false p3; first
                | (rw [ite_eq_left (of_decide_eq_true hX)]; rw [ite_eq_left (by omega)])
                | (rw [ite_eq_right (of_decide_eq_false hX)]; rw [ite_eq_right (by omega)])))
        | (have q2 := of_decide_eq_false p2; first
            | (have q3 := of_decide_eq_true p3; first
                | (rw [ite_eq_left (of_decide_eq_true hX)]; rw [ite_eq_left (by omega)])
                | (rw [ite_eq_right (of_decide_eq_false hX)]; rw [ite_eq_right (by omega)]))
            | (have q3 := of_decide_eq_false p3; first
                | (rw [ite_eq_left (of_decide_eq_true hX)]; rw [ite_eq_left (by omega)])
                | (rw [ite_eq_right (of_decide_eq_false hX)]; rw [ite_eq_right (by omega)]))))


/-! ## `borrowing_sub` -/

/-- The difference `borrowing_sub` returns in `a0`: `l - r`, less 1 when the
borrow mask `b` is all ones. -/
def bsubD (l r b : Word) : Word := aluEval .add (aluEval .sra b 31) (aluEval .sub l r)

/-- The borrow out `borrowing_sub` returns in `a1`, as a mask. -/
def bsubB (l r d : Word) : Word :=
  aluEval .sub 0 (((r &&& (l ^^^ 0xFFFFFFFF)) ||| ((r ||| (l ^^^ 0xFFFFFFFF)) &&& d)) >>> 31)

/-- The borrow in: 0 or 1 for a mask of 0 or all ones. -/
def maskBit (b : Word) : Nat := if b = 0 then 0 else 1

theorem sra_mask : ∀ b : Word, b = 0 ∨ b = 0xFFFFFFFF → aluEval .sra b 31 = b := by
  intro b h; rcases h with rfl | rfl <;> decide

theorem bsubD_toNat (l r b : Word) (hb : b = 0 ∨ b = 0xFFFFFFFF) :
    (bsubD l r b).toNat = (l.toNat + (2 ^ 32 - r.toNat) + (2 ^ 32 - maskBit b)) % 2 ^ 32 := by
  unfold bsubD maskBit
  rw [sra_mask b hb]
  have hl := l.isLt; have hr := r.isLt
  rcases hb with rfl | rfl
  · show (0 + (l - r)).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_sub, show (0 : Word).toNat = 0 from rfl, ite_eq_left rfl]; omega
  · show (0xFFFFFFFF + (l - r)).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_sub, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl,
      ite_eq_right (by decide)]; omega

/-- **What `borrowing_sub` computes**: the difference, and the borrow out as
all ones exactly when `l < r + c` for the borrow in `c`. -/
theorem bsubB_eq (l r b : Word) (hb : b = 0 ∨ b = 0xFFFFFFFF) :
    bsubB l r (bsubD l r b) = if l.toNat < r.toNat + maskBit b then 0xFFFFFFFF else 0 := by
  unfold bsubB
  have hm : maskBit b ≤ 1 := by unfold maskBit; split <;> decide
  rw [hd_borrow l r _ (maskBit b) hm (bsubD_toNat l r b hb)]
  by_cases h : l.toNat < r.toNat + maskBit b
  · rw [ite_eq_left h, ite_eq_left h]; rfl
  · rw [ite_eq_right h, ite_eq_right h]; rfl

section

set_option maxRecDepth 20000

/-- `borrowing_sub` up to its `ret`. -/
def bsubBlock : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFF0, .aluImm .sra a2 a2 31, .alu .sub a3 a0 a1, .aluImm .xor a4 a0 0xFFFFFFFF,
   .alu .add a0 a2 a3, .alu .or a2 a1 a4, .alu .and a1 a1 a4, .alu .and a2 a2 a0, .alu .or a1 a1 a2,
   .aluImm .srl a1 a1 31, .sw sp a1 0xC, .aluImm .add a1 sp 0xC, .lw a1 sp 0xC, .alu .sub a1 x0 a1,
   .aluImm .add sp sp 0x10]

theorem bsubBlock_end : blockEnd borrowingSubCode 0 bsubBlock = some 0x28 := by decide

theorem bs_at_28 : fetchRel borrowingSubCode 0x28 = some (.jalr x0 ra 0x0, 2) := by decide

end

/-- **The compiled `borrowing_sub`.** It returns the difference in `a0` and
the borrow mask in `a1`, restores `sp`, changes only `a0` through `a4`
among the other registers, and writes only the word 4 bytes below `sp`. -/
theorem borrowingSub_correct (m : Machine) (base retAddr l r b : Word)
    (hcode : CodeAt m base borrowingSubCode) (hpc : m.pc = base) (ha0 : reg m a0 = l)
    (ha1 : reg m a1 = r) (ha2 : reg m a2 = b) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 4 = 0) (hsep : Sep (reg m sp + 0xFFFFFFFC) 4 base borrowingSubCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' a0 = bsubD l r b ∧ reg m' a1 = bsubB l r (bsubD l r b) ∧
      reg m' sp = reg m sp ∧ (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → reg m' q = reg m q) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → m'.mem x = m.mem x := by
  have hc : CodeIn m.mem base borrowingSubCode := hcode
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hsp4 : (reg m sp + 0xFFFFFFFC).toNat % 4 = 0 := aligned_add hsp (k := 0xFFFFFFFC) (by omega)
  have ok : BlockOk base borrowingSubCode.length bsubBlock (m.mem, reg m) := by
    simp only [BlockOk, BInstr.ok, BInstr.run, bsubBlock]
    simp +decide only [upd, aluEval, BitVec.add_assoc, BitVec.reduceAdd, ↓reduceIte]
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      ⟨hsp4, hsep⟩, trivial, hsp4, trivial⟩
  obtain ⟨m1, c1, u1⟩ := St.block bsubBlock s0 hc bsubBlock_end ok
  obtain ⟨M1, hM1⟩ : ∃ M1, (runBlock bsubBlock (m.mem, reg m)).1 = M1 := ⟨_, rfl⟩
  obtain ⟨g1, hg1⟩ : ∃ g1, (runBlock bsubBlock (m.mem, reg m)).2 = g1 := ⟨_, rfl⟩
  rw [hM1, hg1] at u1
  have eM : M1 = memStore32 m.mem (reg m sp + 0xFFFFFFFC) (((reg m a1 &&& (reg m a0 ^^^ 0xFFFFFFFF)) |||
      ((reg m a1 ||| (reg m a0 ^^^ 0xFFFFFFFF)) &&& bsubD (reg m a0) (reg m a1) (reg m a2))) >>> 31) := by
    rw [← hM1]; simp only [runBlock, BInstr.run, bsubBlock]
    simp +decide only [upd, aluEval, BitVec.add_assoc, BitVec.reduceAdd, ↓reduceIte]
    rfl
  have gv : g1 a0 = bsubD l r b ∧ g1 a1 = bsubB l r (bsubD l r b) ∧ g1 sp = reg m sp ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ sp → g1 q = reg m q := by
    rw [← hg1]
    simp only [runBlock, BInstr.run, bsubBlock]
    refine ⟨?_, ?_, ?_, fun q q0 q1 q2 q3 q4 qs => ?_⟩
    · simp +decide only [upd, ↓reduceIte]; rw [ha0, ha1, ha2]; rfl
    · simp +decide only [upd, ↓reduceIte]
      rw [memLoad32_store32_same, ha0, ha1, ha2]; rfl
    · simp +decide only [upd, aluEval, BitVec.add_assoc, BitVec.reduceAdd, ↓reduceIte]
      exact BitVec.add_zero _
    · by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd, hz]
      · simp [upd, h0, q0, q1, q2, q3, q4, qs]
  obtain ⟨g0, g1', gsp, gk⟩ := gv
  have hc1 : CodeIn M1 base borrowingSubCode := fun i hi => by
    rw [eM, memStore32_get_sep (hsep.subR (c := i) (l := 1) hi)]; exact hc i hi
  obtain ⟨m2, e2, pc2, mem2, regs2⟩ := u1.jalr hc1 bs_at_28
  refine ⟨m2, c1.trans (.single e2), ?_, ?_, ?_, ?_, ?_, fun x hx => ?_⟩
  · rw [pc2, gk ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hra, add_lit_zero,
      hret]
  · rw [regs2, g0]
  · rw [regs2, g1']
  · rw [regs2, gsp]
  · intro q q0 q1 q2 q3 q4
    rw [regs2]
    by_cases qs : q = sp
    · rw [qs, gsp]
    · exact gk q q0 q1 q2 q3 q4 qs
  · rw [mem2, eM, memStore32_get_sep hx]

end C3.RV32
