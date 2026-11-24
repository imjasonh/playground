import C3BootProofs.Proofs.DateTime

/-!
# `time::digits::<4>`, as compiled

`c3_verify::time::digits::<4>` takes four bytes off the front of a slice and
reads them as an ASCII decimal number. It fails with `BadTime` (0x19) when
the slice is shorter than four bytes or a byte is not a digit; four digits
can't overflow, so its `Overflow` path never runs.
-/

namespace C3.RV32

open C3.Image

abbrev TD4 : Word := BitVec.ofNat 32 timeDigits4Address

section
set_option maxRecDepth 20000
theorem td4_at_0 : fetchRel timeDigits4Code 0x0 = some (.load .lw a4 a1 0x4, 2) := by decide
theorem td4_at_2 : fetchRel timeDigits4Code 0x2 = some (.aluImm .add a2 x0 0x3, 2) := by decide
theorem td4_at_4 : fetchRel timeDigits4Code 0x4 = some (.branch .bgeu a2 a4 0x52, 4) := by decide
theorem td4_at_22 : fetchRel timeDigits4Code 0x22 = some (.branch .beq a4 x0 0x42, 2) := by decide
theorem td4_at_30 : fetchRel timeDigits4Code 0x30 = some (.branch .bltu a3 a6 0x26, 4) := by decide
theorem td4_at_38 : fetchRel timeDigits4Code 0x38 = some (.branch .bne a3 x0 0x1A, 2) := by decide
theorem td4_at_50 : fetchRel timeDigits4Code 0x50 = some (.branch .beq a1 x0 0xFFFFFFD2, 2) := by decide
theorem td4_at_56 : fetchRel timeDigits4Code 0x56 = some (.aluImm .add a1 x0 0x19, 2) := by decide
theorem td4_at_58 : fetchRel timeDigits4Code 0x58 = some (.store .sb a0 a1 0x1, 4) := by decide
theorem td4_at_5c : fetchRel timeDigits4Code 0x5C = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem td4_at_5e : fetchRel timeDigits4Code 0x5E = some (.store .sb a0 a1 0x0, 4) := by decide
theorem td4_at_62 : fetchRel timeDigits4Code 0x62 = some (.jalr x0 ra 0x0, 2) := by decide
theorem td4_at_64 : fetchRel timeDigits4Code 0x64 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem td4_at_66 : fetchRel timeDigits4Code 0x66 = some (.store .sw a0 a2 0x4, 2) := by decide
theorem td4_at_68 : fetchRel timeDigits4Code 0x68 = some (.jal x0 0xFFFFFFF6, 2) := by decide
end

def td4A : List BInstr :=
  [.aluImm .add a2 x0 0x0, .lw a5 a1 0x0, .aluImm .add a6 a4 0xFFFFFFFC, .aluImm .add a4 x0 0x4,
    .aluImm .add a3 a5 0x4, .sw a1 a3 0x0, .sw a1 a6 0x4, .aluImm .add a6 x0 0xF6,
    .aluImm .add (17 : Fin 32) x0 0xA]
def td4Y1 : List BInstr :=
  [.lbu a1 a5 0x0, .aluImm .add a3 a1 0xFFFFFFC6, .aluImm .and a3 a3 0xFF]
def td4Y2 : List BInstr :=
  [.alu .mulhu a3 a2 (17 : Fin 32)]
def td4Y3 : List BInstr :=
  [.alu .mul a3 a2 (17 : Fin 32), .aluImm .add a1 a1 0xFFFFFFD0, .aluImm .and a2 a1 0xFF, .alu .add a2 a2 a3,
    .alu .sltu a1 a2 a3, .aluImm .add a5 a5 0x1, .aluImm .add a4 a4 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem td4A_end : blockEnd timeDigits4Code 0x8 td4A = some 0x22 := by decide
theorem td4Y1_end : blockEnd timeDigits4Code 0x24 td4Y1 = some 0x30 := by decide
theorem td4Y2_end : blockEnd timeDigits4Code 0x34 td4Y2 = some 0x38 := by decide
theorem td4Y3_end : blockEnd timeDigits4Code 0x3A td4Y3 = some 0x50 := by decide
end

theorem readDigits_succ_mem (M : Word → BitVec 8) (q : Word) (k m : Nat) :
    readDigits (k + 1) (memBytes M q (m + 1)) =
      if 48 ≤ (M q).toNat ∧ (M q).toNat ≤ 57 then
        (readDigits k (memBytes M (q + 1) m)).map fun vr => (((M q).toNat - 48) * 10 ^ k + vr.1, vr.2)
      else none := by
  rw [memBytes_succ]
  simp only [readDigits, require, bind, Option.bind, pure]
  by_cases h : 48 ≤ (M q).toNat ∧ (M q).toNat ≤ 57
  · have e : (48 ≤ (M q).toNat && (M q).toNat ≤ 57) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact h
    rw [if_pos h]
    simp only [e, ↓reduceIte]
    rcases readDigits k (memBytes M (q + 1) m) with _ | ⟨v, r⟩ <;> rfl
  · have e : (48 ≤ (M q).toNat && (M q).toNat ≤ 57) = false := Bool.eq_false_iff.mpr fun he => h (by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at he; exact he)
    rw [if_neg h]
    simp only [e, Bool.false_eq_true, ↓reduceIte]

theorem readDigits_short (k : Nat) (l : Bytes) (h : l.length < k) : readDigits k l = none := by
  induction k generalizing l with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      simp only [readDigits, require, bind, Option.bind, pure]
      rw [ih l (by simp at h; omega)]
      split <;> rfl

theorem readDigits_append (k : Nat) (l r : Bytes) (h : k ≤ l.length) :
    readDigits k (l ++ r) = (readDigits k l).map fun vr => (vr.1, vr.2 ++ r) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    cases l with
    | nil => exact absurd h (by simp)
    | cons b l =>
      simp only [List.cons_append, readDigits, require, bind, Option.bind, pure]
      rw [ih l (by simp at h; omega)]
      by_cases hb : (decide (48 ≤ b) && decide (b ≤ 57)) = true
      · simp only [hb, ↓reduceIte]
        rcases readDigits k l with _ | ⟨v, r'⟩ <;> rfl
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        rfl

theorem readDigits_rest (M : Word → BitVec 8) : ∀ k (q : Word) (m v : Nat) (r : Bytes), k ≤ m →
    readDigits k (memBytes M q m) = some (v, r) → r = memBytes M (q + BitVec.ofNat 32 k) (m - k) ∧ v < 10 ^ k := by
  intro k
  induction k with
  | zero =>
    intro q m v r _ h
    simp only [readDigits] at h; cases h
    exact ⟨by rw [add_ofNat_zero, Nat.sub_zero], by decide⟩
  | succ k ih =>
    intro q m v r hm h
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [readDigits_succ_mem] at h
    split at h
    · rename_i hd
      cases hk : readDigits k (memBytes M (q + 1) m') with
      | none => rw [hk] at h; cases h
      | some vr =>
        rw [hk] at h
        obtain ⟨v', r'⟩ := vr
        simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hv, hr⟩ := h
        obtain ⟨e1, e2⟩ := ih (q + 1) m' v' r' (by omega) hk
        refine ⟨by rw [← hr, e1, show q + 1 + BitVec.ofNat 32 k = q + BitVec.ofNat 32 (k + 1) by
          rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc, Nat.add_comm]]; congr 1; omega, ?_⟩
        rw [← hv, Nat.pow_succ]
        have : (M q).toNat - 48 ≤ 9 := by omega
        calc ((M q).toNat - 48) * 10 ^ k + v' < ((M q).toNat - 48) * 10 ^ k + 10 ^ k := by omega
          _ = ((M q).toNat - 48 + 1) * 10 ^ k := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ 10 * 10 ^ k := Nat.mul_le_mul_right _ (by omega)
          _ = 10 ^ k * 10 := Nat.mul_comm _ _
    · cases h

/-- `readDigits 4` of `n ≥ 4` bytes at `p` reads the first four and leaves
the rest. -/
theorem readDigits4_mem (M : Word → BitVec 8) (p : Word) {n : Nat} (hn : 4 ≤ n) :
    readDigits 4 (memBytes M p n) =
      (readDigits 4 (memBytes M p 4)).map fun vr => (vr.1, memBytes M (p + 4) (n - 4)) := by
  rw [show n = 4 + (n - 4) by omega, memBytes_split, readDigits_append 4 _ _ (by rw [memBytes_length]; exact Nat.le_refl 4),
    show 4 + (n - 4) - 4 = n - 4 by omega]
  cases h : readDigits 4 (memBytes M p 4) with
  | none => rfl
  | some vr =>
    obtain ⟨v, r⟩ := vr
    have := (readDigits_rest M 4 p 4 v r (by decide) h).1
    rw [this, Nat.sub_self, memBytes_zero]; rfl

/-- What `digits::<4>` leaves in memory, with its `Result<u32, Error>` at
`out` and the slice `(p, n)` at `d`. -/
def digits4Mem (M : Word → BitVec 8) (out d p : Word) (n : Nat) : Word → BitVec 8 :=
  if n < 4 then memStore8 (memStore8 M (out + 1) 0x19) out 1
  else match readDigits 4 (memBytes M p 4) with
    | some (v, _) => memStore8 (memStore32 (memStore32 (memStore32 M d (p + 4)) (d + 4) (BitVec.ofNat 32 (n - 4)))
        (out + 4) (BitVec.ofNat 32 v)) out 0
    | none => memStore8 (memStore8 (memStore32 (memStore32 M d (p + 4)) (d + 4) (BitVec.ofNat 32 (n - 4)))
        (out + 1) 0x19) out 1

theorem add_one_ne (a : Word) : a + 1 ≠ a := fun e => by
  have e2 := congrArg BitVec.toNat e
  rw [BitVec.toNat_add] at e2
  have hlt := a.isLt
  change (a.toNat + 1) % 2 ^ 32 = a.toNat at e2
  rcases Nat.lt_or_ge (a.toNat + 1) (2 ^ 32) with h | h
  · rw [Nat.mod_eq_of_lt h] at e2; omega
  · rw [show a.toNat + 1 = 2 ^ 32 by omega, Nat.mod_self] at e2; omega

theorem digits4Mem_frame {M : Word → BitVec 8} {out d p x : Word} {n : Nat} (ho : Sep out 8 x 1)
    (hd : Sep d 8 x 1) : digits4Mem M out d p n x = M x := by
  have x0 : x ≠ out := fun e => ho 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e])
  have x1 : x ≠ out + 1 := fun e => ho 1 (by decide) 0 (by decide) (by rw [add_ofNat_zero, e]; rfl)
  have h4 : Sep (out + 4) 4 x 1 := ho.sub (c := 4) (l := 4) (by decide)
  have hd0 : Sep d 4 x 1 := by have := hd.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have hd4 : Sep (d + 4) 4 x 1 := hd.sub (c := 4) (l := 4) (by decide)
  unfold digits4Mem
  by_cases h : n < 4
  · rw [if_pos h, memStore8_ne x0, memStore8_ne x1]
  · rw [if_neg h]
    rcases readDigits 4 (memBytes M p 4) with _ | ⟨v, r⟩ <;> dsimp only
    · rw [memStore8_ne x0, memStore8_ne x1, memStore32_get_sep hd4, memStore32_get_sep hd0]
    · rw [memStore8_ne x0, memStore32_get_sep h4, memStore32_get_sep hd4, memStore32_get_sep hd0]

theorem digits4Mem_err {M : Word → BitVec 8} {out d p : Word} {n : Nat}
    (h : n < 4 ∨ readDigits 4 (memBytes M p 4) = none) :
    digits4Mem M out d p n out = 1 ∧ digits4Mem M out d p n (out + 1) = 0x19 := by
  have o1 := add_one_ne out
  unfold digits4Mem
  by_cases hn : n < 4
  · rw [if_pos hn]
    exact ⟨memStore8_same _ _ _, by rw [memStore8_ne o1, memStore8_same]⟩
  · rw [if_neg hn, h.resolve_left hn]
    dsimp only
    exact ⟨memStore8_same _ _ _, by rw [memStore8_ne o1, memStore8_same]⟩

theorem digits4Mem_ok {M : Word → BitVec 8} {out d p : Word} {n v : Nat} {r : Bytes} (h4 : 4 ≤ n)
    (hR : readDigits 4 (memBytes M p 4) = some (v, r)) (sOD : Sep out 8 d 8) :
    digits4Mem M out d p n out = 0 ∧ memLoad32 (digits4Mem M out d p n) (out + 4) = BitVec.ofNat 32 v ∧
      memLoad32 (digits4Mem M out d p n) d = p + 4 ∧
      memLoad32 (digits4Mem M out d p n) (d + 4) = BitVec.ofNat 32 (n - 4) := by
  have s0 : Sep out 1 (out + 4) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 4) (k := 4) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have sd0 : Sep out 1 d 4 := by
    have := sOD.sub (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this
    have := (this.symm.sub (c := 0) (l := 4) (by decide)).symm; rwa [add_ofNat_zero] at this
  have sd4 : Sep out 1 (d + 4) 4 := by
    have := sOD.sub (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this
    exact (this.symm.sub (c := 4) (l := 4) (by decide)).symm
  have s4d : Sep (out + 4) 4 d 4 := by
    have := ((sOD.sub (c := 4) (l := 4) (by decide)).symm.sub (c := 0) (l := 4) (by decide)).symm
    rwa [add_ofNat_zero] at this
  have s4d4 : Sep (out + 4) 4 (d + 4) 4 := ((sOD.sub (c := 4) (l := 4) (by decide)).symm.sub (c := 4) (l := 4) (by decide)).symm
  have dd : Sep (d + 4) 4 d 4 := by
    have := sep_offsets d (c := 4) (n := 4) (d := 0) (k := 4) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  unfold digits4Mem
  rw [if_neg (by omega), hR]
  refine ⟨memStore8_same _ _ _, ?_, ?_, ?_⟩
  · rw [memLoad32_store8_sep s0, memLoad32_store32_same]
  · rw [memLoad32_store8_sep sd0, memLoad32_store32_sep s4d, memLoad32_store32_sep dd, memLoad32_store32_same]
  · rw [memLoad32_store8_sep sd4, memLoad32_store32_sep s4d4, memLoad32_store32_same]

/-- The registers `digits::<4>` leaves alone. -/
def td4Keep (q : Fin 32) : Bool := q.val ∉ [11, 12, 13, 14, 15, 16, 17]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The loop from 0x22: on to 0x64 with the number in `a2`, or to the
`BadTime` exit at 0x56. -/
theorem td4_loop {M : Word → BitVec 8} {base : Word} (hc : CodeIn M base timeDigits4Code) : ∀ k, k ≤ 4 →
    ∀ {nn : Machine} {acc m : Nat} {q : Word}, St M base nn 0x22 (reg nn) → reg nn a4 = BitVec.ofNat 32 k →
    reg nn a5 = q → reg nn a2 = BitVec.ofNat 32 acc → acc < 10 ^ (4 - k) → reg nn a6 = 0xF6 →
    reg nn (17 : Fin 32) = BitVec.ofNat 32 10 → k ≤ m →
    (readDigits k (memBytes M q m) = none → ∃ nn', Steps nn nn' ∧ St M base nn' 0x56 (reg nn') ∧
      ∀ r, r.val ∉ [11, 12, 13, 14, 15] → reg nn' r = reg nn r) ∧
    (∀ v rest, readDigits k (memBytes M q m) = some (v, rest) → ∃ nn', Steps nn nn' ∧ St M base nn' 0x64 (reg nn') ∧
      reg nn' a2 = BitVec.ofNat 32 (acc * 10 ^ k + v) ∧ ∀ r, r.val ∉ [11, 12, 13, 14, 15] → reg nn' r = reg nn r) := by
  intro k
  induction k with
  | zero =>
    intro _ nn acc m q st r14 r15 r12 hacc r16 r17 _
    obtain ⟨n1, d1, u1⟩ := st.taken hc 0x64 td4_at_22 (by decide) (by rw [r14, st.zero]; rfl)
    refine ⟨fun h => (by simp only [readDigits] at h; cases h), fun v rest h => ?_⟩
    simp only [readDigits] at h; cases h
    exact ⟨n1, .single d1, u1.self, by rw [u1.regs, r12, Nat.pow_zero, Nat.mul_one, Nat.add_zero], fun r _ => u1.regs r⟩
  | succ k ih =>
    intro hk nn acc m q st r14 r15 r12 hacc r16 r17 hm
    have hz := st.zero
    have hk0 : (BitVec.ofNat 32 (k + 1) == (0 : Word)) = false := beq_eq_false_iff_ne.mpr fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this; omega
    obtain ⟨n1, d1, u1⟩ := st.notTaken hc 0x24 td4_at_22 (by decide) (by
      rw [r14, hz]; exact hk0)
    obtain ⟨n2, c2, u2⟩ := St.block td4Y1 u1.self hc td4Y1_end (by simp only [BlockOk, BInstr.ok, td4Y1, and_self])
    have R2 : ∀ r, reg n2 r = (runBlock td4Y1 (M, reg n1)).2 r := u2.regs
    have u2' : St M base n2 0x30 (reg n2) := ⟨u2.pc, by rw [u2.mem]; rfl, fun _ => rfl⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hspec := readDigits_succ_mem M q k m'
    have v2a3 : reg n2 a3 = aluEval .and (aluEval .add ((M q).zeroExtend 32) 0xFFFFFFC6) 0xFF := by
      rw [R2]; simp +decide only [runBlock, BInstr.run, td4Y1, upd_app, ↓reduceIte]; rw [u1.regs, r15, add_lit_zero]
    have v2a1 : reg n2 a1 = (M q).zeroExtend 32 := by
      rw [R2]; simp +decide only [runBlock, BInstr.run, td4Y1, upd_app, ↓reduceIte]; rw [u1.regs, r15, add_lit_zero]
    have K2 : ∀ r, r.val ∉ [11, 13] → reg n2 r = reg nn r := fun r hr => by
      have hd : r ∉ td4Y1.filterMap BInstr.dst := by
        simp only [td4Y1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
        revert hr; revert r; decide
      rw [R2, runBlock_reg _ _ _ r u1.self.zero hd, u1.regs]
    by_cases hd : 48 ≤ (M q).toNat ∧ (M q).toNat ≤ 57
    · have hdig : isDigit (M q) = true := decide_eq_true hd
      obtain ⟨n3, d3, u3⟩ := u2'.notTaken hc 0x34 td4_at_30 (by decide) (by
        rw [v2a3, K2 _ (by decide), r16, td_digit, hdig]; rfl)
      obtain ⟨n4, c4, u4⟩ := St.block td4Y2 u3.self hc td4Y2_end (by simp only [BlockOk, BInstr.ok, td4Y2, and_self])
      have R4 : ∀ r, reg n4 r = (runBlock td4Y2 (M, reg n3)).2 r := u4.regs
      have u4' : St M base n4 0x38 (reg n4) := ⟨u4.pc, by rw [u4.mem]; rfl, fun _ => rfl⟩
      have hacc' : acc < 10 ^ (4 - (k + 1)) := hacc
      have h10 : acc < 10000 :=
        Nat.lt_of_lt_of_le hacc' (show 10 ^ (4 - (k + 1)) ≤ 10 ^ 4 from Nat.pow_le_pow_right (by decide) (by omega))
      have v4a3 : reg n4 a3 = 0 := by
        rw [R4]; simp +decide only [runBlock, BInstr.run, td4Y2, upd_app, ↓reduceIte]
        simp only [u3.regs]; rw [K2 a2 (by decide), K2 17 (by decide), r12, r17, dn_mulhuN _ _ (by omega) (by decide)]
        rw [Nat.div_eq_of_lt (show acc * 10 < 4294967296 by omega)]; rfl
      obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc 0x3A td4_at_38 (by decide) (by rw [v4a3, u4'.zero]; rfl)
      obtain ⟨n6, c6, u6⟩ := St.block td4Y3 u5.self hc td4Y3_end (by simp only [BlockOk, BInstr.ok, td4Y3, and_self])
      have R6 : ∀ r, reg n6 r = (runBlock td4Y3 (M, reg n5)).2 r := u6.regs
      have u6' : St M base n6 0x50 (reg n6) := ⟨u6.pc, by rw [u6.mem]; rfl, fun _ => rfl⟩
      have r12_5 : reg n5 a2 = BitVec.ofNat 32 acc := by
        rw [u5.regs, R4, runBlock_reg _ _ _ _ u3.self.zero (by decide), u3.regs, K2 _ (by decide), r12]
      have r17_5 : reg n5 (17 : Fin 32) = BitVec.ofNat 32 10 := by
        rw [u5.regs, R4, runBlock_reg _ _ _ _ u3.self.zero (by decide), u3.regs, K2 _ (by decide), r17]
      have r11_5 : reg n5 a1 = (M q).zeroExtend 32 := by
        rw [u5.regs, R4, runBlock_reg _ _ _ _ u3.self.zero (by decide), u3.regs, v2a1]
      have r15_5 : reg n5 a5 = q := by
        rw [u5.regs, R4, runBlock_reg _ _ _ _ u3.self.zero (by decide), u3.regs, K2 _ (by decide), r15]
      have r14_5 : reg n5 a4 = BitVec.ofNat 32 (k + 1) := by
        rw [u5.regs, R4, runBlock_reg _ _ _ _ u3.self.zero (by decide), u3.regs, K2 _ (by decide), r14]
      have hdv : (M q).toNat - 48 < 10 := by omega
      have v6a2 : reg n6 a2 = BitVec.ofNat 32 (acc * 10 + ((M q).toNat - 48)) := by
        rw [R6]; simp +decide only [runBlock, BInstr.run, td4Y3, upd_app, ↓reduceIte]
        rw [r12_5, r17_5, r11_5, td_val _ hdig, dn_mulN, dn_addN]
        exact dn_ofNat_congr (by omega)
      have v6a1 : reg n6 a1 = 0 := by
        rw [R6]; simp +decide only [runBlock, BInstr.run, td4Y3, upd_app, ↓reduceIte]
        rw [r12_5, r17_5, r11_5, td_val _ hdig, dn_mulN, dn_addN, dn_sltuN _ _ (by omega) (by omega),
          show acc * 10 % 4294967296 = acc * 10 from Nat.mod_eq_of_lt (by omega),
          show ((M q).toNat - 48 + acc * 10) % 4294967296 = (M q).toNat - 48 + acc * 10 from Nat.mod_eq_of_lt (by omega),
          if_neg (by omega)]; rfl
      have v6a5 : reg n6 a5 = q + 1 := by
        rw [R6]; simp +decide only [runBlock, BInstr.run, td4Y3, upd_app, ↓reduceIte]; rw [r15_5]; rfl
      have v6a4 : reg n6 a4 = BitVec.ofNat 32 k := by
        rw [R6]; simp +decide only [runBlock, BInstr.run, td4Y3, upd_app, ↓reduceIte]; rw [r14_5]
        exact BitVec.eq_of_toNat_eq (by
          rw [dn_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (4294967295 : Word).toNat = 4294967295
            from rfl]; omega)
      have K6 : ∀ r, r.val ∉ [11, 12, 13, 14, 15] → reg n6 r = reg nn r := fun r hr => by
        have hd6 : r ∉ td4Y3.filterMap BInstr.dst := by
          simp only [td4Y3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
          revert hr; revert r; decide
        have hd4 : r ∉ td4Y2.filterMap BInstr.dst := by
          simp only [td4Y2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
          revert hr; revert r; decide
        rw [R6, runBlock_reg _ _ _ r u5.self.zero hd6, u5.regs, R4, runBlock_reg _ _ _ r u3.self.zero hd4, u3.regs,
          K2 r (by revert hr; revert r; decide)]
      obtain ⟨n7, d7, u7⟩ := u6'.taken hc 0x22 td4_at_50 (by decide) (by rw [v6a1, u6'.zero]; rfl)
      have pre : Steps nn n7 :=
        .cons d1 (c2.trans (.cons d3 (c4.trans (.cons d5 (c6.trans (.single d7))))))
      have hacc2 : acc * 10 + ((M q).toNat - 48) < 10 ^ (4 - k) := by
        have e : 10 ^ (4 - k) = 10 ^ (4 - (k + 1)) * 10 := by
          rw [← Nat.pow_succ]; congr 1; omega
        calc acc * 10 + ((M q).toNat - 48) < (acc + 1) * 10 := by omega
          _ ≤ 10 ^ (4 - (k + 1)) * 10 := Nat.mul_le_mul_right _ hacc'
          _ = 10 ^ (4 - k) := e.symm
      obtain ⟨ihN, ihS⟩ := ih (by omega) u7.self (by rw [u7.regs, v6a4]) (by rw [u7.regs, v6a5])
        (by rw [u7.regs, v6a2]) hacc2 (by rw [u7.regs, K6 _ (by decide), r16])
        (by rw [u7.regs, K6 _ (by decide), r17]) (m := m') (by omega)
      rw [if_pos hd] at hspec
      refine ⟨fun h => ?_, fun v rest h => ?_⟩
      · rw [hspec] at h
        cases hk' : readDigits k (memBytes M (q + 1) m') with
        | some vr => rw [hk'] at h; cases h
        | none =>
          obtain ⟨nf, cf, uf, Kf⟩ := ihN hk'
          exact ⟨nf, pre.trans cf, uf, fun r hr => by rw [Kf r hr, u7.regs, K6 r hr]⟩
      · rw [hspec] at h
        cases hk' : readDigits k (memBytes M (q + 1) m') with
        | none => rw [hk'] at h; cases h
        | some vr =>
          rw [hk'] at h
          obtain ⟨v', r'⟩ := vr
          simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hv, _⟩ := h
          obtain ⟨nf, cf, uf, sf, Kf⟩ := ihS v' r' hk'
          refine ⟨nf, pre.trans cf, uf, ?_, fun r hr => by rw [Kf r hr, u7.regs, K6 r hr]⟩
          rw [sf, ← hv, Nat.pow_succ, Nat.add_mul, Nat.add_assoc, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ k)]
    · have hdig : isDigit (M q) = false := decide_eq_false hd
      obtain ⟨n3, d3, u3⟩ := u2'.taken hc 0x56 td4_at_30 (by decide) (by
        rw [v2a3, K2 _ (by decide), r16, td_digit, hdig]; rfl)
      rw [if_neg hd] at hspec
      exact ⟨fun _ => ⟨n3, .cons d1 (c2.trans (.single d3)), u3.self, fun r hr => by
        rw [u3.regs, K2 r (by revert hr; revert r; decide)]⟩,
        fun v rest h => by rw [hspec] at h; cases h⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The compiled `time::digits::<4>`**: with the slice `(p, n)` in the
reader at `d` and the result at `out`, it leaves `digits4Mem` in memory. -/
theorem timeDigits4_correct (m : Machine) {base retAddr out d p : Word} {n : Nat} (hb : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base timeDigits4Code) (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hd : d.toNat % 4 = 0) (hout : out.toNat % 4 = 0) (hn : n < 2 ^ 32)
    (lp : memLoad32 m.mem d = p) (ln : memLoad32 m.mem (d + 4) = BitVec.ofNat 32 n)
    (sOC : Sep out 8 base timeDigits4Code.length) (sDC : Sep d 8 base timeDigits4Code.length) (sDP : Sep d 8 p 4)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = digits4Mem m.mem out d p n ∧
      ∀ q, td4Keep q = true → reg m' q = reg m q := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have o0 : Sep out 1 base timeDigits4Code.length := by
    have := sOC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
  -- the error tail, from 0x56
  have err : ∀ {Mx : Word → BitVec 8} {nn : Machine}, St Mx base nn 0x56 (reg nn) → CodeIn Mx base timeDigits4Code →
      reg nn a0 = out → (∀ q, td4Keep q = true → reg nn q = reg m q) →
      ∃ m', Steps nn m' ∧ m'.pc = retAddr ∧ m'.mem = memStore8 (memStore8 Mx (out + 1) 0x19) out 1 ∧
        ∀ q, td4Keep q = true → reg m' q = reg m q := by
    intro Mx nn st hcx r0 kk
    obtain ⟨n1, d1, u1⟩ := st.aluImm hcx td4_at_56 (off' := 0x58) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.self.sb hcx td4_at_58 (off' := 0x5C) (by decide)
    rw [u1.regs a0, upd_ne' (by decide) st.zero, r0, u1.regs a1] at u2
    simp +decide only [upd_app, ↓reduceIte] at u2
    have hc2 := CodeIn.store8 (v := (aluEval .add (reg nn x0) 0x19).extractLsb' 0 8) hcx (sOC.sub (c := 1) (l := 1) (by decide))
    obtain ⟨n3, d3, u3⟩ := u2.aluImm hc2 td4_at_5c (off' := 0x5E) (by decide)
    obtain ⟨n4, d4, u4⟩ := u3.self.sb hc2 td4_at_5e (off' := 0x62) (by decide)
    rw [u3.regs a0, upd_ne' (by decide) u2.zero, u1.regs a0, upd_ne' (by decide) st.zero, r0, add_lit_zero,
      u3.regs a1] at u4
    simp +decide only [upd_app, ↓reduceIte] at u4
    have hc4 := CodeIn.store8 (v := (aluEval .add (upd (reg nn) a1 (aluEval .add (reg nn x0) 0x19) x0) 1).extractLsb' 0 8)
      hc2 o0
    obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.jalr hc4 td4_at_62
    refine ⟨n5, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5)))), ?_, ?_, fun q hq => ?_⟩
    · rw [pc5, add_lit_zero, u3.regs, upd_ne' (by decide) u2.zero, u1.regs, upd_ne' (by decide) st.zero,
        kk ra (by decide), hra, hret]
    · rw [mem5, st.zero]; rfl
    · have h11 : q ≠ a1 := fun e => by subst e; revert hq; decide
      rw [regs5, u3.regs, upd_ne' h11 u2.zero, u1.regs, upd_ne' h11 st.zero]; exact kk q hq
  obtain ⟨n1, d1, u1⟩ := s0.lw hc td4_at_0 (off' := 2) (by decide) (by rw [ha1]; exact aligned_add hd (k := 4) (by decide))
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hc td4_at_2 (off' := 4) (by decide)
  have v24 : reg n2 a4 = BitVec.ofNat 32 n := by
    rw [u2.regs, upd_ne' (by decide) u1.self.zero, u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha1, ln]
  have v22 : reg n2 a2 = 3 := by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u1.self.zero]; rfl
  have k2 : ∀ q, q ≠ a4 → q ≠ a2 → reg n2 q = reg m q := fun q h4 h2 => by
    rw [u2.regs, upd_ne' h2 u1.self.zero, u1.regs, upd_ne' h4 hz]
  have kk2 : ∀ q, td4Keep q = true → reg n2 q = reg m q := fun q hq =>
    k2 q (fun e => by subst e; revert hq; decide) (fun e => by subst e; revert hq; decide)
  by_cases hn4 : n < 4
  · obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x56 td4_at_4 (by decide) (by
      rw [v22, v24]; show (!decide ((3 : Word).toNat < (BitVec.ofNat 32 n).toNat)) = true
      rw [ofNat_tn hn, show (3 : Word).toNat = 3 from rfl, decide_eq_false (by omega)]; rfl)
    obtain ⟨m', c', h1, h2, h3⟩ := err u3.self hc (by rw [u3.regs, k2 a0 (by decide) (by decide), ha0])
      (fun q hq => by rw [u3.regs]; exact kk2 q hq)
    exact ⟨m', .cons d1 (.cons d2 (.cons d3 c')), h1, by rw [h2, digits4Mem, if_pos hn4], h3⟩
  obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0x8 td4_at_4 (by decide) (by
    rw [v22, v24]; show (!decide ((3 : Word).toNat < (BitVec.ofNat 32 n).toNat)) = false
    rw [ofNat_tn hn, show (3 : Word).toNat = 3 from rfl, decide_eq_true (by omega)]; rfl)
  have r3 : ∀ q, reg n3 q = reg n2 q := u3.regs
  have e1 : reg n3 a1 = d := by rw [r3, k2 a1 (by decide) (by decide), ha1]
  have e4 : reg n3 a4 = BitVec.ofNat 32 n := by rw [r3, v24]
  have hsub : BitVec.ofNat 32 n + 0xFFFFFFFC = BitVec.ofNat 32 (n - 4) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFC : Word).toNat = 4294967292 from rfl]
    omega
  obtain ⟨n4, c4, u4⟩ := St.block td4A u3.self hc td4A_end (by
    simp +decide only [BlockOk, BInstr.ok, td4A, BInstr.run, upd_app, ↓reduceIte, and_true, true_and]
    rw [e1, add_lit_zero]
    exact ⟨hd, ⟨hd, sDC.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h⟩,
      aligned_add hd (k := 4) (by decide), sDC.sub (c := 4) (l := 4) (by decide)⟩)
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 m.mem d (p + 4)) (d + 4) (BitVec.ofNat 32 (n - 4)) = M1 :=
    ⟨_, rfl⟩
  have m4 : (runBlock td4A (m.mem, reg n3)).1 = M1 := by
    simp +decide only [runBlock, td4A, BInstr.run, upd_app, ↓reduceIte]
    rw [e1, add_lit_zero, e4, ← hM1]
    show memStore32 (memStore32 m.mem d (memLoad32 m.mem d + 4)) _ (BitVec.ofNat 32 n + 4294967292) = _
    rw [lp, hsub]
  have R4 : ∀ r, reg n4 r = (runBlock td4A (m.mem, reg n3)).2 r := u4.regs
  have u4' : St M1 base n4 0x22 (reg n4) := ⟨u4.pc, by rw [u4.mem, m4], fun _ => rfl⟩
  have hc4 : CodeIn M1 base timeDigits4Code := by
    rw [← hM1]
    exact CodeIn.store32 (CodeIn.store32 hc (sDC.sub (c := 0) (l := 4) (by decide) |> fun h => by
      rwa [add_ofNat_zero] at h)) (sDC.sub (c := 4) (l := 4) (by decide))
  have K4 : ∀ r, r.val ∉ [12, 13, 14, 15, 16, 17] → reg n4 r = reg n3 r := fun r hr => by
    have hd4 : r ∉ td4A.filterMap BInstr.dst := by
      simp only [td4A, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hr; revert r; decide
    rw [R4, runBlock_reg _ _ _ r u3.self.zero hd4]
  have sD0 : Sep d 4 p 4 := by have := sDP.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have M1p : ∀ i, i < 4 → M1 (p + BitVec.ofNat 32 i) = m.mem (p + BitVec.ofNat 32 i) := fun i hi => by
    rw [← hM1, memStore32_get_sep (a := d + 4) (sDP.sub (c := 4) (l := 4) (by decide) |>.subR (c := i) (l := 1) (by omega)),
      memStore32_get_sep (a := d) (sD0.subR (c := i) (l := 1) (by omega))]
  have hmb : memBytes M1 p 4 = memBytes m.mem p 4 := memBytes_eq_of M1p
  obtain ⟨LN, LS⟩ := td4_loop hc4 4 (by decide) (acc := 0) (m := 4) (q := p) u4'
    (by rw [R4]; simp +decide only [runBlock, td4A, BInstr.run, upd_app, ↓reduceIte])
    (by rw [R4]; simp +decide only [runBlock, td4A, BInstr.run, upd_app, ↓reduceIte]; rw [e1, add_lit_zero, lp])
    (by rw [R4]; simp +decide only [runBlock, td4A, BInstr.run, upd_app, ↓reduceIte]; rw [u3.self.zero]; rfl)
    (by decide)
    (by rw [R4]; simp +decide only [runBlock, td4A, BInstr.run, upd_app, ↓reduceIte])
    (by rw [R4]; simp +decide only [runBlock, td4A, BInstr.run, upd_app, ↓reduceIte])
    (by decide)
  rw [hmb] at LN LS
  have kk4 : ∀ r, td4Keep r = true → reg n4 r = reg m r := fun r hr => by
    rw [K4 r (by revert hr; revert r; decide), r3]; exact kk2 r hr
  have S4 : Steps m n4 := .cons d1 (.cons d2 (.cons d3 c4))
  cases hR : readDigits 4 (memBytes m.mem p 4) with
  | none =>
    obtain ⟨n5, c5, u5, K5⟩ := LN hR
    obtain ⟨m', c', h1, h2, h3⟩ := err u5 hc4
      (by rw [K5 a0 (by decide), K4 a0 (by decide), r3, k2 a0 (by decide) (by decide), ha0])
      (fun q hq => by
        rw [K5 q (by revert hq; revert q; decide)]; exact kk4 q hq)
    refine ⟨m', S4.trans (c5.trans c'), h1, ?_, h3⟩
    rw [h2, digits4Mem, if_neg hn4, hR, ← hM1]
  | some vr =>
    obtain ⟨v, rest⟩ := vr
    obtain ⟨n5, c5, u5, v5, K5⟩ := LS v rest hR
    have r50 : reg n5 a0 = out := by rw [K5 a0 (by decide), K4 a0 (by decide), r3, k2 a0 (by decide) (by decide), ha0]
    obtain ⟨n6, d6, u6⟩ := u5.aluImm hc4 td4_at_64 (off' := 0x66) (by decide)
    obtain ⟨n7, d7, u7⟩ := u6.self.sw hc4 td4_at_66 (off' := 0x68) (by decide) (by
      rw [u6.regs, upd_ne' (by decide) u5.zero, r50]; exact aligned_add hout (k := 4) (by decide))
    rw [u6.regs a0, upd_ne' (by decide) u5.zero, r50, u6.regs a2, upd_ne' (by decide) u5.zero, v5, Nat.zero_mul,
      Nat.zero_add] at u7
    have hc7 := CodeIn.store32 (a := out + 4) (v := BitVec.ofNat 32 v) hc4 (sOC.sub (c := 4) (l := 4) (by decide))
    obtain ⟨n8, d8, u8⟩ := u7.jump hc7 td4_at_68 (off' := 0x5E) (by decide) (by
      rw [u7.pc, show base + BitVec.ofNat 32 0x68 + 0xFFFFFFF6 = base + BitVec.ofNat 32 0x5E by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at base hb 0x5E (by decide)))
    obtain ⟨n9, d9, u9⟩ := u8.sb hc7 td4_at_5e (off' := 0x62) (by decide)
    rw [u6.regs a0, upd_ne' (by decide) u5.zero, r50, add_lit_zero, u6.regs a1] at u9
    simp +decide only [upd_app, ↓reduceIte] at u9
    have hc9 := CodeIn.store8 (v := (aluEval .add (reg n5 x0) 0).extractLsb' 0 8) hc7 o0
    obtain ⟨n10, d10, pc10, mem10, regs10⟩ := u9.jalr hc9 td4_at_62
    refine ⟨n10, S4.trans (c5.trans (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.single d10)))))), ?_, ?_,
      fun q hq => ?_⟩
    · rw [pc10, add_lit_zero, u6.regs, upd_ne' (by decide) u5.zero, K5 ra (by decide), kk4 ra (by decide), hra, hret]
    · rw [mem10, u5.zero, digits4Mem, if_neg hn4, hR, ← hM1]; rfl
    · have h11 : q ≠ a1 := fun e => by subst e; revert hq; decide
      rw [regs10, u6.regs, upd_ne' h11 u5.zero, K5 q (by revert hq; revert q; decide)]; exact kk4 q hq

end C3.RV32
