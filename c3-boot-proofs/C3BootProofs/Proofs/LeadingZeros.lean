import C3BootProofs.Proofs.Ashldi3

/-!
# `UintRef::leading_zeros`, as compiled

`crypto_bigint`'s constant-time `leading_zeros` walks the limbs from the most
significant, counts each limb's leading zeros with `Limb::leading_zeros`'s
binary search, and adds them while every limb so far has been zero.
-/

namespace C3.RV32

open C3.Image

/-- The leading zero bits of a 32-bit word. -/
def lz32 (x : Nat) : Nat := if x = 0 then 32 else 31 - Nat.log2 x

/-- One step of the constant-time binary search: shift left by `s` when the
top `s` bits are zero, and count them. -/
def lzStep (s : Nat) (st : Nat × Nat) : Nat × Nat :=
  if st.1 < 2 ^ (32 - s) then (st.1 * 2 ^ s, st.2 + s) else st

/-- `Limb::leading_zeros`: steps of 16, 8, 4, 2, and 1 bits, then one more
for a word that is still zero. -/
def lzSearch (x : Nat) : Nat :=
  let st := lzStep 1 (lzStep 2 (lzStep 4 (lzStep 8 (lzStep 16 (x, 0)))))
  st.2 + if st.1 = 0 then 1 else 0

theorem lzStep_spec {s c : Nat} {st : Nat × Nat} (hs : 0 < s) (hc : c < 2 * s) (hc31 : c ≤ 31) (hs32 : s ≤ 31)
    (h1 : 2 ^ (31 - c) ≤ st.1) (h2 : st.1 < 2 ^ (32 - c)) :
    ∃ c', c' < s ∧ 2 ^ (31 - c') ≤ (lzStep s st).1 ∧ (lzStep s st).1 < 2 ^ (32 - c') ∧
      (lzStep s st).2 + c' = st.2 + c := by
  unfold lzStep
  by_cases hsc : s ≤ c
  · have hlt : st.1 < 2 ^ (32 - s) := Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega))
    rw [ite_eq_left hlt]
    refine ⟨c - s, by omega, ?_, ?_, by dsimp only; omega⟩
    · dsimp only
      rw [show 31 - (c - s) = (31 - c) + s by omega, Nat.pow_add]; exact Nat.mul_le_mul_right _ h1
    · dsimp only
      rw [show 32 - (c - s) = (32 - c) + s by omega, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos s)
  · have hge : ¬ st.1 < 2 ^ (32 - s) :=
      Nat.not_lt.mpr (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) h1)
    rw [ite_eq_right hge]
    exact ⟨c, by omega, h1, h2, rfl⟩

theorem lzSearch_eq (x : Nat) (hx : x < 2 ^ 32) : lzSearch x = lz32 x := by
  by_cases h0 : x = 0
  · subst h0; decide
  have hL : Nat.log2 x < 32 := (Nat.log2_lt h0).mpr hx
  have h1 : 2 ^ (31 - (31 - Nat.log2 x)) ≤ (x, 0).1 := by
    rw [show 31 - (31 - Nat.log2 x) = Nat.log2 x by omega]; exact Nat.log2_self_le h0
  have h2 : (x, 0).1 < 2 ^ (32 - (31 - Nat.log2 x)) := by
    rw [show 32 - (31 - Nat.log2 x) = Nat.log2 x + 1 by omega]; exact Nat.lt_log2_self
  obtain ⟨c1, hc1, a1, b1, e1⟩ := lzStep_spec (s := 16) (by decide) (by omega) (by omega) (by decide) h1 h2
  obtain ⟨c2, hc2, a2, b2, e2⟩ := lzStep_spec (s := 8) (by decide) (by omega) (by omega) (by decide) a1 b1
  obtain ⟨c3, hc3, a3, b3, e3⟩ := lzStep_spec (s := 4) (by decide) (by omega) (by omega) (by decide) a2 b2
  obtain ⟨c4, hc4, a4, b4, e4⟩ := lzStep_spec (s := 2) (by decide) (by omega) (by omega) (by decide) a3 b3
  obtain ⟨c5, hc5, a5, b5, e5⟩ := lzStep_spec (s := 1) (by decide) (by omega) (by omega) (by decide) a4 b4
  have hc0 : c5 = 0 := by omega
  subst hc0
  have hne : (lzStep 1 (lzStep 2 (lzStep 4 (lzStep 8 (lzStep 16 (x, 0)))))).1 ≠ 0 := by
    have : (1 : Nat) ≤ 2 ^ 31 := Nat.one_le_two_pow
    omega
  unfold lzSearch lz32
  dsimp only
  rw [ite_eq_right hne, ite_eq_right h0]
  dsimp only at e1
  omega


/-- The leading zero bits of the `n` little-endian 32-bit limbs at `p`. -/
def lzLimbs (M : Word → BitVec 8) (p : Word) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    if (memLoad32 M (p + BitVec.ofNat 32 (4 * k))).toNat = 0 then 32 + lzLimbs M p k
    else lz32 (memLoad32 M (p + BitVec.ofNat 32 (4 * k))).toNat

theorem lz_and_ones (w : Word) : w &&& 0xFFFFFFFF = w := by
  have hb : ∀ i : Fin 32, (0xFFFFFFFF : Word).getLsbD i.val = true := by decide
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, hb ⟨i, hi⟩, Bool.and_true]

theorem lz_and0 (w : Word) : w &&& (0 : Word) = 0 := BitVec.and_zero
theorem lz_0and (w : Word) : (0 : Word) &&& w = 0 := BitVec.zero_and
theorem lz_xor0 (w : Word) : w ^^^ (0 : Word) = w := BitVec.xor_zero

theorem lz_ones_and (w : Word) : 0xFFFFFFFF &&& w = w := by rw [BitVec.and_comm, lz_and_ones]

/-- One pass of `Limb::leading_zeros`'s loop on the word `x` with the shift
`s`, as the compiled code computes it. -/
theorem lz_word (x : Word) {s : Nat} (hs1 : 1 ≤ s) (hs : s ≤ 16) :
    (aluEval .xor x (aluEval .and (aluEval .xor (aluEval .sll x (BitVec.ofNat 32 s)) x)
        (aluEval .sub 0 (((aluEval .sltu (aluEval .srl x (aluEval .sub 0 (BitVec.ofNat 32 s))) 1).extractLsb' 0 8).zeroExtend 32)))).toNat =
      (lzStep s (x.toNat, 0)).1 ∧
    (aluEval .and (aluEval .sub 0 (((aluEval .sltu (aluEval .srl x (aluEval .sub 0 (BitVec.ofNat 32 s))) 1).extractLsb' 0 8).zeroExtend 32))
      (BitVec.ofNat 32 s)).toNat = (lzStep s (x.toNat, 0)).2 := by
  have hsn : (BitVec.ofNat 32 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
  have hneg : (aluEval .sub 0 (BitVec.ofNat 32 s)).toNat % 32 = 32 - s := by
    show (0 - BitVec.ofNat 32 s).toNat % 32 = 32 - s
    rw [BitVec.toNat_sub, hsn]
    show (2 ^ 32 - s + 0) % 2 ^ 32 % 32 = 32 - s; omega
  have hsrl : (aluEval .srl x (aluEval .sub 0 (BitVec.ofNat 32 s))).toNat = x.toNat / 2 ^ (32 - s) := by
    rw [srl_mod, hneg]
  have hx := x.isLt
  unfold lzStep
  dsimp only
  by_cases hlt : x.toNat < 2 ^ (32 - s)
  · have hc : aluEval .sltu (aluEval .srl x (aluEval .sub 0 (BitVec.ofNat 32 s))) 1 = 1 := by
      show (if BitVec.ult _ 1 then 1 else 0) = _
      rw [ite_eq_left]
      rw [BitVec.ult, decide_eq_true_eq, hsrl, show (1 : Word).toNat = 1 from rfl]
      exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by omega)
    rw [hc, ite_eq_left hlt]
    have hm : aluEval .sub 0 (((1 : Word).extractLsb' 0 8).zeroExtend 32) = 0xFFFFFFFF := by decide
    rw [hm]
    refine ⟨?_, ?_⟩
    · show (x ^^^ (((x <<< ((BitVec.ofNat 32 s).toNat % 32)) ^^^ x) &&& 0xFFFFFFFF)).toNat = _
      rw [lz_and_ones, BitVec.xor_comm (x <<< _) x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor,
        BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hsn, Nat.mod_eq_of_lt (by omega : s < 32)]
      apply Nat.mod_eq_of_lt
      calc x.toNat * 2 ^ s < 2 ^ (32 - s) * 2 ^ s := Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos s)
        _ = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
    · show ((0xFFFFFFFF : Word) &&& BitVec.ofNat 32 s).toNat = _
      rw [lz_ones_and, hsn]; omega
  · have hc : aluEval .sltu (aluEval .srl x (aluEval .sub 0 (BitVec.ofNat 32 s))) 1 = 0 := by
      show (if BitVec.ult _ 1 then 1 else 0) = _
      rw [ite_eq_right]
      rw [BitVec.ult, decide_eq_true_eq, hsrl, show (1 : Word).toNat = 1 from rfl]
      intro h
      have := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mp h
      omega
    rw [hc, ite_eq_right hlt]
    have hm : aluEval .sub 0 (((0 : Word).extractLsb' 0 8).zeroExtend 32) = 0 := by decide
    rw [hm]
    refine ⟨?_, ?_⟩
    · show (x ^^^ (((x <<< ((BitVec.ofNat 32 s).toNat % 32)) ^^^ x) &&& 0)).toNat = _
      rw [lz_and0, lz_xor0]
    · show ((0 : Word) &&& BitVec.ofNat 32 s).toNat = _
      rw [lz_0and]; rfl


theorem lzStep_acc (s x acc : Nat) : lzStep s (x, acc) = ((lzStep s (x, 0)).1, acc + (lzStep s (x, 0)).2) := by
  unfold lzStep; dsimp only; split <;> simp

theorem lzStep_lt {s x : Nat} (hs : s ≤ 32) (hx : x < 2 ^ 32) : (lzStep s (x, 0)).1 < 2 ^ 32 := by
  unfold lzStep; dsimp only
  split
  · rename_i h
    calc x * 2 ^ s < 2 ^ (32 - s) * 2 ^ s := Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos s)
      _ = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  · exact hx

theorem lzStep_snd {s x : Nat} : (lzStep s (x, 0)).2 ≤ s := by
  unfold lzStep; dsimp only; split <;> simp

section
set_option maxRecDepth 20000
theorem lz_at_0 : fetchRel leadingZerosCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem lz_at_2 : fetchRel leadingZerosCode 0x2 = some (.store .sw sp (8 : Fin 32) 0x1C, 2) := by decide
theorem lz_at_4 : fetchRel leadingZerosCode 0x4 = some (.alu .add (7 : Fin 32) x0 a0, 2) := by decide
theorem lz_at_6 : fetchRel leadingZerosCode 0x6 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem lz_at_8 : fetchRel leadingZerosCode 0x8 = some (.aluImm .add (28 : Fin 32) x0 0x1, 2) := by decide
theorem lz_at_a : fetchRel leadingZerosCode 0xA = some (.aluImm .add a6 sp 0x10, 4) := by decide
theorem lz_at_e : fetchRel leadingZerosCode 0xE = some (.aluImm .add (17 : Fin 32) sp 0x19, 4) := by decide
theorem lz_at_12 : fetchRel leadingZerosCode 0x12 = some (.aluImm .add (5 : Fin 32) sp 0x1B, 4) := by decide
theorem lz_at_16 : fetchRel leadingZerosCode 0x16 = some (.aluImm .add (6 : Fin 32) sp 0xC, 4) := by decide
theorem lz_at_1a : fetchRel leadingZerosCode 0x1A = some (.aluImm .add (30 : Fin 32) sp 0x14, 4) := by decide
theorem lz_at_1e : fetchRel leadingZerosCode 0x1E = some (.aluImm .add (31 : Fin 32) sp 0x1A, 4) := by decide
theorem lz_at_22 : fetchRel leadingZerosCode 0x22 = some (.branch .beq a1 x0 0x78, 2) := by decide
theorem lz_at_24 : fetchRel leadingZerosCode 0x24 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem lz_at_26 : fetchRel leadingZerosCode 0x26 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem lz_at_28 : fetchRel leadingZerosCode 0x28 = some (.aluImm .sll a3 a1 0x2, 4) := by decide
theorem lz_at_2c : fetchRel leadingZerosCode 0x2C = some (.alu .add a3 a3 (7 : Fin 32), 2) := by decide
theorem lz_at_2e : fetchRel leadingZerosCode 0x2E = some (.load .lw (29 : Fin 32) a3 0x0, 4) := by decide
theorem lz_at_32 : fetchRel leadingZerosCode 0x32 = some (.aluImm .add a3 x0 0x10, 2) := by decide
theorem lz_at_34 : fetchRel leadingZerosCode 0x34 = some (.alu .add a4 x0 (29 : Fin 32), 2) := by decide
theorem lz_at_36 : fetchRel leadingZerosCode 0x36 = some (.branch .beq a3 x0 0x30, 2) := by decide
theorem lz_at_38 : fetchRel leadingZerosCode 0x38 = some (.alu .sub a5 x0 a3, 4) := by decide
theorem lz_at_3c : fetchRel leadingZerosCode 0x3C = some (.alu .srl a5 a4 a5, 4) := by decide
theorem lz_at_40 : fetchRel leadingZerosCode 0x40 = some (.store .sw sp a5 0x14, 2) := by decide
theorem lz_at_42 : fetchRel leadingZerosCode 0x42 = some (.load .lw a5 sp 0x14, 2) := by decide
theorem lz_at_44 : fetchRel leadingZerosCode 0x44 = some (.aluImm .sltu a5 a5 0x1, 4) := by decide
theorem lz_at_48 : fetchRel leadingZerosCode 0x48 = some (.store .sb sp a5 0x1A, 4) := by decide
theorem lz_at_4c : fetchRel leadingZerosCode 0x4C = some (.load .lbu a5 sp 0x1A, 4) := by decide
theorem lz_at_50 : fetchRel leadingZerosCode 0x50 = some (.alu .sll (8 : Fin 32) a4 a3, 4) := by decide
theorem lz_at_54 : fetchRel leadingZerosCode 0x54 = some (.alu .xor (8 : Fin 32) (8 : Fin 32) a4, 2) := by decide
theorem lz_at_56 : fetchRel leadingZerosCode 0x56 = some (.alu .sub a5 x0 a5, 4) := by decide
theorem lz_at_5a : fetchRel leadingZerosCode 0x5A = some (.alu .and (8 : Fin 32) (8 : Fin 32) a5, 2) := by decide
theorem lz_at_5c : fetchRel leadingZerosCode 0x5C = some (.alu .and a5 a5 a3, 2) := by decide
theorem lz_at_5e : fetchRel leadingZerosCode 0x5E = some (.alu .xor a4 a4 (8 : Fin 32), 2) := by decide
theorem lz_at_60 : fetchRel leadingZerosCode 0x60 = some (.alu .add a2 a2 a5, 2) := by decide
theorem lz_at_62 : fetchRel leadingZerosCode 0x62 = some (.aluImm .srl a3 a3 0x1, 2) := by decide
theorem lz_at_64 : fetchRel leadingZerosCode 0x64 = some (.branch .bne a3 x0 0xFFFFFFD4, 2) := by decide
theorem lz_at_66 : fetchRel leadingZerosCode 0x66 = some (.store .sw sp a4 0x10, 2) := by decide
theorem lz_at_68 : fetchRel leadingZerosCode 0x68 = some (.load .lw a3 sp 0x10, 2) := by decide
theorem lz_at_6a : fetchRel leadingZerosCode 0x6A = some (.aluImm .sltu a3 a3 0x1, 4) := by decide
theorem lz_at_6e : fetchRel leadingZerosCode 0x6E = some (.store .sb sp a3 0x19, 4) := by decide
theorem lz_at_72 : fetchRel leadingZerosCode 0x72 = some (.store .sb sp (28 : Fin 32) 0x1B, 4) := by decide
theorem lz_at_76 : fetchRel leadingZerosCode 0x76 = some (.load .lbu a3 sp 0x19, 4) := by decide
theorem lz_at_7a : fetchRel leadingZerosCode 0x7A = some (.store .sw sp (29 : Fin 32) 0xC, 2) := by decide
theorem lz_at_7c : fetchRel leadingZerosCode 0x7C = some (.load .lbu a4 sp 0x1B, 4) := by decide
theorem lz_at_80 : fetchRel leadingZerosCode 0x80 = some (.load .lw a5 sp 0xC, 2) := by decide
theorem lz_at_82 : fetchRel leadingZerosCode 0x82 = some (.aluImm .and a3 a3 0x1, 2) := by decide
theorem lz_at_84 : fetchRel leadingZerosCode 0x84 = some (.alu .add a2 a2 a3, 2) := by decide
theorem lz_at_86 : fetchRel leadingZerosCode 0x86 = some (.alu .sub a3 x0 a4, 4) := by decide
theorem lz_at_8a : fetchRel leadingZerosCode 0x8A = some (.alu .sltu a4 x0 a5, 4) := by decide
theorem lz_at_8e : fetchRel leadingZerosCode 0x8E = some (.alu .and a2 a2 a3, 2) := by decide
theorem lz_at_90 : fetchRel leadingZerosCode 0x90 = some (.aluImm .add a4 a4 0xFFFFFFFF, 2) := by decide
theorem lz_at_92 : fetchRel leadingZerosCode 0x92 = some (.alu .add a0 a0 a2, 2) := by decide
theorem lz_at_94 : fetchRel leadingZerosCode 0x94 = some (.alu .and (28 : Fin 32) a4 (28 : Fin 32), 4) := by decide
theorem lz_at_98 : fetchRel leadingZerosCode 0x98 = some (.branch .bne a1 x0 0xFFFFFF8C, 2) := by decide
theorem lz_at_9a : fetchRel leadingZerosCode 0x9A = some (.load .lw (8 : Fin 32) sp 0x1C, 2) := by decide
theorem lz_at_9c : fetchRel leadingZerosCode 0x9C = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem lz_at_9e : fetchRel leadingZerosCode 0x9E = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- One pass of `Limb::leading_zeros`'s loop, from 0x38 to the branch at 0x64. -/
def lzInner : List BInstr :=
  [.alu .sub a5 x0 a3, .alu .srl a5 a4 a5, .sw sp a5 0x14, .lw a5 sp 0x14, .aluImm .sltu a5 a5 1,
   .sb sp a5 0x1A, .lbu a5 sp 0x1A, .alu .sll (8 : Fin 32) a4 a3, .alu .xor (8 : Fin 32) (8 : Fin 32) a4,
   .alu .sub a5 x0 a5, .alu .and (8 : Fin 32) (8 : Fin 32) a5, .alu .and a5 a5 a3, .alu .xor a4 a4 (8 : Fin 32),
   .alu .add a2 a2 a5, .aluImm .srl a3 a3 1]

section
set_option maxRecDepth 20000
theorem lzInner_end : blockEnd leadingZerosCode 0x38 lzInner = some 0x64 := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- One pass of the binary search, with the shift `s` in `a3`, the word in
`a4`, and the count in `a2`. It writes only the 8 bytes at `F + 0x14`. -/
theorem lz_inner {M : Word → BitVec 8} {P F : Word} {nm : Machine} {s acc2 : Nat} {x : Word}
    (hs1 : 1 ≤ s) (hs : s ≤ 16) (st : St M P nm 0x38 (reg nm))
    (hc : CodeIn M P leadingZerosCode) (rsp : reg nm sp = F) (hFa : F.toNat % 4 = 0)
    (sC : Sep (F + 0x14) 8 P leadingZerosCode.length)
    (ra3 : reg nm a3 = BitVec.ofNat 32 s) (ra4 : reg nm a4 = x) (ra2 : reg nm a2 = BitVec.ofNat 32 acc2) :
    ∃ M' n', Steps nm n' ∧ St M' P n' 0x64 (reg n') ∧ CodeIn M' P leadingZerosCode ∧
      (∀ y, Sep (F + 0x14) 8 y 1 → M' y = M y) ∧
      reg n' a3 = BitVec.ofNat 32 (s / 2) ∧ reg n' a4 = BitVec.ofNat 32 (lzStep s (x.toNat, 0)).1 ∧
      reg n' a2 = BitVec.ofNat 32 (acc2 + (lzStep s (x.toNat, 0)).2) ∧ reg n' sp = F ∧
      ∀ r, r.val ≠ 0 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → reg n' r = reg nm r := by
  have s14 : Sep (F + 0x14) 4 P leadingZerosCode.length := by
    have := sC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have s1A : Sep (F + 0x1A) 1 P leadingZerosCode.length := by
    have := sC.sub (c := 6) (l := 1) (by decide)
    rwa [show F + 0x14 + BitVec.ofNat 32 6 = F + 0x1A by rw [BitVec.add_assoc]; rfl] at this
  obtain ⟨n1, c1, u1⟩ := St.block lzInner st hc lzInner_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lzInner, upd_app, ↓reduceIte, and_true, true_and]
    rw [rsp]; exact ⟨⟨aligned_add hFa (k := 0x14) (by decide), s14⟩, aligned_add hFa (k := 0x14) (by decide), s1A⟩)
  simp only [runBlock, BInstr.run, lzInner] at u1
  simp +decide only [upd_app, ↓reduceIte] at u1
  rw [rsp, ra3, ra4, ra2, memLoad32_store32_same, st.zero, memStore8_same] at u1
  have hsn : (BitVec.ofNat 32 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
  obtain ⟨hw1, hw2⟩ := lz_word x hs1 hs
  refine ⟨_, n1, c1, u1.self, CodeIn.store8 (CodeIn.store32 hc s14) s1A, fun y hy => ?_, ?_, ?_, ?_, ?_,
    fun r h0 h2 h3 h4 h5 h8 => ?_⟩
  · have h4 : Sep (F + 0x14) 4 y 1 := by
      have := hy.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [memStore8_ne fun e => hy.point (i := 6) (j := 0) (by decide) (by decide) (by
        rw [add_ofNat_zero, show F + 0x14 + BitVec.ofNat 32 6 = F + 0x1A by rw [BitVec.add_assoc]; rfl]; exact e.symm),
      memStore32_get_sep h4]
  · rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [srl_mod, hsn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s / 2 < 2 ^ 32)]; rfl
  · rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [hw1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lzStep_lt (by omega) x.isLt)]
  · rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 acc2 + _).toNat = _
    rw [BitVec.toNat_add, hw2, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_add_mod]
  · rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; exact rsp
  · rw [u1.regs]
    simp only [upd_app, h0, h2, h3, h4, h5, h8, ite_false]

/-- The rest of one limb, from 0x66 to the branch at 0x98: the count of a
word still zero after the search, and the sum under the all-zero flag. -/
def lzTail : List BInstr :=
  [.sw sp a4 0x10, .lw a3 sp 0x10, .aluImm .sltu a3 a3 1, .sb sp a3 0x19, .sb sp (28 : Fin 32) 0x1B,
   .lbu a3 sp 0x19, .sw sp (29 : Fin 32) 0xC, .lbu a4 sp 0x1B, .lw a5 sp 0xC, .aluImm .and a3 a3 1,
   .alu .add a2 a2 a3, .alu .sub a3 x0 a4, .alu .sltu a4 x0 a5, .alu .and a2 a2 a3,
   .aluImm .add a4 a4 0xFFFFFFFF, .alu .add a0 a0 a2, .alu .and (28 : Fin 32) a4 (28 : Fin 32)]

section
set_option maxRecDepth 20000
theorem lzTail_end : blockEnd leadingZerosCode 0x66 lzTail = some 0x98 := by decide
end

theorem lz_isz (w : Word) :
    aluEval .and (((aluEval .sltu w 1).extractLsb' 0 8).zeroExtend 32) 1 = if w = 0 then 1 else 0 := by
  by_cases h : w = 0
  · subst h; decide
  · have : aluEval .sltu w 1 = 0 := by
      show (if BitVec.ult w 1 then 1 else 0) = _
      rw [ite_eq_right]
      rw [BitVec.ult, decide_eq_true_eq, show (1 : Word).toNat = 1 from rfl]
      intro hl; exact h (BitVec.eq_of_toNat_eq (by rw [show (0 : Word).toNat = 0 from rfl]; omega))
    rw [this, ite_eq_right h]; decide

theorem lz_nz (w : Word) : aluEval .add (aluEval .sltu 0 w) 0xFFFFFFFF = if w = 0 then 0xFFFFFFFF else 0 := by
  by_cases h : w = 0
  · subst h; decide
  · have : aluEval .sltu 0 w = 1 := by
      show (if BitVec.ult 0 w then 1 else 0) = _
      rw [ite_eq_left]
      rw [BitVec.ult, decide_eq_true_eq, show (0 : Word).toNat = 0 from rfl]
      exact Nat.pos_of_ne_zero fun h0 => h (BitVec.eq_of_toNat_eq h0)
    rw [this, ite_eq_right h]; decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The rest of one limb, with the searched word in `a4`, its count in `a2`,
the limb in `t4`, the all-zero flag in `t3`, and the sum in `a0`. It writes
only the 16 bytes at `F + 0xC`. -/
theorem lz_tail {M : Word → BitVec 8} {P F : Word} {nm : Machine} {flag : Nat} (hf : flag ≤ 1)
    (st : St M P nm 0x66 (reg nm)) (hc : CodeIn M P leadingZerosCode) (rsp : reg nm sp = F) (hFa : F.toNat % 4 = 0)
    (sC : Sep (F + 0xC) 16 P leadingZerosCode.length) (r28 : reg nm 28 = BitVec.ofNat 32 flag) :
    ∃ M' n', Steps nm n' ∧ St M' P n' 0x98 (reg n') ∧ CodeIn M' P leadingZerosCode ∧
      (∀ y, Sep (F + 0xC) 16 y 1 → M' y = M y) ∧
      reg n' a0 = reg nm a0 + (if flag = 1 then reg nm a2 + (if reg nm a4 = 0 then 1 else 0) else 0) ∧
      reg n' 28 = (if flag = 1 ∧ reg nm 29 = 0 then 1 else 0) ∧ reg n' sp = F ∧
      ∀ r, r.val ≠ 0 → r ≠ a0 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 28 → reg n' r = reg nm r := by
  have sk : ∀ c l, c + l ≤ 16 → Sep (F + 0xC + BitVec.ofNat 32 c) l P leadingZerosCode.length := fun c l h =>
    sC.sub (by omega)
  have e : ∀ c, F + 0xC + BitVec.ofNat 32 c = F + BitVec.ofNat 32 (0xC + c) := fun c => by
    rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, add_ofNat_assoc]
  have sc : ∀ c l, 0xC ≤ c → c + l ≤ 0x1C → Sep (F + BitVec.ofNat 32 c) l P leadingZerosCode.length := fun c l h1 h2 => by
    have := sk (c - 0xC) l (by omega); rwa [e, show 0xC + (c - 0xC) = c by omega] at this
  have ne : ∀ i j, 0xC ≤ i → i < 0x1C → 0xC ≤ j → j < 0x1C → i ≠ j → F + BitVec.ofNat 32 i ≠ F + BitVec.ofNat 32 j :=
    fun i j hi1 hi2 hj1 hj2 hij h => by
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
      omega
  obtain ⟨n1, c1, u1⟩ := St.block lzTail st hc lzTail_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lzTail, upd_app, ↓reduceIte, and_true, true_and]
    rw [rsp]
    exact ⟨⟨aligned_add hFa (k := 0x10) (by decide), sc 0x10 4 (by decide) (by decide)⟩,
      aligned_add hFa (k := 0x10) (by decide), sc 0x19 1 (by decide) (by decide), sc 0x1B 1 (by decide) (by decide),
      ⟨aligned_add hFa (k := 0xC) (by decide), sc 0xC 4 (by decide) (by decide)⟩,
      aligned_add hFa (k := 0xC) (by decide)⟩)
  simp only [runBlock, BInstr.run, lzTail] at u1
  simp +decide only [upd_app, ↓reduceIte] at u1
  rw [rsp, memLoad32_store32_same, memLoad32_store32_same] at u1
  have n2527 : F + 0x19 ≠ F + 0x1B := ne 0x19 0x1B (by decide) (by decide) (by decide) (by decide) (by decide)
  have s27 : Sep (F + 0xC) 4 (F + 0x1B) 1 :=
    sep_offsets F (c := 0xC) (n := 4) (d := 0x1B) (k := 1) (.inl (by decide)) (by decide) (by decide)
  rw [memStore8_ne (x := F + 0x19) (a := F + 0x1B) n2527, memStore8_same,
    memStore32_get_sep (a := F + 0xC) (x := F + 0x1B) s27, memStore8_same] at u1
  have isz : aluEval .and (((aluEval .sltu (reg nm a4) 1).extractLsb' 0 8).zeroExtend 32) 1 =
      if reg nm a4 = 0 then 1 else 0 := lz_isz _
  have hcode : CodeIn (memStore32 (memStore8 (memStore8 (memStore32 M (F + 0x10) (reg nm a4)) (F + 0x19)
      ((aluEval .sltu (reg nm a4) 1).extractLsb' 0 8)) (F + 0x1B) ((reg nm 28).extractLsb' 0 8)) (F + 0xC) (reg nm 29))
      P leadingZerosCode :=
    CodeIn.store32 (CodeIn.store8 (CodeIn.store8 (CodeIn.store32 hc (sc 0x10 4 (by decide) (by decide)))
      (sc 0x19 1 (by decide) (by decide))) (sc 0x1B 1 (by decide) (by decide))) (sc 0xC 4 (by decide) (by decide))
  refine ⟨_, n1, c1, u1.self, hcode, fun y hy => ?_, ?_, ?_, ?_, fun r h0 ha0 h2 h3 h4 h5 h28 => ?_⟩
  · have h10 : Sep (F + 0x10) 4 y 1 := by
      have := hy.sub (c := 4) (l := 4) (by decide); rwa [e] at this
    have hC : Sep (F + 0xC) 4 y 1 := by
      have := hy.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [memStore32_get_sep hC,
      memStore8_ne fun ex => hy.point (i := 0xF) (j := 0) (by decide) (by decide) (by
        rw [add_ofNat_zero, e]; exact ex.symm),
      memStore8_ne fun ex => hy.point (i := 0xD) (j := 0) (by decide) (by decide) (by
        rw [add_ofNat_zero, e]; exact ex.symm),
      memStore32_get_sep h10]
  · rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [isz, r28]
    rcases (by omega : flag = 0 ∨ flag = 1) with rfl | rfl
    · rw [show aluEval .sub 0 (((BitVec.ofNat 32 0).extractLsb' 0 8).zeroExtend 32) = 0 by decide]
      show _ + (_ &&& (0 : Word)) = _
      rw [lz_and0]; rfl
    · rw [show aluEval .sub 0 (((BitVec.ofNat 32 1).extractLsb' 0 8).zeroExtend 32) = 0xFFFFFFFF by decide]
      show _ + (_ &&& (0xFFFFFFFF : Word)) = _
      rw [lz_and_ones]; rfl
  · rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [lz_nz, r28]
    rcases (by omega : flag = 0 ∨ flag = 1) with rfl | rfl
    · rw [ite_eq_right (fun h : 0 = 1 ∧ reg nm 29 = 0 => absurd h.1 (by decide))]
      by_cases hz : reg nm 29 = 0
      · rw [ite_eq_left hz]; decide
      · rw [ite_eq_right hz]; decide
    · by_cases hz : reg nm 29 = 0
      · rw [ite_eq_left hz, ite_eq_left ⟨rfl, hz⟩]; decide
      · rw [ite_eq_right hz, ite_eq_right fun h => hz h.2]; decide
  · rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; exact rsp
  · rw [u1.regs]
    simp only [upd_app, h0, ha0, h2, h3, h4, h5, h28, ite_false]

theorem lzStep_pair (s : Nat) (q : Nat × Nat) :
    (lzStep s (q.1, 0)).1 = (lzStep s q).1 ∧ q.2 + (lzStep s (q.1, 0)).2 = (lzStep s q).2 := by
  have h := lzStep_acc s q.1 q.2
  rw [show ((q.1, q.2) : Nat × Nat) = q from rfl] at h
  rw [h]; exact ⟨rfl, rfl⟩

theorem lzStep_snd_le (s : Nat) (q : Nat × Nat) : (lzStep s q).2 ≤ q.2 + s := by
  unfold lzStep; split <;> simp

theorem lzStep_fst_lt {s : Nat} {q : Nat × Nat} (hs : s ≤ 32) (hq : q.1 < 2 ^ 32) : (lzStep s q).1 < 2 ^ 32 := by
  rw [← (lzStep_pair s q).1]; exact lzStep_lt hs hq

/-- The instructions from 0x24 to 0x36: the next limb down, into `t4` and `a4`. -/
def lzLoad : List BInstr :=
  [.aluImm .add a2 x0 0, .aluImm .add a1 a1 0xFFFFFFFF, .aluImm .sll a3 a1 2, .alu .add a3 a3 (7 : Fin 32),
   .lw (29 : Fin 32) a3 0, .aluImm .add a3 x0 0x10, .alu .add a4 x0 (29 : Fin 32)]

section
set_option maxRecDepth 20000
theorem lzLoad_end : blockEnd leadingZerosCode 0x24 lzLoad = some 0x36 := by decide
end

theorem lz_addr (k : Nat) (p : Word) :
    aluEval .add (aluEval .sll (aluEval .add (BitVec.ofNat 32 (k + 1)) 0xFFFFFFFF) 2) p =
      p + BitVec.ofNat 32 (4 * k) := by
  have e1 : aluEval .add (BitVec.ofNat 32 (k + 1)) 0xFFFFFFFF = BitVec.ofNat 32 k := by
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
    omega
  have e2 : aluEval .sll (BitVec.ofNat 32 k) 2 = BitVec.ofNat 32 (4 * k) := by
    apply BitVec.eq_of_toNat_eq
    rw [sll_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (2 : Word).toNat % 32 = 2 from rfl]
    omega
  rw [e1, e2]; exact BitVec.add_comm _ _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- One limb of `UintRef::leading_zeros`, from 0x24 to the branch at 0x98:
with `k + 1` limbs left in `a1`, the limbs at `p` in `t2`, the all-zero flag
in `t3`, and the sum in `a0`, it adds the next limb down's leading zeros
while the flag is set, clears the flag at a nonzero limb, and leaves `k` in
`a1`. It writes only the 16 bytes at `F + 0xC`. -/
theorem lz_iter {M : Word → BitVec 8} {P F p : Word} {nm : Machine} {k flag acc : Nat} (hf : flag ≤ 1)
    (st : St M P nm 0x24 (reg nm)) (hc : CodeIn M P leadingZerosCode) (rsp : reg nm sp = F)
    (hFa : F.toNat % 4 = 0) (sC : Sep (F + 0xC) 16 P leadingZerosCode.length) (r7 : reg nm 7 = p)
    (hp : p.toNat % 4 = 0) (ra1 : reg nm a1 = BitVec.ofNat 32 (k + 1)) (r28 : reg nm 28 = BitVec.ofNat 32 flag)
    (ra0 : reg nm a0 = BitVec.ofNat 32 acc) :
    ∃ M' n', Steps nm n' ∧ St M' P n' 0x98 (reg n') ∧ CodeIn M' P leadingZerosCode ∧
      (∀ y, Sep (F + 0xC) 16 y 1 → M' y = M y) ∧ reg n' a1 = BitVec.ofNat 32 k ∧
      reg n' a0 = BitVec.ofNat 32 (acc + if flag = 1 then lz32 (memLoad32 M (p + BitVec.ofNat 32 (4 * k))).toNat
        else 0) ∧
      reg n' 28 = BitVec.ofNat 32 (if flag = 1 ∧ (memLoad32 M (p + BitVec.ofNat 32 (4 * k))).toNat = 0 then 1 else 0) ∧
      reg n' sp = F ∧ reg n' 7 = p ∧
      ∀ r, r.val ∉ [0, 8, 10, 11, 12, 13, 14, 15, 28, 29] → reg n' r = reg nm r := by
  have hz := st.zero
  have ha := lz_addr k p
  have sC14 : Sep (F + 0x14) 8 P leadingZerosCode.length := by
    have := sC.sub (c := 8) (l := 8) (by decide)
    rwa [show F + 0xC + BitVec.ofNat 32 8 = F + 0x14 by rw [BitVec.add_assoc]; rfl] at this
  obtain ⟨n1, c1, u1⟩ := St.block lzLoad st hc lzLoad_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lzLoad, upd_app, ↓reduceIte, and_true, true_and]
    rw [ra1, r7, ha, add_lit_zero]; exact aligned_add hp (by omega))
  simp only [runBlock, BInstr.run, lzLoad] at u1
  simp +decide only [upd_app, ↓reduceIte] at u1
  rw [ra1, r7, ha, add_lit_zero, hz] at u1
  obtain ⟨X, hX⟩ : ∃ X, memLoad32 M (p + BitVec.ofNat 32 (4 * k)) = X := ⟨_, rfl⟩
  rw [hX] at u1 ⊢
  have k1 : ∀ r, r.val ≠ 0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ 29 → reg n1 r = reg nm r :=
    fun r h0 h1 h2 h3 h4 h29 => by rw [u1.regs]; simp only [upd_app, h0, h1, h2, h3, h4, h29, ite_false]
  have a3_1 : reg n1 a3 = BitVec.ofNat 32 16 := by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
  have a4_1 : reg n1 a4 = X := by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; exact zw X
  have a2_1 : reg n1 a2 = BitVec.ofNat 32 0 := by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
  have a1_1 : reg n1 a1 = BitVec.ofNat 32 k := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
    omega
  have t4_1 : reg n1 29 = X := by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0x38 lz_at_36 (by decide) (by rw [a3_1, u1.self.zero]; rfl)
  -- one pass of the search, with the word and count as a pair
  have nxt : ∀ {M1 : Word → BitVec 8} {m1 : Machine} {s : Nat} {q : Nat × Nat}, 1 ≤ s → s ≤ 16 → q.2 ≤ 31 →
      q.1 < 2 ^ 32 → St M1 P m1 0x38 (reg m1) → CodeIn M1 P leadingZerosCode → reg m1 sp = F →
      reg m1 a3 = BitVec.ofNat 32 s → reg m1 a4 = BitVec.ofNat 32 q.1 → reg m1 a2 = BitVec.ofNat 32 q.2 →
      ∃ M2 m2, Steps m1 m2 ∧ St M2 P m2 0x64 (reg m2) ∧ CodeIn M2 P leadingZerosCode ∧
        (∀ y, Sep (F + 0x14) 8 y 1 → M2 y = M1 y) ∧ reg m2 a3 = BitVec.ofNat 32 (s / 2) ∧
        reg m2 a4 = BitVec.ofNat 32 (lzStep s q).1 ∧ reg m2 a2 = BitVec.ofNat 32 (lzStep s q).2 ∧ reg m2 sp = F ∧
        ∀ r, r.val ≠ 0 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → reg m2 r = reg m1 r := by
    intro M1 m1 s q h1 h16 hq2 hq1 st1 hc1 rsp1 ra3 ra4 ra2
    obtain ⟨M2, m2, c, u, hc2, fr, b3, b4, b2, bs, bk⟩ :=
      lz_inner (acc2 := q.2) (x := BitVec.ofNat 32 q.1) h1 h16 st1 hc1 rsp1 hFa sC14 ra3 ra4 ra2
    have hq : (BitVec.ofNat 32 q.1).toNat = q.1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq1]
    rw [hq, (lzStep_pair s q).1] at b4
    rw [hq, (lzStep_pair s q).2] at b2
    exact ⟨M2, m2, c, u, hc2, fr, b3, b4, b2, bs, bk⟩
  have hX32 : X.toNat < 2 ^ 32 := X.isLt
  have sp2 : reg n2 sp = F := by
    rw [u2.regs, k1 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rsp]
  have a4_2 : reg n2 a4 = BitVec.ofNat 32 X.toNat := by
    rw [u2.regs, a4_1]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hX32]
  obtain ⟨M3, n3, c3, u3, hc3, f3, b3_3, b4_3, b2_3, sp3, k3⟩ := nxt (q := (X.toNat, 0)) (s := 16) (by decide)
    (by decide) (Nat.zero_le 31) hX32 u2.self hc sp2 (by rw [u2.regs, a3_1]) a4_2 (by rw [u2.regs, a2_1])
  -- the other four passes, each after the branch back to 0x38
  have hq1 : (lzStep 16 (X.toNat, 0)).1 < 2 ^ 32 := lzStep_fst_lt (by decide) hX32
  have hq1' : (lzStep 16 (X.toNat, 0)).2 ≤ 16 := lzStep_snd_le 16 (X.toNat, 0)
  obtain ⟨n4, d4, u4⟩ := u3.taken hc3 0x38 lz_at_64 (by decide) (by rw [b3_3, u3.zero] <;> decide)
  obtain ⟨M5, n5, c5, u5, hc5, f5, b3_5, b4_5, b2_5, sp5, k5⟩ := nxt (q := lzStep 16 (X.toNat, 0)) (s := 8)
    (by decide) (by decide) (by omega) hq1 u4.self hc3 (by rw [u4.regs, sp3]) (by rw [u4.regs, b3_3] <;> rfl)
    (by rw [u4.regs, b4_3]) (by rw [u4.regs, b2_3])
  have hq2 : (lzStep 8 (lzStep 16 (X.toNat, 0))).1 < 2 ^ 32 := lzStep_fst_lt (by decide) hq1
  have hq2' : (lzStep 8 (lzStep 16 (X.toNat, 0))).2 ≤ 24 :=
    Nat.le_trans (lzStep_snd_le 8 _) (by omega)
  obtain ⟨n6, d6, u6⟩ := u5.taken hc5 0x38 lz_at_64 (by decide) (by rw [b3_5, u5.zero] <;> decide)
  obtain ⟨M7, n7, c7, u7, hc7, f7, b3_7, b4_7, b2_7, sp7, k7⟩ :=
    nxt (q := lzStep 8 (lzStep 16 (X.toNat, 0))) (s := 4)
    (by decide) (by decide) (by omega) hq2 u6.self hc5 (by rw [u6.regs, sp5]) (by rw [u6.regs, b3_5] <;> rfl)
    (by rw [u6.regs, b4_5]) (by rw [u6.regs, b2_5])
  have hq3 : (lzStep 4 (lzStep 8 (lzStep 16 (X.toNat, 0)))).1 < 2 ^ 32 := lzStep_fst_lt (by decide) hq2
  have hq3' : (lzStep 4 (lzStep 8 (lzStep 16 (X.toNat, 0)))).2 ≤ 28 :=
    Nat.le_trans (lzStep_snd_le 4 _) (by omega)
  obtain ⟨n8, d8, u8⟩ := u7.taken hc7 0x38 lz_at_64 (by decide) (by rw [b3_7, u7.zero] <;> decide)
  obtain ⟨M9, n9, c9, u9, hc9, f9, b3_9, b4_9, b2_9, sp9, k9⟩ :=
    nxt (q := lzStep 4 (lzStep 8 (lzStep 16 (X.toNat, 0)))) (s := 2)
    (by decide) (by decide) (by omega) hq3 u8.self hc7 (by rw [u8.regs, sp7]) (by rw [u8.regs, b3_7] <;> rfl)
    (by rw [u8.regs, b4_7]) (by rw [u8.regs, b2_7])
  have hq4 : (lzStep 2 (lzStep 4 (lzStep 8 (lzStep 16 (X.toNat, 0))))).1 < 2 ^ 32 := lzStep_fst_lt (by decide) hq3
  have hq4' : (lzStep 2 (lzStep 4 (lzStep 8 (lzStep 16 (X.toNat, 0))))).2 ≤ 30 :=
    Nat.le_trans (lzStep_snd_le 2 _) (by omega)
  obtain ⟨n10, d10, u10⟩ := u9.taken hc9 0x38 lz_at_64 (by decide) (by rw [b3_9, u9.zero] <;> decide)
  obtain ⟨M11, n11, c11, u11, hc11, f11, b3_11, b4_11, b2_11, sp11, k11⟩ :=
    nxt (q := lzStep 2 (lzStep 4 (lzStep 8 (lzStep 16 (X.toNat, 0))))) (s := 1)
    (by decide) (by decide) (by omega) hq4 u10.self hc9 (by rw [u10.regs, sp9]) (by rw [u10.regs, b3_9] <;> rfl)
    (by rw [u10.regs, b4_9]) (by rw [u10.regs, b2_9])
  obtain ⟨n12, d12, u12⟩ := u11.notTaken hc11 0x66 lz_at_64 (by decide) (by rw [b3_11, u11.zero] <;> decide)
  -- the inner passes keep everything the tail reads but `a2`, `a4`
  have K : ∀ r, r.val ≠ 0 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → reg n12 r = reg n2 r :=
    fun r h0 h2 h3 h4 h5 h8 => by
      rw [u12.regs, k11 r h0 h2 h3 h4 h5 h8, u10.regs, k9 r h0 h2 h3 h4 h5 h8, u8.regs, k7 r h0 h2 h3 h4 h5 h8,
        u6.regs, k5 r h0 h2 h3 h4 h5 h8, u4.regs, k3 r h0 h2 h3 h4 h5 h8]
  have K2 : ∀ r, r.val ≠ 0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → r ≠ 29 → reg n12 r = reg nm r :=
    fun r h0 h1 h2 h3 h4 h5 h8 h29 => by rw [K r h0 h2 h3 h4 h5 h8, u2.regs, k1 r h0 h1 h2 h3 h4 h29]
  obtain ⟨M13, n13, c13, u13, hc13, f13, a0_13, t3_13, sp13, k13⟩ := lz_tail hf u12.self hc11
    (by rw [u12.regs, sp11]) hFa sC
    (by rw [K2 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      r28])
  have hq5 : (lzStep 1 (lzStep 2 (lzStep 4 (lzStep 8 (lzStep 16 (X.toNat, 0)))))).1 < 2 ^ 32 :=
    lzStep_fst_lt (by decide) hq4
  have hls : lzSearch X.toNat = (lzStep 1 (lzStep 2 (lzStep 4 (lzStep 8 (lzStep 16 (X.toNat, 0)))))).2 +
      if (lzStep 1 (lzStep 2 (lzStep 4 (lzStep 8 (lzStep 16 (X.toNat, 0)))))).1 = 0 then 1 else 0 := rfl
  have a0_12 : reg n12 a0 = BitVec.ofNat 32 acc := by
    rw [K2 a0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ra0]
  have t4_12 : reg n12 29 = X := by
    rw [K 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u2.regs, t4_1]
  have a2_12 := (u12.regs a2).trans b2_11
  have a4_12 := (u12.regs a4).trans b4_11
  have hfr : ∀ y, Sep (F + 0xC) 16 y 1 → M13 y = M y := fun y hy => by
    have h8 : Sep (F + 0x14) 8 y 1 := by
      have := hy.sub (c := 8) (l := 8) (by decide)
      rwa [show F + 0xC + BitVec.ofNat 32 8 = F + 0x14 by rw [BitVec.add_assoc]; rfl] at this
    rw [f13 y hy, f11 y h8, f9 y h8, f7 y h8, f5 y h8, f3 y h8]
  refine ⟨M13, n13, c1.trans (.cons d2 (c3.trans (.cons d4 (c5.trans (.cons d6 (c7.trans (.cons d8 (c9.trans
      (.cons d10 (c11.trans (.cons d12 c13))))))))))), u13, hc13, hfr, ?_, ?_, ?_, sp13, ?_, fun r hr => ?_⟩
  · rw [k13 a1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      K a1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u2.regs, a1_1]
  · rw [a0_13, a0_12, a2_12, a4_12, ← lzSearch_eq X.toNat hX32, hls]
    have hz5 : ∀ v : Nat, v < 2 ^ 32 → (BitVec.ofNat 32 v = 0 ↔ v = 0) := fun v hv => by
      constructor
      · intro h; have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] at this; exact this
      · intro h; rw [h]; rfl
    rcases (by omega : flag = 0 ∨ flag = 1) with rfl | rfl
    · rw [ite_eq_right (by decide : ¬ (0 = 1)), ite_eq_right (by decide : ¬ (0 = 1)), Nat.add_zero]
      exact BitVec.add_zero _
    · rw [ite_eq_left rfl, ite_eq_left rfl]
      by_cases h0 : (lzStep 1 (lzStep 2 (lzStep 4 (lzStep 8 (lzStep 16 (X.toNat, 0)))))).1 = 0
      · rw [ite_eq_left ((hz5 _ hq5).mpr h0), ite_eq_left h0]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          show (1 : Word).toNat = 1 from rfl]
        omega
      · rw [ite_eq_right fun h => h0 ((hz5 _ hq5).mp h), ite_eq_right h0]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          show (0 : Word).toNat = 0 from rfl]
        omega
  · rw [t3_13, t4_12]
    have hX0 : X = 0 ↔ X.toNat = 0 := ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
    rcases (by omega : flag = 0 ∨ flag = 1) with rfl | rfl
    · rw [ite_eq_right fun h : 0 = 1 ∧ X = 0 => absurd h.1 (by decide),
        ite_eq_right fun h : 0 = 1 ∧ X.toNat = 0 => absurd h.1 (by decide)]; rfl
    · by_cases h0 : X = 0
      · rw [ite_eq_left ⟨rfl, h0⟩, ite_eq_left ⟨rfl, hX0.mp h0⟩]; rfl
      · rw [ite_eq_right fun h : 1 = 1 ∧ X = 0 => h0 h.2,
          ite_eq_right fun h : 1 = 1 ∧ X.toNat = 0 => h0 (hX0.mpr h.2)]; rfl
  · rw [k13 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      K2 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r7]
  · have h : r.val ≠ 0 ∧ r ≠ a0 ∧ r ≠ a1 ∧ r ≠ a2 ∧ r ≠ a3 ∧ r ≠ a4 ∧ r ≠ a5 ∧ r ≠ 8 ∧ r ≠ 28 ∧ r ≠ 29 := by
      revert hr; revert r; decide
    rw [k13 r h.1 h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1,
      K2 r h.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2]

/-- The instructions from 0x4 to 0x22: the limbs into `t2`, the sum and the
flag cleared and set, and the stack addresses the loop doesn't use. -/
def lzPre : List BInstr :=
  [.alu .add (7 : Fin 32) x0 a0, .aluImm .add a0 x0 0, .aluImm .add (28 : Fin 32) x0 1, .aluImm .add a6 sp 0x10,
   .aluImm .add (17 : Fin 32) sp 0x19, .aluImm .add (5 : Fin 32) sp 0x1B, .aluImm .add (6 : Fin 32) sp 0xC,
   .aluImm .add (30 : Fin 32) sp 0x14, .aluImm .add (31 : Fin 32) sp 0x1A]

section
set_option maxRecDepth 20000
theorem lzPre_end : blockEnd leadingZerosCode 0x4 lzPre = some 0x22 := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `UintRef::leading_zeros`**: with the `n` limbs at `p`, it
returns their leading zero bits. It writes only its 0x20-byte frame below
`sp0`. -/
theorem leadingZeros_correct (m : Machine) {P sp0 p retAddr : Word} {n : Nat}
    (hc : CodeIn m.mem P leadingZerosCode) (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = p)
    (ha1 : reg m a1 = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) (hp : p.toNat % 4 = 0)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp4 : sp0.toNat % 4 = 0)
    (sFC : Sep (sp0 + 0xFFFFFFE0) 0x20 P leadingZerosCode.length)
    (sLF : Sep p (4 * n) (sp0 + 0xFFFFFFE0) 0x20) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ reg m' a0 = BitVec.ofNat 32 (lzLimbs m.mem p n) ∧
      (∀ r, r.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' r = reg m r) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  rw [hF] at sFC sLF ⊢
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hsp4 (k := 0xFFFFFFE0) (by decide)
  have eS : F + 0x20 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have sFk : ∀ c l, c + l ≤ 0x20 → Sep (F + BitVec.ofNat 32 c) l P leadingZerosCode.length := fun c l h =>
    sFC.sub (by omega)
  have s1C : Sep (F + 0x1C) 4 P leadingZerosCode.length := sFk 0x1C 4 (by decide)
  have sC : Sep (F + 0xC) 16 P leadingZerosCode.length := sFk 0xC 16 (by decide)
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc lz_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨n2, d2, u2⟩ := u1.sw hc lz_at_2 (off' := 4) (by decide) (by rw [sp1]; exact aligned_add hFa (by decide))
  rw [sp1, upd_ne (by decide) (by decide)] at u2
  have hc2 := CodeIn.store32 (v := reg m 8) hc s1C
  have k1 : ∀ r, r ≠ sp → upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) r = reg m r := fun r h => updz hz h
  obtain ⟨n3, c3, u3⟩ := St.block lzPre u2.self hc2 lzPre_end (by simp [BlockOk, BInstr.ok, lzPre])
  simp only [runBlock, BInstr.run, lzPre] at u3
  have k3 : ∀ r, r.val ∉ [0, 2, 5, 6, 7, 10, 16, 17, 28, 30, 31] → reg n3 r = reg m r := fun r hr => by
    have h : r.val ≠ 0 ∧ r ≠ (31 : Fin 32) ∧ r ≠ (30 : Fin 32) ∧ r ≠ (6 : Fin 32) ∧ r ≠ (5 : Fin 32) ∧
        r ≠ (17 : Fin 32) ∧ r ≠ a6 ∧ r ≠ (28 : Fin 32) ∧ r ≠ a0 ∧ r ≠ (7 : Fin 32) ∧ r ≠ sp := by
      revert hr; revert r; decide
    rw [u3.regs, upd_ne h.1 h.2.1, upd_ne h.1 h.2.2.1, upd_ne h.1 h.2.2.2.1, upd_ne h.1 h.2.2.2.2.1,
      upd_ne h.1 h.2.2.2.2.2.1, upd_ne h.1 h.2.2.2.2.2.2.1, upd_ne h.1 h.2.2.2.2.2.2.2.1,
      upd_ne h.1 h.2.2.2.2.2.2.2.2.1, upd_ne h.1 h.2.2.2.2.2.2.2.2.2.1, u2.regs, k1 r h.2.2.2.2.2.2.2.2.2.2]
  have sp3 : reg n3 sp = F := by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.regs, sp1]
  have t2_3 : reg n3 7 = p := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.self.zero, u2.regs a0, k1 a0 (by decide), ha0]
    exact zw p
  have a0_3 : reg n3 a0 = BitVec.ofNat 32 0 := by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]
  have t3_3 : reg n3 28 = BitVec.ofNat 32 1 := by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]
  have a1_3 : reg n3 a1 = BitVec.ofNat 32 n := by rw [k3 a1 (by decide), ha1]
  obtain ⟨Ms, hMs⟩ : ∃ Ms, memStore32 m.mem (F + 0x1C) (reg m 8) = Ms := ⟨_, rfl⟩
  rw [hMs] at u3 hc2
  have frS : ∀ y, Sep F 0x20 y 1 → Ms y = m.mem y := fun y hy => by
    rw [← hMs]; exact memStore32_get_sep (hy.sub (c := 0x1C) (l := 4) (by decide))
  have slS : memLoad32 Ms (F + 0x1C) = reg m 8 := by rw [← hMs]; exact memLoad32_store32_same _ _ _
  -- the epilogue, from 0x9A
  have fin : ∀ {Mx : Word → BitVec 8} {nm : Machine}, Steps m nm → St Mx P nm 0x9A (reg nm) →
      CodeIn Mx P leadingZerosCode → memLoad32 Mx (F + 0x1C) = reg m 8 → reg nm sp = F → reg nm ra = retAddr →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = Mx ∧ reg m' sp = sp0 ∧ reg m' 8 = reg m 8 ∧
        ∀ r, r ≠ sp → r ≠ 8 → reg m' r = reg nm r := by
    intro Mx nm S st hcx hsl rsp rra
    obtain ⟨e1, f1, w1⟩ := st.lw hcx lz_at_9a (off' := 0x9C) (by decide)
      (by rw [rsp]; exact aligned_add hFa (k := 0x1C) (by decide))
    rw [rsp, hsl] at w1
    obtain ⟨e2, f2, w2⟩ := w1.aluImm hcx lz_at_9c (off' := 0x9E) (by decide)
    obtain ⟨e3, f3, pc3, mem3, regs3⟩ := w2.jalr hcx lz_at_9e
    refine ⟨e3, S.trans (.cons f1 (.cons f2 (.single f3))), ?_, mem3, ?_, ?_, fun r h1 h2 => ?_⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [rra, add_lit_zero, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp, eS]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]
    · rw [regs3]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact st.zero.symm
      simp only [upd_app, h0, h1, h2, ite_false]
  have Kr : ∀ r, r.val ∈ [1, 3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 r = reg m r := fun r hr =>
    k3 r (by revert hr; revert r; decide)
  -- one limb, from 0x24 to the branch at 0x98, with the limb read from the caller's memory
  have iterF : ∀ {Mx : Word → BitVec 8} {nm : Machine} {k acc flag : Nat}, Steps m nm → St Mx P nm 0x24 (reg nm) →
      CodeIn Mx P leadingZerosCode → (∀ y, Sep F 0x20 y 1 → Mx y = m.mem y) → memLoad32 Mx (F + 0x1C) = reg m 8 →
      reg nm sp = F → reg nm 7 = p → reg nm a1 = BitVec.ofNat 32 (k + 1) → k + 1 ≤ n →
      reg nm 28 = BitVec.ofNat 32 flag → flag ≤ 1 → reg nm a0 = BitVec.ofNat 32 acc →
      ∃ (Mx' : Word → BitVec 8) (nm' : Machine), Steps m nm' ∧ St Mx' P nm' 0x98 (reg nm') ∧
        CodeIn Mx' P leadingZerosCode ∧ (∀ y, Sep F 0x20 y 1 → Mx' y = m.mem y) ∧
        memLoad32 Mx' (F + 0x1C) = reg m 8 ∧ reg nm' sp = F ∧ reg nm' 7 = p ∧ reg nm' a1 = BitVec.ofNat 32 k ∧
        reg nm' a0 = BitVec.ofNat 32 (acc + if flag = 1 then
          lz32 (memLoad32 m.mem (p + BitVec.ofNat 32 (4 * k))).toNat else 0) ∧
        reg nm' 28 = BitVec.ofNat 32 (if flag = 1 ∧ (memLoad32 m.mem (p + BitVec.ofNat 32 (4 * k))).toNat = 0
          then 1 else 0) ∧
        ∀ r, r.val ∉ [0, 8, 10, 11, 12, 13, 14, 15, 28, 29] → reg nm' r = reg nm r := by
    intro Mx nm k acc flag S st hcx hM hsl rsp r7 ra1 hk r28 hf ra0
    obtain ⟨M', n', c, u, hc', fr, a1', a0', t3', sp', t2', keep'⟩ :=
      lz_iter hf st hcx rsp hFa sC r7 hp ra1 r28 ra0
    have eX : memLoad32 Mx (p + BitVec.ofNat 32 (4 * k)) = memLoad32 m.mem (p + BitVec.ofNat 32 (4 * k)) :=
      memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact hM _ (sLF.sub (c := 4 * k + j) (l := 1) (by omega)).symm
    rw [eX] at a0' t3'
    refine ⟨M', n', S.trans c, u, hc', fun y hy => by rw [fr y (hy.sub (c := 0xC) (l := 16) (by decide)), hM y hy],
      ?_, sp', t2', a1', a0', t3', keep'⟩
    rw [← hsl]
    exact memLoad32_congr fun j hj => fr _ (by
      rw [show F + 0x1C + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x1C + j) by rw [← add_ofNat_assoc]; rfl]
      exact sep_offsets F (c := 0xC) (n := 16) (d := 0x1C + j) (k := 1) (.inl (by omega)) (by decide) (by omega))
  have hfl : ∀ (c : Prop) [Decidable c], (if c then 1 else 0) ≤ 1 := fun c _ => by split <;> decide
  -- the loop, by induction on the limbs left after the current one
  have loop : ∀ k, ∀ {Mx : Word → BitVec 8} {nm : Machine} {acc flag : Nat}, Steps m nm →
      St Mx P nm 0x24 (reg nm) → CodeIn Mx P leadingZerosCode → (∀ y, Sep F 0x20 y 1 → Mx y = m.mem y) →
      memLoad32 Mx (F + 0x1C) = reg m 8 → reg nm sp = F → reg nm 7 = p → reg nm a1 = BitVec.ofNat 32 (k + 1) →
      k + 1 ≤ n → reg nm 28 = BitVec.ofNat 32 flag → flag ≤ 1 → reg nm a0 = BitVec.ofNat 32 acc →
      (∀ r, r.val ∈ [1, 3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nm r = reg m r) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        reg m' a0 = BitVec.ofNat 32 (acc + if flag = 1 then lzLimbs m.mem p (k + 1) else 0) ∧
        (∀ r, r.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' r = reg m r) ∧
        ∀ x, Sep F 0x20 x 1 → m'.mem x = m.mem x := by
    intro k
    induction k with
    | zero =>
      intro Mx nm acc flag S st hcx hM hsl rsp r7 ra1 hk r28 hf ra0 kr
      obtain ⟨M', n', S', u, hc', fr, sl, sp', t2', a1', a0', t3', keep'⟩ :=
        iterF S st hcx hM hsl rsp r7 ra1 hk r28 hf ra0
      obtain ⟨n'', d, u'⟩ := u.notTaken hc' 0x9A lz_at_98 (by decide) (by rw [a1', u.zero]; rfl)
      obtain ⟨mf, Sf, pcf, memf, spf, s8f, kf⟩ := fin (S'.trans (.single d)) u'.self hc' sl
        (by rw [u'.regs, sp']) (by rw [u'.regs, keep' ra (by decide), kr ra (by decide), hra])
      refine ⟨mf, Sf, pcf, spf, ?_, fun r hr => ?_, fun x hx => by rw [memf, fr x hx]⟩
      · rw [kf a0 (by decide) (by decide), u'.regs, a0']
        congr 2
        show (if flag = 1 then lz32 _ else 0) = if flag = 1 then
          (if (memLoad32 m.mem (p + BitVec.ofNat 32 (4 * 0))).toNat = 0 then 32 + 0
            else lz32 (memLoad32 m.mem (p + BitVec.ofNat 32 (4 * 0))).toNat) else 0
        by_cases h0 : (memLoad32 m.mem (p + BitVec.ofNat 32 (4 * 0))).toNat = 0
        · rw [ite_eq_left h0, h0]; rfl
        · rw [ite_eq_right h0]
      · by_cases h8 : r = 8
        · subst h8; exact s8f
        · have hs : r ≠ sp := fun e => by subst e; revert hr; decide
          rw [kf r hs h8, u'.regs, keep' r (by revert hr; revert r; decide)]
          exact kr r (by revert hr h8; revert r; decide)
    | succ k ih =>
      intro Mx nm acc flag S st hcx hM hsl rsp r7 ra1 hk r28 hf ra0 kr
      obtain ⟨M', n', S', u, hc', fr, sl, sp', t2', a1', a0', t3', keep'⟩ :=
        iterF S st hcx hM hsl rsp r7 ra1 hk r28 hf ra0
      obtain ⟨n'', d, u'⟩ := u.taken hc' 0x24 lz_at_98 (by decide) (by
        rw [a1', u.zero]
        simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact Nat.succ_ne_zero _ this)
      have e := funext u'.regs
      obtain ⟨mf, Sf, pcf, spf, a0f, kf, frf⟩ := ih (S'.trans (.single d)) u'.self hc' fr sl (by rw [e, sp'])
        (by rw [e, t2']) (by rw [e, a1']) (by omega) (by rw [e, t3']) (hfl _) (by rw [e, a0'])
        (fun r hr => by rw [e, keep' r (by revert hr; revert r; decide)]; exact kr r hr)
      refine ⟨mf, Sf, pcf, spf, ?_, kf, frf⟩
      rw [a0f]
      congr 1
      obtain ⟨X, hX⟩ : ∃ X, (memLoad32 m.mem (p + BitVec.ofNat 32 (4 * (k + 1)))).toNat = X := ⟨_, rfl⟩
      rw [hX, show lzLimbs m.mem p (k + 1 + 1) = if X = 0 then 32 + lzLimbs m.mem p (k + 1) else lz32 X by
        rw [← hX]; rfl]
      rcases (by omega : flag = 0 ∨ flag = 1) with rfl | rfl
      · rw [ite_eq_right (by decide : ¬ (0 = 1)), ite_eq_right fun h : 0 = 1 ∧ X = 0 => absurd h.1 (by decide),
          ite_eq_right (by decide : ¬ (0 = 1)), ite_eq_right (by decide : ¬ (0 = 1))]
      · by_cases h0 : X = 0
        · subst h0
          show acc + 32 + lzLimbs m.mem p (k + 1) = acc + (32 + lzLimbs m.mem p (k + 1)); omega
        · rw [ite_eq_right (fun h : 1 = 1 ∧ X = 0 => h0 h.2), ite_eq_right h0]
          show acc + lz32 X + 0 = acc + lz32 X; rfl
  by_cases hn0 : n = 0
  · subst hn0
    obtain ⟨n4, d4, u4⟩ := u3.self.taken hc2 0x9A lz_at_22 (by decide) (by rw [a1_3, u3.self.zero]; rfl)
    obtain ⟨mf, Sf, pcf, memf, spf, s8f, kf⟩ := fin (.cons d1 (.cons d2 (c3.trans (.single d4)))) u4.self hc2 slS
      (by rw [u4.regs, sp3]) (by rw [u4.regs, Kr ra (by decide), hra])
    refine ⟨mf, Sf, pcf, spf, by rw [kf a0 (by decide) (by decide), u4.regs, a0_3]; rfl, fun r hr => ?_,
      fun x hx => by rw [memf, frS x hx]⟩
    by_cases h8 : r = 8
    · subst h8; exact s8f
    · have hs : r ≠ sp := fun e => by subst e; revert hr; decide
      rw [kf r hs h8, u4.regs]; exact Kr r (by revert hr h8; revert r; decide)
  · obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hc2 0x24 lz_at_22 (by decide) (by
      rw [a1_3, u3.self.zero]; exact beq_false_of_ne fun h => by
        have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this; exact hn0 this)
    have e := funext u4.regs
    obtain ⟨mf, Sf, pcf, spf, a0f, kf, frf⟩ := loop (n - 1) (.cons d1 (.cons d2 (c3.trans (.single d4)))) u4.self hc2
      frS slS (by rw [e, sp3]) (by rw [e, t2_3]) (by rw [e, a1_3, show n - 1 + 1 = n by omega]) (by omega)
      (by rw [e, t3_3]) (by decide) (by rw [e, a0_3]) (fun r hr => by rw [e]; exact Kr r hr)
    refine ⟨mf, Sf, pcf, spf, ?_, kf, frf⟩
    rw [a0f, ite_eq_left rfl, Nat.zero_add, show n - 1 + 1 = n by omega]

end C3.RV32
