import C3BootProofs.Proofs.MontMul12Main
import C3BootProofs.Image.Bootloader

/-!
# Montgomery reduction out of P-384's Montgomery form

`montgomery_retrieve::<12>` zeroes a 12-limb accumulator on its stack, then
runs 12 passes. Pass `i` adds limb `i` of the input and `u` times the
modulus, for the `u` that zeroes the low word, and shifts the sum down a
word. The carry of each column sits in the accumulator's word below the
column until the next column reads it. The function then copies the
accumulator to the result with `memcpy`. It doesn't subtract the modulus at
the end: for an input below the modulus, the sum already is.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000

theorem mr_at_0 : fetchRel montRetrieve12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFB0, 2) := by decide
theorem mr_at_2 : fetchRel montRetrieve12Code 0x2 = some (.store .sw sp ra 0x4C, 2) := by decide
theorem mr_at_4 : fetchRel montRetrieve12Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x48, 2) := by decide
theorem mr_at_6 : fetchRel montRetrieve12Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x44, 2) := by decide
theorem mr_at_8 : fetchRel montRetrieve12Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x40, 2) := by decide
theorem mr_at_a : fetchRel montRetrieve12Code 0xA = some (.store .sw sp (19 : Fin 32) 0x3C, 2) := by decide
theorem mr_at_c : fetchRel montRetrieve12Code 0xC = some (.store .sw sp (20 : Fin 32) 0x38, 2) := by decide
theorem mr_at_e : fetchRel montRetrieve12Code 0xE = some (.store .sw sp (21 : Fin 32) 0x34, 2) := by decide
theorem mr_at_10 : fetchRel montRetrieve12Code 0x10 = some (.alu .add (20 : Fin 32) x0 a3, 2) := by decide
theorem mr_at_12 : fetchRel montRetrieve12Code 0x12 = some (.alu .add (19 : Fin 32) x0 a2, 2) := by decide
theorem mr_at_14 : fetchRel montRetrieve12Code 0x14 = some (.alu .add (21 : Fin 32) x0 a1, 2) := by decide
theorem mr_at_16 : fetchRel montRetrieve12Code 0x16 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem mr_at_18 : fetchRel montRetrieve12Code 0x18 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem mr_at_1a : fetchRel montRetrieve12Code 0x1A = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem mr_at_1e : fetchRel montRetrieve12Code 0x1E = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem mr_at_20 : fetchRel montRetrieve12Code 0x20 = some (.auipc ra 0x1000, 4) := by decide
theorem mr_at_24 : fetchRel montRetrieve12Code 0x24 = some (.jalr ra ra 0xFFFFFA10, 4) := by decide
theorem mr_at_28 : fetchRel montRetrieve12Code 0x28 = some (.aluImm .add (6 : Fin 32) x0 0x0, 2) := by decide
theorem mr_at_2a : fetchRel montRetrieve12Code 0x2A = some (.load .lw (5 : Fin 32) (19 : Fin 32) 0x0, 4) := by decide
theorem mr_at_2e : fetchRel montRetrieve12Code 0x2E = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x4, 2) := by decide
theorem mr_at_30 : fetchRel montRetrieve12Code 0x30 = some (.aluImm .add a6 sp 0x8, 4) := by decide
theorem mr_at_34 : fetchRel montRetrieve12Code 0x34 = some (.aluImm .add (17 : Fin 32) x0 0xC, 2) := by decide
theorem mr_at_36 : fetchRel montRetrieve12Code 0x36 = some (.branch .beq (17 : Fin 32) x0 0x68, 4) := by decide
theorem mr_at_3a : fetchRel montRetrieve12Code 0x3A = some (.aluImm .sll a2 (6 : Fin 32) 0x2, 4) := by decide
theorem mr_at_3e : fetchRel montRetrieve12Code 0x3E = some (.alu .add a2 a2 (21 : Fin 32), 2) := by decide
theorem mr_at_40 : fetchRel montRetrieve12Code 0x40 = some (.load .lw a3 sp 0x4, 2) := by decide
theorem mr_at_42 : fetchRel montRetrieve12Code 0x42 = some (.load .lw a2 a2 0x0, 2) := by decide
theorem mr_at_44 : fetchRel montRetrieve12Code 0x44 = some (.alu .add a2 a2 a3, 2) := by decide
theorem mr_at_46 : fetchRel montRetrieve12Code 0x46 = some (.alu .mul a4 a2 (20 : Fin 32), 4) := by decide
theorem mr_at_4a : fetchRel montRetrieve12Code 0x4A = some (.alu .mul a5 a4 (5 : Fin 32), 4) := by decide
theorem mr_at_4e : fetchRel montRetrieve12Code 0x4E = some (.alu .mulhu (9 : Fin 32) a4 (5 : Fin 32), 4) := by decide
theorem mr_at_52 : fetchRel montRetrieve12Code 0x52 = some (.alu .sltu a3 a2 a3, 4) := by decide
theorem mr_at_56 : fetchRel montRetrieve12Code 0x56 = some (.alu .add a5 a5 a2, 2) := by decide
theorem mr_at_58 : fetchRel montRetrieve12Code 0x58 = some (.alu .add a3 a3 (9 : Fin 32), 2) := by decide
theorem mr_at_5a : fetchRel montRetrieve12Code 0x5A = some (.alu .sltu a2 a5 a2, 4) := by decide
theorem mr_at_5e : fetchRel montRetrieve12Code 0x5E = some (.alu .add a2 a2 a3, 2) := by decide
theorem mr_at_60 : fetchRel montRetrieve12Code 0x60 = some (.aluImm .add a5 x0 0xB, 2) := by decide
theorem mr_at_62 : fetchRel montRetrieve12Code 0x62 = some (.store .sw sp a2 0x4, 2) := by decide
theorem mr_at_64 : fetchRel montRetrieve12Code 0x64 = some (.alu .add a2 x0 a6, 2) := by decide
theorem mr_at_66 : fetchRel montRetrieve12Code 0x66 = some (.alu .add a3 x0 (19 : Fin 32), 2) := by decide
theorem mr_at_68 : fetchRel montRetrieve12Code 0x68 = some (.branch .beq a5 x0 0x30, 2) := by decide
theorem mr_at_6a : fetchRel montRetrieve12Code 0x6A = some (.load .lw (9 : Fin 32) a3 0x0, 2) := by decide
theorem mr_at_6c : fetchRel montRetrieve12Code 0x6C = some (.alu .mul (8 : Fin 32) (9 : Fin 32) a4, 4) := by decide
theorem mr_at_70 : fetchRel montRetrieve12Code 0x70 = some (.alu .mulhu (9 : Fin 32) (9 : Fin 32) a4, 4) := by decide
theorem mr_at_74 : fetchRel montRetrieve12Code 0x74 = some (.load .lw a1 a2 0x0, 2) := by decide
theorem mr_at_76 : fetchRel montRetrieve12Code 0x76 = some (.load .lw a0 a2 0xFFFFFFFC, 4) := by decide
theorem mr_at_7a : fetchRel montRetrieve12Code 0x7A = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem mr_at_7c : fetchRel montRetrieve12Code 0x7C = some (.alu .sltu (8 : Fin 32) a1 (8 : Fin 32), 4) := by decide
theorem mr_at_80 : fetchRel montRetrieve12Code 0x80 = some (.alu .add a0 a0 a1, 2) := by decide
theorem mr_at_82 : fetchRel montRetrieve12Code 0x82 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem mr_at_84 : fetchRel montRetrieve12Code 0x84 = some (.alu .sltu a1 a0 a1, 4) := by decide
theorem mr_at_88 : fetchRel montRetrieve12Code 0x88 = some (.aluImm .add a3 a3 0x4, 2) := by decide
theorem mr_at_8a : fetchRel montRetrieve12Code 0x8A = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem mr_at_8c : fetchRel montRetrieve12Code 0x8C = some (.store .sw a2 a0 0xFFFFFFFC, 4) := by decide
theorem mr_at_90 : fetchRel montRetrieve12Code 0x90 = some (.store .sw a2 a1 0x0, 2) := by decide
theorem mr_at_92 : fetchRel montRetrieve12Code 0x92 = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem mr_at_94 : fetchRel montRetrieve12Code 0x94 = some (.aluImm .add a5 a5 0xFFFFFFFF, 2) := by decide
theorem mr_at_96 : fetchRel montRetrieve12Code 0x96 = some (.branch .bne a5 x0 0xFFFFFFD4, 2) := by decide
theorem mr_at_98 : fetchRel montRetrieve12Code 0x98 = some (.aluImm .add (6 : Fin 32) (6 : Fin 32) 0x1, 2) := by decide
theorem mr_at_9a : fetchRel montRetrieve12Code 0x9A = some (.branch .bne (6 : Fin 32) (17 : Fin 32) 0xFFFFFFA0, 4) := by decide
theorem mr_at_9e : fetchRel montRetrieve12Code 0x9E = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem mr_at_a0 : fetchRel montRetrieve12Code 0xA0 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem mr_at_a4 : fetchRel montRetrieve12Code 0xA4 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem mr_at_a6 : fetchRel montRetrieve12Code 0xA6 = some (.auipc ra 0x1000, 4) := by decide
theorem mr_at_aa : fetchRel montRetrieve12Code 0xAA = some (.jalr ra ra 0xFFFFF9F2, 4) := by decide
theorem mr_at_ae : fetchRel montRetrieve12Code 0xAE = some (.load .lw ra sp 0x4C, 2) := by decide
theorem mr_at_b0 : fetchRel montRetrieve12Code 0xB0 = some (.load .lw (8 : Fin 32) sp 0x48, 2) := by decide
theorem mr_at_b2 : fetchRel montRetrieve12Code 0xB2 = some (.load .lw (9 : Fin 32) sp 0x44, 2) := by decide
theorem mr_at_b4 : fetchRel montRetrieve12Code 0xB4 = some (.load .lw (18 : Fin 32) sp 0x40, 2) := by decide
theorem mr_at_b6 : fetchRel montRetrieve12Code 0xB6 = some (.load .lw (19 : Fin 32) sp 0x3C, 2) := by decide
theorem mr_at_b8 : fetchRel montRetrieve12Code 0xB8 = some (.load .lw (20 : Fin 32) sp 0x38, 2) := by decide
theorem mr_at_ba : fetchRel montRetrieve12Code 0xBA = some (.load .lw (21 : Fin 32) sp 0x34, 2) := by decide
theorem mr_at_bc : fetchRel montRetrieve12Code 0xBC = some (.aluImm .add sp sp 0x50, 2) := by decide
theorem mr_at_be : fetchRel montRetrieve12Code 0xBE = some (.jalr x0 ra 0x0, 2) := by decide

end

/-- One column of the reduction as the compiled code computes it, from the
modulus limb `N`, the factor `U`, the carry `Cin`, and the accumulator word
`O`: the word stored, then the carry out. -/
def mrCols (N U Cin O : Word) : Word × Word :=
  let s0 := aluEval .mul N U
  let s1 := aluEval .mulhu N U
  let a1 := aluEval .add O s0
  let c1 := aluEval .sltu a1 s0
  let a0 := aluEval .add Cin a1
  let t := aluEval .add c1 s1
  let c2 := aluEval .sltu a0 a1
  (a0, aluEval .add c2 t)

set_option maxHeartbeats 2000000 in
theorem mr_col (N U Cin O : Word) :
    (mrCols N U Cin O).1.toNat + 2 ^ 32 * (mrCols N U Cin O).2.toNat =
      O.toNat + N.toNat * U.toNat + Cin.toNat := by
  unfold mrCols
  simp only
  have e0 := mul_mulhu N U
  have e1 := add_carry O (aluEval .mul N U)
  generalize aluEval .mul N U = s0 at e0 e1 ⊢
  generalize aluEval .mulhu N U = s1 at e0 ⊢
  generalize aluEval .add O s0 = a1 at e1 ⊢
  generalize aluEval .sltu a1 s0 = c1 at e1 ⊢
  have e2 := add_carry Cin a1
  have b1 := add_toNat c1 s1
  generalize aluEval .add Cin a1 = a0 at e2 ⊢
  generalize aluEval .add c1 s1 = t at b1 ⊢
  generalize aluEval .sltu a0 a1 = c2 at e2 ⊢
  have b2 := add_toNat c2 t
  generalize aluEval .add c2 t = h at b2 ⊢
  have hN := N.isLt; have hU := U.isLt
  have P1 : N.toNat * U.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  generalize N.toNat * U.toNat = p at e0 P1 ⊢
  have := s0.isLt; have := s1.isLt; have := a1.isLt; have := c1.isLt; have := a0.isLt; have := t.isLt
  have := c2.isLt; have := h.isLt; have := O.isLt; have := Cin.isLt
  have hs1 : s1.toNat ≤ 2 ^ 32 - 2 := by omega
  have hc1 : c1.toNat ≤ 1 := by omega
  have hc2 : c2.toNat ≤ 1 := by omega
  have ht : t.toNat = c1.toNat + s1.toNat := by rw [b1]; exact Nat.mod_eq_of_lt (by omega)
  have hh : h.toNat = c2.toNat + t.toNat := by
    rw [b2]; apply Nat.mod_eq_of_lt
    have : a0.toNat + 2 ^ 32 * (c2.toNat + t.toNat) ≤ 2 ^ 64 - 1 := by omega
    omega
  rw [hh]; omega

/-- The first column of a pass, from the input limb `X`, the accumulator's
low word `B0`, the factor `K`, and the modulus's low limb `N0`: the factor
`u`, then the carry out. The column's own word is zero. -/
def mrHead (X B0 K N0 : Word) : Word × Word :=
  let s := aluEval .add X B0
  let u := aluEval .mul s K
  let lo := aluEval .mul u N0
  let hi := aluEval .mulhu u N0
  let c0 := aluEval .sltu s B0
  let w := aluEval .add lo s
  let t := aluEval .add c0 hi
  let c1 := aluEval .sltu w s
  (u, aluEval .add c1 t)

set_option maxHeartbeats 2000000 in
theorem mr_head (X B0 K N0 : Word) (hk : (K.toNat * N0.toNat + 1) % 2 ^ 32 = 0) :
    X.toNat + B0.toNat + (mrHead X B0 K N0).1.toNat * N0.toNat = 2 ^ 32 * (mrHead X B0 K N0).2.toNat := by
  unfold mrHead
  simp only
  have e1 := add_carry X B0
  have hu : (aluEval .mul (aluEval .add X B0) K).toNat = K.toNat * (aluEval .add X B0).toNat % 2 ^ 32 := by
    show (_ * K).toNat = _; rw [BitVec.toNat_mul, Nat.mul_comm]
  have e3 := mul_mulhu (aluEval .mul (aluEval .add X B0) K) N0
  have hlun : (aluEval .mul (aluEval .mul (aluEval .add X B0) K) N0).toNat =
      (aluEval .mul (aluEval .add X B0) K).toNat * N0.toNat % 2 ^ 32 := by
    show (_ * N0).toNat = _; rw [BitVec.toNat_mul]
  generalize aluEval .add X B0 = s at e1 hu hlun e3 ⊢
  generalize aluEval .mul s K = u at hu hlun e3 ⊢
  generalize aluEval .mul u N0 = lo at e3 hlun ⊢
  generalize aluEval .mulhu u N0 = hi at e3 ⊢
  generalize aluEval .sltu s B0 = c0 at e1 ⊢
  have e4 := add_carry lo s
  have b1 := add_toNat c0 hi
  generalize aluEval .add lo s = w at e4 ⊢
  generalize aluEval .add c0 hi = t at b1 ⊢
  generalize aluEval .sltu w s = c1 at e4 ⊢
  have b2 := add_toNat c1 t
  generalize aluEval .add c1 t = c at b2 ⊢
  have hw : w.toNat = 0 := by
    have h0 := mont_low (s := s.toNat) hk
    rw [← hu, ← hlun] at h0
    have := w.isLt; have := s.isLt; have := lo.isLt
    omega
  have hU := u.isLt; have hN := N0.isLt
  have P2 : u.toNat * N0.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  generalize u.toNat * N0.toNat = p at e3 P2 hlun ⊢
  have := s.isLt; have := lo.isLt; have := hi.isLt; have := c0.isLt; have := t.isLt; have := c1.isLt
  have := c.isLt; have := X.isLt; have := B0.isLt
  have hhi : hi.toNat ≤ 2 ^ 32 - 2 := by omega
  have hc0 : c0.toNat ≤ 1 := by omega
  have hc1 : c1.toNat ≤ 1 := by omega
  have ht : t.toNat = c0.toNat + hi.toNat := by rw [b1]; exact Nat.mod_eq_of_lt (by omega)
  have hc : c.toNat = c1.toNat + t.toNat := by
    rw [b2]; apply Nat.mod_eq_of_lt
    have : 2 ^ 32 * (c1.toNat + t.toNat) ≤ 2 ^ 64 - 1 := by omega
    omega
  rw [hc]; omega

/-- The inner loop's body, from 0x6A to its branch at 0x96. -/
def mrBody : List BInstr :=
  [.lw (9 : Fin 32) a3 0, .alu .mul (8 : Fin 32) (9 : Fin 32) a4, .alu .mulhu (9 : Fin 32) (9 : Fin 32) a4,
   .lw a1 a2 0, .lw a0 a2 0xFFFFFFFC, .alu .add a1 a1 (8 : Fin 32), .alu .sltu (8 : Fin 32) a1 (8 : Fin 32),
   .alu .add a0 a0 a1, .alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), .alu .sltu a1 a0 a1,
   .aluImm .add a3 a3 4, .alu .add a1 a1 (8 : Fin 32), .sw a2 a0 0xFFFFFFFC, .sw a2 a1 0,
   .aluImm .add a2 a2 4, .aluImm .add a5 a5 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem mrBody_end : blockEnd montRetrieve12Code 0x6A mrBody = some 0x96 := by decide
end

set_option maxRecDepth 20000 in
theorem mrBody_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mrBody (M, f)).1 = memStore32 (memStore32 M (f a2 + 0xFFFFFFFC)
        (mrCols (memLoad32 M (f a3 + 0)) (f a4) (memLoad32 M (f a2 + 0xFFFFFFFC)) (memLoad32 M (f a2 + 0))).1)
        (f a2 + 0)
        (mrCols (memLoad32 M (f a3 + 0)) (f a4) (memLoad32 M (f a2 + 0xFFFFFFFC)) (memLoad32 M (f a2 + 0))).2 ∧
    (runBlock mrBody (M, f)).2 a3 = f a3 + 4 ∧
    (runBlock mrBody (M, f)).2 a2 = f a2 + 4 ∧
    (runBlock mrBody (M, f)).2 a5 = f a5 + 0xFFFFFFFF ∧
    ∀ q, q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a5 →
      (runBlock mrBody (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mrBody]
  refine ⟨?_, ?_, ?_, ?_, fun q q8 q9 q10 q11 q12 q13 q15 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, hz]
    · simp [upd, hq, q8, q9, q10, q11, q12, q13, q15]

theorem mrBody_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hn : (f a3 + 0).toNat % 4 = 0) (ho : (f a2 + 0).toNat % 4 = 0)
    (hc : (f a2 + 0xFFFFFFFC).toNat % 4 = 0)
    (hs1 : Sep (f a2 + 0xFFFFFFFC) 4 base len) (hs2 : Sep (f a2 + 0) 4 base len) :
    BlockOk base len mrBody (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, mrBody, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hn, ho, hc, ⟨hc, hs1⟩, ho, hs2⟩

/-- The registers the inner loop's body leaves alone. -/
def rbKeep (q : Fin 32) : Bool := q.val ∉ [8, 9, 10, 11, 12, 13, 15]

/-- **One pass of the inner loop**, from 0x6A: column `k + 1` of a pass,
which reads the carry from the accumulator's word `k` and its word `k + 1`,
and writes the column's word and carry back over them. -/
theorem mr_iter {M : Word → BitVec 8} {B np acc U lo hi : Word} {n : Machine} {k : Nat}
    (s : St M B n 0x6A (reg n)) (hc : CodeIn M B montRetrieve12Code) (hk : k < 11)
    (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hS1 : Sep (acc + BitVec.ofNat 32 (4 * k)) 4 B montRetrieve12Code.length)
    (hS2 : Sep (acc + BitVec.ofNat 32 (4 * (k + 1))) 4 B montRetrieve12Code.length)
    (ra3 : reg n a3 = np + BitVec.ofNat 32 (4 * (k + 1)))
    (ra2 : reg n a2 = acc + BitVec.ofNat 32 (4 * (k + 1)))
    (ra4 : reg n a4 = U) (ra5 : reg n a5 = BitVec.ofNat 32 (11 - k))
    (hcol : mrCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1)))) U (memLoad32 M (acc + BitVec.ofNat 32 (4 * k)))
      (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1)))) = (lo, hi)) :
    ∃ n', Steps n n' ∧
      St (memStore32 (memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo) (acc + BitVec.ofNat 32 (4 * (k + 1))) hi)
        B n' (if k + 1 < 11 then 0x6A else 0x98) (reg n') ∧
      reg n' a3 = np + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' a2 = acc + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' a5 = BitVec.ofNat 32 (11 - (k + 1)) ∧
      ∀ q, rbKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have ok := mrBody_ok (M := M) (f := reg n) (base := B) (len := montRetrieve12Code.length)
    (by rw [ra3, add_lit_zero]; exact aligned_add hnp (by omega))
    (by rw [ra2, add_lit_zero]; exact aligned_add hacc (by omega))
    (by rw [ra2, back4 acc k]; exact aligned_add hacc (by omega))
    (by rw [ra2, back4 acc k]; exact hS1)
    (by rw [ra2, add_lit_zero]; exact hS2)
  obtain ⟨n1, c1, u1⟩ := St.block mrBody s hc mrBody_end ok
  obtain ⟨em, e3, e2, e5, fr⟩ := mrBody_run (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [em, ra3, ra2, ra4, add_lit_zero, add_lit_zero, back4 acc k, hcol] at u1'
  have g : ∀ q, reg n1 q = (runBlock mrBody (M, reg n)).2 q := u1.regs
  have hb : branchTaken .bne (reg n1 a5) (reg n1 x0) = decide (k + 1 < 11) := by
    rw [g, e5, ra5, cnt11_dec k hk, u1'.zero]; exact cnt11_ne k hk
  have hc1 := CodeIn.store32 (v := hi) (CodeIn.store32 (v := lo) hc hS1) hS2
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a3 = np + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n2 a2 = acc + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n2 a5 = BitVec.ofNat 32 (11 - (k + 1)) ∧
      ∀ q, rbKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨?_, ?_, ?_, fun q hq => ?_⟩
    · rw [h2, g, e3, ra3, ptr4]
    · rw [h2, g, e2, ra2, ptr4]
    · rw [h2, g, e5, ra5, cnt11_dec k hk]
    · rw [h2, g]
      exact fr q (pkeep_ne (r := 8) hq rfl) (pkeep_ne (r := 9) hq rfl) (pkeep_ne (r := a0) hq rfl)
        (pkeep_ne (r := a1) hq rfl) (pkeep_ne (r := a2) hq rfl) (pkeep_ne (r := a3) hq rfl)
        (pkeep_ne (r := a5) hq rfl)
  by_cases hl : k + 1 < 11
  · obtain ⟨n2, d2, u2⟩ := u1'.taken hc1 0x6A mr_at_96 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc1 0x98 mr_at_96 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

theorem mr_inner_arith {Ak lo hi Cin P B X U A0 N O Nn : Nat} (h1 : B * (Ak + Cin * P) = A0 + X + U * N)
    (h2 : lo + B * hi = O + Nn * U + Cin) :
    B * (Ak + lo * P + hi * (P * B)) = A0 + O * (P * B) + X + U * (N + Nn * (P * B)) := by
  have e2 : P * B * (lo + B * hi) = P * B * (O + Nn * U + Cin) := by rw [h2]
  simp only [Nat.mul_add] at h1 e2 ⊢
  simp only [Nat.mul_comm, Nat.mul_left_comm] at h1 e2 ⊢
  omega

/-- What one column does to a pass's sum: with the carry in the
accumulator's word `k`, the words below it the pass's new words, and the
words above it the pass's input, column `k + 1` moves one more word of the
input and the modulus into the sum. -/
theorem mr_inv_step {M M0 : Word → BitVec 8} {acc np U lo hi : Word} {X k : Nat} (hk : k < 11)
    (hw : acc.toNat + 48 ≤ 2 ^ 32) (hAN : Sep acc 48 np 48)
    (hfr : ∀ a, Sep acc 48 a 1 → M a = M0 a)
    (hab : ∀ i, k + 1 ≤ i → i < 12 →
      memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)))
    (hinv : 2 ^ 32 * accV M acc (k + 1) = accV M0 acc (k + 1) + X + U.toNat * accV M0 np (k + 1))
    (hcol : mrCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1)))) U (memLoad32 M (acc + BitVec.ofNat 32 (4 * k)))
      (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1)))) = (lo, hi)) :
    2 ^ 32 * accV (memStore32 (memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo) (acc + BitVec.ofNat 32 (4 * (k + 1)))
        hi) acc (k + 2) = accV M0 acc (k + 2) + X + U.toNat * accV M0 np (k + 2) ∧
    (∀ a, Sep acc 48 a 1 → memStore32 (memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo)
      (acc + BitVec.ofNat 32 (4 * (k + 1))) hi a = M0 a) ∧
    (∀ i, k + 2 ≤ i → i < 12 → memLoad32 (memStore32 (memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo)
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

/-- **The inner loop**, from column `k + 1` of a pass to its end at 0x98:
columns `k + 1..11` of the pass. -/
theorem mr_inner {B acc np U : Word} {X : Nat} {M0 : Word → BitVec 8}
    (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0) (hw : acc.toNat + 48 ≤ 2 ^ 32)
    (hAN : Sep acc 48 np 48) (hAC : Sep acc 48 B montRetrieve12Code.length) :
    ∀ m k, k + m + 1 = 11 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M B n 0x6A (reg n) → CodeIn M B montRetrieve12Code →
      (∀ a, Sep acc 48 a 1 → M a = M0 a) →
      (∀ i, k + 1 ≤ i → i < 12 →
        memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) →
      2 ^ 32 * accV M acc (k + 1) = accV M0 acc (k + 1) + X + U.toNat * accV M0 np (k + 1) →
      reg n a3 = np + BitVec.ofNat 32 (4 * (k + 1)) → reg n a2 = acc + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n a4 = U → reg n a5 = BitVec.ofNat 32 (11 - k) →
      ∃ n' M', Steps n n' ∧ St M' B n' 0x98 (reg n') ∧ CodeIn M' B montRetrieve12Code ∧
        2 ^ 32 * accV M' acc 12 = accV M0 acc 12 + X + U.toNat * accV M0 np 12 ∧
        (∀ a, Sep acc 48 a 1 → M' a = M0 a) ∧
        ∀ q, rbKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro k hk M n s hc hfr hab hinv ra3 ra2 ra4 ra5
    have k10 : k = 10 := by omega
    subst k10
    obtain ⟨lo, hi, hcol⟩ : ∃ lo hi, mrCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (10 + 1)))) U
        (memLoad32 M (acc + BitVec.ofNat 32 (4 * 10))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (10 + 1)))) =
        (lo, hi) := ⟨_, _, rfl⟩
    obtain ⟨n1, c1, u1, _, _, _, fr⟩ := mr_iter (k := 10) s hc (by decide) hnp hacc
      (hAC.sub (by omega)) (hAC.sub (by omega)) ra3 ra2 ra4 ra5 hcol
    obtain ⟨i1, i2, _⟩ := mr_inv_step (k := 10) (by decide) hw hAN hfr hab hinv hcol
    exact ⟨n1, _, c1, u1, CodeIn.store32 (CodeIn.store32 hc (hAC.sub (by omega))) (hAC.sub (by omega)), i1, i2, fr⟩
  | succ m ih =>
    intro k hk M n s hc hfr hab hinv ra3 ra2 ra4 ra5
    have hl : k + 1 < 11 := by omega
    obtain ⟨lo, hi, hcol⟩ : ∃ lo hi, mrCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1)))) U
        (memLoad32 M (acc + BitVec.ofNat 32 (4 * k))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1)))) =
        (lo, hi) := ⟨_, _, rfl⟩
    obtain ⟨n1, c1, u1, e3, e2, e5, fr⟩ := mr_iter (k := k) s hc (by omega) hnp hacc
      (hAC.sub (by omega)) (hAC.sub (by omega)) ra3 ra2 ra4 ra5 hcol
    rw [ite_eq_left hl] at u1
    obtain ⟨i1, i2, i3⟩ := mr_inv_step (k := k) (by omega) hw hAN hfr hab hinv hcol
    have k4 : reg n1 a4 = U := by rw [fr _ rfl, ra4]
    obtain ⟨n', M', c', u', hc', f1, f2, fr'⟩ :=
      ih (k + 1) (by omega) u1 (CodeIn.store32 (CodeIn.store32 hc (hAC.sub (by omega))) (hAC.sub (by omega)))
        i2 i3 i1 e3 e2 k4 e5
    exact ⟨n', M', c1.trans c', u', hc', f1, f2, fun q hq => by rw [fr' q hq, fr q hq]⟩

/-- The start of a pass, from 0x3A: load the input's limb and the
accumulator's low word, compute the factor `u` and the first column's carry,
store the carry over the low word, and point at the next words. -/
def mrHeadBlock : List BInstr :=
  [.aluImm .sll a2 (6 : Fin 32) 2, .alu .add a2 a2 (21 : Fin 32), .lw a3 sp 4, .lw a2 a2 0, .alu .add a2 a2 a3,
   .alu .mul a4 a2 (20 : Fin 32), .alu .mul a5 a4 (5 : Fin 32), .alu .mulhu (9 : Fin 32) a4 (5 : Fin 32),
   .alu .sltu a3 a2 a3, .alu .add a5 a5 a2, .alu .add a3 a3 (9 : Fin 32), .alu .sltu a2 a5 a2, .alu .add a2 a2 a3,
   .aluImm .add a5 x0 0xB, .sw sp a2 4, .alu .add a2 x0 a6, .alu .add a3 x0 (19 : Fin 32)]

section
set_option maxRecDepth 20000
theorem mrHeadBlock_end : blockEnd montRetrieve12Code 0x3A mrHeadBlock = some 0x68 := by decide
end

/-- The registers the start of a pass leaves alone. -/
def mhKeep (q : Fin 32) : Bool := q.val ∉ [9, 12, 13, 14, 15]

set_option maxRecDepth 20000 in
theorem mrHeadBlock_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mrHeadBlock (M, f)).1 = memStore32 M (f sp + 4)
      (mrHead (memLoad32 M (aluEval .add (aluEval .sll (f (6 : Fin 32)) 2) (f (21 : Fin 32)) + 0))
        (memLoad32 M (f sp + 4)) (f (20 : Fin 32)) (f (5 : Fin 32))).2 ∧
    (runBlock mrHeadBlock (M, f)).2 a4 =
      (mrHead (memLoad32 M (aluEval .add (aluEval .sll (f (6 : Fin 32)) 2) (f (21 : Fin 32)) + 0))
        (memLoad32 M (f sp + 4)) (f (20 : Fin 32)) (f (5 : Fin 32))).1 ∧
    (runBlock mrHeadBlock (M, f)).2 a5 = BitVec.ofNat 32 (11 - 0) ∧
    (runBlock mrHeadBlock (M, f)).2 a2 = f a6 ∧
    (runBlock mrHeadBlock (M, f)).2 a3 = f (19 : Fin 32) ∧
    ∀ q, mhKeep q = true → (runBlock mrHeadBlock (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mrHeadBlock]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, pkeep_ne (r := 9) hq rfl, pkeep_ne (r := a2) hq rfl,
        pkeep_ne (r := a3) hq rfl, pkeep_ne (r := a4) hq rfl, pkeep_ne (r := a5) hq rfl]

theorem mrHeadBlock_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hx : (aluEval .add (aluEval .sll (f (6 : Fin 32)) 2) (f (21 : Fin 32)) + 0).toNat % 4 = 0)
    (hs : (f sp + 4).toNat % 4 = 0) (hsep : Sep (f sp + 4) 4 base len) :
    BlockOk base len mrHeadBlock (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, mrHeadBlock, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hs, hx, hs, hsep⟩

/-- The registers a pass leaves alone. -/
def mpKeep (q : Fin 32) : Bool := q.val ∉ [6, 8, 9, 10, 11, 12, 13, 14, 15]

theorem mpKeep_head : ∀ q, mpKeep q = true → mhKeep q = true := by decide
theorem mpKeep_body : ∀ q, mpKeep q = true → rbKeep q = true := by decide

set_option exponentiation.threshold 400 in
/-- **One pass of the outer loop**, from 0x3A: add limb `i` of the input,
and `u` times the modulus, to the accumulator, and shift the sum down a
word. -/
theorem mr_pass {B acc xp np K : Word} {MB : Word → BitVec 8} {i : Nat} (hi : i < 12)
    (hxp : xp.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 48 ≤ 2 ^ 32) (hAX : Sep acc 48 xp 48) (hAN : Sep acc 48 np 48)
    (hAC : Sep acc 48 B montRetrieve12Code.length)
    (hk : (K.toNat * (memLoad32 MB np).toNat + 1) % 2 ^ 32 = 0)
    {M : Word → BitVec 8} {n : Machine} (s : St M B n 0x3A (reg n)) (hc : CodeIn M B montRetrieve12Code)
    (hfr : ∀ a, Sep acc 48 a 1 → M a = MB a)
    (r6 : reg n (6 : Fin 32) = BitVec.ofNat 32 i) (r21 : reg n (21 : Fin 32) = xp)
    (r20 : reg n (20 : Fin 32) = K) (r5 : reg n (5 : Fin 32) = memLoad32 MB np) (rsp : reg n sp + 4 = acc)
    (r19 : reg n (19 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)))
    (r16 : reg n a6 = acc + BitVec.ofNat 32 (4 * (0 + 1))) (r17 : reg n (17 : Fin 32) = 12) :
    ∃ n' M', Steps n n' ∧ St M' B n' (if i + 1 < 12 then 0x3A else 0x9E) (reg n') ∧
      CodeIn M' B montRetrieve12Code ∧ (∀ a, Sep acc 48 a 1 → M' a = MB a) ∧
      (∃ u : Nat, u < 2 ^ 32 ∧ 2 ^ 32 * accV M' acc 12 =
        accV M acc 12 + (memLoad32 MB (xp + BitVec.ofNat 32 (4 * i))).toNat + u * accV MB np 12) ∧
      reg n' (6 : Fin 32) = BitVec.ofNat 32 (i + 1) ∧ ∀ q, mpKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hX : aluEval .add (aluEval .sll (reg n (6 : Fin 32)) 2) (reg n (21 : Fin 32)) + 0 =
      xp + BitVec.ofNat 32 (4 * i) := by
    rw [r6, r21, sll12 i hi, add_lit_zero]; exact BitVec.add_comm _ _
  have hS0 : Sep acc 4 B montRetrieve12Code.length :=
    (hAC.sub (c := 0) (l := 4) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h
  have ok1 := mrHeadBlock_ok (M := M) (f := reg n) (base := B) (len := montRetrieve12Code.length)
    (by rw [hX]; exact aligned_add hxp (by omega)) (by rw [rsp]; exact hacc) (by rw [rsp]; exact hS0)
  obtain ⟨n1, c1, u1⟩ := St.block mrHeadBlock s hc mrHeadBlock_end ok1
  obtain ⟨hm1, h4, h5, h2, h3, hfr1⟩ := mrHeadBlock_run (M := M) (f := reg n) hz
  rw [hX, rsp, r20, r5] at hm1 h4
  have eX : memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) = memLoad32 MB (xp + BitVec.ofNat 32 (4 * i)) :=
    load_frame hfr (hAX.subR (by omega))
  obtain ⟨u, c, hH⟩ : ∃ u c, mrHead (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) (memLoad32 M acc) K
      (memLoad32 MB np) = (u, c) := ⟨_, _, rfl⟩
  have hd := mr_head (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) (memLoad32 M acc) K (memLoad32 MB np) hk
  rw [hH] at hd hm1 h4
  simp only at hd hm1 h4
  have u1' := u1.self
  rw [hm1] at u1'
  have g1 : ∀ q, reg n1 q = (runBlock mrHeadBlock (M, reg n)).2 q := u1.regs
  have hb : branchTaken .beq (reg n1 a5) (reg n1 x0) = false := by
    rw [g1, h5, u1'.zero]; decide
  have hc1 := CodeIn.store32 (v := c) hc hS0
  obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc1 0x6A mr_at_68 (by decide) hb
  have g2 : ∀ q, reg n2 q = (runBlock mrHeadBlock (M, reg n)).2 q := fun q => by rw [u2.regs, g1]
  have frH : ∀ a, Sep acc 48 a 1 → memStore32 M acc c a = M a := fun a ha => memStore32_get_sep
    ((ha.sub (c := 0) (l := 4) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h)
  have abH : ∀ j, 0 + 1 ≤ j → j < 12 →
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
    rw [Nat.mul_zero, add_ofNat_zero, add_ofNat_zero, memLoad32_store32_same, eN0]
    simp only [Nat.zero_add, Nat.mul_one]
    omega
  obtain ⟨n3, M1, c3, u3, hc3, I1, I2, fr3⟩ :=
    mr_inner (M0 := M) (U := u) (X := (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))).toNat) hnp hacc hw hAN hAC
      10 0 (by decide) u2.self hc1 frH abH inv0
      (by rw [g2, h3, r19]) (by rw [g2, h2, r16]) (by rw [g2, h4]) (by rw [g2, h5])
  have k3 : ∀ q, mpKeep q = true → reg n3 q = reg n q := fun q hq => by
    rw [fr3 q (mpKeep_body q hq), g2, hfr1 q (mpKeep_head q hq)]
  obtain ⟨n4, d4, u4⟩ := u3.aluImm hc3 mr_at_98 (off' := 0x9A) (by decide)
  have v6 : upd (reg n3) (6 : Fin 32) (aluEval .add (reg n3 (6 : Fin 32)) 1) (6 : Fin 32) =
      BitVec.ofNat 32 (i + 1) := by
    simp +decide only [upd, ↓reduceIte]
    rw [fr3 _ rfl, g2, hfr1 _ rfl, r6]; exact ofNat_succ i
  have v17 : upd (reg n3) (6 : Fin 32) (aluEval .add (reg n3 (6 : Fin 32)) 1) (17 : Fin 32) = 12 := by
    simp +decide only [upd, ↓reduceIte]
    rw [k3 _ rfl, r17]
  have hb4 : branchTaken .bne (upd (reg n3) (6 : Fin 32) (aluEval .add (reg n3 (6 : Fin 32)) 1) (6 : Fin 32))
      (upd (reg n3) (6 : Fin 32) (aluEval .add (reg n3 (6 : Fin 32)) 1) (17 : Fin 32)) = decide (i + 1 < 12) := by
    rw [v6, v17]; exact pass_ne i hi
  have fr4 : ∀ a, Sep acc 48 a 1 → M1 a = MB a := fun a ha => by rw [I2 a ha, hfr a ha]
  have arith : 2 ^ 32 * accV M1 acc 12 =
      accV M acc 12 + (memLoad32 MB (xp + BitVec.ofNat 32 (4 * i))).toNat + u.toNat * accV MB np 12 := by
    rw [I1, eX, accV_frame48 (b := np) (n := 12) hfr hAN]
  have k4 : ∀ q, q ≠ (6 : Fin 32) → upd (reg n3) (6 : Fin 32) (aluEval .add (reg n3 (6 : Fin 32)) 1) q = reg n3 q :=
    fun q hq => by
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd, u3.zero]
      · simp [upd, h0, hq]
  by_cases hl : i + 1 < 12
  · obtain ⟨n5, d5, u5⟩ := u4.taken hc3 0x3A mr_at_9a (by decide) (by rw [hb4]; exact decide_eq_true hl)
    have g5 := u5.regs
    refine ⟨n5, M1, Steps.trans c1 (.cons d2 (c3.trans (.cons d4 (.single d5)))), by
      rw [ite_eq_left hl]; exact u5.self, hc3, fr4, ⟨u.toNat, u.isLt, arith⟩, by rw [g5, v6], fun q hq => ?_⟩
    rw [g5, k4 q (pkeep_ne (r := 6) hq rfl), k3 q hq]
  · obtain ⟨n5, d5, u5⟩ := u4.notTaken hc3 0x9E mr_at_9a (by decide) (by rw [hb4]; exact decide_eq_false hl)
    have g5 := u5.regs
    refine ⟨n5, M1, Steps.trans c1 (.cons d2 (c3.trans (.cons d4 (.single d5)))), by
      rw [ite_eq_right hl]; exact u5.self, hc3, fr4, ⟨u.toNat, u.isLt, arith⟩, by rw [g5, v6], fun q hq => ?_⟩
    rw [g5, k4 q (pkeep_ne (r := 6) hq rfl), k3 q hq]

theorem mr_outer_arith {P B T T' x u N Xi U : Nat} (hp : B * T' = T + x + u * N) (hinv : P * T = Xi + U * N)
    (hU : U < P) (hu : u < B) : P * B * T' = Xi + x * P + (U + P * u) * N ∧ U + P * u < P * B := by
  constructor
  · rw [Nat.mul_assoc, hp]
    simp only [Nat.mul_add, Nat.add_mul, hinv]
    simp only [Nat.mul_comm, Nat.mul_left_comm]
    omega
  · have : P * (u + 1) ≤ P * B := Nat.mul_le_mul_left P (by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega

set_option exponentiation.threshold 400 in
/-- **The outer loop**, from pass `i` to its end at 0x9E. The accumulator
holds a sum `T` with `2^(32 i) T = X_i + U N`, for `X_i` the input's low
`i` limbs and some `U < 2^(32 i)`. -/
theorem mr_outer {B acc xp np K : Word} {MB : Word → BitVec 8}
    (hxp : xp.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 48 ≤ 2 ^ 32) (hAX : Sep acc 48 xp 48) (hAN : Sep acc 48 np 48)
    (hAC : Sep acc 48 B montRetrieve12Code.length)
    (hk : (K.toNat * (memLoad32 MB np).toNat + 1) % 2 ^ 32 = 0) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M B n 0x3A (reg n) → CodeIn M B montRetrieve12Code → (∀ a, Sep acc 48 a 1 → M a = MB a) →
      (∃ U, U < 2 ^ (32 * i) ∧ 2 ^ (32 * i) * accV M acc 12 = accV MB xp i + U * accV MB np 12) →
      reg n (6 : Fin 32) = BitVec.ofNat 32 i → reg n (21 : Fin 32) = xp → reg n (20 : Fin 32) = K →
      reg n (5 : Fin 32) = memLoad32 MB np → reg n sp + 4 = acc →
      reg n (19 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n a6 = acc + BitVec.ofNat 32 (4 * (0 + 1)) → reg n (17 : Fin 32) = 12 →
      ∃ n' M', Steps n n' ∧ St M' B n' 0x9E (reg n') ∧ CodeIn M' B montRetrieve12Code ∧
        (∀ a, Sep acc 48 a 1 → M' a = MB a) ∧
        (∃ U, U < 2 ^ (32 * 12) ∧ 2 ^ (32 * 12) * accV M' acc 12 = accV MB xp 12 + U * accV MB np 12) ∧
        ∀ q, mpKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro i hi M n s hc hfr hinv r6 r21 r20 r5 rsp r19 r16 r17
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, _, k1⟩ := mr_pass (i := 11) (by decide) hxp hnp hacc
      hw hAX hAN hAC hk s hc hfr r6 r21 r20 r5 rsp r19 r16 r17
    obtain ⟨U, hU, hUv⟩ := hinv
    obtain ⟨a1, a2⟩ := mr_outer_arith hp hUv hU hu
    refine ⟨n1, M1, c1, u1, hc1, hf1, ⟨U + 2 ^ (32 * 11) * u, by rw [pow32_succ 11]; exact a2, ?_⟩, k1⟩
    rw [pow32_succ 11, a1, accV_succ1 MB xp 11]
  | succ m ih =>
    intro i hi M n s hc hfr hinv r6 r21 r20 r5 rsp r19 r16 r17
    have hl : i + 1 < 12 := idx_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, e6, k1⟩ := mr_pass (i := i)
      (Nat.lt_trans (Nat.lt_succ_self i) hl) hxp hnp hacc hw hAX hAN hAC hk s hc hfr r6 r21 r20 r5 rsp r19 r16 r17
    rw [ite_eq_left hl] at u1
    obtain ⟨U, hU, hUv⟩ := hinv
    obtain ⟨a1, a2⟩ := mr_outer_arith hp hUv hU hu
    have inv1 : ∃ U, U < 2 ^ (32 * (i + 1)) ∧
        2 ^ (32 * (i + 1)) * accV M1 acc 12 = accV MB xp (i + 1) + U * accV MB np 12 :=
      ⟨U + 2 ^ (32 * i) * u, by rw [pow32_succ i]; exact a2, by rw [pow32_succ i, a1, accV_succ1 MB xp i]⟩
    obtain ⟨n', M', c', u', hc', hf', hv', k'⟩ := ih (i + 1) (idx_succ hi) u1 hc1 hf1 inv1 e6
      (by rw [k1 _ rfl, r21]) (by rw [k1 _ rfl, r20]) (by rw [k1 _ rfl, r5]) (by rw [k1 _ rfl, rsp])
      (by rw [k1 _ rfl, r19]) (by rw [k1 _ rfl, r16]) (by rw [k1 _ rfl, r17])
    exact ⟨n', M', c1.trans c', u', hc', hf', hv', fun q hq => by rw [k' q hq, k1 q hq]⟩

/-- What `montgomery_retrieve::<12>` saves in its frame, at offsets from its
`sp`. -/
abbrev mrPs : List (Fin 32 × Word) :=
  [(ra, 0x4C), ((8 : Fin 32), 0x48), ((9 : Fin 32), 0x44), ((18 : Fin 32), 0x40), ((19 : Fin 32), 0x3C),
   ((20 : Fin 32), 0x38), ((21 : Fin 32), 0x34)]

/-- From 0x10: keep the arguments, and set up the call to `memset`. -/
def mrPro : List BInstr :=
  [.alu .add (20 : Fin 32) x0 a3, .alu .add (19 : Fin 32) x0 a2, .alu .add (21 : Fin 32) x0 a1,
   .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 4, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0]

/-- From 0x28: zero the pass count, load the modulus's low limb, and point at
the next limbs of the modulus and the accumulator. -/
def mrSetup : List BInstr :=
  [.aluImm .add (6 : Fin 32) x0 0, .lw (5 : Fin 32) (19 : Fin 32) 0, .aluImm .add (19 : Fin 32) (19 : Fin 32) 4,
   .aluImm .add a6 sp 8, .aluImm .add (17 : Fin 32) x0 0xC]

/-- From 0x9E: set up the call to `memcpy`. -/
def mrArgs : List BInstr :=
  [.aluImm .add a1 sp 4, .aluImm .add a2 x0 0x30, .alu .add a0 x0 (18 : Fin 32)]

section
set_option maxRecDepth 20000
theorem mrSave_end : blockEnd montRetrieve12Code 2 (saveBlock mrPs) = some 0x10 := by decide
theorem mrPro_end : blockEnd montRetrieve12Code 0x10 mrPro = some 0x20 := by decide
theorem mrSetup_end : blockEnd montRetrieve12Code 0x28 mrSetup = some 0x36 := by decide
theorem mrArgs_end : blockEnd montRetrieve12Code 0x9E mrArgs = some 0xA6 := by decide
theorem mrRestore_end : blockEnd montRetrieve12Code 0xAE (restoreBlock mrPs) = some 0xBC := by decide
end

theorem mrPro_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mrPro (M, f)).1 = M ∧
    (runBlock mrPro (M, f)).2 (20 : Fin 32) = f a3 ∧ (runBlock mrPro (M, f)).2 (19 : Fin 32) = f a2 ∧
    (runBlock mrPro (M, f)).2 (21 : Fin 32) = f a1 ∧ (runBlock mrPro (M, f)).2 (18 : Fin 32) = f a0 ∧
    (runBlock mrPro (M, f)).2 a0 = f sp + 4 ∧ (runBlock mrPro (M, f)).2 a2 = 0x30 ∧
    (runBlock mrPro (M, f)).2 a1 = 0 ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (18 : Fin 32) → q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) →
      q ≠ (21 : Fin 32) → (runBlock mrPro (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mrPro]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q q0 q1 q2 q18 q19 q20 q21 => ?_⟩
  · simp +decide only [upd, ↓reduceIte, hz]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2, q18, q19, q20, q21]

/-- The registers the setup leaves alone. -/
def msKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 16, 17, 19]

set_option maxRecDepth 20000 in
theorem mrSetup_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mrSetup (M, f)).1 = M ∧
    (runBlock mrSetup (M, f)).2 (6 : Fin 32) = BitVec.ofNat 32 0 ∧
    (runBlock mrSetup (M, f)).2 (5 : Fin 32) = memLoad32 M (f (19 : Fin 32) + 0) ∧
    (runBlock mrSetup (M, f)).2 (19 : Fin 32) = f (19 : Fin 32) + 4 ∧
    (runBlock mrSetup (M, f)).2 a6 = f sp + 8 ∧
    (runBlock mrSetup (M, f)).2 (17 : Fin 32) = 12 ∧
    ∀ q, msKeep q = true → (runBlock mrSetup (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mrSetup]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte, hz]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, pkeep_ne (r := 5) hq rfl, pkeep_ne (r := 6) hq rfl, pkeep_ne (r := a6) hq rfl,
        pkeep_ne (r := 17) hq rfl, pkeep_ne (r := 19) hq rfl]

theorem mrArgs_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mrArgs (M, f)).1 = M ∧ (runBlock mrArgs (M, f)).2 a1 = f sp + 4 ∧
    (runBlock mrArgs (M, f)).2 a2 = 0x30 ∧ (runBlock mrArgs (M, f)).2 a0 = f (18 : Fin 32) ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → (runBlock mrArgs (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mrArgs]
  refine ⟨trivial, ?_, ?_, ?_, fun q q0 q1 q2 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2]

/-- Where `montgomery_retrieve::<12>` runs: its code and its callees' at
their offsets, the 0x50 bytes of stack below `sp0` that it uses, and the
result, input, and modulus, aligned and apart from what each must not
touch. -/
structure MREnv (M : Word → BitVec 8) (P sp0 out xp np : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P montRetrieve12Code
  mset : CodeIn M (P + 0xA30) memsetCode
  stub : CodeIn M (P + 0xA98) memcpyStubCode
  body : CodeIn M (P + 0xAA0) memcpyBodyCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x50 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hxp : xp.toNat % 4 = 0
  hnp : np.toNat % 4 = 0
  hwo : out.toNat + 48 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFFB0) 0x50 P montRetrieve12Code.length
  sGM : Sep (sp0 + 0xFFFFFFB0) 0x50 (P + 0xA30) memsetCode.length
  sGU : Sep (sp0 + 0xFFFFFFB0) 0x50 (P + 0xA98) memcpyStubCode.length
  sGY : Sep (sp0 + 0xFFFFFFB0) 0x50 (P + 0xAA0) memcpyBodyCode.length
  sOG : Sep out 48 (sp0 + 0xFFFFFFB0) 0x50
  sOC : Sep out 48 P montRetrieve12Code.length
  sOY : Sep out 48 (P + 0xAA0) memcpyBodyCode.length
  sXG : Sep xp 48 (sp0 + 0xFFFFFFB0) 0x50
  sNG : Sep np 48 (sp0 + 0xFFFFFFB0) 0x50

theorem mrFrame (sp0 : Word) (h : 0x50 ≤ sp0.toNat) : (sp0 + 0xFFFFFFB0).toNat + 0x50 = sp0.toNat := by
  rw [BitVec.toNat_add]; have : (0xFFFFFFB0 : Word).toNat = 0xFFFFFFB0 := rfl; rw [this]; have := sp0.isLt; omega

/-- **The prologue of `montgomery_retrieve::<12>`**, from 0 to the outer
loop at 0x3A: open the frame at `G`, save registers, zero the accumulator
at `G + 4`, and set up the first pass. -/
theorem mr_pro (m : Machine) {P sp0 out xp np K : Word} (E : MREnv m.mem P sp0 out xp np) (hpc : m.pc = P)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp) (ha2 : reg m a2 = np) (ha3 : reg m a3 = K)
    (hsp : reg m sp = sp0) :
    ∃ n M, Steps m n ∧ St M P n 0x3A (reg n) ∧
      (∀ x, Sep (sp0 + 0xFFFFFFB0) 0x50 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ mrPs → memLoad32 M (sp0 + 0xFFFFFFB0 + o) = reg m r) ∧
      accV M (sp0 + 0xFFFFFFB0 + 4) 12 = 0 ∧
      reg n sp = sp0 + 0xFFFFFFB0 ∧ reg n (6 : Fin 32) = BitVec.ofNat 32 0 ∧
      reg n (21 : Fin 32) = xp ∧ reg n (20 : Fin 32) = K ∧ reg n (5 : Fin 32) = memLoad32 m.mem np ∧
      reg n (19 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)) ∧
      reg n a6 = sp0 + 0xFFFFFFB0 + 4 + BitVec.ofNat 32 (4 * (0 + 1)) ∧
      reg n (17 : Fin 32) = 12 ∧ reg n (18 : Fin 32) = out ∧
      ∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg n q = reg m q := by
  have hG := mrFrame sp0 E.hS
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hGa : (sp0 + 0xFFFFFFB0).toNat % 4 = 0 := aligned_add E.hsp (k := 0xFFFFFFB0) (by decide)
  obtain ⟨m1, d1, u1⟩ := s0.aluImm E.code mr_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0) sp = sp0 + 0xFFFFFFB0 := by
    simp +decide [upd, hsp]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock mrPs) u1 E.code mrSave_end (saveBlock_ok _ mrPs _ fun q hq => by
      rw [sp1]
      simp only [mrPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add hGa (by decide), E.sGC.sub (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  have codeS : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFFB0) 0x50 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFFB0) 0x50 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have I2 : ∀ x, Sep (sp0 + 0xFFFFFFB0) 0x50 x 1 →
      saveMem m.mem (sp0 + 0xFFFFFFB0) (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0)) mrPs x = m.mem x :=
    fun x hx => saveMem_outside mrPs fun q hq => by
      simp only [mrPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hx.sub (by decide)
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q1]
  have sp2 : reg m2 sp = sp0 + 0xFFFFFFB0 := by rw [u2.regs]; exact sp1
  have hc2 := codeS E.code E.sGC I2
  obtain ⟨m3, c3, u3⟩ := St.block mrPro u2.self hc2 mrPro_end (by
    simp only [BlockOk, BInstr.ok, mrPro]; exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial⟩)
  obtain ⟨em3, p20, p19, p21, p18, pa0, pa2, pa1, pk⟩ := mrPro_run (M := saveMem m.mem (sp0 + 0xFFFFFFB0)
    (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0)) mrPs) (f := reg m2) u2.self.zero
  rw [em3] at u3
  have g3 : ∀ q, reg m3 q = (runBlock mrPro (saveMem m.mem (sp0 + 0xFFFFFFB0)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0)) mrPs, reg m2)).2 q := u3.regs
  obtain ⟨m4, c4, u4, a04, fr4⟩ := u3.self.memsetW (B := P + 0xA30) (w := 12) (dst := sp0 + 0xFFFFFFB0 + 4)
    (even_at P E.hP 0xA30 (by decide)) hc2 (codeS E.mset E.sGM I2) mr_at_20 mr_at_24
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P E.hP (0x20 + 8) (by decide)) (by decide)
    (by rw [BitVec.toNat_add]; have : (4 : Word).toNat = 4 := rfl; rw [this]; omega) (by decide)
    (aligned_add hGa (k := 4) (by decide)) (E.sGM.sub (c := 4) (l := 48) (by decide))
    (by rw [g3, pa0, sp2]) (by rw [g3, pa1]) (by rw [g3, pa2]; rfl)
  obtain ⟨M4, hM4⟩ : ∃ M4, fillWords (saveMem m.mem (sp0 + 0xFFFFFFB0)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0)) mrPs) (sp0 + 0xFFFFFFB0 + 4) 0 12 = M4 := ⟨_, rfl⟩
  rw [hM4] at u4
  have I4 : ∀ x, Sep (sp0 + 0xFFFFFFB0) 0x50 x 1 → M4 x = m.mem x := fun x hx => by
    rw [← hM4, fillWords_outside (dst := sp0 + 0xFFFFFFB0 + 4) 12 (hx.sub (c := 4) (l := 48) (by decide)), I2 x hx]
  have k4 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg m4 q = reg m3 q := fr4
  have e19 : reg m4 (19 : Fin 32) = np := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3, p19,
      r2 _ (by decide), ha2]
  have sp4 : reg m4 sp = sp0 + 0xFFFFFFB0 := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3,
      pk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp2]
  have hc4 := codeS E.code E.sGC I4
  obtain ⟨m5, c5, u5⟩ := St.block mrSetup u4.self hc4 mrSetup_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, mrSetup, upd, ↓reduceIte, and_true, true_and]
    rw [e19, add_lit_zero]; exact E.hnp)
  obtain ⟨em5, s6, s5, s19, sa6, s17, sk⟩ := mrSetup_run (M := M4) (f := reg m4) u4.self.zero
  rw [em5] at u5
  have g5 : ∀ q, reg m5 q = (runBlock mrSetup (M4, reg m4)).2 q := u5.regs
  obtain ⟨m6, d6, u6⟩ := u5.self.notTaken hc4 0x3A mr_at_36 (by decide) (by
    rw [g5, s17, u5.self.zero]; decide)
  have g6 : ∀ q, reg m6 q = reg m5 q := u6.regs
  have kk : ∀ q, msKeep q = true → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra →
      reg m6 q = (runBlock mrPro (saveMem m.mem (sp0 + 0xFFFFFFB0)
        (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0)) mrPs, reg m2)).2 q :=
    fun q hs h2 h3 h4 h5 h6 hr => by rw [g6, g5, sk q hs, k4 q h2 h3 h4 h5 h6 hr, g3]
  have hnF : Sep (sp0 + 0xFFFFFFB0) 0x50 np 4 := E.sNG.symm.subR (c := 0) (l := 4) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h
  refine ⟨m6, M4, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.single d6))))), u6.self, I4,
    fun r o hm => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · have slot : ∀ (r : Fin 32) (o : Word), (r, o) ∈ mrPs → 0x34 ≤ o.toNat → o.toNat + 4 ≤ 0x50 →
        (∀ p ∈ mrPs, p = (r, o) ∨ ((p.2.toNat + 4 ≤ o.toNat ∨ o.toNat + 4 ≤ p.2.toNat) ∧
          p.2.toNat + 4 ≤ 2 ^ 32 ∧ o.toNat + 4 ≤ 2 ^ 32)) → r ≠ sp →
        memLoad32 M4 (sp0 + 0xFFFFFFB0 + o) = reg m r := fun r o hm h1 h2 hp hr => by
      have hFo : sp0 + 0xFFFFFFB0 + BitVec.ofNat 32 o.toNat = sp0 + 0xFFFFFFB0 + o := by rw [ofNat_toNat_self]
      rw [← hM4, ← hFo, fillWords_load_sep (dst := sp0 + 0xFFFFFFB0 + 4) (by
        have := sep_offsets (sp0 + 0xFFFFFFB0) (c := 4) (n := 48) (d := o.toNat) (k := 4) (.inl (by omega))
          (by omega) (by omega)
        exact this), hFo, saveMem_slot mrPs _ hm hp, upd_ne (by
          intro h; apply hr; exact Fin.ext (by
            simp only [mrPs, List.mem_cons, List.mem_nil_iff, or_false] at hm
            rcases hm with h' | h' | h' | h' | h' | h' | h' <;>
              (rw [Prod.mk.injEq] at h'; rw [h'.1] at h; exact absurd h (by decide)))) hr]
    simp only [mrPs, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with h' | h' | h' | h' | h' | h' | h' <;>
      (rw [Prod.mk.injEq] at h'; obtain ⟨rfl, rfl⟩ := h'; exact slot _ _ (by decide) (by decide) (by decide)
        (by decide) (by decide))
  · have hacw : (sp0 + 0xFFFFFFB0 + 4).toNat + 4 * 12 ≤ 2 ^ 32 := by
      rw [BitVec.toNat_add]; have : (4 : Word).toNat = 4 := rfl; rw [this]; omega
    rw [← hM4]
    exact accV_zero 12 fun i hi => fillWords_load 12 i hi hacw
  · rw [g6, g5, sk _ rfl, sp4]
  · rw [g6, g5, s6]
  · rw [kk _ rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p21, r2 _ (by decide), ha1]
  · rw [kk _ rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p20, r2 _ (by decide), ha3]
  · rw [g6, g5, s5, e19, add_lit_zero, ← hM4,
      fillWords_load_sep (dst := sp0 + 0xFFFFFFB0 + 4) ((hnF.sub (c := 4) (l := 48) (by decide))),
      load_frame I2 hnF]
  · rw [g6, g5, s19, e19]; rfl
  · have e : (4 : Word) + BitVec.ofNat 32 (4 * (0 + 1)) = 8 := by decide
    rw [g6, g5, sa6, sp4, BitVec.add_assoc (sp0 + 0xFFFFFFB0) 4, e]
  · rw [g6, g5, s17]
  · rw [kk _ rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p18, r2 _ (by decide), ha0]
  · have key : ∀ q : Fin 32, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → msKeep q = true ∧ q ≠ a2 ∧ q ≠ a3 ∧
        q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ ra ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ (18 : Fin 32) ∧ q ≠ (19 : Fin 32) ∧
        q ≠ (20 : Fin 32) ∧ q ≠ (21 : Fin 32) ∧ q ≠ sp := by decide
    obtain ⟨hs, h2, h3, h4, h5, h6, hr, h0, h1, h18, h19, h20, h21, hsp'⟩ := key q hq
    rw [kk q hs h2 h3 h4 h5 h6 hr, pk q h0 h1 h2 h18 h19 h20 h21, r2 q hsp']

/-- The result's congruence and bound, from the accumulator's sum. -/
theorem mr_final {R X U N T : Nat} (h : R * T = X + U * N) (hU : U < R) :
    T * R % N = X % N ∧ (X < N → T < N) := by
  refine ⟨by rw [Nat.mul_comm, h, Nat.add_mul_mod_self_right], fun hX => ?_⟩
  have h1 : U * N + N ≤ R * N := by
    have := Nat.mul_le_mul_right N (show U + 1 ≤ R by omega)
    rwa [Nat.add_mul, Nat.one_mul] at this
  have : R * T < R * N := by omega
  exact Nat.lt_of_not_le fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le this (Nat.mul_le_mul_left R h))

set_option exponentiation.threshold 400 in
/-- **The compiled `montgomery_retrieve::<12>`.** For an input `x` and a
modulus `n` of 12 limbs, with `k · n₀ ≡ -1 (mod 2^32)`, it writes to `out` a
number `r` with `r · 2^384 ≡ x (mod n)`, and `r < n` when `x < n`. It
returns with `sp` and the callee-saved registers restored, and writes only
`out` and the 0x50 bytes of stack below `sp`. -/
theorem montRetrieve12_correct (m : Machine) {P sp0 out xp np K retAddr : Word}
    (E : MREnv m.mem P sp0 out xp np) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp)
    (ha2 : reg m a2 = np) (ha3 : reg m a3 = K) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hk : (K.toNat * (memLoad32 m.mem np).toNat + 1) % 2 ^ 32 = 0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      accV m'.mem out 12 * 2 ^ 384 % accV m.mem np 12 = accV m.mem xp 12 % accV m.mem np 12 ∧
      (accV m.mem xp 12 < accV m.mem np 12 → accV m'.mem out 12 < accV m.mem np 12) ∧
      (∀ x, Sep (sp0 + 0xFFFFFFB0) 0x50 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x) ∧
      ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q := by
  have hG := mrFrame sp0 E.hS
  have hGa : (sp0 + 0xFFFFFFB0).toNat % 4 = 0 := aligned_add E.hsp (k := 0xFFFFFFB0) (by decide)
  obtain ⟨n1, M1, c1, u1, hf1, hsl1, hacc0, sp1, r6, r21, r20, r5, r19, ra6, r17, r18, rk⟩ :=
    mr_pro m E hpc ha0 ha1 ha2 ha3 hsp
  have hAw : (sp0 + 0xFFFFFFB0 + 4).toNat + 48 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add]; have : (4 : Word).toNat = 4 := rfl; rw [this]; omega
  have hAa : (sp0 + 0xFFFFFFB0 + 4).toNat % 4 = 0 := aligned_add hGa (k := 4) (by decide)
  have codeG : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFFB0) 0x50 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFFB0) 0x50 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hc1 := codeG E.code E.sGC hf1
  have en0 : memLoad32 M1 np = memLoad32 m.mem np :=
    load_frame hf1 (E.sNG.symm.subR (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
  have hAX : Sep (sp0 + 0xFFFFFFB0 + 4) 48 xp 48 := E.sXG.symm.sub (c := 4) (l := 48) (by decide)
  have hAN : Sep (sp0 + 0xFFFFFFB0 + 4) 48 np 48 := E.sNG.symm.sub (c := 4) (l := 48) (by decide)
  have hAC : Sep (sp0 + 0xFFFFFFB0 + 4) 48 P montRetrieve12Code.length := E.sGC.sub (c := 4) (l := 48) (by decide)
  -- the outer loop
  obtain ⟨n2, M2, c2, u2, hc2, hf2, ⟨U, hU, hUv⟩, k2⟩ := mr_outer (MB := M1) (K := K) E.hxp E.hnp hAa hAw hAX hAN
    hAC (by rw [en0]; exact hk) 11 0 (by decide) u1 hc1 (fun _ _ => rfl)
    ⟨0, by decide, by rw [hacc0, Nat.mul_zero, Nat.zero_mul]; rfl⟩
    r6 r21 r20 (by rw [r5, en0]) (by rw [sp1]) r19 ra6 r17
  rw [accV_frameS hf1 E.sXG.symm, accV_frameS hf1 E.sNG.symm] at hUv
  have hf2G : ∀ x, Sep (sp0 + 0xFFFFFFB0) 0x50 x 1 → M2 x = m.mem x := fun x hx => by
    rw [hf2 x (hx.sub (c := 4) (l := 48) (by decide)), hf1 x hx]
  have sp2 : reg n2 sp = sp0 + 0xFFFFFFB0 := by rw [k2 _ rfl, sp1]
  have hc2' := codeG E.code E.sGC hf2G
  -- the arguments, and the call to `memcpy`
  obtain ⟨n3, c3, u3⟩ := St.block mrArgs u2 hc2' mrArgs_end (by
    simp only [BlockOk, BInstr.ok, mrArgs]; exact ⟨trivial, trivial, trivial, trivial⟩)
  obtain ⟨em3, s1, s2, s0, sk⟩ := mrArgs_run (M := M2) (f := reg n2) u2.zero
  rw [em3] at u3
  have g3 : ∀ q, reg n3 q = (runBlock mrArgs (M2, reg n2)).2 q := u3.regs
  have eY : P + 0xA98 + 8 = P + 0xAA0 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n4, c4, u4, _, fr4⟩ := u3.self.memcpyW (B := P + 0xA98) (w := 12) (dst := out)
    (src := sp0 + 0xFFFFFFB0 + 4) (even_at P E.hP 0xA98 (by decide)) hc2' (codeG E.stub E.sGU hf2G)
    (by rw [eY]; exact codeG E.body E.sGY hf2G) mr_at_a6 mr_at_aa (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (even_at P E.hP (0xA6 + 8) (by decide)) (by decide) (by have := E.hwo; omega) (by decide) E.hout hAa
    (E.sOG.subR (c := 4) (l := 48) (by decide)) (by rw [eY]; exact E.sOY)
    (by rw [g3, s0, k2 _ rfl, r18]) (by rw [g3, s1, sp2]) (by rw [g3, s2]; rfl)
  obtain ⟨M4, hM4⟩ : ∃ M4, copyWords M2 out (sp0 + 0xFFFFFFB0 + 4) 12 = M4 := ⟨_, rfl⟩
  rw [hM4] at u4
  have I4 : ∀ x, Sep out 48 x 1 → M4 x = M2 x := fun x hx => by rw [← hM4, copyWords_outside 12 hx]
  have hc4 : CodeIn M4 P montRetrieve12Code := fun i hi => by
    rw [I4 _ (E.sOC.subR (c := i) (l := 1) (by omega))]; exact hc2' i hi
  have k4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ ra → reg n4 q = reg n2 q := fun q q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qr => by
    rw [fr4 q q1 q2 q3 q4 q5 q6 q7 q8 q9 qr, g3, sk q q0 q1 q2]
  have sp4 : reg n4 sp = sp0 + 0xFFFFFFB0 := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), sp2]
  -- the saved slots
  have slot : ∀ r o, (r, o) ∈ mrPs → memLoad32 M4 (sp0 + 0xFFFFFFB0 + o) = reg m r := fun r o hm => by
    have hb : 0x34 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x50 := by
      simp only [mrPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    have hFo : sp0 + 0xFFFFFFB0 + BitVec.ofNat 32 o.toNat = sp0 + 0xFFFFFFB0 + o := by rw [ofNat_toNat_self]
    have h1 : Sep out (4 * 12) (sp0 + 0xFFFFFFB0 + o) 4 := by
      rw [← hFo]; exact E.sOG.subR (c := o.toNat) (l := 4) (by omega)
    have h2 : Sep (sp0 + 0xFFFFFFB0 + 4) 48 (sp0 + 0xFFFFFFB0 + o) 4 := by
      rw [← hFo]; exact sep_offsets _ (c := 4) (.inl (by omega)) (by omega) (by omega)
    rw [← hM4, copyWords_load_sep h1, load_frame hf2 h2]
    exact hsl1 r o hm
  have hpsp : ∀ p ∈ mrPs, p.1 ≠ sp := by decide
  obtain ⟨n6, c6, u6⟩ := St.block (restoreBlock mrPs) u4 hc4 mrRestore_end
    (restoreBlock_ok M4 (sp0 + 0xFFFFFFB0) mrPs (reg n4) sp4 hpsp fun q hq => by
      simp only [mrPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hGa (by decide))
  simp only [restoreBlock_run M4 (sp0 + 0xFFFFFFB0) mrPs (reg n4) sp4 hpsp] at u6
  have rsp6 : restoreRegs M4 (sp0 + 0xFFFFFFB0) (reg n4) mrPs sp = sp0 + 0xFFFFFFB0 := by
    rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp4
  obtain ⟨n7, d7, u7⟩ := u6.aluImm hc4 mr_at_bc (off' := 0xBE) (by decide)
  obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.jalr hc4 mr_at_be
  have rra : restoreRegs M4 (sp0 + 0xFFFFFFB0) (reg n4) mrPs ra = reg m ra := by
    simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
    exact slot ra _ (by decide)
  -- the value
  have hout : accV n8.mem out 12 = accV M2 (sp0 + 0xFFFFFFB0 + 4) 12 := by
    rw [mem8, ← hM4]
    exact accV_congr2 12 fun i hi => copyWords_load 12 i hi (by have := E.hwo; omega)
  obtain ⟨f1, f2⟩ := mr_final hUv hU
  refine ⟨n8, c1.trans (c2.trans (c3.trans (c4.trans (c6.trans (.cons d7 (.single d8)))))), ?_, ?_,
    by rw [hout]; exact f1, fun h => by rw [hout]; exact f2 h, fun x hx ho => ?_, fun q hq => ?_⟩
  · rw [pc8]; simp +decide only [upd, ↓reduceIte]; rw [rra, add_lit_zero, hra, hret]
  · rw [regs8]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [rsp6, BitVec.add_assoc]; exact BitVec.add_zero _
  · rw [mem8, I4 x ho, hf2G x hx]
  · have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
        restoreRegs M4 (sp0 + 0xFFFFFFB0) f ps q = f q := by
      intro f ps q hq0
      induction ps generalizing f with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro h
        simp only [restoreRegs]
        rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨
        q = (21 : Fin 32) ∨ (q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] ∧ mpKeep q = true ∧ q.val ≠ 0 ∧ q ≠ sp ∧
          q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ ra ∧
          (∀ p ∈ mrPs, p.1 ≠ q)) := by decide
    have hreg : ∀ r o, (r, o) ∈ mrPs → reg n8 r = reg m r := fun r o hm => by
      rw [regs8]
      simp only [mrPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
        exact slot _ _ (by decide)
    rcases key q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      ⟨h1, hp, h0, hsp', q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, qr, hps⟩
    · exact hreg _ 0x4C (by decide)
    · exact hreg _ 0x48 (by decide)
    · exact hreg _ 0x44 (by decide)
    · exact hreg _ 0x40 (by decide)
    · exact hreg _ 0x3C (by decide)
    · exact hreg _ 0x38 (by decide)
    · exact hreg _ 0x34 (by decide)
    · rw [regs8, upd_ne h0 hsp', rr _ _ q h0 hps, k4 q q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qr, k2 q hp, rk q h1]

end C3.RV32
