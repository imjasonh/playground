import C3BootProofs.Proofs.WideMulX2

/-!
# `widening_mul_fixed::<8, 2>`

`crypto_bigint`'s `widening_mul_fixed::<8, 2>`, as compiled: it zeroes a
10-word buffer on its stack (`memset` for the low 8 words, two stores for the
top two), adds each limb of the first operand times the second into it with
two multiply-accumulate steps and a carry store, and copies the buffer out
(`memcpy` for the low 8 words). `scripts`' template writes this file and the
other instance from the decoded instructions.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem k8_at_0 : fetchRel wideMul8x2Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFB0, 2) := by decide
theorem k8_at_2 : fetchRel wideMul8x2Code 0x2 = some (.store .sw sp ra 0x4C, 2) := by decide
theorem k8_at_4 : fetchRel wideMul8x2Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x48, 2) := by decide
theorem k8_at_6 : fetchRel wideMul8x2Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x44, 2) := by decide
theorem k8_at_8 : fetchRel wideMul8x2Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x40, 2) := by decide
theorem k8_at_a : fetchRel wideMul8x2Code 0xA = some (.store .sw sp (19 : Fin 32) 0x3C, 2) := by decide
theorem k8_at_c : fetchRel wideMul8x2Code 0xC = some (.store .sw sp (20 : Fin 32) 0x38, 2) := by decide
theorem k8_at_e : fetchRel wideMul8x2Code 0xE = some (.store .sw sp (21 : Fin 32) 0x34, 2) := by decide
theorem k8_at_10 : fetchRel wideMul8x2Code 0x10 = some (.alu .add (19 : Fin 32) x0 a2, 2) := by decide
theorem k8_at_12 : fetchRel wideMul8x2Code 0x12 = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem k8_at_14 : fetchRel wideMul8x2Code 0x14 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem k8_at_16 : fetchRel wideMul8x2Code 0x16 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem k8_at_18 : fetchRel wideMul8x2Code 0x18 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem k8_at_1c : fetchRel wideMul8x2Code 0x1C = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem k8_at_1e : fetchRel wideMul8x2Code 0x1E = some (.aluImm .add (21 : Fin 32) sp 0x8, 4) := by decide
theorem k8_at_22 : fetchRel wideMul8x2Code 0x22 = some (.auipc ra 0x3000, 4) := by decide
theorem k8_at_26 : fetchRel wideMul8x2Code 0x26 = some (.jalr ra ra 0x68A, 4) := by decide
theorem k8_at_2a : fetchRel wideMul8x2Code 0x2A = some (.aluImm .add (7 : Fin 32) x0 0x0, 2) := by decide
theorem k8_at_2c : fetchRel wideMul8x2Code 0x2C = some (.store .sw sp x0 0x28, 2) := by decide
theorem k8_at_2e : fetchRel wideMul8x2Code 0x2E = some (.store .sw sp x0 0x2C, 2) := by decide
theorem k8_at_30 : fetchRel wideMul8x2Code 0x30 = some (.aluImm .add (5 : Fin 32) sp 0x8, 4) := by decide
theorem k8_at_34 : fetchRel wideMul8x2Code 0x34 = some (.aluImm .add (17 : Fin 32) x0 0x8, 2) := by decide
theorem k8_at_36 : fetchRel wideMul8x2Code 0x36 = some (.aluImm .add a6 x0 0x6, 2) := by decide
theorem k8_at_38 : fetchRel wideMul8x2Code 0x38 = some (.aluImm .add (28 : Fin 32) x0 0x7, 2) := by decide
theorem k8_at_3a : fetchRel wideMul8x2Code 0x3A = some (.branch .beq (17 : Fin 32) x0 0x82, 4) := by decide
theorem k8_at_3e : fetchRel wideMul8x2Code 0x3E = some (.aluImm .add (29 : Fin 32) x0 0x0, 2) := by decide
theorem k8_at_40 : fetchRel wideMul8x2Code 0x40 = some (.aluImm .sll (6 : Fin 32) (7 : Fin 32) 0x2, 4) := by decide
theorem k8_at_44 : fetchRel wideMul8x2Code 0x44 = some (.alu .add a0 (20 : Fin 32) (6 : Fin 32), 4) := by decide
theorem k8_at_48 : fetchRel wideMul8x2Code 0x48 = some (.load .lw (30 : Fin 32) a0 0x0, 4) := by decide
theorem k8_at_4c : fetchRel wideMul8x2Code 0x4C = some (.aluImm .add (8 : Fin 32) x0 0x2, 2) := by decide
theorem k8_at_4e : fetchRel wideMul8x2Code 0x4E = some (.alu .add (9 : Fin 32) x0 (19 : Fin 32), 2) := by decide
theorem k8_at_50 : fetchRel wideMul8x2Code 0x50 = some (.alu .add a0 x0 (7 : Fin 32), 2) := by decide
theorem k8_at_52 : fetchRel wideMul8x2Code 0x52 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem k8_at_54 : fetchRel wideMul8x2Code 0x54 = some (.alu .add a5 x0 (5 : Fin 32), 2) := by decide
theorem k8_at_56 : fetchRel wideMul8x2Code 0x56 = some (.branch .beq (8 : Fin 32) x0 0x46, 2) := by decide
theorem k8_at_58 : fetchRel wideMul8x2Code 0x58 = some (.load .lw a3 (9 : Fin 32) 0x0, 2) := by decide
theorem k8_at_5a : fetchRel wideMul8x2Code 0x5A = some (.alu .mulhu a4 a3 (30 : Fin 32), 4) := by decide
theorem k8_at_5e : fetchRel wideMul8x2Code 0x5E = some (.alu .mul a3 a3 (30 : Fin 32), 4) := by decide
theorem k8_at_62 : fetchRel wideMul8x2Code 0x62 = some (.branch .bltu (28 : Fin 32) a0 0x1A, 4) := by decide
theorem k8_at_66 : fetchRel wideMul8x2Code 0x66 = some (.load .lw a2 a1 0x0, 2) := by decide
theorem k8_at_68 : fetchRel wideMul8x2Code 0x68 = some (.alu .add (29 : Fin 32) (29 : Fin 32) a2, 2) := by decide
theorem k8_at_6a : fetchRel wideMul8x2Code 0x6A = some (.alu .sltu a2 (29 : Fin 32) a2, 4) := by decide
theorem k8_at_6e : fetchRel wideMul8x2Code 0x6E = some (.alu .add a3 a3 (29 : Fin 32), 2) := by decide
theorem k8_at_70 : fetchRel wideMul8x2Code 0x70 = some (.alu .sltu (29 : Fin 32) a3 (29 : Fin 32), 4) := by decide
theorem k8_at_74 : fetchRel wideMul8x2Code 0x74 = some (.alu .add a2 a2 a4, 2) := by decide
theorem k8_at_76 : fetchRel wideMul8x2Code 0x76 = some (.alu .add (29 : Fin 32) (29 : Fin 32) a2, 2) := by decide
theorem k8_at_78 : fetchRel wideMul8x2Code 0x78 = some (.store .sw a1 a3 0x0, 2) := by decide
theorem k8_at_7a : fetchRel wideMul8x2Code 0x7A = some (.jal x0 0x16, 2) := by decide
theorem k8_at_7c : fetchRel wideMul8x2Code 0x7C = some (.load .lw a2 a5 0x0, 2) := by decide
theorem k8_at_7e : fetchRel wideMul8x2Code 0x7E = some (.alu .add (29 : Fin 32) (29 : Fin 32) a2, 2) := by decide
theorem k8_at_80 : fetchRel wideMul8x2Code 0x80 = some (.alu .sltu a2 (29 : Fin 32) a2, 4) := by decide
theorem k8_at_84 : fetchRel wideMul8x2Code 0x84 = some (.alu .add a3 a3 (29 : Fin 32), 2) := by decide
theorem k8_at_86 : fetchRel wideMul8x2Code 0x86 = some (.alu .sltu (29 : Fin 32) a3 (29 : Fin 32), 4) := by decide
theorem k8_at_8a : fetchRel wideMul8x2Code 0x8A = some (.alu .add a2 a2 a4, 2) := by decide
theorem k8_at_8c : fetchRel wideMul8x2Code 0x8C = some (.alu .add (29 : Fin 32) (29 : Fin 32) a2, 2) := by decide
theorem k8_at_8e : fetchRel wideMul8x2Code 0x8E = some (.store .sw a5 a3 0x0, 2) := by decide
theorem k8_at_90 : fetchRel wideMul8x2Code 0x90 = some (.aluImm .add a5 a5 0x4, 2) := by decide
theorem k8_at_92 : fetchRel wideMul8x2Code 0x92 = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem k8_at_94 : fetchRel wideMul8x2Code 0x94 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem k8_at_96 : fetchRel wideMul8x2Code 0x96 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem k8_at_98 : fetchRel wideMul8x2Code 0x98 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem k8_at_9a : fetchRel wideMul8x2Code 0x9A = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFBE, 2) := by decide
theorem k8_at_9c : fetchRel wideMul8x2Code 0x9C = some (.branch .bltu (7 : Fin 32) a6 0xA, 4) := by decide
theorem k8_at_a0 : fetchRel wideMul8x2Code 0xA0 = some (.aluImm .add a0 sp 0x28, 2) := by decide
theorem k8_at_a2 : fetchRel wideMul8x2Code 0xA2 = some (.aluImm .add a1 x0 0xFFFFFFE8, 2) := by decide
theorem k8_at_a4 : fetchRel wideMul8x2Code 0xA4 = some (.jal x0 0x6, 2) := by decide
theorem k8_at_a6 : fetchRel wideMul8x2Code 0xA6 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem k8_at_a8 : fetchRel wideMul8x2Code 0xA8 = some (.aluImm .add a1 x0 0x8, 2) := by decide
theorem k8_at_aa : fetchRel wideMul8x2Code 0xAA = some (.alu .add a0 a0 a1, 2) := by decide
theorem k8_at_ac : fetchRel wideMul8x2Code 0xAC = some (.alu .add a0 a0 (6 : Fin 32), 2) := by decide
theorem k8_at_ae : fetchRel wideMul8x2Code 0xAE = some (.aluImm .add (7 : Fin 32) (7 : Fin 32) 0x1, 2) := by decide
theorem k8_at_b0 : fetchRel wideMul8x2Code 0xB0 = some (.store .sw a0 (29 : Fin 32) 0x0, 4) := by decide
theorem k8_at_b4 : fetchRel wideMul8x2Code 0xB4 = some (.aluImm .add (5 : Fin 32) (5 : Fin 32) 0x4, 2) := by decide
theorem k8_at_b6 : fetchRel wideMul8x2Code 0xB6 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x4, 2) := by decide
theorem k8_at_b8 : fetchRel wideMul8x2Code 0xB8 = some (.branch .bne (7 : Fin 32) (17 : Fin 32) 0xFFFFFF86, 4) := by decide
theorem k8_at_bc : fetchRel wideMul8x2Code 0xBC = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem k8_at_be : fetchRel wideMul8x2Code 0xBE = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem k8_at_c2 : fetchRel wideMul8x2Code 0xC2 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem k8_at_c4 : fetchRel wideMul8x2Code 0xC4 = some (.auipc ra 0x3000, 4) := by decide
theorem k8_at_c8 : fetchRel wideMul8x2Code 0xC8 = some (.jalr ra ra 0x650, 4) := by decide
theorem k8_at_cc : fetchRel wideMul8x2Code 0xCC = some (.load .lw a0 sp 0x28, 2) := by decide
theorem k8_at_ce : fetchRel wideMul8x2Code 0xCE = some (.load .lw a1 sp 0x2C, 2) := by decide
theorem k8_at_d0 : fetchRel wideMul8x2Code 0xD0 = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem k8_at_d2 : fetchRel wideMul8x2Code 0xD2 = some (.store .sw a2 a0 0x20, 2) := by decide
theorem k8_at_d4 : fetchRel wideMul8x2Code 0xD4 = some (.store .sw a2 a1 0x24, 2) := by decide
theorem k8_at_d6 : fetchRel wideMul8x2Code 0xD6 = some (.load .lw ra sp 0x4C, 2) := by decide
theorem k8_at_d8 : fetchRel wideMul8x2Code 0xD8 = some (.load .lw (8 : Fin 32) sp 0x48, 2) := by decide
theorem k8_at_da : fetchRel wideMul8x2Code 0xDA = some (.load .lw (9 : Fin 32) sp 0x44, 2) := by decide
theorem k8_at_dc : fetchRel wideMul8x2Code 0xDC = some (.load .lw (18 : Fin 32) sp 0x40, 2) := by decide
theorem k8_at_de : fetchRel wideMul8x2Code 0xDE = some (.load .lw (19 : Fin 32) sp 0x3C, 2) := by decide
theorem k8_at_e0 : fetchRel wideMul8x2Code 0xE0 = some (.load .lw (20 : Fin 32) sp 0x38, 2) := by decide
theorem k8_at_e2 : fetchRel wideMul8x2Code 0xE2 = some (.load .lw (21 : Fin 32) sp 0x34, 2) := by decide
theorem k8_at_e4 : fetchRel wideMul8x2Code 0xE4 = some (.aluImm .add sp sp 0x50, 2) := by decide
theorem k8_at_e6 : fetchRel wideMul8x2Code 0xE6 = some (.jalr x0 ra 0x0, 2) := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- One multiply-accumulate step of `widening_mul_fixed::<8, 2>`'s inner
loop, from 0x58 to 0x9A: the word at `Wk` becomes `kmWord` of the second
operand's limb at `Ya`, the first operand's limb `xi`, the word, and the
carry `t`, and `t4` holds the new carry. Both of the compiled paths (for the
low words and for the top two) store at `Wk`, which `a1` and `a5` both hold. -/
theorem k8_step {M : Word → BitVec 8} {P : Word} (hP : P.toNat % 2 = 0) (hc : CodeIn M P wideMul8x2Code) {n : Machine}
    (s : St M P n 0x58 (reg n)) {Ya Wk xi t : Word} {k : Nat} (hk : k + 1 < 2 ^ 32)
    (h9 : reg n (9 : Fin 32) = Ya) (h30 : reg n (30 : Fin 32) = xi) (h29 : reg n (29 : Fin 32) = t)
    (ha0 : reg n a0 = BitVec.ofNat 32 k) (ha1 : reg n a1 = Wk) (ha5 : reg n a5 = Wk)
    (h28 : reg n (28 : Fin 32) = BitVec.ofNat 32 7) (hYa : Ya.toNat % 4 = 0) (hWk : Wk.toNat % 4 = 0)
    (sWC : Sep Wk 4 P wideMul8x2Code.length) :
    ∃ n', Steps n n' ∧ St (memStore32 M Wk (kmWord (memLoad32 M Ya) xi (memLoad32 M Wk) t)) P n' 0x9A (reg n') ∧
      reg n' (29 : Fin 32) = kmCarry (memLoad32 M Ya) xi (memLoad32 M Wk) t ∧
      reg n' a0 = BitVec.ofNat 32 (k + 1) ∧ reg n' a1 = Wk + 4 ∧ reg n' a5 = Wk + 4 ∧
      reg n' (9 : Fin 32) = Ya + 4 ∧ reg n' (8 : Fin 32) = reg n (8 : Fin 32) + 0xFFFFFFFF ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) →
        q ≠ (29 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨Y, hY⟩ : ∃ v, memLoad32 M Ya = v := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ v, memLoad32 M Wk = v := ⟨_, rfl⟩
  obtain ⟨n1, d1, u1⟩ := s.lwE hc k8_at_58 (off' := 0x5A) (by decide) (by rw [h9, add_lit_zero]; exact hYa)
    (v := Y) (by rw [h9, add_lit_zero, hY])
  have k1 := u1.oldReg hz
  obtain ⟨n2, d2, u2⟩ := u1.self.alu hc k8_at_5a (off' := 0x5E) (by decide)
  have k2 := u2.oldReg u1.self.zero
  obtain ⟨n3, d3, u3⟩ := u2.self.alu hc k8_at_5e (off' := 0x62) (by decide)
  have k3 := u3.oldReg u2.self.zero
  have a3_3 : reg n3 a3 = aluEval .mul Y xi := by
    rw [u3.newReg (by decide), k2 _ (by decide), u1.newReg (by decide), k2 _ (by decide), k1 _ (by decide), h30]
  have a4_3 : reg n3 a4 = aluEval .mulhu Y xi := by
    rw [k3 _ (by decide), u2.newReg (by decide), u1.newReg (by decide), k1 _ (by decide), h30]
  have back3 : ∀ q, q ≠ a3 → q ≠ a4 → reg n3 q = reg n q := fun q h3 h4 => by rw [k3 q h3, k2 q h4, k1 q h3]
  -- the two paths, for the low words and for the top two
  obtain ⟨nT, cT, uT, t29, tK⟩ : ∃ nT, Steps n3 nT ∧
      St (memStore32 M Wk (kmWord Y xi w t)) P nT 0x90 (reg nT) ∧ reg nT (29 : Fin 32) = kmCarry Y xi w t ∧
      ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (29 : Fin 32) → reg nT q = reg n3 q := by
    have hal : ∀ r : Fin 32, r ≠ a3 → r ≠ a4 → reg n r = Wk → (reg n3 r + 0).toNat % 4 = 0 := fun r h3 h4 h => by
      rw [back3 r h3 h4, h, add_lit_zero]; exact hWk
    have hsc : Sep Wk 4 P wideMul8x2Code.length := sWC
    by_cases hb : 7 < k
    · obtain ⟨m4, e4, v4⟩ := u3.self.taken hc 0x7C k8_at_62 (by decide) (by
        simp only [branchTaken]
        rw [back3 _ (by decide) (by decide), back3 _ (by decide) (by decide), h28, ha0, ult_lit (by decide) (by omega)]
        exact decide_eq_true hb)
      have p : ∀ q, reg m4 q = reg n3 q := v4.regs
      obtain ⟨m5, e5, v5⟩ := v4.self.lwE hc k8_at_7c (off' := 0x7E) (by decide)
        (by rw [p, hal a5 (by decide) (by decide) ha5]) (v := w)
        (by rw [p, back3 _ (by decide) (by decide), ha5, add_lit_zero, hw])
      have j5 := v5.oldReg v4.self.zero
      obtain ⟨m6, e6, v6⟩ := v5.self.alu hc k8_at_7e (off' := 0x80) (by decide)
      have j6 := v6.oldReg v5.self.zero
      obtain ⟨m7, e7, v7⟩ := v6.self.alu hc k8_at_80 (off' := 0x84) (by decide)
      have j7 := v7.oldReg v6.self.zero
      obtain ⟨m8, e8, v8⟩ := v7.self.alu hc k8_at_84 (off' := 0x86) (by decide)
      have j8 := v8.oldReg v7.self.zero
      obtain ⟨m9, e9, v9⟩ := v8.self.alu hc k8_at_86 (off' := 0x8A) (by decide)
      have j9 := v9.oldReg v8.self.zero
      obtain ⟨m10, e10, v10⟩ := v9.self.alu hc k8_at_8a (off' := 0x8C) (by decide)
      have j10 := v10.oldReg v9.self.zero
      obtain ⟨m11, e11, v11⟩ := v10.self.alu hc k8_at_8c (off' := 0x8E) (by decide)
      have j11 := v11.oldReg v10.self.zero
      have t6 : reg m6 (29 : Fin 32) = aluEval .add t w := by
        rw [v6.newReg (by decide), j5 _ (by decide), p, back3 _ (by decide) (by decide), h29, v5.newReg (by decide)]
      have a2_7 : reg m7 a2 = aluEval .sltu (aluEval .add t w) w := by
        rw [v7.newReg (by decide), t6, j6 _ (by decide), v5.newReg (by decide)]
      have a3_8 : reg m8 a3 = kmWord Y xi w t := by
        rw [v8.newReg (by decide), j7 _ (by decide), j6 _ (by decide), j5 _ (by decide), p, a3_3, j7 _ (by decide), t6]
      have t9 : reg m9 (29 : Fin 32) = aluEval .sltu (kmWord Y xi w t) (aluEval .add t w) := by
        rw [v9.newReg (by decide), a3_8, j8 _ (by decide), j7 _ (by decide), t6]
      have a2_10 : reg m10 a2 = aluEval .add (aluEval .sltu (aluEval .add t w) w) (aluEval .mulhu Y xi) := by
        rw [v10.newReg (by decide), j9 _ (by decide), j8 _ (by decide), a2_7, j9 _ (by decide), j8 _ (by decide),
          j7 _ (by decide), j6 _ (by decide), j5 _ (by decide), p, a4_3]
      have t11 : reg m11 (29 : Fin 32) = kmCarry Y xi w t := by
        rw [v11.newReg (by decide), j10 _ (by decide), t9, a2_10]
      have back11 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (29 : Fin 32) → reg m11 q = reg n3 q :=
        fun q h2 h3 h4 h29' => by
          rw [j11 q h29', j10 q h2, j9 q h29', j8 q h3, j7 q h2, j6 q h29', j5 q h2, p]
      obtain ⟨m12, e12, v12⟩ := v11.self.swG hc k8_at_8e (off' := 0x90) (by decide)
        (by rw [back11 _ (by decide) (by decide) (by decide) (by decide), hal a5 (by decide) (by decide) ha5])
        (a := Wk) (v := kmWord Y xi w t)
        (by rw [back11 _ (by decide) (by decide) (by decide) (by decide), back3 _ (by decide) (by decide), ha5,
          add_lit_zero])
        (by rw [j11 _ (by decide), j10 _ (by decide), j9 _ (by decide), a3_8])
      exact ⟨m12, .cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (.cons e9 (.cons e10 (.cons e11 (.single e12)))))))),
        v12.self, by rw [v12.regs, t11], fun q h2 h3 h4 h29' => by rw [v12.regs, back11 q h2 h3 h4 h29']⟩
    · obtain ⟨m4, e4, v4⟩ := u3.self.notTaken hc 0x66 k8_at_62 (by decide) (by
        simp only [branchTaken]
        rw [back3 _ (by decide) (by decide), back3 _ (by decide) (by decide), h28, ha0, ult_lit (by decide) (by omega)]
        exact decide_eq_false hb)
      have p : ∀ q, reg m4 q = reg n3 q := v4.regs
      obtain ⟨m5, e5, v5⟩ := v4.self.lwE hc k8_at_66 (off' := 0x68) (by decide)
        (by rw [p, hal a1 (by decide) (by decide) ha1]) (v := w)
        (by rw [p, back3 _ (by decide) (by decide), ha1, add_lit_zero, hw])
      have j5 := v5.oldReg v4.self.zero
      obtain ⟨m6, e6, v6⟩ := v5.self.alu hc k8_at_68 (off' := 0x6A) (by decide)
      have j6 := v6.oldReg v5.self.zero
      obtain ⟨m7, e7, v7⟩ := v6.self.alu hc k8_at_6a (off' := 0x6E) (by decide)
      have j7 := v7.oldReg v6.self.zero
      obtain ⟨m8, e8, v8⟩ := v7.self.alu hc k8_at_6e (off' := 0x70) (by decide)
      have j8 := v8.oldReg v7.self.zero
      obtain ⟨m9, e9, v9⟩ := v8.self.alu hc k8_at_70 (off' := 0x74) (by decide)
      have j9 := v9.oldReg v8.self.zero
      obtain ⟨m10, e10, v10⟩ := v9.self.alu hc k8_at_74 (off' := 0x76) (by decide)
      have j10 := v10.oldReg v9.self.zero
      obtain ⟨m11, e11, v11⟩ := v10.self.alu hc k8_at_76 (off' := 0x78) (by decide)
      have j11 := v11.oldReg v10.self.zero
      have t6 : reg m6 (29 : Fin 32) = aluEval .add t w := by
        rw [v6.newReg (by decide), j5 _ (by decide), p, back3 _ (by decide) (by decide), h29, v5.newReg (by decide)]
      have a2_7 : reg m7 a2 = aluEval .sltu (aluEval .add t w) w := by
        rw [v7.newReg (by decide), t6, j6 _ (by decide), v5.newReg (by decide)]
      have a3_8 : reg m8 a3 = kmWord Y xi w t := by
        rw [v8.newReg (by decide), j7 _ (by decide), j6 _ (by decide), j5 _ (by decide), p, a3_3, j7 _ (by decide), t6]
      have t9 : reg m9 (29 : Fin 32) = aluEval .sltu (kmWord Y xi w t) (aluEval .add t w) := by
        rw [v9.newReg (by decide), a3_8, j8 _ (by decide), j7 _ (by decide), t6]
      have a2_10 : reg m10 a2 = aluEval .add (aluEval .sltu (aluEval .add t w) w) (aluEval .mulhu Y xi) := by
        rw [v10.newReg (by decide), j9 _ (by decide), j8 _ (by decide), a2_7, j9 _ (by decide), j8 _ (by decide),
          j7 _ (by decide), j6 _ (by decide), j5 _ (by decide), p, a4_3]
      have t11 : reg m11 (29 : Fin 32) = kmCarry Y xi w t := by
        rw [v11.newReg (by decide), j10 _ (by decide), t9, a2_10]
      have back11 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (29 : Fin 32) → reg m11 q = reg n3 q :=
        fun q h2 h3 h4 h29' => by
          rw [j11 q h29', j10 q h2, j9 q h29', j8 q h3, j7 q h2, j6 q h29', j5 q h2, p]
      obtain ⟨m12, e12, v12⟩ := v11.self.swG hc k8_at_78 (off' := 0x7A) (by decide)
        (by rw [back11 _ (by decide) (by decide) (by decide) (by decide), hal a1 (by decide) (by decide) ha1])
        (a := Wk) (v := kmWord Y xi w t)
        (by rw [back11 _ (by decide) (by decide) (by decide) (by decide), back3 _ (by decide) (by decide), ha1,
          add_lit_zero])
        (by rw [j11 _ (by decide), j10 _ (by decide), j9 _ (by decide), a3_8])
      obtain ⟨m13, e13, v13⟩ := v12.self.jump (hc.store32 sWC) k8_at_7a (off' := 0x90) (by decide)
        (pc_even (off := 0x7A) (off' := 0x90) hP v12.self.pc (by decide) (by decide))
      exact ⟨m13, .cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (.cons e9 (.cons e10 (.cons e11 (.cons e12
        (.single e13))))))))), v13.self, by rw [v13.regs, v12.regs, t11],
        fun q h2 h3 h4 h29' => by rw [v13.regs, v12.regs, back11 q h2 h3 h4 h29']⟩
  -- 0x90..0x98: advance the pointers, the index, and the count
  have hcT : CodeIn (memStore32 M Wk (kmWord Y xi w t)) P wideMul8x2Code := hc.store32 sWC
  obtain ⟨g1, f1, w1⟩ := uT.aluImm hcT k8_at_90 (off' := 0x92) (by decide)
  obtain ⟨g2, f2, w2⟩ := w1.self.aluImm hcT k8_at_92 (off' := 0x94) (by decide)
  obtain ⟨g3, f3, w3⟩ := w2.self.aluImm hcT k8_at_94 (off' := 0x96) (by decide)
  obtain ⟨g4, f4, w4⟩ := w3.self.aluImm hcT k8_at_96 (off' := 0x98) (by decide)
  obtain ⟨g5, f5, w5⟩ := w4.self.aluImm hcT k8_at_98 (off' := 0x9A) (by decide)
  have q1 := w1.oldReg uT.zero
  have q2 := w2.oldReg w1.self.zero
  have q3 := w3.oldReg w2.self.zero
  have q4 := w4.oldReg w3.self.zero
  have q5 := w5.oldReg w4.self.zero
  have backT : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (29 : Fin 32) → reg nT q = reg n q := fun q h2 h3 h4 h29' => by
    rw [tK q h2 h3 h4 h29']
    by_cases e3 : q = a3
    · exact absurd e3 h3
    · rw [back3 q h3 h4]
  subst hY hw
  refine ⟨g5, .cons d1 (.cons d2 (.cons d3 (cT.trans (.cons f1 (.cons f2 (.cons f3 (.cons f4 (.single f5)))))))),
    w5.self, ?_, ?_, ?_, ?_, ?_, ?_, fun q h0 h1 h2 h3 h4 h5 h8 h9 h29' => ?_⟩
  · rw [q5 _ (by decide), q4 _ (by decide), q3 _ (by decide), q2 _ (by decide), q1 _ (by decide), t29]
  · rw [q5 _ (by decide), q4 _ (by decide), w3.newReg (by decide)]; show reg g2 a0 + 0x1 = _
    rw [q2 _ (by decide), q1 _ (by decide), backT _ (by decide) (by decide) (by decide) (by decide), ha0]
    exact ofNat_add_lit k 1
  · rw [q5 _ (by decide), q4 _ (by decide), q3 _ (by decide), w2.newReg (by decide)]; show reg g1 a1 + 0x4 = _
    rw [q1 _ (by decide), backT _ (by decide) (by decide) (by decide) (by decide), ha1]
  · rw [q5 _ (by decide), q4 _ (by decide), q3 _ (by decide), q2 _ (by decide), w1.newReg (by decide)]
    show reg nT a5 + 0x4 = _
    rw [backT _ (by decide) (by decide) (by decide) (by decide), ha5]
  · rw [q5 _ (by decide), w4.newReg (by decide)]; show reg g3 (9 : Fin 32) + 0x4 = _
    rw [q3 _ (by decide), q2 _ (by decide), q1 _ (by decide), backT _ (by decide) (by decide) (by decide) (by decide),
      h9]
  · rw [w5.newReg (by decide)]; show reg g4 (8 : Fin 32) + 0xFFFFFFFF = _
    rw [q4 _ (by decide), q3 _ (by decide), q2 _ (by decide), q1 _ (by decide),
      backT _ (by decide) (by decide) (by decide) (by decide)]
  · rw [q5 q h8, q4 q h9, q3 q h0, q2 q h1, q1 q h5, backT q h2 h3 h4 h29']


set_option maxRecDepth 40000 in
set_option maxHeartbeats 40000000 in
/-- The rows of `widening_mul_fixed::<8, 2>`, from 0x3E with `i` rows done:
the buffer at `F + 8` holds the first `i` limbs' product in its low `i + 2`
words and zeros above. It reaches 0xBC with all 8 rows done. -/
theorem k8_rows {Mb : Word → BitVec 8} {P F xp yp : Word} (hP : P.toNat % 2 = 0) (hc : CodeIn Mb P wideMul8x2Code)
    (hF : F.toNat % 4 = 0) (hFt : F.toNat + 48 ≤ 2 ^ 32) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sWC : Sep (F + 8) 40 P wideMul8x2Code.length) (sWX : Sep (F + 8) 40 xp 32) (sWY : Sep (F + 8) 40 yp 8) :
    ∀ r i (n : Machine) (Mi : Word → BitVec 8), i + r = 8 → 0 < r → St Mi P n 0x3E (reg n) →
      reg n (7 : Fin 32) = BitVec.ofNat 32 i → reg n (20 : Fin 32) = xp → reg n (19 : Fin 32) = yp →
      reg n (21 : Fin 32) = F + 8 + BitVec.ofNat 32 (4 * i) → reg n (5 : Fin 32) = F + 8 + BitVec.ofNat 32 (4 * i) →
      reg n (17 : Fin 32) = BitVec.ofNat 32 8 → reg n a6 = BitVec.ofNat 32 6 →
      reg n (28 : Fin 32) = BitVec.ofNat 32 7 → reg n sp = F →
      accV Mi (F + 8) (i + 2) = accV Mb xp i * accV Mb yp 2 →
      (∀ k, i + 2 ≤ k → k < 10 → memLoad32 Mi (F + 8 + BitVec.ofNat 32 (4 * k)) = 0) →
      (∀ x, Sep (F + 8) 40 x 1 → Mi x = Mb x) →
      ∃ n' M', Steps n n' ∧ St M' P n' 0xBC (reg n') ∧
        accV M' (F + 8) 10 = accV Mb xp 8 * accV Mb yp 2 ∧ (∀ x, Sep (F + 8) 40 x 1 → M' x = Mb x) ∧
        ∀ q : Fin 32, q.val ∉ [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 21, 29, 30] → reg n' q = reg n q := by
  intro r
  induction r with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ r ih =>
    intro i n Mi hir _ s h7 h20 h19 h21 h5 h17 h16 h28 hsp hacc hzero hfr
    have hcI : CodeIn Mi P wideMul8x2Code := fun j hj => by
      rw [hfr _ (sWC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    have hz := s.zero
    have hi : i < 8 := by omega
    have hW : (F + 8).toNat = F.toNat + 8 := by
      rw [BitVec.toNat_add, show (8 : Word).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
    have hWa : ∀ k, (F + 8 + BitVec.ofNat 32 (4 * k)).toNat % 4 = 0 := fun k =>
      aligned_add (by rw [hW]; omega) (by omega)
    have sWk : ∀ k, k < 10 → Sep (F + 8 + BitVec.ofNat 32 (4 * k)) 4 P wideMul8x2Code.length := fun k hk =>
      sWC.sub (c := 4 * k) (l := 4) (by omega)
    have sKK : ∀ a b, a < 10 → b < 10 → a ≠ b →
        Sep (F + 8 + BitVec.ofNat 32 (4 * a)) 4 (F + 8 + BitVec.ofNat 32 (4 * b)) 4 := fun a b ha hb hab =>
      sep_offsets (F + 8) (by omega) (by omega) (by omega)
    have sKY : ∀ a d, a < 10 → d + 4 ≤ 8 → Sep (F + 8 + BitVec.ofNat 32 (4 * a)) 4 (yp + BitVec.ofNat 32 d) 4 :=
      fun a d ha hd => (sWY.sub (c := 4 * a) (l := 4) (by omega)).subR (c := d) (l := 4) hd
    -- 0x3E..0x56: the row's limb of the first operand, and the pointers
    obtain ⟨n1, d1, u1⟩ := s.aluImm hcI k8_at_3e (off' := 0x40) (by decide)
    have k1 := u1.oldReg hz
    obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hcI k8_at_40 (off' := 0x44) (by decide)
    have k2 := u2.oldReg u1.self.zero
    have t1_2 : reg n2 (6 : Fin 32) = BitVec.ofNat 32 (4 * i) := by
      rw [u2.newReg (by decide), k1 _ (by decide), h7]; exact km_sll2 i (by omega)
    obtain ⟨n3, d3, u3⟩ := u2.self.alu hcI k8_at_44 (off' := 0x48) (by decide)
    have k3 := u3.oldReg u2.self.zero
    have a0_3 : reg n3 a0 = xp + BitVec.ofNat 32 (4 * i) := by
      rw [u3.newReg (by decide), k2 _ (by decide), k1 _ (by decide), h20, t1_2]; rfl
    obtain ⟨xi, hxi⟩ : ∃ v, memLoad32 Mb (xp + BitVec.ofNat 32 (4 * i)) = v := ⟨_, rfl⟩
    obtain ⟨n4, d4, u4⟩ := u3.self.lwE hcI k8_at_48 (off' := 0x4C) (by decide)
      (by rw [a0_3, add_lit_zero]; exact aligned_add hx (by omega)) (v := xi)
      (by rw [a0_3, add_lit_zero, load_frame hfr (sWX.subR (c := 4 * i) (l := 4) (by omega)), hxi])
    have k4 := u4.oldReg u3.self.zero
    obtain ⟨n5, d5, u5⟩ := u4.self.aluImm hcI k8_at_4c (off' := 0x4E) (by decide)
    have k5 := u5.oldReg u4.self.zero
    obtain ⟨n6, d6, u6⟩ := u5.self.alu hcI k8_at_4e (off' := 0x50) (by decide)
    have k6 := u6.oldReg u5.self.zero
    obtain ⟨n7, d7, u7⟩ := u6.self.alu hcI k8_at_50 (off' := 0x52) (by decide)
    have k7 := u7.oldReg u6.self.zero
    obtain ⟨n8, d8, u8⟩ := u7.self.alu hcI k8_at_52 (off' := 0x54) (by decide)
    have k8 := u8.oldReg u7.self.zero
    obtain ⟨n9, d9, u9⟩ := u8.self.alu hcI k8_at_54 (off' := 0x56) (by decide)
    have k9 := u9.oldReg u8.self.zero
    have back9 : ∀ q : Fin 32, q.val ∉ [29, 6, 10, 30, 8, 9, 11, 15] → reg n9 q = reg n q := fun q hq => by
      have nq : ∀ r : Fin 32, r.val ∈ [29, 6, 10, 30, 8, 9, 11, 15] → q ≠ r := fun r hr e => by subst e; exact hq hr
      rw [k9 q (nq _ (by decide)), k8 q (nq _ (by decide)), k7 q (nq _ (by decide)), k6 q (nq _ (by decide)),
        k5 q (nq _ (by decide)), k4 q (nq _ (by decide)), k3 q (nq _ (by decide)), k2 q (nq _ (by decide)),
        k1 q (nq _ (by decide))]
    have s0_9 : reg n9 (8 : Fin 32) = 0x2 := by
      rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), u5.newReg (by decide)]
      show reg n4 0 + 0x2 = _; rw [u4.self.zero]; rfl
    have s1_9 : reg n9 (9 : Fin 32) = yp := by
      rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), u6.newReg (by decide)]
      show reg n5 0 + reg n5 (19 : Fin 32) = _
      rw [u5.self.zero, k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), h19]
      exact BitVec.zero_add _
    have a0_9 : reg n9 a0 = BitVec.ofNat 32 i := by
      rw [k9 _ (by decide), k8 _ (by decide), u7.newReg (by decide)]; show reg n6 0 + reg n6 (7 : Fin 32) = _
      rw [u6.self.zero, k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide),
        k1 _ (by decide), h7]
      exact BitVec.zero_add _
    have a1_9 : reg n9 a1 = F + 8 + BitVec.ofNat 32 (4 * i) := by
      rw [k9 _ (by decide), u8.newReg (by decide)]; show reg n7 0 + reg n7 (21 : Fin 32) = _
      rw [u7.self.zero, k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide),
        k2 _ (by decide), k1 _ (by decide), h21]
      exact BitVec.zero_add _
    have a5_9 : reg n9 a5 = F + 8 + BitVec.ofNat 32 (4 * i) := by
      rw [u9.newReg (by decide)]; show reg n8 0 + reg n8 (5 : Fin 32) = _
      rw [u8.self.zero, k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), k4 _ (by decide),
        k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), h5]
      exact BitVec.zero_add _
    have t5_9 : reg n9 (30 : Fin 32) = xi := by
      rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide),
        u4.newReg (by decide)]
    have t4_9 : reg n9 (29 : Fin 32) = 0 := by
      rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), k4 _ (by decide),
        k3 _ (by decide), k2 _ (by decide), u1.newReg (by decide)]
      show reg n 0 + 0x0 = _; rw [hz]; rfl
    have t1_9 : reg n9 (6 : Fin 32) = BitVec.ofNat 32 (4 * i) := by
      rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), k4 _ (by decide),
        k3 _ (by decide), t1_2]
    obtain ⟨n10, d10, u10⟩ := u9.self.notTaken hcI 0x58 k8_at_56 (by decide) (by
      simp only [branchTaken, s0_9, u9.self.zero]; decide)
    -- the two multiply-accumulate steps
    obtain ⟨y0, hy0⟩ : ∃ v, memLoad32 Mb yp = v := ⟨_, rfl⟩
    obtain ⟨y1, hy1⟩ : ∃ v, memLoad32 Mb (yp + 4) = v := ⟨_, rfl⟩
    obtain ⟨w0, hw0⟩ : ∃ v, memLoad32 Mi (F + 8 + BitVec.ofNat 32 (4 * i)) = v := ⟨_, rfl⟩
    obtain ⟨w1, hw1⟩ : ∃ v, memLoad32 Mi (F + 8 + BitVec.ofNat 32 (4 * (i + 1))) = v := ⟨_, rfl⟩
    have hy0' : memLoad32 Mi yp = y0 := by
      rw [← hy0]; exact load_frame hfr (by have := sWY.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)
    obtain ⟨sA, cA, uA, c0A, a0A, a1A, a5A, s9A, s8A, kkA⟩ := k8_step hP hcI u10.self (Ya := yp)
      (Wk := F + 8 + BitVec.ofNat 32 (4 * i)) (xi := xi) (t := 0) (k := i) (by omega)
      (by rw [u10.regs, s1_9]) (by rw [u10.regs, t5_9]) (by rw [u10.regs, t4_9]) (by rw [u10.regs, a0_9])
      (by rw [u10.regs, a1_9]) (by rw [u10.regs, a5_9]) (by rw [u10.regs, back9 _ (by decide), h28]) hy (hWa i)
      (sWk i (by omega))
    rw [hy0', hw0] at uA c0A
    obtain ⟨M1, hM1⟩ : ∃ M, memStore32 Mi (F + 8 + BitVec.ofNat 32 (4 * i)) (kmWord y0 xi w0 0) = M := ⟨_, rfl⟩
    rw [hM1] at uA
    have hc1 : CodeIn M1 P wideMul8x2Code := by rw [← hM1]; exact hcI.store32 (sWk i (by omega))
    have s8A' : reg sA (8 : Fin 32) = 0x1 := by rw [s8A, u10.regs, s0_9]; rfl
    obtain ⟨n11, d11, u11⟩ := uA.taken hc1 0x58 k8_at_9a (by decide) (by
      simp only [branchTaken, s8A', uA.zero]; decide)
    have hy1' : memLoad32 M1 (yp + 4) = y1 := by
      have e : (yp + 4 : Word) = yp + BitVec.ofNat 32 4 := rfl
      rw [← hM1, e, memLoad32_store32_sep (sKY i 4 (by omega) (by decide)), ← e, ← hy1]
      exact load_frame hfr (sWY.subR (c := 4) (l := 4) (by decide))
    have hw1' : memLoad32 M1 (F + 8 + BitVec.ofNat 32 (4 * (i + 1))) = w1 := by
      rw [← hM1, memLoad32_store32_sep (sKK i (i + 1) (by omega) (by omega) (by omega)), hw1]
    obtain ⟨sB, cB, uB, c0B, a0B, a1B, a5B, s9B, s8B, kkB⟩ := k8_step hP hc1 u11.self (Ya := yp + 4)
      (Wk := F + 8 + BitVec.ofNat 32 (4 * (i + 1))) (xi := xi) (t := kmCarry y0 xi w0 0) (k := i + 1) (by omega)
      (by rw [u11.regs, s9A])
      (by rw [u11.regs, kkA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), u10.regs, t5_9])
      (by rw [u11.regs, c0A]) (by rw [u11.regs, a0A])
      (by rw [u11.regs, a1A, km_add4]) (by rw [u11.regs, a5A, km_add4])
      (by rw [u11.regs, kkA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), u10.regs, back9 _ (by decide), h28])
      (aligned_add hy (k := 4) (by decide)) (hWa (i + 1)) (sWk (i + 1) (by omega))
    rw [hy1', hw1'] at uB c0B
    obtain ⟨M2, hM2⟩ : ∃ M, memStore32 M1 (F + 8 + BitVec.ofNat 32 (4 * (i + 1)))
        (kmWord y1 xi w1 (kmCarry y0 xi w0 0)) = M := ⟨_, rfl⟩
    rw [hM2] at uB
    have hc2 : CodeIn M2 P wideMul8x2Code := by rw [← hM2]; exact hc1.store32 (sWk (i + 1) (by omega))
    have s8B' : reg sB (8 : Fin 32) = 0x0 := by rw [s8B, u11.regs, s8A']; rfl
    obtain ⟨n12, d12, u12⟩ := uB.notTaken hc2 0x9C k8_at_9a (by decide) (by
      simp only [branchTaken, s8B', uB.zero]; decide)
    have kAB : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) →
        q ≠ (29 : Fin 32) → reg n12 q = reg n10 q := fun q h0 h1 h2 h3 h4 h5 h8 h9 h29 => by
      rw [u12.regs, kkB q h0 h1 h2 h3 h4 h5 h8 h9 h29, u11.regs, kkA q h0 h1 h2 h3 h4 h5 h8 h9 h29]
    have t2_12 : reg n12 (7 : Fin 32) = BitVec.ofNat 32 i := by
      rw [kAB _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), u10.regs, back9 _ (by decide), h7]
    have sub9 : ∀ q : Fin 32, q.val ∈ [29, 6, 10, 30, 8, 9, 11, 15] →
        q.val ∈ [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 21, 29, 30] := by decide
    have bk12 : ∀ q : Fin 32, q.val ∉ [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 21, 29, 30] → reg n12 q = reg n q :=
      fun q hq => by
        have nq : ∀ r : Fin 32, r.val ∈ [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 21, 29, 30] → q ≠ r :=
          fun r hr e => by subst e; exact hq hr
        rw [kAB q (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide))
          (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)), u10.regs,
          back9 q (fun h => hq (sub9 q h))]
    -- 0x9C: the carry's address, `F + 8 + 4 (i + 2)` on both paths
    obtain ⟨nA, cA', uA', a01A, kA⟩ : ∃ nA, Steps n12 nA ∧ St M2 P nA 0xAA (reg nA) ∧
        aluEval .add (reg nA a0) (reg nA a1) = F + 0x10 ∧ ∀ q, q ≠ a0 → q ≠ a1 → reg nA q = reg n12 q := by
      have sp12 : reg n12 sp = F := by rw [bk12 _ (by decide), hsp]
      by_cases hlt : i < 6
      · obtain ⟨m1, e1, v1⟩ := u12.self.taken hc2 0xA6 k8_at_9c (by decide) (by
          simp only [branchTaken]; rw [t2_12, bk12 _ (by decide), h16, ult_lit (by omega) (by decide)]
          exact decide_eq_true hlt)
        obtain ⟨m2, e2, v2⟩ := v1.self.aluImm hc2 k8_at_a6 (off' := 0xA8) (by decide)
        obtain ⟨m3, e3, v3⟩ := v2.self.aluImm hc2 k8_at_a8 (off' := 0xAA) (by decide)
        refine ⟨m3, .cons e1 (.cons e2 (.single e3)), v3.self, ?_, fun q h0 h1 => ?_⟩
        · rw [v3.newReg (by decide), v3.oldReg v2.self.zero _ (by decide), v2.newReg (by decide)]
          show reg m1 sp + 0x8 + (reg m2 0 + 0x8) = _
          rw [v1.regs, sp12, v2.self.zero, BitVec.add_assoc]; rfl
        · rw [v3.oldReg v2.self.zero q h1, v2.oldReg v1.self.zero q h0, v1.regs]
      · obtain ⟨m1, e1, v1⟩ := u12.self.notTaken hc2 0xA0 k8_at_9c (by decide) (by
          simp only [branchTaken]; rw [t2_12, bk12 _ (by decide), h16, ult_lit (by omega) (by decide)]
          exact decide_eq_false hlt)
        obtain ⟨m2, e2, v2⟩ := v1.self.aluImm hc2 k8_at_a0 (off' := 0xA2) (by decide)
        obtain ⟨m3, e3, v3⟩ := v2.self.aluImm hc2 k8_at_a2 (off' := 0xA4) (by decide)
        obtain ⟨m4, e4, v4⟩ := v3.self.jump hc2 k8_at_a4 (off' := 0xAA) (by decide)
          (pc_even (off := 0xA4) (off' := 0xAA) hP v3.self.pc (by decide) (by decide))
        refine ⟨m4, .cons e1 (.cons e2 (.cons e3 (.single e4))), v4.self, ?_, fun q h0 h1 => ?_⟩
        · rw [v4.regs, v4.regs, v3.newReg (by decide), v3.oldReg v2.self.zero _ (by decide), v2.newReg (by decide)]
          show reg m1 sp + 0x28 + (reg m2 0 + 0xFFFFFFE8) = _
          rw [v1.regs, sp12, v2.self.zero, BitVec.add_assoc]; rfl
        · rw [v4.regs, v3.oldReg v2.self.zero q h1, v2.oldReg v1.self.zero q h0, v1.regs]
    -- 0xAA..0xB8: store the carry, advance, and loop
    obtain ⟨n13, d13, u13⟩ := uA'.alu hc2 k8_at_aa (off' := 0xAC) (by decide)
    obtain ⟨n14, d14, u14⟩ := u13.self.alu hc2 k8_at_ac (off' := 0xAE) (by decide)
    obtain ⟨n15, d15, u15⟩ := u14.self.aluImm hc2 k8_at_ae (off' := 0xB0) (by decide)
    have k13 := u13.oldReg uA'.zero
    have k14 := u14.oldReg u13.self.zero
    have k15 := u15.oldReg u14.self.zero
    have bkA : ∀ q, q ≠ a0 → q ≠ a1 → reg nA q = reg n12 q := kA
    have t1_12 : reg n12 (6 : Fin 32) = BitVec.ofNat 32 (4 * i) := by
      rw [kAB _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), u10.regs, t1_9]
    have a0_14 : reg n14 a0 = F + 8 + BitVec.ofNat 32 (4 * (i + 2)) := by
      rw [u14.newReg (by decide), u13.newReg (by decide), a01A, k13 _ (by decide), bkA _ (by decide) (by decide),
        t1_12]
      show F + BitVec.ofNat 32 0x10 + BitVec.ofNat 32 (4 * i) = F + BitVec.ofNat 32 8 + BitVec.ofNat 32 (4 * (i + 2))
      rw [add_ofNat_assoc, add_ofNat_assoc, show 0x10 + 4 * i = 8 + 4 * (i + 2) by omega]
    obtain ⟨c1, hc1v⟩ : ∃ v, kmCarry y1 xi w1 (kmCarry y0 xi w0 0) = v := ⟨_, rfl⟩
    have t4_15 : reg n15 (29 : Fin 32) = c1 := by
      rw [k15 _ (by decide), k14 _ (by decide), k13 _ (by decide), bkA _ (by decide) (by decide), u12.regs, c0B, hc1v]
    obtain ⟨n16, d16, u16⟩ := u15.self.swG hc2 k8_at_b0 (off' := 0xB4) (by decide)
      (by rw [k15 _ (by decide), a0_14, add_lit_zero]; exact hWa (i + 2))
      (a := F + 8 + BitVec.ofNat 32 (4 * (i + 2))) (v := c1) (by rw [k15 _ (by decide), a0_14, add_lit_zero]) t4_15
    obtain ⟨M3, hM3⟩ : ∃ M, memStore32 M2 (F + 8 + BitVec.ofNat 32 (4 * (i + 2))) c1 = M := ⟨_, rfl⟩
    rw [hM3] at u16
    have hc3 : CodeIn M3 P wideMul8x2Code := by rw [← hM3]; exact hc2.store32 (sWk (i + 2) (by omega))
    obtain ⟨n17, d17, u17⟩ := u16.self.aluImm hc3 k8_at_b4 (off' := 0xB6) (by decide)
    obtain ⟨n18, d18, u18⟩ := u17.self.aluImm hc3 k8_at_b6 (off' := 0xB8) (by decide)
    have k17 := u17.oldReg u16.self.zero
    have k18 := u18.oldReg u17.self.zero
    have bk18 : ∀ q : Fin 32, q.val ∉ [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 21, 29, 30] → reg n18 q = reg n q :=
      fun q hq => by
        have nq : ∀ r : Fin 32, r.val ∈ [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 21, 29, 30] → q ≠ r :=
          fun r hr e => by subst e; exact hq hr
        rw [k18 q (nq _ (by decide)), k17 q (nq _ (by decide)), u16.regs, k15 q (nq _ (by decide)),
          k14 q (nq _ (by decide)), k13 q (nq _ (by decide)), bkA q (nq _ (by decide)) (nq _ (by decide)), bk12 q hq]
    have t2_18 : reg n18 (7 : Fin 32) = BitVec.ofNat 32 (i + 1) := by
      rw [k18 _ (by decide), k17 _ (by decide), u16.regs, u15.newReg (by decide)]
      show reg n14 (7 : Fin 32) + 0x1 = _
      rw [k14 _ (by decide), k13 _ (by decide), bkA _ (by decide) (by decide), t2_12]; exact ofNat_add_lit i 1
    have t0_18 : reg n18 (5 : Fin 32) = F + 8 + BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [k18 _ (by decide), u17.newReg (by decide)]; show reg n16 (5 : Fin 32) + 0x4 = _
      rw [u16.regs, k15 _ (by decide), k14 _ (by decide), k13 _ (by decide), bkA _ (by decide) (by decide),
        kAB _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), u10.regs, back9 _ (by decide), h5, km_add4]
    have s5_18 : reg n18 (21 : Fin 32) = F + 8 + BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [u18.newReg (by decide)]; show reg n17 (21 : Fin 32) + 0x4 = _
      rw [k17 _ (by decide), u16.regs, k15 _ (by decide), k14 _ (by decide), k13 _ (by decide),
        bkA _ (by decide) (by decide), kAB _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), u10.regs, back9 _ (by decide), h21, km_add4]
    -- the buffer after the row
    have hWn : (F + 8).toNat + 4 * (i + 3) ≤ 2 ^ 32 := by rw [hW]; omega
    have e1 := accV_store (M := Mi) (b := F + 8) (v := kmWord y0 xi w0 0) (k := i) (i + 3) (by omega) hWn
    have e2 := accV_store (M := M1) (b := F + 8) (v := kmWord y1 xi w1 (kmCarry y0 xi w0 0)) (k := i + 1) (i + 3)
      (by omega) hWn
    have e3 := accV_store (M := M2) (b := F + 8) (v := c1) (k := i + 2) (i + 3) (by omega) hWn
    rw [hM1] at e1
    rw [hM2] at e2
    rw [hM3] at e3
    rw [hw0] at e1
    rw [hw1'] at e2
    have z2 : memLoad32 M2 (F + 8 + BitVec.ofNat 32 (4 * (i + 2))) = 0 := by
      rw [← hM2, memLoad32_store32_sep (sKK (i + 1) (i + 2) (by omega) (by omega) (by omega)), ← hM1,
        memLoad32_store32_sep (sKK i (i + 2) (by omega) (by omega) (by omega)), hzero (i + 2) (by omega) (by omega)]
    rw [z2] at e3
    have hA3 : accV Mi (F + 8) (i + 3) = accV Mi (F + 8) (i + 2) := by
      show accV Mi (F + 8) (i + 2) + (memLoad32 Mi (F + 8 + BitVec.ofNat 32 (4 * (i + 2)))).toNat * 2 ^ (32 * (i + 2)) = _
      rw [hzero (i + 2) (by omega) (by omega), show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]
    have a0 := km_arith y0 xi w0 0
    have a1 := km_arith y1 xi w1 (kmCarry y0 xi w0 0)
    rw [hc1v] at a1
    have hYv : accV Mb yp 2 = y0.toNat + y1.toNat * 2 ^ 32 := by
      rw [show accV Mb yp 2 = 0 + (memLoad32 Mb (yp + BitVec.ofNat 32 0)).toNat * 1 +
        (memLoad32 Mb (yp + 4)).toNat * 2 ^ 32 from rfl, add_ofNat_zero, hy0, hy1]; omega
    have hXv : accV Mb xp (i + 1) = accV Mb xp i + xi.toNat * 2 ^ (32 * i) := by
      show accV Mb xp i + (memLoad32 Mb (xp + BitVec.ofNat 32 (4 * i))).toNat * 2 ^ (32 * i) = _; rw [hxi]
    rw [km_pow1] at e2
    rw [km_pow2] at e3
    have hrow := km_row_arith (A := accV Mi (F + 8) (i + 2)) (A3 := accV M3 (F + 8) (i + 3))
      (X := accV Mb xp i) (x := xi.toNat) (y0 := y0.toNat) (y1 := y1.toNat) (w0 := w0.toNat) (w1 := w1.toNat)
      (lo0 := (kmWord y0 xi w0 0).toNat) (lo1 := (kmWord y1 xi w1 (kmCarry y0 xi w0 0)).toNat)
      (c0 := (kmCarry y0 xi w0 0).toNat) (c1 := c1.toNat) (Pi := 2 ^ (32 * i)) (by rw [hacc, hYv])
      (by rw [show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero] at e3; rw [← hA3]; omega)
      (by rw [show (0 : Word).toNat = 0 from rfl] at a0; omega) (by omega)
    have hacc' : accV M3 (F + 8) (i + 1 + 2) = accV Mb xp (i + 1) * accV Mb yp 2 := by
      rw [hXv, hYv]; exact hrow
    have hzero' : ∀ k, i + 1 + 2 ≤ k → k < 10 → memLoad32 M3 (F + 8 + BitVec.ofNat 32 (4 * k)) = 0 := by
      intro k h1 h2
      rw [← hM3, memLoad32_store32_sep (sKK (i + 2) k (by omega) (by omega) (by omega)), ← hM2,
        memLoad32_store32_sep (sKK (i + 1) k (by omega) (by omega) (by omega)), ← hM1,
        memLoad32_store32_sep (sKK i k (by omega) (by omega) (by omega)), hzero k (by omega) h2]
    have hfr' : ∀ x, Sep (F + 8) 40 x 1 → M3 x = Mb x := fun x hx => by
      rw [← hM3, memStore32_get_sep (hx.sub (c := 4 * (i + 2)) (l := 4) (by omega)), ← hM2,
        memStore32_get_sep (hx.sub (c := 4 * (i + 1)) (l := 4) (by omega)), ← hM1,
        memStore32_get_sep (hx.sub (c := 4 * i) (l := 4) (by omega)), hfr x hx]
    have pre : Steps n n18 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
      (.cons d10 (cA.trans (.cons d11 (cB.trans (.cons d12 (cA'.trans (.cons d13 (.cons d14 (.cons d15 (.cons d16
      (.cons d17 (.single d18))))))))))))))))))))
    by_cases hlast : i + 1 = 8
    · obtain ⟨n19, d19, u19⟩ := u18.self.notTaken hc3 0xBC k8_at_b8 (by decide) (by
        simp only [branchTaken]; rw [t2_18, bk18 _ (by decide), h17, hlast]; decide)
      have hi1 : i = 7 := by omega
      subst hi1
      exact ⟨n19, M3, pre.trans (.single d19), u19.self, hacc', hfr', fun q hq => by rw [u19.regs, bk18 q hq]⟩
    · obtain ⟨n19, d19, u19⟩ := u18.self.taken hc3 0x3E k8_at_b8 (by decide) (by
        simp only [branchTaken]; rw [t2_18, bk18 _ (by decide), h17]
        exact bne_toNat (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega))
      obtain ⟨n', M', c', u', acc', fr', kk'⟩ := ih (i + 1) n19 M3 (by omega) (by omega) u19.self
        (by rw [u19.regs, t2_18]) (by rw [u19.regs, bk18 _ (by decide), h20])
        (by rw [u19.regs, bk18 _ (by decide), h19]) (by rw [u19.regs, s5_18]) (by rw [u19.regs, t0_18])
        (by rw [u19.regs, bk18 _ (by decide), h17]) (by rw [u19.regs, bk18 _ (by decide), h16])
        (by rw [u19.regs, bk18 _ (by decide), h28]) (by rw [u19.regs, bk18 _ (by decide), hsp]) hacc' hzero' hfr'
      exact ⟨n', M', pre.trans (.cons d19 c'), u', acc', fr', fun q hq => by rw [kk' q hq, u19.regs, bk18 q hq]⟩

/-- Where `widening_mul_fixed::<8, 2>` runs: its code at an even `P` and
`memset`'s and `memcpy`'s where its calls reach them, `0x60` bytes of stack
at `G` (its 0x50-byte frame and `memcpy`'s 16 below), the 10-word result
at `out`, and the operands' 8 and 2 limbs at `xp` and `yp`, all 4-aligned.
The result and the operands are apart from the stack, and the result from the
code; the operands may overlap the result, since the function reads them
before it writes it. -/
structure K8Env (M : Word → BitVec 8) (P G out xp yp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P wideMul8x2Code
  ms : CodeIn M (P + 0x36AC) memsetCode
  mcS : CodeIn M (P + 0x3714) memcpyStubCode
  mcB : CodeIn M (P + 0x371C) memcpyBodyCode
  hG : G.toNat % 4 = 0
  hGt : G.toNat + 0x60 ≤ 2 ^ 32
  hx : xp.toNat % 4 = 0
  hy : yp.toNat % 4 = 0
  hout : out.toNat % 4 = 0
  hot : out.toNat + 40 < 2 ^ 32
  sGC : Sep G 0x60 P wideMul8x2Code.length
  sGM : Sep G 0x60 (P + 0x36AC) memsetCode.length
  sGS : Sep G 0x60 (P + 0x3714) memcpyStubCode.length
  sGB : Sep G 0x60 (P + 0x371C) memcpyBodyCode.length
  sOC : Sep out 40 P wideMul8x2Code.length
  sOB : Sep out 40 (P + 0x371C) memcpyBodyCode.length
  sOG : Sep out 40 G 0x60
  sXG : Sep xp 32 G 0x60
  sYG : Sep yp 8 G 0x60

theorem k8_fill_in {M : Word → BitVec 8} {dst : Word} {v : BitVec 8} {n i : Nat} (hi : i < n) (hn : n < 2 ^ 32) :
    fillBytes M dst v n (dst + BitVec.ofNat 32 i) = v := by
  unfold fillBytes; rw [add_sub_toNat dst (by omega), ite_eq_left hi]

theorem k8_fill0 {M : Word → BitVec 8} {dst : Word} {n k : Nat} (hk : k + 4 ≤ n) (hn : n < 2 ^ 32) :
    memLoad32 (fillBytes M dst ((0 : Word).extractLsb' 0 8) n) (dst + BitVec.ofNat 32 k) = 0 := by
  unfold memLoad32
  rw [show dst + BitVec.ofNat 32 k + 3 = dst + BitVec.ofNat 32 (k + 3) by rw [show (3 : Word) = BitVec.ofNat 32 3 from rfl, add_ofNat_assoc],
    show dst + BitVec.ofNat 32 k + 2 = dst + BitVec.ofNat 32 (k + 2) by rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc],
    show dst + BitVec.ofNat 32 k + 1 = dst + BitVec.ofNat 32 (k + 1) by rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc],
    k8_fill_in (by omega) hn, k8_fill_in (by omega) hn, k8_fill_in (by omega) hn, k8_fill_in (by omega) hn]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The compiled `widening_mul_fixed::<8, 2>`**, called with the result at
`out` and the operands at `xp` and `yp`: the 10 words at `out` are the
product of the 8-limb and 2-limb numbers. It returns with `sp` and every
register but `t0` through `t6` and `a0` through `a7` as they were, and
changes no memory outside its 0x60 bytes of stack and the result. -/
theorem wideMul8x2_correct (m : Machine) {P G out xp yp retAddr : Word} (env : K8Env m.mem P G out xp yp)
    (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp) (ha2 : reg m a2 = yp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = G + 0x60) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + 0x60 ∧ (∀ q, feMKeep q = true → reg m' q = reg m q) ∧
      accV m'.mem out 10 = accV m.mem xp 8 * accV m.mem yp 2 ∧
      ∀ x, Sep G 0x60 x 1 → Sep out 40 x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF⟩ : ∃ F, G + 0x10 = F := ⟨_, rfl⟩
  have hGt := env.hGt
  have hot := env.hot
  have hFn : F.toNat = G.toNat + 0x10 := by
    rw [← hF, BitVec.toNat_add, show (0x10 : Word).toNat = 0x10 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; have := env.hG; omega
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x10 + c) := fun c => by
    rw [← hF, show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl, add_ofNat_assoc]
  have hFsp : G + 0x60 + 0xFFFFFFB0 = F := by rw [← hF, BitVec.add_assoc]; rfl
  have hspF : F + 0x50 = G + 0x60 := by rw [← hF, BitVec.add_assoc]; rfl
  have hGF : F + 0xFFFFFFF0 = G := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero G
  have e8 : F + 8 = G + BitVec.ofNat 32 0x18 := fG 8
  have hF8 : (F + 8).toNat = F.toNat + 8 := by
    rw [BitVec.toNat_add, show (8 : Word).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
  have inF : ∀ x, Sep G 0x60 x 1 → Sep F 0x50 x 1 := fun x hx => by
    rw [← hF]; exact hx.sub (c := 0x10) (l := 0x50) (by decide)
  have in8 : ∀ x, Sep G 0x60 x 1 → Sep (F + 8) 40 x 1 := fun x hx => by
    rw [e8]; exact hx.sub (c := 0x18) (l := 40) (by decide)
  have in0 : ∀ x, Sep G 0x60 x 1 → Sep G 16 x 1 := fun x hx => sep_pre hx (by decide)
  have sFC : Sep F 0x50 P wideMul8x2Code.length := by rw [← hF]; exact env.sGC.sub (c := 0x10) (l := 0x50) (by decide)
  have sFM : Sep F 0x50 (P + 0x36AC) memsetCode.length := by
    rw [← hF]; exact env.sGM.sub (c := 0x10) (l := 0x50) (by decide)
  have sFS : Sep F 0x50 (P + 0x3714) memcpyStubCode.length := by
    rw [← hF]; exact env.sGS.sub (c := 0x10) (l := 0x50) (by decide)
  have sFB : Sep F 0x50 (P + 0x371C) memcpyBodyCode.length := by
    rw [← hF]; exact env.sGB.sub (c := 0x10) (l := 0x50) (by decide)
  have s8G : Sep (F + 8) 32 G 16 := by
    rw [e8]; have := sep_offsets G (c := 0x18) (n := 32) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  -- the prologue: the frame, and `ra` and `s0` through `s5` saved at its top
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code k8_at_0 (off' := 0x2) (by decide)
  have k1 := u1.oldReg hz
  have sp1 : reg m1 sp = F := by rw [u1.newReg (by decide)]; show reg m sp + 0xFFFFFFB0 = _; rw [hsp, hFsp]
  obtain ⟨p0, dp0, up0⟩ := u1.self.swG env.code k8_at_2 (off' := 0x4) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x4C) (v := reg m ra) (by rw [sp1])
    (k1 _ (by decide))
  obtain ⟨P0, hP0⟩ : ∃ M', memStore32 m.mem (F + 0x4C) (reg m ra) = M' := ⟨_, rfl⟩
  rw [hP0] at up0
  have hcp0 : CodeIn P0 P wideMul8x2Code := by rw [← hP0]; exact env.code.store32 (frm_sep' sFC (by decide))
  obtain ⟨p1, dp1, up1⟩ := up0.swG hcp0 k8_at_4 (off' := 0x6) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x48) (v := reg m (8 : Fin 32)) (by rw [sp1])
    (k1 _ (by decide))
  obtain ⟨P1, hP1⟩ : ∃ M', memStore32 P0 (F + 0x48) (reg m (8 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP1] at up1
  have hcp1 : CodeIn P1 P wideMul8x2Code := by rw [← hP1]; exact hcp0.store32 (frm_sep' sFC (by decide))
  obtain ⟨p2, dp2, up2⟩ := up1.swG hcp1 k8_at_6 (off' := 0x8) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x44) (v := reg m (9 : Fin 32)) (by rw [sp1])
    (k1 _ (by decide))
  obtain ⟨P2, hP2⟩ : ∃ M', memStore32 P1 (F + 0x44) (reg m (9 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP2] at up2
  have hcp2 : CodeIn P2 P wideMul8x2Code := by rw [← hP2]; exact hcp1.store32 (frm_sep' sFC (by decide))
  obtain ⟨p3, dp3, up3⟩ := up2.swG hcp2 k8_at_8 (off' := 0xA) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x40) (v := reg m (18 : Fin 32)) (by rw [sp1])
    (k1 _ (by decide))
  obtain ⟨P3, hP3⟩ : ∃ M', memStore32 P2 (F + 0x40) (reg m (18 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP3] at up3
  have hcp3 : CodeIn P3 P wideMul8x2Code := by rw [← hP3]; exact hcp2.store32 (frm_sep' sFC (by decide))
  obtain ⟨p4, dp4, up4⟩ := up3.swG hcp3 k8_at_a (off' := 0xC) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x3C) (v := reg m (19 : Fin 32)) (by rw [sp1])
    (k1 _ (by decide))
  obtain ⟨P4, hP4⟩ : ∃ M', memStore32 P3 (F + 0x3C) (reg m (19 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP4] at up4
  have hcp4 : CodeIn P4 P wideMul8x2Code := by rw [← hP4]; exact hcp3.store32 (frm_sep' sFC (by decide))
  obtain ⟨p5, dp5, up5⟩ := up4.swG hcp4 k8_at_c (off' := 0xE) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x38) (v := reg m (20 : Fin 32)) (by rw [sp1])
    (k1 _ (by decide))
  obtain ⟨P5, hP5⟩ : ∃ M', memStore32 P4 (F + 0x38) (reg m (20 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP5] at up5
  have hcp5 : CodeIn P5 P wideMul8x2Code := by rw [← hP5]; exact hcp4.store32 (frm_sep' sFC (by decide))
  obtain ⟨p6, dp6, up6⟩ := up5.swG hcp5 k8_at_e (off' := 0x10) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x34) (v := reg m (21 : Fin 32)) (by rw [sp1])
    (k1 _ (by decide))
  obtain ⟨P6, hP6⟩ : ∃ M', memStore32 P5 (F + 0x34) (reg m (21 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP6] at up6
  have hcp6 : CodeIn P6 P wideMul8x2Code := by rw [← hP6]; exact hcp5.store32 (frm_sep' sFC (by decide))
  have fpro : ∀ x, Sep F 0x50 x 1 → P6 x = m.mem x := fun x hx => by
    rw [← hP6, memStore32_get_sep (frm_sep' hx (by decide)), ← hP5, memStore32_get_sep (frm_sep' hx (by decide)), ← hP4, memStore32_get_sep (frm_sep' hx (by decide)), ← hP3, memStore32_get_sep (frm_sep' hx (by decide)), ← hP2, memStore32_get_sep (frm_sep' hx (by decide)), ← hP1, memStore32_get_sep (frm_sep' hx (by decide)), ← hP0, memStore32_get_sep (frm_sep' hx (by decide))]
  have svra : memLoad32 P6 (F + 0x4C) = reg m ra := by
    rw [← hP6, memLoad32_store32_sep (show Sep (F + 0x34) 4 (F + 0x4C) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x38) 4 (F + 0x4C) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_sep (show Sep (F + 0x3C) 4 (F + 0x4C) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP3, memLoad32_store32_sep (show Sep (F + 0x40) 4 (F + 0x4C) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP2, memLoad32_store32_sep (show Sep (F + 0x44) 4 (F + 0x4C) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP1, memLoad32_store32_sep (show Sep (F + 0x48) 4 (F + 0x4C) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP0, memLoad32_store32_same]
  have svs0 : memLoad32 P6 (F + 0x48) = reg m (8 : Fin 32) := by
    rw [← hP6, memLoad32_store32_sep (show Sep (F + 0x34) 4 (F + 0x48) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x38) 4 (F + 0x48) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_sep (show Sep (F + 0x3C) 4 (F + 0x48) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP3, memLoad32_store32_sep (show Sep (F + 0x40) 4 (F + 0x48) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP2, memLoad32_store32_sep (show Sep (F + 0x44) 4 (F + 0x48) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP1, memLoad32_store32_same]
  have svs1 : memLoad32 P6 (F + 0x44) = reg m (9 : Fin 32) := by
    rw [← hP6, memLoad32_store32_sep (show Sep (F + 0x34) 4 (F + 0x44) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x38) 4 (F + 0x44) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_sep (show Sep (F + 0x3C) 4 (F + 0x44) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP3, memLoad32_store32_sep (show Sep (F + 0x40) 4 (F + 0x44) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP2, memLoad32_store32_same]
  have svs2 : memLoad32 P6 (F + 0x40) = reg m (18 : Fin 32) := by
    rw [← hP6, memLoad32_store32_sep (show Sep (F + 0x34) 4 (F + 0x40) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x38) 4 (F + 0x40) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_sep (show Sep (F + 0x3C) 4 (F + 0x40) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP3, memLoad32_store32_same]
  have svs3 : memLoad32 P6 (F + 0x3C) = reg m (19 : Fin 32) := by
    rw [← hP6, memLoad32_store32_sep (show Sep (F + 0x34) 4 (F + 0x3C) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x38) 4 (F + 0x3C) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_same]
  have svs4 : memLoad32 P6 (F + 0x38) = reg m (20 : Fin 32) := by
    rw [← hP6, memLoad32_store32_sep (show Sep (F + 0x34) 4 (F + 0x38) 4 from sep_offsets F (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_same]
  have svs5 : memLoad32 P6 (F + 0x34) = reg m (21 : Fin 32) := by
    rw [← hP6, memLoad32_store32_same]
  have cOf : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep F 0x50 b code.length →
      CodeIn P6 b code := fun hc hs i hi => by rw [fpro _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  -- the operands, the buffer, and `memset` on its low 8 words
  obtain ⟨n1, e1, v1⟩ := up6.alu hcp6 k8_at_10 (off' := 0x12) (by decide)
  have j1 := v1.oldReg up6.zero
  obtain ⟨n2, e2, v2⟩ := v1.self.alu hcp6 k8_at_12 (off' := 0x14) (by decide)
  have j2 := v2.oldReg v1.self.zero
  obtain ⟨n3, e3, v3⟩ := v2.self.alu hcp6 k8_at_14 (off' := 0x16) (by decide)
  have j3 := v3.oldReg v2.self.zero
  obtain ⟨n4, e4, v4⟩ := v3.self.aluImm hcp6 k8_at_16 (off' := 0x18) (by decide)
  have j4 := v4.oldReg v3.self.zero
  obtain ⟨n5, e5, v5⟩ := v4.self.aluImm hcp6 k8_at_18 (off' := 0x1C) (by decide)
  have j5 := v5.oldReg v4.self.zero
  obtain ⟨n6, e6, v6⟩ := v5.self.aluImm hcp6 k8_at_1c (off' := 0x1E) (by decide)
  have j6 := v6.oldReg v5.self.zero
  obtain ⟨n7, e7, v7⟩ := v6.self.aluImm hcp6 k8_at_1e (off' := 0x22) (by decide)
  have j7 := v7.oldReg v6.self.zero
  have bk7 : ∀ q : Fin 32, q.val ∉ [19, 20, 18, 10, 12, 11, 21, 2] → reg n7 q = reg m q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [19, 20, 18, 10, 12, 11, 21, 2] → q ≠ r := fun r hr e => by subst e; exact hq hr
    rw [j7 q (nq _ (by decide)), j6 q (nq _ (by decide)), j5 q (nq _ (by decide)), j4 q (nq _ (by decide)),
      j3 q (nq _ (by decide)), j2 q (nq _ (by decide)), j1 q (nq _ (by decide)), k1 q (nq _ (by decide))]
  have sp7 : reg n7 sp = F := by
    rw [j7 _ (by decide), j6 _ (by decide), j5 _ (by decide), j4 _ (by decide), j3 _ (by decide), j2 _ (by decide),
      j1 _ (by decide), sp1]
  have x19 : reg n7 (19 : Fin 32) = yp := by
    rw [j7 _ (by decide), j6 _ (by decide), j5 _ (by decide), j4 _ (by decide), j3 _ (by decide), j2 _ (by decide),
      v1.newReg (by decide)]; show reg m1 0 + reg m1 a2 = _
    rw [up6.zero, k1 _ (by decide), ha2]; exact BitVec.zero_add _
  have x20 : reg n7 (20 : Fin 32) = xp := by
    rw [j7 _ (by decide), j6 _ (by decide), j5 _ (by decide), j4 _ (by decide), j3 _ (by decide),
      v2.newReg (by decide)]; show reg n1 0 + reg n1 a1 = _
    rw [v1.self.zero, j1 _ (by decide), k1 _ (by decide), ha1]; exact BitVec.zero_add _
  have x18 : reg n7 (18 : Fin 32) = out := by
    rw [j7 _ (by decide), j6 _ (by decide), j5 _ (by decide), j4 _ (by decide), v3.newReg (by decide)]
    show reg n2 0 + reg n2 a0 = _
    rw [v2.self.zero, j2 _ (by decide), j1 _ (by decide), k1 _ (by decide), ha0]; exact BitVec.zero_add _
  have x10 : reg n7 a0 = F + 8 := by
    rw [j7 _ (by decide), j6 _ (by decide), j5 _ (by decide), v4.newReg (by decide)]; show reg n3 sp + 0x8 = _
    rw [j3 _ (by decide), j2 _ (by decide), j1 _ (by decide), sp1]
  have x12 : reg n7 a2 = BitVec.ofNat 32 32 := by
    rw [j7 _ (by decide), j6 _ (by decide), v5.newReg (by decide)]; show reg n4 0 + 0x20 = _; rw [v4.self.zero]; rfl
  have x11 : reg n7 a1 = 0 := by
    rw [j7 _ (by decide), v6.newReg (by decide)]; show reg n5 0 + 0x0 = _; rw [v5.self.zero]; rfl
  have x21 : reg n7 (21 : Fin 32) = F + 8 := by
    rw [v7.newReg (by decide)]; show reg n6 sp + 0x8 = _
    rw [j6 _ (by decide), j5 _ (by decide), j4 _ (by decide), j3 _ (by decide), j2 _ (by decide), j1 _ (by decide), sp1]
  obtain ⟨n8, c8, pc8, mem8, regs8⟩ := v7.self.callRa hcp6 k8_at_22 k8_at_26 (cb := P + 0x36AC)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x36AC (by decide))
  have r8 := PEnv.reg1 regs8 v7.self.zero
  obtain ⟨n9, c9, pc9, mem9, a09, K9⟩ := memset_correct n8 (P + 0x36AC) (P + BitVec.ofNat 32 (0x22 + 8)) (F + 8)
    0 32 (fun i hi => by show n8.mem _ = _; rw [mem8]; exact cOf env.ms sFM i hi) (even_at P env.hP 0x36AC (by decide))
    pc8 (by rw [r8 _ (by decide), x10]) (by rw [r8 _ (by decide), x11]) (by rw [r8 _ (by decide), x12])
    (by rw [regs8]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x22 + 8) (by decide)))
    (by rw [hF8]; omega) (sFM.sub (c := 8) (l := 32) (by decide))
  rw [mem8] at mem9
  obtain ⟨Mz, hMz⟩ : ∃ M, fillBytes P6 (F + 8) ((0 : Word).extractLsb' 0 8) 32 = M := ⟨_, rfl⟩
  rw [hMz] at mem9
  have bk9 : ∀ q : Fin 32, q.val ∉ [12, 13, 14, 15, 16, 1, 19, 20, 18, 10, 11, 21, 2] → reg n9 q = reg m q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [12, 13, 14, 15, 16, 1, 19, 20, 18, 10, 11, 21, 2] → q ≠ r :=
      fun r hr e => by subst e; exact hq hr
    rw [K9 q (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)),
      r8 q (nq _ (by decide)), bk7 q (fun h => hq ((by decide : ∀ a : Fin 32, a.val ∈ [19, 20, 18, 10, 12, 11, 21, 2] →
        a.val ∈ [12, 13, 14, 15, 16, 1, 19, 20, 18, 10, 11, 21, 2]) q h))]
  have keep9 : ∀ q : Fin 32, q.val ∈ [2, 18, 19, 20, 21] → reg n9 q = reg n7 q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [12, 13, 14, 15, 16, 1] → q ≠ r := fun r hr e =>
      (by decide : ∀ a : Fin 32, a.val ∈ [12, 13, 14, 15, 16, 1] → a.val ∈ [2, 18, 19, 20, 21] → False) r hr
        (by rw [← e]; exact hq)
    rw [K9 q (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)),
      r8 q (nq _ (by decide))]
  have MzF : ∀ x, Sep (F + 8) 32 x 1 → Mz x = P6 x := fun x hx => by rw [← hMz, fillBytes_sep hx (Nat.le_refl _)]
  have hcz : CodeIn Mz P wideMul8x2Code := fun i hi => by
    rw [MzF _ ((sFC.sub (c := 8) (l := 32) (by decide)).subR (c := i) (l := 1) (by omega))]; exact hcp6 i hi
  have w9 : St Mz P n9 0x2A (reg n9) := ⟨by rw [pc9], mem9, fun _ => rfl⟩
  -- the top two words, and the loop's constants
  obtain ⟨n10, e10, v10⟩ := w9.aluImm hcz k8_at_2a (off' := 0x2C) (by decide)
  have j10 := v10.oldReg w9.zero
  have sp10 : reg n10 sp = F := by rw [j10 _ (by decide), keep9 _ (by decide), sp7]
  obtain ⟨n11, e11, v11⟩ := v10.self.swG hcz k8_at_2c (off' := 0x2E) (by decide)
    (by rw [sp10]; exact fr_al' hFa (by decide)) (a := F + 0x28) (v := 0) (by rw [sp10]) v10.self.zero
  obtain ⟨Z1, hZ1⟩ : ∃ M, memStore32 Mz (F + 0x28) 0 = M := ⟨_, rfl⟩
  rw [hZ1] at v11
  have hcz1 : CodeIn Z1 P wideMul8x2Code := by rw [← hZ1]; exact hcz.store32 (frm_sep' sFC (by decide))
  have hZ1' : memStore32 Mz (F + BitVec.ofNat 32 40) 0 = Z1 := hZ1
  obtain ⟨n12, e12, v12⟩ := v11.self.swG hcz1 k8_at_2e (off' := 0x30) (by decide)
    (by rw [v11.regs, sp10]; exact fr_al' hFa (by decide)) (a := F + 0x2C) (v := 0) (by rw [v11.regs, sp10])
    v11.self.zero
  obtain ⟨Mb, hMb⟩ : ∃ M, memStore32 Z1 (F + 0x2C) 0 = M := ⟨_, rfl⟩
  rw [hMb] at v12
  have hcb : CodeIn Mb P wideMul8x2Code := by rw [← hMb]; exact hcz1.store32 (frm_sep' sFC (by decide))
  have hMb' : memStore32 Z1 (F + BitVec.ofNat 32 44) 0 = Mb := hMb
  obtain ⟨n13, e13, v13⟩ := v12.self.aluImm hcb k8_at_30 (off' := 0x34) (by decide)
  obtain ⟨n14, e14, v14⟩ := v13.self.aluImm hcb k8_at_34 (off' := 0x36) (by decide)
  obtain ⟨n15, e15, v15⟩ := v14.self.aluImm hcb k8_at_36 (off' := 0x38) (by decide)
  obtain ⟨n16, e16, v16⟩ := v15.self.aluImm hcb k8_at_38 (off' := 0x3A) (by decide)
  have j13 := v13.oldReg v12.self.zero
  have j14 := v14.oldReg v13.self.zero
  have j15 := v15.oldReg v14.self.zero
  have j16 := v16.oldReg v15.self.zero
  have a7_16 : reg n16 (17 : Fin 32) = BitVec.ofNat 32 8 := by
    rw [j16 _ (by decide), j15 _ (by decide), v14.newReg (by decide)]; show reg n13 0 + 0x8 = _
    rw [v13.self.zero]; rfl
  obtain ⟨n17, e17, v17⟩ := v16.self.notTaken hcb 0x3E k8_at_3a (by decide) (by
    simp only [branchTaken, a7_16, v16.self.zero]; decide)
  have bk17 : ∀ q : Fin 32, q.val ∉ [7, 5, 17, 16, 28] → reg n17 q = reg n9 q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [7, 5, 17, 16, 28] → q ≠ r := fun r hr e => by subst e; exact hq hr
    rw [v17.regs, j16 q (nq _ (by decide)), j15 q (nq _ (by decide)), j14 q (nq _ (by decide)),
      j13 q (nq _ (by decide)), v12.regs, v11.regs, j10 q (nq _ (by decide))]
  -- the starting buffer: all zero
  have MbG : ∀ x, Sep G 0x60 x 1 → Mb x = m.mem x := fun x hx => by
    rw [← hMb, memStore32_get_sep (frm_sep' (inF x hx) (by decide)), ← hZ1,
      memStore32_get_sep (frm_sep' (inF x hx) (by decide)), MzF x (sep_pre (in8 x hx) (by decide)), fpro x (inF x hx)]
  have hW8 : ∀ k, F + 8 + BitVec.ofNat 32 k = F + BitVec.ofNat 32 (8 + k) := fun k => by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]
  have zb : ∀ k, k < 10 → memLoad32 Mb (F + 8 + BitVec.ofNat 32 (4 * k)) = 0 := by
    intro k hk
    by_cases h1 : k < 8
    · have q1 : Sep (F + 44) 4 (F + 8 + BitVec.ofNat 32 (4 * k)) 4 := by
        rw [hW8]; exact sep_offsets F (c := 44) (n := 4) (d := 8 + 4 * k) (k := 4) (.inr (by omega)) (by omega) (by omega)
      have q2 : Sep (F + 40) 4 (F + 8 + BitVec.ofNat 32 (4 * k)) 4 := by
        rw [hW8]; exact sep_offsets F (c := 40) (n := 4) (d := 8 + 4 * k) (k := 4) (.inr (by omega)) (by omega) (by omega)
      rw [← hMb, memLoad32_store32_sep q1, ← hZ1, memLoad32_store32_sep q2, ← hMz]
      exact k8_fill0 (by omega) (by decide)
    · by_cases h2 : k = 8
      · subst h2
        rw [hW8, show F + BitVec.ofNat 32 (8 + 4 * 8) = F + 0x28 from rfl, ← hMb,
          memLoad32_store32_sep (show Sep (F + 0x2C) 4 (F + 0x28) 4 from sep_offsets F (by decide) (by decide)
            (by decide)), ← hZ1, memLoad32_store32_same]
      · have h3 : k = 9 := by omega
        subst h3
        rw [hW8, show F + BitVec.ofNat 32 (8 + 4 * 9) = F + 0x2C from rfl, ← hMb, memLoad32_store32_same]
  have acc0 : accV Mb (F + 8) (0 + 2) = accV Mb xp 0 * accV Mb yp 2 := by
    rw [show accV Mb xp 0 = 0 from rfl, Nat.zero_mul]
    exact accV_zero 2 (fun i hi => zb i (by omega))
  -- the rows
  have t2_17 : reg n17 (7 : Fin 32) = BitVec.ofNat 32 0 := by
    rw [v17.regs, j16 _ (by decide), j15 _ (by decide), j14 _ (by decide), j13 _ (by decide), v12.regs, v11.regs,
      v10.newReg (by decide)]; show reg n9 0 + 0x0 = _; rw [w9.zero]; rfl
  have t0_17 : reg n17 (5 : Fin 32) = F + 8 + BitVec.ofNat 32 (4 * 0) := by
    rw [v17.regs, j16 _ (by decide), j15 _ (by decide), j14 _ (by decide), v13.newReg (by decide)]
    show reg n12 sp + 0x8 = F + 8 + BitVec.ofNat 32 0
    rw [v12.regs, v11.regs, sp10, add_ofNat_zero]
  have a6_17 : reg n17 a6 = BitVec.ofNat 32 6 := by
    rw [v17.regs, j16 _ (by decide), v15.newReg (by decide)]; show reg n14 0 + 0x6 = _; rw [v14.self.zero]; rfl
  have t3_17 : reg n17 (28 : Fin 32) = BitVec.ofNat 32 7 := by
    rw [v17.regs, v16.newReg (by decide)]; show reg n15 0 + 0x7 = _; rw [v15.self.zero]; rfl
  obtain ⟨nR, MR, cR, uR, accR, frR, kR⟩ := k8_rows (Mb := Mb) env.hP hcb hFa (by omega) env.hx env.hy
    (by rw [e8]; exact env.sGC.sub (c := 0x18) (l := 40) (by decide))
    (by rw [e8]; exact (env.sXG.subR (c := 0x18) (l := 40) (by decide)).symm)
    (by rw [e8]; exact (env.sYG.subR (c := 0x18) (l := 40) (by decide)).symm)
    8 0 n17 Mb (by omega) (by omega) v17.self t2_17
    (by rw [bk17 _ (by decide), keep9 _ (by decide), x20]) (by rw [bk17 _ (by decide), keep9 _ (by decide), x19])
    (by rw [bk17 _ (by decide), keep9 _ (by decide), x21]; show F + 8 = F + 8 + BitVec.ofNat 32 0; rw [add_ofNat_zero])
    t0_17 (by rw [v17.regs, a7_16]) a6_17 t3_17 (by rw [bk17 _ (by decide), keep9 _ (by decide), sp7]) acc0
    (fun k _ h2 => zb k h2) (fun _ _ => rfl)
  have bkR : ∀ q : Fin 32, q.val ∉ [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 21, 28, 29, 30] →
      reg nR q = reg n9 q := fun q hq => by
    have sub : ∀ q : Fin 32, q.val ∈ [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 21, 29, 30] →
        q.val ∈ [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 21, 28, 29, 30] := by decide
    have sub2 : ∀ q : Fin 32, q.val ∈ [7, 5, 17, 16, 28] →
        q.val ∈ [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 21, 28, 29, 30] := by decide
    rw [kR q (fun h => hq (sub q h)), bk17 q (fun h => hq (sub2 q h))]
  have spR : reg nR sp = F := by rw [bkR _ (by decide), keep9 _ (by decide), sp7]
  have s2R : reg nR (18 : Fin 32) = out := by rw [bkR _ (by decide), keep9 _ (by decide), x18]
  have MRG : ∀ x, Sep G 0x60 x 1 → MR x = m.mem x := fun x hx => by rw [frR x (in8 x hx), MbG x hx]
  have cOfR : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x60 b code.length →
      CodeIn MR b code := fun hc hs i hi => by rw [MRG _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hcR : CodeIn MR P wideMul8x2Code := cOfR env.code env.sGC
  -- `memcpy` copies the low 8 words out, and two stores the top two
  obtain ⟨nA, eA, vA⟩ := uR.aluImm hcR k8_at_bc (off' := 0xBE) (by decide)
  obtain ⟨nB, eB, vB⟩ := vA.self.aluImm hcR k8_at_be (off' := 0xC2) (by decide)
  obtain ⟨nC, eC, vC⟩ := vB.self.alu hcR k8_at_c2 (off' := 0xC4) (by decide)
  have jA := vA.oldReg uR.zero
  have jB := vB.oldReg vA.self.zero
  have jC := vC.oldReg vB.self.zero
  obtain ⟨nD, cD, pcD, memD, regsD⟩ := vC.self.callRa hcR k8_at_c4 k8_at_c8 (cb := P + 0x3714)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x3714 (by decide))
  have rD := PEnv.reg1 regsD vC.self.zero
  have spD : reg nD sp = F := by rw [rD _ (by decide), jC _ (by decide), jB _ (by decide), jA _ (by decide), spR]
  obtain ⟨nE, cE, pcE, spE, a0E, memE, KE⟩ := memcpy_correct nD (P + 0x3714) (P + BitVec.ofNat 32 (0xC4 + 8))
    out (F + 8) 32 (fun i hi => by show nD.mem _ = _; rw [memD]; exact cOfR env.mcS env.sGS i hi)
    (even_at P env.hP 0x3714 (by decide)) pcD
    (by rw [rD _ (by decide), vC.newReg (by decide)]; show reg nB 0 + reg nB (18 : Fin 32) = _
        rw [vB.self.zero, jB _ (by decide), jA _ (by decide), s2R]; exact BitVec.zero_add _)
    (by rw [rD _ (by decide), jC _ (by decide), jB _ (by decide), vA.newReg (by decide)]; show reg nR sp + 0x8 = _
        rw [spR])
    (by rw [rD _ (by decide), jC _ (by decide), vB.newReg (by decide)]; show reg nA 0 + 0x20 = _
        rw [vA.self.zero]; rfl)
    (by rw [regsD]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0xC4 + 8) (by decide)))
    (by
      rw [memD, spD, hGF, show P + 0x3714 + 8 = P + 0x371C by rw [BitVec.add_assoc]; rfl]
      exact {
               code := cOfR env.mcB env.sGB
               hDC := sep_pre env.sOB (by decide)
               hFC := by have := env.sGB.sub (c := 0) (l := 16) (by decide); rwa [add_ofNat_zero] at this
               hdF := by
                 have := env.sOG.subR (c := 0) (l := 16) (by decide); rw [add_ofNat_zero] at this
                 exact sep_pre this (by decide)
               hsF := s8G
               hsep := by rw [e8]; exact sep_pre (env.sOG.subR (c := 0x18) (l := 32) (by decide)) (by decide)
               hF := env.hG
               hFw := by omega
               hdw := by omega
               hsw := by rw [hF8]; omega })
  rw [memD, spD, hGF] at memE
  rw [spD] at spE
  obtain ⟨Mc, hMc⟩ : ∃ M, nE.mem = M := ⟨_, rfl⟩
  rw [hMc] at memE
  have McG : ∀ x, Sep G 0x60 x 1 → Sep out 40 x 1 → Mc x = m.mem x := fun x hx ho => by
    rw [memE x (in0 x hx), copyBytes_sep (sep_pre ho (by decide)) (Nat.le_refl _), MRG x hx]
  have hcc : CodeIn Mc P wideMul8x2Code := fun i hi => by
    rw [McG _ (env.sGC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  have rdF : ∀ o, 8 ≤ o → o + 4 ≤ 0x50 → memLoad32 Mc (F + BitVec.ofNat 32 o) = memLoad32 MR (F + BitVec.ofNat 32 o) :=
    fun o h1 h2 => by
      have hG16 : Sep G 16 (F + BitVec.ofNat 32 o) 4 := by
        rw [fG]
        have := sep_offsets G (c := 0) (n := 16) (d := 0x10 + o) (k := 4) (.inl (by omega)) (by decide) (by omega)
        rwa [add_ofNat_zero] at this
      have hO : Sep out 32 (F + BitVec.ofNat 32 o) 4 := by
        rw [fG]; exact sep_pre (env.sOG.subR (c := 0x10 + o) (l := 4) (by omega)) (by decide)
      rw [load_frame memE hG16, load_frame (fun a ha => copyBytes_sep ha (Nat.le_refl _)) hO]
  have wE : St Mc P nE 0xCC (reg nE) := ⟨by rw [pcE], hMc, fun _ => rfl⟩
  obtain ⟨f1, g1, w1⟩ := wE.lwE hcc k8_at_cc (off' := 0xCE) (by decide) (by rw [spE]; exact fr_al' hFa (by decide))
    (v := memLoad32 MR (F + 0x28)) (by rw [spE]; exact rdF 40 (by decide) (by decide))
  have q1 := w1.oldReg wE.zero
  obtain ⟨f2, g2, w2⟩ := w1.self.lwE hcc k8_at_ce (off' := 0xD0) (by decide)
    (by rw [q1 _ (by decide), spE]; exact fr_al' hFa (by decide))
    (v := memLoad32 MR (F + 0x2C)) (by rw [q1 _ (by decide), spE]; exact rdF 44 (by decide) (by decide))
  have q2 := w2.oldReg w1.self.zero
  obtain ⟨f3, g3, w3⟩ := w2.self.alu hcc k8_at_d0 (off' := 0xD2) (by decide)
  have q3 := w3.oldReg w2.self.zero
  have s2E : reg nE (18 : Fin 32) = out := by
    rw [KE _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rD _ (by decide), jC _ (by decide),
      jB _ (by decide), jA _ (by decide), s2R]
  have a2_3 : reg f3 a2 = out := by
    rw [w3.newReg (by decide)]; show reg f2 0 + reg f2 (18 : Fin 32) = _
    rw [w2.self.zero, q2 _ (by decide), q1 _ (by decide), s2E]; exact BitVec.zero_add _
  obtain ⟨f4, g4, w4⟩ := w3.self.swG hcc k8_at_d2 (off' := 0xD4) (by decide)
    (by rw [a2_3]; exact fr_al' env.hout (by decide)) (a := out + 0x20) (v := memLoad32 MR (F + 0x28))
    (by rw [a2_3]) (by rw [q3 _ (by decide), q2 _ (by decide), w1.newReg (by decide)])
  obtain ⟨O1, hO1⟩ : ∃ M, memStore32 Mc (out + 0x20) (memLoad32 MR (F + 0x28)) = M := ⟨_, rfl⟩
  rw [hO1] at w4
  have hco1 : CodeIn O1 P wideMul8x2Code := by rw [← hO1]; exact hcc.store32 (env.sOC.sub (c := 32) (l := 4) (by decide))
  have hO1' : memStore32 Mc (out + BitVec.ofNat 32 32) (memLoad32 MR (F + 0x28)) = O1 := hO1
  obtain ⟨f5, g5, w5⟩ := w4.self.swG hco1 k8_at_d4 (off' := 0xD6) (by decide)
    (by rw [w4.regs, a2_3]; exact fr_al' env.hout (by decide)) (a := out + 0x24)
    (v := memLoad32 MR (F + 0x2C)) (by rw [w4.regs, a2_3]) (by rw [w4.regs, q3 _ (by decide), w2.newReg (by decide)])
  obtain ⟨Mf, hMf⟩ : ∃ M, memStore32 O1 (out + 0x24) (memLoad32 MR (F + 0x2C)) = M := ⟨_, rfl⟩
  rw [hMf] at w5
  have hcf : CodeIn Mf P wideMul8x2Code := by rw [← hMf]; exact hco1.store32 (env.sOC.sub (c := 36) (l := 4) (by decide))
  have hMf' : memStore32 O1 (out + BitVec.ofNat 32 36) (memLoad32 MR (F + 0x2C)) = Mf := hMf
  have sOF : ∀ a b, a + 4 ≤ 40 → b + 4 ≤ 0x50 → Sep (out + BitVec.ofNat 32 a) 4 (F + BitVec.ofNat 32 b) 4 :=
    fun a b h1 h2 => by rw [fG]; exact (env.sOG.sub (c := a) (l := 4) h1).subR (c := 0x10 + b) (l := 4) (by omega)
  have rdS : ∀ o, 48 ≤ o → o + 4 ≤ 0x50 → memLoad32 Mf (F + BitVec.ofNat 32 o) = memLoad32 P6 (F + BitVec.ofNat 32 o) :=
    fun o h1 h2 => by
      rw [← hMf', memLoad32_store32_sep (sOF 36 o (by decide) h2), ← hO1', memLoad32_store32_sep (sOF 32 o (by decide) h2),
        rdF o (by omega) h2,
        load_frame frR (sep_offsets F (c := 8) (n := 40) (d := o) (k := 4) (.inl (by omega)) (by omega) (by omega)),
        ← hMb', memLoad32_store32_sep (sep_offsets F (c := 44) (n := 4) (d := o) (k := 4) (.inl (by omega)) (by omega)
          (by omega)), ← hZ1', memLoad32_store32_sep (sep_offsets F (c := 40) (n := 4) (d := o) (k := 4) (.inl (by omega))
          (by omega) (by omega)),
        load_frame MzF (sep_offsets F (c := 8) (n := 32) (d := o) (k := 4) (.inl (by omega)) (by omega) (by omega))]
  -- the epilogue
  have spf5 : reg f5 sp = F := by
    rw [w5.regs, w4.regs, q3 _ (by decide), q2 _ (by decide), q1 _ (by decide), spE]
  obtain ⟨f6, g6, w6⟩ := w5.self.lwE hcf k8_at_d6 (off' := 0xD8) (by decide)
    (by rw [spf5]; exact fr_al' hFa (by decide)) (v := reg m ra)
    (by rw [spf5]; exact (rdS 0x4C (by decide) (by decide)).trans svra)
  obtain ⟨f7, g7, w7⟩ := w6.self.lwE hcf k8_at_d8 (off' := 0xDA) (by decide)
    (by rw [w6.oldReg w5.self.zero _ (by decide), spf5]; exact fr_al' hFa (by decide)) (v := reg m (8 : Fin 32))
    (by rw [w6.oldReg w5.self.zero _ (by decide), spf5]; exact (rdS 0x48 (by decide) (by decide)).trans svs0)
  obtain ⟨f8, g8, w8⟩ := w7.self.lwE hcf k8_at_da (off' := 0xDC) (by decide)
    (by rw [w7.oldReg w6.self.zero _ (by decide), w6.oldReg w5.self.zero _ (by decide), spf5]; exact fr_al' hFa (by decide)) (v := reg m (9 : Fin 32))
    (by rw [w7.oldReg w6.self.zero _ (by decide), w6.oldReg w5.self.zero _ (by decide), spf5]; exact (rdS 0x44 (by decide) (by decide)).trans svs1)
  obtain ⟨f9, g9, w9⟩ := w8.self.lwE hcf k8_at_dc (off' := 0xDE) (by decide)
    (by rw [w8.oldReg w7.self.zero _ (by decide), w7.oldReg w6.self.zero _ (by decide), w6.oldReg w5.self.zero _ (by decide), spf5]; exact fr_al' hFa (by decide)) (v := reg m (18 : Fin 32))
    (by rw [w8.oldReg w7.self.zero _ (by decide), w7.oldReg w6.self.zero _ (by decide), w6.oldReg w5.self.zero _ (by decide), spf5]; exact (rdS 0x40 (by decide) (by decide)).trans svs2)
  obtain ⟨f10, g10, w10⟩ := w9.self.lwE hcf k8_at_de (off' := 0xE0) (by decide)
    (by rw [w9.oldReg w8.self.zero _ (by decide), w8.oldReg w7.self.zero _ (by decide), w7.oldReg w6.self.zero _ (by decide), w6.oldReg w5.self.zero _ (by decide), spf5]; exact fr_al' hFa (by decide)) (v := reg m (19 : Fin 32))
    (by rw [w9.oldReg w8.self.zero _ (by decide), w8.oldReg w7.self.zero _ (by decide), w7.oldReg w6.self.zero _ (by decide), w6.oldReg w5.self.zero _ (by decide), spf5]; exact (rdS 0x3C (by decide) (by decide)).trans svs3)
  obtain ⟨f11, g11, w11⟩ := w10.self.lwE hcf k8_at_e0 (off' := 0xE2) (by decide)
    (by rw [w10.oldReg w9.self.zero _ (by decide), w9.oldReg w8.self.zero _ (by decide), w8.oldReg w7.self.zero _ (by decide), w7.oldReg w6.self.zero _ (by decide), w6.oldReg w5.self.zero _ (by decide), spf5]; exact fr_al' hFa (by decide)) (v := reg m (20 : Fin 32))
    (by rw [w10.oldReg w9.self.zero _ (by decide), w9.oldReg w8.self.zero _ (by decide), w8.oldReg w7.self.zero _ (by decide), w7.oldReg w6.self.zero _ (by decide), w6.oldReg w5.self.zero _ (by decide), spf5]; exact (rdS 0x38 (by decide) (by decide)).trans svs4)
  obtain ⟨f12, g12, w12⟩ := w11.self.lwE hcf k8_at_e2 (off' := 0xE4) (by decide)
    (by rw [w11.oldReg w10.self.zero _ (by decide), w10.oldReg w9.self.zero _ (by decide), w9.oldReg w8.self.zero _ (by decide), w8.oldReg w7.self.zero _ (by decide), w7.oldReg w6.self.zero _ (by decide), w6.oldReg w5.self.zero _ (by decide), spf5]; exact fr_al' hFa (by decide)) (v := reg m (21 : Fin 32))
    (by rw [w11.oldReg w10.self.zero _ (by decide), w10.oldReg w9.self.zero _ (by decide), w9.oldReg w8.self.zero _ (by decide), w8.oldReg w7.self.zero _ (by decide), w7.oldReg w6.self.zero _ (by decide), w6.oldReg w5.self.zero _ (by decide), spf5]; exact (rdS 0x34 (by decide) (by decide)).trans svs5)
  obtain ⟨f13, g13, w13⟩ := w12.self.aluImm hcf k8_at_e4 (off' := 0xE6) (by decide)
  obtain ⟨f14, g14, pc14, mem14, regs14⟩ := w13.self.jalr hcf k8_at_e6
  have finra : reg f12 ra = reg m ra := by rw [w12.oldReg w11.self.zero _ (by decide), w11.oldReg w10.self.zero _ (by decide), w10.oldReg w9.self.zero _ (by decide), w9.oldReg w8.self.zero _ (by decide), w8.oldReg w7.self.zero _ (by decide), w7.oldReg w6.self.zero _ (by decide), w6.newReg (by decide)]
  have fins0 : reg f12 (8 : Fin 32) = reg m (8 : Fin 32) := by rw [w12.oldReg w11.self.zero _ (by decide), w11.oldReg w10.self.zero _ (by decide), w10.oldReg w9.self.zero _ (by decide), w9.oldReg w8.self.zero _ (by decide), w8.oldReg w7.self.zero _ (by decide), w7.newReg (by decide)]
  have fins1 : reg f12 (9 : Fin 32) = reg m (9 : Fin 32) := by rw [w12.oldReg w11.self.zero _ (by decide), w11.oldReg w10.self.zero _ (by decide), w10.oldReg w9.self.zero _ (by decide), w9.oldReg w8.self.zero _ (by decide), w8.newReg (by decide)]
  have fins2 : reg f12 (18 : Fin 32) = reg m (18 : Fin 32) := by rw [w12.oldReg w11.self.zero _ (by decide), w11.oldReg w10.self.zero _ (by decide), w10.oldReg w9.self.zero _ (by decide), w9.newReg (by decide)]
  have fins3 : reg f12 (19 : Fin 32) = reg m (19 : Fin 32) := by rw [w12.oldReg w11.self.zero _ (by decide), w11.oldReg w10.self.zero _ (by decide), w10.newReg (by decide)]
  have fins4 : reg f12 (20 : Fin 32) = reg m (20 : Fin 32) := by rw [w12.oldReg w11.self.zero _ (by decide), w11.newReg (by decide)]
  have fins5 : reg f12 (21 : Fin 32) = reg m (21 : Fin 32) := by rw [w12.newReg (by decide)]
  have kk : ∀ q : Fin 32, q.val ∉ [1, 8, 9, 18, 19, 20, 21] → reg f12 q = reg f5 q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [1, 8, 9, 18, 19, 20, 21] → q ≠ r := fun r hr e => by subst e; exact hq hr
    rw [w12.oldReg w11.self.zero q (nq _ (by decide)), w11.oldReg w10.self.zero q (nq _ (by decide)), w10.oldReg w9.self.zero q (nq _ (by decide)), w9.oldReg w8.self.zero q (nq _ (by decide)), w8.oldReg w7.self.zero q (nq _ (by decide)), w7.oldReg w6.self.zero q (nq _ (by decide)), w6.oldReg w5.self.zero q (nq _ (by decide))]
  have spf : reg f14 sp = G + 0x60 := by
    rw [regs14, w13.newReg (by decide)]; show reg f12 sp + 0x50 = _
    rw [kk _ (by decide), spf5, hspF]
  have kf : ∀ q, q ≠ sp → reg f14 q = reg f12 q := fun q hq => by rw [regs14, w13.oldReg w12.self.zero q hq]
  have pass : ∀ q : Fin 32, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg f12 q = reg m q := by
    intro q hq
    have nl : ∀ r : Fin 32, r.val ∉ [3, 4, 22, 23, 24, 25, 26, 27] → q ≠ r := fun r hr e => by subst e; exact hr hq
    have nn : ∀ L : List Nat, (∀ v, v ∈ L → v ∉ [3, 4, 22, 23, 24, 25, 26, 27]) → q.val ∉ L := fun L hL h =>
      hL _ h hq
    rw [kk q (nn _ (by decide)), w5.regs, w4.regs, q3 q (nl _ (by decide)), q2 q (nl _ (by decide)),
      q1 q (nl _ (by decide)),
      KE q (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide))
        (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide))
        (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)),
      rD q (nl _ (by decide)), jC q (nl _ (by decide)), jB q (nl _ (by decide)), jA q (nl _ (by decide)),
      bkR q (nn _ (by decide)), bk9 q (nn _ (by decide))]
  have hmem : ∀ q : Fin 32, feMKeep q = true → q = 0 ∨ q = ra ∨ q = sp ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨
      q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨
      q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] := by decide
  -- the result's words: the low 8 from `memcpy`, the top two from the stores
  have outw : ∀ i, i < 10 → memLoad32 Mf (out + BitVec.ofNat 32 (4 * i)) =
      memLoad32 MR (F + 8 + BitVec.ofNat 32 (4 * i)) := by
    intro i hi
    by_cases h1 : i < 8
    · rw [← hMf', memLoad32_store32_sep (sep_offsets out (c := 36) (n := 4) (d := 4 * i) (k := 4) (.inr (by omega))
          (by omega) (by omega)), ← hO1', memLoad32_store32_sep (sep_offsets out (c := 32) (n := 4) (d := 4 * i) (k := 4)
          (.inr (by omega)) (by omega) (by omega)),
        load_frame memE (by
          have := (env.sOG.subR (c := 0) (l := 16) (by decide)).symm; rw [add_ofNat_zero] at this
          exact this.subR (c := 4 * i) (l := 4) (by omega)),
        cb_load (by omega) (by decide)]
    · by_cases h2 : i = 8
      · subst h2
        rw [hW8, show out + BitVec.ofNat 32 (4 * 8) = out + 0x20 from rfl,
          show F + BitVec.ofNat 32 (8 + 4 * 8) = F + 0x28 from rfl, ← hMf,
          memLoad32_store32_sep (show Sep (out + 0x24) 4 (out + 0x20) 4 from sep_offsets out (by decide)
            (by decide) (by decide)), ← hO1, memLoad32_store32_same]
      · have h3 : i = 9 := by omega
        subst h3
        rw [hW8, show out + BitVec.ofNat 32 (4 * 9) = out + 0x24 from rfl,
          show F + BitVec.ofNat 32 (8 + 4 * 9) = F + 0x2C from rfl, ← hMf, memLoad32_store32_same]
  have steps : Steps m f14 := .cons d1 (.cons dp0 (.cons dp1 (.cons dp2 (.cons dp3 (.cons dp4 (.cons dp5 (.cons dp6
    (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (c8.trans (c9.trans (.cons e10 (.cons e11
    (.cons e12 (.cons e13 (.cons e14 (.cons e15 (.cons e16 (.cons e17 (cR.trans (.cons eA (.cons eB (.cons eC
    (cD.trans (cE.trans (.cons g1 (.cons g2 (.cons g3 (.cons g4 (.cons g5 (.cons g6 (.cons g7 (.cons g8 (.cons g9
    (.cons g10 (.cons g11 (.cons g12 (.cons g13 (.single g14))))))))))))))))))))))))))))))))))))))))))))
  refine ⟨f14, steps, ?_, spf, ?_, ?_, ?_⟩
  · rw [pc14, w13.oldReg w12.self.zero ra (by decide), add_lit_zero, finra, hra, hret]
  · intro q hq
    rcases hmem q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    · rw [regs14, w13.self.zero, hz]
    · rw [kf _ (by decide), finra]
    · rw [spf, hsp]
    · rw [kf _ (by decide), fins0]
    · rw [kf _ (by decide), fins1]
    · rw [kf _ (by decide), fins2]
    · rw [kf _ (by decide), fins3]
    · rw [kf _ (by decide), fins4]
    · rw [kf _ (by decide), fins5]
    · have hs : q ≠ sp := fun e => by subst e; exact absurd h (by decide)
      rw [kf q hs, pass q h]
  · rw [mem14, accV_congr2 10 (fun i hi => outw i hi), accR]
    congr 1
    exact accV_congr 8 fun i hi => load_frame MbG ((env.sXG.symm).subR (c := 4 * i) (l := 4) (by omega))
    exact accV_congr 2 fun i hi => load_frame MbG ((env.sYG.symm).subR (c := 4 * i) (l := 4) (by omega))
  · intro x hx ho
    rw [mem14, ← hMf', memStore32_get_sep (ho.sub (c := 36) (l := 4) (by decide)), ← hO1',
      memStore32_get_sep (ho.sub (c := 32) (l := 4) (by decide)), McG x hx ho]

end C3.RV32
