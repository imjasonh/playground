import C3BootProofs.Proofs.ShaUpdate

/-!
# SHA-256's `finalize`

The compiled `<sha2::Sha256 as digest::Digest>::finalize` pads the hasher's
buffer (0x80, zeros, and the message's length in bits, big-endian),
compresses the one or two blocks that makes, and writes the 8 hash words
big-endian to its output. It runs these helpers, each proved here:
`hybrid_array`'s `from_fn`, which zeroes a 32-byte array
(`shaZero32_correct`); the closure that copies a block to the stack and
compresses it (`shaFinBlock_correct`); and an outlined helper that stores
one word big-endian (`St.callStoreBe`).
-/

namespace C3.RV32

open C3.Image

section

set_option maxRecDepth 20000

theorem sz_at_0 : fetchRel shaZero32Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem sz_at_2 : fetchRel shaZero32Code 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem sz_at_4 : fetchRel shaZero32Code 0x4 = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem sz_at_6 : fetchRel shaZero32Code 0x6 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem sz_at_a : fetchRel shaZero32Code 0xA = some (.branch .beq a2 x0 0xC, 2) := by decide
theorem sz_at_c : fetchRel shaZero32Code 0xC = some (.store .sb a1 x0 0x0, 4) := by decide
theorem sz_at_10 : fetchRel shaZero32Code 0x10 = some (.aluImm .add a1 a1 0x1, 2) := by decide
theorem sz_at_12 : fetchRel shaZero32Code 0x12 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem sz_at_14 : fetchRel shaZero32Code 0x14 = some (.branch .bne a2 x0 0xFFFFFFF8, 2) := by decide
theorem sz_at_16 : fetchRel shaZero32Code 0x16 = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem sz_at_18 : fetchRel shaZero32Code 0x18 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem sz_at_1c : fetchRel shaZero32Code 0x1C = some (.auipc ra 0x12000, 4) := by decide
theorem sz_at_20 : fetchRel shaZero32Code 0x20 = some (.jalr ra ra 0x6C2, 4) := by decide
theorem sz_at_24 : fetchRel shaZero32Code 0x24 = some (.load .lw ra sp 0x2C, 2) := by decide
theorem sz_at_26 : fetchRel shaZero32Code 0x26 = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem sz_at_28 : fetchRel shaZero32Code 0x28 = some (.jalr x0 ra 0x0, 2) := by decide
theorem sk_at_0 : fetchRel shaFinalizeBlockCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFB0, 2) := by decide
theorem sk_at_2 : fetchRel shaFinalizeBlockCode 0x2 = some (.store .sw sp ra 0x4C, 2) := by decide
theorem sk_at_4 : fetchRel shaFinalizeBlockCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x48, 2) := by decide
theorem sk_at_6 : fetchRel shaFinalizeBlockCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem sk_at_8 : fetchRel shaFinalizeBlockCode 0x8 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem sk_at_a : fetchRel shaFinalizeBlockCode 0xA = some (.aluImm .add a2 x0 0x40, 4) := by decide
theorem sk_at_e : fetchRel shaFinalizeBlockCode 0xE = some (.auipc ra 0x19000, 4) := by decide
theorem sk_at_12 : fetchRel shaFinalizeBlockCode 0x12 = some (.jalr ra ra 0xFFFFFE82, 4) := by decide
theorem sk_at_16 : fetchRel shaFinalizeBlockCode 0x16 = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem sk_at_18 : fetchRel shaFinalizeBlockCode 0x18 = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem sk_at_1a : fetchRel shaFinalizeBlockCode 0x1A = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem sk_at_1c : fetchRel shaFinalizeBlockCode 0x1C = some (.auipc ra 0xD000, 4) := by decide
theorem sk_at_20 : fetchRel shaFinalizeBlockCode 0x20 = some (.jalr ra ra 0xFFFFFCD6, 4) := by decide
theorem sk_at_24 : fetchRel shaFinalizeBlockCode 0x24 = some (.load .lw ra sp 0x4C, 2) := by decide
theorem sk_at_26 : fetchRel shaFinalizeBlockCode 0x26 = some (.load .lw (8 : Fin 32) sp 0x48, 2) := by decide
theorem sk_at_28 : fetchRel shaFinalizeBlockCode 0x28 = some (.aluImm .add sp sp 0x50, 2) := by decide
theorem sk_at_2a : fetchRel shaFinalizeBlockCode 0x2A = some (.jalr x0 ra 0x0, 2) := by decide
theorem sbe_at_0 : fetchRel shaStoreBeCode 0x0 = some (.aluImm .srl a2 a1 0x18, 4) := by decide
theorem sbe_at_4 : fetchRel shaStoreBeCode 0x4 = some (.aluImm .srl a3 a1 0x8, 4) := by decide
theorem sbe_at_8 : fetchRel shaStoreBeCode 0x8 = some (.aluImm .srl a4 a1 0x10, 4) := by decide
theorem sbe_at_c : fetchRel shaStoreBeCode 0xC = some (.store .sb (8 : Fin 32) a2 0x0, 4) := by decide
theorem sbe_at_10 : fetchRel shaStoreBeCode 0x10 = some (.store .sb (8 : Fin 32) a4 0x1, 4) := by decide
theorem sbe_at_14 : fetchRel shaStoreBeCode 0x14 = some (.store .sb (8 : Fin 32) a3 0x2, 4) := by decide
theorem sbe_at_18 : fetchRel shaStoreBeCode 0x18 = some (.store .sb (8 : Fin 32) a1 0x3, 4) := by decide
theorem sbe_at_1c : fetchRel shaStoreBeCode 0x1C = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem sbe_at_1e : fetchRel shaStoreBeCode 0x1E = some (.jalr x0 (5 : Fin 32) 0x0, 2) := by decide
theorem sf_at_0 : fetchRel shaFinalizeCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFA0, 2) := by decide
theorem sf_at_2 : fetchRel shaFinalizeCode 0x2 = some (.auipc (5 : Fin 32) 0x19000, 4) := by decide
theorem sf_at_6 : fetchRel shaFinalizeCode 0x6 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFF984, 4) := by decide
theorem sf_at_a : fetchRel shaFinalizeCode 0xA = some (.store .sw sp (22 : Fin 32) 0x40, 2) := by decide
theorem sf_at_c : fetchRel shaFinalizeCode 0xC = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem sf_at_e : fetchRel shaFinalizeCode 0xE = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem sf_at_10 : fetchRel shaFinalizeCode 0x10 = some (.alu .add a0 x0 sp, 2) := by decide
theorem sf_at_12 : fetchRel shaFinalizeCode 0x12 = some (.auipc ra 0x7000, 4) := by decide
theorem sf_at_16 : fetchRel shaFinalizeCode 0x16 = some (.jalr ra ra 0xFFFFF8B8, 4) := by decide
theorem sf_at_1a : fetchRel shaFinalizeCode 0x1A = some (.aluImm .add (9 : Fin 32) (20 : Fin 32) 0x40, 4) := by decide
theorem sf_at_1e : fetchRel shaFinalizeCode 0x1E = some (.aluImm .add a0 sp 0x20, 2) := by decide
theorem sf_at_20 : fetchRel shaFinalizeCode 0x20 = some (.aluImm .add (8 : Fin 32) sp 0x20, 2) := by decide
theorem sf_at_22 : fetchRel shaFinalizeCode 0x22 = some (.auipc ra 0x7000, 4) := by decide
theorem sf_at_26 : fetchRel shaFinalizeCode 0x26 = some (.jalr ra ra 0xFFFFF8A8, 4) := by decide
theorem sf_at_2a : fetchRel shaFinalizeCode 0x2A = some (.load .lw a0 (20 : Fin 32) 0x60, 4) := by decide
theorem sf_at_2e : fetchRel shaFinalizeCode 0x2E = some (.load .lw a6 (20 : Fin 32) 0x64, 4) := by decide
theorem sf_at_32 : fetchRel shaFinalizeCode 0x32 = some (.load .lbu a2 (20 : Fin 32) 0x3F, 4) := by decide
theorem sf_at_36 : fetchRel shaFinalizeCode 0x36 = some (.lui a3 0x10000, 2) := by decide
theorem sf_at_38 : fetchRel shaFinalizeCode 0x38 = some (.aluImm .add a3 a3 0xFFFFFF00, 4) := by decide
theorem sf_at_3c : fetchRel shaFinalizeCode 0x3C = some (.aluImm .srl (17 : Fin 32) a0 0x17, 4) := by decide
theorem sf_at_40 : fetchRel shaFinalizeCode 0x40 = some (.aluImm .sll a5 a6 0x9, 4) := by decide
theorem sf_at_44 : fetchRel shaFinalizeCode 0x44 = some (.aluImm .sll a1 a0 0x9, 4) := by decide
theorem sf_at_48 : fetchRel shaFinalizeCode 0x48 = some (.aluImm .sll a4 a2 0x3, 4) := by decide
theorem sf_at_4c : fetchRel shaFinalizeCode 0x4C = some (.aluImm .sll a0 a0 0x1, 2) := by decide
theorem sf_at_4e : fetchRel shaFinalizeCode 0x4E = some (.alu .or (5 : Fin 32) a5 (17 : Fin 32), 4) := by decide
theorem sf_at_52 : fetchRel shaFinalizeCode 0x52 = some (.alu .or a4 a4 a1, 2) := by decide
theorem sf_at_54 : fetchRel shaFinalizeCode 0x54 = some (.alu .and a0 a0 a3, 2) := by decide
theorem sf_at_56 : fetchRel shaFinalizeCode 0x56 = some (.aluImm .srl a1 a1 0x18, 2) := by decide
theorem sf_at_58 : fetchRel shaFinalizeCode 0x58 = some (.alu .or a0 a0 a1, 2) := by decide
theorem sf_at_5a : fetchRel shaFinalizeCode 0x5A = some (.alu .and a4 a4 a3, 2) := by decide
theorem sf_at_5c : fetchRel shaFinalizeCode 0x5C = some (.aluImm .sll a4 a4 0x8, 2) := by decide
theorem sf_at_5e : fetchRel shaFinalizeCode 0x5E = some (.aluImm .sll a1 a2 0x1B, 4) := by decide
theorem sf_at_62 : fetchRel shaFinalizeCode 0x62 = some (.alu .or a0 a0 a1, 2) := by decide
theorem sf_at_64 : fetchRel shaFinalizeCode 0x64 = some (.aluImm .sll a6 a6 0x1, 2) := by decide
theorem sf_at_66 : fetchRel shaFinalizeCode 0x66 = some (.alu .and a1 a6 a3, 4) := by decide
theorem sf_at_6a : fetchRel shaFinalizeCode 0x6A = some (.aluImm .srl a5 a5 0x18, 2) := by decide
theorem sf_at_6c : fetchRel shaFinalizeCode 0x6C = some (.alu .or (21 : Fin 32) a0 a4, 4) := by decide
theorem sf_at_70 : fetchRel shaFinalizeCode 0x70 = some (.alu .or a1 a1 a5, 2) := by decide
theorem sf_at_72 : fetchRel shaFinalizeCode 0x72 = some (.alu .and a0 (5 : Fin 32) a3, 4) := by decide
theorem sf_at_76 : fetchRel shaFinalizeCode 0x76 = some (.aluImm .sll (17 : Fin 32) (17 : Fin 32) 0x18, 2) := by decide
theorem sf_at_78 : fetchRel shaFinalizeCode 0x78 = some (.aluImm .sll a0 a0 0x8, 2) := by decide
theorem sf_at_7a : fetchRel shaFinalizeCode 0x7A = some (.alu .or a1 (17 : Fin 32) a1, 4) := by decide
theorem sf_at_7e : fetchRel shaFinalizeCode 0x7E = some (.alu .or (22 : Fin 32) a1 a0, 4) := by decide
theorem sf_at_82 : fetchRel shaFinalizeCode 0x82 = some (.aluImm .xor (19 : Fin 32) a2 0x3F, 4) := by decide
theorem sf_at_86 : fetchRel shaFinalizeCode 0x86 = some (.alu .add a0 (20 : Fin 32) a2, 4) := by decide
theorem sf_at_8a : fetchRel shaFinalizeCode 0x8A = some (.aluImm .add a1 x0 0x80, 4) := by decide
theorem sf_at_8e : fetchRel shaFinalizeCode 0x8E = some (.store .sb a0 a1 0x0, 4) := by decide
theorem sf_at_92 : fetchRel shaFinalizeCode 0x92 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem sf_at_94 : fetchRel shaFinalizeCode 0x94 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem sf_at_96 : fetchRel shaFinalizeCode 0x96 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem sf_at_98 : fetchRel shaFinalizeCode 0x98 = some (.auipc ra 0x19000, 4) := by decide
theorem sf_at_9c : fetchRel shaFinalizeCode 0x9C = some (.jalr ra ra 0xFFFFFEA8, 4) := by decide
theorem sf_at_a0 : fetchRel shaFinalizeCode 0xA0 = some (.aluImm .add a0 x0 0x7, 2) := by decide
theorem sf_at_a2 : fetchRel shaFinalizeCode 0xA2 = some (.branch .bltu a0 (19 : Fin 32) 0x20, 4) := by decide
theorem sf_at_a6 : fetchRel shaFinalizeCode 0xA6 = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem sf_at_a8 : fetchRel shaFinalizeCode 0xA8 = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem sf_at_aa : fetchRel shaFinalizeCode 0xAA = some (.auipc ra 0x0, 4) := by decide
theorem sf_at_ae : fetchRel shaFinalizeCode 0xAE = some (.jalr ra ra 0x6E, 4) := by decide
theorem sf_at_b2 : fetchRel shaFinalizeCode 0xB2 = some (.aluImm .add a2 x0 0x38, 4) := by decide
theorem sf_at_b6 : fetchRel shaFinalizeCode 0xB6 = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem sf_at_b8 : fetchRel shaFinalizeCode 0xB8 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem sf_at_ba : fetchRel shaFinalizeCode 0xBA = some (.auipc ra 0x19000, 4) := by decide
theorem sf_at_be : fetchRel shaFinalizeCode 0xBE = some (.jalr ra ra 0xFFFFFE86, 4) := by decide
theorem sf_at_c2 : fetchRel shaFinalizeCode 0xC2 = some (.store .sw (20 : Fin 32) (22 : Fin 32) 0x38, 4) := by decide
theorem sf_at_c6 : fetchRel shaFinalizeCode 0xC6 = some (.store .sw (20 : Fin 32) (21 : Fin 32) 0x3C, 4) := by decide
theorem sf_at_ca : fetchRel shaFinalizeCode 0xCA = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem sf_at_cc : fetchRel shaFinalizeCode 0xCC = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem sf_at_ce : fetchRel shaFinalizeCode 0xCE = some (.auipc ra 0x0, 4) := by decide
theorem sf_at_d2 : fetchRel shaFinalizeCode 0xD2 = some (.jalr ra ra 0x4A, 4) := by decide
theorem sf_at_d6 : fetchRel shaFinalizeCode 0xD6 = some (.aluImm .add a0 x0 0x8, 2) := by decide
theorem sf_at_d8 : fetchRel shaFinalizeCode 0xD8 = some (.branch .beq a0 x0 0x12, 2) := by decide
theorem sf_at_da : fetchRel shaFinalizeCode 0xDA = some (.load .lw a1 (9 : Fin 32) 0x0, 2) := by decide
theorem sf_at_dc : fetchRel shaFinalizeCode 0xDC = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem sf_at_de : fetchRel shaFinalizeCode 0xDE = some (.auipc (5 : Fin 32) 0x19000, 4) := by decide
theorem sf_at_e2 : fetchRel shaFinalizeCode 0xE2 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFF998, 4) := by decide
theorem sf_at_e6 : fetchRel shaFinalizeCode 0xE6 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem sf_at_e8 : fetchRel shaFinalizeCode 0xE8 = some (.branch .bne a0 x0 0xFFFFFFF2, 2) := by decide
theorem sf_at_ea : fetchRel shaFinalizeCode 0xEA = some (.alu .add a0 x0 sp, 2) := by decide
theorem sf_at_ec : fetchRel shaFinalizeCode 0xEC = some (.aluImm .add a1 sp 0x20, 2) := by decide
theorem sf_at_ee : fetchRel shaFinalizeCode 0xEE = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem sf_at_f2 : fetchRel shaFinalizeCode 0xF2 = some (.auipc ra 0x19000, 4) := by decide
theorem sf_at_f6 : fetchRel shaFinalizeCode 0xF6 = some (.jalr ra ra 0xFFFFFEB6, 4) := by decide
theorem sf_at_fa : fetchRel shaFinalizeCode 0xFA = some (.alu .add a1 x0 sp, 2) := by decide
theorem sf_at_fc : fetchRel shaFinalizeCode 0xFC = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem sf_at_100 : fetchRel shaFinalizeCode 0x100 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem sf_at_102 : fetchRel shaFinalizeCode 0x102 = some (.auipc ra 0x19000, 4) := by decide
theorem sf_at_106 : fetchRel shaFinalizeCode 0x106 = some (.jalr ra ra 0xFFFFFEA6, 4) := by decide
theorem sf_at_10a : fetchRel shaFinalizeCode 0x10A = some (.auipc (5 : Fin 32) 0x19000, 4) := by decide
theorem sf_at_10e : fetchRel shaFinalizeCode 0x10E = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFF86C, 4) := by decide
theorem sf_at_112 : fetchRel shaFinalizeCode 0x112 = some (.load .lw (22 : Fin 32) sp 0x40, 2) := by decide
theorem sf_at_114 : fetchRel shaFinalizeCode 0x114 = some (.aluImm .add sp sp 0x60, 2) := by decide
theorem sf_at_116 : fetchRel shaFinalizeCode 0x116 = some (.jalr x0 ra 0x0, 2) := by decide

end

set_option maxRecDepth 20000 in
/-- `from_fn`'s loop, from offset 0xC: it stores a zero byte and moves on,
until the count runs out. -/
theorem zero_loop {M1 : Word → BitVec 8} {B : Word}
    (hc : ∀ j, j ≤ 32 → CodeIn (fillBytes M1 B 0 j) (BitVec.ofNat 32 shaZero32Address) shaZero32Code) :
    ∀ k q (n : Machine), q + k = 32 → 0 < k →
      St (fillBytes M1 B 0 q) (BitVec.ofNat 32 shaZero32Address) n 0xC (reg n) →
      reg n a2 = BitVec.ofNat 32 k → reg n a1 = B + BitVec.ofNat 32 q →
      ∃ n', Steps n n' ∧ St (fillBytes M1 B 0 32) (BitVec.ofNat 32 shaZero32Address) n' 0x16 (reg n') ∧
        ∀ r, r ≠ a1 → r ≠ a2 → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro q n hqe _ s ha2 ha1
    have hcq := hc q (by omega)
    have hcq1 := hc (q + 1) (by omega)
    obtain ⟨n1, d1, u1⟩ := s.sb hcq sz_at_c (off' := 0x10) (by decide)
    rw [ha1, add_lit_zero, s.zero, show (0 : Word).extractLsb' 0 8 = (0 : BitVec 8) from rfl,
      fillBytes_succ (by omega)] at u1
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hcq1 sz_at_10 (off' := 0x12) (by decide)
    obtain ⟨n3, d3, u3⟩ := u2.aluImm hcq1 sz_at_12 (off' := 0x14) (by decide)
    have r3 : ∀ r, reg n3 r = upd (upd (reg n) a1 (B + BitVec.ofNat 32 (q + 1))) a2 (BitVec.ofNat 32 k) r := by
      intro r
      rw [u3.regs]
      simp only [upd, show (a2 : Fin 32) ≠ a1 by decide, ite_false, ha2, ha1,
        dec_ofNat_succ (show k + 1 < 2 ^ 32 by omega), show (12 : Fin 32).val ≠ 0 by decide]
      rw [show aluEval .add (B + BitVec.ofNat 32 q) 1 = B + BitVec.ofNat 32 (q + 1) from add_ofNat_assoc B q 1]
    have frame : ∀ r, r ≠ a1 → r ≠ a2 → reg n3 r = reg n r := fun r h1 h2 => by
      rw [r3]; simp only [upd, h1, h2, ite_false]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp; exact s.zero.symm
      · simp [h0]
    have c3 : reg n3 a2 = BitVec.ofNat 32 k := by rw [r3]; simp +decide [upd]
    have p3 : reg n3 a1 = B + BitVec.ofNat 32 (q + 1) := by rw [r3]; simp +decide [upd]
    have z3 : reg n3 x0 = 0 := u3.self.zero
    have u3' : St (fillBytes M1 B 0 (q + 1)) (BitVec.ofNat 32 shaZero32Address) n3 0x14 (reg n3) := u3.self
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n4, d4, u4⟩ := u3'.notTaken hcq1 0x16 sz_at_14 (by decide) (by simp [branchTaken, c3, z3])
      have hq : q + 1 = 32 := by omega
      rw [hq] at u4
      exact ⟨n4, .cons d1 (.cons d2 (.cons d3 (.single d4))), u4.self,
        fun r h1 h2 => by rw [u4.regs, frame r h1 h2]⟩
    · obtain ⟨n4, d4, u4⟩ := u3'.taken hcq1 0xC sz_at_14 (by decide) (by
        simp only [branchTaken, c3, z3, bne_iff_ne, ne_eq]
        intro h; exact hk (ofNat_inj (by omega) (by decide) h))
      obtain ⟨n5, c5, u5, f5⟩ := ih (q + 1) n4 (by omega) (by omega) u4.self
        (by rw [u4.regs, c3]) (by rw [u4.regs, p3])
      exact ⟨n5, .cons d1 (.cons d2 (.cons d3 (.cons d4 c5))), u5,
        fun r h1 h2 => by rw [f5 r h1 h2, u4.regs, frame r h1 h2]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **`hybrid_array`'s zeroing `from_fn` for 32 bytes, as compiled.** Called
with `d`, it zeroes the 32 bytes at `d`: it fills 32 bytes of its stack
frame with zeros, one byte at a time, and copies them to `d` with `memcpy`.
It returns with `sp` restored and changes no memory outside `d` and the 0x40
bytes of stack below `sp`. Both `d` and the stack are below 0x40000000,
apart from the code. -/
theorem shaZero32_correct (m : Machine) {d T retAddr : Word}
    (hc : CodeIn m.mem (BitVec.ofNat 32 shaZero32Address) shaZero32Code)
    (hMS : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode)
    (hMB : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode)
    (hpc : m.pc = BitVec.ofNat 32 shaZero32Address) (ha0 : reg m a0 = d) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = T) (hTa : T.toNat % 16 = 0)
    (hTl : 0x40 ≤ T.toNat) (hTw : T.toNat ≤ 0x40000000) (hdw : d.toNat + 32 ≤ 0x40000000)
    (hdT : Sep d 32 (T + 0xFFFFFFC0) 0x40) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = T ∧
      (∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → reg m' r = reg m r) ∧
      ∀ x, Sep (T + 0xFFFFFFC0) 0x40 x 1 → m'.mem x = fillBytes m.mem d 0 32 x := by
  let Z := BitVec.ofNat 32 shaZero32Address
  let M0 := m.mem
  let R := T + 0xFFFFFFC0
  have hRn : R.toNat = T.toNat - 0x40 := by
    show (T + 0xFFFFFFC0).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFFC0 : Word).toNat = 2 ^ 32 - 0x40 from rfl]; omega
  have hRc : ∀ c, c < 0x40 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- Data below 0x40000000 is apart from code above it.
  have dc : ∀ (a : Word) (k : Nat) (b : Word) (l : Nat), a.toNat + k ≤ 0x40000000 → 0x40000000 ≤ b.toNat →
      b.toNat + l ≤ 2 ^ 32 → Sep a k b l := fun a k b l h1 h2 h3 => data_code h1 h2 h3
  have st0 : St M0 Z m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  obtain ⟨n1, d1, u1⟩ := st0.aluImm hc sz_at_0 (off' := 2) (by decide)
  have K1 := u1.upd_ne st0.zero
  have u1' : St M0 Z n1 2 (reg n1) := u1.self
  have sp1 : reg n1 sp = R + BitVec.ofNat 32 0x10 := by
    rw [u1.upd_eq (by decide), hsp]
    show T + 0xFFFFFFD0 = T + 0xFFFFFFC0 + BitVec.ofNat 32 0x10; rw [BitVec.add_assoc]; rfl
  obtain ⟨n2, d2, u2⟩ := u1'.sw hc sz_at_2 (off' := 4) (by decide)
    (by rw [sp1, show (0x2C : Word) = BitVec.ofNat 32 0x2C from rfl, add_ofNat_assoc, hRc _ (by omega)]; have := hTa; omega)
  rw [sp1, show (0x2C : Word) = BitVec.ofNat 32 0x2C from rfl, add_ofNat_assoc, K1 ra (by decide), hra] at u2
  let M1 := memStore32 M0 (R + BitVec.ofNat 32 (0x10 + 0x2C)) retAddr
  have cM1 : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn M1 b code := fun b code h hb hbl =>
    h.store32 (dc _ _ _ _ (by rw [hRc _ (by omega)]; omega) hb hbl)
  have hc1 := cM1 _ _ hc (by decide) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.aluImm hc1 sz_at_4 (off' := 6) (by decide)
  have K3 := u3.upd_ne u1'.zero
  have u3' : St M1 Z n3 6 (reg n3) := u3.self
  obtain ⟨n4, d4, u4⟩ := u3'.aluImm hc1 sz_at_6 (off' := 0xA) (by decide)
  have K4' := u4.upd_ne u3'.zero
  have K4 : ∀ r, r ≠ a1 → r ≠ a2 → reg n4 r = reg n1 r := fun r q1 q2 => by rw [K4' r q2, K3 r q1]
  have a2_4 : reg n4 a2 = BitVec.ofNat 32 32 := by rw [u4.upd_eq (by decide), u3'.zero]; rfl
  have a1_4 : reg n4 a1 = R + BitVec.ofNat 32 0x1C := by
    rw [K4' a1 (by decide), u3.upd_eq (by decide), sp1]
    show R + BitVec.ofNat 32 0x10 + BitVec.ofNat 32 0xC = _; rw [add_ofNat_assoc]
  have u4' : St M1 Z n4 0xA (reg n4) := u4.self
  obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc1 0xC sz_at_a (by decide) (by
    simp only [branchTaken]; rw [a2_4, u4'.zero]; decide)
  let B := R + BitVec.ofNat 32 0x1C
  have hBs : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 → Sep B 32 b l :=
    fun b l hb hbl => dc _ _ _ _ (by rw [hRc _ (by omega)]; omega) hb hbl
  have hcF : ∀ j, j ≤ 32 → CodeIn (fillBytes M1 B 0 j) Z shaZero32Code := fun j hj =>
    hc1.fillBytes (hBs _ _ (by decide) (by decide)) hj
  rw [← fillBytes_zero M1 B 0] at u5
  obtain ⟨n6, c6, u6, K6⟩ := zero_loop hcF 32 0 n5 rfl (by decide) u5.self
    (by rw [u5.regs, a2_4]) (by rw [u5.regs, a1_4, add_ofNat_zero])
  let Mf := fillBytes M1 B 0 32
  have hcf := hcF 32 (Nat.le_refl 32)
  obtain ⟨n7, d7, u7⟩ := u6.aluImm hcf sz_at_16 (off' := 0x18) (by decide)
  obtain ⟨n8, d8, u8⟩ := u7.aluImm hcf sz_at_18 (off' := 0x1C) (by decide)
  obtain ⟨n9, d9, u9⟩ := u8.auipc hcf sz_at_1c (off' := 0x20) (by decide)
  obtain ⟨n10, d10, pc10, mem10, regs10⟩ := u9.call hcf sz_at_20
  have K6' : ∀ r, r ≠ a1 → r ≠ a2 → reg n6 r = reg n1 r := fun r q1 q2 => by
    rw [K6 r q1 q2, u5.regs, K4 r q1 q2]
  have sp6 : reg n6 sp = R + BitVec.ofNat 32 0x10 := by rw [K6' sp (by decide) (by decide), sp1]
  have r10 : ∀ r, reg n10 r = upd (upd (upd (upd (reg n6) a1 (B)) a2 (BitVec.ofNat 32 32)) ra
      (Z + BitVec.ofNat 32 0x1C + 0x12000)) ra (Z + BitVec.ofNat 32 0x24) r := by
    intro r
    rw [regs10]
    have e1 : aluEval .add (reg n6 sp) 0xC = B := by
      rw [sp6]; show R + BitVec.ofNat 32 0x10 + BitVec.ofNat 32 0xC = R + BitVec.ofNat 32 0x1C
      rw [add_ofNat_assoc]
    have e2 : aluEval .add (upd (reg n6) a1 (aluEval .add (reg n6 sp) 0xC) x0) 0x20 = BitVec.ofNat 32 32 := by
      simp only [upd, show (x0 : Fin 32).val = 0 from rfl, ite_true]; rfl
    rw [e2, e1, show Z + BitVec.ofNat 32 0x20 + 4 = Z + BitVec.ofNat 32 0x24 from by
      rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]]
  have K10 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ ra → reg n10 r = reg n1 r := fun r q1 q2 q3 => by
    rw [r10]; simp only [upd, q1, q2, q3, ite_false]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp; exact (K6' 0 (by decide) (by decide)).trans u1'.zero |>.symm
    · simp [h0, K6' r q1 q2]
  have pc10' : n10.pc = BitVec.ofNat 32 memcpyStubAddress := by
    rw [pc10, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
    decide
  have sp10 : reg n10 sp = R + BitVec.ofNat 32 0x10 := by
    rw [K10 sp (by decide) (by decide) (by decide), sp1]
  have eF : R + BitVec.ofNat 32 0x10 + 0xFFFFFFF0 = R := by
    rw [BitVec.add_assoc]; exact BitVec.add_zero R
  obtain ⟨n11, c11, pc11, sp11, a011, mem11, K11⟩ := memcpy_correct n10 (BitVec.ofNat 32 memcpyStubAddress)
    (Z + BitVec.ofNat 32 0x24) d B 32
    (fun i hi => by
      show n10.mem _ = _; rw [mem10]
      exact ((cM1 _ _ hMS (by decide) (by decide)).fillBytes (hBs _ _ (by decide) (by decide)) (Nat.le_refl 32)) i hi)
    (by decide) pc10'
    (by rw [K10 a0 (by decide) (by decide) (by decide), K1 a0 (by decide), ha0])
    (by rw [r10]; simp +decide [upd])
    (by rw [r10]; simp +decide [upd])
    (by rw [r10]; simp +decide [upd]) (by decide)
    (by
      rw [mem10, sp10, eF]
      exact { code := (cM1 _ _ hMB (by decide) (by decide)).fillBytes (hBs _ _ (by decide) (by decide))
                (Nat.le_refl 32)
              hDC := dc _ _ _ _ hdw (by decide) (by decide)
              hFC := dc _ _ _ _ (by omega) (by decide) (by decide)
              hdF := by have h := hdT.subR (c := 0) (l := 16) (by omega); rwa [add_ofNat_zero] at h
              hsF := by
                have h := sep_offsets R (c := 0x1C) (n := 32) (d := 0) (k := 16) (Or.inr (by omega)) (by omega)
                  (by omega)
                rwa [add_ofNat_zero] at h
              hsep := hdT.subR (c := 0x1C) (l := 32) (by omega)
              hF := by rw [hRn]; omega
              hFw := by omega
              hdw := by omega
              hsw := by rw [hRc _ (by omega)]; omega })
  rw [sp10, eF, mem10] at mem11
  let MA := n11.mem
  have mA : ∀ x, Sep R 16 x 1 → MA x = copyBytes Mf d B 32 x := mem11
  have cA : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn MA b code := fun b code h hb hbl i hi => by
    rw [mA _ ((dc R 16 b code.length (by omega) hb hbl).subR (c := i) (l := 1) (by omega)),
      copyBytes_sep ((dc d 32 b code.length hdw hb hbl).subR (c := i) (l := 1) (by omega)) (Nat.le_refl 32)]
    exact (cM1 _ _ h hb hbl).fillBytes (hBs _ _ hb hbl) (Nat.le_refl 32) i hi
  have hcA := cA _ _ hc (by decide) (by decide)
  have u11 : St MA Z n11 0x24 (reg n11) := ⟨by rw [pc11], rfl, fun _ => rfl⟩
  have sp11' : reg n11 sp = R + BitVec.ofNat 32 0x10 := by rw [sp11, sp10]
  obtain ⟨n12, d12, u12⟩ := u11.lw hcA sz_at_24 (off' := 0x26) (by decide)
    (by rw [sp11', show (0x2C : Word) = BitVec.ofNat 32 0x2C from rfl, add_ofNat_assoc, hRc _ (by omega)]; have := hTa; omega)
  have slot : memLoad32 MA (reg n11 sp + 0x2C) = retAddr := by
    rw [sp11', show (0x2C : Word) = BitVec.ofNat 32 0x2C from rfl, add_ofNat_assoc, ← memLoad32_store32_same M0 (R + BitVec.ofNat 32 (0x10 + 0x2C)) retAddr]
    apply memLoad32_congr; intro j hj
    rw [add_ofNat_assoc]
    have hx1 : Sep R 16 (R + BitVec.ofNat 32 (0x10 + 0x2C + j)) 1 :=
      sep_offsets R (c := 0) (n := 16) (d := 0x10 + 0x2C + j) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
        |> fun h => by rwa [add_ofNat_zero] at h
    rw [mA _ hx1, copyBytes_sep ((hdT.subR (c := 0x10 + 0x2C + j) (l := 1) (by omega))) (Nat.le_refl 32)]
    show fillBytes M1 B 0 32 _ = _
    exact fillBytes_sep (sep_offsets R (c := 0x1C) (n := 32) (d := 0x10 + 0x2C + j) (k := 1) (Or.inl (by omega))
      (by omega) (by omega)) (Nat.le_refl 32)
  rw [slot] at u12
  have K12 := u12.upd_ne u11.zero
  have u12' : St MA Z n12 0x26 (reg n12) := u12.self
  obtain ⟨n13, d13, u13⟩ := u12'.aluImm hcA sz_at_26 (off' := 0x28) (by decide)
  have K13 := u13.upd_ne u12'.zero
  have u13' : St MA Z n13 0x28 (reg n13) := u13.self
  obtain ⟨n14, d14, pc14, mem14, regs14⟩ := u13'.jalr hcA sz_at_28
  have ra13 : reg n13 ra = retAddr := by rw [K13 ra (by decide), u12.upd_eq (by decide)]
  have sp13 : reg n13 sp = T := by
    rw [u13.upd_eq (by decide), K12 sp (by decide), sp11']
    show R + BitVec.ofNat 32 0x10 + 0x30 = T
    rw [BitVec.add_assoc]; show T + 0xFFFFFFC0 + (BitVec.ofNat 32 0x10 + 0x30) = T
    rw [BitVec.add_assoc]; exact BitVec.add_zero T
  have k11 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg n11 r = reg n10 r := K11
  refine ⟨n14, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (c6.trans (.cons d7 (.cons d8 (.cons d9
    (.cons d10 (c11.trans (.cons d12 (.cons d13 (.single d14))))))))))))), ?_, ?_,
    fun r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 => ?_, fun x hx => ?_⟩
  · rw [pc14, ra13, add_lit_zero, hret]
  · rw [regs14, sp13]
  · rw [regs14]
    by_cases hra' : r = ra
    · subst hra'; rw [ra13, hra]
    by_cases hsp' : r = sp
    · subst hsp'; rw [sp13, hsp]
    rw [K13 r hsp', K12 r hra', k11 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 hsp', K10 r q11 q12 hra',
      K1 r hsp']
  · rw [mem14]
    show MA x = _
    rw [mA x (hx.sub (c := 0) (l := 16) (by omega) |> fun h => by rwa [add_ofNat_zero] at h)]
    unfold copyBytes fillBytes
    by_cases hin : (x - d).toNat < 32
    · rw [ite_eq_left hin, ite_eq_left hin]
      show fillBytes M1 B 0 32 _ = _
      unfold fillBytes
      rw [BitVec.add_comm B, BitVec.add_sub_cancel, ite_eq_left hin]
    · rw [ite_eq_right hin, ite_eq_right hin]
      show fillBytes M1 B 0 32 x = M0 x
      rw [fillBytes_sep (hx.sub (c := 0x1C) (l := 32) (by omega)) (Nat.le_refl 32)]
      exact memStore32_ne fun i hi e => hx (0x10 + 0x2C + i) (by omega) 0 (by decide)
        (by rw [add_ofNat_zero, ← add_ofNat_assoc]; exact e.symm)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- **The block closure of `finalize`, as compiled.** Called with the hash
state at `st` and a block at `bp`, it copies the block into its stack frame
with `memcpy` and compresses it into the state with `compress256`. It
returns with `ra`, `sp`, and `s0` through `s11` restored, and changes no
memory outside the state and the 0x130 bytes of stack below `sp`. The state,
the block, and the stack are below 0x40000000, apart from the code, and
apart from the round constants. -/
theorem shaFinBlock_correct (m : Machine) {st bp T retAddr : Word}
    (hk : CodeIn m.mem (BitVec.ofNat 32 shaFinalizeBlockAddress) shaFinalizeBlockCode)
    (hMS : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode)
    (hMB : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode)
    (hC : CodeIn m.mem (BitVec.ofNat 32 sha256CompressAddress) sha256CompressCode)
    (hI : CodeIn m.mem (BitVec.ofNat 32 sha256CompressAddress + 0x2B94) shaIndexCode)
    (h97 : CodeIn m.mem (BitVec.ofNat 32 sha256CompressAddress + 0xC09C) shaSigma1PartCode)
    (hK : CodeIn m.mem (BitVec.ofNat 32 shaKAddress) shaKData)
    (hpc : m.pc = BitVec.ofNat 32 shaFinalizeBlockAddress) (ha0 : reg m a0 = st) (ha1 : reg m a1 = bp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = T)
    (hTa : T.toNat % 16 = 0) (hTl : 0x130 ≤ T.toNat) (hTw : T.toNat ≤ 0x40000000)
    (hsta : st.toNat % 4 = 0) (hstw : st.toNat + 32 ≤ 0x40000000) (hbw : bp.toNat + 64 ≤ 0x40000000)
    (hsT : Sep st 32 (T + 0xFFFFFED0) 0x130) (hbT : Sep bp 64 (T + 0xFFFFFED0) 0x130)
    (hKT : Sep (BitVec.ofNat 32 shaKAddress) 256 (T + 0xFFFFFED0) 0x130)
    (hKs : Sep (BitVec.ofNat 32 shaKAddress) 256 st 32) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = T ∧
      (∀ r, r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 →
        r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) →
        r ≠ (31 : Fin 32) → reg m' r = reg m r) ∧
      wordsAt m'.mem st 8 = Sha256.compress (wordsAt m.mem st 8) (memBytes m.mem bp 64) ∧
      ∀ x, Sep (T + 0xFFFFFED0) 0x130 x 1 → Sep st 32 x 1 → m'.mem x = m.mem x := by
  let Kb := BitVec.ofNat 32 shaFinalizeBlockAddress
  let M0 := m.mem
  let R := T + 0xFFFFFED0
  have hRn : R.toNat = T.toNat - 0x130 := by
    show (T + 0xFFFFFED0).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFED0 : Word).toNat = 2 ^ 32 - 0x130 from rfl]; omega
  have hRc : ∀ c, c ≤ 0x130 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have RC : ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 → Sep R 0xE0 b k :=
    fun b k hb hbk => data_code (by omega) hb hbk
  have dc : ∀ (a : Word) (k : Nat) (b : Word) (l : Nat), a.toNat + k ≤ 0x40000000 → 0x40000000 ≤ b.toNat →
      b.toNat + l ≤ 2 ^ 32 → Sep a k b l := fun a k b l h1 h2 h3 => data_code h1 h2 h3
  -- Every address this function writes is `R + c` for some `c < 0x130`.
  have Rd : ∀ c l, c + l ≤ 0x130 → ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (R + BitVec.ofNat 32 c) l b k := fun c l h b k hb hbk =>
    dc _ _ _ _ (by rw [hRc _ (by omega)]; omega) hb hbk
  have st0 : St M0 Kb m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  obtain ⟨n1, d1, u1⟩ := st0.aluImm hk sk_at_0 (off' := 2) (by decide)
  have K1 := u1.upd_ne st0.zero
  have u1' : St M0 Kb n1 2 (reg n1) := u1.self
  have sp1 : reg n1 sp = R + BitVec.ofNat 32 0xE0 := by
    rw [u1.upd_eq (by decide), hsp]
    show T + 0xFFFFFFB0 = T + 0xFFFFFED0 + BitVec.ofNat 32 0xE0; rw [BitVec.add_assoc]; rfl
  obtain ⟨n2, d2, u2⟩ := u1'.sw hk sk_at_2 (off' := 4) (by decide)
    (by rw [sp1, show (0x4C : Word) = BitVec.ofNat 32 0x4C from rfl, add_ofNat_assoc, hRc _ (by omega)]
        have := hTa; omega)
  rw [sp1, show (0x4C : Word) = BitVec.ofNat 32 0x4C from rfl, add_ofNat_assoc, K1 ra (by decide), hra] at u2
  have hk2 := hk.store32 (v := retAddr) (Rd (0xE0 + 0x4C) 4 (by omega) _ _ (by decide) (by decide))
  obtain ⟨n3, d3, u3⟩ := u2.sw hk2 sk_at_4 (off' := 6) (by decide)
    (by rw [sp1, show (0x48 : Word) = BitVec.ofNat 32 0x48 from rfl, add_ofNat_assoc, hRc _ (by omega)]
        have := hTa; omega)
  rw [sp1, show (0x48 : Word) = BitVec.ofNat 32 0x48 from rfl, add_ofNat_assoc] at u3
  let M1 := memStore32 (memStore32 M0 (R + BitVec.ofNat 32 (0xE0 + 0x4C)) retAddr)
    (R + BitVec.ofNat 32 (0xE0 + 0x48)) (reg n1 s0)
  have cM1 : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn M1 b code := fun b code h hb hbl =>
    (h.store32 (Rd _ 4 (by omega) _ _ hb hbl)).store32 (Rd _ 4 (by omega) _ _ hb hbl)
  have hk3 := cM1 _ _ hk (by decide) (by decide)
  have M1o : ∀ x, Sep (R + BitVec.ofNat 32 (0xE0 + 0x48)) 8 x 1 → M1 x = M0 x := fun x hx => by
    show memStore32 (memStore32 M0 _ _) _ _ x = _
    rw [memStore32_ne fun i hi e => hx i (by omega) 0 (by decide) (by rw [add_ofNat_zero]; exact e.symm),
      memStore32_ne fun i hi e => hx (4 + i) (by omega) 0 (by decide)
        (by rw [add_ofNat_zero, add_ofNat_assoc, show 0xE0 + 0x48 + (4 + i) = 0xE0 + 0x4C + i by omega,
              ← add_ofNat_assoc]
            exact e.symm)]
  obtain ⟨n4, d4, u4⟩ := u3.alu hk3 sk_at_6 (off' := 8) (by decide)
  have K4 := u4.upd_ne u1'.zero
  have u4' : St M1 Kb n4 8 (reg n4) := u4.self
  have s0_4 : reg n4 s0 = st := by
    rw [u4.upd_eq (by decide), u1'.zero, K1 a0 (by decide), ha0]; exact BitVec.zero_add _
  obtain ⟨n5, d5, u5⟩ := u4'.aluImm hk3 sk_at_8 (off' := 0xA) (by decide)
  have K5 := u5.upd_ne u4'.zero
  have u5' : St M1 Kb n5 0xA (reg n5) := u5.self
  obtain ⟨n6, d6, u6⟩ := u5'.aluImm hk3 sk_at_a (off' := 0xE) (by decide)
  have K6 := u6.upd_ne u5'.zero
  have u6' : St M1 Kb n6 0xE (reg n6) := u6.self
  obtain ⟨n7, d7, u7⟩ := u6'.auipc hk3 sk_at_e (off' := 0x12) (by decide)
  obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.call hk3 sk_at_12
  have r8 : ∀ r, r ≠ ra → reg n8 r = reg n6 r := fun r h => by
    rw [regs8]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u6'.zero.symm
    · simp [upd, h0, h]
  have ra8 : reg n8 ra = Kb + BitVec.ofNat 32 0x16 := by rw [regs8]; simp +decide [upd]; rfl
  have pc8' : n8.pc = BitVec.ofNat 32 memcpyStubAddress := by
    rw [pc8, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
    decide
  -- From `n1` to `n8`, only `s0`, `a0`, `a2`, and `ra` change.
  have K18 : ∀ r, r ≠ ra → r ≠ s0 → r ≠ a0 → r ≠ a2 → reg n8 r = reg n1 r := fun r q1 q8 q10 q12 => by
    rw [r8 r q1, K6 r q12, K5 r q10, K4 r q8]
  have sp8 : reg n8 sp = R + BitVec.ofNat 32 0xE0 := by
    rw [K18 sp (by decide) (by decide) (by decide) (by decide), sp1]
  have eF : R + BitVec.ofNat 32 0xE0 + 0xFFFFFFF0 = R + BitVec.ofNat 32 0xD0 := by
    rw [BitVec.add_assoc]; rfl
  have eB : aluEval .add (R + BitVec.ofNat 32 0xE0) 8 = R + BitVec.ofNat 32 0xE8 := by
    show R + BitVec.ofNat 32 0xE0 + BitVec.ofNat 32 8 = _; rw [add_ofNat_assoc]
  let Bk := R + BitVec.ofNat 32 0xE8
  obtain ⟨n9, c9, pc9, sp9, a09, mem9, K9⟩ := memcpy_correct n8 (BitVec.ofNat 32 memcpyStubAddress)
    (Kb + BitVec.ofNat 32 0x16) Bk bp 64
    (fun i hi => by show n8.mem _ = _; rw [mem8]; exact (cM1 _ _ hMS (by decide) (by decide)) i hi)
    (by decide) pc8'
    (by rw [r8 a0 (by decide), K6 a0 (by decide), u5.upd_eq (by decide), K4 sp (by decide), sp1, eB])
    (by rw [K18 a1 (by decide) (by decide) (by decide) (by decide), K1 a1 (by decide), ha1])
    (by rw [r8 a2 (by decide), u6.upd_eq (by decide), u5'.zero]; rfl) ra8 (by decide)
    (by
      rw [mem8, sp8, eF]
      exact { code := cM1 _ _ hMB (by decide) (by decide)
              hDC := Rd _ _ (by omega) _ _ (by decide) (by decide)
              hFC := Rd _ _ (by omega) _ _ (by decide) (by decide)
              hdF := sep_offsets R (c := 0xE8) (n := 64) (d := 0xD0) (k := 16) (Or.inr (by omega)) (by omega)
                (by omega)
              hsF := by have h := hbT.subR (c := 0xD0) (l := 16) (by omega); exact h
              hsep := (hbT.subR (c := 0xE8) (l := 64) (by omega)).symm
              hF := by rw [hRc _ (by omega)]; omega
              hFw := by rw [hRc _ (by omega)]; omega
              hdw := by rw [hRc _ (by omega)]; omega
              hsw := by omega })
  rw [sp8, eF, mem8] at mem9
  let MB := n9.mem
  have mB : ∀ x, Sep (R + BitVec.ofNat 32 0xD0) 16 x 1 → MB x = copyBytes M1 Bk bp 64 x := mem9
  -- Outside the frame, the `memcpy` leaves memory as the entry memory.
  have MBo : ∀ x, Sep R 0x130 x 1 → MB x = M0 x := fun x hx => by
    rw [mB x (hx.sub (c := 0xD0) (l := 16) (by omega)), copyBytes_sep (hx.sub (c := 0xE8) (l := 64) (by omega))
      (Nat.le_refl 64), M1o x (hx.sub (c := 0xE0 + 0x48) (l := 8) (by omega))]
  have cB : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn MB b code := fun b code h hb hbl i hi => by
    have hx : Sep R 0x130 (b + BitVec.ofNat 32 i) 1 :=
      ((dc R 0x130 b code.length (by omega) hb hbl).subR (c := i) (l := 1) (by omega))
    rw [MBo _ hx]; exact h i hi
  have hkB := cB _ _ hk (by decide) (by decide)
  have u9 : St MB Kb n9 0x16 (reg n9) := ⟨by rw [pc9], rfl, fun _ => rfl⟩
  have k9 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg n9 r = reg n8 r := K9
  have sp9' : reg n9 sp = R + BitVec.ofNat 32 0xE0 := by rw [sp9, sp8]
  have s0_9 : reg n9 s0 = st := by
    rw [k9 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8 s0 (by decide),
      K6 s0 (by decide), K5 s0 (by decide), s0_4]
  obtain ⟨n10, d10, u10⟩ := u9.aluImm hkB sk_at_16 (off' := 0x18) (by decide)
  have K10 := u10.upd_ne u9.zero
  have u10' : St MB Kb n10 0x18 (reg n10) := u10.self
  obtain ⟨n11, d11, u11⟩ := u10'.aluImm hkB sk_at_18 (off' := 0x1A) (by decide)
  have K11 := u11.upd_ne u10'.zero
  have u11' : St MB Kb n11 0x1A (reg n11) := u11.self
  obtain ⟨n12, d12, u12⟩ := u11'.alu hkB sk_at_1a (off' := 0x1C) (by decide)
  have K12 := u12.upd_ne u11'.zero
  have u12' : St MB Kb n12 0x1C (reg n12) := u12.self
  obtain ⟨n13, d13, u13⟩ := u12'.auipc hkB sk_at_1c (off' := 0x20) (by decide)
  obtain ⟨n14, d14, pc14, mem14, regs14⟩ := u13.call hkB sk_at_20
  have r14 : ∀ r, r ≠ ra → reg n14 r = reg n12 r := fun r h => by
    rw [regs14]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u12'.zero.symm
    · simp [upd, h0, h]
  have ra14 : reg n14 ra = Kb + BitVec.ofNat 32 0x24 := by rw [regs14]; simp +decide [upd]; rfl
  have pc14' : n14.pc = BitVec.ofNat 32 sha256CompressAddress := by
    rw [pc14, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
    decide
  have K9_14 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → reg n14 r = reg n9 r := fun r q1 q10 q11 q12 => by
    rw [r14 r q1, K12 r q10, K11 r q12, K10 r q11]
  have sp14 : reg n14 sp = R + BitVec.ofNat 32 0xE0 := by
    rw [K9_14 sp (by decide) (by decide) (by decide) (by decide), sp9']
  have eV : R + BitVec.ofNat 32 0xE0 + 0xFFFFFF20 = R := by
    rw [BitVec.add_assoc]; exact BitVec.add_zero R
  have hsR : Sep st 32 R 0xE0 := by
    have h := hsT.subR (c := 0) (l := 0xE0) (by omega); rwa [add_ofNat_zero] at h
  have env : SCEnv n14.mem (BitVec.ofNat 32 sha256CompressAddress) (R + BitVec.ofNat 32 0xE0) st Bk 1 :=
    { hP := by decide
      code := by rw [mem14]; exact cB _ _ hC (by decide) (by decide)
      idx := by rw [mem14]; exact cB _ _ hI (by decide) (by decide)
      o97 := by rw [mem14]; exact cB _ _ h97 (by decide) (by decide)
      kdata := fun i hi => by
        have hi' : i < 256 := by rw [show shaKData.length = 256 from rfl] at hi; exact hi
        rw [mem14, MBo _ (hKT.sub (c := i) (l := 1) (by omega)).symm]
        exact hK i hi
      hsp := by rw [hRc _ (by omega)]; omega
      hS := by rw [hRc _ (by omega)]; omega
      hstp := hsta
      hwbp := by rw [hRc _ (by omega)]; omega
      sC := by rw [eV]; exact RC _ _ (by decide) (by decide)
      sI := by rw [eV]; exact RC _ _ (by decide) (by decide)
      s97 := by rw [eV]; exact RC _ _ (by decide) (by decide)
      sK := by
        rw [eV]; have h := hKT.symm.sub (c := 0) (l := 0xE0) (by omega); rwa [add_ofNat_zero] at h
      stC := dc _ _ _ _ hstw (by decide) (by decide)
      stI := dc _ _ _ _ hstw (by decide) (by decide)
      st97 := dc _ _ _ _ hstw (by decide) (by decide)
      stK := hKs.symm
      stF := by rw [eV]; exact hsR
      bF := by
        rw [eV]
        have h := sep_offsets R (c := 0xE8) (n := 64 * 1) (d := 0) (k := 0xE0) (Or.inr (by omega)) (by omega)
          (by omega)
        rwa [add_ofNat_zero] at h
      bSt := (hsT.subR (c := 0xE8) (l := 64 * 1) (by omega)).symm }
  obtain ⟨n15, c15, pc15, sp15, K15, w15, fr15⟩ := sha256Compress_correct n14 env pc14'
    (by rw [r14 a0 (by decide), u12.upd_eq (by decide), u11'.zero, K11 s0 (by decide), K10 s0 (by decide), s0_9]
        exact BitVec.zero_add _)
    (by rw [r14 a1 (by decide), K12 a1 (by decide), K11 a1 (by decide), u10.upd_eq (by decide), sp9', eB])
    (by rw [r14 a2 (by decide), K12 a2 (by decide), u11.upd_eq (by decide), u10'.zero]; rfl)
    ra14 (by decide) sp14
  rw [eV, mem14] at fr15
  rw [mem14] at w15
  let MC := n15.mem
  have fC : ∀ x, Sep R 0xE0 x 1 → Sep st 32 x 1 → MC x = MB x := fr15
  have MCo : ∀ x, Sep R 0x130 x 1 → Sep st 32 x 1 → MC x = M0 x := fun x hx hy => by
    rw [fC x (by have h := hx.sub (c := 0) (l := 0xE0) (by omega); rwa [add_ofNat_zero] at h) hy, MBo x hx]
  have cC : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn MC b code := fun b code h hb hbl i hi => by
    rw [MCo _ ((dc R 0x130 b code.length (by omega) hb hbl).subR (c := i) (l := 1) (by omega))
      ((dc st 32 b code.length hstw hb hbl).subR (c := i) (l := 1) (by omega))]
    exact h i hi
  have hkC := cC _ _ hk (by decide) (by decide)
  have u15 : St MC Kb n15 0x24 (reg n15) := ⟨by rw [pc15], rfl, fun _ => rfl⟩
  have sp15' : reg n15 sp = R + BitVec.ofNat 32 0xE0 := sp15
  -- The two saved words, back from the frame.
  have slotM : ∀ c, 0xE0 + 0x48 ≤ c → c + 4 ≤ 0x130 →
      memLoad32 MC (R + BitVec.ofNat 32 c) = memLoad32 M1 (R + BitVec.ofNat 32 c) := fun c h1 h2 =>
    memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      have hF : Sep R 0xE0 (R + BitVec.ofNat 32 (c + j)) 1 := by
        have := sep_offsets R (c := 0) (n := 0xE0) (d := c + j) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      rw [fC _ hF ((hsT.subR (c := c + j) (l := 1) (by omega))),
        mB _ (sep_offsets R (c := 0xD0) (n := 16) (d := c + j) (k := 1) (Or.inl (by omega)) (by omega) (by omega)),
        copyBytes_sep (sep_offsets R (c := 0xE8) (n := 64) (d := c + j) (k := 1) (Or.inl (by omega)) (by omega)
          (by omega)) (Nat.le_refl 64)]
  have A12 : Sep (R + BitVec.ofNat 32 (0xE0 + 0x48)) 4 (R + BitVec.ofNat 32 (0xE0 + 0x4C)) 4 :=
    sep_offsets R (Or.inl (by omega)) (by omega) (by omega)
  have ldRa : memLoad32 MC (R + BitVec.ofNat 32 (0xE0 + 0x4C)) = retAddr := by
    rw [slotM _ (by omega) (by omega)]
    show memLoad32 (memStore32 (memStore32 M0 _ _) _ _) _ = _
    rw [memLoad32_store32_sep A12, memLoad32_store32_same]
  have ldS0 : memLoad32 MC (R + BitVec.ofNat 32 (0xE0 + 0x48)) = reg m s0 := by
    rw [slotM _ (by omega) (by omega)]
    show memLoad32 (memStore32 (memStore32 M0 _ _) _ _) _ = _
    rw [memLoad32_store32_same, K1 s0 (by decide)]
  obtain ⟨n16, d16, u16⟩ := u15.lw hkC sk_at_24 (off' := 0x26) (by decide)
    (by rw [sp15', show (0x4C : Word) = BitVec.ofNat 32 0x4C from rfl, add_ofNat_assoc, hRc _ (by omega)]
        have := hTa; omega)
  rw [sp15', show (0x4C : Word) = BitVec.ofNat 32 0x4C from rfl, add_ofNat_assoc, ldRa] at u16
  have K16 := u16.upd_ne u15.zero
  have u16' : St MC Kb n16 0x26 (reg n16) := u16.self
  obtain ⟨n17, d17, u17⟩ := u16'.lw hkC sk_at_26 (off' := 0x28) (by decide)
    (by rw [K16 sp (by decide), sp15', show (0x48 : Word) = BitVec.ofNat 32 0x48 from rfl, add_ofNat_assoc,
          hRc _ (by omega)]
        have := hTa; omega)
  rw [K16 sp (by decide), sp15', show (0x48 : Word) = BitVec.ofNat 32 0x48 from rfl, add_ofNat_assoc,
    ldS0] at u17
  have K17 := u17.upd_ne u16'.zero
  have u17' : St MC Kb n17 0x28 (reg n17) := u17.self
  obtain ⟨n18, d18, u18⟩ := u17'.aluImm hkC sk_at_28 (off' := 0x2A) (by decide)
  have K18' := u18.upd_ne u17'.zero
  have u18' : St MC Kb n18 0x2A (reg n18) := u18.self
  obtain ⟨n19, d19, pc19, mem19, regs19⟩ := u18'.jalr hkC sk_at_2a
  have ra18 : reg n18 ra = retAddr := by
    rw [K18' ra (by decide), K17 ra (by decide), u16.upd_eq (by decide)]
  have sp18 : reg n18 sp = T := by
    rw [u18.upd_eq (by decide), K17 sp (by decide), K16 sp (by decide), sp15']
    show R + BitVec.ofNat 32 0xE0 + 0x50 = T
    rw [BitVec.add_assoc]; show T + 0xFFFFFED0 + (BitVec.ofNat 32 0xE0 + 0x50) = T
    rw [BitVec.add_assoc]; exact BitVec.add_zero T
  have s0_18 : reg n18 s0 = reg m s0 := by rw [K18' s0 (by decide), u17.upd_eq (by decide)]
  have k15 : ∀ r, r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 →
      r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
      r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → reg n15 r = reg n14 r := K15
  have blk : memBytes MB (Bk + BitVec.ofNat 32 (64 * 0)) 64 = memBytes M0 bp 64 := by
    rw [Nat.mul_zero, add_ofNat_zero]
    unfold memBytes
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    show (MB (Bk + BitVec.ofNat 32 i)).toNat = (M0 (bp + BitVec.ofNat 32 i)).toNat
    rw [mB _ (by
        show Sep (R + BitVec.ofNat 32 0xD0) 16 (R + BitVec.ofNat 32 0xE8 + BitVec.ofNat 32 i) 1
        rw [add_ofNat_assoc]
        exact sep_offsets R (Or.inl (by omega)) (by omega) (by omega)),
      copyBytes_in hi (by omega), M1o _ ((hbT.subR (c := 0xE0 + 0x48) (l := 8) (by omega)).symm.subR (c := i)
        (l := 1) (by omega))]
  have wB : wordsAt MB st 8 = wordsAt M0 st 8 :=
    wordsAt_congr fun i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      exact MBo _ (hsT.sub (c := 4 * i + j) (l := 1) (by omega)).symm
  refine ⟨n19, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (c9.trans
    (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (c15.trans (.cons d16 (.cons d17 (.cons d18
    (.single d19)))))))))))))))))), ?_, ?_,
    fun r q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => ?_, ?_, fun x hx hy => ?_⟩
  · rw [pc19, ra18, add_lit_zero, hret]
  · rw [regs19, sp18]
  · rw [regs19]
    by_cases hra' : r = ra
    · subst hra'; rw [ra18, hra]
    by_cases hsp' : r = sp
    · subst hsp'; rw [sp18, hsp]
    by_cases hs0' : r = s0
    · subst hs0'; exact s0_18
    rw [K18' r hsp', K17 r hs0', K16 r hra', k15 r q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31,
      K9_14 r hra' q10 q11 q12, k9 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 hsp',
      K18 r hra' hs0' q10 q12, K1 r hsp']
  · have hbl : blockList MB Bk 1 = [memBytes M0 bp 64] := by
      unfold blockList
      rw [show List.range 1 = [0] from rfl, List.map_cons, List.map_nil, ← blk]
    rw [mem19, w15, wB, hbl, List.foldl_cons, List.foldl_nil]
  · rw [mem19]; exact MCo x hx hy

end C3.RV32
