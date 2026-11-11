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

/-! ## The message length in bits

`finalize` computes the message's length in bits, `8 * (64 * blocks + pos)`,
as two 32-bit words, and byte-swaps each with shifts and masks so that a
little-endian store writes it big-endian. These lemmas prove the swaps bit
by bit, one bit index at a time. -/

theorem lt32_cases {P : Nat → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) (h12 : P 12) (h13 : P 13) (h14 : P 14) (h15 : P 15) (h16 : P 16) (h17 : P 17) (h18 : P 18) (h19 : P 19) (h20 : P 20) (h21 : P 21) (h22 : P 22) (h23 : P 23) (h24 : P 24) (h25 : P 25) (h26 : P 26) (h27 : P 27) (h28 : P 28) (h29 : P 29) (h30 : P 30) (h31 : P 31) : ∀ i, i < 32 → P i
  | 0, _ => h0
  | 1, _ => h1
  | 2, _ => h2
  | 3, _ => h3
  | 4, _ => h4
  | 5, _ => h5
  | 6, _ => h6
  | 7, _ => h7
  | 8, _ => h8
  | 9, _ => h9
  | 10, _ => h10
  | 11, _ => h11
  | 12, _ => h12
  | 13, _ => h13
  | 14, _ => h14
  | 15, _ => h15
  | 16, _ => h16
  | 17, _ => h17
  | 18, _ => h18
  | 19, _ => h19
  | 20, _ => h20
  | 21, _ => h21
  | 22, _ => h22
  | 23, _ => h23
  | 24, _ => h24
  | 25, _ => h25
  | 26, _ => h26
  | 27, _ => h27
  | 28, _ => h28
  | 29, _ => h29
  | 30, _ => h30
  | 31, _ => h31
  | n + 32, h => absurd h (by omega)

theorem lt8_cases {P : Nat → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) : ∀ i, i < 8 → P i
  | 0, _ => h0
  | 1, _ => h1
  | 2, _ => h2
  | 3, _ => h3
  | 4, _ => h4
  | 5, _ => h5
  | 6, _ => h6
  | 7, _ => h7
  | n + 8, h => absurd h (by omega)

theorem tbFF00_0 : Nat.testBit 65280 0 = false := by decide
theorem tbFF00_1 : Nat.testBit 65280 1 = false := by decide
theorem tbFF00_2 : Nat.testBit 65280 2 = false := by decide
theorem tbFF00_3 : Nat.testBit 65280 3 = false := by decide
theorem tbFF00_4 : Nat.testBit 65280 4 = false := by decide
theorem tbFF00_5 : Nat.testBit 65280 5 = false := by decide
theorem tbFF00_6 : Nat.testBit 65280 6 = false := by decide
theorem tbFF00_7 : Nat.testBit 65280 7 = false := by decide
theorem tbFF00_8 : Nat.testBit 65280 8 = true := by decide
theorem tbFF00_9 : Nat.testBit 65280 9 = true := by decide
theorem tbFF00_10 : Nat.testBit 65280 10 = true := by decide
theorem tbFF00_11 : Nat.testBit 65280 11 = true := by decide
theorem tbFF00_12 : Nat.testBit 65280 12 = true := by decide
theorem tbFF00_13 : Nat.testBit 65280 13 = true := by decide
theorem tbFF00_14 : Nat.testBit 65280 14 = true := by decide
theorem tbFF00_15 : Nat.testBit 65280 15 = true := by decide
theorem tbFF00_16 : Nat.testBit 65280 16 = false := by decide
theorem tbFF00_17 : Nat.testBit 65280 17 = false := by decide
theorem tbFF00_18 : Nat.testBit 65280 18 = false := by decide
theorem tbFF00_19 : Nat.testBit 65280 19 = false := by decide
theorem tbFF00_20 : Nat.testBit 65280 20 = false := by decide
theorem tbFF00_21 : Nat.testBit 65280 21 = false := by decide
theorem tbFF00_22 : Nat.testBit 65280 22 = false := by decide
theorem tbFF00_23 : Nat.testBit 65280 23 = false := by decide
theorem tbFF00_24 : Nat.testBit 65280 24 = false := by decide
theorem tbFF00_25 : Nat.testBit 65280 25 = false := by decide
theorem tbFF00_26 : Nat.testBit 65280 26 = false := by decide
theorem tbFF00_27 : Nat.testBit 65280 27 = false := by decide
theorem tbFF00_28 : Nat.testBit 65280 28 = false := by decide
theorem tbFF00_29 : Nat.testBit 65280 29 = false := by decide
theorem tbFF00_30 : Nat.testBit 65280 30 = false := by decide
theorem tbFF00_31 : Nat.testBit 65280 31 = false := by decide

/-- A word's bytes in reverse order. -/
def bswap32 (x : Word) : Word := (x >>> 24) ||| ((x >>> 8) &&& 0xFF00) ||| ((x &&& 0xFF00) <<< 8) ||| (x <<< 24)

set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
/-- The low word of the length, as `finalize` swaps it. -/
theorem lenLo_eq (lo pos : Word) (hp : ∀ k, 6 ≤ k → pos.getLsbD k = false) :
    ((((lo <<< 1) &&& 0xFF00) ||| ((lo <<< 9) >>> 24)) ||| (pos <<< 27)) |||
      ((((pos <<< 3) ||| (lo <<< 9)) &&& 0xFF00) <<< 8) = bswap32 ((lo <<< 9) ||| (pos <<< 3)) := by
  apply BitVec.eq_of_getLsbD_eq
  unfold bswap32
  apply lt32_cases
  all_goals simp +decide [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, BitVec.getLsbD_extractLsb', tbFF00_0, tbFF00_1, tbFF00_2, tbFF00_3, tbFF00_4, tbFF00_5, tbFF00_6, tbFF00_7, tbFF00_8, tbFF00_9, tbFF00_10, tbFF00_11, tbFF00_12, tbFF00_13, tbFF00_14, tbFF00_15, tbFF00_16, tbFF00_17, tbFF00_18, tbFF00_19, tbFF00_20, tbFF00_21, tbFF00_22, tbFF00_23, tbFF00_24, tbFF00_25, tbFF00_26, tbFF00_27, tbFF00_28, tbFF00_29, tbFF00_30, tbFF00_31, -BitVec.getLsbD_eq_getElem, hp]

set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
/-- The high word of the length, as `finalize` swaps it when the block
count's high word is zero. -/
theorem lenHi_eq (lo : Word) :
    ((lo >>> 23) <<< 24 ||| ((((0 : Word) <<< 1) &&& 0xFF00) ||| (((0 : Word) <<< 9) >>> 24))) |||
      (((((0 : Word) <<< 9) ||| (lo >>> 23)) &&& 0xFF00) <<< 8) = bswap32 (lo >>> 23) := by
  apply BitVec.eq_of_getLsbD_eq
  unfold bswap32
  apply lt32_cases
  all_goals simp +decide [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, BitVec.getLsbD_extractLsb', tbFF00_0, tbFF00_1, tbFF00_2, tbFF00_3, tbFF00_4, tbFF00_5, tbFF00_6, tbFF00_7, tbFF00_8, tbFF00_9, tbFF00_10, tbFF00_11, tbFF00_12, tbFF00_13, tbFF00_14, tbFF00_15, tbFF00_16, tbFF00_17, tbFF00_18, tbFF00_19, tbFF00_20, tbFF00_21, tbFF00_22, tbFF00_23, tbFF00_24, tbFF00_25, tbFF00_26, tbFF00_27, tbFF00_28, tbFF00_29, tbFF00_30, tbFF00_31, -BitVec.getLsbD_eq_getElem, BitVec.getLsbD_of_ge]

set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
theorem bswap32_byte (x : Word) : ∀ k, k < 4 → (bswap32 x).extractLsb' (8 * k) 8 = x.extractLsb' (8 * (3 - k)) 8 := by
  intro k hk
  apply BitVec.eq_of_getLsbD_eq
  unfold bswap32
  match k, hk with
  | 0, _ => apply lt8_cases <;> simp +decide [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, BitVec.getLsbD_extractLsb', tbFF00_0, tbFF00_1, tbFF00_2, tbFF00_3, tbFF00_4, tbFF00_5, tbFF00_6, tbFF00_7, tbFF00_8, tbFF00_9, tbFF00_10, tbFF00_11, tbFF00_12, tbFF00_13, tbFF00_14, tbFF00_15, tbFF00_16, tbFF00_17, tbFF00_18, tbFF00_19, tbFF00_20, tbFF00_21, tbFF00_22, tbFF00_23, tbFF00_24, tbFF00_25, tbFF00_26, tbFF00_27, tbFF00_28, tbFF00_29, tbFF00_30, tbFF00_31, -BitVec.getLsbD_eq_getElem]
  | 1, _ => apply lt8_cases <;> simp +decide [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, BitVec.getLsbD_extractLsb', tbFF00_0, tbFF00_1, tbFF00_2, tbFF00_3, tbFF00_4, tbFF00_5, tbFF00_6, tbFF00_7, tbFF00_8, tbFF00_9, tbFF00_10, tbFF00_11, tbFF00_12, tbFF00_13, tbFF00_14, tbFF00_15, tbFF00_16, tbFF00_17, tbFF00_18, tbFF00_19, tbFF00_20, tbFF00_21, tbFF00_22, tbFF00_23, tbFF00_24, tbFF00_25, tbFF00_26, tbFF00_27, tbFF00_28, tbFF00_29, tbFF00_30, tbFF00_31, -BitVec.getLsbD_eq_getElem]
  | 2, _ => apply lt8_cases <;> simp +decide [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, BitVec.getLsbD_extractLsb', tbFF00_0, tbFF00_1, tbFF00_2, tbFF00_3, tbFF00_4, tbFF00_5, tbFF00_6, tbFF00_7, tbFF00_8, tbFF00_9, tbFF00_10, tbFF00_11, tbFF00_12, tbFF00_13, tbFF00_14, tbFF00_15, tbFF00_16, tbFF00_17, tbFF00_18, tbFF00_19, tbFF00_20, tbFF00_21, tbFF00_22, tbFF00_23, tbFF00_24, tbFF00_25, tbFF00_26, tbFF00_27, tbFF00_28, tbFF00_29, tbFF00_30, tbFF00_31, -BitVec.getLsbD_eq_getElem]
  | 3, _ => apply lt8_cases <;> simp +decide [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, BitVec.getLsbD_extractLsb', tbFF00_0, tbFF00_1, tbFF00_2, tbFF00_3, tbFF00_4, tbFF00_5, tbFF00_6, tbFF00_7, tbFF00_8, tbFF00_9, tbFF00_10, tbFF00_11, tbFF00_12, tbFF00_13, tbFF00_14, tbFF00_15, tbFF00_16, tbFF00_17, tbFF00_18, tbFF00_19, tbFF00_20, tbFF00_21, tbFF00_22, tbFF00_23, tbFF00_24, tbFF00_25, tbFF00_26, tbFF00_27, tbFF00_28, tbFF00_29, tbFF00_30, tbFF00_31, -BitVec.getLsbD_eq_getElem]

theorem byte_toNat (x : Word) (s : Nat) : (x.extractLsb' s 8).toNat = x.toNat / 2 ^ s % 256 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 10000 in
theorem lenLo_toNat (lo pos : Word) (hp : ∀ k, 6 ≤ k → pos.getLsbD k = false) :
    ((lo <<< 9) ||| (pos <<< 3)).toNat = (lo.toNat * 512 + pos.toNat * 8) % 2 ^ 32 := by
  rw [← Sha256.add_disj (by
      apply lt32_cases
      all_goals simp +decide [BitVec.getLsbD_shiftLeft, hp, -BitVec.getLsbD_eq_getElem]),
    BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  omega

theorem lenHi_toNat (lo : Word) : (lo >>> 23).toNat = lo.toNat / 2 ^ 23 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem low_bits_zero {pos : Word} (h : pos.toNat < 64) : ∀ k, 6 ≤ k → pos.getLsbD k = false := fun k hk =>
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hk : 2 ^ 6 ≤ 2 ^ k))

theorem store32_byte (M : Word → BitVec 8) (a v : Word) :
    ∀ k, k < 4 → memStore32 M a v (a + BitVec.ofNat 32 k) = v.extractLsb' (8 * k) 8 := by
  have ne : ∀ i j, i < 4 → j < 4 → i ≠ j → a + BitVec.ofNat 32 i ≠ a + BitVec.ofNat 32 j :=
    fun i j hi hj h => add_ofNat_ne a (by omega) (by omega) h
  intro k hk
  unfold memStore32
  match k, hk with
  | 0, _ =>
    rw [add_ofNat_zero, memStore8_ne (by have := ne 0 3 (by decide) (by decide) (by decide); rwa [add_ofNat_zero] at this),
      memStore8_ne (by have := ne 0 2 (by decide) (by decide) (by decide); rwa [add_ofNat_zero] at this),
      memStore8_ne (by have := ne 0 1 (by decide) (by decide) (by decide); rwa [add_ofNat_zero] at this),
      memStore8_same]
  | 1, _ =>
    rw [memStore8_ne (show a + BitVec.ofNat 32 1 ≠ a + 3 from ne 1 3 (by decide) (by decide) (by decide)),
      memStore8_ne (show a + BitVec.ofNat 32 1 ≠ a + 2 from ne 1 2 (by decide) (by decide) (by decide)),
      show a + BitVec.ofNat 32 1 = a + 1 from rfl, memStore8_same]
  | 2, _ =>
    rw [memStore8_ne (show a + BitVec.ofNat 32 2 ≠ a + 3 from ne 2 3 (by decide) (by decide) (by decide)),
      show a + BitVec.ofNat 32 2 = a + 2 from rfl,
      memStore8_same]
  | 3, _ => rw [show a + BitVec.ofNat 32 3 = a + 3 from rfl, memStore8_same]

set_option maxRecDepth 20000 in
/-- The two words `finalize` stores at `S + 0x38` are the message's length in
bits, big-endian. -/
theorem len_bytes (M : Word → BitVec 8) (S lo : Word) (pos : Nat) (hp : pos < 64) (hlo : lo.toNat < 2 ^ 26) :
    memBytes (memStore32 (memStore32 M (S + BitVec.ofNat 32 0x38) (bswap32 (lo >>> 23))) (S + BitVec.ofNat 32 0x3C)
      (bswap32 ((lo <<< 9) ||| (BitVec.ofNat 32 pos <<< 3)))) (S + BitVec.ofNat 32 0x38) 8 =
      Sha256.be64 (8 * (64 * lo.toNat + pos)) := by
  have hpb := low_bits_zero (pos := BitVec.ofNat 32 pos) (by rw [BitVec.toNat_ofNat]; omega)
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  let M' := memStore32 (memStore32 M (S + BitVec.ofNat 32 0x38) (bswap32 (lo >>> 23))) (S + BitVec.ofNat 32 0x3C)
      (bswap32 ((lo <<< 9) ||| (BitVec.ofNat 32 pos <<< 3)))
  have bHi : ∀ k, k < 4 → (M' (S + BitVec.ofNat 32 (0x38 + k))).toNat = lo.toNat / 2 ^ 23 / 2 ^ (8 * (3 - k)) % 256 := by
    intro k hk
    show (memStore32 _ _ _ _).toNat = _
    rw [memStore32_ne fun i hi => by
          rw [add_ofNat_assoc]; exact add_ofNat_ne S (c := 0x38 + k) (d := 0x3C + i) (by omega) (by omega) (by omega),
      ← add_ofNat_assoc, store32_byte _ _ _ k hk, bswap32_byte _ k hk,
      byte_toNat, lenHi_toNat]
  have bLo : ∀ k, k < 4 → (M' (S + BitVec.ofNat 32 (0x3C + k))).toNat =
      (lo.toNat * 512 + pos * 8) % 2 ^ 32 / 2 ^ (8 * (3 - k)) % 256 := by
    intro k hk
    show (memStore32 _ _ _ _).toNat = _
    rw [← add_ofNat_assoc, store32_byte _ _ _ k hk, bswap32_byte _ k hk, byte_toNat, lenLo_toNat _ _ hpb, hpn]
  show (List.range 8).map (fun i => (M' (S + BitVec.ofNat 32 0x38 + BitVec.ofNat 32 i)).toNat) =
    (List.range 8).reverse.map fun i => 8 * (64 * lo.toNat + pos) / 2 ^ (8 * i) % 256
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, add_ofNat_assoc]
  have h0 := bHi 0 (by decide); have h1 := bHi 1 (by decide); have h2 := bHi 2 (by decide)
  have h3 := bHi 3 (by decide); have h4 := bLo 0 (by decide); have h5 := bLo 1 (by decide)
  have h6 := bLo 2 (by decide); have h7 := bLo 3 (by decide)
  simp only [Nat.add_zero, show 0x3C + 0 = 0x38 + 4 from rfl, show 0x3C + 1 = 0x38 + 5 from rfl,
    show 0x3C + 2 = 0x38 + 6 from rfl, show 0x3C + 3 = 0x38 + 7 from rfl] at h0 h4 h5 h6 h7
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The 4 bytes the big-endian store helper writes at `p`: `v`'s bytes, most
significant first. -/
def beStore (M : Word → BitVec 8) (p v : Word) : Word → BitVec 8 :=
  memStore8 (memStore8 (memStore8 (memStore8 M p ((aluEval .srl v 0x18).extractLsb' 0 8))
    (p + 1) ((aluEval .srl v 0x10).extractLsb' 0 8)) (p + 2) ((aluEval .srl v 8).extractLsb' 0 8))
    (p + 3) (v.extractLsb' 0 8)

theorem beStore_out {M : Word → BitVec 8} {p v x : Word} (h : Sep p 4 x 1) : beStore M p v x = M x := by
  have hx : ∀ i, i < 4 → x ≠ p + BitVec.ofNat 32 i := fun i hi e => h i hi 0 (by decide) (by rw [add_ofNat_zero]; exact e.symm)
  unfold beStore
  rw [memStore8_ne (show x ≠ p + 3 from hx 3 (by decide)), memStore8_ne (show x ≠ p + 2 from hx 2 (by decide)),
    memStore8_ne (show x ≠ p + 1 from hx 1 (by decide)),
    memStore8_ne (show x ≠ p by have := hx 0 (by decide); rwa [add_ofNat_zero] at this)]

theorem beStore_bytes (M : Word → BitVec 8) (p v : Word) : memBytes (beStore M p v) p 4 = Sha256.wordBytes v := by
  have ne : ∀ i j, i < 4 → j < 4 → i ≠ j → p + BitVec.ofNat 32 i ≠ p + BitVec.ofNat 32 j :=
    fun i j hi hj h => add_ofNat_ne p (by omega) (by omega) h
  have hv := v.isLt
  show (List.range 4).map (fun i => (beStore M p v (p + BitVec.ofNat 32 i)).toNat) = _
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, Sha256.wordBytes, List.cons.injEq, and_true]
  unfold beStore
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [memStore8_ne (show p + BitVec.ofNat 32 0 ≠ p + 3 from ne 0 3 (by decide) (by decide) (by decide)),
      memStore8_ne (show p + BitVec.ofNat 32 0 ≠ p + 2 from ne 0 2 (by decide) (by decide) (by decide)),
      memStore8_ne (show p + BitVec.ofNat 32 0 ≠ p + 1 from ne 0 1 (by decide) (by decide) (by decide)),
      add_ofNat_zero, memStore8_same, byte_toNat]
    show (v >>> 24).toNat / 2 ^ 0 % 256 = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  · rw [memStore8_ne (show p + BitVec.ofNat 32 1 ≠ p + 3 from ne 1 3 (by decide) (by decide) (by decide)),
      memStore8_ne (show p + BitVec.ofNat 32 1 ≠ p + 2 from ne 1 2 (by decide) (by decide) (by decide)),
      show p + BitVec.ofNat 32 1 = p + 1 from rfl, memStore8_same, byte_toNat]
    show (v >>> 16).toNat / 2 ^ 0 % 256 = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  · rw [memStore8_ne (show p + BitVec.ofNat 32 2 ≠ p + 3 from ne 2 3 (by decide) (by decide) (by decide)),
      show p + BitVec.ofNat 32 2 = p + 2 from rfl, memStore8_same, byte_toNat]
    show (v >>> 8).toNat / 2 ^ 0 % 256 = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  · rw [show p + BitVec.ofNat 32 3 = p + 3 from rfl, memStore8_same, byte_toNat]; omega

set_option maxRecDepth 20000 in
/-- A caller's `auipc t0, imm; jalr t0, o(t0)` into the outlined helper that
stores `a1` big-endian at `s0` and adds 4 to `s0`, and the helper, run from
offset `off` to `off + 8` of the caller. It changes `t0` and `a2` through
`a4` besides `s0`. -/
theorem St.callStoreBe {M : Word → BitVec 8} {base : Word} {code : List Nat} {m : Machine}
    {off : Nat} {f : Fin 32 → Word} (s : St M base m off f)
    (hc : CodeIn M base code) {imm o : Word}
    (h1 : fetchRel code off = some (.auipc t0 imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr t0 t0 o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 shaStoreBeAddress)
    (hl : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hh : CodeIn M (BitVec.ofNat 32 shaStoreBeAddress) shaStoreBeCode)
    (hp : Sep (f s0) 4 (BitVec.ofNat 32 shaStoreBeAddress) shaStoreBeCode.length) :
    ∃ m', Steps m m' ∧ St (beStore M (f s0) (f a1)) base m' (off + 8) (reg m') ∧
      reg m' s0 = f s0 + 4 ∧
      ∀ r, r ≠ t0 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ s0 → reg m' r = f r := by
  let SB := BitVec.ofNat 32 shaStoreBeAddress
  have hz := s.zero
  obtain ⟨m1, e1, t1⟩ := s.auipc hc h1 (off' := off + 4) (ofNat_add_ofNat off 4)
  obtain ⟨m2, e2, pc2, mem2, regs2⟩ := t1.call hc h2
  have hL : base + BitVec.ofNat 32 (off + 4) + 4 = base + BitVec.ofNat 32 (off + 8) := by
    rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  let L := base + BitVec.ofNat 32 (off + 8)
  have r2 : ∀ r, r ≠ t0 → reg m2 r = f r := fun r h => by
    rw [regs2]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, h]
  have t2 : reg m2 t0 = L := by rw [regs2, hL]; simp +decide [upd]; rfl
  have hp2 : m2.pc = SB := by
    rw [pc2, show upd f t0 (base + BitVec.ofNat 32 off + imm) t0 = base + BitVec.ofNat 32 off + imm from
      by simp +decide [upd], hb]
    decide
  have u2 : St M SB m2 0 (reg m2) := ⟨by rw [hp2]; simp, mem2, fun _ => rfl⟩
  obtain ⟨m3, e3, u3⟩ := u2.aluImm hh sbe_at_0 (off' := 4) (by decide)
  have K3 := u3.upd_ne u2.zero
  have u3' : St M SB m3 4 (reg m3) := u3.self
  obtain ⟨m4, e4, u4⟩ := u3'.aluImm hh sbe_at_4 (off' := 8) (by decide)
  have K4 := u4.upd_ne u3'.zero
  have u4' : St M SB m4 8 (reg m4) := u4.self
  obtain ⟨m5, e5, u5⟩ := u4'.aluImm hh sbe_at_8 (off' := 0xC) (by decide)
  have K5 := u5.upd_ne u4'.zero
  have u5' : St M SB m5 0xC (reg m5) := u5.self
  have K25 : ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m5 r = reg m2 r := fun r q2 q3 q4 => by
    rw [K5 r q4, K4 r q3, K3 r q2]
  have s0_5 : reg m5 s0 = f s0 := by rw [K25 s0 (by decide) (by decide) (by decide), r2 s0 (by decide)]
  have a1_5 : reg m5 a1 = f a1 := by rw [K25 a1 (by decide) (by decide) (by decide), r2 a1 (by decide)]
  have a2_5 : reg m5 a2 = aluEval .srl (f a1) 0x18 := by
    rw [K5 a2 (by decide), K4 a2 (by decide), u3.upd_eq (by decide), r2 a1 (by decide)]
  have a3_5 : reg m5 a3 = aluEval .srl (f a1) 8 := by
    rw [K5 a3 (by decide), u4.upd_eq (by decide), K3 a1 (by decide), r2 a1 (by decide)]
  have a4_5 : reg m5 a4 = aluEval .srl (f a1) 0x10 := by
    rw [u5.upd_eq (by decide), K4 a1 (by decide), K3 a1 (by decide), r2 a1 (by decide)]
  have hpk : ∀ k, k < 4 → Sep (f s0 + BitVec.ofNat 32 k) 1 SB shaStoreBeCode.length := fun k hk =>
    hp.sub (c := k) (l := 1) (by omega)
  obtain ⟨m6, e6, u6⟩ := u5'.sb hh sbe_at_c (off' := 0x10) (by decide)
  rw [s0_5, add_lit_zero, a2_5] at u6
  have hh6 := hh.store8 (v := (aluEval .srl (f a1) 0x18).extractLsb' 0 8)
    (by have := hpk 0 (by decide); rwa [add_ofNat_zero] at this)
  obtain ⟨m7, e7, u7⟩ := u6.sb hh6 sbe_at_10 (off' := 0x14) (by decide)
  rw [s0_5, a4_5] at u7
  have hh7 := hh6.store8 (a := f s0 + 1) (v := (aluEval .srl (f a1) 0x10).extractLsb' 0 8) (hpk 1 (by decide))
  obtain ⟨m8, e8, u8⟩ := u7.sb hh7 sbe_at_14 (off' := 0x18) (by decide)
  rw [s0_5, a3_5] at u8
  have hh8 := hh7.store8 (a := f s0 + 2) (v := (aluEval .srl (f a1) 8).extractLsb' 0 8) (hpk 2 (by decide))
  obtain ⟨m9, e9, u9⟩ := u8.sb hh8 sbe_at_18 (off' := 0x1C) (by decide)
  rw [s0_5, a1_5] at u9
  have hh9 : CodeIn (beStore M (f s0) (f a1)) SB shaStoreBeCode := hh8.store8 (hpk 3 (by decide))
  obtain ⟨m10, e10, u10⟩ := u9.aluImm hh9 sbe_at_1c (off' := 0x1E) (by decide)
  have K10 := u10.upd_ne u5'.zero
  have u10' : St (beStore M (f s0) (f a1)) SB m10 0x1E (reg m10) := u10.self
  obtain ⟨m11, e11, pc11, mem11, regs11⟩ := u10'.jalr hh9 sbe_at_1e
  refine ⟨m11, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (.cons e9
    (.cons e10 (.single e11)))))))))), ⟨?_, mem11, fun _ => rfl⟩, ?_, fun r q5 q12 q13 q14 q8 => ?_⟩
  · rw [pc11, K10 t0 (by decide), K25 t0 (by decide) (by decide) (by decide), t2, add_lit_zero]
    exact even_clear _ hl
  · rw [regs11, u10.upd_eq (by decide), s0_5]; rfl
  · rw [regs11, K10 r q8, K25 r q12 q13 q14, r2 r q5]

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

theorem xor63 : ∀ p, p < 64 → p ^^^ 63 = 63 - p := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
/-- `finalize` from offset 0x2A to 0x86: it loads the block count and the
buffer's byte count from the hasher at `s4`, and computes the message's
length in bits, byte-swapped, into `s5` (low word) and `s6` (high word), and
`63 - pos` into `s3`. -/
theorem fin_len {Mx : Word → BitVec 8} {n : Machine} {f : Fin 32 → Word} {S lo : Word} {pos : Nat}
    (s : St Mx (BitVec.ofNat 32 shaFinalizeAddress) n 0x2A f)
    (hc : CodeIn Mx (BitVec.ofNat 32 shaFinalizeAddress) shaFinalizeCode) (fs4 : f s4 = S)
    (hS : S.toNat % 4 = 0) (hlo : memLoad32 Mx (S + 0x60) = lo) (hhi : memLoad32 Mx (S + 0x64) = 0)
    (hpos : Mx (S + 0x3F) = BitVec.ofNat 8 pos) (hp : pos < 64) :
    ∃ n', Steps n n' ∧ St Mx (BitVec.ofNat 32 shaFinalizeAddress) n' 0x86 (reg n') ∧
      reg n' s5 = bswap32 ((lo <<< 9) ||| (BitVec.ofNat 32 pos <<< 3)) ∧ reg n' s6 = bswap32 (lo >>> 23) ∧
      reg n' s3 = BitVec.ofNat 32 (63 - pos) ∧ reg n' a2 = BitVec.ofNat 32 pos ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ s3 →
        r ≠ s5 → r ≠ s6 → reg n' r = f r := by
  obtain ⟨n1, e1, t1⟩ := s.lw hc sf_at_2a (off' := 0x2E) (by decide) (by rw [fs4]; exact aligned_add hS (k := 0x60) (by decide))
  obtain ⟨n2, e2, t2⟩ := t1.lw hc sf_at_2e (off' := 0x32) (by decide)
    (by rw [show upd f a0 (memLoad32 Mx (f s4 + 0x60)) s4 = f s4 by simp +decide [upd], fs4]
        exact aligned_add hS (k := 0x64) (by decide))
  obtain ⟨n3, e3, t3⟩ := t2.lbu hc sf_at_32 (off' := 0x36) (by decide)
  obtain ⟨n4, e4, t4⟩ := t3.lui hc sf_at_36 (off' := 0x38) (by decide)
  obtain ⟨n5, e5, t5⟩ := t4.aluImm hc sf_at_38 (off' := 0x3C) (by decide)
  obtain ⟨n6, e6, t6⟩ := t5.aluImm hc sf_at_3c (off' := 0x40) (by decide)
  obtain ⟨n7, e7, t7⟩ := t6.aluImm hc sf_at_40 (off' := 0x44) (by decide)
  obtain ⟨n8, e8, t8⟩ := t7.aluImm hc sf_at_44 (off' := 0x48) (by decide)
  obtain ⟨n9, e9, t9⟩ := t8.aluImm hc sf_at_48 (off' := 0x4C) (by decide)
  obtain ⟨n10, e10, t10⟩ := t9.aluImm hc sf_at_4c (off' := 0x4E) (by decide)
  obtain ⟨n11, e11, t11⟩ := t10.alu hc sf_at_4e (off' := 0x52) (by decide)
  obtain ⟨n12, e12, t12⟩ := t11.alu hc sf_at_52 (off' := 0x54) (by decide)
  obtain ⟨n13, e13, t13⟩ := t12.alu hc sf_at_54 (off' := 0x56) (by decide)
  obtain ⟨n14, e14, t14⟩ := t13.aluImm hc sf_at_56 (off' := 0x58) (by decide)
  obtain ⟨n15, e15, t15⟩ := t14.alu hc sf_at_58 (off' := 0x5A) (by decide)
  obtain ⟨n16, e16, t16⟩ := t15.alu hc sf_at_5a (off' := 0x5C) (by decide)
  obtain ⟨n17, e17, t17⟩ := t16.aluImm hc sf_at_5c (off' := 0x5E) (by decide)
  obtain ⟨n18, e18, t18⟩ := t17.aluImm hc sf_at_5e (off' := 0x62) (by decide)
  obtain ⟨n19, e19, t19⟩ := t18.alu hc sf_at_62 (off' := 0x64) (by decide)
  obtain ⟨n20, e20, t20⟩ := t19.aluImm hc sf_at_64 (off' := 0x66) (by decide)
  obtain ⟨n21, e21, t21⟩ := t20.alu hc sf_at_66 (off' := 0x6A) (by decide)
  obtain ⟨n22, e22, t22⟩ := t21.aluImm hc sf_at_6a (off' := 0x6C) (by decide)
  obtain ⟨n23, e23, t23⟩ := t22.alu hc sf_at_6c (off' := 0x70) (by decide)
  obtain ⟨n24, e24, t24⟩ := t23.alu hc sf_at_70 (off' := 0x72) (by decide)
  obtain ⟨n25, e25, t25⟩ := t24.alu hc sf_at_72 (off' := 0x76) (by decide)
  obtain ⟨n26, e26, t26⟩ := t25.aluImm hc sf_at_76 (off' := 0x78) (by decide)
  obtain ⟨n27, e27, t27⟩ := t26.aluImm hc sf_at_78 (off' := 0x7A) (by decide)
  obtain ⟨n28, e28, t28⟩ := t27.alu hc sf_at_7a (off' := 0x7E) (by decide)
  obtain ⟨n29, e29, t29⟩ := t28.alu hc sf_at_7e (off' := 0x82) (by decide)
  obtain ⟨n30, e30, t30⟩ := t29.aluImm hc sf_at_82 (off' := 0x86) (by decide)
  have hz : BitVec.zeroExtend 32 (BitVec.ofNat 8 pos) = BitVec.ofNat 32 pos := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hpb := low_bits_zero (pos := BitVec.ofNat 32 pos) (by rw [BitVec.toNat_ofNat]; omega)
  have g5 : reg n30 s5 = bswap32 ((lo <<< 9) ||| (BitVec.ofNat 32 pos <<< 3)) := by
    rw [t30.regs]
    simp +decide only [upd, ↓reduceIte, fs4]
    rw [hlo, hpos, hz]
    exact lenLo_eq lo _ hpb
  have g6 : reg n30 s6 = bswap32 (lo >>> 23) := by
    rw [t30.regs]
    simp +decide only [upd, ↓reduceIte, fs4]
    rw [hlo, hhi]
    exact lenHi_eq lo
  have g3 : reg n30 s3 = BitVec.ofNat 32 (63 - pos) := by
    rw [t30.regs]
    simp +decide only [upd, ↓reduceIte, fs4]
    rw [hpos, hz]
    show BitVec.ofNat 32 pos ^^^ 0x3F = _
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pos < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : 63 - pos < 2 ^ 32), show (0x3F : Word).toNat = 63 from rfl]
    exact xor63 pos hp
  have g2 : reg n30 a2 = BitVec.ofNat 32 pos := by
    rw [t30.regs]
    simp +decide only [upd, ↓reduceIte, fs4]
    rw [hpos, hz]
  refine ⟨n30, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (.cons e9 (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.cons e14 (.cons e15 (.cons e16 (.cons e17 (.cons e18 (.cons e19 (.cons e20 (.cons e21 (.cons e22 (.cons e23 (.cons e24 (.cons e25 (.cons e26 (.cons e27 (.cons e28 (.cons e29 (.single e30))))))))))))))))))))))))))))), t30.self, g5, g6, g3, g2, fun r q10 q11 q12 q13 q14 q15 q16 q17 q5 q19 q21 q22 => ?_⟩
  rw [t30.regs]
  simp only [upd, q10, q11, q12, q13, q14, q15, q16, q17, q5, q19, q21, q22, ite_false]
  by_cases h0 : r.val = 0
  · have : r = 0 := Fin.ext h0
    subst this; simp; exact s.zero.symm
  · simp [h0]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- `finalize`'s loop from offset 0xDA: it loads each of the 8 hash words
from `s1` and stores it big-endian at `s0`, through the outlined helper. -/
theorem fin_loop {M0 : Word → BitVec 8} {Sst B : Word}
    (hc : ∀ Mx : Word → BitVec 8, (∀ x, Sep B 32 x 1 → Mx x = M0 x) →
      CodeIn Mx (BitVec.ofNat 32 shaFinalizeAddress) shaFinalizeCode)
    (hbe : ∀ Mx : Word → BitVec 8, (∀ x, Sep B 32 x 1 → Mx x = M0 x) →
      CodeIn Mx (BitVec.ofNat 32 shaStoreBeAddress) shaStoreBeCode)
    (hBw : B.toNat + 32 ≤ 0x40000000) (hSB : Sep Sst 32 B 32) (hSa : Sst.toNat % 4 = 0) :
    ∀ k j (n : Machine) (Mx : Word → BitVec 8), j + k = 8 → 0 < k →
      St Mx (BitVec.ofNat 32 shaFinalizeAddress) n 0xDA (reg n) → (∀ x, Sep B 32 x 1 → Mx x = M0 x) →
      memBytes Mx B (4 * j) =
        ((List.range j).map fun i => memLoad32 M0 (Sst + BitVec.ofNat 32 (4 * i))).flatMap Sha256.wordBytes →
      reg n a0 = BitVec.ofNat 32 k → reg n s1 = Sst + BitVec.ofNat 32 (4 * j) →
      reg n s0 = B + BitVec.ofNat 32 (4 * j) →
      ∃ n' Mf, Steps n n' ∧ St Mf (BitVec.ofNat 32 shaFinalizeAddress) n' 0xEA (reg n') ∧
        (∀ x, Sep B 32 x 1 → Mf x = M0 x) ∧ memBytes Mf B 32 = (wordsAt M0 Sst 8).flatMap Sha256.wordBytes ∧
        ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ t0 → r ≠ s0 → r ≠ s1 → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro j n Mx hjk _ s hag hbytes ha0 hs1 hs0
    have hcx := hc Mx hag
    obtain ⟨n1, d1, u1⟩ := s.lw hcx sf_at_da (off' := 0xDC) (by decide)
      (by rw [hs1, add_lit_zero]; exact aligned_add hSa (k := 4 * j) (by omega))
    have K1 := u1.upd_ne s.zero
    have u1' : St Mx (BitVec.ofNat 32 shaFinalizeAddress) n1 0xDC (reg n1) := u1.self
    have v1 : reg n1 a1 = memLoad32 M0 (Sst + BitVec.ofNat 32 (4 * j)) := by
      rw [u1.upd_eq (by decide), hs1, add_lit_zero]
      apply memLoad32_congr; intro i hi
      rw [add_ofNat_assoc]
      exact hag _ (hSB.sub (c := 4 * j + i) (l := 1) (by omega)).symm
    obtain ⟨n2, d2, u2⟩ := u1'.aluImm hcx sf_at_dc (off' := 0xDE) (by decide)
    have K2 := u2.upd_ne u1'.zero
    have u2' : St Mx (BitVec.ofNat 32 shaFinalizeAddress) n2 0xDE (reg n2) := u2.self
    have s1_2 : reg n2 s1 = Sst + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [u2.upd_eq (by decide), K1 s1 (by decide), hs1]
      show Sst + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc, show 4 * j + 4 = 4 * (j + 1) by omega]
    have s0_2 : reg n2 s0 = B + BitVec.ofNat 32 (4 * j) := by rw [K2 s0 (by decide), K1 s0 (by decide), hs0]
    have a1_2 : reg n2 a1 = memLoad32 M0 (Sst + BitVec.ofNat 32 (4 * j)) := by rw [K2 a1 (by decide), v1]
    obtain ⟨n3, c3, u3, s0_3, K3⟩ := u2'.callStoreBe hcx sf_at_de sf_at_e2 (by decide) (by decide) (hbe Mx hag)
      (by rw [s0_2]; exact data_code (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) (by decide))
    rw [s0_2, a1_2] at u3
    let v := memLoad32 M0 (Sst + BitVec.ofNat 32 (4 * j))
    let M' := beStore Mx (B + BitVec.ofNat 32 (4 * j)) v
    have hag' : ∀ x, Sep B 32 x 1 → M' x = M0 x := fun x hx => by
      show beStore Mx _ v x = M0 x
      rw [beStore_out (hx.sub (c := 4 * j) (l := 4) (by omega)), hag x hx]
    have hcx' := hc M' hag'
    obtain ⟨n4, d4, u4⟩ := u3.aluImm hcx' sf_at_e6 (off' := 0xE8) (by decide)
    have K4 := u4.upd_ne u3.zero
    have u4' : St M' (BitVec.ofNat 32 shaFinalizeAddress) n4 0xE8 (reg n4) := u4.self
    have a0_4 : reg n4 a0 = BitVec.ofNat 32 k := by
      rw [u4.upd_eq (by decide), K3 a0 (by decide) (by decide) (by decide) (by decide) (by decide),
        K2 a0 (by decide), K1 a0 (by decide), ha0]
      exact dec_ofNat_succ (by omega)
    have s1_4 : reg n4 s1 = Sst + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [K4 s1 (by decide), K3 s1 (by decide) (by decide) (by decide) (by decide) (by decide), s1_2]
    have s0_4 : reg n4 s0 = B + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [K4 s0 (by decide), s0_3, s0_2]
      show B + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc, show 4 * j + 4 = 4 * (j + 1) by omega]
    have K14 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ t0 → r ≠ s0 → r ≠ s1 →
        reg n4 r = reg n r := fun r q10 q11 q12 q13 q14 q5 q8 q9 => by
      rw [K4 r q10, K3 r q5 q12 q13 q14 q8, K2 r q9, K1 r q11]
    have hbytes' : memBytes M' B (4 * (j + 1)) =
        ((List.range (j + 1)).map fun i => memLoad32 M0 (Sst + BitVec.ofNat 32 (4 * i))).flatMap Sha256.wordBytes := by
      rw [show 4 * (j + 1) = 4 * j + 4 by omega, memBytes_split, List.range_succ, List.map_append, List.flatMap_append,
        ← hbytes, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, beStore_bytes]
      congr 1
      apply memBytes_congr; intro i hi
      exact beStore_out (sep_offsets B (c := 4 * j) (n := 4) (d := i) (k := 1) (Or.inr (by omega)) (by omega)
        (by omega))
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n5, d5, u5⟩ := u4'.notTaken hcx' 0xEA sf_at_e8 (by decide) (by
        simp only [branchTaken]; rw [a0_4, u4'.zero]; decide)
      have hj : j + 1 = 8 := by omega
      rw [hj] at hbytes'
      exact ⟨n5, M', .cons d1 (.cons d2 (c3.trans (.cons d4 (.single d5)))), u5.self, hag', hbytes',
        fun r q10 q11 q12 q13 q14 q5 q8 q9 => by rw [u5.regs, K14 r q10 q11 q12 q13 q14 q5 q8 q9]⟩
    · obtain ⟨n5, d5, u5⟩ := u4'.taken hcx' 0xDA sf_at_e8 (by decide) (by
        simp only [branchTaken, a0_4, u4'.zero, bne_iff_ne, ne_eq]
        intro h; exact hk (ofNat_inj (by omega) (by decide) h))
      obtain ⟨n6, Mf, c6, u6, hag6, hb6, K6⟩ := ih (j + 1) n5 M' (by omega) (by omega) u5.self hag' hbytes'
        (by rw [u5.regs, a0_4]) (by rw [u5.regs, s1_4]) (by rw [u5.regs, s0_4])
      exact ⟨n6, Mf, .cons d1 (.cons d2 (c3.trans (.cons d4 (.cons d5 c6)))), u6, hag6, hb6,
        fun r q10 q11 q12 q13 q14 q5 q8 q9 => by
          rw [K6 r q10 q11 q12 q13 q14 q5 q8 q9, u5.regs, K14 r q10 q11 q12 q13 q14 q5 q8 q9]⟩

/-- What `finalize`'s save helper stores, and where in the frame. -/
abbrev finSavePs : List (Fin 32 × Word) :=
  [(ra, 0x5C), (s0, 0x58), (s1, 0x54), (s2, 0x50), (s3, 0x4C), (s4, 0x48), (s5, 0x44)]

theorem finSave_shape : SaveAt shaFinalizeSaveCode 0 finSavePs := by simp only [SaveAt]; decide

theorem finRestore_shape : RestoreAt shaFinalizeRestoreCode 0 finSavePs := by simp only [RestoreAt]; decide

theorem saveMem_out (G : Word) (f : Fin 32 → Word) (x : Word) :
    ∀ (ps : List (Fin 32 × Word)) (M : Word → BitVec 8), (∀ p ∈ ps, Sep (G + p.2) 4 x 1) → saveMem M G f ps x = M x
  | [], _, _ => rfl
  | (r, o) :: ps, M, h => by
    simp only [saveMem]
    rw [saveMem_out G f x ps _ (fun p hp => h p (List.mem_cons_of_mem _ hp)),
      memStore32_get_sep (h (r, o) List.mem_cons_self)]

/-- `finalize`'s frame after its prologue stores: the save helper's 7 words,
then `s6` at offset 0x40. -/
abbrev finSaved (M : Word → BitVec 8) (G : Word) (f : Fin 32 → Word) (v : Word) : Word → BitVec 8 :=
  memStore32 (saveMem M G f finSavePs) (G + BitVec.ofNat 32 0x40) v

theorem finSaved_slots (M : Word → BitVec 8) (G : Word) (f : Fin 32 → Word) (v : Word) :
    memLoad32 (finSaved M G f v) (G + BitVec.ofNat 32 0x40) = v ∧
      memLoad32 (finSaved M G f v) (G + 0x5C) = f ra ∧
      memLoad32 (finSaved M G f v) (G + 0x58) = f s0 ∧
      memLoad32 (finSaved M G f v) (G + 0x54) = f s1 ∧
      memLoad32 (finSaved M G f v) (G + 0x50) = f s2 ∧
      memLoad32 (finSaved M G f v) (G + 0x4C) = f s3 ∧
      memLoad32 (finSaved M G f v) (G + 0x48) = f s4 ∧
      memLoad32 (finSaved M G f v) (G + 0x44) = f s5 := by
  have so : ∀ c d, c < 0x60 → d < 0x60 → c + 4 ≤ d ∨ d + 4 ≤ c →
      Sep (G + BitVec.ofNat 32 c) 4 (G + BitVec.ofNat 32 d) 4 :=
    fun c d hc hd h => sep_offsets G h (by omega) (by omega)
  simp only [finSaved, saveMem]
  refine ⟨memLoad32_store32_same _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [memLoad32_store32_sep (show Sep (G + BitVec.ofNat 32 0x40) 4 (G + 0x5C) 4 from so 0x40 0x5C (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x44) 4 (G + 0x5C) 4 from so 0x44 0x5C (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x48) 4 (G + 0x5C) 4 from so 0x48 0x5C (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x4C) 4 (G + 0x5C) 4 from so 0x4C 0x5C (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x50) 4 (G + 0x5C) 4 from so 0x50 0x5C (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x54) 4 (G + 0x5C) 4 from so 0x54 0x5C (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x58) 4 (G + 0x5C) 4 from so 0x58 0x5C (by omega) (by omega) (by omega)), memLoad32_store32_same]
  · rw [memLoad32_store32_sep (show Sep (G + BitVec.ofNat 32 0x40) 4 (G + 0x58) 4 from so 0x40 0x58 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x44) 4 (G + 0x58) 4 from so 0x44 0x58 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x48) 4 (G + 0x58) 4 from so 0x48 0x58 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x4C) 4 (G + 0x58) 4 from so 0x4C 0x58 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x50) 4 (G + 0x58) 4 from so 0x50 0x58 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x54) 4 (G + 0x58) 4 from so 0x54 0x58 (by omega) (by omega) (by omega)), memLoad32_store32_same]
  · rw [memLoad32_store32_sep (show Sep (G + BitVec.ofNat 32 0x40) 4 (G + 0x54) 4 from so 0x40 0x54 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x44) 4 (G + 0x54) 4 from so 0x44 0x54 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x48) 4 (G + 0x54) 4 from so 0x48 0x54 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x4C) 4 (G + 0x54) 4 from so 0x4C 0x54 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x50) 4 (G + 0x54) 4 from so 0x50 0x54 (by omega) (by omega) (by omega)), memLoad32_store32_same]
  · rw [memLoad32_store32_sep (show Sep (G + BitVec.ofNat 32 0x40) 4 (G + 0x50) 4 from so 0x40 0x50 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x44) 4 (G + 0x50) 4 from so 0x44 0x50 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x48) 4 (G + 0x50) 4 from so 0x48 0x50 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x4C) 4 (G + 0x50) 4 from so 0x4C 0x50 (by omega) (by omega) (by omega)), memLoad32_store32_same]
  · rw [memLoad32_store32_sep (show Sep (G + BitVec.ofNat 32 0x40) 4 (G + 0x4C) 4 from so 0x40 0x4C (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x44) 4 (G + 0x4C) 4 from so 0x44 0x4C (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x48) 4 (G + 0x4C) 4 from so 0x48 0x4C (by omega) (by omega) (by omega)), memLoad32_store32_same]
  · rw [memLoad32_store32_sep (show Sep (G + BitVec.ofNat 32 0x40) 4 (G + 0x48) 4 from so 0x40 0x48 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x44) 4 (G + 0x48) 4 from so 0x44 0x48 (by omega) (by omega) (by omega)), memLoad32_store32_same]
  · rw [memLoad32_store32_sep (show Sep (G + BitVec.ofNat 32 0x40) 4 (G + 0x44) 4 from so 0x40 0x44 (by omega) (by omega) (by omega)), memLoad32_store32_same]

theorem finSaved_out (M : Word → BitVec 8) (G : Word) (f : Fin 32 → Word) (v x : Word)
    (h : Sep (G + BitVec.ofNat 32 0x40) 0x20 x 1) : finSaved M G f v x = M x := by
  simp only [finSaved]
  rw [memStore32_get_sep (h.sub (c := 0) (l := 4) (by omega) |> fun h' => by rwa [add_ofNat_zero] at h'),
    saveMem_out G f x finSavePs M (fun p hp => by
      simp only [finSavePs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have := h.sub (c := 0x1C) (l := 4) (by omega); rwa [add_ofNat_assoc] at this
      · have := h.sub (c := 0x18) (l := 4) (by omega); rwa [add_ofNat_assoc] at this
      · have := h.sub (c := 0x14) (l := 4) (by omega); rwa [add_ofNat_assoc] at this
      · have := h.sub (c := 0x10) (l := 4) (by omega); rwa [add_ofNat_assoc] at this
      · have := h.sub (c := 0x0C) (l := 4) (by omega); rwa [add_ofNat_assoc] at this
      · have := h.sub (c := 8) (l := 4) (by omega); rwa [add_ofNat_assoc] at this
      · have := h.sub (c := 4) (l := 4) (by omega); rwa [add_ofNat_assoc] at this)]

theorem fill_memBytes (M : Word → BitVec 8) (dst : Word) (v : BitVec 8) {k n : Nat} (hk : k ≤ n) (hn : n < 2 ^ 32) :
    memBytes (fillBytes M dst v n) dst k = List.replicate k v.toNat := by
  unfold memBytes
  apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_replicate])
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range, List.getElem_replicate]
  unfold fillBytes
  rw [add_sub_toNat dst (by rw [List.length_map, List.length_range] at h1; omega),
    ite_eq_left (by rw [List.length_map, List.length_range] at h1; omega)]

theorem finR_saved (M : Word → BitVec 8) (G : Word) (f : Fin 32 → Word) :
    restoreRegs M G f finSavePs ra = memLoad32 M (G + 0x5C) ∧
    restoreRegs M G f finSavePs s0 = memLoad32 M (G + 0x58) ∧
    restoreRegs M G f finSavePs s1 = memLoad32 M (G + 0x54) ∧
    restoreRegs M G f finSavePs s2 = memLoad32 M (G + 0x50) ∧
    restoreRegs M G f finSavePs s3 = memLoad32 M (G + 0x4C) ∧
    restoreRegs M G f finSavePs s4 = memLoad32 M (G + 0x48) ∧
    restoreRegs M G f finSavePs s5 = memLoad32 M (G + 0x44) := by
  simp +decide [restoreRegs, upd]

theorem finR_other (M : Word → BitVec 8) (G : Word) (f : Fin 32 → Word) (hz : f 0 = 0) (r : Fin 32)
    (q1 : r ≠ ra) (q8 : r ≠ s0) (q9 : r ≠ s1) (q18 : r ≠ s2) (q19 : r ≠ s3) (q20 : r ≠ s4) (q21 : r ≠ s5) :
    restoreRegs M G f finSavePs r = f r := by
  by_cases h0 : r.val = 0
  · have : r = 0 := Fin.ext h0
    subst this; simp [restoreRegs, upd, hz]
  · simp only [restoreRegs, upd, h0, q1, q8, q9, q18, q19, q20, q21, ite_false]

/-- Where `finalize` runs: its code and its callees', the hasher at `S`, the
output at `out`, and 0x190 bytes of stack below `sp0`, all below
0x40000000 and apart from each other and from the round constants. -/
structure FinEnv (M : Word → BitVec 8) (S out sp0 : Word) : Prop where
  cF : CodeIn M (BitVec.ofNat 32 shaFinalizeAddress) shaFinalizeCode
  cSave : CodeIn M (BitVec.ofNat 32 shaFinalizeSaveAddress) shaFinalizeSaveCode
  cRest : CodeIn M (BitVec.ofNat 32 shaFinalizeRestoreAddress) shaFinalizeRestoreCode
  cZ : CodeIn M (BitVec.ofNat 32 shaZero32Address) shaZero32Code
  cBlk : CodeIn M (BitVec.ofNat 32 shaFinalizeBlockAddress) shaFinalizeBlockCode
  cBe : CodeIn M (BitVec.ofNat 32 shaStoreBeAddress) shaStoreBeCode
  cMs : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  cMS : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cMB : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  cC : CodeIn M (BitVec.ofNat 32 sha256CompressAddress) sha256CompressCode
  cI : CodeIn M (BitVec.ofNat 32 sha256CompressAddress + 0x2B94) shaIndexCode
  c97 : CodeIn M (BitVec.ofNat 32 sha256CompressAddress + 0xC09C) shaSigma1PartCode
  cK : CodeIn M (BitVec.ofNat 32 shaKAddress) shaKData
  hS : S.toNat % 4 = 0
  hSw : S.toNat + 0x68 ≤ 0x40000000
  hsp : sp0.toNat % 16 = 0
  hspl : 0x190 ≤ sp0.toNat
  hspw : sp0.toNat ≤ 0x40000000
  hOw : out.toNat + 32 ≤ 0x40000000
  sSF : Sep S 0x68 (sp0 + 0xFFFFFE70) 0x190
  sOF : Sep out 32 (sp0 + 0xFFFFFE70) 0x190
  sOS : Sep out 32 S 0x68
  sKS : Sep (BitVec.ofNat 32 shaKAddress) 256 S 0x68
  sKF : Sep (BitVec.ofNat 32 shaKAddress) 256 (sp0 + 0xFFFFFE70) 0x190

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- **The compiled `finalize` of `sha2`'s SHA-256.** Called with the hasher
at `S` holding `msg` and an output buffer at `out`, it writes FIPS 180-4's
SHA-256 digest of `msg` to the 32 bytes at `out`. It returns to `retAddr`
with `sp` restored and the callee-saved registers kept, and changes no
memory outside the hasher, the output, and 0x190 bytes of stack below `sp`. -/
theorem shaFinalize_correct (m : Machine) {S out sp0 retAddr : Word} {msg : Bytes}
    (E : FinEnv m.mem S out sp0) (hpc : m.pc = BitVec.ofNat 32 shaFinalizeAddress)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = S) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) (H : HasherAt m.mem S msg) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ r, r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 →
        r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) →
        r ≠ (31 : Fin 32) → reg m' r = reg m r) ∧
      memBytes m'.mem out 32 = sha256 msg ∧
      ∀ x, Sep (sp0 + 0xFFFFFE70) 0x190 x 1 → Sep S 0x68 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x := by
  let U := BitVec.ofNat 32 shaFinalizeAddress
  let M0 := m.mem
  let G := sp0 + 0xFFFFFFA0
  let R := sp0 + 0xFFFFFE70
  have hspw := E.hspw
  have hspl := E.hspl
  have hSw := E.hSw
  have hOw := E.hOw
  have hRn : R.toNat = sp0.toNat - 0x190 := by
    show (sp0 + 0xFFFFFE70).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFE70 : Word).toNat = 2 ^ 32 - 0x190 from rfl]; omega
  have hRc : ∀ c, c ≤ 0x190 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hGR : G = R + BitVec.ofNat 32 0x130 := by
    show sp0 + 0xFFFFFFA0 = sp0 + 0xFFFFFE70 + BitVec.ofNat 32 0x130; rw [BitVec.add_assoc]; rfl
  have hGn : G.toNat = sp0.toNat - 0x60 := by rw [hGR, hRc _ (by omega), hRn]; omega
  have Gc : ∀ c, G + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x130 + c) := fun c => by rw [hGR, add_ofNat_assoc]
  have hGc : ∀ c, c ≤ 0x60 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [Gc, hRc _ (by omega), hGn, hRn]; omega
  have hGa : G.toNat % 16 = 0 := by rw [hGn]; have := E.hsp; omega
  have hGa4 : G.toNat % 4 = 0 := by omega
  have codeX : ∀ (My : Word → BitVec 8), (∀ x, Sep R 0x190 x 1 → Sep S 0x68 x 1 → My x = M0 x) →
      ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn My b code := fun My h b code hc hb hbl i hi => by
    rw [h _ ((data_code (by rw [hRn]; omega) hb hbl).subR (c := i) (l := 1) (by omega))
      ((data_code (by omega) hb hbl).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  have Rd : ∀ c l, c + l ≤ 0x190 → ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (R + BitVec.ofNat 32 c) l b k := fun c l h b k hb hbk =>
    data_code (by rw [hRc _ (by omega)]; omega) hb hbk
  have Rx : ∀ c l, c + l ≤ 0x190 → ∀ x, Sep R 0x190 x 1 → Sep (R + BitVec.ofNat 32 c) l x 1 :=
    fun c l h x hx => hx.sub (c := c) (l := l) h
  -- The prologue: the frame, the save helper, and `s6`.
  have st0 : St M0 U m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  obtain ⟨m1, e1, tt1⟩ := st0.aluImm E.cF sf_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFA0 = G by rw [hsp]; rfl] at tt1
  have f1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp G r = reg m r := fun r h => by
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, st0.zero]
    · simp [upd, hr, h]
  have slotP : ∀ (r : Fin 32) (o : Nat), r ≠ t0 → o + 4 ≤ 0x60 → o % 4 = 0 →
      r ≠ t0 ∧ (G + BitVec.ofNat 32 o).toNat % 4 = 0 ∧
        Sep (G + BitVec.ofNat 32 o) 4 (BitVec.ofNat 32 shaFinalizeSaveAddress) shaFinalizeSaveCode.length :=
    fun r o h1 h2 h3 => ⟨h1, aligned_add hGa4 h3, by rw [Gc]; exact Rd _ _ (by omega) _ _ (by decide) (by decide)⟩
  obtain ⟨m2, k2, tt2⟩ := tt1.callSave E.cF sf_at_2 sf_at_6 (b := BitVec.ofNat 32 shaFinalizeSaveAddress)
    (by decide) (by decide) (by decide) E.cSave finSave_shape (by decide) (fun p hp => by
      rw [f1sp]
      simp only [finSavePs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact slotP ra 0x5C (by decide) (by omega) (by omega)
      · exact slotP s0 0x58 (by decide) (by omega) (by omega)
      · exact slotP s1 0x54 (by decide) (by omega) (by omega)
      · exact slotP s2 0x50 (by decide) (by omega) (by omega)
      · exact slotP s3 0x4C (by decide) (by omega) (by omega)
      · exact slotP s4 0x48 (by decide) (by omega) (by omega)
      · exact slotP s5 0x44 (by decide) (by omega) (by omega))
  rw [f1sp] at tt2
  let g1 := upd (reg m) sp G
  have SV : ∀ x, Sep (G + BitVec.ofNat 32 0x40) 0x20 x 1 → saveMem M0 G g1 finSavePs x = M0 x := fun x hx => by
    have := finSaved_out M0 G g1 0 x hx
    simp only [finSaved] at this
    rw [memStore32_get_sep (hx.sub (c := 0) (l := 4) (by omega) |> fun h' => by rwa [add_ofNat_zero] at h')] at this
    exact this
  have SVR : ∀ x, Sep R 0x190 x 1 → saveMem M0 G g1 finSavePs x = M0 x := fun x hx =>
    SV x (by rw [Gc]; exact Rx _ _ (by omega) x hx)
  have g2 : ∀ r, r ≠ sp → r ≠ t0 → upd g1 t0 (U + BitVec.ofNat 32 (2 + 8)) r = reg m r := fun r h1 h2 => by
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, st0.zero]
    · simp [g1, upd, hr, h1, h2]
  have g2sp : upd g1 t0 (U + BitVec.ofNat 32 (2 + 8)) sp = G := by simp +decide [g1, upd]
  have cS := codeX _ (fun x hx _ => SVR x hx) _ _ E.cF (by decide) (by decide)
  obtain ⟨m3, e3, tt3⟩ := tt2.sw cS sf_at_a (off' := 0xC) (by decide)
    (by rw [g2sp]; exact aligned_add hGa4 (k := 0x40) (by decide))
  rw [g2sp, g2 _ (by decide) (by decide), show (0x40 : Word) = BitVec.ofNat 32 0x40 from rfl] at tt3
  let M1 := finSaved M0 G g1 (reg m s6)
  have M1R : ∀ x, Sep R 0x190 x 1 → M1 x = M0 x := fun x hx =>
    finSaved_out M0 G g1 _ x (by rw [Gc]; exact Rx _ _ (by omega) x hx)
  have tt3' : St M1 U m3 0xC (upd g1 t0 (U + BitVec.ofNat 32 (2 + 8))) := tt3
  have K3 : ∀ r, r ≠ sp → r ≠ t0 → reg m3 r = reg m r := fun r h1 h2 => by rw [tt3.regs, g2 r h1 h2]
  have sp3 : reg m3 sp = G := by rw [tt3.regs, g2sp]
  have u3 : St M1 U m3 0xC (reg m3) := tt3'.self
  have cM1 := codeX M1 (fun x hx _ => M1R x hx)
  have cF1 := cM1 _ _ E.cF (by decide) (by decide)
  obtain ⟨m4, e4, u4⟩ := u3.alu cF1 sf_at_c (off' := 0xE) (by decide)
  have K4 := u4.upd_ne u3.zero
  have u4' : St M1 U m4 0xE (reg m4) := u4.self
  obtain ⟨m5, e5, u5⟩ := u4'.alu cF1 sf_at_e (off' := 0x10) (by decide)
  have K5 := u5.upd_ne u4'.zero
  have u5' : St M1 U m5 0x10 (reg m5) := u5.self
  obtain ⟨m6, e6, u6⟩ := u5'.alu cF1 sf_at_10 (off' := 0x12) (by decide)
  have K6 := u6.upd_ne u5'.zero
  have u6' : St M1 U m6 0x12 (reg m6) := u6.self
  obtain ⟨m7, e7, u7⟩ := u6'.auipc cF1 sf_at_12 (off' := 0x16) (by decide)
  obtain ⟨m8, e8, pc8, mem8, regs8⟩ := u7.call cF1 sf_at_16
  have r8 : ∀ r, r ≠ ra → reg m8 r = reg m6 r := fun r h => by
    rw [regs8]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u6'.zero.symm
    · simp [upd, h0, h]
  have K38 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ s2 → r ≠ s4 → reg m8 r = reg m3 r := fun r q1 q10 q18 q20 => by
    rw [r8 r q1, K6 r q10, K5 r q18, K4 r q20]
  have sp8 : reg m8 sp = G := by rw [K38 sp (by decide) (by decide) (by decide) (by decide), sp3]
  have s4_8 : reg m8 s4 = S := by
    rw [r8 s4 (by decide), K6 s4 (by decide), K5 s4 (by decide), u4.upd_eq (by decide), u3.zero,
      K3 a1 (by decide) (by decide), ha1]
    exact BitVec.zero_add _
  have s2_8 : reg m8 s2 = out := by
    rw [r8 s2 (by decide), K6 s2 (by decide), u5.upd_eq (by decide), u4'.zero, K4 a0 (by decide),
      K3 a0 (by decide) (by decide), ha0]
    exact BitVec.zero_add _
  have a0_8 : reg m8 a0 = G := by
    rw [r8 a0 (by decide), u6.upd_eq (by decide), u5'.zero, K5 sp (by decide), K4 sp (by decide), sp3]
    exact BitVec.zero_add _
  have ra8 : reg m8 ra = U + BitVec.ofNat 32 0x1A := by rw [regs8]; simp +decide [upd]; rfl
  have pc8' : m8.pc = BitVec.ofNat 32 shaZero32Address := by
    rw [pc8, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
    decide
  have eZ : G + 0xFFFFFFC0 = R + BitVec.ofNat 32 0xF0 := by
    rw [hGR, BitVec.add_assoc]; rfl
  obtain ⟨m9, c9, pc9, sp9, K9, mem9⟩ := shaZero32_correct m8 (d := G) (T := G)
    (by rw [mem8]; exact cM1 _ _ E.cZ (by decide) (by decide))
    (by rw [mem8]; exact cM1 _ _ E.cMS (by decide) (by decide))
    (by rw [mem8]; exact cM1 _ _ E.cMB (by decide) (by decide))
    pc8' a0_8 ra8 (by decide) sp8 hGa (by omega) (by omega) (by omega)
    (by rw [eZ, hGR]; exact sep_offsets R (Or.inr (by omega)) (by omega) (by omega))
  rw [mem8, eZ] at mem9
  let MA := m9.mem
  have mA : ∀ x, Sep (R + BitVec.ofNat 32 0xF0) 0x40 x 1 → MA x = fillBytes M1 G 0 32 x := mem9
  have MAR : ∀ x, Sep R 0x190 x 1 → MA x = M0 x := fun x hx => by
    rw [mA x (Rx _ _ (by omega) x hx), fillBytes_sep (by rw [hGR]; exact Rx _ _ (by omega) x hx) (Nat.le_refl 32),
      M1R x hx]
  have MAs : ∀ k, 0x40 ≤ k → k < 0x60 → MA (G + BitVec.ofNat 32 k) = M1 (G + BitVec.ofNat 32 k) := fun k h1 h2 => by
    rw [mA _ (by rw [Gc]; exact sep_offsets R (Or.inl (by omega)) (by omega) (by omega)),
      fillBytes_sep (by
        have h := sep_offsets G (c := 0) (n := 32) (d := k) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at h) (Nat.le_refl 32)]
  have cMA := codeX MA (fun x hx _ => MAR x hx)
  have cFA := cMA _ _ E.cF (by decide) (by decide)
  have u9 : St MA U m9 0x1A (reg m9) := ⟨by rw [pc9], rfl, fun _ => rfl⟩
  have k9 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → reg m9 r = reg m8 r := K9
  obtain ⟨m10, e10, u10⟩ := u9.aluImm cFA sf_at_1a (off' := 0x1E) (by decide)
  have K10 := u10.upd_ne u9.zero
  have u10' : St MA U m10 0x1E (reg m10) := u10.self
  obtain ⟨m11, e11, u11⟩ := u10'.aluImm cFA sf_at_1e (off' := 0x20) (by decide)
  have K11 := u11.upd_ne u10'.zero
  have u11' : St MA U m11 0x20 (reg m11) := u11.self
  obtain ⟨m12, e12, u12⟩ := u11'.aluImm cFA sf_at_20 (off' := 0x22) (by decide)
  have K12 := u12.upd_ne u11'.zero
  have u12' : St MA U m12 0x22 (reg m12) := u12.self
  obtain ⟨m13, e13, u13⟩ := u12'.auipc cFA sf_at_22 (off' := 0x26) (by decide)
  obtain ⟨m14, e14, pc14, mem14, regs14⟩ := u13.call cFA sf_at_26
  have r14 : ∀ r, r ≠ ra → reg m14 r = reg m12 r := fun r h => by
    rw [regs14]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u12'.zero.symm
    · simp [upd, h0, h]
  have K914 : ∀ r, r ≠ ra → r ≠ s1 → r ≠ a0 → r ≠ s0 → reg m14 r = reg m9 r := fun r q1 q9 q10 q8 => by
    rw [r14 r q1, K12 r q8, K11 r q10, K10 r q9]
  have sp14 : reg m14 sp = G := by rw [K914 sp (by decide) (by decide) (by decide) (by decide), sp9]
  have a0_14 : reg m14 a0 = G + BitVec.ofNat 32 0x20 := by
    rw [r14 a0 (by decide), K12 a0 (by decide), u11.upd_eq (by decide), K10 sp (by decide), sp9]; rfl
  have ra14 : reg m14 ra = U + BitVec.ofNat 32 0x2A := by rw [regs14]; simp +decide [upd]; rfl
  have pc14' : m14.pc = BitVec.ofNat 32 shaZero32Address := by
    rw [pc14, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
    decide
  obtain ⟨m15, c15, pc15, sp15, K15, mem15⟩ := shaZero32_correct m14 (d := G + BitVec.ofNat 32 0x20) (T := G)
    (by rw [mem14]; exact cMA _ _ E.cZ (by decide) (by decide))
    (by rw [mem14]; exact cMA _ _ E.cMS (by decide) (by decide))
    (by rw [mem14]; exact cMA _ _ E.cMB (by decide) (by decide))
    pc14' a0_14 ra14 (by decide) sp14 hGa (by omega) (by omega) (by rw [hGc _ (by omega)]; omega)
    (by rw [eZ, Gc]; exact sep_offsets R (Or.inr (by omega)) (by omega) (by omega))
  rw [mem14, eZ] at mem15
  let M2 := m15.mem
  have m2 : ∀ x, Sep (R + BitVec.ofNat 32 0xF0) 0x40 x 1 → M2 x = fillBytes MA (G + BitVec.ofNat 32 0x20) 0 32 x :=
    mem15
  have M2R : ∀ x, Sep R 0x190 x 1 → M2 x = M0 x := fun x hx => by
    rw [m2 x (Rx _ _ (by omega) x hx), fillBytes_sep (by rw [Gc]; exact Rx _ _ (by omega) x hx) (Nat.le_refl 32),
      MAR x hx]
  have M2s : ∀ k, 0x40 ≤ k → k < 0x60 → M2 (G + BitVec.ofNat 32 k) = M1 (G + BitVec.ofNat 32 k) := fun k h1 h2 => by
    rw [m2 _ (by rw [Gc]; exact sep_offsets R (Or.inl (by omega)) (by omega) (by omega)),
      fillBytes_sep (sep_offsets G (Or.inl (by omega)) (by omega) (by omega)) (Nat.le_refl 32), MAs k h1 h2]
  have u15 : St M2 U m15 0x2A (reg m15) := ⟨by rw [pc15], rfl, fun _ => rfl⟩
  have k15 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → reg m15 r = reg m14 r := K15
  -- Registers at 0x2A.
  have Kp : ∀ r, r ≠ sp → r ≠ ra → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s4 →
      r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) →
      r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → reg m15 r = reg m r :=
    fun r q2 q1 q5 q6 q7 q8 q9 q18 q20 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 => by
      rw [k15 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30, K914 r q1 q9 q10 q8,
        k9 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30, K38 r q1 q10 q18 q20, K3 r q2 q5]
  have sp15' : reg m15 sp = G := sp15
  have s4_15 : reg m15 s4 = S := by
    rw [k15 s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), K914 s4 (by decide) (by decide) (by decide)
      (by decide), k9 s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s4_8]
  have s2_15 : reg m15 s2 = out := by
    rw [k15 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), K914 s2 (by decide) (by decide) (by decide)
      (by decide), k9 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s2_8]
  have s1_15 : reg m15 s1 = S + 0x40 := by
    rw [k15 s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), r14 s1 (by decide), K12 s1 (by decide),
      K11 s1 (by decide), u10.upd_eq (by decide), k9 s4 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), s4_8]; rfl
  have s0_15 : reg m15 s0 = G + BitVec.ofNat 32 0x20 := by
    rw [k15 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), r14 s0 (by decide), u12.upd_eq (by decide),
      K11 sp (by decide), K10 sp (by decide), sp9]; rfl
  -- The message length.
  have hlen := H.hlen
  have SR : ∀ c, c < 0x68 → Sep R 0x190 (S + BitVec.ofNat 32 c) 1 := fun c hc =>
    (E.sSF.sub (c := c) (l := 1) (by omega)).symm
  have ldS : ∀ (My : Word → BitVec 8), (∀ x, Sep R 0x190 x 1 → My x = M0 x) → ∀ c, c + 4 ≤ 0x68 →
      memLoad32 My (S + BitVec.ofNat 32 c) = memLoad32 M0 (S + BitVec.ofNat 32 c) := fun My h c hc =>
    memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (SR _ (by omega))
  have cF2 := codeX M2 (fun x hx _ => M2R x hx) _ _ E.cF (by decide) (by decide)
  obtain ⟨m16, c16, u16, s5_16, s6_16, s3_16, a2_16, K16⟩ := fin_len (pos := msg.length % 64) (lo := BitVec.ofNat 32 (msg.length / 64)) u15 cF2 s4_15 E.hS
    (by rw [show S + (0x60 : Word) = S + BitVec.ofNat 32 0x60 from rfl, ldS M2 M2R 0x60 (by omega)]; exact H.lo)
    (by rw [show S + (0x64 : Word) = S + BitVec.ofNat 32 0x64 from rfl, ldS M2 M2R 0x64 (by omega)]; exact H.hi)
    (by rw [show S + (0x3F : Word) = S + BitVec.ofNat 32 0x3F from rfl, M2R _ (SR _ (by omega))]; exact H.pos)
    (Nat.mod_lt _ (by decide))
  let pos := msg.length % 64
  have hpos : pos < 64 := Nat.mod_lt _ (by decide)
  have k16 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ s3 →
      r ≠ s5 → r ≠ s6 → reg m16 r = reg m15 r := K16
  have s4_16 : reg m16 s4 = S := by
    rw [k16 s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), s4_15]
  -- The padding byte, then `memset` for the zeros after it.
  obtain ⟨m17, e17, u17⟩ := u16.alu cF2 sf_at_86 (off' := 0x8A) (by decide)
  have K17 := u17.upd_ne u16.zero
  have u17' : St M2 U m17 0x8A (reg m17) := u17.self
  have a0_17 : reg m17 a0 = S + BitVec.ofNat 32 pos := by rw [u17.upd_eq (by decide), s4_16, a2_16]; rfl
  obtain ⟨m18, e18, u18⟩ := u17'.aluImm cF2 sf_at_8a (off' := 0x8E) (by decide)
  have K18 := u18.upd_ne u17'.zero
  have u18' : St M2 U m18 0x8E (reg m18) := u18.self
  obtain ⟨m19, e19, u19⟩ := u18'.sb cF2 sf_at_8e (off' := 0x92) (by decide)
  rw [K18 a0 (by decide), a0_17, add_lit_zero, u18.upd_eq (by decide), u17'.zero] at u19
  let MP := memStore8 M2 (S + BitVec.ofNat 32 pos) ((aluEval .add 0 0x80 : Word).extractLsb' 0 8)
  have MPR : ∀ x, Sep R 0x190 x 1 → Sep S 0x68 x 1 → MP x = M0 x := fun x hx hy => by
    show memStore8 M2 _ _ x = _
    rw [memStore8_ne (fun e => hy pos (by omega) 0 (by decide) (by rw [add_ofNat_zero, e])), M2R x hx]
  have cMP := codeX MP MPR
  have cFP := cMP _ _ E.cF (by decide) (by decide)
  have u19' : St MP U m19 0x92 (reg m19) := u19.self
  obtain ⟨m20, e20, u20⟩ := u19'.aluImm cFP sf_at_92 (off' := 0x94) (by decide)
  have K20 := u20.upd_ne u19'.zero
  have u20' : St MP U m20 0x94 (reg m20) := u20.self
  obtain ⟨m21, e21, u21⟩ := u20'.aluImm cFP sf_at_94 (off' := 0x96) (by decide)
  have K21 := u21.upd_ne u20'.zero
  have u21' : St MP U m21 0x96 (reg m21) := u21.self
  obtain ⟨m22, e22, u22⟩ := u21'.alu cFP sf_at_96 (off' := 0x98) (by decide)
  have K22 := u22.upd_ne u21'.zero
  have u22' : St MP U m22 0x98 (reg m22) := u22.self
  obtain ⟨m23, e23, u23⟩ := u22'.auipc cFP sf_at_98 (off' := 0x9C) (by decide)
  obtain ⟨m24, e24, pc24, mem24, regs24⟩ := u23.call cFP sf_at_9c
  have r24 : ∀ r, r ≠ ra → reg m24 r = reg m22 r := fun r h => by
    rw [regs24]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u22'.zero.symm
    · simp [upd, h0, h]
  have K1624 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m24 r = reg m16 r := fun r q1 q10 q11 q12 => by
    rw [r24 r q1, K22 r q12, K21 r q11, K20 r q10, u19.regs, K18 r q11, K17 r q10]
  have hd1 : (S + BitVec.ofNat 32 (pos + 1)).toNat = S.toNat + (pos + 1) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨m25, c25, pc25, mem25, a025, K25⟩ := memset_correct m24 (BitVec.ofNat 32 memsetAddress)
    (U + BitVec.ofNat 32 0xA0) (S + BitVec.ofNat 32 (pos + 1)) 0 (63 - pos)
    (fun i hi => by show m24.mem _ = _; rw [mem24]; exact cMP _ _ E.cMs (by decide) (by decide) i hi) (by decide)
    (by rw [pc24, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
        decide)
    (by rw [r24 a0 (by decide), K22 a0 (by decide), K21 a0 (by decide), u20.upd_eq (by decide), u19.regs,
          K18 a0 (by decide), a0_17]
        show S + BitVec.ofNat 32 pos + BitVec.ofNat 32 1 = _; rw [add_ofNat_assoc])
    (by rw [r24 a1 (by decide), K22 a1 (by decide), u21.upd_eq (by decide), u20'.zero]; rfl)
    (by rw [r24 a2 (by decide), u22.upd_eq (by decide), u21'.zero, K21 s3 (by decide), K20 s3 (by decide),
          u19.regs, K18 s3 (by decide), K17 s3 (by decide), s3_16]; exact BitVec.zero_add _)
    (by rw [regs24]; simp +decide [upd]; rfl) (by decide)
    (by rw [hd1]; omega)
    (data_code (by rw [hd1]; omega) (by decide) (by decide))
  rw [mem24] at mem25
  let MQ := fillBytes MP (S + BitVec.ofNat 32 (pos + 1)) ((0 : Word).extractLsb' 0 8) (63 - pos)
  have MQR : ∀ x, Sep R 0x190 x 1 → Sep S 0x68 x 1 → MQ x = M0 x := fun x hx hy => by
    show fillBytes MP _ _ _ x = _
    rw [fillBytes_sep (hy.sub (c := pos + 1) (l := 63 - pos) (by omega)) (Nat.le_refl _), MPR x hx hy]
  -- The hasher's bytes after the padding.
  have q1 : ∀ i, i < pos → MQ (S + BitVec.ofNat 32 i) = M0 (S + BitVec.ofNat 32 i) := fun i hi => by
    show fillBytes MP _ _ _ _ = _
    rw [fillBytes_sep (sep_offsets S (Or.inr (by omega)) (by omega) (by omega)) (Nat.le_refl _)]
    show memStore8 M2 _ _ _ = _
    rw [memStore8_ne (add_ofNat_ne S (by omega) (by omega) (by omega)), M2R _ (SR _ (by omega))]
  have q4 : ∀ i, 64 ≤ i → i < 0x68 → MQ (S + BitVec.ofNat 32 i) = M0 (S + BitVec.ofNat 32 i) := fun i h1 h2 => by
    show fillBytes MP _ _ _ _ = _
    rw [fillBytes_sep (sep_offsets S (Or.inl (by omega)) (by omega) (by omega)) (Nat.le_refl _)]
    show memStore8 M2 _ _ _ = _
    rw [memStore8_ne (add_ofNat_ne S (by omega) (by omega) (by omega)), M2R _ (SR _ (by omega))]
  have mq : ∀ k, pos < k → k ≤ 64 → memBytes MQ S k = tailBytes msg ++ [0x80] ++ List.replicate (k - pos - 1) 0 := by
    intro k h1 h2
    rw [show k = pos + (1 + (k - pos - 1)) by omega, memBytes_split, memBytes_split, show pos + (1 + (k - pos - 1)) - pos - 1 = k - pos - 1 by omega]
    have b1 : memBytes MQ S pos = tailBytes msg := by
      rw [← H.buf]; exact memBytes_congr fun i hi => q1 i hi
    have b2 : memBytes MQ (S + BitVec.ofNat 32 pos) 1 = [0x80] := by
      show [(MQ (S + BitVec.ofNat 32 pos + BitVec.ofNat 32 0)).toNat] = _
      rw [add_ofNat_zero]
      show [(fillBytes MP _ _ _ _).toNat] = _
      rw [fillBytes_sep (sep_offsets S (Or.inr (by omega)) (by omega) (by omega)) (Nat.le_refl _)]
      show [(memStore8 M2 _ _ _).toNat] = _
      rw [memStore8_same]; rfl
    have b3 : memBytes MQ (S + BitVec.ofNat 32 pos + BitVec.ofNat 32 1) (k - pos - 1) = List.replicate (k - pos - 1) 0 := by
      rw [add_ofNat_assoc]
      exact fill_memBytes MP _ _ (by omega) (by omega)
    rw [b1, b2, b3, List.append_assoc]
  have wQ : wordsAt MQ (S + 0x40) 8 = (fullBlocks msg).foldl Sha256.compress Sha256.h0 := by
    rw [← H.hash]; apply wordsAt_congr; intro i hi
    apply memLoad32_congr; intro j hj
    rw [show S + (0x40 : Word) = S + BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc, add_ofNat_assoc]
    exact q4 _ (by omega) (by omega)
  have u25 : St MQ U m25 0xA0 (reg m25) := ⟨by rw [pc25], mem25, fun _ => rfl⟩
  have k25 : ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → reg m25 r = reg m24 r := K25
  have cQ := codeX MQ MQR
  have cFQ := cQ _ _ E.cF (by decide) (by decide)
  have K1625 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 →
      reg m25 r = reg m16 r := fun r q1 q10 q11 q12 q13 q14 q15 q16 => by
    rw [k25 r q12 q13 q14 q15 q16, K1624 r q1 q10 q11 q12]
  have g16 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ s3 →
      r ≠ s5 → r ≠ s6 → reg m16 r = reg m15 r := k16
  have s1_16 : reg m16 s1 = S + 0x40 := by
    rw [g16 s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), s1_15]
  obtain ⟨m26, e26, u26⟩ := u25.aluImm cFQ sf_at_a0 (off' := 0xA2) (by decide)
  have K26 := u26.upd_ne u25.zero
  have u26' : St MQ U m26 0xA2 (reg m26) := u26.self
  have s3_26 : reg m26 s3 = BitVec.ofNat 32 (63 - pos) := by
    rw [K26 s3 (by decide), K1625 s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), s3_16]
  have a0_26 : reg m26 a0 = BitVec.ofNat 32 7 := by rw [u26.upd_eq (by decide), u25.zero]; rfl
  let B1 : List Bytes := if pos < 56 then [] else [tailBytes msg ++ [0x80] ++ List.replicate (63 - pos) 0]
  let lastPre : Bytes := if pos < 56 then tailBytes msg ++ [0x80] ++ List.replicate (55 - pos) 0 else List.replicate 56 0
  have C2 : ∃ (nC : Machine) (MC : Word → BitVec 8), Steps m26 nC ∧ St MC U nC 0xC2 (reg nC) ∧
      (∀ x, Sep R 0x190 x 1 → Sep S 0x68 x 1 → MC x = M0 x) ∧
      (∀ k, 0x40 ≤ k → k < 0x60 → MC (G + BitVec.ofNat 32 k) = MQ (G + BitVec.ofNat 32 k)) ∧
      memBytes MC S 56 = lastPre ∧
      wordsAt MC (S + 0x40) 8 = (fullBlocks msg ++ B1).foldl Sha256.compress Sha256.h0 ∧
      ∀ r, r ≠ ra → r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 →
        r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
        r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → reg nC r = reg m26 r := by
    by_cases hsh : pos < 56
    · obtain ⟨n27, d27, u27⟩ := u26'.taken cFQ 0xC2 sf_at_a2 (by decide) (by
        simp only [branchTaken]; rw [a0_26, s3_26, ult_lit (by decide) (by omega)]
        exact decide_eq_true (by omega))
      refine ⟨n27, MQ, .single d27, u27.self, MQR, fun _ _ _ => rfl, ?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        u27.regs r⟩
      · show memBytes MQ S 56 = if pos < 56 then _ else _
        rw [ite_eq_left_of_eq_true _ _ (eq_true hsh), mq 56 (by omega) (by omega),
          show 56 - pos - 1 = 55 - pos by omega]
      · show _ = (fullBlocks msg ++ (if pos < 56 then [] else _)).foldl _ _
        rw [ite_eq_left_of_eq_true _ _ (eq_true hsh), List.append_nil, wQ]
    · -- 56 bytes or more: compress the padded buffer, then zero 56 bytes of it.
      obtain ⟨n27, d27, u27⟩ := u26'.notTaken cFQ 0xA6 sf_at_a2 (by decide) (by
        simp only [branchTaken]; rw [a0_26, s3_26, ult_lit (by decide) (by omega)]
        exact decide_eq_false (by omega))
      have u27' : St MQ U n27 0xA6 (reg n27) := u27.self
      obtain ⟨n28, d28, u28⟩ := u27'.alu cFQ sf_at_a6 (off' := 0xA8) (by decide)
      have K28 := u28.upd_ne u27'.zero
      have u28' : St MQ U n28 0xA8 (reg n28) := u28.self
      obtain ⟨n29, d29, u29⟩ := u28'.alu cFQ sf_at_a8 (off' := 0xAA) (by decide)
      have K29 := u29.upd_ne u28'.zero
      have u29' : St MQ U n29 0xAA (reg n29) := u29.self
      obtain ⟨n30, d30, u30⟩ := u29'.auipc cFQ sf_at_aa (off' := 0xAE) (by decide)
      obtain ⟨n31, d31, pc31, mem31, regs31⟩ := u30.call cFQ sf_at_ae
      have r31 : ∀ r, r ≠ ra → reg n31 r = reg n29 r := fun r h => by
        rw [regs31]
        by_cases h0 : r.val = 0
        · have : r = 0 := Fin.ext h0
          subst this; simp [upd]; exact u29'.zero.symm
        · simp [upd, h0, h]
      have K2631 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → reg n31 r = reg m26 r := fun r q1 q10 q11 => by
        rw [r31 r q1, K29 r q11, K28 r q10, u27.regs]
      have s4_26 : reg m26 s4 = S := by
        rw [K26 s4 (by decide), K1625 s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), s4_16]
      have s1_26 : reg m26 s1 = S + 0x40 := by
        rw [K26 s1 (by decide), K1625 s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), s1_16]
      have sp26 : reg m26 sp = G := by
        rw [K26 sp (by decide), K1625 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), g16 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp15']
      have eT : G + 0xFFFFFED0 = R := by rw [hGR, BitVec.add_assoc]; exact BitVec.add_zero R
      have S40 : (S + 0x40).toNat = S.toNat + 0x40 := by
        rw [show S + (0x40 : Word) = S + BitVec.ofNat 32 0x40 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      obtain ⟨n32, c32, pc32, sp32, K32, w32, fr32⟩ := shaFinBlock_correct n31 (st := S + 0x40) (bp := S) (T := G) (retAddr := U + BitVec.ofNat 32 0xB2)
        (by rw [mem31]; exact cQ _ _ E.cBlk (by decide) (by decide))
        (by rw [mem31]; exact cQ _ _ E.cMS (by decide) (by decide))
        (by rw [mem31]; exact cQ _ _ E.cMB (by decide) (by decide))
        (by rw [mem31]; exact cQ _ _ E.cC (by decide) (by decide))
        (by rw [mem31]; exact cQ _ _ E.cI (by decide) (by decide))
        (by rw [mem31]; exact cQ _ _ E.c97 (by decide) (by decide))
        (fun i hi => by
          have hi' : i < 256 := by rw [show shaKData.length = 256 from rfl] at hi; exact hi
          rw [mem31, MQR _ (E.sKF.sub (c := i) (l := 1) (by omega)).symm (E.sKS.sub (c := i) (l := 1) (by omega)).symm]
          exact E.cK i hi)
        (by rw [pc31, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
            decide)
        (by rw [r31 a0 (by decide), K29 a0 (by decide), u28.upd_eq (by decide), u27'.zero, u27.regs, s1_26]
            exact BitVec.zero_add _)
        (by rw [r31 a1 (by decide), u29.upd_eq (by decide), u28'.zero, K28 s4 (by decide), u27.regs, s4_26]
            exact BitVec.zero_add _)
        (by rw [regs31]; simp +decide [upd]; try rfl) (by decide)
        (by rw [K2631 sp (by decide) (by decide) (by decide), sp26]) hGa (by omega) (by omega)
        (by rw [S40]; have := E.hS; omega) (by rw [S40]; omega) (by omega)
        (by rw [eT]; exact (E.sSF.sub (c := 0x40) (l := 32) (by omega)).subR (c := 0) (l := 0x130) (by omega)
              |> fun h => by rwa [add_ofNat_zero] at h)
        (by rw [eT]; have h := (E.sSF.sub (c := 0) (l := 64) (by omega)).subR (c := 0) (l := 0x130) (by omega)
            rwa [add_ofNat_zero, add_ofNat_zero] at h)
        (by rw [eT]; have h := E.sKF.subR (c := 0) (l := 0x130) (by omega); rwa [add_ofNat_zero] at h)
        (E.sKS.subR (c := 0x40) (l := 32) (by omega))
      rw [eT, mem31] at fr32
      rw [mem31] at w32
      let MF := n32.mem
      have fF : ∀ x, Sep R 0x130 x 1 → Sep (S + 0x40) 32 x 1 → MF x = MQ x := fr32
      have FS : ∀ x, Sep R 0x190 x 1 → Sep S 0x68 x 1 → MF x = MQ x := fun x hx hy =>
        fF x (by have h := hx.sub (c := 0) (l := 0x130) (by omega); rwa [add_ofNat_zero] at h)
          (hy.sub (c := 0x40) (l := 32) (by omega))
      have MFR : ∀ x, Sep R 0x190 x 1 → Sep S 0x68 x 1 → MF x = M0 x := fun x hx hy => by rw [FS x hx hy, MQR x hx hy]
      have cF' := codeX MF MFR
      have cFF := cF' _ _ E.cF (by decide) (by decide)
      have u32 : St MF U n32 0xB2 (reg n32) := ⟨by rw [pc32], rfl, fun _ => rfl⟩
      have k32 : ∀ r, r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 →
          r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
          r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → reg n32 r = reg n31 r := K32
      have s4_32 : reg n32 s4 = S := by
        rw [k32 s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          K2631 s4 (by decide) (by decide) (by decide), s4_26]
      obtain ⟨n33, d33, u33⟩ := u32.aluImm cFF sf_at_b2 (off' := 0xB6) (by decide)
      have K33 := u33.upd_ne u32.zero
      have u33' : St MF U n33 0xB6 (reg n33) := u33.self
      obtain ⟨n34, d34, u34⟩ := u33'.alu cFF sf_at_b6 (off' := 0xB8) (by decide)
      have K34 := u34.upd_ne u33'.zero
      have u34' : St MF U n34 0xB8 (reg n34) := u34.self
      obtain ⟨n35, d35, u35⟩ := u34'.aluImm cFF sf_at_b8 (off' := 0xBA) (by decide)
      have K35 := u35.upd_ne u34'.zero
      have u35' : St MF U n35 0xBA (reg n35) := u35.self
      obtain ⟨n36, d36, u36⟩ := u35'.auipc cFF sf_at_ba (off' := 0xBE) (by decide)
      obtain ⟨n37, d37, pc37, mem37, regs37⟩ := u36.call cFF sf_at_be
      have r37 : ∀ r, r ≠ ra → reg n37 r = reg n35 r := fun r h => by
        rw [regs37]
        by_cases h0 : r.val = 0
        · have : r = 0 := Fin.ext h0
          subst this; simp [upd]; exact u35'.zero.symm
        · simp [upd, h0, h]
      obtain ⟨n38, c38, pc38, mem38, a038, K38⟩ := memset_correct n37 (BitVec.ofNat 32 memsetAddress)
        (U + BitVec.ofNat 32 0xC2) S 0 56
        (fun i hi => by show n37.mem _ = _; rw [mem37]; exact cF' _ _ E.cMs (by decide) (by decide) i hi) (by decide)
        (by rw [pc37, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
            decide)
        (by rw [r37 a0 (by decide), K35 a0 (by decide), u34.upd_eq (by decide), u33'.zero, K33 s4 (by decide), s4_32]
            exact BitVec.zero_add _)
        (by rw [r37 a1 (by decide), u35.upd_eq (by decide), u34'.zero]; rfl)
        (by rw [r37 a2 (by decide), K35 a2 (by decide), K34 a2 (by decide), u33.upd_eq (by decide), u32.zero]; rfl)
        (by rw [regs37]; simp +decide [upd]; try rfl) (by decide) (by omega)
        (data_code (by omega) (by decide) (by decide))
      rw [mem37] at mem38
      let MR := fillBytes MF S ((0 : Word).extractLsb' 0 8) 56
      have RS : ∀ x, Sep S 0x68 x 1 → Sep S 56 x 1 := fun x hy => by
        have h := hy.sub (c := 0) (l := 56) (by omega); rwa [add_ofNat_zero] at h
      have MRR : ∀ x, Sep R 0x190 x 1 → Sep S 0x68 x 1 → MR x = M0 x := fun x hx hy => by
        show fillBytes MF _ _ _ x = _
        rw [fillBytes_sep (RS x hy) (Nat.le_refl 56), MFR x hx hy]
      have k38 : ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → reg n38 r = reg n37 r := K38
      refine ⟨n38, MR, .cons d27 (.cons d28 (.cons d29 (.cons d30 (.cons d31 (c32.trans (.cons d33 (.cons d34
        (.cons d35 (.cons d36 (.cons d37 c38)))))))))), ⟨by rw [pc38], mem38, fun _ => rfl⟩, MRR, ?_, ?_, ?_,
        fun r q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => ?_⟩
      · intro k h1 h2
        have hGk : Sep R 0x130 (G + BitVec.ofNat 32 k) 1 := by
          rw [Gc]
          have h := sep_offsets R (c := 0) (n := 0x130) (d := 0x130 + k) (k := 1) (Or.inl (by omega)) (by omega)
            (by omega)
          rwa [add_ofNat_zero] at h
        have hGs : Sep S 0x68 (G + BitVec.ofNat 32 k) 1 := by
          rw [Gc]; exact (E.sSF.subR (c := 0x130 + k) (l := 1) (by omega))
        show fillBytes MF _ _ _ _ = _
        rw [fillBytes_sep (RS _ hGs) (Nat.le_refl 56), fF _ hGk (hGs.sub (c := 0x40) (l := 32) (by omega))]
      · show memBytes MR S 56 = if pos < 56 then _ else _
        rw [ite_eq_right_of_eq_false _ _ (eq_false hsh)]
        exact fill_memBytes MF S _ (Nat.le_refl 56) (by decide)
      · show _ = (fullBlocks msg ++ (if pos < 56 then [] else _)).foldl _ _
        rw [ite_eq_right_of_eq_false _ _ (eq_false hsh), List.foldl_append, List.foldl_cons, List.foldl_nil,
          ← wQ, show 63 - pos = 64 - pos - 1 by omega, ← mq 64 (by omega) (by omega), ← w32]
        apply wordsAt_congr; intro i hi
        apply memLoad32_congr; intro j hj
        rw [show S + (0x40 : Word) = S + BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc, add_ofNat_assoc]
        have h := sep_offsets S (c := 0) (n := 56) (d := 0x40 + (4 * i + j)) (k := 1) (Or.inl (by omega)) (by omega)
          (by omega)
        rw [add_ofNat_zero] at h
        show fillBytes MF _ _ _ _ = _
        rw [fillBytes_sep h (Nat.le_refl 56)]
      · rw [k38 r q12 q13 q14 q15 q16, r37 r q1, K35 r q11, K34 r q10, K33 r q12,
          k32 r q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, K2631 r q1 q10 q11]
  obtain ⟨nC, MC, cC, uC, MCR, MCs, bC, wC, KC⟩ := C2
  -- Registers at 0xC2, from `m16`.
  have KC16 : ∀ r, r ≠ ra → r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 →
      r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
      r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → reg nC r = reg m16 r :=
    fun r q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => by
      rw [KC r q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, K26 r q10,
        K1625 r q1 q10 q11 q12 q13 q14 q15 q16]
  have rC : ∀ r, r = s0 ∨ r = s1 ∨ r = s2 ∨ r = s4 ∨ r = s5 ∨ r = s6 ∨ r = sp → reg nC r = reg m16 r := by
    intro r h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact KC16 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g16' : ∀ r, r = s0 ∨ r = s1 ∨ r = s2 ∨ r = s4 ∨ r = sp → reg m16 r = reg m15 r := by
    intro r h
    rcases h with rfl | rfl | rfl | rfl | rfl <;>
      exact g16 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
  have s4C : reg nC s4 = S := by rw [rC s4 (by decide), g16' s4 (by decide), s4_15]
  have s1C : reg nC s1 = S + 0x40 := by rw [rC s1 (by decide), g16' s1 (by decide), s1_15]
  have s0C : reg nC s0 = G + BitVec.ofNat 32 0x20 := by rw [rC s0 (by decide), g16' s0 (by decide), s0_15]
  have s2C : reg nC s2 = out := by rw [rC s2 (by decide), g16' s2 (by decide), s2_15]
  have spC : reg nC sp = G := by rw [rC sp (by decide), g16' sp (by decide), sp15']
  have s5C := (rC s5 (by decide)).trans s5_16
  have s6C := (rC s6 (by decide)).trans s6_16
  have cCC := codeX MC MCR
  have cFC := cCC _ _ E.cF (by decide) (by decide)
  -- The length, then the last block.
  obtain ⟨n40, d40, u40⟩ := uC.sw cFC sf_at_c2 (off' := 0xC6) (by decide)
    (by rw [s4C]; exact aligned_add E.hS (k := 0x38) (by decide))
  rw [s4C, s6C, show (0x38 : Word) = BitVec.ofNat 32 0x38 from rfl] at u40
  have hst : ∀ c, 0x38 ≤ c → c + 4 ≤ 0x40 → ∀ x, Sep R 0x190 x 1 → Sep S 0x68 x 1 → Sep (S + BitVec.ofNat 32 c) 4 x 1 :=
    fun c h1 h2 x _ hy => hy.sub (c := c) (l := 4) (by omega)
  obtain ⟨n41, d41, u41⟩ := u40.sw (cCC _ _ E.cF (by decide) (by decide) |>.store32 (data_code
      (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) (by decide))) sf_at_c6 (off' := 0xCA) (by decide)
    (by rw [s4C]; exact aligned_add E.hS (k := 0x3C) (by decide))
  rw [s4C, s5C, show (0x3C : Word) = BitVec.ofNat 32 0x3C from rfl] at u41
  let lo : Word := BitVec.ofNat 32 (msg.length / 64)
  let ML := memStore32 (memStore32 MC (S + BitVec.ofNat 32 0x38) (bswap32 (lo >>> 23))) (S + BitVec.ofNat 32 0x3C)
    (bswap32 ((lo <<< 9) ||| (BitVec.ofNat 32 pos <<< 3)))
  have MLR : ∀ x, Sep R 0x190 x 1 → Sep S 0x68 x 1 → ML x = M0 x := fun x hx hy => by
    show memStore32 (memStore32 MC _ _) _ _ x = _
    rw [memStore32_get_sep (hst 0x3C (by omega) (by omega) x hx hy),
      memStore32_get_sep (hst 0x38 (by omega) (by omega) x hx hy), MCR x hx hy]
  have cML := codeX ML MLR
  have cFL := cML _ _ E.cF (by decide) (by decide)
  have u41' : St ML U n41 0xCA (reg n41) := u41.self
  obtain ⟨n42, d42, u42⟩ := u41'.alu cFL sf_at_ca (off' := 0xCC) (by decide)
  have K42 := u42.upd_ne u41'.zero
  have u42' : St ML U n42 0xCC (reg n42) := u42.self
  obtain ⟨n43, d43, u43⟩ := u42'.alu cFL sf_at_cc (off' := 0xCE) (by decide)
  have K43 := u43.upd_ne u42'.zero
  have u43' : St ML U n43 0xCE (reg n43) := u43.self
  obtain ⟨n44, d44, u44⟩ := u43'.auipc cFL sf_at_ce (off' := 0xD2) (by decide)
  obtain ⟨n45, d45, pc45, mem45, regs45⟩ := u44.call cFL sf_at_d2
  have r45 : ∀ r, r ≠ ra → reg n45 r = reg n43 r := fun r h => by
    rw [regs45]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u43'.zero.symm
    · simp [upd, h0, h]
  have r41 : ∀ r, reg n41 r = reg nC r := fun r => u41.regs r
  have KC45 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → reg n45 r = reg nC r := fun r q1 q10 q11 => by
    rw [r45 r q1, K43 r q11, K42 r q10, r41]
  have eT : G + 0xFFFFFED0 = R := by rw [hGR, BitVec.add_assoc]; exact BitVec.add_zero R
  have S40 : (S + 0x40).toNat = S.toNat + 0x40 := by
    rw [show S + (0x40 : Word) = S + BitVec.ofNat 32 0x40 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨n46, c46, pc46, sp46, K46, w46, fr46⟩ := shaFinBlock_correct n45 (st := S + 0x40) (bp := S) (T := G)
    (retAddr := U + BitVec.ofNat 32 0xD6)
    (by rw [mem45]; exact cML _ _ E.cBlk (by decide) (by decide))
    (by rw [mem45]; exact cML _ _ E.cMS (by decide) (by decide))
    (by rw [mem45]; exact cML _ _ E.cMB (by decide) (by decide))
    (by rw [mem45]; exact cML _ _ E.cC (by decide) (by decide))
    (by rw [mem45]; exact cML _ _ E.cI (by decide) (by decide))
    (by rw [mem45]; exact cML _ _ E.c97 (by decide) (by decide))
    (fun i hi => by
      have hi' : i < 256 := by rw [show shaKData.length = 256 from rfl] at hi; exact hi
      rw [mem45, MLR _ (E.sKF.sub (c := i) (l := 1) (by omega)).symm (E.sKS.sub (c := i) (l := 1) (by omega)).symm]
      exact E.cK i hi)
    (by rw [pc45, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
        decide)
    (by rw [r45 a0 (by decide), K43 a0 (by decide), u42.upd_eq (by decide), u41'.zero, r41, s1C]
        exact BitVec.zero_add _)
    (by rw [r45 a1 (by decide), u43.upd_eq (by decide), u42'.zero, K42 s4 (by decide), r41, s4C]
        exact BitVec.zero_add _)
    (by rw [regs45]; simp +decide [upd]; try rfl) (by decide)
    (by rw [KC45 sp (by decide) (by decide) (by decide), spC]) hGa (by omega) (by omega)
    (by rw [S40]; have := E.hS; omega) (by rw [S40]; omega) (by omega)
    (by rw [eT]; exact (E.sSF.sub (c := 0x40) (l := 32) (by omega)).subR (c := 0) (l := 0x130) (by omega)
          |> fun h => by rwa [add_ofNat_zero] at h)
    (by rw [eT]; have h := (E.sSF.sub (c := 0) (l := 64) (by omega)).subR (c := 0) (l := 0x130) (by omega)
        rwa [add_ofNat_zero, add_ofNat_zero] at h)
    (by rw [eT]; have h := E.sKF.subR (c := 0) (l := 0x130) (by omega); rwa [add_ofNat_zero] at h)
    (E.sKS.subR (c := 0x40) (l := 32) (by omega))
  rw [eT, mem45] at fr46
  rw [mem45] at w46
  let MZ := n46.mem
  have fZ : ∀ x, Sep R 0x130 x 1 → Sep (S + 0x40) 32 x 1 → MZ x = ML x := fr46
  have MZR : ∀ x, Sep R 0x190 x 1 → Sep S 0x68 x 1 → MZ x = M0 x := fun x hx hy => by
    rw [fZ x (by have h := hx.sub (c := 0) (l := 0x130) (by omega); rwa [add_ofNat_zero] at h)
      (hy.sub (c := 0x40) (l := 32) (by omega)), MLR x hx hy]
  -- The final hash value is FIPS 180-4's.
  have hloN : lo.toNat = msg.length / 64 := by
    show (BitVec.ofNat 32 (msg.length / 64)).toNat = _; rw [BitVec.toNat_ofNat]; omega
  have bL : memBytes ML S 64 = lastPre ++ Sha256.be64 (8 * msg.length) := by
    have e1 : memBytes ML S 56 = memBytes MC S 56 := by
      apply memBytes_congr; intro i hi
      show memStore32 (memStore32 MC _ _) _ _ _ = _
      rw [memStore32_get_sep (sep_offsets S (Or.inr (by omega)) (by omega) (by omega)),
        memStore32_get_sep (sep_offsets S (Or.inr (by omega)) (by omega) (by omega))]
    have e2 : memBytes ML (S + BitVec.ofNat 32 56) 8 = Sha256.be64 (8 * msg.length) := by
      rw [show 8 * msg.length = 8 * (64 * lo.toNat + pos) by rw [hloN]; omega]
      exact len_bytes MC S lo pos hpos (by rw [hloN]; omega)
    rw [show (64 : Nat) = 56 + 8 from rfl, memBytes_split, e1, e2, bC]
  have wL : wordsAt ML (S + 0x40) 8 = wordsAt MC (S + 0x40) 8 := by
    apply wordsAt_congr; intro i hi
    apply memLoad32_congr; intro j hj
    rw [show S + (0x40 : Word) = S + BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc, add_ofNat_assoc]
    show memStore32 (memStore32 MC _ _) _ _ _ = _
    rw [memStore32_get_sep (sep_offsets S (Or.inl (by omega)) (by omega) (by omega)),
      memStore32_get_sep (sep_offsets S (Or.inl (by omega)) (by omega) (by omega))]
  have padb : Sha256.blocks ((padTail msg).length / 64) (padTail msg) = B1 ++ [lastPre ++ Sha256.be64 (8 * msg.length)] := by
    by_cases hsh : pos < 56
    · rw [padTail_short msg hsh]
      show [padTail msg] = (if pos < 56 then [] else _) ++ [(if pos < 56 then _ else _) ++ _]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hsh), ite_eq_left_of_eq_true _ _ (eq_true hsh), List.nil_append]
      unfold padTail padZeros
      rw [show (119 - msg.length % 64) % 64 = 55 - pos by omega]
    · rw [padTail_long msg (by omega)]
      show _ = (if pos < 56 then [] else _) ++ [(if pos < 56 then _ else _) ++ _]
      rw [ite_eq_right_of_eq_false _ _ (eq_false hsh), ite_eq_right_of_eq_false _ _ (eq_false hsh)]
      rfl
  have hX : wordsAt MZ (S + 0x40) 8 = (fullBlocks msg ++ Sha256.blocks ((padTail msg).length / 64) (padTail msg)).foldl
      Sha256.compress Sha256.h0 := by
    rw [w46, wL, wC, bL, padb]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have cMZ := codeX MZ MZR
  have u46 : St MZ U n46 0xD6 (reg n46) := ⟨by rw [pc46], rfl, fun _ => rfl⟩
  have k46 : ∀ r, r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 →
      r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
      r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → reg n46 r = reg n45 r := K46
  have r46 : ∀ r, r = s0 ∨ r = s1 ∨ r = s2 ∨ r = sp → reg n46 r = reg nC r := by
    intro r h
    rcases h with rfl | rfl | rfl | rfl <;>
      rw [k46 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        KC45 _ (by decide) (by decide) (by decide)]
  have cFZ := cMZ _ _ E.cF (by decide) (by decide)
  obtain ⟨n47, d47, u47⟩ := u46.aluImm cFZ sf_at_d6 (off' := 0xD8) (by decide)
  have K47 := u47.upd_ne u46.zero
  have u47' : St MZ U n47 0xD8 (reg n47) := u47.self
  have a0_47 : reg n47 a0 = BitVec.ofNat 32 8 := by rw [u47.upd_eq (by decide), u46.zero]; rfl
  obtain ⟨n48, d48, u48⟩ := u47'.notTaken cFZ 0xDA sf_at_d8 (by decide) (by
    simp only [branchTaken]; rw [a0_47, u47'.zero]; decide)
  let B := G + BitVec.ofNat 32 0x20
  have hBn : B.toNat = G.toNat + 0x20 := hGc _ (by omega)
  have hBc : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 → Sep B 32 b l :=
    fun b l hb hbl => data_code (by rw [hBn]; omega) hb hbl
  have cB : ∀ (Mx : Word → BitVec 8), (∀ x, Sep B 32 x 1 → Mx x = MZ x) → ∀ (b : Word) (code : List Nat),
      CodeIn M0 b code → 0x40000000 ≤ b.toNat → b.toNat + code.length ≤ 2 ^ 32 → CodeIn Mx b code :=
    fun Mx h b code hc hb hbl i hi => by
      rw [h _ ((hBc b code.length hb hbl).subR (c := i) (l := 1) (by omega))]; exact cMZ b code hc hb hbl i hi
  have hSB : Sep (S + 0x40) 32 B 32 := by
    show Sep (S + BitVec.ofNat 32 0x40) 32 (G + BitVec.ofNat 32 0x20) 32
    rw [Gc]; exact (E.sSF.sub (c := 0x40) (l := 32) (by omega)).subR (c := 0x130 + 0x20) (l := 32) (by omega)
  obtain ⟨n49, Mf, c49, u49, hagF, hbF, K49⟩ := fin_loop (M0 := MZ) (Sst := S + 0x40) (B := B)
    (fun Mx h => cB Mx h _ _ E.cF (by decide) (by decide)) (fun Mx h => cB Mx h _ _ E.cBe (by decide) (by decide))
    (by rw [hBn]; omega) hSB (by rw [S40]; have := E.hS; omega) 8 0 n48 MZ rfl (by decide) u48.self
    (fun _ _ => rfl) rfl (by rw [u48.regs, a0_47])
    (by rw [u48.regs, K47 s1 (by decide), r46 s1 (by decide), s1C, add_ofNat_zero])
    (by rw [u48.regs, K47 s0 (by decide), r46 s0 (by decide), s0C, add_ofNat_zero])
  rw [hX] at hbF
  -- Copy the digest out through the second array, as the code does.
  have cBf := cB Mf hagF
  have cFf := cBf _ _ E.cF (by decide) (by decide)
  have k49 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ t0 → r ≠ s0 → r ≠ s1 → reg n49 r = reg n48 r := K49
  have r49 : ∀ r, r = s2 ∨ r = sp → reg n49 r = reg nC r := by
    intro r h
    rcases h with rfl | rfl <;>
      rw [k49 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        u48.regs, K47 _ (by decide), r46 _ (by decide)]
  have sp49 : reg n49 sp = G := by rw [r49 sp (by decide), spC]
  obtain ⟨n50, d50, u50⟩ := u49.alu cFf sf_at_ea (off' := 0xEC) (by decide)
  have K50 := u50.upd_ne u49.zero
  have u50' : St Mf U n50 0xEC (reg n50) := u50.self
  obtain ⟨n51, d51, u51⟩ := u50'.aluImm cFf sf_at_ec (off' := 0xEE) (by decide)
  have K51 := u51.upd_ne u50'.zero
  have u51' : St Mf U n51 0xEE (reg n51) := u51.self
  obtain ⟨n52, d52, u52⟩ := u51'.aluImm cFf sf_at_ee (off' := 0xF2) (by decide)
  have K52 := u52.upd_ne u51'.zero
  have u52' : St Mf U n52 0xF2 (reg n52) := u52.self
  obtain ⟨n53, d53, u53⟩ := u52'.auipc cFf sf_at_f2 (off' := 0xF6) (by decide)
  obtain ⟨n54, d54, pc54, mem54, regs54⟩ := u53.call cFf sf_at_f6
  have r54 : ∀ r, r ≠ ra → reg n54 r = reg n52 r := fun r h => by
    rw [regs54]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u52'.zero.symm
    · simp [upd, h0, h]
  have sp54 : reg n54 sp = G := by
    rw [r54 sp (by decide), K52 sp (by decide), K51 sp (by decide), K50 sp (by decide), sp49]
  have eF : G + 0xFFFFFFF0 = R + BitVec.ofNat 32 0x120 := by rw [hGR, BitVec.add_assoc]; rfl
  have hFn : (G + 0xFFFFFFF0).toNat = R.toNat + 0x120 := by rw [eF, hRc _ (by omega)]
  have sGF : Sep G 32 (G + 0xFFFFFFF0) 16 := by
    rw [eF, hGR]; exact sep_offsets R (Or.inr (by omega)) (by omega) (by omega)
  have sBF : Sep B 32 (G + 0xFFFFFFF0) 16 := by
    rw [eF]; show Sep (G + BitVec.ofNat 32 0x20) 32 _ 16; rw [Gc]
    exact sep_offsets R (Or.inr (by omega)) (by omega) (by omega)
  have sGB : Sep G 32 B 32 := by
    have h := sep_offsets G (c := 0) (n := 32) (d := 0x20) (k := 32) (Or.inl (by omega)) (by omega) (by omega)
    rwa [add_ofNat_zero] at h
  have hGw : G.toNat + 0x60 ≤ 0x40000000 := by omega
  obtain ⟨n55, c55, pc55, sp55, a055, mem55, K55⟩ := memcpy_correct n54 (BitVec.ofNat 32 memcpyStubAddress)
    (U + BitVec.ofNat 32 0xFA) G B 32
    (fun i hi => by show n54.mem _ = _; rw [mem54]; exact cBf _ _ E.cMS (by decide) (by decide) i hi) (by decide)
    (by rw [pc54, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]; decide)
    (by rw [r54 a0 (by decide), K52 a0 (by decide), K51 a0 (by decide), u50.upd_eq (by decide), u49.zero, sp49]
        exact BitVec.zero_add _)
    (by rw [r54 a1 (by decide), K52 a1 (by decide), u51.upd_eq (by decide), K50 sp (by decide), sp49]; rfl)
    (by rw [r54 a2 (by decide), u52.upd_eq (by decide), u51'.zero]; rfl)
    (by rw [regs54]; simp +decide [upd]; try rfl) (by decide)
    (by
      rw [mem54, sp54]
      exact { code := cBf _ _ E.cMB (by decide) (by decide)
              hDC := data_code (by omega) (by decide) (by decide)
              hFC := data_code (by rw [hFn, hRn]; omega) (by decide) (by decide)
              hdF := sGF
              hsF := sBF
              hsep := sGB
              hF := by rw [hFn, hRn]; have := E.hsp; omega
              hFw := by rw [hFn, hRn]; omega
              hdw := by omega
              hsw := by rw [hBn]; omega })
  rw [mem54, sp54] at mem55
  let M5 := n55.mem
  have m5 : ∀ x, Sep (G + 0xFFFFFFF0) 16 x 1 → M5 x = copyBytes Mf G B 32 x := mem55
  have FR : ∀ x, Sep R 0x190 x 1 → Sep (G + 0xFFFFFFF0) 16 x 1 := fun x hx => by
    rw [eF]; exact Rx _ _ (by omega) x hx
  have M5R : ∀ x, Sep R 0x190 x 1 → Sep S 0x68 x 1 → M5 x = M0 x := fun x hx hy => by
    rw [m5 x (FR x hx), copyBytes_sep (by rw [hGR]; exact Rx _ _ (by omega) x hx) (Nat.le_refl 32),
      hagF x (by show Sep (G + BitVec.ofNat 32 0x20) 32 x 1; rw [Gc]; exact Rx _ _ (by omega) x hx), MZR x hx hy]
  have cB5 : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn M5 b code := codeX M5 M5R
  have cF5 := cB5 _ _ E.cF (by decide) (by decide)
  have u55 : St M5 U n55 0xFA (reg n55) := ⟨by rw [pc55], rfl, fun _ => rfl⟩
  have k55 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg n55 r = reg n54 r := K55
  have sp55' : reg n55 sp = G := by rw [sp55, sp54]
  obtain ⟨n56, d56, u56⟩ := u55.alu cF5 sf_at_fa (off' := 0xFC) (by decide)
  have K56 := u56.upd_ne u55.zero
  have u56' : St M5 U n56 0xFC (reg n56) := u56.self
  obtain ⟨n57, d57, u57⟩ := u56'.aluImm cF5 sf_at_fc (off' := 0x100) (by decide)
  have K57 := u57.upd_ne u56'.zero
  have u57' : St M5 U n57 0x100 (reg n57) := u57.self
  obtain ⟨n58, d58, u58⟩ := u57'.alu cF5 sf_at_100 (off' := 0x102) (by decide)
  have K58 := u58.upd_ne u57'.zero
  have u58' : St M5 U n58 0x102 (reg n58) := u58.self
  obtain ⟨n59, d59, u59⟩ := u58'.auipc cF5 sf_at_102 (off' := 0x106) (by decide)
  obtain ⟨n60, d60, pc60, mem60, regs60⟩ := u59.call cF5 sf_at_106
  have r60 : ∀ r, r ≠ ra → reg n60 r = reg n58 r := fun r h => by
    rw [regs60]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u58'.zero.symm
    · simp [upd, h0, h]
  have K4960 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 →
      r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) →
      r ≠ sp → reg n60 r = reg n49 r := fun r q1 q10 q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2 => by
    rw [r60 r q1, K58 r q10, K57 r q12, K56 r q11, k55 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2,
      r54 r q1, K52 r q12, K51 r q11, K50 r q10]
  have sp60 : reg n60 sp = G := by
    rw [r60 sp (by decide), K58 sp (by decide), K57 sp (by decide), K56 sp (by decide), sp55']
  have sOFr : Sep out 32 (G + 0xFFFFFFF0) 16 := by
    rw [eF]; exact E.sOF.subR (c := 0x120) (l := 16) (by omega)
  have sOG : Sep out 32 G 32 := by rw [hGR]; exact E.sOF.subR (c := 0x130) (l := 32) (by omega)
  obtain ⟨n61, c61, pc61, sp61, a061, mem61, K61⟩ := memcpy_correct n60 (BitVec.ofNat 32 memcpyStubAddress)
    (U + BitVec.ofNat 32 0x10A) out G 32
    (fun i hi => by show n60.mem _ = _; rw [mem60]; exact cB5 _ _ E.cMS (by decide) (by decide) i hi) (by decide)
    (by rw [pc60, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]; decide)
    (by rw [r60 a0 (by decide), u58.upd_eq (by decide), u57'.zero, K57 s2 (by decide), K56 s2 (by decide),
          k55 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r54 s2 (by decide),
          K52 s2 (by decide), K51 s2 (by decide), K50 s2 (by decide), r49 s2 (by decide), s2C]
        exact BitVec.zero_add _)
    (by rw [r60 a1 (by decide), K58 a1 (by decide), K57 a1 (by decide), u56.upd_eq (by decide), u55.zero, sp55']
        exact BitVec.zero_add _)
    (by rw [r60 a2 (by decide), K58 a2 (by decide), u57.upd_eq (by decide), u56'.zero]; rfl)
    (by rw [regs60]; simp +decide [upd]; try rfl) (by decide)
    (by
      rw [mem60, sp60]
      exact { code := cB5 _ _ E.cMB (by decide) (by decide)
              hDC := data_code (by omega) (by decide) (by decide)
              hFC := data_code (by rw [hFn, hRn]; omega) (by decide) (by decide)
              hdF := sOFr
              hsF := sGF
              hsep := sOG
              hF := by rw [hFn, hRn]; have := E.hsp; omega
              hFw := by rw [hFn, hRn]; omega
              hdw := by omega
              hsw := by omega })
  rw [mem60, sp60] at mem61
  have k61' : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg n61 r = reg n60 r := K61
  let M6 := n61.mem
  have m6 : ∀ x, Sep (G + 0xFFFFFFF0) 16 x 1 → M6 x = copyBytes M5 out G 32 x := mem61
  have M6R : ∀ x, Sep R 0x190 x 1 → Sep S 0x68 x 1 → Sep out 32 x 1 → M6 x = M0 x := fun x hx hy hz => by
    rw [m6 x (FR x hx), copyBytes_sep hz (Nat.le_refl 32), M5R x hx hy]
  have cB6 : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn M6 b code := fun b code hc hb hbl i hi => by
    rw [M6R _ ((data_code (by rw [hRn]; omega) hb hbl).subR (c := i) (l := 1) (by omega))
      ((data_code (by omega) hb hbl).subR (c := i) (l := 1) (by omega))
      ((data_code hOw hb hbl).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  -- The frame's saved words survive to the restore.
  have M6s : ∀ k, 0x40 ≤ k → k < 0x60 → M6 (G + BitVec.ofNat 32 k) = M1 (G + BitVec.ofNat 32 k) := by
    intro k h1 h2
    have hR : Sep R 0x130 (G + BitVec.ofNat 32 k) 1 := by
      rw [Gc]; have h := sep_offsets R (c := 0) (n := 0x130) (d := 0x130 + k) (k := 1) (Or.inl (by omega))
        (by omega) (by omega)
      rwa [add_ofNat_zero] at h
    have hS : Sep S 0x68 (G + BitVec.ofNat 32 k) 1 := by rw [Gc]; exact E.sSF.subR (c := 0x130 + k) (l := 1) (by omega)
    rw [m6 _ (by rw [eF, Gc]; exact sep_offsets R (Or.inl (by omega)) (by omega) (by omega)),
      copyBytes_sep (by rw [Gc]; exact E.sOF.subR (c := 0x130 + k) (l := 1) (by omega)) (Nat.le_refl 32),
      m5 _ (by rw [eF, Gc]; exact sep_offsets R (Or.inl (by omega)) (by omega) (by omega)),
      copyBytes_sep (by
        have h := sep_offsets G (c := 0) (n := 32) (d := k) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at h) (Nat.le_refl 32),
      hagF _ (by
        show Sep (G + BitVec.ofNat 32 0x20) 32 _ 1
        exact sep_offsets G (Or.inl (by omega)) (by omega) (by omega)),
      fZ _ hR (hS.sub (c := 0x40) (l := 32) (by omega))]
    show memStore32 (memStore32 MC _ _) _ _ _ = _
    rw [memStore32_get_sep (hS.sub (c := 0x3C) (l := 4) (by omega)),
      memStore32_get_sep (hS.sub (c := 0x38) (l := 4) (by omega)), MCs k h1 h2]
    show fillBytes MP _ _ _ _ = _
    rw [fillBytes_sep (hS.sub (c := pos + 1) (l := 63 - pos) (by omega)) (Nat.le_refl _)]
    show memStore8 M2 _ _ _ = _
    rw [memStore8_ne (fun e => hS pos (by omega) 0 (by decide) (by rw [add_ofNat_zero, e])), M2s k h1 h2]
  have ld6 : ∀ c, 0x40 ≤ c → c + 4 ≤ 0x60 → memLoad32 M6 (G + BitVec.ofNat 32 c) = memLoad32 M1 (G + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact M6s _ (by omega) (by omega)
  obtain ⟨v40, vra, vs0, vs1, vs2, vs3, vs4, vs5⟩ := finSaved_slots M0 G g1 (reg m s6)
  have cF6 := cB6 _ _ E.cF (by decide) (by decide)
  have u61 : St M6 U n61 0x10A (reg n61) := ⟨by rw [pc61], rfl, fun _ => rfl⟩
  have sp61' : reg n61 sp = G := by rw [sp61, sp60]
  obtain ⟨n62, c62, u62⟩ := u61.callRestore cF6 sf_at_10a sf_at_10e
    (b := BitVec.ofNat 32 shaFinalizeRestoreAddress) (by decide) (by decide) (by decide)
    (cB6 _ _ E.cRest (by decide) (by decide)) finRestore_shape (by decide) (fun p hp => by
      rw [sp61']
      simp only [finSavePs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide, aligned_add hGa4 (k := 0x5C) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hGa4 (k := 0x58) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hGa4 (k := 0x54) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hGa4 (k := 0x50) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hGa4 (k := 0x4C) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hGa4 (k := 0x48) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hGa4 (k := 0x44) (by decide)⟩)
  rw [sp61'] at u62
  obtain ⟨wra, ws0, ws1, ws2, ws3, ws4, ws5⟩ := finR_saved M6 G (upd (reg n61) t0 (U + BitVec.ofNat 32 (0x10A + 8)))
  have zr : upd (reg n61) t0 (U + BitVec.ofNat 32 (0x10A + 8)) 0 = 0 := by simp [upd]
  have rsp : restoreRegs M6 G (upd (reg n61) t0 (U + BitVec.ofNat 32 (0x10A + 8))) finSavePs sp = G := by
    rw [finR_other _ _ _ zr sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp +decide only [upd]; exact sp61'
  have u62' : St M6 U n62 0x112 (reg n62) := u62.self
  have K62 : ∀ r, r ≠ ra → r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → r ≠ s4 → r ≠ s5 → r ≠ t0 → reg n62 r = reg n61 r :=
    fun r q1 q8 q9 q18 q19 q20 q21 q5 => by
      rw [u62.regs, finR_other _ _ _ zr r q1 q8 q9 q18 q19 q20 q21]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact u61.zero.symm
      · simp [upd, h0, q5]
  obtain ⟨n63, d63, u63⟩ := u62'.lw cF6 sf_at_112 (off' := 0x114) (by decide)
    (by rw [u62.regs, rsp]; exact aligned_add hGa4 (k := 0x40) (by decide))
  rw [u62.regs, rsp, show (0x40 : Word) = BitVec.ofNat 32 0x40 from rfl, ld6 _ (by omega) (by omega), v40] at u63
  have K63 := u63.upd_ne u62'.zero
  have u63' : St M6 U n63 0x114 (reg n63) := u63.self
  obtain ⟨n64, d64, u64⟩ := u63'.aluImm cF6 sf_at_114 (off' := 0x116) (by decide)
  have K64 := u64.upd_ne u63'.zero
  have u64' : St M6 U n64 0x116 (reg n64) := u64.self
  obtain ⟨n65, d65, pc65, mem65, regs65⟩ := u64'.jalr cF6 sf_at_116
  -- Restored registers.
  have lds : ∀ (r : Fin 32) (c : Nat), r ≠ sp → 0x44 ≤ c → c + 4 ≤ 0x60 → memLoad32 M1 (G + BitVec.ofNat 32 c) = g1 r →
      memLoad32 M6 (G + BitVec.ofNat 32 c) = reg m r := fun r c q h1 h2 h =>
    (ld6 c (by omega) h2).trans (h.trans (f1 r q))
  have rRa : reg n64 ra = retAddr := by
    rw [K64 ra (by decide), K63 ra (by decide), u62.regs, wra]
    exact (lds ra 0x5C (by decide) (by omega) (by omega) vra).trans hra
  have rSp : reg n64 sp = sp0 := by
    rw [u64.upd_eq (by decide), K63 sp (by decide), u62.regs, rsp]
    show G + 0x60 = sp0
    show sp0 + 0xFFFFFFA0 + 0x60 = sp0
    rw [BitVec.add_assoc]; exact BitVec.add_zero sp0
  -- Everything from `m15` back to the entry, for the registers no callee clobbers.
  have chain : ∀ r, r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 →
      r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) →
      r ≠ (31 : Fin 32) → r ≠ ra → r ≠ sp → r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → r ≠ s4 → r ≠ s5 → r ≠ s6 →
      reg n64 r = reg m r := fun r q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q1 q2 q8 q9 q18 q19
        q20 q21 q22 => by
    rw [K64 r q2, K63 r q22, K62 r q1 q8 q9 q18 q19 q20 q21 q5,
      k61' r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2,
      K4960 r q1 q10 q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2,
      k49 r q10 q11 q12 q13 q14 q5 q8 q9, u48.regs, K47 r q10,
      k46 r q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, KC45 r q1 q10 q11,
      KC16 r q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31,
      g16 r q10 q11 q12 q13 q14 q15 q16 q17 q5 q19 q21 q22,
      Kp r q2 q1 q5 q6 q7 q8 q9 q18 q20 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30]
  have S1 : Steps m m15 := .cons e1 (k2.trans (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (c9.trans
    (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.cons e14 c15)))))))))))))
  have S2 : Steps m15 m26 := c16.trans (.cons e17 (.cons e18 (.cons e19 (.cons e20 (.cons e21 (.cons e22 (.cons e23
    (.cons e24 (c25.trans (.single e26))))))))))
  have S3 : Steps m26 n46 := cC.trans (.cons d40 (.cons d41 (.cons d42 (.cons d43 (.cons d44 (.cons d45 c46))))))
  have S4 : Steps n46 n49 := .cons d47 (.cons d48 c49)
  have S5 : Steps n49 n61 := .cons d50 (.cons d51 (.cons d52 (.cons d53 (.cons d54 (c55.trans (.cons d56 (.cons d57
    (.cons d58 (.cons d59 (.cons d60 c61))))))))))
  have S6 : Steps n61 n65 := c62.trans (.cons d63 (.cons d64 (.single d65)))
  have outB : memBytes M6 out 32 = memBytes Mf B 32 := by
    unfold memBytes
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    show (M6 (out + BitVec.ofNat 32 i)).toNat = (Mf (B + BitVec.ofNat 32 i)).toNat
    rw [m6 _ (sOFr.sub (c := i) (l := 1) (by omega)).symm, copyBytes_in hi (by omega),
      m5 _ (sGF.sub (c := i) (l := 1) (by omega)).symm, copyBytes_in hi (by omega)]
  refine ⟨n65, S1.trans (S2.trans (S3.trans (S4.trans (S5.trans S6)))), ?_, ?_,
    fun r q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => ?_, ?_, fun x hx hy hz => ?_⟩
  · rw [pc65, rRa, add_lit_zero, hret]
  · rw [regs65, rSp]
  · rw [regs65]
    by_cases q1 : r = ra
    · subst q1; rw [rRa, hra]
    by_cases q2 : r = sp
    · subst q2; rw [rSp, hsp]
    by_cases q22 : r = s6
    · subst q22; rw [K64 s6 (by decide), u63.upd_eq (by decide)]
    have sv : ∀ (r : Fin 32) (c : Nat), r ≠ sp → r ≠ s6 → r ≠ t0 → 0x44 ≤ c → c + 4 ≤ 0x60 →
        restoreRegs M6 G (upd (reg n61) t0 (U + BitVec.ofNat 32 (0x10A + 8))) finSavePs r = memLoad32 M6 (G + BitVec.ofNat 32 c) →
        memLoad32 M1 (G + BitVec.ofNat 32 c) = g1 r → reg n64 r = reg m r := fun r c h2 h22 h5 h1 h3 hv hm => by
      rw [K64 r h2, K63 r h22, u62.regs, hv]; exact lds r c h2 h1 h3 hm
    by_cases q8 : r = s0
    · subst q8; exact sv s0 0x58 (by decide) (by decide) (by decide) (by omega) (by omega) ws0 vs0
    by_cases q9 : r = s1
    · subst q9; exact sv s1 0x54 (by decide) (by decide) (by decide) (by omega) (by omega) ws1 vs1
    by_cases q18 : r = s2
    · subst q18; exact sv s2 0x50 (by decide) (by decide) (by decide) (by omega) (by omega) ws2 vs2
    by_cases q19 : r = s3
    · subst q19; exact sv s3 0x4C (by decide) (by decide) (by decide) (by omega) (by omega) ws3 vs3
    by_cases q20 : r = s4
    · subst q20; exact sv s4 0x48 (by decide) (by decide) (by decide) (by omega) (by omega) ws4 vs4
    by_cases q21 : r = s5
    · subst q21; exact sv s5 0x44 (by decide) (by decide) (by decide) (by omega) (by omega) ws5 vs5
    exact chain r q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q1 q2 q8 q9 q18 q19 q20 q21 q22
  · rw [mem65, outB, hbF, sha256_stream]
  · rw [mem65]; exact M6R x hx hy hz

end C3.RV32
