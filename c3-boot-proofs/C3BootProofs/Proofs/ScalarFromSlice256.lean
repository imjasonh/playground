import C3BootProofs.Proofs.ScalarFromSlice384
import C3BootProofs.Proofs.Bytes2Scalar256

/-!
# `ScalarValue<NistP256>::from_slice`, as compiled

The P-256 instance of `ScalarFromSlice384.lean`, with 32 bytes, 8 limbs,
and P-256's order.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem bg_at_0 : fetchRel scalarFromSlice256Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFA0, 2) := by decide
theorem bg_at_2 : fetchRel scalarFromSlice256Code 0x2 = some (.store .sw sp ra 0x5C, 2) := by decide
theorem bg_at_4 : fetchRel scalarFromSlice256Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x58, 2) := by decide
theorem bg_at_6 : fetchRel scalarFromSlice256Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x54, 2) := by decide
theorem bg_at_8 : fetchRel scalarFromSlice256Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x50, 2) := by decide
theorem bg_at_a : fetchRel scalarFromSlice256Code 0xA = some (.store .sw sp (19 : Fin 32) 0x4C, 2) := by decide
theorem bg_at_c : fetchRel scalarFromSlice256Code 0xC = some (.store .sw sp (20 : Fin 32) 0x48, 2) := by decide
theorem bg_at_e : fetchRel scalarFromSlice256Code 0xE = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem bg_at_10 : fetchRel scalarFromSlice256Code 0x10 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem bg_at_12 : fetchRel scalarFromSlice256Code 0x12 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem bg_at_16 : fetchRel scalarFromSlice256Code 0x16 = some (.branch .beq a2 x0 0x12, 2) := by decide
theorem bg_at_18 : fetchRel scalarFromSlice256Code 0x18 = some (.load .lbu a3 a1 0x0, 4) := by decide
theorem bg_at_1c : fetchRel scalarFromSlice256Code 0x1C = some (.aluImm .add a1 a1 0x1, 2) := by decide
theorem bg_at_1e : fetchRel scalarFromSlice256Code 0x1E = some (.store .sb a0 a3 0x0, 4) := by decide
theorem bg_at_22 : fetchRel scalarFromSlice256Code 0x22 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem bg_at_24 : fetchRel scalarFromSlice256Code 0x24 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem bg_at_26 : fetchRel scalarFromSlice256Code 0x26 = some (.branch .bne a2 x0 0xFFFFFFF2, 2) := by decide
theorem bg_at_28 : fetchRel scalarFromSlice256Code 0x28 = some (.aluImm .add a0 sp 0x28, 2) := by decide
theorem bg_at_2a : fetchRel scalarFromSlice256Code 0x2A = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem bg_at_2c : fetchRel scalarFromSlice256Code 0x2C = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem bg_at_30 : fetchRel scalarFromSlice256Code 0x30 = some (.aluImm .add a3 x0 0x100, 4) := by decide
theorem bg_at_34 : fetchRel scalarFromSlice256Code 0x34 = some (.aluImm .add (20 : Fin 32) sp 0x28, 4) := by decide
theorem bg_at_38 : fetchRel scalarFromSlice256Code 0x38 = some (.auipc ra 0x0, 4) := by decide
theorem bg_at_3c : fetchRel scalarFromSlice256Code 0x3C = some (.jalr ra ra 0x10C, 4) := by decide
theorem bg_at_40 : fetchRel scalarFromSlice256Code 0x40 = some (.aluImm .add (19 : Fin 32) x0 0x0, 2) := by decide
theorem bg_at_42 : fetchRel scalarFromSlice256Code 0x42 = some (.lui (9 : Fin 32) 0x3FCC4000, 4) := by decide
theorem bg_at_46 : fetchRel scalarFromSlice256Code 0x46 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xD8, 4) := by decide
theorem bg_at_4a : fetchRel scalarFromSlice256Code 0x4A = some (.aluImm .add (8 : Fin 32) x0 0x8, 2) := by decide
theorem bg_at_4c : fetchRel scalarFromSlice256Code 0x4C = some (.branch .beq (8 : Fin 32) x0 0x1C, 2) := by decide
theorem bg_at_4e : fetchRel scalarFromSlice256Code 0x4E = some (.load .lw a0 (20 : Fin 32) 0x0, 4) := by decide
theorem bg_at_52 : fetchRel scalarFromSlice256Code 0x52 = some (.load .lw a1 (9 : Fin 32) 0x0, 2) := by decide
theorem bg_at_54 : fetchRel scalarFromSlice256Code 0x54 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem bg_at_56 : fetchRel scalarFromSlice256Code 0x56 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem bg_at_5a : fetchRel scalarFromSlice256Code 0x5A = some (.jalr ra ra 0x5DA, 4) := by decide
theorem bg_at_5e : fetchRel scalarFromSlice256Code 0x5E = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem bg_at_60 : fetchRel scalarFromSlice256Code 0x60 = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4, 2) := by decide
theorem bg_at_62 : fetchRel scalarFromSlice256Code 0x62 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem bg_at_64 : fetchRel scalarFromSlice256Code 0x64 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem bg_at_66 : fetchRel scalarFromSlice256Code 0x66 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE8, 2) := by decide
theorem bg_at_68 : fetchRel scalarFromSlice256Code 0x68 = some (.lui a0 0x3FCC4000, 4) := by decide
theorem bg_at_6c : fetchRel scalarFromSlice256Code 0x6C = some (.aluImm .add a0 a0 0xF8, 4) := by decide
theorem bg_at_70 : fetchRel scalarFromSlice256Code 0x70 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem bg_at_72 : fetchRel scalarFromSlice256Code 0x72 = some (.auipc ra 0x0, 4) := by decide
theorem bg_at_76 : fetchRel scalarFromSlice256Code 0x76 = some (.jalr ra ra 0xFFFFFF0A, 4) := by decide
theorem bg_at_7a : fetchRel scalarFromSlice256Code 0x7A = some (.aluImm .add a1 sp 0x48, 2) := by decide
theorem bg_at_7c : fetchRel scalarFromSlice256Code 0x7C = some (.aluImm .and (8 : Fin 32) a0 0xFF, 4) := by decide
theorem bg_at_80 : fetchRel scalarFromSlice256Code 0x80 = some (.alu .add a0 x0 a1, 2) := by decide
theorem bg_at_82 : fetchRel scalarFromSlice256Code 0x82 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem bg_at_84 : fetchRel scalarFromSlice256Code 0x84 = some (.auipc ra 0x0, 4) := by decide
theorem bg_at_88 : fetchRel scalarFromSlice256Code 0x88 = some (.jalr ra ra 0xFFFFFEF8, 4) := by decide
theorem bg_at_8c : fetchRel scalarFromSlice256Code 0x8C = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem bg_at_90 : fetchRel scalarFromSlice256Code 0x90 = some (.aluImm .xor a0 a0 0xFFFFFFFF, 4) := by decide
theorem bg_at_94 : fetchRel scalarFromSlice256Code 0x94 = some (.alu .and a0 (19 : Fin 32) a0, 4) := by decide
theorem bg_at_98 : fetchRel scalarFromSlice256Code 0x98 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem bg_at_9a : fetchRel scalarFromSlice256Code 0x9A = some (.alu .or a0 a0 (8 : Fin 32), 2) := by decide
theorem bg_at_9c : fetchRel scalarFromSlice256Code 0x9C = some (.auipc ra 0xC000, 4) := by decide
theorem bg_at_a0 : fetchRel scalarFromSlice256Code 0xA0 = some (.jalr ra ra 0x7C8, 4) := by decide
theorem bg_at_a4 : fetchRel scalarFromSlice256Code 0xA4 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem bg_at_a6 : fetchRel scalarFromSlice256Code 0xA6 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem bg_at_aa : fetchRel scalarFromSlice256Code 0xAA = some (.branch .bne a0 a1 0x18, 4) := by decide
theorem bg_at_ae : fetchRel scalarFromSlice256Code 0xAE = some (.aluImm .add a0 (18 : Fin 32) 0x4, 4) := by decide
theorem bg_at_b2 : fetchRel scalarFromSlice256Code 0xB2 = some (.aluImm .add a1 sp 0x28, 2) := by decide
theorem bg_at_b4 : fetchRel scalarFromSlice256Code 0xB4 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem bg_at_b8 : fetchRel scalarFromSlice256Code 0xB8 = some (.auipc ra 0x14000, 4) := by decide
theorem bg_at_bc : fetchRel scalarFromSlice256Code 0xBC = some (.jalr ra ra 0xFFFFF8B6, 4) := by decide
theorem bg_at_c0 : fetchRel scalarFromSlice256Code 0xC0 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem bg_at_c2 : fetchRel scalarFromSlice256Code 0xC2 = some (.store .sw (18 : Fin 32) a1 0x0, 4) := by decide
theorem bg_at_c6 : fetchRel scalarFromSlice256Code 0xC6 = some (.load .lw ra sp 0x5C, 2) := by decide
theorem bg_at_c8 : fetchRel scalarFromSlice256Code 0xC8 = some (.load .lw (8 : Fin 32) sp 0x58, 2) := by decide
theorem bg_at_ca : fetchRel scalarFromSlice256Code 0xCA = some (.load .lw (9 : Fin 32) sp 0x54, 2) := by decide
theorem bg_at_cc : fetchRel scalarFromSlice256Code 0xCC = some (.load .lw (18 : Fin 32) sp 0x50, 2) := by decide
theorem bg_at_ce : fetchRel scalarFromSlice256Code 0xCE = some (.load .lw (19 : Fin 32) sp 0x4C, 2) := by decide
theorem bg_at_d0 : fetchRel scalarFromSlice256Code 0xD0 = some (.load .lw (20 : Fin 32) sp 0x48, 2) := by decide
theorem bg_at_d2 : fetchRel scalarFromSlice256Code 0xD2 = some (.aluImm .add sp sp 0x60, 2) := by decide
theorem bg_at_d4 : fetchRel scalarFromSlice256Code 0xD4 = some (.jalr x0 ra 0x0, 2) := by decide
end

abbrev BV : Word := BitVec.ofNat 32 scalarFromSlice256Address

/-- One round of the comparison, from 0x4E to the branch at 0x66: compare
the end of the tail. -/
def bgCmpTail : List BInstr :=
  [.alu .add (19 : Fin 32) x0 a1, .aluImm .add (20 : Fin 32) (20 : Fin 32) 4, .aluImm .add (9 : Fin 32) (9 : Fin 32) 4,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem bgCmpTail_end : blockEnd scalarFromSlice256Code 0x5E bgCmpTail = some 0x66 := by decide
end

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 400 in
/-- **The comparison**, from round `i` to its end at 0x68: `s3` ends as the
borrow mask of `X - N` over the 8 limbs at `X` and `N`, with the bounds
that say which of the two is larger. `borrowing_sub` writes the word below
`sp`. -/
theorem bg_cmp_loop {P F X N : Word} {M0 : Word → BitVec 8} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hX : X.toNat % 4 = 0) (hN : N.toNat % 4 = 0)
    (sFX : Sep (F + 0xFFFFFFFC) 4 X 32) (sFN : Sep (F + 0xFFFFFFFC) 4 N 32)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (P + 0xFFFFF630) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P scalarFromSlice256Code.length) :
    ∀ m i, i + m + 1 = 8 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x4E (reg n) → CodeIn M P scalarFromSlice256Code → CodeIn M (P + 0xFFFFF630) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 N i ≤ accV M0 X i + 2 ^ (32 * i) * maskBit b →
      accV M0 X i + 2 ^ (32 * i) * maskBit b < accV M0 N i + 2 ^ (32 * i) →
      reg n sp = F → reg n (20 : Fin 32) = X + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = N + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = BitVec.ofNat 32 (8 - i) →
      reg n (19 : Fin 32) = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x68 (reg n') ∧ CodeIn M' P scalarFromSlice256Code ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → M' x = M0 x) ∧
        (reg n' (19 : Fin 32) = 0 ∨ reg n' (19 : Fin 32) = 0xFFFFFFFF) ∧
        accV M0 N 8 ≤ accV M0 X 8 + 2 ^ (32 * 8) * maskBit (reg n' (19 : Fin 32)) ∧
        accV M0 X 8 + 2 ^ (32 * 8) * maskBit (reg n' (19 : Fin 32)) < accV M0 N 8 + 2 ^ (32 * 8) ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) →
          q ≠ (8 : Fin 32) → q ≠ (19 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 8 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x4E (reg n) → CodeIn M P scalarFromSlice256Code → CodeIn M (P + 0xFFFFF630) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 N i ≤ accV M0 X i + 2 ^ (32 * i) * maskBit b →
      accV M0 X i + 2 ^ (32 * i) * maskBit b < accV M0 N i + 2 ^ (32 * i) →
      reg n sp = F → reg n (20 : Fin 32) = X + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = N + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = BitVec.ofNat 32 (8 - i) →
      reg n (19 : Fin 32) = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 8 then 0x4E else 0x68) (reg n') ∧
        CodeIn M' P scalarFromSlice256Code ∧ CodeIn M' (P + 0xFFFFF630) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → M' x = M0 x) ∧
        (reg n' (19 : Fin 32) = 0 ∨ reg n' (19 : Fin 32) = 0xFFFFFFFF) ∧
        accV M0 N (i + 1) ≤ accV M0 X (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' (19 : Fin 32)) ∧
        accV M0 X (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' (19 : Fin 32)) <
          accV M0 N (i + 1) + 2 ^ (32 * (i + 1)) ∧
        reg n' sp = F ∧ reg n' (20 : Fin 32) = X + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (9 : Fin 32) = N + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) →
          q ≠ (8 : Fin 32) → q ≠ (19 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm h1 h2 rsp r20 r9 r8 r19
    have hz := s.zero
    have eX : memLoad32 M (X + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (X + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hfr _ (sFX.subR (c := 4 * i + j) (l := 1) (by omega))
    have eN : memLoad32 M (N + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (N + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hfr _ (sFN.subR (c := 4 * i + j) (l := 1) (by omega))
    obtain ⟨n1, d1, u1⟩ := s.lw hc bg_at_4e (off' := 0x52) (by decide)
      (by rw [r20, add_lit_zero]; exact aligned_add hX (by omega))
    have e1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q h => by rw [u1.regs, updz hz h]
    have a01 : reg n1 a0 = memLoad32 M0 (X + BitVec.ofNat 32 (4 * i)) := by
      rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r20, add_lit_zero, eX]
    obtain ⟨n2, d2, u2⟩ := u1.self.lw hc bg_at_52 (off' := 0x54) (by decide)
      (by rw [e1 9 (by decide), r9, add_lit_zero]; exact aligned_add hN (by omega))
    have e2 : ∀ q, q ≠ a1 → reg n2 q = reg n1 q := fun q h => by rw [u2.regs, updz u1.self.zero h]
    have a12 : reg n2 a1 = memLoad32 M0 (N + BitVec.ofNat 32 (4 * i)) := by
      rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [e1 9 (by decide), r9, add_lit_zero, eN]
    obtain ⟨n3, d3, u3⟩ := u2.self.alu hc bg_at_54 (off' := 0x56) (by decide)
    have e3 : ∀ q, q ≠ a2 → reg n3 q = reg n2 q := fun q h => by rw [u3.regs, updz u2.self.zero h]
    have g3a0 : reg n3 a0 = memLoad32 M0 (X + BitVec.ofNat 32 (4 * i)) := by
      rw [e3 a0 (by decide), e2 a0 (by decide), a01]
    have g3a1 : reg n3 a1 = memLoad32 M0 (N + BitVec.ofNat 32 (4 * i)) := by rw [e3 a1 (by decide), a12]
    have g3a2 : reg n3 a2 = b := by
      rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u2.self.zero, e2 19 (by decide), e1 19 (by decide), r19]; exact zw b
    have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n3 q = reg n q := fun q q0 q1 q2 => by
      rw [e3 q q2, e2 q q1, e1 q q0]
    obtain ⟨n4, c4, u4, a04, a14, sp4, fr4, mem4⟩ := u3.self.bsubCall hc hb (even_at P hP 0xFFFFF630 (by decide))
      bg_at_56 bg_at_5a (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x56 + 8) (by decide))
      (by rw [k3 sp (by decide) (by decide) (by decide), rsp]) hF sFB
    rw [g3a0, g3a1, g3a2] at a04 a14
    have hc4 : CodeIn n4.mem P scalarFromSlice256Code := fun j hj => by
      rw [mem4 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    have hb4 : CodeIn n4.mem (P + 0xFFFFF630) borrowingSubCode := fun j hj => by
      rw [mem4 _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have k4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n4 q = reg n q :=
      fun q q0 q1 q2 q3 q4 qr => by rw [fr4 q q0 q1 q2 q3 q4 qr, k3 q q0 q1 q2]
    obtain ⟨n5, c5, u5⟩ := St.block bgCmpTail u4 hc4 bgCmpTail_end (by simp only [BlockOk, BInstr.ok, bgCmpTail, and_self])
    have R5 : ∀ q, reg n5 q = (runBlock bgCmpTail (n4.mem, reg n4)).2 q := u5.regs
    have u5' : St n4.mem P n5 0x66 (reg n5) := ⟨u5.pc, by rw [u5.mem]; rfl, fun _ => rfl⟩
    have v5 : reg n5 (19 : Fin 32) = bsubB (memLoad32 M0 (X + BitVec.ofNat 32 (4 * i)))
          (memLoad32 M0 (N + BitVec.ofNat 32 (4 * i)))
          (bsubD (memLoad32 M0 (X + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (N + BitVec.ofNat 32 (4 * i))) b) ∧
        reg n5 (20 : Fin 32) = X + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n5 (9 : Fin 32) = N + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n5 (8 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) := by
      simp +decide only [R5, runBlock, BInstr.run, bgCmpTail, upd_app, ↓reduceIte]
      rw [a14, k4 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        k4 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        k4 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r20, r9, r8, u4.zero]
      simp only [ev_add]
      rw [cnt8_dec i hi, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc, add_ofNat_assoc, Nat.mul_succ]
      exact ⟨zw _, rfl, rfl, rfl⟩
    obtain ⟨v519, v520, v59, v58⟩ := v5
    have K5 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) →
        q ≠ (8 : Fin 32) → q ≠ (19 : Fin 32) → reg n5 q = reg n q := fun q q0 q1 q2 q3 q4 qr q20 q9 q8 q19 => by
      rw [R5]; rw [runBlock_reg _ _ _ q u4.zero (by
        simp only [bgCmpTail, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [q20, q9, q8, q19])]
      exact k4 q q0 q1 q2 q3 q4 qr
    have sp5 : reg n5 sp = F := by
      rw [K5 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), rsp]
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (X + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (N + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hd := (bsubD (memLoad32 M0 (X + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (N + BitVec.ofNat 32 (4 * i))) b).isLt
    have st := cmp_step h1 h2 hd bv
    have fr5 : ∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → n4.mem x = M0 x := fun x hx => by rw [mem4 x hx, hfr x hx]
    have hb5 : branchTaken .bne (reg n5 (8 : Fin 32)) (reg n5 x0) = decide (i + 1 < 8) := by
      rw [v58, u5'.zero]; exact cnt8_ne i hi
    have val : accV M0 N (i + 1) ≤ accV M0 X (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n5 (19 : Fin 32)) ∧
        accV M0 X (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n5 (19 : Fin 32)) <
          accV M0 N (i + 1) + 2 ^ (32 * (i + 1)) := by
      rw [accV_succ1, accV_succ1, pow32_succ, v519]; exact st
    by_cases hl : i + 1 < 8
    · obtain ⟨n6, d6, u6⟩ := u5'.taken hc4 0x4E bg_at_66 (by decide) (by rw [hb5]; exact decide_eq_true hl)
      exact ⟨n6, n4.mem, .cons d1 (.cons d2 (.cons d3 (c4.trans (c5.trans (.single d6))))),
        by rw [ite_eq_left hl]; exact u6.self, hc4, hb4, fr5, by rw [u6.regs, v519]; exact bm,
        by rw [u6.regs]; exact val.1, by rw [u6.regs]; exact val.2, by rw [u6.regs, sp5], by rw [u6.regs, v520],
        by rw [u6.regs, v59], by rw [u6.regs, v58], fun q q0 q1 q2 q3 q4 qr q20 q9 q8 q19 => by
          rw [u6.regs, K5 q q0 q1 q2 q3 q4 qr q20 q9 q8 q19]⟩
    · obtain ⟨n6, d6, u6⟩ := u5'.notTaken hc4 0x68 bg_at_66 (by decide) (by rw [hb5]; exact decide_eq_false hl)
      exact ⟨n6, n4.mem, .cons d1 (.cons d2 (.cons d3 (c4.trans (c5.trans (.single d6))))),
        by rw [ite_eq_right hl]; exact u6.self, hc4, hb4, fr5, by rw [u6.regs, v519]; exact bm,
        by rw [u6.regs]; exact val.1, by rw [u6.regs]; exact val.2, by rw [u6.regs, sp5], by rw [u6.regs, v520],
        by rw [u6.regs, v59], by rw [u6.regs, v58], fun q q0 q1 q2 q3 q4 qr q20 q9 q8 q19 => by
          rw [u6.regs, K5 q q0 q1 q2 q3 q4 qr q20 q9 q8 q19]⟩
  intro m
  induction m with
  | zero =>
    intro i hi M n b s hc hb hfr hbm h1 h2 rsp r20 r9 r8 r19
    have i7 : i = 7 := Nat.succ.inj hi
    subst i7
    obtain ⟨n1, M1, c1, u1, hc1, _, hf1, hm1, v1, v2, sp1, _, _, _, fr⟩ :=
      step 7 (by decide) s hc hb hfr hbm h1 h2 rsp r20 r9 r8 r19
    exact ⟨n1, M1, c1, u1, hc1, hf1, hm1, v1, v2, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm h1 h2 rsp r20 r9 r8 r19
    have hl : i + 1 < 8 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, v1, v2, sp1, e20, e9, e8, fr⟩ :=
      step i (by omega) s hc hb hfr hbm h1 h2 rsp r20 r9 r8 r19
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hm', v1', v2', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 v1 v2 sp1 e20 e9 e8 rfl
    exact ⟨n', M', c1.trans c', u', hc', hf', hm', v1', v2', sp', fun q q0 q1 q2 q3 q4 qr q20 q9 q8 q19 => by
      rw [fr' q q0 q1 q2 q3 q4 qr q20 q9 q8 q19, fr q q0 q1 q2 q3 q4 qr q20 q9 q8 q19]⟩

/-- The byte loop's body, from 0x18 to its branch at 0x26: copy one byte. -/
def bgCopy : List BInstr :=
  [.lbu a3 a1 0, .aluImm .add a1 a1 1, .sb a0 a3 0, .aluImm .add a0 a0 1, .aluImm .add a2 a2 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem bgCopy_end : blockEnd scalarFromSlice256Code 0x18 bgCopy = some 0x26 := by decide
end

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The byte loop from 0x18, with `k` of the 32 bytes left after the first
`j`: it copies the bytes at `src` to the 32 at `C`, one at a time. -/
theorem bg_copy {Mb : Word → BitVec 8} {src C : Word}
    (hc : ∀ Mx : Word → BitVec 8, (∀ x, Sep C 32 x 1 → Mx x = Mb x) → CodeIn Mx BV scalarFromSlice256Code)
    (hsT : Sep src 32 C 32) (hTw : C.toNat + 32 ≤ 0x40000000) :
    ∀ k j (n : Machine) (Mx : Word → BitVec 8), j + k = 32 → 0 < k →
      St Mx BV n 0x18 (reg n) → (∀ x, Sep C 32 x 1 → Mx x = Mb x) →
      (∀ i, i < j → Mx (C + BitVec.ofNat 32 i) = Mb (src + BitVec.ofNat 32 i)) →
      reg n a2 = BitVec.ofNat 32 k → reg n a0 = C + BitVec.ofNat 32 j → reg n a1 = src + BitVec.ofNat 32 j →
      ∃ n' Mf, Steps n n' ∧ St Mf BV n' 0x28 (reg n') ∧ (∀ x, Sep C 32 x 1 → Mf x = Mb x) ∧
        (∀ i, i < 32 → Mf (C + BitVec.ofNat 32 i) = Mb (src + BitVec.ofNat 32 i)) ∧
        ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro j n Mx hjk _ st hag hj ha2 ha0 ha1
    have hcx := hc Mx hag
    have hz := st.zero
    have hTj : Sep (C + BitVec.ofNat 32 j) 1 BV scalarFromSlice256Code.length :=
      sep_of_le (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, show BV.toNat = (img% scalarFromSlice256Address) by decide]; omega)
        (by decide)
    obtain ⟨n1, c1, u1⟩ := St.block bgCopy st hcx bgCopy_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, bgCopy, upd_app, ↓reduceIte, and_true, true_and]
      rw [ha0, add_lit_zero]; exact hTj)
    have eM : (runBlock bgCopy (Mx, reg n)).1 =
        memStore8 Mx (C + BitVec.ofNat 32 j) (Mb (src + BitVec.ofNat 32 j)) := by
      simp +decide only [runBlock, BInstr.run, bgCopy, upd_app, ↓reduceIte]
      rw [ha0, ha1, add_lit_zero, add_lit_zero, uo_ext_zext,
        hag _ (hsT.sub (c := j) (l := 1) (by omega)).symm]
    have R1 : ∀ q, reg n1 q = (runBlock bgCopy (Mx, reg n)).2 q := u1.regs
    have u1' : St (memStore8 Mx (C + BitVec.ofNat 32 j) (Mb (src + BitVec.ofNat 32 j))) BV n1 0x26 (reg n1) :=
      ⟨u1.pc, by rw [u1.mem, eM], fun _ => rfl⟩
    have hag' : ∀ x, Sep C 32 x 1 → memStore8 Mx (C + BitVec.ofNat 32 j) (Mb (src + BitVec.ofNat 32 j)) x = Mb x :=
      fun x hx => by rw [memStore8_ne (sep1_ne (hx.sub (c := j) (l := 1) (by omega))), hag x hx]
    have hj' : ∀ i, i < j + 1 → memStore8 Mx (C + BitVec.ofNat 32 j) (Mb (src + BitVec.ofNat 32 j))
        (C + BitVec.ofNat 32 i) = Mb (src + BitVec.ofNat 32 i) := fun i hi => by
      by_cases hij : i = j
      · subst hij; exact memStore8_same _ _ _
      · rw [memStore8_ne (sep1_ne (sep_offsets C (c := j) (n := 1) (d := i) (k := 1) (by omega) (by omega)
          (by omega))), hj i (by omega)]
    have hcx' := hc _ hag'
    have a21 : reg n1 a2 = BitVec.ofNat 32 k := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, bgCopy, upd_app, ↓reduceIte]; rw [ha2]
      exact frp_ofNat_dec k
    have a01 : reg n1 a0 = C + BitVec.ofNat 32 (j + 1) := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, bgCopy, upd_app, ↓reduceIte]; rw [ha0]
      exact add_ofNat_assoc C j 1
    have a11 : reg n1 a1 = src + BitVec.ofNat 32 (j + 1) := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, bgCopy, upd_app, ↓reduceIte]; rw [ha1]
      exact add_ofNat_assoc src j 1
    have K1 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg n1 r = reg n r := fun r h0 h1 h2 h3 => by
      rw [R1]; refine runBlock_reg _ _ _ r hz ?_
      simp only [bgCopy, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      simp [h0, h1, h2, h3]
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n2, d2, u2⟩ := u1'.notTaken hcx' 0x28 bg_at_26 (by decide) (by
        simp only [branchTaken]; rw [a21, u1'.zero]; decide)
      have hj48 : j + 1 = 32 := by omega
      rw [hj48] at hj'
      exact ⟨n2, _, c1.trans (.single d2), u2.self, hag', hj',
        fun r h0 h1 h2 h3 => by rw [u2.regs, K1 r h0 h1 h2 h3]⟩
    · obtain ⟨n2, d2, u2⟩ := u1'.taken hcx' 0x18 bg_at_26 (by decide) (by
        simp only [branchTaken, a21, u1'.zero, bne_iff_ne, ne_eq]
        intro h; exact hk (by have := ofNat_inj (c := k) (d := 0) (by omega) (by decide) h; omega))
      obtain ⟨n3, Mf, c3, u3, hag3, hb3, K3⟩ := ih (j + 1) n2 _ (by omega) (by omega) u2.self hag' hj'
        (by rw [u2.regs, a21]) (by rw [u2.regs, a01]) (by rw [u2.regs, a11])
      exact ⟨n3, Mf, c1.trans (.cons d2 c3), u3, hag3, hb3,
        fun r h0 h1 h2 h3 => by rw [K3 r h0 h1 h2 h3, u2.regs, K1 r h0 h1 h2 h3]⟩

/-- The code `from_slice` runs, its callees', and the copy of the order it
compares against, with that copy's value. -/
structure BGEnv (M : Word → BitVec 8) : Prop where
  cod : CodeIn M BV scalarFromSlice256Code
  fb : FCEnv M
  bsb : CodeIn M (BitVec.ofNat 32 borrowingSubAddress) borrowingSubCode
  nz : CodeIn M (BitVec.ofNat 32 uintRefIsNonzeroAddress) uintRefIsNonzeroCode
  bb : CodeIn M (BitVec.ofNat 32 blackBoxU8Address) blackBoxU8Code
  ord : accV M BYO 8 = C3.p256.n

abbrev bgPs : List (Fin 32 × Word) :=
  [(ra, 0x5C), ((8 : Fin 32), 0x58), ((9 : Fin 32), 0x54), ((18 : Fin 32), 0x50), ((19 : Fin 32), 0x4C),
   ((20 : Fin 32), 0x48)]

def bgS1 : List BInstr := [.alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0x8, .aluImm .add a2 x0 0x20]
def bgS2 : List BInstr :=
  [.aluImm .add a0 sp 0x28, .aluImm .add a1 sp 0x8, .aluImm .add a2 x0 0x20, .aluImm .add a3 x0 0x100,
   .aluImm .add (20 : Fin 32) sp 0x28]
def bgS3 : List BInstr :=
  [.aluImm .add (19 : Fin 32) x0 0x0, .lui (9 : Fin 32) 0x3FCC4000, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xD8,
   .aluImm .add (8 : Fin 32) x0 0x8]
def bgS4 : List BInstr := [.lui a0 0x3FCC4000, .aluImm .add a0 a0 0xF8, .aluImm .add a1 x0 0x0]
def bgS5 : List BInstr :=
  [.aluImm .add a1 sp 0x48, .aluImm .and (8 : Fin 32) a0 0xFF, .alu .add a0 x0 a1, .aluImm .add a1 x0 0x0]
def bgS6 : List BInstr :=
  [.aluImm .and a0 a0 0xFF, .aluImm .xor a0 a0 0xFFFFFFFF, .alu .and a0 (19 : Fin 32) a0, .aluImm .and a0 a0 0x1,
   .alu .or a0 a0 (8 : Fin 32)]
def bgS7 : List BInstr := [.aluImm .add a1 x0 0x1, .aluImm .and a0 a0 0xFF]
def bgS8 : List BInstr := [.aluImm .add a0 (18 : Fin 32) 0x4, .aluImm .add a1 sp 0x28, .aluImm .add a2 x0 0x20]

section
set_option maxRecDepth 20000
theorem bgSave_end : blockEnd scalarFromSlice256Code 2 (saveBlock bgPs) = some 0xE := by decide
theorem bgS1_end : blockEnd scalarFromSlice256Code 0xE bgS1 = some 0x16 := by decide
theorem bgS2_end : blockEnd scalarFromSlice256Code 0x28 bgS2 = some 0x38 := by decide
theorem bgS3_end : blockEnd scalarFromSlice256Code 0x40 bgS3 = some 0x4C := by decide
theorem bgS4_end : blockEnd scalarFromSlice256Code 0x68 bgS4 = some 0x72 := by decide
theorem bgS5_end : blockEnd scalarFromSlice256Code 0x7A bgS5 = some 0x84 := by decide
theorem bgS6_end : blockEnd scalarFromSlice256Code 0x8C bgS6 = some 0x9C := by decide
theorem bgS7_end : blockEnd scalarFromSlice256Code 0xA4 bgS7 = some 0xAA := by decide
theorem bgS8_end : blockEnd scalarFromSlice256Code 0xAE bgS8 = some 0xB8 := by decide
theorem bgRestore_end : blockEnd scalarFromSlice256Code 0xC6 (restoreBlock bgPs) = some 0xD2 := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
set_option exponentiation.threshold 400 in
/-- **The compiled `ScalarValue<NistP384>::from_slice`**: for the 32 bytes
at `b`, read as a big-endian number `x`, it writes to `out` the tag 0 and
`x`'s 8 limbs when `x < n`, and the tag 1 otherwise. It returns with `sp`
and the callee-saved registers restored and writes only `out` and the 0xC0
bytes of stack below `sp`. -/
theorem scalarFromSlice256_correct (m : Machine) {sp0 out b retAddr : Word} (E : BGEnv m.mem)
    (hpc : m.pc = BV) (ha0 : reg m a0 = out) (ha1 : reg m a1 = b)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hsa : sp0.toNat % 4 = 0) (hsl : 0xC0 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (how : out.toNat + 36 ≤ 0x40000000) (hoa : out.toNat % 4 = 0)
    (sBG : Sep b 32 (sp0 + 0xFFFFFF40) 0xC0) (sOG : Sep out 36 (sp0 + 0xFFFFFF40) 0xC0)
    (sGO : Sep (sp0 + 0xFFFFFF40) 0xC0 BYO 32) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (beNat (memBytes m.mem b 32) < C3.p256.n → memLoad32 m'.mem out = 0 ∧
        accV m'.mem (out + 4) 8 = beNat (memBytes m.mem b 32)) ∧
      (C3.p256.n ≤ beNat (memBytes m.mem b 32) → memLoad32 m'.mem out = 1) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF40) 0xC0 x 1 → Sep out 36 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF40 = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFA0 = F := ⟨_, rfl⟩
  rw [hG] at sBG sOG sGO ⊢
  have hGn : G.toNat = sp0.toNat - 0xC0 := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF40 : Word).toNat = 2 ^ 32 - 0xC0 from rfl]; have := sp0.isLt; omega
  have hGF : G + BitVec.ofNat 32 0x60 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGc : ∀ c, c ≤ 0xC0 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hFn : F.toNat = G.toNat + 0x60 := by rw [← hGF]; exact hGc _ (by decide)
  have hFa : F.toNat % 4 = 0 := by omega
  have hGw : ∀ c, c ≤ 0xC0 → (G + BitVec.ofNat 32 c).toNat + 4 * 8 < 2 ^ 32 := fun c hc => by
    rw [hGc c hc]; omega
  have hOw : (out + 4).toNat + 4 * 8 < 2 ^ 32 := by
    rw [BitVec.toNat_add, show (4 : Word).toNat = 4 from rfl]; omega
  have hO4 : (out + 4).toNat = out.toNat + 4 := by rw [BitVec.toNat_add, show (4 : Word).toNat = 4 from rfl]; omega
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x60 + k) := fun k => by
    rw [← hGF, add_ofNat_assoc]
  have eFS : F + 0x60 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0xC0 → d + k ≤ 0xC0 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have inG : ∀ {c l : Nat} {x : Word}, Sep G 0xC0 x 1 → c + l ≤ 0xC0 → Sep (G + BitVec.ofNat 32 c) l x 1 :=
    fun hx h => (hx.symm.subR h).symm
  have hiG : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep G 0xC0 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hiO : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep out 36 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hiC : ∀ {c l : Nat} {a : Word} {len : Nat}, c + l ≤ 0xC0 → 0x40000000 ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 →
      Sep (G + BitVec.ofNat 32 c) l a len := fun h h1 h2 => sep_of_le (by rw [hGc _ (by omega)]; omega) h2
  have cd : ∀ {M' : Word → BitVec 8} {c : Word} {code : List Nat}, CodeIn m.mem c code → 0x40000000 ≤ c.toNat →
      c.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep G 0xC0 x 1 → M' x = m.mem x) → CodeIn M' c code :=
    fun hc h1 h2 hM i hi' => by
      rw [hM _ (hiG _ (code_hi h1 h2 hi'))]; exact hc i hi'
  have hBFn : BV.toNat = (img% scalarFromSlice256Address) := by decide
  have hc := E.cod
  have st0 : St m.mem BV m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hc bg_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFA0) sp = F := by
    simp +decide only [upd, ↓reduceIte]; rw [hsp]; exact hF
  have slotO : ∀ o : Word, F + o = F + BitVec.ofNat 32 o.toNat := fun o => by rw [ofNat_toNat_self]
  have slotC : ∀ o : Word, o.toNat ≤ 0x5C → Sep (F + o) 4 BV scalarFromSlice256Code.length := fun o ho =>
    sep_of_le (by rw [BitVec.toNat_add, hBFn]; have := Nat.mod_le (F.toNat + o.toNat) (2 ^ 32); omega)
      (by rw [hBFn]; decide)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock bgPs) u1 hc bgSave_end (saveBlock_ok _ bgPs _ fun q hq => by
      rw [sp1]
      simp only [bgPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add hFa (by decide), slotC _ (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFA0)) bgPs = Ms :=
    ⟨_, rfl⟩
  rw [hMs] at u2
  have IMs : ∀ x, Sep G 0xC0 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside bgPs fun q hq => by
      simp only [bgPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
        (rw [slotO, eFk]; exact inG hx (by decide))
  have slots : ∀ r o, (r, o) ∈ bgPs → memLoad32 Ms (F + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [bgPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot bgPs _ hm (by
      simp only [bgPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide), upd_ne (by
        simp only [bgPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hr]
  have hc2 : CodeIn Ms BV scalarFromSlice256Code := cd hc (by rw [hBFn]; decide) (by rw [hBFn]; decide) IMs
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  obtain ⟨m3, c3, u3⟩ := St.block bgS1 u2.self hc2 bgS1_end (by simp only [BlockOk, BInstr.ok, bgS1, and_self])
  have R3 : ∀ q, reg m3 q = (runBlock bgS1 (Ms, reg m2)).2 q := u3.regs
  have u3' : St Ms BV m3 0x16 (reg m3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  have K3 : ∀ q, q.val ∉ [10, 12, 18] → reg m3 q = reg m2 q := fun q hq => by
    rw [R3]; refine runBlock_reg _ _ _ q u2.self.zero ?_
    simp only [bgS1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  obtain ⟨C, hC⟩ : ∃ C, G + BitVec.ofNat 32 0x68 = C := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, G + BitVec.ofNat 32 0x88 = X := ⟨_, rfl⟩
  have eFC : F + 0x8 = C := by rw [← hC, show (0x8 : Word) = BitVec.ofNat 32 0x8 from rfl, eFk]
  have eFX : F + 0x28 = X := by rw [← hX, show (0x28 : Word) = BitVec.ofNat 32 0x28 from rfl, eFk]
  have hCn : C.toNat = G.toNat + 0x68 := by rw [← hC]; exact hGc _ (by decide)
  have hXn : X.toNat = G.toNat + 0x88 := by rw [← hX]; exact hGc _ (by decide)
  have v3 : reg m3 (18 : Fin 32) = out ∧ reg m3 a0 = C ∧ reg m3 a2 = BitVec.ofNat 32 32 := by
    simp +decide only [R3, runBlock, BInstr.run, bgS1, upd_app, ↓reduceIte]
    rw [r2 a0 (by decide), ha0, sp2, u2.self.zero]; simp only [ev_add, eFC, and_true]; exact zw _
  obtain ⟨v318, v3a0, v3a2⟩ := v3
  obtain ⟨m4, d4, u4⟩ := u3'.notTaken hc2 0x18 bg_at_16 (by decide) (by
    simp only [branchTaken]; rw [v3a2, u3'.zero]; decide)
  have sCs : Sep b 32 C 32 := by rw [← hC]; exact sBG.subR (c := 0x68) (l := 32) (by decide)
  have sCB : Sep C 32 BV scalarFromSlice256Code.length := by
    rw [← hC]; exact hiC (by decide) (by rw [hBFn]; decide) (by rw [hBFn]; decide)
  have hcopy : ∀ Mx : Word → BitVec 8, (∀ x, Sep C 32 x 1 → Mx x = Ms x) → CodeIn Mx BV scalarFromSlice256Code :=
    fun Mx hM i hi => by rw [hM _ (sCB.subR (c := i) (l := 1) (by omega))]; exact hc2 i hi
  obtain ⟨m5, Mc, c5, u5, fr5, cp5, K5⟩ := bg_copy (Mb := Ms) (src := b) (C := C) hcopy sCs (by omega)
    32 0 m4 Ms (by decide) (by decide) u4.self (fun _ _ => rfl) (fun i hi => absurd hi (by omega))
    (by rw [u4.regs, v3a2]) (by rw [u4.regs, v3a0, add_ofNat_zero])
    (by rw [u4.regs, K3 a1 (by decide), r2 a1 (by decide), ha1, add_ofNat_zero])
  have IMc : ∀ x, Sep G 0xC0 x 1 → Mc x = m.mem x := fun x hx => by
    rw [fr5 x (by rw [← hC]; exact inG hx (by decide)), IMs x hx]
  have hc5 : CodeIn Mc BV scalarFromSlice256Code := cd hc (by rw [hBFn]; decide) (by rw [hBFn]; decide) IMc
  have K5' : ∀ q, q.val ∉ [10, 11, 12, 13, 18] → reg m5 q = reg m2 q := fun q hq => by
    rw [K5 q (by intro h; apply hq; rw [h]; decide) (by intro h; apply hq; rw [h]; decide)
      (by intro h; apply hq; rw [h]; decide) (by intro h; apply hq; rw [h]; decide), u4.regs,
      K3 q (by intro h; apply hq; revert h; revert q; decide)]
  have sp5 : reg m5 sp = F := by rw [K5' sp (by decide), sp2]
  obtain ⟨m6, c6, u6⟩ := St.block bgS2 u5 hc5 bgS2_end (by simp only [BlockOk, BInstr.ok, bgS2, and_self])
  have R6 : ∀ q, reg m6 q = (runBlock bgS2 (Mc, reg m5)).2 q := u6.regs
  have u6' : St Mc BV m6 0x38 (reg m6) := ⟨u6.pc, by rw [u6.mem]; rfl, fun _ => rfl⟩
  have K6 : ∀ q, q.val ∉ [10, 11, 12, 13, 20] → reg m6 q = reg m5 q := fun q hq => by
    rw [R6]; refine runBlock_reg _ _ _ q u5.zero ?_
    simp only [bgS2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have v6 : reg m6 a0 = X ∧ reg m6 a1 = C ∧ reg m6 a2 = BitVec.ofNat 32 32 ∧ reg m6 a3 = BitVec.ofNat 32 256 ∧
      reg m6 (20 : Fin 32) = X := by
    simp +decide only [R6, runBlock, BInstr.run, bgS2, upd_app, ↓reduceIte]
    rw [sp5]; simp only [ev_add, eFX, eFC, and_true]
  obtain ⟨v6a0, v6a1, v6a2, v6a3, v620⟩ := v6
  obtain ⟨m7, c7, pc7, mem7, regs7⟩ := u6'.callRa hc5 bg_at_38 bg_at_3c (cb := FC) (by decide) (by decide)
  have r7 := PEnv.reg1 regs7 u6'.zero
  have hFBn : FC.toNat = fromBeSliceTrunc8Address := by decide
  have eF70 : F + 0xFFFFFFA0 = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
  have EF : FCEnv m7.mem := by
    rw [mem7]
    exact ⟨cd E.fb.cod (by rw [hFBn]; decide) (by rw [hFBn]; decide) IMc,
      cd E.fb.ms (by decide) (by decide) IMc, cd E.fb.fl (by decide) (by decide) IMc,
      cd E.fb.cs (by decide) (by decide) IMc, cd E.fb.cb (by decide) (by decide) IMc⟩
  have sp6 : reg m6 sp = F := by rw [K6 sp (by decide), sp5]
  have low70 : ∀ {c l : Nat}, 0x60 ≤ c → c + l ≤ 0xC0 → Sep (G + BitVec.ofNat 32 c) l G 0x60 := fun {c l} h1 h2 => by
    have := offs (c := c) (n := l) (d := 0) (k := 0x60) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  obtain ⟨m8, c8, pc8, sp8, K8, val8, fr8⟩ := fromBeSliceTrunc8_correct m7 (sp0 := F) (out := X) (b := C)
    (n := 32) (bits := 256) (retAddr := BV + BitVec.ofNat 32 (0x38 + 8)) EF pc7
    (by rw [r7 a0 (by decide), v6a0]) (by rw [r7 a1 (by decide), v6a1]) (by rw [r7 a2 (by decide), v6a2])
    (by rw [r7 a3 (by decide), v6a3]) (by rw [regs7]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at BV (by decide) _ (by decide))) (by rw [r7 sp (by decide), sp6]) (by decide)
    (Nat.le_refl _) (by omega) hFa (by omega) (by omega) (by omega) (by omega)
    (by rw [eF70, ← hC]; exact low70 (by decide) (by decide)) (by rw [eF70, ← hX]; exact low70 (by decide) (by decide))
  rw [show (256 : Nat) / 8 = 32 from rfl, Nat.min_self, BitVec.add_sub_cancel, mem7] at val8
  have xval : accV m8.mem X 8 = beNat (memBytes m.mem b 32) := by
    rw [val8]; unfold memBytes
    exact congrArg beNat (List.map_congr_left fun i hi => congrArg BitVec.toNat (by
      rw [cp5 i (List.mem_range.mp hi), IMs _ (sBG.sub (c := i) (l := 1) (by have := List.mem_range.mp hi; omega)).symm]))
  rw [mem7, eF70] at fr8
  have IM8 : ∀ x, Sep G 0xC0 x 1 → m8.mem x = m.mem x := fun x hx => by
    have h0 := inG (c := 0) (l := 0x60) hx (by decide); rw [add_ofNat_zero] at h0
    rw [fr8 x h0 (by rw [← hX]; exact inG hx (by decide)), IMc x hx]
  have hc8 : CodeIn m8.mem BV scalarFromSlice256Code := cd hc (by rw [hBFn]; decide) (by rw [hBFn]; decide) IM8
  have u8 : St m8.mem BV m8 0x40 (reg m8) := ⟨by rw [pc8], rfl, fun _ => rfl⟩
  have K8' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m8 q = reg m6 q := fun q hq => by
    rw [K8 q (by revert hq; revert q; decide), r7 q (by revert hq; revert q; decide)]
  obtain ⟨m9, c9, u9⟩ := St.block bgS3 u8 hc8 bgS3_end (by simp only [BlockOk, BInstr.ok, bgS3, and_self])
  have R9 : ∀ q, reg m9 q = (runBlock bgS3 (m8.mem, reg m8)).2 q := u9.regs
  have u9' : St m8.mem BV m9 0x4C (reg m9) := ⟨u9.pc, by rw [u9.mem]; rfl, fun _ => rfl⟩
  have K9 : ∀ q, q.val ∉ [8, 9, 19] → reg m9 q = reg m8 q := fun q hq => by
    rw [R9]; refine runBlock_reg _ _ _ q u8.zero ?_
    simp only [bgS3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have v9 : reg m9 (19 : Fin 32) = 0 ∧ reg m9 (9 : Fin 32) = BYO ∧ reg m9 (8 : Fin 32) = BitVec.ofNat 32 8 := by
    simp +decide only [R9, runBlock, BInstr.run, bgS3, upd_app, ↓reduceIte]; rw [u8.zero]
    exact ⟨rfl, trivial⟩
  obtain ⟨v919, v99, v98⟩ := v9
  obtain ⟨m10, d10, u10⟩ := u9'.notTaken hc8 0x4E bg_at_4c (by decide) (by
    simp only [branchTaken]; rw [v98, u9'.zero]; decide)
  have sp9 : reg m9 sp = F := by
    rw [K9 sp (by decide), sp8]
  have v920 : reg m9 (20 : Fin 32) = X := by rw [K9 _ (by decide), K8' _ (by decide), v620]
  have eFm4 : F + 0xFFFFFFFC = G + BitVec.ofNat 32 0x5C := by rw [← hGF, BitVec.add_assoc]; rfl
  have hBBn : BV + 0xFFFFF630 = BitVec.ofNat 32 borrowingSubAddress := by decide
  have hBSb : (BitVec.ofNat 32 borrowingSubAddress : Word).toNat = borrowingSubAddress := by decide
  obtain ⟨n11, M11, c11, u11, hc11, fr11, hm11, I1, I2, sp11, K11⟩ := bg_cmp_loop (P := BV) (F := F) (X := X)
    (N := BYO) (M0 := m8.mem) (by decide) hFa (by omega) (by decide)
    (by rw [eFm4, ← hX]; exact offs (by omega) (by omega) (by omega)) (by rw [eFm4]; exact sGO.sub (by decide))
    (by rw [eFm4, hBBn]; exact hiC (by decide) (by rw [hBSb]; decide) (by rw [hBSb]; decide))
    (by rw [eFm4]; exact hiC (by decide) (by rw [hBFn]; decide) (by rw [hBFn]; decide))
    7 0 rfl u10.self hc8 (by rw [hBBn]; exact cd E.bsb (by rw [hBSb]; decide) (by rw [hBSb]; decide) IM8)
    (fun _ _ => rfl) (.inl rfl) (Nat.zero_le _) (by show 0 + 2 ^ (32 * 0) * maskBit 0 < 0 + 2 ^ (32 * 0); decide)
    (by rw [u10.regs, sp9]) (by rw [u10.regs, v920, add_ofNat_zero]) (by rw [u10.regs, v99, add_ofNat_zero])
    (by rw [u10.regs, v98]) (by rw [u10.regs, v919])
  have nz8 : accV m8.mem BYO 8 = C3.p256.n := by
    rw [accV_congr (M := m.mem) 8 fun i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact IM8 _ (sGO.subR (c := 4 * i + j) (l := 1) (by omega)), E.ord]
  rw [nz8, xval] at I1 I2
  have IM11 : ∀ x, Sep G 0xC0 x 1 → M11 x = m.mem x := fun x hx => by
    rw [fr11 x (by rw [eFm4]; exact inG hx (by decide)), IM8 x hx]
  -- the slots below `sp0` that hold the saved registers, untouched since the prologue
  have lowS : ∀ {a l c : Nat}, a + l ≤ c → c < 0xC0 → Sep (G + BitVec.ofNat 32 a) l (G + BitVec.ofNat 32 c) 1 :=
    fun h1 h2 => offs (by omega) (by omega) (by omega)
  have slot11 : ∀ c, 0xA8 ≤ c → c < 0xC0 → M11 (G + BitVec.ofNat 32 c) = Ms (G + BitVec.ofNat 32 c) := fun c h1 h2 => by
    have hG0 : Sep G 0x60 (G + BitVec.ofNat 32 c) 1 := by
      have := lowS (a := 0) (l := 0x60) (c := c) (by omega) h2; rwa [add_ofNat_zero] at this
    rw [fr11 _ (by rw [eFm4]; exact lowS (by omega) h2), fr8 _ hG0 (by rw [← hX]; exact lowS (by omega) h2),
      fr5 _ (by rw [← hC]; exact lowS (by omega) h2)]
  -- the end, from 0xC2: store the tag, restore the registers, and return
  have hpsp : ∀ p ∈ bgPs, p.1 ≠ sp := by decide
  have tail : ∀ {Mt : Word → BitVec 8} {n : Machine} {v : Word}, St Mt BV n 0xC2 (reg n) →
      CodeIn Mt BV scalarFromSlice256Code → reg n sp = F → reg n (18 : Fin 32) = out → reg n a1 = v →
      (∀ c, 0xA8 ≤ c → c < 0xC0 → Mt (G + BitVec.ofNat 32 c) = Ms (G + BitVec.ofNat 32 c)) →
      (∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg n q = reg m q) →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ reg n' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg m q) ∧
        n'.mem = memStore32 Mt out v := by
    intro Mt n v st hct rsp r18 ra1 hsl' hK
    obtain ⟨n1, d1, u1⟩ := st.sw hct bg_at_c2 (off' := 0xC6) (by decide) (by rw [r18, add_lit_zero]; exact hoa)
    rw [r18, add_lit_zero, ra1] at u1
    have hct1 : CodeIn (memStore32 Mt out v) BV scalarFromSlice256Code :=
      hct.store32 (sep_of_le (by rw [hBFn]; omega) (by rw [hBFn]; decide))
    have slotT : ∀ o : Word, 0x48 ≤ o.toNat → o.toNat + 4 ≤ 0x60 →
        memLoad32 (memStore32 Mt out v) (F + o) = memLoad32 Ms (F + o) := fun o h1 h2 => by
      rw [slotO]; apply memLoad32_congr; intro j hj
      rw [add_ofNat_assoc, eFk, memStore32_get_sep (sOG.sub (c := 0) (l := 4) (by decide) |> fun h => by
        rw [add_ofNat_zero] at h; exact h.subR (c := 0x60 + (o.toNat + j)) (l := 1) (by omega)),
        hsl' _ (by omega) (by omega)]
    obtain ⟨n2, c2', u2'⟩ := St.block (restoreBlock bgPs) u1 hct1 bgRestore_end
      (restoreBlock_ok (memStore32 Mt out v) F bgPs (reg n) rsp hpsp fun q hq => by
        simp only [bgPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
    simp only [restoreBlock_run (memStore32 Mt out v) F bgPs (reg n) rsp hpsp] at u2'
    have rsp' : restoreRegs (memStore32 Mt out v) F (reg n) bgPs sp = F := by
      rw [restoreRegs_sp _ _ _ _ hpsp]; exact rsp
    obtain ⟨n3, d3, u3⟩ := u2'.aluImm hct1 bg_at_d2 (off' := 0xD4) (by decide)
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hct1 bg_at_d4
    have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
        restoreRegs (memStore32 Mt out v) F f ps q = f q := by
      intro f ps q hq0
      induction ps generalizing f with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro h
        simp only [restoreRegs]
        rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
    have hslot : ∀ r o, (r, o) ∈ bgPs → reg n4 r = reg m r := fun r o hm => by
      rw [regs4]
      simp only [bgPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
        rw [slotT _ (by decide) (by decide)]; exact slots _ _ (by decide)
    refine ⟨n4, .cons d1 (c2'.trans (.cons d3 (.single d4))), ?_, ?_, fun q hq => ?_, ?_⟩
    · rw [pc4, ← regs4, hslot ra 0x5C (by decide), hra, add_lit_zero, hret]
    · rw [regs4]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [rsp', eFS]
    · rcases (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
          q = (20 : Fin 32) ∨ q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27]) q hq with
        rfl | rfl | rfl | rfl | rfl | rfl | hL
      · exact hslot _ 0x5C (by decide)
      · exact hslot _ 0x58 (by decide)
      · exact hslot _ 0x54 (by decide)
      · exact hslot _ 0x50 (by decide)
      · exact hslot _ 0x4C (by decide)
      · exact hslot _ 0x48 (by decide)
      · obtain ⟨hv, hs, hps⟩ : q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ bgPs, p.1 ≠ q) := by revert hL; revert q; decide
        rw [regs4, upd_ne hv hs, rr _ _ q hv hps, hK q hL]
    · rw [mem4]
  have hc11' : CodeIn M11 BV scalarFromSlice256Code := hc11
  have hNZa : (BitVec.ofNat 32 uintRefIsNonzeroAddress : Word).toNat = uintRefIsNonzeroAddress := by decide
  have sNZ : Sep (F + 0xFFFFFFFC) 4 (BitVec.ofNat 32 uintRefIsNonzeroAddress) uintRefIsNonzeroCode.length := by
    rw [eFm4]; exact hiC (by decide) (by rw [hNZa]; decide) (by rw [hNZa]; decide)
  obtain ⟨m12, c12, u12⟩ := St.block bgS4 u11 hc11' bgS4_end (by simp only [BlockOk, BInstr.ok, bgS4, and_self])
  have R12 : ∀ q, reg m12 q = (runBlock bgS4 (M11, reg n11)).2 q := u12.regs
  have u12' : St M11 BV m12 0x72 (reg m12) := ⟨u12.pc, by rw [u12.mem]; rfl, fun _ => rfl⟩
  have K12 : ∀ q, q ≠ a0 → q ≠ a1 → reg m12 q = reg n11 q := fun q h0 h1 => by
    rw [R12]; refine runBlock_reg _ _ _ q u11.zero ?_
    simp only [bgS4, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1]
  have v12 : reg m12 a0 = (img% p256OrderBeAddress) ∧ reg m12 a1 = 0 := by
    simp +decide only [R12, runBlock, BInstr.run, bgS4, upd_app, ↓reduceIte]
  obtain ⟨n13, c13, u13, a013, k13, fr13⟩ := u12'.nzCall0 hc11'
    (cd E.nz (by rw [hNZa]; decide) (by rw [hNZa]; decide) IM11) bg_at_72 bg_at_76 (by decide) (by decide)
    v12.1 v12.2 (by decide) (by rw [K12 sp (by decide) (by decide), sp11]) hFa sNZ
  have IM13 : ∀ x, Sep G 0xC0 x 1 → n13.mem x = m.mem x := fun x hx => by
    rw [fr13 x (by rw [eFm4]; exact inG hx (by decide)), IM11 x hx]
  have hc13 : CodeIn n13.mem BV scalarFromSlice256Code := cd hc (by rw [hBFn]; decide) (by rw [hBFn]; decide) IM13
  obtain ⟨m14, c14, u14⟩ := St.block bgS5 u13 hc13 bgS5_end (by simp only [BlockOk, BInstr.ok, bgS5, and_self])
  have R14 : ∀ q, reg m14 q = (runBlock bgS5 (n13.mem, reg n13)).2 q := u14.regs
  have u14' : St n13.mem BV m14 0x84 (reg m14) := ⟨u14.pc, by rw [u14.mem]; rfl, fun _ => rfl⟩
  have K14 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ (8 : Fin 32) → reg m14 q = reg n13 q := fun q h0 h1 h8 => by
    rw [R14]; refine runBlock_reg _ _ _ q u13.zero ?_
    simp only [bgS5, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h8]
  have sp13 : reg n13 sp = F := by
    rw [k13 sp (by decide) (by decide) (by decide) (by decide) (by decide), K12 sp (by decide) (by decide), sp11]
  have v14 : reg m14 a0 = F + 0x48 ∧ reg m14 a1 = 0 ∧ reg m14 (8 : Fin 32) = 0 := by
    simp +decide only [R14, runBlock, BInstr.run, bgS5, upd_app, ↓reduceIte]
    rw [sp13, a013]; simp only [ev_add]; exact ⟨zw _, trivial, rfl⟩
  obtain ⟨n15, c15, u15, a015, k15, fr15⟩ := u14'.nzCall0 hc13
    (cd E.nz (by rw [hNZa]; decide) (by rw [hNZa]; decide) IM13) bg_at_84 bg_at_88 (by decide) (by decide)
    v14.1 v14.2.1 (aligned_add hFa (k := 0x48) (by decide))
    (by rw [K14 sp (by decide) (by decide) (by decide), sp13]) hFa sNZ
  have IM15 : ∀ x, Sep G 0xC0 x 1 → n15.mem x = m.mem x := fun x hx => by
    rw [fr15 x (by rw [eFm4]; exact inG hx (by decide)), IM13 x hx]
  have hc15 : CodeIn n15.mem BV scalarFromSlice256Code := cd hc (by rw [hBFn]; decide) (by rw [hBFn]; decide) IM15
  obtain ⟨m16, c16, u16⟩ := St.block bgS6 u15 hc15 bgS6_end (by simp only [BlockOk, BInstr.ok, bgS6, and_self])
  have R16 : ∀ q, reg m16 q = (runBlock bgS6 (n15.mem, reg n15)).2 q := u16.regs
  have u16' : St n15.mem BV m16 0x9C (reg m16) := ⟨u16.pc, by rw [u16.mem]; rfl, fun _ => rfl⟩
  have K16 : ∀ q, q ≠ a0 → reg m16 q = reg n15 q := fun q h0 => by
    rw [R16]; refine runBlock_reg _ _ _ q u15.zero ?_
    simp only [bgS6, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0]
  -- registers the calls since the comparison loop keep
  have K15 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → q ≠ (8 : Fin 32) → reg n15 q = reg n11 q :=
    fun q h0 h1 h2 h3 hr h8 => by
      rw [k15 q h0 h1 h2 h3 hr, K14 q h0 h1 h8, k13 q h0 h1 h2 h3 hr, K12 q h0 h1]
  have v15_19 : reg n15 (19 : Fin 32) = reg n11 (19 : Fin 32) :=
    K15 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨mb, hmb⟩ : ∃ mb, maskBit (reg n11 (19 : Fin 32)) = mb := ⟨_, rfl⟩
  have hmb01 : mb = 0 ∨ mb = 1 := by
    rw [← hmb]; unfold maskBit; by_cases h : reg n11 (19 : Fin 32) = 0
    · rw [ite_eq_left h]; exact .inl rfl
    · rw [ite_eq_right h]; exact .inr rfl
  have hmbW : BitVec.ofNat 32 mb = 0 ∨ BitVec.ofNat 32 mb = 1 := by rcases hmb01 with rfl | rfl <;> decide
  have v16 : reg m16 a0 = BitVec.ofNat 32 mb := by
    simp +decide only [R16, runBlock, BInstr.run, bgS6, upd_app, ↓reduceIte]
    rw [a015, v15_19, k15 8 (by decide) (by decide) (by decide) (by decide) (by decide), v14.2.2, ← hmb]
    rcases hm11 with h | h <;> rw [h] <;> decide
  have hBBa : (BitVec.ofNat 32 blackBoxU8Address : Word).toNat = blackBoxU8Address := by decide
  obtain ⟨m17, c17, pc17, mem17, regs17⟩ := u16'.callRa hc15 bg_at_9c bg_at_a0
    (cb := BitVec.ofNat 32 blackBoxU8Address) (by decide) (by decide)
  have r17 := PEnv.reg1 regs17 u16'.zero
  have sp15 : reg n15 sp = F := by
    rw [K15 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp11]
  have sp16 : reg m16 sp = F := by rw [K16 sp (by decide), sp15]
  have eFm1 : F + 0xFFFFFFFF = G + BitVec.ofNat 32 0x5F := by rw [← hGF, BitVec.add_assoc]; rfl
  obtain ⟨m18, c18, pc18, a018, K18, fr18⟩ := blackBoxU8_correct m17 (base := BitVec.ofNat 32 blackBoxU8Address)
    (retAddr := BV + BitVec.ofNat 32 (0x9C + 8))
    (by rw [mem17]; exact cd E.bb (by rw [hBBa]; decide) (by rw [hBBa]; decide) IM15) pc17
    (by rw [regs17]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at BV (by decide) _ (by decide)))
    (by rw [r17 sp (by decide), sp16, eFm1]; exact hiC (by decide) (by rw [hBBa]; decide) (by rw [hBBa]; decide))
  rw [r17 a0 (by decide), v16, frp_c8 hmbW] at a018
  rw [r17 sp (by decide), sp16, eFm1, mem17] at fr18
  have IM18 : ∀ x, Sep G 0xC0 x 1 → m18.mem x = m.mem x := fun x hx => by
    rw [fr18 x (inG hx (by decide)), IM15 x hx]
  have hc18 : CodeIn m18.mem BV scalarFromSlice256Code := cd hc (by rw [hBFn]; decide) (by rw [hBFn]; decide) IM18
  have u18 : St m18.mem BV m18 0xA4 (reg m18) := ⟨by rw [pc18], rfl, fun _ => rfl⟩
  obtain ⟨m19, c19, u19⟩ := St.block bgS7 u18 hc18 bgS7_end (by simp only [BlockOk, BInstr.ok, bgS7, and_self])
  have R19 : ∀ q, reg m19 q = (runBlock bgS7 (m18.mem, reg m18)).2 q := u19.regs
  have u19' : St m18.mem BV m19 0xAA (reg m19) := ⟨u19.pc, by rw [u19.mem]; rfl, fun _ => rfl⟩
  have K19 : ∀ q, q ≠ a0 → q ≠ a1 → reg m19 q = reg m18 q := fun q h0 h1 => by
    rw [R19]; refine runBlock_reg _ _ _ q u18.zero ?_
    simp only [bgS7, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1]
  have v19 : reg m19 a1 = 1 ∧ reg m19 a0 = BitVec.ofNat 32 mb := by
    simp +decide only [R19, runBlock, BInstr.run, bgS7, upd_app, ↓reduceIte]
    rw [u18.zero, a018]; rcases hmbW with h | h <;> rw [h] <;> decide
  -- registers kept since `m`
  have Kall : ∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg m19 q = reg m q := fun q hq => by
    have n0 : q ≠ a0 := (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a0) q hq
    have n1 : q ≠ a1 := (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a1) q hq
    have n2 : q ≠ a2 := (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a2) q hq
    have n3 : q ≠ a3 := (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a3) q hq
    have n4 : q ≠ a4 := (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a4) q hq
    have nr : q ≠ ra := (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ ra) q hq
    have n8 : q ≠ (8 : Fin 32) := (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ (8 : Fin 32)) q hq
    have n9 : q ≠ (9 : Fin 32) := (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ (9 : Fin 32)) q hq
    have n19 : q ≠ (19 : Fin 32) := (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ (19 : Fin 32)) q hq
    have n20 : q ≠ (20 : Fin 32) := (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ (20 : Fin 32)) q hq
    have ns : q ≠ sp := (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ sp) q hq
    rw [K19 q n0 n1, K18 q n0, r17 q nr, K16 q n0, K15 q n0 n1 n2 n3 nr n8,
      K11 q n0 n1 n2 n3 n4 nr n20 n9 n8 n19, u10.regs, K9 q (by intro h; revert h; revert hq; revert q; decide),
      K8' q (by revert hq; revert q; decide), K6 q (by intro h; revert h; revert hq; revert q; decide),
      K5' q (by intro h; revert h; revert hq; revert q; decide), r2 q ns]
  have v19_18 : reg m19 (18 : Fin 32) = out := by
    rw [K19 _ (by decide) (by decide), K18 _ (by decide), r17 _ (by decide), K16 _ (by decide),
      K15 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      K11 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), u10.regs, K9 _ (by decide), K8' _ (by decide), K6 _ (by decide),
      K5 _ (by decide) (by decide) (by decide) (by decide), u4.regs, v318]
  have sp19 : reg m19 sp = F := by
    rw [K19 _ (by decide) (by decide), K18 _ (by decide), r17 _ (by decide), sp16]
  have slot18 : ∀ c, 0xA8 ≤ c → c < 0xC0 → m18.mem (G + BitVec.ofNat 32 c) = Ms (G + BitVec.ofNat 32 c) :=
    fun c h1 h2 => by
      rw [fr18 _ (lowS (by omega) h2), fr15 _ (by rw [eFm4]; exact lowS (by omega) h2),
        fr13 _ (by rw [eFm4]; exact lowS (by omega) h2), slot11 c h1 h2]
  have hx : beNat (memBytes m.mem b 32) < C3.p256.n ↔ mb = 1 := by
    rw [← hmb]
    rcases hm11 with h | h
    · rw [h, show maskBit 0 = 0 from rfl, Nat.mul_zero, Nat.add_zero] at I1
      rw [h]
      exact ⟨fun h' => absurd I1 (Nat.not_le.mpr h'), fun h' => absurd h' (by decide)⟩
    · rw [h, show maskBit 0xFFFFFFFF = 1 from rfl, Nat.mul_one] at I2
      rw [h]
      exact ⟨fun _ => rfl, fun _ => Nat.lt_of_add_lt_add_right I2⟩
  have X18 : accV m18.mem X 8 = beNat (memBytes m.mem b 32) := by
    rw [← xval]
    exact accV_congr 8 fun i hi => memLoad32_congr fun j hj => by
      rw [← hX, add_ofNat_assoc, add_ofNat_assoc]
      rw [fr18 _ (lowS (by omega) (by omega)), fr15 _ (by rw [eFm4]; exact lowS (by omega) (by omega)),
        fr13 _ (by rw [eFm4]; exact lowS (by omega) (by omega)), fr11 _ (by rw [eFm4]; exact lowS (by omega) (by omega))]
  have pre : Steps m m19 :=
    .cons d1 (c2.trans (c3.trans (.cons d4 (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (.cons d10
      (c11.trans (c12.trans (c13.trans (c14.trans (c15.trans (c16.trans (c17.trans (c18.trans c19)))))))))))))))))
  have sO4 : ∀ {x : Word}, Sep out 36 x 1 → Sep out 4 x 1 ∧ Sep (out + 4) (4 * 8) x 1 := fun hx =>
    ⟨by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this, hx.sub (c := 4) (l := 32) (by decide)⟩
  by_cases h1 : mb = 1
  · obtain ⟨m20, d20, u20⟩ := u19'.notTaken hc18 0xAE bg_at_aa (by decide) (by
      simp only [branchTaken]; rw [v19.2, v19.1, h1]; decide)
    obtain ⟨m21, c21, u21⟩ := St.block bgS8 u20.self hc18 bgS8_end (by simp only [BlockOk, BInstr.ok, bgS8, and_self])
    have R21 : ∀ q, reg m21 q = (runBlock bgS8 (m18.mem, reg m20)).2 q := u21.regs
    have u21' : St m18.mem BV m21 0xB8 (reg m21) := ⟨u21.pc, by rw [u21.mem]; rfl, fun _ => rfl⟩
    have K21 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m21 q = reg m19 q := fun q h0 h1 h2 => by
      rw [R21, runBlock_reg _ _ _ q u20.self.zero (by
        simp only [bgS8, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2]), u20.regs]
    have v21 : reg m21 a0 = out + 4 ∧ reg m21 a1 = X ∧ reg m21 a2 = BitVec.ofNat 32 (4 * 8) := by
      simp +decide only [R21, runBlock, BInstr.run, bgS8, upd_app, ↓reduceIte]
      rw [u20.regs, u20.regs, v19_18, sp19]; simp only [ev_add, eFX, and_true]
    have hMCb : (BitVec.ofNat 32 memcpyStubAddress + 8 : Word).toNat = memcpyStubAddress + 8 := by decide
    have hMCn : (BitVec.ofNat 32 memcpyStubAddress : Word).toNat = memcpyStubAddress := by decide
    obtain ⟨m22, c22, u22, _, k22⟩ := u21'.memcpyW (B := BitVec.ofNat 32 memcpyStubAddress) (w := 8) (dst := out + 4)
      (src := X) (by decide) hc18 (cd E.fb.cs (by rw [hMCn]; decide) (by rw [hMCn]; decide) IM18)
      (cd E.fb.cb (by rw [hMCb]; decide) (by rw [hMCb]; decide) IM18) bg_at_b8 bg_at_bc (by decide) (by decide)
      (by decide) hOw (by decide) (by rw [hO4]; omega) (by omega)
      (by rw [← hX]; exact (sOG.sub (c := 4) (l := 32) (by decide)).subR (c := 0x88) (l := 32) (by decide))
      (sep_of_le (by rw [hMCb, hO4]; unfold memcpyStubAddress; omega) (by rw [hMCb]; decide)) v21.1 v21.2.1 v21.2.2
    have hcm : CodeIn (copyWords m18.mem (out + 4) X 8) BV scalarFromSlice256Code := fun i hi => by
      have hxc := code_hi (b := BV) (by rw [hBFn]; decide) (by rw [hBFn]; decide) hi
      rw [copyWords_outside 8 (sep_of_le (by rw [hO4]; omega) (by have := (BV + BitVec.ofNat 32 i).isLt; omega))]
      exact hc18 i hi
    obtain ⟨m23, d23, u23⟩ := u22.aluImm hcm bg_at_c0 (off' := 0xC2) (by decide)
    have K23 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        q ≠ ra → reg m23 q = reg m19 q := fun q h0 h1 h2 h3 h4 h5 h6 h7 ht0 ht1 hr => by
      rw [u23.regs, updz u22.zero h1, k22 q h1 h2 h3 h4 h5 h6 h7 ht0 ht1 hr, K21 q h0 h1 h2]
    obtain ⟨nf, cf, pcf, spf, Kf, memf⟩ := tail (Mt := copyWords m18.mem (out + 4) X 8) (v := 0) u23.self hcm
      (by rw [K23 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), sp19])
      (by rw [K23 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), v19_18])
      (by rw [u23.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u22.zero]; rfl)
      (fun c h1 h2 => by
        rw [copyWords_outside 8 ((sO4 (sOG.subR (c := c) (l := 1) (by omega))).2), slot18 c h1 h2])
      (fun q hq => by
        rw [K23 q ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a0) q hq)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a1) q hq)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a2) q hq)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a3) q hq)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a4) q hq)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a5) q hq)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a6) q hq)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a7) q hq)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ t0) q hq)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ t1) q hq)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ ra) q hq), Kall q hq])
    refine ⟨nf, pre.trans (.cons d20 (c21.trans (c22.trans (.cons d23 cf)))), pcf, spf, Kf,
      fun _ => ⟨?_, ?_⟩, fun h => absurd (hx.mpr h1) (Nat.not_lt.mpr h), fun x hx' hl => ?_⟩
    · rw [memf, memLoad32_store32_same]
    · rw [memf, ← X18]
      refine accV_congr2 8 fun i hi => ?_
      rw [memLoad32_congr fun j hj => memStore32_get_sep (by
        have h := sep_offsets out (c := 0) (n := 4) (d := 4 + 4 * i + j) (k := 1) (by omega) (by omega) (by omega)
        rw [add_ofNat_zero, ← add_ofNat_assoc, ← add_ofNat_assoc] at h
        rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl]; exact h)]
      exact copyWords_load 8 i hi (Nat.le_of_lt hOw)
    · rw [memf, memStore32_get_sep (sO4 hl).1, copyWords_outside 8 (sO4 hl).2, IM18 x hx']
  · obtain ⟨m20, d20, u20⟩ := u19'.taken hc18 0xC2 bg_at_aa (by decide) (by
      simp only [branchTaken]; rw [v19.2, v19.1]
      rcases hmb01 with h | h
      · rw [h]; decide
      · exact absurd h h1)
    obtain ⟨nf, cf, pcf, spf, Kf, memf⟩ := tail (Mt := m18.mem) (v := 1) u20.self hc18
      (by rw [u20.regs, sp19]) (by rw [u20.regs, v19_18]) (by rw [u20.regs, v19.1]) slot18
      (fun q hq => by rw [u20.regs, Kall q hq])
    refine ⟨nf, pre.trans (.cons d20 cf), pcf, spf, Kf, fun h => absurd (hx.mp h) h1,
      fun _ => by rw [memf, memLoad32_store32_same], fun x hx' hl => ?_⟩
    rw [memf, memStore32_get_sep (sO4 hl).1, IM18 x hx']

end C3.RV32
