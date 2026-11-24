import C3BootProofs.Proofs.Bytes2Scalar384
import C3BootProofs.Proofs.Norm8

/-!
# `ecdsa::hazmat::bytes2scalar::<NistP256>`, as compiled

The P-256 instance of `Bytes2Scalar384.lean`. Its input is a 32-byte digest,
so it reads all 32 bytes as a big-endian number `x`, subtracts the order `n`
once when `x ≥ n`, and copies the result out: P-256 scalars here are not in
Montgomery form, so the scalar it returns is `x mod n`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem by_at_0 : fetchRel bytes2scalar256Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF80, 2) := by decide
theorem by_at_2 : fetchRel bytes2scalar256Code 0x2 = some (.store .sw sp ra 0x7C, 2) := by decide
theorem by_at_4 : fetchRel bytes2scalar256Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x78, 2) := by decide
theorem by_at_6 : fetchRel bytes2scalar256Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x74, 2) := by decide
theorem by_at_8 : fetchRel bytes2scalar256Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x70, 2) := by decide
theorem by_at_a : fetchRel bytes2scalar256Code 0xA = some (.store .sw sp (19 : Fin 32) 0x6C, 2) := by decide
theorem by_at_c : fetchRel bytes2scalar256Code 0xC = some (.store .sw sp (20 : Fin 32) 0x68, 2) := by decide
theorem by_at_e : fetchRel bytes2scalar256Code 0xE = some (.store .sw sp (21 : Fin 32) 0x64, 2) := by decide
theorem by_at_10 : fetchRel bytes2scalar256Code 0x10 = some (.store .sw sp (22 : Fin 32) 0x60, 2) := by decide
theorem by_at_12 : fetchRel bytes2scalar256Code 0x12 = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem by_at_14 : fetchRel bytes2scalar256Code 0x14 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem by_at_16 : fetchRel bytes2scalar256Code 0x16 = some (.lui (21 : Fin 32) 0x3FCC4000, 4) := by decide
theorem by_at_1a : fetchRel bytes2scalar256Code 0x1A = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x268, 4) := by decide
theorem by_at_1e : fetchRel bytes2scalar256Code 0x1E = some (.aluImm .add a1 x0 0x8, 2) := by decide
theorem by_at_20 : fetchRel bytes2scalar256Code 0x20 = some (.alu .add a0 x0 (21 : Fin 32), 2) := by decide
theorem by_at_22 : fetchRel bytes2scalar256Code 0x22 = some (.aluImm .add (22 : Fin 32) x0 0x8, 2) := by decide
theorem by_at_24 : fetchRel bytes2scalar256Code 0x24 = some (.auipc ra 0xA000, 4) := by decide
theorem by_at_28 : fetchRel bytes2scalar256Code 0x28 = some (.jalr ra ra 0x2D2, 4) := by decide
theorem by_at_2c : fetchRel bytes2scalar256Code 0x2C = some (.aluImm .add a1 x0 0x100, 4) := by decide
theorem by_at_30 : fetchRel bytes2scalar256Code 0x30 = some (.alu .sub (20 : Fin 32) a1 a0, 4) := by decide
theorem by_at_34 : fetchRel bytes2scalar256Code 0x34 = some (.aluImm .and a0 (20 : Fin 32) 0x7, 4) := by decide
theorem by_at_38 : fetchRel bytes2scalar256Code 0x38 = some (.aluImm .srl a1 (20 : Fin 32) 0x3, 4) := by decide
theorem by_at_3c : fetchRel bytes2scalar256Code 0x3C = some (.alu .sltu a0 x0 a0, 4) := by decide
theorem by_at_40 : fetchRel bytes2scalar256Code 0x40 = some (.alu .add a0 a0 a1, 2) := by decide
theorem by_at_42 : fetchRel bytes2scalar256Code 0x42 = some (.store .sb sp x0 0x40, 4) := by decide
theorem by_at_46 : fetchRel bytes2scalar256Code 0x46 = some (.store .sw sp a0 0x44, 2) := by decide
theorem by_at_48 : fetchRel bytes2scalar256Code 0x48 = some (.aluImm .add a0 sp 0x40, 2) := by decide
theorem by_at_4a : fetchRel bytes2scalar256Code 0x4A = some (.auipc ra 0x0, 4) := by decide
theorem by_at_4e : fetchRel bytes2scalar256Code 0x4E = some (.jalr ra ra 0xFFFFFAA6, 4) := by decide
theorem by_at_52 : fetchRel bytes2scalar256Code 0x52 = some (.alu .add a2 x0 a0, 2) := by decide
theorem by_at_54 : fetchRel bytes2scalar256Code 0x54 = some (.aluImm .add a0 x0 0x20, 4) := by decide
theorem by_at_58 : fetchRel bytes2scalar256Code 0x58 = some (.branch .bltu a2 a0 0x8, 4) := by decide
theorem by_at_5c : fetchRel bytes2scalar256Code 0x5C = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem by_at_60 : fetchRel bytes2scalar256Code 0x60 = some (.aluImm .add a0 sp 0x20, 2) := by decide
theorem by_at_62 : fetchRel bytes2scalar256Code 0x62 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem by_at_64 : fetchRel bytes2scalar256Code 0x64 = some (.alu .add a3 x0 (20 : Fin 32), 2) := by decide
theorem by_at_66 : fetchRel bytes2scalar256Code 0x66 = some (.aluImm .add (9 : Fin 32) sp 0x20, 2) := by decide
theorem by_at_68 : fetchRel bytes2scalar256Code 0x68 = some (.auipc ra 0x0, 4) := by decide
theorem by_at_6c : fetchRel bytes2scalar256Code 0x6C = some (.jalr ra ra 0xFFFFFDC2, 4) := by decide
theorem by_at_70 : fetchRel bytes2scalar256Code 0x70 = some (.alu .add a0 x0 sp, 2) := by decide
theorem by_at_72 : fetchRel bytes2scalar256Code 0x72 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem by_at_76 : fetchRel bytes2scalar256Code 0x76 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem by_at_78 : fetchRel bytes2scalar256Code 0x78 = some (.alu .add (8 : Fin 32) x0 sp, 2) := by decide
theorem by_at_7a : fetchRel bytes2scalar256Code 0x7A = some (.auipc ra 0x11000, 4) := by decide
theorem by_at_7e : fetchRel bytes2scalar256Code 0x7E = some (.jalr ra ra 0x762, 4) := by decide
theorem by_at_82 : fetchRel bytes2scalar256Code 0x82 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem by_at_84 : fetchRel bytes2scalar256Code 0x84 = some (.branch .beq (22 : Fin 32) x0 0x22, 4) := by decide
theorem by_at_88 : fetchRel bytes2scalar256Code 0x88 = some (.load .lw a0 (9 : Fin 32) 0x0, 2) := by decide
theorem by_at_8a : fetchRel bytes2scalar256Code 0x8A = some (.load .lw a1 (21 : Fin 32) 0x0, 4) := by decide
theorem by_at_8e : fetchRel bytes2scalar256Code 0x8E = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem by_at_92 : fetchRel bytes2scalar256Code 0x92 = some (.jalr ra ra 0x288, 4) := by decide
theorem by_at_96 : fetchRel bytes2scalar256Code 0x96 = some (.alu .add a2 x0 a1, 2) := by decide
theorem by_at_98 : fetchRel bytes2scalar256Code 0x98 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem by_at_9a : fetchRel bytes2scalar256Code 0x9A = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem by_at_9c : fetchRel bytes2scalar256Code 0x9C = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x4, 2) := by decide
theorem by_at_9e : fetchRel bytes2scalar256Code 0x9E = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem by_at_a0 : fetchRel bytes2scalar256Code 0xA0 = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem by_at_a2 : fetchRel bytes2scalar256Code 0xA2 = some (.branch .bne (22 : Fin 32) x0 0xFFFFFFE6, 4) := by decide
theorem by_at_a6 : fetchRel bytes2scalar256Code 0xA6 = some (.aluImm .srl a0 a2 0x1F, 4) := by decide
theorem by_at_aa : fetchRel bytes2scalar256Code 0xAA = some (.auipc ra 0xA000, 4) := by decide
theorem by_at_ae : fetchRel bytes2scalar256Code 0xAE = some (.jalr ra ra 0x690, 4) := by decide
theorem by_at_b2 : fetchRel bytes2scalar256Code 0xB2 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem by_at_b6 : fetchRel bytes2scalar256Code 0xB6 = some (.auipc ra 0xF000, 4) := by decide
theorem by_at_ba : fetchRel bytes2scalar256Code 0xBA = some (.jalr ra ra 0xFFFFF896, 4) := by decide
theorem by_at_be : fetchRel bytes2scalar256Code 0xBE = some (.aluImm .and a4 a0 0xFF, 4) := by decide
theorem by_at_c2 : fetchRel bytes2scalar256Code 0xC2 = some (.aluImm .add a0 sp 0x20, 2) := by decide
theorem by_at_c4 : fetchRel bytes2scalar256Code 0xC4 = some (.aluImm .add a1 x0 0x8, 2) := by decide
theorem by_at_c6 : fetchRel bytes2scalar256Code 0xC6 = some (.alu .add a2 x0 sp, 2) := by decide
theorem by_at_c8 : fetchRel bytes2scalar256Code 0xC8 = some (.aluImm .add a3 x0 0x8, 2) := by decide
theorem by_at_ca : fetchRel bytes2scalar256Code 0xCA = some (.aluImm .add (19 : Fin 32) sp 0x20, 4) := by decide
theorem by_at_ce : fetchRel bytes2scalar256Code 0xCE = some (.aluImm .add (9 : Fin 32) x0 0x8, 2) := by decide
theorem by_at_d0 : fetchRel bytes2scalar256Code 0xD0 = some (.auipc ra 0xA000, 4) := by decide
theorem by_at_d4 : fetchRel bytes2scalar256Code 0xD4 = some (.jalr ra ra 0x5AC, 4) := by decide
theorem by_at_d8 : fetchRel bytes2scalar256Code 0xD8 = some (.aluImm .add a0 sp 0x40, 2) := by decide
theorem by_at_da : fetchRel bytes2scalar256Code 0xDA = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem by_at_de : fetchRel bytes2scalar256Code 0xDE = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem by_at_e0 : fetchRel bytes2scalar256Code 0xE0 = some (.aluImm .add (8 : Fin 32) sp 0x40, 2) := by decide
theorem by_at_e2 : fetchRel bytes2scalar256Code 0xE2 = some (.auipc ra 0x11000, 4) := by decide
theorem by_at_e6 : fetchRel bytes2scalar256Code 0xE6 = some (.jalr ra ra 0x6FA, 4) := by decide
theorem by_at_ea : fetchRel bytes2scalar256Code 0xEA = some (.branch .beq (9 : Fin 32) x0 0x10, 2) := by decide
theorem by_at_ec : fetchRel bytes2scalar256Code 0xEC = some (.load .lw a0 (19 : Fin 32) 0x0, 4) := by decide
theorem by_at_f0 : fetchRel bytes2scalar256Code 0xF0 = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x4, 2) := by decide
theorem by_at_f2 : fetchRel bytes2scalar256Code 0xF2 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem by_at_f4 : fetchRel bytes2scalar256Code 0xF4 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem by_at_f6 : fetchRel bytes2scalar256Code 0xF6 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem by_at_f8 : fetchRel bytes2scalar256Code 0xF8 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFF4, 2) := by decide
theorem by_at_fa : fetchRel bytes2scalar256Code 0xFA = some (.aluImm .add a1 sp 0x40, 2) := by decide
theorem by_at_fc : fetchRel bytes2scalar256Code 0xFC = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem by_at_100 : fetchRel bytes2scalar256Code 0x100 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem by_at_102 : fetchRel bytes2scalar256Code 0x102 = some (.auipc ra 0x11000, 4) := by decide
theorem by_at_106 : fetchRel bytes2scalar256Code 0x106 = some (.jalr ra ra 0x742, 4) := by decide
theorem by_at_10a : fetchRel bytes2scalar256Code 0x10A = some (.load .lw ra sp 0x7C, 2) := by decide
theorem by_at_10c : fetchRel bytes2scalar256Code 0x10C = some (.load .lw (8 : Fin 32) sp 0x78, 2) := by decide
theorem by_at_10e : fetchRel bytes2scalar256Code 0x10E = some (.load .lw (9 : Fin 32) sp 0x74, 2) := by decide
theorem by_at_110 : fetchRel bytes2scalar256Code 0x110 = some (.load .lw (18 : Fin 32) sp 0x70, 2) := by decide
theorem by_at_112 : fetchRel bytes2scalar256Code 0x112 = some (.load .lw (19 : Fin 32) sp 0x6C, 2) := by decide
theorem by_at_114 : fetchRel bytes2scalar256Code 0x114 = some (.load .lw (20 : Fin 32) sp 0x68, 2) := by decide
theorem by_at_116 : fetchRel bytes2scalar256Code 0x116 = some (.load .lw (21 : Fin 32) sp 0x64, 2) := by decide
theorem by_at_118 : fetchRel bytes2scalar256Code 0x118 = some (.load .lw (22 : Fin 32) sp 0x60, 2) := by decide
theorem by_at_11a : fetchRel bytes2scalar256Code 0x11A = some (.aluImm .add sp sp 0x80, 2) := by decide
theorem by_at_11c : fetchRel bytes2scalar256Code 0x11C = some (.jalr x0 ra 0x0, 2) := by decide
end

abbrev BY : Word := BitVec.ofNat 32 bytes2scalar256Address

/-- Where `bytes2scalar` calls `borrowing_sub`, from its start `P`. -/
abbrev byBsub (P : Word) : Word := P + 0xFFFFF316

/-- The end of a subtraction round, from 0x96: keep the borrow, store the
difference, and advance the pointers and the count. -/
def bySubTail : List BInstr :=
  [.alu .add a2 x0 a1, .aluImm .add (9 : Fin 32) (9 : Fin 32) 4, .sw (8 : Fin 32) a0 0,
   .aluImm .add (21 : Fin 32) (21 : Fin 32) 4, .aluImm .add (8 : Fin 32) (8 : Fin 32) 4,
   .aluImm .add (22 : Fin 32) (22 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem bySubTail_end : blockEnd bytes2scalar256Code 0x96 bySubTail = some 0xA2 := by decide
end

set_option maxRecDepth 20000 in
theorem bySubTail_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock bySubTail (M, f)).1 = memStore32 M (f (8 : Fin 32) + 0) (f a0) ∧
    (runBlock bySubTail (M, f)).2 a2 = f a1 ∧
    (runBlock bySubTail (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 4 ∧
    (runBlock bySubTail (M, f)).2 (21 : Fin 32) = f (21 : Fin 32) + 4 ∧
    (runBlock bySubTail (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 4 ∧
    (runBlock bySubTail (M, f)).2 (22 : Fin 32) = f (22 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ a2 → q ≠ (9 : Fin 32) → q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (22 : Fin 32) →
      (runBlock bySubTail (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, bySubTail]
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

theorem bySubTail_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f (8 : Fin 32) + 0).toNat % 4 = 0) (hs : Sep (f (8 : Fin 32) + 0) 4 base len) :
    BlockOk base len bySubTail (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, bySubTail, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h, hs⟩

set_option maxRecDepth 20000 in
/-- **One round of the subtraction**, from 0x88: subtract limb `i` of the
order at `xp` and the borrow from limb `i` of the number at `np`, and store
the difference at limb `i` of the buffer at `D`. `borrowing_sub` also
writes the word below `sp`. -/
theorem by_sub_iter {M : Word → BitVec 8} {P F np xp D b : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x88 (reg n)) (hc : CodeIn M P bytes2scalar256Code) (hb : CodeIn M (byBsub P) borrowingSubCode)
    (hP : P.toNat % 2 = 0) (hi : i < 8) (hF : F.toNat % 4 = 0) (hnp : np.toNat % 4 = 0)
    (hxp : xp.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (byBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P bytes2scalar256Code.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P bytes2scalar256Code.length)
    (rsp : reg n sp = F) (rnp : reg n (9 : Fin 32) = np + BitVec.ofNat 32 (4 * i))
    (rxp : reg n (21 : Fin 32) = xp + BitVec.ofNat 32 (4 * i)) (rd : reg n (8 : Fin 32) = D + BitVec.ofNat 32 (4 * i))
    (rc : reg n (22 : Fin 32) = BitVec.ofNat 32 (8 - i)) (ra2 : reg n a2 = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < 8 then 0x88 else 0xA6) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' a2 = bsubB (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' (9 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (21 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (22 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (21 : Fin 32) →
        q ≠ (8 : Fin 32) → q ≠ (22 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc by_at_88 (off' := 0x8A) (by decide)
    (by rw [rnp, add_lit_zero]; exact aligned_add hnp (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.lw hc by_at_8a (off' := 0x8E) (by decide)
    (by rw [upd_ne (by decide) (by decide), rxp, add_lit_zero]; exact aligned_add hxp (by omega))
  rw [rnp, add_lit_zero] at u2
  have f0 : upd (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (21 : Fin 32) + 0)) a0 =
      memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by simp +decide [upd]
  have f1 : upd (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (21 : Fin 32) + 0)) a1 =
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
  obtain ⟨n3, c3, u3, a03, a13, sp3, fr3, mem3⟩ := u2'.bsubCall hc hb (even_at P hP 0xFFFFF316 (by decide))
    by_at_8e by_at_92 (by rw [BitVec.add_assoc, BitVec.add_assoc,
      show BitVec.ofNat 32 0x8E + ((0xFFFFF000 : Word) + 0x288) = 0xFFFFF316 by decide]) (even_at P hP (0x8E + 8) (by decide))
    (by rw [k2 sp (by decide) (by decide), rsp]) hF sFB
  rw [g2a0, g2a1, k2 a2 (by decide) (by decide), ra2] at a03 a13
  have hc3 : CodeIn n3.mem P bytes2scalar256Code := fun j hj => by
    rw [mem3 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n3 q = reg n q := fun q q0 q1 q2 q3 q4 qr =>
    by rw [fr3 q q0 q1 q2 q3 q4 qr, k2 q q0 q1]
  have ed : reg n3 (8 : Fin 32) + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rd, add_lit_zero]
  obtain ⟨n4, c4, u4⟩ := St.block bySubTail u3 hc3 bySubTail_end
    (bySubTail_ok (by rw [ed]; exact aligned_add hD (by omega)) (by rw [ed]; exact sDC))
  obtain ⟨em4, t2, tnp, txp, td, tc, tk⟩ := bySubTail_run (M := n3.mem) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [em4, ed, a03] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock bySubTail (n3.mem, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) hc3 sDC
  have ec : reg n4 (22 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) := by
    rw [g4, tc, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rc, cnt8_dec i hi]
  have hb4 : branchTaken .bne (reg n4 (22 : Fin 32)) (reg n4 x0) = decide (i + 1 < 8) := by
    rw [ec, u4'.zero]; exact cnt8_ne i hi
  have post : ∀ n5 : Machine, (∀ q, reg n5 q = reg n4 q) →
      reg n5 a2 = bsubB (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n5 sp = F ∧ reg n5 (9 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (21 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (8 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (22 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (21 : Fin 32) →
        q ≠ (8 : Fin 32) → q ≠ (22 : Fin 32) → reg n5 q = reg n q := fun n5 h5 => by
    refine ⟨by rw [h5, g4, t2, a13], by rw [h5, g4, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3],
      ?_, ?_, ?_, by rw [h5, ec], fun q q0 q1 q2 q3 q4 qr qnp qxp qd qc => ?_⟩
    · rw [h5, g4, tnp, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rnp, ptr4]
    · rw [h5, g4, txp, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rxp, ptr4]
    · rw [h5, g4, td, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rd, ptr4]
    · rw [h5, g4, tk q q2 qnp qxp qd qc, k3 q q0 q1 q2 q3 q4 qr]
  by_cases hl : i + 1 < 8
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x88 by_at_a2 (by decide) (by rw [hb4]; exact decide_eq_true hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      mem3, post n5 u5.regs⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0xA6 by_at_a2 (by decide) (by rw [hb4]; exact decide_eq_false hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      mem3, post n5 u5.regs⟩

set_option exponentiation.threshold 400 in
/-- **The subtraction**, from round `i` to its end at 0xA6: the buffer at
`D` gets the number at `np` minus the order at `xp`, and `a2` the borrow out
as a mask. -/
theorem by_sub_loop {P F np xp D : Word} {M0 : Word → BitVec 8} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hnp : np.toNat % 4 = 0) (hxp : xp.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 32 ≤ 2 ^ 32)
    (sFN : Sep (F + 0xFFFFFFFC) 4 np 32) (sFX : Sep (F + 0xFFFFFFFC) 4 xp 32) (sFD : Sep (F + 0xFFFFFFFC) 4 D 32)
    (sDN : Sep D 32 np 32) (sDX : Sep D 32 xp 32)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (byBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P bytes2scalar256Code.length)
    (sDB : Sep D 32 (byBsub P) borrowingSubCode.length) (sDC : Sep D 32 P bytes2scalar256Code.length) :
    ∀ m i, i + m + 1 = 8 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x88 (reg n) → CodeIn M P bytes2scalar256Code → CodeIn M (byBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 np i + 2 ^ (32 * i) * maskBit b = accV M0 xp i + accV M D i →
      reg n sp = F → reg n (9 : Fin 32) = np + BitVec.ofNat 32 (4 * i) →
      reg n (21 : Fin 32) = xp + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (22 : Fin 32) = BitVec.ofNat 32 (8 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0xA6 (reg n') ∧ CodeIn M' P bytes2scalar256Code ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 np 8 + 2 ^ (32 * 8) * maskBit (reg n' a2) = accV M0 xp 8 + accV M' D 8 ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (21 : Fin 32) →
          q ≠ (8 : Fin 32) → q ≠ (22 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 8 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x88 (reg n) → CodeIn M P bytes2scalar256Code → CodeIn M (byBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 np i + 2 ^ (32 * i) * maskBit b = accV M0 xp i + accV M D i →
      reg n sp = F → reg n (9 : Fin 32) = np + BitVec.ofNat 32 (4 * i) →
      reg n (21 : Fin 32) = xp + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (22 : Fin 32) = BitVec.ofNat 32 (8 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 8 then 0x88 else 0xA6) (reg n') ∧
        CodeIn M' P bytes2scalar256Code ∧ CodeIn M' (byBsub P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 np (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' a2) = accV M0 xp (i + 1) + accV M' D (i + 1) ∧
        reg n' sp = F ∧ reg n' (9 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (21 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (22 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (21 : Fin 32) →
          q ≠ (8 : Fin 32) → q ≠ (22 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    obtain ⟨n1, Mb, c1, u1, hMb, e2, esp, enp, exp, ed, ec, fr⟩ := by_sub_iter (i := i) s hc hb hP hi hF hnp hxp hD
      sFB sFC (sDC.sub (by omega)) rsp rnp rxp rd rc ra2
    have eA : memLoad32 M (np + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    have eN : memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFX.subR (by omega)) (sDX.subR (by omega))
    rw [eA, eN] at u1 e2
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb (byBsub P) borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb P bytes2scalar256Code := fun j hj => by
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
    have i7 : i = 7 := Nat.succ.inj hi
    subst i7
    obtain ⟨n1, M1, c1, u1, hc1, _, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step 7 (by decide) s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    exact ⟨n1, M1, c1, u1, hc1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    have hl : i + 1 < 8 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, enp, exp, ed, ec, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 hv1 sp1 enp exp ed ec rfl
    exact ⟨n', M', c1.trans c', u', hc', hf', hm', hv', sp', fun q q0 q1 q2 q3 q4 qr qnp qxp qd qc => by
      rw [fr' q q0 q1 q2 q3 q4 qr qnp qxp qd qc, fr q q0 q1 q2 q3 q4 qr qnp qxp qd qc]⟩

/-- One round of the copy, from 0xEC to the branch at 0xF8: copy the word at
`s3` to `s0`, and advance both and the count. -/
def byCp : List BInstr :=
  [.lw a0 (19 : Fin 32) 0, .aluImm .add (19 : Fin 32) (19 : Fin 32) 4, .sw (8 : Fin 32) a0 0,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 4, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem byCp_end : blockEnd bytes2scalar256Code 0xEC byCp = some 0xF8 := by decide
end

set_option maxRecDepth 20000 in
/-- **The copy**, from round `i` to its end at 0xFA: the 8 words at `X` go
to the 8 at `Y`. -/
theorem by_copy_loop {P X Y : Word} {M0 : Word → BitVec 8} (hX : X.toNat % 4 = 0) (hY : Y.toNat % 4 = 0)
    (sYX : Sep Y 32 X 32)
    (sYC : Sep Y 32 P bytes2scalar256Code.length) (hc : CodeIn M0 P bytes2scalar256Code) :
    ∀ m i, i + m + 1 = 8 → ∀ {n : Machine}, St (copyWords M0 Y X i) P n 0xEC (reg n) →
      reg n (19 : Fin 32) = X + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = Y + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = BitVec.ofNat 32 (8 - i) →
      ∃ n', Steps n n' ∧ St (copyWords M0 Y X 8) P n' 0xFA (reg n') ∧
        ∀ q, q ≠ a0 → q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  have hcw : ∀ i, i ≤ 8 → CodeIn (copyWords M0 Y X i) P bytes2scalar256Code := fun i hi j hj => by
    have h := (sYC.subR (c := j) (l := 1) (by omega)).sub (c := 0) (l := 4 * i) (by omega)
    rw [add_ofNat_zero] at h
    rw [copyWords_outside i h]; exact hc j hj
  have step : ∀ i, i < 8 → ∀ {n : Machine}, St (copyWords M0 Y X i) P n 0xEC (reg n) →
      reg n (19 : Fin 32) = X + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = Y + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = BitVec.ofNat 32 (8 - i) →
      ∃ n', Steps n n' ∧ St (copyWords M0 Y X (i + 1)) P n' (if i + 1 < 8 then 0xEC else 0xFA) (reg n') ∧
        reg n' (19 : Fin 32) = X + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = Y + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
    intro i hi n s r19 r8 r9
    have hz := s.zero
    obtain ⟨n1, c1, u1⟩ := St.block byCp s (hcw i (by omega)) byCp_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, byCp, upd, ↓reduceIte, and_true, true_and]
      rw [r19, r8, add_lit_zero, add_lit_zero]
      exact ⟨aligned_add hX (by omega), aligned_add hY (by omega), sYC.sub (c := 4 * i) (l := 4) (by omega)⟩)
    have sYi : Sep Y (4 * i) (X + BitVec.ofNat 32 (4 * i)) 4 := by
      have h := (sYX.subR (c := 4 * i) (l := 4) (by omega)).sub (c := 0) (l := 4 * i) (by omega)
      rwa [add_ofNat_zero] at h
    have e1 : (runBlock byCp (copyWords M0 Y X i, reg n)).1 = copyWords M0 Y X (i + 1) := by
      simp +decide only [runBlock, BInstr.run, byCp, upd, ↓reduceIte]
      rw [r19, r8, add_lit_zero, add_lit_zero, copyWords_load_sep sYi]; rfl
    have R : ∀ q, reg n1 q = (runBlock byCp (copyWords M0 Y X i, reg n)).2 q := u1.regs
    have v19 : reg n1 (19 : Fin 32) = X + BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [R]; simp +decide only [runBlock, BInstr.run, byCp, upd_app, ↓reduceIte]
      rw [r19, ev_add, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc, Nat.mul_succ]
    have v8 : reg n1 (8 : Fin 32) = Y + BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [R]; simp +decide only [runBlock, BInstr.run, byCp, upd_app, ↓reduceIte]
      rw [r8, ev_add, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc, Nat.mul_succ]
    have v9 : reg n1 (9 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) := by
      rw [R]; simp +decide only [runBlock, BInstr.run, byCp, upd_app, ↓reduceIte]
      rw [r9, ev_add, cnt8_dec i hi]
    have K : ∀ q, q ≠ a0 → q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n1 q = reg n q :=
      fun q h0 h19 h8 h9 => by
        rw [R]; refine runBlock_reg _ _ _ q hz ?_
        simp only [byCp, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h19, h8, h9]
    have u1' : St (copyWords M0 Y X (i + 1)) P n1 0xF8 (reg n1) := ⟨u1.pc, by rw [u1.mem, e1], fun _ => rfl⟩
    have hb : branchTaken .bne (reg n1 (9 : Fin 32)) (reg n1 x0) = decide (i + 1 < 8) := by
      rw [v9, u1'.zero]; exact cnt8_ne i hi
    by_cases hl : i + 1 < 8
    · obtain ⟨n2, d2, u2⟩ := u1'.taken (hcw (i + 1) (by omega)) 0xEC by_at_f8 (by decide)
        (by rw [hb]; exact decide_eq_true hl)
      exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, by rw [u2.regs, v19],
        by rw [u2.regs, v8], by rw [u2.regs, v9], fun q h0 h19 h8 h9 => by rw [u2.regs, K q h0 h19 h8 h9]⟩
    · obtain ⟨n2, d2, u2⟩ := u1'.notTaken (hcw (i + 1) (by omega)) 0xFA by_at_f8 (by decide)
        (by rw [hb]; exact decide_eq_false hl)
      exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, by rw [u2.regs, v19],
        by rw [u2.regs, v8], by rw [u2.regs, v9], fun q h0 h19 h8 h9 => by rw [u2.regs, K q h0 h19 h8 h9]⟩
  intro m
  induction m with
  | zero =>
    intro i hi n s r19 r8 r9
    have i7 : i = 7 := Nat.succ.inj hi
    subst i7
    obtain ⟨n1, c1, u1, _, _, _, K⟩ := step 7 (by decide) s r19 r8 r9
    exact ⟨n1, c1, u1, K⟩
  | succ m ih =>
    intro i hi n s r19 r8 r9
    have hl : i + 1 < 8 := sel_lt1 hi
    obtain ⟨n1, c1, u1, v19, v8, v9, K⟩ := step i (by omega) s r19 r8 r9
    rw [ite_eq_left hl] at u1
    obtain ⟨n', c', u', K'⟩ := ih (i + 1) (sel_succ hi) u1 v19 v8 v9
    exact ⟨n', c1.trans c', u', fun q h0 h19 h8 h9 => by rw [K' q h0 h19 h8 h9, K q h0 h19 h8 h9]⟩


abbrev BYO : Word := BitVec.ofNat 32 b2sOrder256Address

/-- The code `bytes2scalar::<NistP256>` runs, its callees', and the copy of
the order that it compares against, with that copy's value and leading zero
bits. -/
structure BYEnv (M : Word → BitVec 8) : Prop where
  cod : CodeIn M BY bytes2scalar256Code
  lz : CodeIn M (BitVec.ofNat 32 leadingZerosAddress) leadingZerosCode
  pan : PanicCode M
  exu : CodeIn M (BitVec.ofNat 32 expectUsizeAddress) expectUsizeCode
  fc : FCEnv M
  bsb : CodeIn M (BitVec.ofNat 32 borrowingSubAddress) borrowingSubCode
  bb : CodeIn M (BitVec.ofNat 32 blackBoxU8Address) blackBoxU8Code
  cn : CodeIn M (BitVec.ofNat 32 choiceNotAddress) choiceNotCode
  sca : CodeIn M (BitVec.ofNat 32 sliceCtAssignAddress) sliceCtAssignCode
  ord : accV M BYO 8 = C3.p256.n
  ordLz : lzLimbs M BYO 8 = 0

abbrev byPs : List (Fin 32 × Word) :=
  [(ra, 0x7C), ((8 : Fin 32), 0x78), ((9 : Fin 32), 0x74), ((18 : Fin 32), 0x70), ((19 : Fin 32), 0x6C),
   ((20 : Fin 32), 0x68), ((21 : Fin 32), 0x64), ((22 : Fin 32), 0x60)]

def byA : List BInstr :=
  [.alu .add (19 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .lui (21 : Fin 32) 0x3FCC4000,
   .aluImm .add (21 : Fin 32) (21 : Fin 32) 0x268, .aluImm .add a1 x0 0x8, .alu .add a0 x0 (21 : Fin 32),
   .aluImm .add (22 : Fin 32) x0 0x8]
def byB : List BInstr :=
  [.aluImm .add a1 x0 0x100, .alu .sub (20 : Fin 32) a1 a0, .aluImm .and a0 (20 : Fin 32) 0x7,
   .aluImm .srl a1 (20 : Fin 32) 0x3, .alu .sltu a0 x0 a0, .alu .add a0 a0 a1]
def byC : List BInstr := [.sb sp x0 0x40, .sw sp a0 0x44, .aluImm .add a0 sp 0x40]
def byM : List BInstr := [.alu .add a2 x0 a0, .aluImm .add a0 x0 0x20]
def byD : List BInstr :=
  [.aluImm .add a0 sp 0x20, .alu .add a1 x0 (19 : Fin 32), .alu .add a3 x0 (20 : Fin 32),
   .aluImm .add (9 : Fin 32) sp 0x20]
def byE : List BInstr :=
  [.alu .add a0 x0 sp, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0, .alu .add (8 : Fin 32) x0 sp]
def byF : List BInstr :=
  [.aluImm .add a0 sp 0x20, .aluImm .add a1 x0 0x8, .alu .add a2 x0 sp, .aluImm .add a3 x0 0x8,
   .aluImm .add (19 : Fin 32) sp 0x20, .aluImm .add (9 : Fin 32) x0 0x8]
def byG : List BInstr :=
  [.aluImm .add a0 sp 0x40, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0, .aluImm .add (8 : Fin 32) sp 0x40]
def byH : List BInstr := [.aluImm .add a1 sp 0x40, .aluImm .add a2 x0 0x20, .alu .add a0 x0 (18 : Fin 32)]

section
set_option maxRecDepth 20000
theorem bySave_end : blockEnd bytes2scalar256Code 2 (saveBlock byPs) = some 0x12 := by decide
theorem byA_end : blockEnd bytes2scalar256Code 0x12 byA = some 0x24 := by decide
theorem byB_end : blockEnd bytes2scalar256Code 0x2C byB = some 0x42 := by decide
theorem byC_end : blockEnd bytes2scalar256Code 0x42 byC = some 0x4A := by decide
theorem byM_end : blockEnd bytes2scalar256Code 0x52 byM = some 0x58 := by decide
theorem byD_end : blockEnd bytes2scalar256Code 0x60 byD = some 0x68 := by decide
theorem byE_end : blockEnd bytes2scalar256Code 0x70 byE = some 0x7A := by decide
theorem byF_end : blockEnd bytes2scalar256Code 0xC2 byF = some 0xD0 := by decide
theorem byG_end : blockEnd bytes2scalar256Code 0xD8 byG = some 0xE2 := by decide
theorem byH_end : blockEnd bytes2scalar256Code 0xFA byH = some 0x102 := by decide
theorem byRestore_end : blockEnd bytes2scalar256Code 0x10A (restoreBlock byPs) = some 0x11A := by decide
end

theorem by_res {M : Word → BitVec 8} {F : Word} :
    (memStore32 (memStore8 M (F + 0x40) 0) (F + 0x44) 0x20) (F + 0x40) = 0 ∧
      memLoad32 (memStore32 (memStore8 M (F + 0x40) 0) (F + 0x44) 0x20) (F + 0x40 + 4) = 0x20 := by
  have e : F + 0x40 + 4 = F + 0x44 := by rw [BitVec.add_assoc]; rfl
  refine ⟨?_, by rw [e, memLoad32_store32_same]⟩
  rw [memStore32_get_sep (by
    have := sep_offsets F (c := 0x44) (n := 4) (d := 0x40) (k := 1) (by omega) (by omega) (by omega)
    exact this), memStore8_same]

theorem by_foldl_lt : ∀ (l : List Nat) (acc k : Nat), (∀ x ∈ l, x < 256) → acc < 256 ^ k →
    l.foldl (fun a x => a * 256 + x) acc < 256 ^ (k + l.length)
  | [], acc, k, _, h => by rw [List.foldl_nil, List.length_nil, Nat.add_zero]; exact h
  | x :: l, acc, k, hl, h => by
    rw [List.foldl_cons, List.length_cons, show k + (l.length + 1) = (k + 1) + l.length by omega]
    have hx := hl x List.mem_cons_self
    refine by_foldl_lt l _ (k + 1) (fun y hy => hl y (List.mem_cons_of_mem _ hy)) ?_
    rw [Nat.pow_succ]
    generalize 256 ^ k = P at h ⊢
    omega

theorem by_beNat_lt (M : Word → BitVec 8) (p : Word) (n : Nat) : beNat (memBytes M p n) < 2 ^ (8 * n) := by
  have h := by_foldl_lt (memBytes M p n) 0 0 (fun x hx => by
    unfold memBytes at hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact (M (p + BitVec.ofNat 32 i)).isLt) (by decide)
  rw [Nat.zero_add, memBytes_length, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at h
  exact h

theorem p256n_gt : 2 ^ 255 < C3.p256.n := by decide
theorem p256n_lt : C3.p256.n < 2 ^ 256 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `bytes2scalar::<NistP256>`**: for the 32 bytes at `b`,
read as a big-endian number `x`, it writes to `out` the 8 limbs of `x mod
n`. It returns with `sp` and the callee-saved registers restored and writes
only `out` and the 0xE0 bytes of stack below `sp`. -/
theorem bytes2scalar256_correct (m : Machine) {sp0 out b retAddr : Word} (E : BYEnv m.mem)
    (hpc : m.pc = BY) (ha0 : reg m a0 = out) (ha1 : reg m a1 = b)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hsa : sp0.toNat % 16 = 0) (hsl : 0x3FC80000 + 0x200 ≤ sp0.toNat) (hsw : sp0.toNat ≤ dramEnd)
    (how : out.toNat + 32 ≤ dramEnd) (hoa : out.toNat % 4 = 0) (hbn : b.toNat + 32 < 2 ^ 32)
    (sBG : Sep b 32 (sp0 + 0xFFFFFF20) 0xE0) (sOG : Sep out 32 (sp0 + 0xFFFFFF20) 0xE0)
    (sGO : Sep (sp0 + 0xFFFFFF20) 0xE0 BYO 32) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      accV m'.mem out 8 = beNat (memBytes m.mem b 32) % C3.p256.n ∧
      ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF20 = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFF80 = F := ⟨_, rfl⟩
  rw [hG] at sBG sOG sGO ⊢
  have hGn : G.toNat = sp0.toNat - 0xE0 := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF20 : Word).toNat = 2 ^ 32 - 0xE0 from rfl]; have := sp0.isLt; omega
  have hGF : G + BitVec.ofNat 32 0x60 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGc : ∀ c, c ≤ 0xE0 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold dramEnd at hsw; omega
  have hFn : F.toNat = G.toNat + 0x60 := by rw [← hGF]; exact hGc _ (by decide)
  have hFa : F.toNat % 4 = 0 := by omega
  have hGw : ∀ c, c ≤ 0xE0 → (G + BitVec.ofNat 32 c).toNat + 4 * 8 < 2 ^ 32 := fun c hc => by
    rw [hGc c hc]; unfold dramEnd at hsw; omega
  have hOw : out.toNat + 4 * 8 < 2 ^ 32 := by unfold dramEnd at how; omega
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x60 + k) := fun k => by
    rw [← hGF, add_ofNat_assoc]
  have eFS : F + 0x80 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0xE0 → d + k ≤ 0xE0 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have inG : ∀ {c l : Nat} {x : Word}, Sep G 0xE0 x 1 → c + l ≤ 0xE0 → Sep (G + BitVec.ofNat 32 c) l x 1 :=
    fun hx h => (hx.symm.subR h).symm
  have hiG : ∀ x : Word, dramEnd ≤ x.toNat → Sep G 0xE0 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hiO : ∀ x : Word, dramEnd ≤ x.toNat → Sep out 32 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have sOcode : ∀ {a : Word} {len : Nat}, dramEnd ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 → Sep out 32 a len :=
    fun h1 h2 => sep_of_le (by omega) h2
  have hiC : ∀ {c l : Nat} {a : Word} {len : Nat}, c + l ≤ 0xE0 → dramEnd ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 →
      Sep (G + BitVec.ofNat 32 c) l a len := fun h h1 h2 => sep_of_le (by rw [hGc _ (by omega)]; omega) h2
  have cd : ∀ {M' : Word → BitVec 8} {c : Word} {code : List Nat}, CodeIn m.mem c code → dramEnd ≤ c.toNat →
      c.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep G 0xE0 x 1 → M' x = m.mem x) → CodeIn M' c code :=
    fun hc h1 h2 hM i hi' => by
      rw [hM _ (hiG _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]; exact hc i hi'
  have pcd : ∀ {M' : Word → BitVec 8}, (∀ x, Sep G 0xE0 x 1 → M' x = m.mem x) → PanicCode M' :=
    fun hM p hp => by
      have hb := panicFns_hi p hp
      exact cd (E.pan p hp) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hb.1)
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) hM
  have hBSn : BY.toNat = (img% bytes2scalar256Address) := by decide
  have hc := E.cod
  have st0 : St m.mem BY m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hc by_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF80) sp = F := by
    simp +decide only [upd, ↓reduceIte]; rw [hsp]; exact hF
  have slotO : ∀ o : Word, F + o = F + BitVec.ofNat 32 o.toNat := fun o => by rw [ofNat_toNat_self]
  have slotC : ∀ o : Word, o.toNat ≤ 0x7C → Sep (F + o) 4 BY bytes2scalar256Code.length := fun o ho =>
    sep_of_le (by rw [BitVec.toNat_add, hBSn]; have := Nat.mod_le (F.toNat + o.toNat) (2 ^ 32); unfold dramEnd at hsw
                  omega) (by rw [hBSn]; decide)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock byPs) u1 hc bySave_end (saveBlock_ok _ byPs _ fun q hq => by
      rw [sp1]
      simp only [byPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add hFa (by decide), slotC _ (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF80)) byPs = Ms :=
    ⟨_, rfl⟩
  rw [hMs] at u2
  have IMs : ∀ x, Sep G 0xE0 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside byPs fun q hq => by
      simp only [byPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (rw [slotO, eFk]; exact inG hx (by decide))
  have slots : ∀ r o, (r, o) ∈ byPs → memLoad32 Ms (F + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [byPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot byPs _ hm (by
      simp only [byPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;> decide), upd_ne (by
        simp only [byPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ <;> decide) hr]
  have hc2 : CodeIn Ms BY bytes2scalar256Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IMs
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  obtain ⟨m3, c3, u3⟩ := St.block byA u2.self hc2 byA_end (by simp only [BlockOk, BInstr.ok, byA, and_self])
  have R3 : ∀ q, reg m3 q = (runBlock byA (Ms, reg m2)).2 q := u3.regs
  have u3' : St Ms BY m3 0x24 (reg m3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  have K3 : ∀ q, q.val ∉ [10, 11, 18, 19, 21, 22] → reg m3 q = reg m2 q := fun q hq => by
    rw [R3]; refine runBlock_reg _ _ _ q u2.self.zero ?_
    simp only [byA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have v3 : reg m3 (19 : Fin 32) = b ∧ reg m3 (18 : Fin 32) = out ∧
      reg m3 (21 : Fin 32) = BYO ∧ reg m3 a1 = BitVec.ofNat 32 8 ∧ reg m3 a0 = BYO ∧
      reg m3 (22 : Fin 32) = BitVec.ofNat 32 8 := by
    simp +decide only [R3, runBlock, BInstr.run, byA, upd_app, ↓reduceIte]
    rw [r2 a1 (by decide), r2 a0 (by decide), ha0, ha1, u2.self.zero]
    exact ⟨zw _, zw _, trivial⟩
  obtain ⟨v319, v318, v321, v3a1, v3a0, v322⟩ := v3
  have hLZn : (BitVec.ofNat 32 leadingZerosAddress : Word).toNat = leadingZerosAddress := by decide
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3'.callRa hc2 by_at_24 by_at_28 (cb := BitVec.ofNat 32 leadingZerosAddress)
    (by decide) (by decide)
  have r4 := PEnv.reg1 regs4 u3'.zero
  have eFm : F + 0xFFFFFFE0 = G + BitVec.ofNat 32 0x40 := by rw [← hGF, BitVec.add_assoc]; rfl
  have sp3 : reg m3 sp = F := by rw [K3 sp (by decide), sp2]
  have sLZ : Sep (G + BitVec.ofNat 32 0x40) 0x20 (BitVec.ofNat 32 leadingZerosAddress) leadingZerosCode.length :=
    hiC (by decide) (by rw [hLZn]; decide) (by rw [hLZn]; decide)
  obtain ⟨m5, c5, pc5, sp5, a05, K5, fr5⟩ := leadingZeros_correct m4 (P := BitVec.ofNat 32 leadingZerosAddress)
    (sp0 := F) (p := BYO) (n := 8) (retAddr := BY + BitVec.ofNat 32 (0x24 + 8))
    (by rw [mem4]; exact cd E.lz (by rw [hLZn]; decide) (by rw [hLZn]; decide) IMs) pc4
    (by rw [r4 sp (by decide), sp3]) (by rw [r4 a0 (by decide), v3a0]) (by rw [r4 a1 (by decide), v3a1]) (by decide)
    (by decide) (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at BY (by decide) _ (by decide))) hFa
    (by rw [eFm]; exact sLZ)
    (by rw [eFm]; exact (sGO.sub (c := 0x40) (l := 0x20) (by decide)).symm)
  have IM5 : ∀ x, Sep G 0xE0 x 1 → m5.mem x = m.mem x := fun x hx => by
    rw [fr5 x (by rw [eFm]; exact inG hx (by decide)), mem4, IMs x hx]
  have hz0 : lzLimbs m4.mem BYO 8 = 0 := by
    rw [mem4, lz_congr (M := m.mem) (M' := Ms) 8 fun i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact IMs _ (sGO.subR (c := 4 * i + j) (l := 1) (by omega))]
    exact E.ordLz
  rw [hz0] at a05
  have hc5 : CodeIn m5.mem BY bytes2scalar256Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IM5
  have u5 : St m5.mem BY m5 0x2C (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have K5' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m5 q = reg m3 q := fun q hq => by
    rw [K5 q (by revert hq; revert q; decide), r4 q (by revert hq; revert q; decide)]
  obtain ⟨m6, c6, u6⟩ := St.block byB u5 hc5 byB_end (by simp only [BlockOk, BInstr.ok, byB, and_self])
  have R6 : ∀ q, reg m6 q = (runBlock byB (m5.mem, reg m5)).2 q := u6.regs
  have u6' : St m5.mem BY m6 0x42 (reg m6) := ⟨u6.pc, by rw [u6.mem]; rfl, fun _ => rfl⟩
  have K6 : ∀ q, q.val ∉ [10, 11, 20] → reg m6 q = reg m5 q := fun q hq => by
    rw [R6]; refine runBlock_reg _ _ _ q u5.zero ?_
    simp only [byB, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have v6 : reg m6 (20 : Fin 32) = 0x100 ∧ reg m6 a0 = 0x20 := by
    simp +decide only [R6, runBlock, BInstr.run, byB, upd_app, ↓reduceIte]
    rw [a05, u5.zero]; decide
  obtain ⟨v620, v6a0⟩ := v6
  have sp6 : reg m6 sp = F := by rw [K6 sp (by decide), sp5]
  obtain ⟨m7, c7, u7⟩ := St.block byC u6' hc5 byC_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, byC, and_true]
    rw [sp6]
    have h4 := (slotC 0x40 (by decide)).sub (c := 0) (l := 1) (by decide)
    rw [add_ofNat_zero] at h4
    exact ⟨h4, aligned_add hFa (by decide), slotC _ (by decide)⟩)
  obtain ⟨Mr, hMr⟩ : ∃ Mr, memStore32 (memStore8 m5.mem (F + 0x40) 0) (F + 0x44) 0x20 = Mr := ⟨_, rfl⟩
  have e7 : (runBlock byC (m5.mem, reg m6)).1 = Mr := by
    simp +decide only [runBlock, BInstr.run, byC]
    rw [sp6, v6a0, u6'.zero, ← hMr]; rfl
  have R7 : ∀ q, reg m7 q = (runBlock byC (m5.mem, reg m6)).2 q := u7.regs
  have u7' : St Mr BY m7 0x4A (reg m7) := ⟨u7.pc, by rw [u7.mem, e7], fun _ => rfl⟩
  have K7 : ∀ q, q ≠ a0 → reg m7 q = reg m6 q := fun q h0 => by
    rw [R7]; refine runBlock_reg _ _ _ q u6.zero ?_
    simp only [byC, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0]
  have v7 : reg m7 a0 = F + 0x40 := by
    simp +decide only [R7, runBlock, BInstr.run, byC, upd_app, ↓reduceIte]; rw [sp6, ev_add]
  have IMr : ∀ x, Sep G 0xE0 x 1 → Mr x = m.mem x := fun x hx => by
    have h8 : Sep (F + 0x44) 4 x 1 := by
      rw [show (0x44 : Word) = BitVec.ofNat 32 0x44 from rfl, eFk]; exact inG hx (by decide)
    have h4 : x ≠ F + 0x40 := fun e => by
      have h := inG (c := 0x60 + 0x40) (l := 1) hx (by decide)
      rw [← eFk] at h
      exact h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e]; rfl)
    rw [← hMr, memStore32_get_sep h8, memStore8_ne h4, IM5 x hx]
  have hc7 : CodeIn Mr BY bytes2scalar256Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IMr
  have hEXn : (BitVec.ofNat 32 expectUsizeAddress : Word).toNat = expectUsizeAddress := by decide
  obtain ⟨m8, c8, pc8, mem8, regs8⟩ := u7'.callRa hc7 by_at_4a by_at_4e (cb := BitVec.ofNat 32 expectUsizeAddress)
    (by decide) (by decide)
  have r8 := PEnv.reg1 regs8 u7'.zero
  have sp7 : reg m7 sp = F := by rw [K7 sp (by decide), sp6]
  obtain ⟨m9, c9, pc9, a09, mem9, K9⟩ := (expectUsize_correct m8 (p := F + 0x40)
    (retAddr := BY + BitVec.ofNat 32 (0x4A + 8)) (by rw [mem8]; exact pcd IMr)
    (by rw [mem8]; exact cd E.exu (by rw [hEXn]; decide) (by rw [hEXn]; decide) IMr) pc8
    (by rw [r8 a0 (by decide), v7]) (aligned_add hFa (k := 0x40) (by decide))
    (by rw [regs8]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at BY (by decide) _ (by decide)))
    (by rw [r8 sp (by decide), sp7]; exact ⟨hFa, by omega, by omega⟩)).1 (by rw [mem8, ← hMr]; exact by_res.1)
  rw [mem8] at a09 mem9
  have a09' : reg m9 a0 = 0x20 := by rw [a09, ← hMr]; exact by_res.2
  have u9 : St Mr BY m9 0x52 (reg m9) := ⟨by rw [pc9], mem9, fun _ => rfl⟩
  have K9' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ ra → reg m9 q = reg m7 q := fun q h0 h1 hr => by
    rw [K9 q h0 h1, r8 q hr]
  obtain ⟨m10, c10, u10⟩ := St.block byM u9 hc7 byM_end (by simp only [BlockOk, BInstr.ok, byM, and_self])
  have R10 : ∀ q, reg m10 q = (runBlock byM (Mr, reg m9)).2 q := u10.regs
  have u10' : St Mr BY m10 0x58 (reg m10) := ⟨u10.pc, by rw [u10.mem]; rfl, fun _ => rfl⟩
  have v10 : reg m10 a2 = 0x20 ∧ reg m10 a0 = 0x20 := by
    simp +decide only [R10, runBlock, BInstr.run, byM, upd_app, ↓reduceIte]; rw [u9.zero, a09']; decide
  obtain ⟨n10, d10, w10⟩ := u10'.notTaken hc7 0x5C by_at_58 (by decide) (by
    simp only [branchTaken]; rw [v10.1, v10.2]; decide)
  obtain ⟨n10', d10', w10'⟩ := w10.aluImm hc7 by_at_5c (off' := 0x60) (by decide)
  have K10 : ∀ q, q ≠ a0 → q ≠ a2 → reg n10' q = reg m9 q := fun q h0 h2 => by
    rw [w10'.regs, updz w10.zero h2, R10]; refine runBlock_reg _ _ _ q u9.zero ?_
    simp only [byM, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h2]
  have v10a2 : reg n10' a2 = BitVec.ofNat 32 32 := by
    rw [w10'.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [w10.zero]; rfl
  have u10 : St Mr BY n10' 0x60 (reg n10') := w10'.self
  obtain ⟨X, hX⟩ : ∃ X, G + BitVec.ofNat 32 0x80 = X := ⟨_, rfl⟩
  have eFX : F + 0x20 = X := by rw [← hX, show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, eFk]
  have hXn : X.toNat = G.toNat + 0x80 := by rw [← hX]; exact hGc _ (by decide)
  obtain ⟨m11, c11, u11⟩ := St.block byD u10 hc7 byD_end (by simp only [BlockOk, BInstr.ok, byD, and_self])
  have R11 : ∀ q, reg m11 q = (runBlock byD (Mr, reg n10')).2 q := u11.regs
  have u11' : St Mr BY m11 0x68 (reg m11) := ⟨u11.pc, by rw [u11.mem]; rfl, fun _ => rfl⟩
  have K11 : ∀ q, q.val ∉ [9, 10, 11, 13] → reg m11 q = reg n10' q := fun q hq => by
    rw [R11]; refine runBlock_reg _ _ _ q u10.zero ?_
    simp only [byD, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have K10' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ (20 : Fin 32) →
      reg n10' q = reg m3 q := fun q hq h20 => by
    rw [K10 q (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      K9' q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      K7 q (by revert hq; revert q; decide), K6 q (by intro h; revert h; revert hq h20; revert q; decide), K5' q hq]
  have sp10 : reg n10' sp = F := by
    rw [K10 sp (by decide) (by decide), K9' sp (by decide) (by decide) (by decide), sp7]
  have v11 : reg m11 a0 = X ∧ reg m11 a1 = b ∧ reg m11 a3 = BitVec.ofNat 32 256 ∧ reg m11 (9 : Fin 32) = X := by
    simp +decide only [R11, runBlock, BInstr.run, byD, upd_app, ↓reduceIte]
    rw [sp10, K10' 19 (by decide) (by decide), v319,
      K10 20 (by decide) (by decide), K9' 20 (by decide) (by decide) (by decide), K7 20 (by decide), v620]
    simp only [ev_add, eFX, zw, true_and, and_true]
    rfl
  obtain ⟨v11a0, v11a1, v11a3, v119⟩ := v11
  have v11a2 : reg m11 a2 = BitVec.ofNat 32 32 := by rw [K11 a2 (by decide), v10a2]
  obtain ⟨m12, c12, pc12, mem12, regs12⟩ := u11'.callRa hc7 by_at_68 by_at_6c (cb := FC) (by decide) (by decide)
  have r12 := PEnv.reg1 regs12 u11'.zero
  have hFCn : FC.toNat = fromBeSliceTrunc8Address := by decide
  have eF60 : F + 0xFFFFFFA0 = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
  have EF : FCEnv m12.mem := by
    rw [mem12]
    exact ⟨cd E.fc.cod (by rw [hFCn]; decide) (by rw [hFCn]; decide) IMr,
      cd E.fc.ms (by decide) (by decide) IMr, cd E.fc.fl (by decide) (by decide) IMr,
      cd E.fc.cs (by decide) (by decide) IMr, cd E.fc.cb (by decide) (by decide) IMr⟩
  have sBF : Sep b 32 (F + 0xFFFFFFA0) 0x60 := by
    rw [eF60]; have h := sBG.subR (c := 0) (l := 0x60) (by decide); rwa [add_ofNat_zero] at h
  have sXF : Sep X 32 (F + 0xFFFFFFA0) 0x60 := by
    rw [eF60, ← hX]; have h := offs (c := 0x80) (n := 32) (d := 0) (k := 0x60) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at h
  have sp11 : reg m11 sp = F := by rw [K11 sp (by decide), sp10]
  obtain ⟨m13, c13, pc13, sp13, K13, val13, fr13⟩ := fromBeSliceTrunc8_correct m12 (sp0 := F) (out := X) (b := b)
    (n := 32) (bits := 256) (retAddr := BY + BitVec.ofNat 32 (0x68 + 8)) EF pc12
    (by rw [r12 a0 (by decide), v11a0]) (by rw [r12 a1 (by decide), v11a1]) (by rw [r12 a2 (by decide), v11a2])
    (by rw [r12 a3 (by decide), v11a3]) (by rw [regs12]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at BY (by decide) _ (by decide))) (by rw [r12 sp (by decide), sp11]) (by decide)
    (Nat.le_refl _) hbn hFa (by omega) (by unfold dramEnd at hsw; omega) (by unfold dramEnd at hsw; omega)
    (by omega) sBF sXF
  rw [show (256 : Nat) / 8 = 32 from rfl, Nat.min_self, BitVec.add_sub_cancel, mem12] at val13
  have xval : accV m13.mem X 8 = beNat (memBytes m.mem b 32) := by
    rw [val13]
    exact congrArg beNat (memBytes_congr fun i hi =>
      IMr _ (by have h := (sBG.sub (c := i) (l := 1) (by omega)).symm; exact h))
  have IM13 : ∀ x, Sep G 0xE0 x 1 → m13.mem x = m.mem x := fun x hx => by
    rw [fr13 x (by rw [eF60]; have h := inG (c := 0) (l := 0x60) hx (by decide); rwa [add_ofNat_zero] at h)
      (by rw [← hX]; exact inG hx (by decide)), mem12, IMr x hx]
  have hc13 : CodeIn m13.mem BY bytes2scalar256Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IM13
  have u13 : St m13.mem BY m13 0x70 (reg m13) := ⟨by rw [pc13], rfl, fun _ => rfl⟩
  have K13' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m13 q = reg m11 q :=
    fun q hq => by rw [K13 q (by revert hq; revert q; decide), r12 q (by revert hq; revert q; decide)]
  obtain ⟨m14, c14, u14⟩ := St.block byE u13 hc13 byE_end (by simp only [BlockOk, BInstr.ok, byE, and_self])
  have R14 : ∀ q, reg m14 q = (runBlock byE (m13.mem, reg m13)).2 q := u14.regs
  have u14' : St m13.mem BY m14 0x7A (reg m14) := ⟨u14.pc, by rw [u14.mem]; rfl, fun _ => rfl⟩
  have K14 : ∀ q, q.val ∉ [8, 10, 11, 12] → reg m14 q = reg m13 q := fun q hq => by
    rw [R14]; refine runBlock_reg _ _ _ q u13.zero ?_
    simp only [byE, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have v14 : reg m14 a0 = F ∧ reg m14 a2 = BitVec.ofNat 32 (4 * 8) ∧ reg m14 a1 = 0 ∧ reg m14 (8 : Fin 32) = F := by
    simp +decide only [R14, runBlock, BInstr.run, byE, upd_app, ↓reduceIte]
    rw [sp13, u13.zero]; exact ⟨zw _, trivial, trivial, zw _⟩
  obtain ⟨v14a0, v14a2, v14a1, v148⟩ := v14
  have hMSn : (BitVec.ofNat 32 memsetAddress : Word).toNat = memsetAddress := by decide
  obtain ⟨m15, c15, u15, _, k15⟩ := u14'.memsetW (B := BitVec.ofNat 32 memsetAddress) (w := 8) (dst := F)
    (by decide) hc13 (cd E.fc.ms (by rw [hMSn]; decide) (by rw [hMSn]; decide) IM13) by_at_7a by_at_7e (by decide)
    (by decide) (by decide) (by rw [← hGF]; exact hGw _ (by decide)) (by decide) hFa
    (by rw [← hGF]; exact hiC (by decide) (by rw [hMSn]; decide) (by rw [hMSn]; decide)) v14a0 v14a1 v14a2
  obtain ⟨Mz, hMz⟩ : ∃ Mz, fillWords m13.mem F 0 8 = Mz := ⟨_, rfl⟩
  rw [hMz] at u15
  have IMz : ∀ x, Sep G 0xE0 x 1 → Mz x = m.mem x := fun x hx => by
    rw [← hMz, fillWords_outside 8 (by rw [← hGF]; exact inG hx (by decide)), IM13 x hx]
  have hcz : CodeIn Mz BY bytes2scalar256Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IMz
  obtain ⟨m16, d16, u16⟩ := u15.aluImm hcz by_at_82 (off' := 0x84) (by decide)
  have K15 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m15 q = reg m11 q := fun q hq => by
    rw [k15 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      K14 q (by intro h; revert h; revert hq; revert q; decide), K13' q (by revert hq; revert q; decide)]
  have v1522 : reg m15 (22 : Fin 32) = BitVec.ofNat 32 8 := by
    rw [K15 _ (by decide), K11 _ (by decide), K10' _ (by decide) (by decide), v322]
  have v1521 : reg m15 (21 : Fin 32) = BYO := by
    rw [K15 _ (by decide), K11 _ (by decide), K10' _ (by decide) (by decide), v321]
  have v159 : reg m15 (9 : Fin 32) = X := by rw [K15 _ (by decide), v119]
  have v158 : reg m15 (8 : Fin 32) = F := by
    rw [k15 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v148]
  have sp15 : reg m15 sp = F := by
    rw [k15 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), K14 sp (by decide), sp13]
  have K16 : ∀ q, q ≠ a2 → reg m16 q = reg m15 q := fun q h => by rw [u16.regs, updz u15.zero h]
  obtain ⟨m17, d17, u17⟩ := u16.self.notTaken hcz 0x88 by_at_84 (by decide) (by
    simp only [branchTaken]; rw [K16 _ (by decide), v1522, u16.self.zero]; decide)
  have hBBn : byBsub BY = BitVec.ofNat 32 borrowingSubAddress := by decide
  have eFm4 : F + 0xFFFFFFFC = G + BitVec.ofNat 32 0x5C := by rw [← hGF, BitVec.add_assoc]; rfl
  have hBSb : (BitVec.ofNat 32 borrowingSubAddress : Word).toNat = borrowingSubAddress := by decide
  obtain ⟨n18, M18, c18, u18, hc18, fr18, hm18, hv18, sp18, K18⟩ := by_sub_loop (P := BY) (F := F) (np := X)
    (xp := BYO) (D := F) (M0 := Mz) (by decide) hFa (by omega) (by decide) hFa (by omega)
    (by rw [eFm4, ← hX]; exact offs (by omega) (by omega) (by omega))
    (by rw [eFm4]; exact sGO.sub (by decide))
    (by rw [eFm4, ← hGF]; exact offs (by omega) (by omega) (by omega))
    (by rw [← hGF, ← hX]; exact offs (by omega) (by omega) (by omega))
    (by rw [← hGF]; exact sGO.sub (by decide))
    (by rw [eFm4, hBBn]; exact hiC (by decide) (by rw [hBSb]; decide) (by rw [hBSb]; decide))
    (by rw [eFm4]; exact hiC (by decide) (by rw [hBSn]; decide) (by rw [hBSn]; decide))
    (by rw [← hGF, hBBn]; exact hiC (by decide) (by rw [hBSb]; decide) (by rw [hBSb]; decide))
    (by rw [← hGF]; exact hiC (by decide) (by rw [hBSn]; decide) (by rw [hBSn]; decide))
    7 0 rfl u17.self hcz (by rw [hBBn]; exact cd E.bsb (by rw [hBSb]; decide) (by rw [hBSb]; decide) IMz)
    (fun _ _ _ => rfl) (.inl rfl) rfl
    (by rw [u17.regs, K16 _ (by decide), sp15]) (by rw [u17.regs, K16 _ (by decide), v159, add_ofNat_zero])
    (by rw [u17.regs, K16 _ (by decide), v1521, add_ofNat_zero]) (by rw [u17.regs, K16 _ (by decide), v158, add_ofNat_zero])
    (by rw [u17.regs, K16 _ (by decide), v1522]) (by rw [u17.regs, u16.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u15.zero]; rfl)
  have IM18 : ∀ x, Sep G 0xE0 x 1 → M18 x = m.mem x := fun x hx => by
    rw [fr18 x (by rw [eFm4]; exact inG hx (by decide)) (by rw [← hGF]; exact inG hx (by decide)), IMz x hx]
  obtain ⟨mb, hmb⟩ : ∃ mb, maskBit (reg n18 a2) = mb := ⟨_, rfl⟩
  have hmb01 : mb = 0 ∨ mb = 1 := by
    rw [← hmb]; unfold maskBit; by_cases h : reg n18 a2 = 0
    · rw [ite_eq_left h]; exact .inl rfl
    · rw [ite_eq_right h]; exact .inr rfl
  have hmbW : BitVec.ofNat 32 mb = 0 ∨ BitVec.ofNat 32 mb = 1 := by rcases hmb01 with rfl | rfl <;> decide
  obtain ⟨m19, d19, u19⟩ := u18.aluImm hc18 by_at_a6 (off' := 0xAA) (by decide)
  have v19 : reg m19 a0 = BitVec.ofNat 32 mb := by
    rw [u19.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [bz_srl31 hm18, hmb]
  have K19 : ∀ q, q ≠ a0 → reg m19 q = reg n18 q := fun q h => by rw [u19.regs, updz u18.zero h]
  have hBBa : (BitVec.ofNat 32 blackBoxU8Address : Word).toNat = blackBoxU8Address := by decide
  obtain ⟨m20, c20, pc20, mem20, regs20⟩ := u19.self.callRa hc18 by_at_aa by_at_ae
    (cb := BitVec.ofNat 32 blackBoxU8Address) (by decide) (by decide)
  have r20 := PEnv.reg1 regs20 u19.self.zero
  have sp20 : reg m20 sp = F := by rw [r20 sp (by decide), K19 sp (by decide), sp18]
  have eFm1 : F + 0xFFFFFFFF = G + BitVec.ofNat 32 0x5F := by rw [← hGF, BitVec.add_assoc]; rfl
  obtain ⟨m21, c21, pc21, a021, K21, fr21⟩ := blackBoxU8_correct m20 (base := BitVec.ofNat 32 blackBoxU8Address)
    (retAddr := BY + BitVec.ofNat 32 (0xAA + 8))
    (by rw [mem20]; exact cd E.bb (by rw [hBBa]; decide) (by rw [hBBa]; decide) IM18) pc20
    (by rw [regs20]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at BY (by decide) _ (by decide)))
    (by rw [sp20, eFm1]; exact hiC (by decide) (by rw [hBBa]; decide) (by rw [hBBa]; decide))
  rw [r20 a0 (by decide), v19, frp_c8 hmbW] at a021
  rw [sp20, eFm1, mem20] at fr21
  have IM21 : ∀ x, Sep G 0xE0 x 1 → m21.mem x = m.mem x := fun x hx => by
    rw [fr21 x (inG hx (by decide)), IM18 x hx]
  have hc21 : CodeIn m21.mem BY bytes2scalar256Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IM21
  have u21 : St m21.mem BY m21 0xB2 (reg m21) := ⟨by rw [pc21], rfl, fun _ => rfl⟩
  obtain ⟨m22, d22, u22⟩ := u21.aluImm hc21 by_at_b2 (off' := 0xB6) (by decide)
  have v22 : reg m22 a0 = BitVec.ofNat 32 mb := by
    rw [u22.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [a021]; rcases hmbW with h | h <;> rw [h] <;> decide
  have K22 : ∀ q, q ≠ a0 → reg m22 q = reg m21 q := fun q h => by rw [u22.regs, updz u21.zero h]
  have hCNa : (BitVec.ofNat 32 choiceNotAddress : Word).toNat = choiceNotAddress := by decide
  obtain ⟨m23, c23, pc23, mem23, regs23⟩ := u22.self.callRa hc21 by_at_b6 by_at_ba
    (cb := BitVec.ofNat 32 choiceNotAddress) (by decide) (by decide)
  have r23 := PEnv.reg1 regs23 u22.self.zero
  have sp22 : reg m22 sp = F := by
    rw [K22 sp (by decide), K21 sp (by decide), r20 sp (by decide), K19 sp (by decide), sp18]
  have hmbv : (BitVec.ofNat 32 mb).toNat ≤ 1 := by rcases hmb01 with rfl | rfl <;> decide
  obtain ⟨m24, c24, pc24, a024, K24, fr24⟩ := choiceNot_correct m23 (P := BitVec.ofNat 32 choiceNotAddress)
    (retAddr := BY + BitVec.ofNat 32 (0xB6 + 8)) (c := BitVec.ofNat 32 mb) (by decide)
    (by rw [mem23]; exact cd E.cn (by rw [hCNa]; decide) (by rw [hCNa]; decide) IM21)
    (by rw [mem23, show BitVec.ofNat 32 choiceNotAddress + 0xFFFFBDEE = BitVec.ofNat 32 blackBoxU8Address by decide]
        exact cd E.bb (by rw [hBBa]; decide) (by rw [hBBa]; decide) IM21) pc23
    (by rw [r23 a0 (by decide), v22]) hmbv (by rw [regs23]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at BY (by decide) _ (by decide)))
    (by rw [r23 sp (by decide), sp22, eFm1,
          show BitVec.ofNat 32 choiceNotAddress + 0xFFFFBDEE = BitVec.ofNat 32 blackBoxU8Address by decide]
        exact hiC (by decide) (by rw [hBBa]; decide) (by rw [hBBa]; decide))
  rw [r23 sp (by decide), sp22, eFm1, mem23] at fr24
  have IM24 : ∀ x, Sep G 0xE0 x 1 → m24.mem x = m.mem x := fun x hx => by
    rw [fr24 x (inG hx (by decide)), IM21 x hx]
  have hc24 : CodeIn m24.mem BY bytes2scalar256Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IM24
  have u24 : St m24.mem BY m24 0xBE (reg m24) := ⟨by rw [pc24], rfl, fun _ => rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc : Word, BitVec.ofNat 32 (1 - (BitVec.ofNat 32 mb).toNat) = cc := ⟨_, rfl⟩
  have hcc01 : cc = 0 ∨ cc = 1 := by rw [← hcc]; rcases hmb01 with rfl | rfl <;> decide
  have hccmb : cc = 1 ↔ mb = 0 := by rw [← hcc]; rcases hmb01 with rfl | rfl <;> decide
  rw [hcc] at a024
  obtain ⟨m25, d25, u25⟩ := u24.aluImm hc24 by_at_be (off' := 0xC2) (by decide)
  have v25 : reg m25 a4 = cc := by
    rw [u25.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [a024]; rcases hcc01 with h | h <;> rw [h] <;> decide
  have K25 : ∀ q, q ≠ a4 → reg m25 q = reg m24 q := fun q h => by rw [u25.regs, updz u24.zero h]
  have K25' : ∀ q, q ≠ a0 → q ≠ a4 → q ≠ t1 → q ≠ ra → reg m25 q = reg n18 q := fun q h0 h4 ht hr => by
    rw [K25 q h4, K24 q h0 ht, r23 q hr, K22 q h0, K21 q h0, r20 q hr, K19 q h0]
  have sp25 : reg m25 sp = F := by
    rw [K25' sp (by decide) (by decide) (by decide) (by decide), sp18]
  obtain ⟨m26, c26, u26⟩ := St.block byF u25.self hc24 byF_end (by simp only [BlockOk, BInstr.ok, byF, and_self])
  have R26 : ∀ q, reg m26 q = (runBlock byF (m24.mem, reg m25)).2 q := u26.regs
  have u26' : St m24.mem BY m26 0xD0 (reg m26) := ⟨u26.pc, by rw [u26.mem]; rfl, fun _ => rfl⟩
  have K26 : ∀ q, q.val ∉ [9, 10, 11, 12, 13, 19] → reg m26 q = reg m25 q := fun q hq => by
    rw [R26]; refine runBlock_reg _ _ _ q u25.zero ?_
    simp only [byF, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have v26 : reg m26 a0 = X ∧ reg m26 a1 = BitVec.ofNat 32 8 ∧ reg m26 a2 = F ∧ reg m26 a3 = BitVec.ofNat 32 8 ∧
      reg m26 (19 : Fin 32) = X ∧ reg m26 (9 : Fin 32) = BitVec.ofNat 32 8 := by
    simp +decide only [R26, runBlock, BInstr.run, byF, upd_app, ↓reduceIte]
    rw [sp25]; simp only [ev_add, eFX, zw, and_true]
  obtain ⟨v26a0, v26a1, v26a2, v26a3, v2619, v269⟩ := v26
  have hSCa : (BitVec.ofNat 32 sliceCtAssignAddress : Word).toNat = sliceCtAssignAddress := by decide
  obtain ⟨m27, c27, pc27, mem27, regs27⟩ := u26'.callRa hc24 by_at_d0 by_at_d4
    (cb := BitVec.ofNat 32 sliceCtAssignAddress) (by decide) (by decide)
  have r27 := PEnv.reg1 regs27 u26'.zero
  have sp26 : reg m26 sp = F := by rw [K26 sp (by decide), sp25]
  obtain ⟨m28, c28, pc28, sp28, lim28, fr28, K28⟩ := sliceCtAssign_correct m27
    (B := BitVec.ofNat 32 sliceCtAssignAddress) (sp0 := F) (dst := X) (src := F) (c := cc) (n := 8)
    (retAddr := BY + BitVec.ofNat 32 (0xD0 + 8))
    (by rw [mem27]; exact cd E.sca (by rw [hSCa]; decide) (by rw [hSCa]; decide) IM24) pc27
    (by rw [r27 sp (by decide), sp26]) hFa (by omega) (by rw [r27 a0 (by decide), v26a0])
    (by rw [r27 a1 (by decide), v26a1]) (by rw [r27 a2 (by decide), v26a2]) (by rw [r27 a3 (by decide), v26a3])
    (by rw [r27 a4 (by decide), K26 a4 (by decide), v25]) hcc01
    (by rw [regs27]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at BY (by decide) _ (by decide)))
    (by omega) hFa (by rw [← hX]; exact Nat.le_of_lt (hGw _ (by decide)))
    (by rw [eFm]; exact hiC (by decide) (by rw [hSCa]; decide) (by rw [hSCa]; decide))
    (by rw [← hX]; exact hiC (by decide) (by rw [hSCa]; decide) (by rw [hSCa]; decide))
    (by rw [eFm, ← hX]; exact offs (by omega) (by omega) (by omega))
    (by rw [eFm, ← hGF]; exact offs (by omega) (by omega) (by omega))
    (by rw [← hX, ← hGF]; exact offs (by omega) (by omega) (by omega))
  rw [mem27, eFm] at fr28
  rw [mem27] at lim28
  have P24X : ∀ j, j < 32 → m24.mem (X + BitVec.ofNat 32 j) = m13.mem (X + BitVec.ofNat 32 j) := fun j hj => by
    rw [← hX, add_ofNat_assoc]
    have h1 : Sep (G + BitVec.ofNat 32 0x5F) 1 (G + BitVec.ofNat 32 (0x80 + j)) 1 := offs (by omega) (by omega) (by omega)
    rw [fr24 _ h1, fr21 _ h1, fr18 _ (by rw [eFm4]; exact offs (by omega) (by omega) (by omega))
      (by rw [← hGF]; exact offs (by omega) (by omega) (by omega)), ← hMz,
      fillWords_outside 8 (by rw [← hGF]; exact offs (by omega) (by omega) (by omega))]
  have P24D : ∀ j, j < 32 → m24.mem (F + BitVec.ofNat 32 j) = M18 (F + BitVec.ofNat 32 j) := fun j hj => by
    rw [← hGF, add_ofNat_assoc]
    have h1 : Sep (G + BitVec.ofNat 32 0x5F) 1 (G + BitVec.ofNat 32 (0x60 + j)) 1 := offs (by omega) (by omega) (by omega)
    rw [fr24 _ h1, fr21 _ h1]
  have PzX : ∀ j, j < 32 → Mz (X + BitVec.ofNat 32 j) = m13.mem (X + BitVec.ofNat 32 j) := fun j hj => by
    rw [← hX, add_ofNat_assoc, ← hMz, fillWords_outside 8 (by rw [← hGF]; exact offs (by omega) (by omega) (by omega))]
  have accEq : ∀ {M M' : Word → BitVec 8} {p : Word}, (∀ j, j < 32 → M' (p + BitVec.ofNat 32 j) = M (p + BitVec.ofNat 32 j)) →
      accV M' p 8 = accV M p 8 := fun h =>
    accV_congr 8 fun i hi => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega)
  have xz : accV Mz X 8 = beNat (memBytes m.mem b 32) := by rw [accEq PzX, xval]
  have nz : accV Mz BYO 8 = C3.p256.n := by
    rw [accEq (M := m.mem) fun j hj => IMz _ (sGO.subR (c := j) (l := 1) (by omega)), E.ord]
  rw [xz, nz, hmb] at hv18
  have dz : accV m24.mem F 8 = accV M18 F 8 := accEq P24D
  have x28 : accV m28.mem X 8 = if cc = 1 then accV M18 F 8 else beNat (memBytes m.mem b 32) := by
    by_cases h1 : cc = 1
    · rw [ite_eq_left h1, ← dz]
      exact accV_congr2 8 fun i hi => by rw [lim28 i hi, ite_eq_left h1]
    · rw [ite_eq_right h1, ← xval, ← accEq P24X]
      exact accV_congr 8 fun i hi => by rw [lim28 i hi, ite_eq_right h1]
  have hx256 := by_beNat_lt m.mem b 32
  have hd256 := accV_lt M18 F 8
  have xmod : (if cc = 1 then accV M18 F 8 else beNat (memBytes m.mem b 32)) =
      beNat (memBytes m.mem b 32) % C3.p256.n := by
    have hn1 := p256n_gt
    by_cases h1 : cc = 1
    · rw [ite_eq_left h1]
      have h0 := hccmb.mp h1
      rw [h0, Nat.mul_zero, Nat.add_zero] at hv18
      rw [hv18, Nat.add_mod_left, Nat.mod_eq_of_lt]
      generalize accV M18 F 8 = d at hv18 ⊢
      generalize beNat (memBytes m.mem b 32) = x at hv18 hx256
      generalize C3.p256.n = nn at hv18 hn1
      have : (2 : Nat) ^ (8 * 32) = 2 * 2 ^ 255 := by decide
      omega
    · rw [ite_eq_right h1]
      have h0 : mb = 1 := hmb01.resolve_left fun h => h1 (hccmb.mpr h)
      rw [h0, Nat.mul_one] at hv18
      rw [Nat.mod_eq_of_lt]
      generalize accV M18 F 8 = d at hv18 hd256
      generalize beNat (memBytes m.mem b 32) = x at hv18 ⊢
      generalize C3.p256.n = nn at hv18
      have : (2 : Nat) ^ (32 * 8) = 2 ^ (32 * 8) := rfl
      omega
  rw [← x28] at xmod
  have IM28 : ∀ x, Sep G 0xE0 x 1 → m28.mem x = m.mem x := fun x hx => by
    rw [fr28 x (inG hx (by decide)) (by rw [← hX]; exact inG hx (by decide)), IM24 x hx]
  have hc28 : CodeIn m28.mem BY bytes2scalar256Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IM28
  have u28 : St m28.mem BY m28 0xD8 (reg m28) := ⟨by rw [pc28], rfl, fun _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, G + BitVec.ofNat 32 0xA0 = Y := ⟨_, rfl⟩
  have eFY : F + 0x40 = Y := by rw [← hY, show (0x40 : Word) = BitVec.ofNat 32 0x40 from rfl, eFk]
  have hYn : Y.toNat = G.toNat + 0xA0 := by rw [← hY]; exact hGc _ (by decide)
  obtain ⟨m29, c29, u29⟩ := St.block byG u28 hc28 byG_end (by simp only [BlockOk, BInstr.ok, byG, and_self])
  have R29 : ∀ q, reg m29 q = (runBlock byG (m28.mem, reg m28)).2 q := u29.regs
  have u29' : St m28.mem BY m29 0xE2 (reg m29) := ⟨u29.pc, by rw [u29.mem]; rfl, fun _ => rfl⟩
  have K29 : ∀ q, q.val ∉ [8, 10, 11, 12] → reg m29 q = reg m28 q := fun q hq => by
    rw [R29]; refine runBlock_reg _ _ _ q u28.zero ?_
    simp only [byG, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    intro h; apply hq; revert h; revert q; decide
  have v29 : reg m29 a0 = Y ∧ reg m29 a2 = BitVec.ofNat 32 (4 * 8) ∧ reg m29 a1 = 0 ∧ reg m29 (8 : Fin 32) = Y := by
    simp +decide only [R29, runBlock, BInstr.run, byG, upd_app, ↓reduceIte]
    rw [sp28]; simp only [ev_add, eFY, and_true]
  obtain ⟨v29a0, v29a2, v29a1, v298⟩ := v29
  obtain ⟨m30, c30, u30, _, k30⟩ := u29'.memsetW (B := BitVec.ofNat 32 memsetAddress) (w := 8) (dst := Y)
    (by decide) hc28 (cd E.fc.ms (by rw [hMSn]; decide) (by rw [hMSn]; decide) IM28) by_at_e2 by_at_e6 (by decide)
    (by decide) (by decide) (by rw [← hY]; exact hGw _ (by decide)) (by decide) (by omega)
    (by rw [← hY]; exact hiC (by decide) (by rw [hMSn]; decide) (by rw [hMSn]; decide)) v29a0 v29a1 v29a2
  obtain ⟨My, hMy⟩ : ∃ My, fillWords m28.mem Y 0 8 = My := ⟨_, rfl⟩
  rw [hMy] at u30
  have IMy : ∀ x, Sep G 0xE0 x 1 → My x = m.mem x := fun x hx => by
    rw [← hMy, fillWords_outside 8 (by rw [← hY]; exact inG hx (by decide)), IM28 x hx]
  have hcy : CodeIn My BY bytes2scalar256Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IMy
  have K30 : ∀ q, q.val ∉ [1, 8, 10, 11, 12, 13, 14, 15, 16] → reg m30 q = reg m28 q := fun q hq => by
    rw [k30 q (by intro h; apply hq; rw [h]; decide) (by intro h; apply hq; rw [h]; decide)
      (by intro h; apply hq; rw [h]; decide) (by intro h; apply hq; rw [h]; decide)
      (by intro h; apply hq; rw [h]; decide) (by intro h; apply hq; rw [h]; decide),
      K29 q (by intro h; apply hq; revert h; revert q; decide)]
  have K28' : ∀ q, q.val ∉ [1, 10, 11, 12, 13, 14, 15, 16] → reg m28 q = reg m26 q := fun q hq => by
    rw [K28 q (by intro h; apply hq; revert h; revert q; decide), r27 q (by intro h; apply hq; rw [h]; decide)]
  have v309 : reg m30 (9 : Fin 32) = BitVec.ofNat 32 8 := by rw [K30 _ (by decide), K28' _ (by decide), v269]
  have v3019 : reg m30 (19 : Fin 32) = X := by rw [K30 _ (by decide), K28' _ (by decide), v2619]
  have v308 : reg m30 (8 : Fin 32) = Y := by
    rw [k30 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v298]
  obtain ⟨m31, d31, u31⟩ := u30.notTaken hcy 0xEC by_at_ea (by decide) (by
    simp only [branchTaken]; rw [v309, u30.zero]; decide)
  have sYX : Sep Y 32 X 32 := by rw [← hY, ← hX]; exact offs (by omega) (by omega) (by omega)
  obtain ⟨m32, c32, u32, K32⟩ := by_copy_loop (P := BY) (X := X) (Y := Y) (M0 := My) (by omega) (by omega) sYX
    (by rw [← hY]; exact hiC (by decide) (by rw [hBSn]; decide) (by rw [hBSn]; decide)) hcy 7 0 rfl u31.self
    (by rw [u31.regs, v3019, add_ofNat_zero]) (by rw [u31.regs, v308, add_ofNat_zero]) (by rw [u31.regs, v309])
  obtain ⟨Mc, hMc⟩ : ∃ Mc, copyWords My Y X 8 = Mc := ⟨_, rfl⟩
  rw [hMc] at u32
  have IMc : ∀ x, Sep G 0xE0 x 1 → Mc x = m.mem x := fun x hx => by
    rw [← hMc, copyWords_outside 8 (by rw [← hY]; exact inG hx (by decide)), IMy x hx]
  have hcc' : CodeIn Mc BY bytes2scalar256Code := cd hc (by rw [hBSn]; decide) (by rw [hBSn]; decide) IMc
  have accY : accV Mc Y 8 = accV m28.mem X 8 := accV_congr2 8 fun i hi => by
    rw [← hMc, copyWords_load 8 i hi (by rw [← hY]; exact Nat.le_of_lt (hGw _ (by decide))), ← hMy, fillWords_load_sep
      ((sYX.subR (c := 4 * i) (l := 4) (by omega)))]
  have Kall : ∀ q, q.val ∈ [3, 4, 18, 23, 24, 25, 26, 27] → reg m32 q = reg m3 q := fun q hq => by
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
      K10' q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  have sp32 : reg m32 sp = F := by
    rw [K32 sp (by decide) (by decide) (by decide) (by decide), u31.regs, K30 sp (by decide), K28' sp (by decide), sp26]
  obtain ⟨m33, c33, u33⟩ := St.block byH u32 hcc' byH_end (by simp only [BlockOk, BInstr.ok, byH, and_self])
  have R33 : ∀ q, reg m33 q = (runBlock byH (Mc, reg m32)).2 q := u33.regs
  have u33' : St Mc BY m33 0x102 (reg m33) := ⟨u33.pc, by rw [u33.mem]; rfl, fun _ => rfl⟩
  have K33 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m33 q = reg m32 q := fun q h0 h1 h2 => by
    rw [R33]; refine runBlock_reg _ _ _ q u32.zero ?_
    simp only [byH, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2]
  have v33 : reg m33 a1 = Y ∧ reg m33 a2 = BitVec.ofNat 32 (4 * 8) ∧ reg m33 a0 = out := by
    simp +decide only [R33, runBlock, BInstr.run, byH, upd_app, ↓reduceIte]
    rw [sp32, Kall 18 (by decide), v318]; simp only [ev_add, eFY, true_and]; exact zw _
  obtain ⟨v33a1, v33a2, v33a0⟩ := v33
  have hMCn : (BitVec.ofNat 32 memcpyStubAddress : Word).toNat = memcpyStubAddress := by decide
  have hMCb : (BitVec.ofNat 32 memcpyStubAddress + 8 : Word).toNat = memcpyStubAddress + 8 := by decide
  obtain ⟨m34, c34, u34, _, k34⟩ := u33'.memcpyW (B := BitVec.ofNat 32 memcpyStubAddress) (w := 8) (dst := out)
    (src := Y) (by decide) hcc' (cd E.fc.cs (by rw [hMCn]; decide) (by rw [hMCn]; decide) IMc)
    (cd E.fc.cb (by rw [hMCb]; decide) (by rw [hMCb]; decide) IMc) by_at_102 by_at_106 (by decide) (by decide)
    (by decide) hOw (by decide) hoa (by omega) (by rw [← hY]; exact sOG.subR (c := 0xA0) (l := 32) (by decide))
    (sOcode (by rw [hMCb]; decide) (by rw [hMCb]; decide)) v33a0 v33a1 v33a2
  obtain ⟨Mo, hMo⟩ : ∃ Mo, copyWords Mc out Y 8 = Mo := ⟨_, rfl⟩
  rw [hMo] at u34
  have FrO : ∀ x, Sep G 0xE0 x 1 → Sep out 32 x 1 → Mo x = m.mem x := fun x hx ho => by
    rw [← hMo, copyWords_outside 8 ho, IMc x hx]
  have hc34 : CodeIn Mo BY bytes2scalar256Code := fun i hi => by
    have hx := code_hi (b := BY) (by rw [hBSn]; decide) (by rw [hBSn]; decide) hi
    have hx' : dramEnd ≤ (BY + BitVec.ofNat 32 i).toNat := by unfold dramEnd; omega
    rw [FrO _ (hiG _ hx') (hiO _ hx')]; exact hc i hi
  have sp34 : reg m34 sp = F := by
    rw [k34 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), K33 sp (by decide) (by decide) (by decide), sp32]
  have lowS : ∀ {a l c : Nat}, a + l ≤ c → c < 0xE0 → Sep (G + BitVec.ofNat 32 a) l (G + BitVec.ofNat 32 c) 1 :=
    fun h1 h2 => offs (by omega) (by omega) (by omega)
  have slotM : ∀ c, 0xC0 ≤ c → c < 0xE0 → Mo (G + BitVec.ofNat 32 c) = Ms (G + BitVec.ofNat 32 c) :=
    fun c h1 h2 => by
      have hG0 : Sep G 0x60 (G + BitVec.ofNat 32 c) 1 := by
        have := lowS (a := 0) (l := 0x60) (c := c) (by omega) h2; rwa [add_ofNat_zero] at this
      have h4 : G + BitVec.ofNat 32 c ≠ F + 0x40 := fun e => by
        have h := lowS (a := 0x60 + 0x40) (l := 1) (c := c) (by omega) h2
        rw [← eFk] at h
        exact h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e]; rfl)
      rw [← hMo, copyWords_outside 8 (sOG.subR (c := c) (l := 1) (by omega)), ← hMc,
        copyWords_outside 8 (by rw [← hY]; exact lowS (by omega) h2), ← hMy,
        fillWords_outside 8 (by rw [← hY]; exact lowS (by omega) h2),
        fr28 _ (lowS (by omega) h2) (by rw [← hX]; exact lowS (by omega) h2),
        fr24 _ (lowS (by omega) h2), fr21 _ (lowS (by omega) h2),
        fr18 _ (by rw [eFm4]; exact lowS (by omega) h2) (by rw [← hGF]; exact lowS (by omega) h2), ← hMz,
        fillWords_outside 8 (by rw [← hGF]; exact lowS (by omega) h2),
        fr13 _ (by rw [eF60]; exact hG0) (by rw [← hX]; exact lowS (by omega) h2), mem12, ← hMr,
        memStore32_get_sep (by rw [show (0x44 : Word) = BitVec.ofNat 32 0x44 from rfl, eFk]; exact lowS (by omega) h2),
        memStore8_ne h4, fr5 _ (by rw [eFm]; exact lowS (by omega) h2), mem4]
  have slot : ∀ o : Word, 0x60 ≤ o.toNat → o.toNat + 4 ≤ 0x80 → memLoad32 Mo (F + o) = memLoad32 Ms (F + o) :=
    fun o h1 h2 => by
      rw [slotO]
      apply memLoad32_congr; intro j hj
      rw [add_ofNat_assoc, eFk]; exact slotM _ (by omega) (by omega)
  have hpsp : ∀ p ∈ byPs, p.1 ≠ sp := by decide
  obtain ⟨n1, c36, u36⟩ := St.block (restoreBlock byPs) u34 hc34 byRestore_end
    (restoreBlock_ok Mo F byPs (reg m34) sp34 hpsp fun q hq => by
      simp only [byPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run Mo F byPs (reg m34) sp34 hpsp] at u36
  have rsp : restoreRegs Mo F (reg m34) byPs sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp34
  obtain ⟨n2, d37, u37⟩ := u36.aluImm hc34 by_at_11a (off' := 0x11C) (by decide)
  obtain ⟨n3, d38, pc38, mem38, regs38⟩ := u37.jalr hc34 by_at_11c
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs Mo F f ps q = f q := by
    intro f ps q hq0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
  have hslot : ∀ r o, (r, o) ∈ byPs → reg n3 r = reg m r := fun r o hm => by
    rw [regs38]
    simp only [byPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
      rw [slot _ (by decide) (by decide)]; exact slots _ _ (by decide)
  have val : accV Mo out 8 = accV Mc Y 8 := accV_congr2 8 fun i hi => by
    rw [← hMo]; exact copyWords_load 8 i hi (Nat.le_of_lt hOw)
  refine ⟨n3, (.cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans (.cons d10 (.cons d10' (c11.trans (c12.trans (c13.trans (c14.trans (c15.trans (.cons d16 (.cons d17 (c18.trans (.cons d19 (c20.trans (c21.trans (.cons d22 (c23.trans (c24.trans (.cons d25 (c26.trans (c27.trans (c28.trans (c29.trans (c30.trans (.cons d31 (c32.trans (c33.trans (c34.trans (c36.trans (.cons d37 (.single d38))))))))))))))))))))))))))))))))))))))), ?_, ?_, fun q hq => ?_, ?_, fun x hx hl => ?_⟩
  · rw [pc38, ← regs38, hslot ra 0x7C (by decide), hra, add_lit_zero, hret]
  · rw [regs38]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [rsp, eFS]
  · rcases (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨
        q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q.val ∈ [3, 4, 23, 24, 25, 26, 27]) q hq with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hL
    · exact hslot _ 0x7C (by decide)
    · exact hslot _ 0x78 (by decide)
    · exact hslot _ 0x74 (by decide)
    · exact hslot _ 0x70 (by decide)
    · exact hslot _ 0x6C (by decide)
    · exact hslot _ 0x68 (by decide)
    · exact hslot _ 0x64 (by decide)
    · exact hslot _ 0x60 (by decide)
    · obtain ⟨hv, hs, hps, hr, h0, h1, h2⟩ : q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ byPs, p.1 ≠ q) ∧ q ≠ ra ∧ q ≠ a0 ∧ q ≠ a1 ∧
          q ≠ a2 := by
        revert hL; revert q; decide
      rw [regs38, upd_ne hv hs, rr _ _ q hv hps,
        k34 q h1 h2 ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → q ≠ a3) q hL)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → q ≠ a4) q hL)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → q ≠ a5) q hL)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → q ≠ a6) q hL)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → q ≠ a7) q hL)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → q ≠ t0) q hL)
          ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → q ≠ t1) q hL) hr,
        K33 q h0 h1 h2,
        Kall q ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → q.val ∈ [3, 4, 18, 23, 24, 25, 26, 27]) q hL),
        K3 q ((by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 23, 24, 25, 26, 27] → q.val ∉ [10, 11, 18, 19, 21, 22]) q hL),
        r2 q hs]
  · rw [mem38, val, accY]; exact xmod
  · rw [mem38]; exact FrO x hx hl

end C3.RV32
