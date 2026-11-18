import C3BootProofs.Proofs.Pv384Lib2
import C3BootProofs.Proofs.SelectI64

/-!
# `p384_verify_prehash`: the constant-time divsteps

The inversion of the projective `z` coordinate runs its divsteps in
constant time: each step computes both outcomes and picks one with
`select_i64`. This file proves that one pass of that loop, at 0xD36, is the
same `dsStep` that models the variable-time loop of the inversion of `s`.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

set_option maxHeartbeats 4000000 in
/-- A call to `select_i64`, with the choice 0 or 1 in `a0`. -/
theorem pv_si {B : Word} {m : Machine} {off : Nat} {imm o : Word} (F : Fr B 0x21A0)
    (E : PvEnv3 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 selectI64Address)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : reg m sp = B + 0x420)
    (hc : reg m a0 = 0 ∨ reg m a0 = 1) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem 0 0 ∧
      (∀ q : Fin 32, q ≠ ra → q ≠ a0 → q ≠ a1 → q ≠ a3 → q ≠ a4 → q ≠ a5 → reg m' q = reg m q) ∧
      reg m' a0 = (if reg m a0 = 1 then reg m a3 else reg m a1) ∧
      reg m' a1 = (if reg m a0 = 1 then reg m a4 else reg m a2) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = B + 0x420 := by rw [r1 sp (by decide)]; exact hsp
  obtain ⟨n2, c2, pc2, sp2, k2, v0, v1, fr2⟩ := selectI64_correct n1 (by rw [mem1]; exact E.C3.si) pc1
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
    (by rw [sp1]; exact FS.lowHi (k := 0xFFFFFFFF) (c := 1) (by decide) rfl (by decide) (by decide))
  have hlow : ∀ x, PvR B x → x ≠ reg n1 sp + 0xFFFFFFFF := fun x hx h => by
    have := pvR_lo (k := 1) hx (by decide) (by decide)
    rw [h, sp1] at this
    exact sep1_ne this rfl
  have a0e : reg n1 a0 = reg m a0 := r1 a0 (by decide)
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => by rw [fr2 x (hlow x hx), mem1],
    fun q hq => ?_⟩, fun e he1 _ => ?_, fun q hr h0 h1' h3 h4 h5 => by
      rw [k2 q h0 h1' h3 h4 h5, r1 q hr], ?_, ?_⟩
  · by_cases h : q = sp
    · subst h; rw [sp2, sp1, hsp]
    · rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · rw [fr2 _ (fun h => by
      rw [sp1] at h
      have := pv_lowB F (k := 1) (by decide) (by decide) (show e + 1 ≤ 0x1D80 by omega)
      rw [show (BitVec.ofNat 32 (2 ^ 32 - 1) : Word) = 0xFFFFFFFF by decide] at this
      exact sep1_ne this.symm h.symm), mem1]
  · rcases hc with h | h
    · rw [ite_eq_right (by rw [h]; decide), (v0 (by rw [a0e, h]; rfl)).1, r1 a1 (by decide)]
    · rw [ite_eq_left h, (v1 (by rw [a0e, h]; rfl)).1, r1 a3 (by decide)]
  · rcases hc with h | h
    · rw [ite_eq_right (by rw [h]; decide), (v0 (by rw [a0e, h]; rfl)).2, r1 a2 (by decide)]
    · rw [ite_eq_left h, (v1 (by rw [a0e, h]; rfl)).2, r1 a4 (by decide)]

theorem fr_toNat {S a : Word} (hS : S.toNat + 0x1D80 ≤ 2 ^ 32) (ha : a.toNat < 0x1D80) :
    (S + a).toNat = S.toNat + a.toNat := by
  rw [BitVec.toNat_add]; omega

theorem fr_sep {S a b : Word} {n k : Nat} (hS : S.toNat + 0x1D80 ≤ 2 ^ 32) (hn : 0 < n) (hk : 0 < k)
    (ha : a.toNat + n ≤ 0x1D80) (hb : b.toNat + k ≤ 0x1D80) (h : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat) :
    Sep (S + a) n (S + b) k := by
  rcases h with h | h
  · exact sep_of_le (by rw [fr_toNat hS (by omega), fr_toNat hS (by omega)]; omega)
      (by rw [fr_toNat hS (by omega)]; omega)
  · exact (sep_of_le (by rw [fr_toNat hS (by omega), fr_toNat hS (by omega)]; omega)
      (by rw [fr_toNat hS (by omega)]; omega)).symm

/-- A load from one stack slot past a store to another. -/
theorem ldst_ne {M : Word → BitVec 8} {S a b v : Word} (hS : S.toNat + 0x1D80 ≤ 2 ^ 32)
    (ha : a.toNat + 4 ≤ 0x1D80) (hb : b.toNat + 4 ≤ 0x1D80) (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    memLoad32 (memStore32 M (S + a) v) (S + b) = memLoad32 M (S + b) :=
  memLoad32_store32_sep (fr_sep hS (by decide) (by decide) ha hb h)

theorem ldst8_ne {M : Word → BitVec 8} {S a b : Word} {v : BitVec 8} (hS : S.toNat + 0x1D80 ≤ 2 ^ 32)
    (ha : a.toNat + 1 ≤ 0x1D80) (hb : b.toNat + 4 ≤ 0x1D80) (h : a.toNat + 1 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    memLoad32 (memStore8 M (S + a) v) (S + b) = memLoad32 M (S + b) :=
  memLoad32_store8_sep (fr_sep hS (by decide) (by decide) ha hb h)

theorem st8_get {M : Word → BitVec 8} {S a b : Word} {v : BitVec 8} (hS : S.toNat + 0x1D80 ≤ 2 ^ 32)
    (ha : a.toNat + 1 ≤ 0x1D80) (hb : b.toNat + 1 ≤ 0x1D80) (h : a.toNat + 1 ≤ b.toNat ∨ b.toNat + 1 ≤ a.toNat) :
    memStore8 M (S + a) v (S + b) = M (S + b) :=
  memStore8_ne (sep1_ne (fr_sep hS (by decide) (by decide) ha hb h))

def ctS1 : List BInstr :=
  [.lw (21 : Fin 32) sp 0x44, .aluImm .and (27 : Fin 32) (21 : Fin 32) 0x1, .lui a5 0x80000000,
   .alu .xor a0 (24 : Fin 32) a5, .sb (8 : Fin 32) (27 : Fin 32) 0x514, .alu .add (19 : Fin 32) x0 (20 : Fin 32),
   .lw (9 : Fin 32) sp 0x40, .sw sp (25 : Fin 32) 0x30, .alu .sltu a2 x0 (9 : Fin 32), .lui a1 0x1000,
   .aluImm .add a1 a1 0x294, .alu .add a1 a1 sp, .aluImm .add a1 (9 : Fin 32) 0x2, .sw sp a3 0x28, .sw sp a4 0x3C,
   .lbu a4 (8 : Fin 32) 0x514, .aluImm .add a6 x0 0x2, .alu .sub a3 a6 (9 : Fin 32), .alu .sub a5 a5 a0,
   .alu .sub a5 a5 a2, .alu .sltu a2 a1 (9 : Fin 32), .alu .add a2 a2 (24 : Fin 32), .alu .and a0 a0 a5,
   .aluImm .srl a5 a0 0x1F, .sw sp a5 0x24, .aluImm .sltu a0 a4 0x1, .alu .sub a4 x0 a4,
   .aluImm .add a0 a0 0xFFFFFFFF, .sw sp (18 : Fin 32) 0x1C, .alu .add (18 : Fin 32) x0 (22 : Fin 32),
   .lw (22 : Fin 32) sp 0x48, .lw (20 : Fin 32) sp 0x50, .alu .and (8 : Fin 32) (20 : Fin 32) a4,
   .alu .sltu a4 a6 (9 : Fin 32), .alu .and (25 : Fin 32) (22 : Fin 32) a0, .alu .sub a0 x0 (24 : Fin 32),
   .alu .sub a4 a0 a4, .alu .and (24 : Fin 32) (27 : Fin 32) a5, .alu .add a0 x0 (24 : Fin 32)]
set_option maxHeartbeats 4000000 in
theorem ctS1_end : blockEnd p384VerifyPrehashCode 0xD36 ctS1 = some 0xDAA := by decide
def ctS2 : List BInstr :=
  [.sw sp a0 0x40, .sw sp a1 0x38, .alu .add a0 x0 (24 : Fin 32), .alu .add a1 x0 (20 : Fin 32),
   .alu .add a2 x0 (22 : Fin 32), .alu .add (22 : Fin 32) x0 (18 : Fin 32), .alu .add a3 x0 (21 : Fin 32),
   .lw (9 : Fin 32) sp 0x4C, .alu .add a4 x0 (9 : Fin 32)]
set_option maxHeartbeats 4000000 in
theorem ctS2_end : blockEnd p384VerifyPrehashCode 0xDB2 ctS2 = some 0xDC4 := by decide
def ctS3 : List BInstr :=
  [.sw sp a0 0x50, .sw sp a1 0x48, .alu .add a1 (8 : Fin 32) (21 : Fin 32), .alu .sltu a2 a1 (8 : Fin 32),
   .alu .add a0 (25 : Fin 32) (9 : Fin 32), .alu .add a2 a2 a0, .alu .sltu a0 (21 : Fin 32) (8 : Fin 32),
   .alu .sub a4 (9 : Fin 32) (25 : Fin 32), .alu .sub a4 a4 a0, .alu .sub a3 (21 : Fin 32) (8 : Fin 32),
   .alu .add a0 x0 (24 : Fin 32)]
set_option maxHeartbeats 4000000 in
theorem ctS3_end : blockEnd p384VerifyPrehashCode 0xDCC ctS3 = some 0xDEE := by decide
def ctS4 : List BInstr :=
  [.aluImm .sll a2 a1 0x1F, .aluImm .srl a0 a0 0x1, .alu .or a0 a0 a2, .sw sp a0 0x44, .aluImm .sra a1 a1 0x1,
   .sw sp a1 0x4C, .alu .add a0 x0 (24 : Fin 32), .alu .add a1 x0 (23 : Fin 32), .alu .add a2 x0 (26 : Fin 32),
   .lw (18 : Fin 32) sp 0x54, .alu .add a3 x0 (18 : Fin 32), .lw (25 : Fin 32) sp 0x1C, .alu .add a4 x0 (25 : Fin 32)]
set_option maxHeartbeats 4000000 in
theorem ctS4_end : blockEnd p384VerifyPrehashCode 0xDF6 ctS4 = some 0xE12 := by decide
def ctS5 : List BInstr :=
  [.aluImm .srl a2 a0 0x1F, .aluImm .sll a1 a1 0x1, .alu .or a1 a1 a2, .sw sp a1 0x34, .aluImm .sll a0 a0 0x1,
   .sw sp a0 0x2C, .alu .add a0 x0 (24 : Fin 32), .alu .add a1 x0 (19 : Fin 32), .lw (8 : Fin 32) sp 0x30,
   .alu .add a2 x0 (8 : Fin 32), .alu .add a3 x0 (22 : Fin 32), .lw (21 : Fin 32) sp 0x28, .alu .add a4 x0 (21 : Fin 32)]
set_option maxHeartbeats 4000000 in
theorem ctS5_end : blockEnd p384VerifyPrehashCode 0xE1A ctS5 = some 0xE36 := by decide
def ctS6 : List BInstr :=
  [.aluImm .srl a2 a0 0x1F, .aluImm .sll a1 a1 0x1, .aluImm .sll (20 : Fin 32) a0 0x1, .alu .or a1 a1 a2,
   .sw sp a1 0x20, .alu .sltu a0 x0 (23 : Fin 32), .alu .sub a4 x0 (26 : Fin 32), .alu .sub a3 x0 (23 : Fin 32),
   .alu .sub a4 a4 a0, .lw (9 : Fin 32) sp 0x24, .alu .add a0 x0 (9 : Fin 32), .alu .add a1 x0 (23 : Fin 32),
   .alu .add a2 x0 (26 : Fin 32)]
set_option maxHeartbeats 4000000 in
theorem ctS6_end : blockEnd p384VerifyPrehashCode 0xE3E ctS6 = some 0xE62 := by decide
def ctS7 : List BInstr :=
  [.aluImm .add a2 sp 0x7FF, .aluImm .add a2 a2 0x581, .sb a2 (27 : Fin 32) 0x514, .lui a2 0x1000,
   .aluImm .add a2 a2 0x294, .alu .add (23 : Fin 32) sp a2, .aluImm .add a2 sp 0x7FF, .aluImm .add a2 a2 0x581,
   .lbu a2 a2 0x514, .alu .sub a3 x0 a2, .aluImm .sltu a2 a2 0x1, .alu .and a0 a0 a3,
   .alu .sltu a4 x0 (19 : Fin 32), .aluImm .add a2 a2 0xFFFFFFFF, .alu .and a1 a1 a2,
   .alu .add (18 : Fin 32) (18 : Fin 32) a0, .sw sp (18 : Fin 32) 0x54, .alu .sltu a0 (18 : Fin 32) a0,
   .alu .add a1 a1 (25 : Fin 32), .alu .sub a5 x0 (8 : Fin 32), .alu .add (18 : Fin 32) a1 a0,
   .alu .sub a3 x0 (19 : Fin 32), .alu .sub a4 a5 a4, .alu .add a0 x0 (9 : Fin 32),
   .aluImm .add (24 : Fin 32) sp 0x7FF, .aluImm .add (24 : Fin 32) (24 : Fin 32) 0x581, .alu .add a1 x0 (19 : Fin 32),
   .alu .add a2 x0 (8 : Fin 32)]
set_option maxHeartbeats 4000000 in
theorem ctS7_end : blockEnd p384VerifyPrehashCode 0xE6A ctS7 = some 0xEC6 := by decide
def ctS8 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 (24 : Fin 32), .lw a4 sp 0x3C, .sb (24 : Fin 32) (27 : Fin 32) 0x514,
   .lbu a2 (24 : Fin 32) 0x514, .aluImm .add a4 a4 0xFFFFFFFF, .alu .sub a3 x0 a2, .aluImm .sltu a2 a2 0x1,
   .aluImm .add a2 a2 0xFFFFFFFF, .alu .and a0 a0 a3, .alu .and a1 a1 a2, .alu .add (22 : Fin 32) (22 : Fin 32) a0,
   .alu .sltu a0 (22 : Fin 32) a0, .alu .add a1 a1 (21 : Fin 32), .lw (25 : Fin 32) sp 0x20, .alu .add a3 a1 a0,
   .lw (23 : Fin 32) sp 0x2C, .lw (24 : Fin 32) sp 0x38, .lw (26 : Fin 32) sp 0x34]
set_option maxHeartbeats 4000000 in
theorem ctS8_end : blockEnd p384VerifyPrehashCode 0xECE ctS8 = some 0xEFE := by decide

/-- The constant-time loop's state: `δ` in the slot at 0x40 and `s8`, `f`
in the slots at 0x50 and 0x48, `g` in the slots at 0x44 and 0x4C, `u` in
`s7:s10`, `v` in `s4:s9`, `q` in the slot at 0x54 and `s2`, and `r` in
`s6:a3` (low word first). -/
def CtRegs (B : Word) (M : Word → BitVec 8) (f : Fin 32 → Word) (s : Ds) : Prop :=
  W64 (memLoad32 M (B + 0x420 + 0x40)) (f 24) = s.δ ∧
  W64 (memLoad32 M (B + 0x420 + 0x50)) (memLoad32 M (B + 0x420 + 0x48)) = s.f ∧
  W64 (memLoad32 M (B + 0x420 + 0x44)) (memLoad32 M (B + 0x420 + 0x4C)) = s.g ∧
  W64 (f 23) (f 26) = s.u ∧ W64 (f 20) (f 25) = s.v ∧
  W64 (memLoad32 M (B + 0x420 + 0x54)) (f 18) = s.q ∧ W64 (f 22) (f 13) = s.r

end C3.RV32.Pv
