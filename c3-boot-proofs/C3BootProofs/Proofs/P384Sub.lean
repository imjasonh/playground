import C3BootProofs.Proofs.P384Add

/-!
# `ConstMontyForm<p384::FieldParams, 12>::sub`

P-384's field subtraction as compiled: a 12-limb `borrowing_sub` of the
operands into a frame buffer, the modulus masked with the borrow into a
second buffer, and their 12-limb sum, with carries, copied to the result.
-/

namespace C3.RV32

open C3.Image

set_option exponentiation.threshold 400

section
set_option maxRecDepth 20000

theorem ps3_at_0 : fetchRel p384SubCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF50, 2) := by decide
theorem ps3_at_2 : fetchRel p384SubCode 0x2 = some (.store .sw sp ra 0xAC, 2) := by decide
theorem ps3_at_4 : fetchRel p384SubCode 0x4 = some (.store .sw sp (8 : Fin 32) 0xA8, 2) := by decide
theorem ps3_at_6 : fetchRel p384SubCode 0x6 = some (.store .sw sp (9 : Fin 32) 0xA4, 2) := by decide
theorem ps3_at_8 : fetchRel p384SubCode 0x8 = some (.store .sw sp (18 : Fin 32) 0xA0, 2) := by decide
theorem ps3_at_a : fetchRel p384SubCode 0xA = some (.store .sw sp (19 : Fin 32) 0x9C, 2) := by decide
theorem ps3_at_c : fetchRel p384SubCode 0xC = some (.store .sw sp (20 : Fin 32) 0x98, 2) := by decide
theorem ps3_at_e : fetchRel p384SubCode 0xE = some (.store .sw sp (21 : Fin 32) 0x94, 2) := by decide
theorem ps3_at_10 : fetchRel p384SubCode 0x10 = some (.alu .add (20 : Fin 32) x0 a2, 2) := by decide
theorem ps3_at_12 : fetchRel p384SubCode 0x12 = some (.alu .add (21 : Fin 32) x0 a1, 2) := by decide
theorem ps3_at_14 : fetchRel p384SubCode 0x14 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem ps3_at_16 : fetchRel p384SubCode 0x16 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem ps3_at_18 : fetchRel p384SubCode 0x18 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem ps3_at_1c : fetchRel p384SubCode 0x1C = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem ps3_at_1e : fetchRel p384SubCode 0x1E = some (.aluImm .add (8 : Fin 32) sp 0x4, 2) := by decide
theorem ps3_at_20 : fetchRel p384SubCode 0x20 = some (.auipc ra 0x12000, 4) := by decide
theorem ps3_at_24 : fetchRel p384SubCode 0x24 = some (.jalr ra ra 0x57C, 4) := by decide
theorem ps3_at_28 : fetchRel p384SubCode 0x28 = some (.aluImm .add (19 : Fin 32) x0 0x0, 2) := by decide
theorem ps3_at_2a : fetchRel p384SubCode 0x2A = some (.aluImm .add (9 : Fin 32) x0 0xC, 2) := by decide
theorem ps3_at_2c : fetchRel p384SubCode 0x2C = some (.branch .beq (9 : Fin 32) x0 0x22, 2) := by decide
theorem ps3_at_2e : fetchRel p384SubCode 0x2E = some (.load .lw a0 (21 : Fin 32) 0x0, 4) := by decide
theorem ps3_at_32 : fetchRel p384SubCode 0x32 = some (.load .lw a1 (20 : Fin 32) 0x0, 4) := by decide
theorem ps3_at_36 : fetchRel p384SubCode 0x36 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem ps3_at_38 : fetchRel p384SubCode 0x38 = some (.auipc ra 0x0, 4) := by decide
theorem ps3_at_3c : fetchRel p384SubCode 0x3C = some (.jalr ra ra 0x9E, 4) := by decide
theorem ps3_at_40 : fetchRel p384SubCode 0x40 = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem ps3_at_42 : fetchRel p384SubCode 0x42 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x4, 2) := by decide
theorem ps3_at_44 : fetchRel p384SubCode 0x44 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem ps3_at_46 : fetchRel p384SubCode 0x46 = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4, 2) := by decide
theorem ps3_at_48 : fetchRel p384SubCode 0x48 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem ps3_at_4a : fetchRel p384SubCode 0x4A = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem ps3_at_4c : fetchRel p384SubCode 0x4C = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFE2, 2) := by decide
theorem ps3_at_4e : fetchRel p384SubCode 0x4E = some (.aluImm .add a0 sp 0x64, 2) := by decide
theorem ps3_at_50 : fetchRel p384SubCode 0x50 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem ps3_at_54 : fetchRel p384SubCode 0x54 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem ps3_at_56 : fetchRel p384SubCode 0x56 = some (.aluImm .add (8 : Fin 32) sp 0x64, 2) := by decide
theorem ps3_at_58 : fetchRel p384SubCode 0x58 = some (.auipc ra 0x12000, 4) := by decide
theorem ps3_at_5c : fetchRel p384SubCode 0x5C = some (.jalr ra ra 0x544, 4) := by decide
theorem ps3_at_60 : fetchRel p384SubCode 0x60 = some (.lui a0 0x3FCC5000, 4) := by decide
theorem ps3_at_64 : fetchRel p384SubCode 0x64 = some (.aluImm .add a0 a0 0xFFFFFC8C, 4) := by decide
theorem ps3_at_68 : fetchRel p384SubCode 0x68 = some (.aluImm .add a1 x0 0xC, 2) := by decide
theorem ps3_at_6a : fetchRel p384SubCode 0x6A = some (.branch .beq a1 x0 0x12, 2) := by decide
theorem ps3_at_6c : fetchRel p384SubCode 0x6C = some (.load .lw a2 a0 0x0, 2) := by decide
theorem ps3_at_6e : fetchRel p384SubCode 0x6E = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem ps3_at_70 : fetchRel p384SubCode 0x70 = some (.alu .and a2 a2 (19 : Fin 32), 4) := by decide
theorem ps3_at_74 : fetchRel p384SubCode 0x74 = some (.store .sw (8 : Fin 32) a2 0x0, 2) := by decide
theorem ps3_at_76 : fetchRel p384SubCode 0x76 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem ps3_at_78 : fetchRel p384SubCode 0x78 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem ps3_at_7a : fetchRel p384SubCode 0x7A = some (.branch .bne a1 x0 0xFFFFFFF2, 2) := by decide
theorem ps3_at_7c : fetchRel p384SubCode 0x7C = some (.aluImm .add a0 sp 0x34, 2) := by decide
theorem ps3_at_7e : fetchRel p384SubCode 0x7E = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem ps3_at_82 : fetchRel p384SubCode 0x82 = some (.aluImm .add (8 : Fin 32) sp 0x34, 2) := by decide
theorem ps3_at_84 : fetchRel p384SubCode 0x84 = some (.auipc ra 0x12000, 4) := by decide
theorem ps3_at_88 : fetchRel p384SubCode 0x88 = some (.jalr ra ra 0x518, 4) := by decide
theorem ps3_at_8c : fetchRel p384SubCode 0x8C = some (.aluImm .add a3 x0 0x0, 2) := by decide
theorem ps3_at_8e : fetchRel p384SubCode 0x8E = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem ps3_at_90 : fetchRel p384SubCode 0x90 = some (.aluImm .add a1 sp 0x64, 2) := by decide
theorem ps3_at_92 : fetchRel p384SubCode 0x92 = some (.aluImm .add a2 x0 0xC, 2) := by decide
theorem ps3_at_94 : fetchRel p384SubCode 0x94 = some (.branch .beq a2 x0 0x20, 2) := by decide
theorem ps3_at_96 : fetchRel p384SubCode 0x96 = some (.load .lw a4 a0 0x0, 2) := by decide
theorem ps3_at_98 : fetchRel p384SubCode 0x98 = some (.load .lw a5 a1 0x0, 2) := by decide
theorem ps3_at_9a : fetchRel p384SubCode 0x9A = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem ps3_at_9c : fetchRel p384SubCode 0x9C = some (.alu .add a3 a3 a4, 2) := by decide
theorem ps3_at_9e : fetchRel p384SubCode 0x9E = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem ps3_at_a0 : fetchRel p384SubCode 0xA0 = some (.alu .add a5 a5 a3, 2) := by decide
theorem ps3_at_a2 : fetchRel p384SubCode 0xA2 = some (.alu .sltu a4 a3 a4, 4) := by decide
theorem ps3_at_a6 : fetchRel p384SubCode 0xA6 = some (.alu .sltu a3 a5 a3, 4) := by decide
theorem ps3_at_aa : fetchRel p384SubCode 0xAA = some (.store .sw (8 : Fin 32) a5 0x0, 2) := by decide
theorem ps3_at_ac : fetchRel p384SubCode 0xAC = some (.alu .add a3 a3 a4, 2) := by decide
theorem ps3_at_ae : fetchRel p384SubCode 0xAE = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem ps3_at_b0 : fetchRel p384SubCode 0xB0 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem ps3_at_b2 : fetchRel p384SubCode 0xB2 = some (.branch .bne a2 x0 0xFFFFFFE4, 2) := by decide
theorem ps3_at_b4 : fetchRel p384SubCode 0xB4 = some (.aluImm .add a1 sp 0x34, 2) := by decide
theorem ps3_at_b6 : fetchRel p384SubCode 0xB6 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem ps3_at_ba : fetchRel p384SubCode 0xBA = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem ps3_at_bc : fetchRel p384SubCode 0xBC = some (.auipc ra 0x12000, 4) := by decide
theorem ps3_at_c0 : fetchRel p384SubCode 0xC0 = some (.jalr ra ra 0x548, 4) := by decide
theorem ps3_at_c4 : fetchRel p384SubCode 0xC4 = some (.load .lw ra sp 0xAC, 2) := by decide
theorem ps3_at_c6 : fetchRel p384SubCode 0xC6 = some (.load .lw (8 : Fin 32) sp 0xA8, 2) := by decide
theorem ps3_at_c8 : fetchRel p384SubCode 0xC8 = some (.load .lw (9 : Fin 32) sp 0xA4, 2) := by decide
theorem ps3_at_ca : fetchRel p384SubCode 0xCA = some (.load .lw (18 : Fin 32) sp 0xA0, 2) := by decide
theorem ps3_at_cc : fetchRel p384SubCode 0xCC = some (.load .lw (19 : Fin 32) sp 0x9C, 2) := by decide
theorem ps3_at_ce : fetchRel p384SubCode 0xCE = some (.load .lw (20 : Fin 32) sp 0x98, 2) := by decide
theorem ps3_at_d0 : fetchRel p384SubCode 0xD0 = some (.load .lw (21 : Fin 32) sp 0x94, 2) := by decide
theorem ps3_at_d2 : fetchRel p384SubCode 0xD2 = some (.aluImm .add sp sp 0xB0, 2) := by decide
theorem ps3_at_d4 : fetchRel p384SubCode 0xD4 = some (.jalr x0 ra 0x0, 2) := by decide

end

/-- What `sub` stores: the difference when it doesn't borrow, else the
difference plus `p`, modulo 2^384. -/
def p3SubRes (A B : Nat) : Nat := if B ≤ A then A - B else (A + 2 ^ 384 - B + p384) % 2 ^ 384

theorem p3SubRes_mod {A B : Nat} (hA : A < p384) (hB : B < p384) : p3SubRes A B = (A + p384 - B) % p384 := by
  have hp : p384 < 2 ^ 384 := by unfold p384; decide
  unfold p3SubRes
  generalize p384 = p at *
  generalize (2 : Nat) ^ 384 = K at *
  split
  · rw [show A + p - B = (A - B) + p by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [show A + K - B + p = (A + p - B) + K by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]

/-- The prologue's argument moves, from 0x10 to 0x20. -/
def psPro : List BInstr :=
  [.alu .add (20 : Fin 32) x0 a2, .alu .add (21 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0,
   .aluImm .add a0 sp 0x4, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0, .aluImm .add (8 : Fin 32) sp 0x4]

def psSubInit : List BInstr := [.aluImm .add (19 : Fin 32) x0 0x0, .aluImm .add (9 : Fin 32) x0 0xC]

/-- The start of one limb of the difference, from 0x2E to the call at 0x38. -/
def psSubHead : List BInstr := [.lw a0 (21 : Fin 32) 0x0, .lw a1 (20 : Fin 32) 0x0, .alu .add a2 x0 (19 : Fin 32)]

/-- The end of one limb of the difference, from 0x40 to 0x4C. -/
def psSubTail : List BInstr :=
  [.alu .add (19 : Fin 32) x0 a1, .aluImm .add (21 : Fin 32) (21 : Fin 32) 0x4, .sw (8 : Fin 32) a0 0x0,
   .aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4,
   .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]

def psMid1 : List BInstr :=
  [.aluImm .add a0 sp 0x64, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0, .aluImm .add (8 : Fin 32) sp 0x64]

def psMaskInit : List BInstr :=
  [.lui a0 0x3FCC5000, .aluImm .add a0 a0 0xFFFFFC8C, .aluImm .add a1 x0 0xC]

/-- One limb of the masked modulus, from 0x6C to 0x7A. -/
def psMaskBody : List BInstr :=
  [.lw a2 a0 0x0, .aluImm .add a0 a0 0x4, .alu .and a2 a2 (19 : Fin 32), .sw (8 : Fin 32) a2 0x0,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, .aluImm .add a1 a1 0xFFFFFFFF]

def psMid2 : List BInstr := [.aluImm .add a0 sp 0x34, .aluImm .add a2 x0 0x30, .aluImm .add (8 : Fin 32) sp 0x34]

def psAddInit : List BInstr :=
  [.aluImm .add a3 x0 0x0, .aluImm .add a0 sp 0x4, .aluImm .add a1 sp 0x64, .aluImm .add a2 x0 0xC]

/-- One limb of the sum, from 0x96 to 0xB2. -/
def psAddBody : List BInstr :=
  [.lw a4 a0 0x0, .lw a5 a1 0x0, .aluImm .add a0 a0 0x4, .alu .add a3 a3 a4, .aluImm .add a1 a1 0x4,
   .alu .add a5 a5 a3, .alu .sltu a4 a3 a4, .alu .sltu a3 a5 a3, .sw (8 : Fin 32) a5 0x0, .alu .add a3 a3 a4,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, .aluImm .add a2 a2 0xFFFFFFFF]

def psCpyArgs : List BInstr := [.aluImm .add a1 sp 0x34, .aluImm .add a2 x0 0x30, .alu .add a0 x0 (18 : Fin 32)]

section
set_option maxRecDepth 20000
theorem psSave_end : blockEnd p384SubCode 2 (saveBlock p3Ps) = some 0x10 := by decide
theorem psPro_end : blockEnd p384SubCode 0x10 psPro = some 0x20 := by decide
theorem psSubInit_end : blockEnd p384SubCode 0x28 psSubInit = some 0x2C := by decide
theorem psSubHead_end : blockEnd p384SubCode 0x2E psSubHead = some 0x38 := by decide
theorem psSubTail_end : blockEnd p384SubCode 0x40 psSubTail = some 0x4C := by decide
theorem psMid1_end : blockEnd p384SubCode 0x4E psMid1 = some 0x58 := by decide
theorem psMaskInit_end : blockEnd p384SubCode 0x60 psMaskInit = some 0x6A := by decide
theorem psMaskBody_end : blockEnd p384SubCode 0x6C psMaskBody = some 0x7A := by decide
theorem psMid2_end : blockEnd p384SubCode 0x7C psMid2 = some 0x84 := by decide
theorem psAddInit_end : blockEnd p384SubCode 0x8C psAddInit = some 0x94 := by decide
theorem psAddBody_end : blockEnd p384SubCode 0x96 psAddBody = some 0xB2 := by decide
theorem psCpyArgs_end : blockEnd p384SubCode 0xB4 psCpyArgs = some 0xBC := by decide
theorem psRestore_end : blockEnd p384SubCode 0xC4 (restoreBlock p3Ps) = some 0xD2 := by decide
end

/-- `borrowing_sub`'s offset from `sub`. -/
abbrev psBsub (P : Word) : Word := P + 0xD6

/-- The registers one limb of the difference leaves alone. -/
def psSubKeep (q : Fin 32) : Bool := q.val ∉ [0, 1, 8, 9, 10, 11, 12, 13, 14, 19, 20, 21]

set_option maxRecDepth 20000 in
theorem psSubHead_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock psSubHead (M, f)).1 = M ∧
    (runBlock psSubHead (M, f)).2 a0 = memLoad32 M (f 21 + 0) ∧
    (runBlock psSubHead (M, f)).2 a1 = memLoad32 M (f 20 + 0) ∧
    (runBlock psSubHead (M, f)).2 a2 = f 19 ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → (runBlock psSubHead (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, psSubHead, upd_app, ↓reduceIte]
  refine ⟨trivial, trivial, trivial, BitVec.zero_add _, fun q q0 q1 q2 => ?_⟩
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; simp [hz]
  · simp [h0, q0, q1, q2]

set_option maxRecDepth 20000 in
theorem psSubHead_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h21 : (f 21 + 0).toNat % 4 = 0) (h20 : (f 20 + 0).toNat % 4 = 0) : BlockOk base len psSubHead (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, psSubHead, upd_app, ↓reduceIte, and_true]
  exact ⟨h21, h20⟩

set_option maxRecDepth 20000 in
theorem psSubTail_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock psSubTail (M, f)).1 = memStore32 M (f 8 + 0) (f a0) ∧
    (runBlock psSubTail (M, f)).2 19 = f a1 ∧
    (runBlock psSubTail (M, f)).2 21 = f 21 + 4 ∧
    (runBlock psSubTail (M, f)).2 20 = f 20 + 4 ∧
    (runBlock psSubTail (M, f)).2 8 = f 8 + 4 ∧
    (runBlock psSubTail (M, f)).2 9 = f 9 + 0xFFFFFFFF ∧
    ∀ q, q ≠ (19 : Fin 32) → q ≠ (21 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) →
      (runBlock psSubTail (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, psSubTail, upd_app, ↓reduceIte]
  refine ⟨trivial, ?_, rfl, rfl, rfl, rfl, fun q q19 q21 q20 q8 q9 => ?_⟩
  · rw [hz]; exact BitVec.zero_add _
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [hz]
    · simp [h0, q19, q21, q20, q8, q9]

set_option maxRecDepth 20000 in
theorem psSubTail_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f 8 + 0).toNat % 4 = 0) (hs : Sep (f 8 + 0) 4 base len) : BlockOk base len psSubTail (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, psSubTail, upd_app, ↓reduceIte, and_true, true_and]
  exact ⟨h, hs⟩

/-- **One limb of the difference**, from 0x2E: subtract limb `i` of the
right operand and the borrow from limb `i` of the left operand, and store
the difference at limb `i` of the buffer at `D`. `borrowing_sub` also writes
the word below `sp`. -/
theorem ps_sub_iter {M : Word → BitVec 8} {P F lp rp D b : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x2E (reg n)) (hc : CodeIn M P p384SubCode) (hb : CodeIn M (psBsub P) borrowingSubCode)
    (hP : P.toNat % 2 = 0) (hi : i < 12) (hF : F.toNat % 4 = 0) (hlp : lp.toNat % 4 = 0)
    (hrp : rp.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (psBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P p384SubCode.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P p384SubCode.length)
    (rsp : reg n sp = F) (r21 : reg n 21 = lp + BitVec.ofNat 32 (4 * i))
    (r20 : reg n 20 = rp + BitVec.ofNat 32 (4 * i)) (r8 : reg n 8 = D + BitVec.ofNat 32 (4 * i))
    (r9 : reg n 9 = BitVec.ofNat 32 (12 - i)) (r19 : reg n 19 = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 M (rp + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < 12 then 0x2E else 0x4E) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' 19 = bsubB (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 M (rp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 M (rp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' 21 = lp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' 20 = rp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' 8 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' 9 = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, psSubKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨E1, Ea0, Ea1, Ea2, Ek⟩ := psSubHead_run (M := M) (f := reg n) hz
  obtain ⟨n1, c1, u1⟩ := St.block psSubHead s hc psSubHead_end
    (psSubHead_ok (by rw [r21, add_lit_zero]; exact aligned_add hlp (by omega))
      (by rw [r20, add_lit_zero]; exact aligned_add hrp (by omega)))
  rw [E1] at u1
  rw [r21, add_lit_zero] at Ea0
  rw [r20, add_lit_zero] at Ea1
  rw [r19] at Ea2
  have g1 : ∀ q, reg n1 q = (runBlock psSubHead (M, reg n)).2 q := u1.regs
  obtain ⟨n3, c3, u3, a03, a13, sp3, fr3, mem3⟩ := u1.self.bsubCall hc hb (even_at P hP 0xD6 (by decide))
    ps3_at_38 ps3_at_3c (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x38 + 8) (by decide))
    (by rw [g1, Ek sp (by decide) (by decide) (by decide), rsp]) hF sFB
  simp only [g1] at a03 a13
  rw [Ea0, Ea1, Ea2] at a03 a13
  have hc3 : CodeIn n3.mem P p384SubCode := fun j hj => by
    rw [mem3 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n3 q = reg n q :=
    fun q q0 q1 q2 q3 q4 qr => by rw [fr3 q q0 q1 q2 q3 q4 qr, g1, Ek q q0 q1 q2]
  have e8 : reg n3 8 + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8, add_lit_zero]
  obtain ⟨n4, c4, u4⟩ := St.block psSubTail u3 hc3 psSubTail_end
    (psSubTail_ok (by rw [e8]; exact aligned_add hD (by omega)) (by rw [e8]; exact sDC))
  obtain ⟨em4, t19, t21, t20, t8, t9, tk⟩ := psSubTail_run (M := n3.mem) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [em4, e8, a03] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock psSubTail (n3.mem, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := bsubD (memLoad32 M (lp + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (rp + BitVec.ofNat 32 (4 * i))) b) hc3 sDC
  have k3' : ∀ r, r = (21 : Fin 32) ∨ r = (20 : Fin 32) ∨ r = (8 : Fin 32) ∨ r = (9 : Fin 32) → reg n3 r = reg n r :=
    fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl <;>
      exact k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e9 : reg n4 9 = BitVec.ofNat 32 (12 - (i + 1)) := by
    rw [g4, t9, k3' 9 (by decide), r9, cnt12_dec i hi]
  have hb4 : branchTaken .bne (reg n4 9) (reg n4 x0) = decide (i + 1 < 12) := by
    rw [e9, u4'.zero]; exact cnt12_ne i hi
  have post : ∀ n5 : Machine, (∀ q, reg n5 q = reg n4 q) →
      reg n5 19 = bsubB (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 M (rp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 M (rp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n5 sp = F ∧ reg n5 21 = lp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 20 = rp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n5 8 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 9 = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, psSubKeep q = true → reg n5 q = reg n q := fun n5 h5 => by
    refine ⟨by rw [h5, g4, t19, a13], by rw [h5, g4, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3],
      by rw [h5, g4, t21, k3' 21 (by decide), r21, ptr4], by rw [h5, g4, t20, k3' 20 (by decide), r20, ptr4],
      by rw [h5, g4, t8, k3' 8 (by decide), r8, ptr4], by rw [h5, e9], fun q hq => ?_⟩
    rw [h5, g4, tk q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl),
      k3 q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)]
  by_cases hl : i + 1 < 12
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x2E ps3_at_4c (by decide) (by rw [hb4]; exact decide_eq_true hl)
    exact ⟨n5, n3.mem, c1.trans (c3.trans (c4.trans (.single d5))), by rw [ite_eq_left hl]; exact u5.self,
      mem3, post n5 u5.regs⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x4E ps3_at_4c (by decide) (by rw [hb4]; exact decide_eq_false hl)
    exact ⟨n5, n3.mem, c1.trans (c3.trans (c4.trans (.single d5))), by rw [ite_eq_right hl]; exact u5.self,
      mem3, post n5 u5.regs⟩

/-- **The difference**, from limb `i` to the loop's exit at 0x4E: the buffer
at `D` gets the left operand minus the right one, and `s3` the borrow out as
a mask. -/
theorem ps_sub_loop {P F lp rp D : Word} {M0 : Word → BitVec 8} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hlp : lp.toNat % 4 = 0) (hrp : rp.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 48 ≤ 2 ^ 32)
    (sFA : Sep (F + 0xFFFFFFFC) 4 lp 48) (sFN : Sep (F + 0xFFFFFFFC) 4 rp 48) (sFD : Sep (F + 0xFFFFFFFC) 4 D 48)
    (sDA : Sep D 48 lp 48) (sDN : Sep D 48 rp 48)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (psBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P p384SubCode.length)
    (sDB : Sep D 48 (psBsub P) borrowingSubCode.length) (sDC : Sep D 48 P p384SubCode.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x2E (reg n) → CodeIn M P p384SubCode → CodeIn M (psBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 lp i + 2 ^ (32 * i) * maskBit b = accV M0 rp i + accV M D i →
      reg n sp = F → reg n 21 = lp + BitVec.ofNat 32 (4 * i) → reg n 20 = rp + BitVec.ofNat 32 (4 * i) →
      reg n 8 = D + BitVec.ofNat 32 (4 * i) → reg n 9 = BitVec.ofNat 32 (12 - i) → reg n 19 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x4E (reg n') ∧ CodeIn M' P p384SubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' 19 = 0 ∨ reg n' 19 = 0xFFFFFFFF) ∧
        accV M0 lp 12 + 2 ^ (32 * 12) * maskBit (reg n' 19) = accV M0 rp 12 + accV M' D 12 ∧
        reg n' sp = F ∧ ∀ q, psSubKeep q = true → reg n' q = reg n q := by
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x2E (reg n) → CodeIn M P p384SubCode → CodeIn M (psBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 lp i + 2 ^ (32 * i) * maskBit b = accV M0 rp i + accV M D i →
      reg n sp = F → reg n 21 = lp + BitVec.ofNat 32 (4 * i) → reg n 20 = rp + BitVec.ofNat 32 (4 * i) →
      reg n 8 = D + BitVec.ofNat 32 (4 * i) → reg n 9 = BitVec.ofNat 32 (12 - i) → reg n 19 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0x2E else 0x4E) (reg n') ∧
        CodeIn M' P p384SubCode ∧ CodeIn M' (psBsub P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' 19 = 0 ∨ reg n' 19 = 0xFFFFFFFF) ∧
        accV M0 lp (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' 19) = accV M0 rp (i + 1) + accV M' D (i + 1) ∧
        reg n' sp = F ∧ reg n' 21 = lp + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' 20 = rp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' 8 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' 9 = BitVec.ofNat 32 (12 - (i + 1)) ∧
        ∀ q, psSubKeep q = true → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp r21 r20 r8 r9 r19
    obtain ⟨n1, Mb, c1, u1, hMb, e19, esp, e21, e20, e8, e9, fr⟩ := ps_sub_iter (i := i) s hc hb hP hi hF hlp hrp hD
      sFB sFC (sDC.sub (by omega)) rsp r21 r20 r8 r9 r19
    have eA : memLoad32 M (lp + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (lp + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFA.subR (by omega)) (sDA.subR (by omega))
    have eN : memLoad32 M (rp + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (rp + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    rw [eA, eN] at u1 e19
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (rp + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb (psBsub P) borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb P p384SubCode := fun j hj => by
      rw [hMb _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    refine ⟨n1, _, c1, u1, CodeIn.store32 hCb (sDC.sub (by omega)), CodeIn.store32 hDb (sDB.sub (by omega)),
      fun x hx hd => ?_, by rw [e19]; exact bm, ?_, esp, e21, e20, e8, e9, fr⟩
    · rw [memStore32_get_sep (hd.sub (c := 4 * i) (l := 4) (by omega)), hMb x hx, hfr x hx hd]
    · have hA : accV (memStore32 Mb (D + BitVec.ofNat 32 (4 * i)) (bsubD (memLoad32 M0 (lp + BitVec.ofNat 32 (4 * i)))
          (memLoad32 M0 (rp + BitVec.ofNat 32 (4 * i))) b)) D (i + 1) = accV M D i +
          (bsubD (memLoad32 M0 (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (rp + BitVec.ofNat 32 (4 * i))) b).toNat *
            2 ^ (32 * i) := by
        rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same]
        congr 1
        exact accV_congr i fun j hj => memLoad32_congr fun q hq =>
          hMb _ ((sFD.subR (c := 4 * j) (l := 4) (by omega)).subR (c := q) (l := 1) (by omega))
      rw [hA, accV_succ1, accV_succ1, pow32_succ, e19]
      exact sub_arith hv bv
  intro m
  induction m with
  | zero =>
    intro i hi M n b s hc hb hfr hbm hv rsp r21 r20 r8 r9 r19
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, _, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step 11 (by decide) s hc hb hfr hbm hv rsp r21 r20 r8 r9 r19
    exact ⟨n1, M1, c1, u1, hc1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp r21 r20 r8 r9 r19
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, e21, e20, e8, e9, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hb hfr hbm hv rsp r21 r20 r8 r9 r19
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 hv1 sp1 e21 e20 e8 e9 rfl
    exact ⟨n', M', c1.trans c', u', hc', hf', hm', hv', sp', fun q hq => by rw [fr' q hq, fr q hq]⟩


theorem and_ones (w : Word) : w &&& 0xFFFFFFFF = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  have : (0xFFFFFFFF : Word).getLsbD i = true :=
    (by decide : ∀ i : Fin 32, (0xFFFFFFFF : Word).getLsbD i.val = true) ⟨i, hi⟩
  rw [this, Bool.and_true]

/-- A word masked with a borrow mask is the word or zero. -/
theorem and_mask (w b : Word) (hb : b = 0 ∨ b = 0xFFFFFFFF) : (aluEval .and w b).toNat = w.toNat * maskBit b := by
  rcases hb with rfl | rfl
  · show (w &&& 0#32).toNat = _
    rw [BitVec.and_zero, maskBit_zero']; rfl
  · show (w &&& 0xFFFFFFFF).toNat = _
    rw [and_ones, show maskBit 0xFFFFFFFF = 1 by unfold maskBit; decide, Nat.mul_one]

/-- The registers one limb of the masked modulus leaves alone. -/
def psMaskKeep (q : Fin 32) : Bool := q.val ∉ [0, 8, 10, 11, 12]

set_option maxRecDepth 20000 in
theorem psMaskBody_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock psMaskBody (M, f)).1 = memStore32 M (f 8 + 0) (aluEval .and (memLoad32 M (f a0 + 0)) (f 19)) ∧
    (runBlock psMaskBody (M, f)).2 a0 = f a0 + 4 ∧ (runBlock psMaskBody (M, f)).2 8 = f 8 + 4 ∧
    (runBlock psMaskBody (M, f)).2 a1 = f a1 + 0xFFFFFFFF ∧
    ∀ q, psMaskKeep q = true → (runBlock psMaskBody (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, psMaskBody, upd_app, ↓reduceIte]
  refine ⟨trivial, rfl, rfl, rfl, fun q hq => ?_⟩
  have h0 : q.val ≠ 0 := fun e => absurd (show psMaskKeep q = false by unfold psMaskKeep; simp [e]) (by rw [hq]; decide)
  simp only [h0, ite_false, pkeep_ne (r := 8) hq rfl, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl,
    pkeep_ne (r := a2) hq rfl]

set_option maxRecDepth 20000 in
theorem psMaskBody_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (ha : (f a0 + 0).toNat % 4 = 0) (h8 : (f 8 + 0).toNat % 4 = 0) (hs : Sep (f 8 + 0) 4 base len) :
    BlockOk base len psMaskBody (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, psMaskBody, upd_app, ↓reduceIte, and_true, true_and]
  exact ⟨ha, h8, hs⟩

/-- **One limb of the masked modulus**, from 0x6C: store limb `i` of the
modulus, masked with `b`, at limb `i` of the buffer at `E`. -/
theorem ps_mask_iter {M : Word → BitVec 8} {P E b : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x6C (reg n)) (hc : CodeIn M P p384SubCode) (hi : i < 12) (hE : E.toNat % 4 = 0)
    (sC : Sep (E + BitVec.ofNat 32 (4 * i)) 4 P p384SubCode.length)
    (ra0 : reg n a0 = p3M + BitVec.ofNat 32 (4 * i)) (r8 : reg n 8 = E + BitVec.ofNat 32 (4 * i))
    (ra1 : reg n a1 = BitVec.ofNat 32 (12 - i)) (r19 : reg n 19 = b) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (E + BitVec.ofNat 32 (4 * i)) (aluEval .and (memLoad32 M (p3M + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < 12 then 0x6C else 0x7C) (reg n') ∧
      reg n' a0 = p3M + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' 8 = E + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' a1 = BitVec.ofNat 32 (12 - (i + 1)) ∧ ∀ q, psMaskKeep q = true → reg n' q = reg n q := by
  obtain ⟨E1, Ea0, E8, Ea1, Ek⟩ := psMaskBody_run (M := M) (f := reg n)
  obtain ⟨n1, c1, u1⟩ := St.block psMaskBody s hc psMaskBody_end
    (psMaskBody_ok (by rw [ra0, add_lit_zero]; exact aligned_add (show p3M.toNat % 4 = 0 by decide) (by omega))
      (by rw [r8, add_lit_zero]; exact aligned_add hE (by omega)) (by rw [r8, add_lit_zero]; exact sC))
  rw [E1, r8, ra0, r19, add_lit_zero, add_lit_zero] at u1
  have hc1 := CodeIn.store32 (v := aluEval .and (memLoad32 M (p3M + BitVec.ofNat 32 (4 * i))) b) hc sC
  have ea1 : reg n1 a1 = BitVec.ofNat 32 (12 - (i + 1)) := by rw [u1.regs, Ea1, ra1, cnt12_dec i hi]
  have hb : branchTaken .bne (reg n1 a1) (reg n1 x0) = decide (i + 1 < 12) := by
    rw [ea1, u1.self.zero]; exact cnt12_ne i hi
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a0 = p3M + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 8 = E + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n2 a1 = BitVec.ofNat 32 (12 - (i + 1)) ∧ ∀ q, psMaskKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, u1.regs, Ea0, ra0, ptr4], by rw [h2, u1.regs, E8, r8, ptr4], by rw [h2, ea1],
      fun q hq => by rw [h2, u1.regs, Ek q hq]⟩
  by_cases hl : i + 1 < 12
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0x6C ps3_at_7a (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x7C ps3_at_7a (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- **The masked modulus**, from limb `i` to the loop's exit at 0x7C: the
buffer at `E` holds the modulus times the borrow bit. -/
theorem ps_mask_loop {P E b : Word} {M1 : Word → BitVec 8} (hE : E.toNat % 4 = 0) (hEw : E.toNat + 0x30 ≤ 2 ^ 32)
    (hb : b = 0 ∨ b = 0xFFFFFFFF) (sEP : Sep E 0x30 p3M 48) (sC : Sep E 0x30 P p384SubCode.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M P n 0x6C (reg n) → CodeIn M P p384SubCode → (∀ x, Sep E 0x30 x 1 → M x = M1 x) →
      accV M E i = accV M1 p3M i * maskBit b →
      reg n a0 = p3M + BitVec.ofNat 32 (4 * i) → reg n 8 = E + BitVec.ofNat 32 (4 * i) →
      reg n a1 = BitVec.ofNat 32 (12 - i) → reg n 19 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x7C (reg n') ∧ CodeIn M' P p384SubCode ∧
        (∀ x, Sep E 0x30 x 1 → M' x = M1 x) ∧ accV M' E 12 = accV M1 p3M 12 * maskBit b ∧
        reg n' a1 = 0 ∧ ∀ q, psMaskKeep q = true → reg n' q = reg n q := by
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M P n 0x6C (reg n) → CodeIn M P p384SubCode → (∀ x, Sep E 0x30 x 1 → M x = M1 x) →
      accV M E i = accV M1 p3M i * maskBit b →
      reg n a0 = p3M + BitVec.ofNat 32 (4 * i) → reg n 8 = E + BitVec.ofNat 32 (4 * i) →
      reg n a1 = BitVec.ofNat 32 (12 - i) → reg n 19 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0x6C else 0x7C) (reg n') ∧ CodeIn M' P p384SubCode ∧
        (∀ x, Sep E 0x30 x 1 → M' x = M1 x) ∧ accV M' E (i + 1) = accV M1 p3M (i + 1) * maskBit b ∧
        reg n' a0 = p3M + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' 8 = E + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' a1 = BitVec.ofNat 32 (12 - (i + 1)) ∧ ∀ q, psMaskKeep q = true → reg n' q = reg n q := by
    intro i hi M n s hc hfr hv ra0 r8 ra1 r19
    have sCi : Sep (E + BitVec.ofNat 32 (4 * i)) 4 P p384SubCode.length := sC.sub (by omega)
    obtain ⟨n1, c1, u1, ea0, e8, ea1, fr⟩ := ps_mask_iter s hc hi hE sCi ra0 r8 ra1 r19
    have eP : memLoad32 M (p3M + BitVec.ofNat 32 (4 * i)) = memLoad32 M1 (p3M + BitVec.ofNat 32 (4 * i)) :=
      load_frame hfr (sEP.subR (by omega))
    rw [eP] at u1
    refine ⟨n1, _, c1, u1, hc.store32 sCi, fun x hx => ?_, ?_, ea0, e8, ea1, fr⟩
    · rw [memStore32_get_sep (hx.sub (c := 4 * i) (l := 4) (by omega)), hfr x hx]
    · rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same, accV_succ1, hv,
        and_mask _ _ hb, Nat.add_mul, Nat.mul_right_comm]
  intro m
  induction m with
  | zero =>
    intro i hi M n s hc hfr hv ra0 r8 ra1 r19
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M', c1, u1, hc1, hf1, hv1, _, _, ea1, fr⟩ := step 11 (by decide) s hc hfr hv ra0 r8 ra1 r19
    exact ⟨n1, M', c1, u1, hc1, hf1, hv1, ea1, fr⟩
  | succ m ih =>
    intro i hi M n s hc hfr hv ra0 r8 ra1 r19
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M', c1, u1, hc1, hf1, hv1, ea0, e8, ea1, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hfr hv ra0 r8 ra1 r19
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M'', c', u', hc', hf', hv', ha', fr'⟩ := ih (i + 1) (sel_succ hi) u1 hc1 hf1 hv1 ea0 e8 ea1
      (by rw [fr 19 rfl, r19])
    exact ⟨n', M'', c1.trans c', u', hc', hf', hv', ha', fun q hq => by rw [fr' q hq, fr q hq]⟩

/-- The registers one limb of the sum leaves alone. -/
def psAddKeep (q : Fin 32) : Bool := q.val ∉ [0, 8, 10, 11, 12, 13, 14, 15]

set_option maxRecDepth 20000 in
theorem psAddBody_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock psAddBody (M, f)).1 = memStore32 M (f 8 + 0)
      (aluEval .add (memLoad32 M (f a1 + 0)) (aluEval .add (f a3) (memLoad32 M (f a0 + 0)))) ∧
    (runBlock psAddBody (M, f)).2 a3 =
      aluEval .add (aluEval .sltu (aluEval .add (memLoad32 M (f a1 + 0)) (aluEval .add (f a3) (memLoad32 M (f a0 + 0))))
        (aluEval .add (f a3) (memLoad32 M (f a0 + 0))))
        (aluEval .sltu (aluEval .add (f a3) (memLoad32 M (f a0 + 0))) (memLoad32 M (f a0 + 0))) ∧
    (runBlock psAddBody (M, f)).2 a0 = f a0 + 4 ∧ (runBlock psAddBody (M, f)).2 a1 = f a1 + 4 ∧
    (runBlock psAddBody (M, f)).2 8 = f 8 + 4 ∧ (runBlock psAddBody (M, f)).2 a2 = f a2 + 0xFFFFFFFF ∧
    ∀ q, psAddKeep q = true → (runBlock psAddBody (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, psAddBody, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 6
  have h0 : q.val ≠ 0 := fun e => absurd (show psAddKeep q = false by unfold psAddKeep; simp [e]) (by rw [hq]; decide)
  simp only [h0, ite_false, pkeep_ne (r := 8) hq rfl, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl,
    pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a3) hq rfl, pkeep_ne (r := a4) hq rfl, pkeep_ne (r := a5) hq rfl]
  all_goals first | trivial | rfl

set_option maxRecDepth 20000 in
theorem psAddBody_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h9 : (f a0 + 0).toNat % 4 = 0) (h20 : (f a1 + 0).toNat % 4 = 0) (h8 : (f 8 + 0).toNat % 4 = 0)
    (hs : Sep (f 8 + 0) 4 base len) : BlockOk base len psAddBody (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, psAddBody, upd_app, ↓reduceIte, and_true, true_and]
  exact ⟨h9, h20, h8, hs⟩

/-- **One limb of the sum**, from 0x96: add limb `i` of both operands and the
carry, and store the limb at `F + 4 i`. -/
theorem ps_add_iter {M : Word → BitVec 8} {P F lp rp c : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x96 (reg n)) (hc : CodeIn M P p384SubCode) (hi : i < 12)
    (hF : F.toNat % 4 = 0) (hlp : lp.toNat % 4 = 0) (hrp : rp.toNat % 4 = 0)
    (sC : Sep (F + BitVec.ofNat 32 (4 * i)) 4 P p384SubCode.length)
    (r9 : reg n a0 = lp + BitVec.ofNat 32 (4 * i)) (r20 : reg n a1 = rp + BitVec.ofNat 32 (4 * i))
    (r8 : reg n 8 = F + BitVec.ofNat 32 (4 * i)) (ra2 : reg n a2 = BitVec.ofNat 32 (12 - i)) (r19 : reg n a3 = c) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (F + BitVec.ofNat 32 (4 * i)) (aluEval .add (memLoad32 M (rp + BitVec.ofNat 32 (4 * i)))
          (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))))))
        P n' (if i + 1 < 12 then 0x96 else 0xB4) (reg n') ∧
      reg n' a3 = aluEval .add (aluEval .sltu (aluEval .add (memLoad32 M (rp + BitVec.ofNat 32 (4 * i)))
          (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i)))))
          (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i)))))
        (aluEval .sltu (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))))
          (memLoad32 M (lp + BitVec.ofNat 32 (4 * i)))) ∧
      reg n' a0 = lp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a1 = rp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' 8 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a2 = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, psAddKeep q = true → reg n' q = reg n q := by
  obtain ⟨E1, E19, E9, E20, E8, Ea2, Ek⟩ := psAddBody_run (M := M) (f := reg n)
  obtain ⟨n1, c1, u1⟩ := St.block psAddBody s hc psAddBody_end
    (psAddBody_ok (by rw [r9, add_lit_zero]; exact aligned_add hlp (by omega))
      (by rw [r20, add_lit_zero]; exact aligned_add hrp (by omega))
      (by rw [r8, add_lit_zero]; exact aligned_add hF (by omega)) (by rw [r8, add_lit_zero]; exact sC))
  rw [E1, r8, r9, r20, r19, add_lit_zero, add_lit_zero, add_lit_zero] at u1
  rw [r9, r20, r19, add_lit_zero, add_lit_zero] at E19
  have hc1 := CodeIn.store32 (v := aluEval .add (memLoad32 M (rp + BitVec.ofNat 32 (4 * i)))
    (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))))) hc sC
  have ea2 : reg n1 a2 = BitVec.ofNat 32 (12 - (i + 1)) := by rw [u1.regs, Ea2, ra2, cnt12_dec i hi]
  have hb : branchTaken .bne (reg n1 a2) (reg n1 x0) = decide (i + 1 < 12) := by
    rw [ea2, u1.self.zero]; exact cnt12_ne i hi
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a3 = aluEval .add (aluEval .sltu (aluEval .add (memLoad32 M (rp + BitVec.ofNat 32 (4 * i)))
          (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i)))))
          (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i)))))
        (aluEval .sltu (aluEval .add c (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))))
          (memLoad32 M (lp + BitVec.ofNat 32 (4 * i)))) ∧
      reg n2 a0 = lp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a1 = rp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n2 8 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a2 = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, psAddKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, u1.regs, E19], by rw [h2, u1.regs, E9, r9, ptr4], by rw [h2, u1.regs, E20, r20, ptr4],
      by rw [h2, u1.regs, E8, r8, ptr4], by rw [h2, ea2], fun q hq => by rw [h2, u1.regs, Ek q hq]⟩
  by_cases hl : i + 1 < 12
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0x96 ps3_at_b2 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0xB4 ps3_at_b2 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- **The sum**, from limb `i` to the loop's exit at 0xB4: the buffer at `F`
and the carry in `s3` hold the two operands' sum. -/
theorem ps_add_loop {P F lp rp : Word} {M1 : Word → BitVec 8} (hF : F.toNat % 4 = 0)
    (hFw : F.toNat + 0x30 ≤ 2 ^ 32) (hlp : lp.toNat % 4 = 0) (hrp : rp.toNat % 4 = 0)
    (sL : Sep F 0x30 lp 48) (sR : Sep F 0x30 rp 48) (sC : Sep F 0x30 P p384SubCode.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine} {c : Word},
      St M P n 0x96 (reg n) → CodeIn M P p384SubCode → (∀ x, Sep F 0x30 x 1 → M x = M1 x) → c.toNat ≤ 1 →
      accV M F i + 2 ^ (32 * i) * c.toNat = accV M1 lp i + accV M1 rp i →
      reg n a0 = lp + BitVec.ofNat 32 (4 * i) → reg n a1 = rp + BitVec.ofNat 32 (4 * i) →
      reg n 8 = F + BitVec.ofNat 32 (4 * i) → reg n a2 = BitVec.ofNat 32 (12 - i) → reg n a3 = c →
      ∃ n' M', Steps n n' ∧ St M' P n' 0xB4 (reg n') ∧ CodeIn M' P p384SubCode ∧
        (∀ x, Sep F 0x30 x 1 → M' x = M1 x) ∧ (reg n' a3).toNat ≤ 1 ∧
        accV M' F 12 + 2 ^ (32 * 12) * (reg n' a3).toNat = accV M1 lp 12 + accV M1 rp 12 ∧
        ∀ q, psAddKeep q = true → reg n' q = reg n q := by
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine} {c : Word},
      St M P n 0x96 (reg n) → CodeIn M P p384SubCode → (∀ x, Sep F 0x30 x 1 → M x = M1 x) → c.toNat ≤ 1 →
      accV M F i + 2 ^ (32 * i) * c.toNat = accV M1 lp i + accV M1 rp i →
      reg n a0 = lp + BitVec.ofNat 32 (4 * i) → reg n a1 = rp + BitVec.ofNat 32 (4 * i) →
      reg n 8 = F + BitVec.ofNat 32 (4 * i) → reg n a2 = BitVec.ofNat 32 (12 - i) → reg n a3 = c →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0x96 else 0xB4) (reg n') ∧
        CodeIn M' P p384SubCode ∧ (∀ x, Sep F 0x30 x 1 → M' x = M1 x) ∧ (reg n' a3).toNat ≤ 1 ∧
        accV M' F (i + 1) + 2 ^ (32 * (i + 1)) * (reg n' a3).toNat = accV M1 lp (i + 1) + accV M1 rp (i + 1) ∧
        reg n' a0 = lp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a1 = rp + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' 8 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a2 = BitVec.ofNat 32 (12 - (i + 1)) ∧
        ∀ q, psAddKeep q = true → reg n' q = reg n q := by
    intro i hi M n c s hc hfr hcb hv r9 r20 r8 ra2 r19
    have sCi : Sep (F + BitVec.ofNat 32 (4 * i)) 4 P p384SubCode.length := sC.sub (by omega)
    obtain ⟨n1, c1, u1, e19, e9, e20, e8, ea2, fr⟩ := ps_add_iter s hc hi hF hlp hrp sCi r9 r20 r8 ra2 r19
    have eL : memLoad32 M (lp + BitVec.ofNat 32 (4 * i)) = memLoad32 M1 (lp + BitVec.ofNat 32 (4 * i)) :=
      load_frame hfr (sL.subR (by omega))
    have eR : memLoad32 M (rp + BitVec.ofNat 32 (4 * i)) = memLoad32 M1 (rp + BitVec.ofNat 32 (4 * i)) :=
      load_frame hfr (sR.subR (by omega))
    rw [eL, eR] at u1 e19
    obtain ⟨hv1, hc1⟩ := adc_val (memLoad32 M1 (lp + BitVec.ofNat 32 (4 * i)))
      (memLoad32 M1 (rp + BitVec.ofNat 32 (4 * i))) c hcb
    refine ⟨n1, _, c1, u1, hc.store32 sCi, fun x hx => ?_, by rw [e19]; exact hc1, ?_, e9, e20, e8, ea2, fr⟩
    · rw [memStore32_get_sep (hx.sub (c := 4 * i) (l := 4) (by omega)), hfr x hx]
    · rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same, accV_succ1,
        accV_succ1, pow32_succ, e19]
      exact adc_arith hv hv1
  intro m
  induction m with
  | zero =>
    intro i hi M n c s hc hfr hcb hv r9 r20 r8 ra2 r19
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M', c1, u1, hc1, hf1, hb1, hv1, _, _, _, _, fr⟩ := step 11 (by decide) s hc hfr hcb hv r9 r20 r8 ra2 r19
    exact ⟨n1, M', c1, u1, hc1, hf1, hb1, hv1, fr⟩
  | succ m ih =>
    intro i hi M n c s hc hfr hcb hv r9 r20 r8 ra2 r19
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M', c1, u1, hc1, hf1, hb1, hv1, e9, e20, e8, ea2, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hfr hcb hv r9 r20 r8 ra2 r19
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M'', c', u', hc', hf', hb', hv', fr'⟩ := ih (i + 1) (sel_succ hi) u1 hc1 hf1 hb1 hv1 e9 e20 e8 ea2 rfl
    exact ⟨n', M'', c1.trans c', u', hc', hf', hb', hv', fun q hq => by rw [fr' q hq, fr q hq]⟩



/-- What the final select leaves: the difference when there was no borrow,
else the difference plus `p`, modulo 2^384. -/
theorem ps_final {A B D S c mb : Nat} (hD : D < 2 ^ 384) (hS : S < 2 ^ 384) (hc : c ≤ 1) (hmb : mb ≤ 1)
    (hsub : A + 2 ^ 384 * mb = B + D) (hadd : S + 2 ^ 384 * c = D + p384 * mb) : S = p3SubRes A B := by
  have hp : p384 < 2 ^ 384 := by unfold p384; decide
  unfold p3SubRes
  generalize p384 = p at *
  generalize (2 : Nat) ^ 384 = K at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hmb with rfl | rfl
  · simp only [Nat.mul_zero, Nat.add_zero] at hsub hadd
    rw [ite_eq_left (by omega)]; omega
  · simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hsub hadd
    rw [ite_eq_right (by omega), show A + K - B + p = S by omega, Nat.mod_eq_of_lt hS]
  · simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hsub hadd
    omega
  · simp only [Nat.mul_one] at hsub hadd
    rw [ite_eq_right (by omega), show A + K - B + p = S + K by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hS]

/-- Where `sub` runs: its code and its callees' at their offsets from an
even `P`, the modulus where the image keeps it, the 0xB4 bytes of stack
below `sp0` that it and `borrowing_sub` use, the 12-word result at `out`,
and the operands at `lp` and `rp`, all apart where they must be. -/
structure PSEnv (M : Word → BitVec 8) (P sp0 out lp rp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P p384SubCode
  mset : CodeIn M (P + 0x1259C) memsetCode
  bsub : CodeIn M (psBsub P) borrowingSubCode
  stub : CodeIn M (P + 0x12604) memcpyStubCode
  body : CodeIn M (P + 0x1260C) memcpyBodyCode
  pmod : CodeIn M p3M p384ModulusData
  hsp : sp0.toNat % 4 = 0
  hS : 0xB4 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hlp : lp.toNat % 4 = 0
  hrp : rp.toNat % 4 = 0
  hwo : out.toNat + 48 < 2 ^ 32
  sSC : Sep (sp0 + 0xFFFFFF4C) 0xB4 P p384SubCode.length
  sSM : Sep (sp0 + 0xFFFFFF4C) 0xB4 (P + 0x1259C) memsetCode.length
  sSB : Sep (sp0 + 0xFFFFFF4C) 0xB4 (psBsub P) borrowingSubCode.length
  sSU : Sep (sp0 + 0xFFFFFF4C) 0xB4 (P + 0x12604) memcpyStubCode.length
  sSY : Sep (sp0 + 0xFFFFFF4C) 0xB4 (P + 0x1260C) memcpyBodyCode.length
  sSP : Sep (sp0 + 0xFFFFFF4C) 0xB4 p3M 48
  sOC : Sep out 48 P p384SubCode.length
  sOY : Sep out 48 (P + 0x1260C) memcpyBodyCode.length
  sOS : Sep out 48 (sp0 + 0xFFFFFF4C) 0xB4
  sLS : Sep lp 48 (sp0 + 0xFFFFFF4C) 0xB4
  sRS : Sep rp 48 (sp0 + 0xFFFFFF4C) 0xB4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `sub`'s prologue, from entry to the subtraction loop at 0x2E. -/
theorem ps_pro (m : Machine) {P sp0 out lp rp : Word} (env : PSEnv m.mem P sp0 out lp rp) (hpc : m.pc = P)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = lp) (ha2 : reg m a2 = rp) (hsp : reg m sp = sp0) :
    ∃ n M, Steps m n ∧ St M P n 0x2E (reg n) ∧
      (∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ p3Ps → memLoad32 M (sp0 + 0xFFFFFF50 + o) = reg m r) ∧
      reg n sp = sp0 + 0xFFFFFF50 ∧ reg n 21 = lp + BitVec.ofNat 32 (4 * 0) ∧
      reg n 20 = rp + BitVec.ofNat 32 (4 * 0) ∧
      reg n 8 = sp0 + 0xFFFFFF50 + BitVec.ofNat 32 4 + BitVec.ofNat 32 (4 * 0) ∧
      reg n 9 = BitVec.ofNat 32 (12 - 0) ∧ reg n 19 = 0 ∧ reg n 18 = out ∧
      ∀ q, p3Keep q = true → reg n q = reg m q := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hGw := p3G_w sp0 env.hS
  have hFa : (sp0 + 0xFFFFFF50).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF50) (by decide)
  have hFw : (sp0 + 0xFFFFFF50).toNat + 0xB0 ≤ 2 ^ 32 := by
    rw [← p3G_F, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have sFC : Sep (sp0 + 0xFFFFFF50) 0xB0 P p384SubCode.length := by
    have := p3inF' (c := 0) (l := 0xB0) (by decide) env.sSC; rwa [add_ofNat_zero] at this
  have fF : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Sep (sp0 + 0xFFFFFF50) 0xB0 x 1 := fun x hx => by
    have := p3inF (c := 0) (l := 0xB0) (by decide) hx; rwa [add_ofNat_zero] at this
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code ps3_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF50) sp = sp0 + 0xFFFFFF50 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [hsp]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock p3Ps) u1 env.code psSave_end (saveBlock_ok _ p3Ps _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (p3Ps_range p hp).1, frm_sep' sFC (by have := p3Ps_range p hp; omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (sp0 + 0xFFFFFF50)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF50)) p3Ps = Msv := ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; exact saveMem_outside p3Ps fun p hp => frm_sep' (fF x hx) (by have := p3Ps_range p hp; omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFF4C) 0xB4 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have k2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q hq => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, hq]
  have sp2 : reg m2 sp = sp0 + 0xFFFFFF50 := by rw [u2.regs]; exact sp1
  obtain ⟨m3, c3, u3⟩ := St.block psPro u2.self (cIn env.code env.sSC frSv) psPro_end
    (by simp [BlockOk, BInstr.ok, psPro])
  simp only [runBlock, BInstr.run, psPro] at u3
  have g3 : ∀ q, reg m3 q = _ := u3.regs
  obtain ⟨m4, c4, u4, a04, k4⟩ := St.memsetW (B := P + 0x1259C) (w := 12)
    (dst := sp0 + 0xFFFFFF50 + BitVec.ofNat 32 4)
    (even_at P env.hP 0x1259C (by decide)) u3.self (cIn env.code env.sSC frSv) (cIn env.mset env.sSM frSv)
    ps3_at_20 ps3_at_24 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x20 + 8) (by decide))
    (by decide) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) (aligned_add hFa (by decide))
    (p3inF' (c := 4) (l := 4 * 12) (by decide) env.sSM)
    (by rw [g3]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [g3]; simp +decide only [upd_app, ↓reduceIte, aluEval])
    (by rw [g3]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  obtain ⟨Mz, hMz⟩ : ∃ Mz, fillWords Msv (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 4) 0 12 = Mz := ⟨_, rfl⟩
  rw [hMz] at u4
  have frZ : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Mz x = m.mem x := fun x hx => by
    rw [← hMz, fillWords_outside 12 (p3inF (c := 4) (l := 4 * 12) (by decide) hx), frSv x hx]
  have cZ := cIn env.code env.sSC frZ
  obtain ⟨m5, c5, u5⟩ := St.block psSubInit u4 cZ psSubInit_end (by simp [BlockOk, BInstr.ok, psSubInit])
  simp only [runBlock, BInstr.run, psSubInit] at u5
  have x9 : reg m5 9 = 0xC := by rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨m6, d6, u6⟩ := u5.self.notTaken cZ 0x2E ps3_at_2c (by decide) (by rw [x9, u5.self.zero]; decide)
  have k5 : ∀ q, q ≠ (9 : Fin 32) → q ≠ (19 : Fin 32) → reg m6 q = reg m4 q := fun q h1 h2 => by
    rw [u6.regs, u5.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, u4.zero]
    · simp [upd, h0, h1, h2]
  have k3 : ∀ q, q.val ≠ 0 → q ≠ (20 : Fin 32) → q ≠ (21 : Fin 32) → q ≠ (18 : Fin 32) → q ≠ a0 → q ≠ a2 →
      q ≠ a1 → q ≠ (8 : Fin 32) → reg m3 q = reg m2 q := fun q h0 h20 h21 h18 h10 h12 h11 h8 => by
    rw [g3]; simp only [upd_app, h0, h20, h21, h18, h10, h12, h11, h8, ite_false]
  refine ⟨m6, Mz, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.single d6))))), u6.self, frZ, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro r o h
    obtain ⟨_, ho1, ho2⟩ := p3Ps_range (r, o) h
    dsimp only at ho1 ho2
    have hs : Sep (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 4) (4 * 12) (sp0 + 0xFFFFFF50 + o) 4 := by
      have := sep_offsets (sp0 + 0xFFFFFF50) (c := 4) (n := 4 * 12) (d := o.toNat) (k := 4) (.inl (by omega))
        (by decide) (by omega)
      rwa [ofNat_toNat_self] at this
    rw [← hMz, fillWords_load_sep hs, ← hMsv]
    simp only [p3Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  · rw [k5 sp (by decide) (by decide), k4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp2]
  · rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [k2 a1 (by decide), ha1]; exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm
  · rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [k2 a2 (by decide), ha2]; exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm
  · rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [sp2]; exact (add_ofNat_zero _).symm
  · rw [u6.regs, x9]; rfl
  · rw [u6.regs, u5.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [u4.zero]; rfl
  · rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3]
    simp +decide only [upd_app, ↓reduceIte]
    rw [k2 a0 (by decide), ha0]; exact BitVec.zero_add _
  · intro q hq
    have k := fun r (hr : p3Keep r = false) => pkeep_ne hq hr
    rw [k5 q (k 9 rfl) (k 19 rfl), k4 q (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k ra rfl),
      k3 q (fun e => k 0 rfl (Fin.ext e)) (k 20 rfl) (k 21 rfl) (k 18 rfl) (k a0 rfl) (k a2 rfl) (k a1 rfl) (k 8 rfl),
      k2 q (k sp rfl)]

/-- The registers from the subtraction loop's exit to the mask loop leave alone. -/
def psMid1Keep (q : Fin 32) : Bool := q.val ∉ [0, 1, 8, 10, 11, 12, 13, 14, 15, 16]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From the subtraction loop's exit at 0x4E to the mask loop at 0x6C: zero
the buffer at `F + 0x64` and point at it and the modulus. -/
theorem ps_mid1 {M : Word → BitVec 8} {P F : Word} {n : Machine} (hP : P.toNat % 2 = 0)
    (s : St M P n 0x4E (reg n)) (hc : CodeIn M P p384SubCode) (hms : CodeIn M (P + 0x1259C) memsetCode)
    (hF : F.toNat % 4 = 0) (hFw : F.toNat + 0xB0 ≤ 2 ^ 32)
    (sM : Sep (F + BitVec.ofNat 32 0x64) (4 * 12) (P + 0x1259C) memsetCode.length)
    (sC : Sep (F + BitVec.ofNat 32 0x64) (4 * 12) P p384SubCode.length) (rsp : reg n sp = F) :
    ∃ n', Steps n n' ∧ St (fillWords M (F + BitVec.ofNat 32 0x64) 0 12) P n' 0x6C (reg n') ∧
      reg n' sp = F ∧ reg n' a0 = p3M + BitVec.ofNat 32 (4 * 0) ∧
      reg n' 8 = F + BitVec.ofNat 32 0x64 + BitVec.ofNat 32 (4 * 0) ∧ reg n' a1 = BitVec.ofNat 32 (12 - 0) ∧
      ∀ q, psMid1Keep q = true → reg n' q = reg n q := by
  obtain ⟨n1, c1, u1⟩ := St.block psMid1 s hc psMid1_end (by simp [BlockOk, BInstr.ok, psMid1])
  simp only [runBlock, BInstr.run, psMid1] at u1
  obtain ⟨n2, c2, u2, a02, k2⟩ := St.memsetW (B := P + 0x1259C) (w := 12) (dst := F + BitVec.ofNat 32 0x64)
    (even_at P hP 0x1259C (by decide)) u1.self hc hms ps3_at_58 ps3_at_5c
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x58 + 8) (by decide))
    (by decide) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) (aligned_add hF (by decide)) sM
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval])
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  have hc2 : CodeIn (fillWords M (F + BitVec.ofNat 32 0x64) 0 12) P p384SubCode := fun i hi => by
    rw [fillWords_outside 12 (sC.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  obtain ⟨n3, c3, u3⟩ := St.block psMaskInit u2 hc2 psMaskInit_end (by simp [BlockOk, BInstr.ok, psMaskInit])
  simp only [runBlock, BInstr.run, psMaskInit] at u3
  have x11 : reg n3 a1 = 0xC := by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hc2 0x6C ps3_at_6a (by decide) (by rw [x11, u3.self.zero]; decide)
  have k1 : ∀ q, psMid1Keep q = true → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl]
  have k3 : ∀ q, psMid1Keep q = true → reg n4 q = reg n2 q := fun q hq => by
    rw [u4.regs, u3.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl]
  have sp2 : reg n2 sp = F := by
    rw [k2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k1 sp rfl, rsp]
  refine ⟨n4, c1.trans (c2.trans (c3.trans (.single d4))), u4.self, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [k3 sp rfl, sp2]
  · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]
  · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u1.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; exact (add_ofNat_zero _).symm
  · rw [u4.regs, x11]; rfl
  · rw [k3 q hq, k2 q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)
      (pkeep_ne hq rfl), k1 q hq]

/-- The registers from the mask loop's exit to the sum loop leave alone. -/
def psMid2Keep (q : Fin 32) : Bool := q.val ∉ [0, 1, 8, 10, 11, 12, 13, 14, 15, 16]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From the mask loop's exit at 0x7C to the sum loop at 0x96: zero the sum
buffer at `F + 0x34` and point at the three buffers. -/
theorem ps_mid2 {M : Word → BitVec 8} {P F : Word} {n : Machine} (hP : P.toNat % 2 = 0)
    (s : St M P n 0x7C (reg n)) (hc : CodeIn M P p384SubCode) (hms : CodeIn M (P + 0x1259C) memsetCode)
    (hF : F.toNat % 4 = 0) (hFw : F.toNat + 0xB0 ≤ 2 ^ 32)
    (sM : Sep (F + BitVec.ofNat 32 0x34) (4 * 12) (P + 0x1259C) memsetCode.length)
    (sC : Sep (F + BitVec.ofNat 32 0x34) (4 * 12) P p384SubCode.length) (rsp : reg n sp = F) (ra1 : reg n a1 = 0) :
    ∃ n', Steps n n' ∧ St (fillWords M (F + BitVec.ofNat 32 0x34) 0 12) P n' 0x96 (reg n') ∧
      reg n' sp = F ∧ reg n' a0 = F + BitVec.ofNat 32 4 + BitVec.ofNat 32 (4 * 0) ∧
      reg n' a1 = F + BitVec.ofNat 32 0x64 + BitVec.ofNat 32 (4 * 0) ∧
      reg n' 8 = F + BitVec.ofNat 32 0x34 + BitVec.ofNat 32 (4 * 0) ∧ reg n' a2 = BitVec.ofNat 32 (12 - 0) ∧
      reg n' a3 = 0 ∧ ∀ q, psMid2Keep q = true → reg n' q = reg n q := by
  obtain ⟨n1, c1, u1⟩ := St.block psMid2 s hc psMid2_end (by simp [BlockOk, BInstr.ok, psMid2])
  simp only [runBlock, BInstr.run, psMid2] at u1
  obtain ⟨n2, c2, u2, a02, k2⟩ := St.memsetW (B := P + 0x1259C) (w := 12) (dst := F + BitVec.ofNat 32 0x34)
    (even_at P hP 0x1259C (by decide)) u1.self hc hms ps3_at_84 ps3_at_88
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x84 + 8) (by decide))
    (by decide) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) (aligned_add hF (by decide)) sM
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; exact ra1)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  have hc2 : CodeIn (fillWords M (F + BitVec.ofNat 32 0x34) 0 12) P p384SubCode := fun i hi => by
    rw [fillWords_outside 12 (sC.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  obtain ⟨n3, c3, u3⟩ := St.block psAddInit u2 hc2 psAddInit_end (by simp [BlockOk, BInstr.ok, psAddInit])
  simp only [runBlock, BInstr.run, psAddInit] at u3
  have x12 : reg n3 a2 = 0xC := by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hc2 0x96 ps3_at_94 (by decide) (by rw [x12, u3.self.zero]; decide)
  have k1 : ∀ q, psMid2Keep q = true → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl]
  have k3 : ∀ q, psMid2Keep q = true → reg n4 q = reg n2 q := fun q hq => by
    rw [u4.regs, u3.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl]
  have sp2 : reg n2 sp = F := by
    rw [k2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k1 sp rfl, rsp]
  refine ⟨n4, c1.trans (c2.trans (c3.trans (.single d4))), u4.self, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [k3 sp rfl, sp2]
  · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; exact (add_ofNat_zero _).symm
  · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; exact (add_ofNat_zero _).symm
  · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u1.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; exact (add_ofNat_zero _).symm
  · rw [u4.regs, x12]; rfl
  · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [u2.zero]; rfl
  · rw [k3 q hq, k2 q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)
      (pkeep_ne hq rfl), k1 q hq]

theorem psG_34 (sp0 : Word) : sp0 + 0xFFFFFF4C + BitVec.ofNat 32 0x38 = sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x34 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `sub`'s epilogue, from 0xB4: copy the result out, restore the saved
registers, and return. -/
theorem ps_epi {P sp0 out lp rp : Word} {M0 Mx : Word → BitVec 8} {n : Machine} {v : Fin 32 → Word}
    (env : PSEnv M0 P sp0 out lp rp) (s : St Mx P n 0xB4 (reg n))
    (hfr : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Mx x = M0 x)
    (hsl : ∀ r o, (r, o) ∈ p3Ps → memLoad32 Mx (sp0 + 0xFFFFFF50 + o) = v r)
    (rsp : reg n sp = sp0 + 0xFFFFFF50) (r18 : reg n 18 = out) :
    ∃ n', Steps n n' ∧ n'.pc = v ra &&& ~~~1 ∧
      n'.mem = copyWords Mx out (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x34) 12 ∧
      reg n' sp = sp0 ∧ (∀ r o, (r, o) ∈ p3Ps → reg n' r = v r) ∧
      ∀ q, p3Keep q = true → reg n' q = reg n q := by
  have hGw := p3G_w sp0 env.hS
  have hFa : (sp0 + 0xFFFFFF50).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF50) (by decide)
  have cX : ∀ {b : Word} {code : List Nat}, CodeIn M0 b code → Sep (sp0 + 0xFFFFFF4C) 0xB4 b code.length →
      CodeIn Mx b code := fun hc hs i hi => by
    rw [hfr _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hc := cX env.code env.sSC
  obtain ⟨n1, c1, u1⟩ := St.block psCpyArgs s hc psCpyArgs_end (by simp [BlockOk, BInstr.ok, psCpyArgs])
  simp only [runBlock, BInstr.run, psCpyArgs] at u1
  have e8 : P + 0x12604 + 8 = P + 0x1260C := by rw [BitVec.add_assoc]; rfl
  have sO60 : Sep out 48 (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x34) 48 := by
    have := env.sOS.subR (c := 0x38) (l := 48) (by decide); rwa [psG_34] at this
  obtain ⟨n2, c2, u2, a02, k2⟩ := St.memcpyW (B := P + 0x12604) (w := 12) (dst := out)
    (src := sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x34) (even_at P env.hP 0x12604 (by decide)) u1.self hc
    (cX env.stub env.sSU) (by rw [e8]; exact cX env.body env.sSY) ps3_at_bc ps3_at_c0
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0xBC + 8) (by decide))
    (by decide) env.hwo (by decide) env.hout (aligned_add hFa (by decide)) sO60 (by rw [e8]; exact env.sOY)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r18]; exact BitVec.zero_add _)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  obtain ⟨Mc, hMc⟩ : ∃ Mc, copyWords Mx out (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x34) 12 = Mc := ⟨_, rfl⟩
  rw [hMc] at u2
  have hc2 : CodeIn Mc P p384SubCode := fun i hi => by
    rw [← hMc, copyWords_outside 12 (env.sOC.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have k1 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n1 q = reg n q := fun q h0 h1 h2 => by
    rw [u1.regs]
    by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, s.zero]
    · simp [upd, hq, h0, h1, h2]
  have sp2 : reg n2 sp = sp0 + 0xFFFFFF50 := by
    rw [k2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k1 sp (by decide) (by decide) (by decide), rsp]
  obtain ⟨n3, c3, u3⟩ := St.block (restoreBlock p3Ps) u2 hc2 psRestore_end
    (restoreBlock_ok Mc _ p3Ps (reg n2) sp2 p3Ps_sp fun p hp => fr_al' hFa (p3Ps_range p hp).1)
  simp only [restoreBlock_run Mc _ p3Ps (reg n2) sp2 p3Ps_sp] at u3
  have slot : ∀ r o, (r, o) ∈ p3Ps → memLoad32 Mc (sp0 + 0xFFFFFF50 + o) = v r := fun r o h => by
    obtain ⟨_, ho1, ho2⟩ := p3Ps_range (r, o) h
    dsimp only at ho1 ho2
    have hs : Sep out 48 (sp0 + 0xFFFFFF50 + o) 4 := by
      have := env.sOS.subR (c := 4 + o.toNat) (l := 4) (by omega)
      rwa [← add_ofNat_assoc, p3G_F, ofNat_toNat_self] at this
    rw [← hMc, copyWords_load_sep (k := 12) hs, hsl r o h]
  have rsp3 : restoreRegs Mc (sp0 + 0xFFFFFF50) (reg n2) p3Ps sp = sp0 + 0xFFFFFF50 := by
    rw [restoreRegs_sp _ _ _ _ p3Ps_sp]; exact sp2
  obtain ⟨n4, d4, u4⟩ := u3.aluImm hc2 ps3_at_d2 (off' := 0xD4) (by decide)
  obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.jalr hc2 ps3_at_d4
  refine ⟨n5, c1.trans (c2.trans (c3.trans (.cons d4 (.single d5)))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc5]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [add_lit_zero, slot ra 0xAC (by decide)]
  · rw [mem5, ← hMc]
  · rw [regs5]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rsp3, BitVec.add_assoc]
    exact BitVec.add_zero _
  · intro r o h
    rw [regs5]
    simp only [p3Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slot _ _ (by decide)
  · intro q hq
    rw [regs5, upd_kp hq rfl rfl]
    simp only [restoreRegs]
    repeat rw [upd_kp hq rfl rfl]
    rw [k2 q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)
      (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl),
      k1 q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)]

theorem psKeep_sub : ∀ q, p3Keep q = true → psSubKeep q = true := by decide
theorem psKeep_mid1 : ∀ q, p3Keep q = true → psMid1Keep q = true := by decide
theorem psKeep_mask : ∀ q, p3Keep q = true → psMaskKeep q = true := by decide
theorem psKeep_mid2 : ∀ q, p3Keep q = true → psMid2Keep q = true := by decide
theorem psKeep_add : ∀ q, p3Keep q = true → psAddKeep q = true := by decide

theorem psG_D (sp0 : Word) : sp0 + 0xFFFFFF4C + BitVec.ofNat 32 8 = sp0 + 0xFFFFFF50 + BitVec.ofNat 32 4 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `ConstMontyForm<p384::FieldParams, 12>::sub`**, called with
the result at `out` and 12-limb operands `A` at `lp` and `B` at `rp`. It
stores `p3SubRes A B`, which is `(A - B) mod p` for operands below `p`
(`p3SubRes_mod`). It returns with `sp` and every register but `a0` through
`a7`, `t0`, and `t1` as they were, and changes no memory outside the 0xB4
bytes of stack below `sp` and the result. -/
theorem p384Sub_correct (m : Machine) {P sp0 out lp rp retAddr : Word}
    (env : PSEnv m.mem P sp0 out lp rp) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = lp)
    (ha2 : reg m a2 = rp) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        reg m' q = reg m q) ∧
      limbVal (wordsAt m'.mem out 12) = p3SubRes (limbVal (wordsAt m.mem lp 12)) (limbVal (wordsAt m.mem rp 12)) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x := by
  have hGw := p3G_w sp0 env.hS
  have hFa : (sp0 + 0xFFFFFF50).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF50) (by decide)
  have hFw : (sp0 + 0xFFFFFF50).toNat + 0xB0 ≤ 2 ^ 32 := by
    rw [← p3G_F, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have toF : ∀ {b : Word} {k : Nat} {c l : Nat}, c + l ≤ 0xB0 → Sep (sp0 + 0xFFFFFF4C) 0xB4 b k →
      Sep (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 c) l b k := fun h hs => p3inF' h hs
  have toG4 : ∀ {b : Word} {k : Nat}, Sep (sp0 + 0xFFFFFF4C) 0xB4 b k → Sep (sp0 + 0xFFFFFF50 + 0xFFFFFFFC) 4 b k :=
    fun h => by
      rw [p3F_G]; have := h.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have cOf : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFF4C) 0xB4 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have sFF : ∀ a n c k, a + n ≤ 0xB0 → c + k ≤ 0xB0 → (a + n ≤ c ∨ c + k ≤ a) →
      Sep (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 a) n (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 c) k :=
    fun a n c k h1 h2 h3 => sep_offsets _ h3 (by omega) (by omega)
  have sGF : ∀ c k, c + k ≤ 0xB0 →
      Sep (sp0 + 0xFFFFFF50 + 0xFFFFFFFC) 4 (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 c) k := fun c k h => by
    rw [p3F_G, ← p3G_F, add_ofNat_assoc]
    have := sep_offsets (sp0 + 0xFFFFFF4C) (c := 0) (n := 4) (d := 4 + c) (k := k) (.inl (by omega)) (by decide)
      (by omega)
    rwa [add_ofNat_zero] at this
  -- the prologue
  obtain ⟨n1, M1, c1, s1, fr1, hsl, sp1, r21, r20, r8, r9, r19, r18, k1⟩ := ps_pro m env hpc ha0 ha1 ha2 hsp
  -- the difference
  have hD : (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 4).toNat % 4 = 0 := aligned_add hFa (by decide)
  obtain ⟨n2, M2, c2, s2, cM2, fr2, hb2, hv2, sp2, k2⟩ := ps_sub_loop (M0 := M1) env.hP hFa env.hlp env.hrp hD
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (toG4 env.sLS.symm) (toG4 env.sRS.symm)
    (sGF 4 48 (by decide)) (toF (by decide) env.sLS.symm) (toF (by decide) env.sRS.symm) (toG4 env.sSB)
    (toG4 env.sSC) (toF (by decide) env.sSB) (toF (by decide) env.sSC)
    11 0 rfl s1 (cOf env.code env.sSC fr1) (cOf env.bsub env.sSB fr1) (fun _ _ _ => rfl) (.inl rfl)
    (by simp [accV, maskBit]) sp1 r21 r20 r8 r9 r19
  have inD : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Sep (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 4) 48 x 1 :=
    fun x hx => p3inF (by decide) hx
  have frM2 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M2 x = m.mem x := fun x hx => by
    rw [fr2 x (toG4 hx) (inD x hx), fr1 x hx]
  -- the masked modulus
  obtain ⟨n3, c3, s3, sp3, ra0_3, r8_3, ra1_3, k3⟩ := ps_mid1 env.hP s2 cM2 (cOf env.mset env.sSM frM2) hFa hFw
    (toF (by decide) env.sSM) (toF (by decide) env.sSC) sp2
  obtain ⟨M3, hM3⟩ : ∃ M3, fillWords M2 (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x64) 0 12 = M3 := ⟨_, rfl⟩
  rw [hM3] at s3
  have frM3 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3, fillWords_outside 12 (p3inF (by decide) hx), frM2 x hx]
  obtain ⟨n4, M4, c4, s4, cM4, fr4, hv4, ra1_4, k4⟩ := ps_mask_loop (M1 := M3)
    (E := sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x64) (b := reg n2 19) (aligned_add hFa (by decide))
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) hb2 (toF (by decide) env.sSP) (toF (by decide) env.sSC)
    11 0 rfl s3 (cOf env.code env.sSC frM3) (fun _ _ => rfl) (by simp [accV]) ra0_3 r8_3 ra1_3 (k3 19 rfl)
  have frM4 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M4 x = m.mem x := fun x hx => by
    rw [fr4 x (p3inF (by decide) hx), frM3 x hx]
  -- the sum
  obtain ⟨n5, c5, s5, sp5, ra0_5, ra1_5, r8_5, ra2_5, ra3_5, k5⟩ := ps_mid2 env.hP s4 cM4
    (cOf env.mset env.sSM frM4) hFa hFw (toF (by decide) env.sSM) (toF (by decide) env.sSC)
    (by rw [k4 sp rfl, sp3]) ra1_4
  obtain ⟨M5, hM5⟩ : ∃ M5, fillWords M4 (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x34) 0 12 = M5 := ⟨_, rfl⟩
  rw [hM5] at s5
  have frM5 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M5 x = m.mem x := fun x hx => by
    rw [← hM5, fillWords_outside 12 (p3inF (by decide) hx), frM4 x hx]
  obtain ⟨n6, M6, c6, s6, cM6, fr6, hc6, hv6, k6⟩ := ps_add_loop (M1 := M5)
    (F := sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x34) (lp := sp0 + 0xFFFFFF50 + BitVec.ofNat 32 4)
    (rp := sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x64) (aligned_add hFa (by decide))
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) hD (aligned_add hFa (by decide))
    (sFF 0x34 0x30 4 48 (by decide) (by decide) (.inr (by decide)))
    (sFF 0x34 0x30 0x64 48 (by decide) (by decide) (.inl (by decide))) (toF (by decide) env.sSC)
    11 0 rfl (M := M5) (n := n5) (c := 0) s5 (cOf env.code env.sSC frM5) (fun _ _ => rfl) (Nat.zero_le 1)
    (by simp [accV]) ra0_5 ra1_5 r8_5 ra2_5 ra3_5
  have frM6 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M6 x = m.mem x := fun x hx => by
    rw [fr6 x (p3inF (by decide) hx), frM5 x hx]
  -- the saved registers are where the prologue put them
  have hsl6 : ∀ r o, (r, o) ∈ p3Ps → memLoad32 M6 (sp0 + 0xFFFFFF50 + o) = reg m r := fun r o h => by
    obtain ⟨_, ho1, ho2⟩ := p3Ps_range (r, o) h
    dsimp only at ho1 ho2
    have e : sp0 + 0xFFFFFF50 + o = sp0 + 0xFFFFFF50 + BitVec.ofNat 32 o.toNat := by rw [ofNat_toNat_self]
    have sF : ∀ c l, c + l ≤ o.toNat → Sep (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 c) l (sp0 + 0xFFFFFF50 + o) 4 :=
      fun c l hcl => by rw [e]; exact sep_offsets _ (.inl hcl) (by omega) (by omega)
    have sG : Sep (sp0 + 0xFFFFFF50 + 0xFFFFFFFC) 4 (sp0 + 0xFFFFFF50 + o) 4 := by
      rw [e]; exact sGF _ 4 (by omega)
    rw [load_frame fr6 (sF 0x34 0x30 (by omega)), ← hM5, fillWords_load_sep (sF 0x34 (4 * 12) (by omega)),
      load_frame fr4 (sF 0x64 0x30 (by omega)), ← hM3, fillWords_load_sep (sF 0x64 (4 * 12) (by omega)),
      load_frame2 fr2 sG (sF 4 48 (by omega)), hsl r o h]
  have r18_6 : reg n6 18 = out := by
    rw [k6 18 rfl, k5 18 rfl, k4 18 rfl, k3 18 rfl, k2 18 rfl, r18]
  have sp6 : reg n6 sp = sp0 + 0xFFFFFF50 := by rw [k6 sp rfl, sp5]
  -- the epilogue
  obtain ⟨n7, c7, pc7, mem7, sp7, sv7, k7⟩ := ps_epi (v := reg m) env s6 frM6 hsl6 sp6 r18_6
  refine ⟨n7, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans c7))))), by rw [pc7, hra, hret], sp7, ?_,
    ?_, ?_⟩
  · intro q q10 q11 q12 q13 q14 q15 q16 q17 q5 q6
    have cat := (by decide : ∀ q : Fin 32, q = 0 ∨ q = sp ∨ q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨
      q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ p3Keep q = true ∨
      q = a0 ∨ q = a1 ∨ q = a2 ∨ q = a3 ∨ q = a4 ∨ q = a5 ∨ q = a6 ∨ q = a7 ∨ q = t0 ∨ q = t1) q
    rcases cat with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; rfl
    · subst h; rw [sp7, hsp]
    · subst h; exact sv7 _ 0xAC (by decide)
    · subst h; exact sv7 _ 0xA8 (by decide)
    · subst h; exact sv7 _ 0xA4 (by decide)
    · subst h; exact sv7 _ 0xA0 (by decide)
    · subst h; exact sv7 _ 0x9C (by decide)
    · subst h; exact sv7 _ 0x98 (by decide)
    · subst h; exact sv7 _ 0x94 (by decide)
    · rw [k7 q h, k6 q (psKeep_add q h), k5 q (psKeep_mid2 q h), k4 q (psKeep_mask q h), k3 q (psKeep_mid1 q h),
        k2 q (psKeep_sub q h), k1 q h]
    · exact absurd h q10
    · exact absurd h q11
    · exact absurd h q12
    · exact absurd h q13
    · exact absurd h q14
    · exact absurd h q15
    · exact absurd h q16
    · exact absurd h q17
    · exact absurd h q5
    · exact absurd h q6
  · have hwo := env.hwo
    have eOut : limbVal (wordsAt n7.mem out 12) = accV M6 (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x34) 12 := by
      rw [limbVal_wordsAt, mem7]
      exact accV_congr2 12 fun j hj => copyWords_load 12 j hj (by omega)
    have hDv : accV M5 (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 4) 12 = accV M2 (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 4) 12 :=
      accV_congr2 12 fun j hj => by
        rw [add_ofNat_assoc, ← hM5, fillWords_load_sep (sFF 0x34 (4 * 12) (4 + 4 * j) 4 (by decide) (by omega)
          (.inr (by omega))), load_frame fr4 (sFF 0x64 0x30 (4 + 4 * j) 4 (by decide) (by omega) (.inr (by omega))),
          ← hM3, fillWords_load_sep (sFF 0x64 (4 * 12) (4 + 4 * j) 4 (by decide) (by omega) (.inr (by omega)))]
    have hEv : accV M5 (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x64) 12 =
        accV M4 (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 0x64) 12 :=
      accV_congr2 12 fun j hj => by
        rw [add_ofNat_assoc, ← hM5, fillWords_load_sep (sFF 0x34 (4 * 12) (0x64 + 4 * j) 4 (by decide) (by omega)
          (.inl (by omega)))]
    have hP3 : accV M3 p3M 12 = p384 := p3M_val (cOf env.pmod env.sSP frM3)
    have hA : accV M1 lp 12 = accV m.mem lp 12 := accV_congr 12 fun j hj =>
      load_frame fr1 (env.sLS.symm.subR (c := 4 * j) (l := 4) (by omega))
    have hB : accV M1 rp 12 = accV m.mem rp 12 := accV_congr 12 fun j hj =>
      load_frame fr1 (env.sRS.symm.subR (c := 4 * j) (l := 4) (by omega))
    rw [eOut, limbVal_wordsAt, limbVal_wordsAt]
    have e384 : (2 : Nat) ^ (32 * 12) = 2 ^ 384 := rfl
    refine ps_final (D := accV M2 (sp0 + 0xFFFFFF50 + BitVec.ofNat 32 4) 12) (mb := maskBit (reg n2 19))
      (accV_lt _ _ 12) (accV_lt _ _ 12) hc6 (mb_le1 _) ?_ ?_
    · rw [← hA, ← hB, ← e384]; exact hv2
    · rw [← e384, hv6, hDv, hEv, hv4, hP3]
  · intro x hx ho
    rw [mem7, copyWords_outside 12 ho, frM6 x hx]

end C3.RV32
