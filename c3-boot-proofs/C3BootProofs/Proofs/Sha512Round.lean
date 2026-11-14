import C3BootProofs.Proofs.Sha512Decode
import C3BootProofs.Proofs.Sha512Spec

/-!
# `compress512`: one round

The round loop's body, from 0x238 to 0x374, on the halves of the working
variables. The body has 111 instructions, so the proof splits it into
segments: each segment lemma names every value the segment computes, and
`s5Round_run` chains them, reads each value's meaning from its operands',
and adds the 64-bit sums from their halves with `HoldsN`.
-/

namespace C3.RV32

open C3.Image

theorem lo64_not (x : Sha512.W64) : lo64 (~~~x) = lo64 x ^^^ 0xFFFFFFFF := by
  rw [Sha512.not_eq_xor, lo64_xor]; rfl

theorem hi64_not (x : Sha512.W64) : hi64 (~~~x) = hi64 x ^^^ 0xFFFFFFFF := by
  rw [Sha512.not_eq_xor, hi64_xor]; rfl

/-- `l` and the low 32 bits of `H` are the low and high words of `X`: the
high word is a sum the code has not yet reduced modulo `2 ^ 32`. -/
def HoldsN (l : Word) (H : Nat) (X : Sha512.W64) : Prop := l.toNat + 2 ^ 32 * (H % 2 ^ 32) = X.toNat

theorem holdsN_atom (X : Sha512.W64) : HoldsN (lo64 X) (hi64 X).toNat X := by
  unfold HoldsN; rw [Nat.mod_eq_of_lt (hi64 X).isLt, val64 X]

/-- A 64-bit addition from the two low words, the `sltu` carry, and the
high words still to be summed. -/
theorem holdsN_add {xl yl l c : Word} {Hx Hy : Nat} {X Y : Sha512.W64} (hx : HoldsN xl Hx X) (hy : HoldsN yl Hy Y)
    (hl : l.toNat = (xl.toNat + yl.toNat) % 2 ^ 32) (hc : c.toNat = (xl.toNat + yl.toNat) / 2 ^ 32) :
    HoldsN l (Hx + Hy + c.toNat) (X + Y) := by
  unfold HoldsN at *
  have := xl.isLt
  have := yl.isLt
  rw [BitVec.toNat_add, ← hx, ← hy, hl, hc]
  omega

theorem holdsN_add' {xl yl l c : Word} {Hx Hy : Nat} {X Y : Sha512.W64} (hx : HoldsN xl Hx X) (hy : HoldsN yl Hy Y)
    (hl : l.toNat = (yl.toNat + xl.toNat) % 2 ^ 32) (hc : c.toNat = (yl.toNat + xl.toNat) / 2 ^ 32) :
    HoldsN l (Hx + Hy + c.toNat) (X + Y) := by
  rw [Nat.add_comm] at hl hc; exact holdsN_add hx hy hl hc

theorem dm_leaf (y : Word) : y.toNat = y.toNat % 2 ^ 32 := (Nat.mod_eq_of_lt y.isLt).symm

/-- A 32-bit sum of two sums, as one sum modulo `2 ^ 32`. -/
theorem dm_add {x y z : Word} {S T : Nat} (hx : x.toNat = (y.toNat + z.toNat) % 2 ^ 32)
    (hy : y.toNat = S % 2 ^ 32) (hz : z.toNat = T % 2 ^ 32) : x.toNat = (S + T) % 2 ^ 32 := by
  rw [hx, hy, hz, ← Nat.add_mod]

/-- Replaces the unreduced high sum with the register that holds it. -/
theorem holdsN_close {l h : Word} {H H' : Nat} {X : Sha512.W64} (hp : HoldsN l H X) (hh : h.toNat = H' % 2 ^ 32)
    (e : H' = H) : HoldsN l h.toNat X := by
  unfold HoldsN at *; rw [Nat.mod_eq_of_lt h.isLt, hh, e]; exact hp

/-- The two registers are the halves of `X`. -/
theorem holdsN_halves {l h : Word} {H H' : Nat} {X : Sha512.W64} (hp : HoldsN l H X) (hh : h.toNat = H' % 2 ^ 32)
    (e : H' = H) : l = lo64 X ∧ h = hi64 X := by
  unfold HoldsN at hp
  have := l.isLt
  constructor
  · apply BitVec.eq_of_toNat_eq; rw [lo64_toNat, ← hp]; omega
  · apply BitVec.eq_of_toNat_eq; rw [hi64_toNat, ← hp, hh, e]; omega


def s5Round : List BInstr :=
  [.aluImm .sll a2 (27 : Fin 32) 0x12,
   .aluImm .srl a3 (22 : Fin 32) 0xE,
   .aluImm .srl (9 : Fin 32) (27 : Fin 32) 0xE,
   .alu .or a2 a2 a3,
   .aluImm .sll a3 (22 : Fin 32) 0x12,
   .alu .or a3 a3 (9 : Fin 32),
   .aluImm .sll (9 : Fin 32) (27 : Fin 32) 0xE,
   .aluImm .srl a1 (27 : Fin 32) 0x12,
   .aluImm .sll a0 (22 : Fin 32) 0xE,
   .aluImm .srl (8 : Fin 32) (22 : Fin 32) 0x12,
   .alu .or a0 a0 a1,
   .alu .or (8 : Fin 32) (8 : Fin 32) (9 : Fin 32),
   .alu .xor a0 a0 a3,
   .alu .xor a2 a2 (8 : Fin 32),
   .aluImm .sll a1 (27 : Fin 32) 0x17,
   .aluImm .srl a3 (27 : Fin 32) 0x9,
   .aluImm .sll (8 : Fin 32) (22 : Fin 32) 0x17,
   .aluImm .srl (9 : Fin 32) (22 : Fin 32) 0x9,
   .alu .or a3 a3 (8 : Fin 32),
   .alu .or a1 a1 (9 : Fin 32),
   .alu .xor a2 a2 a3,
   .alu .xor a0 a0 a1,
   .alu .and (23 : Fin 32) (6 : Fin 32) (27 : Fin 32),
   .alu .and a4 (5 : Fin 32) (22 : Fin 32),
   .aluImm .xor (8 : Fin 32) (22 : Fin 32) 0xFFFFFFFF,
   .aluImm .xor (9 : Fin 32) (27 : Fin 32) 0xFFFFFFFF,
   .alu .and (8 : Fin 32) (21 : Fin 32) (8 : Fin 32),
   .alu .and (9 : Fin 32) (17 : Fin 32) (9 : Fin 32),
   .alu .add a2 a2 a6,
   .alu .add a2 a2 (8 : Fin 32),
   .alu .add a3 x0 (25 : Fin 32),
   .lw (8 : Fin 32) a3 0x0,
   .lw a1 a3 0x4,
   .alu .add ra ra a0,
   .alu .sltu a0 ra a0,
   .alu .add (9 : Fin 32) (9 : Fin 32) ra,
   .alu .sltu a3 (9 : Fin 32) ra,
   .alu .add a0 a0 a2,
   .alu .add a0 a0 a3,
   .alu .add a5 x0 (30 : Fin 32),
   .lw a2 a5 0x0,
   .lw a3 a5 0x4,
   .alu .add (23 : Fin 32) (23 : Fin 32) (9 : Fin 32),
   .alu .add a0 a0 a4,
   .alu .sltu (9 : Fin 32) (23 : Fin 32) (9 : Fin 32),
   .alu .add a1 a1 (9 : Fin 32),
   .alu .add (8 : Fin 32) (8 : Fin 32) (23 : Fin 32),
   .alu .add a0 a0 a1,
   .alu .sltu a1 (8 : Fin 32) (23 : Fin 32),
   .alu .add a1 a1 a3,
   .alu .add (23 : Fin 32) (8 : Fin 32) a2,
   .alu .add a0 a0 a1,
   .alu .sltu a1 (23 : Fin 32) (8 : Fin 32),
   .aluImm .srl a2 (31 : Fin 32) 0x1C,
   .aluImm .sll a3 (24 : Fin 32) 0x4,
   .alu .add a0 a0 a1,
   .alu .or a2 a2 a3,
   .aluImm .sll a1 (31 : Fin 32) 0x4,
   .aluImm .srl a3 (24 : Fin 32) 0x1C,
   .alu .or a1 a1 a3,
   .aluImm .sll a3 (31 : Fin 32) 0x1E,
   .aluImm .srl a4 (31 : Fin 32) 0x2,
   .aluImm .sll a5 (24 : Fin 32) 0x1E,
   .alu .or a4 a4 a5,
   .aluImm .srl a5 (24 : Fin 32) 0x2,
   .alu .or a3 a3 a5,
   .alu .xor a1 a1 a4,
   .alu .xor a2 a2 a3,
   .aluImm .srl a3 (31 : Fin 32) 0x7,
   .aluImm .sll a4 (31 : Fin 32) 0x19,
   .aluImm .srl a5 (24 : Fin 32) 0x7,
   .alu .or a4 a4 a5,
   .aluImm .sll a5 (24 : Fin 32) 0x19,
   .alu .or a3 a3 a5,
   .alu .xor a2 a2 a4,
   .alu .xor a1 a1 a3,
   .alu .xor a3 (7 : Fin 32) (26 : Fin 32),
   .alu .xor a4 (28 : Fin 32) (18 : Fin 32),
   .alu .and a3 a3 (24 : Fin 32),
   .alu .and a4 a4 (31 : Fin 32),
   .alu .and a5 (28 : Fin 32) (18 : Fin 32),
   .alu .xor a4 a4 a5,
   .alu .and a5 (7 : Fin 32) (26 : Fin 32),
   .alu .xor a3 a3 a5,
   .alu .add a5 a4 a2,
   .alu .add a1 a1 a3,
   .alu .sltu a2 a5 a4,
   .alu .add a1 a1 a2,
   .alu .add a2 (23 : Fin 32) (19 : Fin 32),
   .alu .sltu a3 a2 (23 : Fin 32),
   .alu .add (23 : Fin 32) (23 : Fin 32) a5,
   .alu .add a3 a3 (20 : Fin 32),
   .alu .sltu a4 (23 : Fin 32) a5,
   .alu .add a1 a1 a4,
   .alu .add a3 a3 a0,
   .alu .add a0 a0 a1,
   .aluImm .add (25 : Fin 32) (25 : Fin 32) 0x8,
   .aluImm .add (30 : Fin 32) (30 : Fin 32) 0x8,
   .aluImm .add (29 : Fin 32) (29 : Fin 32) 0xFFFFFFFF,
   .alu .add ra x0 (17 : Fin 32),
   .alu .add a6 x0 (21 : Fin 32),
   .alu .add (17 : Fin 32) x0 (6 : Fin 32),
   .alu .add (21 : Fin 32) x0 (5 : Fin 32),
   .alu .add (6 : Fin 32) x0 (27 : Fin 32),
   .alu .add (5 : Fin 32) x0 (22 : Fin 32),
   .alu .add (19 : Fin 32) x0 (18 : Fin 32),
   .alu .add (20 : Fin 32) x0 (26 : Fin 32),
   .alu .add (18 : Fin 32) x0 (28 : Fin 32),
   .alu .add (26 : Fin 32) x0 (7 : Fin 32),
   .alu .add (28 : Fin 32) x0 (31 : Fin 32),
   .alu .add (7 : Fin 32) x0 (24 : Fin 32)]

def s5RoundS0 : List BInstr :=
  [.aluImm .sll a2 (27 : Fin 32) 0x12,
   .aluImm .srl a3 (22 : Fin 32) 0xE,
   .aluImm .srl (9 : Fin 32) (27 : Fin 32) 0xE,
   .alu .or a2 a2 a3,
   .aluImm .sll a3 (22 : Fin 32) 0x12,
   .alu .or a3 a3 (9 : Fin 32),
   .aluImm .sll (9 : Fin 32) (27 : Fin 32) 0xE,
   .aluImm .srl a1 (27 : Fin 32) 0x12,
   .aluImm .sll a0 (22 : Fin 32) 0xE,
   .aluImm .srl (8 : Fin 32) (22 : Fin 32) 0x12,
   .alu .or a0 a0 a1,
   .alu .or (8 : Fin 32) (8 : Fin 32) (9 : Fin 32)]

def s5RoundS1 : List BInstr :=
  [.alu .xor a0 a0 a3,
   .alu .xor a2 a2 (8 : Fin 32),
   .aluImm .sll a1 (27 : Fin 32) 0x17,
   .aluImm .srl a3 (27 : Fin 32) 0x9,
   .aluImm .sll (8 : Fin 32) (22 : Fin 32) 0x17,
   .aluImm .srl (9 : Fin 32) (22 : Fin 32) 0x9,
   .alu .or a3 a3 (8 : Fin 32),
   .alu .or a1 a1 (9 : Fin 32),
   .alu .xor a2 a2 a3,
   .alu .xor a0 a0 a1,
   .alu .and (23 : Fin 32) (6 : Fin 32) (27 : Fin 32),
   .alu .and a4 (5 : Fin 32) (22 : Fin 32)]

def s5RoundS2 : List BInstr :=
  [.aluImm .xor (8 : Fin 32) (22 : Fin 32) 0xFFFFFFFF,
   .aluImm .xor (9 : Fin 32) (27 : Fin 32) 0xFFFFFFFF,
   .alu .and (8 : Fin 32) (21 : Fin 32) (8 : Fin 32),
   .alu .and (9 : Fin 32) a7 (9 : Fin 32),
   .alu .add a2 a2 a6,
   .alu .add a2 a2 (8 : Fin 32),
   .alu .add a3 x0 (25 : Fin 32),
   .lw (8 : Fin 32) a3 0x0,
   .lw a1 a3 0x4,
   .alu .add ra ra a0,
   .alu .sltu a0 ra a0,
   .alu .add (9 : Fin 32) (9 : Fin 32) ra]

def s5RoundS3 : List BInstr :=
  [.alu .sltu a3 (9 : Fin 32) ra,
   .alu .add a0 a0 a2,
   .alu .add a0 a0 a3,
   .alu .add a5 x0 (30 : Fin 32),
   .lw a2 a5 0x0,
   .lw a3 a5 0x4,
   .alu .add (23 : Fin 32) (23 : Fin 32) (9 : Fin 32),
   .alu .add a0 a0 a4,
   .alu .sltu (9 : Fin 32) (23 : Fin 32) (9 : Fin 32),
   .alu .add a1 a1 (9 : Fin 32),
   .alu .add (8 : Fin 32) (8 : Fin 32) (23 : Fin 32),
   .alu .add a0 a0 a1]

def s5RoundS4 : List BInstr :=
  [.alu .sltu a1 (8 : Fin 32) (23 : Fin 32),
   .alu .add a1 a1 a3,
   .alu .add (23 : Fin 32) (8 : Fin 32) a2,
   .alu .add a0 a0 a1,
   .alu .sltu a1 (23 : Fin 32) (8 : Fin 32),
   .aluImm .srl a2 (31 : Fin 32) 0x1C,
   .aluImm .sll a3 (24 : Fin 32) 0x4,
   .alu .add a0 a0 a1,
   .alu .or a2 a2 a3,
   .aluImm .sll a1 (31 : Fin 32) 0x4,
   .aluImm .srl a3 (24 : Fin 32) 0x1C,
   .alu .or a1 a1 a3]

def s5RoundS5 : List BInstr :=
  [.aluImm .sll a3 (31 : Fin 32) 0x1E,
   .aluImm .srl a4 (31 : Fin 32) 0x2,
   .aluImm .sll a5 (24 : Fin 32) 0x1E,
   .alu .or a4 a4 a5,
   .aluImm .srl a5 (24 : Fin 32) 0x2,
   .alu .or a3 a3 a5,
   .alu .xor a1 a1 a4,
   .alu .xor a2 a2 a3,
   .aluImm .srl a3 (31 : Fin 32) 0x7,
   .aluImm .sll a4 (31 : Fin 32) 0x19,
   .aluImm .srl a5 (24 : Fin 32) 0x7,
   .alu .or a4 a4 a5]

def s5RoundS6 : List BInstr :=
  [.aluImm .sll a5 (24 : Fin 32) 0x19,
   .alu .or a3 a3 a5,
   .alu .xor a2 a2 a4,
   .alu .xor a1 a1 a3,
   .alu .xor a3 (7 : Fin 32) (26 : Fin 32),
   .alu .xor a4 (28 : Fin 32) (18 : Fin 32),
   .alu .and a3 a3 (24 : Fin 32),
   .alu .and a4 a4 (31 : Fin 32),
   .alu .and a5 (28 : Fin 32) (18 : Fin 32),
   .alu .xor a4 a4 a5,
   .alu .and a5 (7 : Fin 32) (26 : Fin 32),
   .alu .xor a3 a3 a5]

def s5RoundS7 : List BInstr :=
  [.alu .add a5 a4 a2,
   .alu .add a1 a1 a3,
   .alu .sltu a2 a5 a4,
   .alu .add a1 a1 a2,
   .alu .add a2 (23 : Fin 32) (19 : Fin 32),
   .alu .sltu a3 a2 (23 : Fin 32),
   .alu .add (23 : Fin 32) (23 : Fin 32) a5,
   .alu .add a3 a3 (20 : Fin 32),
   .alu .sltu a4 (23 : Fin 32) a5,
   .alu .add a1 a1 a4,
   .alu .add a3 a3 a0,
   .alu .add a0 a0 a1]

def s5RoundS8 : List BInstr :=
  [.aluImm .add (25 : Fin 32) (25 : Fin 32) 0x8,
   .aluImm .add (30 : Fin 32) (30 : Fin 32) 0x8,
   .aluImm .add (29 : Fin 32) (29 : Fin 32) 0xFFFFFFFF,
   .alu .add ra x0 a7,
   .alu .add a6 x0 (21 : Fin 32),
   .alu .add a7 x0 (6 : Fin 32),
   .alu .add (21 : Fin 32) x0 (5 : Fin 32),
   .alu .add (6 : Fin 32) x0 (27 : Fin 32),
   .alu .add (5 : Fin 32) x0 (22 : Fin 32),
   .alu .add (19 : Fin 32) x0 (18 : Fin 32),
   .alu .add (20 : Fin 32) x0 (26 : Fin 32),
   .alu .add (18 : Fin 32) x0 (28 : Fin 32),
   .alu .add (26 : Fin 32) x0 (7 : Fin 32),
   .alu .add (28 : Fin 32) x0 (31 : Fin 32),
   .alu .add (7 : Fin 32) x0 (24 : Fin 32)]

theorem s5Round_split : s5Round = s5RoundS0 ++ s5RoundS1 ++ s5RoundS2 ++ s5RoundS3 ++ s5RoundS4 ++ s5RoundS5 ++ s5RoundS6 ++ s5RoundS7 ++ s5RoundS8 := rfl

set_option maxRecDepth 100000 in
theorem s5RoundS0_dag (M : Word → BitVec 8) (f : Fin 32 → Word) :
    ∃ g : Fin 32 → Word, runBlock s5RoundS0 (M, f) = (M, g) ∧ ∃ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Word,
      aluEval .sll (f (27 : Fin 32)) 0x12 = v0 ∧
      aluEval .srl (f (22 : Fin 32)) 0xE = v1 ∧
      aluEval .srl (f (27 : Fin 32)) 0xE = v2 ∧
      aluEval .or v0 v1 = v3 ∧
      aluEval .sll (f (22 : Fin 32)) 0x12 = v4 ∧
      aluEval .or v4 v2 = v5 ∧
      aluEval .sll (f (27 : Fin 32)) 0xE = v6 ∧
      aluEval .srl (f (27 : Fin 32)) 0x12 = v7 ∧
      aluEval .sll (f (22 : Fin 32)) 0xE = v8 ∧
      aluEval .srl (f (22 : Fin 32)) 0x12 = v9 ∧
      aluEval .or v8 v7 = v10 ∧
      aluEval .or v9 v6 = v11 ∧
      g ra = f ra ∧
      g (5 : Fin 32) = f (5 : Fin 32) ∧
      g (6 : Fin 32) = f (6 : Fin 32) ∧
      g (7 : Fin 32) = f (7 : Fin 32) ∧
      g (8 : Fin 32) = v11 ∧
      g a0 = v10 ∧
      g a2 = v3 ∧
      g a3 = v5 ∧
      g a6 = f a6 ∧
      g a7 = f a7 ∧
      g (18 : Fin 32) = f (18 : Fin 32) ∧
      g (19 : Fin 32) = f (19 : Fin 32) ∧
      g (20 : Fin 32) = f (20 : Fin 32) ∧
      g (21 : Fin 32) = f (21 : Fin 32) ∧
      g (22 : Fin 32) = f (22 : Fin 32) ∧
      g (24 : Fin 32) = f (24 : Fin 32) ∧
      g (25 : Fin 32) = f (25 : Fin 32) ∧
      g (26 : Fin 32) = f (26 : Fin 32) ∧
      g (27 : Fin 32) = f (27 : Fin 32) ∧
      g (28 : Fin 32) = f (28 : Fin 32) ∧
      g (29 : Fin 32) = f (29 : Fin 32) ∧
      g (30 : Fin 32) = f (30 : Fin 32) ∧
      g (31 : Fin 32) = f (31 : Fin 32) :=
  ⟨_, rfl, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem s5RoundS1_dag (M : Word → BitVec 8) (f : Fin 32 → Word) :
    ∃ g : Fin 32 → Word, runBlock s5RoundS1 (M, f) = (M, g) ∧ ∃ v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : Word,
      aluEval .xor (f a0) (f a3) = v12 ∧
      aluEval .xor (f a2) (f (8 : Fin 32)) = v13 ∧
      aluEval .sll (f (27 : Fin 32)) 0x17 = v14 ∧
      aluEval .srl (f (27 : Fin 32)) 0x9 = v15 ∧
      aluEval .sll (f (22 : Fin 32)) 0x17 = v16 ∧
      aluEval .srl (f (22 : Fin 32)) 0x9 = v17 ∧
      aluEval .or v15 v16 = v18 ∧
      aluEval .or v14 v17 = v19 ∧
      aluEval .xor v13 v18 = v20 ∧
      aluEval .xor v12 v19 = v21 ∧
      aluEval .and (f (6 : Fin 32)) (f (27 : Fin 32)) = v22 ∧
      aluEval .and (f (5 : Fin 32)) (f (22 : Fin 32)) = v23 ∧
      g ra = f ra ∧
      g (5 : Fin 32) = f (5 : Fin 32) ∧
      g (6 : Fin 32) = f (6 : Fin 32) ∧
      g (7 : Fin 32) = f (7 : Fin 32) ∧
      g a0 = v21 ∧
      g a2 = v20 ∧
      g a4 = v23 ∧
      g a6 = f a6 ∧
      g a7 = f a7 ∧
      g (18 : Fin 32) = f (18 : Fin 32) ∧
      g (19 : Fin 32) = f (19 : Fin 32) ∧
      g (20 : Fin 32) = f (20 : Fin 32) ∧
      g (21 : Fin 32) = f (21 : Fin 32) ∧
      g (22 : Fin 32) = f (22 : Fin 32) ∧
      g (23 : Fin 32) = v22 ∧
      g (24 : Fin 32) = f (24 : Fin 32) ∧
      g (25 : Fin 32) = f (25 : Fin 32) ∧
      g (26 : Fin 32) = f (26 : Fin 32) ∧
      g (27 : Fin 32) = f (27 : Fin 32) ∧
      g (28 : Fin 32) = f (28 : Fin 32) ∧
      g (29 : Fin 32) = f (29 : Fin 32) ∧
      g (30 : Fin 32) = f (30 : Fin 32) ∧
      g (31 : Fin 32) = f (31 : Fin 32) :=
  ⟨_, rfl, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem s5RoundS2_dag (M : Word → BitVec 8) (f : Fin 32 → Word) :
    ∃ g : Fin 32 → Word, runBlock s5RoundS2 (M, f) = (M, g) ∧ ∃ v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 : Word,
      aluEval .xor (f (22 : Fin 32)) 0xFFFFFFFF = v24 ∧
      aluEval .xor (f (27 : Fin 32)) 0xFFFFFFFF = v25 ∧
      aluEval .and (f (21 : Fin 32)) v24 = v26 ∧
      aluEval .and (f a7) v25 = v27 ∧
      aluEval .add (f a2) (f a6) = v28 ∧
      aluEval .add v28 v26 = v29 ∧
      aluEval .add 0 (f (25 : Fin 32)) = v30 ∧
      memLoad32 M (v30 + 0x0) = v31 ∧
      memLoad32 M (v30 + 0x4) = v32 ∧
      aluEval .add (f ra) (f a0) = v33 ∧
      aluEval .sltu v33 (f a0) = v34 ∧
      aluEval .add v27 v33 = v35 ∧
      g ra = v33 ∧
      g (5 : Fin 32) = f (5 : Fin 32) ∧
      g (6 : Fin 32) = f (6 : Fin 32) ∧
      g (7 : Fin 32) = f (7 : Fin 32) ∧
      g (8 : Fin 32) = v31 ∧
      g (9 : Fin 32) = v35 ∧
      g a0 = v34 ∧
      g a1 = v32 ∧
      g a2 = v29 ∧
      g a4 = f a4 ∧
      g a7 = f a7 ∧
      g (18 : Fin 32) = f (18 : Fin 32) ∧
      g (19 : Fin 32) = f (19 : Fin 32) ∧
      g (20 : Fin 32) = f (20 : Fin 32) ∧
      g (21 : Fin 32) = f (21 : Fin 32) ∧
      g (22 : Fin 32) = f (22 : Fin 32) ∧
      g (23 : Fin 32) = f (23 : Fin 32) ∧
      g (24 : Fin 32) = f (24 : Fin 32) ∧
      g (25 : Fin 32) = f (25 : Fin 32) ∧
      g (26 : Fin 32) = f (26 : Fin 32) ∧
      g (27 : Fin 32) = f (27 : Fin 32) ∧
      g (28 : Fin 32) = f (28 : Fin 32) ∧
      g (29 : Fin 32) = f (29 : Fin 32) ∧
      g (30 : Fin 32) = f (30 : Fin 32) ∧
      g (31 : Fin 32) = f (31 : Fin 32) :=
  ⟨_, rfl, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem s5RoundS3_dag (M : Word → BitVec 8) (f : Fin 32 → Word) :
    ∃ g : Fin 32 → Word, runBlock s5RoundS3 (M, f) = (M, g) ∧ ∃ v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 : Word,
      aluEval .sltu (f (9 : Fin 32)) (f ra) = v36 ∧
      aluEval .add (f a0) (f a2) = v37 ∧
      aluEval .add v37 v36 = v38 ∧
      aluEval .add 0 (f (30 : Fin 32)) = v39 ∧
      memLoad32 M (v39 + 0x0) = v40 ∧
      memLoad32 M (v39 + 0x4) = v41 ∧
      aluEval .add (f (23 : Fin 32)) (f (9 : Fin 32)) = v42 ∧
      aluEval .add v38 (f a4) = v43 ∧
      aluEval .sltu v42 (f (9 : Fin 32)) = v44 ∧
      aluEval .add (f a1) v44 = v45 ∧
      aluEval .add (f (8 : Fin 32)) v42 = v46 ∧
      aluEval .add v43 v45 = v47 ∧
      g (5 : Fin 32) = f (5 : Fin 32) ∧
      g (6 : Fin 32) = f (6 : Fin 32) ∧
      g (7 : Fin 32) = f (7 : Fin 32) ∧
      g (8 : Fin 32) = v46 ∧
      g a0 = v47 ∧
      g a2 = v40 ∧
      g a3 = v41 ∧
      g a7 = f a7 ∧
      g (18 : Fin 32) = f (18 : Fin 32) ∧
      g (19 : Fin 32) = f (19 : Fin 32) ∧
      g (20 : Fin 32) = f (20 : Fin 32) ∧
      g (21 : Fin 32) = f (21 : Fin 32) ∧
      g (22 : Fin 32) = f (22 : Fin 32) ∧
      g (23 : Fin 32) = v42 ∧
      g (24 : Fin 32) = f (24 : Fin 32) ∧
      g (25 : Fin 32) = f (25 : Fin 32) ∧
      g (26 : Fin 32) = f (26 : Fin 32) ∧
      g (27 : Fin 32) = f (27 : Fin 32) ∧
      g (28 : Fin 32) = f (28 : Fin 32) ∧
      g (29 : Fin 32) = f (29 : Fin 32) ∧
      g (30 : Fin 32) = f (30 : Fin 32) ∧
      g (31 : Fin 32) = f (31 : Fin 32) :=
  ⟨_, rfl, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem s5RoundS4_dag (M : Word → BitVec 8) (f : Fin 32 → Word) :
    ∃ g : Fin 32 → Word, runBlock s5RoundS4 (M, f) = (M, g) ∧ ∃ v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 : Word,
      aluEval .sltu (f (8 : Fin 32)) (f (23 : Fin 32)) = v48 ∧
      aluEval .add v48 (f a3) = v49 ∧
      aluEval .add (f (8 : Fin 32)) (f a2) = v50 ∧
      aluEval .add (f a0) v49 = v51 ∧
      aluEval .sltu v50 (f (8 : Fin 32)) = v52 ∧
      aluEval .srl (f (31 : Fin 32)) 0x1C = v53 ∧
      aluEval .sll (f (24 : Fin 32)) 0x4 = v54 ∧
      aluEval .add v51 v52 = v55 ∧
      aluEval .or v53 v54 = v56 ∧
      aluEval .sll (f (31 : Fin 32)) 0x4 = v57 ∧
      aluEval .srl (f (24 : Fin 32)) 0x1C = v58 ∧
      aluEval .or v57 v58 = v59 ∧
      g (5 : Fin 32) = f (5 : Fin 32) ∧
      g (6 : Fin 32) = f (6 : Fin 32) ∧
      g (7 : Fin 32) = f (7 : Fin 32) ∧
      g a0 = v55 ∧
      g a1 = v59 ∧
      g a2 = v56 ∧
      g a7 = f a7 ∧
      g (18 : Fin 32) = f (18 : Fin 32) ∧
      g (19 : Fin 32) = f (19 : Fin 32) ∧
      g (20 : Fin 32) = f (20 : Fin 32) ∧
      g (21 : Fin 32) = f (21 : Fin 32) ∧
      g (22 : Fin 32) = f (22 : Fin 32) ∧
      g (23 : Fin 32) = v50 ∧
      g (24 : Fin 32) = f (24 : Fin 32) ∧
      g (25 : Fin 32) = f (25 : Fin 32) ∧
      g (26 : Fin 32) = f (26 : Fin 32) ∧
      g (27 : Fin 32) = f (27 : Fin 32) ∧
      g (28 : Fin 32) = f (28 : Fin 32) ∧
      g (29 : Fin 32) = f (29 : Fin 32) ∧
      g (30 : Fin 32) = f (30 : Fin 32) ∧
      g (31 : Fin 32) = f (31 : Fin 32) :=
  ⟨_, rfl, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem s5RoundS5_dag (M : Word → BitVec 8) (f : Fin 32 → Word) :
    ∃ g : Fin 32 → Word, runBlock s5RoundS5 (M, f) = (M, g) ∧ ∃ v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 : Word,
      aluEval .sll (f (31 : Fin 32)) 0x1E = v60 ∧
      aluEval .srl (f (31 : Fin 32)) 0x2 = v61 ∧
      aluEval .sll (f (24 : Fin 32)) 0x1E = v62 ∧
      aluEval .or v61 v62 = v63 ∧
      aluEval .srl (f (24 : Fin 32)) 0x2 = v64 ∧
      aluEval .or v60 v64 = v65 ∧
      aluEval .xor (f a1) v63 = v66 ∧
      aluEval .xor (f a2) v65 = v67 ∧
      aluEval .srl (f (31 : Fin 32)) 0x7 = v68 ∧
      aluEval .sll (f (31 : Fin 32)) 0x19 = v69 ∧
      aluEval .srl (f (24 : Fin 32)) 0x7 = v70 ∧
      aluEval .or v69 v70 = v71 ∧
      g (5 : Fin 32) = f (5 : Fin 32) ∧
      g (6 : Fin 32) = f (6 : Fin 32) ∧
      g (7 : Fin 32) = f (7 : Fin 32) ∧
      g a0 = f a0 ∧
      g a1 = v66 ∧
      g a2 = v67 ∧
      g a3 = v68 ∧
      g a4 = v71 ∧
      g a7 = f a7 ∧
      g (18 : Fin 32) = f (18 : Fin 32) ∧
      g (19 : Fin 32) = f (19 : Fin 32) ∧
      g (20 : Fin 32) = f (20 : Fin 32) ∧
      g (21 : Fin 32) = f (21 : Fin 32) ∧
      g (22 : Fin 32) = f (22 : Fin 32) ∧
      g (23 : Fin 32) = f (23 : Fin 32) ∧
      g (24 : Fin 32) = f (24 : Fin 32) ∧
      g (25 : Fin 32) = f (25 : Fin 32) ∧
      g (26 : Fin 32) = f (26 : Fin 32) ∧
      g (27 : Fin 32) = f (27 : Fin 32) ∧
      g (28 : Fin 32) = f (28 : Fin 32) ∧
      g (29 : Fin 32) = f (29 : Fin 32) ∧
      g (30 : Fin 32) = f (30 : Fin 32) ∧
      g (31 : Fin 32) = f (31 : Fin 32) :=
  ⟨_, rfl, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem s5RoundS6_dag (M : Word → BitVec 8) (f : Fin 32 → Word) :
    ∃ g : Fin 32 → Word, runBlock s5RoundS6 (M, f) = (M, g) ∧ ∃ v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 : Word,
      aluEval .sll (f (24 : Fin 32)) 0x19 = v72 ∧
      aluEval .or (f a3) v72 = v73 ∧
      aluEval .xor (f a2) (f a4) = v74 ∧
      aluEval .xor (f a1) v73 = v75 ∧
      aluEval .xor (f (7 : Fin 32)) (f (26 : Fin 32)) = v76 ∧
      aluEval .xor (f (28 : Fin 32)) (f (18 : Fin 32)) = v77 ∧
      aluEval .and v76 (f (24 : Fin 32)) = v78 ∧
      aluEval .and v77 (f (31 : Fin 32)) = v79 ∧
      aluEval .and (f (28 : Fin 32)) (f (18 : Fin 32)) = v80 ∧
      aluEval .xor v79 v80 = v81 ∧
      aluEval .and (f (7 : Fin 32)) (f (26 : Fin 32)) = v82 ∧
      aluEval .xor v78 v82 = v83 ∧
      g (5 : Fin 32) = f (5 : Fin 32) ∧
      g (6 : Fin 32) = f (6 : Fin 32) ∧
      g (7 : Fin 32) = f (7 : Fin 32) ∧
      g a0 = f a0 ∧
      g a1 = v75 ∧
      g a2 = v74 ∧
      g a3 = v83 ∧
      g a4 = v81 ∧
      g a7 = f a7 ∧
      g (18 : Fin 32) = f (18 : Fin 32) ∧
      g (19 : Fin 32) = f (19 : Fin 32) ∧
      g (20 : Fin 32) = f (20 : Fin 32) ∧
      g (21 : Fin 32) = f (21 : Fin 32) ∧
      g (22 : Fin 32) = f (22 : Fin 32) ∧
      g (23 : Fin 32) = f (23 : Fin 32) ∧
      g (24 : Fin 32) = f (24 : Fin 32) ∧
      g (25 : Fin 32) = f (25 : Fin 32) ∧
      g (26 : Fin 32) = f (26 : Fin 32) ∧
      g (27 : Fin 32) = f (27 : Fin 32) ∧
      g (28 : Fin 32) = f (28 : Fin 32) ∧
      g (29 : Fin 32) = f (29 : Fin 32) ∧
      g (30 : Fin 32) = f (30 : Fin 32) ∧
      g (31 : Fin 32) = f (31 : Fin 32) :=
  ⟨_, rfl, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem s5RoundS7_dag (M : Word → BitVec 8) (f : Fin 32 → Word) :
    ∃ g : Fin 32 → Word, runBlock s5RoundS7 (M, f) = (M, g) ∧ ∃ v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 : Word,
      aluEval .add (f a4) (f a2) = v84 ∧
      aluEval .add (f a1) (f a3) = v85 ∧
      aluEval .sltu v84 (f a4) = v86 ∧
      aluEval .add v85 v86 = v87 ∧
      aluEval .add (f (23 : Fin 32)) (f (19 : Fin 32)) = v88 ∧
      aluEval .sltu v88 (f (23 : Fin 32)) = v89 ∧
      aluEval .add (f (23 : Fin 32)) v84 = v90 ∧
      aluEval .add v89 (f (20 : Fin 32)) = v91 ∧
      aluEval .sltu v90 v84 = v92 ∧
      aluEval .add v87 v92 = v93 ∧
      aluEval .add v91 (f a0) = v94 ∧
      aluEval .add (f a0) v93 = v95 ∧
      g (5 : Fin 32) = f (5 : Fin 32) ∧
      g (6 : Fin 32) = f (6 : Fin 32) ∧
      g (7 : Fin 32) = f (7 : Fin 32) ∧
      g a0 = v95 ∧
      g a2 = v88 ∧
      g a3 = v94 ∧
      g a7 = f a7 ∧
      g (18 : Fin 32) = f (18 : Fin 32) ∧
      g (21 : Fin 32) = f (21 : Fin 32) ∧
      g (22 : Fin 32) = f (22 : Fin 32) ∧
      g (23 : Fin 32) = v90 ∧
      g (24 : Fin 32) = f (24 : Fin 32) ∧
      g (25 : Fin 32) = f (25 : Fin 32) ∧
      g (26 : Fin 32) = f (26 : Fin 32) ∧
      g (27 : Fin 32) = f (27 : Fin 32) ∧
      g (28 : Fin 32) = f (28 : Fin 32) ∧
      g (29 : Fin 32) = f (29 : Fin 32) ∧
      g (30 : Fin 32) = f (30 : Fin 32) ∧
      g (31 : Fin 32) = f (31 : Fin 32) :=
  ⟨_, rfl, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem s5RoundS8_dag (M : Word → BitVec 8) (f : Fin 32 → Word) :
    ∃ g : Fin 32 → Word, runBlock s5RoundS8 (M, f) = (M, g) ∧ ∃ v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 : Word,
      aluEval .add (f (25 : Fin 32)) 0x8 = v96 ∧
      aluEval .add (f (30 : Fin 32)) 0x8 = v97 ∧
      aluEval .add (f (29 : Fin 32)) 0xFFFFFFFF = v98 ∧
      aluEval .add 0 (f a7) = v99 ∧
      aluEval .add 0 (f (21 : Fin 32)) = v100 ∧
      aluEval .add 0 (f (6 : Fin 32)) = v101 ∧
      aluEval .add 0 (f (5 : Fin 32)) = v102 ∧
      aluEval .add 0 (f (27 : Fin 32)) = v103 ∧
      aluEval .add 0 (f (22 : Fin 32)) = v104 ∧
      aluEval .add 0 (f (18 : Fin 32)) = v105 ∧
      aluEval .add 0 (f (26 : Fin 32)) = v106 ∧
      aluEval .add 0 (f (28 : Fin 32)) = v107 ∧
      aluEval .add 0 (f (7 : Fin 32)) = v108 ∧
      aluEval .add 0 (f (31 : Fin 32)) = v109 ∧
      aluEval .add 0 (f (24 : Fin 32)) = v110 ∧
      g ra = v99 ∧
      g (5 : Fin 32) = v104 ∧
      g (6 : Fin 32) = v103 ∧
      g (7 : Fin 32) = v110 ∧
      g a0 = f a0 ∧
      g a2 = f a2 ∧
      g a3 = f a3 ∧
      g a6 = v100 ∧
      g a7 = v101 ∧
      g (18 : Fin 32) = v107 ∧
      g (19 : Fin 32) = v105 ∧
      g (20 : Fin 32) = v106 ∧
      g (21 : Fin 32) = v102 ∧
      g (23 : Fin 32) = f (23 : Fin 32) ∧
      g (25 : Fin 32) = v96 ∧
      g (26 : Fin 32) = v108 ∧
      g (28 : Fin 32) = v109 ∧
      g (29 : Fin 32) = v98 ∧
      g (30 : Fin 32) = v97 :=
  ⟨_, rfl, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
/-- One round, from 0x238 to 0x374, on the halves of the working
variables: the new `a` in `s7` and `a0`, the new `e` in `a2` and `a3`, and
the rest shifted down. -/
theorem s5Round_run {M : Word → BitVec 8} {f : Fin 32 → Word} {v : Sha512.V8} {w : Nat → Sha512.W64}
    {t : Nat} {kp wp : Word}
    (hi_al : f (31 : Fin 32) = lo64 v.a) (hi_ah : f (24 : Fin 32) = hi64 v.a)
    (hi_bl : f (28 : Fin 32) = lo64 v.b) (hi_bh : f (7 : Fin 32) = hi64 v.b)
    (hi_cl : f (18 : Fin 32) = lo64 v.c) (hi_ch : f (26 : Fin 32) = hi64 v.c)
    (hi_dl : f (19 : Fin 32) = lo64 v.d) (hi_dh : f (20 : Fin 32) = hi64 v.d)
    (hi_el : f (27 : Fin 32) = lo64 v.e) (hi_eh : f (22 : Fin 32) = hi64 v.e)
    (hi_fl : f (6 : Fin 32) = lo64 v.f) (hi_fh : f (5 : Fin 32) = hi64 v.f)
    (hi_gl : f a7 = lo64 v.g) (hi_gh : f (21 : Fin 32) = hi64 v.g)
    (hi_hl : f ra = lo64 v.h) (hi_hh : f a6 = hi64 v.h)
    (hkp : f (25 : Fin 32) = kp) (hwp : f (30 : Fin 32) = wp)
    (hk0 : memLoad32 M (kp + 0x0) = lo64 Sha512.k[t]!) (hk1 : memLoad32 M (kp + 0x4) = hi64 Sha512.k[t]!)
    (hw0 : memLoad32 M (wp + 0x0) = lo64 (w t)) (hw1 : memLoad32 M (wp + 0x4) = hi64 (w t)) :
    (runBlock s5Round (M, f)).2 (23 : Fin 32) = lo64 ((v.h + Sha512.bigSigma1 v.e + Sha512.ch v.e v.f v.g + Sha512.k[t]! + w t) + (Sha512.bigSigma0 v.a + Sha512.maj v.a v.b v.c)) ∧
    (runBlock s5Round (M, f)).2 a0 = hi64 ((v.h + Sha512.bigSigma1 v.e + Sha512.ch v.e v.f v.g + Sha512.k[t]! + w t) + (Sha512.bigSigma0 v.a + Sha512.maj v.a v.b v.c)) ∧
    (runBlock s5Round (M, f)).2 a2 = lo64 (v.d + (v.h + Sha512.bigSigma1 v.e + Sha512.ch v.e v.f v.g + Sha512.k[t]! + w t)) ∧
    (runBlock s5Round (M, f)).2 a3 = hi64 (v.d + (v.h + Sha512.bigSigma1 v.e + Sha512.ch v.e v.f v.g + Sha512.k[t]! + w t)) ∧
    (runBlock s5Round (M, f)).2 ra = lo64 v.g ∧
    (runBlock s5Round (M, f)).2 a6 = hi64 v.g ∧
    (runBlock s5Round (M, f)).2 a7 = lo64 v.f ∧
    (runBlock s5Round (M, f)).2 (21 : Fin 32) = hi64 v.f ∧
    (runBlock s5Round (M, f)).2 (6 : Fin 32) = lo64 v.e ∧
    (runBlock s5Round (M, f)).2 (5 : Fin 32) = hi64 v.e ∧
    (runBlock s5Round (M, f)).2 (19 : Fin 32) = lo64 v.c ∧
    (runBlock s5Round (M, f)).2 (20 : Fin 32) = hi64 v.c ∧
    (runBlock s5Round (M, f)).2 (18 : Fin 32) = lo64 v.b ∧
    (runBlock s5Round (M, f)).2 (26 : Fin 32) = hi64 v.b ∧
    (runBlock s5Round (M, f)).2 (28 : Fin 32) = lo64 v.a ∧
    (runBlock s5Round (M, f)).2 (7 : Fin 32) = hi64 v.a ∧
    (runBlock s5Round (M, f)).2 (25 : Fin 32) = kp + 0x8 ∧
    (runBlock s5Round (M, f)).2 (30 : Fin 32) = wp + 0x8 ∧
    (runBlock s5Round (M, f)).2 (29 : Fin 32) = f (29 : Fin 32) + 0xFFFFFFFF := by
  have E : runBlock s5Round (M, f) = runBlock s5RoundS8 (runBlock s5RoundS7 (runBlock s5RoundS6 (runBlock s5RoundS5 (runBlock s5RoundS4 (runBlock s5RoundS3 (runBlock s5RoundS2 (runBlock s5RoundS1 (runBlock s5RoundS0 (M, f))))))))) := by
    rw [s5Round_split]; simp only [runBlock_append]
  obtain ⟨f1, e1, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, F1_1, F1_5, F1_6, F1_7, F1_8, F1_10, F1_12, F1_13, F1_16, F1_17, F1_18, F1_19, F1_20, F1_21, F1_22, F1_24, F1_25, F1_26, F1_27, F1_28, F1_29, F1_30, F1_31⟩ := s5RoundS0_dag M f
  rw [e1] at E
  rw [hi_el] at h0
  rw [hi_eh] at h1
  rw [hi_el] at h2
  rw [hi_eh] at h4
  rw [hi_el] at h6
  rw [hi_el] at h7
  rw [hi_eh] at h8
  rw [hi_eh] at h9
  rw [hi_hl] at F1_1
  rw [hi_fh] at F1_5
  rw [hi_fl] at F1_6
  rw [hi_bh] at F1_7
  rw [hi_hh] at F1_16
  rw [hi_gl] at F1_17
  rw [hi_cl] at F1_18
  rw [hi_dl] at F1_19
  rw [hi_dh] at F1_20
  rw [hi_gh] at F1_21
  rw [hi_eh] at F1_22
  rw [hi_ah] at F1_24
  rw [hkp] at F1_25
  rw [hi_ch] at F1_26
  rw [hi_el] at F1_27
  rw [hi_bl] at F1_28
  rw [hwp] at F1_30
  rw [hi_al] at F1_31
  obtain ⟨f2, e2, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, F2_1, F2_5, F2_6, F2_7, F2_10, F2_12, F2_14, F2_16, F2_17, F2_18, F2_19, F2_20, F2_21, F2_22, F2_23, F2_24, F2_25, F2_26, F2_27, F2_28, F2_29, F2_30, F2_31⟩ := s5RoundS1_dag M f1
  rw [e2] at E
  rw [F1_10, F1_13] at h12
  rw [F1_12, F1_8] at h13
  rw [F1_27] at h14
  rw [F1_27] at h15
  rw [F1_22] at h16
  rw [F1_22] at h17
  rw [F1_6, F1_27] at h22
  rw [F1_5, F1_22] at h23
  rw [F1_1] at F2_1
  rw [F1_5] at F2_5
  rw [F1_6] at F2_6
  rw [F1_7] at F2_7
  rw [F1_16] at F2_16
  rw [F1_17] at F2_17
  rw [F1_18] at F2_18
  rw [F1_19] at F2_19
  rw [F1_20] at F2_20
  rw [F1_21] at F2_21
  rw [F1_22] at F2_22
  rw [F1_24] at F2_24
  rw [F1_25] at F2_25
  rw [F1_26] at F2_26
  rw [F1_27] at F2_27
  rw [F1_28] at F2_28
  rw [F1_29] at F2_29
  rw [F1_30] at F2_30
  rw [F1_31] at F2_31
  obtain ⟨f3, e3, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, F3_1, F3_5, F3_6, F3_7, F3_8, F3_9, F3_10, F3_11, F3_12, F3_14, F3_17, F3_18, F3_19, F3_20, F3_21, F3_22, F3_23, F3_24, F3_25, F3_26, F3_27, F3_28, F3_29, F3_30, F3_31⟩ := s5RoundS2_dag M f2
  rw [e3] at E
  rw [F2_22] at h24
  rw [F2_27] at h25
  rw [F2_21] at h26
  rw [F2_17] at h27
  rw [F2_12, F2_16] at h28
  rw [F2_25] at h30
  rw [F2_1, F2_10] at h33
  rw [F2_10] at h34
  rw [F2_5] at F3_5
  rw [F2_6] at F3_6
  rw [F2_7] at F3_7
  rw [F2_14] at F3_14
  rw [F2_17] at F3_17
  rw [F2_18] at F3_18
  rw [F2_19] at F3_19
  rw [F2_20] at F3_20
  rw [F2_21] at F3_21
  rw [F2_22] at F3_22
  rw [F2_23] at F3_23
  rw [F2_24] at F3_24
  rw [F2_25] at F3_25
  rw [F2_26] at F3_26
  rw [F2_27] at F3_27
  rw [F2_28] at F3_28
  rw [F2_29] at F3_29
  rw [F2_30] at F3_30
  rw [F2_31] at F3_31
  obtain ⟨f4, e4, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, F4_5, F4_6, F4_7, F4_8, F4_10, F4_12, F4_13, F4_17, F4_18, F4_19, F4_20, F4_21, F4_22, F4_23, F4_24, F4_25, F4_26, F4_27, F4_28, F4_29, F4_30, F4_31⟩ := s5RoundS3_dag M f3
  rw [e4] at E
  rw [F3_9, F3_1] at h36
  rw [F3_10, F3_12] at h37
  rw [F3_30] at h39
  rw [F3_23, F3_9] at h42
  rw [F3_14] at h43
  rw [F3_9] at h44
  rw [F3_11] at h45
  rw [F3_8] at h46
  rw [F3_5] at F4_5
  rw [F3_6] at F4_6
  rw [F3_7] at F4_7
  rw [F3_17] at F4_17
  rw [F3_18] at F4_18
  rw [F3_19] at F4_19
  rw [F3_20] at F4_20
  rw [F3_21] at F4_21
  rw [F3_22] at F4_22
  rw [F3_24] at F4_24
  rw [F3_25] at F4_25
  rw [F3_26] at F4_26
  rw [F3_27] at F4_27
  rw [F3_28] at F4_28
  rw [F3_29] at F4_29
  rw [F3_30] at F4_30
  rw [F3_31] at F4_31
  obtain ⟨f5, e5, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, F5_5, F5_6, F5_7, F5_10, F5_11, F5_12, F5_17, F5_18, F5_19, F5_20, F5_21, F5_22, F5_23, F5_24, F5_25, F5_26, F5_27, F5_28, F5_29, F5_30, F5_31⟩ := s5RoundS4_dag M f4
  rw [e5] at E
  rw [F4_8, F4_23] at h48
  rw [F4_13] at h49
  rw [F4_8, F4_12] at h50
  rw [F4_10] at h51
  rw [F4_8] at h52
  rw [F4_31] at h53
  rw [F4_24] at h54
  rw [F4_31] at h57
  rw [F4_24] at h58
  rw [F4_5] at F5_5
  rw [F4_6] at F5_6
  rw [F4_7] at F5_7
  rw [F4_17] at F5_17
  rw [F4_18] at F5_18
  rw [F4_19] at F5_19
  rw [F4_20] at F5_20
  rw [F4_21] at F5_21
  rw [F4_22] at F5_22
  rw [F4_24] at F5_24
  rw [F4_25] at F5_25
  rw [F4_26] at F5_26
  rw [F4_27] at F5_27
  rw [F4_28] at F5_28
  rw [F4_29] at F5_29
  rw [F4_30] at F5_30
  rw [F4_31] at F5_31
  obtain ⟨f6, e6, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, F6_5, F6_6, F6_7, F6_10, F6_11, F6_12, F6_13, F6_14, F6_17, F6_18, F6_19, F6_20, F6_21, F6_22, F6_23, F6_24, F6_25, F6_26, F6_27, F6_28, F6_29, F6_30, F6_31⟩ := s5RoundS5_dag M f5
  rw [e6] at E
  rw [F5_31] at h60
  rw [F5_31] at h61
  rw [F5_24] at h62
  rw [F5_24] at h64
  rw [F5_11] at h66
  rw [F5_12] at h67
  rw [F5_31] at h68
  rw [F5_31] at h69
  rw [F5_24] at h70
  rw [F5_5] at F6_5
  rw [F5_6] at F6_6
  rw [F5_7] at F6_7
  rw [F5_10] at F6_10
  rw [F5_17] at F6_17
  rw [F5_18] at F6_18
  rw [F5_19] at F6_19
  rw [F5_20] at F6_20
  rw [F5_21] at F6_21
  rw [F5_22] at F6_22
  rw [F5_23] at F6_23
  rw [F5_24] at F6_24
  rw [F5_25] at F6_25
  rw [F5_26] at F6_26
  rw [F5_27] at F6_27
  rw [F5_28] at F6_28
  rw [F5_29] at F6_29
  rw [F5_30] at F6_30
  rw [F5_31] at F6_31
  obtain ⟨f7, e7, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, F7_5, F7_6, F7_7, F7_10, F7_11, F7_12, F7_13, F7_14, F7_17, F7_18, F7_19, F7_20, F7_21, F7_22, F7_23, F7_24, F7_25, F7_26, F7_27, F7_28, F7_29, F7_30, F7_31⟩ := s5RoundS6_dag M f6
  rw [e7] at E
  rw [F6_24] at h72
  rw [F6_13] at h73
  rw [F6_12, F6_14] at h74
  rw [F6_11] at h75
  rw [F6_7, F6_26] at h76
  rw [F6_28, F6_18] at h77
  rw [F6_24] at h78
  rw [F6_31] at h79
  rw [F6_28, F6_18] at h80
  rw [F6_7, F6_26] at h82
  rw [F6_5] at F7_5
  rw [F6_6] at F7_6
  rw [F6_7] at F7_7
  rw [F6_10] at F7_10
  rw [F6_17] at F7_17
  rw [F6_18] at F7_18
  rw [F6_19] at F7_19
  rw [F6_20] at F7_20
  rw [F6_21] at F7_21
  rw [F6_22] at F7_22
  rw [F6_23] at F7_23
  rw [F6_24] at F7_24
  rw [F6_25] at F7_25
  rw [F6_26] at F7_26
  rw [F6_27] at F7_27
  rw [F6_28] at F7_28
  rw [F6_29] at F7_29
  rw [F6_30] at F7_30
  rw [F6_31] at F7_31
  obtain ⟨f8, e8, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, h84, h85, h86, h87, h88, h89, h90, h91, h92, h93, h94, h95, F8_5, F8_6, F8_7, F8_10, F8_12, F8_13, F8_17, F8_18, F8_21, F8_22, F8_23, F8_24, F8_25, F8_26, F8_27, F8_28, F8_29, F8_30, F8_31⟩ := s5RoundS7_dag M f7
  rw [e8] at E
  rw [F7_14, F7_12] at h84
  rw [F7_11, F7_13] at h85
  rw [F7_14] at h86
  rw [F7_23, F7_19] at h88
  rw [F7_23] at h89
  rw [F7_23] at h90
  rw [F7_20] at h91
  rw [F7_10] at h94
  rw [F7_10] at h95
  rw [F7_5] at F8_5
  rw [F7_6] at F8_6
  rw [F7_7] at F8_7
  rw [F7_17] at F8_17
  rw [F7_18] at F8_18
  rw [F7_21] at F8_21
  rw [F7_22] at F8_22
  rw [F7_24] at F8_24
  rw [F7_25] at F8_25
  rw [F7_26] at F8_26
  rw [F7_27] at F8_27
  rw [F7_28] at F8_28
  rw [F7_29] at F8_29
  rw [F7_30] at F8_30
  rw [F7_31] at F8_31
  obtain ⟨f9, e9, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, h96, h97, h98, h99, h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, F9_1, F9_5, F9_6, F9_7, F9_10, F9_12, F9_13, F9_16, F9_17, F9_18, F9_19, F9_20, F9_21, F9_23, F9_25, F9_26, F9_28, F9_29, F9_30⟩ := s5RoundS8_dag M f8
  rw [e9] at E
  rw [F8_25] at h96
  rw [F8_30] at h97
  rw [F8_29] at h98
  rw [F8_17] at h99
  rw [F8_21] at h100
  rw [F8_6] at h101
  rw [F8_5] at h102
  rw [F8_27] at h103
  rw [F8_22] at h104
  rw [F8_18] at h105
  rw [F8_26] at h106
  rw [F8_28] at h107
  rw [F8_7] at h108
  rw [F8_31] at h109
  rw [F8_24] at h110
  rw [F8_10] at F9_10
  rw [F8_12] at F9_12
  rw [F8_13] at F9_13
  rw [F8_23] at F9_23
  simp only [E]
  rw [F9_23, F9_10, F9_12, F9_13, F9_1, F9_16, F9_17, F9_21, F9_6, F9_5, F9_19, F9_20, F9_18, F9_26, F9_28, F9_7, F9_25, F9_30, F9_29]
  have s3 : v3 = hi64 (v.e.rotateRight 14) := by
    rw [← h3, ← h0, ← h1, hi64_rotr (r := 14) v.e (by decide) (by decide)]; exact BitVec.or_comm _ _
  have s5 : v5 = lo64 (v.e.rotateRight 14) := by
    rw [← h5, ← h4, ← h2, lo64_rotr (r := 14) v.e (by decide) (by decide)]; exact BitVec.or_comm _ _
  have s10 : v10 = lo64 (v.e.rotateRight 18) := by
    rw [← h10, ← h8, ← h7, lo64_rotr (r := 18) v.e (by decide) (by decide)]; exact BitVec.or_comm _ _
  have s11 : v11 = hi64 (v.e.rotateRight 18) := by
    rw [← h11, ← h9, ← h6, hi64_rotr (r := 18) v.e (by decide) (by decide)]; rfl
  have s12 : v12 = lo64 ((v.e.rotateRight 18) ^^^ (v.e.rotateRight 14)) := by rw [← h12, s10, s5, lo64_xor (v.e.rotateRight 18) (v.e.rotateRight 14)]; rfl
  have s13 : v13 = hi64 ((v.e.rotateRight 14) ^^^ (v.e.rotateRight 18)) := by rw [← h13, s3, s11, hi64_xor (v.e.rotateRight 14) (v.e.rotateRight 18)]; rfl
  have s18 : v18 = hi64 (v.e.rotateRight 41) := by
    rw [← h18, ← h15, ← h16, hi64_rotr' (r := 41) v.e (by decide) (by decide)]; rfl
  have s19 : v19 = lo64 (v.e.rotateRight 41) := by
    rw [← h19, ← h14, ← h17, lo64_rotr' (r := 41) v.e (by decide) (by decide)]; exact BitVec.or_comm _ _
  have s20 : v20 = hi64 (((v.e.rotateRight 14) ^^^ (v.e.rotateRight 18)) ^^^ (v.e.rotateRight 41)) := by rw [← h20, s13, s18, hi64_xor ((v.e.rotateRight 14) ^^^ (v.e.rotateRight 18)) (v.e.rotateRight 41)]; rfl
  have s21 : v21 = lo64 (((v.e.rotateRight 18) ^^^ (v.e.rotateRight 14)) ^^^ (v.e.rotateRight 41)) := by rw [← h21, s12, s19, lo64_xor ((v.e.rotateRight 18) ^^^ (v.e.rotateRight 14)) (v.e.rotateRight 41)]; rfl
  have s22 : v22 = lo64 (v.f &&& v.e) := by rw [← h22, lo64_and v.f v.e]; rfl
  have s23 : v23 = hi64 (v.f &&& v.e) := by rw [← h23, hi64_and v.f v.e]; rfl
  have s24 : v24 = hi64 (~~~v.e) := by rw [← h24, hi64_not]; rfl
  have s25 : v25 = lo64 (~~~v.e) := by rw [← h25, lo64_not]; rfl
  have s26 : v26 = hi64 (v.g &&& (~~~v.e)) := by rw [← h26, s24, hi64_and v.g (~~~v.e)]; rfl
  have s27 : v27 = lo64 (v.g &&& (~~~v.e)) := by rw [← h27, s25, lo64_and v.g (~~~v.e)]; rfl
  have s31 : v31 = lo64 Sha512.k[t]! := by rw [← h31, ← h30, show aluEval .add 0 kp = kp from BitVec.zero_add _]; exact hk0
  have s32 : v32 = hi64 Sha512.k[t]! := by rw [← h32, ← h30, show aluEval .add 0 kp = kp from BitVec.zero_add _]; exact hk1
  have s40 : v40 = lo64 (w t) := by rw [← h40, ← h39, show aluEval .add 0 wp = wp from BitVec.zero_add _]; exact hw0
  have s41 : v41 = hi64 (w t) := by rw [← h41, ← h39, show aluEval .add 0 wp = wp from BitVec.zero_add _]; exact hw1
  have s56 : v56 = lo64 (v.a.rotateRight 28) := by
    rw [← h56, ← h53, ← h54, lo64_rotr (r := 28) v.a (by decide) (by decide)]; rfl
  have s59 : v59 = hi64 (v.a.rotateRight 28) := by
    rw [← h59, ← h57, ← h58, hi64_rotr (r := 28) v.a (by decide) (by decide)]; exact BitVec.or_comm _ _
  have s63 : v63 = hi64 (v.a.rotateRight 34) := by
    rw [← h63, ← h61, ← h62, hi64_rotr' (r := 34) v.a (by decide) (by decide)]; rfl
  have s65 : v65 = lo64 (v.a.rotateRight 34) := by
    rw [← h65, ← h60, ← h64, lo64_rotr' (r := 34) v.a (by decide) (by decide)]; exact BitVec.or_comm _ _
  have s66 : v66 = hi64 ((v.a.rotateRight 28) ^^^ (v.a.rotateRight 34)) := by rw [← h66, s59, s63, hi64_xor (v.a.rotateRight 28) (v.a.rotateRight 34)]; rfl
  have s67 : v67 = lo64 ((v.a.rotateRight 28) ^^^ (v.a.rotateRight 34)) := by rw [← h67, s56, s65, lo64_xor (v.a.rotateRight 28) (v.a.rotateRight 34)]; rfl
  have s70 : v70 = hi64 (v.a >>> 7) := by rw [← h70, hi64_shr 7 v.a]; rfl
  have s71 : v71 = lo64 (v.a.rotateRight 39) := by
    rw [← h71, ← h69, ← h70, lo64_rotr' (r := 39) v.a (by decide) (by decide)]; exact BitVec.or_comm _ _
  have s73 : v73 = hi64 (v.a.rotateRight 39) := by
    rw [← h73, ← h68, ← h72, hi64_rotr' (r := 39) v.a (by decide) (by decide)]; rfl
  have s74 : v74 = lo64 (((v.a.rotateRight 28) ^^^ (v.a.rotateRight 34)) ^^^ (v.a.rotateRight 39)) := by rw [← h74, s67, s71, lo64_xor ((v.a.rotateRight 28) ^^^ (v.a.rotateRight 34)) (v.a.rotateRight 39)]; rfl
  have s75 : v75 = hi64 (((v.a.rotateRight 28) ^^^ (v.a.rotateRight 34)) ^^^ (v.a.rotateRight 39)) := by rw [← h75, s66, s73, hi64_xor ((v.a.rotateRight 28) ^^^ (v.a.rotateRight 34)) (v.a.rotateRight 39)]; rfl
  have s76 : v76 = hi64 (v.b ^^^ v.c) := by rw [← h76, hi64_xor v.b v.c]; rfl
  have s77 : v77 = lo64 (v.b ^^^ v.c) := by rw [← h77, lo64_xor v.b v.c]; rfl
  have s78 : v78 = hi64 ((v.b ^^^ v.c) &&& v.a) := by rw [← h78, s76, hi64_and (v.b ^^^ v.c) v.a]; rfl
  have s79 : v79 = lo64 ((v.b ^^^ v.c) &&& v.a) := by rw [← h79, s77, lo64_and (v.b ^^^ v.c) v.a]; rfl
  have s80 : v80 = lo64 (v.b &&& v.c) := by rw [← h80, lo64_and v.b v.c]; rfl
  have s81 : v81 = lo64 (((v.b ^^^ v.c) &&& v.a) ^^^ (v.b &&& v.c)) := by rw [← h81, s79, s80, lo64_xor ((v.b ^^^ v.c) &&& v.a) (v.b &&& v.c)]; rfl
  have s82 : v82 = hi64 (v.b &&& v.c) := by rw [← h82, hi64_and v.b v.c]; rfl
  have s83 : v83 = hi64 (((v.b ^^^ v.c) &&& v.a) ^^^ (v.b &&& v.c)) := by rw [← h83, s78, s82, hi64_xor ((v.b ^^^ v.c) &&& v.a) (v.b &&& v.c)]; rfl
  have s99 : v99 = lo64 v.g := by rw [← h99]; exact BitVec.zero_add _
  have s100 : v100 = hi64 v.g := by rw [← h100]; exact BitVec.zero_add _
  have s101 : v101 = lo64 v.f := by rw [← h101]; exact BitVec.zero_add _
  have s102 : v102 = hi64 v.f := by rw [← h102]; exact BitVec.zero_add _
  have s103 : v103 = lo64 v.e := by rw [← h103]; exact BitVec.zero_add _
  have s104 : v104 = hi64 v.e := by rw [← h104]; exact BitVec.zero_add _
  have s105 : v105 = lo64 v.c := by rw [← h105]; exact BitVec.zero_add _
  have s106 : v106 = hi64 v.c := by rw [← h106]; exact BitVec.zero_add _
  have s107 : v107 = lo64 v.b := by rw [← h107]; exact BitVec.zero_add _
  have s108 : v108 = hi64 v.b := by rw [← h108]; exact BitVec.zero_add _
  have s109 : v109 = lo64 v.a := by rw [← h109]; exact BitVec.zero_add _
  have s110 : v110 = hi64 v.a := by rw [← h110]; exact BitVec.zero_add _
  have c20 : v20 = hi64 (Sha512.bigSigma1 v.e) := by
    rw [s20, show (((v.e.rotateRight 14) ^^^ (v.e.rotateRight 18)) ^^^ (v.e.rotateRight 41)) = (Sha512.bigSigma1 v.e) by unfold Sha512.bigSigma1 Sha512.rotr; ac_rfl]
  have c21 : v21 = lo64 (Sha512.bigSigma1 v.e) := by
    rw [s21, show (((v.e.rotateRight 18) ^^^ (v.e.rotateRight 14)) ^^^ (v.e.rotateRight 41)) = (Sha512.bigSigma1 v.e) by unfold Sha512.bigSigma1 Sha512.rotr; ac_rfl]
  have c26 : v26 = hi64 (v.g &&& ~~~v.e) := by rw [s26]
  have c27 : v27 = lo64 (v.g &&& ~~~v.e) := by rw [s27]
  have c81 : v81 = lo64 (Sha512.maj v.a v.b v.c) := by rw [s81, Sha512.maj_alt]
  have c83 : v83 = hi64 (Sha512.maj v.a v.b v.c) := by rw [s83, Sha512.maj_alt]
  have c74 : v74 = lo64 (Sha512.bigSigma0 v.a) := by
    rw [s74, show (((v.a.rotateRight 28) ^^^ (v.a.rotateRight 34)) ^^^ (v.a.rotateRight 39)) = (Sha512.bigSigma0 v.a) by unfold Sha512.bigSigma0 Sha512.rotr; ac_rfl]
  have c75 : v75 = hi64 (Sha512.bigSigma0 v.a) := by
    rw [s75, show (((v.a.rotateRight 28) ^^^ (v.a.rotateRight 34)) ^^^ (v.a.rotateRight 39)) = (Sha512.bigSigma0 v.a) by unfold Sha512.bigSigma0 Sha512.rotr; ac_rfl]
  have n28 : v28.toNat = (v20.toNat + (hi64 v.h).toNat) % 2 ^ 32 := by rw [← h28]; exact BitVec.toNat_add _ _
  have n29 : v29.toNat = (v28.toNat + v26.toNat) % 2 ^ 32 := by rw [← h29]; exact BitVec.toNat_add _ _
  have n33 : v33.toNat = ((lo64 v.h).toNat + v21.toNat) % 2 ^ 32 := by rw [← h33]; exact BitVec.toNat_add _ _
  have n34 : v34.toNat = ((lo64 v.h).toNat + v21.toNat) / 2 ^ 32 := by
    rw [← h34, ← h33]; exact sltu_carry' _ _
  have n35 : v35.toNat = (v27.toNat + v33.toNat) % 2 ^ 32 := by rw [← h35]; exact BitVec.toNat_add _ _
  have n36 : v36.toNat = (v27.toNat + v33.toNat) / 2 ^ 32 := by
    rw [← h36, ← h35]; exact sltu_carry' _ _
  have n37 : v37.toNat = (v34.toNat + v29.toNat) % 2 ^ 32 := by rw [← h37]; exact BitVec.toNat_add _ _
  have n38 : v38.toNat = (v37.toNat + v36.toNat) % 2 ^ 32 := by rw [← h38]; exact BitVec.toNat_add _ _
  have n42 : v42.toNat = (v22.toNat + v35.toNat) % 2 ^ 32 := by rw [← h42]; exact BitVec.toNat_add _ _
  have n43 : v43.toNat = (v38.toNat + v23.toNat) % 2 ^ 32 := by rw [← h43]; exact BitVec.toNat_add _ _
  have n44 : v44.toNat = (v22.toNat + v35.toNat) / 2 ^ 32 := by
    rw [← h44, ← h42]; exact sltu_carry' _ _
  have n45 : v45.toNat = (v32.toNat + v44.toNat) % 2 ^ 32 := by rw [← h45]; exact BitVec.toNat_add _ _
  have n46 : v46.toNat = (v31.toNat + v42.toNat) % 2 ^ 32 := by rw [← h46]; exact BitVec.toNat_add _ _
  have n47 : v47.toNat = (v43.toNat + v45.toNat) % 2 ^ 32 := by rw [← h47]; exact BitVec.toNat_add _ _
  have n48 : v48.toNat = (v31.toNat + v42.toNat) / 2 ^ 32 := by
    rw [← h48, ← h46]; exact sltu_carry' _ _
  have n49 : v49.toNat = (v48.toNat + v41.toNat) % 2 ^ 32 := by rw [← h49]; exact BitVec.toNat_add _ _
  have n50 : v50.toNat = (v46.toNat + v40.toNat) % 2 ^ 32 := by rw [← h50]; exact BitVec.toNat_add _ _
  have n51 : v51.toNat = (v47.toNat + v49.toNat) % 2 ^ 32 := by rw [← h51]; exact BitVec.toNat_add _ _
  have n52 : v52.toNat = (v46.toNat + v40.toNat) / 2 ^ 32 := by
    rw [← h52, ← h50]; exact sltu_carry _ _
  have n55 : v55.toNat = (v51.toNat + v52.toNat) % 2 ^ 32 := by rw [← h55]; exact BitVec.toNat_add _ _
  have n84 : v84.toNat = (v81.toNat + v74.toNat) % 2 ^ 32 := by rw [← h84]; exact BitVec.toNat_add _ _
  have n85 : v85.toNat = (v75.toNat + v83.toNat) % 2 ^ 32 := by rw [← h85]; exact BitVec.toNat_add _ _
  have n86 : v86.toNat = (v81.toNat + v74.toNat) / 2 ^ 32 := by
    rw [← h86, ← h84]; exact sltu_carry _ _
  have n87 : v87.toNat = (v85.toNat + v86.toNat) % 2 ^ 32 := by rw [← h87]; exact BitVec.toNat_add _ _
  have n88 : v88.toNat = (v50.toNat + (lo64 v.d).toNat) % 2 ^ 32 := by rw [← h88]; exact BitVec.toNat_add _ _
  have n89 : v89.toNat = (v50.toNat + (lo64 v.d).toNat) / 2 ^ 32 := by
    rw [← h89, ← h88]; exact sltu_carry _ _
  have n90 : v90.toNat = (v50.toNat + v84.toNat) % 2 ^ 32 := by rw [← h90]; exact BitVec.toNat_add _ _
  have n91 : v91.toNat = (v89.toNat + (hi64 v.d).toNat) % 2 ^ 32 := by rw [← h91]; exact BitVec.toNat_add _ _
  have n92 : v92.toNat = (v50.toNat + v84.toNat) / 2 ^ 32 := by
    rw [← h92, ← h90]; exact sltu_carry' _ _
  have n93 : v93.toNat = (v87.toNat + v92.toNat) % 2 ^ 32 := by rw [← h93]; exact BitVec.toNat_add _ _
  have n94 : v94.toNat = (v91.toNat + v55.toNat) % 2 ^ 32 := by rw [← h94]; exact BitVec.toNat_add _ _
  have n95 : v95.toNat = (v55.toNat + v93.toNat) % 2 ^ 32 := by rw [← h95]; exact BitVec.toNat_add _ _
  have A_h : HoldsN (lo64 v.h) (hi64 v.h).toNat v.h := holdsN_atom _
  have A_s1 : HoldsN v21 v20.toNat (Sha512.bigSigma1 v.e) := by rw [c21, c20]; exact holdsN_atom _
  have A_gne : HoldsN v27 v26.toNat (v.g &&& ~~~v.e) := by rw [c27, c26]; exact holdsN_atom _
  have A_fe : HoldsN v22 v23.toNat (v.f &&& v.e) := by rw [s22, s23]; exact holdsN_atom _
  have A_k : HoldsN v31 v32.toNat Sha512.k[t]! := by rw [s31, s32]; exact holdsN_atom _
  have A_w : HoldsN v40 v41.toNat (w t) := by rw [s40, s41]; exact holdsN_atom _
  have A_s0 : HoldsN v74 v75.toNat (Sha512.bigSigma0 v.a) := by rw [c74, c75]; exact holdsN_atom _
  have A_mj : HoldsN v81 v83.toNat (Sha512.maj v.a v.b v.c) := by rw [c81, c83]; exact holdsN_atom _
  have A_d : HoldsN (lo64 v.d) (hi64 v.d).toNat v.d := holdsN_atom _
  have P5 := holdsN_add (holdsN_add' (holdsN_add' (holdsN_add' (holdsN_add A_h A_s1 n33 n34) A_gne n35 n36)
    A_fe n42 n44) A_k n46 n48) A_w n50 n52
  have H55 := dm_add n55 (dm_add n51 (dm_add n47 (dm_add n43 (dm_add n38 (dm_add n37 (dm_leaf v34)
    (dm_add n29 (dm_add n28 (dm_leaf v20) (dm_leaf (hi64 v.h))) (dm_leaf v26))) (dm_leaf v36)) (dm_leaf v23))
    (dm_add n45 (dm_leaf v32) (dm_leaf v44))) (dm_add n49 (dm_leaf v48) (dm_leaf v41))) (dm_leaf v52)
  have Q1 := holdsN_close P5 H55 (by ac_rfl)
  have Q2 := holdsN_close (holdsN_add A_mj A_s0 n84 n86)
    (dm_add n87 (dm_add n85 (dm_leaf v75) (dm_leaf v83)) (dm_leaf v86)) (by ac_rfl)
  have RA := holdsN_halves (holdsN_add Q1 Q2 n90 n92)
    (dm_add n95 (dm_leaf v55) (dm_add n93 (dm_leaf v87) (dm_leaf v92))) (by ac_rfl)
  have RE := holdsN_halves (holdsN_add Q1 A_d n88 n89)
    (dm_add n94 (dm_add n91 (dm_leaf v89) (dm_leaf (hi64 v.d))) (dm_leaf v55)) (by ac_rfl)
  have eT1 : v.h + Sha512.bigSigma1 v.e + (v.g &&& ~~~v.e) + (v.f &&& v.e) + Sha512.k[t]! + w t =
      v.h + Sha512.bigSigma1 v.e + Sha512.ch v.e v.f v.g + Sha512.k[t]! + w t := by
    rw [Sha512.ch_add, BitVec.add_comm (v.f &&& v.e), ← BitVec.add_assoc]
  rw [eT1, BitVec.add_comm (Sha512.maj v.a v.b v.c)] at RA
  rw [eT1, BitVec.add_comm _ v.d] at RE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact RA.1
  · exact RA.2
  · exact RE.1
  · exact RE.2
  · exact s99
  · exact s100
  · exact s101
  · exact s102
  · exact s103
  · exact s104
  · exact s105
  · exact s106
  · exact s107
  · exact s108
  · exact s109
  · exact s110
  · rw [← h96]; rfl
  · rw [← h97]; rfl
  · rw [← h98]; rfl

end C3.RV32
