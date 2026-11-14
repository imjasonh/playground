import C3BootProofs.Proofs.FeSquare
import C3BootProofs.Proofs.FeAdd
import C3BootProofs.Proofs.FeSub
import C3BootProofs.Proofs.P384Double

/-!
# `curve25519_dalek`'s `ProjectivePoint::double`

The doubling of a projective point, as compiled: three `square` calls,
`square2` inlined as `square_inner`, a loop that doubles each `u64`, and
`reduce`, then two `add` calls and three `sub` calls into its frame and the
result, and two `memcpy` calls that copy the last two coordinates out.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem edd_at_0 : fetchRel edDoubleCode 0x0 = some (.aluImm .add sp sp 0xFFFFFEA0, 2) := by decide
theorem edd_at_2 : fetchRel edDoubleCode 0x2 = some (.aluImm .add a2 sp 0x100, 2) := by decide
theorem edd_at_4 : fetchRel edDoubleCode 0x4 = some (.store .sw a2 ra 0x5C, 4) := by decide
theorem edd_at_8 : fetchRel edDoubleCode 0x8 = some (.store .sw a2 (8 : Fin 32) 0x58, 2) := by decide
theorem edd_at_a : fetchRel edDoubleCode 0xA = some (.store .sw a2 (9 : Fin 32) 0x54, 2) := by decide
theorem edd_at_c : fetchRel edDoubleCode 0xC = some (.store .sw a2 (18 : Fin 32) 0x50, 4) := by decide
theorem edd_at_10 : fetchRel edDoubleCode 0x10 = some (.store .sw a2 (19 : Fin 32) 0x4C, 4) := by decide
theorem edd_at_14 : fetchRel edDoubleCode 0x14 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem edd_at_16 : fetchRel edDoubleCode 0x16 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem edd_at_18 : fetchRel edDoubleCode 0x18 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem edd_at_1a : fetchRel edDoubleCode 0x1A = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem edd_at_1e : fetchRel edDoubleCode 0x1E = some (.jalr ra ra 0x14A, 4) := by decide
theorem edd_at_22 : fetchRel edDoubleCode 0x22 = some (.aluImm .add (19 : Fin 32) (9 : Fin 32) 0x28, 4) := by decide
theorem edd_at_26 : fetchRel edDoubleCode 0x26 = some (.aluImm .add a0 sp 0x30, 2) := by decide
theorem edd_at_28 : fetchRel edDoubleCode 0x28 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem edd_at_2a : fetchRel edDoubleCode 0x2A = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem edd_at_2e : fetchRel edDoubleCode 0x2E = some (.jalr ra ra 0x13A, 4) := by decide
theorem edd_at_32 : fetchRel edDoubleCode 0x32 = some (.aluImm .add a1 (9 : Fin 32) 0x50, 4) := by decide
theorem edd_at_36 : fetchRel edDoubleCode 0x36 = some (.aluImm .add a0 sp 0xF8, 2) := by decide
theorem edd_at_38 : fetchRel edDoubleCode 0x38 = some (.aluImm .add (8 : Fin 32) sp 0xF8, 2) := by decide
theorem edd_at_3a : fetchRel edDoubleCode 0x3A = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem edd_at_3e : fetchRel edDoubleCode 0x3E = some (.jalr ra ra 0x150, 4) := by decide
theorem edd_at_42 : fetchRel edDoubleCode 0x42 = some (.aluImm .add a0 x0 0x50, 4) := by decide
theorem edd_at_46 : fetchRel edDoubleCode 0x46 = some (.branch .beq a0 x0 0x1A, 2) := by decide
theorem edd_at_48 : fetchRel edDoubleCode 0x48 = some (.load .lw a1 (8 : Fin 32) 0x0, 2) := by decide
theorem edd_at_4a : fetchRel edDoubleCode 0x4A = some (.load .lw a2 (8 : Fin 32) 0x4, 2) := by decide
theorem edd_at_4c : fetchRel edDoubleCode 0x4C = some (.aluImm .srl a3 a1 0x1F, 4) := by decide
theorem edd_at_50 : fetchRel edDoubleCode 0x50 = some (.aluImm .sll a2 a2 0x1, 2) := by decide
theorem edd_at_52 : fetchRel edDoubleCode 0x52 = some (.aluImm .sll a1 a1 0x1, 2) := by decide
theorem edd_at_54 : fetchRel edDoubleCode 0x54 = some (.alu .or a2 a2 a3, 2) := by decide
theorem edd_at_56 : fetchRel edDoubleCode 0x56 = some (.store .sw (8 : Fin 32) a1 0x0, 2) := by decide
theorem edd_at_58 : fetchRel edDoubleCode 0x58 = some (.store .sw (8 : Fin 32) a2 0x4, 2) := by decide
theorem edd_at_5a : fetchRel edDoubleCode 0x5A = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x8, 2) := by decide
theorem edd_at_5c : fetchRel edDoubleCode 0x5C = some (.aluImm .add a0 a0 0xFFFFFFF8, 2) := by decide
theorem edd_at_5e : fetchRel edDoubleCode 0x5E = some (.branch .bne a0 x0 0xFFFFFFEA, 2) := by decide
theorem edd_at_60 : fetchRel edDoubleCode 0x60 = some (.aluImm .add a0 sp 0x58, 2) := by decide
theorem edd_at_62 : fetchRel edDoubleCode 0x62 = some (.aluImm .add a1 sp 0xF8, 2) := by decide
theorem edd_at_64 : fetchRel edDoubleCode 0x64 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem edd_at_68 : fetchRel edDoubleCode 0x68 = some (.jalr ra ra 0xFFFFFD8C, 4) := by decide
theorem edd_at_6c : fetchRel edDoubleCode 0x6C = some (.aluImm .add a0 sp 0x80, 2) := by decide
theorem edd_at_6e : fetchRel edDoubleCode 0x6E = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem edd_at_70 : fetchRel edDoubleCode 0x70 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem edd_at_72 : fetchRel edDoubleCode 0x72 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem edd_at_76 : fetchRel edDoubleCode 0x76 = some (.jalr ra ra 0x602, 4) := by decide
theorem edd_at_7a : fetchRel edDoubleCode 0x7A = some (.aluImm .add a0 sp 0xA8, 2) := by decide
theorem edd_at_7c : fetchRel edDoubleCode 0x7C = some (.aluImm .add a1 sp 0x80, 2) := by decide
theorem edd_at_7e : fetchRel edDoubleCode 0x7E = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem edd_at_82 : fetchRel edDoubleCode 0x82 = some (.jalr ra ra 0xE6, 4) := by decide
theorem edd_at_86 : fetchRel edDoubleCode 0x86 = some (.aluImm .add a0 sp 0xD0, 2) := by decide
theorem edd_at_88 : fetchRel edDoubleCode 0x88 = some (.aluImm .add a1 sp 0x30, 2) := by decide
theorem edd_at_8a : fetchRel edDoubleCode 0x8A = some (.aluImm .add a2 sp 0x8, 2) := by decide
theorem edd_at_8c : fetchRel edDoubleCode 0x8C = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem edd_at_90 : fetchRel edDoubleCode 0x90 = some (.jalr ra ra 0x5E8, 4) := by decide
theorem edd_at_94 : fetchRel edDoubleCode 0x94 = some (.aluImm .add a0 sp 0xF8, 2) := by decide
theorem edd_at_96 : fetchRel edDoubleCode 0x96 = some (.aluImm .add a1 sp 0x30, 2) := by decide
theorem edd_at_98 : fetchRel edDoubleCode 0x98 = some (.aluImm .add a2 sp 0x8, 2) := by decide
theorem edd_at_9a : fetchRel edDoubleCode 0x9A = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem edd_at_9e : fetchRel edDoubleCode 0x9E = some (.jalr ra ra 0x628, 4) := by decide
theorem edd_at_a2 : fetchRel edDoubleCode 0xA2 = some (.aluImm .add a1 sp 0xA8, 2) := by decide
theorem edd_at_a4 : fetchRel edDoubleCode 0xA4 = some (.aluImm .add a2 sp 0xD0, 2) := by decide
theorem edd_at_a6 : fetchRel edDoubleCode 0xA6 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem edd_at_a8 : fetchRel edDoubleCode 0xA8 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem edd_at_ac : fetchRel edDoubleCode 0xAC = some (.jalr ra ra 0x61A, 4) := by decide
theorem edd_at_b0 : fetchRel edDoubleCode 0xB0 = some (.aluImm .add a0 (18 : Fin 32) 0x78, 4) := by decide
theorem edd_at_b4 : fetchRel edDoubleCode 0xB4 = some (.aluImm .add a1 sp 0x58, 2) := by decide
theorem edd_at_b6 : fetchRel edDoubleCode 0xB6 = some (.aluImm .add a2 sp 0xF8, 2) := by decide
theorem edd_at_b8 : fetchRel edDoubleCode 0xB8 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem edd_at_bc : fetchRel edDoubleCode 0xBC = some (.jalr ra ra 0x60A, 4) := by decide
theorem edd_at_c0 : fetchRel edDoubleCode 0xC0 = some (.aluImm .add a0 (18 : Fin 32) 0x28, 4) := by decide
theorem edd_at_c4 : fetchRel edDoubleCode 0xC4 = some (.aluImm .add a1 sp 0xD0, 2) := by decide
theorem edd_at_c6 : fetchRel edDoubleCode 0xC6 = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem edd_at_ca : fetchRel edDoubleCode 0xCA = some (.auipc ra 0x4000, 4) := by decide
theorem edd_at_ce : fetchRel edDoubleCode 0xCE = some (.jalr ra ra 0x332, 4) := by decide
theorem edd_at_d2 : fetchRel edDoubleCode 0xD2 = some (.aluImm .add a0 (18 : Fin 32) 0x50, 4) := by decide
theorem edd_at_d6 : fetchRel edDoubleCode 0xD6 = some (.aluImm .add a1 sp 0xF8, 2) := by decide
theorem edd_at_d8 : fetchRel edDoubleCode 0xD8 = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem edd_at_dc : fetchRel edDoubleCode 0xDC = some (.auipc ra 0x4000, 4) := by decide
theorem edd_at_e0 : fetchRel edDoubleCode 0xE0 = some (.jalr ra ra 0x320, 4) := by decide
theorem edd_at_e4 : fetchRel edDoubleCode 0xE4 = some (.aluImm .add a0 sp 0x100, 2) := by decide
theorem edd_at_e6 : fetchRel edDoubleCode 0xE6 = some (.load .lw ra a0 0x5C, 4) := by decide
theorem edd_at_ea : fetchRel edDoubleCode 0xEA = some (.load .lw (8 : Fin 32) a0 0x58, 2) := by decide
theorem edd_at_ec : fetchRel edDoubleCode 0xEC = some (.load .lw (9 : Fin 32) a0 0x54, 2) := by decide
theorem edd_at_ee : fetchRel edDoubleCode 0xEE = some (.load .lw (18 : Fin 32) a0 0x50, 4) := by decide
theorem edd_at_f2 : fetchRel edDoubleCode 0xF2 = some (.load .lw (19 : Fin 32) a0 0x4C, 4) := by decide
theorem edd_at_f6 : fetchRel edDoubleCode 0xF6 = some (.aluImm .add sp sp 0x160, 2) := by decide
theorem edd_at_f8 : fetchRel edDoubleCode 0xF8 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- The ten limbs of the field element at `a`. -/
def feW (M : Word → BitVec 8) (a : Word) : List Nat :=
  [limbAt M a 0, limbAt M a 1, limbAt M a 2, limbAt M a 3, limbAt M a 4, limbAt M a 5, limbAt M a 6,
   limbAt M a 7, limbAt M a 8, limbAt M a 9]

/-- `FieldElement2625::square` on limbs. -/
def sqL (l : List Nat) : List Nat := feSquareSpec l[0]! l[1]! l[2]! l[3]! l[4]! l[5]! l[6]! l[7]! l[8]! l[9]!

/-- `reduce` of ten `u64`s, each doubled modulo 2^64. -/
def dblRed (z : List Nat) : List Nat :=
  feReduceSpec (2 * z[0]! % 2 ^ 64) (2 * z[1]! % 2 ^ 64) (2 * z[2]! % 2 ^ 64) (2 * z[3]! % 2 ^ 64)
    (2 * z[4]! % 2 ^ 64) (2 * z[5]! % 2 ^ 64) (2 * z[6]! % 2 ^ 64) (2 * z[7]! % 2 ^ 64) (2 * z[8]! % 2 ^ 64)
    (2 * z[9]! % 2 ^ 64)

/-- `FieldElement2625::square2`: `square_inner`'s ten sums, each doubled as a
`u64`, then `reduce`. -/
def sq2L (l : List Nat) : List Nat := dblRed (feSqZ l[0]! l[1]! l[2]! l[3]! l[4]! l[5]! l[6]! l[7]! l[8]! l[9]!)

/-- `<&FieldElement2625 as Add>::add` on limbs: each sum modulo 2^32. -/
def addL (l r : List Nat) : List Nat :=
  [(l[0]! + r[0]!) % 2 ^ 32, (l[1]! + r[1]!) % 2 ^ 32, (l[2]! + r[2]!) % 2 ^ 32, (l[3]! + r[3]!) % 2 ^ 32,
   (l[4]! + r[4]!) % 2 ^ 32, (l[5]! + r[5]!) % 2 ^ 32, (l[6]! + r[6]!) % 2 ^ 32, (l[7]! + r[7]!) % 2 ^ 32,
   (l[8]! + r[8]!) % 2 ^ 32, (l[9]! + r[9]!) % 2 ^ 32]

/-- `<&FieldElement2625 as Sub>::sub` on limbs. -/
def subL (l r : List Nat) : List Nat := feSubSpec (fun i => BitVec.ofNat 32 l[i]!) (fun i => BitVec.ofNat 32 r[i]!)

/-- `ProjectivePoint::double` in the Rust source's order: the result's `X`,
`Y`, `Z`, and `T`. -/
def edDoubleSpec (X Y Z : List Nat) : List Nat × List Nat × List Nat × List Nat :=
  let XX := sqL X
  let YY := sqL Y
  let ZZ2 := sq2L Z
  let XpYsq := sqL (addL X Y)
  let YYpXX := addL YY XX
  let YYmXX := subL YY XX
  (subL XpYsq YYpXX, YYpXX, YYmXX, subL ZZ2 YYmXX)

theorem feW_words (M : Word → BitVec 8) (a : Word) : (wordsAt M a 10).map BitVec.toNat = feW M a := rfl

theorem w_ofNat_toNat (w : Word) : BitVec.ofNat 32 w.toNat = w :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt w.isLt])

theorem feW_ofNat (M : Word → BitVec 8) (a : Word) :
    ∀ i, i < 10 → memLoad32 M (a + BitVec.ofNat 32 (4 * i)) = BitVec.ofNat 32 (feW M a)[i]!
  | 0, _ => (w_ofNat_toNat _).symm
  | 1, _ => (w_ofNat_toNat _).symm
  | 2, _ => (w_ofNat_toNat _).symm
  | 3, _ => (w_ofNat_toNat _).symm
  | 4, _ => (w_ofNat_toNat _).symm
  | 5, _ => (w_ofNat_toNat _).symm
  | 6, _ => (w_ofNat_toNat _).symm
  | 7, _ => (w_ofNat_toNat _).symm
  | 8, _ => (w_ofNat_toNat _).symm
  | 9, _ => (w_ofNat_toNat _).symm
  | n + 10, h => absurd h (by omega)

theorem feSubSpec_ext {x y x' y' : Nat → Word} (hx : ∀ i, i < 10 → x i = x' i) (hy : ∀ i, i < 10 → y i = y' i) :
    feSubSpec x y = feSubSpec x' y' := by
  unfold feSubSpec
  rw [hx 0 (by decide), hx 1 (by decide), hx 2 (by decide), hx 3 (by decide), hx 4 (by decide), hx 5 (by decide),
    hx 6 (by decide), hx 7 (by decide), hx 8 (by decide), hx 9 (by decide), hy 0 (by decide), hy 1 (by decide),
    hy 2 (by decide), hy 3 (by decide), hy 4 (by decide), hy 5 (by decide), hy 6 (by decide), hy 7 (by decide),
    hy 8 (by decide), hy 9 (by decide)]

/-- `sub`'s theorem, restated over limb lists. -/
theorem feW_sub {M M' : Word → BitVec 8} {o x y : Word}
    (h : (wordsAt M' o 10).map BitVec.toNat = feSubSpec (fun i => memLoad32 M (x + BitVec.ofNat 32 (4 * i)))
      (fun i => memLoad32 M (y + BitVec.ofNat 32 (4 * i)))) :
    feW M' o = subL (feW M x) (feW M y) := by
  rw [← feW_words, h]
  exact feSubSpec_ext (feW_ofNat M x) (feW_ofNat M y)

/-- `add`'s theorem, restated over limb lists. -/
theorem feW_add {M M' : Word → BitVec 8} {o x y : Word}
    (h : ∀ i, i < 10 → memLoad32 M' (o + BitVec.ofNat 32 (4 * i)) =
      memLoad32 M (x + BitVec.ofNat 32 (4 * i)) + memLoad32 M (y + BitVec.ofNat 32 (4 * i))) :
    feW M' o = addL (feW M x) (feW M y) := by
  have e : ∀ i, i < 10 → limbAt M' o i = (limbAt M x i + limbAt M y i) % 2 ^ 32 := fun i hi => by
    unfold limbAt; rw [h i hi, BitVec.toNat_add]
  unfold feW
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide), e 5 (by decide),
    e 6 (by decide), e 7 (by decide), e 8 (by decide), e 9 (by decide)]
  rfl

/-- What `memcpy` copied, as limbs. -/
theorem feW_copy {M : Word → BitVec 8} {dst src : Word} : feW (copyBytes M dst src 40) dst = feW M src := by
  unfold feW limbAt
  rw [cb_load (i := 0) (by decide) (by decide), cb_load (i := 1) (by decide) (by decide),
    cb_load (i := 2) (by decide) (by decide), cb_load (i := 3) (by decide) (by decide),
    cb_load (i := 4) (by decide) (by decide), cb_load (i := 5) (by decide) (by decide),
    cb_load (i := 6) (by decide) (by decide), cb_load (i := 7) (by decide) (by decide),
    cb_load (i := 8) (by decide) (by decide), cb_load (i := 9) (by decide) (by decide)]

theorem feW_frame {M M' : Word → BitVec 8} {a : Word} (h : ∀ i, i < 10 →
    memLoad32 M' (a + BitVec.ofNat 32 (4 * i)) = memLoad32 M (a + BitVec.ofNat 32 (4 * i))) :
    feW M' a = feW M a := by
  unfold feW limbAt
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide),
    h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]

/-- A field element that a callee's frame leaves alone. -/
theorem feW_frame2 {M M' : Word → BitVec 8} {u v a : Word} {n k : Nat}
    (hf : ∀ x, Sep u n x 1 → Sep v k x 1 → M' x = M x) (h1 : Sep u n a 40) (h2 : Sep v k a 40) :
    feW M' a = feW M a :=
  feW_frame fun i hi => load_frame2 hf (h1.subR (c := 4 * i) (l := 4) (by omega)) (h2.subR (c := 4 * i) (l := 4) (by omega))

/-- One `u64` doubled the way the loop does it: the low word shifted left a
bit, and the high word shifted left a bit with the low word's top bit. -/
theorem dbl64 (lo hi : Word) :
    (aluEval .sll lo 1).toNat + 2 ^ 32 * (aluEval .or (aluEval .sll hi 1) (aluEval .srl lo 0x1F)).toNat =
      2 * (lo.toNat + 2 ^ 32 * hi.toNat) % 2 ^ 64 := by
  have hl := lo.isLt
  have hh := hi.isLt
  have sl : (aluEval .sll lo 1).toNat = lo.toNat * 2 % 2 ^ 32 := by
    show (lo <<< 1).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have sh : (aluEval .sll hi 1).toNat = hi.toNat * 2 % 2 ^ 32 := by
    show (hi <<< 1).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have sr : (aluEval .srl lo 0x1F).toNat = lo.toNat / 2 ^ 31 := by
    show (lo >>> 31).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have he : (aluEval .sll hi 1).toNat % 2 = 0 := by rw [sh]; omega
  have ho := or_low1 (aluEval .sll hi 1) (aluEval .srl lo 0x1F) he (by rw [sr]; omega)
  show (aluEval .sll lo 1).toNat + 2 ^ 32 * (aluEval .or (aluEval .sll hi 1) (aluEval .srl lo 0x1F)).toNat = _
  rw [show (aluEval .or (aluEval .sll hi 1) (aluEval .srl lo 0x1F)) = aluEval .sll hi 1 ||| aluEval .srl lo 0x1F
    from rfl, ho, sl, sh, sr]
  omega

theorem edd_e4 (W : Word) (j : Nat) : W + BitVec.ofNat 32 j + 4 = W + BitVec.ofNat 32 (j + 4) := by
  rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `square2`'s doubling loop, from 0x48 with `j` of the ten `u64`s at `W`
doubled: it reaches 0x60 with all ten doubled modulo 2^64, and nothing else in
memory changed. -/
theorem edd_loop {Mb : Word → BitVec 8} {P W : Word} (hc : CodeIn Mb P edDoubleCode)
    (hW : W.toNat % 4 = 0) (sWC : Sep W 80 P edDoubleCode.length) :
    ∀ r j (n : Machine) (Mj : Word → BitVec 8), j + r = 10 → 0 < r → St Mj P n 0x48 (reg n) →
      reg n a0 = BitVec.ofNat 32 (8 * r) → reg n (8 : Fin 32) = W + BitVec.ofNat 32 (8 * j) →
      (∀ t, t < j → u64At Mj W t = 2 * u64At Mb W t % 2 ^ 64) →
      (∀ x, Sep W (8 * j) x 1 → Mj x = Mb x) →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x60 (reg n') ∧
        (∀ t, t < 10 → u64At M' W t = 2 * u64At Mb W t % 2 ^ 64) ∧
        (∀ x, Sep W 80 x 1 → M' x = Mb x) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  intro r
  induction r with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ r ih =>
    intro j n Mj hjr _ s ha0 hs0 hdone hrest
    have hcj : CodeIn Mj P edDoubleCode := fun i hi => by
      rw [hrest _ (sep_pre (sWC.subR (c := i) (l := 1) (by omega)) (by omega))]; exact hc i hi
    have hz := s.zero
    have hA : (W + BitVec.ofNat 32 (8 * j)).toNat % 4 = 0 := aligned_add hW (by omega)
    have hA4 : (W + BitVec.ofNat 32 (8 * j + 4)).toNat % 4 = 0 := aligned_add hW (by omega)
    have sJ : ∀ {d k : Nat}, 8 * j ≤ d → d + k ≤ 80 → Sep W (8 * j) (W + BitVec.ofNat 32 d) k :=
      fun {d k} h1 h2 => by
        have := sep_offsets W (c := 0) (n := 8 * j) (d := d) (k := k) (.inl (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
    obtain ⟨lo, hlo⟩ : ∃ v, memLoad32 Mb (W + BitVec.ofNat 32 (8 * j)) = v := ⟨_, rfl⟩
    obtain ⟨hi, hhi⟩ : ∃ v, memLoad32 Mb (W + BitVec.ofNat 32 (8 * j + 4)) = v := ⟨_, rfl⟩
    -- 0x48 `lw a1, 0(s0)`, 0x4A `lw a2, 4(s0)`
    obtain ⟨n1, d1, u1⟩ := s.lwE hcj edd_at_48 (off' := 0x4A) (by decide)
      (by rw [hs0, add_lit_zero]; exact hA) (v := lo)
      (by rw [hs0, add_lit_zero, load_frame hrest (sJ (Nat.le_refl _) (by omega)), hlo])
    have k1 := u1.oldReg hz
    obtain ⟨n2, d2, u2⟩ := u1.self.lwE hcj edd_at_4a (off' := 0x4C) (by decide)
      (by rw [k1 _ (by decide), hs0, edd_e4]; exact hA4) (v := hi)
      (by rw [k1 _ (by decide), hs0, edd_e4, load_frame hrest (sJ (by omega) (by omega)), hhi])
    have k2 := u2.oldReg u1.self.zero
    -- 0x4C..0x54: the shifts
    obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hcj edd_at_4c (off' := 0x50) (by decide)
    have k3 := u3.oldReg u2.self.zero
    obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hcj edd_at_50 (off' := 0x52) (by decide)
    have k4 := u4.oldReg u3.self.zero
    obtain ⟨n5, d5, u5⟩ := u4.self.aluImm hcj edd_at_52 (off' := 0x54) (by decide)
    have k5 := u5.oldReg u4.self.zero
    obtain ⟨n6, d6, u6⟩ := u5.self.alu hcj edd_at_54 (off' := 0x56) (by decide)
    have k6 := u6.oldReg u5.self.zero
    have a1_6 : reg n6 a1 = aluEval .sll lo 1 := by
      rw [k6 _ (by decide), u5.newReg (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide),
        u1.newReg (by decide)]
    have a2_6 : reg n6 a2 = aluEval .or (aluEval .sll hi 1) (aluEval .srl lo 0x1F) := by
      rw [u6.newReg (by decide), k5 a2 (by decide), k5 a3 (by decide), u4.newReg (by decide), k4 a3 (by decide),
        k3 a2 (by decide), u2.newReg (by decide), u3.newReg (by decide), k2 a1 (by decide), u1.newReg (by decide)]
    have s0_6 : reg n6 (8 : Fin 32) = W + BitVec.ofNat 32 (8 * j) := by
      rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide),
        k1 _ (by decide), hs0]
    -- 0x56 `sw a1, 0(s0)`, 0x58 `sw a2, 4(s0)`
    obtain ⟨n7, d7, u7⟩ := u6.self.swG hcj edd_at_56 (off' := 0x58) (by decide)
      (by rw [s0_6, add_lit_zero]; exact hA) (a := W + BitVec.ofNat 32 (8 * j)) (v := aluEval .sll lo 1)
      (by rw [s0_6, add_lit_zero]) a1_6
    obtain ⟨M7, hM7⟩ : ∃ M, memStore32 Mj (W + BitVec.ofNat 32 (8 * j)) (aluEval .sll lo 1) = M := ⟨_, rfl⟩
    rw [hM7] at u7
    have hc7 : CodeIn M7 P edDoubleCode := by rw [← hM7]; exact hcj.store32 (sWC.sub (c := 8 * j) (l := 4) (by omega))
    obtain ⟨n8, d8, u8⟩ := u7.swG hc7 edd_at_58 (off' := 0x5A) (by decide)
      (by rw [s0_6, edd_e4]; exact hA4) (a := W + BitVec.ofNat 32 (8 * j + 4))
      (v := aluEval .or (aluEval .sll hi 1) (aluEval .srl lo 0x1F)) (by rw [s0_6, edd_e4]) a2_6
    obtain ⟨M8, hM8⟩ : ∃ M, memStore32 M7 (W + BitVec.ofNat 32 (8 * j + 4))
        (aluEval .or (aluEval .sll hi 1) (aluEval .srl lo 0x1F)) = M := ⟨_, rfl⟩
    rw [hM8] at u8
    have hc8 : CodeIn M8 P edDoubleCode := by
      rw [← hM8]; exact hc7.store32 (sWC.sub (c := 8 * j + 4) (l := 4) (by omega))
    have hrest8 : ∀ x, Sep W (8 * (j + 1)) x 1 → M8 x = Mb x := fun x hx => by
      rw [← hM8, memStore32_get_sep (hx.sub (c := 8 * j + 4) (l := 4) (by omega)), ← hM7,
        memStore32_get_sep (hx.sub (c := 8 * j) (l := 4) (by omega)), hrest x (sep_pre hx (by omega))]
    have hdone8 : ∀ t, t < j + 1 → u64At M8 W t = 2 * u64At Mb W t % 2 ^ 64 := by
      intro t ht
      by_cases htj : t = j
      · subst htj
        unfold u64At
        rw [← hM8, memLoad32_store32_same, memLoad32_store32_sep (sep_offsets W (.inr (by omega)) (by omega)
          (by omega)), ← hM7, memLoad32_store32_same, hlo, hhi]
        exact dbl64 lo hi
      · have e := hdone t (by omega)
        unfold u64At at e ⊢
        rw [← hM8, memLoad32_store32_sep (sep_offsets W (.inr (by omega)) (by omega) (by omega)),
          memLoad32_store32_sep (sep_offsets W (.inr (by omega)) (by omega) (by omega)), ← hM7,
          memLoad32_store32_sep (sep_offsets W (.inr (by omega)) (by omega) (by omega)),
          memLoad32_store32_sep (sep_offsets W (.inr (by omega)) (by omega) (by omega))]
        exact e
    -- 0x5A `addi s0, s0, 8`, 0x5C `addi a0, a0, -8`, 0x5E `bnez a0`
    obtain ⟨n9, d9, u9⟩ := u8.aluImm hc8 edd_at_5a (off' := 0x5C) (by decide)
    have k9 := u9.oldReg u8.zero
    obtain ⟨n10, d10, u10⟩ := u9.self.aluImm hc8 edd_at_5c (off' := 0x5E) (by decide)
    have k10 := u10.oldReg u9.self.zero
    have a0_10 : reg n10 a0 = BitVec.ofNat 32 (8 * r) := by
      rw [u10.newReg (by decide)]; show reg n9 a0 + 0xFFFFFFF8 = _
      rw [k9 _ (by decide), k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide),
        k2 _ (by decide), k1 _ (by decide), ha0]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFF8 : Word).toNat = 2 ^ 32 - 8 from rfl]
      omega
    have s0_10 : reg n10 (8 : Fin 32) = W + BitVec.ofNat 32 (8 * (j + 1)) := by
      rw [k10 _ (by decide), u9.newReg (by decide)]; show reg n6 (8 : Fin 32) + 0x8 = _
      rw [s0_6, show (0x8 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_assoc, show 8 * j + 8 = 8 * (j + 1) by omega]
    have keep10 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ (8 : Fin 32) → reg n10 q = reg n q :=
      fun q h0 h1 h2 h3 h8 => by
        rw [k10 q h0, k9 q h8, k6 q h2, k5 q h1, k4 q h2, k3 q h3, k2 q h2, k1 q h1]
    by_cases hr : r = 0
    · subst hr
      obtain ⟨n11, d11, u11⟩ := u10.self.notTaken hc8 0x60 edd_at_5e (by decide) (by
        simp only [branchTaken, a0_10, u10.self.zero]; decide)
      refine ⟨n11, M8, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
        (.cons d10 (.single d11)))))))))), u11.self, fun t ht => hdone8 t (by omega),
        fun x hx => hrest8 x (by rwa [show 8 * (j + 1) = 80 by omega]),
        fun q h0 h1 h2 h3 h8 => by rw [u11.regs, keep10 q h0 h1 h2 h3 h8]⟩
    · obtain ⟨n11, d11, u11⟩ := u10.self.taken hc8 0x48 edd_at_5e (by decide) (by
        simp only [branchTaken, a0_10, u10.self.zero]
        exact bne_toNat (by rw [BitVec.toNat_ofNat, zero_toNat]; omega))
      obtain ⟨n', M', c', u', dn', fr', kk⟩ := ih (j + 1) n11 M8 (by omega) (by omega) u11.self
        (by rw [u11.regs, a0_10]) (by rw [u11.regs, s0_10]) hdone8 hrest8
      exact ⟨n', M', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
        (.cons d10 (.cons d11 c')))))))))), u', dn', fr',
        fun q h0 h1 h2 h3 h8 => by rw [kk q h0 h1 h2 h3 h8, u11.regs, keep10 q h0 h1 h2 h3 h8]⟩

/-- Where `double` runs: its code at an even `P` and its callees' where its
calls reach them, 0x210 bytes of stack at `G` (its 0x160-byte frame and the
0xB0 bytes below it that its callees use), the result's 160 bytes at `out`,
and the operand's 120 at `sf`. The stack is apart from the code, the result,
and the operand, and the result from the code. -/
structure EdDblEnv (M : Word → BitVec 8) (P G out sf : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P edDoubleCode
  sq : CodeIn M (P + 0xFFFFE164) feSquareCode
  sqi : CodeIn M (P + 0xFFFFE18A) feSquareInnerCode
  red : CodeIn M (P + 0xFFFFDDF0) feReduceCode
  add : CodeIn M (P + 0xFFFFE674) feAddCode
  sub : CodeIn M (P + 0xFFFFE6C2) feSubCode
  mcS : CodeIn M (P + 0x43FC) memcpyStubCode
  mcB : CodeIn M (P + 0x4404) memcpyBodyCode
  hG : G.toNat % 4 = 0
  hGt : G.toNat + 0x210 ≤ 2 ^ 32
  hout : out.toNat % 4 = 0
  hot : out.toNat + 160 < 2 ^ 32
  hsf : sf.toNat % 4 = 0
  hst : sf.toNat + 120 < 2 ^ 32
  sGC : Sep G 0x210 P edDoubleCode.length
  sGQ : Sep G 0x210 (P + 0xFFFFE164) feSquareCode.length
  sGI : Sep G 0x210 (P + 0xFFFFE18A) feSquareInnerCode.length
  sGR : Sep G 0x210 (P + 0xFFFFDDF0) feReduceCode.length
  sGA : Sep G 0x210 (P + 0xFFFFE674) feAddCode.length
  sGS : Sep G 0x210 (P + 0xFFFFE6C2) feSubCode.length
  sGM : Sep G 0x210 (P + 0x43FC) memcpyStubCode.length
  sGB : Sep G 0x210 (P + 0x4404) memcpyBodyCode.length
  sOC : Sep out 160 P edDoubleCode.length
  sOQ : Sep out 160 (P + 0xFFFFE164) feSquareCode.length
  sOI : Sep out 160 (P + 0xFFFFE18A) feSquareInnerCode.length
  sOR : Sep out 160 (P + 0xFFFFDDF0) feReduceCode.length
  sOA : Sep out 160 (P + 0xFFFFE674) feAddCode.length
  sOS : Sep out 160 (P + 0xFFFFE6C2) feSubCode.length
  sOM : Sep out 160 (P + 0x43FC) memcpyStubCode.length
  sOB : Sep out 160 (P + 0x4404) memcpyBodyCode.length
  sOG : Sep out 160 G 0x210
  sFG : Sep sf 120 G 0x210

theorem edd_code {M M0 : Word → BitVec 8} {G out b : Word} {code : List Nat} (hc : CodeIn M0 b code)
    (hG : Sep G 0x210 b code.length) (hO : Sep out 160 b code.length)
    (fr : ∀ y, Sep G 0x210 y 1 → Sep out 160 y 1 → M y = M0 y) : CodeIn M b code :=
  fun i hi => by
    rw [fr _ (hG.subR (c := i) (l := 1) (by omega)) (hO.subR (c := i) (l := 1) (by omega))]; exact hc i hi

theorem edd_g (G a b : Word) (d : Nat) (h : a + b = BitVec.ofNat 32 d) : G + a + b = G + BitVec.ofNat 32 d := by
  rw [BitVec.add_assoc, h]

theorem edd_gw {G : Word} (hGt : G.toNat + 0x210 ≤ 2 ^ 32) {c : Nat} (hc : c < 0x210) :
    (G + BitVec.ofNat 32 c).toNat = G.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]

theorem edd_sepG {G : Word} {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c) (h1 : c + n ≤ 0x210) (h2 : d + k ≤ 0x210) :
    Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
  sep_offsets G h (by omega) (by omega)

theorem edd_sepG0 {G : Word} {c n k : Nat} (h : k ≤ c) (h1 : c + n ≤ 0x210) :
    Sep (G + BitVec.ofNat 32 c) n G k := by
  have := edd_sepG (G := G) (c := c) (n := n) (d := 0) (k := k) (.inr (by omega)) h1 (by omega)
  rwa [add_ofNat_zero] at this

theorem edd_low (G : Word) : G + 0xB0 + 0xFFFFFF50 = G := by rw [BitVec.add_assoc]; exact BitVec.add_zero G

/-- `square`'s environment, for a call from `double`. -/
theorem edd_sqEnv {M M0 : Word → BitVec 8} {P G out sf o x : Word} (env : EdDblEnv M0 P G out sf)
    (fr : ∀ y, Sep G 0x210 y 1 → Sep out 160 y 1 → M y = M0 y) (ho : o.toNat % 4 = 0) (hx : x.toNat % 4 = 0)
    (sOQ : Sep o 40 (P + 0xFFFFE164) feSquareCode.length) (sOR : Sep o 40 (P + 0xFFFFDDF0) feReduceCode.length)
    (sOG : Sep o 40 G 0xB0) (sXG : Sep x 40 G 0xB0) : FeSquareEnv M (P + 0xFFFFE164) (G + 0xB0) o x := by
  have hGt := env.hGt
  have e1 : P + 0xFFFFE164 + 0x26 = P + 0xFFFFE18A := by rw [BitVec.add_assoc]; rfl
  have e2 : P + 0xFFFFE164 + 0xFFFFFC8C = P + 0xFFFFDDF0 := by rw [BitVec.add_assoc]; rfl
  have g := edd_gw (G := G) hGt (c := 0xB0) (by decide)
  refine ⟨even_at P env.hP 0xFFFFE164 (by decide), edd_code env.sq env.sGQ env.sOQ fr, ?_, ?_,
    aligned_add env.hG (k := 0xB0) (by decide), by rw [show (G + 0xB0 : Word) = G + BitVec.ofNat 32 0xB0 from rfl, g]; omega,
    ho, hx, ?_, ?_, ?_, sOQ, by rw [e2]; exact sOR, by rw [edd_low]; exact sOG, by rw [edd_low]; exact sXG⟩
  · rw [e1]; exact edd_code env.sqi env.sGI env.sOI fr
  · rw [e2]; exact edd_code env.red env.sGR env.sOR fr
  · rw [edd_low]; exact sep_pre env.sGQ (by decide)
  · rw [edd_low, e1]; exact sep_pre env.sGI (by decide)
  · rw [edd_low, e2]; exact sep_pre env.sGR (by decide)

/-- `add`'s environment, for a call from `double`, with its stack at `G + 0x60`. -/
theorem edd_addEnv {M M0 : Word → BitVec 8} {P G out sf o x y : Word} (env : EdDblEnv M0 P G out sf)
    (fr : ∀ y, Sep G 0x210 y 1 → Sep out 160 y 1 → M y = M0 y) (ho : o.toNat + 40 < 2 ^ 32)
    (hx : x.toNat + 40 < 2 ^ 32) (hy : y.toNat % 4 = 0)
    (sOA : Sep o 40 (P + 0xFFFFE674) feAddCode.length) (sOB : Sep o 40 (P + 0x4404) memcpyBodyCode.length)
    (sOG : Sep o 40 (G + BitVec.ofNat 32 0x60) 0x50) (sXG : Sep x 40 (G + BitVec.ofNat 32 0x60) 0x50)
    (sYG : Sep y 40 (G + BitVec.ofNat 32 0x60) 0x50) :
    FeAddEnv M (P + 0xFFFFE674) (G + BitVec.ofNat 32 0x60) o x y := by
  have hGt := env.hGt
  have e1 : P + 0xFFFFE674 + 0x5D88 = P + 0x43FC := by rw [BitVec.add_assoc]; rfl
  have e2 : P + 0xFFFFE674 + 0x5D90 = P + 0x4404 := by rw [BitVec.add_assoc]; rfl
  have g := edd_gw (G := G) hGt (c := 0x60) (by decide)
  refine ⟨even_at P env.hP 0xFFFFE674 (by decide), edd_code env.add env.sGA env.sOA fr, ?_, ?_,
    aligned_add env.hG (k := 0x60) (by decide), by rw [g]; omega, hy, ho, hx, env.sGA.sub (by decide), ?_, ?_, sOA,
    by rw [e2]; exact sOB, sOG, sXG, sYG⟩
  · rw [e1]; exact edd_code env.mcS env.sGM env.sOM fr
  · rw [e2]; exact edd_code env.mcB env.sGB env.sOB fr
  · rw [e1]; exact env.sGM.sub (by decide)
  · rw [e2]; exact env.sGB.sub (by decide)

/-- `sub`'s environment, for a call from `double`, with its stack at `G`. -/
theorem edd_subEnv {M M0 : Word → BitVec 8} {P G out sf o x y : Word} (env : EdDblEnv M0 P G out sf)
    (fr : ∀ y, Sep G 0x210 y 1 → Sep out 160 y 1 → M y = M0 y) (ho : o.toNat % 4 = 0)
    (hx : x.toNat % 4 = 0) (hy : y.toNat % 4 = 0) (sOS : Sep o 40 (P + 0xFFFFE6C2) feSubCode.length)
    (sOG : Sep o 40 G 0xB0) (sXG : Sep x 40 G 0xB0) (sYG : Sep y 40 G 0xB0) :
    FeSubEnv M (P + 0xFFFFE6C2) G o x y := by
  have hGt := env.hGt
  have e1 : P + 0xFFFFE6C2 + 0xFFFFF72E = P + 0xFFFFDDF0 := by rw [BitVec.add_assoc]; rfl
  refine ⟨even_at P env.hP 0xFFFFE6C2 (by decide), edd_code env.sub env.sGS env.sOS fr, ?_, env.hG,
    by omega, hx, hy, ho, sep_pre env.sGS (by decide), ?_, sOS, sOG, sXG, sYG⟩
  · rw [e1]; exact edd_code env.red env.sGR env.sOR fr
  · rw [e1]; exact sep_pre env.sGR (by decide)

/-- The registers `double` leaves alone, other than the saved ones. -/
def edKeep (q : Fin 32) : Bool :=
  q.val ∉ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 28, 29, 30, 31]

theorem edk_ne {q r : Fin 32} (hq : edKeep q = true) (hr : edKeep r = false) : q ≠ r := fun e => by
  subst e; rw [hr] at hq; exact Bool.noConfusion hq

/-- The registers `double` keeps track of between its calls: `sp`, `s1`
(the operand), `s2` (the result), `s3`, and the rest as they were at entry. -/
def EdRF (f r0 : Fin 32 → Word) (G sf out s3 : Word) : Prop :=
  f sp = G + 0xB0 ∧ f 9 = sf ∧ f 18 = out ∧ f 19 = s3 ∧ ∀ q, edKeep q = true → f q = r0 q

theorem EdRF.block {f r0 : Fin 32 → Word} {G sf out s3 : Word} (h : EdRF f r0 G sf out s3) (hz : f 0 = 0)
    (is : List BInstr) (M : Word → BitVec 8)
    (hd : ∀ r ∈ is.filterMap BInstr.dst, r.val ∉ [2, 9, 18, 19] ∧ edKeep r = false) :
    EdRF (runBlock is (M, f)).2 r0 G sf out s3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [runBlock_reg is M f _ hz (fun hm => (hd _ hm).1 (by decide)), h1]
  · rw [runBlock_reg is M f _ hz (fun hm => (hd _ hm).1 (by decide)), h2]
  · rw [runBlock_reg is M f _ hz (fun hm => (hd _ hm).1 (by decide)), h3]
  · rw [runBlock_reg is M f _ hz (fun hm => (hd _ hm).1 (by decide)), h4]
  · rw [runBlock_reg is M f _ hz (fun hm => by have := (hd _ hm).2; rw [hq] at this; exact Bool.noConfusion this),
      h5 q hq]

theorem EdRF.call {f r0 : Fin 32 → Word} {G sf out s3 L : Word} {m1 m2 : Machine} {K : Fin 32 → Bool}
    (h : EdRF f r0 G sf out s3) (hz : f 0 = 0) (regs : ∀ r, reg m1 r = upd f ra L r)
    (kk : ∀ q, K q = true → reg m2 q = reg m1 q) (hK : ∀ q, edKeep q = true → K q = true)
    (h9 : K 9 = true) (h18 : K 18 = true) (h19 : K 19 = true) (hsp : reg m2 sp = G + 0xB0) :
    EdRF (reg m2) r0 G sf out s3 := by
  have r1 := PEnv.reg1 regs hz
  obtain ⟨_, e2, e3, e4, e5⟩ := h
  refine ⟨hsp, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [kk _ h9, r1 _ (by decide), e2]
  · rw [kk _ h18, r1 _ (by decide), e3]
  · rw [kk _ h19, r1 _ (by decide), e4]
  · rw [kk _ (hK q hq), r1 _ (fun e => by subst e; exact absurd hq (by decide)), e5 q hq]

theorem EdRF.mono {f g r0 : Fin 32 → Word} {G sf out s3 : Word} (h : EdRF f r0 G sf out s3)
    (hk : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ (8 : Fin 32) → g q = f q) : EdRF g r0 G sf out s3 := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide), e1]
  · rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide), e2]
  · rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide), e3]
  · rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide), e4]
  · rw [hk q (edk_ne hq (by decide)) (edk_ne hq (by decide)) (edk_ne hq (by decide)) (edk_ne hq (by decide))
      (edk_ne hq (by decide)), e5 q hq]

theorem EdRF.mc {f r0 : Fin 32 → Word} {G sf out s3 L : Word} {m1 m2 : Machine}
    (h : EdRF f r0 G sf out s3) (hz : f 0 = 0) (regs : ∀ r, reg m1 r = upd f ra L r) (sp2 : reg m2 sp = reg m1 sp)
    (K : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp → reg m2 r = reg m1 r) :
    EdRF (reg m2) r0 G sf out s3 := by
  have r1 := PEnv.reg1 regs hz
  have kk : ∀ q, edKeep q = true ∨ q.val ∈ [9, 18, 19] → reg m2 q = reg m1 q := fun q hq => by
    have hm : feMKeep q = true ∧ q ≠ sp := by
      rcases hq with hq | hq
      · exact ⟨(by revert hq; revert q; decide : ∀ q, edKeep q = true → feMKeep q = true) q hq,
          edk_ne hq (by decide)⟩
      · exact (by revert hq; revert q; decide : ∀ q : Fin 32, q.val ∈ [9, 18, 19] → feMKeep q = true ∧ q ≠ sp) q hq
    obtain ⟨hk, hs⟩ := hm
    exact K q (fun e => by subst e; exact absurd hk (by decide)) (fun e => by subst e; exact absurd hk (by decide))
      (fun e => by subst e; exact absurd hk (by decide)) (fun e => by subst e; exact absurd hk (by decide))
      (fun e => by subst e; exact absurd hk (by decide)) (fun e => by subst e; exact absurd hk (by decide))
      (fun e => by subst e; exact absurd hk (by decide)) (fun e => by subst e; exact absurd hk (by decide))
      (fun e => by subst e; exact absurd hk (by decide)) (fun e => by subst e; exact absurd hk (by decide))
      (fun e => by subst e; exact absurd hk (by decide)) (fun e => by subst e; exact absurd hk (by decide))
      (fun e => by subst e; exact absurd hk (by decide)) hs
  obtain ⟨e1, e2, e3, e4, e5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [sp2, r1 _ (by decide), e1]
  · rw [kk _ (.inr (by decide)), r1 _ (by decide), e2]
  · rw [kk _ (.inr (by decide)), r1 _ (by decide), e3]
  · rw [kk _ (.inr (by decide)), r1 _ (by decide), e4]
  · rw [kk _ (.inl hq), r1 _ (edk_ne hq (by decide)), e5 q hq]

theorem feM_ed : ∀ q, feMKeep q = true → q = ra ∨ q = sp ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨
    q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ edKeep q = true := by decide

theorem edKeep_feM : ∀ q, edKeep q = true → feMKeep q = true := by decide
theorem edKeep_sq : ∀ q, edKeep q = true → feSquareKeep q = true := by decide
theorem edKeep_sqi : ∀ q, edKeep q = true → fsqKeep q = true := by decide
theorem edKeep_fr : ∀ q, edKeep q = true → frKeep q = true := by decide

def eSeg1 : List BInstr := [.alu .add (9 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0x8]
def eSeg2 : List BInstr := [.aluImm .add (19 : Fin 32) (9 : Fin 32) 0x28, .aluImm .add a0 sp 0x30, .alu .add a1 x0 (19 : Fin 32)]
def eSeg3 : List BInstr := [.aluImm .add a1 (9 : Fin 32) 0x50, .aluImm .add a0 sp 0xF8, .aluImm .add (8 : Fin 32) sp 0xF8]
def eSeg4 : List BInstr := [.aluImm .add a0 sp 0x58, .aluImm .add a1 sp 0xF8]
def eSeg5 : List BInstr := [.aluImm .add a0 sp 0x80, .alu .add a1 x0 (9 : Fin 32), .alu .add a2 x0 (19 : Fin 32)]
def eSeg6 : List BInstr := [.aluImm .add a0 sp 0xA8, .aluImm .add a1 sp 0x80]
def eSeg7 : List BInstr := [.aluImm .add a0 sp 0xD0, .aluImm .add a1 sp 0x30, .aluImm .add a2 sp 0x8]
def eSeg8 : List BInstr := [.aluImm .add a0 sp 0xF8, .aluImm .add a1 sp 0x30, .aluImm .add a2 sp 0x8]
def eSeg9 : List BInstr := [.aluImm .add a1 sp 0xA8, .aluImm .add a2 sp 0xD0, .alu .add a0 x0 (18 : Fin 32)]
def eSeg10 : List BInstr := [.aluImm .add a0 (18 : Fin 32) 0x78, .aluImm .add a1 sp 0x58, .aluImm .add a2 sp 0xF8]
def eSeg11 : List BInstr := [.aluImm .add a0 (18 : Fin 32) 0x28, .aluImm .add a1 sp 0xD0, .aluImm .add a2 x0 0x28]
def eSeg12 : List BInstr := [.aluImm .add a0 (18 : Fin 32) 0x50, .aluImm .add a1 sp 0xF8, .aluImm .add a2 x0 0x28]

section
set_option maxRecDepth 20000
theorem eSeg1_end : blockEnd edDoubleCode 0x14 eSeg1 = some 0x1A := by decide
theorem eSeg2_end : blockEnd edDoubleCode 0x22 eSeg2 = some 0x2A := by decide
theorem eSeg3_end : blockEnd edDoubleCode 0x32 eSeg3 = some 0x3A := by decide
theorem eSeg4_end : blockEnd edDoubleCode 0x60 eSeg4 = some 0x64 := by decide
theorem eSeg5_end : blockEnd edDoubleCode 0x6C eSeg5 = some 0x72 := by decide
theorem eSeg6_end : blockEnd edDoubleCode 0x7A eSeg6 = some 0x7E := by decide
theorem eSeg7_end : blockEnd edDoubleCode 0x86 eSeg7 = some 0x8C := by decide
theorem eSeg8_end : blockEnd edDoubleCode 0x94 eSeg8 = some 0x9A := by decide
theorem eSeg9_end : blockEnd edDoubleCode 0xA2 eSeg9 = some 0xA8 := by decide
theorem eSeg10_end : blockEnd edDoubleCode 0xB0 eSeg10 = some 0xB8 := by decide
theorem eSeg11_end : blockEnd edDoubleCode 0xC0 eSeg11 = some 0xCA := by decide
theorem eSeg12_end : blockEnd edDoubleCode 0xD2 eSeg12 = some 0xDC := by decide
theorem eSeg3_d : ∀ r ∈ eSeg3.filterMap BInstr.dst, r.val ∉ [2, 9, 18, 19] ∧ edKeep r = false := by decide
theorem eSeg4_d : ∀ r ∈ eSeg4.filterMap BInstr.dst, r.val ∉ [2, 9, 18, 19] ∧ edKeep r = false := by decide
theorem eSeg5_d : ∀ r ∈ eSeg5.filterMap BInstr.dst, r.val ∉ [2, 9, 18, 19] ∧ edKeep r = false := by decide
theorem eSeg6_d : ∀ r ∈ eSeg6.filterMap BInstr.dst, r.val ∉ [2, 9, 18, 19] ∧ edKeep r = false := by decide
theorem eSeg7_d : ∀ r ∈ eSeg7.filterMap BInstr.dst, r.val ∉ [2, 9, 18, 19] ∧ edKeep r = false := by decide
theorem eSeg8_d : ∀ r ∈ eSeg8.filterMap BInstr.dst, r.val ∉ [2, 9, 18, 19] ∧ edKeep r = false := by decide
theorem eSeg9_d : ∀ r ∈ eSeg9.filterMap BInstr.dst, r.val ∉ [2, 9, 18, 19] ∧ edKeep r = false := by decide
theorem eSeg10_d : ∀ r ∈ eSeg10.filterMap BInstr.dst, r.val ∉ [2, 9, 18, 19] ∧ edKeep r = false := by decide
theorem eSeg11_d : ∀ r ∈ eSeg11.filterMap BInstr.dst, r.val ∉ [2, 9, 18, 19] ∧ edKeep r = false := by decide
theorem eSeg12_d : ∀ r ∈ eSeg12.filterMap BInstr.dst, r.val ∉ [2, 9, 18, 19] ∧ edKeep r = false := by decide
end

theorem edKeep_notin {L : List (Fin 32)} (hL : ∀ r ∈ L, edKeep r = false) {q : Fin 32} (hq : edKeep q = true) :
    q ∉ L := fun h => by rw [hL q h] at hq; exact Bool.noConfusion hq

theorem sepR0 {a G : Word} {n k k' : Nat} (h : Sep a n G k) (hk : k' ≤ k) : Sep a n G k' := by
  have := h.subR (c := 0) (l := k') (by omega); rwa [add_ofNat_zero] at this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
/-- **The compiled `ProjectivePoint::double`** of `curve25519_dalek`, called
with the result at `out` and the point's `X`, `Y`, and `Z` at `sf`,
`sf + 0x28`, and `sf + 0x50`: it stores `edDoubleSpec` of the three
coordinates' limbs as the result's `X`, `Y`, `Z`, and `T`. It returns with
`sp` and every register but `t0` through `t6` and `a0` through `a7` as they
were, and changes no memory outside its 0x210 bytes of stack and the result. -/
theorem edDouble_correct (m : Machine) {P G out sf retAddr : Word} (env : EdDblEnv m.mem P G out sf)
    (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = sf) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = G + 0x210) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + 0x210 ∧ (∀ q, feMKeep q = true → reg m' q = reg m q) ∧
      feW m'.mem out = (edDoubleSpec (feW m.mem sf) (feW m.mem (sf + 0x28)) (feW m.mem (sf + 0x50))).1 ∧
      feW m'.mem (out + 0x28) = (edDoubleSpec (feW m.mem sf) (feW m.mem (sf + 0x28)) (feW m.mem (sf + 0x50))).2.1 ∧
      feW m'.mem (out + 0x50) = (edDoubleSpec (feW m.mem sf) (feW m.mem (sf + 0x28)) (feW m.mem (sf + 0x50))).2.2.1 ∧
      feW m'.mem (out + 0x78) = (edDoubleSpec (feW m.mem sf) (feW m.mem (sf + 0x28)) (feW m.mem (sf + 0x50))).2.2.2 ∧
      ∀ x, Sep G 0x210 x 1 → Sep out 160 x 1 → m'.mem x = m.mem x := by
  have hGt := env.hGt
  have hGa := env.hG
  have hc0 := env.code
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have alG : ∀ c, c % 4 = 0 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c hc => aligned_add hGa hc
  have gA : ∀ (c : Nat) (o : Word) (d : Nat), BitVec.ofNat 32 c + o = BitVec.ofNat 32 d →
      G + BitVec.ofNat 32 c + o = G + BitVec.ofNat 32 d := fun c o d h => edd_g G _ _ d h
  have gB : ∀ (o : Word) (d : Nat), (0xB0 : Word) + o = BitVec.ofNat 32 d → G + 0xB0 + o = G + BitVec.ofNat 32 d :=
    fun o d h => edd_g G _ _ d h
  have sepS : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x210 → d + k ≤ 0x210 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 => edd_sepG h h1 h2
  have sep0 : ∀ {n d k : Nat}, n ≤ d → d + k ≤ 0x210 → Sep G n (G + BitVec.ofNat 32 d) k := fun {n d k} h1 h2 => by
    have := edd_sepG (G := G) (c := 0) (n := n) (d := d) (k := k) (.inl (by omega)) (by omega) h2
    rwa [add_ofNat_zero] at this
  have inG : ∀ {c l : Nat}, c + l ≤ 0x210 → ∀ y, Sep G 0x210 y 1 → Sep (G + BitVec.ofNat 32 c) l y 1 :=
    fun h y hy => hy.sub h
  have inG0 : ∀ {l : Nat}, l ≤ 0x210 → ∀ y, Sep G 0x210 y 1 → Sep G l y 1 := fun h y hy => sep_pre hy h
  have sfw : ∀ {c : Nat}, c + 40 ≤ 120 → Sep (sf + BitVec.ofNat 32 c) 40 G 0x210 := fun h => env.sFG.sub h
  -- the prologue: the frame, and `ra` and `s0` through `s3` saved at its top
  obtain ⟨m1, d1, u1⟩ := s0.aluImm hc0 edd_at_0 (off' := 2) (by decide)
  have k1 := u1.oldReg hz
  have sp1 : reg m1 sp = G + 0xB0 := by
    rw [u1.newReg (by decide)]; show reg m sp + 0xFFFFFEA0 = _; rw [hsp, BitVec.add_assoc]; rfl
  obtain ⟨m2, d2, u2⟩ := u1.self.aluImm hc0 edd_at_2 (off' := 4) (by decide)
  have k2 := u2.oldReg u1.self.zero
  have a2_2 : reg m2 a2 = G + BitVec.ofNat 32 0x1B0 := by
    rw [u2.newReg (by decide)]; show reg m1 sp + 0x100 = _; rw [sp1]; exact gB _ _ rfl
  have r2 : ∀ q, q ≠ a2 → q ≠ sp → reg m2 q = reg m q := fun q h1 h2 => by rw [k2 q h1, k1 q h2]
  have sGC4 : ∀ c, c + 4 ≤ 0x210 → Sep (G + BitVec.ofNat 32 c) 4 P edDoubleCode.length :=
    fun c h => env.sGC.sub (c := c) (l := 4) h
  obtain ⟨p0, dp0, up0⟩ := u2.self.swG hc0 edd_at_4 (off' := 8) (by decide)
    (by rw [a2_2, gA 0x1B0 0x5C 0x20C rfl]; exact alG _ (by decide)) (a := G + BitVec.ofNat 32 0x20C)
    (v := reg m ra) (by rw [a2_2]; exact gA _ _ _ rfl) (r2 _ (by decide) (by decide))
  obtain ⟨Q0, hQ0⟩ : ∃ M, memStore32 m.mem (G + BitVec.ofNat 32 0x20C) (reg m ra) = M := ⟨_, rfl⟩
  rw [hQ0] at up0
  have hq0 : CodeIn Q0 P edDoubleCode := by rw [← hQ0]; exact hc0.store32 (sGC4 _ (by decide))
  obtain ⟨p1, dp1, up1⟩ := up0.swG hq0 edd_at_8 (off' := 0xA) (by decide)
    (by rw [a2_2, gA 0x1B0 0x58 0x208 rfl]; exact alG _ (by decide)) (a := G + BitVec.ofNat 32 0x208)
    (v := reg m (8 : Fin 32)) (by rw [a2_2]; exact gA _ _ _ rfl) (r2 _ (by decide) (by decide))
  obtain ⟨Q1, hQ1⟩ : ∃ M, memStore32 Q0 (G + BitVec.ofNat 32 0x208) (reg m (8 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hQ1] at up1
  have hq1 : CodeIn Q1 P edDoubleCode := by rw [← hQ1]; exact hq0.store32 (sGC4 _ (by decide))
  obtain ⟨p2, dp2, up2⟩ := up1.swG hq1 edd_at_a (off' := 0xC) (by decide)
    (by rw [a2_2, gA 0x1B0 0x54 0x204 rfl]; exact alG _ (by decide)) (a := G + BitVec.ofNat 32 0x204)
    (v := reg m (9 : Fin 32)) (by rw [a2_2]; exact gA _ _ _ rfl) (r2 _ (by decide) (by decide))
  obtain ⟨Q2, hQ2⟩ : ∃ M, memStore32 Q1 (G + BitVec.ofNat 32 0x204) (reg m (9 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hQ2] at up2
  have hq2 : CodeIn Q2 P edDoubleCode := by rw [← hQ2]; exact hq1.store32 (sGC4 _ (by decide))
  obtain ⟨p3, dp3, up3⟩ := up2.swG hq2 edd_at_c (off' := 0x10) (by decide)
    (by rw [a2_2, gA 0x1B0 0x50 0x200 rfl]; exact alG _ (by decide)) (a := G + BitVec.ofNat 32 0x200)
    (v := reg m (18 : Fin 32)) (by rw [a2_2]; exact gA _ _ _ rfl) (r2 _ (by decide) (by decide))
  obtain ⟨Q3, hQ3⟩ : ∃ M, memStore32 Q2 (G + BitVec.ofNat 32 0x200) (reg m (18 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hQ3] at up3
  have hq3 : CodeIn Q3 P edDoubleCode := by rw [← hQ3]; exact hq2.store32 (sGC4 _ (by decide))
  obtain ⟨p4, dp4, up4⟩ := up3.swG hq3 edd_at_10 (off' := 0x14) (by decide)
    (by rw [a2_2, gA 0x1B0 0x4C 0x1FC rfl]; exact alG _ (by decide)) (a := G + BitVec.ofNat 32 0x1FC)
    (v := reg m (19 : Fin 32)) (by rw [a2_2]; exact gA _ _ _ rfl) (r2 _ (by decide) (by decide))
  obtain ⟨Q4, hQ4⟩ : ∃ M, memStore32 Q3 (G + BitVec.ofNat 32 0x1FC) (reg m (19 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hQ4] at up4
  have fpro : ∀ y, Sep (G + BitVec.ofNat 32 0x1FC) 20 y 1 → Q4 y = m.mem y := fun y hy => by
    rw [← hQ4, memStore32_get_sep (sep_pre hy (by decide)), ← hQ3,
      memStore32_get_sep (by have := hy.sub (c := 4) (l := 4) (by decide); rwa [add_ofNat_assoc] at this), ← hQ2,
      memStore32_get_sep (by have := hy.sub (c := 8) (l := 4) (by decide); rwa [add_ofNat_assoc] at this), ← hQ1,
      memStore32_get_sep (by have := hy.sub (c := 12) (l := 4) (by decide); rwa [add_ofNat_assoc] at this), ← hQ0,
      memStore32_get_sep (by have := hy.sub (c := 16) (l := 4) (by decide); rwa [add_ofNat_assoc] at this)]
  have fr4 : ∀ y, Sep G 0x210 y 1 → Q4 y = m.mem y := fun y hy => fpro y (inG (by decide) y hy)
  have frO4 : ∀ y, Sep G 0x210 y 1 → Sep out 160 y 1 → Q4 y = m.mem y := fun y hy _ => fr4 y hy
  have hq4 : CodeIn Q4 P edDoubleCode := edd_code env.code env.sGC env.sOC frO4
  have sfX : ∀ {M : Word → BitVec 8} {a : Word}, Sep a 40 G 0x210 → (∀ y, Sep G 0x210 y 1 → M y = m.mem y) →
      feW M a = feW m.mem a := fun h hM =>
    feW_frame fun i hi => load_frame hM (h.symm.subR (c := 4 * i) (l := 4) (by omega))
  have sfS0 : Sep sf 40 G 0x210 := sep_pre env.sFG (by decide)
  have sfS1 : Sep (sf + 0x28) 40 G 0x210 := env.sFG.sub (c := 0x28) (l := 40) (by decide)
  have sfS2 : Sep (sf + 0x50) 40 G 0x210 := env.sFG.sub (c := 0x50) (l := 40) (by decide)
  -- 0x14..0x1A: `mv s1, a1`, `mv s2, a0`, `addi a0, sp, 8`, and `square` into `XX` at `G + 0xB8`
  obtain ⟨b1, cb1, ub1⟩ := St.block eSeg1 up4 hq4 eSeg1_end (by simp [BlockOk, BInstr.ok, eSeg1])
  have z2 : reg m2 0 = 0 := u2.self.zero
  have RF1 : EdRF (runBlock eSeg1 (Q4, reg m2)).2 (reg m) G sf out (reg m (19 : Fin 32)) := by
    refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
    · simp +decide only [runBlock, BInstr.run, eSeg1, upd_app, ↓reduceIte]; rw [k2 _ (by decide), sp1]
    · simp +decide only [runBlock, BInstr.run, eSeg1, upd_app, ↓reduceIte]
      show reg m2 0 + reg m2 a1 = _; rw [z2, r2 _ (by decide) (by decide), ha1]; exact BitVec.zero_add _
    · simp +decide only [runBlock, BInstr.run, eSeg1, upd_app, ↓reduceIte]
      show reg m2 0 + reg m2 a0 = _; rw [z2, r2 _ (by decide) (by decide), ha0]; exact BitVec.zero_add _
    · simp +decide only [runBlock, BInstr.run, eSeg1, upd_app, ↓reduceIte]; rw [r2 _ (by decide) (by decide)]
    · rw [runBlock_reg eSeg1 Q4 (reg m2) q z2 (edKeep_notin (by decide) hq), r2 q (edk_ne hq (by decide))
        (edk_ne hq (by decide))]
  have ab1 : (runBlock eSeg1 (Q4, reg m2)).2 a0 = G + BitVec.ofNat 32 0xB8 := by
    simp +decide only [runBlock, BInstr.run, eSeg1, upd_app, ↓reduceIte]
    show reg m2 sp + 0x8 = _; rw [k2 _ (by decide), sp1]; exact gB _ _ rfl
  obtain ⟨c1m, cc1m, pc1m, mem1m, regs1m⟩ := ub1.callRa hq4 edd_at_1a edd_at_1e (cb := P + 0xFFFFE164)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE164 (by decide))
  have r1m := PEnv.reg1 regs1m ub1.zero
  rw [show (runBlock eSeg1 (Q4, reg m2)).1 = Q4 from rfl] at mem1m
  obtain ⟨c1, cc1, pc1, sp1c, kk1, out1, fr1⟩ := feSquare_correct c1m (retAddr := P + BitVec.ofNat 32 (0x1A + 8))
    (edd_sqEnv env (by rw [mem1m]; exact frO4) (o := G + BitVec.ofNat 32 0xB8) (x := sf) (alG _ (by decide)) env.hsf
      (env.sGQ.sub (by decide)) (env.sGR.sub (by decide)) (edd_sepG0 (by decide) (by decide)) (sepR0 sfS0 (by decide)))
    pc1m (by rw [r1m _ (by decide), ab1])
    (by rw [r1m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg1, upd_app, ↓reduceIte]
        rw [r2 _ (by decide) (by decide), ha1])
    (by rw [regs1m]; try simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x1A + 8) (by decide)))
    (by rw [r1m _ (by decide), RF1.1])
  rw [mem1m, edd_low] at fr1
  rw [mem1m] at out1
  have w1 : St c1.mem P c1 0x22 (reg c1) := ⟨by rw [pc1]; try rfl, rfl, fun _ => rfl⟩
  have RFc1 := EdRF.call RF1 ub1.zero regs1m kk1 edKeep_sq (by decide) (by decide) (by decide) sp1c
  have frS1 : ∀ y, Sep G 0x210 y 1 → c1.mem y = m.mem y := fun y hy => by
    rw [fr1 y (inG0 (by decide) y hy) (inG (by decide) y hy), fr4 y hy]
  have up1 : ∀ i, i < 20 → c1.mem (G + BitVec.ofNat 32 (0x1FC + i)) = Q4 (G + BitVec.ofNat 32 (0x1FC + i)) :=
    fun i hi => fr1 _ (sep0 (by omega) (by omega)) (sepS (.inl (by omega)) (by omega) (by omega))
  have hXX : feW c1.mem (G + BitVec.ofNat 32 0xB8) = sqL (feW m.mem sf) := by
    rw [← feW_words, out1]; show sqL (feW Q4 sf) = _; rw [sfX sfS0 fr4]
  -- 0x22..0x2A: `addi s3, s1, 0x28`, `addi a0, sp, 0x30`, `mv a1, s3`, and `square` into `YY` at `G + 0xE0`
  obtain ⟨b2, cb2, ub2⟩ := St.block eSeg2 w1 (edd_code env.code env.sGC env.sOC fun y hy _ => frS1 y hy) eSeg2_end
    (by simp [BlockOk, BInstr.ok, eSeg2])
  have hc1 : CodeIn c1.mem P edDoubleCode := edd_code env.code env.sGC env.sOC fun y hy _ => frS1 y hy
  have z1 : reg c1 0 = 0 := w1.zero
  have RF2 : EdRF (runBlock eSeg2 (c1.mem, reg c1)).2 (reg m) G sf out (sf + 0x28) := by
    obtain ⟨e1, e2, e3, _, e5⟩ := RFc1
    refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
    · simp +decide only [runBlock, BInstr.run, eSeg2, upd_app, ↓reduceIte]; exact e1
    · simp +decide only [runBlock, BInstr.run, eSeg2, upd_app, ↓reduceIte]; exact e2
    · simp +decide only [runBlock, BInstr.run, eSeg2, upd_app, ↓reduceIte]; exact e3
    · simp +decide only [runBlock, BInstr.run, eSeg2, upd_app, ↓reduceIte]; show reg c1 9 + 0x28 = _; rw [e2]
    · rw [runBlock_reg eSeg2 c1.mem (reg c1) q z1 (edKeep_notin (by decide) hq), e5 q hq]
  obtain ⟨c2m, cc2m, pc2m, mem2m, regs2m⟩ := ub2.callRa hc1 edd_at_2a edd_at_2e (cb := P + 0xFFFFE164)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE164 (by decide))
  have r2m := PEnv.reg1 regs2m ub2.zero
  rw [show (runBlock eSeg2 (c1.mem, reg c1)).1 = c1.mem from rfl] at mem2m
  obtain ⟨c2, cc2, pc2, sp2c, kk2, out2, fr2⟩ := feSquare_correct c2m (retAddr := P + BitVec.ofNat 32 (0x2A + 8))
    (edd_sqEnv env (by rw [mem2m]; exact fun y hy _ => frS1 y hy) (o := G + BitVec.ofNat 32 0xE0) (x := sf + 0x28)
      (alG _ (by decide)) (aligned_add env.hsf (k := 0x28) (by decide))
      (env.sGQ.sub (by decide)) (env.sGR.sub (by decide)) (edd_sepG0 (by decide) (by decide)) (sepR0 sfS1 (by decide)))
    pc2m
    (by rw [r2m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg2, upd_app, ↓reduceIte]
        show reg c1 sp + 0x30 = _; rw [RFc1.1]; exact gB _ _ rfl)
    (by rw [r2m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg2, upd_app, ↓reduceIte]
        show (0 : Word) + (reg c1 9 + 0x28) = _; rw [RFc1.2.1]; exact BitVec.zero_add _)
    (by rw [regs2m]; try simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x2A + 8) (by decide)))
    (by rw [r2m _ (by decide), RF2.1])
  rw [mem2m, edd_low] at fr2
  rw [mem2m] at out2
  have w2 : St c2.mem P c2 0x32 (reg c2) := ⟨by rw [pc2]; try rfl, rfl, fun _ => rfl⟩
  have RFc2 := EdRF.call RF2 ub2.zero regs2m kk2 edKeep_sq (by decide) (by decide) (by decide) sp2c
  have frS2 : ∀ y, Sep G 0x210 y 1 → c2.mem y = m.mem y := fun y hy => by
    rw [fr2 y (inG0 (by decide) y hy) (inG (by decide) y hy), frS1 y hy]
  have up2 : ∀ i, i < 20 → c2.mem (G + BitVec.ofNat 32 (0x1FC + i)) = Q4 (G + BitVec.ofNat 32 (0x1FC + i)) :=
    fun i hi => by rw [fr2 _ (sep0 (by omega) (by omega)) (sepS (.inl (by omega)) (by omega) (by omega)), up1 i hi]
  have hYY : feW c2.mem (G + BitVec.ofNat 32 0xE0) = sqL (feW m.mem (sf + 0x28)) := by
    rw [← feW_words, out2]; show sqL (feW c1.mem (sf + 0x28)) = _; rw [sfX sfS1 frS1]
  have hXX2 : feW c2.mem (G + BitVec.ofNat 32 0xB8) = sqL (feW m.mem sf) := by
    rw [feW_frame2 fr2 (sep0 (by decide) (by decide)) (sepS (.inr (by decide)) (by decide) (by decide)), hXX]
  -- 0x32..0x3A: `addi a1, s1, 0x50`, `addi a0, sp, 0xF8`, `addi s0, sp, 0xF8`, and `square_inner` at `G + 0x1A8`
  have hc2 : CodeIn c2.mem P edDoubleCode := edd_code env.code env.sGC env.sOC fun y hy _ => frS2 y hy
  obtain ⟨b3, cb3, ub3⟩ := St.block eSeg3 w2 hc2 eSeg3_end (by simp [BlockOk, BInstr.ok, eSeg3])
  have RF3 := RFc2.block w2.zero eSeg3 c2.mem eSeg3_d
  have f3 : ∀ q : Fin 32, q.val ∈ [8, 10] → (runBlock eSeg3 (c2.mem, reg c2)).2 q = G + BitVec.ofNat 32 0x1A8 := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with h | h
    · rw [show q = 8 from Fin.ext h]; simp +decide only [runBlock, BInstr.run, eSeg3, upd_app, ↓reduceIte]
      show reg c2 sp + 0xF8 = _; rw [RFc2.1]; exact gB _ _ rfl
    · rw [show q = a0 from Fin.ext h]; simp +decide only [runBlock, BInstr.run, eSeg3, upd_app, ↓reduceIte]
      show reg c2 sp + 0xF8 = _; rw [RFc2.1]; exact gB _ _ rfl
  obtain ⟨c3m, cc3m, pc3m, mem3m, regs3m⟩ := ub3.callRa hc2 edd_at_3a edd_at_3e (cb := P + 0xFFFFE18A)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE18A (by decide))
  have r3m := PEnv.reg1 regs3m ub3.zero
  rw [show (runBlock eSeg3 (c2.mem, reg c2)).1 = c2.mem from rfl] at mem3m
  have e60 : G + 0xB0 + 0xFFFFFFB0 = G + BitVec.ofNat 32 0x60 := gB _ _ rfl
  have SE3 : FeSqEnv c3m.mem (P + 0xFFFFE18A) (G + 0xB0) (G + BitVec.ofNat 32 0x1A8) (sf + 0x50) := by
    rw [mem3m]
    refine ⟨even_at P env.hP 0xFFFFE18A (by decide), edd_code env.sqi env.sGI env.sOI fun y hy _ => frS2 y hy,
      alG 0xB0 (by decide), ?_, alG _ (by decide), aligned_add env.hsf (k := 0x50) (by decide), ?_,
      env.sGI.sub (by decide), ?_, ?_, sfS2.subR (c := 0x1A8) (l := 0x50) (by decide)⟩
    · rw [show (G + 0xB0 : Word) = G + BitVec.ofNat 32 0xB0 from rfl, edd_gw hGt (by decide)]; omega
    · rw [e60]; exact env.sGI.sub (by decide)
    · rw [e60]; exact sepS (.inr (by decide)) (by decide) (by decide)
    · rw [e60]; exact sfS2.subR (c := 0x60) (l := 0x50) (by decide)
  obtain ⟨c3, cc3, pc3, sp3c, kk3, out3, fr3⟩ := feSqInner_correct c3m (retAddr := P + BitVec.ofNat 32 (0x3A + 8))
    SE3 pc3m (by rw [r3m _ (by decide), f3 _ (by decide)])
    (by rw [r3m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg3, upd_app, ↓reduceIte]
        show reg c2 9 + 0x50 = _; rw [RFc2.2.1])
    (by rw [regs3m]; try simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x3A + 8) (by decide)))
    (by rw [r3m _ (by decide), RF3.1])
  rw [mem3m, e60] at fr3
  rw [mem3m] at out3
  have w3 : St c3.mem P c3 0x42 (reg c3) := ⟨by rw [pc3]; try rfl, rfl, fun _ => rfl⟩
  have RFc3 := EdRF.call RF3 ub3.zero regs3m kk3 edKeep_sqi (by decide) (by decide) (by decide) sp3c
  have s0_3 : reg c3 (8 : Fin 32) = G + BitVec.ofNat 32 0x1A8 := by
    rw [kk3 _ (by decide), r3m _ (by decide), f3 _ (by decide)]
  have frS3 : ∀ y, Sep G 0x210 y 1 → c3.mem y = m.mem y := fun y hy => by
    rw [fr3 y (inG (by decide) y hy) (inG (by decide) y hy), frS2 y hy]
  have up3 : ∀ i, i < 20 → c3.mem (G + BitVec.ofNat 32 (0x1FC + i)) = Q4 (G + BitVec.ofNat 32 (0x1FC + i)) :=
    fun i hi => by
      rw [fr3 _ (sepS (.inl (by omega)) (by omega) (by omega)) (sepS (.inl (by omega)) (by omega) (by omega)), up2 i hi]
  have hXX3 : feW c3.mem (G + BitVec.ofNat 32 0xB8) = sqL (feW m.mem sf) := by
    rw [feW_frame2 fr3 (sepS (.inl (by decide)) (by decide) (by decide)) (sepS (.inr (by decide)) (by decide) (by decide)),
      hXX2]
  have hYY3 : feW c3.mem (G + BitVec.ofNat 32 0xE0) = sqL (feW m.mem (sf + 0x28)) := by
    rw [feW_frame2 fr3 (sepS (.inl (by decide)) (by decide) (by decide)) (sepS (.inr (by decide)) (by decide) (by decide)),
      hYY]
  -- 0x42 `li a0, 0x50`, 0x46 `beqz a0`, and the doubling loop
  have hc3 : CodeIn c3.mem P edDoubleCode := edd_code env.code env.sGC env.sOC fun y hy _ => frS3 y hy
  obtain ⟨n4, d4, u4⟩ := w3.aluImm hc3 edd_at_42 (off' := 0x46) (by decide)
  have k4 := u4.oldReg w3.zero
  have a0_4 : reg n4 a0 = BitVec.ofNat 32 (8 * 10) := by
    rw [u4.newReg (by decide)]; show reg c3 0 + 0x50 = _; rw [w3.zero]; rfl
  obtain ⟨n5, d5, u5⟩ := u4.self.notTaken hc3 0x48 edd_at_46 (by decide) (by
    simp only [branchTaken, a0_4, u4.self.zero]; decide)
  obtain ⟨nL, ML, cL, uL, dnL, frL, kL⟩ := edd_loop (Mb := c3.mem) (P := P) (W := G + BitVec.ofNat 32 0x1A8) hc3
    (alG _ (by decide)) (env.sGC.sub (by decide)) 10 0 n5 c3.mem (by decide)
    (by decide) u5.self (by rw [u5.regs, a0_4]) (by rw [u5.regs, k4 _ (by decide), s0_3]; exact (add_ofNat_zero _).symm)
    (fun t ht => absurd ht (Nat.not_lt_zero _)) (fun _ _ => rfl)
  have RFL : EdRF (reg nL) (reg m) G sf out (sf + 0x28) := RFc3.mono fun q h0 h1 h2 h3 h8 => by
    rw [kL q h0 h1 h2 h3 h8, u5.regs, k4 q h0]
  have frSL : ∀ y, Sep G 0x210 y 1 → ML y = m.mem y := fun y hy => by
    rw [frL y (inG (by decide) y hy), frS3 y hy]
  have hcL : CodeIn ML P edDoubleCode := edd_code env.code env.sGC env.sOC fun y hy _ => frSL y hy
  -- 0x60..0x64: `addi a0, sp, 0x58`, `addi a1, sp, 0xF8`, and `reduce` into `ZZ2` at `G + 0x108`
  obtain ⟨b4, cb4, ub4⟩ := St.block eSeg4 uL hcL eSeg4_end (by simp [BlockOk, BInstr.ok, eSeg4])
  have RF4 := RFL.block uL.zero eSeg4 ML eSeg4_d
  obtain ⟨c4m, cc4m, pc4m, mem4m, regs4m⟩ := ub4.callRa hcL edd_at_64 edd_at_68 (cb := P + 0xFFFFDDF0)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFDDF0 (by decide))
  have r4m := PEnv.reg1 regs4m ub4.zero
  rw [show (runBlock eSeg4 (ML, reg nL)).1 = ML from rfl] at mem4m
  have e90 : G + 0xB0 + 0xFFFFFFE0 = G + BitVec.ofNat 32 0x90 := gB _ _ rfl
  have RE4 : FREnv c4m.mem (P + 0xFFFFDDF0) (G + 0xB0) (G + BitVec.ofNat 32 0x108) (G + BitVec.ofNat 32 0x1A8) := by
    rw [mem4m]
    refine ⟨even_at P env.hP 0xFFFFDDF0 (by decide), edd_code env.red env.sGR env.sOR fun y hy _ => frSL y hy,
      alG 0xB0 (by decide), ?_, alG _ (by decide), alG _ (by decide), ?_, env.sGR.sub (by decide), ?_, ?_⟩
    · rw [show (G + 0xB0 : Word) = G + BitVec.ofNat 32 0xB0 from rfl, edd_gw hGt (by decide)]; omega
    · rw [e90]; exact env.sGR.sub (by decide)
    · rw [e90]; exact sepS (.inr (by decide)) (by decide) (by decide)
    · rw [e90]; exact sepS (.inr (by decide)) (by decide) (by decide)
  obtain ⟨c4, cc4, pc4, sp4c, kk4, out4, frc4⟩ := feReduce_correct c4m (retAddr := P + BitVec.ofNat 32 (0x64 + 8))
    RE4 pc4m
    (by rw [r4m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg4, upd_app, ↓reduceIte]
        show reg nL sp + 0x58 = _; rw [RFL.1]; exact gB _ _ rfl)
    (by rw [r4m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg4, upd_app, ↓reduceIte]
        show reg nL sp + 0xF8 = _; rw [RFL.1]; exact gB _ _ rfl)
    (by rw [regs4m]; try simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x64 + 8) (by decide)))
    (by rw [r4m _ (by decide), RF4.1])
  rw [mem4m, e90] at frc4
  rw [mem4m] at out4
  have w4 : St c4.mem P c4 0x6C (reg c4) := ⟨by rw [pc4]; try rfl, rfl, fun _ => rfl⟩
  have RFc4 := EdRF.call RF4 ub4.zero regs4m kk4 edKeep_fr (by decide) (by decide) (by decide) sp4c
  have frS4 : ∀ y, Sep G 0x210 y 1 → c4.mem y = m.mem y := fun y hy => by
    rw [frc4 y (inG (by decide) y hy) (inG (by decide) y hy), frSL y hy]
  have up4 : ∀ i, i < 20 → c4.mem (G + BitVec.ofNat 32 (0x1FC + i)) = Q4 (G + BitVec.ofNat 32 (0x1FC + i)) :=
    fun i hi => by
      rw [frc4 _ (sepS (.inl (by omega)) (by omega) (by omega)) (sepS (.inl (by omega)) (by omega) (by omega)),
        frL _ (sepS (.inl (by omega)) (by omega) (by omega)), up3 i hi]
  have hZZ : feW c4.mem (G + BitVec.ofNat 32 0x108) = sq2L (feW m.mem (sf + 0x50)) := by
    have e : sq2L (feW c2.mem (sf + 0x50)) = dblRed [u64At c3.mem (G + BitVec.ofNat 32 0x1A8) 0,
        u64At c3.mem (G + BitVec.ofNat 32 0x1A8) 1, u64At c3.mem (G + BitVec.ofNat 32 0x1A8) 2,
        u64At c3.mem (G + BitVec.ofNat 32 0x1A8) 3, u64At c3.mem (G + BitVec.ofNat 32 0x1A8) 4,
        u64At c3.mem (G + BitVec.ofNat 32 0x1A8) 5, u64At c3.mem (G + BitVec.ofNat 32 0x1A8) 6,
        u64At c3.mem (G + BitVec.ofNat 32 0x1A8) 7, u64At c3.mem (G + BitVec.ofNat 32 0x1A8) 8,
        u64At c3.mem (G + BitVec.ofNat 32 0x1A8) 9] := by rw [out3]; rfl
    rw [← feW_words, out4, dnL 0 (by decide), dnL 1 (by decide), dnL 2 (by decide), dnL 3 (by decide),
      dnL 4 (by decide), dnL 5 (by decide), dnL 6 (by decide), dnL 7 (by decide), dnL 8 (by decide),
      dnL 9 (by decide), ← sfX sfS2 frS2, e]
    rfl
  have hXX4 : feW c4.mem (G + BitVec.ofNat 32 0xB8) = sqL (feW m.mem sf) := by
    rw [feW_frame2 frc4 (sepS (.inl (by decide)) (by decide) (by decide)) (sepS (.inr (by decide)) (by decide) (by decide)),
      feW_frame fun i hi => load_frame frL ((sepS (.inr (by decide)) (by decide) (by decide) :
        Sep (G + BitVec.ofNat 32 0x1A8) 80 (G + BitVec.ofNat 32 0xB8) 40).subR (c := 4 * i) (l := 4) (by omega)), hXX3]
  have hYY4 : feW c4.mem (G + BitVec.ofNat 32 0xE0) = sqL (feW m.mem (sf + 0x28)) := by
    rw [feW_frame2 frc4 (sepS (.inl (by decide)) (by decide) (by decide)) (sepS (.inr (by decide)) (by decide) (by decide)),
      feW_frame fun i hi => load_frame frL ((sepS (.inr (by decide)) (by decide) (by decide) :
        Sep (G + BitVec.ofNat 32 0x1A8) 80 (G + BitVec.ofNat 32 0xE0) 40).subR (c := 4 * i) (l := 4) (by omega)), hYY3]
  have e60s : G + BitVec.ofNat 32 0x60 + 0x50 = G + 0xB0 := by rw [BitVec.add_assoc]; rfl
  -- 0x6C..0x72: `addi a0, sp, 0x80`, `mv a1, s1`, `mv a2, s3`, and `add` into `X + Y` at `G + 0x130`
  have hc4 : CodeIn c4.mem P edDoubleCode := edd_code env.code env.sGC env.sOC fun y hy _ => frS4 y hy
  obtain ⟨b5, cb5, ub5⟩ := St.block eSeg5 w4 hc4 eSeg5_end (by simp [BlockOk, BInstr.ok, eSeg5])
  have RF5 := RFc4.block w4.zero eSeg5 c4.mem eSeg5_d
  obtain ⟨c5m, cc5m, pc5m, mem5m, regs5m⟩ := ub5.callRa hc4 edd_at_72 edd_at_76 (cb := P + 0xFFFFE674)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE674 (by decide))
  have r5m := PEnv.reg1 regs5m ub5.zero
  rw [show (runBlock eSeg5 (c4.mem, reg c4)).1 = c4.mem from rfl] at mem5m
  obtain ⟨c5, cc5, pc5, sp5c, kk5, out5, fr5⟩ := feAdd_correct c5m (retAddr := P + BitVec.ofNat 32 (0x72 + 8))
    (edd_addEnv env (by rw [mem5m]; exact fun y hy _ => frS4 y hy) (o := G + BitVec.ofNat 32 0x130) (x := sf)
      (y := sf + 0x28) (by rw [edd_gw hGt (by decide)]; omega) (by have := env.hst; omega)
      (aligned_add env.hsf (k := 0x28) (by decide)) (env.sGA.sub (by decide)) (env.sGB.sub (by decide))
      (sepS (.inr (by decide)) (by decide) (by decide)) (sfS0.subR (c := 0x60) (l := 0x50) (by decide))
      (sfS1.subR (c := 0x60) (l := 0x50) (by decide)))
    pc5m
    (by rw [r5m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg5, upd_app, ↓reduceIte]
        show reg c4 sp + 0x80 = _; rw [RFc4.1]; exact gB _ _ rfl)
    (by rw [r5m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg5, upd_app, ↓reduceIte]
        show reg c4 0 + reg c4 9 = _; rw [w4.zero, RFc4.2.1]; exact BitVec.zero_add _)
    (by rw [r5m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg5, upd_app, ↓reduceIte]
        show reg c4 0 + reg c4 19 = _; rw [w4.zero, RFc4.2.2.2.1]; exact BitVec.zero_add _)
    (by rw [regs5m]; try simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x72 + 8) (by decide)))
    (by rw [r5m _ (by decide), RF5.1, e60s])
  rw [mem5m] at fr5 out5
  rw [e60s] at sp5c
  have w5 : St c5.mem P c5 0x7A (reg c5) := ⟨by rw [pc5]; try rfl, rfl, fun _ => rfl⟩
  have RFc5 := EdRF.call RF5 ub5.zero regs5m kk5 edKeep_feM (by decide) (by decide) (by decide) sp5c
  have frS5 : ∀ y, Sep G 0x210 y 1 → c5.mem y = m.mem y := fun y hy => by
    rw [fr5 y (inG (by decide) y hy) (inG (by decide) y hy), frS4 y hy]
  have up5 : ∀ i, i < 20 → c5.mem (G + BitVec.ofNat 32 (0x1FC + i)) = Q4 (G + BitVec.ofNat 32 (0x1FC + i)) :=
    fun i hi => by
      rw [fr5 _ (sepS (.inl (by omega)) (by omega) (by omega)) (sepS (.inl (by omega)) (by omega) (by omega)), up4 i hi]
  have hXY : feW c5.mem (G + BitVec.ofNat 32 0x130) = addL (feW m.mem sf) (feW m.mem (sf + 0x28)) := by
    rw [feW_add out5, sfX sfS0 frS4, sfX sfS1 frS4]
  have pv5 : ∀ {b : Nat}, 0xB0 ≤ b → b + 40 ≤ 0x210 → (b + 40 ≤ 0x130 ∨ 0x158 ≤ b) →
      feW c5.mem (G + BitVec.ofNat 32 b) = feW c4.mem (G + BitVec.ofNat 32 b) := fun h1 h2 h3 =>
    feW_frame2 fr5 (sepS (.inl (by omega)) (by omega) (by omega)) (sepS (by omega) (by omega) (by omega))
  -- 0x7A..0x7E: `addi a0, sp, 0xA8`, `addi a1, sp, 0x80`, and `square` into `(X + Y)²` at `G + 0x158`
  have hc5 : CodeIn c5.mem P edDoubleCode := edd_code env.code env.sGC env.sOC fun y hy _ => frS5 y hy
  obtain ⟨b6, cb6, ub6⟩ := St.block eSeg6 w5 hc5 eSeg6_end (by simp [BlockOk, BInstr.ok, eSeg6])
  have RF6 := RFc5.block w5.zero eSeg6 c5.mem eSeg6_d
  obtain ⟨c6m, cc6m, pc6m, mem6m, regs6m⟩ := ub6.callRa hc5 edd_at_7e edd_at_82 (cb := P + 0xFFFFE164)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE164 (by decide))
  have r6m := PEnv.reg1 regs6m ub6.zero
  rw [show (runBlock eSeg6 (c5.mem, reg c5)).1 = c5.mem from rfl] at mem6m
  obtain ⟨c6, cc6, pc6, sp6c, kk6, out6, fr6⟩ := feSquare_correct c6m (retAddr := P + BitVec.ofNat 32 (0x7E + 8))
    (edd_sqEnv env (by rw [mem6m]; exact fun y hy _ => frS5 y hy) (o := G + BitVec.ofNat 32 0x158)
      (x := G + BitVec.ofNat 32 0x130) (alG _ (by decide)) (alG _ (by decide))
      (env.sGQ.sub (by decide)) (env.sGR.sub (by decide)) (edd_sepG0 (by decide) (by decide))
      (edd_sepG0 (by decide) (by decide)))
    pc6m
    (by rw [r6m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg6, upd_app, ↓reduceIte]
        show reg c5 sp + 0xA8 = _; rw [RFc5.1]; exact gB _ _ rfl)
    (by rw [r6m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg6, upd_app, ↓reduceIte]
        show reg c5 sp + 0x80 = _; rw [RFc5.1]; exact gB _ _ rfl)
    (by rw [regs6m]; try simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x7E + 8) (by decide)))
    (by rw [r6m _ (by decide), RF6.1])
  rw [mem6m, edd_low] at fr6
  rw [mem6m] at out6
  have w6 : St c6.mem P c6 0x86 (reg c6) := ⟨by rw [pc6]; try rfl, rfl, fun _ => rfl⟩
  have RFc6 := EdRF.call RF6 ub6.zero regs6m kk6 edKeep_sq (by decide) (by decide) (by decide) sp6c
  have frS6 : ∀ y, Sep G 0x210 y 1 → c6.mem y = m.mem y := fun y hy => by
    rw [fr6 y (inG0 (by decide) y hy) (inG (by decide) y hy), frS5 y hy]
  have up6 : ∀ i, i < 20 → c6.mem (G + BitVec.ofNat 32 (0x1FC + i)) = Q4 (G + BitVec.ofNat 32 (0x1FC + i)) :=
    fun i hi => by
      rw [fr6 _ (sep0 (by omega) (by omega)) (sepS (.inl (by omega)) (by omega) (by omega)), up5 i hi]
  have hXYS : feW c6.mem (G + BitVec.ofNat 32 0x158) = sqL (addL (feW m.mem sf) (feW m.mem (sf + 0x28))) := by
    rw [← feW_words, out6]; show sqL (feW c5.mem (G + BitVec.ofNat 32 0x130)) = _; rw [hXY]
  have pv6 : ∀ {b : Nat}, 0xB0 ≤ b → b + 40 ≤ 0x210 → (b + 40 ≤ 0x158 ∨ 0x180 ≤ b) →
      feW c6.mem (G + BitVec.ofNat 32 b) = feW c5.mem (G + BitVec.ofNat 32 b) := fun h1 h2 h3 =>
    feW_frame2 fr6 (sep0 (by omega) (by omega)) (sepS (by omega) (by omega) (by omega))
  -- 0x86..0x8C: `addi a0, sp, 0xD0`, `addi a1, sp, 0x30`, `addi a2, sp, 8`, and `add` into `YY + XX` at `G + 0x180`
  have hc6 : CodeIn c6.mem P edDoubleCode := edd_code env.code env.sGC env.sOC fun y hy _ => frS6 y hy
  obtain ⟨b7, cb7, ub7⟩ := St.block eSeg7 w6 hc6 eSeg7_end (by simp [BlockOk, BInstr.ok, eSeg7])
  have RF7 := RFc6.block w6.zero eSeg7 c6.mem eSeg7_d
  obtain ⟨c7m, cc7m, pc7m, mem7m, regs7m⟩ := ub7.callRa hc6 edd_at_8c edd_at_90 (cb := P + 0xFFFFE674)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE674 (by decide))
  have r7m := PEnv.reg1 regs7m ub7.zero
  rw [show (runBlock eSeg7 (c6.mem, reg c6)).1 = c6.mem from rfl] at mem7m
  obtain ⟨c7, cc7, pc7, sp7c, kk7, out7, fr7⟩ := feAdd_correct c7m (retAddr := P + BitVec.ofNat 32 (0x8C + 8))
    (edd_addEnv env (by rw [mem7m]; exact fun y hy _ => frS6 y hy) (o := G + BitVec.ofNat 32 0x180)
      (x := G + BitVec.ofNat 32 0xE0) (y := G + BitVec.ofNat 32 0xB8) (by rw [edd_gw hGt (by decide)]; omega)
      (by rw [edd_gw hGt (by decide)]; omega) (alG _ (by decide)) (env.sGA.sub (by decide)) (env.sGB.sub (by decide))
      (sepS (.inr (by decide)) (by decide) (by decide)) (sepS (.inr (by decide)) (by decide) (by decide))
      (sepS (.inr (by decide)) (by decide) (by decide)))
    pc7m
    (by rw [r7m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg7, upd_app, ↓reduceIte]
        show reg c6 sp + 0xD0 = _; rw [RFc6.1]; exact gB _ _ rfl)
    (by rw [r7m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg7, upd_app, ↓reduceIte]
        show reg c6 sp + 0x30 = _; rw [RFc6.1]; exact gB _ _ rfl)
    (by rw [r7m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg7, upd_app, ↓reduceIte]
        show reg c6 sp + 0x8 = _; rw [RFc6.1]; exact gB _ _ rfl)
    (by rw [regs7m]; try simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x8C + 8) (by decide)))
    (by rw [r7m _ (by decide), RF7.1, e60s])
  rw [mem7m] at fr7 out7
  rw [e60s] at sp7c
  have w7 : St c7.mem P c7 0x94 (reg c7) := ⟨by rw [pc7]; try rfl, rfl, fun _ => rfl⟩
  have RFc7 := EdRF.call RF7 ub7.zero regs7m kk7 edKeep_feM (by decide) (by decide) (by decide) sp7c
  have frS7 : ∀ y, Sep G 0x210 y 1 → c7.mem y = m.mem y := fun y hy => by
    rw [fr7 y (inG (by decide) y hy) (inG (by decide) y hy), frS6 y hy]
  have up7 : ∀ i, i < 20 → c7.mem (G + BitVec.ofNat 32 (0x1FC + i)) = Q4 (G + BitVec.ofNat 32 (0x1FC + i)) :=
    fun i hi => by
      rw [fr7 _ (sepS (.inl (by omega)) (by omega) (by omega)) (sepS (.inl (by omega)) (by omega) (by omega)), up6 i hi]
  have pv7 : ∀ {b : Nat}, 0xB0 ≤ b → b + 40 ≤ 0x210 → (b + 40 ≤ 0x180 ∨ 0x1A8 ≤ b) →
      feW c7.mem (G + BitVec.ofNat 32 b) = feW c6.mem (G + BitVec.ofNat 32 b) := fun h1 h2 h3 =>
    feW_frame2 fr7 (sepS (.inl (by omega)) (by omega) (by omega)) (sepS (by omega) (by omega) (by omega))
  have hXX6 : feW c6.mem (G + BitVec.ofNat 32 0xB8) = sqL (feW m.mem sf) := by
    rw [pv6 (by decide) (by decide) (by decide), pv5 (by decide) (by decide) (by decide), hXX4]
  have hYY6 : feW c6.mem (G + BitVec.ofNat 32 0xE0) = sqL (feW m.mem (sf + 0x28)) := by
    rw [pv6 (by decide) (by decide) (by decide), pv5 (by decide) (by decide) (by decide), hYY4]
  have hPP : feW c7.mem (G + BitVec.ofNat 32 0x180) = addL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf)) := by
    rw [feW_add out7, hYY6, hXX6]
  -- 0x94..0x9A: `addi a0, sp, 0xF8`, `addi a1, sp, 0x30`, `addi a2, sp, 8`, and `sub` into `YY - XX` at `G + 0x1A8`
  have hc7 : CodeIn c7.mem P edDoubleCode := edd_code env.code env.sGC env.sOC fun y hy _ => frS7 y hy
  obtain ⟨b8, cb8, ub8⟩ := St.block eSeg8 w7 hc7 eSeg8_end (by simp [BlockOk, BInstr.ok, eSeg8])
  have RF8 := RFc7.block w7.zero eSeg8 c7.mem eSeg8_d
  obtain ⟨c8m, cc8m, pc8m, mem8m, regs8m⟩ := ub8.callRa hc7 edd_at_9a edd_at_9e (cb := P + 0xFFFFE6C2)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE6C2 (by decide))
  have r8m := PEnv.reg1 regs8m ub8.zero
  rw [show (runBlock eSeg8 (c7.mem, reg c7)).1 = c7.mem from rfl] at mem8m
  obtain ⟨c8, cc8, pc8, sp8c, kk8, out8, fr8⟩ := feSub_correct c8m (retAddr := P + BitVec.ofNat 32 (0x9A + 8))
    (edd_subEnv env (by rw [mem8m]; exact fun y hy _ => frS7 y hy) (o := G + BitVec.ofNat 32 0x1A8)
      (x := G + BitVec.ofNat 32 0xE0) (y := G + BitVec.ofNat 32 0xB8) (alG _ (by decide)) (alG _ (by decide))
      (alG _ (by decide)) (env.sGS.sub (by decide)) (edd_sepG0 (by decide) (by decide))
      (edd_sepG0 (by decide) (by decide)) (edd_sepG0 (by decide) (by decide)))
    pc8m
    (by rw [r8m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg8, upd_app, ↓reduceIte]
        show reg c7 sp + 0xF8 = _; rw [RFc7.1]; exact gB _ _ rfl)
    (by rw [r8m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg8, upd_app, ↓reduceIte]
        show reg c7 sp + 0x30 = _; rw [RFc7.1]; exact gB _ _ rfl)
    (by rw [r8m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg8, upd_app, ↓reduceIte]
        show reg c7 sp + 0x8 = _; rw [RFc7.1]; exact gB _ _ rfl)
    (by rw [regs8m]; try simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x9A + 8) (by decide)))
    (by rw [r8m _ (by decide), RF8.1])
  rw [mem8m] at fr8 out8
  have w8 : St c8.mem P c8 0xA2 (reg c8) := ⟨by rw [pc8]; try rfl, rfl, fun _ => rfl⟩
  have RFc8 := EdRF.call RF8 ub8.zero regs8m kk8 edKeep_feM (by decide) (by decide) (by decide) sp8c
  have frS8 : ∀ y, Sep G 0x210 y 1 → c8.mem y = m.mem y := fun y hy => by
    rw [fr8 y (inG0 (by decide) y hy) (inG (by decide) y hy), frS7 y hy]
  have up8 : ∀ i, i < 20 → c8.mem (G + BitVec.ofNat 32 (0x1FC + i)) = Q4 (G + BitVec.ofNat 32 (0x1FC + i)) :=
    fun i hi => by
      rw [fr8 _ (sep0 (by omega) (by omega)) (sepS (.inl (by omega)) (by omega) (by omega)), up7 i hi]
  have pv8 : ∀ {b : Nat}, 0xB0 ≤ b → b + 40 ≤ 0x210 → (b + 40 ≤ 0x1A8 ∨ 0x1D0 ≤ b) →
      feW c8.mem (G + BitVec.ofNat 32 b) = feW c7.mem (G + BitVec.ofNat 32 b) := fun h1 h2 h3 =>
    feW_frame2 fr8 (sep0 (by omega) (by omega)) (sepS (by omega) (by omega) (by omega))
  have hXX7 : feW c7.mem (G + BitVec.ofNat 32 0xB8) = sqL (feW m.mem sf) := by
    rw [pv7 (by decide) (by decide) (by decide), hXX6]
  have hYY7 : feW c7.mem (G + BitVec.ofNat 32 0xE0) = sqL (feW m.mem (sf + 0x28)) := by
    rw [pv7 (by decide) (by decide) (by decide), hYY6]
  have hMM : feW c8.mem (G + BitVec.ofNat 32 0x1A8) = subL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf)) := by
    rw [feW_sub out8, hYY7, hXX7]
  -- from here on the calls write the result
  have oG : ∀ {d : Nat}, d + 40 ≤ 160 → Sep (out + BitVec.ofNat 32 d) 40 G 0x210 := fun h => env.sOG.sub h
  have oS : ∀ {c d : Nat}, c + 40 ≤ d ∨ d + 40 ≤ c → c + 40 ≤ 160 → d + 40 ≤ 160 →
      Sep (out + BitVec.ofNat 32 c) 40 (out + BitVec.ofNat 32 d) 40 := fun h h1 h2 => sep_offsets out h (by omega) (by omega)
  have o0 : out + BitVec.ofNat 32 0 = out := add_ofNat_zero out
  -- 0xA2..0xA8: `addi a1, sp, 0xA8`, `addi a2, sp, 0xD0`, `mv a0, s2`, and `sub` into the result's `X`
  have hc8 : CodeIn c8.mem P edDoubleCode := edd_code env.code env.sGC env.sOC fun y hy _ => frS8 y hy
  obtain ⟨b9, cb9, ub9⟩ := St.block eSeg9 w8 hc8 eSeg9_end (by simp [BlockOk, BInstr.ok, eSeg9])
  have RF9 := RFc8.block w8.zero eSeg9 c8.mem eSeg9_d
  obtain ⟨c9m, cc9m, pc9m, mem9m, regs9m⟩ := ub9.callRa hc8 edd_at_a8 edd_at_ac (cb := P + 0xFFFFE6C2)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE6C2 (by decide))
  have r9m := PEnv.reg1 regs9m ub9.zero
  rw [show (runBlock eSeg9 (c8.mem, reg c8)).1 = c8.mem from rfl] at mem9m
  obtain ⟨c9, cc9, pc9, sp9c, kk9, out9, fr9⟩ := feSub_correct c9m (retAddr := P + BitVec.ofNat 32 (0xA8 + 8))
    (edd_subEnv env (by rw [mem9m]; exact fun y hy _ => frS8 y hy) (o := out)
      (x := G + BitVec.ofNat 32 0x158) (y := G + BitVec.ofNat 32 0x180) env.hout (alG _ (by decide))
      (alG _ (by decide)) (sep_pre env.sOS (by decide)) (sepR0 (sep_pre env.sOG (by decide)) (by decide))
      (edd_sepG0 (by decide) (by decide)) (edd_sepG0 (by decide) (by decide)))
    pc9m
    (by rw [r9m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg9, upd_app, ↓reduceIte]
        show reg c8 0 + reg c8 18 = _; rw [w8.zero, RFc8.2.2.1]; exact BitVec.zero_add _)
    (by rw [r9m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg9, upd_app, ↓reduceIte]
        show reg c8 sp + 0xA8 = _; rw [RFc8.1]; exact gB _ _ rfl)
    (by rw [r9m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg9, upd_app, ↓reduceIte]
        show reg c8 sp + 0xD0 = _; rw [RFc8.1]; exact gB _ _ rfl)
    (by rw [regs9m]; try simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0xA8 + 8) (by decide)))
    (by rw [r9m _ (by decide), RF9.1])
  rw [mem9m] at fr9 out9
  have w9 : St c9.mem P c9 0xB0 (reg c9) := ⟨by rw [pc9]; try rfl, rfl, fun _ => rfl⟩
  have RFc9 := EdRF.call RF9 ub9.zero regs9m kk9 edKeep_feM (by decide) (by decide) (by decide) sp9c
  have frO9 : ∀ y, Sep G 0x210 y 1 → Sep out 160 y 1 → c9.mem y = m.mem y := fun y hy ho => by
    rw [fr9 y (inG0 (by decide) y hy) (sep_pre ho (by decide)), frS8 y hy]
  have up9 : ∀ i, i < 20 → c9.mem (G + BitVec.ofNat 32 (0x1FC + i)) = Q4 (G + BitVec.ofNat 32 (0x1FC + i)) :=
    fun i hi => by
      rw [fr9 _ (sep0 (by omega) (by omega)) ((sep_pre env.sOG (by decide)).subR (c := 0x1FC + i) (l := 1) (by omega)),
        up8 i hi]
  have pv9 : ∀ {b : Nat}, 0xB0 ≤ b → b + 40 ≤ 0x210 →
      feW c9.mem (G + BitVec.ofNat 32 b) = feW c8.mem (G + BitVec.ofNat 32 b) := fun {b} h1 h2 =>
    feW_frame2 fr9 (sep0 (by omega) (by omega)) ((sep_pre env.sOG (by decide)).subR (c := b) (l := 40) (by omega))
  have hXYS8 : feW c8.mem (G + BitVec.ofNat 32 0x158) = sqL (addL (feW m.mem sf) (feW m.mem (sf + 0x28))) := by
    rw [pv8 (by decide) (by decide) (by decide), pv7 (by decide) (by decide) (by decide), hXYS]
  have hPP8 : feW c8.mem (G + BitVec.ofNat 32 0x180) = addL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf)) := by
    rw [pv8 (by decide) (by decide) (by decide), hPP]
  have hOX : feW c9.mem out = subL (sqL (addL (feW m.mem sf) (feW m.mem (sf + 0x28))))
      (addL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf))) := by
    rw [feW_sub out9, hXYS8, hPP8]
  -- 0xB0..0xB8: `addi a0, s2, 0x78`, `addi a1, sp, 0x58`, `addi a2, sp, 0xF8`, and `sub` into the result's `T`
  have hc9 : CodeIn c9.mem P edDoubleCode := edd_code env.code env.sGC env.sOC frO9
  obtain ⟨b10, cb10, ub10⟩ := St.block eSeg10 w9 hc9 eSeg10_end (by simp [BlockOk, BInstr.ok, eSeg10])
  have RF10 := RFc9.block w9.zero eSeg10 c9.mem eSeg10_d
  obtain ⟨c10m, cc10m, pc10m, mem10m, regs10m⟩ := ub10.callRa hc9 edd_at_b8 edd_at_bc (cb := P + 0xFFFFE6C2)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE6C2 (by decide))
  have r10m := PEnv.reg1 regs10m ub10.zero
  rw [show (runBlock eSeg10 (c9.mem, reg c9)).1 = c9.mem from rfl] at mem10m
  obtain ⟨c10, cc10, pc10, sp10c, kk10, out10, fr10⟩ := feSub_correct c10m (retAddr := P + BitVec.ofNat 32 (0xB8 + 8))
    (edd_subEnv env (by rw [mem10m]; exact frO9) (o := out + 0x78)
      (x := G + BitVec.ofNat 32 0x108) (y := G + BitVec.ofNat 32 0x1A8) (aligned_add env.hout (k := 0x78) (by decide))
      (alG _ (by decide)) (alG _ (by decide)) (env.sOS.sub (c := 0x78) (l := 40) (by decide))
      (sepR0 (oG (d := 0x78) (by decide)) (by decide))
      (edd_sepG0 (by decide) (by decide)) (edd_sepG0 (by decide) (by decide)))
    pc10m
    (by rw [r10m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg10, upd_app, ↓reduceIte]
        show reg c9 18 + 0x78 = _; rw [RFc9.2.2.1])
    (by rw [r10m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg10, upd_app, ↓reduceIte]
        show reg c9 sp + 0x58 = _; rw [RFc9.1]; exact gB _ _ rfl)
    (by rw [r10m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg10, upd_app, ↓reduceIte]
        show reg c9 sp + 0xF8 = _; rw [RFc9.1]; exact gB _ _ rfl)
    (by rw [regs10m]; try simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0xB8 + 8) (by decide)))
    (by rw [r10m _ (by decide), RF10.1])
  rw [mem10m] at fr10 out10
  have w10 : St c10.mem P c10 0xC0 (reg c10) := ⟨by rw [pc10]; try rfl, rfl, fun _ => rfl⟩
  have RFc10 := EdRF.call RF10 ub10.zero regs10m kk10 edKeep_feM (by decide) (by decide) (by decide) sp10c
  have frO10 : ∀ y, Sep G 0x210 y 1 → Sep out 160 y 1 → c10.mem y = m.mem y := fun y hy ho => by
    rw [fr10 y (inG0 (by decide) y hy) (ho.sub (c := 0x78) (l := 40) (by decide)), frO9 y hy ho]
  have up10 : ∀ i, i < 20 → c10.mem (G + BitVec.ofNat 32 (0x1FC + i)) = Q4 (G + BitVec.ofNat 32 (0x1FC + i)) :=
    fun i hi => by
      rw [fr10 _ (sep0 (by omega) (by omega)) ((oG (d := 0x78) (by decide)).subR (c := 0x1FC + i) (l := 1) (by omega)),
        up9 i hi]
  have pv10 : ∀ {b : Nat}, 0xB0 ≤ b → b + 40 ≤ 0x210 →
      feW c10.mem (G + BitVec.ofNat 32 b) = feW c9.mem (G + BitVec.ofNat 32 b) := fun {b} h1 h2 =>
    feW_frame2 fr10 (sep0 (by omega) (by omega)) ((oG (d := 0x78) (by decide)).subR (c := b) (l := 40) (by omega))
  have hZZ9 : feW c9.mem (G + BitVec.ofNat 32 0x108) = sq2L (feW m.mem (sf + 0x50)) := by
    rw [pv9 (by decide) (by decide), pv8 (by decide) (by decide) (by decide), pv7 (by decide) (by decide) (by decide),
      pv6 (by decide) (by decide) (by decide), pv5 (by decide) (by decide) (by decide), hZZ]
  have hMM9 : feW c9.mem (G + BitVec.ofNat 32 0x1A8) = subL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf)) := by
    rw [pv9 (by decide) (by decide), hMM]
  have hOT : feW c10.mem (out + 0x78) = subL (sq2L (feW m.mem (sf + 0x50)))
      (subL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf))) := by
    rw [feW_sub out10, hZZ9, hMM9]
  have sGO : ∀ {d : Nat}, d + 40 ≤ 160 → Sep G 0xB0 (out + BitVec.ofNat 32 d) 40 := fun h =>
    (sepR0 (oG h) (by decide)).symm
  have hOX10 : feW c10.mem out = subL (sqL (addL (feW m.mem sf) (feW m.mem (sf + 0x28))))
      (addL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf))) := by
    rw [feW_frame2 fr10 (by have := sGO (d := 0) (by decide); rwa [o0] at this)
      (by have := oS (c := 0x78) (d := 0) (.inr (by decide)) (by decide) (by decide); rwa [o0] at this), hOX]
  have eA0 : G + 0xB0 + 0xFFFFFFF0 = G + BitVec.ofNat 32 0xA0 := gB _ _ rfl
  have eMC : P + 0x43FC + 8 = P + 0x4404 := by rw [BitVec.add_assoc]; rfl
  -- 0xC0..0xCA: `addi a0, s2, 0x28`, `addi a1, sp, 0xD0`, `li a2, 0x28`, and `memcpy` of `YY + XX` to the result's `Y`
  have hc10 : CodeIn c10.mem P edDoubleCode := edd_code env.code env.sGC env.sOC frO10
  obtain ⟨b11, cb11, ub11⟩ := St.block eSeg11 w10 hc10 eSeg11_end (by simp [BlockOk, BInstr.ok, eSeg11])
  have RF11 := RFc10.block w10.zero eSeg11 c10.mem eSeg11_d
  obtain ⟨c11m, cc11m, pc11m, mem11m, regs11m⟩ := ub11.callRa hc10 edd_at_ca edd_at_ce (cb := P + 0x43FC)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x43FC (by decide))
  have r11m := PEnv.reg1 regs11m ub11.zero
  rw [show (runBlock eSeg11 (c10.mem, reg c10)).1 = c10.mem from rfl] at mem11m
  obtain ⟨c11, cc11, pc11, sp11c, _, mem11, K11⟩ := memcpy_correct c11m (P + 0x43FC) (P + BitVec.ofNat 32 (0xCA + 8))
    (out + 0x28) (G + BitVec.ofNat 32 0x180) 40
    (fun i hi => by show c11m.mem _ = _; rw [mem11m]; exact edd_code env.mcS env.sGM env.sOM frO10 i hi)
    (even_at P env.hP 0x43FC (by decide)) pc11m
    (by rw [r11m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg11, upd_app, ↓reduceIte]
        show reg c10 18 + 0x28 = _; rw [RFc10.2.2.1])
    (by rw [r11m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg11, upd_app, ↓reduceIte]
        show reg c10 sp + 0xD0 = _; rw [RFc10.1]; exact gB _ _ rfl)
    (by rw [r11m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg11, upd_app, ↓reduceIte]; try rfl)
    (by rw [regs11m]; try simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0xCA + 8) (by decide)))
    (by
      rw [r11m _ (by decide), RF11.1, eA0, mem11m, eMC]
      exact { code := edd_code env.mcB env.sGB env.sOB frO10
              hDC := env.sOB.sub (c := 0x28) (l := 40) (by decide)
              hFC := env.sGB.sub (c := 0xA0) (l := 16) (by decide)
              hdF := (oG (d := 0x28) (by decide)).subR (c := 0xA0) (l := 16) (by decide)
              hsF := sepS (.inr (by decide)) (by decide) (by decide)
              hsep := (oG (d := 0x28) (by decide)).subR (c := 0x180) (l := 40) (by decide)
              hF := alG _ (by decide)
              hFw := by rw [edd_gw hGt (by decide)]; omega
              hdw := by
                have := env.hot
                rw [show (out + 0x28 : Word) = out + BitVec.ofNat 32 0x28 from rfl, BitVec.toNat_add,
                  BitVec.toNat_ofNat]
                omega
              hsw := by rw [edd_gw hGt (by decide)]; omega })
  rw [r11m _ (by decide), RF11.1, eA0, mem11m] at mem11
  have w11 : St c11.mem P c11 0xD2 (reg c11) := ⟨by rw [pc11]; try rfl, rfl, fun _ => rfl⟩
  have RFc11 := EdRF.mc RF11 ub11.zero regs11m sp11c K11
  have fr11 : ∀ y, Sep (G + BitVec.ofNat 32 0xA0) 16 y 1 → Sep (out + 0x28) 40 y 1 → c11.mem y = c10.mem y :=
    fun y h1 h2 => by rw [mem11 y h1, copyBytes_sep h2 (Nat.le_refl _)]
  have frO11 : ∀ y, Sep G 0x210 y 1 → Sep out 160 y 1 → c11.mem y = m.mem y := fun y hy ho => by
    rw [fr11 y (inG (by decide) y hy) (ho.sub (c := 0x28) (l := 40) (by decide)), frO10 y hy ho]
  have up11 : ∀ i, i < 20 → c11.mem (G + BitVec.ofNat 32 (0x1FC + i)) = Q4 (G + BitVec.ofNat 32 (0x1FC + i)) :=
    fun i hi => by
      rw [fr11 _ (sepS (.inl (by omega)) (by omega) (by omega))
        ((oG (d := 0x28) (by decide)).subR (c := 0x1FC + i) (l := 1) (by omega)), up10 i hi]
  have hPP10 : feW c10.mem (G + BitVec.ofNat 32 0x180) = addL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf)) := by
    rw [pv10 (by decide) (by decide), pv9 (by decide) (by decide), hPP8]
  have hOY : feW c11.mem (out + 0x28) = addL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf)) := by
    rw [feW_frame (a := out + 0x28) fun i hi => load_frame mem11 ((oG (d := 0x28) (by decide)).subR (c := 0xA0)
      (l := 16) (by decide) |>.symm.subR (c := 4 * i) (l := 4) (by omega)), feW_copy, hPP10]
  have hOX11 : feW c11.mem out = subL (sqL (addL (feW m.mem sf) (feW m.mem (sf + 0x28))))
      (addL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf))) := by
    rw [feW_frame2 fr11 (by have := (oG (d := 0) (by decide)).subR (c := 0xA0) (l := 16) (by decide); rw [o0] at this; exact this.symm)
      (by have := oS (c := 0x28) (d := 0) (.inr (by decide)) (by decide) (by decide); rwa [o0] at this), hOX10]
  have hOT11 : feW c11.mem (out + 0x78) = subL (sq2L (feW m.mem (sf + 0x50)))
      (subL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf))) := by
    rw [feW_frame2 (a := out + 0x78) fr11 ((oG (d := 0x78) (by decide)).subR (c := 0xA0) (l := 16) (by decide)).symm
      (oS (c := 0x28) (d := 0x78) (.inl (by decide)) (by decide) (by decide)), hOT]
  -- 0xD2..0xDC: `addi a0, s2, 0x50`, `addi a1, sp, 0xF8`, `li a2, 0x28`, and `memcpy` of `YY - XX` to the result's `Z`
  have hc11 : CodeIn c11.mem P edDoubleCode := edd_code env.code env.sGC env.sOC frO11
  obtain ⟨b12, cb12, ub12⟩ := St.block eSeg12 w11 hc11 eSeg12_end (by simp [BlockOk, BInstr.ok, eSeg12])
  have RF12 := RFc11.block w11.zero eSeg12 c11.mem eSeg12_d
  obtain ⟨c12m, cc12m, pc12m, mem12m, regs12m⟩ := ub12.callRa hc11 edd_at_dc edd_at_e0 (cb := P + 0x43FC)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x43FC (by decide))
  have r12m := PEnv.reg1 regs12m ub12.zero
  rw [show (runBlock eSeg12 (c11.mem, reg c11)).1 = c11.mem from rfl] at mem12m
  obtain ⟨c12, cc12, pc12, sp12c, _, mem12, K12⟩ := memcpy_correct c12m (P + 0x43FC) (P + BitVec.ofNat 32 (0xDC + 8))
    (out + 0x50) (G + BitVec.ofNat 32 0x1A8) 40
    (fun i hi => by show c12m.mem _ = _; rw [mem12m]; exact edd_code env.mcS env.sGM env.sOM frO11 i hi)
    (even_at P env.hP 0x43FC (by decide)) pc12m
    (by rw [r12m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg12, upd_app, ↓reduceIte]
        show reg c11 18 + 0x50 = _; rw [RFc11.2.2.1])
    (by rw [r12m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg12, upd_app, ↓reduceIte]
        show reg c11 sp + 0xF8 = _; rw [RFc11.1]; exact gB _ _ rfl)
    (by rw [r12m _ (by decide)]; simp +decide only [runBlock, BInstr.run, eSeg12, upd_app, ↓reduceIte]; try rfl)
    (by rw [regs12m]; try simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0xDC + 8) (by decide)))
    (by
      rw [r12m _ (by decide), RF12.1, eA0, mem12m, eMC]
      exact { code := edd_code env.mcB env.sGB env.sOB frO11
              hDC := env.sOB.sub (c := 0x50) (l := 40) (by decide)
              hFC := env.sGB.sub (c := 0xA0) (l := 16) (by decide)
              hdF := (oG (d := 0x50) (by decide)).subR (c := 0xA0) (l := 16) (by decide)
              hsF := sepS (.inr (by decide)) (by decide) (by decide)
              hsep := (oG (d := 0x50) (by decide)).subR (c := 0x1A8) (l := 40) (by decide)
              hF := alG _ (by decide)
              hFw := by rw [edd_gw hGt (by decide)]; omega
              hdw := by
                have := env.hot
                rw [show (out + 0x50 : Word) = out + BitVec.ofNat 32 0x50 from rfl, BitVec.toNat_add,
                  BitVec.toNat_ofNat]
                omega
              hsw := by rw [edd_gw hGt (by decide)]; omega })
  rw [r12m _ (by decide), RF12.1, eA0, mem12m] at mem12
  have w12 : St c12.mem P c12 0xE4 (reg c12) := ⟨by rw [pc12]; try rfl, rfl, fun _ => rfl⟩
  have RFc12 := EdRF.mc RF12 ub12.zero regs12m sp12c K12
  have fr12 : ∀ y, Sep (G + BitVec.ofNat 32 0xA0) 16 y 1 → Sep (out + 0x50) 40 y 1 → c12.mem y = c11.mem y :=
    fun y h1 h2 => by rw [mem12 y h1, copyBytes_sep h2 (Nat.le_refl _)]
  have frO12 : ∀ y, Sep G 0x210 y 1 → Sep out 160 y 1 → c12.mem y = m.mem y := fun y hy ho => by
    rw [fr12 y (inG (by decide) y hy) (ho.sub (c := 0x50) (l := 40) (by decide)), frO11 y hy ho]
  have up12 : ∀ i, i < 20 → c12.mem (G + BitVec.ofNat 32 (0x1FC + i)) = Q4 (G + BitVec.ofNat 32 (0x1FC + i)) :=
    fun i hi => by
      rw [fr12 _ (sepS (.inl (by omega)) (by omega) (by omega))
        ((oG (d := 0x50) (by decide)).subR (c := 0x1FC + i) (l := 1) (by omega)), up11 i hi]
  have hMM11 : feW c11.mem (G + BitVec.ofNat 32 0x1A8) = subL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf)) := by
    rw [feW_frame2 fr11 (sepS (.inl (by decide)) (by decide) (by decide))
      ((oG (d := 0x28) (by decide)).subR (c := 0x1A8) (l := 40) (by decide)), pv10 (by decide) (by decide), hMM9]
  have hOZ : feW c12.mem (out + 0x50) = subL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf)) := by
    rw [feW_frame (a := out + 0x50) fun i hi => load_frame mem12 ((oG (d := 0x50) (by decide)).subR (c := 0xA0)
      (l := 16) (by decide) |>.symm.subR (c := 4 * i) (l := 4) (by omega)), feW_copy, hMM11]
  have hOX12 : feW c12.mem out = subL (sqL (addL (feW m.mem sf) (feW m.mem (sf + 0x28))))
      (addL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf))) := by
    rw [feW_frame2 fr12 (by have := (oG (d := 0) (by decide)).subR (c := 0xA0) (l := 16) (by decide); rw [o0] at this; exact this.symm)
      (by have := oS (c := 0x50) (d := 0) (.inr (by decide)) (by decide) (by decide); rwa [o0] at this), hOX11]
  have hOY12 : feW c12.mem (out + 0x28) = addL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf)) := by
    rw [feW_frame2 (a := out + 0x28) fr12 ((oG (d := 0x28) (by decide)).subR (c := 0xA0) (l := 16) (by decide)).symm
      (oS (c := 0x50) (d := 0x28) (.inr (by decide)) (by decide) (by decide)), hOY]
  have hOT12 : feW c12.mem (out + 0x78) = subL (sq2L (feW m.mem (sf + 0x50)))
      (subL (sqL (feW m.mem (sf + 0x28))) (sqL (feW m.mem sf))) := by
    rw [feW_frame2 (a := out + 0x78) fr12 ((oG (d := 0x78) (by decide)).subR (c := 0xA0) (l := 16) (by decide)).symm
      (oS (c := 0x50) (d := 0x78) (.inl (by decide)) (by decide) (by decide)), hOT11]
  -- the epilogue: restore `ra` and `s0` through `s3`, pop the frame, and return
  have hc12 : CodeIn c12.mem P edDoubleCode := edd_code env.code env.sGC env.sOC frO12
  have slot : ∀ c, 0x1FC ≤ c → c + 4 ≤ 0x210 →
      memLoad32 c12.mem (G + BitVec.ofNat 32 c) = memLoad32 Q4 (G + BitVec.ofNat 32 c) := fun c h1 h2 =>
    memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, show c + j = 0x1FC + (c - 0x1FC + j) by omega, up12 _ (by omega)]
  have q4s : ∀ {c d : Nat}, c + 4 ≤ d ∨ d + 4 ≤ c → c + 4 ≤ 0x210 → d + 4 ≤ 0x210 →
      Sep (G + BitVec.ofNat 32 c) 4 (G + BitVec.ofNat 32 d) 4 := fun h h1 h2 => sepS h h1 h2
  have sv0 : memLoad32 Q4 (G + BitVec.ofNat 32 0x20C) = reg m ra := by
    rw [← hQ4, memLoad32_store32_sep (q4s (.inl (by decide)) (by decide) (by decide)), ← hQ3,
      memLoad32_store32_sep (q4s (.inl (by decide)) (by decide) (by decide)), ← hQ2,
      memLoad32_store32_sep (q4s (.inl (by decide)) (by decide) (by decide)), ← hQ1,
      memLoad32_store32_sep (q4s (.inl (by decide)) (by decide) (by decide)), ← hQ0, memLoad32_store32_same]
  have sv1 : memLoad32 Q4 (G + BitVec.ofNat 32 0x208) = reg m (8 : Fin 32) := by
    rw [← hQ4, memLoad32_store32_sep (q4s (.inl (by decide)) (by decide) (by decide)), ← hQ3,
      memLoad32_store32_sep (q4s (.inl (by decide)) (by decide) (by decide)), ← hQ2,
      memLoad32_store32_sep (q4s (.inl (by decide)) (by decide) (by decide)), ← hQ1, memLoad32_store32_same]
  have sv2 : memLoad32 Q4 (G + BitVec.ofNat 32 0x204) = reg m (9 : Fin 32) := by
    rw [← hQ4, memLoad32_store32_sep (q4s (.inl (by decide)) (by decide) (by decide)), ← hQ3,
      memLoad32_store32_sep (q4s (.inl (by decide)) (by decide) (by decide)), ← hQ2, memLoad32_store32_same]
  have sv3 : memLoad32 Q4 (G + BitVec.ofNat 32 0x200) = reg m (18 : Fin 32) := by
    rw [← hQ4, memLoad32_store32_sep (q4s (.inl (by decide)) (by decide) (by decide)), ← hQ3, memLoad32_store32_same]
  have sv4 : memLoad32 Q4 (G + BitVec.ofNat 32 0x1FC) = reg m (19 : Fin 32) := by rw [← hQ4, memLoad32_store32_same]
  obtain ⟨e0, de0, ue0⟩ := w12.aluImm hc12 edd_at_e4 (off' := 0xE6) (by decide)
  have ke0 := ue0.oldReg w12.zero
  have a0e : reg e0 a0 = G + BitVec.ofNat 32 0x1B0 := by
    rw [ue0.newReg (by decide)]; show reg c12 sp + 0x100 = _; rw [RFc12.1]; exact gB _ _ rfl
  obtain ⟨e1, de1, ue1⟩ := ue0.self.lwE hc12 edd_at_e6 (off' := 0xEA) (by decide)
    (by rw [a0e, gA 0x1B0 0x5C 0x20C rfl]; exact alG _ (by decide)) (v := reg m ra)
    (by rw [a0e, gA 0x1B0 0x5C 0x20C rfl, slot _ (by decide) (by decide), sv0])
  have ke1 := ue1.oldReg ue0.self.zero
  obtain ⟨e2, de2, ue2⟩ := ue1.self.lwE hc12 edd_at_ea (off' := 0xEC) (by decide)
    (by rw [ke1 _ (by decide), a0e, gA 0x1B0 0x58 0x208 rfl]; exact alG _ (by decide)) (v := reg m (8 : Fin 32))
    (by rw [ke1 _ (by decide), a0e, gA 0x1B0 0x58 0x208 rfl, slot _ (by decide) (by decide), sv1])
  have ke2 := ue2.oldReg ue1.self.zero
  obtain ⟨e3, de3, ue3⟩ := ue2.self.lwE hc12 edd_at_ec (off' := 0xEE) (by decide)
    (by rw [ke2 _ (by decide), ke1 _ (by decide), a0e, gA 0x1B0 0x54 0x204 rfl]; exact alG _ (by decide))
    (v := reg m (9 : Fin 32))
    (by rw [ke2 _ (by decide), ke1 _ (by decide), a0e, gA 0x1B0 0x54 0x204 rfl, slot _ (by decide) (by decide), sv2])
  have ke3 := ue3.oldReg ue2.self.zero
  obtain ⟨e4, de4, ue4⟩ := ue3.self.lwE hc12 edd_at_ee (off' := 0xF2) (by decide)
    (by rw [ke3 _ (by decide), ke2 _ (by decide), ke1 _ (by decide), a0e, gA 0x1B0 0x50 0x200 rfl]
        exact alG _ (by decide))
    (v := reg m (18 : Fin 32))
    (by rw [ke3 _ (by decide), ke2 _ (by decide), ke1 _ (by decide), a0e, gA 0x1B0 0x50 0x200 rfl,
          slot _ (by decide) (by decide), sv3])
  have ke4 := ue4.oldReg ue3.self.zero
  obtain ⟨e5, de5, ue5⟩ := ue4.self.lwE hc12 edd_at_f2 (off' := 0xF6) (by decide)
    (by rw [ke4 _ (by decide), ke3 _ (by decide), ke2 _ (by decide), ke1 _ (by decide), a0e,
          gA 0x1B0 0x4C 0x1FC rfl]
        exact alG _ (by decide))
    (v := reg m (19 : Fin 32))
    (by rw [ke4 _ (by decide), ke3 _ (by decide), ke2 _ (by decide), ke1 _ (by decide), a0e,
          gA 0x1B0 0x4C 0x1FC rfl, slot _ (by decide) (by decide), sv4])
  have ke5 := ue5.oldReg ue4.self.zero
  obtain ⟨e6, de6, ue6⟩ := ue5.self.aluImm hc12 edd_at_f6 (off' := 0xF8) (by decide)
  have ke6 := ue6.oldReg ue5.self.zero
  obtain ⟨e7, de7, pce7, meme7, regse7⟩ := ue6.self.jalr hc12 edd_at_f8
  have ra6 : reg e6 ra = reg m ra := by
    rw [ke6 _ (by decide), ke5 _ (by decide), ke4 _ (by decide), ke3 _ (by decide), ke2 _ (by decide),
      ue1.newReg (by decide)]
  have sp6 : reg e6 sp = G + 0x210 := by
    rw [ue6.newReg (by decide)]; show reg e5 sp + 0x160 = _
    rw [ke5 _ (by decide), ke4 _ (by decide), ke3 _ (by decide), ke2 _ (by decide), ke1 _ (by decide),
      ke0 _ (by decide), RFc12.1, BitVec.add_assoc]; rfl
  have steps : Steps m e7 := .cons d1 (.cons d2 (.cons dp0 (.cons dp1 (.cons dp2 (.cons dp3 (.cons dp4 (cb1.trans
    (cc1m.trans (cc1.trans (cb2.trans (cc2m.trans (cc2.trans (cb3.trans (cc3m.trans (cc3.trans (.cons d4 (.cons d5
    (cL.trans (cb4.trans (cc4m.trans (cc4.trans (cb5.trans (cc5m.trans (cc5.trans (cb6.trans (cc6m.trans (cc6.trans
    (cb7.trans (cc7m.trans (cc7.trans (cb8.trans (cc8m.trans (cc8.trans (cb9.trans (cc9m.trans (cc9.trans
    (cb10.trans (cc10m.trans (cc10.trans (cb11.trans (cc11m.trans (cc11.trans (cb12.trans (cc12m.trans (cc12.trans
    (.cons de0 (.cons de1 (.cons de2 (.cons de3 (.cons de4 (.cons de5 (.cons de6 (.single
    de7)))))))))))))))))))))))))))))))))))))))))))))))))))))
  refine ⟨e7, steps, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pce7, ra6, add_lit_zero, hra, hret]
  · rw [regse7, sp6]
  · intro q hq
    rw [regse7]
    by_cases h1 : q = sp
    · subst h1; rw [sp6, hsp]
    by_cases h2 : q = (19 : Fin 32)
    · subst h2; rw [ke6 _ (by decide), ue5.newReg (by decide)]
    by_cases h3 : q = (18 : Fin 32)
    · subst h3; rw [ke6 _ (by decide), ke5 _ (by decide), ue4.newReg (by decide)]
    by_cases h4 : q = (9 : Fin 32)
    · subst h4; rw [ke6 _ (by decide), ke5 _ (by decide), ke4 _ (by decide), ue3.newReg (by decide)]
    by_cases h5 : q = (8 : Fin 32)
    · subst h5; rw [ke6 _ (by decide), ke5 _ (by decide), ke4 _ (by decide), ke3 _ (by decide), ue2.newReg (by decide)]
    by_cases h6 : q = ra
    · subst h6; exact ra6
    have he : edKeep q = true := by
      rcases feM_ed q hq with e | e | e | e | e | e | e
      · exact absurd e h6
      · exact absurd e h1
      · exact absurd e h5
      · exact absurd e h4
      · exact absurd e h3
      · exact absurd e h2
      · exact e
    rw [ke6 q h1, ke5 q h2, ke4 q h3, ke3 q h4, ke2 q h5, ke1 q h6, ke0 q (edk_ne he (by decide)), RFc12.2.2.2.2 q he]
  · rw [meme7, hOX12]; rfl
  · rw [meme7, hOY12]; rfl
  · rw [meme7, hOZ]; rfl
  · rw [meme7, hOT12]; rfl
  · intro x hx ho; rw [meme7, frO12 x hx ho]

end C3.RV32
