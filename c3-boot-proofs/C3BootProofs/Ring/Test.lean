import C3BootProofs.Ring.Tactic

/-!
# Tests for `ring_eq` and `ring_mod`

Identities of the kinds the elliptic-curve proofs need, each with its
axioms pinned, and the time each tactic call took on Lean 4.34 (one core
of a cloud VM): the whole call, from the file's elaboration time less that
of the same statement proved by `sorry`, and the kernel's part of it.

| Theorem | Tactic | Kernel |
|---------|--------|--------|
| `atoms` | 10 ms | 2 ms |
| `nat_numerals` | under 10 ms | 2 ms |
| `mod_zero` | under 10 ms | 1 ms |
| `mod_zero_nat` | under 10 ms | 1 ms |
| `cofactor_nat_exponents` | under 10 ms | 5 ms |
| `xyz6` | 100 ms | 31 ms |
| `xyz6_nat` | 40 ms | 35 ms |
| `deg12` | 1.8 s | 1.8 s |
| `big_constant` | under 10 ms | 4 ms |
| `mod_p384` | 50 ms | 32 ms |
| `mod_p256_nat` | under 10 ms | 1 ms |
| `cert_sub_eq_mul` | 10 ms | 1 ms |
| `edwards_closure` | 110 ms | 41 ms |
| `rcb_affine_x` | 120 ms | 60 ms |
| `rcb_affine_y` | 220 ms | 109 ms |
| `rcb_projective_x` | 160 ms | 80 ms |
| `rcb_projective_y` | 310 ms | 153 ms |

`deg12` normalizes `(x + y + z + w) ^ 12`, 455 terms, through products of
that size, so the kernel time grows with the terms the normal forms reach.
The curve identities have 4 to 6 variables and 256-bit coefficients and
take a few hundred milliseconds or less.

Elaborating the statements costs more than proving some of them: `xyz6`'s
statement, with 28 terms of `x ^ k`, takes about a second before the
tactic runs (see "Failures and cost" in `C3BootProofs.Ring.Tactic`).

The axioms of every theorem and instance in `C3BootProofs.Ring.Basic` and
`C3BootProofs.Ring.Tactic` are pinned at the end, too.
-/

namespace C3.Ring.Test

/-- The P-256 field prime. -/
def p256 : Int := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

/-- P-256's `b`. -/
def b256 : Int := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

/-- The P-384 field prime. -/
def p384 : Int := 2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1

/-- The Curve25519 field prime. -/
def p25519 : Int := 2 ^ 255 - 19

/-- Ed25519's `d`, `-121665 / 121666` modulo `p25519`. -/
def d25519 : Int :=
  37095705934669439343138083508754565189542113879843219016388785533085940283555

theorem atoms (x y : Int) (f : Int → Int) (n : Nat) :
    f x * (y + -x ^ n) + 0 = f x * y - x ^ n * f x := by
  ring_eq

theorem nat_numerals (a : Nat) : (a + 1) ^ 3 = a ^ 3 + 3 * a ^ 2 + 3 * a + 1 := by
  ring_eq

theorem mod_zero (x : Int) : (7 * x + 14) ^ 2 % 7 = 0 := by
  ring_mod

theorem mod_zero_nat (x : Nat) : (7 * x + 14) ^ 2 % 7 = 0 := by
  ring_mod

theorem cofactor_nat_exponents (x₁ y₁ x₂ y₂ : Int)
    (h₁ : (y₁ ^ 2 - x₁ ^ 3 - 7) % 101 = 0) (h₂ : (y₂ ^ 2 - x₂ ^ 3 - 7) % 101 = 0) :
    (y₁ ^ 2 * y₂ ^ 2) % 101 = ((x₁ ^ 3 + 7) * (x₂ ^ 3 + 7)) % 101 := by
  ring_mod [h₁ * (x₂ ^ (3 : Nat) + 7), h₂ * (y₁ ^ (2 : Nat))]

theorem xyz6 (x y z : Int) :
    (x + y + z) ^ 6 =
      x ^ 6 + 6 * x ^ 5 * y + 6 * x ^ 5 * z + 15 * x ^ 4 * y ^ 2 + 30 * x ^ 4 * y * z + 15 * x ^ 4 * z ^ 2 + 20 * x ^ 3 * y ^ 3 + 60 * x ^ 3 * y ^ 2 * z + 60 * x ^ 3 * y * z ^ 2 + 20 * x ^ 3 * z ^ 3 + 15 * x ^ 2 * y ^ 4 + 60 * x ^ 2 * y ^ 3 * z + 90 * x ^ 2 * y ^ 2 * z ^ 2 + 60 * x ^ 2 * y * z ^ 3 + 15 * x ^ 2 * z ^ 4 + 6 * x * y ^ 5 + 30 * x * y ^ 4 * z + 60 * x * y ^ 3 * z ^ 2 + 60 * x * y ^ 2 * z ^ 3 + 30 * x * y * z ^ 4 + 6 * x * z ^ 5 + y ^ 6 + 6 * y ^ 5 * z + 15 * y ^ 4 * z ^ 2 + 20 * y ^ 3 * z ^ 3 + 15 * y ^ 2 * z ^ 4 + 6 * y * z ^ 5 + z ^ 6 := by
  ring_eq

theorem xyz6_nat (x y z : Nat) :
    (x + y + z) ^ 6 =
      x ^ 6 + 6 * x ^ 5 * y + 6 * x ^ 5 * z + 15 * x ^ 4 * y ^ 2 + 30 * x ^ 4 * y * z + 15 * x ^ 4 * z ^ 2 + 20 * x ^ 3 * y ^ 3 + 60 * x ^ 3 * y ^ 2 * z + 60 * x ^ 3 * y * z ^ 2 + 20 * x ^ 3 * z ^ 3 + 15 * x ^ 2 * y ^ 4 + 60 * x ^ 2 * y ^ 3 * z + 90 * x ^ 2 * y ^ 2 * z ^ 2 + 60 * x ^ 2 * y * z ^ 3 + 15 * x ^ 2 * z ^ 4 + 6 * x * y ^ 5 + 30 * x * y ^ 4 * z + 60 * x * y ^ 3 * z ^ 2 + 60 * x * y ^ 2 * z ^ 3 + 30 * x * y * z ^ 4 + 6 * x * z ^ 5 + y ^ 6 + 6 * y ^ 5 * z + 15 * y ^ 4 * z ^ 2 + 20 * y ^ 3 * z ^ 3 + 15 * y ^ 2 * z ^ 4 + 6 * y * z ^ 5 + z ^ 6 := by
  ring_eq

theorem deg12 (x y z w : Int) : ((x + y + z + w) ^ 3) ^ 4 = (x + y + z + w) ^ 12 := by
  ring_eq

theorem big_constant (x : Int) :
    (x + p384) ^ 4 - x ^ 4 =
      p384 * (4 * x ^ 3 + 6 * x ^ 2 * p384 + 4 * x * p384 ^ 2 + p384 ^ 3) := by
  ring_eq

theorem mod_p384 (x y z : Int) :
    (x * y + p384 * z) ^ 3 % p384 = (x * y) ^ 3 % p384 := by
  dsimp only [p384]
  ring_mod

theorem mod_p256_nat (x y : Nat) :
    (x + 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff * y) ^ 2 %
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff =
      x ^ 2 % 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff := by
  ring_mod

theorem cert_sub_eq_mul (x y : Int) :
    (x ^ 2 + p256 * x * y) % p256 = x ^ 2 % p256 :=
  emod_eq_of_sub_eq_mul (k := x * y) (by ring_eq)

/-- Edwards addition is closed on Ed25519 (`a = -1`): with denominators
cleared, the sum of two points on the curve satisfies the curve equation. -/
theorem edwards_closure (x₁ y₁ x₂ y₂ : Int)
    (h1 : (-x₁ ^ 2 + y₁ ^ 2 - 1 - d25519 * x₁ ^ 2 * y₁ ^ 2) % p25519 = 0)
    (h2 : (-x₂ ^ 2 + y₂ ^ 2 - 1 - d25519 * x₂ ^ 2 * y₂ ^ 2) % p25519 = 0) :
    let t := d25519 * x₁ * x₂ * y₁ * y₂
    let x := x₁ * y₂ + y₁ * x₂
    let y := y₁ * y₂ + x₁ * x₂
    (-x ^ 2 * (1 - t) ^ 2 + y ^ 2 * (1 + t) ^ 2 - (1 + t) ^ 2 * (1 - t) ^ 2
      - d25519 * x ^ 2 * y ^ 2) % p25519 = 0 := by
  dsimp only [d25519] at h1 h2 ⊢
  ring_mod [h1 * (-23822367343412287473648479214562764352186410588372722838149638232335439264081 * x₁ ^ (2 : Nat) * y₁ ^ (2 : Nat) * x₂ ^ (4 : Nat) * y₂ ^ (4 : Nat) + 1159843021668779879193775521855586647937357759715417654439879720876111806837 * x₁ ^ (2 : Nat) * x₂ ^ (4 : Nat) * y₂ ^ (4 : Nat) - 1159843021668779879193775521855586647937357759715417654439879720876111806837 * y₁ ^ (2 : Nat) * x₂ ^ (4 : Nat) * y₂ ^ (4 : Nat) + 20800338683988658368647408995589388737092878452977063003340006470870624536394 * x₁ ^ (2 : Nat) * x₂ ^ (4 : Nat) * y₂ ^ (2 : Nat) - 20800338683988658368647408995589388737092878452977063003340006470870624536394 * y₁ ^ (2 : Nat) * x₂ ^ (4 : Nat) * y₂ ^ (2 : Nat) - 20800338683988658368647408995589388737092878452977063003340006470870624536394 * x₁ ^ (2 : Nat) * x₂ ^ (2 : Nat) * y₂ ^ (4 : Nat) + 20800338683988658368647408995589388737092878452977063003340006470870624536394 * y₁ ^ (2 : Nat) * x₂ ^ (2 : Nat) * y₂ ^ (4 : Nat) - 15135524229012001095296898991309589804511877667150738358608899341339203940324 * x₂ ^ (4 : Nat) * y₂ ^ (4 : Nat) - 2 * x₂ ^ (4 : Nat) * y₂ ^ (2 : Nat) + 2 * x₂ ^ (2 : Nat) * y₂ ^ (4 : Nat) + x₂ ^ (4 : Nat) - 16295367250680780974490674513165176452449235426866156013048779062215315747165 * x₂ ^ (2 : Nat) * y₂ ^ (2 : Nat) + y₂ ^ (4 : Nat)), h2 * (-20800338683988658368647408995589388737092878452977063003340006470870624536394 * x₁ ^ (4 : Nat) * x₂ ^ (2 : Nat) * y₂ ^ (2 : Nat) - 20800338683988658368647408995589388737092878452977063003340006470870624536394 * y₁ ^ (4 : Nat) * x₂ ^ (2 : Nat) * y₂ ^ (2 : Nat) + 16295367250680780974490674513165176452449235426866156013048779062215315747163 * x₁ ^ (2 : Nat) * x₂ ^ (2 : Nat) * y₂ ^ (2 : Nat) - 16295367250680780974490674513165176452449235426866156013048779062215315747163 * y₁ ^ (2 : Nat) * x₂ ^ (2 : Nat) * y₂ ^ (2 : Nat) - x₁ ^ (2 : Nat) * x₂ ^ (2 : Nat) + y₁ ^ (2 : Nat) * x₂ ^ (2 : Nat) + x₁ ^ (2 : Nat) * y₂ ^ (2 : Nat) - y₁ ^ (2 : Nat) * y₂ ^ (2 : Nat) - 20800338683988658368647408995589388737092878452977063003340006470870624536392 * x₂ ^ (2 : Nat) * y₂ ^ (2 : Nat) - x₂ ^ (2 : Nat) + y₂ ^ (2 : Nat) + 1)]

/-- Renes, Costello, and Batina's complete addition for `a = -3`
(Algorithm 4 of "Complete addition formulas for prime order elliptic
curves", 2015), on projective coordinates. -/
def rcbAdd (b X1 Y1 Z1 X2 Y2 Z2 : Int) : Int × Int × Int :=
  let t0 := X1 * X2
  let t1 := Y1 * Y2
  let t2 := Z1 * Z2
  let t3 := X1 + Y1
  let t4 := X2 + Y2
  let t3 := t3 * t4
  let t4 := t0 + t1
  let t3 := t3 - t4
  let t4 := Y1 + Z1
  let X3 := Y2 + Z2
  let t4 := t4 * X3
  let X3 := t1 + t2
  let t4 := t4 - X3
  let X3 := X1 + Z1
  let Y3 := X2 + Z2
  let X3 := X3 * Y3
  let Y3 := t0 + t2
  let Y3 := X3 - Y3
  let Z3 := b * t2
  let X3 := Y3 - Z3
  let Z3 := X3 + X3
  let X3 := X3 + Z3
  let Z3 := t1 - X3
  let X3 := t1 + X3
  let Y3 := b * Y3
  let t1 := t2 + t2
  let t2 := t1 + t2
  let Y3 := Y3 - t2
  let Y3 := Y3 - t0
  let t1 := Y3 + Y3
  let Y3 := t1 + Y3
  let t1 := t0 + t0
  let t0 := t1 + t0
  let t0 := t0 - t2
  let t1 := t4 * Y3
  let t2 := t0 * Y3
  let Y3 := X3 * Z3
  let Y3 := Y3 + t2
  let X3 := t3 * X3
  let X3 := X3 - t1
  let Z3 := t4 * Z3
  let t1 := t3 * t0
  let Z3 := Z3 + t1
  (X3, Y3, Z3)

/-- On affine inputs, `rcbAdd`'s `X / Z` is the chord rule's `x`. -/
theorem rcb_affine_x (x1 y1 x2 y2 : Int)
    (h1 : (y1 ^ 2 - x1 ^ 3 + 3 * x1 - b256) % p256 = 0)
    (h2 : (y2 ^ 2 - x2 ^ 3 + 3 * x2 - b256) % p256 = 0) :
    ((rcbAdd b256 x1 y1 1 x2 y2 1).1 * (x2 - x1) ^ 2) % p256 =
      ((rcbAdd b256 x1 y1 1 x2 y2 1).2.2 *
        ((y2 - y1) ^ 2 - (x1 + x2) * (x2 - x1) ^ 2)) % p256 := by
  dsimp only [rcbAdd, b256] at h1 h2 ⊢
  ring_mod [h1 * (-3 * x1 * y1 * x2 ^ (2 : Nat) + 3 * y1 * x2 ^ (3 : Nat) - 3 * x1 ^ (2 : Nat) * x2 * y2 + 3 * x1 * x2 ^ (2 : Nat) * y2 + 3 * x2 ^ (3 : Nat) * y2 - y1 ^ (2 : Nat) * y2 - 2 * y1 * y2 ^ (2 : Nat) + 3 * x1 * y1 - 3 * y1 * x2 + 3 * x1 * y2 - 12 * x2 * y2 + 7383001965100177625280942390734231697257179632690862468972137633251304349922 * y2), h2 * (3 * x1 ^ (2 : Nat) * y1 * x2 - 3 * x1 * y1 * x2 ^ (2 : Nat) - 3 * x1 ^ (2 : Nat) * x2 * y2 + 3 * y1 ^ (3 : Nat) + y1 ^ (2 : Nat) * y2 - y1 * y2 ^ (2 : Nat) - 3 * x1 * y1 + 3 * y1 * x2 + 6 * x1 * y2 + 3 * x2 * y2 - 7383001965100177625280942390734231697257179632690862468972137633251304349922 * y2)]

/-- On affine inputs, `rcbAdd`'s `Y / Z` is the chord rule's `y`. -/
theorem rcb_affine_y (x1 y1 x2 y2 : Int)
    (h1 : (y1 ^ 2 - x1 ^ 3 + 3 * x1 - b256) % p256 = 0)
    (h2 : (y2 ^ 2 - x2 ^ 3 + 3 * x2 - b256) % p256 = 0) :
    ((rcbAdd b256 x1 y1 1 x2 y2 1).2.1 * (x2 - x1) ^ 3) % p256 =
      ((rcbAdd b256 x1 y1 1 x2 y2 1).2.2 *
        ((y2 - y1) * (x1 * (x2 - x1) ^ 2 - ((y2 - y1) ^ 2 - (x1 + x2) * (x2 - x1) ^ 2))
          - y1 * (x2 - x1) ^ 3)) % p256 := by
  dsimp only [rcbAdd, b256] at h1 h2 ⊢
  ring_mod [h1 * (-3 * x1 * y1 ^ (2 : Nat) * x2 ^ (2 : Nat) - 3 * x1 ^ (2 : Nat) * y1 * x2 * y2 + 6 * x1 * y1 * x2 ^ (2 : Nat) * y2 + 6 * x1 ^ (2 : Nat) * x2 * y2 ^ (2 : Nat) - 9 * x1 * x2 ^ (2 : Nat) * y2 ^ (2 : Nat) - 9 * x1 ^ (2 : Nat) * x2 ^ (2 : Nat) + 27 * x1 * x2 ^ (3 : Nat) - 27 * x2 ^ (4 : Nat) - y1 ^ (3 : Nat) * y2 + 2 * y1 ^ (2 : Nat) * y2 ^ (2 : Nat) + 2 * y1 * y2 ^ (3 : Nat) + 3 * x1 * y1 ^ (2 : Nat) + 22149005895300532875842827172202695091771538898072587406916412899753913049766 * x1 ^ (2 : Nat) * x2 + 6 * y1 ^ (2 : Nat) * x2 - 44298011790601065751685654344405390183543077796145174813832825799507826099532 * x1 * x2 ^ (2 : Nat) - 9 * y1 * x2 * y2 - 12 * x1 * y2 ^ (2 : Nat) + 30 * x2 * y2 ^ (2 : Nat) - 9 * x1 ^ (2 : Nat) - 7383001965100177625280942390734231697257179632690862468972137633251304349922 * y1 ^ (2 : Nat) - 9 * x1 * x2 + 45 * x2 ^ (2 : Nat) + 7383001965100177625280942390734231697257179632690862468972137633251304349922 * y1 * y2 + 14766003930200355250561884781468463394514359265381724937944275266502608699844 * y2 ^ (2 : Nat) + 22149005895300532875842827172202695091771538898072587406916412899753913049766 * x1 + 22149005895300532875842827172202695091771538898072587406916412899753913049766 * x2 - 25555177184827196577817035637622321028039128952880116173690298809461776703487), h2 * (9 * x1 ^ (2 : Nat) * y1 ^ (2 : Nat) * x2 - 6 * x1 * y1 ^ (2 : Nat) * x2 ^ (2 : Nat) - 6 * x1 ^ (2 : Nat) * y1 * x2 * y2 + 3 * x1 * y1 * x2 ^ (2 : Nat) * y2 + 3 * x1 ^ (2 : Nat) * x2 * y2 ^ (2 : Nat) + 9 * x1 ^ (2 : Nat) * x2 ^ (2 : Nat) - 2 * y1 ^ (3 : Nat) * y2 - 2 * y1 ^ (2 : Nat) * y2 ^ (2 : Nat) + y1 * y2 ^ (3 : Nat) - 3 * x1 * y1 ^ (2 : Nat) + 44298011790601065751685654344405390183543077796145174813832825799507826099532 * x1 ^ (2 : Nat) * x2 - 15 * y1 ^ (2 : Nat) * x2 - 22149005895300532875842827172202695091771538898072587406916412899753913049766 * x1 * x2 ^ (2 : Nat) + 9 * x1 * y1 * y2 - 6 * x1 * y2 ^ (2 : Nat) - 3 * x2 * y2 ^ (2 : Nat) + 36 * x1 ^ (2 : Nat) - 14766003930200355250561884781468463394514359265381724937944275266502608699844 * y1 ^ (2 : Nat) - 72 * x1 * x2 + 9 * x2 ^ (2 : Nat) - 7383001965100177625280942390734231697257179632690862468972137633251304349922 * y1 * y2 + 7383001965100177625280942390734231697257179632690862468972137633251304349922 * y2 ^ (2 : Nat) + 27196065629154117259326138260596793162999987822999964567867979709851445654887 * x1 + 44298011790601065751685654344405390183543077796145174813832825799507826099532 * x2 + 25555177184827196577817035637622321028039128952880116173690298809461776703487)]

/-- On projective inputs, `rcbAdd`'s `X / Z` is the chord rule's `x`. -/
theorem rcb_projective_x (X1 Y1 Z1 X2 Y2 Z2 : Int)
    (h1 : (Y1 ^ 2 * Z1 - X1 ^ 3 + 3 * X1 * Z1 ^ 2 - b256 * Z1 ^ 3) % p256 = 0)
    (h2 : (Y2 ^ 2 * Z2 - X2 ^ 3 + 3 * X2 * Z2 ^ 2 - b256 * Z2 ^ 3) % p256 = 0) :
    let U := Y2 * Z1 - Y1 * Z2
    let V := X2 * Z1 - X1 * Z2
    ((rcbAdd b256 X1 Y1 Z1 X2 Y2 Z2).1 * V ^ 2 * Z1 * Z2) % p256 =
      ((rcbAdd b256 X1 Y1 Z1 X2 Y2 Z2).2.2 *
        (U ^ 2 * Z1 * Z2 - (X1 * Z2 + X2 * Z1) * V ^ 2)) % p256 := by
  dsimp only [rcbAdd, b256] at h1 h2 ⊢
  ring_mod [h1 * (3 * Z1 ^ (2 : Nat) * X2 ^ (3 : Nat) * Y2 * Z2 + 3 * Y1 * Z1 * X2 ^ (3 : Nat) * Z2 ^ (2 : Nat) + 3 * X1 * Z1 * X2 ^ (2 : Nat) * Y2 * Z2 ^ (2 : Nat) - 3 * X1 * Y1 * X2 ^ (2 : Nat) * Z2 ^ (3 : Nat) - 3 * X1 ^ (2 : Nat) * X2 * Y2 * Z2 ^ (3 : Nat) - 12 * Z1 ^ (2 : Nat) * X2 * Y2 * Z2 ^ (3 : Nat) - 2 * Y1 * Z1 * Y2 ^ (2 : Nat) * Z2 ^ (3 : Nat) - 3 * Y1 * Z1 * X2 * Z2 ^ (4 : Nat) - Y1 ^ (2 : Nat) * Y2 * Z2 ^ (4 : Nat) + 3 * X1 * Z1 * Y2 * Z2 ^ (4 : Nat) + 7383001965100177625280942390734231697257179632690862468972137633251304349922 * Z1 ^ (2 : Nat) * Y2 * Z2 ^ (4 : Nat) + 3 * X1 * Y1 * Z2 ^ (5 : Nat)), h2 * (-3 * X1 * Y1 * Z1 ^ (3 : Nat) * X2 ^ (2 : Nat) - 3 * X1 ^ (2 : Nat) * Z1 ^ (3 : Nat) * X2 * Y2 + 3 * Z1 ^ (5 : Nat) * X2 * Y2 - Y1 * Z1 ^ (4 : Nat) * Y2 ^ (2 : Nat) + 3 * X1 ^ (2 : Nat) * Y1 * Z1 ^ (2 : Nat) * X2 * Z2 + 3 * Y1 * Z1 ^ (4 : Nat) * X2 * Z2 + Y1 ^ (2 : Nat) * Z1 ^ (3 : Nat) * Y2 * Z2 + 6 * X1 * Z1 ^ (4 : Nat) * Y2 * Z2 - 7383001965100177625280942390734231697257179632690862468972137633251304349922 * Z1 ^ (5 : Nat) * Y2 * Z2 + 3 * Y1 ^ (3 : Nat) * Z1 ^ (2 : Nat) * Z2 ^ (2 : Nat) - 3 * X1 * Y1 * Z1 ^ (3 : Nat) * Z2 ^ (2 : Nat))]

/-- On projective inputs, `rcbAdd`'s `Y / Z` is the chord rule's `y`. -/
theorem rcb_projective_y (X1 Y1 Z1 X2 Y2 Z2 : Int)
    (h1 : (Y1 ^ 2 * Z1 - X1 ^ 3 + 3 * X1 * Z1 ^ 2 - b256 * Z1 ^ 3) % p256 = 0)
    (h2 : (Y2 ^ 2 * Z2 - X2 ^ 3 + 3 * X2 * Z2 ^ 2 - b256 * Z2 ^ 3) % p256 = 0) :
    let U := Y2 * Z1 - Y1 * Z2
    let V := X2 * Z1 - X1 * Z2
    let N := U ^ 2 * Z1 * Z2 - (X1 * Z2 + X2 * Z1) * V ^ 2
    ((rcbAdd b256 X1 Y1 Z1 X2 Y2 Z2).2.1 * V ^ 3 * Z1 * Z2) % p256 =
      ((rcbAdd b256 X1 Y1 Z1 X2 Y2 Z2).2.2 *
        (U * (X1 * V ^ 2 * Z2 - N) - Y1 * V ^ 3 * Z2)) % p256 := by
  dsimp only [rcbAdd, b256] at h1 h2 ⊢
  ring_mod [h1 * (-27 * Z1 ^ (3 : Nat) * X2 ^ (4 : Nat) * Z2 ^ (2 : Nat) - 9 * X1 * Z1 ^ (2 : Nat) * X2 ^ (2 : Nat) * Y2 ^ (2 : Nat) * Z2 ^ (2 : Nat) + 27 * X1 * Z1 ^ (2 : Nat) * X2 ^ (3 : Nat) * Z2 ^ (3 : Nat) + 6 * X1 * Y1 * Z1 * X2 ^ (2 : Nat) * Y2 * Z2 ^ (3 : Nat) + 6 * X1 ^ (2 : Nat) * Z1 * X2 * Y2 ^ (2 : Nat) * Z2 ^ (3 : Nat) + 30 * Z1 ^ (3 : Nat) * X2 * Y2 ^ (2 : Nat) * Z2 ^ (3 : Nat) + 2 * Y1 * Z1 ^ (2 : Nat) * Y2 ^ (3 : Nat) * Z2 ^ (3 : Nat) - 3 * X1 * Y1 ^ (2 : Nat) * X2 ^ (2 : Nat) * Z2 ^ (4 : Nat) - 9 * X1 ^ (2 : Nat) * Z1 * X2 ^ (2 : Nat) * Z2 ^ (4 : Nat) - 44298011790601065751685654344405390183543077796145174813832825799507826099532 * X1 * Z1 ^ (2 : Nat) * X2 ^ (2 : Nat) * Z2 ^ (4 : Nat) + 45 * Z1 ^ (3 : Nat) * X2 ^ (2 : Nat) * Z2 ^ (4 : Nat) - 3 * X1 ^ (2 : Nat) * Y1 * X2 * Y2 * Z2 ^ (4 : Nat) - 9 * Y1 * Z1 ^ (2 : Nat) * X2 * Y2 * Z2 ^ (4 : Nat) + 2 * Y1 ^ (2 : Nat) * Z1 * Y2 ^ (2 : Nat) * Z2 ^ (4 : Nat) - 12 * X1 * Z1 ^ (2 : Nat) * Y2 ^ (2 : Nat) * Z2 ^ (4 : Nat) + 14766003930200355250561884781468463394514359265381724937944275266502608699844 * Z1 ^ (3 : Nat) * Y2 ^ (2 : Nat) * Z2 ^ (4 : Nat) + 22149005895300532875842827172202695091771538898072587406916412899753913049766 * X1 ^ (2 : Nat) * Z1 * X2 * Z2 ^ (5 : Nat) + 6 * Y1 ^ (2 : Nat) * Z1 * X2 * Z2 ^ (5 : Nat) - 9 * X1 * Z1 ^ (2 : Nat) * X2 * Z2 ^ (5 : Nat) + 22149005895300532875842827172202695091771538898072587406916412899753913049766 * Z1 ^ (3 : Nat) * X2 * Z2 ^ (5 : Nat) - Y1 ^ (3 : Nat) * Y2 * Z2 ^ (5 : Nat) + 7383001965100177625280942390734231697257179632690862468972137633251304349922 * Y1 * Z1 ^ (2 : Nat) * Y2 * Z2 ^ (5 : Nat) + 3 * X1 * Y1 ^ (2 : Nat) * Z2 ^ (6 : Nat) - 9 * X1 ^ (2 : Nat) * Z1 * Z2 ^ (6 : Nat) - 7383001965100177625280942390734231697257179632690862468972137633251304349922 * Y1 ^ (2 : Nat) * Z1 * Z2 ^ (6 : Nat) + 22149005895300532875842827172202695091771538898072587406916412899753913049766 * X1 * Z1 ^ (2 : Nat) * Z2 ^ (6 : Nat) - 25555177184827196577817035637622321028039128952880116173690298809461776703487 * Z1 ^ (3 : Nat) * Z2 ^ (6 : Nat)), h2 * (3 * X1 * Y1 * Z1 ^ (4 : Nat) * X2 ^ (2 : Nat) * Y2 + 3 * X1 ^ (2 : Nat) * Z1 ^ (4 : Nat) * X2 * Y2 ^ (2 : Nat) - 3 * Z1 ^ (6 : Nat) * X2 * Y2 ^ (2 : Nat) + Y1 * Z1 ^ (5 : Nat) * Y2 ^ (3 : Nat) - 6 * X1 * Y1 ^ (2 : Nat) * Z1 ^ (3 : Nat) * X2 ^ (2 : Nat) * Z2 + 9 * X1 ^ (2 : Nat) * Z1 ^ (4 : Nat) * X2 ^ (2 : Nat) * Z2 - 22149005895300532875842827172202695091771538898072587406916412899753913049766 * X1 * Z1 ^ (5 : Nat) * X2 ^ (2 : Nat) * Z2 + 9 * Z1 ^ (6 : Nat) * X2 ^ (2 : Nat) * Z2 - 6 * X1 ^ (2 : Nat) * Y1 * Z1 ^ (3 : Nat) * X2 * Y2 * Z2 - 2 * Y1 ^ (2 : Nat) * Z1 ^ (4 : Nat) * Y2 ^ (2 : Nat) * Z2 - 6 * X1 * Z1 ^ (5 : Nat) * Y2 ^ (2 : Nat) * Z2 + 7383001965100177625280942390734231697257179632690862468972137633251304349922 * Z1 ^ (6 : Nat) * Y2 ^ (2 : Nat) * Z2 + 9 * X1 ^ (2 : Nat) * Y1 ^ (2 : Nat) * Z1 ^ (2 : Nat) * X2 * Z2 ^ (2 : Nat) + 44298011790601065751685654344405390183543077796145174813832825799507826099532 * X1 ^ (2 : Nat) * Z1 ^ (4 : Nat) * X2 * Z2 ^ (2 : Nat) - 15 * Y1 ^ (2 : Nat) * Z1 ^ (4 : Nat) * X2 * Z2 ^ (2 : Nat) - 72 * X1 * Z1 ^ (5 : Nat) * X2 * Z2 ^ (2 : Nat) + 44298011790601065751685654344405390183543077796145174813832825799507826099532 * Z1 ^ (6 : Nat) * X2 * Z2 ^ (2 : Nat) - 2 * Y1 ^ (3 : Nat) * Z1 ^ (3 : Nat) * Y2 * Z2 ^ (2 : Nat) + 9 * X1 * Y1 * Z1 ^ (4 : Nat) * Y2 * Z2 ^ (2 : Nat) - 7383001965100177625280942390734231697257179632690862468972137633251304349922 * Y1 * Z1 ^ (5 : Nat) * Y2 * Z2 ^ (2 : Nat) - 3 * X1 * Y1 ^ (2 : Nat) * Z1 ^ (3 : Nat) * Z2 ^ (3 : Nat) + 36 * X1 ^ (2 : Nat) * Z1 ^ (4 : Nat) * Z2 ^ (3 : Nat) - 14766003930200355250561884781468463394514359265381724937944275266502608699844 * Y1 ^ (2 : Nat) * Z1 ^ (4 : Nat) * Z2 ^ (3 : Nat) + 27196065629154117259326138260596793162999987822999964567867979709851445654887 * X1 * Z1 ^ (5 : Nat) * Z2 ^ (3 : Nat) + 25555177184827196577817035637622321028039128952880116173690298809461776703487 * Z1 ^ (6 : Nat) * Z2 ^ (3 : Nat))]

/-- info: 'C3.Ring.Test.atoms' depends on axioms: [propext] -/
#guard_msgs in #print axioms atoms

/-- info: 'C3.Ring.Test.nat_numerals' depends on axioms: [propext] -/
#guard_msgs in #print axioms nat_numerals

/-- info: 'C3.Ring.Test.mod_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms mod_zero

/-- info: 'C3.Ring.Test.mod_zero_nat' depends on axioms: [propext] -/
#guard_msgs in #print axioms mod_zero_nat

/-- info: 'C3.Ring.Test.cofactor_nat_exponents' depends on axioms: [propext] -/
#guard_msgs in #print axioms cofactor_nat_exponents

/-- info: 'C3.Ring.Test.xyz6' depends on axioms: [propext] -/
#guard_msgs in #print axioms xyz6

/-- info: 'C3.Ring.Test.xyz6_nat' depends on axioms: [propext] -/
#guard_msgs in #print axioms xyz6_nat

/-- info: 'C3.Ring.Test.deg12' depends on axioms: [propext] -/
#guard_msgs in #print axioms deg12

/-- info: 'C3.Ring.Test.big_constant' depends on axioms: [propext] -/
#guard_msgs in #print axioms big_constant

/-- info: 'C3.Ring.Test.mod_p384' depends on axioms: [propext] -/
#guard_msgs in #print axioms mod_p384

/-- info: 'C3.Ring.Test.mod_p256_nat' depends on axioms: [propext] -/
#guard_msgs in #print axioms mod_p256_nat

/-- info: 'C3.Ring.Test.cert_sub_eq_mul' depends on axioms: [propext] -/
#guard_msgs in #print axioms cert_sub_eq_mul

/-- info: 'C3.Ring.Test.edwards_closure' depends on axioms: [propext] -/
#guard_msgs in #print axioms edwards_closure

/-- info: 'C3.Ring.Test.rcb_affine_x' depends on axioms: [propext] -/
#guard_msgs in #print axioms rcb_affine_x

/-- info: 'C3.Ring.Test.rcb_affine_y' depends on axioms: [propext] -/
#guard_msgs in #print axioms rcb_affine_y

/-- info: 'C3.Ring.Test.rcb_projective_x' depends on axioms: [propext] -/
#guard_msgs in #print axioms rcb_projective_x

/-- info: 'C3.Ring.Test.rcb_projective_y' depends on axioms: [propext] -/
#guard_msgs in #print axioms rcb_projective_y

end C3.Ring.Test

/-- info: 'C3.Ring.get_nil' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.get_nil

/-- info: 'C3.Ring.get_cons_zero' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.get_cons_zero

/-- info: 'C3.Ring.get_cons_succ' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.get_cons_succ

/-- info: 'C3.Ring.emod_add_cong' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.emod_add_cong

/-- info: 'C3.Ring.emod_mul_cong' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.emod_mul_cong

/-- info: 'C3.Ring.emod_neg_cong' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.emod_neg_cong

/-- info: 'C3.Ring.emod_pow_cong' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.emod_pow_cong

/-- info: 'C3.Ring.emod_emod_cong' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.emod_emod_cong

/-- info: 'C3.Ring.nat_eq_of_not_lt' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.nat_eq_of_not_lt

/-- info: 'C3.Ring.not_lt_of_blt_false' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.not_lt_of_blt_false

/-- info: 'C3.Ring.intBeq_eq' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.intBeq_eq

/-- info: 'C3.Ring.intIsZero_eq' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.intIsZero_eq

/-- info: 'C3.Ring.Mon.eval_one' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Mon.eval_one

/-- info: 'C3.Ring.Mon.eval_cons' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Mon.eval_cons

/-- info: 'C3.Ring.Mon.mul_one_left' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Mon.mul_one_left

/-- info: 'C3.Ring.Mon.mul_cons_one' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Mon.mul_cons_one

/-- info: 'C3.Ring.Mon.mul_cons_cons' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Mon.mul_cons_cons

/-- info: 'C3.Ring.Mon.eval_mul' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.Mon.eval_mul

/-- info: 'C3.Ring.Poly.eval_zero' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Poly.eval_zero

/-- info: 'C3.Ring.Poly.eval_term' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Poly.eval_term

/-- info: 'C3.Ring.Poly.eval_mkTerm' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.Poly.eval_mkTerm

/-- info: 'C3.Ring.Poly.eval_monomial' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.Poly.eval_monomial

/-- info: 'C3.Ring.Poly.add_zero_left' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Poly.add_zero_left

/-- info: 'C3.Ring.Poly.add_term_zero' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Poly.add_term_zero

/-- info: 'C3.Ring.Poly.add_term_term' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Poly.add_term_term

/-- info: 'C3.Ring.Mon.cmp_cons_cons' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Mon.cmp_cons_cons

/-- info: 'C3.Ring.Mon.eq_of_cmp_eq' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Mon.eq_of_cmp_eq

/-- info: 'C3.Ring.Poly.eval_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.Poly.eval_add

/-- info: 'C3.Ring.Poly.mulTerm_zero' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Poly.mulTerm_zero

/-- info: 'C3.Ring.Poly.mulTerm_term' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Poly.mulTerm_term

/-- info: 'C3.Ring.Poly.eval_mulTerm' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.Poly.eval_mulTerm

/-- info: 'C3.Ring.Poly.mul_zero_left' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Poly.mul_zero_left

/-- info: 'C3.Ring.Poly.mul_term' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Poly.mul_term

/-- info: 'C3.Ring.Poly.eval_mul' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.Poly.eval_mul

/-- info: 'C3.Ring.Poly.eval_neg' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.Poly.eval_neg

/-- info: 'C3.Ring.Poly.pow_zero' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Poly.pow_zero

/-- info: 'C3.Ring.Poly.pow_succ' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Poly.pow_succ

/-- info: 'C3.Ring.Poly.eval_pow' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.Poly.eval_pow

/-- info: 'C3.Ring.Expr.eval_const' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Expr.eval_const

/-- info: 'C3.Ring.Expr.eval_var' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Expr.eval_var

/-- info: 'C3.Ring.Expr.eval_add' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Expr.eval_add

/-- info: 'C3.Ring.Expr.eval_sub' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Expr.eval_sub

/-- info: 'C3.Ring.Expr.eval_neg' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Expr.eval_neg

/-- info: 'C3.Ring.Expr.eval_mul' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Expr.eval_mul

/-- info: 'C3.Ring.Expr.eval_pow' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Expr.eval_pow

/-- info: 'C3.Ring.Expr.toPoly_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.Expr.toPoly_sound

/-- info: 'C3.Ring.Mon.eq_of_beq' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Mon.eq_of_beq

/-- info: 'C3.Ring.Poly.eq_of_beq' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.Poly.eq_of_beq

/-- info: 'C3.Ring.emod_eq_of_beq' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.emod_eq_of_beq

/-- info: 'C3.Ring.eq_of_beq' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.eq_of_beq

/-- info: 'C3.Ring.emod_eq_of_sub_eq_mul' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.emod_eq_of_sub_eq_mul

/-- info: 'C3.Ring.emod_eq_of_emod_eq_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.emod_eq_of_emod_eq_add

/-- info: 'C3.Ring.emod_add_eq_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.emod_add_eq_zero

/-- info: 'C3.Ring.emod_mul_eq_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.emod_mul_eq_zero

/-- info: 'C3.Ring.emod_eq_zero_of_emod_eq' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.emod_eq_zero_of_emod_eq

/-- info: 'C3.Ring.nat_emod_eq_zero_of_emod_eq' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.nat_emod_eq_zero_of_emod_eq

/-- info: 'C3.Ring.nat_emod_eq_of_int' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.nat_emod_eq_of_int

/-- info: 'C3.Ring.get_append_length' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.get_append_length

/-- info: 'C3.Ring.lenNil' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.lenNil

/-- info: 'C3.Ring.lenCons' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.lenCons

/-- info: 'C3.Ring.findHead' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.findHead

/-- info: 'C3.Ring.findTail' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.findTail

/-- info: 'C3.Ring.ReifyInt.sound_of_ext' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.ReifyInt.sound_of_ext

/-- info: 'C3.Ring.ext_trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.ext_trans

/-- info: 'C3.Ring.ReifyInt.binop' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.ReifyInt.binop

/-- info: 'C3.Ring.ReifyInt.unop' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.ReifyInt.unop

/-- info: 'C3.Ring.reifyAdd' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.reifyAdd

/-- info: 'C3.Ring.reifySub' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.reifySub

/-- info: 'C3.Ring.reifyMul' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.reifyMul

/-- info: 'C3.Ring.reifyNeg' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.reifyNeg

/-- info: 'C3.Ring.isNumeralZero' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.isNumeralZero

/-- info: 'C3.Ring.isNumeralSucc' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.isNumeralSucc

/-- info: 'C3.Ring.reifyPow' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.reifyPow

/-- info: 'C3.Ring.reifyZero' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.reifyZero

/-- info: 'C3.Ring.reifySucc' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.reifySucc

/-- info: 'C3.Ring.reifyNatCastAdd' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.reifyNatCastAdd

/-- info: 'C3.Ring.reifyNatCastMul' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.reifyNatCastMul

/-- info: 'C3.Ring.reifyNatCastPow' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.reifyNatCastPow

/-- info: 'C3.Ring.reifyNatCastZero' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.reifyNatCastZero

/-- info: 'C3.Ring.reifyNatCastSucc' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.reifyNatCastSucc

/-- info: 'C3.Ring.reifyOldAtom' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.reifyOldAtom

/-- info: 'C3.Ring.reifyNewAtom' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.reifyNewAtom

/-- info: 'C3.Ring.RingEq.eq' does not depend on any axioms -/
#guard_msgs in #print axioms C3.Ring.RingEq.eq

/-- info: 'C3.Ring.reify_eval' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.reify_eval

/-- info: 'C3.Ring.ringEqInt' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.ringEqInt

/-- info: 'C3.Ring.ringEqNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.ringEqNat

/-- info: 'C3.Ring.ringModInt' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.ringModInt

/-- info: 'C3.Ring.ringModIntZero' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.ringModIntZero

/-- info: 'C3.Ring.ringModNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.ringModNat

/-- info: 'C3.Ring.ringModNatZero' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Ring.ringModNatZero
