import C3BootProofs.Proofs.FieldDouble

/-!
# The P-256 field operations as functions, and complete point addition

The compiled field operations work on numbers below `p` in Montgomery form:
`multiply` returns `a · b · 2^-256 mod p`. These are those operations as
functions on such numbers, and `ptAddSpec` is `primeorder`'s complete
addition (Renes, Costello, and Batina 2015, algorithm 4, for `a = -3`) in
them, in the order of its Rust source.
-/

namespace C3.RV32

/-- `2^-256 mod p`. -/
def rInv : Nat := 115792089183396302114378112356516095823261736990586219612555396166510339686400

/-- The Montgomery product `a · b · 2^-256 mod p`. -/
def fm (a b : Nat) : Nat := a * b * rInv % p256

def fa (a b : Nat) : Nat := (a + b) % p256

def fs (a b : Nat) : Nat := (a + p256 - b) % p256

def fd (a : Nat) : Nat := (a + a) % p256

theorem p256_pos : 0 < p256 := by decide

theorem fm_lt (a b : Nat) : fm a b < p256 := Nat.mod_lt _ p256_pos
theorem fa_lt (a b : Nat) : fa a b < p256 := Nat.mod_lt _ p256_pos
theorem fs_lt (a b : Nat) : fs a b < p256 := Nat.mod_lt _ p256_pos
theorem fd_lt (a : Nat) : fd a < p256 := Nat.mod_lt _ p256_pos

set_option exponentiation.threshold 600 in
/-- `multiply`'s result as the Montgomery product: below `p`, and `2^256`
times it is the operands' product modulo `p`. -/
theorem mont_fm {R A B : Nat} (hR : R < p256) (h : (R * 2 ^ 256) % p256 = (A * B) % p256) : R = fm A B := by
  have hinv : (2 ^ 256 * rInv) % p256 = 1 := rfl
  unfold fm
  calc R = R % p256 := (Nat.mod_eq_of_lt hR).symm
    _ = (R * ((2 ^ 256 * rInv) % p256)) % p256 := by rw [hinv, Nat.mul_one]
    _ = (R * 2 ^ 256 * rInv) % p256 := by rw [Nat.mul_mod_mod, Nat.mul_assoc]
    _ = ((R * 2 ^ 256) % p256 * rInv) % p256 := by rw [Nat.mod_mul_mod]
    _ = ((A * B) % p256 * rInv) % p256 := by rw [h]
    _ = (A * B * rInv) % p256 := by rw [Nat.mod_mul_mod]

set_option exponentiation.threshold 600 in
theorem mul_lt_mont {A B : Nat} (hA : A < p256) (hB : B < p256) : A * B < p256 * 2 ^ 256 :=
  Nat.mul_lt_mul_of_lt_of_lt hA (Nat.lt_trans hB (by decide))

theorem fa_eq {A B : Nat} (hA : A < p256) (hB : B < p256) : subRes (A + B) = fa A B := subRes_add hA hB

theorem fs_eq {A B : Nat} (hA : A < p256) (hB : B < p256) : subGen A B = fs A B := subGen_field hA hB

theorem fd_eq {A : Nat} (hA : A < p256) : subRes (A + A) = fd A := subRes_add hA hA

/-- Complete point addition for `a = -3`, in the order of `primeorder`'s
`add_assign`, with `b` the curve constant in Montgomery form. -/
def ptAddSpec (bM x1 y1 z1 x2 y2 z2 : Nat) : Nat × Nat × Nat :=
  let xx := fm x1 x2
  let yy := fm y1 y2
  let zz := fm z1 z2
  let xyPairs := fs (fm (fa x1 y1) (fa x2 y2)) (fa xx yy)
  let yzPairs := fs (fm (fa y1 z1) (fa y2 z2)) (fa yy zz)
  let xzPairs := fs (fm (fa x1 z1) (fa x2 z2)) (fa xx zz)
  let bzzPart := fs xzPairs (fm bM zz)
  let bzz3Part := fa (fd bzzPart) bzzPart
  let yyMBzz3 := fs yy bzz3Part
  let yyPBzz3 := fa yy bzz3Part
  let zz3 := fa (fd zz) zz
  let bxzPart := fs (fm bM xzPairs) (fa zz3 xx)
  let bxz3Part := fa (fd bxzPart) bxzPart
  let xx3MZz3 := fs (fa (fd xx) xx) zz3
  (fs (fm yyPBzz3 xyPairs) (fm yzPairs bxz3Part),
   fa (fm yyPBzz3 yyMBzz3) (fm xx3MZz3 bxz3Part),
   fa (fm yyMBzz3 yzPairs) (fm xyPairs xx3MZz3))

end C3.RV32
