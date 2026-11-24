import C3BootProofs.Models.P256BarrettChain
import C3BootProofs.Models.P256Model

/-!
# P-256's compiled `barrett_reduce` reduces modulo `n`

`P256BarrettChain` gives each stage of the compiled reduction as an
identity. With `q1` the input's limbs 7 to 15, `q3` is
`⌊q1 ⌊2 ^ 512 / n⌋ / 2 ^ 288⌋`, and for an input `X < n * n`,
`barrett_lo` and `barrett_hi` bound `X - q3 n` to `[0, 2n)`: one
conditional subtraction of `n` is enough. `psmVal_eq` joins the stages, and
`p256PsmOk` is `P256PsmOk`.
-/

namespace C3.Models

open C3.RV32 C3.RV32.Sv

local notation "nP" => 115792089210356248762697446949407573529996955224135760342422259061068512044369
local notation "muP" => 115792089264276142090721624801893421302707618245269942344307673200490803338238
local notation "w7" => 26959946667150639794667015087019630673637144422540572481103610249216
local notation "w8" => 115792089237316195423570985008687907853269984665640564039457584007913129639936
local notation "w9" => 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056

theorem barrett_lo {X q1 x0 q3 L : Nat} (hX : X = x0 + w7 * q1) (hL : L < w9)
    (hQ : q1 * muP = L + w9 * q3) : q3 * nP ≤ X := by
  omega

theorem barrett_hi {X q1 x0 q3 L : Nat} (hX : X = x0 + w7 * q1) (hx0 : x0 < w7)
    (hXn : X < nP * nP) (hL : L < w9) (hQ : q1 * muP = L + w9 * q3) : X < q3 * nP + 2 * nP := by
  omega

theorem barrett_diff {X q3 R1 R2 hi xh U c : Nat} (hB : q3 * nP = R2 + w9 * hi)
    (hU : R1 + w9 * c = U + R2) (hUl : U < w9) (hX : X = R1 + w9 * xh) (h1 : q3 * nP ≤ X) (h2 : X < q3 * nP + 2 * nP) : U + q3 * nP = X := by
  omega

theorem barrett_sel {X q3 U c V8 d8 out h : Nat} (hu : U + q3 * nP = X)
    (h2 : X < q3 * nP + 2 * nP) (hV : U + w9 * c = V8 + w8 * d8 + nP)
    (hS : V8 + nP * c = out + w8 * h) (hV8 : V8 < w8) (hd8 : d8 < 2 ^ 32) (hout : out < w8)
    (hc : c ≤ 1) : out = X % nP := by
  cases c with
  | zero =>
    obtain rfl : d8 = 0 := by omega
    obtain rfl : h = 0 := by omega
    have e : X = out + nP * (q3 + 1) := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  | succ c =>
    obtain rfl : c = 0 := by omega
    have hU : U < nP := by omega
    have e : X = out + nP * q3 := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem psmProd_lt (X i : Nat) : psmProd X i < 2 ^ 32 := by
  unfold psmProd
  by_cases h : i < 16
  · rw [ite_eq_left h]; exact Nat.mod_lt _ (by decide)
  · rw [ite_eq_right h]; decide

theorem mod_mul_eq (X a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    X % (a * b) = X % a + a * (X / a % b) := by
  have h1 : X = X % a + a * (X / a % b) + a * b * (X / a / b) :=
    calc X = X % a + a * (X / a) := (Nat.mod_add_div X a).symm
      _ = X % a + a * (X / a % b + b * (X / a / b)) := by rw [Nat.mod_add_div (X / a) b]
      _ = _ := by ring_eq
  have h2 : X % a + a * (X / a % b) < a * b := by
    have := Nat.mod_lt X ha
    have h3 : a * (X / a % b + 1) ≤ a * b := Nat.mul_le_mul_left a (Nat.mod_lt _ hb)
    rw [Nat.mul_succ] at h3
    omega
  rw [congrArg (· % (a * b)) h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]

theorem psmProd_step (X k : Nat) (hk : k < 16) :
    X % 2 ^ (32 * (k + 1)) = X % 2 ^ (32 * k) + 2 ^ (32 * k) * psmProd X k := by
  rw [psmProd, ite_eq_left hk, show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add,
    mod_mul_eq X _ _ (Nat.two_pow_pos _) (Nat.two_pow_pos _)]

set_option exponentiation.threshold 600 in
/-- The input in limbs: `X` is `x0 + 2 ^ 224 q1` and `r1 + 2 ^ 288 xh`. -/
theorem psmProd_split (X : Nat) (hX : X < 2 ^ 512) :
    X = (psmProd X 0 + 4294967296 * psmProd X 1 + 18446744073709551616 * psmProd X 2 +
      79228162514264337593543950336 * psmProd X 3 +
      340282366920938463463374607431768211456 * psmProd X 4 +
      1461501637330902918203684832716283019655932542976 * psmProd X 5 +
      6277101735386680763835789423207666416102355444464034512896 * psmProd X 6) +
      w7 * bQ1 (psmProd X) ∧
    X = bR1 (psmProd X) + w9 * (psmProd X 9 + 4294967296 * psmProd X 10 +
      18446744073709551616 * psmProd X 11 + 79228162514264337593543950336 * psmProd X 12 +
      340282366920938463463374607431768211456 * psmProd X 13 +
      1461501637330902918203684832716283019655932542976 * psmProd X 14 +
      6277101735386680763835789423207666416102355444464034512896 * psmProd X 15) := by
  have e0 : X % 2 ^ 32 = X % 2 ^ 0 + 2 ^ 0 * psmProd X 0 := psmProd_step X 0 (by decide)
  have e1 : X % 2 ^ 64 = X % 2 ^ 32 + 2 ^ 32 * psmProd X 1 := psmProd_step X 1 (by decide)
  have e2 : X % 2 ^ 96 = X % 2 ^ 64 + 2 ^ 64 * psmProd X 2 := psmProd_step X 2 (by decide)
  have e3 : X % 2 ^ 128 = X % 2 ^ 96 + 2 ^ 96 * psmProd X 3 := psmProd_step X 3 (by decide)
  have e4 : X % 2 ^ 160 = X % 2 ^ 128 + 2 ^ 128 * psmProd X 4 := psmProd_step X 4 (by decide)
  have e5 : X % 2 ^ 192 = X % 2 ^ 160 + 2 ^ 160 * psmProd X 5 := psmProd_step X 5 (by decide)
  have e6 : X % 2 ^ 224 = X % 2 ^ 192 + 2 ^ 192 * psmProd X 6 := psmProd_step X 6 (by decide)
  have e7 : X % 2 ^ 256 = X % 2 ^ 224 + 2 ^ 224 * psmProd X 7 := psmProd_step X 7 (by decide)
  have e8 : X % 2 ^ 288 = X % 2 ^ 256 + 2 ^ 256 * psmProd X 8 := psmProd_step X 8 (by decide)
  have e9 : X % 2 ^ 320 = X % 2 ^ 288 + 2 ^ 288 * psmProd X 9 := psmProd_step X 9 (by decide)
  have e10 : X % 2 ^ 352 = X % 2 ^ 320 + 2 ^ 320 * psmProd X 10 := psmProd_step X 10 (by decide)
  have e11 : X % 2 ^ 384 = X % 2 ^ 352 + 2 ^ 352 * psmProd X 11 := psmProd_step X 11 (by decide)
  have e12 : X % 2 ^ 416 = X % 2 ^ 384 + 2 ^ 384 * psmProd X 12 := psmProd_step X 12 (by decide)
  have e13 : X % 2 ^ 448 = X % 2 ^ 416 + 2 ^ 416 * psmProd X 13 := psmProd_step X 13 (by decide)
  have e14 : X % 2 ^ 480 = X % 2 ^ 448 + 2 ^ 448 * psmProd X 14 := psmProd_step X 14 (by decide)
  have e15 : X % 2 ^ 512 = X % 2 ^ 480 + 2 ^ 480 * psmProd X 15 := psmProd_step X 15 (by decide)
  have z : X % 2 ^ 0 = 0 := Nat.mod_one X
  have t : X % 2 ^ 512 = X := Nat.mod_eq_of_lt hX
  unfold bQ1 bR1
  constructor <;> omega

theorem psmOut_sum (a : Nat → Nat) : limbSum (psmOut a) 8 = bOut a := by
  show 0 + psvS123l a * 2 ^ 0 + psvS124l a * 2 ^ 32 + psvS125l a * 2 ^ 64 +
    psvS126l a * 2 ^ 96 + psvS127l a * 2 ^ 128 + psvS128l a * 2 ^ 160 + psvS129l a * 2 ^ 192 +
    psvS130l a * 2 ^ 224 = _
  unfold bOut
  ring_eq

set_option exponentiation.threshold 600 in
/-- **The compiled `barrett_reduce` reduces modulo `n`** on the products of
two scalars. -/
theorem psmVal_eq (X : Nat) (hX : X < nP * nP) : psmVal X = X % nP := by
  have ha := psmProd_lt X
  have hs := psmProd_split X (Nat.lt_of_lt_of_le hX (by decide))
  have hx0 : psmProd X 0 + 4294967296 * psmProd X 1 + 18446744073709551616 * psmProd X 2 +
      79228162514264337593543950336 * psmProd X 3 +
      340282366920938463463374607431768211456 * psmProd X 4 +
      1461501637330902918203684832716283019655932542976 * psmProd X 5 +
      6277101735386680763835789423207666416102355444464034512896 * psmProd X 6 < w7 := by
    have := ha 0; have := ha 1; have := ha 2; have := ha 3; have := ha 4; have := ha 5
    have := ha 6
    omega
  have h1 := barrett_lo hs.1 (bLowA_lt _) (barrettA _)
  have h2 := barrett_hi hs.1 hx0 hX (bLowA_lt _) (barrettA _)
  have hu := barrett_diff (barrettB _) (barrettU _ ha) (bU_lt _) hs.2
    h1 h2
  show limbSum (psmOut (psmProd X)) 8 = _
  rw [psmOut_sum]
  exact barrett_sel hu h2 (barrettV _) (barrettS _) (bV8_lt _) (lt32 _) (bOut_lt _)
    (bstep_le _ _ _)

theorem p256PsmOk : P256PsmOk := fun X hX => psmVal_eq X hX

end C3.Models
