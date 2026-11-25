/-!
Formal specifications and correctness properties for ESP32-C3 silicon ROM asymmetric crypto routines:
- `ets_rsa_pss_verify` (`mcu-lab/proofs/rom_asm/ets_rsa_pss_verify.asm`)
- `r_ecc_is_valid_point` (`mcu-lab/proofs/rom_asm/r_ecc_is_valid_point.asm`)
- `r_ecc_point_multiplication_win_256` (`mcu-lab/proofs/rom_asm/r_ecc_point_multiplication_win_256.asm`)
-/

namespace Esp32c3Rom.Crypto

/-- Modular exponentiation `base ^ exp % mod` (used by `ets_rsa_pss_verify`). -/
def modPow (base exp mod : Nat) : Nat :=
  if mod ≤ 1 then 0
  else (base ^ exp) % mod

/-- `ets_rsa_pss_verify`: checks `sig < n` and `emsaPssVerify(hash, modPow sig e n)`. -/
def etsRsaPssVerify (n e sig : Nat) (emsaPssVerify : Nat → Bool) : Bool :=
  decide (sig < n) && emsaPssVerify (modPow sig e n)

theorem etsRsaPssVerify_sound (n e sig : Nat) (emsaPssVerify : Nat → Bool)
    (h : etsRsaPssVerify n e sig emsaPssVerify = true) :
    sig < n ∧ emsaPssVerify (modPow sig e n) = true := by
  unfold etsRsaPssVerify at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- `r_ecc_is_valid_point`: short Weierstrass curve `y^2 ≡ x^3 - 3x + b (mod p)`
    with coordinate bounds `x < p` and `y < p`. -/
def isValidPoint (p b x y : Nat) : Bool :=
  decide (x < p) && decide (y < p) &&
    decide ((y * y) % p = (x * x * x + (p - 3 % p) * x + b) % p)

theorem isValidPoint_iff (p b x y : Nat) :
    isValidPoint p b x y = true ↔
      x < p ∧ y < p ∧ (y * y) % p = (x * x * x + (p - 3 % p) * x + b) % p := by
  unfold isValidPoint
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- Abstract group operation for `r_ecc_point_multiplication_win_256`. -/
structure EcGroup (Point : Type) where
  zero : Point
  add : Point → Point → Point
  add_zero : ∀ p, add p zero = p
  zero_add : ∀ p, add zero p = p

/-- Scalar multiplication `k * P` (specification for `r_ecc_point_multiplication_win_256`). -/
def scalarMul {Point : Type} (G : EcGroup Point) (k : Nat) (P : Point) : Point :=
  match k with
  | 0 => G.zero
  | k' + 1 => G.add P (scalarMul G k' P)

theorem scalarMul_zero {Point : Type} (G : EcGroup Point) (P : Point) :
    scalarMul G 0 P = G.zero := rfl

theorem scalarMul_one {Point : Type} (G : EcGroup Point) (P : Point) :
    scalarMul G 1 P = P := by
  simp [scalarMul, G.add_zero]

/-- `ets_emsa_pss_verify`: checks trailer byte `0xBC` and maskedDB/hash consistency. -/
def etsEmsaPssVerify (em : List UInt8) (hLen sLen : Nat) (checkSalt : List UInt8 → Bool) : Bool :=
  match em.getLast? with
  | some 0xBC => decide (em.length ≥ hLen + sLen + 2) && checkSalt em
  | _ => false

theorem etsEmsaPssVerify_trailer (em : List UInt8) (hLen sLen : Nat) (checkSalt : List UInt8 → Bool)
    (h : etsEmsaPssVerify em hLen sLen checkSalt = true) :
    em.getLast? = some 0xBC ∧ em.length ≥ hLen + sLen + 2 := by
  unfold etsEmsaPssVerify at h
  cases hlast : em.getLast? with
  | none => simp [hlast] at h
  | some b =>
    by_cases hbc : b = 0xBC
    · subst hbc
      simp only [hlast, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨rfl, h.1⟩
    · exfalso
      simp [hlast, hbc] at h

/-- Exact ESP32-C3 RSA accelerator MMIO register offsets from `hwcrypto_reg.h`. -/
def rsaMemMBlockOff : UInt32 := 0x000
def rsaMemZBlockOff : UInt32 := 0x200
def rsaMemYBlockOff : UInt32 := 0x400
def rsaMemXBlockOff : UInt32 := 0x600
def rsaMDashRegOff : UInt32 := 0x800
def rsaLengthRegOff : UInt32 := 0x804
def rsaQueryCleanRegOff : UInt32 := 0x808
def rsaModexpStartRegOff : UInt32 := 0x80c
def rsaQueryInterruptRegOff : UInt32 := 0x818
def rsaClearInterruptRegOff : UInt32 := 0x81c

/-- Hardware MMIO state for `ets_bigint_{enable,disable,modexp,wait_finish,getz}`. -/
structure BigintState where
  enabled : Bool
  idle : Bool
  x : Nat
  y : Nat
  m : Nat
  mDash : UInt32
  lengthWords : Nat
  z : Nat

def bigintEnable (s : BigintState) : BigintState := { s with enabled := true, idle := true }
def bigintDisable (s : BigintState) : BigintState := { s with enabled := false, idle := false }
def bigintModexp (s : BigintState) (base exp mod : Nat) (mDash : UInt32) (len : Nat) : BigintState :=
  if s.enabled then
    { s with idle := true, x := base, y := exp, m := mod, mDash := mDash, lengthWords := len,
             z := modPow base exp mod }
  else s

theorem bigintModexp_getz (s : BigintState) (base exp mod : Nat) (mDash : UInt32) (len : Nat) :
    (bigintModexp (bigintEnable s) base exp mod mDash len).z = modPow base exp mod := by
  rfl

end Esp32c3Rom.Crypto
