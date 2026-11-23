import C3BootProofs.Models.Ed25519Group

/-!
# Field values of limb lists, and the curve's concrete constants

`fv` reads ten radix-2^25.5 limbs as a field element modulo `p`, and `Lim`
bounds each limb. The constants `sqrtM1` and `B` are computed in the kernel
through `powModF`, a fuel-bounded `powMod`, so `B` is on the curve by
evaluation.
-/

namespace C3.RV32.EdM

/-- `powMod` with fuel: structural recursion, so the kernel evaluates it. -/
def powModF : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m => 1 % m
  | f + 1, a, e, m =>
    if e = 0 then 1 % m
    else if e % 2 = 1 then powModF f (a * a % m) (e / 2) m * a % m else powModF f (a * a % m) (e / 2) m

theorem powMod_F : ∀ f a e m, e < 2 ^ f → powMod a e m = powModF f a e m
  | 0, a, e, m, h => by
    have : e = 0 := by omega
    subst this; rw [powMod]; rfl
  | f + 1, a, e, m, h => by
    rw [powMod]
    by_cases he : e = 0
    · simp only [he, ↓reduceIte, powModF]
    · simp only [he, ↓reduceIte, powModF]
      rw [powMod_F f (a * a % m) (e / 2) m (by rw [Nat.pow_succ] at h; omega)]

theorem sqrtM1_eq :
    Ed25519.sqrtM1 = 19681161376707505956807079304988542015446066515923890162744021073123829784752 := by
  unfold Ed25519.sqrtM1; rw [powMod_F 255 _ _ _ (by decide)]; decide +kernel

theorem sqrtM1_sq : Ed25519.sqrtM1 * Ed25519.sqrtM1 % Ed25519.p = Ed25519.p - 1 := by
  rw [sqrtM1_eq]; decide +kernel

theorem B_eq : Ed25519.B = (15112221349535400772501151409588531511454012693041857206046113283949847762202,
    46316835694926478169428394003475163141307993866256225615783033603165251855960) := by
  unfold Ed25519.B Ed25519.recoverX
  have h3 : ∀ a, powMod a 3 Ed25519.p = powModF 255 a 3 Ed25519.p := fun a => powMod_F _ _ _ _ (by decide)
  have h7 : ∀ a, powMod a 7 Ed25519.p = powModF 255 a 7 Ed25519.p := fun a => powMod_F _ _ _ _ (by decide)
  have h8 : ∀ a, powMod a ((Ed25519.p - 5) / 8) Ed25519.p = powModF 255 a ((Ed25519.p - 5) / 8) Ed25519.p :=
    fun a => powMod_F _ _ _ _ (by decide)
  simp only [h3, h7, h8, sqrtM1_eq]
  decide +kernel

/-- **The base point is on the curve.** -/
theorem onCurve_B : OnCurve Ed25519.B := by rw [B_eq]; unfold OnCurve; decide +kernel

/-- The field element ten limbs hold: `∑ l[i] 2^⌈25.5 i⌉` modulo `p`. -/
def fv (l : List Nat) : Nat :=
  (l.getD 0 0 + 2 ^ 26 * l.getD 1 0 + 2 ^ 51 * l.getD 2 0 + 2 ^ 77 * l.getD 3 0 + 2 ^ 102 * l.getD 4 0 +
    2 ^ 128 * l.getD 5 0 + 2 ^ 153 * l.getD 6 0 + 2 ^ 179 * l.getD 7 0 + 2 ^ 204 * l.getD 8 0 +
    2 ^ 230 * l.getD 9 0) % Ed25519.p

/-- Ten limbs, each below `B`. -/
def Lim (B : Nat) (l : List Nat) : Prop := l.length = 10 ∧ ∀ i, i < 10 → l.getD i 0 < B

theorem Lim.mono {B B' : Nat} {l : List Nat} (h : Lim B l) (hB : B ≤ B') : Lim B' l :=
  ⟨h.1, fun i hi => Nat.lt_of_lt_of_le (h.2 i hi) hB⟩

theorem fv_lt (l : List Nat) : fv l < Ed25519.p := Nat.mod_lt _ p_pos

theorem neg_of_sum {u v : Nat} (h : (u + v) % Ed25519.p = 0) : u % Ed25519.p = (Ed25519.p - v % Ed25519.p) % Ed25519.p := by
  unfold Ed25519.p at *; omega

/-- Negating one factor negates the product. -/
theorem neg_mul_mod (a b : Nat) :
    (Ed25519.p - a % Ed25519.p) % Ed25519.p * b % Ed25519.p = (Ed25519.p - a * b % Ed25519.p) % Ed25519.p := by
  apply neg_of_sum
  have h : ((Ed25519.p - a % Ed25519.p) % Ed25519.p + a) % Ed25519.p = 0 := by unfold Ed25519.p; omega
  rw [← Nat.add_mul, Nat.mul_mod, h, Nat.zero_mul, Nat.zero_mod]

theorem mod_mul_mod' (a b : Nat) : a * (b % Ed25519.p) % Ed25519.p = a * b % Ed25519.p := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem mod_mul_mod'' (a b : Nat) : a % Ed25519.p * b % Ed25519.p = a * b % Ed25519.p := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

end C3.RV32.EdM
