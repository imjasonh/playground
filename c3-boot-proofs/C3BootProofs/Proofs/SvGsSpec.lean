import C3BootProofs.Proofs.SvModels

/-!
# A point `from_sec1_bytes` accepts is on P-256

`GsOk` checks the curve equation in Montgomery form. With `R = 2^256`
invertible modulo `p`, it is the equation `decodePoint` checks.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Gs C3.RV32.P2

theorem p2_rinv : 2 ^ 256 * p2RInv % p256 = 1 := by unfold p256 p2RInv; decide

/-- The Montgomery product of `a`'s and `b`'s Montgomery forms is `ab`'s. -/
theorem p2fm_mont {A B a b : Nat} (hA : A % p256 = a * 2 ^ 256 % p256) (hB : B % p256 = b * 2 ^ 256 % p256) :
    p2fm A B = a * b * 2 ^ 256 % p256 := by
  unfold p2fm
  calc A * B * p2RInv % p256 = A % p256 * (B * p2RInv) % p256 := by rw [Nat.mod_mul_mod, Nat.mul_assoc]
    _ = a * 2 ^ 256 % p256 * (B * p2RInv) % p256 := by rw [hA]
    _ = B * (a * 2 ^ 256 * p2RInv) % p256 := by
      rw [Nat.mod_mul_mod]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ = B % p256 * (a * 2 ^ 256 * p2RInv) % p256 := by rw [Nat.mod_mul_mod]
    _ = b * 2 ^ 256 % p256 * (a * 2 ^ 256 * p2RInv) % p256 := by rw [hB]
    _ = a * b * 2 ^ 256 * (2 ^ 256 * p2RInv) % p256 := by
      rw [Nat.mod_mul_mod]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ = a * b * 2 ^ 256 * (2 ^ 256 * p2RInv % p256) % p256 := by rw [Nat.mul_mod_mod]
    _ = a * b * 2 ^ 256 % p256 := by rw [p2_rinv, Nat.mul_one]

theorem p256_lt : p256 < 2 ^ 256 := by unfold p256; decide

theorem subRes_mod {L : Nat} (h : L < 2 * p256) : subRes L = L % p256 := by
  unfold subRes
  by_cases hl : L < p256
  · rw [ite_eq_left hl, Nat.mod_eq_of_lt (Nat.lt_trans hl p256_lt), Nat.mod_eq_of_lt hl]
  · have hle : p256 ≤ L := Nat.le_of_not_lt hl
    have hs : L - p256 < p256 := Nat.sub_lt_left_of_lt_add hle (by rw [← Nat.two_mul]; exact h)
    rw [ite_eq_right hl, Nat.mod_eq_of_lt (Nat.lt_trans hs p256_lt), Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hs]

theorem mod3 (a b c : Nat) : ((a % p256 + b % p256) % p256 + c % p256) % p256 = (a + b + c) % p256 := by
  calc ((a % p256 + b % p256) % p256 + c % p256) % p256 = (a % p256 + (b % p256 + c)) % p256 := by
        rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
    _ = (a + c + b % p256) % p256 := by rw [Nat.mod_add_mod, Nat.add_comm (b % p256) c, ← Nat.add_assoc]
    _ = (a + b + c) % p256 := by rw [Nat.add_mod_mod, Nat.add_right_comm]

theorem add_mod_congr {u u' c : Nat} (h : u % p256 = u' % p256) : (u + c) % p256 = (u' + c) % p256 := by
  rw [Nat.add_mod, h, ← Nat.add_mod]

/-- `x³ + ax + b` in Montgomery form. -/
theorem gsAlpha_mont (x : Nat) :
    gsAlpha (x * 2 ^ 256 % p256) = (x * x * x + (p256 - 3) * x + C3.p256.b) * 2 ^ 256 % p256 := by
  have hX : x * 2 ^ 256 % p256 % p256 = x * 2 ^ 256 % p256 := Nat.mod_mod _ _
  have h2 := p2fm_mont hX hX
  have h3 := p2fm_mont (A := p2fm (x * 2 ^ 256 % p256) (x * 2 ^ 256 % p256)) (a := x * x) (by rw [h2, Nat.mod_mod]) hX
  have hA : p2A % p256 = (p256 - 3) * 2 ^ 256 % p256 := by rw [p2A_mont, Nat.mod_mod]
  have h4 := p2fm_mont hA hX
  have hB : p2B < p256 := by unfold p2B p256; decide
  have hS1 : p2fm (p2fm (x * 2 ^ 256 % p256) (x * 2 ^ 256 % p256)) (x * 2 ^ 256 % p256) +
      p2fm p2A (x * 2 ^ 256 % p256) < 2 * p256 := by
    rw [Nat.two_mul]; exact Nat.add_lt_add (p2fm_lt _ _) (p2fm_lt _ _)
  unfold gsAlpha
  rw [subRes_mod hS1]
  rw [subRes_mod (by rw [Nat.two_mul]; exact Nat.add_lt_add (Nat.mod_lt _ p256_pos) hB)]
  rw [h3, h4, p2B_mont, mod3, Nat.add_mul, Nat.add_mul]
  rfl

/-- Cancels `R` from both sides. -/
theorem cancelR {u v : Nat} (h : u * 2 ^ 256 % p256 = v * 2 ^ 256 % p256) : u % p256 = v % p256 := by
  have e : ∀ w, w % p256 = w * 2 ^ 256 % p256 * p2RInv % p256 := fun w => by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.mul_mod_mod, p2_rinv, Nat.mul_one]
  rw [e u, e v, h]

theorem memBytes_dropK' (M : Word → BitVec 8) (p : Word) {k n : Nat} (h : k ≤ n) :
    (memBytes M p n).drop k = memBytes M (p + BitVec.ofNat 32 k) (n - k) := by
  have := memBytes_split M p k (n - k)
  rw [show k + (n - k) = n by omega] at this
  rw [this, List.drop_left' (memBytes_length M p k)]

theorem require_true : require true = some () := rfl

theorem gsModel {M : Word → BitVec 8} : SvGsModel M := by
  intro bp h4 hg
  obtain ⟨-, hx, hy, he⟩ := hg
  have hYY := p2fm_mont (A := gsVal M bp 0x21 * 2 ^ 256 % p256) (B := gsVal M bp 0x21 * 2 ^ 256 % p256)
    (a := gsVal M bp 0x21) (b := gsVal M bp 0x21) (Nat.mod_mod _ _) (Nat.mod_mod _ _)
  rw [he, gsAlpha_mont] at hYY
  have hc := cancelR hYY
  have heq : gsVal M bp 0x21 * gsVal M bp 0x21 % p256 =
      (gsVal M bp 1 * gsVal M bp 1 % p256 * gsVal M bp 1 + (p256 - 3) * gsVal M bp 1 + C3.p256.b) % p256 := by
    rw [← hc]
    exact add_mod_congr (add_mod_congr (Nat.mod_mul_mod _ _ _).symm)
  have hlen := memBytes_length M bp 65
  have hx' : beNat (((memBytes M bp 65).drop 1).take 32) = gsVal M bp 1 := by
    rw [memBytes_dropK' M bp (by decide), memBytes_take' (by decide)]
    rfl
  have hy' : beNat ((memBytes M bp 65).drop (1 + 32)) = gsVal M bp 0x21 := by
    rw [memBytes_dropK' M bp (by decide)]
    rfl
  have hhead : (memBytes M bp 65).head? = some 0x04 := by
    rw [show 65 = 64 + 1 from rfl, memBytes_succ, List.head?_cons, h4]
    rfl
  unfold Curve.decodePoint
  simp only [Option.bind_eq_bind]
  rw [hlen, hhead, show C3.p256.size = 32 from rfl, show (65 == 1 + 2 * 32 && some 4 == some 4) = true from rfl,
    require_true, Option.bind_some, hx', hy', show C3.p256.p = p256 from rfl, show C3.p256.a = p256 - 3 from rfl,
    decide_eq_true hx, decide_eq_true hy, heq, beq_iff_eq.mpr rfl]
  rfl

end C3.RV32.Sv
