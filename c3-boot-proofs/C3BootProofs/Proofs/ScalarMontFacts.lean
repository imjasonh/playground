import C3BootProofs.Proofs.ScalarMontDecode

/-!
# Facts for `Scalar29::montgomery_mul`'s generated proof

The operands' limbs as `montgomery_mul`'s definitions read them, the
instruction facts `ScalarMontBody.lean` needs beyond `Fe25519.lean`'s, and the
last step of its sum lemmas.
-/

namespace C3.RV32

/-- Limb `i` of the nine at `p`, and zero past them: `montgomery_mul`'s operands. -/
def smmIn (M : Word → BitVec 8) (p : Word) (i : Nat) : Nat := if i < 9 then limbAt M p i else 0

theorem smm_tn_sub {a b v : Word} (h : aluEval .sub a b = v) : v.toNat = (a.toNat + 2 ^ 32 - b.toNat) % 2 ^ 32 := by
  rw [← h]; show (a - b).toNat = _
  rw [BitVec.toNat_sub]; have := b.isLt; omega

/-- A subtraction and its borrow, as one equation. -/
theorem smmS1 {a b y c : Word} (hy : aluEval .sub a b = y) (hc : aluEval .sltu a b = c) :
    y.toNat + b.toNat = a.toNat + 2 ^ 32 * c.toNat := by
  have ey := smm_tn_sub hy
  have := a.isLt; have := b.isLt
  rcases tn_sltu hc with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-- A word pair's value from an exact identity with quotients. -/
theorem smm_key {A R X Y : Nat} (h : A + 2 ^ 64 * X = R + 2 ^ 64 * Y) (hA : A < 2 ^ 64) : A = R % 2 ^ 64 := by
  omega

theorem smm_lt (lo hi : Word) : lo.toNat + 2 ^ 32 * hi.toNat < 2 ^ 64 := by
  have := lo.isLt; have := hi.isLt; omega

theorem tn_and29 {a m v : Word} (h : aluEval .and a m = v) (hm : m = 0x1FFFFFFF) : v.toNat = a.toNat % 2 ^ 29 := by
  rw [← h, hm]; exact and_low (by decide) (by decide)

theorem tn_and29' {a m v : Word} (h : aluEval .and m a = v) (hm : m = 0x1FFFFFFF) : v.toNat = a.toNat % 2 ^ 29 := by
  rw [← h, hm]; show (0x1FFFFFFF &&& a).toNat = _
  rw [BitVec.and_comm]; exact and_low (by decide) (by decide)

end C3.RV32
