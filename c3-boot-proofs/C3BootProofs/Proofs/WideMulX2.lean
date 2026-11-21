import C3BootProofs.Proofs.FeAdd

/-!
# Arithmetic for `widening_mul_fixed::<N, 2>`

`crypto_bigint`'s `widening_mul_fixed::<N, 2>` multiplies an `N`-limb number
by a 2-limb one with a schoolbook loop: for each limb of the first, two
multiply-accumulate steps into an `N + 2`-word buffer and a carry stored
above them. `kmWord` and `kmCarry` are one step's new word and carry in the
compiled code's order, and `km_row_arith` is one row's effect on the
buffer's value.
-/

namespace C3.RV32

/-- The new buffer word from one multiply-accumulate step: `y * x + (t + w)`. -/
abbrev kmWord (y x w t : Word) : Word := aluEval .add (aluEval .mul y x) (aluEval .add t w)

/-- The step's carry out, in the compiled code's order. -/
abbrev kmCarry (y x w t : Word) : Word :=
  aluEval .add (aluEval .sltu (kmWord y x w t) (aluEval .add t w))
    (aluEval .add (aluEval .sltu (aluEval .add t w) w) (aluEval .mulhu y x))

theorem km_arith (y x w t : Word) :
    (kmWord y x w t).toNat + 2 ^ 32 * (kmCarry y x w t).toNat = y.toNat * x.toNat + w.toNat + t.toNat := by
  have h := wm_step y x w t
  have e : kmCarry y x w t = wmCarry y x w t := by
    show aluEval .add _ (aluEval .add _ _) = aluEval .add _ (aluEval .add _ _)
    rw [show aluEval .add (aluEval .sltu (aluEval .add t w) w) (aluEval .mulhu y x) =
      aluEval .add (aluEval .mulhu y x) (aluEval .sltu (aluEval .add t w) w) from BitVec.add_comm _ _]
    rfl
  rw [e]; exact h

/-- One row of the schoolbook loop: the buffer's value `A` before the row is
the first `i` limbs' product `X * Y`; the row's two steps and its carry store
leave `A3`, which is the first `i + 1` limbs' product. -/
theorem km_row_arith {A A3 X x y0 y1 w0 w1 lo0 lo1 c0 c1 Pi : Nat}
    (hA : A = X * (y0 + y1 * 2 ^ 32))
    (hS : A3 + w0 * Pi + w1 * (Pi * 2 ^ 32) = A + lo0 * Pi + lo1 * (Pi * 2 ^ 32) + c1 * (Pi * 2 ^ 64))
    (h0 : lo0 + 2 ^ 32 * c0 = y0 * x + w0 + 0) (h1 : lo1 + 2 ^ 32 * c1 = y1 * x + w1 + c0) :
    A3 = (X + x * Pi) * (y0 + y1 * 2 ^ 32) := by
  have hL : lo0 + 2 ^ 32 * lo1 + 2 ^ 64 * c1 = y0 * x + w0 + 2 ^ 32 * (y1 * x) + 2 ^ 32 * w1 := by omega
  have hM := congrArg (· * Pi) hL
  simp only [Nat.add_mul, Nat.mul_add] at hM hS hA ⊢
  simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] at hM hS hA ⊢
  omega

theorem km_sll2 : ∀ i : Nat, i < 16 → aluEval .sll (BitVec.ofNat 32 i) 0x2 = BitVec.ofNat 32 (4 * i) := by decide

theorem km_add4 (b : Word) (k : Nat) : b + BitVec.ofNat 32 (4 * k) + 4 = b + BitVec.ofNat 32 (4 * (k + 1)) := by
  rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc, Nat.mul_succ]

theorem km_pow1 (i : Nat) : 2 ^ (32 * (i + 1)) = 2 ^ (32 * i) * 2 ^ 32 := by
  rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]

theorem km_pow2 (i : Nat) : 2 ^ (32 * (i + 2)) = 2 ^ (32 * i) * 2 ^ 64 := by
  rw [Nat.mul_add, Nat.pow_add]

end C3.RV32
