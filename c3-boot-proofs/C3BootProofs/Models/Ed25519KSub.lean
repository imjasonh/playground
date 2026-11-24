import C3BootProofs.Models.Ed25519KMont
import C3BootProofs.Proofs.Ed25519VerifyB

/-!
# The value of `Scalar29::sub(a, &L)`

For limbs below 2^29 whose value is below `2 L`, `sub` returns the value
modulo `L` (`s29Out_val`): the first loop subtracts `L` with borrows, and
`conditional_add_l` adds `L` back exactly when the subtraction borrowed out
of the top limb.
-/

namespace C3.RV32.EdK

open C3.RV32

theorem bstep (x : Nat → Nat) (i Li : Nat) (hL : scalarL.getD i 0 = Li) (hLi : Li < 2 ^ 29) (hx : x i < 2 ^ 29) :
    s29Borrow x (i + 1) % 2 ^ 29 + Li + s29Borrow x i / 2 ^ 31 = x i + 2 ^ 29 * (s29Borrow x (i + 1) / 2 ^ 31) := by
  have hw := s29Borrow_lt x i
  have e : s29Borrow x (i + 1) = (x i + 2 ^ 32 - (scalarL.getD i 0 + s29Borrow x i / 2 ^ 31) % 2 ^ 32) % 2 ^ 32 := rfl
  rw [e, hL]
  omega

theorem cstep (x : Nat → Nat) (c i Li : Nat) (hL : scalarL.getD i 0 = Li) (hLi : Li < 2 ^ 29) (hc : c ≤ 1) :
    s29Carry x c (i + 1) = s29Carry x c i / 2 ^ 29 + s29Borrow x (i + 1) % 2 ^ 29 + c * Li := by
  match c, hc with
  | 0, _ =>
    have hk := s29Carry_lt x 0 i
    show (s29Carry x 0 i / 2 ^ 29 + s29Borrow x (i + 1) % 2 ^ 29 + (if 0 = 1 then scalarL.getD i 0 else 0)) %
      2 ^ 32 = _
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    omega
  | 1, _ =>
    have hk := s29Carry_lt x 1 i
    show (s29Carry x 1 i / 2 ^ 29 + s29Borrow x (i + 1) % 2 ^ 29 + (if 1 = 1 then scalarL.getD i 0 else 0)) %
      2 ^ 32 = _
    simp only [↓reduceIte, hL]
    omega

theorem sub_sum {x0 x1 x2 x3 x4 x5 x6 x7 x8 D1 D2 D3 D4 D5 D6 D7 D8 D9 β1 β2 β3 β4 β5 β6 β7 β8 β9 : Nat}
    (b0 : D1 + 485872621 = x0 + 2 ^ 29 * β1)
    (b1 : D2 + 9640146 + β1 = x1 + 2 ^ 29 * β2)
    (b2 : D3 + 501691798 + β2 = x2 + 2 ^ 29 * β3)
    (b3 : D4 + 502512965 + β3 = x3 + 2 ^ 29 * β4)
    (b4 : D5 + 333 + β4 = x4 + 2 ^ 29 * β5)
    (b5 : D6 + 0 + β5 = x5 + 2 ^ 29 * β6)
    (b6 : D7 + 0 + β6 = x6 + 2 ^ 29 * β7)
    (b7 : D8 + 0 + β7 = x7 + 2 ^ 29 * β8)
    (b8 : D9 + 1048576 + β8 = x8 + 2 ^ 29 * β9) :
    D1 + 2 ^ 29 * D2 + 2 ^ 58 * D3 + 2 ^ 87 * D4 + 2 ^ 116 * D5 + 2 ^ 145 * D6 + 2 ^ 174 * D7 + 2 ^ 203 * D8 + 2 ^ 232 * D9 + Ed25519.L = x0 + 2 ^ 29 * x1 + 2 ^ 58 * x2 + 2 ^ 87 * x3 + 2 ^ 116 * x4 + 2 ^ 145 * x5 + 2 ^ 174 * x6 + 2 ^ 203 * x7 + 2 ^ 232 * x8 + 2 ^ 261 * β9 := by
  unfold Ed25519.L
  omega

theorem add_sum {C1 C2 C3 C4 C5 C6 C7 C8 C9 D1 D2 D3 D4 D5 D6 D7 D8 D9 β : Nat}
    (c0 : C1 = 0 / 2 ^ 29 + D1 + β * 485872621)
    (c1 : C2 = C1 / 2 ^ 29 + D2 + β * 9640146)
    (c2 : C3 = C2 / 2 ^ 29 + D3 + β * 501691798)
    (c3 : C4 = C3 / 2 ^ 29 + D4 + β * 502512965)
    (c4 : C5 = C4 / 2 ^ 29 + D5 + β * 333)
    (c5 : C6 = C5 / 2 ^ 29 + D6 + β * 0)
    (c6 : C7 = C6 / 2 ^ 29 + D7 + β * 0)
    (c7 : C8 = C7 / 2 ^ 29 + D8 + β * 0)
    (c8 : C9 = C8 / 2 ^ 29 + D9 + β * 1048576) :
    C1 % 2 ^ 29 + 2 ^ 29 * (C2 % 2 ^ 29) + 2 ^ 58 * (C3 % 2 ^ 29) + 2 ^ 87 * (C4 % 2 ^ 29) + 2 ^ 116 * (C5 % 2 ^ 29) + 2 ^ 145 * (C6 % 2 ^ 29) + 2 ^ 174 * (C7 % 2 ^ 29) + 2 ^ 203 * (C8 % 2 ^ 29) + 2 ^ 232 * (C9 % 2 ^ 29) + 2 ^ 261 * (C9 / 2 ^ 29) = D1 + 2 ^ 29 * D2 + 2 ^ 58 * D3 + 2 ^ 87 * D4 + 2 ^ 116 * D5 + 2 ^ 145 * D6 + 2 ^ 174 * D7 + 2 ^ 203 * D8 + 2 ^ 232 * D9 + β * Ed25519.L := by
  unfold Ed25519.L
  omega

theorem sub_fin {X D O γ β : Nat} (hv : X < 2 * Ed25519.L) (hβ : β ≤ 1) (hsub : D + Ed25519.L = X + 2 ^ 261 * β)
    (hD : D < 2 ^ 261) (hadd : O + 2 ^ 261 * γ = D + β * Ed25519.L) (ho : O < 2 ^ 261) : O = X % Ed25519.L := by
  have hL : Ed25519.L < 2 ^ 253 := by unfold Ed25519.L; omega
  have hL0 : 0 < Ed25519.L := by unfold Ed25519.L; omega
  cases β with
  | zero =>
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  | succ n =>
    have h0 : n = 0 := by omega
    subst h0
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

set_option exponentiation.threshold 600 in
theorem s29Out_val {x : Nat → Nat} (hx : ∀ i, i < 9 → x i < 2 ^ 29) (hv : sv9 x < 2 * Ed25519.L) :
    sv9 (s29Out x) = sv9 x % Ed25519.L := by
  have b0 : s29Borrow x 1 % 2 ^ 29 + 485872621 + s29Borrow x 0 / 2 ^ 31 = x 0 + 2 ^ 29 * (s29Borrow x 1 / 2 ^ 31) :=
    bstep x 0 485872621 rfl (by decide) (hx 0 (by decide))
  have b1 : s29Borrow x 2 % 2 ^ 29 + 9640146 + s29Borrow x 1 / 2 ^ 31 = x 1 + 2 ^ 29 * (s29Borrow x 2 / 2 ^ 31) :=
    bstep x 1 9640146 rfl (by decide) (hx 1 (by decide))
  have b2 : s29Borrow x 3 % 2 ^ 29 + 501691798 + s29Borrow x 2 / 2 ^ 31 = x 2 + 2 ^ 29 * (s29Borrow x 3 / 2 ^ 31) :=
    bstep x 2 501691798 rfl (by decide) (hx 2 (by decide))
  have b3 : s29Borrow x 4 % 2 ^ 29 + 502512965 + s29Borrow x 3 / 2 ^ 31 = x 3 + 2 ^ 29 * (s29Borrow x 4 / 2 ^ 31) :=
    bstep x 3 502512965 rfl (by decide) (hx 3 (by decide))
  have b4 : s29Borrow x 5 % 2 ^ 29 + 333 + s29Borrow x 4 / 2 ^ 31 = x 4 + 2 ^ 29 * (s29Borrow x 5 / 2 ^ 31) :=
    bstep x 4 333 rfl (by decide) (hx 4 (by decide))
  have b5 : s29Borrow x 6 % 2 ^ 29 + 0 + s29Borrow x 5 / 2 ^ 31 = x 5 + 2 ^ 29 * (s29Borrow x 6 / 2 ^ 31) :=
    bstep x 5 0 rfl (by decide) (hx 5 (by decide))
  have b6 : s29Borrow x 7 % 2 ^ 29 + 0 + s29Borrow x 6 / 2 ^ 31 = x 6 + 2 ^ 29 * (s29Borrow x 7 / 2 ^ 31) :=
    bstep x 6 0 rfl (by decide) (hx 6 (by decide))
  have b7 : s29Borrow x 8 % 2 ^ 29 + 0 + s29Borrow x 7 / 2 ^ 31 = x 7 + 2 ^ 29 * (s29Borrow x 8 / 2 ^ 31) :=
    bstep x 7 0 rfl (by decide) (hx 7 (by decide))
  have b8 : s29Borrow x 9 % 2 ^ 29 + 1048576 + s29Borrow x 8 / 2 ^ 31 = x 8 + 2 ^ 29 * (s29Borrow x 9 / 2 ^ 31) :=
    bstep x 8 1048576 rfl (by decide) (hx 8 (by decide))
  have z0 : s29Borrow x 0 = 0 := rfl
  rw [z0, Nat.zero_div, Nat.add_zero] at b0
  have hc : s29Borrow x 9 / 2 ^ 31 ≤ 1 := by have := s29Borrow_lt x 9; omega
  have c0 : s29Carry x (s29Borrow x 9 / 2 ^ 31) 1 = s29Carry x (s29Borrow x 9 / 2 ^ 31) 0 / 2 ^ 29 +
      s29Borrow x 1 % 2 ^ 29 + s29Borrow x 9 / 2 ^ 31 * 485872621 := cstep x _ 0 485872621 rfl (by decide) hc
  have c1 : s29Carry x (s29Borrow x 9 / 2 ^ 31) 2 = s29Carry x (s29Borrow x 9 / 2 ^ 31) 1 / 2 ^ 29 +
      s29Borrow x 2 % 2 ^ 29 + s29Borrow x 9 / 2 ^ 31 * 9640146 := cstep x _ 1 9640146 rfl (by decide) hc
  have c2 : s29Carry x (s29Borrow x 9 / 2 ^ 31) 3 = s29Carry x (s29Borrow x 9 / 2 ^ 31) 2 / 2 ^ 29 +
      s29Borrow x 3 % 2 ^ 29 + s29Borrow x 9 / 2 ^ 31 * 501691798 := cstep x _ 2 501691798 rfl (by decide) hc
  have c3 : s29Carry x (s29Borrow x 9 / 2 ^ 31) 4 = s29Carry x (s29Borrow x 9 / 2 ^ 31) 3 / 2 ^ 29 +
      s29Borrow x 4 % 2 ^ 29 + s29Borrow x 9 / 2 ^ 31 * 502512965 := cstep x _ 3 502512965 rfl (by decide) hc
  have c4 : s29Carry x (s29Borrow x 9 / 2 ^ 31) 5 = s29Carry x (s29Borrow x 9 / 2 ^ 31) 4 / 2 ^ 29 +
      s29Borrow x 5 % 2 ^ 29 + s29Borrow x 9 / 2 ^ 31 * 333 := cstep x _ 4 333 rfl (by decide) hc
  have c5 : s29Carry x (s29Borrow x 9 / 2 ^ 31) 6 = s29Carry x (s29Borrow x 9 / 2 ^ 31) 5 / 2 ^ 29 +
      s29Borrow x 6 % 2 ^ 29 + s29Borrow x 9 / 2 ^ 31 * 0 := cstep x _ 5 0 rfl (by decide) hc
  have c6 : s29Carry x (s29Borrow x 9 / 2 ^ 31) 7 = s29Carry x (s29Borrow x 9 / 2 ^ 31) 6 / 2 ^ 29 +
      s29Borrow x 7 % 2 ^ 29 + s29Borrow x 9 / 2 ^ 31 * 0 := cstep x _ 6 0 rfl (by decide) hc
  have c7 : s29Carry x (s29Borrow x 9 / 2 ^ 31) 8 = s29Carry x (s29Borrow x 9 / 2 ^ 31) 7 / 2 ^ 29 +
      s29Borrow x 8 % 2 ^ 29 + s29Borrow x 9 / 2 ^ 31 * 0 := cstep x _ 7 0 rfl (by decide) hc
  have c8 : s29Carry x (s29Borrow x 9 / 2 ^ 31) 9 = s29Carry x (s29Borrow x 9 / 2 ^ 31) 8 / 2 ^ 29 +
      s29Borrow x 9 % 2 ^ 29 + s29Borrow x 9 / 2 ^ 31 * 1048576 := cstep x _ 8 1048576 rfl (by decide) hc
  have k0 : s29Carry x (s29Borrow x 9 / 2 ^ 31) 0 = 0 := rfl
  rw [k0] at c0
  have hD : s29Borrow x 1 % 2 ^ 29 + 2 ^ 29 * (s29Borrow x 2 % 2 ^ 29) + 2 ^ 58 * (s29Borrow x 3 % 2 ^ 29) + 2 ^ 87 * (s29Borrow x 4 % 2 ^ 29) + 2 ^ 116 * (s29Borrow x 5 % 2 ^ 29) + 2 ^ 145 * (s29Borrow x 6 % 2 ^ 29) + 2 ^ 174 * (s29Borrow x 7 % 2 ^ 29) + 2 ^ 203 * (s29Borrow x 8 % 2 ^ 29) + 2 ^ 232 * (s29Borrow x 9 % 2 ^ 29) < 2 ^ 261 := by
    have := Nat.mod_lt (s29Borrow x 1) (show 0 < 2 ^ 29 by decide)
    have := Nat.mod_lt (s29Borrow x 2) (show 0 < 2 ^ 29 by decide)
    have := Nat.mod_lt (s29Borrow x 3) (show 0 < 2 ^ 29 by decide)
    have := Nat.mod_lt (s29Borrow x 4) (show 0 < 2 ^ 29 by decide)
    have := Nat.mod_lt (s29Borrow x 5) (show 0 < 2 ^ 29 by decide)
    have := Nat.mod_lt (s29Borrow x 6) (show 0 < 2 ^ 29 by decide)
    have := Nat.mod_lt (s29Borrow x 7) (show 0 < 2 ^ 29 by decide)
    have := Nat.mod_lt (s29Borrow x 8) (show 0 < 2 ^ 29 by decide)
    have := Nat.mod_lt (s29Borrow x 9) (show 0 < 2 ^ 29 by decide)
    omega
  have ho : sv9 (s29Out x) < 2 ^ 261 := by
    have := s29Out_lt29 x 0
    have := s29Out_lt29 x 1
    have := s29Out_lt29 x 2
    have := s29Out_lt29 x 3
    have := s29Out_lt29 x 4
    have := s29Out_lt29 x 5
    have := s29Out_lt29 x 6
    have := s29Out_lt29 x 7
    have := s29Out_lt29 x 8
    unfold sv9; omega
  exact sub_fin hv hc (sub_sum b0 b1 b2 b3 b4 b5 b6 b7 b8) hD (add_sum c0 c1 c2 c3 c4 c5 c6 c7 c8) ho

end C3.RV32.EdK
