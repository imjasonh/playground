import C3BootProofs.Models.Ed25519KMont
import C3BootProofs.Proofs.Ed25519VerifyP5b

/-!
# The value of `Scalar29::add`'s carry loop

For limbs below 2^29 whose values sum below 2^261, the carry loop's limbs
spell the sum (`add9`).
-/

namespace C3.RV32.EdK

open C3.RV32

theorem add9_sum {X0 X1 X2 X3 X4 X5 X6 X7 X8 Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 C1 C2 C3 C4 C5 C6 C7 C8 C9 : Nat}
    (c0 : C1 = 0 / 2 ^ 29 + X0 + Y0) (c1 : C2 = C1 / 2 ^ 29 + X1 + Y1) (c2 : C3 = C2 / 2 ^ 29 + X2 + Y2)
    (c3 : C4 = C3 / 2 ^ 29 + X3 + Y3) (c4 : C5 = C4 / 2 ^ 29 + X4 + Y4) (c5 : C6 = C5 / 2 ^ 29 + X5 + Y5)
    (c6 : C7 = C6 / 2 ^ 29 + X6 + Y6) (c7 : C8 = C7 / 2 ^ 29 + X7 + Y7) (c8 : C9 = C8 / 2 ^ 29 + X8 + Y8) :
    C1 % 2 ^ 29 + 2 ^ 29 * (C2 % 2 ^ 29) + 2 ^ 58 * (C3 % 2 ^ 29) + 2 ^ 87 * (C4 % 2 ^ 29) +
        2 ^ 116 * (C5 % 2 ^ 29) + 2 ^ 145 * (C6 % 2 ^ 29) + 2 ^ 174 * (C7 % 2 ^ 29) + 2 ^ 203 * (C8 % 2 ^ 29) +
        2 ^ 232 * (C9 % 2 ^ 29) + 2 ^ 261 * (C9 / 2 ^ 29) =
      X0 + 2 ^ 29 * X1 + 2 ^ 58 * X2 + 2 ^ 87 * X3 + 2 ^ 116 * X4 + 2 ^ 145 * X5 + 2 ^ 174 * X6 + 2 ^ 203 * X7 +
          2 ^ 232 * X8 +
        (Y0 + 2 ^ 29 * Y1 + 2 ^ 58 * Y2 + 2 ^ 87 * Y3 + 2 ^ 116 * Y4 + 2 ^ 145 * Y5 + 2 ^ 174 * Y6 +
          2 ^ 203 * Y7 + 2 ^ 232 * Y8) := by
  omega

set_option exponentiation.threshold 600 in
theorem add9 {X Y : Nat → Nat} (hs : sv9 X + sv9 Y < 2 ^ 261) :
    (∀ i, i < 9 → s29AddC X Y (i + 1) % 2 ^ 29 < 2 ^ 29) ∧
      sv9 (fun j => s29AddC X Y (j + 1) % 2 ^ 29) = sv9 X + sv9 Y := by
  refine ⟨fun i _ => Nat.mod_lt _ (by decide), ?_⟩
  have h := add9_sum (X0 := X 0) (X1 := X 1) (X2 := X 2) (X3 := X 3) (X4 := X 4) (X5 := X 5) (X6 := X 6)
    (X7 := X 7) (X8 := X 8) (Y0 := Y 0) (Y1 := Y 1) (Y2 := Y 2) (Y3 := Y 3) (Y4 := Y 4) (Y5 := Y 5) (Y6 := Y 6)
    (Y7 := Y 7) (Y8 := Y 8)
    (C1 := s29AddC X Y 1) (C2 := s29AddC X Y 2) (C3 := s29AddC X Y 3)
    (C4 := s29AddC X Y 4) (C5 := s29AddC X Y 5) (C6 := s29AddC X Y 6) (C7 := s29AddC X Y 7)
    (C8 := s29AddC X Y 8) (C9 := s29AddC X Y 9) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  unfold sv9 at hs ⊢
  dsimp only [Nat.reduceAdd]
  omega

end C3.RV32.EdK
