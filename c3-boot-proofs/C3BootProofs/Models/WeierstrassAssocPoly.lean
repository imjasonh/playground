import C3BootProofs.Models.WeierstrassRcb

/-!
# Associativity of algorithm 4: the polynomial identities

Let `a = (x₁, y₁)`, `b = (x₂, y₂)`, and `d = (x₃, y₃)` be affine points, and
let `l₁` and `l₃` be the slopes of the lines through `a` and `b` and
through `b` and `d`, so that `a + b = (x₄, y₄)` and `b + d = (x₅, y₅)`.
`assoc_x` and `assoc_y` say that algorithm 4 at `(x₄, y₄, 1)` and
`(x₃, y₃, 1)` and algorithm 4 at `(x₁, y₁, 1)` and `(x₅, y₅, 1)` are
proportional, modulo the rules that eliminate `x₄`, `y₄`, `x₅`, `y₅`, `y₃`,
`y₂`, `x₃²`, `x₂²`, `y₁²`, and `a`. Under a lexicographic order with
`x₃ > x₂ > y₁` the leading terms `x₃²`, `x₂²`, and `y₁²` are pairwise coprime,
so the rules reduce every polynomial to a unique normal form.

Each check takes the kernel about 40 seconds and 6 GB.
-/

namespace C3.Models.EC

open C3.Ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem assoc_x {p : Nat} {a b x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 l1 l3 : Int}
    (ey4 : MEq p (y4 ^ 1) (l1 * (x1 - x4) - y1)) (ex4 : MEq p (x4 ^ 1) (l1 * l1 - x1 - x2))
    (ey5 : MEq p (y5 ^ 1) (l3 * (x2 - x5) - y2)) (ex5 : MEq p (x5 ^ 1) (l3 * l3 - x2 - x3))
    (ry3 : MEq p (y3 ^ 1) (y2 + l3 * (x3 - x2))) (ry2 : MEq p (y2 ^ 1) (y1 + l1 * (x2 - x1)))
    (rx3 : MEq p (x3 ^ 2) (2 * y2 * l3 + l3 * l3 * (x3 - x2) - x2 * x3 - x2 * x2 - a))
    (rx2 : MEq p (x2 ^ 2) (2 * y1 * l1 + l1 * l1 * (x2 - x1) - x1 * x2 - x1 * x1 - a))
    (r1 : MEq p (y1 ^ 2) (x1 ^ 3 + a * x1 + b)) (ra : MEq p (a ^ 1) (-3)) :
    MEq p ((rcbAddI b x4 y4 1 x3 y3 1).1 * (rcbAddI b x1 y1 1 x5 y5 1).2.2)
      ((rcbAddI b x1 y1 1 x5 y5 1).1 * (rcbAddI b x4 y4 1 x3 y3 1).2.2) := by
  simp only [rcbAdd]
  curve_mod (fuel := 3) [ey4, ex4, ey5, ex5, ry3, rx3, ry2, rx2, r1, ra] []

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem assoc_y {p : Nat} {a b x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 l1 l3 : Int}
    (ey4 : MEq p (y4 ^ 1) (l1 * (x1 - x4) - y1)) (ex4 : MEq p (x4 ^ 1) (l1 * l1 - x1 - x2))
    (ey5 : MEq p (y5 ^ 1) (l3 * (x2 - x5) - y2)) (ex5 : MEq p (x5 ^ 1) (l3 * l3 - x2 - x3))
    (ry3 : MEq p (y3 ^ 1) (y2 + l3 * (x3 - x2))) (ry2 : MEq p (y2 ^ 1) (y1 + l1 * (x2 - x1)))
    (rx3 : MEq p (x3 ^ 2) (2 * y2 * l3 + l3 * l3 * (x3 - x2) - x2 * x3 - x2 * x2 - a))
    (rx2 : MEq p (x2 ^ 2) (2 * y1 * l1 + l1 * l1 * (x2 - x1) - x1 * x2 - x1 * x1 - a))
    (r1 : MEq p (y1 ^ 2) (x1 ^ 3 + a * x1 + b)) (ra : MEq p (a ^ 1) (-3)) :
    MEq p ((rcbAddI b x4 y4 1 x3 y3 1).2.1 * (rcbAddI b x1 y1 1 x5 y5 1).2.2)
      ((rcbAddI b x1 y1 1 x5 y5 1).2.1 * (rcbAddI b x4 y4 1 x3 y3 1).2.2) := by
  simp only [rcbAdd]
  curve_mod (fuel := 3) [ey4, ex4, ey5, ex5, ry3, rx3, ry2, rx2, r1, ra] []

end C3.Models.EC
