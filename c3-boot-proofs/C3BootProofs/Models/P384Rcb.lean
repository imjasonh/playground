import C3BootProofs.Models.EcdsaRcb
import C3BootProofs.Models.P384Model

/-!
# P-384's compiled point formulas from `RcbAddOk`

The compiled `ptAddT` and `ptDblT` are `rcbAdd` and `rcbDbl` over P-384's
Montgomery operations, so `P384AddOk` and `P384DblOk` follow from
`RcbAddOk C3.p384` and `RcbDblPoly`.
-/

namespace C3.Models

open C3.RV32 C3.RV32.Pv C3.RV32.P3

set_option exponentiation.threshold 800

theorem ptAddT_rcb (A B : Pt) :
    ptAddT A B = rcbAdd (mm C3.p384.p p3RInv) (ma C3.p384.p) (ms C3.p384.p) (md C3.p384.p) p3B A.1 A.2.1 A.2.2
      B.1 B.2.1 B.2.2 := by
  rw [p384_p]; rfl

theorem ptDblT_rcb (A : Pt) :
    ptDblT A = rcbDbl (mm C3.p384.p p3RInv) (ma C3.p384.p) (ms C3.p384.p) (md C3.p384.p) p3B A.1 A.2.1 A.2.2 := by
  rw [p384_p]; rfl

theorem p3B_lt' : p3B < C3.p384.p := by rw [p384_p]; exact p3B_lt

theorem p3B_meq : MEq C3.p384.p p3B ((C3.p384.b : Int) * ((2 ^ 384 : Nat) : Int)) := by
  rw [← Int.natCast_mul]
  exact MEq.natCast.mpr (by rw [p384_p]; unfold p3B RV32.p384; decide)

theorem p384AddOk_of (h : RcbAddOk C3.p384) : P384AddOk := fun A B _ _ hA hB ha hb => by
  rw [ptAddT_rcb]
  exact mont_add_rep (by decide) p3_rinv p3B_lt' p3B_meq h hA hB ha hb

theorem p384DblOk_of (h : RcbAddOk C3.p384) (hd : RcbDblPoly) : P384DblOk := fun A _ hA ha => by
  rw [ptDblT_rcb]
  exact mont_dbl_rep (by decide) (by decide) p3_rinv p3B_lt' p3B_meq h hd hA ha

/-- **The P-384 check accepts only signatures `p384Verify` accepts**,
given P-384's group law (`p` prime, closure, and associativity),
`RcbAddOk C3.p384`, and the doubling identity. -/
theorem p384_model_rcb {M : Word → BitVec 8} (hp : IsPrime C3.p384.p) (hc : EC.AddClosed C3.p384)
    (ha : EC.AddAssoc C3.p384) (hadd : RcbAddOk C3.p384) (hpoly : RcbDblPoly) : SvP384Model' M :=
  p384_model hp hc ha (p384AddOk_of hadd) (p384DblOk_of hadd hpoly)

end C3.Models
