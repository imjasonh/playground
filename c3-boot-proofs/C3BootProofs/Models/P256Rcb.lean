import C3BootProofs.Models.EcdsaRcb
import C3BootProofs.Models.P256Model

/-!
# P-256's compiled point formulas from `RcbAddOk`

The compiled `ptAdd2` and `ptDbl2` are `rcbAdd` and `rcbDbl` over P-256's
Montgomery operations, so `P256AddOk` and `P256DblOk` follow from
`RcbAddOk C3.p256` and `RcbDblPoly`.
-/

namespace C3.Models

open C3.RV32 C3.RV32.Sv C3.RV32.P2

set_option exponentiation.threshold 600

theorem ptAdd2_rcb (A B : Pt2) :
    ptAdd2 A B = rcbAdd (mm C3.p256.p rInv) (ma C3.p256.p) (ms C3.p256.p) (md C3.p256.p) bMont A.1 A.2.1 A.2.2 B.1
      B.2.1 B.2.2 := by
  rw [p256_p]; rfl

theorem ptDbl2_rcb (A : Pt2) :
    ptDbl2 A = rcbDbl (mm C3.p256.p rInv) (ma C3.p256.p) (ms C3.p256.p) (md C3.p256.p) bMont A.1 A.2.1 A.2.2 := by
  rw [p256_p]; rfl

theorem p256_rinv : 2 ^ 256 * rInv % C3.p256.p = 1 := by rw [p256_p]; rfl

theorem bMont_lt : bMont < C3.p256.p := by decide

theorem bMont_meq : MEq C3.p256.p bMont ((C3.p256.b : Int) * ((2 ^ 256 : Nat) : Int)) := by
  rw [← Int.natCast_mul]
  exact MEq.natCast.mpr (by decide)

theorem p256AddOk_of (h : RcbAddOk C3.p256) : P256AddOk := fun A B _ _ hA hB ha hb => by
  rw [ptAdd2_rcb]
  exact mont_add_rep (by decide) p256_rinv bMont_lt bMont_meq h hA hB ha hb

theorem p256DblOk_of (h : RcbAddOk C3.p256) (hd : RcbDblPoly) : P256DblOk := fun A _ hA ha => by
  rw [ptDbl2_rcb]
  exact mont_dbl_rep (by decide) (by decide) p256_rinv bMont_lt bMont_meq h hd hA ha

/-- **The P-256 check accepts only signatures `p256Verify` accepts**,
given P-256's group law (`p` prime, closure, and associativity),
`RcbAddOk C3.p256`, the doubling identity, the scalar reduction, and the
image's constants. -/
theorem p256_model_rcb {M : Word → BitVec 8} (hp : IsPrime C3.p256.p) (hc : EC.AddClosed C3.p256)
    (ha : EC.AddAssoc C3.p256) (hadd : RcbAddOk C3.p256) (hpoly : RcbDblPoly) (hpsm : P256PsmOk)
    (K : P256Consts M) : SvP256Model' M :=
  p256_model hp hc ha (p256AddOk_of hadd) (p256DblOk_of hadd hpoly) hpsm K

end C3.Models
