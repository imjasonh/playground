import C3BootProofs.Models.WeierstrassAssoc
import C3BootProofs.Models.WeierstrassNoRoot
import C3BootProofs.Models.P256Rcb
import C3BootProofs.Models.P384Rcb

/-!
The group law and algorithm 4 for P-256 and P-384, given that `p` is prime.
The kernel checks a certificate that `x³ + a x + b` has no root modulo `p`.
-/

namespace C3.Models

open EC

theorem p256_noRoot (hp : IsPrime C3.p256.p) : NoRoot C3.p256 :=
  noRoot_of_cert hp 256 (by decide +kernel)
    (0xa969487079f1744798bf0de6fded091b66e9d328eb0645fe5d979d1339b7f47f,
      0xa4a08891884100c13323460107a8d28eede4387fa3e6e9bfebec9f6d72d0b5cc,
      0x4cde11cf86cb876cd59cf0115813c55af0ecd3cda667d98bb9a347a56aa74a6d)
    (by decide +kernel)

theorem p384_noRoot (hp : IsPrime C3.p384.p) : NoRoot C3.p384 :=
  noRoot_of_cert hp 384 (by decide +kernel)
    (0x95adec811ebe8d4b9e2b41150d78f91a619189a415583b8f5e01888da3353b61765cde8cd6c12846310c3f0c10aae682,
      0x3581b884702fb0931c541a5cacefbe3bea864db86e01e048170560418dca3aa8689f246d9d11ccd2e145532dd48491af,
      0x4efcebfdccd7cb25d1b864228f0c32d3a83ec026134ae4753bdff5d3f1fa20b278b31dc3487beb792024fe436f36b43a)
    (by decide +kernel)

theorem p256_addClosed (hp : IsPrime C3.p256.p) : AddClosed C3.p256 := addClosed_of_prime hp

theorem p384_addClosed (hp : IsPrime C3.p384.p) : AddClosed C3.p384 := addClosed_of_prime hp

theorem p256_addAssoc (hp : IsPrime C3.p256.p) : AddAssoc C3.p256 :=
  addAssoc_of hp (by decide +kernel) (by decide +kernel) (p256_noRoot hp)

theorem p384_addAssoc (hp : IsPrime C3.p384.p) : AddAssoc C3.p384 :=
  addAssoc_of hp (by decide +kernel) (by decide +kernel) (p384_noRoot hp)

theorem p256_rcbAddOk (hp : IsPrime C3.p256.p) : RcbAddOk C3.p256 :=
  rcbAddOk_of hp (by decide +kernel) (by decide +kernel) (p256_noRoot hp)

theorem p384_rcbAddOk (hp : IsPrime C3.p384.p) : RcbAddOk C3.p384 :=
  rcbAddOk_of hp (by decide +kernel) (by decide +kernel) (p384_noRoot hp)

/-- **The P-256 check accepts only signatures `p256Verify` accepts**, given
that P-256's `p` is prime, the doubling identity, the scalar reduction, and
the image's constants. -/
theorem p256_model_prime {M : RV32.Word → BitVec 8} (hp : IsPrime C3.p256.p) (hpoly : RcbDblPoly)
    (hpsm : P256PsmOk) (K : P256Consts M) : SvP256Model' M :=
  p256_model_rcb hp (p256_addClosed hp) (p256_addAssoc hp) (p256_rcbAddOk hp) hpoly hpsm K

/-- **The P-384 check accepts only signatures `p384Verify` accepts**, given
that P-384's `p` is prime and the doubling identity. -/
theorem p384_model_prime {M : RV32.Word → BitVec 8} (hp : IsPrime C3.p384.p) (hpoly : RcbDblPoly) :
    SvP384Model' M :=
  p384_model_rcb hp (p384_addClosed hp) (p384_addAssoc hp) (p384_rcbAddOk hp) hpoly

end C3.Models
