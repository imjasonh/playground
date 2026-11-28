import C3BootProofs.Models.WeierstrassNist
import C3BootProofs.Models.EcdsaDbl
import C3BootProofs.Models.P256Barrett
import C3BootProofs.Models.PrimeCurves

/-!
# The ECDSA models with no mathematical hypotheses

The P-256 check accepts only signatures that `p256Verify` accepts, given the
image's P-256 constants, and the P-384 check accepts only signatures that
`p384Verify` accepts.
-/

namespace C3.Models

theorem p256_model_closed {M : RV32.Word → BitVec 8} (K : P256Consts M) : SvP256Model' M :=
  p256_model_prime p256_prime rcbDblPoly p256PsmOk K

theorem p384_model_closed {M : RV32.Word → BitVec 8} : SvP384Model' M :=
  p384_model_prime p384_prime rcbDblPoly

end C3.Models
