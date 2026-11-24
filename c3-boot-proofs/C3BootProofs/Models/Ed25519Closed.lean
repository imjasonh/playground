import C3BootProofs.Models.Ed25519SvModelPrime
import C3BootProofs.Models.PrimeCurves

/-!
# The Ed25519 model with Ed25519's prime certified

`svEdModel_prime` with `IsPrime Ed25519.p` from its Pratt certificate.
-/

namespace C3.RV32.EdM

theorem svEdModel_closed {M : Word → BitVec 8} (I : EdImage M) (hdec : DecOK) (hiso : IsoOK) (hcmp : CompressOK)
    (hk : KOK M) : C3.RV32.Sv.SvEdModel M :=
  svEdModel_prime I C3.Models.ed25519_spec_p_prime hdec hiso hcmp hk

end C3.RV32.EdM
