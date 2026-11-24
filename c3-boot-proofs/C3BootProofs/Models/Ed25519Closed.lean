import C3BootProofs.Models.Ed25519SvModelPrime
import C3BootProofs.Models.PrimeCurves
import C3BootProofs.Models.Ed25519Dec
import C3BootProofs.Models.Ed25519K

/-!
# The Ed25519 model with Ed25519's prime certified

`svEdModel_prime` with `IsPrime Ed25519.p` from its Pratt certificate, the
decoding proved, and the reduction of `k` modulo `L` proved from the two
Montgomery constants in memory.
-/

namespace C3.RV32.EdM

theorem svEdModel_closed {M : Word → BitVec 8} (I : EdImage M) (K : EdK.KImage M) (hiso : IsoOK)
    (hcmp : CompressOK) : C3.RV32.Sv.SvEdModel M :=
  svEdModel_prime I C3.Models.ed25519_spec_p_prime (decOK C3.Models.ed25519_spec_p_prime) hiso hcmp (EdK.kOK K)

end C3.RV32.EdM
