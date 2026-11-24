import C3BootProofs.Models.Ed25519SvModelPrime
import C3BootProofs.Models.Ed25519Compress
import C3BootProofs.Models.Ed25519Iso

/-!
# `SvEdModel` without `IsoOK` and `CompressOK`

`svEdModel_iso_cmp` is `svEdModel_prime` with `IsoOK` and `CompressOK`
discharged from `IsPrime Ed25519.p`.
-/

namespace C3.RV32.EdM

open C3.Models

theorem svEdModel_iso_cmp {M : Word → BitVec 8} (I : EdImage M) (hp : IsPrime Ed25519.p) (hdec : DecOK)
    (hk : KOK M) : C3.RV32.Sv.SvEdModel M :=
  svEdModel_prime I hp hdec (iso_ok hp) (compress_ok hp) hk

end C3.RV32.EdM
