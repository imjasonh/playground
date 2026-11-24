import C3BootProofs.Models.Ed25519SvModel
import C3BootProofs.Models.Ed25519Formulas
import C3BootProofs.Models.Ed25519RecoverX

/-!
# `SvEdModel` from the primality of `p`

`svEdModel_prime` is `svEdModel` with `EdGroupLaws`, `EdFormulas`, and
`RecoverXOK` discharged from `IsPrime Ed25519.p`.
-/

namespace C3.RV32.EdM

open C3.Models

theorem svEdModel_prime {M : Word → BitVec 8} (I : EdImage M) (hp : IsPrime Ed25519.p) (hdec : DecOK)
    (hiso : IsoOK) (hcmp : CompressOK) (hk : KOK M) : C3.RV32.Sv.SvEdModel M :=
  svEdModel I (edGroupLaws hp) (edFormulas hp) hdec hiso hcmp hk (recoverX_ok hp)

end C3.RV32.EdM
