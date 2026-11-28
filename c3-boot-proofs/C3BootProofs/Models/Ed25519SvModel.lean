import C3BootProofs.Models.Ed25519Model
import C3BootProofs.Proofs.SvModels

/-!
# `SvEdModel` from the Ed25519 model

`svEdModel` discharges `SvEdModel M` with `evSpec_sound`, under the same
hypotheses.
-/

namespace C3.RV32.EdM

theorem svEdModel {M : Word → BitVec 8} (I : EdImage M) (G : EdGroupLaws) (F : EdFormulas) (hdec : DecOK)
    (hiso : IsoOK) (hcmp : CompressOK) (hk : KOK M) (hrx : RecoverXOK) : C3.RV32.Sv.SvEdModel M :=
  fun pk sig msg len h => evSpec_sound I G F hdec hiso hcmp hk hrx pk sig msg len h

end C3.RV32.EdM
