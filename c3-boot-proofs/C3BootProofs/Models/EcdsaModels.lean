import C3BootProofs.Models.EcdsaDbl
import C3BootProofs.Models.P256Barrett
import C3BootProofs.Models.P256Rcb
import C3BootProofs.Models.P384Rcb

/-!
# Both ECDSA models, from the curves' group laws

`p256_model_rcb` and `p384_model_rcb` with the doubling identity
(`rcbDblPoly`) and the scalar reduction (`p256PsmOk`) discharged. What they
still assume is that each curve's field order is prime, that its addition
is closed and associative, and that algorithm 4 computes it (`RcbAddOk`).
-/

namespace C3.Models

open C3.RV32

theorem p256_model_rcb' {M : Word → BitVec 8} (hp : IsPrime C3.p256.p)
    (hc : EC.AddClosed C3.p256) (ha : EC.AddAssoc C3.p256) (hadd : RcbAddOk C3.p256)
    (K : P256Consts M) : SvP256Model' M :=
  p256_model_rcb hp hc ha hadd rcbDblPoly p256PsmOk K

theorem p384_model_rcb' {M : Word → BitVec 8} (hp : IsPrime C3.p384.p)
    (hc : EC.AddClosed C3.p384) (ha : EC.AddAssoc C3.p384) (hadd : RcbAddOk C3.p384) :
    SvP384Model' M :=
  p384_model_rcb hp hc ha hadd rcbDblPoly

end C3.Models
