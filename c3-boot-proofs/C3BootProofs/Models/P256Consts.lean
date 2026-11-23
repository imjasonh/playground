import C3BootProofs.Models.P256Model
import C3BootProofs.Proofs.P2Lib
import C3BootProofs.Proofs.Dec384Calls
import C3BootProofs.Image.Bootloader
import C3BootProofs.Image.BootloaderData5

/-!
# The image's P-256 constants

`P256Consts.of` derives `P256Consts` from the image's data in memory.
-/

namespace C3.Models

open C3.RV32 C3.RV32.Dq C3.RV32.P2 C3.Image

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 600 in
/-- The constants the P-256 check reads are the image's. -/
theorem P256Consts.of {M : Word → BitVec 8} (D : P2Data M)
    (ND : CodeIn M (BitVec.ofNat 32 b2sOrder256Address) b2sOrder256Data)
    (UD : CodeIn M (BitVec.ofNat 32 p256OneAddress) p256OneData)
    (GD : CodeIn M (BitVec.ofNat 32 p256GMontAddress) p256GMontData)
    (OD : CodeIn M (BitVec.ofNat 32 p256MontOneAddress) p256MontOneData)
    (AD : CodeIn M (BitVec.ofNat 32 p256AffineIdXAddress) p256AffineIdXData) : P256Consts M where
  n := (code_accV ND 0 8 (by decide)).trans (by decide +kernel)
  one := (code_accV UD 0 8 (by decide)).trans (by decide +kernel)
  p := (code_accV D.params 0 8 (by decide)).trans (by decide +kernel)
  r2 := (code_accV D.params 0x40 8 (by decide)).trans (by decide +kernel)
  gx := (code_accV GD 0 8 (by decide)).trans (by decide +kernel)
  gy := (code_accV GD 0x20 8 (by decide)).trans (by decide +kernel)
  gz := (code_accV GD 0x40 8 (by decide)).trans (by decide +kernel)
  mone := (code_accV OD 0 8 (by decide)).trans (by decide +kernel)
  idx := (code_accV AD 0 8 (by decide)).trans (by decide +kernel)

end C3.Models
