import C3BootProofs.Proofs.SvExtListLink
import C3BootProofs.Spec.Sigstore

/-!
# `sigstore::verify`'s constants as the specification's

The OIDs and strings in `SvData`, the 304 bytes from 0x3FCC4818, as the
values `Spec/X509.lean`, `Spec/Tsa.lean`, and `Spec/Checkpoint.lean` name.
-/

namespace C3.RV32.Sv

open C3.Image

theorem sv_const {M : Word → BitVec 8} (D : SvData M) {a : Word} (i n : Nat) {v : Bytes}
    (ha : a = SVK + BitVec.ofNat 32 i) (hn : i + n ≤ svConstData.length)
    (hv : (List.range n).map (fun j => svConstData.getD (i + j) 0) = v) : memBytes M a n = v := by
  rw [ha, D.mb hn, hv]

set_option maxRecDepth 100000

theorem sv_ecdsa384 {M : Word → BitVec 8} (D : SvData M) : memBytes M (BitVec.ofNat 32 0x3FCC4840) 8 = oidEcdsaSha384 :=
  sv_const D 0x28 8 (by decide) (by decide) (by decide)
theorem sv_prime256 {M : Word → BitVec 8} (D : SvData M) : memBytes M (BitVec.ofNat 32 0x3FCC4848) 8 = oidPrime256v1 :=
  sv_const D 0x30 8 (by decide) (by decide) (by decide)
theorem sv_ecpub {M : Word → BitVec 8} (D : SvData M) : memBytes M (BitVec.ofNat 32 0x3FCC4914) 7 = oidEcPublicKey :=
  sv_const D 0xFC 7 (by decide) (by decide) (by decide)
theorem sv_signedData {M : Word → BitVec 8} (D : SvData M) : memBytes M (BitVec.ofNat 32 0x3FCC4859) 9 = oidSignedData :=
  sv_const D 0x41 9 (by decide) (by decide) (by decide)
theorem sv_tstInfo {M : Word → BitVec 8} (D : SvData M) : memBytes M (BitVec.ofNat 32 0x3FCC4862) 11 = oidTstInfo :=
  sv_const D 0x4A 11 (by decide) (by decide) (by decide)
theorem sv_ecdsa256 {M : Word → BitVec 8} (D : SvData M) : memBytes M (BitVec.ofNat 32 0x3FCC4818) 8 = oidEcdsaSha256 :=
  sv_const D 0 8 (by decide) (by decide) (by decide)
theorem sv_contentType {M : Word → BitVec 8} (D : SvData M) : memBytes M (BitVec.ofNat 32 0x3FCC486E) 9 = oidContentType :=
  sv_const D 0x56 9 (by decide) (by decide) (by decide)
theorem sv_messageDigest {M : Word → BitVec 8} (D : SvData M) :
    memBytes M (BitVec.ofNat 32 0x3FCC4877) 9 = oidMessageDigest :=
  sv_const D 0x5F 9 (by decide) (by decide) (by decide)
theorem sv_sigPrefix {M : Word → BitVec 8} (D : SvData M) : memBytes M (BitVec.ofNat 32 0x3FCC4855) 4 = sigLinePrefix :=
  sv_const D 0x3D 4 (by decide) (by decide) (by decide)
theorem sv_newline {M : Word → BitVec 8} (D : SvData M) : memBytes M (BitVec.ofNat 32 0x3FCC4850) 1 = [0x0A] :=
  sv_const D 0x38 1 (by decide) (by decide) (by decide)
theorem sv_setTag {M : Word → BitVec 8} (D : SvData M) : memBytes M (BitVec.ofNat 32 0x3FCC486D) 1 = [0x31] :=
  sv_const D 0x55 1 (by decide) (by decide) (by decide)

theorem sv_extConsts {M : Word → BitVec 8} (D : SvData M) : ExtConsts M where
  ku := sv_const D 0x71 3 (by decide) (by decide) (by decide)
  san := sv_const D 0x74 3 (by decide) (by decide) (by decide)
  bc := sv_const D 0x77 3 (by decide) (by decide) (by decide)
  eku := sv_const D 0x7A 3 (by decide) (by decide) (by decide)
  cs := sv_const D 0x08 8 (by decide) (by decide) (by decide)
  p0 := sv_const D 0xA0 10 (by decide) (by decide) (by decide)
  p1 := sv_const D 0xAA 10 (by decide) (by decide) (by decide)
  p2 := sv_const D 0xB4 10 (by decide) (by decide) (by decide)
  p3 := sv_const D 0xBE 10 (by decide) (by decide) (by decide)
  p4 := sv_const D 0xC8 10 (by decide) (by decide) (by decide)

end C3.RV32.Sv
