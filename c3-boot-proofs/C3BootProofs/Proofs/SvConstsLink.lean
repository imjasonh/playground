import C3BootProofs.Proofs.SvExtListLink
import C3BootProofs.Spec.Sigstore

/-!
# `sigstore::verify`'s constants as the specification's

The OIDs and strings in `SvData`'s three tables, and the ones the image keeps
on their own (`SvOidData`), as the values `Spec/X509.lean`, `Spec/Tsa.lean`,
and `Spec/Checkpoint.lean` name.
-/

namespace C3.RV32.Sv

open C3.Image

/-- The OIDs and strings that `sigstore::verify` reads outside `SvData`'s
tables, where the image puts them. -/
structure SvOidData (M : Word → BitVec 8) : Prop where
  ecdsa384 : CodeIn M (BitVec.ofNat 32 svOidEcdsaSha384Address) svOidEcdsaSha384Data
  prime256 : CodeIn M (BitVec.ofNat 32 svOidPrime256v1Address) svOidPrime256v1Data
  ecpub : CodeIn M (BitVec.ofNat 32 svOidEcPublicKeyAddress) svOidEcPublicKeyData
  newline : CodeIn M (BitVec.ofNat 32 svNewlineAddress) svNewlineData
  dash : CodeIn M (BitVec.ofNat 32 svDashAddress) svDashData

theorem sv_tab {M : Word → BitVec 8} {q : Word} {d : List Nat} (D : CodeIn M q d) (hd : ∀ k, k < d.length → d.getD k 0 < 256)
    {a : Word} (i n : Nat) {v : Bytes} (ha : a = q + BitVec.ofNat 32 i) (hn : i + n ≤ d.length)
    (hv : (List.range n).map (fun j => d.getD (i + j) 0) = v) : memBytes M a n = v := by
  rw [ha, CodeIn.mbc D hd hn, hv]

set_option maxRecDepth 100000

theorem sv_ecdsa384 {M : Word → BitVec 8} (D : SvOidData M) :
    memBytes M (BitVec.ofNat 32 (img% svOidEcdsaSha384Address)) 8 = oidEcdsaSha384 :=
  sv_tab D.ecdsa384 (by decide) 0 8 (by decide) (by decide) (by decide)
theorem sv_prime256 {M : Word → BitVec 8} (D : SvOidData M) :
    memBytes M (BitVec.ofNat 32 (img% svOidPrime256v1Address)) 8 = oidPrime256v1 :=
  sv_tab D.prime256 (by decide) 0 8 (by decide) (by decide) (by decide)
theorem sv_ecpub {M : Word → BitVec 8} (D : SvOidData M) :
    memBytes M (BitVec.ofNat 32 (img% svOidEcPublicKeyAddress)) 7 = oidEcPublicKey :=
  sv_tab D.ecpub (by decide) 0 7 (by decide) (by decide) (by decide)
theorem sv_newline {M : Word → BitVec 8} (D : SvOidData M) : memBytes M (BitVec.ofNat 32 (img% svNewlineAddress)) 1 = [0x0A] :=
  sv_tab D.newline (by decide) 0 1 (by decide) (by decide) (by decide)
theorem sv_sigPrefix {M : Word → BitVec 8} (D : SvOidData M) : memBytes M (BitVec.ofNat 32 (img% svDashAddress)) 4 = sigLinePrefix :=
  sv_tab D.dash (by decide) 0 4 (by decide) (by decide) (by decide)

theorem sv_ecdsa256 {M : Word → BitVec 8} (D : SvData M) : memBytes M (BitVec.ofNat 32 (img% svConstAddress)) 8 = oidEcdsaSha256 :=
  sv_tab D.c (by decide) 0 8 (by decide) (by decide) (by decide)
theorem sv_signedData {M : Word → BitVec 8} (D : SvData M) :
    memBytes M (BitVec.ofNat 32 (img% svConstCmsAddress)) 9 = oidSignedData :=
  sv_tab D.cms (by decide) 0 9 (by decide) (by decide) (by decide)
theorem sv_tstInfo {M : Word → BitVec 8} (D : SvData M) :
    memBytes M (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11 = oidTstInfo :=
  sv_tab D.cms (by decide) 0x9 11 (by decide) (by decide) (by decide)
theorem sv_setTag {M : Word → BitVec 8} (D : SvData M) : memBytes M (BitVec.ofNat 32 (img% svConstCmsAddress + 0x14)) 1 = [0x31] :=
  sv_tab D.cms (by decide) 0x14 1 (by decide) (by decide) (by decide)
theorem sv_contentType {M : Word → BitVec 8} (D : SvData M) :
    memBytes M (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9 = oidContentType :=
  sv_tab D.cms (by decide) 0x15 9 (by decide) (by decide) (by decide)
theorem sv_messageDigest {M : Word → BitVec 8} (D : SvData M) :
    memBytes M (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9 = oidMessageDigest :=
  sv_tab D.cms (by decide) 0x1E 9 (by decide) (by decide) (by decide)

theorem sv_extConsts {M : Word → BitVec 8} (D : SvData M) : ExtConsts M where
  ku := sv_tab D.ext (by decide) 0 3 (by decide) (by decide) (by decide)
  san := sv_tab D.ext (by decide) 0x3 3 (by decide) (by decide) (by decide)
  bc := sv_tab D.ext (by decide) 0x6 3 (by decide) (by decide) (by decide)
  eku := sv_tab D.ext (by decide) 0x9 3 (by decide) (by decide) (by decide)
  cs := sv_tab D.c (by decide) 0x8 8 (by decide) (by decide) (by decide)
  p0 := sv_tab D.ext (by decide) 0x2D 10 (by decide) (by decide) (by decide)
  p1 := sv_tab D.ext (by decide) 0x37 10 (by decide) (by decide) (by decide)
  p2 := sv_tab D.ext (by decide) 0x41 10 (by decide) (by decide) (by decide)
  p3 := sv_tab D.ext (by decide) 0x4B 10 (by decide) (by decide) (by decide)
  p4 := sv_tab D.ext (by decide) 0x55 10 (by decide) (by decide) (by decide)

end C3.RV32.Sv
