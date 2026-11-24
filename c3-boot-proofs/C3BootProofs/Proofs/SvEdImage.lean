import C3BootProofs.Proofs.SvSpecAux
import C3BootProofs.Models.Ed25519Closed
import C3BootProofs.Image.BootloaderData5
import C3BootProofs.Image.BootloaderData7

/-!
# The Ed25519 model's constants, from the image

`EdImage.ofCode` and `KImage.ofCode` derive the constants that
`svEdModel_closed` takes from the image's bytes. `EdImage.congr` and
`KImage.congr` carry them to memory that agrees on the read-only data, such
as `sigMem`, which differs from the caller's memory only in a stack slot.
-/

namespace C3.RV32.EdM

open C3.Image C3.RV32.Sv

theorem EdImage.congr {M M' : Word → BitVec 8} (h : RoAgree M M') (I : EdImage M) : EdImage M' where
  order := (ro_mb h (img% edOrderAddress) 32 (by omega) (by omega)).symm.trans I.order
  prime := (ro_mb h (img% edPrimeAddress) 32 (by omega) (by omega)).symm.trans I.prime
  xzero := ⟨(ro_mb h (img% p256OneAddress) 32 (by omega) (by omega)).symm.trans I.xzero.1,
    (ro_mb h (img% edPm1Address) 32 (by omega) (by omega)).symm.trans I.xzero.2⟩
  one := (ro_mb h edOneAddress 40 (by decide) (by decide)).symm.trans I.one
  d := (ro_mb h edDAddress 40 (by decide) (by decide)).symm.trans I.d
  sqrtM1 := (ro_mb h edSqrtM1Address 40 (by decide) (by decide)).symm.trans I.sqrtM1
  d2 := (ro_mb h (img% edwardsD2Address) 40 (by omega) (by omega)).symm.trans I.d2
  base := by rw [← ro_pt h (img% edBaseAddress) (by omega) (by omega)]; exact I.base

/-- The image's base point, its four coordinates' limbs, represents `B`. -/
theorem edBase_rep : ERep (limbsOf (edBaseData.take 40), limbsOf ((edBaseData.drop 40).take 40),
    limbsOf ((edBaseData.drop 80).take 40), limbsOf ((edBaseData.drop 120).take 40)) Ed25519.B := by
  rw [B_eq]; unfold ERep Lim; decide +kernel

theorem EdImage.ofCode {M : Word → BitVec 8}
    (LD : CodeIn M (BitVec.ofNat 32 edOrderAddress) edOrderData)
    (PD : CodeIn M (BitVec.ofNat 32 edPrimeAddress) edPrimeData)
    (UD : CodeIn M (BitVec.ofNat 32 p256OneAddress) p256OneData)
    (PmD : CodeIn M (BitVec.ofNat 32 edPm1Address) edPm1Data)
    (E1D : CodeIn M (BitVec.ofNat 32 edOneAddress) edOneData)
    (EdD : CodeIn M (BitVec.ofNat 32 edDAddress) edDData)
    (SmD : CodeIn M (BitVec.ofNat 32 edSqrtM1Address) edSqrtM1Data)
    (D2D : CodeIn M (BitVec.ofNat 32 edwardsD2Address) edwardsD2Data)
    (BsD : CodeIn M (BitVec.ofNat 32 edBaseAddress) edBaseData) : EdImage M where
  order := (codeIn_memBytes LD (by decide)).trans (by decide)
  prime := (codeIn_memBytes PD (by decide)).trans (by decide)
  xzero := ⟨(codeIn_memBytes UD (by decide)).trans (by decide), (codeIn_memBytes PmD (by decide)).trans (by decide)⟩
  one := codeIn_memBytes E1D (by decide)
  d := codeIn_memBytes EdD (by decide)
  sqrtM1 := codeIn_memBytes SmD (by decide)
  d2 := codeIn_memBytes D2D (by decide)
  base := by
    have hB : memBytes M (BitVec.ofNat 32 (img% edBaseAddress)) 160 = edBaseData := codeIn_memBytes BsD (by decide +kernel)
    have e0 : memBytes M (BitVec.ofNat 32 (img% edBaseAddress)) 40 = edBaseData.take 40 := by
      rw [← memBytes_take' (n := 160) (by decide), hB]
    have ek : ∀ k, k + 40 ≤ 160 →
        memBytes M (BitVec.ofNat 32 (img% edBaseAddress) + BitVec.ofNat 32 k) 40 = (edBaseData.drop k).take 40 :=
      fun k hk => by rw [← memBytes_drop_take hk, hB]
    unfold ptAt
    rw [feW_bytes e0, feW_bytes (ek 40 (by decide)), feW_bytes (ek 80 (by decide)), feW_bytes (ek 120 (by decide))]
    exact edBase_rep

end C3.RV32.EdM

namespace C3.RV32.EdK

open C3.Image

theorem KImage.congr {M M' : Word → BitVec 8} (h : RoAgree M M') (K : KImage M) : KImage M' where
  r := (ro_mb h (img% edMontRAddress) 36 (by omega) (by omega)).symm.trans K.r
  rr := (ro_mb h (img% edMontRRAddress) 36 (by omega) (by omega)).symm.trans K.rr

theorem KImage.ofCode {M : Word → BitVec 8}
    (KRD : CodeIn M (BitVec.ofNat 32 edMontRAddress) edMontRData)
    (KRRD : CodeIn M (BitVec.ofNat 32 edMontRRAddress) edMontRRData) : KImage M where
  r := (C3.RV32.Sv.codeIn_memBytes KRD (by decide)).trans (by decide)
  rr := (C3.RV32.Sv.codeIn_memBytes KRRD (by decide)).trans (by decide)

end C3.RV32.EdK

namespace C3.RV32.Sv

open C3.Image

/-- `sigMem` changes only the signature's 64 bytes in the frame, which lie
outside the read-only data. -/
theorem sigMem_roAgree {M : Word → BitVec 8} {B : Word} {L : Bytes} (RS : SvRoSep B) :
    RoAgree M (sigMem M (B + 0x21A0 + BitVec.ofNat 32 0x420) L) := fun i hi => by
  have hro : SvR B (BitVec.ofNat 32 ((img% roWindowAddress) + i)) := by
    have := RS.symm.sub (c := i) (l := 1) (by omega)
    rw [ofNat_add_ofNat] at this; exact this.symm
  exact (sigMem_out (svR_hi hro (by decide))).symm

/-- The Ed25519 model holds for the memory `ed25519_verify` reads in
`verify_checkpoint`, given the image's constants. -/
theorem svEdModel_sigMem {M : Word → BitVec 8} {B : Word} (RS : SvRoSep B) (I : EdM.EdImage M) (K : EdK.KImage M)
    (L : Bytes) : SvEdModel (sigMem M (B + 0x21A0 + BitVec.ofNat 32 0x420) L) :=
  EdM.svEdModel_closed (I.congr (sigMem_roAgree RS)) (K.congr (sigMem_roAgree RS))

end C3.RV32.Sv
