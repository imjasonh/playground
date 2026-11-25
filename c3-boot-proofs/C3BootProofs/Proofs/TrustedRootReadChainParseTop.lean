import C3BootProofs.Proofs.TrustedRootReadChainParse

/-!
# The front of `parse_cert` inside `read_chain`

The blocks from 0x148 to 0x1EF: the certificate's outer sequence, its
three parts, and the `tbsCertificate`'s optional version. They end in
`RcCtx.pSerial`.
-/

namespace C3.RV32

open C3.Image C3.Json C3.RV32.Dq C3.RV32.P3

set_option maxRecDepth 20000

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

/-- From 0x1D0: the reader over the `tbsCertificate`'s contents `tr` at
`F + 0xB0`, its optional version, then the serial number at 0x1F0. -/
theorem RcCtx.pTbs (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f w : Fin 32 → Word}
    {B : Word} {L : Bytes} {tr : RcRd} {kc : Word}
    {r : Except (Option Nat) (RcCert × RcSt)}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hK : RcK [19, 21, 24, 27] w f)
    (hL : RcL M G B L) (h9 : f 9 = B + BitVec.ofNat 32 tr.1) (h8 : f 8 = BitVec.ofNat 32 tr.2)
    (htr : tr.1 + tr.2 ≤ L.length) (h22 : f 22 = kc) (h23 : f 23 = F + BitVec.ofNat 32 0xE5)
    (hok : ∀ c, rcTbs L B tr = .ok c →
      RcCertK M0 G F out fr fp fl g0 w (trPost (rcMem M0 G out fr fp fl r) g0) M kc c)
    (herr : ∀ e, rcTbs L B tr = .error e → r = .error e) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x1D0 f := by
  refine WP.sw trc_at_1d0 (by rw [hR.2.1]; exact X.fal (c := 0xB0) (by decide))
    (by rw [hR.2.1]; exact X.flo (c := 0xB0) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_1d2 (by rw [hR.2.1]; exact X.fal (c := 0xB4) (by decide))
    (by rw [hR.2.1]; exact X.flo (c := 0xB4) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_1d4 (by rw [hR.2.1]; exact X.fal (c := 0xB8) (by decide))
    (by rw [hR.2.1]; exact X.flo (c := 0xB8) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_1d6 (by rw [hR.2.1]; exact X.fal (c := 0xBC) (by decide))
    (by rw [hR.2.1]; exact X.flo (c := 0xBC) (k := 4) (by decide)) ?_; wn
  rw [hR.2.1, h9, h8]
  have hM1 : ∀ a b : Word,
      RcKeep G M (memStore32 (memStore32 (memStore32 (memStore32 M (F + 176) a) (F + 180) b) (F + 184)
        (B + BitVec.ofNat 32 tr.1)) (F + 188) (BitVec.ofNat 32 tr.2)) ∧
      RcMemInv M0 G F fr fp fl g0 (memStore32 (memStore32 (memStore32 (memStore32 M (F + 176) a) (F + 180) b)
        (F + 184) (B + BitVec.ofNat 32 tr.1)) (F + 188) (BitVec.ofNat 32 tr.2)) ∧
      RcRdAt (memStore32 (memStore32 (memStore32 (memStore32 M (F + 176) a) (F + 180) b) (F + 184)
        (B + BitVec.ofNat 32 tr.1)) (F + 188) (BitVec.ofNat 32 tr.2)) (F + BitVec.ofNat 32 0xB0) B L tr :=
    fun a b =>
    ⟨(((X.stK (c := 0xB0) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0xB0 _)).trans
        (X.stK (c := 0xB4) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0xB4 _))).trans
        (X.stK (c := 0xB8) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0xB8 _))).trans
        (X.stK (c := 0xBC) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0xBC _)),
      X.stI (X.stI (X.stI (X.stI hI (c := 0xB0) (k := 4) (by decide) (X.sw32 _ 0xB0 _))
        (c := 0xB4) (k := 4) (by decide) (X.sw32 _ 0xB4 _)) (c := 0xB8) (k := 4) (by decide) (X.sw32 _ 0xB8 _))
        (c := 0xBC) (k := 4) (by decide) (X.sw32 _ 0xBC _),
      ⟨by
        rw [X.f8]
        exact (rcf_ld32o (B := F) (c := 0xB8) (d := 0xBC) (Or.inl (by decide)) (by decide) (by decide)).trans
          (memLoad32_store32_same _ _ _),
       by
        rw [show F + BitVec.ofNat 32 0xB0 + 0xC = F + BitVec.ofNat 32 0xBC from add_ofNat_assoc F 0xB0 0xC]
        exact memLoad32_store32_same _ _ _,
       htr⟩⟩
  obtain ⟨hK1, hI1, hr1⟩ := hM1 _ _
  refine WP.aluImm trc_at_1d8 ?_; wn
  refine WP.aluImm trc_at_1da ?_; wn
  refine WP.aluImm trc_at_1dc ?_; wn
  refine X.callOpt (off := 0x1E0) (oc := 0xE0) (dc := 0xB0) (tag := 0xA0) trc_at_1e0 trc_at_1e4 (by decide)
    (by decide) (by rc_r hR) hI1 (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl)
    (by trsimp; rw [hR.2.1]; rfl) (by trsimp) (by decide) (hL.keep hK1) hr1 (fun m2 hK2 _ hI2 hT => ?_)
  refine WP.lbu trc_at_1e8 ?_; wn
  have hKB : RcKB G 0x24 M m2.mem := (hK1.trans hK2).kb
  rcases hO : derOptRes 0xA0 (rcView L tr) with _ | (e | u)
  · rw [hO] at hT
    refine WP.branch trc_at_1ec (fun ht => absurd ht (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hT.1]; decide)) (fun _ => ?_); wn
    have hsel : rcTbs L B tr = rcSerial L B tr := by simp only [rcTbs, hO]
    exact X.pSerial (by rc_r hR) hI2 (by rc_k hK) ((hL.keep hK1).keep hK2) hT.2 (by trsimp; exact h22)
      (by trsimp; exact h23) (fun c hc => (hok c (hsel.trans hc)).mono hKB) (fun e he => herr e (hsel.trans he))
  · rw [hO] at hT
    refine WP.branch trc_at_1ec (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hT.1]; decide)); wn
    refine X.e4f6 (herr (some (derErrByte e).toNat) (by simp only [rcTbs, hO])) (by rc_r hR) hI2 (fun b hb => ?_)
    cases hb
    exact ((congrArg m2.mem (add_ofNat_assoc F 0xE0 1)).symm.trans hT.2).trans (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
  · rw [hO] at hT
    refine WP.branch trc_at_1ec (fun ht => absurd ht (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hT.1]; decide)) (fun _ => ?_); wn
    have hsel : rcTbs L B tr = rcSerial L B (rcAdv tr u) := by simp only [rcTbs, hO]
    exact X.pSerial (by rc_r hR) hI2 (by rc_k hK) ((hL.keep hK1).keep hK2) hT.2.1 (by trsimp; exact h22)
      (by trsimp; exact h23) (fun c hc => (hok c (hsel.trans hc)).mono hKB) (fun e he => herr e (hsel.trans he))

end

end C3.RV32
