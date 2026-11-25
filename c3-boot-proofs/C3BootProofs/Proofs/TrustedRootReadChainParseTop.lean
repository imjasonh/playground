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

set_option maxHeartbeats 1000000 in
/-- From 0x148: the decoded certificate, the bytes `L` at `B`, then its outer
sequence, the three parts of its contents, and the checks on them, then the
`tbsCertificate` at 0x1D0. -/
theorem RcCtx.pOuter (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f w : Fin 32 → Word}
    {B : Word} {L : Bytes} {kc : Word}
    {r : Except (Option Nat) (RcCert × RcSt)}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hK : RcK [19, 21, 24, 27] w f)
    (hL : RcL M G B L) (hD0 : memLoad32 M (F + BitVec.ofNat 32 0xD0) = B)
    (hD4 : memLoad32 M (F + BitVec.ofNat 32 0xD4) = BitVec.ofNat 32 L.length)
    (h9 : f 9 = F + BitVec.ofNat 32 0xA5) (h20 : f 20 = F + BitVec.ofNat 32 0xE5) (h22 : f 22 = kc)
    (h23 : f 23 = F + BitVec.ofNat 32 0xE5)
    (hok : ∀ c, rcParse L B = .ok c →
      RcCertK M0 G F out fr fp fl g0 w (trPost (rcMem M0 G out fr fp fl r) g0) M kc c)
    (herr : ∀ e, rcParse L B = .error e → r = .error e) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x148 f := by
  have hw := hL.hw
  have hD0' : memLoad32 M (F + 0xD0) = B := hD0
  have hD4' : memLoad32 M (F + 0xD4) = BitVec.ofNat 32 L.length := hD4
  have hB : B ≠ 0 := fun h => by have := hL.pos; rw [h] at this; exact absurd this (by decide)
  refine WP.lw trc_at_148 (by rw [hR.2.1]; exact X.fal (c := 0xD0) (by decide)) ?_; wn
  refine WP.branch trc_at_14a (fun ht => absurd ht (by trsimp; rw [hR.2.1, hD0', rck_beqF hB]; decide))
    (fun _ => ?_); wn
  refine WP.lw trc_at_14e (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xD4) (by decide)) ?_; wn
  refine WP.sw trc_at_150 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0x90) (by decide))
    (by (try trsimp); rw [hR.2.1]; exact X.flo (c := 0x90) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_152 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0x94) (by decide))
    (by (try trsimp); rw [hR.2.1]; exact X.flo (c := 0x94) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_154 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0x98) (by decide))
    (by (try trsimp); rw [hR.2.1]; exact X.flo (c := 0x98) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_156 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0x9C) (by decide))
    (by (try trsimp); rw [hR.2.1]; exact X.flo (c := 0x9C) (k := 4) (by decide)) ?_; wn
  rw [hR.2.1, hD0', hD4']
  have hK1 : RcKeep G M (memStore32 (memStore32 (memStore32 (memStore32 M (F + 144) B) (F + 148)
      (BitVec.ofNat 32 L.length)) (F + 152) B) (F + 156) (BitVec.ofNat 32 L.length)) :=
    ((X.stK (c := 0x90) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0x90 _)).trans
      (X.stK (c := 0x94) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0x94 _))).trans
      (X.stK (c := 0x98) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0x98 _)) |>.trans
      (X.stK (c := 0x9C) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0x9C _))
  have hI1 : RcMemInv M0 G F fr fp fl g0 (memStore32 (memStore32 (memStore32 (memStore32 M (F + 144) B)
      (F + 148) (BitVec.ofNat 32 L.length)) (F + 152) B) (F + 156) (BitVec.ofNat 32 L.length)) :=
    X.stI (X.stI (X.stI (X.stI hI (c := 0x90) (k := 4) (by decide) (X.sw32 _ 0x90 _))
      (c := 0x94) (k := 4) (by decide) (X.sw32 _ 0x94 _)) (c := 0x98) (k := 4) (by decide) (X.sw32 _ 0x98 _))
      (c := 0x9C) (k := 4) (by decide) (X.sw32 _ 0x9C _)
  have hr1 : RcRdAt (memStore32 (memStore32 (memStore32 (memStore32 M (F + 144) B) (F + 148)
      (BitVec.ofNat 32 L.length)) (F + 152) B) (F + 156) (BitVec.ofNat 32 L.length))
      (F + BitVec.ofNat 32 0x90) B L (0, L.length) := by
    refine ⟨?_, ?_, Nat.le_of_eq (Nat.zero_add _)⟩
    · rw [X.f8]
      exact (rcf_ld32o (B := F) (c := 0x98) (d := 0x9C) (Or.inl (by decide)) (by decide) (by decide)).trans
        ((memLoad32_store32_same _ _ _).trans (BitVec.add_zero B).symm)
    · rw [show F + BitVec.ofNat 32 0x90 + 0xC = F + BitVec.ofNat 32 0x9C from add_ofNat_assoc F 0x90 0xC]
      exact memLoad32_store32_same _ _ _
  refine WP.aluImm trc_at_158 ?_; wn
  refine WP.aluImm trc_at_15a ?_; wn
  refine X.callSeq (off := 0x15C) (oc := 0xE0) (dc := 0x90) trc_at_15c trc_at_160 (by decide) (by decide)
    (by rc_r hR) hI1 (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    (hL.keep hK1) hr1 (fun m2 hK2 _ hI2 hT => ?_)
  refine WP.lw trc_at_164 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  refine WP.lbu trc_at_166 ?_; wn
  rcases hE : rcElem L 0x30 (0, L.length) with e | c
  · rw [hE] at hT
    refine WP.branch trc_at_16a (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hT.1]; decide)); wn
    refine X.e504 (herr e (by simp only [rcParse, hE])) (by rc_r hR) hI2 (fun b hb => ?_)
    trsimp; rw [hR.2.1, tlv_zext]; exact rcp_e4 hT.2 b hb
  rw [hE] at hT
  obtain ⟨e0, hin, hadv, hb⟩ := hT
  have hb' : c.header + c.len ≤ L.length := hb
  have e0' : memLoad32 m2.mem (F + 0xE0) = B + BitVec.ofNat 32 (0 + c.header) := e0
  refine WP.branch trc_at_16a (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, e0', rck_beqF (rck_pne hL (by omega))]; decide)) (fun _ => ?_); wn
  refine WP.aluImm trc_at_16e ?_; wn
  refine WP.alu trc_at_170 ?_; wn
  refine WP.alu trc_at_172 ?_; wn
  refine X.callMc (off := 0x174) (dd := 0xA5) (N := 0xB) (src := F + BitVec.ofNat 32 0xE5) trc_at_174 trc_at_178
    (by decide) (by decide) (by rc_r hR) hI2 (by trsimp; exact h9) (by trsimp; exact h20) (by trsimp)
    (by decide) (by rw [X.fG, X.gc (by decide)]; have := X.gw; omega)
    (by rw [X.fG]; exact X.gsep (Or.inr (by decide)) (by decide) (by decide))
    (by rw [X.fG, X.fG]; exact X.gsep (Or.inl (by decide)) (by decide) (by decide)) (fun m3 hI3 hC3 => ?_)
  have hK3 : RcKeep G M m3.mem := (hK1.trans hK2).trans (X.mcKeep (by decide) (by decide) hC3)
  have hin3 : RcRdAt m3.mem (F + BitVec.ofNat 32 0xA0) B L (rcIn (0, L.length) c) := by
    refine ⟨?_, ?_, hin.2.2⟩
    · rw [X.f8]
      exact (X.cpLd hC3 ⟨by decide, by decide⟩ (by decide)).trans (by
        rw [add_ofNat_assoc]; exact (congrArg _ (add_ofNat_assoc F 0xE0 8)).symm.trans hin.1)
    · rw [show F + BitVec.ofNat 32 0xA0 + 0xC = F + BitVec.ofNat 32 0xAC from add_ofNat_assoc F 0xA0 0xC]
      exact (X.cpLd hC3 ⟨by decide, by decide⟩ (by decide)).trans (by
        rw [add_ofNat_assoc]; exact (congrArg _ (add_ofNat_assoc F 0xE0 0xC)).symm.trans hin.2.1)
  have hadv3 : RcRdAt m3.mem (F + BitVec.ofNat 32 0x90) B L (rcAdv (0, L.length) c) :=
    X.cpRdO hC3 hadv (by decide) (by decide) (by decide)
  have h9C : memLoad32 m3.mem (F + 156) = BitVec.ofNat 32 (L.length - (c.header + c.len)) :=
    (congrArg (memLoad32 m3.mem) (add_ofNat_assoc F 0x90 0xC)).symm.trans hadv3.2.1
  refine WP.lw trc_at_17c (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x9C) (by decide)) ?_; wn
  refine WP.sw trc_at_17e (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xA0) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xA0) (k := 4) (by decide)) ?_; wn
  refine WP.sb trc_at_180 (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xA4) (k := 1) (by decide)) ?_; wn
  refine WP.aluImm trc_at_184 ?_; wn
  rw [hR.2.1, h9C]
  have hM4 : ∀ (a : Word) (cb : BitVec 8),
      RcKeep G M (memStore8 (memStore32 m3.mem (F + 160) a) (F + 164) cb) ∧
      RcMemInv M0 G F fr fp fl g0 (memStore8 (memStore32 m3.mem (F + 160) a) (F + 164) cb) ∧
      RcRdAt (memStore8 (memStore32 m3.mem (F + 160) a) (F + 164) cb) (F + BitVec.ofNat 32 0xA0) B L
        (rcIn (0, L.length) c) := fun a cb =>
    ⟨(hK3.trans (X.stK (c := 0xA0) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0xA0 _))).trans
        (X.stK (c := 0xA4) (k := 1) ⟨by decide, by decide⟩ (X.sw8 _ 0xA4 _)),
      X.stI (X.stI hI3 (c := 0xA0) (k := 4) (by decide) (X.sw32 _ 0xA0 _)) (c := 0xA4) (k := 1) (by decide)
        (X.sw8 _ 0xA4 _),
      rcp_rdSb (d := 0xA4) (rcp_rdSt (d := 0xA0) hin3 (by decide) (by decide) (by decide)) (by decide) (by decide)
        (by decide)⟩
  obtain ⟨hK4, hI4, hin4⟩ := hM4 _ _
  have hb1 := hin4.2.2
  by_cases hz : L.length - (c.header + c.len) ≠ 0
  · refine WP.branch trc_at_186 (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [rck_bneT (rck_nz hz (by omega))]; decide)); wn
    refine X.e504 (herr (some 1) ?_) (by rc_r hR) hI4 (fun b hb => ?_)
    · simp only [rcParse, hE]; rw [ite_eq_left hz]
    · cases hb; trsimp
  replace hz : L.length - (c.header + c.len) = 0 := by omega
  refine WP.branch trc_at_186 (fun ht => absurd ht (by trsimp; rw [hz]; decide)) (fun _ => ?_); wn
  have hsel0 : rcParse L B = rcBody L B (rcIn (0, L.length) c) := by
    simp only [rcParse, hE]; rw [ite_eq_right (by omega)]
  refine WP.aluImm trc_at_18a ?_; wn
  refine WP.aluImm trc_at_18c ?_; wn
  refine WP.aluImm trc_at_18e ?_; wn
  refine X.callElem (off := 0x192) (oc := 0xE0) (dc := 0xA0) (tag := 0x30) trc_at_192 trc_at_196 (by decide)
    (by decide) hI4 (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    (by trsimp) (by decide) (hL.keep hK4) hin4 (fun m5 hK5 _ hI5 hT5 => ?_)
  refine WP.lw trc_at_19a (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  rcases hE1 : rcElem L 0x30 (rcIn (0, L.length) c) with e | tbs
  · rw [hE1] at hT5
    refine WP.branch trc_at_19c (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hT5.1]; decide)); wn
    exact X.e4d2 (herr e (hsel0.trans (by simp only [rcBody, hE1]))) (by rc_r hR) hI5 (rcp_e4 hT5.2)
  rw [hE1] at hT5
  obtain ⟨t0, t4, -, -, hra5, hbt⟩ := hT5
  have t0' : memLoad32 m5.mem (F + 0xE0) = B + BitVec.ofNat 32 ((rcIn (0, L.length) c).1 + tbs.header) := t0
  have t4' : memLoad32 m5.mem (F + 228) = BitVec.ofNat 32 tbs.len :=
    (congrArg (memLoad32 m5.mem) (add_ofNat_assoc F 0xE0 4)).symm.trans t4
  refine WP.branch trc_at_19c (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, t0', rck_beqF (rck_pne hL (by simp only [rcIn] at hbt hb1 ⊢; omega))]; decide))
    (fun _ => ?_); wn
  refine WP.lw trc_at_1a0 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE4) (by decide)) ?_; wn
  have hra52 := hra5.2.2
  refine WP.aluImm trc_at_1a2 ?_; wn
  refine WP.aluImm trc_at_1a4 ?_; wn
  refine WP.aluImm trc_at_1a6 ?_; wn
  refine X.callElem (off := 0x1AA) (oc := 0xE0) (dc := 0xA0) (tag := 0x30) trc_at_1aa trc_at_1ae (by decide)
    (by decide) hI5 (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    (by trsimp) (by decide) ((hL.keep hK4).keep hK5) hra5 (fun m6 hK6 _ hI6 hT6 => ?_)
  refine WP.lw trc_at_1b2 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  rcases hE2 : rcElem L 0x30 (rcAdv (rcIn (0, L.length) c) tbs) with e | a
  · rw [hE2] at hT6
    refine WP.branch trc_at_1b4 (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hT6.1]; decide)); wn
    exact X.e4d2 (herr e (hsel0.trans (by simp only [rcBody, hE1, hE2]))) (by rc_r hR) hI6 (rcp_e4 hT6.2)
  rw [hE2] at hT6
  obtain ⟨q0, -, -, -, hra6, hba⟩ := hT6
  have q0' : memLoad32 m6.mem (F + 0xE0) =
      B + BitVec.ofNat 32 ((rcAdv (rcIn (0, L.length) c) tbs).1 + a.header) := q0
  refine WP.branch trc_at_1b4 (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, q0', rck_beqF (rck_pne hL (by simp only [rcAdv] at hba hra52 ⊢; omega))]; decide))
    (fun _ => ?_); wn
  have hra62 := hra6.2.2
  refine WP.aluImm trc_at_1b8 ?_; wn
  refine WP.aluImm trc_at_1ba ?_; wn
  refine X.callBits (off := 0x1BC) (oc := 0xE0) (dc := 0xA0) trc_at_1bc trc_at_1c0 (by decide) (by decide)
    (by rc_r hR) hI6 (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    (((hL.keep hK4).keep hK5).keep hK6) hra6 (fun m7 hK7 _ hI7 hBo => ?_)
  refine WP.lw trc_at_1c4 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  rcases hE3 : rcElem L 3 (rcAdv (rcAdv (rcIn (0, L.length) c) tbs) a) with e | bt
  · rw [hE3] at hBo
    refine WP.branch trc_at_1c6 (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hBo.1]; decide)); wn
    exact X.e4d2 (herr e (hsel0.trans (by simp only [rcBody, hE1, hE2, hE3]))) (by rc_r hR) hI7 (rcp_e4 hBo.2)
  rw [hE3] at hBo
  by_cases hc' : ¬(bt.len ≠ 0 ∧ (rcView L (rcAdv (rcAdv (rcIn (0, L.length) c) tbs) a)).getD bt.header 0 = 0)
  · have hc := hc'
    simp only [RcBitsOut] at hBo
    rw [ite_eq_right hc] at hBo
    refine WP.branch trc_at_1c6 (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hBo.1]; decide)); wn
    refine X.e4d2 (herr (some 0x14) (hsel0.trans ?_)) (by rc_r hR) hI7 (fun v hv => ?_)
    · simp only [rcBody, hE1, hE2, hE3]; rw [ite_eq_left hc]
    · cases hv; exact (congrArg m7.mem (add_ofNat_assoc F 0xE0 4)).symm.trans hBo.2
  have hc : bt.len ≠ 0 ∧ (rcView L (rcAdv (rcAdv (rcIn (0, L.length) c) tbs) a)).getD bt.header 0 = 0 :=
    Classical.byContradiction hc'
  simp only [RcBitsOut] at hBo
  rw [ite_eq_left hc] at hBo
  obtain ⟨b0, -, hra7, hbb⟩ := hBo
  have hc1 := hc.1
  have b0' : memLoad32 m7.mem (F + 0xE0) =
      B + BitVec.ofNat 32 ((rcAdv (rcAdv (rcIn (0, L.length) c) tbs) a).1 + bt.header + 1) := b0
  refine WP.branch trc_at_1c6 (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, b0', rck_beqF (rck_pne hL (by simp only [rcAdv] at hbb hra62 ⊢; omega))]; decide))
    (fun _ => ?_); wn
  refine WP.lw trc_at_1ca (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xAC) (by decide)) ?_; wn
  have hAC : memLoad32 m7.mem (F + 172) =
      BitVec.ofNat 32 (rcAdv (rcAdv (rcAdv (rcIn (0, L.length) c) tbs) a) bt).2 :=
    (congrArg (memLoad32 m7.mem) (add_ofNat_assoc F 0xA0 0xC)).symm.trans hra7.2.1
  have hra72 := hra7.2.2
  by_cases hz2 : (rcAdv (rcAdv (rcAdv (rcIn (0, L.length) c) tbs) a) bt).2 ≠ 0
  · refine WP.branch trc_at_1cc (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, hAC, rck_bneT (rck_nz hz2 (by omega))]; decide)); wn
    refine X.e504 (herr (some 1) (hsel0.trans ?_)) (by rc_r hR) hI7 (fun v hv => ?_)
    · simp only [rcBody, hE1, hE2, hE3]; rw [ite_eq_right (fun h => h hc), ite_eq_left hz2]
    · cases hv; trsimp
  replace hz2 : (rcAdv (rcAdv (rcAdv (rcIn (0, L.length) c) tbs) a) bt).2 = 0 := by omega
  refine WP.branch trc_at_1cc (fun ht => absurd ht (by trsimp; rw [hR.2.1, hAC, hz2]; decide))
    (fun _ => ?_); wn
  have hsel : rcParse L B = rcTbs L B (rcIn (rcIn (0, L.length) c) tbs) := hsel0.trans (by
    simp only [rcBody, hE1, hE2, hE3]; rw [ite_eq_right (fun h => h hc), ite_eq_right (by omega)])
  have hKB : RcKB G 0x24 M m7.mem := (((hK4.trans hK5).trans hK6).trans hK7).kb
  exact X.pTbs (by rc_r hR) hI7 (by rc_k hK) ((((hL.keep hK4).keep hK5).keep hK6).keep hK7)
    (by trsimp; (try rw [hR.2.1]); exact t0') (by trsimp; (try rw [hR.2.1]); exact t4')
    (by simp only [rcIn] at hbt hb1 ⊢; omega) (by trsimp; exact h22) (by trsimp; exact h23)
    (fun c hc => (hok c (hsel.trans hc)).mono hKB) (fun e he => herr e (hsel.trans he))

end

end C3.RV32
