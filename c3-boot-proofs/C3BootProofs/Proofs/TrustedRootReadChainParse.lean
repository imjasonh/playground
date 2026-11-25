import C3BootProofs.Proofs.TrustedRootReadChainKeySeg

/-!
# `parse_cert` inside `read_chain`

The compiler inlined `parse_cert` at 0x14E to 0x2DE of `read_chain`, with
`p384_key` after it. Each lemma here covers one block of it and ends in
the next, so that every path reaches either an error writer with the
error that `rcParse` gives or the join at 0x308 with the fields of the
certificate that `rcParse` returns.
-/

namespace C3.RV32

open C3.Image C3.Json C3.RV32.Dq C3.RV32.P3

set_option maxRecDepth 20000

/-- What follows `parse_cert`: the block at 0x308, entered with the
certificate `c` in registers and in the frame below `F + 0x20`, the
window's registers `s3`, `s5`, `s8`, and `s11` as in `w`, the loop
counter `kc` at `F + 0x20`, and memory that changed from `M` only below
`F + 0x24` and in the scratch area. -/
def RcCertK (M0 : Word → BitVec 8) (G F out fr fp : Word) (fl : Nat) (g0 w : Fin 32 → Word) (Q : Post)
    (M : Word → BitVec 8) (kc : Word) (c : RcCert) : Prop :=
  ∀ (M' : Word → BitVec 8) (f' : Fin 32 → Word), RcRegs F out fr g0 f' → RcMemInv M0 G F fr fp fl g0 M' →
    RcKB G 0x24 M M' → RcK [19, 21, 24, 27] w f' →
    f' 20 = c.serial → f' 22 = BitVec.ofNat 32 c.serialLen →
    memLoad32 M' (F + BitVec.ofNat 32 0x18) = c.issuer →
    memLoad32 M' (F + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 c.issuerLen →
    memLoad32 M' (F + BitVec.ofNat 32 0x10) = c.subject →
    memLoad32 M' (F + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 c.subjectLen →
    f' 9 = BitVec.ofNat 32 (c.notBefore % 2 ^ 32) → f' 8 = BitVec.ofNat 32 (c.notBefore / 2 ^ 32) →
    f' 23 = BitVec.ofNat 32 (c.notAfter % 2 ^ 32) → f' 18 = BitVec.ofNat 32 (c.notAfter / 2 ^ 32) →
    c.notBefore < 2 ^ 64 → c.notAfter < 2 ^ 64 → f' a1 = c.key →
    memLoad32 M' (F + BitVec.ofNat 32 0x20) = kc → c.serial ≠ 0 →
    WP trustedRootReadChainCode TRC Q M' 0x308 f'

theorem RcCertK.mono {M0 : Word → BitVec 8} {G F out fr fp : Word} {fl : Nat} {g0 w : Fin 32 → Word}
    {Q : Post} {M M1 : Word → BitVec 8} {kc : Word} {c : RcCert} (k : RcCertK M0 G F out fr fp fl g0 w Q M kc c)
    (h : RcKB G 0x24 M M1) : RcCertK M0 G F out fr fp fl g0 w Q M1 kc c :=
  fun M' f' a b d => k M' f' a b (h.trans d)

/-- The error byte of a callee's result at `F + 0xE0`. -/
theorem rcp_e4 {M : Word → BitVec 8} {F : Word} {e : Option Nat}
    (h : ∀ v, e = some v → M (F + BitVec.ofNat 32 0xE0 + 4) = BitVec.ofNat 8 v) :
    ∀ v, e = some v → M (F + 0xE4) = BitVec.ofNat 8 v := by
  rwa [show F + BitVec.ofNat 32 0xE0 + 4 = F + 0xE4 from add_ofNat_assoc F 0xE0 4] at h

/-- A frame reader that a word store apart from it keeps. -/
theorem rcp_rdSt {M : Word → BitVec 8} {F B v : Word} {L : Bytes} {r : RcRd} {dc d : Nat}
    (h : RcRdAt M (F + BitVec.ofNat 32 dc) B L r) (hd : d + 4 ≤ dc + 8 ∨ dc + 16 ≤ d) (hdc : dc + 16 ≤ 0x180)
    (hd' : d + 4 ≤ 0x180) : RcRdAt (memStore32 M (F + BitVec.ofNat 32 d) v) (F + BitVec.ofNat 32 dc) B L r :=
  h.keep (by
      rw [show F + BitVec.ofNat 32 dc + 8 = F + BitVec.ofNat 32 (dc + 8) from add_ofNat_assoc F dc 8]
      exact rcf_ld32o (by omega) (by omega) (by omega))
    (by
      rw [show F + BitVec.ofNat 32 dc + 0xC = F + BitVec.ofNat 32 (dc + 0xC) from add_ofNat_assoc F dc 0xC]
      exact rcf_ld32o (by omega) (by omega) (by omega))

/-- A frame reader that a byte store apart from it keeps. -/
theorem rcp_rdSb {M : Word → BitVec 8} {F B : Word} {v : BitVec 8} {L : Bytes} {r : RcRd} {dc d : Nat}
    (h : RcRdAt M (F + BitVec.ofNat 32 dc) B L r) (hd : d + 1 ≤ dc + 8 ∨ dc + 16 ≤ d) (hdc : dc + 16 ≤ 0x180)
    (hd' : d + 1 ≤ 0x180) : RcRdAt (memStore8 M (F + BitVec.ofNat 32 d) v) (F + BitVec.ofNat 32 dc) B L r :=
  h.keep (by
      rw [show F + BitVec.ofNat 32 dc + 8 = F + BitVec.ofNat 32 (dc + 8) from add_ofNat_assoc F dc 8]
      exact rcf_ld8o (by omega) (by omega) (by omega))
    (by
      rw [show F + BitVec.ofNat 32 dc + 0xC = F + BitVec.ofNat 32 (dc + 0xC) from add_ofNat_assoc F dc 0xC]
      exact rcf_ld8o (by omega) (by omega) (by omega))

theorem rcp_kl_cases : ∀ q : Fin 32, q.val ∈ rcKL →
    q = 8 ∨ q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 20 ∨ q = 21 ∨ q = 22 ∨ q = 23 ∨ q = 24 ∨ q = 27 := by
  decide

theorem rcp_k4_cases : ∀ q : Fin 32, q.val ∈ [19, 21, 24, 27] → q = 19 ∨ q = 21 ∨ q = 24 ∨ q = 27 := by
  decide

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

/-- A frame word at `F + 0x10` or above that a change below `F + lo` keeps. -/
theorem RcCtx.kbLd (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {lo c : Nat}
    (h : RcKB G lo M M') (hc : lo ≤ c ∧ c + 4 ≤ 0x60) :
    memLoad32 M' (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by
    rw [X.fG, add_ofNat_assoc]
    exact h _ (sep_offsets G (c := 0) (n := 0x5C0 + lo) (d := 0x5C0 + c + j) (k := 1)
        (Or.inl (by omega)) (by omega) (by omega) |> fun s => by rwa [add_ofNat_zero] at s)
      (sep_offsets G (c := 0x620) (n := 0xEC) (d := 0x5C0 + c + j) (k := 1)
        (Or.inr (by omega)) (by omega) (by omega))

/-- From 0x2A0: the subject and the subject public key, then `p384_key`. -/
theorem RcCtx.pSubj (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f w : Fin 32 → Word}
    {B : Word} {L : Bytes} {sr ir t : RcRd} {nb na : Nat} {kc : Word}
    {r : Except (Option Nat) (RcCert × RcSt)}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hK : RcK [19, 21, 24, 27] w f)
    (hL : RcL M G B L) (hr : RcRdAt M (F + BitVec.ofNat 32 0xB0) B L t)
    (h20 : f 20 = B + BitVec.ofNat 32 sr.1) (h22 : f 22 = BitVec.ofNat 32 sr.2)
    (hm18 : memLoad32 M (F + BitVec.ofNat 32 0x18) = B + BitVec.ofNat 32 ir.1)
    (hm1C : memLoad32 M (F + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ir.2)
    (h9 : f 9 = BitVec.ofNat 32 (nb % 2 ^ 32)) (h8 : f 8 = BitVec.ofNat 32 (nb / 2 ^ 32))
    (h23 : f 23 = BitVec.ofNat 32 (na % 2 ^ 32)) (h18 : f 18 = BitVec.ofNat 32 (na / 2 ^ 32))
    (hnb : nb < 2 ^ 64) (hna : na < 2 ^ 64) (hm20 : memLoad32 M (F + BitVec.ofNat 32 0x20) = kc)
    (hs : sr.1 ≤ L.length)
    (hok : ∀ c, rcSubj L B sr ir nb na t = .ok c →
      RcCertK M0 G F out fr fp fl g0 w (trPost (rcMem M0 G out fr fp fl r) g0) M kc c)
    (herr : ∀ e, rcSubj L B sr ir nb na t = .error e → r = .error e) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x2A0 f := by
  have hw := hL.hw
  have hr2 := hr.2.2
  refine WP.aluImm trc_at_2a0 ?_; wn
  refine WP.aluImm trc_at_2a2 ?_; wn
  refine WP.aluImm trc_at_2a4 ?_; wn
  refine X.callElem (off := 0x2A8) (oc := 0xE0) (dc := 0xB0) (tag := 0x30) trc_at_2a8 trc_at_2ac (by decide)
    (by decide) hI (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    (by trsimp) (by decide) hL hr (fun m2 hK2 _ hI2 hT => ?_)
  refine WP.lw trc_at_2b0 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  rcases hE : rcElem L 0x30 t with e | s
  · rw [hE] at hT
    refine WP.branch trc_at_2b2 (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hT.1]; decide)); wn
    exact X.e4d2 (herr e (by simp only [rcSubj, hE])) (by rc_r hR) hI2 (rcp_e4 hT.2)
  rw [hE] at hT
  obtain ⟨e0, -, e8, eC, hra, hb⟩ := hT
  have e0' : memLoad32 m2.mem (F + 0xE0) = B + BitVec.ofNat 32 (t.1 + s.header) := e0
  have e8' : memLoad32 m2.mem (F + 232) = B + BitVec.ofNat 32 t.1 :=
    (congrArg (memLoad32 m2.mem) (add_ofNat_assoc F 0xE0 8)).symm.trans e8
  have eC' : memLoad32 m2.mem (F + 236) = BitVec.ofNat 32 (s.header + s.len) :=
    (congrArg (memLoad32 m2.mem) (add_ofNat_assoc F 0xE0 0xC)).symm.trans eC
  refine WP.branch trc_at_2b2 (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, e0', rck_beqF (rck_pne hL (by omega))]; decide)) (fun _ => ?_); wn
  refine WP.lw trc_at_2b6 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE8) (by decide)) ?_; wn
  refine WP.sw trc_at_2b8 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x10) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0x10) (k := 4) (by decide)) ?_; wn
  refine WP.lw trc_at_2ba (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xEC) (by decide)) ?_; wn
  refine WP.sw trc_at_2bc (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x14) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0x14) (k := 4) (by decide)) ?_; wn
  have l1 : ∀ v, memLoad32 (memStore32 m2.mem (F + 16) v) (F + 236) = memLoad32 m2.mem (F + 236) := fun _ =>
    rcf_ld32o (B := F) (c := 0xEC) (d := 0x10) (Or.inr (by decide)) (by decide) (by decide)
  rw [hR.2.1, l1, e8', eC']
  have hS3 : RcKB G 0x18 m2.mem (memStore32 (memStore32 m2.mem (F + 16) (B + BitVec.ofNat 32 t.1)) (F + 20)
      (BitVec.ofNat 32 (s.header + s.len))) :=
    (X.stB (c := 0x10) (k := 4) (by decide) (X.sw32 _ 0x10 _)).trans
      (X.stB (c := 0x14) (k := 4) (by decide) (X.sw32 _ 0x14 _))
  have hI3 : RcMemInv M0 G F fr fp fl g0 (memStore32 (memStore32 m2.mem (F + 16) (B + BitVec.ofNat 32 t.1))
      (F + 20) (BitVec.ofNat 32 (s.header + s.len))) :=
    X.stI (X.stI hI2 (c := 0x10) (k := 4) (by decide) (X.sw32 _ 0x10 _)) (c := 0x14) (k := 4) (by decide)
      (X.sw32 _ 0x14 _)
  have hr3 : RcRdAt (memStore32 (memStore32 m2.mem (F + 16) (B + BitVec.ofNat 32 t.1)) (F + 20)
      (BitVec.ofNat 32 (s.header + s.len))) (F + BitVec.ofNat 32 0xB0) B L (rcAdv t s) :=
    rcp_rdSt (d := 0x14) (rcp_rdSt (d := 0x10) hra (by decide) (by decide) (by decide)) (by decide) (by decide)
      (by decide)
  have hL3 := (hL.keep hK2).kb (hS3.mono (lo' := 0x24) (by decide)) (by decide)
  have hra2 := hra.2.2
  refine WP.aluImm trc_at_2be ?_; wn
  refine WP.aluImm trc_at_2c0 ?_; wn
  refine WP.aluImm trc_at_2c2 ?_; wn
  refine X.callElem (off := 0x2C6) (oc := 0xE0) (dc := 0xB0) (tag := 0x30) trc_at_2c6 trc_at_2ca (by decide)
    (by decide) hI3 (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    (by trsimp) (by decide) hL3 hr3
    (fun m4 hK4 _ hI4 hT2 => ?_)
  refine WP.lw trc_at_2ce (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  rcases hE2 : rcElem L 0x30 (rcAdv t s) with e | k
  · rw [hE2] at hT2
    refine WP.branch trc_at_2d0 (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hT2.1]; decide)); wn
    exact X.e4d2 (herr e (by simp only [rcSubj, hE, hE2])) (by rc_r hR) hI4 (rcp_e4 hT2.2)
  rw [hE2] at hT2
  obtain ⟨f0, -, f8, fC, -, hb2⟩ := hT2
  have f0' : memLoad32 m4.mem (F + 0xE0) = B + BitVec.ofNat 32 ((rcAdv t s).1 + k.header) := f0
  have f8' : memLoad32 m4.mem (F + 232) = B + BitVec.ofNat 32 (rcAdv t s).1 :=
    (congrArg (memLoad32 m4.mem) (add_ofNat_assoc F 0xE0 8)).symm.trans f8
  have fC' : memLoad32 m4.mem (F + 236) = BitVec.ofNat 32 (k.header + k.len) :=
    (congrArg (memLoad32 m4.mem) (add_ofNat_assoc F 0xE0 0xC)).symm.trans fC
  refine WP.branch trc_at_2d0 (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, f0', rck_beqF (rck_pne hL (by simp only [rcAdv] at hb2 ⊢; omega))]; decide))
    (fun _ => ?_); wn
  refine WP.lw trc_at_2d4 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE8) (by decide)) ?_; wn
  refine WP.lw trc_at_2d6 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xEC) (by decide)) ?_; wn
  refine WP.sw trc_at_2d8 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xD0) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xD0) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_2da (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xD4) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xD4) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_2dc (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xD8) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xD8) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_2de (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xDC) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xDC) (k := 4) (by decide)) ?_; wn
  rw [hR.2.1, f8', fC']
  have hS5 : RcKeep G m4.mem (memStore32 (memStore32 (memStore32 (memStore32 m4.mem (F + 208)
      (B + BitVec.ofNat 32 (rcAdv t s).1)) (F + 212) (BitVec.ofNat 32 (k.header + k.len))) (F + 216)
      (B + BitVec.ofNat 32 (rcAdv t s).1)) (F + 220) (BitVec.ofNat 32 (k.header + k.len))) :=
    (((X.stK (c := 0xD0) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0xD0 _)).trans
      (X.stK (c := 0xD4) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0xD4 _))).trans
      (X.stK (c := 0xD8) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0xD8 _))).trans
      (X.stK (c := 0xDC) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0xDC _))
  have hI5 : RcMemInv M0 G F fr fp fl g0 (memStore32 (memStore32 (memStore32 (memStore32 m4.mem (F + 208)
      (B + BitVec.ofNat 32 (rcAdv t s).1)) (F + 212) (BitVec.ofNat 32 (k.header + k.len))) (F + 216)
      (B + BitVec.ofNat 32 (rcAdv t s).1)) (F + 220) (BitVec.ofNat 32 (k.header + k.len))) :=
    X.stI (X.stI (X.stI (X.stI hI4 (c := 0xD0) (k := 4) (by decide) (X.sw32 _ 0xD0 _))
      (c := 0xD4) (k := 4) (by decide) (X.sw32 _ 0xD4 _)) (c := 0xD8) (k := 4) (by decide) (X.sw32 _ 0xD8 _))
      (c := 0xDC) (k := 4) (by decide) (X.sw32 _ 0xDC _)
  have hr5 : RcRdAt (memStore32 (memStore32 (memStore32 (memStore32 m4.mem (F + 208)
      (B + BitVec.ofNat 32 (rcAdv t s).1)) (F + 212) (BitVec.ofNat 32 (k.header + k.len))) (F + 216)
      (B + BitVec.ofNat 32 (rcAdv t s).1)) (F + 220) (BitVec.ofNat 32 (k.header + k.len)))
      (F + BitVec.ofNat 32 0xD0) B L (rcRaw (rcAdv t s) k) := by
    refine ⟨?_, ?_, by simp only [rcRaw, rcAdv] at hb2 ⊢; omega⟩
    · rw [show F + BitVec.ofNat 32 0xD0 + 8 = F + BitVec.ofNat 32 0xD8 from add_ofNat_assoc F 0xD0 8]
      exact (rcf_ld32o (B := F) (c := 0xD8) (d := 0xDC) (Or.inl (by decide)) (by decide) (by decide)).trans
        (memLoad32_store32_same _ _ _)
    · rw [show F + BitVec.ofNat 32 0xD0 + 0xC = F + BitVec.ofNat 32 0xDC from add_ofNat_assoc F 0xD0 0xC]
      exact memLoad32_store32_same _ _ _
  refine X.keySeq (by rc_r hR) hI5 (fun _ _ => rfl) ((hL3.keep hK4).keep hS5) hr5 ?_
  intro M' f' hR' hI' hKB hK' ha1
  have hKM : RcKB G 0x18 M M' := (((hK2.kb.trans hS3).trans hK4.kb).trans hS5.kb).trans (hKB.mono (by decide))
  have hKr : ∀ q : Fin 32, q.val ∈ rcKL → f' q = f q := fun q hq => by
    rw [hK' q hq]
    rcases rcp_kl_cases q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trsimp
  have hsub : ∀ c, 0x10 ≤ c → c + 4 ≤ 0x60 → memLoad32 M' (F + BitVec.ofNat 32 c) =
      memLoad32 (memStore32 (memStore32 m2.mem (F + 16) (B + BitVec.ofNat 32 t.1)) (F + 20)
        (BitVec.ofNat 32 (s.header + s.len))) (F + BitVec.ofNat 32 c) := fun c h1 h2 =>
    ((X.kbLd hKB ⟨h1, h2⟩).trans (X.kbLd (hS5.kb (lo := 0x10)) ⟨h1, h2⟩)).trans
      (X.kbLd (hK4.kb (lo := 0x10)) ⟨h1, h2⟩)
  refine hok ⟨B + BitVec.ofNat 32 sr.1, sr.2, B + BitVec.ofNat 32 ir.1, ir.2, B + BitVec.ofNat 32 t.1,
    s.header + s.len, nb, na, rcKey L B (rcRaw (rcAdv t s) k)⟩ (by simp only [rcSubj, hE, hE2]) M' f' hR' hI' (hKM.mono (by decide))
    (fun q hq => by
      rw [hKr q (by rcases rcp_k4_cases q hq with rfl | rfl | rfl | rfl <;> decide)]; exact hK q hq)
    ((hKr 20 (by decide)).trans h20) ((hKr 22 (by decide)).trans h22)
    ((X.kbLd (c := 0x18) hKM ⟨by decide, by decide⟩).trans hm18)
    ((X.kbLd (c := 0x1C) hKM ⟨by decide, by decide⟩).trans hm1C)
    ((hsub 0x10 (by decide) (by decide)).trans
      ((rcf_ld32o (B := F) (c := 0x10) (d := 0x14) (Or.inl (by decide)) (by decide) (by decide)).trans
        (memLoad32_store32_same _ _ _)))
    ((hsub 0x14 (by decide) (by decide)).trans (memLoad32_store32_same _ _ _))
    ((hKr 9 (by decide)).trans h9) ((hKr 8 (by decide)).trans h8) ((hKr 23 (by decide)).trans h23)
    ((hKr 18 (by decide)).trans h18) hnb hna ha1
    ((X.kbLd (c := 0x20) hKM ⟨by decide, by decide⟩).trans hm20) (rck_pne hL hs)

end

end C3.RV32
