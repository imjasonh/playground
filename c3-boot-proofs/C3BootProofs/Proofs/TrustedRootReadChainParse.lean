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

/-- From the validity: the validity, its two times, then the subject and
the key. `rcSerial` reads the validity this way. -/
def rcpValid (L : Bytes) (p : Word) (sr ir t : RcRd) : Except (Option Nat) RcCert :=
  match rcElem L 0x30 t with
  | .error e => .error e
  | .ok v => rcTimes L p sr ir (rcIn t v) (rcAdv t v)

/-- A word of the frame after a copy into the frame. -/
theorem RcCtx.cpLd (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {dd N c : Nat} {S : Word}
    (h : ∀ x, Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 → M' x = copyBytes M (F + BitVec.ofNat 32 dd) S N x)
    (hc : dd ≤ c ∧ c + 4 ≤ dd + N) (hN : dd + N ≤ 0x180) :
    memLoad32 M' (F + BitVec.ofNat 32 c) = memLoad32 M (S + BitVec.ofNat 32 (c - dd)) :=
  memLoad32_congr2 fun j hj => by
    have e1 : F + BitVec.ofNat 32 c + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (c + j) := add_ofNat_assoc F c j
    have e2 : S + BitVec.ofNat 32 (c - dd) + BitVec.ofNat 32 j = S + BitVec.ofNat 32 (c + j - dd) := by
      rw [add_ofNat_assoc, show c - dd + j = c + j - dd by omega]
    rw [e1, e2, h _ ?_, rcf_cpi M F S ⟨by omega, by omega⟩ (by omega)]
    rw [X.fG]
    exact sep_offsets G (c := 0x5B0) (n := 16) (d := 0x5C0 + (c + j)) (k := 1) (Or.inl (by omega)) (by omega)
      (by omega)

/-- A word of the frame that a copy into the frame leaves. -/
theorem RcCtx.cpLdO (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {dd N c : Nat} {S : Word}
    (h : ∀ x, Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 → M' x = copyBytes M (F + BitVec.ofNat 32 dd) S N x)
    (hc : c + 4 ≤ dd ∨ dd + N ≤ c) (hN : dd + N ≤ 0x180) (hc' : c + 4 ≤ 0x180) :
    memLoad32 M' (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc, h _ ?_, rcf_cpo M F S (by omega) (by omega) (by omega)]
    rw [X.fG]
    exact sep_offsets G (c := 0x5B0) (n := 16) (d := 0x5C0 + (c + j)) (k := 1) (Or.inl (by omega)) (by omega)
      (by omega)

/-- A frame reader that a copy into the frame leaves. -/
theorem RcCtx.cpRdO (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {dd N dc : Nat} {S B : Word}
    {L : Bytes} {r : RcRd}
    (h : ∀ x, Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 → M' x = copyBytes M (F + BitVec.ofNat 32 dd) S N x)
    (hr : RcRdAt M (F + BitVec.ofNat 32 dc) B L r) (hc : dc + 16 ≤ dd ∨ dd + N ≤ dc + 8) (hN : dd + N ≤ 0x180)
    (hc' : dc + 16 ≤ 0x180) : RcRdAt M' (F + BitVec.ofNat 32 dc) B L r :=
  hr.keep (by rw [X.f8]; exact X.cpLdO h (by omega) hN (by omega))
    (by
      rw [show F + BitVec.ofNat 32 dc + 0xC = F + BitVec.ofNat 32 (dc + 0xC) from add_ofNat_assoc F dc 0xC]
      exact X.cpLdO h (by omega) hN (by omega))

/-- A word of the frame that a callee with the footprint `RcFr` leaves. -/
theorem RcCtx.frLd (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {oc ol dc c : Nat}
    (h : RcFr G M M' (F + BitVec.ofNat 32 oc) ol (F + BitVec.ofNat 32 (dc + 8)) 8)
    (ho : c + 4 ≤ oc ∨ oc + ol ≤ c) (hd : c + 4 ≤ dc + 8 ∨ dc + 16 ≤ c) (hc : c + 4 ≤ 0x180)
    (hol : oc + ol ≤ 0x180) (hdc : dc + 16 ≤ 0x180) :
    memLoad32 M' (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]
    refine h _ ?_ (sep_offsets F (c := oc) (n := ol) (d := c + j) (k := 1) (by omega) (by omega) (by omega))
      (sep_offsets F (c := dc + 8) (n := 8) (d := c + j) (k := 1) (by omega) (by omega) (by omega))
    rw [X.fG]
    exact rc_g0' (sep_offsets G (c := 0) (n := 0x5C0) (d := 0x5C0 + (c + j)) (k := 1) (Or.inl (by omega))
      (by omega) (by omega))

/-- A frame reader that a callee with the footprint `RcFr` leaves. -/
theorem RcCtx.frRd (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {oc ol dc c : Nat} {B : Word}
    {L : Bytes} {r : RcRd}
    (h : RcFr G M M' (F + BitVec.ofNat 32 oc) ol (F + BitVec.ofNat 32 (dc + 8)) 8)
    (hr : RcRdAt M (F + BitVec.ofNat 32 c) B L r)
    (ho : c + 16 ≤ oc ∨ oc + ol ≤ c + 8) (hd : c + 16 ≤ dc + 8 ∨ dc + 16 ≤ c + 8) (hc : c + 16 ≤ 0x180)
    (hol : oc + ol ≤ 0x180) (hdc : dc + 16 ≤ 0x180) : RcRdAt M' (F + BitVec.ofNat 32 c) B L r :=
  hr.keep (by rw [X.f8]; exact X.frLd h (by omega) (by omega) (by omega) hol hdc)
    (by
      rw [show F + BitVec.ofNat 32 c + 0xC = F + BitVec.ofNat 32 (c + 0xC) from add_ofNat_assoc F c 0xC]
      exact X.frLd h (by omega) (by omega) (by omega) hol hdc)

/-- From 0x23C: the validity and its times, then the subject at 0x2A0. -/
theorem RcCtx.pTimes (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f w : Fin 32 → Word}
    {B : Word} {L : Bytes} {sr ir t : RcRd} {kc : Word}
    {r : Except (Option Nat) (RcCert × RcSt)}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hK : RcK [19, 21, 24, 27] w f)
    (hL : RcL M G B L) (hr : RcRdAt M (F + BitVec.ofNat 32 0xB0) B L t)
    (h20 : f 20 = B + BitVec.ofNat 32 sr.1) (h22 : f 22 = BitVec.ofNat 32 sr.2)
    (h9 : f 9 = B + BitVec.ofNat 32 ir.1)
    (hm1C : memLoad32 M (F + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ir.2)
    (h23 : f 23 = F + BitVec.ofNat 32 0xE5) (hm20 : memLoad32 M (F + BitVec.ofNat 32 0x20) = kc)
    (hs : sr.1 ≤ L.length)
    (hok : ∀ c, rcpValid L B sr ir t = .ok c →
      RcCertK M0 G F out fr fp fl g0 w (trPost (rcMem M0 G out fr fp fl r) g0) M kc c)
    (herr : ∀ e, rcpValid L B sr ir t = .error e → r = .error e) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x23C f := by
  have hw := hL.hw
  have hr2 := hr.2.2
  refine WP.aluImm trc_at_23c ?_; wn
  refine WP.aluImm trc_at_23e ?_; wn
  refine X.callSeq (off := 0x240) (oc := 0xE0) (dc := 0xB0) trc_at_240 trc_at_244 (by decide) (by decide)
    (by rc_r hR) hI (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    hL hr (fun m2 hK2 _ hI2 hT => ?_)
  refine WP.lw trc_at_248 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  refine WP.lbu trc_at_24a ?_; wn
  rcases hE : rcElem L 0x30 t with e | v
  · rw [hE] at hT
    refine WP.branch trc_at_24e (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hT.1]; decide)); wn
    refine X.e504 (herr e (by simp only [rcpValid, hE])) (by rc_r hR) hI2 (fun b hb => ?_)
    trsimp; rw [hR.2.1, tlv_zext]; exact rcp_e4 hT.2 b hb
  rw [hE] at hT
  obtain ⟨e0, hin, hadv, hb⟩ := hT
  have e0' : memLoad32 m2.mem (F + 0xE0) = B + BitVec.ofNat 32 (t.1 + v.header) := e0
  refine WP.branch trc_at_24e (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, e0', rck_beqF (rck_pne hL (by omega))]; decide)) (fun _ => ?_); wn
  refine WP.aluImm trc_at_252 ?_; wn
  refine WP.aluImm trc_at_254 ?_; wn
  refine WP.alu trc_at_258 ?_; wn
  refine X.callMc (off := 0x25A) (dd := 0xC5) (N := 0xB) (src := F + BitVec.ofNat 32 0xE5) trc_at_25a trc_at_25e
    (by decide) (by decide) (by rc_r hR) hI2 (by trsimp; rw [hR.2.1]; rfl) (by trsimp; exact h23) (by trsimp)
    (by decide) (by rw [X.fG, X.gc (by decide)]; have := X.gw; omega)
    (by rw [X.fG]; exact X.gsep (Or.inr (by decide)) (by decide) (by decide))
    (by rw [X.fG, X.fG]; exact X.gsep (Or.inl (by decide)) (by decide) (by decide)) (fun m3 hI3 hC3 => ?_)
  have hK3 : RcKeep G M m3.mem := hK2.trans (X.mcKeep (by decide) (by decide) hC3)
  have hin3 : RcRdAt m3.mem (F + BitVec.ofNat 32 0xC0) B L (rcIn t v) := by
    refine ⟨?_, ?_, hin.2.2⟩
    · rw [X.f8]
      exact (X.cpLd hC3 ⟨by decide, by decide⟩ (by decide)).trans (by
        rw [add_ofNat_assoc]; exact (congrArg _ (add_ofNat_assoc F 0xE0 8)).symm.trans hin.1)
    · rw [show F + BitVec.ofNat 32 0xC0 + 0xC = F + BitVec.ofNat 32 0xCC from add_ofNat_assoc F 0xC0 0xC]
      exact (X.cpLd hC3 ⟨by decide, by decide⟩ (by decide)).trans (by
        rw [add_ofNat_assoc]; exact (congrArg _ (add_ofNat_assoc F 0xE0 0xC)).symm.trans hin.2.1)
  have hadv3 : RcRdAt m3.mem (F + BitVec.ofNat 32 0xB0) B L (rcAdv t v) :=
    X.cpRdO hC3 hadv (by decide) (by decide) (by decide)
  refine WP.sw trc_at_262 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xC0) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xC0) (k := 4) (by decide)) ?_; wn
  refine WP.sb trc_at_264 (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xC4) (k := 1) (by decide)) ?_; wn
  rw [hR.2.1]
  have hM4 : ∀ (a : Word) (c : BitVec 8),
      RcKeep G M (memStore8 (memStore32 m3.mem (F + 192) a) (F + 196) c) ∧
      RcMemInv M0 G F fr fp fl g0 (memStore8 (memStore32 m3.mem (F + 192) a) (F + 196) c) ∧
      RcRdAt (memStore8 (memStore32 m3.mem (F + 192) a) (F + 196) c) (F + BitVec.ofNat 32 0xC0) B L (rcIn t v) ∧
      RcRdAt (memStore8 (memStore32 m3.mem (F + 192) a) (F + 196) c) (F + BitVec.ofNat 32 0xB0) B L (rcAdv t v) := fun a c =>
    ⟨(hK3.trans (X.stK (c := 0xC0) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0xC0 _))).trans
        (X.stK (c := 0xC4) (k := 1) ⟨by decide, by decide⟩ (X.sw8 _ 0xC4 _)),
      X.stI (X.stI hI3 (c := 0xC0) (k := 4) (by decide) (X.sw32 _ 0xC0 _)) (c := 0xC4) (k := 1) (by decide)
        (X.sw8 _ 0xC4 _),
      rcp_rdSb (d := 0xC4) (rcp_rdSt (d := 0xC0) hin3 (by decide) (by decide) (by decide)) (by decide) (by decide)
        (by decide),
      rcp_rdSb (d := 0xC4) (rcp_rdSt (d := 0xC0) hadv3 (by decide) (by decide) (by decide)) (by decide) (by decide)
        (by decide)⟩
  obtain ⟨hK4, hI4, hin4, hadv4⟩ := hM4 _ _
  refine WP.aluImm trc_at_268 ?_; wn
  refine WP.aluImm trc_at_26a ?_; wn
  refine X.callTime (off := 0x26C) (oc := 0xE0) (dc := 0xC0) trc_at_26c trc_at_270 (by decide) (by decide)
    (by rc_r hR) hI4 (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    (hL.keep hK4) hin4 (fun m5 hK5 hF5 hI5 hT5 => ?_)
  refine WP.lbu trc_at_274 ?_; wn
  rcases hN : readTime (rcView L (rcIn t v)) with _ | ⟨nb, r1⟩
  · rw [hN] at hT5
    refine WP.branch trc_at_278 (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hT5]; decide)); wn
    exact X.e4f6 (herr none (by simp only [rcpValid, hE, rcTimes, hN])) (by rc_r hR) hI5 (fun _ h => by cases h)
  rw [hN] at hT5
  obtain ⟨hnb, h0, hlo, hhi, hlen, hrd⟩ := hT5
  refine WP.branch trc_at_278 (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, h0]; decide)) (fun _ => ?_); wn
  refine WP.sw trc_at_27c (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x18) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0x18) (k := 4) (by decide)) ?_; wn
  refine WP.lw trc_at_27e (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE8) (by decide)) ?_; wn
  refine WP.lw trc_at_280 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xEC) (by decide)) ?_; wn
  have l8 : ∀ a, memLoad32 (memStore32 m5.mem (F + 24) a) (F + 232) = BitVec.ofNat 32 (nb % 2 ^ 32) := fun _ =>
    (rcf_ld32o (B := F) (c := 0xE8) (d := 0x18) (Or.inr (by decide)) (by decide) (by decide)).trans
      ((congrArg (memLoad32 m5.mem) (add_ofNat_assoc F 0xE0 8)).symm.trans hlo)
  have lC : ∀ a, memLoad32 (memStore32 m5.mem (F + 24) a) (F + 236) = BitVec.ofNat 32 (nb / 2 ^ 32) := fun _ =>
    (rcf_ld32o (B := F) (c := 0xEC) (d := 0x18) (Or.inr (by decide)) (by decide) (by decide)).trans
      ((congrArg (memLoad32 m5.mem) (add_ofNat_assoc F 0xE0 0xC)).symm.trans hhi)
  rw [hR.2.1, h9, l8, lC]
  have hS6 : RcKB G 0x24 m5.mem (memStore32 m5.mem (F + 24) (B + BitVec.ofNat 32 ir.1)) :=
    X.stB (c := 0x18) (k := 4) (by decide) (X.sw32 _ 0x18 _)
  have hI6 : RcMemInv M0 G F fr fp fl g0 (memStore32 m5.mem (F + 24) (B + BitVec.ofNat 32 ir.1)) :=
    X.stI hI5 (c := 0x18) (k := 4) (by decide) (X.sw32 _ 0x18 _)
  have hrd6 := rcp_rdSt (d := 0x18) (v := B + BitVec.ofNat 32 ir.1) hrd (by decide) (by decide) (by decide)
  have hadv6 := rcp_rdSt (d := 0x18) (v := B + BitVec.ofNat 32 ir.1)
    (X.frRd hF5 hadv4 (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide)
    (by decide)
  have hL6 := ((hL.keep hK4).keep hK5).kb hS6 (by decide)
  refine WP.aluImm trc_at_282 ?_; wn
  refine WP.aluImm trc_at_284 ?_; wn
  refine X.callTime (off := 0x286) (oc := 0xE0) (dc := 0xC0) trc_at_286 trc_at_28a (by decide) (by decide)
    (by rc_r hR) hI6 (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    hL6 hrd6 (fun m7 hK7 hF7 hI7 hT7 => ?_)
  refine WP.lbu trc_at_28e ?_; wn
  rcases hN2 : readTime (rcView L ((rcIn t v).1 + ((rcIn t v).2 - r1.length), r1.length)) with _ | ⟨na, r2⟩
  · rw [hN2] at hT7
    refine WP.branch trc_at_292 (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hT7]; decide)); wn
    exact X.e4f6 (herr none (by simp only [rcpValid, hE, rcTimes, hN, hN2])) (by rc_r hR) hI7
      (fun _ h => by cases h)
  rw [hN2] at hT7
  obtain ⟨hna, h0', hlo', hhi', hlen', hrd'⟩ := hT7
  refine WP.branch trc_at_292 (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, h0']; decide)) (fun _ => ?_); wn
  refine WP.lw trc_at_296 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xCC) (by decide)) ?_; wn
  have hCC : memLoad32 m7.mem (F + 204) = BitVec.ofNat 32 r2.length :=
    (congrArg (memLoad32 m7.mem) (add_ofNat_assoc F 0xC0 0xC)).symm.trans hrd'.2.1
  simp only [rcIn] at hlen hlen'
  by_cases hz : r2.length ≠ 0
  · refine WP.branch trc_at_298 (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, hCC, rck_bneT (rck_nz hz (by omega))]; decide)); wn
    refine X.e502 (herr (some 1) ?_) (by rc_r hR) hI7
    simp only [rcpValid, hE, rcTimes, hN, hN2]; rw [ite_eq_left hz]
  replace hz : r2.length = 0 := Decidable.of_not_not hz
  refine WP.branch trc_at_298 (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, hCC, hz]; decide)) (fun _ => ?_); wn
  refine WP.lw trc_at_29c (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE8) (by decide)) ?_; wn
  refine WP.lw trc_at_29e (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xEC) (by decide)) ?_; wn
  have l8' : memLoad32 m7.mem (F + 232) = BitVec.ofNat 32 (na % 2 ^ 32) :=
    (congrArg (memLoad32 m7.mem) (add_ofNat_assoc F 0xE0 8)).symm.trans hlo'
  have lC' : memLoad32 m7.mem (F + 236) = BitVec.ofNat 32 (na / 2 ^ 32) :=
    (congrArg (memLoad32 m7.mem) (add_ofNat_assoc F 0xE0 0xC)).symm.trans hhi'
  rw [hR.2.1, l8', lC']
  have hKB7 : RcKB G 0x24 M m7.mem := ((hK4.kb.trans hK5.kb).trans hS6).trans hK7.kb
  have hsel : rcpValid L B sr ir t = rcSubj L B sr ir nb na (rcAdv t v) := by
    simp only [rcpValid, hE, rcTimes, hN, hN2]; rw [ite_eq_right (by omega)]
  refine X.pSubj (by rc_r hR) hI7 (by rc_k hK) (hL6.keep hK7)
    (X.frRd hF7 hadv6 (by decide) (by decide) (by decide) (by decide) (by decide)) (by trsimp; exact h20)
    (by trsimp; exact h22) ((X.keepLd hK7 (c := 0x18) (by decide)).trans (memLoad32_store32_same _ _ _))
    ((X.keepLd hK7 (c := 0x1C) (by decide)).trans
      ((rcf_ld32o (B := F) (c := 0x1C) (d := 0x18) (Or.inr (by decide)) (by decide) (by decide)).trans
        ((X.keepLd hK5 (c := 0x1C) (by decide)).trans ((X.keepLd hK4 (c := 0x1C) (by decide)).trans hm1C))))
    (by trsimp) (by trsimp) (by trsimp) (by trsimp) hnb hna
    ((X.keepLd hK7 (c := 0x20) (by decide)).trans
      ((rcf_ld32o (B := F) (c := 0x20) (d := 0x18) (Or.inr (by decide)) (by decide) (by decide)).trans
        ((X.keepLd hK5 (c := 0x20) (by decide)).trans ((X.keepLd hK4 (c := 0x20) (by decide)).trans hm20))))
    hs (fun c hc => (hok c (hsel.trans hc)).mono hKB7) (fun e he => herr e (hsel.trans he))

/-- From 0x1F0: the serial number, signature algorithm, and issuer, then the
validity at 0x23C. The loop's counter in `s6` moves to `F + 0x20`. -/
theorem RcCtx.pSerial (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f w : Fin 32 → Word}
    {B : Word} {L : Bytes} {t : RcRd} {kc : Word}
    {r : Except (Option Nat) (RcCert × RcSt)}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hK : RcK [19, 21, 24, 27] w f)
    (hL : RcL M G B L) (hr : RcRdAt M (F + BitVec.ofNat 32 0xB0) B L t)
    (h22 : f 22 = kc) (h23 : f 23 = F + BitVec.ofNat 32 0xE5)
    (hok : ∀ c, rcSerial L B t = .ok c →
      RcCertK M0 G F out fr fp fl g0 w (trPost (rcMem M0 G out fr fp fl r) g0) M kc c)
    (herr : ∀ e, rcSerial L B t = .error e → r = .error e) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x1F0 f := by
  have hw := hL.hw
  have hr2 := hr.2.2
  refine WP.aluImm trc_at_1f0 ?_; wn
  refine WP.aluImm trc_at_1f2 ?_; wn
  refine WP.aluImm trc_at_1f4 ?_; wn
  refine X.callElem (off := 0x1F6) (oc := 0xE0) (dc := 0xB0) (tag := 2) trc_at_1f6 trc_at_1fa (by decide)
    (by decide) hI (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    (by trsimp) (by decide) hL hr (fun m2 hK2 _ hI2 hT => ?_)
  refine WP.lw trc_at_1fe (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  rcases hE : rcElem L 2 t with e | sv
  · rw [hE] at hT
    refine WP.branch trc_at_200 (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hT.1]; decide)); wn
    exact X.e4d2 (herr e (by simp only [rcSerial, hE])) (by rc_r hR) hI2 (rcp_e4 hT.2)
  rw [hE] at hT
  obtain ⟨e0, -, e8, eC, hra, hb⟩ := hT
  have e0' : memLoad32 m2.mem (F + 0xE0) = B + BitVec.ofNat 32 (t.1 + sv.header) := e0
  have e8' : memLoad32 m2.mem (F + 232) = B + BitVec.ofNat 32 t.1 :=
    (congrArg (memLoad32 m2.mem) (add_ofNat_assoc F 0xE0 8)).symm.trans e8
  have eC' : memLoad32 m2.mem (F + 236) = BitVec.ofNat 32 (sv.header + sv.len) :=
    (congrArg (memLoad32 m2.mem) (add_ofNat_assoc F 0xE0 0xC)).symm.trans eC
  refine WP.branch trc_at_200 (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, e0', rck_beqF (rck_pne hL (by omega))]; decide)) (fun _ => ?_); wn
  refine WP.sw trc_at_204 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x20) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0x20) (k := 4) (by decide)) ?_; wn
  refine WP.lw trc_at_206 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE8) (by decide)) ?_; wn
  refine WP.lw trc_at_208 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xEC) (by decide)) ?_; wn
  have l8 : ∀ a, memLoad32 (memStore32 m2.mem (F + 32) a) (F + 232) = B + BitVec.ofNat 32 t.1 := fun _ =>
    (rcf_ld32o (B := F) (c := 0xE8) (d := 0x20) (Or.inr (by decide)) (by decide) (by decide)).trans e8'
  have lC : ∀ a, memLoad32 (memStore32 m2.mem (F + 32) a) (F + 236) = BitVec.ofNat 32 (sv.header + sv.len) :=
    fun _ => (rcf_ld32o (B := F) (c := 0xEC) (d := 0x20) (Or.inr (by decide)) (by decide) (by decide)).trans eC'
  rw [hR.2.1, h22, l8, lC]
  have hS3 : RcKB G 0x24 m2.mem (memStore32 m2.mem (F + 32) kc) :=
    X.stB (c := 0x20) (k := 4) (by decide) (X.sw32 _ 0x20 _)
  have hI3 : RcMemInv M0 G F fr fp fl g0 (memStore32 m2.mem (F + 32) kc) :=
    X.stI hI2 (c := 0x20) (k := 4) (by decide) (X.sw32 _ 0x20 _)
  have hr3 := rcp_rdSt (d := 0x20) (v := kc) hra (by decide) (by decide) (by decide)
  have hL3 := (hL.keep hK2).kb hS3 (by decide)
  have hm3 : memLoad32 (memStore32 m2.mem (F + 32) kc) (F + BitVec.ofNat 32 0x20) = kc :=
    memLoad32_store32_same _ _ _
  have hra2 := hra.2.2
  refine WP.aluImm trc_at_20a ?_; wn
  refine WP.aluImm trc_at_20c ?_; wn
  refine WP.aluImm trc_at_20e ?_; wn
  refine X.callElem (off := 0x212) (oc := 0xE0) (dc := 0xB0) (tag := 0x30) trc_at_212 trc_at_216 (by decide)
    (by decide) hI3 (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    (by trsimp) (by decide) hL3 hr3 (fun m4 hK4 _ hI4 hT4 => ?_)
  refine WP.lw trc_at_21a (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  rcases hE2 : rcElem L 0x30 (rcAdv t sv) with e | a
  · rw [hE2] at hT4
    refine WP.branch trc_at_21c (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hT4.1]; decide)); wn
    exact X.e4d2 (herr e (by simp only [rcSerial, hE, hE2])) (by rc_r hR) hI4 (rcp_e4 hT4.2)
  rw [hE2] at hT4
  obtain ⟨f0, -, -, -, hra4, hb4⟩ := hT4
  have f0' : memLoad32 m4.mem (F + 0xE0) = B + BitVec.ofNat 32 ((rcAdv t sv).1 + a.header) := f0
  refine WP.branch trc_at_21c (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, f0', rck_beqF (rck_pne hL (by simp only [rcAdv] at hb4 hra2 ⊢; omega))]; decide))
    (fun _ => ?_); wn
  have hra42 := hra4.2.2
  refine WP.aluImm trc_at_220 ?_; wn
  refine WP.aluImm trc_at_222 ?_; wn
  refine WP.aluImm trc_at_224 ?_; wn
  refine X.callElem (off := 0x228) (oc := 0xE0) (dc := 0xB0) (tag := 0x30) trc_at_228 trc_at_22c (by decide)
    (by decide) hI4 (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    (by trsimp) (by decide) (hL3.keep hK4) hra4 (fun m5 hK5 _ hI5 hT5 => ?_)
  refine WP.lw trc_at_230 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  rcases hE3 : rcElem L 0x30 (rcAdv (rcAdv t sv) a) with e | iv
  · rw [hE3] at hT5
    refine WP.branch trc_at_232 (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hT5.1]; decide)); wn
    exact X.e4d2 (herr e (by simp only [rcSerial, hE, hE2, hE3])) (by rc_r hR) hI5 (rcp_e4 hT5.2)
  rw [hE3] at hT5
  obtain ⟨g0', -, g8, gC, hra5, hb5⟩ := hT5
  have g0'' : memLoad32 m5.mem (F + 0xE0) = B + BitVec.ofNat 32 ((rcAdv (rcAdv t sv) a).1 + iv.header) := g0'
  have g8' : memLoad32 m5.mem (F + 232) = B + BitVec.ofNat 32 (rcAdv (rcAdv t sv) a).1 :=
    (congrArg (memLoad32 m5.mem) (add_ofNat_assoc F 0xE0 8)).symm.trans g8
  have gC' : memLoad32 m5.mem (F + 236) = BitVec.ofNat 32 (iv.header + iv.len) :=
    (congrArg (memLoad32 m5.mem) (add_ofNat_assoc F 0xE0 0xC)).symm.trans gC
  refine WP.branch trc_at_232 (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, g0'', rck_beqF (rck_pne hL (by simp only [rcAdv] at hb5 hra42 ⊢; omega))]; decide))
    (fun _ => ?_); wn
  refine WP.lw trc_at_236 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE8) (by decide)) ?_; wn
  refine WP.lw trc_at_238 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xEC) (by decide)) ?_; wn
  refine WP.sw trc_at_23a (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x1C) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0x1C) (k := 4) (by decide)) ?_; wn
  rw [hR.2.1, g8', gC']
  have hS6 : RcKB G 0x24 m5.mem (memStore32 m5.mem (F + 28) (BitVec.ofNat 32 (iv.header + iv.len))) :=
    X.stB (c := 0x1C) (k := 4) (by decide) (X.sw32 _ 0x1C _)
  have hKB : RcKB G 0x24 M (memStore32 m5.mem (F + 28) (BitVec.ofNat 32 (iv.header + iv.len))) :=
    (((hK2.kb.trans hS3).trans hK4.kb).trans hK5.kb).trans hS6
  have hsel : rcSerial L B t = rcpValid L B (rcRaw t sv) (rcRaw (rcAdv (rcAdv t sv) a) iv)
      (rcAdv (rcAdv (rcAdv t sv) a) iv) := by
    simp only [rcSerial, hE, hE2, hE3]; rfl
  exact X.pTimes (by rc_r hR) (X.stI hI5 (c := 0x1C) (k := 4) (by decide) (X.sw32 _ 0x1C _)) (by rc_k hK)
    (((hL3.keep hK4).keep hK5).kb hS6 (by decide)) (rcp_rdSt (d := 0x1C) hra5 (by decide) (by decide) (by decide))
    (by trsimp; rfl) (by trsimp; rfl) (by trsimp; rfl) (memLoad32_store32_same _ _ _) (by trsimp; exact h23)
    ((rcf_ld32o (B := F) (c := 0x20) (d := 0x1C) (Or.inr (by decide)) (by decide) (by decide)).trans
      ((X.keepLd hK5 (c := 0x20) (by decide)).trans ((X.keepLd hK4 (c := 0x20) (by decide)).trans hm3)))
    (by simp only [rcRaw]; omega) (fun c hc => (hok c (hsel.trans hc)).mono hKB) (fun e he => herr e (hsel.trans he))

end

end C3.RV32
