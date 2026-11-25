import C3BootProofs.Proofs.TufParseMetadata

/-!
# `tuf::parse_metadata`: from the entry to the outer loop

The proof of `tuf::parse_metadata` from its entry through `parse`, the
members of the top-level object, and the checks on `signed`, to the loop
over `signatures` that `TufParseMetadata` proves, and the main theorem.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

theorem pm_co_none {o : Nat} {p : Word} {d : Bytes} (h : curOpen o p d = none) :
    d.length = 0 ∨ d.getD 0 0 ≠ o := by
  unfold curOpen at h
  split at h
  · exact Or.inl ‹_›
  · split at h
    · exact Or.inr ‹_›
    · nomatch h

theorem pm_co_some {o : Nat} {p q : Word} {d : Bytes} {l k : Nat} (h : curOpen o p d = some (q, l, k)) :
    q = p ∧ l = d.length ∧ k = skipWs d 1 ∧ ¬(d.length = 0 ∨ d.getD 0 0 ≠ o) := by
  unfold curOpen at h
  split at h
  · nomatch h
  · rename_i h1
    split at h
    · nomatch h
    · rename_i h2
      cases h
      exact ⟨rfl, rfl, rfl, fun h => h.elim h1 h2⟩

/-- A cursor at `C`: the address `Q` and length `L` of the bytes and the
position `pos`. -/
def PmCc (M : Word → BitVec 8) (C Q : Word) (L pos : Nat) : Prop :=
  memLoad32 M C = Q ∧ memLoad32 M (C + 4) = BitVec.ofNat 32 L ∧ memLoad32 M (C + 8) = BitVec.ofNat 32 pos

/-- The copy of the cursor that `members` or `elements` left at `F + a` to
`F + d`: seven bytes by `memcpy`, then a word and a byte. -/
theorem pm_ccopy {M2 M3 M5 : Word → BitVec 8} {F S q : Word} {d a l k : Nat}
    (hd : d + 12 ≤ 128)
    (hSD : Sep (F + BitVec.ofNat 32 d) 12 S 16)
    (t4 : memLoad32 M2 (F + BitVec.ofNat 32 (a + 4)) = BitVec.ofNat 32 l)
    (t8 : memLoad32 M2 (F + BitVec.ofNat 32 (a + 8)) = BitVec.ofNat 32 k)
    (hO3 : Out (copyBytes M2 (F + BitVec.ofNat 32 (d + 5)) (F + BitVec.ofNat 32 (a + 5)) 7) M3 S 16)
    (hM5 : memStore8 (memStore32 M3 (F + BitVec.ofNat 32 d) q) (F + BitVec.ofNat 32 (d + 4))
      (M2 (F + BitVec.ofNat 32 (a + 4))) = M5) :
    PmCc M5 (F + BitVec.ofNat 32 d) q l k ∧
      ∀ x, Sep x 1 (F + BitVec.ofNat 32 d) 12 → Sep x 1 S 16 → M5 x = M2 x := by
  have oC : Out M2 (copyBytes M2 (F + BitVec.ofNat 32 (d + 5)) (F + BitVec.ofNat 32 (a + 5)) 7)
      (F + BitVec.ofNat 32 (d + 5)) 7 := fun x hx => copyBytes_sep hx.symm (Nat.le_refl _)
  have hcp : ∀ c, 5 ≤ c → c < 12 → M5 (F + BitVec.ofNat 32 (d + c)) = M2 (F + BitVec.ofNat 32 (a + c)) := by
    intro c hc1 hc2
    rw [← hM5, memStore8_ne ?_]
    · rw [out_store32 _ _ _ _ ?_, hO3 _ ?_]
      · have := copyBytes_at (M := M2) (dst := F + BitVec.ofNat 32 (d + 5)) (src := F + BitVec.ofNat 32 (a + 5))
          (N := 7) (i := c - 5) (by omega) (by decide)
        rw [add_ofNat_assoc, add_ofNat_assoc, show d + 5 + (c - 5) = d + c by omega,
          show a + 5 + (c - 5) = a + c by omega] at this
        exact this
      · have := hSD.sub (c := c) (l := 1) (by omega)
        rwa [add_ofNat_assoc] at this
      · exact pm_ff F (c := d + c) (n := 1) (d := d) (k := 4) (Or.inr (by omega)) (by omega) (by omega)
    · exact sep_byte0 (pm_ff F (c := d + c) (n := 1) (d := d + 4) (k := 1) (Or.inr (by omega)) (by omega)
        (by omega)) (by decide)
  refine ⟨⟨?_, ?_, ?_⟩, fun x hx hS => ?_⟩
  · rw [← hM5, (out_store8 _ _ _).load32 (pm_ff F (c := d + 4) (n := 1) (d := d) (k := 4) (Or.inr (by omega))
      (by omega) (by omega)), memLoad32_store32_same]
  · rw [← t4]
    refine memLoad32_shift fun j hj => ?_
    show M5 (F + BitVec.ofNat 32 d + BitVec.ofNat 32 4 + BitVec.ofNat 32 j) =
      M2 (F + BitVec.ofNat 32 (a + 4) + BitVec.ofNat 32 j)
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [add_ofNat_assoc, Nat.add_zero]
      rw [← hM5, memStore8_same]
    · simp only [add_ofNat_assoc, Nat.add_assoc]
      rw [hcp (4 + j) (by omega) (by omega)]
  · rw [← t8]
    refine memLoad32_shift fun j hj => ?_
    show M5 (F + BitVec.ofNat 32 d + BitVec.ofNat 32 8 + BitVec.ofNat 32 j) =
      M2 (F + BitVec.ofNat 32 (a + 8) + BitVec.ofNat 32 j)
    simp only [add_ofNat_assoc, Nat.add_assoc]
    rw [hcp (8 + j) (by omega) (by omega)]
  · have h4 : Sep x 1 (F + BitVec.ofNat 32 (d + 4)) 1 := by
      have := sep_in hx (d := 4) (l := 1) (by decide); rwa [add_ofNat_assoc] at this
    have h0 : Sep x 1 (F + BitVec.ofNat 32 d) 4 := by
      have := sep_in hx (d := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    have h5 : Sep x 1 (F + BitVec.ofNat 32 (d + 5)) 7 := by
      have := sep_in hx (d := 5) (l := 7) (by decide); rwa [add_ofNat_assoc] at this
    rw [← hM5, memStore8_ne (sep_byte0 h4 (by decide)), out_store32 _ _ _ _ h0, hO3 _ hS, oC _ h5]

section
variable {M0 M1 : Word → BitVec 8} {s out F : Word} {g0 : Fin 32 → Word}

/-- `pm_outer` with the fixed registers named. -/
theorem pm_outer0 (E : PmEnv M0 M1 s out F g0) {g : Fin 32 → Word} (hsp : g sp = F) (h26 : g 26 = out)
    (h23 : g 23 = TPM_KK) (h22 : g 22 = TPM_KG) {V2 V1 : Word} {L1 L2 : Nat} (h19 : g 19 = V2) (h21 : g 21 = V1)
    (h20 : g 20 = BitVec.ofNat 32 L1) (h18 : g 18 = BitVec.ofNat 32 L2) (hP0 : V1.toNat ≠ 0)
    (hPN : V1.toNat + L2 < 2 ^ 32) (hSP : Sep s 532 V1 L2) {k pos : Nat} {Mk : Word → BitVec 8}
    (hO : Out M1 Mk s 484) (hC : PmOc Mk F V1 L2 pos) (hpos : pos ≤ L2) (hk : L2 < pos + k) (hz : g 0 = 0)
    (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (pmThen (pmSigs (memBytes M0 V1 L2) k pos) (.ok (V2, L1, V1, L2))))
      Mk 0x19C g := by
  have := pm_outer E (gK := g) hsp h26 h23 h22 h20 h18 hP0 hPN hSP k pos Mk g hO hC hpos hk (fun _ _ => rfl) hz hfr
  rwa [h19, h21] at this

/-- From 0x15C: `elements` on `signatures`, the `V1` bytes of length `v1l`,
and then the outer loop. -/
theorem pm_arr (E : PmEnv M0 M1 s out F g0) {Mk : Word → BitVec 8} {g : Fin 32 → Word}
    (hO : Out M1 Mk s 484) (hgsp : g sp = F) (hg26 : g 26 = out) {V1 V2 : Word} {v1l v2l : Nat}
    (hg19 : g 19 = V2) (hg21 : g 21 = V1) (hg18 : g 18 = BitVec.ofNat 32 v1l) (hg20 : g 20 = BitVec.ofNat 32 v2l)
    (hV0 : V1.toNat ≠ 0) (hVN : V1.toNat + v1l < 2 ^ 32) (hSV : Sep s 532 V1 v1l)
    (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM
      (pmQ M0 s out g0 (pmThen (pmArr (memBytes M0 V1 v1l)) (.ok (V2, v2l, V1, v1l)))) Mk 0x15C g := by
  have hc := E.code hO
  refine WP.aluImm pm_at_15c ?_; wn
  refine WP.alu pm_at_15e ?_; wn
  refine WP.alu pm_at_160 ?_; wn
  refine WP.callElements (tb := TPM_JEL) (out := F + 0x1C) (s := s + BitVec.ofNat 32 388) (p := V1) (n := v1l)
    pm_at_162 pm_at_166 (by decide) (by decide) (by decide) hc.el hc.sw
    (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); (try simp only [ev0]); exact hg21)
    (by (try rsimp); (try simp only [ev0]); exact hg18)
    (by (try rsimp); rw [hgsp]; exact (E.sp 388 (by decide)).symm) (by omega) (E.alS (by decide))
    (aligned_add E.halF (by decide)) (E.lowS (by decide) (by decide) (by decide))
    (E.lowS (by decide) (by decide) (by decide)) (hSV.sub (by decide))
    (E.fs (Or.inr (by decide)) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide))
    (E.lowS (by decide) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide)) fun m2 hR => ?_
  rw [E.bytes hO hSV] at hR
  generalize m2.mem = M2 at hR
  obtain ⟨Ma, hOa, hCR⟩ := hR
  have hO2 : Out M1 M2 s 484 :=
    hO.trans ((Out.upK rfl hOa (by decide)).trans (Out.upK (c := 432) (E.Fc 0x1C).symm hCR.out (by decide)))
  refine WP.zero fun hz2 => ?_
  refine WP.lw pm_at_16a (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x1C) (by decide)) ?_; wn
  refine WP.lbu pm_at_16c ?_; wn
  rcases hco : curOpen 91 V1 (memBytes M0 V1 v1l) with _ | ⟨q, l, k⟩ <;> rw [hco] at hCR
  · obtain ⟨-, t1, t2⟩ := hCR
    rw [pmArr, ite_eq_left (pm_co_none hco)]
    refine WP.branch pm_at_170 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
    exact pm_272 E hO2 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
      (by (try rsimp); rw [hgsp, show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl, t2, ri_ze]; (try rfl))
      (by (try rsimp); (try exact hz)) (by keepz E.hz0)
  · obtain ⟨hq, hl, hk, hn⟩ := pm_co_some hco
    rw [pmArr, ite_eq_right hn]
    rw [memBytes_length] at hl
    obtain ⟨-, t1, t2, t3⟩ := hCR
    rw [hq] at t1; rw [hl] at t2; rw [hk] at t3
    refine WP.branch pm_at_170 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb
      have e0 : V1 = 0 := by simpa [branchTaken] using eb
      exact hV0 (by rw [e0]; rfl)
    refine WP.aluImm pm_at_174 ?_; wn
    refine WP.aluImm pm_at_178 ?_; wn
    refine WP.aluImm pm_at_17c ?_; wn
    have hc2 := E.code hO2
    have EM : McEnv M2 (TPM_JG + 0xBFDA + 8) (F + 0x35) (F + 0x21) (s + BitVec.ofNat 32 388) 7 := by
      refine ⟨by rw [show TPM_JG + 0xBFDA + 8 = TPM_JG + 0xBFE2 by decide]; exact hc2.get.mc,
        E.lowF (by decide) (by decide) (by decide), E.lowS (by decide) (by decide) (by decide),
        E.fs (Or.inr (by decide)) (by decide) (by decide), E.fs (Or.inr (by decide)) (by decide) (by decide),
        pm_ff F (Or.inr (by decide)) (by decide) (by decide), E.alS (by decide), ?_, ?_, ?_⟩
      · have := E.wS (d := 388) (k := 16) (by decide); omega
      · show (F + BitVec.ofNat 32 0x35).toNat + 7 < 2 ^ 32
        rw [E.FN (by decide)]; have := E.hsw; omega
      · show (F + BitVec.ofNat 32 0x21).toNat + 7 < 2 ^ 32
        rw [E.FN (by decide)]; have := E.hsw; omega
    refine WP.callMemcpy (tb := TPM_JG + 0xBFDA) (dst := F + 0x35) (src := F + 0x21)
      (F := s + BitVec.ofNat 32 388) (N := 7) pm_at_17e pm_at_182 (by decide) (by decide) (by decide)
      hc2.get.stub EM (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); rw [ev_add, hgsp])
      (by (try rsimp); (try simp only [ev0]); try rfl)
      (by (try rsimp); rw [hgsp]; exact (E.sp 388 (by decide)).symm) (E.lowS (by decide) (by decide) (by decide))
      (E.lowF (by decide) (by decide) (by decide)) fun m3 hO3 => ?_
    generalize m3.mem = M3 at hO3
    refine WP.sw pm_at_186 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x30) (by decide))
      (by (try rsimp); rw [hgsp]; exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
    refine WP.sb pm_at_188 (by (try rsimp); rw [hgsp]; exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
    refine WP.lui pm_at_18c ?_; wn
    refine WP.aluImm pm_at_190 ?_; wn
    refine WP.lui pm_at_194 ?_; wn
    refine WP.aluImm pm_at_198 ?_; wn
    (try rsimp)
    rw [hgsp, t1, ri_ze]
    generalize hM5 : memStore8 (memStore32 M3 (F + 0x30) V1) (F + 0x34) (M2 (F + 0x20)) = M5
    have hsk := skipWs_le (memBytes M0 V1 v1l) 1
    rw [memBytes_length] at hsk hn
    have hcc := pm_ccopy (M2 := M2) (M3 := M3) (F := F) (S := s + BitVec.ofNat 32 388) (q := V1) (d := 0x30)
      (a := 0x1C) (by decide) (E.fs (Or.inr (by decide)) (by decide) (by decide))
      (by rw [show F + BitVec.ofNat 32 (0x1C + 4) = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2)
      (by rw [show F + BitVec.ofNat 32 (0x1C + 8) = F + 0x1C + 8 by rw [BitVec.add_assoc]; rfl]; exact t3) hO3 hM5
    obtain ⟨⟨c0, c4, c8⟩, hfa⟩ := hcc
    have hO5 : Out M1 M5 s 484 := fun x hx =>
      (hfa x (by rw [E.Fc]; exact sep_in hx (by decide)) (sep_in hx (by decide))).trans (hO2 x hx)
    refine pm_outer0 E (by (try rsimp); exact hgsp) (by (try rsimp); exact hg26) (by (try rsimp); (try decide))
      (by (try rsimp); (try decide)) (by (try rsimp); exact hg19) (by (try rsimp); exact hg21)
      (by (try rsimp); exact hg20) (by (try rsimp); exact hg18) hV0 hVN hSV hO5
      ⟨c0, by rw [show F + 0x34 = F + BitVec.ofNat 32 0x30 + 4 by rw [BitVec.add_assoc]; rfl]; exact c4,
        by rw [show F + 0x38 = F + BitVec.ofNat 32 0x30 + 8 by rw [BitVec.add_assoc]; rfl]; exact c8⟩
      (by omega) (by rw [memBytes_length]; omega) (by (try rsimp); (try exact hz)) (by keepz E.hz0)


/-- From 0x11C: the `_type` member of the `v2l` bytes at `V2` against the
`KL` bytes at `KQ`, and then `pm_arr`. -/
theorem pm_ty (E : PmEnv M0 M1 s out F g0) {Mk : Word → BitVec 8} {g : Fin 32 → Word}
    (hO : Out M1 Mk s 484) (hgsp : g sp = F) (hg26 : g 26 = out) {KQ : Word} {KL : Nat}
    (hg23 : g 23 = KQ) (hg22 : g 22 = BitVec.ofNat 32 KL) (hKL : KL < 2 ^ 32) (hSK : Sep s 532 KQ KL)
    {V1 V2 : Word} {v1l v2l : Nat}
    (hg19 : g 19 = V2) (hg21 : g 21 = V1) (hg18 : g 18 = BitVec.ofNat 32 v1l) (hg20 : g 20 = BitVec.ofNat 32 v2l)
    (hV0 : V1.toNat ≠ 0) (hVN : V1.toNat + v1l < 2 ^ 32) (hSV : Sep s 532 V1 v1l)
    (hV20 : V2.toNat ≠ 0) (hV2N : V2.toNat + v2l < 2 ^ 32) (hSV2 : Sep s 532 V2 v2l)
    (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (pmThen (pmTy (memBytes M0 V2 v2l) (memBytes M0 V1 v1l)
      (memBytes M0 KQ KL)) (.ok (V2, v2l, V1, v1l)))) Mk 0x11C g := by
  have hc := E.code hO
  refine WP.lui pm_at_11c ?_; wn
  refine WP.aluImm pm_at_120 ?_; wn
  refine WP.aluImm pm_at_124 ?_; wn
  refine WP.aluImm pm_at_126 ?_; wn
  refine WP.alu pm_at_128 ?_; wn
  refine WP.alu pm_at_12a ?_; wn
  refine WP.callField (tb := TPM_JF) (out := F + 0x1C) (s := s + BitVec.ofNat 32 144)
    (p := V2) (kq := TPM_KT) (n := v2l) (kl := 5)
    pm_at_12c pm_at_130 (by decide) (by decide) (by decide) hc.fieldC
    (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); (try simp only [ev0]); exact hg19)
    (by (try rsimp); (try simp only [ev0]); exact hg20)
    (by (try rsimp); (try rfl); (try decide)) (by (try rsimp); (try simp only [ev0]); (try rfl))
    (by (try rsimp); rw [hgsp]; exact (E.sp 144 (by decide)).symm)
    (E.alS (by decide)) (aligned_add E.halF (by decide)) (by have := E.wS (d := 144) (k := 260) (by decide); omega)
    (by decide) hV20 hV2N
    (tuf_fieldSep (E.wS (by decide)) (E.hro.sub (by decide))) (hSV2.sub (by decide))
    (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) (E.fs (Or.inr (by decide)) (by decide) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) (E.lowS (by decide) (by decide) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) fun m3 hR => ?_
  rw [E.bytes hO hSV2, tpm_kt hc] at hR
  generalize m3.mem = M3 at hR
  obtain ⟨Mb, hOb, hFR⟩ := hR
  have hO3 : Out M1 M3 s 484 :=
    hO.trans ((Out.upK rfl hOb (by decide)).trans (Out.upK (c := 432) (E.Fc 0x1C).symm hFR.out (by decide)))
  refine WP.zero fun hz3 => ?_
  refine WP.lw pm_at_134 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x1C) (by decide)) ?_; wn
  simp only [pmTy]
  rcases hof : objField (memBytes M0 V2 v2l) (ascii!"_type") with e | ⟨yp, yl⟩ <;>
    rw [hof] at hFR <;> simp only [fieldRes, Except.map] at hFR <;> (try dsimp only)
  · obtain ⟨-, t1, t2⟩ := hFR
    refine WP.branch pm_at_136 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
    exact pm_264 E hO3 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
      (by rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2) (by keepz E.hz0)
  · obtain ⟨-, t1, t2⟩ := hFR
    have hv := objField_val hof
    rw [memBytes_length] at hv
    have t2' : memLoad32 M3 (F + 0x20) = BitVec.ofNat 32 yl := by
      rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
    have hq1 := nx_q0 hV20 (n := v2l) (pos := yp) (by omega) (by omega)
    refine WP.branch pm_at_136 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t1, hq1] at eb; exact absurd eb (by decide)
    refine WP.lw pm_at_13a (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
    refine WP.aluImm pm_at_13c ?_; wn
    have hc3 := E.code hO3
    refine WP.callStr (tb := TPM_JS) (out := F + 0x3C) (p := V2 + BitVec.ofNat 32 yp) (n := yl)
      pm_at_13e pm_at_142 (by decide) (by decide) (by decide) hc3.str (by (try rsimp); rw [ev_add, hgsp])
      (by (try rsimp); rw [hgsp, t1]) (by (try rsimp); rw [hgsp, t2']) (by omega)
      (aligned_add E.halF (k := 0x3C) (by decide)) (E.lowF (by decide) (by decide) (by decide))
      (E.lowF (by decide) (by decide) (by decide)) fun m4 hS => ?_
    have hSy : Sep s 532 (V2 + BitVec.ofNat 32 yp) yl := hSV2.subR hv.2
    rw [E.bytes hO3 hSy, tex_strRes] at hS
    generalize m4.mem = M4 at hS
    have hO4 : Out M1 M4 s 484 := hO3.trans (Out.upK (c := 464) (E.Fc 0x3C).symm hS.out (by decide))
    refine WP.zero fun hz4 => ?_
    refine WP.lw pm_at_146 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x3C) (by decide)) ?_; wn
    rw [show slice (memBytes M0 V2 v2l) yp yl = memBytes M0 (V2 + BitVec.ofNat 32 yp) yl from
      tuf_memBytes_drop_take hv.2]
    rcases hsb : strBody (memBytes M0 (V2 + BitVec.ofNat 32 yp) yl) with _ | b <;>
      rw [hsb] at hS <;> simp only [Option.map_none, Option.map_some] at hS <;> (try dsimp only)
    · obtain ⟨-, t1, t2⟩ := hS
      refine WP.branch pm_at_148 (fun _ => ?_) (fun eb => ?_) <;> wn
      rotate_left
      · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
      exact pm_296 E hO4 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
        (by rw [show F + 0x40 = F + 0x3C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2) (by keepz E.hz0)
    · obtain ⟨-, t1, t2⟩ := hS
      obtain ⟨hb2, hbe⟩ := tex_body hsb
      rw [memBytes_length] at hb2 hbe
      rw [tuf_memBytes_drop_take (by omega), add_ofNat_assoc] at hbe
      have hbl : b.length = yl - 2 := by rw [hbe, memBytes_length]
      have t1' : memLoad32 M4 (F + 0x3C) = V2 + BitVec.ofNat 32 (yp + 1) := t1.trans (add_ofNat_assoc V2 yp 1)
      have t2b : memLoad32 M4 (F + 0x40) = BitVec.ofNat 32 b.length := by
        rw [show F + 0x40 = F + 0x3C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
      have hq2 := nx_q0 hV20 (n := v2l) (pos := yp + 1) (by omega) (by omega)
      have hSbb : Sep s 532 (V2 + BitVec.ofNat 32 (yp + 1)) b.length := hSV2.subR (by omega)
      have hkb : memBytes M0 (V2 + BitVec.ofNat 32 (yp + 1)) b.length = b := by rw [hbl, ← hbe]
      refine WP.branch pm_at_148 (fun eb => ?_) (fun _ => ?_) <;> wn
      · exfalso; (try rsimp at eb); rw [hgsp, t1', hq2] at eb; exact absurd eb (by decide)
      refine WP.lw pm_at_14c (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x40) (by decide)) ?_; wn
      refine WP.alu pm_at_14e ?_; wn
      refine WP.alu pm_at_150 ?_; wn
      have hc4 := E.code hO4
      have hs384 : F + 0xFFFFFFEC = s + BitVec.ofNat 32 384 := by rw [← E.hF, BitVec.add_assoc]; rfl
      refine WP.callSliceNe (tb := TPM_JP + 0xFFFFFFEA) (p := V2 + BitVec.ofNat 32 (yp + 1)) (q := KQ)
        (pl := b.length) (ql := KL) pm_at_152 pm_at_156 (by decide) (by decide) (by decide) hc4.parse.ne
        (by rw [pa_ad_eq]; exact hc4.get.eq) (by rw [pa_ad_es]; exact hc4.get.ri.es)
        (by rw [pa_ad_mm]; exact hc4.get.ri.mc)
        (by (try rsimp); rw [hgsp, t1']) (by (try rsimp); rw [hgsp, t2b])
        (by (try rsimp); (try simp only [ev0]); exact hg23) (by (try rsimp); (try simp only [ev0]); exact hg22)
        (by omega) hKL (by (try rsimp); rw [hgsp]; exact E.halF)
        (by (try rsimp); rw [hgsp, hs384]; exact E.lowS (by decide) (by decide) (by decide))
        (by (try rsimp); rw [hgsp, hs384]; exact E.lowS (by decide) (by decide) (by decide))
        (by (try rsimp); rw [hgsp, hs384]; exact E.lowS (by decide) (by decide) (by decide))
        (by (try rsimp); rw [hgsp, hs384]; exact E.lowS (by decide) (by decide) (by decide))
        (by (try rsimp); rw [hgsp, hs384]; exact hSbb.sub (by decide))
        (by (try rsimp); rw [hgsp, hs384]; exact hSK.sub (by decide))
        (by (try rsimp); rw [hgsp, hs384]; exact E.lowS (by decide) (by decide) (by decide)) fun m5 ha0 hO5' => ?_
      rw [E.bytes hO4 hSbb, E.bytes hO4 hSK, hkb] at ha0
      have hO5'' : Out M4 m5.mem (s + BitVec.ofNat 32 384) 20 := by
        (try rsimp at hO5'); rw [hgsp, hs384] at hO5'; exact hO5'
      have hO5 : Out M1 m5.mem s 484 := hO4.trans (Out.upK rfl hO5'' (by decide))
      refine WP.zero fun hz5 => ?_
      by_cases hbk : b = memBytes M0 KQ KL
      · rw [ite_eq_left hbk] at ha0
        refine WP.branch pm_at_15a (fun eb => ?_) (fun _ => ?_) <;> wn
        · exfalso; (try rsimp at eb); rw [ha0] at eb; exact absurd eb (by decide)
        rw [ite_eq_left hbk]
        exact pm_arr E hO5 (by (try rsimp); exact hgsp) (by (try rsimp); exact hg26) (by (try rsimp); exact hg19)
          (by (try rsimp); exact hg21) (by (try rsimp); exact hg18) (by (try rsimp); exact hg20) hV0 hVN hSV
          (by keepz E.hz0)
      · rw [ite_eq_right hbk] at ha0
        refine WP.branch pm_at_15a (fun _ => ?_) (fun eb => ?_) <;> wn
        rotate_left
        · exfalso; (try rsimp at eb); rw [ha0] at eb; exact absurd eb (by decide)
        rw [ite_eq_right hbk]
        exact pm_116 E hO5 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
          (by (try rsimp); (try exact hz5)) (by keepz E.hz0)

theorem PmCc.keep {M M' : Word → BitVec 8} {C Q r : Word} {L pos l : Nat} (h : PmCc M C Q L pos)
    (hO : Out M M' r l) (hs : Sep r l C 12) : PmCc M' C Q L pos :=
  ⟨(hO.load32 (by have := hs.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)).trans h.1,
    (hO.load32 (hs.subR (c := 4) (l := 4) (by decide))).trans h.2.1,
    (hO.load32 (hs.subR (c := 8) (l := 4) (by decide))).trans h.2.2⟩

theorem pm_c24 (F : Word) : F + BitVec.ofNat 32 16 + 8 = F + BitVec.ofNat 32 24 := by
  rw [BitVec.add_assoc]; rfl

/-- The cursor at `F + 16` after `next_member` moved it to `a`. -/
theorem pm_ccNext {Ma M2 : Word → BitVec 8} {F Q : Word} {L pos a : Nat}
    (hC : PmCc Ma (F + BitVec.ofNat 32 16) Q L pos)
    (hfa : ∀ x, Sep x 1 (F + 0x1C) 20 → Sep x 1 (F + BitVec.ofNat 32 16 + 8) 4 → M2 x = Ma x)
    (ta : memLoad32 M2 (F + BitVec.ofNat 32 16 + 8) = BitVec.ofNat 32 a) :
    PmCc M2 (F + BitVec.ofNat 32 16) Q L a := by
  have hs : ∀ c, c + 4 ≤ 8 → Sep (F + BitVec.ofNat 32 16 + BitVec.ofNat 32 c) 4 (F + 0x1C) 20 ∧
      Sep (F + BitVec.ofNat 32 16 + BitVec.ofNat 32 c) 4 (F + BitVec.ofNat 32 16 + 8) 4 := fun c hc => by
    rw [add_ofNat_assoc, pm_c24]
    exact ⟨pm_ff F (c := 16 + c) (n := 4) (d := 28) (k := 20) (Or.inl (by omega)) (by omega) (by decide),
      pm_ff F (c := 16 + c) (n := 4) (d := 24) (k := 4) (Or.inl (by omega)) (by omega) (by decide)⟩
  have ld : ∀ c, c + 4 ≤ 8 → memLoad32 M2 (F + BitVec.ofNat 32 16 + BitVec.ofNat 32 c) =
      memLoad32 Ma (F + BitVec.ofNat 32 16 + BitVec.ofNat 32 c) := fun c hc =>
    memLoad32_congr fun _ hj => hfa _ (sep_pt (hs c hc).1.symm hj) (sep_pt (hs c hc).2.symm hj)
  refine ⟨?_, ?_, ta⟩
  · have := ld 0 (by decide); rw [add_ofNat_zero] at this; exact this.trans hC.1
  · exact (ld 4 (by decide)).trans hC.2.1

/-- The memory after `next_member` writes its result at `F + 0x1C` and the
position at `F + 24`. -/
theorem pm_nmOut (E : PmEnv M0 M1 s out F g0) {Mk Ma M2 : Word → BitVec 8}
    {r : Option (Option (Word × Nat × Word × Nat × Nat))} (hO : Out M1 Mk s 484)
    (hOa : Out Mk Ma (s + BitVec.ofNat 32 240) 164) (hMR : MemRes Ma M2 (F + 0x1C) (F + BitVec.ofNat 32 16) r) :
    Out M1 M2 s 484 := by
  refine hO.trans ((Out.upK rfl hOa (by decide)).trans fun x hx => hMR.out ?_ ?_)
  · show Sep x 1 (F + BitVec.ofNat 32 0x1C) 20
    rw [E.Fc]; exact sep_in hx (by decide)
  · rw [pm_c24, E.Fc]; exact sep_in hx (by decide)

/-- A call to `next_member` with the cursor at `F + 16` and the result at
`F + 0x1C`. -/
theorem pm_nm (E : PmEnv M0 M1 s out F g0) {Mk : Word → BitVec 8} {f : Fin 32 → Word} {off : Nat}
    {hi lo : Word} {R : Except Nat (Word × Nat × Word × Nat)}
    (h1 : fetchRel tufParseMetadataCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel tufParseMetadataCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : TPM + BitVec.ofNat 32 off + hi + lo = TPM_JG + 0xFFFFF438) (hev : (off + 8) % 2 = 0)
    (hO : Out M1 Mk s 484) (h0 : f a0 = F + 0x1C) (ha1 : f a1 = F + BitVec.ofNat 32 16) (hsp : f sp = F)
    {Q : Word} {L pos : Nat} (hC : PmCc Mk (F + BitVec.ofNat 32 16) Q L pos) (hQ0 : Q.toNat ≠ 0)
    (hQN : Q.toNat + L < 2 ^ 32) (hpos : pos ≤ L) (hSQ : Sep s 532 Q L)
    (k : ∀ m2 : Machine, MemResF Mk m2.mem (F + 0x1C) (F + BitVec.ofNat 32 16) (s + BitVec.ofNat 32 240) 164
      (memRes Q (nextMember (memBytes M0 Q L) pos)) →
      WP tufParseMetadataCode TPM (pmQ M0 s out g0 R) m2.mem (off + 8)
        (clob (upd f ra (TPM + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 R) Mk off f := by
  have hc := E.code hO
  have hPS := tpm_parseSep E.hsw E.hro
  refine WP.callNextMember (tb := TPM_JG + 0xFFFFF438) (out := F + 0x1C) (c := F + BitVec.ofNat 32 16)
    (s := s + BitVec.ofNat 32 240) (p := Q) (n := L) (pos := pos) h1 h2 htgt (by decide) hev hc.get.nm
    (by rw [show TPM_JG + 0xFFFFF438 + 0x1DE = TPM_JG + 0xFFFFF616 by decide]; exact hc.get.ri)
    (by rw [show TPM_JG + 0xFFFFF438 + 0x144 = TPM_JG + 0xFFFFF57C by decide]; exact hc.get.ke)
    h0 ha1 (by rw [hsp]; exact (E.sp 240 (by decide)).symm) (E.alS (by decide))
    (aligned_add E.halF (by decide)) (aligned_add E.halF (by decide)) hC.1 hC.2.1 hC.2.2 (by omega) (by omega)
    hQ0 (by omega)
    (by rw [show TPM_JG + 0xFFFFF438 + 0x1DE = TPM_JG + 0xFFFFF616 by decide]; exact hPS.2.ri.sub (by decide))
    (by rw [show TPM_JG + 0xFFFFF438 + 0x144 = TPM_JG + 0xFFFFF57C by decide]; exact hPS.2.ke.sub (by decide))
    (hPS.2.nm.sub (by decide)) (hSQ.sub (by decide))
    (E.fs (Or.inr (by decide)) (by decide) (by decide)) (E.fs (Or.inr (by decide)) (by decide) (by decide))
    (pm_ff F (Or.inr (by decide)) (by decide) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide))
    (E.lowS (by decide) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) fun m2 hR => k m2 (by rw [E.bytes hO hSQ] at hR; exact hR)

theorem pm_resThen (Q : Word) (r : Except Nat Unit) (x : Nat × Nat × Nat × Nat) :
    pmRes Q (pmThen r (.ok x)) = pmThen r (.ok (Q + BitVec.ofNat 32 x.1, x.2.1, Q + BitVec.ofNat 32 x.2.2.1, x.2.2.2)) := by
  cases r <;> rfl

/-- From 0x100: the third member of the top-level object, the `L` bytes at
`Q`, from `a2`, then `pm_ty` on `signed` at `v2p` and `signatures` at
`v1p`. -/
theorem pm_rest (E : PmEnv M0 M1 s out F g0) {Mk : Word → BitVec 8} {g : Fin 32 → Word}
    (hO : Out M1 Mk s 484) (hgsp : g sp = F) (hg26 : g 26 = out) {KQ : Word} {KL : Nat}
    (hg23 : g 23 = KQ) (hg22 : g 22 = BitVec.ofNat 32 KL) (hKL : KL < 2 ^ 32) (hSK : Sep s 532 KQ KL)
    {Q : Word} {L a2 : Nat} (hC : PmCc Mk (F + BitVec.ofNat 32 16) Q L a2) (hQ0 : Q.toNat ≠ 0)
    (hQN : Q.toNat + L < 2 ^ 32) (hSQ : Sep s 532 Q L) (ha2 : a2 ≤ L) {v1p v1l v2p v2l : Nat}
    (hv1 : v1p + v1l ≤ L) (hv2 : v2p + v2l ≤ L)
    (hg19 : g 19 = Q + BitVec.ofNat 32 v2p) (hg20 : g 20 = BitVec.ofNat 32 v2l)
    (hg21 : g 21 = Q + BitVec.ofNat 32 v1p) (hg18 : g 18 = BitVec.ofNat 32 v1l)
    (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (pmRes Q (pmThen (pmRest (memBytes M0 Q L) (memBytes M0 KQ KL)
      a2 v1p v1l v2p v2l) (.ok (v2p, v2l, v1p, v1l))))) Mk 0x100 g := by
  rw [pm_resThen]
  refine WP.aluImm pm_at_100 ?_; wn
  refine WP.aluImm pm_at_102 ?_; wn
  refine pm_nm E pm_at_104 pm_at_108 (by decide) (by decide) hO (by (try rsimp); rw [ev_add, hgsp])
    (by (try rsimp); rw [ev_add, hgsp]; (try rfl)) (by (try rsimp); exact hgsp) hC hQ0 hQN ha2 hSQ
    fun m2 hR => ?_
  obtain ⟨Ma, hOa, hMR⟩ := hR
  generalize m2.mem = M2 at hMR
  have hO2 : Out M1 M2 s 484 := pm_nmOut E hO hOa hMR
  refine WP.zero fun hz2 => ?_
  refine WP.lbu pm_at_10c ?_; wn
  rcases hnm : nextMember (memBytes M0 Q L) a2 with _ | _ | ⟨k3p, k3l, v3p, v3l, a3⟩ <;>
    rw [hnm] at hMR <;> simp only [memRes, Option.map_none, Option.map_some] at hMR <;>
    simp only [pmRest, hnm]
  · obtain ⟨-, t0, t1⟩ := hMR
    refine WP.branch pm_at_110 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hgsp, t0] at eb; exact absurd eb (by decide)
    exact pm_8e E hO2 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
      (by rw [show F + 0x1D = F + 0x1C + 1 by rw [BitVec.add_assoc]; rfl]; exact t1) (by keepz E.hz0)
  · obtain ⟨-, t0, t1⟩ := hMR
    refine WP.branch pm_at_110 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t0] at eb; exact absurd eb (by decide)
    refine WP.lw pm_at_112 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
    have t1' : memLoad32 M2 (F + 0x20) = 0 := by
      rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t1
    refine WP.branch pm_at_114 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hgsp, t1'] at eb; exact absurd eb (by decide)
    rw [show slice (memBytes M0 Q L) v2p v2l = memBytes M0 (Q + BitVec.ofNat 32 v2p) v2l from
        tuf_memBytes_drop_take hv2,
      show slice (memBytes M0 Q L) v1p v1l = memBytes M0 (Q + BitVec.ofNat 32 v1p) v1l from
        tuf_memBytes_drop_take hv1]
    exact pm_ty E hO2 (by (try rsimp); exact hgsp) (by (try rsimp); exact hg26) (by (try rsimp); exact hg23)
      (by (try rsimp); exact hg22) hKL hSK (by (try rsimp); exact hg19) (by (try rsimp); exact hg21)
      (by (try rsimp); exact hg18) (by (try rsimp); exact hg20)
      (by rw [tex_toNat (by omega)]; omega) (by rw [tex_toNat (by omega)]; omega) (hSQ.subR hv1)
      (by rw [tex_toNat (by omega)]; omega) (by rw [tex_toNat (by omega)]; omega) (hSQ.subR hv2)
      (by keepz E.hz0)
  · obtain ⟨-, t0, t1, -⟩ := hMR
    have hl := nextMember_lt hnm
    rw [memBytes_length] at hl
    refine WP.branch pm_at_110 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t0] at eb; exact absurd eb (by decide)
    refine WP.lw pm_at_112 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
    have t1' : memLoad32 M2 (F + 0x20) = Q + BitVec.ofNat 32 k3p := by
      rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t1
    have hq := nx_q0 hQ0 (n := L + 1) (pos := k3p) (by omega) (by omega)
    refine WP.branch pm_at_114 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t1', hq] at eb; exact absurd eb (by decide)
    exact pm_116 E hO2 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp) (by (try rsimp); (try exact hz2))
      (by keepz E.hz0)

theorem pm_key {M : Word → BitVec 8} {Q : Word} {L p l n : Nat} {key : Bytes} (hpl : p + l ≤ L)
    (hn : key.length = n) :
    slice (memBytes M Q L) p l = key ↔ l = n ∧ memBytes M (Q + BitVec.ofNat 32 p) n = key := by
  rw [show slice (memBytes M Q L) p l = memBytes M (Q + BitVec.ofNat 32 p) l from tuf_memBytes_drop_take hpl]
  constructor
  · intro h
    have hl : l = n := by rw [← hn, ← h, memBytes_length]
    subst hl; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact h

theorem pm_bne {x y : Word} (h : branchTaken .bne x y = false) : x = y := by
  simpa [branchTaken] using h

theorem pm_ofNat_ne {l n : Nat} (hl : l < 2 ^ 32) (hn : n < 2 ^ 32) (h : BitVec.ofNat 32 l = BitVec.ofNat 32 n) :
    l = n := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hn] at this

/-- From 0x7C: the second member of the top-level object, the `L` bytes at
`Q`, from `a1`, after the first member, with its key at `k1p` and its
value at `v1p`. -/
theorem pm_two (E : PmEnv M0 M1 s out F g0) {Mk : Word → BitVec 8} {g : Fin 32 → Word}
    (hO : Out M1 Mk s 484) (hgsp : g sp = F) (hg26 : g 26 = out) {KQ : Word} {KL : Nat}
    (hg23 : g 23 = KQ) (hg22 : g 22 = BitVec.ofNat 32 KL) (hKL : KL < 2 ^ 32) (hSK : Sep s 532 KQ KL)
    {Q : Word} {L a1 : Nat} (hC : PmCc Mk (F + BitVec.ofNat 32 16) Q L a1) (hQ0 : Q.toNat ≠ 0)
    (hQN : Q.toNat + L < 2 ^ 32) (hSQ : Sep s 532 Q L) (ha1 : a1 ≤ L) {k1p k1l v1p v1l : Nat}
    (hk1 : k1p + k1l ≤ L) (hv1 : v1p + v1l ≤ L)
    (hg9 : g 9 = Q + BitVec.ofNat 32 k1p) (hg19 : g 19 = BitVec.ofNat 32 k1l)
    (hg21 : g 21 = Q + BitVec.ofNat 32 v1p) (hg18 : g 18 = BitVec.ofNat 32 v1l)
    (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (pmRes Q (pmTwo (memBytes M0 Q L) (memBytes M0 KQ KL)
      a1 k1p k1l v1p v1l))) Mk 0x7C g := by
  refine WP.aluImm pm_at_7c ?_; wn
  refine WP.aluImm pm_at_7e ?_; wn
  refine pm_nm E pm_at_80 pm_at_84 (by decide) (by decide) hO (by (try rsimp); rw [ev_add, hgsp])
    (by (try rsimp); rw [ev_add, hgsp]; (try rfl)) (by (try rsimp); exact hgsp) hC hQ0 hQN ha1 hSQ
    fun m2 hR => ?_
  obtain ⟨Ma, hOa, hMR⟩ := hR
  generalize m2.mem = M2 at hMR
  have hC2 : PmCc Ma (F + BitVec.ofNat 32 16) Q L a1 :=
    hC.keep hOa (E.fs (Or.inr (by decide)) (by decide) (by decide)).symm
  have hO2 : Out M1 M2 s 484 := pm_nmOut E hO hOa hMR
  have hc2 := E.code hO2
  refine WP.zero fun hz2 => ?_
  refine WP.lbu pm_at_88 ?_; wn
  rcases hnm : nextMember (memBytes M0 Q L) a1 with _ | _ | ⟨k2p, k2l, v2p, v2l, a2⟩ <;>
    rw [hnm] at hMR <;> simp only [memRes, Option.map_none, Option.map_some] at hMR <;>
    simp only [pmTwo, hnm]
  · obtain ⟨-, t0, t1⟩ := hMR
    refine WP.branch pm_at_8c (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t0] at eb; exact absurd eb (by decide)
    exact pm_8e E hO2 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
      (by rw [show F + 0x1D = F + 0x1C + 1 by rw [BitVec.add_assoc]; rfl]; exact t1) (by keepz E.hz0)
  · obtain ⟨-, t0, t1⟩ := hMR
    refine WP.branch pm_at_8c (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hgsp, t0] at eb; exact absurd eb (by decide)
    refine WP.lw pm_at_94 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
    have t1' : memLoad32 M2 (F + 0x20) = 0 := by
      rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t1
    refine WP.branch pm_at_96 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hgsp, t1'] at eb; exact absurd eb (by decide)
    exact pm_116 E hO2 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp) (by (try rsimp); (try exact hz2))
      (by keepz E.hz0)
  · obtain ⟨hfa, t0, t1, t2, t3, t4, t5⟩ := hMR
    have hl := nextMember_lt hnm
    rw [memBytes_length] at hl
    have hC3 : PmCc M2 (F + BitVec.ofNat 32 16) Q L a2 := pm_ccNext hC2 hfa t5
    have t1' : memLoad32 M2 (F + 0x20) = Q + BitVec.ofNat 32 k2p := by
      rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t1
    have t2' : memLoad32 M2 (F + 0x24) = BitVec.ofNat 32 k2l := by
      rw [show F + 0x24 = F + 0x1C + 8 by rw [BitVec.add_assoc]; rfl]; exact t2
    have t3' : memLoad32 M2 (F + 0x28) = Q + BitVec.ofNat 32 v2p := by
      rw [show F + 0x28 = F + 0x1C + 12 by rw [BitVec.add_assoc]; rfl]; exact t3
    have t4' : memLoad32 M2 (F + 0x2C) = BitVec.ofNat 32 v2l := by
      rw [show F + 0x2C = F + 0x1C + 16 by rw [BitVec.add_assoc]; rfl]; exact t4
    refine WP.branch pm_at_8c (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hgsp, t0] at eb; exact absurd eb (by decide)
    refine WP.lw pm_at_94 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
    have hq := nx_q0 hQ0 (n := L + 1) (pos := k2p) (by omega) (by omega)
    refine WP.branch pm_at_96 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t1', hq] at eb; exact absurd eb (by decide)
    refine WP.aluImm pm_at_9a ?_; wn
    have hbad : ¬(slice (memBytes M0 Q L) k1p k1l = ascii!"signatures" ∧
        slice (memBytes M0 Q L) k2p k2l = ascii!"signed") → ∀ g' : Fin 32 → Word, g' 26 = out → g' sp = F →
        g' 0 = 0 → (∀ x, x ∉ pmE → g' x = g0 x) → WP tufParseMetadataCode TPM (pmQ M0 s out g0 (pmRes Q (if slice (memBytes M0 Q L) k1p k1l = ascii!"signatures" ∧
          slice (memBytes M0 Q L) k2p k2l = ascii!"signed" then
          pmThen (pmRest (memBytes M0 Q L) (memBytes M0 KQ KL) a2 v1p v1l v2p v2l) (.ok (v2p, v2l, v1p, v1l))
        else .error 0x21))) M2 0x116 g' := fun hn g' h26 hsp hz hf => by
      rw [ite_eq_right hn]; exact pm_116 E hO2 h26 hsp hz hf
    by_cases hl10 : k1l = 10
    rotate_left
    · refine WP.branch pm_at_9c (fun _ => ?_) (fun eb => ?_) <;> wn
      rotate_left
      · exfalso; (try rsimp at eb); rw [hg19] at eb; (try simp only [ev0] at eb)
        exact hl10 (pm_ofNat_ne (n := 10) (by omega) (by decide) (pm_bne eb))
      exact hbad (fun h => hl10 ((pm_key hk1 rfl).1 h.1).1) _ (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
        (by (try rsimp); (try exact hz2)) (by keepz E.hz0)
    subst hl10
    refine WP.branch pm_at_9c (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hg19] at eb; (try simp only [ev0] at eb); exact absurd eb (by decide)
    refine WP.lw pm_at_a0 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x24) (by decide)) ?_; wn
    refine WP.lw pm_at_a2 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x28) (by decide)) ?_; wn
    refine WP.lw pm_at_a4 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x2C) (by decide)) ?_; wn
    refine WP.lui pm_at_a6 ?_; wn
    refine WP.aluImm pm_at_aa ?_; wn
    refine WP.aluImm pm_at_ae ?_; wn
    refine WP.alu pm_at_b0 ?_; wn
    refine WP.callMemcmpIff (tb := BitVec.ofNat 32 memcmpAddress) (p := Q + BitVec.ofNat 32 k1p) (q := TPM_KS)
      (n := 10) pm_at_b2 pm_at_b6 (by decide) (by decide) (by decide) hc2.mc
      (by (try rsimp); (try simp only [ev0]); exact hg9) (by (try rsimp); (try rfl); (try decide))
      (by (try rsimp); (try simp only [ev0]); (try rfl)) (by decide) fun m3 hcmp hm3 => ?_
    rw [hm3]
    rw [E.bytes hO2 (hSQ.subR hk1), tpm_ks hc2] at hcmp
    by_cases hm : memBytes M0 (Q + BitVec.ofNat 32 k1p) 10 = ascii!"signatures"
    rotate_left
    · refine WP.branch pm_at_ba (fun _ => ?_) (fun eb => ?_) <;> wn
      rotate_left
      · exfalso; (try rsimp at eb); exact hm (hcmp.1 (pm_bne eb))
      exact hbad (fun h => hm ((pm_key hk1 rfl).1 h.1).2) _ (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
        (by (try rsimp); (try exact hz2)) (by keepz E.hz0)
    have ha0 := hcmp.2 hm
    refine WP.branch pm_at_ba (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [ha0] at eb; exact absurd eb (by decide)
    refine WP.aluImm pm_at_bc ?_; wn
    by_cases hl6 : k2l = 6
    rotate_left
    · refine WP.branch pm_at_be (fun _ => ?_) (fun eb => ?_) <;> wn
      rotate_left
      · exfalso; (try rsimp at eb); rw [hgsp, t2'] at eb; (try simp only [ev0] at eb)
        exact hl6 (pm_ofNat_ne (n := 6) (by omega) (by decide) (pm_bne eb))
      exact hbad (fun h => hl6 ((pm_key hl.2.2.1 rfl).1 h.2).1) _ (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
        (by (try rsimp); (try exact hz2)) (by keepz E.hz0)
    subst hl6
    refine WP.branch pm_at_be (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t2'] at eb; (try simp only [ev0] at eb); exact absurd eb (by decide)
    refine WP.lbu pm_at_c2 ?_; wn
    refine WP.lbu pm_at_c6 ?_; wn
    refine WP.lbu pm_at_ca ?_; wn
    refine WP.lbu pm_at_ce ?_; wn
    refine WP.lbu pm_at_d2 ?_; wn
    refine WP.lbu pm_at_d6 ?_; wn
    refine WP.aluImm pm_at_da ?_; wn
    refine WP.alu pm_at_dc ?_; wn
    refine WP.aluImm pm_at_de ?_; wn
    refine WP.aluImm pm_at_e0 ?_; wn
    refine WP.alu pm_at_e2 ?_; wn
    refine WP.aluImm pm_at_e4 ?_; wn
    refine WP.alu pm_at_e6 ?_; wn
    refine WP.alu pm_at_e8 ?_; wn
    refine WP.lui pm_at_ea ?_; wn
    refine WP.lui pm_at_ee ?_; wn
    refine WP.aluImm pm_at_f0 ?_; wn
    refine WP.aluImm pm_at_f4 ?_; wn
    refine WP.alu pm_at_f8 ?_; wn
    refine WP.alu pm_at_fa ?_; wn
    refine WP.alu pm_at_fc ?_; wn
    have hk2 : slice (memBytes M0 Q L) k2p 6 = ascii!"signed" ↔
        [(M2 (Q + BitVec.ofNat 32 k2p + 0)).toNat, (M2 (Q + BitVec.ofNat 32 k2p + 1)).toNat,
          (M2 (Q + BitVec.ofNat 32 k2p + 2)).toNat, (M2 (Q + BitVec.ofNat 32 k2p + 3)).toNat,
          (M2 (Q + BitVec.ofNat 32 k2p + 4)).toNat, (M2 (Q + BitVec.ofNat 32 k2p + 5)).toNat] = ascii!"signed" := by
      rw [pm_key (n := 6) hl.2.2.1 rfl, ← E.bytes hO2 (hSQ.subR hl.2.2.1)]
      exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
    have hsig := (pm_signed (M2 (Q + BitVec.ofNat 32 k2p + 0)) (M2 (Q + BitVec.ofNat 32 k2p + 1))
      (M2 (Q + BitVec.ofNat 32 k2p + 2)) (M2 (Q + BitVec.ofNat 32 k2p + 3)) (M2 (Q + BitVec.ofNat 32 k2p + 4))
      (M2 (Q + BitVec.ofNat 32 k2p + 5))).trans hk2.symm
    have c1 : aluEval AluOp.add 1852272640 4294965619 = (0x6E676973 : Word) := by decide
    have c2 : aluEval AluOp.add 24576 1125 = (0x6465 : Word) := by decide
    refine WP.branch pm_at_fe (fun eb => ?_) (fun eb => ?_) <;> wn
    · (try rsimp at eb); rw [hgsp, t1', c1, c2] at eb
      refine hbad (fun h => ?_) _ (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
          (by (try rsimp); (try exact hz2)) (by keepz E.hz0)
      rw [hsig.2 h.2] at eb; exact absurd eb (by decide)
    · (try rsimp at eb); rw [hgsp, t1', c1, c2] at eb
      rw [ite_eq_left ⟨(pm_key (n := 10) hk1 rfl).2 ⟨rfl, hm⟩, hsig.1 (pm_bne eb)⟩]
      exact pm_rest E hO2 (by (try rsimp); exact hgsp) (by (try rsimp); exact hg26) (by (try rsimp); exact hg23)
        (by (try rsimp); exact hg22) hKL hSK hC3 hQ0 hQN hSQ hl.2.2.2.1 hv1 hl.2.2.2.2.2
        (by (try rsimp); rw [hgsp, t3']) (by (try rsimp); rw [hgsp, t4']) (by (try rsimp); exact hg21)
        (by (try rsimp); exact hg18) (by keepz E.hz0)

/-- From 0x60: the members of the top-level object, the `L` bytes at `Q`,
from `pos`. -/
theorem pm_members (E : PmEnv M0 M1 s out F g0) {Mk : Word → BitVec 8} {g : Fin 32 → Word}
    (hO : Out M1 Mk s 484) (hgsp : g sp = F) (hg26 : g 26 = out) {KQ : Word} {KL : Nat}
    (hg23 : g 23 = KQ) (hg22 : g 22 = BitVec.ofNat 32 KL) (hKL : KL < 2 ^ 32) (hSK : Sep s 532 KQ KL)
    {Q : Word} {L pos : Nat} (hC : PmCc Mk (F + BitVec.ofNat 32 16) Q L pos) (hQ0 : Q.toNat ≠ 0)
    (hQN : Q.toNat + L < 2 ^ 32) (hSQ : Sep s 532 Q L) (hpos : pos ≤ L)
    (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (pmRes Q (pmMembers (memBytes M0 Q L) (memBytes M0 KQ KL)
      pos))) Mk 0x60 g := by
  refine WP.aluImm pm_at_60 ?_; wn
  refine WP.aluImm pm_at_62 ?_; wn
  refine pm_nm E pm_at_64 pm_at_68 (by decide) (by decide) hO (by (try rsimp); rw [ev_add, hgsp])
    (by (try rsimp); rw [ev_add, hgsp]; (try rfl)) (by (try rsimp); exact hgsp) hC hQ0 hQN hpos hSQ
    fun m2 hR => ?_
  obtain ⟨Ma, hOa, hMR⟩ := hR
  generalize m2.mem = M2 at hMR
  have hC2 : PmCc Ma (F + BitVec.ofNat 32 16) Q L pos :=
    hC.keep hOa (E.fs (Or.inr (by decide)) (by decide) (by decide)).symm
  have hO2 : Out M1 M2 s 484 := pm_nmOut E hO hOa hMR
  refine WP.zero fun hz2 => ?_
  refine WP.lbu pm_at_6c ?_; wn
  rcases hnm : nextMember (memBytes M0 Q L) pos with _ | _ | ⟨k1p, k1l, v1p, v1l, a1⟩ <;>
    rw [hnm] at hMR <;> simp only [memRes, Option.map_none, Option.map_some] at hMR <;>
    simp only [pmMembers, hnm]
  · obtain ⟨-, t0, t1⟩ := hMR
    refine WP.branch pm_at_70 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hgsp, t0] at eb; exact absurd eb (by decide)
    exact pm_8e E hO2 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
      (by rw [show F + 0x1D = F + 0x1C + 1 by rw [BitVec.add_assoc]; rfl]; exact t1) (by keepz E.hz0)
  · obtain ⟨-, t0, t1⟩ := hMR
    refine WP.branch pm_at_70 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t0] at eb; exact absurd eb (by decide)
    refine WP.lw pm_at_72 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
    have t1' : memLoad32 M2 (F + 0x20) = 0 := by
      rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t1
    refine WP.branch pm_at_74 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hgsp, t1'] at eb; exact absurd eb (by decide)
    exact pm_116 E hO2 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp) (by (try rsimp); (try exact hz2))
      (by keepz E.hz0)
  · obtain ⟨hfa, t0, t1, t2, t3, t4, t5⟩ := hMR
    have hl := nextMember_lt hnm
    rw [memBytes_length] at hl
    have hC3 : PmCc M2 (F + BitVec.ofNat 32 16) Q L a1 := pm_ccNext hC2 hfa t5
    have t1' : memLoad32 M2 (F + 0x20) = Q + BitVec.ofNat 32 k1p := by
      rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t1
    have t2' : memLoad32 M2 (F + 0x24) = BitVec.ofNat 32 k1l := by
      rw [show F + 0x24 = F + 0x1C + 8 by rw [BitVec.add_assoc]; rfl]; exact t2
    have t3' : memLoad32 M2 (F + 0x28) = Q + BitVec.ofNat 32 v1p := by
      rw [show F + 0x28 = F + 0x1C + 12 by rw [BitVec.add_assoc]; rfl]; exact t3
    have t4' : memLoad32 M2 (F + 0x2C) = BitVec.ofNat 32 v1l := by
      rw [show F + 0x2C = F + 0x1C + 16 by rw [BitVec.add_assoc]; rfl]; exact t4
    refine WP.branch pm_at_70 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t0] at eb; exact absurd eb (by decide)
    refine WP.lw pm_at_72 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
    have hq := nx_q0 hQ0 (n := L + 1) (pos := k1p) (by omega) (by omega)
    refine WP.branch pm_at_74 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t1', hq] at eb; exact absurd eb (by decide)
    refine WP.lw pm_at_76 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x24) (by decide)) ?_; wn
    refine WP.lw pm_at_78 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x28) (by decide)) ?_; wn
    refine WP.lw pm_at_7a (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x2C) (by decide)) ?_; wn
    exact pm_two E hO2 (by (try rsimp); exact hgsp) (by (try rsimp); exact hg26) (by (try rsimp); exact hg23)
      (by (try rsimp); exact hg22) hKL hSK hC3 hQ0 hQN hSQ hl.2.2.2.1 hl.2.2.1 hl.2.2.2.2.2
      (by (try rsimp); rw [hgsp, t1']) (by (try rsimp); rw [hgsp, t2']) (by (try rsimp); rw [hgsp, t3'])
      (by (try rsimp); rw [hgsp, t4']) (by keepz E.hz0)

/-- In strict mode the value `parse` returns is the whole document, so the
model's offsets are those of `pmObj` on the document. -/
theorem pm_model_eq {d kind : Bytes} {tp tl : Nat} (h : parseModel true d = .ok (tp, tl)) :
    pmModel d kind = pmObj d kind := by
  obtain ⟨rfl, rfl⟩ := parseModel_ok_canon h
  simp only [pmModel, h]
  have hs : slice d 0 d.length = d := by
    show (d.drop 0).take d.length = d
    rw [List.drop_zero, List.take_length]
  rw [hs]
  rcases pmObj d kind with _ | ⟨_, _, _, _⟩ <;> first | rfl | simp only [Nat.zero_add]

/-- From 0x1A, after the prologue: `parse`, `members`, the copy of the
cursor, and `pm_members`. -/
theorem pm_body (E : PmEnv M0 M1 s out F g0) {g : Fin 32 → Word} (hgsp : g sp = F) {p KQ : Word} {n KL : Nat}
    (hg0 : g a0 = out) (hg1 : g a1 = p) (hg2 : g a2 = BitVec.ofNat 32 n) (hg3 : g a3 = KQ)
    (hg4 : g a4 = BitVec.ofNat 32 KL) (hz : g 0 = 0) (hfr : ∀ x, x ∉ pmE → g x = g0 x) (hn : n < 2 ^ 31)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n < 2 ^ 32) (hSp : Sep s 532 p n) (hKL : KL < 2 ^ 32)
    (hSK : Sep s 532 KQ KL) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (pmRes p (pmModel (memBytes M0 p n) (memBytes M0 KQ KL))))
      M1 0x1A g := by
  have hc := E.code (Out.refl M1 s 484)
  refine WP.alu pm_at_1a ?_; wn
  refine WP.alu pm_at_1c ?_; wn
  refine WP.alu pm_at_1e ?_; wn
  refine WP.aluImm pm_at_20 ?_; wn
  refine WP.aluImm pm_at_22 ?_; wn
  refine WP.callParse (tb := TPM_JP) (out := F + 0x1C) (s := s) (p := p) (n := n) (c := true)
    pm_at_24 pm_at_28 (by decide) (by decide) (by decide) hc.parse (by (try rsimp); rw [ev_add, hgsp])
    (by (try rsimp); exact hg1) (by (try rsimp); exact hg2) (by (try rsimp); (try rfl); (try decide))
    (by (try rsimp); rw [hgsp]; exact E.hF.symm) E.hal (aligned_add E.halF (by decide))
    (by have := E.hsw; omega) hn hp0 hpn (tpm_parseSep (by have := E.hsw; omega) (tex_sepL E.hro (by decide)))
    (tex_sepL hSp (by decide))
    (by rw [show F + 0x1C = F + BitVec.ofNat 32 0x1C from rfl, E.Fc]
        exact (tex_sepS (by decide) (by have := E.hsw; omega)).symm)
    (E.lowF (by decide) (by decide) (by decide))
    (lowSep (by have := E.hsw; omega) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide))
    fun m2 hR => ?_
  rw [E.bytes (Out.refl M1 s 484) hSp] at hR
  generalize m2.mem = M2 at hR
  obtain ⟨Mb, hOb, hFR⟩ := hR
  have hO2 : Out M1 M2 s 484 :=
    (hOb.mono (by decide)).trans (Out.upK (c := 432) (E.Fc 0x1C).symm hFR.out (by decide))
  refine WP.zero fun hz2 => ?_
  refine WP.lw pm_at_2c (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x1C) (by decide)) ?_; wn
  rcases hpm : parseModel true (memBytes M0 p n) with e | ⟨tp, tl⟩ <;>
    rw [hpm] at hFR <;> simp only [fieldRes, Except.map] at hFR <;> (try dsimp only)
  · obtain ⟨-, t1, t2⟩ := hFR
    simp only [pmModel, hpm]
    refine WP.branch pm_at_2e (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
    exact pm_264 E hO2 (by (try rsimp); (try simp only [ev0]); exact hg0) (by (try rsimp); exact hgsp)
      (by rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2) (by keepz E.hz0)
  · obtain ⟨-, t1, t2⟩ := hFR
    obtain ⟨rfl, htl⟩ := parseModel_ok_canon hpm
    rw [memBytes_length] at htl; subst tl
    rw [pm_model_eq hpm]
    rw [add_ofNat_zero] at t1
    have t2' : memLoad32 M2 (F + 0x20) = BitVec.ofNat 32 n := by
      rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
    refine WP.branch pm_at_2e (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb
      have e0 : p = 0 := by simpa [branchTaken] using eb
      exact hp0 (by rw [e0]; rfl)
    refine WP.lw pm_at_32 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
    refine WP.aluImm pm_at_34 ?_; wn
    have hc2 := E.code hO2
    refine WP.callMembers (tb := TPM_JG + 0xA6) (out := F + 0x1C) (s := s + BitVec.ofNat 32 388) (p := p) (n := n)
      pm_at_36 pm_at_3a (by decide) (by decide) (by decide) hc2.get.me
      (by rw [show TPM_JG + 0xA6 + 0xFFFFF7F8 = TPM_JG + 0xFFFFF616 + 0x288 by decide]; exact hc2.get.ri.sw)
      (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); rw [hgsp, t1]) (by (try rsimp); rw [hgsp, t2'])
      (by (try rsimp); rw [hgsp]; exact (E.sp 388 (by decide)).symm) (by omega) (E.alS (by decide))
      (aligned_add E.halF (by decide)) (E.lowS (by decide) (by decide) (by decide))
      (E.lowS (by decide) (by decide) (by decide)) (hSp.sub (by decide))
      (E.fs (Or.inr (by decide)) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide))
      (E.lowS (by decide) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide)) fun m3 hR => ?_
    rw [E.bytes hO2 hSp] at hR
    generalize m3.mem = M3 at hR
    obtain ⟨Mc, hOc, hCR⟩ := hR
    have hO3 : Out M1 M3 s 484 :=
      hO2.trans ((Out.upK rfl hOc (by decide)).trans (Out.upK (c := 432) (E.Fc 0x1C).symm hCR.out (by decide)))
    refine WP.zero fun hz3 => ?_
    refine WP.lw pm_at_3e (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x1C) (by decide)) ?_; wn
    refine WP.lbu pm_at_40 ?_; wn
    rcases hco : curOpen 123 p (memBytes M0 p n) with _ | ⟨q, l, k⟩ <;> rw [hco] at hCR
    · obtain ⟨-, u1, u2⟩ := hCR
      rw [pmObj, ite_eq_left (pm_co_none hco)]
      refine WP.branch pm_at_44 (fun _ => ?_) (fun eb => ?_) <;> wn
      rotate_left
      · exfalso; (try rsimp at eb); rw [hgsp, u1] at eb; exact absurd eb (by decide)
      exact pm_272 E hO3 (by (try rsimp); (try simp only [ev0]); exact hg0) (by (try rsimp); exact hgsp)
        (by (try rsimp); rw [hgsp, show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl, u2, ri_ze]; (try rfl))
        (by (try rsimp); (try exact hz3)) (by keepz E.hz0)
    · obtain ⟨hq, hl, hk, hnn⟩ := pm_co_some hco
      rw [pmObj, ite_eq_right hnn]
      rw [memBytes_length] at hl
      obtain ⟨-, u1, u2, u3⟩ := hCR
      rw [hq] at u1; rw [hl] at u2; rw [hk] at u3
      refine WP.branch pm_at_44 (fun eb => ?_) (fun _ => ?_) <;> wn
      · exfalso; (try rsimp at eb); rw [hgsp, u1] at eb
        have e0 : p = 0 := by simpa [branchTaken] using eb
        exact hp0 (by rw [e0]; rfl)
      refine WP.aluImm pm_at_48 ?_; wn
      refine WP.aluImm pm_at_4c ?_; wn
      refine WP.aluImm pm_at_50 ?_; wn
      have hc3 := E.code hO3
      have EM : McEnv M3 (TPM_JG + 0xBFDA + 8) (F + 0x15) (F + 0x21) (s + BitVec.ofNat 32 388) 7 := by
        refine ⟨by rw [show TPM_JG + 0xBFDA + 8 = TPM_JG + 0xBFE2 by decide]; exact hc3.get.mc,
          E.lowF (by decide) (by decide) (by decide), E.lowS (by decide) (by decide) (by decide),
          E.fs (Or.inr (by decide)) (by decide) (by decide), E.fs (Or.inr (by decide)) (by decide) (by decide),
          pm_ff F (Or.inl (by decide)) (by decide) (by decide), E.alS (by decide), ?_, ?_, ?_⟩
        · have := E.wS (d := 388) (k := 16) (by decide); omega
        · show (F + BitVec.ofNat 32 0x15).toNat + 7 < 2 ^ 32
          rw [E.FN (by decide)]; have := E.hsw; omega
        · show (F + BitVec.ofNat 32 0x21).toNat + 7 < 2 ^ 32
          rw [E.FN (by decide)]; have := E.hsw; omega
      refine WP.callMemcpy (tb := TPM_JG + 0xBFDA) (dst := F + 0x15) (src := F + 0x21)
        (F := s + BitVec.ofNat 32 388) (N := 7) pm_at_52 pm_at_56 (by decide) (by decide) (by decide)
        hc3.get.stub EM (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); rw [ev_add, hgsp])
        (by (try rsimp); (try simp only [ev0]); try rfl)
        (by (try rsimp); rw [hgsp]; exact (E.sp 388 (by decide)).symm) (E.lowS (by decide) (by decide) (by decide))
        (E.lowF (by decide) (by decide) (by decide)) fun m4 hO4 => ?_
      generalize m4.mem = M4 at hO4
      refine WP.sw pm_at_5a (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x10) (by decide))
        (by (try rsimp); rw [hgsp]; exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
      refine WP.sb pm_at_5c (by (try rsimp); rw [hgsp]; exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
      (try rsimp)
      rw [hgsp, u1, ri_ze]
      generalize hM5 : memStore8 (memStore32 M4 (F + 16) p) (F + 20) (M3 (F + 0x20)) = M5
      have hsk := skipWs_le (memBytes M0 p n) 1
      rw [memBytes_length] at hsk hnn
      have hcc := pm_ccopy (M2 := M3) (M3 := M4) (F := F) (S := s + BitVec.ofNat 32 388) (q := p) (d := 0x10)
        (a := 0x1C) (by decide) (E.fs (Or.inr (by decide)) (by decide) (by decide))
        (by rw [show F + BitVec.ofNat 32 (0x1C + 4) = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact u2)
        (by rw [show F + BitVec.ofNat 32 (0x1C + 8) = F + 0x1C + 8 by rw [BitVec.add_assoc]; rfl]; exact u3) hO4 hM5
      obtain ⟨hC5, hfa⟩ := hcc
      have hO5 : Out M1 M5 s 484 := fun x hx =>
        (hfa x (by rw [E.Fc]; exact sep_in hx (by decide)) (sep_in hx (by decide))).trans (hO3 x hx)
      exact pm_members E hO5 (by (try rsimp); exact hgsp) (by (try rsimp); (try simp only [ev0]); exact hg0)
        (by (try rsimp); (try simp only [ev0]); exact hg3)
        (by (try rsimp); (try simp only [ev_mv hz]); exact hg4) hKL hSK hC5
        hp0 hpn hSp (by omega) (by keepz E.hz0)

end

/-- `tuf::parse_metadata` from its entry, as a weakest precondition. -/
theorem pm_wp {M0 : Word → BitVec 8} {s out p KQ : Word} {n KL : Nat} {g0 : Fin 32 → Word}
    (hg0 : g0 a0 = out) (hg1 : g0 a1 = p) (hg2 : g0 a2 = BitVec.ofNat 32 n) (hg3 : g0 a3 = KQ)
    (hg4 : g0 a4 = BitVec.ofNat 32 KL) (hsp : g0 sp = s + BitVec.ofNat 32 532) (hret : g0 ra &&& ~~~1 = g0 ra)
    (hal : s.toNat % 4 = 0) (hsw : s.toNat + 532 ≤ 0x40000000)
    (hro : Sep s 532 (BitVec.ofNat 32 roWindowAddress) roWindowSize) (halo : out.toNat % 4 = 0)
    (how : out.toNat + 16 ≤ 0x40000000) (hso : Sep out 16 s 532) (hc : PmCode M0) (hn : n < 2 ^ 31)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n < 2 ^ 32) (hSp : Sep s 532 p n) (hKL : KL < 2 ^ 32)
    (hSK : Sep s 532 KQ KL) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (pmRes p (pmModel (memBytes M0 p n) (memBytes M0 KQ KL))))
      M0 0 g0 := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm pm_at_0 ?_; wn
  have esp : aluEval .add (g0 sp) 0xFFFFFF80 = s + BitVec.ofNat 32 404 := by
    rw [hsp, ev_add, BitVec.add_assoc]; rfl
  rw [esp]
  generalize hF : s + BitVec.ofNat 32 404 = F
  obtain ⟨hO1, hv⟩ := tpm_pro M0 F g0
  have E : PmEnv M0 (pmM1 M0 F g0) s out F g0 :=
    ⟨hF, hal, hsw, halo, how, hso, hro, hc, Out.upK hF hO1 (by decide), hv,
      by rw [hsp, ← hF, add_ofNat_assoc], hret, hz⟩
  refine WP.sw pm_at_2 (by (try rsimp); exact aligned_add E.halF (k := 0x7C) (by decide))
    (by (try rsimp); exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
  refine WP.sw pm_at_4 (by (try rsimp); exact aligned_add E.halF (k := 0x78) (by decide))
    (by (try rsimp); exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
  refine WP.sw pm_at_6 (by (try rsimp); exact aligned_add E.halF (k := 0x74) (by decide))
    (by (try rsimp); exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
  refine WP.sw pm_at_8 (by (try rsimp); exact aligned_add E.halF (k := 0x70) (by decide))
    (by (try rsimp); exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
  refine WP.sw pm_at_a (by (try rsimp); exact aligned_add E.halF (k := 0x6C) (by decide))
    (by (try rsimp); exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
  refine WP.sw pm_at_c (by (try rsimp); exact aligned_add E.halF (k := 0x68) (by decide))
    (by (try rsimp); exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
  refine WP.sw pm_at_e (by (try rsimp); exact aligned_add E.halF (k := 0x64) (by decide))
    (by (try rsimp); exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
  refine WP.sw pm_at_10 (by (try rsimp); exact aligned_add E.halF (k := 0x60) (by decide))
    (by (try rsimp); exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
  refine WP.sw pm_at_12 (by (try rsimp); exact aligned_add E.halF (k := 0x5C) (by decide))
    (by (try rsimp); exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
  refine WP.sw pm_at_14 (by (try rsimp); exact aligned_add E.halF (k := 0x58) (by decide))
    (by (try rsimp); exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
  refine WP.sw pm_at_16 (by (try rsimp); exact aligned_add E.halF (k := 0x54) (by decide))
    (by (try rsimp); exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
  refine WP.sw pm_at_18 (by (try rsimp); exact aligned_add E.halF (k := 0x50) (by decide))
    (by (try rsimp); exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
  change WP tufParseMetadataCode TPM _ (pmM1 M0 F g0) 0x1A _
  exact pm_body E (by rsimp) (by (try rsimp); exact hg0) (by (try rsimp); exact hg1) (by (try rsimp); exact hg2)
    (by (try rsimp); exact hg3) (by (try rsimp); exact hg4) (by (try rsimp); (try exact hz)) (by keepz hz) hn hp0 hpn
    hSp hKL hSK

/-- `tuf::parse_metadata` from its entry, with `out` in `a0`, the `n`-byte
document at `p` in `a1` and `a2`, the `KL`-byte type at `KQ` in `a3` and
`a4`, and the stack the 532 bytes below `sp` (its own 128-byte frame and the
404 bytes that its callees use). It returns to `ra` with `pmModel` of the
document and the type at `out`: on success the address and length of
`signed`, then of `signatures`; otherwise the zero word and the error byte.
Memory outside the stack and the 16 bytes at `out` is as before, and so is
every register outside `jClob`. The stack and `out` lie below the code, and
the stack is apart from the read-only data window, `out`, the document, and
the type. -/
theorem tufParseMetadata_correct (m : Machine) {retAddr out s p KQ : Word} {n KL : Nat}
    (hc : PmCode m.mem) (hpc : m.pc = TPM) (ha0 : reg m a0 = out) (ha1 : reg m a1 = p)
    (ha2 : reg m a2 = BitVec.ofNat 32 n) (ha3 : reg m a3 = KQ) (ha4 : reg m a4 = BitVec.ofNat 32 KL)
    (hsp : reg m sp = s + BitVec.ofNat 32 532) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hal : s.toNat % 4 = 0) (hsw : s.toNat + 532 ≤ 0x40000000)
    (hro : Sep s 532 (BitVec.ofNat 32 roWindowAddress) roWindowSize) (halo : out.toNat % 4 = 0)
    (how : out.toNat + 16 ≤ 0x40000000) (hso : Sep out 16 s 532) (hn : n < 2 ^ 31) (hp0 : p.toNat ≠ 0)
    (hpn : p.toNat + n < 2 ^ 32) (hSp : Sep s 532 p n) (hKL : KL < 2 ^ 32) (hSK : Sep s 532 KQ KL) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      PmRes m.mem m'.mem s out (pmRes p (pmModel (memBytes m.mem p n) (memBytes m.mem KQ KL))) ∧
      ∀ r, r ∉ jClob → reg m' r = reg m r := by
  obtain ⟨m', st, hpc', hR, hfr⟩ := WP.run (pm_wp ha0 ha1 ha2 ha3 ha4 hsp (by rw [hra]; exact hret) hal hsw hro
    halo how hso hc hn hp0 hpn hSp hKL hSK) (by decide) hc.self hpc
  exact ⟨m', st, hpc'.trans hra, hR, hfr⟩

end C3.RV32
