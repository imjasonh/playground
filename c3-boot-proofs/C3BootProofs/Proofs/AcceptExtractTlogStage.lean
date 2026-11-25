import C3BootProofs.Proofs.AcceptExtractTlogKey

/-! `AceTlogStage`: a pass's start at 0xEF2, a log that isn't Ed25519, and the loop. -/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

set_option maxRecDepth 100000

section
variable {X : AceCtx} {n0 : Machine} {fp0 : Word} {jr : Json} {fs : List FulcioKey} {j : Json}
  {rest : List Json} {ls : List LogKey} {M : Word → BitVec 8} {f : Fin 32 → Word}

set_option maxHeartbeats 4000000 in
/-- At 0xEBA after a pass that skips its log, whose key isn't Ed25519. -/
theorem acetl_skip (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs (j :: rest) ls)
    (R : AceHR X f) (h26 : f 26 = reg n0 26) (S : AcetlS X n0 fp0 M fp0 rest) (hj : logEntry j = some none) :
    WP bootMainClosure0Code AC (acetlQ X 0xEBA (acetlNx X jr fs rest)) M 0xEBA f := by
  have hfp0 := A.fr.lo
  have hfh := A.fr.hi
  have hbw := O.lay.hi
  unfold acBufLen at hbw
  have hprog := I.tlogs.step hj
  rw [show (none : Option LogKey).toList = [] from rfl, List.append_nil] at hprog
  refine WP.here (acetl_close O A I R h26 (fp1 := fp0) (Nat.le_refl _) S.hi S.fpv S.flv
    (fun x hx _ _ => S.m x hx) S.cur hprog ?_ ?_)
  · refine ace_array_move I.logs (fun c hc => ?_) fun y h1 h2 => ?_
    · rw [acetl_slot4 X.B (s := 0x350) (i := c) rfl]
      refine S.m _ (acetl_U_slot O hfp0 (k := 0x350 + c) (by omega) (fun r hr => ?_) (.inl (by omega)))
      simp only [acetlW, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
    · have hs := ace_ofSep (ace_bufOut O.lay (y := y) (by omega) (by unfold acBufLen; omega))
      exact S.m y (acetl_U_out hs (.inl h2))
  · rw [acetl_ld O S.m hfp0 (s := 0x2C) (by decide) (by decide) (by decide)]; exact I.count

set_option maxHeartbeats 4000000 in
/-- From 0xEF2: `field` for `publicKey` and `keyDetails`, `str`, and the
check for `PKIX_ED25519`. -/
theorem acetl_tEF2 (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs (j :: rest) ls)
    (R : AceHR X f) (h26 : f 26 = reg n0 26) (S : AcetlS X n0 fp0 M fp0 rest)
    {jq : Word} {jl : Nat} (hjv : AceVal X.D X.json jq jl j) (h22 : f 22 = jq)
    (hjl : memLoad32 M (acSlot X.B 0x1328) = BitVec.ofNat 32 jl) :
    WP bootMainClosure0Code AC (acetlQ X 0xEBA (acetlNx X jr fs rest)) M 0xEF2 f := by
  have F := O.lay.fr
  have hfp0 := A.fr.lo
  have hd := S.doc O A
  have E := acetl_env O A S.m
  have e1328 : ∀ w : Word, w = acSlot X.B 0x1328 → memLoad32 M w = BitVec.ofNat 32 jl := fun w h => h ▸ hjl
  refine WP.lui ac_at_ef2 ?_; wn
  refine WP.aluImm ac_at_ef4 ?_; wn
  refine WP.alu ac_at_ef8 ?_; wn
  refine WP.lw ac_at_efc (acetl_al O (s := 0x1328) (by (try rsimp); simp only [ev_add, R.rsp, acSlot]; bv_omega)
    (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_f00 ?_; wn
  refine WP.aluImm ac_at_f02 ?_; wn
  refine WP.alu ac_at_f06 ?_; wn
  refine WP.aluImm ac_at_f08 ?_; wn
  refine WP.alu ac_at_f0a ?_; wn
  refine WP.alu ac_at_f0c ?_; wn
  refine WP.lui ac_at_f0e ?_; wn
  refine WP.aluImm ac_at_f12 ?_; wn
  refine WP.acetlField O (o := 0x1320) (a := 0x4D70) (b := 0x4D88) (kq := (img% roWindowAddress + 0x80B)) (kl := 9)
    (by decide) (by decide) (by decide) (by decide) ac_at_f16 ac_at_f1a (by decide) (by decide) E hd hjv E.kKey
    (by decide) (by decide) (by rsimp; exact R.rsp)
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [h22, ev_add]; exact BitVec.zero_add _)
    (by rsimp; simp only [ev_add, R.rsp]; exact (BitVec.zero_add _).trans (e1328 _ (by simp only [acSlot]; bv_omega)))
    (by rsimp <;> rfl)
    (by rsimp <;> rfl) fun m2 hfr _ hres => ?_
  have S2 := S.call O hfr
  generalize m2.mem = M2 at hfr hres S2
  have e28 : X.B + 0x3A50 + 0x28 = acSlot X.B 0x28 := by simp only [acSlot]; bv_omega
  refine WP.lui ac_at_f1e ?_; wn
  refine WP.aluImm ac_at_f20 ?_; wn
  refine WP.alu ac_at_f24 ?_; wn
  refine WP.lw ac_at_f26 (acetl_al O (s := 0x1320) (by (try rsimp); simp only [ev_add, R.rsp, acSlot]; bv_omega)
    (by decide) (by decide)) ?_; wn
  refine WP.sw ac_at_f28 (by rsimp; rw [R.rsp, e28]; exact ace_al4 F (by decide) (by decide))
    (by rsimp; rw [R.rsp, e28]; exact ace_cs F (by decide)) ?_; wn
  have e1320 : aluEval .add (X.B + 0x3A50) (aluEval .add 4096 784) + 16 = acSlot X.B 0x1320 := by
    simp only [ev_add, acSlot]; bv_omega
  rw [R.rsp, e28, e1320]
  have S3 := S2.store O (s := 0x28) (.inr rfl) (memLoad32 M2 (acSlot X.B 0x1320))
  have e4 : acSlot X.B 0x1320 + 4 = acSlot X.B 0x1324 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  have h1324 : memStore32 M2 (acSlot X.B 0x28) (memLoad32 M2 (acSlot X.B 0x1320)) (acSlot X.B 0x1324) =
      M2 (acSlot X.B 0x1324) := memStore32_get_sep (ace_sepB' F (.inl (by decide)) (by decide) (by decide))
  have l1324 : memLoad32 (memStore32 M2 (acSlot X.B 0x28) (memLoad32 M2 (acSlot X.B 0x1320))) (acSlot X.B 0x1324) =
      memLoad32 M2 (acSlot X.B 0x1324) := memLoad32_store32_sep (ace_sepB' F (.inl (by decide)) (by decide) (by decide))
  have l28 : memLoad32 (memStore32 M2 (acSlot X.B 0x28) (memLoad32 M2 (acSlot X.B 0x1320))) (acSlot X.B 0x28) =
      memLoad32 M2 (acSlot X.B 0x1320) := memLoad32_store32_same _ _ _
  generalize memStore32 M2 (acSlot X.B 0x28) (memLoad32 M2 (acSlot X.B 0x1320)) = M3 at S3 h1324 l1324 l28
  rcases hf : j.field (ascii!"publicKey") with _ | key <;> rw [hf] at hres
  · obtain ⟨t0, t4⟩ := hres
    refine WP.branch ac_at_f2a (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact acetl_f140A O A S3.m (by hr) (by rsimp; simp only [ev_add, acSlot]; bv_omega)
        (by rw [h1324, ← e4, t4]; decide)
    · exfalso; rsimp at eb; rw [t0] at eb; exact absurd eb (by decide)
  obtain ⟨kq, kl, hkv, t0, t4⟩ := hres
  obtain ⟨b1, b2, b3, b4, b5⟩ := acetl_valB O hkv
  refine WP.branch ac_at_f2a (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [t0] at eb
    have e : kq = 0 := by simpa [branchTaken] using eb
    rw [e] at b3; simp at b3
  have e1C : X.B + 0x3A50 + 0x1C = acSlot X.B 0x1C := by simp only [acSlot]; bv_omega
  have e1324 : aluEval .add (X.B + 0x3A50) (aluEval .add 4096 784) + 20 = acSlot X.B 0x1324 := by
    simp only [ev_add, acSlot]; bv_omega
  refine WP.lui ac_at_f2e ?_; wn
  refine WP.aluImm ac_at_f30 ?_; wn
  refine WP.alu ac_at_f34 ?_; wn
  refine WP.lw ac_at_f38 (acetl_al O (s := 0x1324) (by (try rsimp); simp only [ev_add, R.rsp, acSlot]; bv_omega)
    (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_f3a ?_; wn
  refine WP.aluImm ac_at_f3c ?_; wn
  refine WP.alu ac_at_f40 ?_; wn
  refine WP.aluImm ac_at_f42 ?_; wn
  refine WP.lw ac_at_f44 (by rsimp; rw [R.rsp, e28]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.sw ac_at_f46 (by rsimp; rw [R.rsp, e1C]; exact ace_al4 F (by decide) (by decide))
    (by rsimp; rw [R.rsp, e1C]; exact ace_cs F (by decide)) ?_; wn
  rw [R.rsp, e1C, e1324, e28, l1324, l28, t0, ← e4, t4]
  have S4 := S3.store O (s := 0x1C) (.inl rfl) (BitVec.ofNat 32 kl)
  have l1C : memLoad32 (memStore32 M3 (acSlot X.B 0x1C) (BitVec.ofNat 32 kl)) (acSlot X.B 0x1C) =
      BitVec.ofNat 32 kl := memLoad32_store32_same _ _ _
  have l28' : memLoad32 (memStore32 M3 (acSlot X.B 0x1C) (BitVec.ofNat 32 kl)) (acSlot X.B 0x28) = kq := by
    rw [acetl_ldS F (.inl (by decide)) (by decide) (by decide), l28, t0]
  generalize memStore32 M3 (acSlot X.B 0x1C) (BitVec.ofNat 32 kl) = M4 at S4 l1C l28'
  refine WP.lui ac_at_f48 ?_; wn
  refine WP.aluImm ac_at_f4c ?_; wn
  have hd4 := S4.doc O A
  have E4 := acetl_env O A S4.m
  refine WP.acetlField O (o := 0x1320) (a := 0x4D70) (b := 0x4D88) (kq := (img% roWindowAddress + 0x814)) (kl := 10)
    (by decide) (by decide) (by decide) (by decide) ac_at_f50 ac_at_f54 (by decide) (by decide) E4 hd4 hkv E4.kDetails
    (by decide) (by decide) (by rsimp; exact R.rsp)
    (by rsimp; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp)
    (by rsimp)
    (by rsimp <;> rfl)
    (by rsimp <;> rfl) fun m5 hfr5 _ hres5 => ?_
  have S5 := S4.call O hfr5
  have h28' : memLoad32 m5.mem (acSlot X.B 0x28) = kq :=
    (acetl_ldV O hfr5 (s := 0x28) (by decide) (by decide)).trans l28'
  have h1C' : memLoad32 m5.mem (acSlot X.B 0x1C) = BitVec.ofNat 32 kl :=
    (acetl_ldV O hfr5 (s := 0x1C) (by decide) (by decide)).trans l1C
  generalize m5.mem = M5 at hfr5 hres5 S5 h28' h1C'
  refine WP.lw ac_at_f58 (acetl_al O (s := 0x1320) (by (try rsimp); simp only [ev_add, acSlot]; bv_omega)
    (by decide) (by decide)) ?_; wn
  rw [e1320]
  rcases hf5 : key.field (ascii!"keyDetails") with _ | ju <;> rw [hf5] at hres5
  · obtain ⟨t0, t4⟩ := hres5
    refine WP.branch ac_at_f5a (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact acetl_f1402 O A S5.m (by hr) (by rw [← e4, t4]; decide)
    · exfalso; rsimp at eb; rw [t0] at eb; exact absurd eb (by decide)
  obtain ⟨uq, ul, huv, t0, t4⟩ := hres5
  obtain ⟨c1, c2, c3, c4, c5⟩ := acetl_valB O huv
  refine WP.branch ac_at_f5a (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [t0] at eb
    have e : uq = 0 := by simpa [branchTaken] using eb
    rw [e] at c3; simp at c3
  refine WP.lui ac_at_f5e ?_; wn
  refine WP.aluImm ac_at_f60 ?_; wn
  refine WP.alu ac_at_f64 ?_; wn
  refine WP.lw ac_at_f66 (acetl_al O (s := 0x1324) (by (try rsimp); simp only [ev_add, R.rsp, acSlot]; bv_omega)
    (by decide) (by decide)) ?_; wn
  refine WP.aluImm ac_at_f68 ?_; wn
  refine WP.aluImm ac_at_f6c ?_; wn
  have hd5 := S5.doc O A
  have e1324' : ∀ w, w = acSlot X.B 0x1324 → memLoad32 M5 w = BitVec.ofNat 32 ul := fun w h => by
    rw [h, ← e4]; exact t4
  have E5 := acetl_env O A S5.m
  refine WP.acetlStr O ac_at_f70 ac_at_f74 (by decide) (by decide) E5 hd5 huv
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [t0])
    (by rsimp; exact e1324' _ (by simp only [ev_add, R.rsp, acSlot]; bv_omega)) fun m6 hfr6 hstr => ?_
  have S6 := S5.call O hfr6
  have h28'' : memLoad32 m6.mem (acSlot X.B 0x28) = kq :=
    (acetl_ldV O hfr6 (s := 0x28) (by decide) (by decide)).trans h28'
  have h1C'' : memLoad32 m6.mem (acSlot X.B 0x1C) = BitVec.ofNat 32 kl :=
    (acetl_ldV O hfr6 (s := 0x1C) (by decide) (by decide)).trans h1C'
  generalize m6.mem = M6 at hfr6 hstr S6 h28'' h1C''
  have e0 : acSlot X.B 0x890 + 0 = acSlot X.B 0x890 := BitVec.add_zero _
  have e894 : acSlot X.B 0x890 + 4 = acSlot X.B 0x894 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  rcases hs : ju.asStr with _ | s <;> rw [hs] at hstr
  · obtain ⟨t0, t4⟩ := hstr
    refine WP.lw ac_at_f78 (by rsimp; rw [R.r19, e0]; exact ace_al4 F (by decide) (by decide)) ?_; wn
    refine WP.branch ac_at_f7c (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact acetl_f1410 O A S6.m (by hr) (by rw [t4]; decide)
    · exfalso; rsimp at eb; rw [R.r19, e0, t0] at eb; exact absurd eb (by decide)
  obtain ⟨q, hsq, t0, t4⟩ := hstr
  have hb := acetl_inB O hsq
  refine WP.lw ac_at_f78 (by rsimp; rw [R.r19, e0]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.branch ac_at_f7c (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [R.r19, e0, t0] at eb
    have e : q = 0 := by simpa [branchTaken] using eb
    rw [e] at hb; have : (0 : Word).toNat = 0 := rfl
    omega
  have hdet : (key.field (ascii!"keyDetails") >>= Json.asStr) = some s := by rw [hf5]; exact hs
  refine WP.lw ac_at_f80 (by rsimp; rw [R.r19, e894]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.aluImm ac_at_f84 ?_; wn
  refine WP.branch ac_at_f86 (fun eb => ?_) (fun eb => ?_) <;> wn
  · have hl : s.length ≠ 12 := by
      intro h; rsimp at eb; rw [R.r19, t4, h] at eb; exact absurd eb (by decide)
    exact acetl_skip O A I (by hr) (by rsimp; exact h26) S6
      (acetl_logEntry_none hf hdet fun h => hl (by rw [h]; rfl))
  obtain ⟨hb1, hb2, hb3⟩ := hb
  have hl12 : s.length = 12 := by
    rsimp at eb; rw [R.r19, t4] at eb
    have e1 : (BitVec.ofNat 32 s.length != 12) = false := eb
    have e12 : BitVec.ofNat 32 s.length = 12 := by
      cases h : (BitVec.ofNat 32 s.length == 12)
      · rw [bne, h] at e1; exact absurd e1 (by decide)
      · exact beq_iff_eq.mp h
    have := congrArg BitVec.toNat e12
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    exact this
  refine WP.aluImm ac_at_f8a ?_; wn
  refine WP.lui ac_at_f8c ?_; wn
  refine WP.aluImm ac_at_f90 ?_; wn
  have E6 := acetl_env O A S6.m
  refine WP.callMemcmpIff (tb := RMC) (p := q) (q := (img% roWindowAddress + 0x81E)) (n := 12) ac_at_f94 ac_at_f98
    (by decide) (by decide) (by decide) E6.memcmp (by rsimp; rw [R.r19, e0, t0]) (by rsimp <;> rfl)
    (by rsimp <;> rfl) (by decide) fun m7 hiff hm7 => ?_
  have hq12 : memBytes M6 q 12 = s := by rw [← hl12]; exact acetl_inBytes O (S6.doc O A) hsq
  rw [hm7]
  rw [hq12, E6.vEd25519] at hiff
  refine WP.branch ac_at_f9c (fun eb => ?_) (fun eb => ?_) <;> wn
  · have hne : s ≠ ascii!"PKIX_ED25519" := fun h => by
      rsimp at eb; rw [hiff.mpr h] at eb; exact absurd eb (by decide)
    exact acetl_skip O A I (by hr) (by rsimp; exact h26) S6 (acetl_logEntry_none hf hdet hne)
  have h0 : reg m7 a0 = 0 := by
    rsimp at eb
    have e1 : (reg m7 a0 != 0) = false := eb
    cases h : (reg m7 a0 == 0)
    · rw [bne, h] at e1; exact absurd e1 (by decide)
    · exact beq_iff_eq.mp h
  have hdk : (key.field (ascii!"keyDetails") >>= Json.asStr) = some (ascii!"PKIX_ED25519") := by
    rw [hdet, hiff.mp h0]
  exact acetl_tF9E O A I (by hr) (by rsimp; exact h26) S6 hkv h28'' h1C'' hjv
    (fun pk hp hq s' r hu hr ho w hw => acetl_logEntry_some hf hdk hp hq hu hr ho hw) (by rsimp; exact h22)
    (by rsimp; exact e1328 _ (by simp only [ev_add, acSlot]; bv_omega))

/-- One pass, from 0xEBA back to 0xEBA. -/
theorem acetl_pass (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs (j :: rest) ls) :
    WP bootMainClosure0Code AC (acetlQ X 0xEBA (acetlNx X jr fs rest)) n0.mem 0xEBA (reg n0) := by
  have hm : ∀ x, AcetlU X.B X.Bf fp0 true x → n0.mem x = n0.mem x := fun _ _ => rfl
  have R : AceHR X (reg n0) := ⟨rfl, A.inv.sp, A.inv.gp, A.inv.tp, I.r19, A.keep.regs 21 (by decide),
    A.keep.regs 25 (by decide), A.keep.regs 27 (by decide)⟩
  have F := O.lay.fr
  refine acetl_pre O R (acetl_env O A hm) (fun _ _ h1 h2 => acetl_doc O A hm h1 h2) I.cur (fun h => nomatch h) ?_
  intro j' rest' h M2 g q l Rg hg hfr hq hv hl hcur
  cases h
  have hU : ∀ x, AcetlU X.B X.Bf fp0 false x → M2 x = n0.mem x := fun x hx =>
    hfr x (acetl_UV hx) (acetl_sep F hx (a := 0x52B8) (b := 0x52BC) (by decide) (by decide) (by decide))
  have S : AcetlS X n0 fp0 M2 fp0 rest :=
    ⟨fun x hx => hU x hx.weak, hcur,
      (ace_load_eq fun i hi => hU _ (acetl_Uf O (s := 0x1FDC) (l := 4) (by decide) (by decide) hi)).trans A.fr.ptr,
      (ace_load_eq fun i hi => hU _ (acetl_Uf O (s := 0x1FE0) (l := 4) (by decide) (by decide) hi)).trans A.fr.len,
      Nat.le_refl _, A.fr.hi⟩
  exact acetl_tEF2 O A I Rg hg S hv hq hl

end

/-- **The transparency log loop**, from 0xEBA to 0x123A. -/
theorem acetl_tlog_stage : AceTlogStage := by
  intro X O n fp jr fs rest ls A I
  induction rest generalizing n fp ls with
  | nil => exact acetl_stage A.code A.st (acetl_end O A I)
  | cons j rest ih =>
    refine AcStage.seq (acetl_stage A.code A.st (acetl_pass O A I)) fun n1 _ _ h1 => ?_
    obtain ⟨fp1, ls1, A1, I1⟩ := h1
    exact ih n1 fp1 ls1 A1 I1

end C3.RV32.Ac
