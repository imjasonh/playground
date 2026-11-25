import C3BootProofs.Proofs.AcceptTargetsMet

/-!
# The `targets.json` stage from 0x836

From 0x836: keep the root's expiry at `sp + 0x28`, read `targets.json`,
parse its metadata, and go on to `act_89a`. `act_stage` proves
`AcTargetsStage`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.Json

set_option maxRecDepth 200000

section
variable {romBase : Word} {romCode : List Nat} {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8}
  {M : Word → BitVec 8} {f : Fin 32 → Word}

/-- **From 0x836**: store the root's expiry at `sp + 0x28`, read
`targets.json` into `doc`, parse its metadata, then `act_89a`. -/
theorem act_836 {flash : Nat → BitVec 8} {R : Nat} (hROM : RomRead flash R romBase romCode)
    (hR4 : R % 4 = 0) (hR : R ≤ 0x3A50 - 0x180)
    (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f)
    (hr : memLoad32 M (acSlot B 0x40) = r) {pinned : Bytes} {parts : TufParts} {root : TufRoot} {re : Nat}
    {x21 x25 x27 : Word} {Mi : Word → BitVec 8} {tt : Nat} {es : List (Bytes × Option TufKey)}
    (hO : ∀ x, ActOut B Bf x → M x = Mi x)
    (hroot : actRoot pinned parts = some root) (hre : expires root.md = some re)
    (h1318 : memLoad32 M (acSlot B 0x1318) = BitVec.ofNat 32 re)
    (h131C : memLoad32 M (acSlot B 0x131C) = BitVec.ofNat 32 (re / 2 ^ 32))
    (hrk : roleKeys root.md.signed (ascii!"targets") = some (tt, es))
    (hRk : RkAt M (acSlot B 0xDD0) tt (es.map C3.Json.rkTag)) (hw : RkWf (es.map C3.Json.rkTag))
    (hB : RkBytes es)
    (hdT : ActDoc flash M (acSlot B 0x244) (f 24) (memLoad32 M (acSlot B 0x1C)).toNat parts.targets)
    (hdoc : ActDoc flash M (acSlot B 0x244) (f 24) ((memLoad32 M (acSlot B 0x1C)).toNat + 1) parts.trustedRoot)
    (hs4 : f 20 = Bf + 0x4000) (hs5 : f 21 = x21) (hs9 : f 25 = x25) (hs11 : f 27 = x27) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 (AcTargetsPost pinned parts root re B Bf x21 x25 x27 Mi))
      M 0x836 f := by
  have F := X.F
  have hbh := X.bhi
  have hbl : acBufLen = 0xB954 := rfl
  refine WP.zero fun hz => ?_
  have e1310 : 4096 + 784 + f sp = acSlot B 0x1310 := by rw [BitVec.add_comm]; exact act_spc hI.rsp _ _ rfl
  have e8 : acSlot B 0x1310 + 8 = acSlot B 0x1318 := add_ofNat_assoc B _ _
  have eC : acSlot B 0x1310 + 0xC = acSlot B 0x131C := add_ofNat_assoc B _ _
  refine WP.lui ac_at_836 ?_; wn
  refine WP.aluImm ac_at_838 ?_; wn
  refine WP.alu ac_at_83c ?_; wn
  refine WP.lw ac_at_83e (by act_r; rw [e1310, e8]; exact X.al (by decide) (by decide)) ?_; wn
  have e1310' : aluEval AluOp.add (aluEval AluOp.add 4096 784) (f sp) = acSlot B 0x1310 := e1310
  rw [e1310', e8, h1318]
  have e28 : f sp + 0x28 = B + BitVec.ofNat 32 0x3A78 := act_spc hI.rsp _ _ rfl
  have e2C : f sp + 0x2C = B + BitVec.ofNat 32 0x3A7C := act_spc hI.rsp _ _ rfl
  refine WP.sw ac_at_840 (by act_r; rw [e28]; exact X.al (by decide) (by decide))
    (by act_r; rw [e28]; exact X.sc (by decide) (by decide) (by decide)) ?_; wn
  refine WP.lw ac_at_842 (by act_r; rw [eC]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.sw ac_at_844 (by act_r; rw [e2C]; exact X.al (by decide) (by decide))
    (by act_r; rw [e2C]; exact X.sc (by decide) (by decide) (by decide)) ?_; wn
  rw [e28, e2C, eC, memLoad32_store32_sep (X.ss (by decide) (by decide) (Or.inl (by decide))), h131C]
  have K1 := (act_kp_sw (B := B) (M := M) (w := BitVec.ofNat 32 re) (c0 := 0x3A78) (n0 := 8) (d := 0x3A78)
    (by decide) (by decide)).trans (act_kp_sw (w := BitVec.ofNat 32 (re / 2 ^ 32)) (d := 0x3A7C)
    (by decide) (by decide))
  have h28 : memLoad32 (memStore32 (memStore32 M (B + BitVec.ofNat 32 0x3A78) (BitVec.ofNat 32 re))
      (B + BitVec.ofNat 32 0x3A7C) (BitVec.ofNat 32 (re / 2 ^ 32))) (acSlot B 0x28) = BitVec.ofNat 32 re := by
    rw [memLoad32_store32_sep (X.ss (by decide) (by decide) (Or.inr (by decide)))]
    exact memLoad32_store32_same _ _ _
  have h2C : memLoad32 (memStore32 (memStore32 M (B + BitVec.ofNat 32 0x3A78) (BitVec.ofNat 32 re))
      (B + BitVec.ofNat 32 0x3A7C) (BitVec.ofNat 32 (re / 2 ^ 32))) (acSlot B 0x2C) =
      BitVec.ofNat 32 (re / 2 ^ 32) := memLoad32_store32_same _ _ _
  generalize memStore32 (memStore32 M (B + BitVec.ofNat 32 0x3A78) (BitVec.ofNat 32 re))
      (B + BitVec.ofNat 32 0x3A7C) (BitVec.ofNat 32 (re / 2 ^ 32)) = M1 at K1 h28 h2C ⊢
  have o1 : ∀ x, ActOut B Bf x → Sep x 1 (B + BitVec.ofNat 32 0x3A78) 8 := fun x hx => by
    have := hx.2.2.1.subR (c := 8) (l := 8) (by decide)
    rwa [show acSlot B 0x20 + BitVec.ofNat 32 8 = B + BitVec.ofNat 32 0x3A78 from add_ofNat_assoc B _ _] at this
  have hI1 := hI.mem F X.sB (K1.out o1)
  have kO1 : ∀ x, ActOut B Bf x → M1 x = Mi x := fun x hx => (K1.out o1 x hx).trans (hO x hx)
  have l1C : memLoad32 M1 (acSlot B 0x1C) = memLoad32 M (acSlot B 0x1C) :=
    K1.ld X (c := 0x3A6C) (by decide) (by decide) (by decide) (Or.inl (by decide))
  have hr1 : memLoad32 M1 (acSlot B 0x40) = r :=
    (K1.ld X (c := 0x3A90) (by decide) (by decide) (by decide) (Or.inr (by decide))).trans hr
  have hdT1 : ActDoc flash M1 (acSlot B 0x244) (f 24) (memLoad32 M1 (acSlot B 0x1C)).toNat parts.targets := by
    rw [l1C]; exact K1.doc X (by decide) (Or.inr (by decide)) hdT
  have hdoc1 : ActDoc flash M1 (acSlot B 0x244) (f 24) ((memLoad32 M1 (acSlot B 0x1C)).toNat + 1)
      parts.trustedRoot := by
    rw [l1C]; exact K1.doc X (by decide) (Or.inr (by decide)) hdoc
  have hRk1 : RkAt M1 (B + BitVec.ofNat 32 0x4820) tt (es.map C3.Json.rkTag) := hRk.congr fun o ho => by
    rw [add_ofNat_assoc]
    exact K1.at X (by decide) (by omega) (by omega) (Or.inr (by omega))
  clear hI hr hO hdT hdoc hRk l1C
  refine WP.aluImm ac_at_846 ?_; wn
  refine WP.aluImm ac_at_848 ?_; wn
  refine WP.alu ac_at_84a ?_; wn
  refine WP.alu ac_at_84c ?_; wn
  have e1C : f sp + 0x1C = acSlot B 0x1C := act_spc hI1.rsp _ _ rfl
  refine WP.lw ac_at_84e (by act_r; rw [e1C]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.alu ac_at_850 ?_; wn
  refine act_rd (c := 0x3DA0) (start := f 24) (plen := f 23) (iw := memLoad32 M1 (acSlot B 0x1C)) hROM hR4 hR X
    (hI1.regs (by act_r) (by act_r) (by act_r)) ac_at_852 ac_at_856 (by decide) (by decide)
    (by act_r; exact act_spc hI1.rsp _ _ rfl) (by act_r) (by act_r)
    (by act_r; exact act_spc hI1.rsp _ _ rfl) (by act_r; rw [e1C]) (by act_r; exact hs4) (by decide)
    fun m2 hout hfr => ?_
  have hc0 : 0x3DA0 + 8 ≤ 0x5A70 := by decide
  have kO2 := act_rd_out hfr act_out_350
  have hI2 := hI1.mem F X.sB kO2
  have hr2 : memLoad32 m2.mem (acSlot B 0x40) = r :=
    (act_rd_ld X hfr hc0 (c := 0x3A90) (by decide) (by decide) (by decide)).trans hr1
  have h28' : memLoad32 m2.mem (acSlot B 0x28) = BitVec.ofNat 32 re :=
    (act_rd_ld X hfr hc0 (c := 0x3A78) (by decide) (by decide) (by decide)).trans h28
  have h2C' : memLoad32 m2.mem (acSlot B 0x2C) = BitVec.ofNat 32 (re / 2 ^ 32) :=
    (act_rd_ld X hfr hc0 (c := 0x3A7C) (by decide) (by decide) (by decide)).trans h2C
  have l1C : memLoad32 m2.mem (acSlot B 0x1C) = memLoad32 M1 (acSlot B 0x1C) :=
    act_rd_ld X hfr hc0 (c := 0x3A6C) (by decide) (by decide) (by decide)
  have tid2 : ∀ i, tufIndexDocSpec m2.mem (acSlot B 0x244) i = tufIndexDocSpec M1 (acSlot B 0x244) i :=
    act_tid_congr fun j hj => by
      rw [add_ofNat_assoc]; exact act_rd_at X hfr hc0 (by omega) (by omega) (by omega)
  have hdoc2 : ActDoc flash m2.mem (acSlot B 0x244) (f 24) ((memLoad32 m2.mem (acSlot B 0x1C)).toNat + 1)
      parts.trustedRoot := fun o l e => hdoc1 o l (by rw [← tid2, ← l1C]; exact e)
  have hRk2 : RkAt m2.mem (B + BitVec.ofNat 32 0x4820) tt (es.map C3.Json.rkTag) := hRk1.congr fun o ho => by
    rw [add_ofNat_assoc]
    exact act_rd_at X hfr hc0 (by omega) (by omega) (Or.inr (by omega))
  have hres := act_trd_res hout (fun o l h => hdT1 o l h) (fun e h => act_tid_err h)
  have e4 : B + BitVec.ofNat 32 0x3DA0 + 4 = acSlot B 0x354 := add_ofNat_assoc B _ _
  rw [e4] at hres
  clear hI1 hr1 h28 h2C hdoc1 hRk1 hdT1 tid2
  wn
  have e350 : f sp + 0x350 = B + BitVec.ofNat 32 0x3DA0 := act_spc hI2.rsp _ _ rfl
  refine WP.lw ac_at_85a (by act_r; rw [e350]; exact X.al (by decide) (by decide)) ?_; wn
  rcases hres with ⟨h0, he⟩ | ⟨h0, hL, hL2, hdm⟩
  · refine WP.branch ac_at_85e (fun hb => ?_) (fun _ => ?_)
    · exfalso; revert hb; act_r; rw [e350, h0]; decide
    refine WP.jal ac_at_860 (by decide) ?_; wn
    exact act_x66 (hI2.regs (by act_r) (by act_r) (by act_r)) hr2 he
  refine WP.branch ac_at_85e (fun _ => ?_) (fun hb => ?_)
  rotate_left
  · exfalso; revert hb; act_r; rw [e350, h0]; intro hb
    simp only [branchTaken, bne_eq_false_iff_eq] at hb
    have := congrArg BitVec.toNat hb
    rw [BitVec.toNat_add, show (16384 : Word).toNat = 16384 from rfl, show (0 : Word).toNat = 0 from rfl,
      Nat.mod_eq_of_lt (by omega)] at this
    omega
  wn
  have hbt : (Bf + 0x4000).toNat = Bf.toNat + 0x4000 := by
    rw [BitVec.toNat_add, show (0x4000 : Word).toNat = 0x4000 from rfl, Nat.mod_eq_of_lt (by omega)]
  have e354 : f sp + 0x354 = acSlot B 0x354 := act_spc hI2.rsp _ _ rfl
  refine WP.lw ac_at_864 (by act_r; rw [e354]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_868 ?_; wn
  refine WP.aluImm ac_at_86c ?_; wn
  refine WP.lui ac_at_870 ?_; wn
  refine WP.aluImm ac_at_872 ?_; wn
  refine WP.alu ac_at_876 ?_; wn
  refine WP.aluImm ac_at_878 ?_; wn
  refine act_pm (c := 0x52C0) (p := Bf + 0x4000) (n := parts.targets.length)
    (kq := BitVec.ofNat 32 acTargetsKeysAddress + BitVec.ofNat 32 0) (kl := 7) X
    (hI2.regs (by act_r) (by act_r) (by act_r)) ac_at_87a ac_at_87e (by decide) (by decide)
    (by act_r; rw [BitVec.add_comm]; exact act_spc hI2.rsp _ _ rfl) (by act_r; rw [e350, h0])
    (by act_r; rw [e354, hL]) (by act_r <;> decide) (by act_r <;> decide) (by decide) (by omega) (by decide)
    (by omega) (by omega) (X.sfb (by decide) (by omega) (by omega)) (X.key (by decide) (by decide))
    fun m3 hpm => ?_
  rw [act_keyB (X.E hI2) (by decide), hdm, show (acTargetsKeysData.drop 0).take 7 = ascii!"targets" from by decide]
    at hpm
  have hpf : ∀ x, Sep x 1 (B + BitVec.ofNat 32 0x383C) 532 → Sep x 1 (B + BitVec.ofNat 32 0x52C0) 16 →
      m3.mem x = m2.mem x := by
    revert hpm; generalize pmRes _ _ = q; rcases q with _ | ⟨_, _, _, _⟩ <;> exact fun h => h.1
  have P3 : ∀ c, 0x3A50 ≤ c → c < 0x5A70 → c < 0x52C0 ∨ 0x52D0 ≤ c →
      m3.mem (B + BitVec.ofNat 32 c) = m2.mem (B + BitVec.ofNat 32 c) := fun c h1 h2 h3 =>
    hpf _ (X.ss (by omega) (by decide) (Or.inr (by omega))) (X.ss (by omega) (by decide) (by omega))
  have L3 : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x5A70 → c + 4 ≤ 0x52C0 ∨ 0x52D0 ≤ c →
      memLoad32 m3.mem (B + BitVec.ofNat 32 c) = memLoad32 m2.mem (B + BitVec.ofNat 32 c) := fun c h1 h2 h3 =>
    memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact P3 _ (by omega) (by omega) (by omega)
  have bf3 : ∀ (p : Word) (n : Nat), Bf.toNat ≤ p.toNat → p.toNat + n ≤ Bf.toNat + acBufLen →
      memBytes m3.mem p n = memBytes m2.mem p n := fun p n h1 h2 => memBytes_congr fun j hj =>
    hpf _ ((X.sfb (by decide) h1 h2).symm.sub (c := j) (l := 1) (by omega))
      ((X.sfb (by decide) h1 h2).symm.sub (c := j) (l := 1) (by omega))
  have kO3 : ∀ x, ActOut B Bf x → m3.mem x = m2.mem x := fun x hx =>
    hpf x (hx.1.subR (c := 0x383C) (l := 532) (by decide)) (act_ks hx.2.2.2.2.1 0x10 16 (by decide))
  have hI3 := hI2.mem F X.sB kO3
  have hr3 : memLoad32 m3.mem (acSlot B 0x40) = r := (L3 0x3A90 (by decide) (by decide) (by decide)).trans hr2
  have h28 : memLoad32 m3.mem (acSlot B 0x28) = BitVec.ofNat 32 re :=
    (L3 0x3A78 (by decide) (by decide) (by decide)).trans h28'
  have h2C : memLoad32 m3.mem (acSlot B 0x2C) = BitVec.ofNat 32 (re / 2 ^ 32) :=
    (L3 0x3A7C (by decide) (by decide) (by decide)).trans h2C'
  have l1C3 : memLoad32 m3.mem (acSlot B 0x1C) = memLoad32 m2.mem (acSlot B 0x1C) :=
    L3 0x3A6C (by decide) (by decide) (by decide)
  have tid3 : ∀ i, tufIndexDocSpec m3.mem (acSlot B 0x244) i = tufIndexDocSpec m2.mem (acSlot B 0x244) i :=
    act_tid_congr fun j hj => by
      rw [add_ofNat_assoc]; exact P3 _ (by omega) (by omega) (by omega)
  have hdoc3 : ActDoc flash m3.mem (acSlot B 0x244) (f 24) ((memLoad32 m3.mem (acSlot B 0x1C)).toNat + 1)
      parts.trustedRoot := fun o l e => hdoc2 o l (by rw [← tid3, ← l1C3]; exact e)
  have hRk3 : RkAt m3.mem (B + BitVec.ofNat 32 0x4820) tt (es.map C3.Json.rkTag) := hRk2.congr fun o ho => by
    rw [add_ofNat_assoc]; exact P3 _ (by omega) (by omega) (by omega)
  clear hI2 hr2 h28' h2C' l1C tid3 hdoc2 hRk2
  wn
  refine WP.lui ac_at_882 ?_; wn
  refine WP.aluImm ac_at_884 ?_; wn
  refine WP.alu ac_at_888 ?_; wn
  have e1310 : 4096 + 784 + f sp = acSlot B 0x1310 := by rw [BitVec.add_comm]; exact act_spc hI3.rsp _ _ rfl
  have e560 : acSlot B 0x1310 + 0x560 = B + BitVec.ofNat 32 0x52C0 := add_ofNat_assoc B _ _
  have e564 : acSlot B 0x1310 + 0x564 = B + BitVec.ofNat 32 0x52C4 := add_ofNat_assoc B _ _
  refine WP.lw ac_at_88a (by act_r; rw [e1310, e560]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.lbu ac_at_88e ?_; wn
  have e1310' : aluEval AluOp.add (aluEval AluOp.add 4096 784) (f sp) = acSlot B 0x1310 := e1310
  rw [e1310', e560, e564]
  rcases hp : pmModel parts.targets (ascii!"targets") with e | ⟨gp, gl, sq, sl⟩
  · rw [hp] at hpm
    obtain ⟨_, hq, he⟩ := hpm
    have ee := act_eb_pmModel _ _ e hp
    rw [show B + BitVec.ofNat 32 0x52C0 + 4 = B + BitVec.ofNat 32 0x52C4 from add_ofNat_assoc B _ _] at he
    rw [hq, he]
    refine WP.branch ac_at_892 (fun hb => ?_) (fun _ => ?_)
    · exfalso; revert hb; act_r
    refine WP.jal ac_at_896 (by decide) ?_; wn
    refine act_x6a (hI3.regs (by act_r) (by act_r) (by act_r)) hr3 ?_
    act_r
    rw [BitVec.toNat_and]
    refine Nat.lt_of_le_of_lt Nat.and_le_left ?_
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [hp] at hpm
  obtain ⟨_, hq, hq4, hq8, hqC⟩ := hpm
  dsimp only at hq hq4 hq8 hqC
  have hs := pmModel_spec parts.targets (ascii!"targets")
  rw [hp] at hs
  obtain ⟨md, sj, hmd, ⟨hb1, hv1⟩, ⟨hb2, hv2⟩, hps⟩ := hs
  have hw4 : ∀ a, a ≤ parts.targets.length → (Bf + 0x4000 + BitVec.ofNat 32 a).toNat = Bf.toNat + 0x4000 + a :=
    fun a ha => by
      rw [BitVec.toNat_add, hbt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hm1 := hw4 gp (by omega)
  have hm2 := hw4 sq (by omega)
  rw [show B + BitVec.ofNat 32 0x52C0 + 4 = B + BitVec.ofNat 32 0x52C4 from add_ofNat_assoc B _ _] at hq4
  rw [show B + BitVec.ofNat 32 0x52C0 + 8 = B + BitVec.ofNat 32 0x52C8 from add_ofNat_assoc B _ _] at hq8
  rw [show B + BitVec.ofNat 32 0x52C0 + 0xC = B + BitVec.ofNat 32 0x52CC from add_ofNat_assoc B _ _] at hqC
  have hd : memBytes m3.mem (Bf + 0x4000 + BitVec.ofNat 32 gp) gl = slice parts.targets gp gl := by
    rw [bf3 _ _ (by omega) (by omega), ← act_slice_mem hb1, hdm]
  have hsj : JVal true (memBytes m3.mem (Bf + 0x4000 + BitVec.ofNat 32 sq) sl) sj := by
    rw [bf3 _ _ (by omega) (by omega), ← act_slice_mem hb2, hdm]; exact hv2
  have hb1' : gp + gl ≤ parts.targets.length := hb1
  have hb2' : sq + sl ≤ parts.targets.length := hb2
  refine WP.branch ac_at_892 (fun _ => ?_) (fun hb => ?_)
  rotate_left
  · exfalso; revert hb; act_r; rw [hq]; intro hb
    simp only [branchTaken, bne_eq_false_iff_eq] at hb
    have := congrArg BitVec.toNat hb
    rw [hm1, show (0 : Word).toNat = 0 from rfl] at this
    omega
  wn
  refine act_89a (S := Bf + 0x4000 + BitVec.ofNat 32 gp) (SP := Bf + 0x4000 + BitVec.ofNat 32 sq) hROM hR4 hR X
    (hI3.regs (by act_r) (by act_r) (by act_r)) hr3 (fun x hx => (kO3 x hx).trans ((kO2 x hx).trans (kO1 x hx)))
    (by act_r; exact hdoc3) (by act_r; exact hs4) (by act_r; exact hq) (by act_r) hq4 hq8 hqC
    (by omega) (by omega) (by omega) (by omega) hd (CanonEncode _ _ hv1) hsj hps hrk hRk3 hw hB ?_ h28 h2C
    (by act_r; exact hs5) (by act_r; exact hs9) (by act_r; exact hs11)
  intro hth te hte p1 l1 p2 l2 p3 l3 val p4 l4 p5 l5 body h1 h2 h3 h4 h5 h6 h7 hv hbd
  rw [act_verifyTuf, hroot]
  exact act_finish hre hp (fun md' h => by rw [hmd] at h; cases h; exact hth) hte h1 h2 h3 h4 h5 h6 h7 hv hbd

end

/-- The `targets.json` stage holds. -/
theorem act_stage : AcTargetsStage := by
  intro flash R romBase romCode hROM n B Bf g t r v M0 pinned parts root re hE hC F sB sRo sRom sBR bal bhi hR4 hR
    hS hInv hPre
  obtain ⟨hroot, hre, h1318, h131C, ⟨tt, es, hrk, hRk, hw, hB⟩, hdT, hdoc, hs4, hr⟩ := hPre
  have X : ActX romBase romCode B Bf M0 := ⟨F, sB, sRo, sRom, sBR, bal, bhi, hE⟩
  have hI : ActI B Bf g t v M0 n.mem (reg n) := ⟨hInv.sp, hInv.gp, hInv.tp, hInv.saves, hInv.out⟩
  obtain ⟨n', hst, hq⟩ := act_836 hROM hR4 hR X hI hr (Mi := n.mem) (fun _ _ => rfl) hroot hre h1318 h131C
    hrk hRk hw hB hdT hdoc hs4 rfl rfl rfl (by decide) hC n hS
  exact ⟨n', hst, hq n' rfl rfl rfl⟩

end C3.RV32.Ac
