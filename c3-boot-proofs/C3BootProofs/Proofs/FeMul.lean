import C3BootProofs.Proofs.FeMulBody
import C3BootProofs.Proofs.FeReduce

/-!
# `<&FieldElement2625 as Mul>::mul`

`curve25519_dalek`'s field multiplication, as compiled: it saves `ra` and
`s0` through `s11`, runs the body that `FeMulBody.lean` proves (the ten `u64`
sums into its frame), calls `reduce` on them with the result pointer it saved,
restores the registers, and returns.
-/

namespace C3.RV32

open C3.Image

/-- Where `mul` runs: its code at an even `P` and `reduce`'s at `P + 0xAF0`,
the 0x140 bytes of stack below `sp0` that it and `reduce` use, the result at
`out`, and the operands at `xp` and `yp`, aligned and apart where they must
be. -/
structure FeMEnv (M : Word → BitVec 8) (P sp0 out xp yp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P feMulCode
  red : CodeIn M (P + 0xAF0) feReduceCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x140 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hx : xp.toNat % 4 = 0
  hy : yp.toNat % 4 = 0
  sGC : Sep (sp0 + 0xFFFFFEC0) 0x140 P feMulCode.length
  sGR : Sep (sp0 + 0xFFFFFEC0) 0x140 (P + 0xAF0) feReduceCode.length
  sOC : Sep out 40 P feMulCode.length
  sOR : Sep out 40 (P + 0xAF0) feReduceCode.length
  sOG : Sep out 40 (sp0 + 0xFFFFFEC0) 0x140
  sXG : Sep xp 40 (sp0 + 0xFFFFFEC0) 0x140
  sYG : Sep yp 40 (sp0 + 0xFFFFFEC0) 0x140

/-- The registers `mul` leaves as they were. -/
def feMKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

theorem fmu_reduce_at (P : Word) : P + BitVec.ofNat 32 0x8AC + 0x0 + 0x244 = P + 0xAF0 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The compiled `<&FieldElement2625 as Mul>::mul`**, called with the result
at `out` and the operands' ten limbs at `xp` and `yp`: it stores
`feMulSpec` of the limbs, returns with `sp` and every register but `t0`
through `t6` and `a0` through `a7` as they were, and changes no memory
outside its 0x140 bytes of stack and the result. -/
theorem feMul_correct (m : Machine) {P sp0 out xp yp retAddr : Word} (env : FeMEnv m.mem P sp0 out xp yp)
    (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp) (ha2 : reg m a2 = yp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, feMKeep q = true → reg m' q = reg m q) ∧
      (wordsAt m'.mem out 10).map BitVec.toNat =
        feMulSpec (limbAt m.mem xp 0) (limbAt m.mem xp 1) (limbAt m.mem xp 2) (limbAt m.mem xp 3)
          (limbAt m.mem xp 4) (limbAt m.mem xp 5) (limbAt m.mem xp 6) (limbAt m.mem xp 7) (limbAt m.mem xp 8)
          (limbAt m.mem xp 9) (limbAt m.mem yp 0) (limbAt m.mem yp 1) (limbAt m.mem yp 2) (limbAt m.mem yp 3)
          (limbAt m.mem yp 4) (limbAt m.mem yp 5) (limbAt m.mem yp 6) (limbAt m.mem yp 7) (limbAt m.mem yp 8)
          (limbAt m.mem yp 9) ∧
      ∀ x, Sep (sp0 + 0xFFFFFEC0) 0x140 x 1 → Sep out 40 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFEC0 = G := ⟨_, rfl⟩
  obtain ⟨F, hFG⟩ : ∃ F, G + 0x20 = F := ⟨_, rfl⟩
  rw [hG]
  have sGC : Sep G 0x140 P feMulCode.length := hG ▸ env.sGC
  have sGR : Sep G 0x140 (P + 0xAF0) feReduceCode.length := hG ▸ env.sGR
  have sOG : Sep out 40 G 0x140 := hG ▸ env.sOG
  have sXG : Sep xp 40 G 0x140 := hG ▸ env.sXG
  have sYG : Sep yp 40 G 0x140 := hG ▸ env.sYG
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFEC0) (by decide)
  have hF : F.toNat % 4 = 0 := by rw [← hFG]; exact fr_al' hGa (by decide)
  have hFsp : sp0 + 0xFFFFFEE0 = F := by rw [← hFG, ← hG, BitVec.add_assoc]; rfl
  have hFr : F + 0xFFFFFFE0 = G := by rw [← hFG, BitVec.add_assoc]; exact BitVec.add_zero G
  have hspF : F + 0x120 = sp0 := by
    rw [← hFG, ← hG, BitVec.add_assoc, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have fG : ∀ {c : Nat}, c + 4 ≤ 0x120 → F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x20 + c) := fun _ => by
    rw [← hFG, BitVec.add_assoc, show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, ofNat_add_ofNat]
  have sFC : Sep F 0x120 P feMulCode.length := by
    have := sGC.sub (c := 0x20) (l := 0x120) (by decide); rwa [show G + BitVec.ofNat 32 0x20 = F from hFG] at this
  have sXF : Sep xp 40 F 0x120 := by
    have := sXG.subR (c := 0x20) (l := 0x120) (by decide); rwa [show G + BitVec.ofNat 32 0x20 = F from hFG] at this
  have sYF : Sep yp 40 F 0x120 := by
    have := sYG.subR (c := 0x20) (l := 0x120) (by decide); rwa [show G + BitVec.ofNat 32 0x20 = F from hFG] at this
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code fmu_at_0 (off' := 2) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.aluImm env.code fmu_at_2 (off' := 4) (by decide)
  have r2sp : reg m2 sp = F := by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [hsp, hFsp]
  have r2a3 : reg m2 a3 = F + 0x100 := by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [hsp, hFsp]
  have rk2 : ∀ r, r ≠ sp → r ≠ a3 → reg m2 r = reg m r := fun r h1 h2 => by
    rw [u2.regs]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, h1, h2]
  have cOf : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep G 0x140 b code.length → (∀ x, Sep G 0x140 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have inF : ∀ x, Sep G 0x140 x 1 → Sep F 0x120 x 1 := fun x hx => by
    have := hx.sub (c := 0x20) (l := 0x120) (by decide); rwa [show G + BitVec.ofNat 32 0x20 = F from hFG] at this
  have sepG0 : ∀ {d k : Nat}, 0x20 ≤ d → d + k ≤ 0x140 → Sep G 0x20 (G + BitVec.ofNat 32 d) k := fun {d k} h1 h2 => by
    have := sep_offsets G (c := 0) (n := 0x20) (d := d) (k := k) (.inl h1) (by decide) (by omega)
    rwa [add_ofNat_zero] at this
  obtain ⟨p0, dp0, up0⟩ := u2.self.swG env.code fmu_at_4 (off' := 0x8) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hF (by decide)) (a := F + 0x11C) (v := reg m ra)
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P0, hP0⟩ : ∃ M', memStore32 m.mem (F + 0x11C) (reg m ra) = M' := ⟨_, rfl⟩
  rw [hP0] at up0
  have hcp0 : CodeIn P0 P feMulCode := by rw [← hP0]; exact env.code.store32 (frm_sep' sFC (by decide))
  obtain ⟨p1, dp1, up1⟩ := up0.swG hcp0 fmu_at_8 (off' := 0xA) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hF (by decide)) (a := F + 0x118) (v := reg m (8 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P1, hP1⟩ : ∃ M', memStore32 P0 (F + 0x118) (reg m (8 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP1] at up1
  have hcp1 : CodeIn P1 P feMulCode := by rw [← hP1]; exact hcp0.store32 (frm_sep' sFC (by decide))
  obtain ⟨p2, dp2, up2⟩ := up1.swG hcp1 fmu_at_a (off' := 0xC) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hF (by decide)) (a := F + 0x114) (v := reg m (9 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P2, hP2⟩ : ∃ M', memStore32 P1 (F + 0x114) (reg m (9 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP2] at up2
  have hcp2 : CodeIn P2 P feMulCode := by rw [← hP2]; exact hcp1.store32 (frm_sep' sFC (by decide))
  obtain ⟨p3, dp3, up3⟩ := up2.swG hcp2 fmu_at_c (off' := 0x10) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hF (by decide)) (a := F + 0x110) (v := reg m (18 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P3, hP3⟩ : ∃ M', memStore32 P2 (F + 0x110) (reg m (18 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP3] at up3
  have hcp3 : CodeIn P3 P feMulCode := by rw [← hP3]; exact hcp2.store32 (frm_sep' sFC (by decide))
  obtain ⟨p4, dp4, up4⟩ := up3.swG hcp3 fmu_at_10 (off' := 0x14) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hF (by decide)) (a := F + 0x10C) (v := reg m (19 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P4, hP4⟩ : ∃ M', memStore32 P3 (F + 0x10C) (reg m (19 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP4] at up4
  have hcp4 : CodeIn P4 P feMulCode := by rw [← hP4]; exact hcp3.store32 (frm_sep' sFC (by decide))
  obtain ⟨p5, dp5, up5⟩ := up4.swG hcp4 fmu_at_14 (off' := 0x18) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hF (by decide)) (a := F + 0x108) (v := reg m (20 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P5, hP5⟩ : ∃ M', memStore32 P4 (F + 0x108) (reg m (20 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP5] at up5
  have hcp5 : CodeIn P5 P feMulCode := by rw [← hP5]; exact hcp4.store32 (frm_sep' sFC (by decide))
  obtain ⟨p6, dp6, up6⟩ := up5.swG hcp5 fmu_at_18 (off' := 0x1C) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hF (by decide)) (a := F + 0x104) (v := reg m (21 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P6, hP6⟩ : ∃ M', memStore32 P5 (F + 0x104) (reg m (21 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP6] at up6
  have hcp6 : CodeIn P6 P feMulCode := by rw [← hP6]; exact hcp5.store32 (frm_sep' sFC (by decide))
  obtain ⟨p7, dp7, up7⟩ := up6.swG hcp6 fmu_at_1c (off' := 0x20) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hF (by decide)) (a := F + 0x100) (v := reg m (22 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P7, hP7⟩ : ∃ M', memStore32 P6 (F + 0x100) (reg m (22 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP7] at up7
  have hcp7 : CodeIn P7 P feMulCode := by rw [← hP7]; exact hcp6.store32 (frm_sep' sFC (by decide))
  obtain ⟨p8, dp8, up8⟩ := up7.swG hcp7 fmu_at_20 (off' := 0x22) (by decide)
    (by rw [r2sp]; exact fr_al' hF (by decide)) (a := F + 0xFC) (v := reg m (23 : Fin 32))
    (by rw [r2sp]) (rk2 _ (by decide) (by decide))
  obtain ⟨P8, hP8⟩ : ∃ M', memStore32 P7 (F + 0xFC) (reg m (23 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP8] at up8
  have hcp8 : CodeIn P8 P feMulCode := by rw [← hP8]; exact hcp7.store32 (frm_sep' sFC (by decide))
  obtain ⟨p9, dp9, up9⟩ := up8.swG hcp8 fmu_at_22 (off' := 0x24) (by decide)
    (by rw [r2sp]; exact fr_al' hF (by decide)) (a := F + 0xF8) (v := reg m (24 : Fin 32))
    (by rw [r2sp]) (rk2 _ (by decide) (by decide))
  obtain ⟨P9, hP9⟩ : ∃ M', memStore32 P8 (F + 0xF8) (reg m (24 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP9] at up9
  have hcp9 : CodeIn P9 P feMulCode := by rw [← hP9]; exact hcp8.store32 (frm_sep' sFC (by decide))
  obtain ⟨p10, dp10, up10⟩ := up9.swG hcp9 fmu_at_24 (off' := 0x26) (by decide)
    (by rw [r2sp]; exact fr_al' hF (by decide)) (a := F + 0xF4) (v := reg m (25 : Fin 32))
    (by rw [r2sp]) (rk2 _ (by decide) (by decide))
  obtain ⟨P10, hP10⟩ : ∃ M', memStore32 P9 (F + 0xF4) (reg m (25 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP10] at up10
  have hcp10 : CodeIn P10 P feMulCode := by rw [← hP10]; exact hcp9.store32 (frm_sep' sFC (by decide))
  obtain ⟨p11, dp11, up11⟩ := up10.swG hcp10 fmu_at_26 (off' := 0x28) (by decide)
    (by rw [r2sp]; exact fr_al' hF (by decide)) (a := F + 0xF0) (v := reg m (26 : Fin 32))
    (by rw [r2sp]) (rk2 _ (by decide) (by decide))
  obtain ⟨P11, hP11⟩ : ∃ M', memStore32 P10 (F + 0xF0) (reg m (26 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP11] at up11
  have hcp11 : CodeIn P11 P feMulCode := by rw [← hP11]; exact hcp10.store32 (frm_sep' sFC (by decide))
  obtain ⟨p12, dp12, up12⟩ := up11.swG hcp11 fmu_at_28 (off' := 0x2A) (by decide)
    (by rw [r2sp]; exact fr_al' hF (by decide)) (a := F + 0xEC) (v := reg m (27 : Fin 32))
    (by rw [r2sp]) (rk2 _ (by decide) (by decide))
  obtain ⟨P12, hP12⟩ : ∃ M', memStore32 P11 (F + 0xEC) (reg m (27 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP12] at up12
  have hcp12 : CodeIn P12 P feMulCode := by rw [← hP12]; exact hcp11.store32 (frm_sep' sFC (by decide))
  obtain ⟨p13, dp13, up13⟩ := up12.swG hcp12 fmu_at_2a (off' := 0x2C) (by decide)
    (by rw [r2sp]; exact fr_al' hF (by decide)) (a := F + 0x58) (v := reg m a0)
    (by rw [r2sp]) (rk2 _ (by decide) (by decide))
  obtain ⟨P13, hP13⟩ : ∃ M', memStore32 P12 (F + 0x58) (reg m a0) = M' := ⟨_, rfl⟩
  rw [hP13] at up13
  have hcp13 : CodeIn P13 P feMulCode := by rw [← hP13]; exact hcp12.store32 (frm_sep' sFC (by decide))
  have fpro : ∀ x, Sep F 0x120 x 1 → P13 x = m.mem x := fun x hx => by
    rw [← hP13, memStore32_get_sep (frm_sep' hx (by decide)), ← hP12, memStore32_get_sep (frm_sep' hx (by decide)), ← hP11, memStore32_get_sep (frm_sep' hx (by decide)), ← hP10, memStore32_get_sep (frm_sep' hx (by decide)), ← hP9, memStore32_get_sep (frm_sep' hx (by decide)), ← hP8, memStore32_get_sep (frm_sep' hx (by decide)), ← hP7, memStore32_get_sep (frm_sep' hx (by decide)), ← hP6, memStore32_get_sep (frm_sep' hx (by decide)), ← hP5, memStore32_get_sep (frm_sep' hx (by decide)), ← hP4, memStore32_get_sep (frm_sep' hx (by decide)), ← hP3, memStore32_get_sep (frm_sep' hx (by decide)), ← hP2, memStore32_get_sep (frm_sep' hx (by decide)), ← hP1, memStore32_get_sep (frm_sep' hx (by decide)), ← hP0, memStore32_get_sep (frm_sep' hx (by decide))]
  have sv11C : memLoad32 P13 (F + 0x11C) = reg m ra := by rw [← hP13, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x11C) 4 from sep_offsets F (c := 88) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hP12, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x11C) 4 from sep_offsets F (c := 236) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hP11, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x11C) 4 from sep_offsets F (c := 240) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0xF4) 4 (F + 0x11C) 4 from sep_offsets F (c := 244) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x11C) 4 from sep_offsets F (c := 248) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x11C) 4 from sep_offsets F (c := 252) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x11C) 4 from sep_offsets F (c := 256) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hP6, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x11C) 4 from sep_offsets F (c := 260) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x11C) 4 from sep_offsets F (c := 264) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x11C) 4 from sep_offsets F (c := 268) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hP3, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x11C) 4 from sep_offsets F (c := 272) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hP2, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x11C) 4 from sep_offsets F (c := 276) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hP1, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x11C) 4 from sep_offsets F (c := 280) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hP0, memLoad32_store32_same]
  have sv118 : memLoad32 P13 (F + 0x118) = reg m (8 : Fin 32) := by rw [← hP13, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x118) 4 from sep_offsets F (c := 88) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hP12, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x118) 4 from sep_offsets F (c := 236) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hP11, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x118) 4 from sep_offsets F (c := 240) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0xF4) 4 (F + 0x118) 4 from sep_offsets F (c := 244) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x118) 4 from sep_offsets F (c := 248) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x118) 4 from sep_offsets F (c := 252) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x118) 4 from sep_offsets F (c := 256) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hP6, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x118) 4 from sep_offsets F (c := 260) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x118) 4 from sep_offsets F (c := 264) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x118) 4 from sep_offsets F (c := 268) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hP3, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x118) 4 from sep_offsets F (c := 272) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hP2, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x118) 4 from sep_offsets F (c := 276) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hP1, memLoad32_store32_same]
  have sv114 : memLoad32 P13 (F + 0x114) = reg m (9 : Fin 32) := by rw [← hP13, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x114) 4 from sep_offsets F (c := 88) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hP12, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x114) 4 from sep_offsets F (c := 236) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hP11, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x114) 4 from sep_offsets F (c := 240) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0xF4) 4 (F + 0x114) 4 from sep_offsets F (c := 244) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x114) 4 from sep_offsets F (c := 248) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x114) 4 from sep_offsets F (c := 252) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x114) 4 from sep_offsets F (c := 256) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hP6, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x114) 4 from sep_offsets F (c := 260) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x114) 4 from sep_offsets F (c := 264) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x114) 4 from sep_offsets F (c := 268) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hP3, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x114) 4 from sep_offsets F (c := 272) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hP2, memLoad32_store32_same]
  have sv110 : memLoad32 P13 (F + 0x110) = reg m (18 : Fin 32) := by rw [← hP13, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x110) 4 from sep_offsets F (c := 88) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hP12, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x110) 4 from sep_offsets F (c := 236) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hP11, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x110) 4 from sep_offsets F (c := 240) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0xF4) 4 (F + 0x110) 4 from sep_offsets F (c := 244) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x110) 4 from sep_offsets F (c := 248) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x110) 4 from sep_offsets F (c := 252) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x110) 4 from sep_offsets F (c := 256) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hP6, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x110) 4 from sep_offsets F (c := 260) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x110) 4 from sep_offsets F (c := 264) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x110) 4 from sep_offsets F (c := 268) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hP3, memLoad32_store32_same]
  have sv10C : memLoad32 P13 (F + 0x10C) = reg m (19 : Fin 32) := by rw [← hP13, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x10C) 4 from sep_offsets F (c := 88) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hP12, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x10C) 4 from sep_offsets F (c := 236) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hP11, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x10C) 4 from sep_offsets F (c := 240) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0xF4) 4 (F + 0x10C) 4 from sep_offsets F (c := 244) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x10C) 4 from sep_offsets F (c := 248) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x10C) 4 from sep_offsets F (c := 252) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x10C) 4 from sep_offsets F (c := 256) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hP6, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x10C) 4 from sep_offsets F (c := 260) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x10C) 4 from sep_offsets F (c := 264) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_same]
  have sv108 : memLoad32 P13 (F + 0x108) = reg m (20 : Fin 32) := by rw [← hP13, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x108) 4 from sep_offsets F (c := 88) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hP12, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x108) 4 from sep_offsets F (c := 236) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hP11, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x108) 4 from sep_offsets F (c := 240) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0xF4) 4 (F + 0x108) 4 from sep_offsets F (c := 244) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x108) 4 from sep_offsets F (c := 248) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x108) 4 from sep_offsets F (c := 252) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x108) 4 from sep_offsets F (c := 256) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hP6, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x108) 4 from sep_offsets F (c := 260) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_same]
  have sv104 : memLoad32 P13 (F + 0x104) = reg m (21 : Fin 32) := by rw [← hP13, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x104) 4 from sep_offsets F (c := 88) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hP12, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x104) 4 from sep_offsets F (c := 236) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hP11, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x104) 4 from sep_offsets F (c := 240) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0xF4) 4 (F + 0x104) 4 from sep_offsets F (c := 244) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x104) 4 from sep_offsets F (c := 248) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x104) 4 from sep_offsets F (c := 252) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x104) 4 from sep_offsets F (c := 256) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hP6, memLoad32_store32_same]
  have sv100 : memLoad32 P13 (F + 0x100) = reg m (22 : Fin 32) := by rw [← hP13, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x100) 4 from sep_offsets F (c := 88) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hP12, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x100) 4 from sep_offsets F (c := 236) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hP11, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x100) 4 from sep_offsets F (c := 240) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0xF4) 4 (F + 0x100) 4 from sep_offsets F (c := 244) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x100) 4 from sep_offsets F (c := 248) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x100) 4 from sep_offsets F (c := 252) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_same]
  have svFC : memLoad32 P13 (F + 0xFC) = reg m (23 : Fin 32) := by rw [← hP13, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0xFC) 4 from sep_offsets F (c := 88) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hP12, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0xFC) 4 from sep_offsets F (c := 236) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hP11, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xFC) 4 from sep_offsets F (c := 240) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0xF4) 4 (F + 0xFC) 4 from sep_offsets F (c := 244) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0xFC) 4 from sep_offsets F (c := 248) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_same]
  have svF8 : memLoad32 P13 (F + 0xF8) = reg m (24 : Fin 32) := by rw [← hP13, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0xF8) 4 from sep_offsets F (c := 88) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hP12, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0xF8) 4 from sep_offsets F (c := 236) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hP11, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xF8) 4 from sep_offsets F (c := 240) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0xF4) 4 (F + 0xF8) 4 from sep_offsets F (c := 244) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_same]
  have svF4 : memLoad32 P13 (F + 0xF4) = reg m (25 : Fin 32) := by rw [← hP13, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0xF4) 4 from sep_offsets F (c := 88) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), ← hP12, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0xF4) 4 from sep_offsets F (c := 236) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), ← hP11, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xF4) 4 from sep_offsets F (c := 240) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_same]
  have svF0 : memLoad32 P13 (F + 0xF0) = reg m (26 : Fin 32) := by rw [← hP13, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0xF0) 4 from sep_offsets F (c := 88) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), ← hP12, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0xF0) 4 from sep_offsets F (c := 236) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), ← hP11, memLoad32_store32_same]
  have svEC : memLoad32 P13 (F + 0xEC) = reg m (27 : Fin 32) := by rw [← hP13, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0xEC) 4 from sep_offsets F (c := 88) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hP12, memLoad32_store32_same]
  have sv58 : memLoad32 P13 (F + 0x58) = reg m a0 := by rw [← hP13, memLoad32_store32_same]
  have frP : ∀ x, Sep G 0x140 x 1 → P13 x = m.mem x := fun x hx => fpro x (inF x hx)
  -- the body
  have q13sp : reg p13 sp = F := by rw [up13.regs]; exact r2sp
  have q13a1 : reg p13 a1 = xp := by rw [up13.regs, rk2 _ (by decide) (by decide), ha1]
  have q13a2 : reg p13 a2 = yp := by rw [up13.regs, rk2 _ (by decide) (by decide), ha2]
  obtain ⟨n3, M3, c3, u3, fr3, k58, kEC, kF0, kF4, kF8, kFC, k100, k104, k108, k10C, k110, k114, k118, k11C,
    hzs, sp3, gp3, tp3⟩ := fmu_body up13.self hcp13 q13sp q13a1 q13a2 hF env.hx env.hy sFC sXF sYF
  have fr3G : ∀ x, Sep G 0x140 x 1 → M3 x = m.mem x := fun x hx => by rw [fr3 x (inF x hx), frP x hx]
  have hc3 := cOf env.code sGC fr3G
  -- `a1` and `a0` for `reduce`, and the call
  obtain ⟨n4, d4, u4⟩ := u3.aluImm hc3 fmu_at_8a8 (off' := 0x8AA) (by decide)
  obtain ⟨n5, d5, u5⟩ := u4.lwE hc3 fmu_at_8aa (off' := 0x8AC) (by decide)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [sp3]; exact fr_al' hF (by decide)) (v := out)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [sp3, k58, sv58, ha0])
  obtain ⟨n6, c6, pc6, mem6, regs6⟩ := u5.callRa hc3 fmu_at_8ac fmu_at_8b0 (cb := P + 0xAF0) (fmu_reduce_at P)
    (even_at P env.hP 0xAF0 (by decide))
  have r6 := PEnv.reg1 regs6 u5.zero
  have hS20 : 0x20 ≤ F.toNat := by
    have := env.hS; rw [← hFsp, BitVec.toNat_add, show (0xFFFFFEE0 : Word).toNat = 4294967008 from rfl]; omega
  have RE : FREnv n6.mem (P + 0xAF0) F out (F + 0x98) := by
    rw [mem6]
    refine ⟨even_at P env.hP 0xAF0 (by decide), cOf env.red sGR fr3G, hF, hS20, env.hout,
      fr_al' hF (by decide), ?_, env.sOR, ?_, ?_⟩
    · rw [hFr]; have := sGR.sub (c := 0) (l := 0x20) (by decide); rwa [add_ofNat_zero] at this
    · rw [hFr]; have := sOG.subR (c := 0) (l := 0x20) (by decide); rwa [add_ofNat_zero] at this
    · rw [hFr, show F + 0x98 = G + BitVec.ofNat 32 0xB8 from fG (c := 0x98) (by decide)]
      exact (sepG0 (by decide) (by decide)).symm
  obtain ⟨n7, c7, pc7, sp7, k7, out7, fr7⟩ := feReduce_correct n6 RE pc6
    (by rw [r6 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [r6 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [sp3])
    (by rw [regs6]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0x8AC + 8) (by decide)))
    (by rw [r6 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte]; exact sp3)
  have fr7G : ∀ x, Sep G 0x140 x 1 → Sep out 40 x 1 → n7.mem x = m.mem x := fun x hx ho => by
    have h20 : Sep (F + 0xFFFFFFE0) 0x20 x 1 := by
      rw [hFr]; exact hx.sub (c := 0) (l := 0x20) (by decide) |> fun h => by rwa [add_ofNat_zero] at h
    rw [fr7 x h20 ho, mem6, fr3G x hx]
  have hcE : CodeIn n7.mem P feMulCode := fun i hi => by
    rw [fr7G _ (sGC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  -- the saved registers, read back
  have rdOf : ∀ {o : Nat} {v : Word}, 0x58 ≤ o → o + 4 ≤ 0x120 →
      memLoad32 M3 (F + BitVec.ofNat 32 o) = v → memLoad32 n7.mem (F + BitVec.ofNat 32 o) = v := fun h1 h2 hv => by
    rw [load_frame2 fr7 (by rw [hFr, fG h2]; exact sepG0 (by omega) (by omega))
      (by rw [fG h2]; exact sOG.subR (c := 0x20 + _) (l := 4) (by omega)), mem6, hv]
  have rd11C : memLoad32 n7.mem (F + 0x11C) = reg m ra :=
    rdOf (o := 0x11C) (by decide) (by decide) (by rw [show F + BitVec.ofNat 32 0x11C = F + 0x11C from rfl, k11C, sv11C])
  have rd118 : memLoad32 n7.mem (F + 0x118) = reg m (8 : Fin 32) :=
    rdOf (o := 0x118) (by decide) (by decide) (by rw [show F + BitVec.ofNat 32 0x118 = F + 0x118 from rfl, k118, sv118])
  have rd114 : memLoad32 n7.mem (F + 0x114) = reg m (9 : Fin 32) :=
    rdOf (o := 0x114) (by decide) (by decide) (by rw [show F + BitVec.ofNat 32 0x114 = F + 0x114 from rfl, k114, sv114])
  have rd110 : memLoad32 n7.mem (F + 0x110) = reg m (18 : Fin 32) :=
    rdOf (o := 0x110) (by decide) (by decide) (by rw [show F + BitVec.ofNat 32 0x110 = F + 0x110 from rfl, k110, sv110])
  have rd10C : memLoad32 n7.mem (F + 0x10C) = reg m (19 : Fin 32) :=
    rdOf (o := 0x10C) (by decide) (by decide) (by rw [show F + BitVec.ofNat 32 0x10C = F + 0x10C from rfl, k10C, sv10C])
  have rd108 : memLoad32 n7.mem (F + 0x108) = reg m (20 : Fin 32) :=
    rdOf (o := 0x108) (by decide) (by decide) (by rw [show F + BitVec.ofNat 32 0x108 = F + 0x108 from rfl, k108, sv108])
  have rd104 : memLoad32 n7.mem (F + 0x104) = reg m (21 : Fin 32) :=
    rdOf (o := 0x104) (by decide) (by decide) (by rw [show F + BitVec.ofNat 32 0x104 = F + 0x104 from rfl, k104, sv104])
  have rd100 : memLoad32 n7.mem (F + 0x100) = reg m (22 : Fin 32) :=
    rdOf (o := 0x100) (by decide) (by decide) (by rw [show F + BitVec.ofNat 32 0x100 = F + 0x100 from rfl, k100, sv100])
  have rdFC : memLoad32 n7.mem (F + 0xFC) = reg m (23 : Fin 32) :=
    rdOf (o := 0xFC) (by decide) (by decide) (by rw [show F + BitVec.ofNat 32 0xFC = F + 0xFC from rfl, kFC, svFC])
  have rdF8 : memLoad32 n7.mem (F + 0xF8) = reg m (24 : Fin 32) :=
    rdOf (o := 0xF8) (by decide) (by decide) (by rw [show F + BitVec.ofNat 32 0xF8 = F + 0xF8 from rfl, kF8, svF8])
  have rdF4 : memLoad32 n7.mem (F + 0xF4) = reg m (25 : Fin 32) :=
    rdOf (o := 0xF4) (by decide) (by decide) (by rw [show F + BitVec.ofNat 32 0xF4 = F + 0xF4 from rfl, kF4, svF4])
  have rdF0 : memLoad32 n7.mem (F + 0xF0) = reg m (26 : Fin 32) :=
    rdOf (o := 0xF0) (by decide) (by decide) (by rw [show F + BitVec.ofNat 32 0xF0 = F + 0xF0 from rfl, kF0, svF0])
  have rdEC : memLoad32 n7.mem (F + 0xEC) = reg m (27 : Fin 32) :=
    rdOf (o := 0xEC) (by decide) (by decide) (by rw [show F + BitVec.ofNat 32 0xEC = F + 0xEC from rfl, kEC, svEC])
  -- the epilogue
  have w : St n7.mem P n7 0x8B4 (reg n7) := ⟨by rw [pc7]; try rfl, rfl, fun _ => rfl⟩
  obtain ⟨w1, dw, w0⟩ := w.aluImm hcE fmu_at_8b4 (off' := 0x8B6) (by decide)
  have ea : reg w1 a0 = F + 0x100 := by rw [w0.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [sp7]
  have es : reg w1 sp = F := by rw [w0.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp7
  have kw : ∀ q, q ≠ a0 → reg w1 q = reg n7 q := fun q hq => by
    rw [w0.regs]; by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact w.zero.symm
    · simp [upd, h0, hq]
  obtain ⟨e0, de0, ue0⟩ := w0.self.lwE hcE fmu_at_8b6 (off' := 0x8BA) (by decide)
    (by rw [ea, BitVec.add_assoc]; exact fr_al' hF (by decide)) (v := reg m ra)
    (by rw [ea, BitVec.add_assoc]; exact rd11C)
  have ke0 : ∀ q, q ≠ ra → reg e0 q = reg w1 q := fun q hq => by
    rw [ue0.regs]; by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact w0.self.zero.symm
    · simp [upd, h0, hq]
  have re0 : reg e0 ra = reg m ra := by rw [ue0.regs]; simp +decide [upd]
  have ea0 : reg e0 a0 = F + 0x100 := by rw [ke0 _ (by decide), ea]
  have es0 : reg e0 sp = F := by rw [ke0 _ (by decide), es]
  obtain ⟨e1, de1, ue1⟩ := ue0.self.lwE hcE fmu_at_8ba (off' := 0x8BC) (by decide)
    (by rw [ea0, BitVec.add_assoc]; exact fr_al' hF (by decide)) (v := reg m (8 : Fin 32))
    (by rw [ea0, BitVec.add_assoc]; exact rd118)
  have ke1 : ∀ q, q ≠ (8 : Fin 32) → reg e1 q = reg e0 q := fun q hq => by
    rw [ue1.regs]; by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact ue0.self.zero.symm
    · simp [upd, h0, hq]
  have re1 : reg e1 (8 : Fin 32) = reg m (8 : Fin 32) := by rw [ue1.regs]; simp +decide [upd]
  have ea1 : reg e1 a0 = F + 0x100 := by rw [ke1 _ (by decide), ea0]
  have es1 : reg e1 sp = F := by rw [ke1 _ (by decide), es0]
  obtain ⟨e2, de2, ue2⟩ := ue1.self.lwE hcE fmu_at_8bc (off' := 0x8BE) (by decide)
    (by rw [ea1, BitVec.add_assoc]; exact fr_al' hF (by decide)) (v := reg m (9 : Fin 32))
    (by rw [ea1, BitVec.add_assoc]; exact rd114)
  have ke2 : ∀ q, q ≠ (9 : Fin 32) → reg e2 q = reg e1 q := fun q hq => by
    rw [ue2.regs]; by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact ue1.self.zero.symm
    · simp [upd, h0, hq]
  have re2 : reg e2 (9 : Fin 32) = reg m (9 : Fin 32) := by rw [ue2.regs]; simp +decide [upd]
  have ea2 : reg e2 a0 = F + 0x100 := by rw [ke2 _ (by decide), ea1]
  have es2 : reg e2 sp = F := by rw [ke2 _ (by decide), es1]
  obtain ⟨e3, de3, ue3⟩ := ue2.self.lwE hcE fmu_at_8be (off' := 0x8C2) (by decide)
    (by rw [ea2, BitVec.add_assoc]; exact fr_al' hF (by decide)) (v := reg m (18 : Fin 32))
    (by rw [ea2, BitVec.add_assoc]; exact rd110)
  have ke3 : ∀ q, q ≠ (18 : Fin 32) → reg e3 q = reg e2 q := fun q hq => by
    rw [ue3.regs]; by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact ue2.self.zero.symm
    · simp [upd, h0, hq]
  have re3 : reg e3 (18 : Fin 32) = reg m (18 : Fin 32) := by rw [ue3.regs]; simp +decide [upd]
  have ea3 : reg e3 a0 = F + 0x100 := by rw [ke3 _ (by decide), ea2]
  have es3 : reg e3 sp = F := by rw [ke3 _ (by decide), es2]
  obtain ⟨e4, de4, ue4⟩ := ue3.self.lwE hcE fmu_at_8c2 (off' := 0x8C6) (by decide)
    (by rw [ea3, BitVec.add_assoc]; exact fr_al' hF (by decide)) (v := reg m (19 : Fin 32))
    (by rw [ea3, BitVec.add_assoc]; exact rd10C)
  have ke4 : ∀ q, q ≠ (19 : Fin 32) → reg e4 q = reg e3 q := fun q hq => by
    rw [ue4.regs]; by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact ue3.self.zero.symm
    · simp [upd, h0, hq]
  have re4 : reg e4 (19 : Fin 32) = reg m (19 : Fin 32) := by rw [ue4.regs]; simp +decide [upd]
  have ea4 : reg e4 a0 = F + 0x100 := by rw [ke4 _ (by decide), ea3]
  have es4 : reg e4 sp = F := by rw [ke4 _ (by decide), es3]
  obtain ⟨e5, de5, ue5⟩ := ue4.self.lwE hcE fmu_at_8c6 (off' := 0x8CA) (by decide)
    (by rw [ea4, BitVec.add_assoc]; exact fr_al' hF (by decide)) (v := reg m (20 : Fin 32))
    (by rw [ea4, BitVec.add_assoc]; exact rd108)
  have ke5 : ∀ q, q ≠ (20 : Fin 32) → reg e5 q = reg e4 q := fun q hq => by
    rw [ue5.regs]; by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact ue4.self.zero.symm
    · simp [upd, h0, hq]
  have re5 : reg e5 (20 : Fin 32) = reg m (20 : Fin 32) := by rw [ue5.regs]; simp +decide [upd]
  have ea5 : reg e5 a0 = F + 0x100 := by rw [ke5 _ (by decide), ea4]
  have es5 : reg e5 sp = F := by rw [ke5 _ (by decide), es4]
  obtain ⟨e6, de6, ue6⟩ := ue5.self.lwE hcE fmu_at_8ca (off' := 0x8CE) (by decide)
    (by rw [ea5, BitVec.add_assoc]; exact fr_al' hF (by decide)) (v := reg m (21 : Fin 32))
    (by rw [ea5, BitVec.add_assoc]; exact rd104)
  have ke6 : ∀ q, q ≠ (21 : Fin 32) → reg e6 q = reg e5 q := fun q hq => by
    rw [ue6.regs]; by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact ue5.self.zero.symm
    · simp [upd, h0, hq]
  have re6 : reg e6 (21 : Fin 32) = reg m (21 : Fin 32) := by rw [ue6.regs]; simp +decide [upd]
  have ea6 : reg e6 a0 = F + 0x100 := by rw [ke6 _ (by decide), ea5]
  have es6 : reg e6 sp = F := by rw [ke6 _ (by decide), es5]
  obtain ⟨e7, de7, ue7⟩ := ue6.self.lwE hcE fmu_at_8ce (off' := 0x8D2) (by decide)
    (by rw [ea6, BitVec.add_assoc]; exact fr_al' hF (by decide)) (v := reg m (22 : Fin 32))
    (by rw [ea6, BitVec.add_assoc]; exact rd100)
  have ke7 : ∀ q, q ≠ (22 : Fin 32) → reg e7 q = reg e6 q := fun q hq => by
    rw [ue7.regs]; by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact ue6.self.zero.symm
    · simp [upd, h0, hq]
  have re7 : reg e7 (22 : Fin 32) = reg m (22 : Fin 32) := by rw [ue7.regs]; simp +decide [upd]
  have ea7 : reg e7 a0 = F + 0x100 := by rw [ke7 _ (by decide), ea6]
  have es7 : reg e7 sp = F := by rw [ke7 _ (by decide), es6]
  obtain ⟨e8, de8, ue8⟩ := ue7.self.lwE hcE fmu_at_8d2 (off' := 0x8D4) (by decide)
    (by rw [es7]; exact fr_al' hF (by decide)) (v := reg m (23 : Fin 32))
    (by rw [es7]; exact rdFC)
  have ke8 : ∀ q, q ≠ (23 : Fin 32) → reg e8 q = reg e7 q := fun q hq => by
    rw [ue8.regs]; by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact ue7.self.zero.symm
    · simp [upd, h0, hq]
  have re8 : reg e8 (23 : Fin 32) = reg m (23 : Fin 32) := by rw [ue8.regs]; simp +decide [upd]
  have ea8 : reg e8 a0 = F + 0x100 := by rw [ke8 _ (by decide), ea7]
  have es8 : reg e8 sp = F := by rw [ke8 _ (by decide), es7]
  obtain ⟨e9, de9, ue9⟩ := ue8.self.lwE hcE fmu_at_8d4 (off' := 0x8D6) (by decide)
    (by rw [es8]; exact fr_al' hF (by decide)) (v := reg m (24 : Fin 32))
    (by rw [es8]; exact rdF8)
  have ke9 : ∀ q, q ≠ (24 : Fin 32) → reg e9 q = reg e8 q := fun q hq => by
    rw [ue9.regs]; by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact ue8.self.zero.symm
    · simp [upd, h0, hq]
  have re9 : reg e9 (24 : Fin 32) = reg m (24 : Fin 32) := by rw [ue9.regs]; simp +decide [upd]
  have ea9 : reg e9 a0 = F + 0x100 := by rw [ke9 _ (by decide), ea8]
  have es9 : reg e9 sp = F := by rw [ke9 _ (by decide), es8]
  obtain ⟨e10, de10, ue10⟩ := ue9.self.lwE hcE fmu_at_8d6 (off' := 0x8D8) (by decide)
    (by rw [es9]; exact fr_al' hF (by decide)) (v := reg m (25 : Fin 32))
    (by rw [es9]; exact rdF4)
  have ke10 : ∀ q, q ≠ (25 : Fin 32) → reg e10 q = reg e9 q := fun q hq => by
    rw [ue10.regs]; by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact ue9.self.zero.symm
    · simp [upd, h0, hq]
  have re10 : reg e10 (25 : Fin 32) = reg m (25 : Fin 32) := by rw [ue10.regs]; simp +decide [upd]
  have ea10 : reg e10 a0 = F + 0x100 := by rw [ke10 _ (by decide), ea9]
  have es10 : reg e10 sp = F := by rw [ke10 _ (by decide), es9]
  obtain ⟨e11, de11, ue11⟩ := ue10.self.lwE hcE fmu_at_8d8 (off' := 0x8DA) (by decide)
    (by rw [es10]; exact fr_al' hF (by decide)) (v := reg m (26 : Fin 32))
    (by rw [es10]; exact rdF0)
  have ke11 : ∀ q, q ≠ (26 : Fin 32) → reg e11 q = reg e10 q := fun q hq => by
    rw [ue11.regs]; by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact ue10.self.zero.symm
    · simp [upd, h0, hq]
  have re11 : reg e11 (26 : Fin 32) = reg m (26 : Fin 32) := by rw [ue11.regs]; simp +decide [upd]
  have ea11 : reg e11 a0 = F + 0x100 := by rw [ke11 _ (by decide), ea10]
  have es11 : reg e11 sp = F := by rw [ke11 _ (by decide), es10]
  obtain ⟨e12, de12, ue12⟩ := ue11.self.lwE hcE fmu_at_8da (off' := 0x8DC) (by decide)
    (by rw [es11]; exact fr_al' hF (by decide)) (v := reg m (27 : Fin 32))
    (by rw [es11]; exact rdEC)
  have ke12 : ∀ q, q ≠ (27 : Fin 32) → reg e12 q = reg e11 q := fun q hq => by
    rw [ue12.regs]; by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact ue11.self.zero.symm
    · simp [upd, h0, hq]
  have re12 : reg e12 (27 : Fin 32) = reg m (27 : Fin 32) := by rw [ue12.regs]; simp +decide [upd]
  have ea12 : reg e12 a0 = F + 0x100 := by rw [ke12 _ (by decide), ea11]
  have es12 : reg e12 sp = F := by rw [ke12 _ (by decide), es11]
  have fin0 : reg e12 ra = reg m ra := by rw [ke12 _ (by decide), ke11 _ (by decide), ke10 _ (by decide), ke9 _ (by decide), ke8 _ (by decide), ke7 _ (by decide), ke6 _ (by decide), ke5 _ (by decide), ke4 _ (by decide), ke3 _ (by decide), ke2 _ (by decide), ke1 _ (by decide)]; exact re0
  have fin1 : reg e12 (8 : Fin 32) = reg m (8 : Fin 32) := by rw [ke12 _ (by decide), ke11 _ (by decide), ke10 _ (by decide), ke9 _ (by decide), ke8 _ (by decide), ke7 _ (by decide), ke6 _ (by decide), ke5 _ (by decide), ke4 _ (by decide), ke3 _ (by decide), ke2 _ (by decide)]; exact re1
  have fin2 : reg e12 (9 : Fin 32) = reg m (9 : Fin 32) := by rw [ke12 _ (by decide), ke11 _ (by decide), ke10 _ (by decide), ke9 _ (by decide), ke8 _ (by decide), ke7 _ (by decide), ke6 _ (by decide), ke5 _ (by decide), ke4 _ (by decide), ke3 _ (by decide)]; exact re2
  have fin3 : reg e12 (18 : Fin 32) = reg m (18 : Fin 32) := by rw [ke12 _ (by decide), ke11 _ (by decide), ke10 _ (by decide), ke9 _ (by decide), ke8 _ (by decide), ke7 _ (by decide), ke6 _ (by decide), ke5 _ (by decide), ke4 _ (by decide)]; exact re3
  have fin4 : reg e12 (19 : Fin 32) = reg m (19 : Fin 32) := by rw [ke12 _ (by decide), ke11 _ (by decide), ke10 _ (by decide), ke9 _ (by decide), ke8 _ (by decide), ke7 _ (by decide), ke6 _ (by decide), ke5 _ (by decide)]; exact re4
  have fin5 : reg e12 (20 : Fin 32) = reg m (20 : Fin 32) := by rw [ke12 _ (by decide), ke11 _ (by decide), ke10 _ (by decide), ke9 _ (by decide), ke8 _ (by decide), ke7 _ (by decide), ke6 _ (by decide)]; exact re5
  have fin6 : reg e12 (21 : Fin 32) = reg m (21 : Fin 32) := by rw [ke12 _ (by decide), ke11 _ (by decide), ke10 _ (by decide), ke9 _ (by decide), ke8 _ (by decide), ke7 _ (by decide)]; exact re6
  have fin7 : reg e12 (22 : Fin 32) = reg m (22 : Fin 32) := by rw [ke12 _ (by decide), ke11 _ (by decide), ke10 _ (by decide), ke9 _ (by decide), ke8 _ (by decide)]; exact re7
  have fin8 : reg e12 (23 : Fin 32) = reg m (23 : Fin 32) := by rw [ke12 _ (by decide), ke11 _ (by decide), ke10 _ (by decide), ke9 _ (by decide)]; exact re8
  have fin9 : reg e12 (24 : Fin 32) = reg m (24 : Fin 32) := by rw [ke12 _ (by decide), ke11 _ (by decide), ke10 _ (by decide)]; exact re9
  have fin10 : reg e12 (25 : Fin 32) = reg m (25 : Fin 32) := by rw [ke12 _ (by decide), ke11 _ (by decide)]; exact re10
  have fin11 : reg e12 (26 : Fin 32) = reg m (26 : Fin 32) := by rw [ke12 _ (by decide)]; exact re11
  have fin12 : reg e12 (27 : Fin 32) = reg m (27 : Fin 32) := by exact re12
  have kpass : ∀ q, q ≠ a0 → q ≠ ra → q.val ∉ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg e12 q = reg n7 q := fun q h1 h2 h3 => by
    rw [ke12 q (fun e => by subst e; exact h3 (by decide)), ke11 q (fun e => by subst e; exact h3 (by decide)), ke10 q (fun e => by subst e; exact h3 (by decide)), ke9 q (fun e => by subst e; exact h3 (by decide)), ke8 q (fun e => by subst e; exact h3 (by decide)), ke7 q (fun e => by subst e; exact h3 (by decide)), ke6 q (fun e => by subst e; exact h3 (by decide)), ke5 q (fun e => by subst e; exact h3 (by decide)), ke4 q (fun e => by subst e; exact h3 (by decide)), ke3 q (fun e => by subst e; exact h3 (by decide)), ke2 q (fun e => by subst e; exact h3 (by decide)), ke1 q (fun e => by subst e; exact h3 (by decide)), ke0 q (fun e => by subst e; exact h2 (by decide)), kw q h1]
  obtain ⟨n8, d8, u8⟩ := ue12.self.aluImm hcE fmu_at_8dc (off' := 0x8DE) (by decide)
  obtain ⟨n9, d9, pc9, mem9, regs9⟩ := u8.jalr hcE fmu_at_8de
  have lX : ∀ i, i < 10 → limbAt m.mem xp i = limbAt P13 xp i := fun i hi => by
    unfold limbAt; rw [load_frame fpro (sXF.symm.subR (c := 4 * i) (l := 4) (by omega))]
  have lY : ∀ i, i < 10 → limbAt m.mem yp i = limbAt P13 yp i := fun i hi => by
    unfold limbAt; rw [load_frame fpro (sYF.symm.subR (c := 4 * i) (l := 4) (by omega))]
  have hmem : ∀ q : Fin 32, feMKeep q = true → q = 0 ∨ q = ra ∨ q = sp ∨ q = (3 : Fin 32) ∨ q = (4 : Fin 32) ∨
      q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨
      q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q = (23 : Fin 32) ∨ q = (24 : Fin 32) ∨ q = (25 : Fin 32) ∨
      q = (26 : Fin 32) ∨ q = (27 : Fin 32) := by decide
  have pass3 : reg n7 (3 : Fin 32) = reg m (3 : Fin 32) := by
    rw [k7 _ rfl, r6 _ (by decide), upd_ne (by decide) (by decide), upd_ne (by decide) (by decide), gp3, up13.regs,
      rk2 _ (by decide) (by decide)]
  have pass4 : reg n7 (4 : Fin 32) = reg m (4 : Fin 32) := by
    rw [k7 _ rfl, r6 _ (by decide), upd_ne (by decide) (by decide), upd_ne (by decide) (by decide), tp3, up13.regs,
      rk2 _ (by decide) (by decide)]
  refine ⟨n9, .cons d1 (.cons d2 (.cons dp0 (.cons dp1 (.cons dp2 (.cons dp3 (.cons dp4 (.cons dp5 (.cons dp6 (.cons dp7 (.cons dp8 (.cons dp9 (.cons dp10 (.cons dp11 (.cons dp12 (.cons dp13 (c3.trans (.cons d4 (.cons d5 (c6.trans (c7.trans (.cons dw (.cons de0 (.cons de1 (.cons de2 (.cons de3 (.cons de4 (.cons de5 (.cons de6 (.cons de7 (.cons de8 (.cons de9 (.cons de10 (.cons de11 (.cons de12 (.cons d8 (.single d9)))))))))))))))))))))))))))))))))))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc9]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, fin0, hra, hret]
  · rw [regs9]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [es12, hspF]
  · intro q hq
    rw [regs9]
    rcases hmem q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [upd]; exact hz.symm
    · rw [upd_ne (by decide) (by decide)]; exact fin0
    · simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [es12, hspF, hsp]
    · rw [upd_ne (by decide) (by decide), kpass _ (by decide) (by decide) (by decide)]; exact pass3
    · rw [upd_ne (by decide) (by decide), kpass _ (by decide) (by decide) (by decide)]; exact pass4
    · rw [upd_ne (by decide) (by decide)]; exact fin1
    · rw [upd_ne (by decide) (by decide)]; exact fin2
    · rw [upd_ne (by decide) (by decide)]; exact fin3
    · rw [upd_ne (by decide) (by decide)]; exact fin4
    · rw [upd_ne (by decide) (by decide)]; exact fin5
    · rw [upd_ne (by decide) (by decide)]; exact fin6
    · rw [upd_ne (by decide) (by decide)]; exact fin7
    · rw [upd_ne (by decide) (by decide)]; exact fin8
    · rw [upd_ne (by decide) (by decide)]; exact fin9
    · rw [upd_ne (by decide) (by decide)]; exact fin10
    · rw [upd_ne (by decide) (by decide)]; exact fin11
    · rw [upd_ne (by decide) (by decide)]; exact fin12
  · rw [mem9, out7, mem6, lX 0 (by decide), lX 1 (by decide), lX 2 (by decide), lX 3 (by decide), lX 4 (by decide),
      lX 5 (by decide), lX 6 (by decide), lX 7 (by decide), lX 8 (by decide), lX 9 (by decide), lY 0 (by decide),
      lY 1 (by decide), lY 2 (by decide), lY 3 (by decide), lY 4 (by decide), lY 5 (by decide), lY 6 (by decide),
      lY 7 (by decide), lY 8 (by decide), lY 9 (by decide)]
    simp only [feMulSpec]
    rw [← hzs]
    rfl
  · intro x hx ho; rw [mem9, fr7G x hx ho]

end C3.RV32
