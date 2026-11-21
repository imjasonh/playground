import C3BootProofs.Proofs.FeSqBody

/-!
# `FieldElement2625::square_inner`

`curve25519_dalek`'s squaring before the carry, as compiled: a leaf function
that saves `ra` and `s0` through `s11`, runs the body that `FeSqBody.lean`
proves (the ten `u64` sums into the result), restores the registers, and
returns.
-/

namespace C3.RV32

open C3.Image

/-- The registers `square_inner` saves, at offsets from its `sp`. -/
abbrev fsqPs : List (Fin 32 × Word) :=
  [(ra, 0x4C), ((8 : Fin 32), 0x48), ((9 : Fin 32), 0x44), ((18 : Fin 32), 0x40), ((19 : Fin 32), 0x3C), ((20 : Fin 32), 0x38), ((21 : Fin 32), 0x34), ((22 : Fin 32), 0x30), ((23 : Fin 32), 0x2C), ((24 : Fin 32), 0x28), ((25 : Fin 32), 0x24), ((26 : Fin 32), 0x20), ((27 : Fin 32), 0x1C)]

section
set_option maxRecDepth 20000
theorem fsqSave_end : blockEnd feSquareInnerCode 2 (saveBlock fsqPs) = some 0x1C := by decide
theorem fsqRestore_end : blockEnd feSquareInnerCode 0x4CC (restoreBlock fsqPs) = some 0x4E6 := by decide
theorem fsqPs_range : ∀ p ∈ fsqPs, p.2.toNat % 4 = 0 ∧ 0x1C ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x50 := by decide
theorem fsqPs_sp : ∀ p ∈ fsqPs, p.1 ≠ sp := by decide
end

/-- Where `square_inner` runs: its code at an even `P`, the 0x50 bytes of
stack below `sp0`, the ten `u64` sums at `out`, and the operand at `xp`,
aligned and apart where they must be. -/
structure FeSqEnv (M : Word → BitVec 8) (P sp0 out xp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P feSquareInnerCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x50 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hx : xp.toNat % 4 = 0
  sSC : Sep (sp0 + 0xFFFFFFB0) 0x50 P feSquareInnerCode.length
  sOC : Sep out 0x50 P feSquareInnerCode.length
  sOS : Sep out 0x50 (sp0 + 0xFFFFFFB0) 0x50
  sXS : Sep xp 40 (sp0 + 0xFFFFFFB0) 0x50
  sXO : Sep xp 40 out 0x50

/-- The registers `square_inner` leaves as they were. -/
def fsqKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `FieldElement2625::square_inner`**, called with the result
at `out` and the operand's ten limbs at `xp`: it stores `feSqZ` of the limbs
as ten `u64`s, returns with `sp` and every register but `t0` through `t6`
and `a0` through `a7` as they were, and changes no memory outside its 0x50
bytes of stack and the result. -/
theorem feSqInner_correct (m : Machine) {P sp0 out xp retAddr : Word} (env : FeSqEnv m.mem P sp0 out xp)
    (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, fsqKeep q = true → reg m' q = reg m q) ∧
      [u64At m'.mem out 0, u64At m'.mem out 1, u64At m'.mem out 2, u64At m'.mem out 3, u64At m'.mem out 4,
        u64At m'.mem out 5, u64At m'.mem out 6, u64At m'.mem out 7, u64At m'.mem out 8, u64At m'.mem out 9] =
        feSqZ (limbAt m.mem xp 0) (limbAt m.mem xp 1) (limbAt m.mem xp 2) (limbAt m.mem xp 3)
          (limbAt m.mem xp 4) (limbAt m.mem xp 5) (limbAt m.mem xp 6) (limbAt m.mem xp 7)
          (limbAt m.mem xp 8) (limbAt m.mem xp 9) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFB0) 0x50 x 1 → Sep out 0x50 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hFa : (sp0 + 0xFFFFFFB0).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFFB0) (by decide)
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code fsq_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0) sp = sp0 + 0xFFFFFFB0 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [hsp]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock fsqPs) u1 env.code fsqSave_end (saveBlock_ok _ fsqPs _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (fsqPs_range p hp).1, frm_sep' env.sSC (by have := fsqPs_range p hp; omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (sp0 + 0xFFFFFFB0)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0)) fsqPs = Msv := ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep (sp0 + 0xFFFFFFB0) 0x50 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; exact saveMem_outside fsqPs fun p hp => frm_sep' hx (by have := fsqPs_range p hp; omega)
  have hcS : CodeIn Msv P feSquareInnerCode := fun i hi => by
    rw [frSv _ (env.sSC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  have k2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q hq => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, hq]
  have sp2 : reg m2 sp = sp0 + 0xFFFFFFB0 := by rw [u2.regs]; exact sp1
  -- the body
  obtain ⟨n3, M3, c3, u3, fr3, k1C, k20, k24, k28, k2C, k30, k34, k38, k3C, k40, k44, k48, k4C, hl3, sp3, gp3, tp3⟩ :=
    fsq_body u2.self hcS sp2 (by rw [k2 a0 (by decide), ha0]) (by rw [k2 a1 (by decide), ha1]) hFa env.hout env.hx
      env.sSC env.sOC env.sXS env.sXO env.sOS.symm
  have hc3 : CodeIn M3 P feSquareInnerCode := fun i hi => by
    rw [fr3 _ (env.sSC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]
    exact hcS i hi
  -- the restores and the return
  obtain ⟨n4, c4, u4⟩ := St.block (restoreBlock fsqPs) u3 hc3 fsqRestore_end
    (restoreBlock_ok M3 _ fsqPs (reg n3) sp3 fsqPs_sp fun p hp => fr_al' hFa (fsqPs_range p hp).1)
  simp only [restoreBlock_run M3 _ fsqPs (reg n3) sp3 fsqPs_sp] at u4
  have rsp4 : restoreRegs M3 (sp0 + 0xFFFFFFB0) (reg n3) fsqPs sp = sp0 + 0xFFFFFFB0 := by
    rw [restoreRegs_sp _ _ _ _ fsqPs_sp]; exact sp3
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc3 fsq_at_4e6 (off' := 0x4E8) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hc3 fsq_at_4e8
  have slot : ∀ r o, (r, o) ∈ fsqPs → memLoad32 M3 (sp0 + 0xFFFFFFB0 + o) = reg m r := fun r o h => by
    simp only [fsqPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · first | rw [k1C] | rw [k20] | rw [k24] | rw [k28] | rw [k2C] | rw [k30] | rw [k34] | rw [k38] | rw [k3C] | rw [k40] | rw [k44] | rw [k48] | rw [k4C]
      rw [← hMsv]
      simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have lX : ∀ i, i < 10 → limbAt m.mem xp i = limbAt Msv xp i := fun i hi => by
    unfold limbAt; rw [load_frame frSv (env.sXS.symm.subR (c := 4 * i) (l := 4) (by omega))]
  have uO : ∀ i, i < 10 → u64At n6.mem out i = u64At M3 out i := fun i _ => by rw [mem6]
  refine ⟨n6, .cons d1 (c2.trans (c3.trans (c4.trans (.cons d5 (.single d6))))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc6]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [add_lit_zero, slot ra 0x4C (by decide), hra, hret]
  · rw [regs6]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rsp4, BitVec.add_assoc]
    exact BitVec.add_zero _
  · intro q hq
    rw [regs6]
    by_cases hs : q = sp
    · subst hs
      simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rsp4, BitVec.add_assoc, hsp]
      exact BitVec.add_zero _
    by_cases hsv : q ∈ fsqPs.map Prod.fst
    · simp only [fsqPs, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hsv
      rcases hsv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · simp +decide only [upd_app, ↓reduceIte]
        simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
        exact slot _ _ (by decide)
    · have hm : q = 0 ∨ q = (3 : Fin 32) ∨ q = (4 : Fin 32) := by
        revert hq hsv hs; revert q; decide
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      rw [upd_ne h0 hs]
      simp only [restoreRegs]
      have ne : ∀ r ∈ fsqPs.map Prod.fst, q ≠ r := fun r hr e => hsv (e ▸ hr)
      rw [upd_ne h0 (ne (27 : Fin 32) (by decide)), upd_ne h0 (ne (26 : Fin 32) (by decide)), upd_ne h0 (ne (25 : Fin 32) (by decide)), upd_ne h0 (ne (24 : Fin 32) (by decide)), upd_ne h0 (ne (23 : Fin 32) (by decide)), upd_ne h0 (ne (22 : Fin 32) (by decide)), upd_ne h0 (ne (21 : Fin 32) (by decide)), upd_ne h0 (ne (20 : Fin 32) (by decide)), upd_ne h0 (ne (19 : Fin 32) (by decide)), upd_ne h0 (ne (18 : Fin 32) (by decide)), upd_ne h0 (ne (9 : Fin 32) (by decide)), upd_ne h0 (ne (8 : Fin 32) (by decide)), upd_ne h0 (ne ra (by decide))]
      rcases hm with rfl | rfl | rfl
      · exact absurd rfl h0
      · rw [gp3, k2 _ (by decide)]
      · rw [tp3, k2 _ (by decide)]
  · rw [uO 0 (by decide), uO 1 (by decide), uO 2 (by decide), uO 3 (by decide), uO 4 (by decide),
      uO 5 (by decide), uO 6 (by decide), uO 7 (by decide), uO 8 (by decide), uO 9 (by decide), hl3,
      lX 0 (by decide), lX 1 (by decide), lX 2 (by decide), lX 3 (by decide), lX 4 (by decide),
      lX 5 (by decide), lX 6 (by decide), lX 7 (by decide), lX 8 (by decide), lX 9 (by decide)]
  · intro x hx ho
    rw [mem6, fr3 x hx ho, frSv x hx]

end C3.RV32
