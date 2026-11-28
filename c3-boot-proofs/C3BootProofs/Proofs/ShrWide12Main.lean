import C3BootProofs.Proofs.ShrWide12

/-!
# `shr_in_place_wide::<12, 2>`: the whole function

The stages in `ShrWide12`, chained from entry to return.
-/

namespace C3.RV32

open C3.Image

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
set_option exponentiation.threshold 600 in
/-- **The compiled `safegcd::shr_in_place_wide::<12, 2>`**, called with `lo`
(12 limbs), `hi` (2 limbs), and `shift` from 1 to 63. It returns to its
caller with the 448-bit value `lo + 2^384 hi` shifted right `shift` bits,
the callee-saved registers and `sp` restored, and memory changed only in
its frame, `lo`, and `hi`. -/
theorem shr12_correct (m : Machine) {P sp0 lo hi retAddr : Word} {s : Nat} (env : SHEnv m.mem P sp0 lo hi)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = lo) (ha1 : reg m a1 = hi)
    (ha2 : reg m a2 = BitVec.ofNat 32 s) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hs1 : 1 ≤ s) (hs2 : s ≤ 63) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17] → reg m' q = reg m q) ∧
      accV m'.mem lo 12 + 2 ^ 384 * accV m'.mem hi 2 = (accV m.mem lo 12 + 2 ^ 384 * accV m.mem hi 2) / 2 ^ s ∧
      ∀ x, Sep (shF sp0) 0x90 x 1 → Sep lo 48 x 1 → Sep hi 8 x 1 → m'.mem x = m.mem x := by
  have hFw := shF_w env.hS
  have hFa : (shF sp0).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF70) (by decide)
  have hFw' : (shF sp0).toNat + 0x90 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  -- a memory that differs from `m`'s only in the frame and `hi` still holds the code
  have cA : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (shF sp0) 0x90 b code.length → Sep hi 8 b code.length →
      (∀ x, Sep (shF sp0) 0x90 x 1 → Sep hi 8 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hh hM i hi' => by
      rw [hM _ (hs.subR (c := i) (l := 1) (by omega)) (hh.subR (c := i) (l := 1) (by omega))]; exact hc i hi'
  have inF : ∀ {x : Word} {c l : Nat}, c + l ≤ 0x90 → Sep (shF sp0) 0x90 x 1 →
      Sep (shF sp0 + BitVec.ofNat 32 c) l x 1 := fun h hx => hx.sub h
  -- the prologue
  obtain ⟨n0, M0, c0, s0, fr0, hsl0, z38, -, -, sp0', r21, r19, r18, ra1, ra2, ra0, ra3, ra4, ra5, k0⟩ :=
    sh_pro m env hpc hsp ha0 ha1 ha2 hs1 hs2
  have frA0 : ∀ x, Sep (shF sp0) 0x90 x 1 → Sep hi 8 x 1 → M0 x = m.mem x := fun x hx _ => fr0 x hx
  -- the bits that cross from `hi`
  obtain ⟨n1, M1, c1, s1, fr1, hW, r22, k1⟩ := sh_T hs1 hs2 s0 (cA env.code env.sC env.hC frA0) hFa env.sC
    env.hhi env.sH z38 sp0' r21 ra1 ra2 ra0 ra3 ra4 ra5
  have frA1 : ∀ x, Sep (shF sp0) 0x90 x 1 → Sep hi 8 x 1 → M1 x = m.mem x := fun x hx hh => by
    rw [fr1 x (inF (by decide) hx) (by have := inF (c := 0) (l := 8) (by decide) hx; rwa [add_ofNat_zero] at this),
      frA0 x hx hh]
  have kk : ∀ {q : Fin 32} {l : List Nat}, q.val ∉ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
      21, 22, 23] → (∀ v ∈ l, v ∈ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]) →
      q.val ∉ l := fun hq hl h => hq (hl _ h)
  have sp1 : reg n1 sp = shF sp0 := by rw [k1 sp (by decide), sp0']
  have r21_1 : reg n1 21 = BitVec.ofNat 32 s := by rw [k1 21 (by decide), r21]
  have r19_1 : reg n1 19 = hi := by rw [k1 19 (by decide), r19]
  -- `hi`'s right shift
  obtain ⟨n2, M2, c2, s2, fr2, vH, r20_2, r9_2, k2⟩ := sh_H hs1 hs2 env.hP s1 (cA env.code env.sC env.hC frA1)
    (cA env.lm env.sLm env.hLm frA1) (cA env.tr env.sTr env.hTr frA1) hFa hFw' env.sC env.sLm env.sTr env.hhi
    env.hwh env.sH env.hC sp1 r21_1 r19_1
  have frA2 : ∀ x, Sep (shF sp0) 0x90 x 1 → Sep hi 8 x 1 → M2 x = m.mem x := fun x hx hh => by
    rw [fr2 x (inF (by decide) hx) hh, frA1 x hx hh]
  have sp2 : reg n2 sp = shF sp0 := by rw [k2 sp (by decide), sp1]
  have r18_2 : reg n2 18 = lo := by rw [k2 18 (by decide), k1 18 (by decide), r18]
  -- `lo`'s right shift
  obtain ⟨n3, M3, c3, s3, fr3, vL, k3⟩ := sh_L hs1 hs2 env.hP s2 (cA env.code env.sC env.hC frA2)
    (cA env.lm env.sLm env.hLm frA2) (cA env.tr env.sTr env.hTr frA2) (cA env.mset env.sMs env.hMs frA2) hFa hFw'
    env.sC env.sLm env.sTr env.sMs env.hlo env.hwl env.sL sp2 r20_2 r18_2 r9_2
  have frA3 : ∀ x, Sep (shF sp0) 0x90 x 1 → Sep hi 8 x 1 → M3 x = m.mem x := fun x hx hh => by
    rw [fr3 x (inF (by decide) hx), frA2 x hx hh]
  have sp3 : reg n3 sp = shF sp0 := by rw [k3 sp (by decide), sp2]
  have r18_3 : reg n3 18 = lo := by rw [k3 18 (by decide), r18_2]
  -- the copies to `lo`
  obtain ⟨n4, c4, s4, k4⟩ := sh_E env.hP s3 (cA env.code env.sC env.hC frA3) (cA env.stub env.sU env.hU frA3)
    (cA env.body env.sB env.hB frA3) hFa hFw' env.sC env.sB env.sU env.hlo env.hwl env.sL env.lB env.lC sp3 r18_3
  obtain ⟨M4, hM4⟩ : ∃ M4, copyWords (copyWords M3 (shF sp0 + BitVec.ofNat 32 8) (shF sp0 + BitVec.ofNat 32 0x38) 12)
      lo (shF sp0 + BitVec.ofNat 32 8) 12 = M4 := ⟨_, rfl⟩
  rw [hM4] at s4
  have fr4 : ∀ x, Sep (shF sp0 + BitVec.ofNat 32 8) 48 x 1 → Sep lo 48 x 1 → M4 x = M3 x := fun x h8 hl => by
    rw [← hM4, copyWords_outside 12 hl, copyWords_outside 12 h8]
  have hc4 : CodeIn M4 P shr12Code := fun i hi' => by
    rw [fr4 _ ((env.sC.sub (c := 8) (l := 48) (by decide)).subR (c := i) (l := 1) (by omega))
      (env.lC.subR (c := i) (l := 1) (by omega)), frA3 _ (env.sC.subR (c := i) (l := 1) (by omega))
      (env.hC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi'
  have kE : ∀ q : Fin 32, q.val ∉ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] →
      reg n4 q = reg n1 q := fun q hq => by
    rw [k4 q (kk hq (by decide)), k3 q (kk hq (by decide)), k2 q (kk hq (by decide))]
  have sp4 : reg n4 sp = shF sp0 := by rw [k4 sp (by decide), sp3]
  have r18_4 : reg n4 18 = lo := by rw [k4 18 (by decide), r18_3]
  have r9_4 : reg n4 9 = BitVec.ofNat 32 (s % 32) := by rw [k4 9 (by decide), k3 9 (by decide), r9_2]
  have r20_4 : reg n4 20 = BitVec.ofNat 32 (s / 32) := by rw [k4 20 (by decide), k3 20 (by decide), r20_2]
  -- the two words at `F` are still the crossing bits
  have hF0 : ∀ j, j + 4 ≤ 8 → memLoad32 M4 (shF sp0 + BitVec.ofNat 32 j) = memLoad32 M1 (shF sp0 + BitVec.ofNat 32 j) :=
    fun j hj => memLoad32_congr fun t ht => by
      have hx : ∀ c l, j + t < c ∨ c + l ≤ j + t → c + l ≤ 0x90 →
          Sep (shF sp0 + BitVec.ofNat 32 c) l (shF sp0 + BitVec.ofNat 32 j + BitVec.ofNat 32 t) 1 := fun c l h hl => by
        rw [add_ofNat_assoc]; exact sep_offsets _ (h.elim (fun h => .inr (by omega)) (fun h => .inl h)) (by omega) (by omega)
      have hl : Sep lo 48 (shF sp0 + BitVec.ofNat 32 j + BitVec.ofNat 32 t) 1 := by
        rw [add_ofNat_assoc]; exact env.sL.subR (by omega)
      have hh : Sep hi 8 (shF sp0 + BitVec.ofNat 32 j + BitVec.ofNat 32 t) 1 := by
        rw [add_ofNat_assoc]; exact env.sH.subR (by omega)
      rw [fr4 _ (hx 8 48 (.inl (by omega)) (by decide)) hl, fr3 _ (hx 0x38 48 (.inl (by omega)) (by decide)),
        fr2 _ (hx 0x38 8 (.inl (by omega)) (by decide)) hh]
  have hF0' : memLoad32 M4 (shF sp0) = memLoad32 M1 (shF sp0) := by
    have := hF0 0 (by decide); rwa [add_ofNat_zero] at this
  have hF4' : memLoad32 M4 (shF sp0 + 4) = memLoad32 M1 (shF sp0 + 4) := hF0 4 (by decide)
  have r22_4 : reg n4 22 = memLoad32 M4 (shF sp0 + 4) := by
    rw [k4 22 (by decide), k3 22 (by decide), k2 22 (by decide), r22, hF4']
  -- `lo` after the copies is `lo` shifted
  have accLo : accV M4 lo 12 = accV m.mem lo 12 / 2 ^ s := by
    have hFw8 : (shF sp0 + BitVec.ofNat 32 8).toNat + 4 * 12 ≤ 2 ^ 32 := by
      rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega
    have e2 : accV M2 lo 12 = accV m.mem lo 12 := accV_congr 12 fun i hi => memLoad32_congr fun t ht => by
      rw [add_ofNat_assoc]
      exact frA2 _ (env.sL.symm.subR (by omega)) (env.sLH.symm.subR (by omega))
    have hlw : lo.toNat + 4 * 12 ≤ 2 ^ 32 := by have := env.hwl; omega
    rw [← hM4, accV_congr2 12 fun i hi => copyWords_load (dst := lo) 12 i hi hlw,
      accV_congr2 12 fun i hi => copyWords_load (dst := shF sp0 + BitVec.ofNat 32 8) 12 i hi hFw8, vL, e2]
  have hacc : accV M4 lo 12 < 2 ^ (384 - s) := by
    rw [accLo]; apply shDivLt
    have := accV_lt m.mem lo 12
    rwa [← Nat.pow_add, show s + (384 - s) = 32 * 12 by omega]
  have hX : (memLoad32 M4 (shF sp0)).toNat + 2 ^ 32 * (memLoad32 M4 (shF sp0 + 4)).toNat =
      accV m.mem hi 2 * 2 ^ (64 - s) % 2 ^ 64 := by
    have e0 : accV M0 hi 2 = accV m.mem hi 2 := accV_congr 2 fun i hi' => memLoad32_congr fun t ht => by
      rw [add_ofNat_assoc]
      exact fr0 _ (env.sH.symm.subR (by omega))
    rw [hF0', hF4', hW, ← accV_two, e0]
  -- the bits from `hi` into `lo`
  obtain ⟨n5, M5, c5, s5, fr5, vF, k5⟩ := sh_F hs1 hs2 s4 hc4 hFa env.hlo env.hwl env.lC sp4 r18_4 r9_4 r20_4
    r22_4 hX hacc
  have hc5 : CodeIn M5 P shr12Code := fun i hi' => by
    rw [fr5 _ (env.lC.subR (c := i) (l := 1) (by omega))]; exact hc4 i hi'
  have sp5 : reg n5 sp = shF sp0 := by rw [k5 sp (by decide), sp4]
  -- the saved registers survive to the epilogue
  have hsl5 : ∀ r o, (r, o) ∈ shPs → memLoad32 M5 (shF sp0 + o) = reg m r := fun r o h => by
    clear vF hacc hX accLo hW vL vH
    obtain ⟨_, ho1, ho2⟩ := shPs_range (r, o) h
    dsimp only at ho1 ho2
    have e : shF sp0 + o = shF sp0 + BitVec.ofNat 32 o.toNat := by rw [ofNat_toNat_self]
    have sF : ∀ c l, c + l ≤ o.toNat → Sep (shF sp0 + BitVec.ofNat 32 c) l (shF sp0 + o) 4 := fun c l hcl => by
      rw [e]; exact sep_offsets _ (.inl hcl) (by omega) (by omega)
    have sL : Sep lo 48 (shF sp0 + o) 4 := by rw [e]; exact env.sL.subR (by omega)
    have sHo : Sep hi 8 (shF sp0 + o) 4 := by rw [e]; exact env.sH.subR (by omega)
    have sF0 : Sep (shF sp0) 8 (shF sp0 + o) 4 := by have := sF 0 8 (by omega); rwa [add_ofNat_zero] at this
    rw [load_frame fr5 sL, load_frame2 fr4 (sF 8 48 (by omega)) sL, load_frame fr3 (sF 0x38 48 (by omega)),
      load_frame2 fr2 (sF 0x38 8 (by omega)) sHo, load_frame2 fr1 (sF 0x38 8 (by omega)) sF0, hsl0 r o h]
  -- the epilogue
  obtain ⟨n6, c6, pc6, sp6, mem6, sv6, k6⟩ := sh_epi (v := reg m) s5 hc5 hFa sp5 hsl5
  have hiM5 : accV M5 hi 2 = accV M2 hi 2 := accV_congr 2 fun i hi' => memLoad32_congr fun t ht => by
    clear vF hacc hX accLo hW vL vH
    rw [add_ofNat_assoc]
    have hx : Sep (shF sp0) 0x90 (hi + BitVec.ofNat 32 (4 * i + t)) 1 := env.sH.symm.subR (by omega)
    have hl : Sep lo 48 (hi + BitVec.ofNat 32 (4 * i + t)) 1 := env.sLH.subR (by omega)
    rw [fr5 _ hl, fr4 _ (inF (by decide) hx) hl, fr3 _ (inF (by decide) hx)]
  have hiM1 : accV M1 hi 2 = accV m.mem hi 2 := accV_congr 2 fun i hi' => memLoad32_congr fun t ht => by
    clear vF hacc hX accLo hW vL vH hiM5
    rw [add_ofNat_assoc]
    rw [fr1 _ (inF (by decide) (env.sH.symm.subR (by omega)))
      (by have := inF (c := 0) (l := 8) (by decide) (env.sH.symm.subR (c := 4 * i + t) (l := 1) (by omega))
          rwa [add_ofNat_zero] at this)]
    exact fr0 _ (env.sH.symm.subR (by omega))
  have hsave : ∀ q : Fin 32, q.val ∈ [8, 9, 18, 19, 20, 21, 22, 23] → ∃ o, (q, o) ∈ shPs := fun q hq => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h | h | h | h | h | h | h <;> rw [show q = ⟨_, by decide⟩ from Fin.ext h]
    · exact ⟨0x88, by decide⟩
    · exact ⟨0x84, by decide⟩
    · exact ⟨0x80, by decide⟩
    · exact ⟨0x7C, by decide⟩
    · exact ⟨0x78, by decide⟩
    · exact ⟨0x74, by decide⟩
    · exact ⟨0x70, by decide⟩
    · exact ⟨0x6C, by decide⟩
  refine ⟨n6, c0.trans (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6))))), ?_, ?_, fun q hq => ?_, ?_,
    fun x hx hl hh => ?_⟩
  · rw [pc6, hra, hret]
  · rw [sp6, BitVec.add_assoc, show (0xFFFFFF70 : Word) + 0x90 = 0 by decide, add_lit_zero]
  · clear vF hacc hX accLo hW vL vH hiM5 hiM1
    by_cases hsv : q.val ∈ [8, 9, 18, 19, 20, 21, 22, 23]
    · obtain ⟨o, ho⟩ := hsave q hsv
      exact sv6 q o ho
    by_cases hsp' : q = sp
    · subst hsp'
      rw [sp6, hsp, BitVec.add_assoc, show (0xFFFFFF70 : Word) + 0x90 = 0 by decide, add_lit_zero]
    have hq' : q.val ∉ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] := by
      intro h; apply hsp'; apply Fin.ext
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at h hq hsv
      show q.val = 2; omega
    rw [k6 q (kk hq' (by decide)) hsp', k5 q (kk hq' (by decide)), kE q hq', k1 q (kk hq' (by decide))]
    exact k0 q (by simp only [shKeep, decide_eq_true_eq]; exact hq')
  · rw [mem6, vF, accLo, hX, hiM5, vH, hiM1]
    exact shFinal hs2
  · rw [mem6, fr5 x hl, fr4 x (inF (by decide) hx) hl]
    exact frA3 x hx hh

end C3.RV32
