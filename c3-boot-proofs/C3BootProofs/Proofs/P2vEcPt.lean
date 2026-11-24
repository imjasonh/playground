import C3BootProofs.Proofs.P2vIvLib
import C3BootProofs.Proofs.P256Defs

/-!
# `p256VerifyPrehash`: scalar products and points in the frame

The calls of the P-256 check that work on scalars and points in
`p256VerifyPrehash`'s frame: the scalar field's `mul`, which computes `u₁`
and `u₂` from the inverse of `s`, and the point doubling and addition, on
points whose three coordinates are 8-limb values in Montgomery form.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Sv

set_option maxRecDepth 100000

theorem codeIn_eq {M : Word → BitVec 8} {a b : Word} {c : List Nat} (hc : CodeIn M b c) (h : a = b) :
    CodeIn M a c := h ▸ hc

set_option maxHeartbeats 8000000 in
/-- **A call to the P-256 scalar field's `mul`** of the scalars at offsets
`ca` and `cb`, into offset `co`. -/
theorem p2v_psmF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co ca cb : Nat}
    (F : Fr B 0x3590) (C : P2vCode M) (hpm : CodeIn M (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode)
    (hwm : CodeIn M (BitVec.ofNat 32 wideMulAddress) wideMulCode) (st : St M P2V n off (reg n))
    (h1 : fetchRel p256VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P2V + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 p256ScalarMulAddress)
    (hev : (P2V + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 ca)
    (ha2 : reg n a2 = B + 0x21A0 + BitVec.ofNat 32 cb)
    (hco : co + 32 ≤ 0x13F0) (hca : ca + 32 ≤ 0x13F0) (hcb : cb + 32 ≤ 0x13F0)
    (aco : co % 4 = 0) (aca : ca % 4 = 0) (acb : cb % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem P2V n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 =
        psmVal (accV M (B + 0x21A0 + BitVec.ofNat 32 ca) 8 * accV M (B + 0x21A0 + BitVec.ofNat 32 cb) 8) ∧
      P2vKeepL B M n'.mem [(co, 32)] ∧ (∀ x, P2vR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x13F0 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hGn : (B + 0x21A0 + BitVec.ofNat 32 (2 ^ 32 - 0x100)).toNat = (B + 0x21A0).toNat - 0x100 :=
    FS.below 0x100 (by decide) (by decide)
  have EN : PSMEnv n1.mem (BitVec.ofNat 32 p256ScalarMulAddress) (B + 0x21A0 + 0xFFFFFF00)
      (B + 0x21A0 + BitVec.ofNat 32 co) (B + 0x21A0 + BitVec.ofNat 32 ca) (B + 0x21A0 + BitVec.ofNat 32 cb) := by
    rw [mem1]
    refine ⟨by decide, hpm, ?_, ?_, ?_, ?_, ?_,
      by rw [show (0xFFFFFF00 : Word) = BitVec.ofNat 32 (2 ^ 32 - 0x100) from rfl, hGn, hS]; omega,
      by rw [show (0xFFFFFF00 : Word) = BitVec.ofNat 32 (2 ^ 32 - 0x100) from rfl, hGn, hS]; omega,
      p2v_al F (by omega) aco, p2v_al F (by omega) aca, p2v_al F (by omega) acb,
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowN (k := 0x100) (by decide) (by decide) hca, FS.lowN (k := 0x100) (by decide) (by decide) hcb,
      FS.lowN (k := 0x100) (by decide) (by decide) hco,
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide)⟩
    · exact codeIn_eq hwm (by decide)
    · exact codeIn_eq C.K.mset (by decide)
    · exact codeIn_eq C.K.stub (by decide)
    · exact codeIn_eq C.K.body (by decide)
    · exact codeIn_eq C.K.bsub (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, W2, f2⟩ := p256ScalarMul_correct n1 EN pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
    (by rw [r1 sp (by decide), rsp, BitVec.add_assoc, show (0xFFFFFF00 : Word) + 0x100 = 0 from rfl]
        exact (BitVec.add_zero _).symm)
  rw [mem1] at W2 f2
  have e1 : B + 0x21A0 + 0xFFFFFF00 = B + BitVec.ofNat 32 0x20A0 := p2v_spX B 0x100 (by decide)
  rw [e1] at f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩,
    by rw [sp2, BitVec.add_assoc, show (0xFFFFFF00 : Word) + 0x100 = 0 from rfl]; exact BitVec.add_zero _,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)],
    accV_of_toNats 8 W2, fun e he hL => ?_,
    fun x hx => f2 x (p2vR_spX hx (by decide) (by decide) (by decide)) (p2vR_hi hx hco)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact f2 _ (by rw [← p2v_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

/-- Limbs inside a run of frame bytes copied from `p`. -/
theorem acc_of_frame_at {M M0 : Word → BitVec 8} {B p : Word} {c d n N : Nat}
    (h : ∀ j, j < N → M (B + 0x21A0 + BitVec.ofNat 32 (c + j)) = M0 (p + BitVec.ofNat 32 j)) (hd : d + 4 * n ≤ N) :
    accV M (B + 0x21A0 + BitVec.ofNat 32 (c + d)) n = accV M0 (p + BitVec.ofNat 32 d) n :=
  acc_of_bytes fun j hj => by
    rw [add_ofNat_assoc, add_ofNat_assoc, show c + d + j = c + (d + j) by omega]; exact h _ (by omega)

/-- The code the point doubling and addition run, and the curve constant
`b` in Montgomery form. -/
structure P2vPtCode (M : Word → BitVec 8) : Prop where
  pd : CodeIn M (BitVec.ofNat 32 p256PtDoubleAddress) p256PtDoubleCode
  pa : CodeIn M (BitVec.ofNat 32 pointAddAddress) pointAddCode
  mul : CodeIn M (BitVec.ofNat 32 fieldMulAddress) fieldMulCode
  wm : CodeIn M (BitVec.ofNat 32 wideMulAddress) wideMulCode
  si : CodeIn M (BitVec.ofNat 32 subInnerAddress) subInnerCode
  add : CodeIn M (BitVec.ofNat 32 fieldAddAddress) fieldAddCode
  sub : CodeIn M (BitVec.ofNat 32 fieldSubAddress) fieldSubCode
  dbl : CodeIn M (BitVec.ofNat 32 fieldDoubleAddress) fieldDoubleCode
  sqr : CodeIn M (BitVec.ofNat 32 fieldSquareAddress) fieldSquareCode
  b : accV M bAddr 8 = bMont

theorem P2vPtCode.p2v {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3590) (D : P2vPtCode M0)
    (fR : ∀ x, P2vR B x → M x = M0 x) : P2vPtCode M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  exact ⟨codeHi D.pd (by decide) (by decide) hx, codeHi D.pa (by decide) (by decide) hx,
    codeHi D.mul (by decide) (by decide) hx, codeHi D.wm (by decide) (by decide) hx,
    codeHi D.si (by decide) (by decide) hx, codeHi D.add (by decide) (by decide) hx,
    codeHi D.sub (by decide) (by decide) hx, codeHi D.dbl (by decide) (by decide) hx,
    codeHi D.sqr (by decide) (by decide) hx, by rw [accV_dataR F fR (by decide) (by decide)]; exact D.b⟩

theorem ptF_lt {M : Word → BitVec 8} {B : Word} {c : Nat} {P : Pt2} (h : ptF M B c = P) (hP : Pt2Lt P) :
    limbVal (wordsAt M (B + 0x21A0 + BitVec.ofNat 32 c) 8) < p256 ∧
      limbVal (wordsAt M (B + 0x21A0 + BitVec.ofNat 32 c + 0x20) 8) < p256 ∧
      limbVal (wordsAt M (B + 0x21A0 + BitVec.ofNat 32 c + 0x40) 8) < p256 := by
  subst h
  rw [limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt, add_lit20, add_lit40]
  exact hP

set_option maxHeartbeats 16000000 in
/-- **A call to the P-256 point doubling** of the point at offset `cs`, into
offset `co`. -/
theorem p2v_pd2F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co cs : Nat} {P : Pt2}
    (F : Fr B 0x3590) (C : P2vCode M) (PC : P2vPtCode M) (st : St M P2V n off (reg n))
    (h1 : fetchRel p256VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P2V + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 p256PtDoubleAddress)
    (hev : (P2V + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cs)
    (hco : co + 96 ≤ 0x13F0) (hcs : cs + 96 ≤ 0x13F0) (aco : co % 4 = 0) (acs : cs % 4 = 0)
    (hP : ptF M B cs = P) (hlt : Pt2Lt P) :
    ∃ n', Steps n n' ∧ St n'.mem P2V n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      ptF n'.mem B co = ptDbl2 P ∧ P2vKeepL B M n'.mem [(co, 96)] ∧ (∀ x, P2vR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x13F0 := F.sub (c := 0x21A0) (by decide) (by decide)
  have eD : d2S (B + 0x21A0) = B + BitVec.ofNat 32 0x1D90 := p2v_spX B 0x410 (by decide)
  have gH : ∀ {b : Word} {len : Nat}, 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 →
      Sep (d2S (B + 0x21A0)) 0x410 b len := fun h1 h2 => by rw [eD]; exact F.sepHi (by decide) h1 h2
  obtain ⟨lx, ly, lz⟩ := ptF_lt hP hlt
  have EN : D2Env n1.mem (BitVec.ofNat 32 p256PtDoubleAddress) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 co)
      (B + 0x21A0 + BitVec.ofNat 32 cs) := by
    rw [mem1]
    refine ⟨by decide, PC.pd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [limbVal_wordsAt]; exact PC.b,
      by rw [hS]; omega, by rw [hS]; omega, p2v_al F (by omega) acs, p2v_al F (by omega) aco,
      by rw [p2v_at F _ (by omega)]; omega,
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      by rw [eD]; exact F.bufData (by decide) (by decide) (by decide),
      by rw [eD, ← p2v_base']; exact sepS B (by omega) (by omega) (by omega),
      by rw [eD, ← p2v_base']; exact sepS B (by omega) (by omega) (by omega),
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide)⟩
    · exact codeIn_eq PC.mul (by decide)
    · exact codeIn_eq PC.wm (by decide)
    · exact codeIn_eq C.K.mset (by decide)
    · exact codeIn_eq C.K.stub (by decide)
    · exact codeIn_eq C.K.body (by decide)
    · exact codeIn_eq PC.si (by decide)
    · exact codeIn_eq C.K.bsub (by decide)
    · exact codeIn_eq PC.add (by decide)
    · exact codeIn_eq PC.sub (by decide)
    · exact codeIn_eq PC.dbl (by decide)
    · exact codeIn_eq PC.sqr (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, V2, f2⟩ := p256PtDouble_correct n1 EN pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev) (by rw [r1 sp (by decide), rsp]) (by rw [mem1]; exact lx) (by rw [mem1]; exact ly)
    (by rw [mem1]; exact lz)
  rw [mem1, eD] at f2
  rw [mem1, limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt,
    add_lit20, add_lit40, add_lit20, add_lit40] at V2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_, ?_,
    fun e he hL => ?_, fun x hx => f2 x (p2vR_spX hx (by decide) (by decide) (by decide)) (p2vR_hi hx hco)⟩
  · have hq' := hq
    rw [k2 q (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide)
      (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide)
      (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide)
      (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide)
      (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide),
      r1 q (by revert hq; revert q; decide)]
  · rw [← hP]; unfold ptF ptDbl2; exact V2
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [← p2v_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

set_option maxHeartbeats 16000000 in
/-- **A call to the P-256 point addition** of the point at offset `cr` to the
one at `cl`, in place. -/
theorem p2v_pa2F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {cl cr : Nat}
    {P Q : Pt2} (F : Fr B 0x3590) (C : P2vCode M) (PC : P2vPtCode M) (st : St M P2V n off (reg n))
    (h1 : fetchRel p256VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P2V + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 pointAddAddress)
    (hev : (P2V + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 cl) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cr)
    (hcl : cl + 96 ≤ 0x13F0) (hcr : cr + 96 ≤ 0x13F0) (acl : cl % 4 = 0) (acr : cr % 4 = 0)
    (hP : ptF M B cl = P) (hQ : ptF M B cr = Q) (hlP : Pt2Lt P) (hlQ : Pt2Lt Q) :
    ∃ n', Steps n n' ∧ St n'.mem P2V n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      ptF n'.mem B cl = ptAdd2 P Q ∧ P2vKeepL B M n'.mem [(cl, 96)] ∧ (∀ x, P2vR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x13F0 := F.sub (c := 0x21A0) (by decide) (by decide)
  have eD : B + 0x21A0 + (0xFFFFFC90 : Word) = B + BitVec.ofNat 32 0x1E30 := p2v_spX B 0x370 (by decide)
  have gH : ∀ {b : Word} {len : Nat}, 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 →
      Sep (B + 0x21A0 + 0xFFFFFC90) 0x370 b len := fun h1 h2 => by rw [eD]; exact F.sepHi (by decide) h1 h2
  obtain ⟨lx, ly, lz⟩ := ptF_lt hP hlP
  obtain ⟨rx, ry, rz⟩ := ptF_lt hQ hlQ
  have lH : ∀ {b : Word} {len : Nat}, 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 →
      Sep (B + 0x21A0 + BitVec.ofNat 32 cl) 96 b len := fun h1 h2 => FS.sepHi hcl h1 h2
  have EN : PAEnv n1.mem (BitVec.ofNat 32 pointAddAddress) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 cl)
      (B + 0x21A0 + BitVec.ofNat 32 cr) := by
    rw [mem1]
    refine ⟨by decide, PC.pa, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [limbVal_wordsAt]; exact PC.b,
      by rw [hS]; omega, by rw [hS]; omega, p2v_al F (by omega) acl, p2v_al F (by omega) acr,
      by rw [p2v_at F _ (by omega)]; omega,
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      by rw [eD]; exact (F.bufData (by decide) (by decide) (by decide)).symm,
      by rw [eD, ← p2v_base']; exact sepS B (by omega) (by omega) (by omega),
      by rw [eD, ← p2v_base']; exact sepS B (by omega) (by omega) (by omega),
      lH (by decide) (by decide), lH (by decide) (by decide), lH (by decide) (by decide), lH (by decide) (by decide),
      lH (by decide) (by decide), lH (by decide) (by decide), lH (by decide) (by decide), lH (by decide) (by decide),
      lH (by decide) (by decide), lH (by decide) (by decide), lH (by decide) (by decide)⟩
    · exact codeIn_eq PC.mul (by decide)
    · exact codeIn_eq PC.wm (by decide)
    · exact codeIn_eq C.K.mset (by decide)
    · exact codeIn_eq C.K.stub (by decide)
    · exact codeIn_eq C.K.body (by decide)
    · exact codeIn_eq PC.si (by decide)
    · exact codeIn_eq C.K.bsub (by decide)
    · exact codeIn_eq PC.add (by decide)
    · exact codeIn_eq PC.sub (by decide)
    · exact codeIn_eq PC.dbl (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, V2, f2⟩ := pointAdd_correct n1 EN pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev) (by rw [r1 sp (by decide), rsp]) (by rw [mem1]; exact lx) (by rw [mem1]; exact ly)
    (by rw [mem1]; exact lz) (by rw [mem1]; exact rx) (by rw [mem1]; exact ry) (by rw [mem1]; exact rz)
  rw [mem1, eD] at f2
  rw [mem1] at V2
  simp only [limbVal_wordsAt, add_lit20, add_lit40] at V2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_, ?_,
    fun e he hL => ?_, fun x hx => f2 x (p2vR_spX hx (by decide) (by decide) (by decide)) (p2vR_hi hx hcl)⟩
  · have hq' := hq
    rw [k2 q (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide)
      (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide)
      (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide)
      (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide)
      (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide),
      r1 q (by revert hq; revert q; decide)]
  · rw [← hP, ← hQ]; unfold ptF ptAdd2; exact V2
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [← p2v_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

/-- A point survives a step that wrote elsewhere. -/
theorem P2vKeep.pt {B : Word} {M M' : Word → BitVec 8} {c w d : Nat} (K : P2vKeep B M M' c w)
    (hd : d + 96 ≤ 0x13F0) (h : d + 96 ≤ c ∨ c + w ≤ d) : ptF M' B d = ptF M B d := by
  unfold ptF
  rw [K.acc (n := 8) (by omega) (by omega), K.acc (n := 8) (by omega) (by omega), K.acc (n := 8) (by omega) (by omega)]

theorem P2vKeepL.pt {B : Word} {M M' : Word → BitVec 8} {L : List (Nat × Nat)} {d : Nat} (K : P2vKeepL B M M' L)
    (hd : d + 96 ≤ 0x13F0) (h : ∀ p ∈ L, d + 96 ≤ p.1 ∨ p.1 + p.2 ≤ d) : ptF M' B d = ptF M B d := by
  unfold ptF
  rw [K.acc (n := 8) (by omega) (fun p hp => by have := h p hp; omega),
    K.acc (n := 8) (by omega) (fun p hp => by have := h p hp; omega),
    K.acc (n := 8) (by omega) (fun p hp => by have := h p hp; omega)]

/-- A point moves with a copy of the bytes that hold it. -/
theorem ptF_cp {B : Word} {M M' : Word → BitVec 8} {dst src N c d : Nat}
    (X : ∀ j, j < N → M' (B + 0x21A0 + BitVec.ofNat 32 (dst + j)) = M (B + 0x21A0 + BitVec.ofNat 32 (src + j)))
    (h1 : src ≤ c) (h2 : c + 96 ≤ src + N) (hd : d + src = c + dst) : ptF M' B d = ptF M B c := by
  have e : ∀ o, o + 32 ≤ 96 → accV M' (B + 0x21A0 + BitVec.ofNat 32 (d + o)) 8 =
      accV M (B + 0x21A0 + BitVec.ofNat 32 (c + o)) 8 := fun o ho => accV_S 8 fun q hq => by
    have := X (c - src + o + q) (by omega)
    rwa [show dst + (c - src + o + q) = d + o + q by omega, show src + (c - src + o + q) = c + o + q by omega] at this
  unfold ptF
  have e0 := e 0 (by decide)
  rw [Nat.add_zero, Nat.add_zero] at e0
  rw [e0, e 0x20 (by decide), e 0x40 (by decide)]

end C3.RV32.P2v
