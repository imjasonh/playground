import C3BootProofs.Proofs.SvEcLib2
import C3BootProofs.Proofs.P256PtDouble
import C3BootProofs.Proofs.PointAdd

/-!
# `sigstore::verify`: P-256 points in the frame

The point doubling and addition the P-256 check calls, from
`sigstore::verify`'s frame, on points whose three coordinates are 8-limb
values in Montgomery form.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

/-- A P-256 point in projective Montgomery coordinates. -/
abbrev Pt2 := Nat × Nat × Nat

/-- Each coordinate is below the field's modulus. -/
def Pt2Lt (P : Pt2) : Prop := P.1 < p256 ∧ P.2.1 < p256 ∧ P.2.2 < p256

/-- The compiled point addition. -/
def ptAdd2 (P Q : Pt2) : Pt2 := ptAddSpec bMont P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2

/-- The compiled point doubling. -/
def ptDbl2 (P : Pt2) : Pt2 := p2Dbl bMont P.1 P.2.1 P.2.2

theorem ptAdd2_lt (P Q : Pt2) : Pt2Lt (ptAdd2 P Q) := by
  unfold Pt2Lt ptAdd2 ptAddSpec
  simp only [C3.RV32.fm, C3.RV32.fa, C3.RV32.fs, C3.RV32.fd]
  exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

theorem ptDbl2_lt (P : Pt2) : Pt2Lt (ptDbl2 P) := by
  unfold Pt2Lt ptDbl2 p2Dbl
  simp only [C3.RV32.fm, C3.RV32.fa, C3.RV32.fs, C3.RV32.fd]
  exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

/-- The table of odd multiples `P, 3P, 5P, …` the check builds: entry `j` is
`P + j·2P`. -/
def tbl2 (P : Pt2) : Nat → Pt2
  | 0 => P
  | j + 1 => ptAdd2 (tbl2 P j) (ptDbl2 P)

theorem tbl2_lt {P : Pt2} (h : Pt2Lt P) : ∀ j, Pt2Lt (tbl2 P j)
  | 0 => h
  | _ + 1 => ptAdd2_lt _ _

/-- The point the frame holds at offset `c`. -/
def ptF (M : Word → BitVec 8) (B : Word) (c : Nat) : Pt2 :=
  (accV M (B + 0x21A0 + BitVec.ofNat 32 c) 8, accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x20)) 8,
    accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x40)) 8)

theorem add_lit40 (S : Word) (c : Nat) : S + BitVec.ofNat 32 c + 0x40 = S + BitVec.ofNat 32 (c + 0x40) :=
  add_ofNat_assoc S c 0x40

/-- The code the point doubling and addition run, and the curve constant
`b` in Montgomery form. -/
structure SvPtCode (M : Word → BitVec 8) : Prop where
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

theorem SvPtCode.sv {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (D : SvPtCode M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : SvPtCode M := by
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
theorem sv_pd2F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co cs : Nat} {P : Pt2}
    (F : Fr B 0x3830) (C : SvCode M) (PC : SvPtCode M) (st : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 p256PtDoubleAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cs)
    (hco : co + 96 ≤ 0x1690) (hcs : cs + 96 ≤ 0x1690) (aco : co % 4 = 0) (acs : cs % 4 = 0)
    (hP : ptF M B cs = P) (hlt : Pt2Lt P) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      ptF n'.mem B co = ptDbl2 P ∧ SvKeepL B M n'.mem [(co, 96)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have eD : d2S (B + 0x21A0) = B + BitVec.ofNat 32 0x1D90 := sv_spX B 0x410 (by decide)
  have gH : ∀ {b : Word} {len : Nat}, 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 →
      Sep (d2S (B + 0x21A0)) 0x410 b len := fun h1 h2 => by rw [eD]; exact F.sepHi (by decide) h1 h2
  obtain ⟨lx, ly, lz⟩ := ptF_lt hP hlt
  have EN : D2Env n1.mem (BitVec.ofNat 32 p256PtDoubleAddress) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 co)
      (B + 0x21A0 + BitVec.ofNat 32 cs) := by
    rw [mem1]
    refine ⟨by decide, PC.pd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [limbVal_wordsAt]; exact PC.b,
      by rw [hS]; omega, by rw [hS]; omega, sv_al F (by omega) acs, sv_al F (by omega) aco,
      by rw [sv_at F _ (by omega)]; omega,
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      by rw [eD]; exact F.bufData (by decide) (by decide) (by decide),
      by rw [eD, ← sv_base']; exact sepS B (by omega) (by omega) (by omega),
      by rw [eD, ← sv_base']; exact sepS B (by omega) (by omega) (by omega),
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide)⟩
    · rw [show BitVec.ofNat 32 p256PtDoubleAddress + 0xF312 = BitVec.ofNat 32 fieldMulAddress by decide]; exact PC.mul
    · rw [show BitVec.ofNat 32 p256PtDoubleAddress + 0xB056 = BitVec.ofNat 32 wideMulAddress by decide]; exact PC.wm
    · rw [show BitVec.ofNat 32 p256PtDoubleAddress + 0x1249C = MSET by decide]; exact C.K.mset
    · rw [show BitVec.ofNat 32 p256PtDoubleAddress + 0x12504 = MCS by decide]; exact C.K.stub
    · rw [show BitVec.ofNat 32 p256PtDoubleAddress + 0x1250C = MCS + 8 by decide]; exact C.K.body
    · rw [show BitVec.ofNat 32 p256PtDoubleAddress + 0xF71E = BitVec.ofNat 32 subInnerAddress by decide]; exact PC.si
    · rw [show siBsub (BitVec.ofNat 32 p256PtDoubleAddress + 0xF71E) = BSUB by decide]; exact C.K.bsub
    · rw [show BitVec.ofNat 32 p256PtDoubleAddress + 0xFAD8 = BitVec.ofNat 32 fieldAddAddress by decide]; exact PC.add
    · rw [show BitVec.ofNat 32 p256PtDoubleAddress + 0xFBFA = BitVec.ofNat 32 fieldSubAddress by decide]; exact PC.sub
    · rw [show BitVec.ofNat 32 p256PtDoubleAddress + 0xFDF4 = BitVec.ofNat 32 fieldDoubleAddress by decide]
      exact PC.dbl
    · rw [show BitVec.ofNat 32 p256PtDoubleAddress + 0xFDFE = BitVec.ofNat 32 fieldSquareAddress by decide]
      exact PC.sqr
  obtain ⟨n2, c2, pc2, sp2, k2, V2, f2⟩ := p256PtDouble_correct n1 EN pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev) (by rw [r1 sp (by decide), rsp]) (by rw [mem1]; exact lx) (by rw [mem1]; exact ly)
    (by rw [mem1]; exact lz)
  rw [mem1, eD] at f2
  rw [mem1, limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt,
    add_lit20, add_lit40, add_lit20, add_lit40] at V2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_, ?_,
    fun e he hL => ?_, fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx hco)⟩
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
    exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

set_option maxHeartbeats 16000000 in
/-- **A call to the P-256 point addition** of the point at offset `cr` to the
one at `cl`, in place. -/
theorem sv_pa2F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {cl cr : Nat}
    {P Q : Pt2} (F : Fr B 0x3830) (C : SvCode M) (PC : SvPtCode M) (st : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 pointAddAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 cl) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cr)
    (hcl : cl + 96 ≤ 0x1690) (hcr : cr + 96 ≤ 0x1690) (acl : cl % 4 = 0) (acr : cr % 4 = 0)
    (hP : ptF M B cl = P) (hQ : ptF M B cr = Q) (hlP : Pt2Lt P) (hlQ : Pt2Lt Q) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      ptF n'.mem B cl = ptAdd2 P Q ∧ SvKeepL B M n'.mem [(cl, 96)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have eD : B + 0x21A0 + (0xFFFFFC90 : Word) = B + BitVec.ofNat 32 0x1E30 := sv_spX B 0x370 (by decide)
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
      by rw [hS]; omega, by rw [hS]; omega, sv_al F (by omega) acl, sv_al F (by omega) acr,
      by rw [sv_at F _ (by omega)]; omega,
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      by rw [eD]; exact (F.bufData (by decide) (by decide) (by decide)).symm,
      by rw [eD, ← sv_base']; exact sepS B (by omega) (by omega) (by omega),
      by rw [eD, ← sv_base']; exact sepS B (by omega) (by omega) (by omega),
      lH (by decide) (by decide), lH (by decide) (by decide), lH (by decide) (by decide), lH (by decide) (by decide),
      lH (by decide) (by decide), lH (by decide) (by decide), lH (by decide) (by decide), lH (by decide) (by decide),
      lH (by decide) (by decide), lH (by decide) (by decide), lH (by decide) (by decide)⟩
    · rw [show BitVec.ofNat 32 pointAddAddress + 0xF0BE = BitVec.ofNat 32 fieldMulAddress by decide]; exact PC.mul
    · rw [show BitVec.ofNat 32 pointAddAddress + 0xAE02 = BitVec.ofNat 32 wideMulAddress by decide]; exact PC.wm
    · rw [show BitVec.ofNat 32 pointAddAddress + 0x12248 = MSET by decide]; exact C.K.mset
    · rw [show BitVec.ofNat 32 pointAddAddress + 0x122B0 = MCS by decide]; exact C.K.stub
    · rw [show BitVec.ofNat 32 pointAddAddress + 0x122B8 = MCS + 8 by decide]; exact C.K.body
    · rw [show BitVec.ofNat 32 pointAddAddress + 0xF4CA = BitVec.ofNat 32 subInnerAddress by decide]; exact PC.si
    · rw [show siBsub (BitVec.ofNat 32 pointAddAddress + 0xF4CA) = BSUB by decide]; exact C.K.bsub
    · rw [show BitVec.ofNat 32 pointAddAddress + 0xF884 = BitVec.ofNat 32 fieldAddAddress by decide]; exact PC.add
    · rw [show BitVec.ofNat 32 pointAddAddress + 0xF9A6 = BitVec.ofNat 32 fieldSubAddress by decide]; exact PC.sub
    · rw [show BitVec.ofNat 32 pointAddAddress + 0xFBA0 = BitVec.ofNat 32 fieldDoubleAddress by decide]; exact PC.dbl
  obtain ⟨n2, c2, pc2, sp2, k2, V2, f2⟩ := pointAdd_correct n1 EN pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev) (by rw [r1 sp (by decide), rsp]) (by rw [mem1]; exact lx) (by rw [mem1]; exact ly)
    (by rw [mem1]; exact lz) (by rw [mem1]; exact rx) (by rw [mem1]; exact ry) (by rw [mem1]; exact rz)
  rw [mem1, eD] at f2
  rw [mem1] at V2
  simp only [limbVal_wordsAt, add_lit20, add_lit40] at V2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_, ?_,
    fun e he hL => ?_, fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx hcl)⟩
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
    exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

end C3.RV32.Sv
