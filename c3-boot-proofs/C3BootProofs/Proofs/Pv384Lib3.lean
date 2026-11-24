import C3BootProofs.Proofs.Pv384Lib2
import C3BootProofs.Proofs.P384PtAdd
import C3BootProofs.Proofs.P384PtDouble

/-!
# `p384_verify_prehash`: the calls of the linear combination

Wrappers, in the terms of `Pv384Lib.lean`, for the calls that compute
`u₁·G + u₂·Q`: the scalar multiplications that make `u₁` and `u₂`, and the
point doubling and addition of the tables and the main loop.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- The functions the linear combination and the final steps call. -/
structure PvCode4 (M : Word → BitVec 8) : Prop where
  sm : CodeIn M (BitVec.ofNat 32 p384ScalarMulAddress) p384ScalarMulCode
  pa : CodeIn M (BitVec.ofNat 32 p384PtAddAddress) p384PtAddCode
  pd : CodeIn M (BitVec.ofNat 32 p384PtDoubleAddress) p384PtDoubleCode
  sub : CodeIn M (BitVec.ofNat 32 p384SubAddress) p384SubCode
  dbl : CodeIn M (BitVec.ofNat 32 p384DoubleAddress) p384DoubleCode
  sqr : CodeIn M (BitVec.ofNat 32 p384SqrAddress) p384SqrCode
  sqm : CodeIn M (BitVec.ofNat 32 sqMont12Address) sqMont12Code

theorem PvCode4.hi {M M' : Word → BitVec 8} (C : PvCode4 M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    PvCode4 M' :=
  ⟨codeHi C.sm (by decide) (by decide) h, codeHi C.pa (by decide) (by decide) h,
    codeHi C.pd (by decide) (by decide) h, codeHi C.sub (by decide) (by decide) h,
    codeHi C.dbl (by decide) (by decide) h, codeHi C.sqr (by decide) (by decide) h,
    codeHi C.sqm (by decide) (by decide) h⟩

/-- Everything the stages after the inversion of `s` need. -/
structure PvEnv4 (M : Word → BitVec 8) : Prop where
  E : PvEnv3 M
  C4 : PvCode4 M

theorem PvEnv4.fr {B : Word} {M M' : Word → BitVec 8} (E : PvEnv4 M) (F : Fr B 0x21A0)
    (h : ∀ x, PvR B x → M' x = M x) : PvEnv4 M' :=
  ⟨E.E.fr F h, E.C4.hi fun x hx => h x (pvR_of_hi F hx)⟩

set_option maxHeartbeats 8000000 in
/-- A call to `ConstMontyForm<p384::ScalarParams, 12>::mul`: the Montgomery
product of the limbs at offsets `cx` and `cy` of the frame, at `co`. -/
theorem pv_smul {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cx cy : Nat} (F : Fr B 0x21A0)
    (E : PvEnv4 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 p384ScalarMulAddress)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cx) (ha2 : reg m a2 = B + 0x420 + BitVec.ofNat 32 cy)
    (hco : co + 48 ≤ 0x1D4C) (hcx : cx + 48 ≤ 0x1D4C) (hcy : cy + 48 ≤ 0x1D4C)
    (aco : co % 4 = 0) (acx : cx % 4 = 0) (acy : cy % 4 = 0)
    (hB : accV m.mem (B + 0x420 + BitVec.ofNat 32 cy) 12 < n384) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 48 ∧
      accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12 =
        n3fm (accV m.mem (B + 0x420 + BitVec.ofNat 32 cx) 12) (accV m.mem (B + 0x420 + BitVec.ofNat 32 cy) 12) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  have hbF : (B + 0x420 + 0xFFFFFF10).toNat = (B + 0x420).toNat - 0xF0 := FS.below 0xF0 (by decide) (by decide)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + 0xFFFFFF10) 0xF0 b l := fun b l hb hl => FS.lowHi (by decide) rfl hb hl
  have EN : N3MEnv n1.mem (BitVec.ofNat 32 p384ScalarMulAddress) (B + 0x420) (B + 0x420 + BitVec.ofNat 32 co)
      (B + 0x420 + BitVec.ofNat 32 cx) (B + 0x420 + BitVec.ofNat 32 cy) := by
    rw [mem1]
    refine ⟨by decide, E.C4.sm, E.E.E.D2.nmod, ?_⟩
    refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega, by rw [FS.at _ (by omega)]; omega,
      by rw [FS.at _ (by omega)]; omega, by rw [FS.at _ (by omega)]; omega, by decide,
      by rw [FS.at _ (by omega)]; omega,
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      FS.lowN (k := 0xF0) (by decide) (by decide) (by omega), FS.sepHi (by omega) (by decide) (by decide),
      FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide),
      FS.lowN (k := 0xF0) (by decide) (by decide) (by omega), FS.lowN (k := 0xF0) (by decide) (by decide) (by omega),
      pv_lowK F (n := 48) (k := 0xF0) (by decide) (by decide) (by decide)⟩
    · rw [show BitVec.ofNat 32 p384ScalarMulAddress + 0xFFFFEF58 = MM by decide]; exact E.E.E.C.K.mm
    · rw [show BitVec.ofNat 32 p384ScalarMulAddress + 0xFFFFEF58 + 0x1B0C = MSET by decide]; exact E.E.E.C.K.mset
    · rw [show mmBsub (BitVec.ofNat 32 p384ScalarMulAddress + 0xFFFFEF58) = BSUB by decide]; exact E.E.E.C.K.bsub
    · rw [show BitVec.ofNat 32 p384ScalarMulAddress + 0xFFFFEF58 + 0x18E = SEL by decide]; exact E.E.E.C.K.sel
    · rw [show BitVec.ofNat 32 p384ScalarMulAddress + 0xFFFFEF58 + 0x1B74 = MCS by decide]; exact E.E.E.C.K.stub
    · rw [show BitVec.ofNat 32 p384ScalarMulAddress + 0xFFFFEF58 + 0x1B7C = MCS + 8 by decide]; exact E.E.E.C.K.body
  obtain ⟨n2, c2, pc2, sp2, k2, val2, fr2⟩ := p384ScalarMul_correct n1 EN pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) (by rw [r1 sp (by decide)]; exact hsp) (by rw [mem1]; exact hB)
  rw [mem1] at val2 fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0xF0) hx (by decide) (by decide))
      (pvR_hi hx hco), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 0xF0) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), val2⟩
  by_cases h : q = sp
  · subst h; rw [sp2, hsp]
  · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]

/-- Constants against the stack below `sp`, as far as the frame reaches. -/
theorem pv_lowD {B K : Word} (F : Fr B 0x21A0) {n k : Nat} (hk : k ≤ 0x5C0) (hK : (img% dataWindowAddress) ≤ K.toNat)
    (hK' : K.toNat + n ≤ (img% dataWindowAddress + dataWindowSize)) : Sep K n (B + 0x420 + BitVec.ofNat 32 (2 ^ 32 - k)) k := by
  have h1 := F.dsep.sub (c := 0x5C0 - k) (l := k) (by omega)
  have h2 := h1.subR (c := K.toNat - (img% dataWindowAddress)) (l := n) (by omega)
  rw [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x5C0 - k) = B + 0x420 + BitVec.ofNat 32 (2 ^ 32 - k) by
    rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl, show (0x420 : Word).toNat = 0x420 from rfl]
    omega, show (img% dataWindowAddress : Word) + BitVec.ofNat 32 (K.toNat - (img% dataWindowAddress)) = K by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (img% dataWindowAddress : Word).toNat = (img% dataWindowAddress) from rfl]
    omega] at h2
  exact h2.symm

/-- A point in the frame: its three coordinates at `c`, `c + 0x30`, and
`c + 0x60`. -/
def ptV (M : Word → BitVec 8) (B : Word) (c : Nat) : Nat × Nat × Nat :=
  (accV M (B + 0x420 + BitVec.ofNat 32 c) 12, accV M (B + 0x420 + BitVec.ofNat 32 (c + 0x30)) 12,
    accV M (B + 0x420 + BitVec.ofNat 32 (c + 0x60)) 12)

/-- Every coordinate below `p`. -/
def PtLt (P : Nat × Nat × Nat) : Prop := P.1 < p384 ∧ P.2.1 < p384 ∧ P.2.2 < p384

theorem ptv30 {M : Word → BitVec 8} {B : Word} {c : Nat} :
    limbVal (wordsAt M (B + 0x420 + BitVec.ofNat 32 c + 0x30) 12) = accV M (B + 0x420 + BitVec.ofNat 32 (c + 0x30)) 12 := by
  rw [limbVal_wordsAt, show (0x30 : Word) = BitVec.ofNat 32 0x30 from rfl, add_ofNat_assoc]

theorem ptv60 {M : Word → BitVec 8} {B : Word} {c : Nat} :
    limbVal (wordsAt M (B + 0x420 + BitVec.ofNat 32 c + 0x60) 12) = accV M (B + 0x420 + BitVec.ofNat 32 (c + 0x60)) 12 := by
  rw [limbVal_wordsAt, show (0x60 : Word) = BitVec.ofNat 32 0x60 from rfl, add_ofNat_assoc]

set_option maxHeartbeats 16000000 in
/-- A call to the point doubling: `p3Dbl` of the point at offset `cx` of
the frame, at `co`. -/
theorem pv_pd {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cx : Nat} (F : Fr B 0x21A0)
    (E : PvEnv4 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 p384PtDoubleAddress)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cx) (hco : co + 144 ≤ 0x1D4C) (hcx : cx + 144 ≤ 0x1D4C)
    (aco : co % 4 = 0) (acx : cx % 4 = 0) (hx : accV m.mem (B + 0x420 + BitVec.ofNat 32 cx) 12 < p384)
    (hy : accV m.mem (B + 0x420 + BitVec.ofNat 32 (cx + 0x30)) 12 < p384)
    (hz : accV m.mem (B + 0x420 + BitVec.ofNat 32 (cx + 0x60)) 12 < p384) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 144 ∧
      (accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12, accV m'.mem (B + 0x420 + BitVec.ofNat 32 (co + 0x30)) 12,
        accV m'.mem (B + 0x420 + BitVec.ofNat 32 (co + 0x60)) 12) =
      p3Dbl p3B (accV m.mem (B + 0x420 + BitVec.ofNat 32 cx) 12) (accV m.mem (B + 0x420 + BitVec.ofNat 32 (cx + 0x30)) 12)
        (accV m.mem (B + 0x420 + BitVec.ofNat 32 (cx + 0x60)) 12) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (d3S (B + 0x420)) 0x540 b l := fun b l hb hl => pv_lowHi F (k := 0x540) (by decide) (by decide) hb hl
  have oh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + BitVec.ofNat 32 co) 144 b l := fun b l hb hl => FS.sepHi (by omega) hb hl
  have EN : D3Env n1.mem (BitVec.ofNat 32 p384PtDoubleAddress) (B + 0x420) (B + 0x420 + BitVec.ofNat 32 co)
      (B + 0x420 + BitVec.ofNat 32 cx) := by
    rw [mem1]
    refine ⟨by decide, E.C4.pd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, E.E.E.D.D.pmod, E.E.E.D.D.cb,
      by omega, by omega, pv_al F (by omega) acx, pv_al F (by omega) aco, pv_wr F (by omega),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), (pv_lowD F (k := 0x540) (by decide) (by decide) (by decide)).symm,
      (pv_lowD F (k := 0x540) (by decide) (by decide) (by decide)).symm,
      pv_lowS F (k := 0x540) (by omega) (by decide) (by decide), pv_lowS F (k := 0x540) (by omega) (by decide) (by decide),
      oh _ _ (by decide) (by decide), oh _ _ (by decide) (by decide)⟩
    · rw [show BitVec.ofNat 32 p384PtDoubleAddress + 0x11C82 = BitVec.ofNat 32 p384MulAddress by decide]
      exact E.E.E.C.K.p3mul
    · rw [show BitVec.ofNat 32 p384PtDoubleAddress + 0x12426 = BitVec.ofNat 32 p384SqrAddress by decide]
      exact E.C4.sqr
    · rw [show BitVec.ofNat 32 p384PtDoubleAddress + 0x110E0 = MM by decide]; exact E.E.E.C.K.mm
    · rw [show BitVec.ofNat 32 p384PtDoubleAddress + 0x11D8E = BitVec.ofNat 32 sqMont12Address by decide]
      exact E.C4.sqm
    · rw [show BitVec.ofNat 32 p384PtDoubleAddress + 0x53A = BitVec.ofNat 32 p384AddAddress by decide]
      exact E.E.E.C.K.p3add
    · rw [show BitVec.ofNat 32 p384PtDoubleAddress + 0x650 = BitVec.ofNat 32 p384SubAddress by decide]
      exact E.C4.sub
    · rw [show BitVec.ofNat 32 p384PtDoubleAddress + 0x1235E = BitVec.ofNat 32 p384DoubleAddress by decide]
      exact E.C4.dbl
    · rw [show BitVec.ofNat 32 p384PtDoubleAddress + 0x12BEC = MSET by decide]; exact E.E.E.C.K.mset
    · rw [show BitVec.ofNat 32 p384PtDoubleAddress + 0x726 = BSUB by decide]; exact E.E.E.C.K.bsub
    · rw [show BitVec.ofNat 32 p384PtDoubleAddress + 0x1126E = SEL by decide]; exact E.E.E.C.K.sel
    · rw [show BitVec.ofNat 32 p384PtDoubleAddress + 0x12C54 = MCS by decide]; exact E.E.E.C.K.stub
    · rw [show BitVec.ofNat 32 p384PtDoubleAddress + 0x12C5C = MCS + 8 by decide]; exact E.E.E.C.K.body
  obtain ⟨n2, c2, pc2, sp2, k2, val2, fr2⟩ := p384PtDouble_correct n1 EN pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) (by rw [r1 sp (by decide)]; exact hsp)
    (by rw [mem1, limbVal_wordsAt]; exact hx) (by rw [mem1, ptv30]; exact hy) (by rw [mem1, ptv60]; exact hz)
  rw [mem1] at val2 fr2
  simp only [ptv30, ptv60] at val2
  simp only [limbVal_wordsAt] at val2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0x540) hx (by decide) (by decide))
      (pvR_hi hx hco), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x540) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), val2⟩
  by_cases h : q = sp
  · subst h; rw [sp2, hsp]
  · rw [k2 q (by revert hq h; revert q; decide) (by revert hq h; revert q; decide) (by revert hq h; revert q; decide)
      (by revert hq h; revert q; decide) (by revert hq h; revert q; decide) (by revert hq h; revert q; decide)
      (by revert hq h; revert q; decide) (by revert hq h; revert q; decide) (by revert hq h; revert q; decide)
      (by revert hq h; revert q; decide) (by revert hq h; revert q; decide) (by revert hq h; revert q; decide)
      (by revert hq h; revert q; decide) (by revert hq h; revert q; decide) (by revert hq h; revert q; decide),
      r1 q (by revert hq; revert q; decide)]

set_option maxHeartbeats 16000000 in
/-- A call to the point addition: `p3Add` of the points at offsets `cl` and
`cr` of the frame, over the one at `cl`. -/
theorem pv_pa {B : Word} {m : Machine} {off : Nat} {imm o : Word} {cl cr : Nat} (F : Fr B 0x21A0)
    (E : PvEnv4 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 p384PtAddAddress)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 cl)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cr) (hcl : cl + 144 ≤ 0x1D4C) (hcr : cr + 144 ≤ 0x1D4C)
    (acl : cl % 4 = 0) (acr : cr % 4 = 0)
    (hx1 : accV m.mem (B + 0x420 + BitVec.ofNat 32 cl) 12 < p384)
    (hy1 : accV m.mem (B + 0x420 + BitVec.ofNat 32 (cl + 0x30)) 12 < p384)
    (hz1 : accV m.mem (B + 0x420 + BitVec.ofNat 32 (cl + 0x60)) 12 < p384)
    (hx2 : accV m.mem (B + 0x420 + BitVec.ofNat 32 cr) 12 < p384)
    (hy2 : accV m.mem (B + 0x420 + BitVec.ofNat 32 (cr + 0x30)) 12 < p384)
    (hz2 : accV m.mem (B + 0x420 + BitVec.ofNat 32 (cr + 0x60)) 12 < p384) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem cl 144 ∧
      (accV m'.mem (B + 0x420 + BitVec.ofNat 32 cl) 12, accV m'.mem (B + 0x420 + BitVec.ofNat 32 (cl + 0x30)) 12,
        accV m'.mem (B + 0x420 + BitVec.ofNat 32 (cl + 0x60)) 12) =
      p3Add p3B (accV m.mem (B + 0x420 + BitVec.ofNat 32 cl) 12) (accV m.mem (B + 0x420 + BitVec.ofNat 32 (cl + 0x30)) 12)
        (accV m.mem (B + 0x420 + BitVec.ofNat 32 (cl + 0x60)) 12) (accV m.mem (B + 0x420 + BitVec.ofNat 32 cr) 12)
        (accV m.mem (B + 0x420 + BitVec.ofNat 32 (cr + 0x30)) 12)
        (accV m.mem (B + 0x420 + BitVec.ofNat 32 (cr + 0x60)) 12) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (a3S (B + 0x420)) 0x440 b l := fun b l hb hl => pv_lowHi F (k := 0x440) (by decide) (by decide) hb hl
  have oh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + BitVec.ofNat 32 cl) 144 b l := fun b l hb hl => FS.sepHi (by omega) hb hl
  have EN : A3Env n1.mem (BitVec.ofNat 32 p384PtAddAddress) (B + 0x420) (B + 0x420 + BitVec.ofNat 32 cl)
      (B + 0x420 + BitVec.ofNat 32 cr) := by
    rw [mem1]
    refine ⟨by decide, E.C4.pa, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, E.E.E.D.D.pmod, E.E.E.D.D.cb,
      by omega, by omega, pv_al F (by omega) acl, pv_al F (by omega) acr, pv_wr F (by omega),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      (pv_lowD F (k := 0x440) (by decide) (by decide) (by decide)).symm,
      (pv_lowD F (k := 0x440) (by decide) (by decide) (by decide)).symm,
      pv_lowS F (k := 0x440) (by omega) (by decide) (by decide), pv_lowS F (k := 0x440) (by omega) (by decide) (by decide),
      oh _ _ (by decide) (by decide), oh _ _ (by decide) (by decide), oh _ _ (by decide) (by decide),
      oh _ _ (by decide) (by decide), oh _ _ (by decide) (by decide), oh _ _ (by decide) (by decide),
      oh _ _ (by decide) (by decide), oh _ _ (by decide) (by decide), oh _ _ (by decide) (by decide),
      oh _ _ (by decide) (by decide), oh _ _ (by decide) (by decide),
      FS.bufData (by omega) (by decide) (by decide), FS.bufData (by omega) (by decide) (by decide)⟩
    · rw [show BitVec.ofNat 32 p384PtAddAddress + 0x11A24 = BitVec.ofNat 32 p384MulAddress by decide]
      exact E.E.E.C.K.p3mul
    · rw [show BitVec.ofNat 32 p384PtAddAddress + 0x10E82 = MM by decide]; exact E.E.E.C.K.mm
    · rw [show BitVec.ofNat 32 p384PtAddAddress + 0x2DC = BitVec.ofNat 32 p384AddAddress by decide]
      exact E.E.E.C.K.p3add
    · rw [show BitVec.ofNat 32 p384PtAddAddress + 0x3F2 = BitVec.ofNat 32 p384SubAddress by decide]
      exact E.C4.sub
    · rw [show BitVec.ofNat 32 p384PtAddAddress + 0x12100 = BitVec.ofNat 32 p384DoubleAddress by decide]
      exact E.C4.dbl
    · rw [show BitVec.ofNat 32 p384PtAddAddress + 0x1298E = MSET by decide]; exact E.E.E.C.K.mset
    · rw [show BitVec.ofNat 32 p384PtAddAddress + 0x4C8 = BSUB by decide]; exact E.E.E.C.K.bsub
    · rw [show BitVec.ofNat 32 p384PtAddAddress + 0x11010 = SEL by decide]; exact E.E.E.C.K.sel
    · rw [show BitVec.ofNat 32 p384PtAddAddress + 0x129F6 = MCS by decide]; exact E.E.E.C.K.stub
    · rw [show BitVec.ofNat 32 p384PtAddAddress + 0x129FE = MCS + 8 by decide]; exact E.E.E.C.K.body
  obtain ⟨n2, c2, pc2, sp2, k2, val2, fr2⟩ := p384PtAdd_correct n1 EN pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) (by rw [r1 sp (by decide)]; exact hsp)
    (by rw [mem1, limbVal_wordsAt]; exact hx1) (by rw [mem1, ptv30]; exact hy1) (by rw [mem1, ptv60]; exact hz1)
    (by rw [mem1, limbVal_wordsAt]; exact hx2) (by rw [mem1, ptv30]; exact hy2) (by rw [mem1, ptv60]; exact hz2)
  rw [mem1] at val2 fr2
  simp only [ptv30, ptv60] at val2
  simp only [limbVal_wordsAt] at val2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0x440) hx (by decide) (by decide))
      (pvR_hi hx hcl), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x440) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), val2⟩
  by_cases h : q = sp
  · subst h; rw [sp2, hsp]
  · rw [k2 q (by revert hq h; revert q; decide) (by revert hq h; revert q; decide) (by revert hq h; revert q; decide)
      (by revert hq h; revert q; decide) (by revert hq h; revert q; decide) (by revert hq h; revert q; decide)
      (by revert hq h; revert q; decide) (by revert hq h; revert q; decide) (by revert hq h; revert q; decide)
      (by revert hq h; revert q; decide) (by revert hq h; revert q; decide) (by revert hq h; revert q; decide)
      (by revert hq h; revert q; decide) (by revert hq h; revert q; decide) (by revert hq h; revert q; decide),
      r1 q (by revert hq; revert q; decide)]

theorem accV_KD {M M' : Word → BitVec 8} {S K : Word} {c d : Nat} :
    ∀ k, (∀ q, q < 4 * k → M' (S + BitVec.ofNat 32 (c + q)) = M (K + BitVec.ofNat 32 (d + q))) →
    accV M' (S + BitVec.ofNat 32 c) k = accV M (K + BitVec.ofNat 32 d) k :=
  fun k h => accV_congr2 k fun i hi => by
    rw [ld_ofNat, ld_ofNat]
    simp only [add_ofNat_assoc, Nat.add_assoc]
    rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

/-- A point in projective coordinates, each in Montgomery form. -/
abbrev Pt := Nat × Nat × Nat

/-- The compiled point addition, on points. -/
def ptAddT (P Q : Pt) : Pt := p3Add p3B P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2

/-- The compiled point doubling, on points. -/
def ptDblT (P : Pt) : Pt := p3Dbl p3B P.1 P.2.1 P.2.2

/-- The table of odd multiples: entry `j` is `P + j·(2P)`, as the compiled
code adds. -/
def tblPt (P : Pt) : Nat → Pt
  | 0 => P
  | j + 1 => ptAddT (tblPt P j) (ptDblT P)

theorem ptAddT_lt (P Q : Pt) : PtLt (ptAddT P Q) := by
  unfold ptAddT p3Add; exact ⟨p3fs_lt _ _, p3fa_lt _ _, p3fa_lt _ _⟩

theorem ptDblT_lt (P : Pt) : PtLt (ptDblT P) := by
  unfold ptDblT p3Dbl; exact ⟨p3fs_lt _ _, p3fa_lt _ _, p3fd_lt _⟩

theorem tblPt_lt {P : Pt} (h : PtLt P) : ∀ j, PtLt (tblPt P j)
  | 0 => h
  | j + 1 => ptAddT_lt _ _

end C3.RV32.Pv
