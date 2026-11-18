import C3BootProofs.Proofs.Pv384Ds
import C3BootProofs.Proofs.Lowest
import C3BootProofs.Proofs.Norm12
import C3BootProofs.Proofs.UpdateFg12
import C3BootProofs.Proofs.UpdateDe12
import C3BootProofs.Proofs.UintEq
import C3BootProofs.Proofs.Prim

/-!
# `p384_verify_prehash`: the inversion's calls

Wrappers for the calls the two safegcd inversions make, in the terms of
`Pv384Lib.lean`: `memset`, `u32_min`, `SignedInt<12>::lowest`, `update_fg`,
`update_de`, `SignedInt<12>::norm`, and `Uint<12>::eq`. The signed values
they pass around are integers: a sign byte and a magnitude, as `sgnVal`.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- The functions the inversions call, at their addresses in the image. -/
structure PvCode3 (M : Word → BitVec 8) : Prop where
  um : CodeIn M (BitVec.ofNat 32 u32MinAddress) u32MinCode
  low : CodeIn M (BitVec.ofNat 32 lowest12Address) lowest12Code
  si : CodeIn M (BitVec.ofNat 32 selectI64Address) selectI64Code
  ufg : CodeIn M (BitVec.ofNat 32 updateFg12Address) updateFg12Code
  fi : CodeIn M (BitVec.ofNat 32 fromI64Address) fromI64Code
  ls : CodeIn M (BitVec.ofNat 32 lincombShift12Address) lincombShift12Code
  lc : CodeIn M (BitVec.ofNat 32 lincomb12Address) lincomb12Code
  abs : CodeIn M (BitVec.ofNat 32 absSign2Address) absSign2Code
  wide : CodeIn M (BitVec.ofNat 32 wideMul12x2Address) wideMul12x2Code
  neg : CodeIn M (BitVec.ofNat 32 condNeg12Address) condNeg12Code
  sel2 : CodeIn M (BitVec.ofNat 32 uintSelect2Address) uintSelect2Code
  shr : CodeIn M (BitVec.ofNat 32 shr12Address) shr12Code
  lm : CodeIn M (BitVec.ofNat 32 leadMut12Address) leadMut12Code
  tr : CodeIn M (BitVec.ofNat 32 trailing12Address) trailing12Code
  ude : CodeIn M (BitVec.ofNat 32 updateDe12Address) updateDe12Code
  lmc : CodeIn M (BitVec.ofNat 32 lincombShiftMod12Address) lincombShiftMod12Code
  tur : CodeIn M (BitVec.ofNat 32 toUintResize2Address) toUintResize2Code
  nm : CodeIn M (BitVec.ofNat 32 norm12Address) norm12Code
  ueq : CodeIn M (BitVec.ofNat 32 uint12EqAddress) uint12EqCode

theorem PvCode3.hi {M M' : Word → BitVec 8} (C : PvCode3 M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    PvCode3 M' :=
  ⟨codeHi C.um (by decide) (by decide) h, codeHi C.low (by decide) (by decide) h,
    codeHi C.si (by decide) (by decide) h, codeHi C.ufg (by decide) (by decide) h,
    codeHi C.fi (by decide) (by decide) h, codeHi C.ls (by decide) (by decide) h,
    codeHi C.lc (by decide) (by decide) h, codeHi C.abs (by decide) (by decide) h,
    codeHi C.wide (by decide) (by decide) h, codeHi C.neg (by decide) (by decide) h,
    codeHi C.sel2 (by decide) (by decide) h, codeHi C.shr (by decide) (by decide) h,
    codeHi C.lm (by decide) (by decide) h, codeHi C.tr (by decide) (by decide) h,
    codeHi C.ude (by decide) (by decide) h, codeHi C.lmc (by decide) (by decide) h,
    codeHi C.tur (by decide) (by decide) h, codeHi C.nm (by decide) (by decide) h,
    codeHi C.ueq (by decide) (by decide) h⟩

/-- The constants the inversions read. -/
structure PvData3 (M : Word → BitVec 8) : Prop where
  zero2 : CodeIn M (BitVec.ofNat 32 u2ZeroAddress) u2ZeroData
  one2 : CodeIn M (BitVec.ofNat 32 u2OneAddress) u2OneData
  max2 : CodeIn M (BitVec.ofNat 32 u2MaxAddress) u2MaxData

theorem PvData3.of {M M' : Word → BitVec 8} {S : Word} {N : Nat} (F : Fr S N) (D : PvData3 M)
    (h : ∀ x, Sep (S + 0xFFFFFE60) (N + 0x1A0) x 1 → M' x = M x) : PvData3 M' :=
  ⟨F.dataIn h D.zero2 (by decide) (by decide), F.dataIn h D.one2 (by decide) (by decide),
    F.dataIn h D.max2 (by decide) (by decide)⟩

/-- Everything the stages after the checks need. -/
structure PvEnv3 (M : Word → BitVec 8) : Prop where
  E : PvEnv M
  C3 : PvCode3 M
  D3 : PvData3 M

theorem PvEnv3.fr {B : Word} {M M' : Word → BitVec 8} (E : PvEnv3 M) (F : Fr B 0x21A0)
    (h : ∀ x, PvR B x → M' x = M x) : PvEnv3 M' :=
  have hb : ∀ x, Sep (B + 0xFFFFFE60) (0x21A0 + 0x1A0) x 1 → PvR B x := fun x hx => by
    have := hx.sub (c := 0) (l := 0x230C) (by decide); rwa [add_ofNat_zero] at this
  ⟨E.E.fr F h, E.C3.hi fun x hx => h x (pvR_of_hi F hx), E.D3.of F fun x hx => h x (hb x hx)⟩

/-- An integer from a sign byte and a magnitude, with the sign of `X`. -/
def sgnI (X : Int) (A : Nat) : Int := if X < 0 then -(A : Int) else (A : Int)

/-- What `update_fg` leaves for the row `[u, v]` and the shift `s`: the
magnitude of `f u + g v`, shifted right by `s` and cut to 384 bits, with its
sign. -/
def fgUpd (F G u v : Int) (s : Nat) : Int :=
  sgnI (F * u + G * v) ((F * u + G * v).natAbs / 2 ^ s % 2 ^ 384)

/-- What `update_de` leaves for the row `[u, v]`, the shift `s`, the
modulus `M`, and `-M⁻¹ mod 2^64` as `MI`. -/
def deUpd (D E u v : Int) (MI s M : Nat) : Int :=
  let X := D * u + E * v
  let r := lrsm (if X < 0 then 1 else 0) X.natAbs MI s M
  sgnVal r.1 r.2

theorem sgnVal_rep {σ A : Nat} {X : Int} (hσ : σ ≤ 1) (h : sgnVal σ A = X) :
    (X < 0 → σ = 1 ∧ A = X.natAbs) ∧ (0 < X → σ = 0 ∧ A = X.natAbs) ∧ (X = 0 → A = 0) := by
  unfold sgnVal at h
  by_cases h1 : σ = 1
  · rw [ite_eq_left h1] at h; subst h; refine ⟨fun _ => ⟨h1, by omega⟩, fun h2 => by omega, fun h2 => by omega⟩
  · rw [ite_eq_right h1] at h; subst h; refine ⟨fun h2 => by omega, fun _ => ⟨by omega, by omega⟩, fun h2 => by omega⟩

theorem fgUpd_of {σ A b R : Nat} {F G u v : Int} {s : Nat} (hσ : σ ≤ 1)
    (h : sgnVal σ A = F * u + G * v) (hb : b = σ) (hR : R = A / 2 ^ s % 2 ^ 384) :
    sgnVal b R = fgUpd F G u v s ∧ b ≤ 1 := by
  subst hb hR
  obtain ⟨n1, n2, n3⟩ := sgnVal_rep hσ h
  refine ⟨?_, hσ⟩
  unfold fgUpd sgnI sgnVal
  rcases Int.lt_trichotomy (F * u + G * v) 0 with h0 | h0 | h0
  · obtain ⟨e1, e2⟩ := n1 h0; rw [ite_eq_left e1, ite_eq_left h0, e2]
  · rw [n3 h0, Nat.zero_div, Nat.zero_mod, h0]; simp
  · obtain ⟨e1, e2⟩ := n2 h0; rw [ite_eq_right (by omega), ite_eq_right (by omega), e2]

theorem lrsm_zero (σ MI s M : Nat) (hM : 0 < M) : (lrsm σ 0 MI s M).2 = 0 := by
  unfold lrsm lrsmMf; simp [hM]

theorem lrsm_le {σ A MI s M : Nat} (hσ : σ ≤ 1) : (lrsm σ A MI s M).1 ≤ 1 := by
  unfold lrsm; dsimp only; split <;> omega

theorem deUpd_of {σ A b R MI s M : Nat} {D E u v : Int} (hσ : σ ≤ 1) (hM : 0 < M)
    (h : sgnVal σ A = D * u + E * v) (hb : b = (lrsm σ A MI s M).1) (hR : R = (lrsm σ A MI s M).2) :
    sgnVal b R = deUpd D E u v MI s M ∧ b ≤ 1 := by
  subst hb hR
  obtain ⟨n1, n2, n3⟩ := sgnVal_rep hσ h
  refine ⟨?_, lrsm_le hσ⟩
  unfold deUpd; dsimp only
  rcases Int.lt_trichotomy (D * u + E * v) 0 with h0 | h0 | h0
  · obtain ⟨e1, e2⟩ := n1 h0; rw [ite_eq_left h0, ← e1, ← e2]
  · rw [n3 h0, h0, Int.natAbs_zero, lrsm_zero _ _ _ _ hM, lrsm_zero _ _ _ _ hM]; simp [sgnVal]
  · obtain ⟨e1, e2⟩ := n2 h0; rw [ite_eq_right (by omega), ← e1, ← e2]

theorem add_lit30 (S : Word) (c : Nat) : S + BitVec.ofNat 32 c + 0x30 = S + BitVec.ofNat 32 (c + 0x30) :=
  add_ofNat_assoc S c 0x30
theorem add_lit8 (S : Word) (c : Nat) : S + BitVec.ofNat 32 c + 8 = S + BitVec.ofNat 32 (c + 8) :=
  add_ofNat_assoc S c 8
theorem add_lit10 (S : Word) (c : Nat) : S + BitVec.ofNat 32 c + 0x10 = S + BitVec.ofNat 32 (c + 0x10) :=
  add_ofNat_assoc S c 0x10
theorem add_lit18 (S : Word) (c : Nat) : S + BitVec.ofNat 32 c + 0x18 = S + BitVec.ofNat 32 (c + 0x18) :=
  add_ofNat_assoc S c 0x18
theorem add_lit34 (S : Word) (c : Nat) : S + BitVec.ofNat 32 c + 0x34 = S + BitVec.ofNat 32 (c + 0x34) :=
  add_ofNat_assoc S c 0x34

/-- Code above 0x40000000 is apart from the `k` bytes below `sp`. -/
theorem pv_lowHi {B b : Word} (F : Fr B 0x21A0) {k l : Nat} (hk : 0 < k) (hk' : k ≤ 0x5C0)
    (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + l ≤ 2 ^ 32) :
    Sep (B + 0x420 + BitVec.ofNat 32 (2 ^ 32 - k)) k b l := by
  have := F.lo; have := F.hi
  exact sep_of_le (by rw [pv_below F hk hk']; omega) hl

theorem pv_al {B : Word} (F : Fr B 0x21A0) {c : Nat} (hc : c ≤ 0x1D80) (ac : c % 4 = 0) :
    (B + 0x420 + BitVec.ofNat 32 c).toNat % 4 = 0 := by
  have := F.al; rw [pv_at F c hc]; omega

theorem pv_wr {B : Word} (F : Fr B 0x21A0) {c n : Nat} (hc : c + n ≤ 0x1D80) :
    (B + 0x420 + BitVec.ofNat 32 c).toNat + n < 2 ^ 32 := by
  have := F.hi; rw [pv_at F c (by omega)]; omega

set_option maxHeartbeats 4000000 in
/-- A call to `memset` of `N` bytes at offset `c` of the frame with zero. -/
theorem pv_ms {B : Word} {m : Machine} {off : Nat} {imm o : Word} {c N : Nat} (F : Fr B 0x21A0)
    (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = MSET) (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 c) (ha1 : reg m a1 = 0)
    (ha2 : reg m a2 = BitVec.ofNat 32 N) (hc : c + N ≤ 0x1D4C) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem c N ∧
      ∀ j, j < N → m'.mem (B + 0x420 + BitVec.ofNat 32 (c + j)) = 0 := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  obtain ⟨n2, c2, u2, mem2, k2⟩ := c_memset (N := N) s E.C.self E.C.K h1 h2 hb he8 ha0 ha1 ha2 (pv_wr F (by omega))
    (FS.sepHi (by omega) (by decide) (by decide))
  refine ⟨n2, ⟨c2, u2, fun x hx => ?_, fun q hq => ?_⟩, fun e he1 he2 => ?_, fun j hj => ?_⟩
  · rw [mem2, fillBytes_sep (pvR_hi (c := c) (l := N) hx hc) (Nat.le_refl _)]
  · exact k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)
  · rw [mem2, fillBytes_sep (sepS (B + 0x420) (c := c) (n := N) (d := e) (k := 1) (by omega) (by omega) (by omega))
      (Nat.le_refl _)]
  · rw [mem2, ← add_ofNat_assoc, fill_at hj (by omega)]; rfl

/-- A call to `u32_min`: the smaller of `a0` and 62. -/
theorem pv_umin {B : Word} {m : Machine} {off : Nat} {imm o : Word} (F : Fr B 0x21A0)
    (E : PvEnv3 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 u32MinAddress)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : reg m sp = B + 0x420) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem 0 0 ∧
      reg m' a0 = (if (reg m a0).toNat < 62 then reg m a0 else 62) := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = B + 0x420 := by rw [r1 sp (by decide)]; exact hsp
  obtain ⟨n2, c2, pc2, a02, k2, fr2⟩ := u32Min_correct n1 (by rw [mem1]; exact E.C3.um) pc1
    (r1 a0 (by decide)) (by rw [sp1]; exact pv_lowHi F (k := 1) (by decide) (by decide) (by decide) (by decide))
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at fr2
  rw [sp1] at fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 1) hx (by decide)
      (by decide)), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 1) (by decide) (by decide) (by omega)),
      a02⟩
  rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]

/-- A call to `SignedInt<12>::lowest` on the value at offset `c` of the
frame: `a1:a0` gets `lowestVal` of its sign and low 64 bits. -/
theorem pv_low {B : Word} {m : Machine} {off : Nat} {imm o : Word} {c : Nat} (F : Fr B 0x21A0)
    (E : PvEnv3 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 lowest12Address)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : reg m sp = B + 0x420)
    (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 c) (hc : c + 49 ≤ 0x1D4C) (ac : c % 4 = 0)
    (hσ : (m.mem (B + 0x420 + BitVec.ofNat 32 (c + 0x30))).toNat ≤ 1) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem 0 0 ∧
      (reg m' a0).toNat + 2 ^ 32 * (reg m' a1).toNat =
        lowestVal (m.mem (B + 0x420 + BitVec.ofNat 32 (c + 0x30))).toNat
          (accV m.mem (B + 0x420 + BitVec.ofNat 32 c) 2) := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = B + 0x420 := by rw [r1 sp (by decide)]; exact hsp
  obtain ⟨n2, c2, pc2, sp2, k2, v2, fr2⟩ := lowest12_correct n1 (p := B + 0x420 + BitVec.ofNat 32 c) (by decide)
    (by rw [mem1]; exact E.C3.low)
    (by rw [mem1, show BitVec.ofNat 32 lowest12Address + 0xFFFFE0D8 = BitVec.ofNat 32 selectI64Address by decide];
        exact E.C3.si) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
    (pv_al F (by omega) ac) (by rw [mem1, add_lit30]; exact hσ)
    (by rw [sp1]; exact pv_lowHi F (k := 1) (by decide) (by decide) (by decide) (by decide))
  rw [mem1, add_lit30] at v2
  rw [mem1, sp1] at fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => ?_, fun q hq => ?_⟩,
    fun e he1 he2 => ?_, v2⟩
  · exact fr2 x (sep1_ne (pvR_lo (k := 1) hx (by decide) (by decide)))
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · exact fr2 _ (sep1_ne (pv_lowB F (k := 1) (by decide) (by decide) (by omega)))

set_option maxHeartbeats 16000000 in
/-- A call to `update_fg` with the result at offset `co`, `f` at `ca`, `g` at
`cb`, the matrix at `ct`, and the shift `s`: the two new values, as integers. -/
theorem pv_ufg {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co ca cb ct s : Nat} (F : Fr B 0x21A0)
    (E : PvEnv3 m.mem) (st : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 updateFg12Address)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : reg m sp = B + 0x420)
    (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co) (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 ca)
    (ha2 : reg m a2 = B + 0x420 + BitVec.ofNat 32 cb) (ha3 : reg m a3 = B + 0x420 + BitVec.ofNat 32 ct)
    (ha4 : reg m a4 = BitVec.ofNat 32 s) (hs1 : 1 ≤ s) (hs2 : s ≤ 63)
    (hco : co + 0x65 ≤ 0x1D4C) (hca : ca + 49 ≤ 0x1D4C) (hcb : cb + 49 ≤ 0x1D4C) (hct : ct + 32 ≤ 0x1D4C)
    (aco : co % 4 = 0) (aca : ca % 4 = 0) (acb : cb % 4 = 0) (act : ct % 4 = 0)
    (sa : ca + 49 ≤ co ∨ co + 0x65 ≤ ca) (sb : cb + 49 ≤ co ∨ co + 0x65 ≤ cb) (stt : ct + 32 ≤ co ∨ co + 0x65 ≤ ct)
    (hσa : (m.mem (B + 0x420 + BitVec.ofNat 32 (ca + 0x30))).toNat ≤ 1)
    (hσb : (m.mem (B + 0x420 + BitVec.ofNat 32 (cb + 0x30))).toNat ≤ 1) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 0x65 ∧
      (let Fa := sgnVal (m.mem (B + 0x420 + BitVec.ofNat 32 (ca + 0x30))).toNat
          (accV m.mem (B + 0x420 + BitVec.ofNat 32 ca) 12)
       let Gb := sgnVal (m.mem (B + 0x420 + BitVec.ofNat 32 (cb + 0x30))).toNat
          (accV m.mem (B + 0x420 + BitVec.ofNat 32 cb) 12)
       sgnVal (m'.mem (B + 0x420 + BitVec.ofNat 32 (co + 0x30))).toNat
          (accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12) =
         fgUpd Fa Gb (i64Val (accV m.mem (B + 0x420 + BitVec.ofNat 32 ct) 2))
           (i64Val (accV m.mem (B + 0x420 + BitVec.ofNat 32 (ct + 8)) 2)) s ∧
       (m'.mem (B + 0x420 + BitVec.ofNat 32 (co + 0x30))).toNat ≤ 1 ∧
       sgnVal (m'.mem (B + 0x420 + BitVec.ofNat 32 (co + 0x64))).toNat
          (accV m'.mem (B + 0x420 + BitVec.ofNat 32 (co + 0x34)) 12) =
         fgUpd Fa Gb (i64Val (accV m.mem (B + 0x420 + BitVec.ofNat 32 (ct + 0x10)) 2))
           (i64Val (accV m.mem (B + 0x420 + BitVec.ofNat 32 (ct + 0x18)) 2)) s ∧
       (m'.mem (B + 0x420 + BitVec.ofNat 32 (co + 0x64))).toNat ≤ 1) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz st.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + 0xFFFFFD50) 0x2B0 b l := fun b l hb hl => pv_lowHi F (k := 0x2B0) (by decide) (by decide) hb hl
  have hG : (B + 0x420 + 0xFFFFFD50).toNat = B.toNat + 0x420 - 0x2B0 := pv_below F (k := 0x2B0) (by decide) (by decide)
  have hBa := F.al; have hBl := F.lo; have hBh := F.hi
  have EN : UFEnv n1.mem (BitVec.ofNat 32 updateFg12Address) (B + 0x420 + 0xFFFFFD50) (B + 0x420 + BitVec.ofNat 32 co)
      (B + 0x420 + BitVec.ofNat 32 ca) (B + 0x420 + BitVec.ofNat 32 cb) (B + 0x420 + BitVec.ofNat 32 ct) := by
    rw [mem1]
    refine ⟨by decide, E.C3.ufg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, E.D3.zero2, E.D3.one2, ?_, ?_, ?_,
      by rw [hG]; omega, by rw [hG]; omega, pv_al F (by omega) aco, pv_al F (by omega) aca, pv_al F (by omega) acb,
      pv_al F (by omega) act, pv_wr F (by omega), pv_wr F (by omega), pv_wr F (by omega),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      (pv_lowK F (n := 8) (k := 0x2B0) (by decide) (by decide) (by decide)).symm,
      (pv_lowK F (n := 8) (k := 0x2B0) (by decide) (by decide) (by decide)).symm, lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide),
      FS.bufData (by omega) (by decide) (by decide), FS.bufData (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide),
      pv_lowS F (k := 0x2B0) (by omega) (by decide) (by decide), pv_lowS F (k := 0x2B0) (by omega) (by decide) (by decide),
      pv_lowS F (k := 0x2B0) (by omega) (by decide) (by decide), pv_lowS F (k := 0x2B0) (by omega) (by decide) (by decide),
      sepS (B + 0x420) sa (by omega) (by omega), sepS (B + 0x420) sb (by omega) (by omega),
      sepS (B + 0x420) stt (by omega) (by omega)⟩
    · rw [show BitVec.ofNat 32 updateFg12Address + 0x13C = BitVec.ofNat 32 fromI64Address by decide]; exact E.C3.fi
    · rw [show BitVec.ofNat 32 updateFg12Address + 0xFFFFF2F2 = BitVec.ofNat 32 lincombShift12Address by decide]
      exact E.C3.ls
    · rw [show BitVec.ofNat 32 updateFg12Address + 0xFFFFF2F2 + 0x62 = BitVec.ofNat 32 lincomb12Address by decide]
      exact E.C3.lc
    · rw [show BitVec.ofNat 32 updateFg12Address + 0xFFFFF2F2 + 0x62 + 0xFFFFA54E = BitVec.ofNat 32 absSign2Address by
        decide]; exact E.C3.abs
    · rw [show BitVec.ofNat 32 updateFg12Address + 0xFFFFF2F2 + 0x62 + 0x398 = BitVec.ofNat 32 wideMul12x2Address by
        decide]; exact E.C3.wide
    · rw [show BitVec.ofNat 32 updateFg12Address + 0xFFFFF2F2 + 0x62 + 0x482 = BitVec.ofNat 32 condNeg12Address by
        decide]; exact E.C3.neg
    · rw [show BitVec.ofNat 32 updateFg12Address + 0xFFFFF2F2 + 0x62 + 0x18A8 = MSET by decide]; exact E.E.C.K.mset
    · rw [show BitVec.ofNat 32 updateFg12Address + 0xFFFFF2F2 + 0x62 + 0x1910 = MCS by decide]; exact E.E.C.K.stub
    · rw [show BitVec.ofNat 32 updateFg12Address + 0xFFFFF2F2 + 0x62 + 0x1918 = MCS + 8 by decide]; exact E.E.C.K.body
    · rw [show lcBsub (BitVec.ofNat 32 updateFg12Address + 0xFFFFF2F2 + 0x62) = BSUB by decide]; exact E.E.C.K.bsub
    · rw [show BitVec.ofNat 32 updateFg12Address + 0xFFFFF2F2 + 0x62 + 0x592 = BitVec.ofNat 32 uintSelect2Address by
        decide]; exact E.C3.sel2
    · rw [show BitVec.ofNat 32 updateFg12Address + 0xFFFFF2F2 + 0x62 + 0xFFFFFF2A = SEL by decide]; exact E.E.C.K.sel
    · rw [show BitVec.ofNat 32 updateFg12Address + 0xFFFFF2F2 + 0x1E6 = BitVec.ofNat 32 shr12Address by decide]
      exact E.C3.shr
    · rw [show BitVec.ofNat 32 updateFg12Address + 0xFFFFF2F2 + 0x1E6 + 0x1EE = BitVec.ofNat 32 leadMut12Address by
        decide]; exact E.C3.lm
    · rw [show BitVec.ofNat 32 updateFg12Address + 0xFFFFF2F2 + 0x1E6 + 0x1FE = BitVec.ofNat 32 trailing12Address by
        decide]; exact E.C3.tr
  obtain ⟨n2, c2, pc2, sp2, k2, ⟨σ1, A1, hσ1, e1, b1, v1⟩, ⟨σ2, A2, hσ2, e2, b2, v2⟩, fr2⟩ :=
    updateFg12_correct n1 (s := s) EN pc1
      (by rw [r1 sp (by decide), hsp, BitVec.add_assoc, show (0xFFFFFD50 : Word) + 0x2B0 = 0 from rfl]
          exact (BitVec.add_zero _).symm)
      (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
      (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
      (by rw [r1 a4 (by decide)]; exact ha4) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) hs1 hs2
      (by rw [mem1, add_lit30]; exact hσa) (by rw [mem1, add_lit30]; exact hσb)
  rw [mem1] at e1 e2 fr2
  rw [add_lit30, add_lit30, add_lit8] at e1
  rw [add_lit30, add_lit30, add_lit10, add_lit18] at e2
  rw [add_lit30] at b1
  rw [add_lit34, add_lit30, show co + 0x34 + 0x30 = co + 0x64 by omega] at b2
  rw [add_lit34] at v2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x
      (pvR_lo (k := 0x2B0) hx (by decide) (by decide)) (pvR_hi hx hco), fun q hq => ?_⟩,
    fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x2B0) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), ?_⟩
  · by_cases h : q = sp
    · subst h; rw [sp2, hsp, BitVec.add_assoc, show (0xFFFFFD50 : Word) + 0x2B0 = 0 from rfl]
      exact BitVec.add_zero _
    · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · obtain ⟨f1, l1⟩ := fgUpd_of hσ1 e1 b1 v1
    obtain ⟨f2, l2⟩ := fgUpd_of hσ2 e2 b2 v2
    exact ⟨f1, l1, f2, l2⟩

set_option maxHeartbeats 16000000 in
/-- A call to `update_de` with the result at offset `co`, `d` at `ca`, `e` at
`cb`, the modulus at `cm`, the matrix at `ct`, `-M⁻¹ mod 2^64` in
`a5:a4`, and the shift `s`: the two new values, as integers. -/
theorem pv_ude {B : Word} {m : Machine} {off : Nat} {imm o mlo mhi : Word} {co ca cb cm ct s : Nat}
    (F : Fr B 0x21A0) (E : PvEnv3 m.mem) (st : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 updateDe12Address)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : reg m sp = B + 0x420)
    (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co) (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 ca)
    (ha2 : reg m a2 = B + 0x420 + BitVec.ofNat 32 cb) (ha3 : reg m a3 = B + 0x420 + BitVec.ofNat 32 cm)
    (ha4 : reg m a4 = mlo) (ha5 : reg m a5 = mhi) (ha6 : reg m a6 = B + 0x420 + BitVec.ofNat 32 ct)
    (ha7 : reg m (17 : Fin 32) = BitVec.ofNat 32 s) (hs1 : 1 ≤ s) (hs2 : s ≤ 63)
    (hco : co + 0x65 ≤ 0x1D4C) (hca : ca + 49 ≤ 0x1D4C) (hcb : cb + 49 ≤ 0x1D4C) (hcm : cm + 48 ≤ 0x1D4C)
    (hct : ct + 32 ≤ 0x1D4C) (aco : co % 4 = 0) (aca : ca % 4 = 0) (acb : cb % 4 = 0) (acm : cm % 4 = 0)
    (act : ct % 4 = 0)
    (sa : ca + 49 ≤ co ∨ co + 0x65 ≤ ca) (sb : cb + 49 ≤ co ∨ co + 0x65 ≤ cb) (sm : cm + 48 ≤ co ∨ co + 0x65 ≤ cm)
    (stt : ct + 32 ≤ co ∨ co + 0x65 ≤ ct)
    (hσa : (m.mem (B + 0x420 + BitVec.ofNat 32 (ca + 0x30))).toNat ≤ 1)
    (hσb : (m.mem (B + 0x420 + BitVec.ofNat 32 (cb + 0x30))).toNat ≤ 1)
    (hM : 0 < accV m.mem (B + 0x420 + BitVec.ofNat 32 cm) 12) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 0x65 ∧
      (let Da := sgnVal (m.mem (B + 0x420 + BitVec.ofNat 32 (ca + 0x30))).toNat
          (accV m.mem (B + 0x420 + BitVec.ofNat 32 ca) 12)
       let Eb := sgnVal (m.mem (B + 0x420 + BitVec.ofNat 32 (cb + 0x30))).toNat
          (accV m.mem (B + 0x420 + BitVec.ofNat 32 cb) 12)
       let MI := mlo.toNat + 2 ^ 32 * mhi.toNat
       let Mv := accV m.mem (B + 0x420 + BitVec.ofNat 32 cm) 12
       sgnVal (m'.mem (B + 0x420 + BitVec.ofNat 32 (co + 0x30))).toNat
          (accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12) =
         deUpd Da Eb (i64Val (accV m.mem (B + 0x420 + BitVec.ofNat 32 ct) 2))
           (i64Val (accV m.mem (B + 0x420 + BitVec.ofNat 32 (ct + 8)) 2)) MI s Mv ∧
       (m'.mem (B + 0x420 + BitVec.ofNat 32 (co + 0x30))).toNat ≤ 1 ∧
       sgnVal (m'.mem (B + 0x420 + BitVec.ofNat 32 (co + 0x64))).toNat
          (accV m'.mem (B + 0x420 + BitVec.ofNat 32 (co + 0x34)) 12) =
         deUpd Da Eb (i64Val (accV m.mem (B + 0x420 + BitVec.ofNat 32 (ct + 0x10)) 2))
           (i64Val (accV m.mem (B + 0x420 + BitVec.ofNat 32 (ct + 0x18)) 2)) MI s Mv ∧
       (m'.mem (B + 0x420 + BitVec.ofNat 32 (co + 0x64))).toNat ≤ 1) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz st.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + 0xFFFFFC80) 0x380 b l := fun b l hb hl => pv_lowHi F (k := 0x380) (by decide) (by decide) hb hl
  have hG : (B + 0x420 + 0xFFFFFC80).toNat = B.toNat + 0x420 - 0x380 := pv_below F (k := 0x380) (by decide) (by decide)
  have hBa := F.al; have hBl := F.lo; have hBh := F.hi
  have EN : UDEnv n1.mem (BitVec.ofNat 32 updateDe12Address) (B + 0x420 + 0xFFFFFC80)
      (B + 0x420 + BitVec.ofNat 32 co) (B + 0x420 + BitVec.ofNat 32 ca) (B + 0x420 + BitVec.ofNat 32 cb)
      (B + 0x420 + BitVec.ofNat 32 cm) (B + 0x420 + BitVec.ofNat 32 ct) := by
    rw [mem1]
    refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, E.D3.zero2, E.D3.one2, ?_, ?_, ?_, ?_, E.D3.max2,
      E.C3.ude, ?_,
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), (pv_lowK F (n := 8) (k := 0x380) (by decide) (by decide) (by decide)).symm, (pv_lowK F (n := 8) (k := 0x380) (by decide) (by decide) (by decide)).symm, lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), (pv_lowK F (n := 8) (k := 0x380) (by decide) (by decide) (by decide)).symm, lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.bufData (by omega) (by decide) (by decide), FS.bufData (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.bufData (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide),
      by rw [hG]; omega, by rw [hG]; omega, pv_al F (by omega) aco, pv_al F (by omega) aca, pv_al F (by omega) acb,
      pv_al F (by omega) acm, pv_al F (by omega) act, pv_wr F (by omega), pv_wr F (by omega), pv_wr F (by omega),
      pv_lowS F (k := 0x380) (by omega) (by decide) (by decide), pv_lowS F (k := 0x380) (by omega) (by decide) (by decide), pv_lowS F (k := 0x380) (by omega) (by decide) (by decide), pv_lowS F (k := 0x380) (by omega) (by decide) (by decide), pv_lowS F (k := 0x380) (by omega) (by decide) (by decide),
      sepS (B + 0x420) sa (by omega) (by omega), sepS (B + 0x420) sb (by omega) (by omega),
      sepS (B + 0x420) sm (by omega) (by omega), sepS (B + 0x420) stt (by omega) (by omega)⟩
    · rw [show udL (BitVec.ofNat 32 updateDe12Address) = BitVec.ofNat 32 lincombShiftMod12Address by decide]
      exact E.C3.lmc
    · rw [show lmLc (udL (BitVec.ofNat 32 updateDe12Address)) = BitVec.ofNat 32 lincomb12Address by decide]
      exact E.C3.lc
    · rw [show lmLc (udL (BitVec.ofNat 32 updateDe12Address)) + 0xFFFFA54E = BitVec.ofNat 32 absSign2Address by
        decide]; exact E.C3.abs
    · rw [show lmLc (udL (BitVec.ofNat 32 updateDe12Address)) + 0x398 = BitVec.ofNat 32 wideMul12x2Address by
        decide]; exact E.C3.wide
    · rw [show lmLc (udL (BitVec.ofNat 32 updateDe12Address)) + 0x482 = BitVec.ofNat 32 condNeg12Address by
        decide]; exact E.C3.neg
    · rw [show lmLc (udL (BitVec.ofNat 32 updateDe12Address)) + 0x18A8 = MSET by decide]; exact E.E.C.K.mset
    · rw [show lmLc (udL (BitVec.ofNat 32 updateDe12Address)) + 0x1910 = MCS by decide]; exact E.E.C.K.stub
    · rw [show lmLc (udL (BitVec.ofNat 32 updateDe12Address)) + 0x1918 = MCS + 8 by decide]; exact E.E.C.K.body
    · rw [show lcBsub (lmLc (udL (BitVec.ofNat 32 updateDe12Address))) = BSUB by decide]; exact E.E.C.K.bsub
    · rw [show lmLc (udL (BitVec.ofNat 32 updateDe12Address)) + 0x592 = BitVec.ofNat 32 uintSelect2Address by
        decide]; exact E.C3.sel2
    · rw [show lmLc (udL (BitVec.ofNat 32 updateDe12Address)) + 0xFFFFFF2A = SEL by decide]; exact E.E.C.K.sel
    · rw [show lmShr (udL (BitVec.ofNat 32 updateDe12Address)) = BitVec.ofNat 32 shr12Address by decide]
      exact E.C3.shr
    · rw [show lmShr (udL (BitVec.ofNat 32 updateDe12Address)) + 0x1EE = BitVec.ofNat 32 leadMut12Address by
        decide]; exact E.C3.lm
    · rw [show lmShr (udL (BitVec.ofNat 32 updateDe12Address)) + 0x1FE = BitVec.ofNat 32 trailing12Address by
        decide]; exact E.C3.tr
    · rw [show udL (BitVec.ofNat 32 updateDe12Address) + 0xFFFF9DCE = BitVec.ofNat 32 toUintResize2Address by
        decide]; exact E.C3.tur
    · rw [show BitVec.ofNat 32 updateDe12Address + 0xB2 = BitVec.ofNat 32 fromI64Address by decide]; exact E.C3.fi
  obtain ⟨n2, c2, pc2, sp2, k2, ⟨σ1, A1, hσ1, e1, b1, v1⟩, ⟨σ2, A2, hσ2, e2, b2, v2⟩, fr2⟩ :=
    updateDe12_correct n1 (s := s) (mlo := mlo) (mhi := mhi) EN pc1
      (by rw [r1 sp (by decide), hsp, BitVec.add_assoc, show (0xFFFFFC80 : Word) + 0x380 = 0 from rfl]
          exact (BitVec.add_zero _).symm)
      (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
      (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
      (by rw [r1 a4 (by decide)]; exact ha4) (by rw [r1 a5 (by decide)]; exact ha5)
      (by rw [r1 a6 (by decide)]; exact ha6) (by rw [r1 17 (by decide)]; exact ha7)
      (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) hs1 hs2
      (by rw [mem1, add_lit30]; exact hσa) (by rw [mem1, add_lit30]; exact hσb)
  rw [mem1] at e1 e2 fr2 b1 b2 v1 v2
  rw [add_lit30, add_lit30, add_lit8] at e1
  rw [add_lit30, add_lit30, add_lit10, add_lit18] at e2
  rw [add_lit30] at b1
  rw [add_lit34, add_lit30, show co + 0x34 + 0x30 = co + 0x64 by omega] at b2
  rw [add_lit34] at v2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x
      (pvR_lo (k := 0x380) hx (by decide) (by decide)) (pvR_hi hx hco), fun q hq => ?_⟩,
    fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x380) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), ?_⟩
  · by_cases h : q = sp
    · subst h; rw [sp2, hsp, BitVec.add_assoc, show (0xFFFFFC80 : Word) + 0x380 = 0 from rfl]
      exact BitVec.add_zero _
    · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · obtain ⟨f1, l1⟩ := deUpd_of hσ1 hM e1 b1 v1
    obtain ⟨f2, l2⟩ := deUpd_of hσ2 hM e2 b2 v2
    exact ⟨f1, l1, f2, l2⟩

set_option maxHeartbeats 8000000 in
/-- A call to `SignedInt<12>::norm` with the result at offset `co`, the value
at `cx`, `f`'s sign in `a2`, and the modulus at `cn`. -/
theorem pv_norm {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cx cn : Nat} (F : Fr B 0x21A0)
    (E : PvEnv3 m.mem) (st : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 norm12Address)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : reg m sp = B + 0x420)
    (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co) (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cx)
    (ha2 : reg m a2 = 0 ∨ reg m a2 = 1) (ha3 : reg m a3 = B + 0x420 + BitVec.ofNat 32 cn)
    (hco : co + 48 ≤ 0x1D4C) (hcx : cx + 49 ≤ 0x1D4C) (hcn : cn + 48 ≤ 0x1D4C)
    (aco : co % 4 = 0) (acx : cx % 4 = 0) (acn : cn % 4 = 0)
    (hσ : (m.mem (B + 0x420 + BitVec.ofNat 32 (cx + 0x30))).toNat ≤ 1) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 48 ∧
      accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12 =
        normVal (m.mem (B + 0x420 + BitVec.ofNat 32 (cx + 0x30))).toNat (reg m a2).toNat
          (accV m.mem (B + 0x420 + BitVec.ofNat 32 cx) 12) (accV m.mem (B + 0x420 + BitVec.ofNat 32 cn) 12) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz st.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (nmR (B + 0x420)) 0xB0 b l := fun b l hb hl => pv_lowHi F (k := 0xB0) (by decide) (by decide) hb hl
  have EN : NmEnv n1.mem (BitVec.ofNat 32 norm12Address) (B + 0x420) (B + 0x420 + BitVec.ofNat 32 co)
      (B + 0x420 + BitVec.ofNat 32 cx) (B + 0x420 + BitVec.ofNat 32 cn) := by
    rw [mem1]
    refine ⟨by decide, E.C3.nm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by have := pv_S F; have := F.lo; omega,
      pv_al F (by omega) aco, pv_al F (by omega) acx, pv_al F (by omega) acn, pv_wr F (by omega),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide),
      FS.sepHi (by omega) (by decide) (by decide),
      pv_lowS F (k := 0xB0) (by omega) (by decide) (by decide), pv_lowS F (k := 0xB0) (by omega) (by decide) (by decide),
      pv_lowS F (k := 0xB0) (by omega) (by decide) (by decide)⟩
    · rw [show BitVec.ofNat 32 norm12Address + 0xFFFFFFE6 = BitVec.ofNat 32 uint12IsNonzeroAddress by decide]
      exact E.E.C2.unz
    · rw [show BitVec.ofNat 32 norm12Address + 0xFFFEF13C = BitVec.ofNat 32 uintRefIsNonzeroAddress by decide]
      exact E.E.C.K.refnz
    · rw [show BitVec.ofNat 32 norm12Address + 0xCB6 = MSET by decide]; exact E.E.C.K.mset
    · rw [show nmBsub (BitVec.ofNat 32 norm12Address) = BSUB by decide]; exact E.E.C.K.bsub
    · rw [show BitVec.ofNat 32 norm12Address + 0xFFFFF338 = SEL by decide]; exact E.E.C.K.sel
    · rw [show BitVec.ofNat 32 norm12Address + 0xD1E = MCS by decide]; exact E.E.C.K.stub
    · rw [show BitVec.ofNat 32 norm12Address + 0xD26 = MCS + 8 by decide]; exact E.E.C.K.body
  obtain ⟨n2, c2, pc2, sp2, k2, v2, fr2⟩ := norm12_correct n1 EN pc1 (by rw [r1 sp (by decide)]; exact hsp)
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
    (by rw [mem1, add_lit30]; exact hσ) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1, add_lit30, r1 a2 (by decide)] at v2
  rw [mem1] at fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x
      (pvR_lo (k := 0xB0) hx (by decide) (by decide)) (pvR_hi hx hco), fun q hq => ?_⟩,
    fun e he1 he2 => fr2 _ (pv_lowB F (k := 0xB0) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), v2⟩
  by_cases h : q = sp
  · subst h; rw [sp2, hsp]
  · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]

/-- A call to `Uint<12>::eq` on the 12 limbs at offset `c` of the frame and
those at the constant `K`. -/
theorem pv_eq {B K : Word} {m : Machine} {off : Nat} {imm o : Word} {c : Nat} (F : Fr B 0x21A0)
    (E : PvEnv3 m.mem) (st : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 uint12EqAddress)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : reg m sp = B + 0x420)
    (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 c) (ha1 : reg m a1 = K) (hc : c + 48 ≤ 0x1D4C)
    (ac : c % 4 = 0) (aK : K.toNat % 4 = 0) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem 0 0 ∧
      reg m' a0 = (if ∀ i : Nat, i < 12 → memLoad32 m.mem (B + 0x420 + BitVec.ofNat 32 c + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (K + BitVec.ofNat 32 (4 * i)) then 1 else 0) := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz st.zero h
  have sp1 : reg n1 sp = B + 0x420 := by rw [r1 sp (by decide)]; exact hsp
  have hFa := F.al
  obtain ⟨n2, c2, pc2, a02, k2, fr2⟩ := uint12Eq_correct n1 (by rw [mem1]; exact E.C3.ueq) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (pv_al F (by omega) ac) aK
    (by rw [sp1, pv_S F]; omega) (by rw [sp1]; exact pv_lowHi F (k := 4) (by decide) (by decide) (by decide) (by decide))
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at a02 fr2
  rw [sp1] at fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 4) hx (by decide)
      (by decide)), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 4) (by decide) (by decide) (by omega)),
      a02⟩
  rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
    r1 q (by revert hq; revert q; decide)]

/-- Limbs whose bytes are all zero. -/
theorem accV_zero_S {M : Word → BitVec 8} {S : Word} {c : Nat} (k : Nat)
    (h : ∀ q, q < 4 * k → M (S + BitVec.ofNat 32 (c + q)) = 0) : accV M (S + BitVec.ofNat 32 c) k = 0 :=
  (accV_eq_zero_iff k).2 fun i hi => by
    rw [ld_ofNat]
    simp only [add_ofNat_assoc, Nat.add_assoc]
    rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]
    decide

/-- Two limbs as a 64-bit word. -/
theorem accV2_S (M : Word → BitVec 8) (S : Word) (c : Nat) :
    accV M (S + BitVec.ofNat 32 c) 2 = W64 (memLoad32 M (S + BitVec.ofNat 32 c)) (memLoad32 M (S + BitVec.ofNat 32 (c + 4))) := by
  simp only [accV, W64, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, add_ofNat_zero,
    show 4 * 1 = 4 from rfl, add_ofNat_assoc, show 32 * 1 = 32 from rfl]
  omega

set_option exponentiation.threshold 600 in
theorem ord_val : dataVal p384OrderData 0 12 = n384 := by unfold n384; decide

/-- `lowest`'s word for an integer: the low 63 bits of its magnitude, negated
modulo `2^64` when it is negative. -/
def lowestI (X : Int) : Nat := lowestVal (if X < 0 then 1 else 0) (X.natAbs % 2 ^ 64)

theorem accV_mod64 (M : Word → BitVec 8) (p : Word) : ∀ k, accV M p (k + 2) % 2 ^ 64 = accV M p 2
  | 0 => Nat.mod_eq_of_lt (accV_lt M p 2)
  | k + 1 => by
    rw [show k + 1 + 2 = (k + 2) + 1 from rfl, accV_succ1, show 32 * (k + 2) = 64 + 32 * k by omega, Nat.pow_add,
      Nat.mul_comm (2 ^ 64), ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
    exact accV_mod64 M p k

theorem lowestI_of {σ A : Nat} {X : Int} (hσ : σ ≤ 1) (h : sgnVal σ A = X) :
    lowestVal σ (A % 2 ^ 64) = lowestI X := by
  obtain ⟨n1, n2, n3⟩ := sgnVal_rep hσ h
  unfold lowestI
  rcases Int.lt_trichotomy X 0 with h0 | h0 | h0
  · obtain ⟨e1, e2⟩ := n1 h0; rw [ite_eq_left h0, e1, e2]
  · rw [n3 h0, h0]; unfold lowestVal; split <;> simp
  · obtain ⟨e1, e2⟩ := n2 h0; rw [ite_eq_right (by omega), e1, e2]

/-- `lowest`'s result for a value held as a sign byte and 12 limbs. -/
theorem lowest_sv {M : Word → BitVec 8} {p a : Word} {X : Int} (hσ : (M a).toNat ≤ 1)
    (h : sgnVal (M a).toNat (accV M p 12) = X) : lowestVal (M a).toNat (accV M p 2) = lowestI X := by
  rw [← accV_mod64 M p 10]; exact lowestI_of hσ h

theorem umin_ofNat {r : Nat} (h : r < 2 ^ 32) :
    (if (BitVec.ofNat 32 r).toNat < 62 then BitVec.ofNat 32 r else 62) = BitVec.ofNat 32 (min r 62) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  by_cases hr : r < 62
  · rw [ite_eq_left hr, Nat.min_eq_left (by omega)]
  · rw [ite_eq_right hr, Nat.min_eq_right (by omega)]; rfl

end C3.RV32.Pv
