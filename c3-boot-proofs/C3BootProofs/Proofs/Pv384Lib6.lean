import C3BootProofs.Proofs.Pv384Lib5
import C3BootProofs.Proofs.Dec384Calls
import C3BootProofs.Proofs.CondSelect
import C3BootProofs.Proofs.P384Retrieve
import C3BootProofs.Proofs.CtWrap
import C3BootProofs.Proofs.P384Mont

/-!
# `p384_verify_prehash`: the calls of the last stage

Wrappers for the calls that turn the sum into an affine `x` coordinate
and compare it with `r`: the field multiplication and retrieval, the
`CtOption` map and `unwrap_or`, `bytes2scalar` of bytes in the frame, and
the scalar comparison.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- The functions of the last stage that no earlier stage calls. -/
structure PvCode7 (M : Word → BitVec 8) : Prop where
  cmap : CodeIn M CMAP ctMap384Code
  rt : CodeIn M RT p384FieldRetrieveCode

theorem PvCode7.hi {M M' : Word → BitVec 8} (C : PvCode7 M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    PvCode7 M' :=
  ⟨codeHi C.cmap (by decide) (by decide) h, codeHi C.rt (by decide) (by decide) h⟩

/-- Everything the last stage needs. -/
structure PvEnv7 (M : Word → BitVec 8) : Prop where
  E : PvEnv6 M
  C7 : PvCode7 M
  aid : CodeIn M (BitVec.ofNat 32 p384AffineIdentityAddress) p384AffineIdentityData

theorem PvEnv7.fr {B : Word} {M M' : Word → BitVec 8} (E : PvEnv7 M) (F : Fr B 0x21A0)
    (h : ∀ x, PvR B x → M' x = M x) : PvEnv7 M' :=
  have hb : ∀ x, Sep (B + 0xFFFFFE60) (0x21A0 + 0x1A0) x 1 → PvR B x := fun x hx => by
    have := hx.sub (c := 0) (l := 0x230C) (by decide); rwa [add_ofNat_zero] at this
  ⟨E.E.fr F h, E.C7.hi fun x hx => h x (pvR_of_hi F hx),
    F.dataIn (fun x hx => h x (hb x hx)) E.aid (by decide) (by decide)⟩

theorem pv_pmod {M : Word → BitVec 8} (E : PvEnv M) : CodeIn M p3M p384ModulusData := fun i hi => by
  have hb : ∀ i, i < 48 → byteAt p384ParamsData i = byteAt p384ModulusData i := by decide
  have h1 : p384ModulusData.length = 48 := rfl
  have h2 : p384ParamsData.length = 156 := rfl
  rw [show p3M = PARAMS from rfl, E.D.D.params i (by omega), hb i (by omega)]

set_option maxHeartbeats 8000000 in
/-- A call to `ConstMontyForm<p384::FieldParams, 12>::mul`: the Montgomery
product of the limbs at offsets `cx` and `cy` of the frame, at `co`. -/
theorem pv_fmul {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cx cy : Nat} (F : Fr B 0x21A0)
    (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = P3MUL)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cx) (ha2 : reg m a2 = B + 0x420 + BitVec.ofNat 32 cy)
    (hco : co + 48 ≤ 0x1D4C) (hcx : cx + 48 ≤ 0x1D4C) (hcy : cy + 48 ≤ 0x1D4C)
    (aco : co % 4 = 0) (acx : cx % 4 = 0) (acy : cy % 4 = 0)
    (hB : accV m.mem (B + 0x420 + BitVec.ofNat 32 cy) 12 < p384) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 48 ∧
      accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12 =
        p3fm (accV m.mem (B + 0x420 + BitVec.ofNat 32 cx) 12) (accV m.mem (B + 0x420 + BitVec.ofNat 32 cy) 12) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + 0xFFFFFF10) 0xF0 b l := fun b l hb hl => FS.lowHi (by decide) rfl hb hl
  have EN : P3MEnv n1.mem P3MUL (B + 0x420) (B + 0x420 + BitVec.ofNat 32 co)
      (B + 0x420 + BitVec.ofNat 32 cx) (B + 0x420 + BitVec.ofNat 32 cy) := by
    rw [mem1]
    refine ⟨by decide, E.C.K.p3mul, pv_pmod E, ?_⟩
    rw [p3mul_mm]
    refine ⟨by decide, E.C.K.mm, by rw [mm_mset]; exact E.C.K.mset, by rw [mm_bsub]; exact E.C.K.bsub,
      by rw [mm_sel]; exact E.C.K.sel, by rw [mm_stub]; exact E.C.K.stub, by rw [mm_body]; exact E.C.K.body,
      by omega, by omega, by rw [FS.at _ (by omega)]; omega,
      by rw [FS.at _ (by omega)]; omega, by rw [FS.at _ (by omega)]; omega, by decide,
      by rw [FS.at _ (by omega)]; omega,
      lh _ _ (by decide) (by decide), lh _ _ (by rw [mm_mset]; decide) (by rw [mm_mset]; decide),
      lh _ _ (by rw [mm_bsub]; decide) (by rw [mm_bsub]; decide), lh _ _ (by rw [mm_sel]; decide) (by rw [mm_sel]; decide),
      lh _ _ (by rw [mm_stub]; decide) (by rw [mm_stub]; decide), lh _ _ (by rw [mm_body]; decide) (by rw [mm_body]; decide),
      FS.lowN (k := 0xF0) (by decide) (by decide) (by omega), FS.sepHi (by omega) (by decide) (by decide),
      by rw [mm_sel]; exact FS.sepHi (by omega) (by decide) (by decide),
      by rw [mm_body]; exact FS.sepHi (by omega) (by decide) (by decide),
      FS.lowN (k := 0xF0) (by decide) (by decide) (by omega), FS.lowN (k := 0xF0) (by decide) (by decide) (by omega),
      pv_lowK F (n := 48) (k := 0xF0) (by decide) (by decide) (by decide)⟩
  obtain ⟨n2, c2, pc2, sp2, k2, val2, fr2⟩ := p384Mul_correct n1 EN pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) (by rw [r1 sp (by decide)]; exact hsp) (by rw [mem1, limbVal_wordsAt]; exact hB)
  rw [mem1, limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt] at val2
  rw [mem1] at fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0xF0) hx (by decide) (by decide))
      (pvR_hi hx hco), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 0xF0) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), val2⟩
  by_cases h : q = sp
  · subst h; rw [sp2, hsp]
  · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]

set_option maxHeartbeats 8000000 in
/-- A call to `ConstMontyForm<p384::FieldParams, 12>::retrieve`: the limbs
at offset `cx` of the frame, out of Montgomery form, at `co`. -/
theorem pv_rt {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cx : Nat} (F : Fr B 0x21A0)
    (E : PvEnv7 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = RT)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cx) (hco : co + 48 ≤ 0x1D4C) (hcx : cx + 48 ≤ 0x1D4C)
    (aco : co % 4 = 0) (acx : cx % 4 = 0) (hX : accV m.mem (B + 0x420 + BitVec.ofNat 32 cx) 12 < p384) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 48 ∧
      accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12 = p3fm (accV m.mem (B + 0x420 + BitVec.ofNat 32 cx) 12) 1 := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  have E1 := E.E.E.E.E.E
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E1.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + 0xFFFFFFB0) 0x50 b l := fun b l hb hl => FS.lowHi (by decide) rfl hb hl
  have EN : P3REnv n1.mem RT (B + 0x420) (B + 0x420 + BitVec.ofNat 32 co) (B + 0x420 + BitVec.ofNat 32 cx) := by
    rw [mem1]
    refine ⟨by decide, E.C7.rt, pv_pmod E1, ?_⟩
    refine ⟨by decide, by rw [rt_mr]; exact E.E.E.C5.mr, by rw [rt_mset]; exact E1.C.K.mset,
      by rw [rt_stub]; exact E1.C.K.stub, by rw [rt_body]; exact E1.C.K.body, by omega, by omega,
      pv_al F (by omega) aco, pv_al F (by omega) acx, by decide, pv_wr F (by omega),
      lh _ _ (by rw [rt_mr]; decide) (by rw [rt_mr]; decide), lh _ _ (by rw [rt_mset]; decide) (by rw [rt_mset]; decide),
      lh _ _ (by rw [rt_stub]; decide) (by rw [rt_stub]; decide), lh _ _ (by rw [rt_body]; decide) (by rw [rt_body]; decide),
      FS.lowN (k := 0x50) (by decide) (by decide) (by omega),
      by rw [rt_mr]; exact FS.sepHi (by omega) (by decide) (by decide),
      by rw [rt_body]; exact FS.sepHi (by omega) (by decide) (by decide),
      FS.lowN (k := 0x50) (by decide) (by decide) (by omega),
      pv_lowK F (n := 48) (k := 0x50) (by decide) (by decide) (by decide)⟩
  obtain ⟨n2, c2, pc2, sp2, k2, val2, fr2⟩ := p384FieldRetrieve_correct n1 EN pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) (by rw [r1 sp (by decide)]; exact hsp) (by rw [mem1]; exact hX)
  rw [mem1] at val2 fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0x50) hx (by decide) (by decide))
      (pvR_hi hx hco), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x50) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), val2⟩
  by_cases h : q = sp
  · subst h; rw [sp2, hsp]
  · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]

theorem accV_of_words {M M' : Word → BitVec 8} {b b' : Word} {c : Prop} [Decidable c]
    (h : ∀ i, i < 12 → memLoad32 M' (b' + BitVec.ofNat 32 (4 * i)) =
      if c then memLoad32 M (b + BitVec.ofNat 32 (4 * i)) else 0) :
    accV M' b' 12 = if c then accV M b 12 else 0 := by
  by_cases hc : c
  · rw [ite_eq_left hc]
    exact accV_congr2 12 fun i hi => by rw [h i hi, ite_eq_left hc]
  · rw [ite_eq_right hc]
    exact (accV_eq_zero_iff 12).2 fun i hi => by rw [h i hi, ite_eq_right hc]

set_option maxHeartbeats 8000000 in
/-- A call to `CtOption<MontyFieldElement<p384>>::map`: with the choice
byte at offset `cx + 0x30` of the frame, the limbs at `cx` or zeros at `co`,
and the choice after them. -/
theorem pv_cmap {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cx : Nat} (F : Fr B 0x21A0)
    (E : PvEnv7 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = CMAP)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cx) (hco : co + 0x31 ≤ 0x1D4C) (hcx : cx + 0x31 ≤ 0x1D4C)
    (acx : cx % 4 = 0)
    (hc : m.mem (B + 0x420 + BitVec.ofNat 32 (cx + 0x30)) = 0 ∨ m.mem (B + 0x420 + BitVec.ofNat 32 (cx + 0x30)) = 1) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 0x31 ∧
      accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12 =
        (if m.mem (B + 0x420 + BitVec.ofNat 32 (cx + 0x30)) = 1 then accV m.mem (B + 0x420 + BitVec.ofNat 32 cx) 12
          else 0) ∧
      m'.mem (B + 0x420 + BitVec.ofNat 32 (co + 0x30)) = m.mem (B + 0x420 + BitVec.ofNat 32 (cx + 0x30)) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  have E1 := E.E.E.E.E.E
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E1.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + 0xFFFFFF60) 0xA0 b l := fun b l hb hl => FS.lowHi (by decide) rfl hb hl
  have EN : CMEnv n1.mem CMAP (B + 0x420) (B + 0x420 + BitVec.ofNat 32 co) (B + 0x420 + BitVec.ofNat 32 cx) := by
    rw [mem1]
    refine ⟨by decide, E.C7.cmap, by rw [cmap_mset]; exact E1.C.K.mset, by rw [cmap_cs]; exact E1.C.K.csel,
      by rw [cmap_stub]; exact E1.C.K.stub, by rw [cmap_body]; exact E1.C.K.body, by rw [cmap_cta]; exact E1.C.K.cta,
      by rw [cmap_sca]; exact E1.C.K.sca, by omega, by omega, pv_al F (by omega) acx, pv_wr F (by omega),
      lh _ _ (by decide) (by decide), lh _ _ (by rw [cmap_mset]; decide) (by rw [cmap_mset]; decide),
      lh _ _ (by rw [cmap_cs]; decide) (by rw [cmap_cs]; decide), lh _ _ (by rw [cmap_stub]; decide)
        (by rw [cmap_stub]; decide), lh _ _ (by rw [cmap_body]; decide) (by rw [cmap_body]; decide),
      lh _ _ (by rw [cmap_cta]; decide) (by rw [cmap_cta]; decide), lh _ _ (by rw [cmap_sca]; decide)
        (by rw [cmap_sca]; decide),
      FS.sepHi (by omega) (by decide) (by decide), by rw [cmap_cs]; exact FS.sepHi (by omega) (by decide) (by decide),
      by rw [cmap_body]; exact FS.sepHi (by omega) (by decide) (by decide),
      FS.lowN (k := 0xA0) (by decide) (by decide) (by omega), FS.lowN (k := 0xA0) (by decide) (by decide) (by omega)⟩
  obtain ⟨n2, c2, pc2, sp2, vals, top, k2, fr2⟩ := ctMap384_correct n1 EN pc1 (by rw [r1 sp (by decide)]; exact hsp)
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [mem1, add_lit30]; exact hc) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1, add_lit30] at vals top
  rw [add_lit30] at top
  rw [mem1] at fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0xA0) hx (by decide) (by decide))
      (pvR_hi hx hco), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 0xA0) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), accV_of_words vals, top⟩
  by_cases h : q = sp
  · subst h; rw [sp2, hsp]
  · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]

/-- Frame bytes against a constant. -/
theorem pv_dat {B K : Word} (F : Fr B 0x21A0) {c n len : Nat} (h : c + n ≤ 0x1D80) (hK : 0x3FCC4200 ≤ K.toNat)
    (hK' : K.toNat + len ≤ 0x3FCC4E60) : Sep (B + 0x420 + BitVec.ofNat 32 c) n K len := by
  have := F.bufData (c := 0x420 + c) (n := n) (by omega) hK hK'
  rwa [← add_ofNat_assoc] at this

theorem add_lit64 (S : Word) (c : Nat) : S + BitVec.ofNat 32 c + 0x64 = S + BitVec.ofNat 32 (c + 0x64) :=
  add_ofNat_assoc S c 0x64

theorem accV_ite {M M' : Word → BitVec 8} {b b' d : Word} {c : Prop} [Decidable c]
    (h : ∀ i, i < 12 → memLoad32 M' (b' + BitVec.ofNat 32 (4 * i)) =
      if c then memLoad32 M (b + BitVec.ofNat 32 (4 * i)) else memLoad32 M (d + BitVec.ofNat 32 (4 * i))) :
    accV M' b' 12 = if c then accV M b 12 else accV M d 12 := by
  by_cases hc : c
  · rw [ite_eq_left hc]
    exact accV_congr2 12 fun i hi => by rw [h i hi, ite_eq_left hc]
  · rw [ite_eq_right hc]
    exact accV_congr2 12 fun i hi => by rw [h i hi, ite_eq_right hc]

abbrev UOR : Word := BitVec.ofNat 32 unwrapOr384Address
abbrev AID : Word := BitVec.ofNat 32 p384AffineIdentityAddress
theorem uor_cs : UOR + 0x1070C = CSEL := by decide
theorem uor_stub : UOR + 0x1070C + 0x101A = MCS := by decide
theorem uor_body : UOR + 0x1070C + 0x101A + 8 = MCS + 8 := by decide
theorem uor_cta : UOR + 0x1070C + 0x2EC = BitVec.ofNat 32 uint12CtAssignAddress := by decide
theorem uor_sca : UOR + 0x1070C + 0x2EC + 0xFFFF9B66 = BitVec.ofNat 32 sliceCtAssignAddress := by decide

theorem aid_x {M : Word → BitVec 8} (h : CodeIn M AID p384AffineIdentityData) : accV M AID 12 = 0 := by
  rw [show AID = AID + BitVec.ofNat 32 0 from (add_ofNat_zero _).symm, code_accV h 0 12 (by decide)]; decide

set_option maxHeartbeats 8000000 in
/-- A call to `CtOption<AffinePoint<NistP384>>::unwrap_or` with the identity
as the default: with the choice byte at offset `cs + 0x64` of the frame, the
`x` coordinate at `cs` or zero at `co`. -/
theorem pv_uo {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cs : Nat} (F : Fr B 0x21A0)
    (E : PvEnv7 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = UOR)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cs) (ha2 : reg m a2 = AID) (hco : co + 0x61 ≤ 0x1D4C)
    (hcs : cs + 0x65 ≤ 0x1D4C) (acs : cs % 4 = 0) (sos : co + 0x61 ≤ cs ∨ cs + 0x65 ≤ co)
    (hc : m.mem (B + 0x420 + BitVec.ofNat 32 (cs + 0x64)) = 0 ∨ m.mem (B + 0x420 + BitVec.ofNat 32 (cs + 0x64)) = 1) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 0x61 ∧
      accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12 =
        (if m.mem (B + 0x420 + BitVec.ofNat 32 (cs + 0x64)) = 1 then accV m.mem (B + 0x420 + BitVec.ofNat 32 cs) 12
          else 0) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  have E1 := E.E.E.E.E.E
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E1.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + 0xFFFFFF80) 0x80 b l := fun b l hb hl => FS.lowHi (by decide) rfl hb hl
  have EN : UOEnv n1.mem UOR (B + 0x420) (B + 0x420 + BitVec.ofNat 32 co) (B + 0x420 + BitVec.ofNat 32 cs) AID := by
    rw [mem1]
    refine ⟨by decide, E1.C.K.uor, by rw [uor_cs]; exact E1.C.K.csel, by rw [uor_stub]; exact E1.C.K.stub,
      by rw [uor_body]; exact E1.C.K.body, by rw [uor_cta]; exact E1.C.K.cta, by rw [uor_sca]; exact E1.C.K.sca,
      by omega, by omega, pv_al F (by omega) acs, pv_wr F (by omega), by decide, pv_wr F (by omega),
      lh _ _ (by decide) (by decide), lh _ _ (by rw [uor_cs]; decide) (by rw [uor_cs]; decide),
      lh _ _ (by rw [uor_stub]; decide) (by rw [uor_stub]; decide), lh _ _ (by rw [uor_body]; decide)
        (by rw [uor_body]; decide), lh _ _ (by rw [uor_cta]; decide) (by rw [uor_cta]; decide),
      lh _ _ (by rw [uor_sca]; decide) (by rw [uor_sca]; decide),
      FS.sepHi (by omega) (by decide) (by decide), by rw [uor_cs]; exact FS.sepHi (by omega) (by decide) (by decide),
      by rw [uor_body]; exact FS.sepHi (by omega) (by decide) (by decide),
      by rw [uor_stub]; exact FS.sepHi (by omega) (by decide) (by decide),
      by rw [uor_cta]; exact FS.sepHi (by omega) (by decide) (by decide),
      by rw [uor_sca]; exact FS.sepHi (by omega) (by decide) (by decide),
      FS.lowN (k := 0x80) (by decide) (by decide) (by omega), FS.lowN (k := 0x80) (by decide) (by decide) (by omega),
      pv_lowK F (n := 0x61) (k := 0x80) (by decide) (by decide) (by decide),
      sepS (B + 0x420) sos (by omega) (by omega), pv_dat F (by omega) (by decide) (by decide)⟩
  obtain ⟨n2, c2, pc2, sp2, wx, wy, w60, k2, fr2⟩ := unwrapOr384_correct n1 EN pc1 (by rw [r1 sp (by decide)]; exact hsp)
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2)
    (by rw [mem1, add_lit64]; exact hc) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1, add_lit64] at wx
  rw [mem1] at fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0x80) hx (by decide) (by decide))
      (pvR_hi hx hco), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x80) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), ?_⟩
  · by_cases h : q = sp
    · subst h; rw [sp2, hsp]
    · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · rw [accV_ite wx, aid_x E.aid]

abbrev MCE : Word := BitVec.ofNat 32 montyScalarCtEq384Address
theorem mce_uce : MCE + 0xFFFFFAF4 = BitVec.ofNat 32 uint12CtEqAddress := by decide
theorem mce_spl : MCE + 0xFFFFFAF4 + 0x80 = BitVec.ofNat 32 splitAt12Address := by decide
theorem mce_lce : MCE + 0xFFFFFAF4 + 0xFFFF9DBC = BitVec.ofNat 32 limbCtEqAddress := by decide
theorem mce_uiz : MCE + 0xFFFFFAF4 + 0xFFFEF3C4 = BitVec.ofNat 32 uintRefIsZeroAddress := by decide
theorem mce_unz : MCE + 0xFFFFFAF4 + 0xFFFEF3C4 + 0x1A = BitVec.ofNat 32 uintRefIsNonzeroAddress := by decide
theorem mce_bb : MCE + 0xFFFF99AA = BitVec.ofNat 32 blackBoxU8Address := by decide

set_option maxHeartbeats 8000000 in
/-- A call to `ConstMontyForm<p384::ScalarParams, 12>::ct_eq` on the limbs
at offsets `ca` and `cb` of the frame. -/
theorem pv_mseq {B : Word} {m : Machine} {off : Nat} {imm o : Word} {ca cb : Nat} (F : Fr B 0x21A0)
    (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = MCE)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 ca)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cb) (hca : ca + 48 ≤ 0x1D4C) (hcb : cb + 48 ≤ 0x1D4C)
    (aca : ca % 4 = 0) (acb : cb % 4 = 0) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem 0 0 ∧
      reg m' a0 = (if accV m.mem (B + 0x420 + BitVec.ofNat 32 ca) 12 = accV m.mem (B + 0x420 + BitVec.ofNat 32 cb) 12
        then 1 else 0) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + 0xFFFFFFAC) 0x54 b l := fun b l hb hl => FS.lowHi (by decide) rfl hb hl
  have EN : MSEnv n1.mem MCE (B + 0x420) (B + 0x420 + BitVec.ofNat 32 ca) (B + 0x420 + BitVec.ofNat 32 cb) := by
    rw [mem1]
    refine ⟨by decide, E.C2.mce, by rw [mce_uce]; exact E.C.K.uce, by rw [mce_spl]; exact E.C.K.spl,
      by rw [mce_lce]; exact E.C.K.lce, by rw [mce_uiz]; exact E.C.K.uiz, by rw [mce_unz]; exact E.C.K.refnz,
      by rw [mce_bb]; exact E.C.K.bb, by omega, by omega, pv_al F (by omega) aca, pv_al F (by omega) acb,
      lh _ _ (by decide) (by decide), lh _ _ (by rw [mce_uce]; decide) (by rw [mce_uce]; decide),
      lh _ _ (by rw [mce_spl]; decide) (by rw [mce_spl]; decide), lh _ _ (by rw [mce_lce]; decide)
        (by rw [mce_lce]; decide), lh _ _ (by rw [mce_uiz]; decide) (by rw [mce_uiz]; decide),
      lh _ _ (by rw [mce_unz]; decide) (by rw [mce_unz]; decide), lh _ _ (by rw [mce_bb]; decide) (by rw [mce_bb]; decide),
      FS.lowN (k := 0x54) (by decide) (by decide) (by omega), FS.lowN (k := 0x54) (by decide) (by decide) (by omega)⟩
  obtain ⟨n2, c2, pc2, sp2, a02, k2, fr2⟩ := montyScalarCtEq384_correct n1 EN pc1 (by rw [r1 sp (by decide)]; exact hsp)
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8)
  rw [mem1] at a02 fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0x54) hx (by decide) (by decide)),
      fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x54) (by decide) (by decide) (by omega)), ?_⟩
  · by_cases h : q = sp
    · subst h; rw [sp2, hsp]
    · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · rw [a02]
    by_cases h : accV m.mem (B + 0x420 + BitVec.ofNat 32 ca) 12 = accV m.mem (B + 0x420 + BitVec.ofNat 32 cb) 12
    · rw [ite_eq_left (accV_inj 12 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (accV_congr2 12 fun i hi => (h' i hi).symm).symm), ite_eq_right h]

set_option maxHeartbeats 8000000 in
/-- A call to `bytes2scalar` on `n` bytes at offset `cb` of the frame. -/
theorem pv_b2sF {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cb n : Nat} (F : Fr B 0x21A0)
    (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BS)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cb) (ha2 : reg m a2 = BitVec.ofNat 32 n) (hco : co + 48 ≤ 0x1D4C)
    (aco : co % 4 = 0) (hcb : cb + n ≤ 0x1D4C) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 48 ∧
      accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12 =
        beNat (memBytes m.mem (B + 0x420 + BitVec.ofNat 32 cb) (min n 48)) * 2 ^ 384 % n384 := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have EB : BZEnv n1.mem := by
    rw [mem1]
    exact ⟨E.C2.bs, E.C2.lz, E.C.K.panic, E.C2.exu, E.C.fb, E.C.K.bsub, E.C.K.bb, E.C2.cn, E.C.K.sca, E.C2.nw,
      E.C.K.mm, E.C.K.sel, E.D2.nmod, E.D2.r2, E.D.n, E.D.lz⟩
  obtain ⟨n2, c2, pc2, sp2, k2, val2, fr2⟩ := bytes2scalar384_correct n1 (sp0 := B + 0x420)
    (out := B + 0x420 + BitVec.ofNat 32 co) EB pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) (by rw [r1 sp (by decide)]; exact hsp) hFa
    (by have := pv_S F; have := F.lo; omega) (by unfold dramEnd; omega) (by rw [FS.at _ (by omega)]; unfold dramEnd; omega)
    (by rw [FS.at _ (by omega)]; omega) (pv_wr F (by omega))
    (pv_lowS F (k := 0x1B0) (by omega) (by decide) (by decide))
    (pv_lowS F (k := 0x1B0) (by omega) (by decide) (by decide))
    (pv_lowK F (n := 48) (k := 0x1B0) (by decide) (by decide) (by decide)).symm
    (pv_lowK F (n := 48) (k := 0x1B0) (by decide) (by decide) (by decide)).symm
    (pv_lowK F (n := 48) (k := 0x1B0) (by decide) (by decide) (by decide)).symm
  rw [mem1] at val2 fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0x1B0) hx (by decide)
      (by decide)) (pvR_hi hx hco), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x1B0) (by decide)
      (by decide) (by omega)) (sepS (B + 0x420) (by omega) (by omega) (by omega)), val2⟩
  by_cases h : q = sp
  · subst h; rw [sp2, hsp]
  · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]

theorem ite10_ff (c : Prop) [Decidable c] : ((if c then 1 else 0 : Word) &&& 0xFF) = if c then 1 else 0 := by
  by_cases h : c
  · rw [ite_eq_left h]; rfl
  · rw [ite_eq_right h]; rfl

theorem ite10_snez (c : Prop) [Decidable c] :
    aluEval .sltu 0 (aluEval .and (if c then 1 else 0 : Word) 0xFF) = if c then 1 else 0 := by
  by_cases h : c
  · rw [ite_eq_left h]; rfl
  · rw [ite_eq_right h]; rfl

theorem okb (c : Prop) [Decidable c] {zf : Word} (hz : zf = 0 ∨ zf = 1) :
    (((if c then 1 else 0 : Word) &&& zf).extractLsb' 0 8).zeroExtend 32 = if c ∧ zf = 1 then 1 else 0 := by
  by_cases h : c
  · rcases hz with rfl | rfl
    · rw [ite_eq_left h, ite_eq_right (fun h' => absurd h'.2 (by decide))]; rfl
    · rw [ite_eq_left h, ite_eq_left ⟨h, rfl⟩]; rfl
  · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.1)]
    rcases hz with rfl | rfl <;> rfl

theorem beNat_foldl : ∀ (l : List Nat) (a : Nat),
    l.foldl (fun acc x => acc * 256 + x) a = a * 256 ^ l.length + leN l.reverse
  | [], a => by simp only [List.foldl_nil, List.length_nil, Nat.pow_zero, Nat.mul_one, List.reverse_nil, leN,
      Nat.add_zero]
  | x :: l, a => by
    rw [List.foldl_cons, beNat_foldl l, List.reverse_cons, leN_append, List.length_cons, List.length_reverse]
    simp only [leN, Nat.mul_zero, Nat.add_zero, Nat.pow_succ]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ l.length), Nat.mul_comm x (256 ^ l.length)]
    omega

theorem beNat_eq_leN (l : List Nat) : beNat l = leN l.reverse := by
  rw [beNat, beNat_foldl, Nat.zero_mul, Nat.zero_add]

end C3.RV32.Pv
