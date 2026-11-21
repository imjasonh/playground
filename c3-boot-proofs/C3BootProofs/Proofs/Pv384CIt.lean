import C3BootProofs.Proofs.Pv384CA
import C3BootProofs.Proofs.Pv384CB

/-!
# `p384_verify_prehash`: the inversion of `s`, one batch at a time

The loop from 0x3EC to 0x624 stops when `g`'s low 12 limbs are all zero,
and otherwise runs a batch of `min rem 62` divsteps and applies its matrix
to `f`, `g`, `d`, and `e`. `ivStep` is that batch on integers, and
`pv_iter` proves the loop's body runs it.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- `-n⁻¹ mod 2^64`, as the loop holds it in `s4` and `s6`. -/
abbrev pvMI : Nat := (BitVec.ofNat 32 0x177023BB).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x912B9F76).toNat

/-- The inversion's state: `δ` as a 64-bit word, `f`, `g`, `d`, and `e`, and
the steps left. -/
structure Iv where
  δ : Nat
  f : Int
  g : Int
  d : Int
  e : Int
  rem : Nat

/-- One batch: `min rem 62` divsteps on the low words of `f` and `g`, then
their matrix applied to `f`, `g`, `d`, and `e`. -/
def ivStep (s : Iv) : Iv :=
  let n := min s.rem 62
  let t := dsIter n ⟨s.δ, lowestI s.f, lowestI s.g, 1, 0, 0, 1⟩
  ⟨t.δ, fgUpd s.f s.g (i64Val t.u) (i64Val t.v) n, fgUpd s.f s.g (i64Val t.q) (i64Val t.r) n,
    deUpd s.d s.e (i64Val t.u) (i64Val t.v) pvMI n (dataVal p384OrderData 0 12),
    deUpd s.d s.e (i64Val t.q) (i64Val t.r) pvMI n (dataVal p384OrderData 0 12), s.rem - n⟩

/-- Batches until no steps are left or `g` is zero, with `k` batches at most. -/
def ivLoop : Nat → Iv → Iv
  | 0, s => s
  | k + 1, s => if s.rem = 0 ∨ s.g = 0 then s else ivLoop k (ivStep s)

theorem ofNat_pred (i : Nat) : BitVec.ofNat 32 (i + 1) + (0xFFFFFFFF : Word) = BitVec.ofNat 32 i := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl,
    show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_add_mod,
    show i + 1 + 4294967295 = i + 4294967296 by omega, Nat.add_mod_right]

def scB : List BInstr := [.lw a2 a1 0x0, .aluImm .add a0 a0 0x1, .aluImm .add a1 a1 0x4]
theorem scB_end : blockEnd p384VerifyPrehashCode 0x3FA scB = some 0x400 := by decide

/-- **The scan** at 0x3F6 for a nonzero limb of `g`, from limb `i`: to 0x628
when all 12 are zero, and to 0x406 otherwise. -/
theorem pv_scan {Mx : Word → BitVec 8} {B : Word} (F : Fr B 0x21A0) (hc : CodeIn Mx PV p384VerifyPrehashCode) :
    ∀ j i {m : Machine}, i + j = 12 → St Mx PV m 0x3F6 (reg m) → reg m a0 = BitVec.ofNat 32 i + 0xFFFFFFFF →
      reg m a1 = B + 0x420 + BitVec.ofNat 32 0xD50 + BitVec.ofNat 32 (4 * i) → reg m 26 = BitVec.ofNat 32 0xB →
      (∀ k, k < i → memLoad32 Mx (B + 0x420 + BitVec.ofNat 32 0xD50 + BitVec.ofNat 32 (4 * k)) = 0) →
      ∃ m', Steps m m' ∧ (∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m' q = reg m q) ∧
        (((∀ k, k < 12 → memLoad32 Mx (B + 0x420 + BitVec.ofNat 32 0xD50 + BitVec.ofNat 32 (4 * k)) = 0) ∧
          St Mx PV m' 0x628 (reg m')) ∨
         ((¬ ∀ k, k < 12 → memLoad32 Mx (B + 0x420 + BitVec.ofNat 32 0xD50 + BitVec.ofNat 32 (4 * k)) = 0) ∧
          St Mx PV m' 0x406 (reg m'))) := by
  intro j
  induction j with
  | zero =>
    intro i m hij st h0 _ h26 hz
    obtain rfl : i = 12 := by omega
    obtain ⟨m1, d1, u1⟩ := st.taken hc 0x628 pv_at_3f6 (by decide)
      (by show (reg m a0 == reg m 26) = true; rw [h0, h26, ofNat_pred 11]; rfl)
    exact ⟨m1, .single d1, fun q _ _ _ => u1.regs q, .inl ⟨hz, u1.self⟩⟩
  | succ j ih =>
    intro i m hij st h0 h1 h26 hz
    have hi : i < 12 := by omega
    have hne : reg m a0 ≠ reg m 26 := by
      rw [h0, h26]
      cases i with
      | zero => decide
      | succ i =>
        rw [ofNat_pred i]; intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        omega
    obtain ⟨m1, d1, u1⟩ := st.notTaken hc 0x3FA pv_at_3f6 (by decide)
      (by show (reg m a0 == reg m 26) = false; simpa using hne)
    have hal : (B + 0x420 + BitVec.ofNat 32 0xD50 + BitVec.ofNat 32 (4 * i)).toNat % 4 = 0 := by
      rw [add_ofNat_assoc]; exact pv_al F (by omega) (by omega)
    obtain ⟨m2, c2, u2⟩ := u1.self.block scB hc scB_end
      ⟨by show (reg m1 a1 + 0x0).toNat % 4 = 0
          rw [u1.regs, h1, show (0x0 : Word) = BitVec.ofNat 32 0 from rfl, add_ofNat_zero]; exact hal,
        trivial, trivial, trivial⟩
    have s2 : St Mx PV m2 0x400 (reg m2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
    have e1 : reg m1 = reg m := funext u1.regs
    have r2a2 : reg m2 a2 = memLoad32 Mx (B + 0x420 + BitVec.ofNat 32 0xD50 + BitVec.ofNat 32 (4 * i)) := by
      rw [u2.regs, e1]; simp +decide only [runBlock, BInstr.run, scB, upd, ↓reduceIte, aluEval]
      rw [h1, show (0x0 : Word) = BitVec.ofNat 32 0 from rfl, add_ofNat_zero]
    have r2a0 : reg m2 a0 = BitVec.ofNat 32 i := by
      rw [u2.regs, e1]; simp +decide only [runBlock, BInstr.run, scB, upd, ↓reduceIte, aluEval]
      rw [h0, BitVec.add_assoc, show (0xFFFFFFFF : Word) + 0x1 = 0 from rfl]; exact BitVec.add_zero _
    have r2a1 : reg m2 a1 = B + 0x420 + BitVec.ofNat 32 0xD50 + BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [u2.regs, e1]; simp +decide only [runBlock, BInstr.run, scB, upd, ↓reduceIte, aluEval]
      rw [h1, BitVec.add_assoc, show BitVec.ofNat 32 (4 * i) + 0x4 = BitVec.ofNat 32 (4 * (i + 1)) by
        rw [show (0x4 : Word) = BitVec.ofNat 32 4 from rfl, BitVec.ofNat_add_ofNat, show 4 * i + 4 = 4 * (i + 1) by omega]]
    have k2 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m2 q = reg m q := fun q h0' h1' h2' => by
      have hq : q ∉ scB.filterMap BInstr.dst := by
        simp only [scB, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0', h1', h2']
      rw [u2.regs, e1, runBlock_reg _ _ _ q st.zero hq]
    by_cases hw : memLoad32 Mx (B + 0x420 + BitVec.ofNat 32 0xD50 + BitVec.ofNat 32 (4 * i)) = 0
    · obtain ⟨m3, d3, u3⟩ := s2.taken hc 0x3F6 pv_at_400 (by decide)
        (by show (reg m2 a2 == reg m2 x0) = true; rw [r2a2, hw, s2.zero]; rfl)
      obtain ⟨m4, c4, k4, h4⟩ := ih (i + 1) (by omega) u3.self (by rw [u3.regs, r2a0, ofNat_pred i])
        (by rw [u3.regs, r2a1]) (by rw [u3.regs, k2 26 (by decide) (by decide) (by decide), h26])
        (fun k hk => by
          rcases Nat.lt_or_ge k i with h | h
          · exact hz k h
          · obtain rfl : k = i := by omega
            exact hw)
      exact ⟨m4, .cons d1 (c2.trans (.cons d3 c4)), fun q h0' h1' h2' => by
        rw [k4 q h0' h1' h2', u3.regs, k2 q h0' h1' h2'], h4⟩
    · obtain ⟨m3, d3, u3⟩ := s2.notTaken hc 0x402 pv_at_400 (by decide)
        (by show (reg m2 a2 == reg m2 x0) = false; rw [r2a2, s2.zero]; simpa using hw)
      obtain ⟨m4, d4, u4⟩ := u3.self.notTaken hc 0x406 pv_at_402 (by decide)
        (by
          show (reg m3 26).ult (reg m3 a0) = false
          rw [u3.regs, u3.regs, k2 26 (by decide) (by decide) (by decide), h26, r2a0]
          simp only [BitVec.ult, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (show i < 2 ^ 32 by omega)]
          simp only [decide_eq_false_iff_not]; omega)
      exact ⟨m4, .cons d1 (c2.trans (.cons d3 (.single d4))), fun q h0' h1' h2' => by
        rw [u4.regs, u3.regs, k2 q h0' h1' h2'], .inr ⟨fun h => hw (h i hi), u4.self⟩⟩

/-- What holds at 0x3EC, the head of the loop, for the state `st`. -/
structure IvInv (B : Word) (m : Machine) (r3 r4 : Word) (QX QY QZ RM SM ZM : Nat) (st : Iv) : Prop where
  sp : reg m sp = B + 0x420
  g3 : reg m (3 : Fin 32) = r3
  g4 : reg m (4 : Fin 32) = r4
  dl : W64 (reg m (21 : Fin 32)) (reg m (19 : Fin 32)) = st.δ
  g20 : reg m (20 : Fin 32) = BitVec.ofNat 32 0x177023BB
  g22 : reg m (22 : Fin 32) = BitVec.ofNat 32 0x912B9F76
  g23 : reg m (23 : Fin 32) = BitVec.ofNat 32 st.rem
  g24 : reg m (24 : Fin 32) = BitVec.ofNat 32 0x1
  g26 : reg m (26 : Fin 32) = BitVec.ofNat 32 0xB
  a120 : accV m.mem (B + 0x420 + BitVec.ofNat 32 0x120) 12 = QX
  a150 : accV m.mem (B + 0x420 + BitVec.ofNat 32 0x150) 12 = QY
  a180 : accV m.mem (B + 0x420 + BitVec.ofNat 32 0x180) 12 = QZ
  a1b0 : accV m.mem (B + 0x420 + BitVec.ofNat 32 0x1B0) 12 = RM
  a1e0 : accV m.mem (B + 0x420 + BitVec.ofNat 32 0x1E0) 12 = SM
  a210 : accV m.mem (B + 0x420 + BitVec.ofNat 32 0x210) 12 = ZM
  ae10 : accV m.mem (B + 0x420 + BitVec.ofNat 32 0xE10) 12 = dataVal p384OrderData 0 12
  ae40 : accV m.mem (B + 0x420 + BitVec.ofNat 32 0xE40) 12 = dataVal p384ScalarR2Data 0 12
  we70 : memLoad32 m.mem (B + 0x420 + BitVec.ofNat 32 0xE70) = BitVec.ofNat 32 0x177023BB
  we74 : memLoad32 m.mem (B + 0x420 + BitVec.ofNat 32 0xE74) = BitVec.ofNat 32 0x912B9F76
  vd : sgnVal (m.mem (B + 0x420 + BitVec.ofNat 32 (0x270 + 0x30))).toNat
    (accV m.mem (B + 0x420 + BitVec.ofNat 32 0x270) 12) = st.d
  ld : (m.mem (B + 0x420 + BitVec.ofNat 32 (0x270 + 0x30))).toNat ≤ 1
  vg : sgnVal (m.mem (B + 0x420 + BitVec.ofNat 32 (0xD50 + 0x30))).toNat
    (accV m.mem (B + 0x420 + BitVec.ofNat 32 0xD50) 12) = st.g
  lg : (m.mem (B + 0x420 + BitVec.ofNat 32 (0xD50 + 0x30))).toNat ≤ 1
  vf : sgnVal (m.mem (B + 0x420 + BitVec.ofNat 32 (0x1714 + 0x30))).toNat
    (accV m.mem (B + 0x420 + BitVec.ofNat 32 0x1714) 12) = st.f
  lf : (m.mem (B + 0x420 + BitVec.ofNat 32 (0x1714 + 0x30))).toNat ≤ 1
  ve : sgnVal (m.mem (B + 0x420 + BitVec.ofNat 32 (0x17A4 + 0x30))).toNat
    (accV m.mem (B + 0x420 + BitVec.ofNat 32 0x17A4) 12) = st.e
  le : (m.mem (B + 0x420 + BitVec.ofNat 32 (0x17A4 + 0x30))).toNat ≤ 1
  rem : st.rem < 2 ^ 32

/-- The invariant moves to a machine with the same memory and the registers
it names. -/
theorem IvInv.of {B r3 r4 : Word} {QX QY QZ RM SM ZM : Nat} {m m' : Machine} {st : Iv}
    (I : IvInv B m r3 r4 QX QY QZ RM SM ZM st) (hm : m'.mem = m.mem)
    (hr : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 19, 20, 21, 22, 23, 24, 26] → reg m' q = reg m q) :
    IvInv B m' r3 r4 QX QY QZ RM SM ZM st := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, I.rem⟩
  · rw [hr 2 (by decide)]; exact I.sp
  · rw [hr 3 (by decide)]; exact I.g3
  · rw [hr 4 (by decide)]; exact I.g4
  · rw [hr 21 (by decide), hr 19 (by decide)]; exact I.dl
  · rw [hr 20 (by decide)]; exact I.g20
  · rw [hr 22 (by decide)]; exact I.g22
  · rw [hr 23 (by decide)]; exact I.g23
  · rw [hr 24 (by decide)]; exact I.g24
  · rw [hr 26 (by decide)]; exact I.g26
  · rw [hm]; exact I.a120
  · rw [hm]; exact I.a150
  · rw [hm]; exact I.a180
  · rw [hm]; exact I.a1b0
  · rw [hm]; exact I.a1e0
  · rw [hm]; exact I.a210
  · rw [hm]; exact I.ae10
  · rw [hm]; exact I.ae40
  · rw [hm]; exact I.we70
  · rw [hm]; exact I.we74
  · rw [hm]; exact I.vd
  · rw [hm]; exact I.ld
  · rw [hm]; exact I.vg
  · rw [hm]; exact I.lg
  · rw [hm]; exact I.vf
  · rw [hm]; exact I.lf
  · rw [hm]; exact I.ve
  · rw [hm]; exact I.le

/-- A value held as a sign byte and 12 limbs is zero exactly when its limbs are. -/
theorem sv_zero {σ A : Nat} : (sgnVal σ A = 0 ↔ A = 0) := by
  unfold sgnVal
  constructor
  · intro h; split at h <;> omega
  · intro h; subst h; split <;> simp

theorem ofNat_sub_ofNat {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega), show 2 ^ 32 - b + a = (a - b) + 2 ^ 32 by omega, Nat.add_mod_right]

def scA : List BInstr := [.aluImm .add a0 x0 0xFFFFFFFF, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x551]
theorem scA_end : blockEnd p384VerifyPrehashCode 0x3EC scA = some 0x3F6 := by decide

set_option maxHeartbeats 16000000 in
/-- **One pass of the loop** at 0x3EC: to 0x628 when `g` is zero, and
otherwise one batch, `ivStep`, back to 0x3EC or, when no steps are left, on
to 0x628. -/
theorem pv_iter {B r3 r4 : Word} {QX QY QZ RM SM ZM : Nat} {m : Machine} {st : Iv} (F : Fr B 0x21A0)
    (E : PvEnv3 m.mem) (s : St m.mem PV m 0x3EC (reg m)) (I : IvInv B m r3 r4 QX QY QZ RM SM ZM st)
    (h0 : st.rem ≠ 0) :
    ∃ m', Steps m m' ∧ PvEnv3 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
      ((st.g = 0 ∧ St m'.mem PV m' 0x628 (reg m') ∧ IvInv B m' r3 r4 QX QY QZ RM SM ZM st) ∨
       (st.g ≠ 0 ∧ IvInv B m' r3 r4 QX QY QZ RM SM ZM (ivStep st) ∧
         (((ivStep st).rem = 0 ∧ St m'.mem PV m' 0x628 (reg m')) ∨
          ((ivStep st).rem ≠ 0 ∧ St m'.mem PV m' 0x3EC (reg m'))))) := by
  have hz := s.zero
  obtain ⟨m1, c1, u1⟩ := s.block scA E.E.C.self scA_end ⟨trivial, trivial, trivial, trivial⟩
  have s1 : St m.mem PV m1 0x3F6 (reg m1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg m1 q = reg m q := fun q h0' h1' => by
    have hq : q ∉ scA.filterMap BInstr.dst := by
      simp only [scA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0', h1']
    rw [u1.regs, runBlock_reg _ _ _ q hz hq]
  have r1a0 : reg m1 a0 = BitVec.ofNat 32 0 + 0xFFFFFFFF := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, scA, upd, ↓reduceIte, aluEval, hz]
  have r1a1 : reg m1 a1 = B + 0x420 + BitVec.ofNat 32 0xD50 + BitVec.ofNat 32 (4 * 0) := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, scA, upd, ↓reduceIte, aluEval, hz]; rw [I.sp]
    rw [show B + 0x420 + 0x7FF + 0x551 = B + 0x420 + BitVec.ofNat 32 0xD50 by
      rw [BitVec.add_assoc]; rfl]; exact (add_ofNat_zero _).symm
  obtain ⟨m2, c2, k2, h2⟩ := pv_scan F E.E.C.self 12 0 rfl s1 r1a0 r1a1
    (by rw [k1 26 (by decide) (by decide)]; exact I.g26) (fun k hk => absurd hk (Nat.not_lt_zero _))
  have kk : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 19, 20, 21, 22, 23, 24, 26] → reg m2 q = reg m q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      k1 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  rcases h2 with ⟨hzr, s2⟩ | ⟨hnz, s2⟩
  · have hg : st.g = 0 := by
      rw [← I.vg, sv_zero.2]
      exact (accV_eq_zero_iff 12).2 hzr
    have m2m : m2.mem = m.mem := s2.mem
    refine ⟨m2, c1.trans c2, by rw [m2m]; exact E, fun x _ => by rw [m2m], .inl ⟨hg, ⟨s2.pc, rfl, fun _ => rfl⟩,
      I.of m2m kk⟩⟩
  · have hg : st.g ≠ 0 := by
      rw [← I.vg]; intro h
      exact hnz ((accV_eq_zero_iff 12).1 (sv_zero.1 h))
    have m2m : m2.mem = m.mem := s2.mem
    have s2' : St m2.mem PV m2 0x406 (reg m2) := ⟨s2.pc, rfl, fun _ => rfl⟩
    have E2 : PvEnv3 m2.mem := by rw [m2m]; exact E
    have I2 := I.of m2m kk
    obtain ⟨n3, t3, s3, E3, f3, g3_2, g3_3, g3_4, g3_5, g3_6, g3_7, g3_9, g3_12, g3_16, g3_17, g3_18, g3_19, g3_20,
      g3_21, g3_22, g3_23, g3_24, g3_26, g3_30, wf3, wg3, a3_120, a3_150, a3_180, a3_1b0, a3_1e0, a3_210, a3_e10,
      a3_e40, w3_54, w3_e70, w3_e74, v3_270, l3_270, v3_d50, l3_d50, v3_1714, l3_1714, v3_17a4, l3_17a4⟩ :=
      pv_stCA (dlo := reg m2 21) (dhi := reg m2 19) (rem := st.rem) (Fv := st.f) (Gv := st.g) (Dv := st.d)
        (Ev := st.e) (QX := QX) (QY := QY) (QZ := QZ) (RM := RM) (SM := SM) (ZM := ZM) F E2 s2' I2.sp rfl rfl rfl I2.g20 rfl I2.g22 I2.g23 I2.g24 I2.g26 I2.a120 I2.a150 I2.a180
        I2.a1b0 I2.a1e0 I2.a210 I2.ae10 I2.ae40 I2.we70 I2.we74 I2.vd I2.ld I2.vg I2.lg I2.vf I2.lf I2.ve I2.le I2.rem
    have hn1 : 1 ≤ min st.rem 62 := by omega
    have hn2 : min st.rem 62 ≤ 62 := Nat.min_le_right _ _
    have hn0 : BitVec.ofNat 32 (min st.rem 62) ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show (0 : Word).toNat = 0 from rfl] at this; omega
    obtain ⟨n4, d4, u4⟩ := s3.notTaken E3.E.C.self 0x44E pv_at_44a (by decide)
      (by show (reg n3 18 == reg n3 x0) = false; rw [g3_18, s3.zero]; simpa using hn0)
    have e4 : reg n4 = reg n3 := funext u4.regs
    have hds : DsRegs (reg n4) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩ := by
      rw [e4]
      refine ⟨by rw [g3_21, g3_19]; exact I2.dl, wf3, wg3, by rw [g3_9, g3_17]; rfl, by rw [g3_12, g3_16]; rfl,
        by rw [g3_24, g3_7]; rfl, by rw [g3_30, g3_6]; rfl⟩
    have hn : min st.rem 62 - 1 + 1 = min st.rem 62 := by omega
    obtain ⟨n5, c5, s5, h5, k5⟩ := ds_loop E3.E.C.self (min st.rem 62 - 1) u4.self hds
      (by rw [e4, g3_5, hn]) (by omega)
    rw [hn] at h5
    have m5 : n5.mem = n3.mem := s5.mem
    have s5' : St n5.mem PV n5 0x530 (reg n5) := ⟨s5.pc, rfl, fun _ => rfl⟩
    have E5 : PvEnv3 n5.mem := by rw [m5]; exact E3
    have k5' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 22, 23, 26] → reg n5 q = reg n3 q := fun q hq => by
      rw [k5 q hq, e4]
    obtain ⟨n6, t6, s6, E6, f6, g6_2, g6_3, g6_4, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_26, a6_120, a6_150,
      a6_180, a6_1b0, a6_1e0, a6_210, a6_e10, a6_e40, w6_e70, w6_e74, v6_270, l6_270, v6_d50, l6_d50, v6_1714,
      l6_1714, v6_17a4, l6_17a4⟩ :=
      pv_stCB (n := min st.rem 62) (rem := st.rem) (dlo := reg n5 21) (dhi := reg n5 19) (ulo := reg n5 9)
        (uhi := reg n5 17) (vlo := reg n5 12) (vhi := reg n5 16) (qlo := reg n5 24) (qhi := reg n5 7)
        (rlo := reg n5 30) (rhi := reg n5 6) (Fv := st.f) (Gv := st.g) (Dv := st.d) (Ev := st.e)
        (QX := QX) (QY := QY) (QZ := QZ) (RM := RM) (SM := SM) (ZM := ZM)
        F E5 s5' (by rw [k5' 2 (by decide)]; exact g3_2) rfl rfl rfl rfl rfl rfl rfl rfl
        (by rw [k5' 18 (by decide)]; exact g3_18) rfl (by rw [k5' 20 (by decide)]; exact g3_20) rfl
        (by rw [k5' 22 (by decide)]; exact g3_22) (by rw [k5' 23 (by decide)]; exact g3_23) rfl
        (by rw [k5' 26 (by decide)]; exact g3_26) rfl
        (by rw [m5]; exact a3_120) (by rw [m5]; exact a3_150) (by rw [m5]; exact a3_180) (by rw [m5]; exact a3_1b0)
        (by rw [m5]; exact a3_1e0) (by rw [m5]; exact a3_210) (by rw [m5]; exact a3_e10) (by rw [m5]; exact a3_e40)
        (by rw [m5]; exact w3_54) (by rw [m5]; exact w3_e70) (by rw [m5]; exact w3_e74)
        (by rw [m5]; exact v3_270) (by rw [m5]; exact l3_270) (by rw [m5]; exact v3_d50) (by rw [m5]; exact l3_d50)
        (by rw [m5]; exact v3_1714) (by rw [m5]; exact l3_1714) (by rw [m5]; exact v3_17a4)
        (by rw [m5]; exact l3_17a4) hn1 hn2
    obtain ⟨hδ, -, -, hu, hv, hq, hr⟩ := h5
    rw [hu, hv] at v6_270 v6_1714
    rw [hq, hr] at v6_d50 v6_17a4
    have I6 : IvInv B n6 r3 r4 QX QY QZ RM SM ZM (ivStep st) :=
      ⟨g6_2, by rw [g6_3, k5' 3 (by decide), g3_3]; exact I2.g3, by rw [g6_4, k5' 4 (by decide), g3_4]; exact I2.g4,
        by rw [g6_21, g6_19]; exact hδ, g6_20, g6_22,
        by rw [g6_23, ofNat_sub_ofNat (Nat.min_le_left _ _) I.rem]; rfl, g6_24, g6_26, a6_120, a6_150, a6_180,
        a6_1b0, a6_1e0, a6_210, a6_e10, a6_e40, w6_e70, w6_e74, v6_270, l6_270, v6_d50, l6_d50, v6_1714, l6_1714,
        v6_17a4, l6_17a4, by show st.rem - min st.rem 62 < 2 ^ 32; have := I.rem; omega⟩
    have fr : ∀ x, PvR B x → n6.mem x = m.mem x := fun x hx => by
      rw [f6 x hx, m5, f3 x hx, m2m]
    by_cases hz' : st.rem - min st.rem 62 = 0
    · obtain ⟨n7, d7, u7⟩ := s6.notTaken E6.E.C.self 0x628 pv_at_624 (by decide)
        (by show (reg n6 23 != reg n6 x0) = false; rw [I6.g23, s6.zero]
            show (BitVec.ofNat 32 (st.rem - min st.rem 62) != 0) = false; rw [hz']; rfl)
      exact ⟨n7, c1.trans (c2.trans (t3.trans (.cons d4 (c5.trans (t6.trans (.single d7)))))),
        by rw [u7.mem]; exact E6, fun x hx => by rw [u7.mem]; exact fr x hx,
        .inr ⟨hg, I6.of u7.mem fun q _ => u7.regs q, .inl ⟨hz', ⟨u7.pc, rfl, fun _ => rfl⟩⟩⟩⟩
    · have hne : BitVec.ofNat 32 (st.rem - min st.rem 62) ≠ 0 := by
        intro e; have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := I.rem; omega), show (0 : Word).toNat = 0 from rfl] at this
        exact hz' this
      obtain ⟨n7, d7, u7⟩ := s6.taken E6.E.C.self 0x3EC pv_at_624 (by decide)
        (by show (reg n6 23 != reg n6 x0) = true; rw [I6.g23, s6.zero]
            show (BitVec.ofNat 32 (st.rem - min st.rem 62) != 0) = true; simpa using hne)
      exact ⟨n7, c1.trans (c2.trans (t3.trans (.cons d4 (c5.trans (t6.trans (.single d7)))))),
        by rw [u7.mem]; exact E6, fun x hx => by rw [u7.mem]; exact fr x hx,
        .inr ⟨hg, I6.of u7.mem fun q _ => u7.regs q, .inr ⟨hz', ⟨u7.pc, rfl, fun _ => rfl⟩⟩⟩⟩

end C3.RV32.Pv
