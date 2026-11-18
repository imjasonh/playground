import C3BootProofs.Proofs.Pv384G1

/-!
# `p384_verify_prehash`: the main loop

The main loop of the linear combination, from its head at 0xADE to its exit
at 0xBEE, against `mlLoop`: one position per pass, doubling the accumulator
once it has an entry and then stepping the two pairs.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- The registers at the loop head, with `k + 1` positions left. -/
structure GH (B : Word) (m : Machine) (r3 r4 : Word) (k : Nat) : Prop where
  sp : reg m sp = B + 0x420
  g3 : reg m (3 : Fin 32) = r3
  g4 : reg m (4 : Fin 32) = r4
  s0 : reg m (8 : Fin 32) = 2
  s1 : reg m (9 : Fin 32) = BitVec.ofNat 32 (k + 1)
  s4 : reg m (20 : Fin 32) = 0x90
  s6 : reg m (22 : Fin 32) = 0x188
  s7 : reg m (23 : Fin 32) = B + 0x420 + BitVec.ofNat 32 (0x1928 + k)
  s8 : reg m (24 : Fin 32) = 0x181
  s9 : reg m (25 : Fin 32) = 0x480
  s10 : reg m (26 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0x450
  s11 : reg m (27 : Fin 32) = 0x10

theorem GH.of {B : Word} {m m' : Machine} {r3 r4 : Word} {k : Nat} (R : GH B m r3 r4 k)
    (h : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 20, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) :
    GH B m' r3 r4 k :=
  ⟨by rw [h RV32.sp (by decide), R.sp], by rw [h _ (by decide), R.g3], by rw [h _ (by decide), R.g4],
    by rw [h _ (by decide), R.s0], by rw [h _ (by decide), R.s1], by rw [h _ (by decide), R.s4],
    by rw [h _ (by decide), R.s6], by rw [h _ (by decide), R.s7], by rw [h _ (by decide), R.s8],
    by rw [h _ (by decide), R.s9], by rw [h _ (by decide), R.s10], by rw [h _ (by decide), R.s11]⟩

def pvGade : List BInstr := [.aluImm .and a0 (21 : Fin 32) 0x1]
theorem pvGade_end : blockEnd p384VerifyPrehashCode 0xADE pvGade = some 0xAE2 := by decide
def pvGae4 : List BInstr := [.lui a0 0x1000, .aluImm .add a0 a0 0x294, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF,
  .aluImm .add a1 a1 0x611]
theorem pvGae4_end : blockEnd p384VerifyPrehashCode 0xAE4 pvGae4 = some 0xAF4 := by decide
def pvGafc : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x611, .lui a1 0x1000,
  .aluImm .add a1 a1 0x294, .alu .add a1 a1 sp, .aluImm .add a2 x0 0x90]
theorem pvGafc_end : blockEnd p384VerifyPrehashCode 0xAFC pvGafc = some 0xB10 := by decide
def pvGb18 : List BInstr := [.aluImm .add (18 : Fin 32) x0 0x0, .aluImm .add (19 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]
theorem pvGb18_end : blockEnd p384VerifyPrehashCode 0xB18 pvGb18 = some 0xB1E := by decide
def pvGbe6 : List BInstr := [.aluImm .add (23 : Fin 32) (23 : Fin 32) 0xFFFFFFFF, .alu .add (9 : Fin 32) x0 (19 : Fin 32)]
theorem pvGbe6_end : blockEnd p384VerifyPrehashCode 0xBE6 pvGbe6 = some 0xBEA := by decide

set_option maxHeartbeats 16000000 in
/-- The doubling at the top of a pass, from 0xADE to 0xB18: the
accumulator doubled when it has an entry. -/
theorem ml_dbl {B r3 r4 : Word} {T0 T1 : Nat → Pt} {D0 D1 : List Nat} {RM k : Nat} {st : Pt × Bool}
    {m : Machine} (F : Fr B 0x21A0) (E : PvEnv6 m.mem) (s : St m.mem PV m 0xADE (reg m)) (R : GH B m r3 r4 k)
    (hs5 : reg m (21 : Fin 32) = if st.2 then 1 else 0) (M : GM B m.mem T0 T1 D0 D1 RM)
    (A : ptV m.mem B 0xE10 = st.1) (hl : PtLt st.1) :
    ∃ m', Steps m m' ∧ PvEnv6 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
      St m'.mem PV m' 0xB18 (reg m') ∧ GH B m' r3 r4 k ∧ reg m' (21 : Fin 32) = (if st.2 then 1 else 0) ∧
      GM B m'.mem T0 T1 D0 D1 RM ∧ ptV m'.mem B 0xE10 = (if st.2 then ptDblT st.1 else st.1) ∧
      PtLt (if st.2 then ptDblT st.1 else st.1) := by
  have C := E.E.E.E.E.C.self
  obtain ⟨n1, c1, u1⟩ := s.block pvGade C pvGade_end ⟨trivial, trivial⟩
  have s1 : St m.mem PV n1 0xAE2 (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q ≠ a0 → reg n1 q = reg m q := fun q h => by
    rw [u1.regs, runBlock_reg _ _ _ q s.zero (by simp [pvGade, BInstr.dst, h])]
  have a01 : reg n1 a0 = if st.2 then 1 else 0 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, pvGade, upd, ↓reduceIte]; rw [hs5]
    cases st.2 <;> rfl
  have R1 : GH B n1 r3 r4 k := R.of fun q hq => k1 q (by revert hq; revert q; decide)
  cases hf : st.2
  · rw [hf] at a01 hs5
    obtain ⟨n2, d2, u2⟩ := s1.taken C 0xB18 pv_at_ae2 (by decide) (by rw [a01, s1.zero]; rfl)
    refine ⟨n2, c1.trans (.single d2), by rw [u2.mem]; exact E, fun x _ => by rw [u2.mem],
      ⟨u2.pc, rfl, fun _ => rfl⟩, R1.of fun q _ => u2.regs q, by rw [u2.regs, k1 _ (by decide), hs5],
      by rw [u2.mem]; exact M, by rw [u2.mem]; exact A, hl⟩
  · rw [hf] at a01 hs5
    obtain ⟨n2, d2, u2⟩ := s1.notTaken C 0xAE4 pv_at_ae2 (by decide) (by rw [a01, s1.zero]; rfl)
    have s2 : St m.mem PV n2 0xAE4 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
    obtain ⟨n3, c3, u3⟩ := s2.block pvGae4 C pvGae4_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    have s3 : St n3.mem PV n3 0xAF4 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = m.mem := s2.mem ▸ u3.mem
    have k3 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg n3 q = reg m q := fun q h0 h1 => by
      rw [u3.regs, runBlock_reg _ _ _ q s2.zero (by simp [pvGae4, BInstr.dst, h0, h1]), u2.regs, k1 q h0]
    have R3 : GH B n3 r3 r4 k := R.of fun q hq => k3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    obtain ⟨a1', a2', a3'⟩ := ptV_eq A
    have E3 : PvEnv6 n3.mem := by rw [m3]; exact E
    obtain ⟨n4, P4, K4, V4⟩ := pv_pd F E3.E.E s3 pv_at_af4 pv_at_af8 (by decide) (by decide) R3.sp
      (by rw [u3.regs]; simp +decide only [runBlock, BInstr.run, pvGae4, upd, ↓reduceIte]
          rw [u2.regs, k1 _ (by decide), R.sp]; simp only [aluEval]; rw [BitVec.add_comm]; rfl)
      (by rw [u3.regs]; simp +decide only [runBlock, BInstr.run, pvGae4, upd, ↓reduceIte]
          rw [u2.regs, k1 _ (by decide), R.sp]; simp only [aluEval]; exact sp_e10 _)
      (co := 0x1294) (cx := 0xE10) (by decide) (by decide) (by decide) (by decide)
      (by rw [m3, a1']; exact hl.1) (by rw [m3, a2']; exact hl.2.1) (by rw [m3, a3']; exact hl.2.2)
    rw [m3, a1', a2', a3'] at V4
    have E4 : PvEnv6 n4.mem := E3.fr F P4.fr
    have R4 := R3.of fun q hq => P4.regs q (by revert hq; revert q; decide)
    obtain ⟨n5, c5, u5⟩ := P4.st.block pvGafc E4.E.E.E.E.C.self pvGafc_end
      ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    have s5 : St n5.mem PV n5 0xB10 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have m5 : n5.mem = n4.mem := u5.mem
    have k5 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n5 q = reg n4 q := fun q h0 h1 h2 => by
      rw [u5.regs, runBlock_reg _ _ _ q P4.st.zero (by simp [pvGafc, BInstr.dst, h0, h1, h2])]
    have E5 : PvEnv6 n5.mem := by rw [m5]; exact E4
    obtain ⟨n6, P6, K6, V6⟩ := pv_mc F E5.E.E.E.E s5 pv_at_b10 pv_at_b14 (by decide) (by decide)
      (by rw [k5 _ (by decide) (by decide) (by decide), R4.sp])
      (by rw [u5.regs]; simp +decide only [runBlock, BInstr.run, pvGafc, upd, ↓reduceIte]
          rw [R4.sp]; simp only [aluEval]; exact sp_e10 _)
      (by rw [u5.regs]; simp +decide only [runBlock, BInstr.run, pvGafc, upd, ↓reduceIte]
          rw [R4.sp]; simp only [aluEval]; rw [BitVec.add_comm]; rfl)
      (by rw [u5.regs]; simp +decide only [runBlock, BInstr.run, pvGafc, upd, ↓reduceIte])
      (c := 0xE10) (d := 0x1294) (N := 0x90) (by decide) (by decide) (by decide)
    have hV : ptV n6.mem B 0xE10 = ptDblT st.1 := by
      unfold ptV
      rw [accV_S 12 fun q hq => V6 q (by omega), accV_S (c := 0xE10 + 0x30) (d := 0x1294 + 0x30) 12 fun q hq => by
          have := V6 (0x30 + q) (by omega); rwa [show 0xE10 + (0x30 + q) = 0xE10 + 0x30 + q by omega,
            show 0x1294 + (0x30 + q) = 0x1294 + 0x30 + q by omega] at this,
        accV_S (c := 0xE10 + 0x60) (d := 0x1294 + 0x60) 12 fun q hq => by
          have := V6 (0x60 + q) (by omega); rwa [show 0xE10 + (0x60 + q) = 0xE10 + 0x60 + q by omega,
            show 0x1294 + (0x60 + q) = 0x1294 + 0x60 + q by omega] at this, m5]
      exact V4
    have M6 : GM B n6.mem T0 T1 D0 D1 RM :=
      (((M.keep (M' := n3.mem) (c := 0x1294) (w := 0) (fun e _ _ => by rw [m3]) (.inl ⟨by decide, by decide⟩)).keep K4
        (.inl ⟨by decide, by decide⟩)).keep (M' := n5.mem) (c := 0x1294) (w := 0) (fun e _ _ => by rw [m5])
        (.inl ⟨by decide, by decide⟩)).keep K6 (.inr ⟨by decide, by decide⟩)
    refine ⟨n6, c1.trans (.cons d2 (c3.trans (P4.steps.trans (c5.trans P6.steps)))), E5.fr F P6.fr,
      fun x hx => by rw [P6.fr x hx, m5, P4.fr x hx, m3], P6.st,
      R4.of fun q hq => by rw [P6.regs q (by revert hq; revert q; decide), k5 q (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide)],
      by rw [P6.regs _ (by decide), k5 _ (by decide) (by decide) (by decide), P4.regs _ (by decide),
        k3 _ (by decide) (by decide), hs5], M6, hV, ptDblT_lt _⟩

theorem dec_ofNat (S : Word) (c : Nat) : S + BitVec.ofNat 32 (c + 1) + 0xFFFFFFFF = S + BitVec.ofNat 32 c := by
  rw [BitVec.add_assoc, ofNat_dec]

set_option maxHeartbeats 32000000 in
/-- **One pass of the main loop**, from 0xADE with `k + 1` positions left:
position `k`, as `mlIter` computes it. -/
theorem ml_body {B r3 r4 : Word} {T0 T1 : Nat → Pt} {D0 D1 : List Nat} {RM k : Nat} {st : Pt × Bool}
    {m : Machine} (F : Fr B 0x21A0) (E : PvEnv6 m.mem) (s : St m.mem PV m 0xADE (reg m)) (R : GH B m r3 r4 k)
    (hs5 : reg m (21 : Fin 32) = if st.2 then 1 else 0) (M : GM B m.mem T0 T1 D0 D1 RM)
    (A : ptV m.mem B 0xE10 = st.1) (hl : PtLt st.1) (hk : k + 1 ≤ 0x181) :
    (mlIter T0 T1 D0 D1 k st = none ∧ Panics m) ∨
    (∃ st', mlIter T0 T1 D0 D1 k st = some st' ∧
      ∃ m', Steps m m' ∧ PvEnv6 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
        St m'.mem PV m' (if k = 0 then 0xBEE else 0xADE) (reg m') ∧ (k ≠ 0 → GH B m' r3 r4 (k - 1)) ∧
        reg m' sp = B + 0x420 ∧ reg m' (3 : Fin 32) = r3 ∧ reg m' (4 : Fin 32) = r4 ∧
        reg m' (21 : Fin 32) = (if st'.2 then 1 else 0) ∧ GM B m'.mem T0 T1 D0 D1 RM ∧
        ptV m'.mem B 0xE10 = st'.1 ∧ PtLt st'.1) := by
  obtain ⟨n1, c1, E1, fr1, s1, R1, h21, M1, A1, l1⟩ := ml_dbl F E s R hs5 M A hl
  have C := E1.E.E.E.E.C.self
  obtain ⟨n2, c2, u2⟩ := s1.block pvGb18 C pvGb18_end ⟨trivial, trivial, trivial⟩
  have s2 : St n1.mem PV n2 0xB1E (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have k2 : ∀ q : Fin 32, q ≠ (18 : Fin 32) → q ≠ (19 : Fin 32) → reg n2 q = reg n1 q := fun q h0 h1 => by
    rw [u2.regs, runBlock_reg _ _ _ q s1.zero (by simp [pvGb18, BInstr.dst, h0, h1])]
  have r18 : reg n2 (18 : Fin 32) = BitVec.ofNat 32 0 := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, pvGb18, upd, ↓reduceIte, aluEval]; rw [s1.zero]; rfl
  have r19 : reg n2 (19 : Fin 32) = BitVec.ofNat 32 k := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, pvGb18, upd, ↓reduceIte, aluEval]; rw [R1.s1]
    exact ofNat_dec k
  obtain ⟨n3, c3, u3⟩ := s2.block pvGb1e C pvGb1e_end ⟨trivial, trivial, trivial⟩
  have s3 : St n1.mem PV n3 0xB24 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  have k3 : ∀ q : Fin 32, q ≠ a0 → reg n3 q = reg n2 q := fun q h => by
    rw [u3.regs, runBlock_reg _ _ _ q s2.zero (by simp [pvGb1e, BInstr.dst, h])]
  have a03 : reg n3 a0 = B + 0x420 + BitVec.ofNat 32 (0x1928 + k + 0x188 * 0) := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, pvGb1e, upd, ↓reduceIte, aluEval]
    rw [r18, k2 _ (by decide) (by decide), k2 _ (by decide) (by decide), R1.s6, R1.s7]
    exact ofNat_mul_add (B + 0x420) 0 (0x1928 + k) 0x188 (by omega) (by decide) (by decide)
  obtain ⟨n4, d4, u4⟩ := s3.notTaken C 0xB28 pv_at_b24 (by decide)
    (by rw [k3 _ (by decide), r18, k3 _ (by decide), k2 _ (by decide) (by decide), R1.s0]; decide)
  have e4 : reg n4 = reg n3 := funext u4.regs
  have s4 : St n4.mem PV n4 0xB28 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n1.mem := u4.mem
  have G4 : GR B n4 r3 r4 k := by
    have h : ∀ q : Fin 32, q ≠ a0 → q ≠ (18 : Fin 32) → q ≠ (19 : Fin 32) → reg n4 q = reg n1 q := fun q h0 h1 h2 => by
      rw [e4, k3 q h0, k2 q h1 h2]
    exact ⟨by rw [h _ (by decide) (by decide) (by decide), R1.sp], by rw [h _ (by decide) (by decide) (by decide), R1.g3],
      by rw [h _ (by decide) (by decide) (by decide), R1.g4], by rw [h _ (by decide) (by decide) (by decide), R1.s0],
      by rw [h _ (by decide) (by decide) (by decide), R1.s1], by rw [e4, k3 _ (by decide), r19],
      by rw [h _ (by decide) (by decide) (by decide), R1.s4], by rw [h _ (by decide) (by decide) (by decide), R1.s6],
      by rw [h _ (by decide) (by decide) (by decide), R1.s7], by rw [h _ (by decide) (by decide) (by decide), R1.s8],
      by rw [h _ (by decide) (by decide) (by decide), R1.s9], by rw [h _ (by decide) (by decide) (by decide), R1.s10],
      by rw [h _ (by decide) (by decide) (by decide), R1.s11]⟩
  have E4 : PvEnv6 n4.mem := by rw [m4]; exact E1
  unfold mlIter
  have P0 := ml_pair (j := 0) (st := (if st.2 then ptDblT st.1 else st.1, st.2)) F E4 s4 G4
    (by rw [e4, k3 _ (by decide), k2 _ (by decide) (by decide), h21])
    (by rw [e4, k3 _ (by decide), r18]) (by rw [e4, a03]) (by rw [m4]; exact M1) (by rw [m4]; exact A1) l1
    (by decide) hk
  simp only [ite_true] at P0
  rcases P0 with ⟨hn, hp⟩ | ⟨st1, h1, n5, c5, E5, fr5, s5, G5, r21, r18', a05, M5, A5, l5⟩
  · left; rw [hn]
    exact ⟨rfl, Panics.of_steps (c1.trans (c2.trans (c3.trans (.single d4)))) hp⟩
  rw [h1, Option.bind_some]
  have P1 := ml_pair (j := 1) (st := st1) F E5 s5 G5 r21 r18' a05 M5 A5 l5 (by decide) hk
  simp only [Nat.one_ne_zero, ite_false] at P1
  rcases P1 with ⟨hn, hp⟩ | ⟨st2, h2, n6, c6, E6, fr6, s6, G6, r21', -, -, M6, A6, l6⟩
  · left; rw [hn]
    exact ⟨rfl, Panics.of_steps (c1.trans (c2.trans (c3.trans (.cons d4 c5)))) hp⟩
  right
  refine ⟨st2, h2, ?_⟩
  obtain ⟨n7, c7, u7⟩ := s6.block pvGbe6 E6.E.E.E.E.C.self pvGbe6_end ⟨trivial, trivial, trivial⟩
  have s7 : St n6.mem PV n7 0xBEA (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
  have k7 : ∀ q : Fin 32, q ≠ (23 : Fin 32) → q ≠ (9 : Fin 32) → reg n7 q = reg n6 q := fun q h0 h1 => by
    rw [u7.regs, runBlock_reg _ _ _ q s6.zero (by simp [pvGbe6, BInstr.dst, h0, h1])]
  have r9 : reg n7 (9 : Fin 32) = BitVec.ofNat 32 k := by
    rw [u7.regs]; simp +decide only [runBlock, BInstr.run, pvGbe6, upd, ↓reduceIte, aluEval]
    rw [G6.s3]; exact BitVec.zero_add _
  have st : Steps m n7 := c1.trans (c2.trans (c3.trans (.cons d4 (c5.trans (c6.trans c7)))))
  have k7' : ∀ q : Fin 32, q.val ∈ [2, 3, 4] → reg n7 q = reg n6 q := fun q hq =>
    k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    obtain ⟨n8, d8, u8⟩ := s7.notTaken E6.E.E.E.E.C.self 0xBEE pv_at_bea (by decide)
      (by rw [k7 _ (by decide) (by decide), G6.s3, s7.zero]; decide)
    exact ⟨n8, st.trans (.single d8), by rw [u8.mem]; exact E6, fun x hx => by rw [u8.mem, fr6 x hx, fr5 x hx, m4, fr1 x hx],
      ⟨u8.pc, rfl, fun _ => rfl⟩, fun h => absurd rfl h, by rw [u8.regs, k7' sp (by decide), G6.sp],
      by rw [u8.regs, k7' _ (by decide), G6.g3], by rw [u8.regs, k7' _ (by decide), G6.g4],
      by rw [u8.regs, k7 _ (by decide) (by decide), r21'], by rw [u8.mem]; exact M6,
      by rw [u8.mem]; exact A6, l6⟩
  · obtain ⟨n8, d8, u8⟩ := s7.taken E6.E.E.E.E.C.self 0xADE pv_at_bea (by decide)
      (by rw [k7 _ (by decide) (by decide), G6.s3, s7.zero]; simp only [branchTaken]
          exact bne_iff_ne.2 (ofNat_ne0 hk0 (by omega)))
    have r23 : reg n7 (23 : Fin 32) = B + 0x420 + BitVec.ofNat 32 (0x1928 + (k - 1)) := by
      rw [u7.regs]; simp +decide only [runBlock, BInstr.run, pvGbe6, upd, ↓reduceIte, aluEval]
      rw [G6.s7, show 0x1928 + k = 0x1928 + (k - 1) + 1 by omega]; exact dec_ofNat _ _
    rw [ite_eq_right (by omega)]
    refine ⟨n8, st.trans (.single d8), by rw [u8.mem]; exact E6, fun x hx => by rw [u8.mem, fr6 x hx, fr5 x hx, m4, fr1 x hx],
      ⟨u8.pc, rfl, fun _ => rfl⟩, fun _ => ?_, by rw [u8.regs, k7' sp (by decide), G6.sp],
      by rw [u8.regs, k7' _ (by decide), G6.g3], by rw [u8.regs, k7' _ (by decide), G6.g4],
      by rw [u8.regs, k7 _ (by decide) (by decide), r21'], by rw [u8.mem]; exact M6,
      by rw [u8.mem]; exact A6, l6⟩
    exact ⟨by rw [u8.regs, k7 _ (by decide) (by decide), G6.sp], by rw [u8.regs, k7 _ (by decide) (by decide), G6.g3],
      by rw [u8.regs, k7 _ (by decide) (by decide), G6.g4], by rw [u8.regs, k7 _ (by decide) (by decide), G6.s0],
      by rw [u8.regs, r9, show k - 1 + 1 = k by omega], by rw [u8.regs, k7 _ (by decide) (by decide), G6.s4],
      by rw [u8.regs, k7 _ (by decide) (by decide), G6.s6], by rw [u8.regs, r23],
      by rw [u8.regs, k7 _ (by decide) (by decide), G6.s8], by rw [u8.regs, k7 _ (by decide) (by decide), G6.s9],
      by rw [u8.regs, k7 _ (by decide) (by decide), G6.s10], by rw [u8.regs, k7 _ (by decide) (by decide), G6.s11]⟩

/-- **The main loop**, from its head at 0xADE with `k + 1` positions left to
its exit at 0xBEE, as `mlLoop` computes it. -/
theorem ml_loop {B r3 r4 : Word} {T0 T1 : Nat → Pt} {D0 D1 : List Nat} {RM : Nat} (F : Fr B 0x21A0) :
    ∀ k {m : Machine} {st : Pt × Bool}, PvEnv6 m.mem → St m.mem PV m 0xADE (reg m) → GH B m r3 r4 k →
      reg m (21 : Fin 32) = (if st.2 then 1 else 0) → GM B m.mem T0 T1 D0 D1 RM → ptV m.mem B 0xE10 = st.1 →
      PtLt st.1 → k + 1 ≤ 0x181 →
      (mlLoop T0 T1 D0 D1 (k + 1) st = none ∧ Panics m) ∨
      (∃ st', mlLoop T0 T1 D0 D1 (k + 1) st = some st' ∧
        ∃ m', Steps m m' ∧ PvEnv6 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
          St m'.mem PV m' 0xBEE (reg m') ∧ reg m' sp = B + 0x420 ∧ reg m' (3 : Fin 32) = r3 ∧
          reg m' (4 : Fin 32) = r4 ∧ GM B m'.mem T0 T1 D0 D1 RM ∧ ptV m'.mem B 0xE10 = st'.1 ∧ PtLt st'.1)
  | k, m, st, E, s, R, hs5, M, A, hl, hk => by
    rcases ml_body F E s R hs5 M A hl hk with ⟨hn, hp⟩ | ⟨st1, h1, n1, c1, E1, fr1, s1, G1, sp1, g31, g41, r21, M1, A1, l1⟩
    · left; simp only [mlLoop, hn, Option.bind_none]; exact ⟨trivial, hp⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      right; refine ⟨st1, by simp only [mlLoop, h1, Option.bind_some], n1, c1, E1, fr1, s1, sp1, g31, g41, M1, A1, l1⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [ite_eq_right (by omega)] at s1
      have G1' := G1 (by omega)
      rw [show k' + 1 - 1 = k' by omega] at G1'
      rcases ml_loop F k' E1 s1 G1' r21 M1 A1 l1 (by omega) with ⟨hn, hp⟩ | ⟨st2, h2, n2, c2, rest⟩
      · left; simp only [mlLoop, h1, Option.bind_some]
        exact ⟨by simpa [mlLoop] using hn, Panics.of_steps c1 hp⟩
      · right
        refine ⟨st2, by simp only [mlLoop, h1, Option.bind_some]; simpa [mlLoop] using h2, n2, c1.trans c2, ?_⟩
        obtain ⟨E2, fr2, rest⟩ := rest
        exact ⟨E2, fun x hx => by rw [fr2 x hx, fr1 x hx], rest⟩

/-- The identity point, as the image keeps it, in Montgomery form. -/
def idPt : Pt := (dataVal p384IdentityData 0 12, dataVal p384IdentityData 0x30 12, dataVal p384IdentityData 0x60 12)

set_option exponentiation.threshold 600 in
theorem idPt_lt : PtLt idPt := by unfold idPt PtLt p384; decide

def pvGa76 : List BInstr := [.lui a0 0x1000, .aluImm .add a0 a0 0x744, .alu .add a0 a0 sp]
theorem pvGa76_end : blockEnd p384VerifyPrehashCode 0xA76 pvGa76 = some 0xA7E := by decide
def pvGa86 : List BInstr := [.aluImm .add a1 x0 0x0, .aluImm .and a1 a1 0x1]
theorem pvGa86_end : blockEnd p384VerifyPrehashCode 0xA86 pvGa86 = some 0xA8A := by decide
def pvGa90 : List BInstr := [.alu .add (9 : Fin 32) x0 a0]
theorem pvGa90_end : blockEnd p384VerifyPrehashCode 0xA90 pvGa90 = some 0xA92 := by decide
def pvGa92 : List BInstr := [.aluImm .add a1 x0 0x1]
theorem pvGa92_end : blockEnd p384VerifyPrehashCode 0xA92 pvGa92 = some 0xA94 := by decide
def pvGa88 : List BInstr := [.aluImm .and a1 a1 0x1]
theorem pvGa88_end : blockEnd p384VerifyPrehashCode 0xA88 pvGa88 = some 0xA8A := by decide
def pvGa96 : List BInstr := [.lui a1 0x3FCC4000, .aluImm .add a1 a1 0x4D0, .aluImm .add a0 sp 0x7FF,
  .aluImm .add a0 a0 0x611, .aluImm .add a2 x0 0x90, .aluImm .add (20 : Fin 32) x0 0x90]
theorem pvGa96_end : blockEnd p384VerifyPrehashCode 0xA96 pvGa96 = some 0xAAE := by decide
def pvGab6 : List BInstr := [.aluImm .add (21 : Fin 32) x0 0x0, .lui a0 0x2000, .aluImm .add a0 a0 0xFFFFF924,
  .alu .add a0 a0 sp, .alu .add a0 a0 (9 : Fin 32), .aluImm .add (23 : Fin 32) a0 0x3,
  .aluImm .add (22 : Fin 32) x0 0x188, .aluImm .add (8 : Fin 32) x0 0x2, .aluImm .add (24 : Fin 32) x0 0x181,
  .aluImm .add (25 : Fin 32) x0 0x480, .aluImm .add (26 : Fin 32) sp 0x450, .aluImm .add (27 : Fin 32) x0 0x10]
theorem pvGab6_end : blockEnd p384VerifyPrehashCode 0xAB6 pvGab6 = some 0xADA := by decide

theorem s7_val (S : Word) (x : Nat) (hx : 1 ≤ x) :
    (8192 : Word) + 4294965540 + S + BitVec.ofNat 32 x + 3 = S + BitVec.ofNat 32 (6440 + (x - 1)) := by
  pv_addr

set_option maxHeartbeats 32000000 in
/-- **The setup of the main loop**, from 0xA76: the longer digit count, the
identity in the accumulator, and the loop's registers; then the loop head,
or the exit when both counts are zero. -/
theorem ml_pre {B : Word} {T0 T1 : Nat → Pt} {D0 D1 : List Nat} {RM L0 L1 : Nat} {m : Machine}
    (F : Fr B 0x21A0) (E : PvEnv6 m.mem) (s : St m.mem PV m 0xA76 (reg m)) (hsp : reg m sp = B + 0x420)
    (w0 : memLoad32 m.mem (B + 0x420 + BitVec.ofNat 32 0x1924) = BitVec.ofNat 32 L0)
    (w1 : memLoad32 m.mem (B + 0x420 + BitVec.ofNat 32 0x1AAC) = BitVec.ofNat 32 L1)
    (hL0 : L0 ≤ 0x181) (hL1 : L1 ≤ 0x181) (M : GM B m.mem T0 T1 D0 D1 RM) :
    ∃ m', Steps m m' ∧ PvEnv6 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
      St m'.mem PV m' (if max L0 L1 = 0 then 0xBEE else 0xADE) (reg m') ∧
      (max L0 L1 ≠ 0 → GH B m' (reg m (3 : Fin 32)) (reg m (4 : Fin 32)) (max L0 L1 - 1)) ∧
      reg m' sp = B + 0x420 ∧ reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧
      reg m' (21 : Fin 32) = 0 ∧ GM B m'.mem T0 T1 D0 D1 RM ∧ ptV m'.mem B 0xE10 = idPt := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have C := E.E.E.E.E.C.self
  obtain ⟨n1, c1, u1⟩ := s.block pvGa76 C pvGa76_end ⟨trivial, trivial, trivial, trivial⟩
  have s1 : St m.mem PV n1 0xA7E (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q ≠ a0 → reg n1 q = reg m q := fun q h => by
    rw [u1.regs, runBlock_reg _ _ _ q s.zero (by simp [pvGa76, BInstr.dst, h])]
  have a01 : reg n1 a0 = B + 0x420 + BitVec.ofNat 32 0x1744 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, pvGa76, upd, ↓reduceIte, aluEval]; rw [hsp]
    rw [BitVec.add_comm]; rfl
  obtain ⟨n2, d2, u2⟩ := s1.lw C pv_at_a7e (off' := 0xA82) (by decide)
    (by rw [a01, show (0x1E0 : Word) = BitVec.ofNat 32 0x1E0 from rfl, add_ofNat_assoc]
        exact pv_al F (by decide) (by decide))
  rw [a01, show (0x1E0 : Word) = BitVec.ofNat 32 0x1E0 from rfl, add_ofNat_assoc, w0] at u2
  obtain ⟨n3, d3, u3⟩ := u2.lw C pv_at_a82 (off' := 0xA86) (by decide)
    (by rw [upd_ne (by decide) (by decide), a01, show (0x368 : Word) = BitVec.ofNat 32 0x368 from rfl, add_ofNat_assoc]
        exact pv_al F (by decide) (by decide))
  rw [upd_ne (by decide) (by decide), a01, show (0x368 : Word) = BitVec.ofNat 32 0x368 from rfl, add_ofNat_assoc,
    w1] at u3
  have s3 : St m.mem PV n3 0xA86 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  have r93 : reg n3 (9 : Fin 32) = BitVec.ofNat 32 L0 := by rw [u3.regs, upd_ne (by decide) (by decide), upd_same (by decide)]
  have a03 : reg n3 a0 = BitVec.ofNat 32 L1 := by rw [u3.regs, upd_same (by decide)]
  have k3 : ∀ q : Fin 32, q ≠ a0 → q ≠ (9 : Fin 32) → reg n3 q = reg m q := fun q h0 h9 => by
    rw [u3.regs, updz (by rw [updz s1.zero (by decide)]; exact s1.zero) h0, updz s1.zero h9, k1 q h0]
  obtain ⟨n4, c4, u4⟩ := s3.block pvGa86 C pvGa86_end ⟨trivial, trivial, trivial⟩
  have s4 : St m.mem PV n4 0xA8A (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
  have k4 : ∀ q : Fin 32, q ≠ a1 → reg n4 q = reg n3 q := fun q h => by
    rw [u4.regs, runBlock_reg _ _ _ q s3.zero (by simp [pvGa86, BInstr.dst, h])]
  have a14 : reg n4 a1 = 0 := by
    rw [u4.regs]; simp +decide only [runBlock, BInstr.run, pvGa86, upd, ↓reduceIte, aluEval]; rw [s3.zero]; rfl
  obtain ⟨n5, d5, u5⟩ := s4.notTaken C 0xA8C pv_at_a8a (by decide) (by rw [a14, s4.zero]; rfl)
  have s5 : St m.mem PV n5 0xA8C (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
  have e5 : reg n5 = reg n4 := funext u5.regs
  -- the longer count in s1, then back to 0xA88 and out at 0xA96
  have hmax : ∃ n6, Steps n5 n6 ∧ St m.mem PV n6 0xA92 (reg n6) ∧
      reg n6 (9 : Fin 32) = BitVec.ofNat 32 (max L0 L1) ∧ ∀ q : Fin 32, q ≠ (9 : Fin 32) → reg n6 q = reg n5 q := by
    by_cases hlt : L1 < L0
    · obtain ⟨n6, d6, u6⟩ := s5.taken C 0xA92 pv_at_a8c (by decide)
        (by rw [e5, k4 _ (by decide), a03, k4 _ (by decide), r93]; simp only [branchTaken]
            rw [ult_ofNat (by omega) (by omega)]; simp [hlt])
      exact ⟨n6, .single d6, ⟨u6.pc, u6.mem, fun _ => rfl⟩,
        by rw [u6.regs, e5, k4 _ (by decide), r93, Nat.max_eq_left (by omega)], fun q _ => u6.regs q⟩
    · obtain ⟨n6, d6, u6⟩ := s5.notTaken C 0xA90 pv_at_a8c (by decide)
        (by rw [e5, k4 _ (by decide), a03, k4 _ (by decide), r93]; simp only [branchTaken]
            rw [ult_ofNat (by omega) (by omega)]; simp [hlt])
      have s6 : St m.mem PV n6 0xA90 (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
      obtain ⟨n7, c7, u7⟩ := s6.block pvGa90 C pvGa90_end ⟨trivial, trivial⟩
      refine ⟨n7, .cons d6 c7, ⟨u7.pc, u7.mem, fun _ => rfl⟩, ?_, fun q h => ?_⟩
      · rw [u7.regs]; simp +decide only [runBlock, BInstr.run, pvGa90, upd, ↓reduceIte, aluEval]
        rw [s6.zero, u6.regs, e5, k4 _ (by decide), a03, Nat.max_eq_right (by omega)]; exact BitVec.zero_add _
      · rw [u7.regs, runBlock_reg _ _ _ q s6.zero (by simp [pvGa90, BInstr.dst, h]), u6.regs]
  obtain ⟨n6, c6, s6, r96, k6⟩ := hmax
  obtain ⟨n7, c7, u7⟩ := s6.block pvGa92 C pvGa92_end ⟨trivial, trivial⟩
  have s7 : St m.mem PV n7 0xA94 (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
  obtain ⟨n8, d8, u8⟩ := s7.jump C pv_at_a94 (off' := 0xA88) (by decide) (by rw [s7.pc]; decide)
  have s8 : St m.mem PV n8 0xA88 (reg n8) := ⟨u8.pc, u8.mem, fun _ => rfl⟩
  obtain ⟨n9, c9, u9⟩ := s8.block pvGa88 C pvGa88_end ⟨trivial, trivial⟩
  have s9 : St m.mem PV n9 0xA8A (reg n9) := ⟨u9.pc, u9.mem, fun _ => rfl⟩
  have a19 : reg n9 a1 = 1 := by
    rw [u9.regs]; simp +decide only [runBlock, BInstr.run, pvGa88, upd, ↓reduceIte, aluEval]
    rw [u8.regs, u7.regs]; simp +decide only [runBlock, BInstr.run, pvGa92, upd, ↓reduceIte, aluEval]
    rw [s6.zero]; rfl
  have k9 : ∀ q : Fin 32, q ≠ a1 → reg n9 q = reg n6 q := fun q h => by
    rw [u9.regs, runBlock_reg _ _ _ q s8.zero (by simp [pvGa88, BInstr.dst, h]), u8.regs, u7.regs,
      runBlock_reg _ _ _ q s6.zero (by simp [pvGa92, BInstr.dst, h])]
  obtain ⟨n10, d10, u10⟩ := s9.taken C 0xA96 pv_at_a8a (by decide) (by rw [a19, s9.zero]; decide)
  have s10 : St m.mem PV n10 0xA96 (reg n10) := ⟨u10.pc, u10.mem, fun _ => rfl⟩
  have k10 : ∀ q : Fin 32, q ≠ a1 → q ≠ a0 → q ≠ (9 : Fin 32) → reg n10 q = reg m q := fun q h1 h0 h9 => by
    rw [u10.regs, k9 q h1, k6 q h9, e5, k4 q h1, k3 q h0 h9]
  have r910 : reg n10 (9 : Fin 32) = BitVec.ofNat 32 (max L0 L1) := by rw [u10.regs, k9 _ (by decide), r96]
  obtain ⟨n11, c11, u11⟩ := s10.block pvGa96 C pvGa96_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have s11 : St n11.mem PV n11 0xAAE (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = m.mem := s10.mem ▸ u11.mem
  have k11 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (20 : Fin 32) → reg n11 q = reg n10 q :=
    fun q h0 h1 h2 h20 => by rw [u11.regs, runBlock_reg _ _ _ q s10.zero (by simp [pvGa96, BInstr.dst, h0, h1, h2, h20])]
  have E11 : PvEnv6 n11.mem := by rw [m11]; exact E
  have sp10 : reg n10 sp = B + 0x420 := by rw [k10 _ (by decide) (by decide) (by decide), hsp]
  have a011 : reg n11 a0 = B + 0x420 + BitVec.ofNat 32 0xE10 := by
    rw [u11.regs]; simp +decide only [runBlock, BInstr.run, pvGa96, upd, ↓reduceIte, aluEval, sp10, sp_e10]
  have a111 : reg n11 a1 = BitVec.ofNat 32 p384IdentityAddress := by
    rw [u11.regs]; simp +decide only [runBlock, BInstr.run, pvGa96, upd, ↓reduceIte, aluEval]
  have a211 : reg n11 a2 = BitVec.ofNat 32 0x90 := by
    rw [u11.regs]; simp +decide only [runBlock, BInstr.run, pvGa96, upd, ↓reduceIte, aluEval]
  obtain ⟨n12, P12, K12, V12⟩ := pv_mcK F E11.E.E.E.E s11 pv_at_aae pv_at_ab2 (by decide) (by decide)
    (by rw [k11 _ (by decide) (by decide) (by decide) (by decide), sp10]) a011 a111 a211
    (by decide) (by decide) (by decide)
  have E12 : PvEnv6 n12.mem := E11.fr F P12.fr
  have hidp := E11.E.E.E.E.D2.idp
  have hA : ptV n12.mem B 0xE10 = idPt := by
    unfold ptV idPt
    rw [accV_KD (M := n11.mem) (K := BitVec.ofNat 32 p384IdentityAddress) (d := 0) 12 fun q hq => by
        have := V12 q (by omega); rwa [Nat.zero_add],
      code_accV hidp 0 12 (by decide),
      accV_KD (M := n11.mem) (K := BitVec.ofNat 32 p384IdentityAddress) (d := 0x30) 12 fun q hq => by
        have := V12 (0x30 + q) (by omega)
        rwa [show 0xE10 + (0x30 + q) = 0xE10 + 0x30 + q by omega] at this,
      code_accV hidp 0x30 12 (by decide),
      accV_KD (M := n11.mem) (K := BitVec.ofNat 32 p384IdentityAddress) (d := 0x60) 12 fun q hq => by
        have := V12 (0x60 + q) (by omega)
        rwa [show 0xE10 + (0x60 + q) = 0xE10 + 0x60 + q by omega] at this,
      code_accV hidp 0x60 12 (by decide)]
  have M12 : GM B n12.mem T0 T1 D0 D1 RM :=
    (M.keep (M' := n11.mem) (c := 0x1294) (w := 0) (fun e _ _ => by rw [m11]) (.inl ⟨by decide, by decide⟩)).keep K12
      (.inr ⟨by decide, by decide⟩)
  obtain ⟨n13, c13, u13⟩ := P12.st.block pvGab6 E12.E.E.E.E.C.self pvGab6_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have s13 : St n12.mem PV n13 0xADA (reg n13) := ⟨u13.pc, u13.mem, fun _ => rfl⟩
  have r9_12 : reg n12 (9 : Fin 32) = BitVec.ofNat 32 (max L0 L1) := by
    rw [P12.regs _ (by decide), k11 _ (by decide) (by decide) (by decide) (by decide), r910]
  have sp12 : reg n12 sp = B + 0x420 := by
    rw [P12.regs _ (by decide), k11 _ (by decide) (by decide) (by decide) (by decide), sp10]
  have k13 : ∀ q : Fin 32, q.val ∈ [2, 3, 4] → reg n13 q = reg m q := fun q hq => by
    rw [u13.regs, runBlock_reg _ _ _ q P12.st.zero (by revert hq; revert q; decide), P12.regs q (by revert hq; revert q; decide),
      k11 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide), k10 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide)]
  have r913 : reg n13 (9 : Fin 32) = BitVec.ofNat 32 (max L0 L1) := by
    rw [u13.regs, runBlock_reg _ _ _ _ P12.st.zero (by decide), r9_12]
  have r21 : reg n13 (21 : Fin 32) = 0 := by
    rw [u13.regs]; simp +decide only [runBlock, BInstr.run, pvGab6, upd, ↓reduceIte, aluEval]; rw [P12.st.zero]; rfl
  have fr : ∀ x, PvR B x → n13.mem x = m.mem x := fun x hx => by rw [s13.mem, P12.fr x hx, m11]
  have st : Steps m n13 := c1.trans (.cons d2 (.cons d3 (c4.trans (.cons d5 (c6.trans (c7.trans (.cons d8 (c9.trans
    (.cons d10 (c11.trans (P12.steps.trans c13)))))))))))
  have E13 : PvEnv6 n13.mem := by rw [s13.mem]; exact E12
  have M13 : GM B n13.mem T0 T1 D0 D1 RM := by rw [s13.mem]; exact M12
  have A13 : ptV n13.mem B 0xE10 = idPt := by rw [s13.mem]; exact hA
  by_cases h0 : max L0 L1 = 0
  · obtain ⟨n14, d14, u14⟩ := s13.taken E12.E.E.E.E.C.self 0xBEE pv_at_ada (by decide)
      (by rw [r913, h0, s13.zero]; rfl)
    rw [ite_eq_left h0]
    exact ⟨n14, st.trans (.single d14), by rw [u14.mem, ← s13.mem]; exact E13, fun x hx => by rw [u14.mem, ← s13.mem, fr x hx],
      ⟨u14.pc, rfl, fun _ => rfl⟩, fun h => absurd h0 h, by rw [u14.regs, k13 sp (by decide), hsp],
      by rw [u14.regs, k13 _ (by decide)], by rw [u14.regs, k13 _ (by decide)], by rw [u14.regs, r21],
      by rw [u14.mem, ← s13.mem]; exact M13, by rw [u14.mem, ← s13.mem]; exact A13⟩
  · obtain ⟨n14, d14, u14⟩ := s13.notTaken E12.E.E.E.E.C.self 0xADE pv_at_ada (by decide)
      (by rw [r913, s13.zero]; simp only [branchTaken]
          exact beq_eq_false_iff_ne.2 (ofNat_ne0 (by omega) (by omega)))
    rw [ite_eq_right h0]
    have hv : ∀ q : Fin 32, reg n14 q = (runBlock pvGab6 (n12.mem, reg n12)).2 q := fun q => by rw [u14.regs, u13.regs]
    refine ⟨n14, st.trans (.single d14), by rw [u14.mem, ← s13.mem]; exact E13,
      fun x hx => by rw [u14.mem, ← s13.mem, fr x hx], ⟨u14.pc, rfl, fun _ => rfl⟩, fun _ => ?_,
      by rw [u14.regs, k13 sp (by decide), hsp], by rw [u14.regs, k13 _ (by decide)], by rw [u14.regs, k13 _ (by decide)],
      by rw [u14.regs, r21], by rw [u14.mem, ← s13.mem]; exact M13, by rw [u14.mem, ← s13.mem]; exact A13⟩
    have z12 := P12.st.zero
    have r20 : reg n12 (20 : Fin 32) = 0x90 := by
      rw [P12.regs _ (by decide), u11.regs]; simp +decide only [runBlock, BInstr.run, pvGa96, upd, ↓reduceIte, aluEval]
    refine ⟨by rw [u14.regs, k13 sp (by decide), hsp], by rw [u14.regs, k13 _ (by decide)],
      by rw [u14.regs, k13 _ (by decide)], ?_, by rw [u14.regs, r913, show max L0 L1 - 1 + 1 = max L0 L1 by omega],
      by rw [hv, runBlock_reg _ _ _ _ z12 (by decide), r20], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv]; simp +decide only [runBlock, BInstr.run, pvGab6, upd, ↓reduceIte, aluEval]
    · rw [hv]; simp +decide only [runBlock, BInstr.run, pvGab6, upd, ↓reduceIte, aluEval]
    · rw [hv]; simp +decide only [runBlock, BInstr.run, pvGab6, upd, ↓reduceIte, aluEval]
      rw [sp12, r9_12]; exact s7_val _ _ (by omega)
    · rw [hv]; simp +decide only [runBlock, BInstr.run, pvGab6, upd, ↓reduceIte, aluEval]
    · rw [hv]; simp +decide only [runBlock, BInstr.run, pvGab6, upd, ↓reduceIte, aluEval]
    · rw [hv]; simp +decide only [runBlock, BInstr.run, pvGab6, upd, ↓reduceIte, aluEval, sp12]; rfl
    · rw [hv]; simp +decide only [runBlock, BInstr.run, pvGab6, upd, ↓reduceIte, aluEval]

end C3.RV32.Pv
