import C3BootProofs.Proofs.P2vEcMl

/-!
# `p256VerifyPrehash`: the main loop

The main loop of `u₁·G + u₂·Q`, from its head at 0x9F0 to its exit at
0xB00, against `mlLoop2`: one position per pass, doubling the accumulator
once it has an entry and then stepping the two pairs. It follows
`Pv384G2.lean`.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Sv

set_option maxRecDepth 100000

/-- The registers at the loop head, with `k + 1` positions left. -/
structure GH2 (B : Word) (m : Machine) (r3 r4 : Word) (k : Nat) : Prop where
  sp : reg m sp = B + 0x21A0
  g3 : reg m (3 : Fin 32) = r3
  g4 : reg m (4 : Fin 32) = r4
  s0 : reg m (8 : Fin 32) = 2
  s1 : reg m (9 : Fin 32) = BitVec.ofNat 32 (k + 1)
  s4 : reg m (20 : Fin 32) = 0x60
  s6 : reg m (22 : Fin 32) = 0x108
  s7 : reg m (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x10E8 + k)
  s8 : reg m (24 : Fin 32) = 0x101
  s9 : reg m (25 : Fin 32) = 0x300
  s10 : reg m (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300
  s11 : reg m (27 : Fin 32) = 0x10

theorem GH2.of {B : Word} {m m' : Machine} {r3 r4 : Word} {k : Nat} (R : GH2 B m r3 r4 k)
    (h : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 20, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) :
    GH2 B m' r3 r4 k :=
  ⟨by rw [h RV32.sp (by decide), R.sp], by rw [h _ (by decide), R.g3], by rw [h _ (by decide), R.g4],
    by rw [h _ (by decide), R.s0], by rw [h _ (by decide), R.s1], by rw [h _ (by decide), R.s4],
    by rw [h _ (by decide), R.s6], by rw [h _ (by decide), R.s7], by rw [h _ (by decide), R.s8],
    by rw [h _ (by decide), R.s9], by rw [h _ (by decide), R.s10], by rw [h _ (by decide), R.s11]⟩

def mlI0 : List BInstr := [.aluImm .and a0 (21 : Fin 32) 0x1]
theorem mlI0_end : blockEnd p256VerifyPrehashCode 0x9F0 mlI0 = some 0x9F4 := by decide
def mlD0 : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a1 sp 0x7FF,
  .aluImm .add a1 a1 0x181]
theorem mlD0_end : blockEnd p256VerifyPrehashCode 0x9F6 mlD0 = some 0xA06 := by decide
def mlD1 : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a1 sp 0x7FF,
  .aluImm .add a1 a1 0x481, .aluImm .add a2 x0 0x60]
theorem mlD1_end : blockEnd p256VerifyPrehashCode 0xA0E mlD1 = some 0xA22 := by decide
def mlB0 : List BInstr := [.aluImm .add (18 : Fin 32) x0 0x0, .aluImm .add (19 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]
theorem mlB0_end : blockEnd p256VerifyPrehashCode 0xA2A mlB0 = some 0xA30 := by decide
def mlE : List BInstr := [.aluImm .add (23 : Fin 32) (23 : Fin 32) 0xFFFFFFFF, .alu .add (9 : Fin 32) x0 (19 : Fin 32)]
theorem mlE_end : blockEnd p256VerifyPrehashCode 0xAF8 mlE = some 0xAFC := by decide

set_option maxHeartbeats 16000000 in
/-- The doubling at the top of a pass, from 0x9F0 to 0xA2A: the
accumulator doubled when it has an entry. -/
theorem ml2_dbl {B r3 r4 : Word} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} {k : Nat} {st : Pt2 × Bool}
    {m : Machine} (F : Fr B 0x3590) (E : MlEnv m.mem) (s : St m.mem P2V m 0x9F0 (reg m)) (R : GH2 B m r3 r4 k)
    (hs5 : reg m (21 : Fin 32) = if st.2 then 1 else 0) (M : GM2 B m.mem T0 T1 D0 D1)
    (A : ptF m.mem B 0x980 = st.1) (hl : Pt2Lt st.1) :
    ∃ m', Steps m m' ∧ MlEnv m'.mem ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧ P2vKeepL B m.mem m'.mem mlW ∧
      St m'.mem P2V m' 0xA2A (reg m') ∧ GH2 B m' r3 r4 k ∧ reg m' (21 : Fin 32) = (if st.2 then 1 else 0) ∧
      GM2 B m'.mem T0 T1 D0 D1 ∧ ptF m'.mem B 0x980 = (if st.2 then ptDbl2 st.1 else st.1) ∧
      Pt2Lt (if st.2 then ptDbl2 st.1 else st.1) := by
  have C := E.C.self
  obtain ⟨n1, c1, u1⟩ := s.block mlI0 C mlI0_end ⟨trivial, trivial⟩
  have s1 : St m.mem P2V n1 0x9F4 (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q ≠ a0 → reg n1 q = reg m q := fun q h => by
    rw [u1.regs, runBlock_reg _ _ _ q s.zero (by simp [mlI0, BInstr.dst, h])]
  have a01 : reg n1 a0 = if st.2 then 1 else 0 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, mlI0, upd, ↓reduceIte]; rw [hs5]
    cases st.2 <;> rfl
  have R1 : GH2 B n1 r3 r4 k := R.of fun q hq => k1 q (by revert hq; revert q; decide)
  cases hf : st.2
  · rw [hf] at a01 hs5
    obtain ⟨n2, d2, u2⟩ := s1.taken C 0xA2A p2v_at_9f4 (by decide) (by rw [a01, s1.zero]; rfl)
    have m2 : n2.mem = m.mem := u2.mem
    refine ⟨n2, c1.trans (.single d2), by rw [m2]; exact E, fun x _ => by rw [m2],
      (P2vKeepL.same m2).wider (by decide), ⟨u2.pc, rfl, fun _ => rfl⟩, R1.of fun q _ => u2.regs q,
      by rw [u2.regs, k1 _ (by decide), hs5], by rw [m2]; exact M, by rw [m2]; exact A, hl⟩
  · rw [hf] at a01 hs5
    obtain ⟨n2, d2, u2⟩ := s1.notTaken C 0x9F6 p2v_at_9f4 (by decide) (by rw [a01, s1.zero]; rfl)
    have s2 : St m.mem P2V n2 0x9F6 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
    obtain ⟨n3, c3, u3⟩ := s2.block mlD0 C mlD0_end ⟨trivial, trivial, trivial, trivial, trivial⟩
    have s3 : St n3.mem P2V n3 0xA06 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = m.mem := s2.mem ▸ u3.mem
    have k3 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg n3 q = reg m q := fun q h0 h1 => by
      rw [u3.regs, runBlock_reg _ _ _ q s2.zero (by simp [mlD0, BInstr.dst, h0, h1]), u2.regs, k1 q h0]
    have R3 : GH2 B n3 r3 r4 k := R.of fun q hq => k3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    have E3 : MlEnv n3.mem := by rw [m3]; exact E
    obtain ⟨n4, c4, s4, sp4, rk4, V4, K4, f4⟩ := p2v_pd2F (co := 0xC80) (cs := 0x980) F E3.C E3.PC s3 p2v_at_a06
      p2v_at_a0a (by decide) (by decide) R3.sp
      (by rw [u3.regs]; simp +decide only [runBlock, BInstr.run, mlD0, upd, ↓reduceIte]
          rw [u2.regs, k1 _ (by decide), R.sp]; simp only [aluEval]; exact sp_c80 _)
      (by rw [u3.regs]; simp +decide only [runBlock, BInstr.run, mlD0, upd, ↓reduceIte]
          rw [u2.regs, k1 _ (by decide), R.sp]; simp only [aluEval]; exact sp_980 _)
      (by decide) (by decide) (by decide) (by decide) (by rw [m3]; exact A) hl
    have E4 : MlEnv n4.mem := E3.fr F f4
    have R4 : GH2 B n4 r3 r4 k := R3.of fun q hq => by
      by_cases h : q = sp
      · subst h; rw [sp4, R3.sp]
      · exact rk4 q (by revert hq h; revert q; decide)
    obtain ⟨n5, c5, u5⟩ := s4.block mlD1 E4.C.self mlD1_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    have s5 : St n5.mem P2V n5 0xA22 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have m5 : n5.mem = n4.mem := u5.mem
    have k5 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n5 q = reg n4 q := fun q h0 h1 h2 => by
      rw [u5.regs, runBlock_reg _ _ _ q s4.zero (by simp [mlD1, BInstr.dst, h0, h1, h2])]
    have E5 : MlEnv n5.mem := by rw [m5]; exact E4
    obtain ⟨n6, P6, K6, X6⟩ := p2v_mc (c := 0x980) (d := 0xC80) (N := 0x60) F E5.C s5 p2v_at_a22 p2v_at_a26
      (by decide) (by decide) (by rw [k5 _ (by decide) (by decide) (by decide), R4.sp])
      (by rw [u5.regs]; simp +decide only [runBlock, BInstr.run, mlD1, upd, ↓reduceIte]
          rw [R4.sp]; simp only [aluEval]; exact sp_980 _)
      (by rw [u5.regs]; simp +decide only [runBlock, BInstr.run, mlD1, upd, ↓reduceIte]
          rw [R4.sp]; simp only [aluEval]; exact sp_c80 _)
      (by rw [u5.regs]; simp +decide only [runBlock, BInstr.run, mlD1, upd, ↓reduceIte, aluEval]; try rfl)
      (by decide) (by decide) (by decide)
    have hV : ptF n6.mem B 0x980 = ptDbl2 st.1 := by
      rw [ptF_cp X6 (c := 0xC80) (by decide) (by decide) (by decide), m5, V4]
    have K6' : P2vKeepL B n4.mem n6.mem [(0x980, 0x60)] := by rw [← m5]; exact P2vKeepL.of K6
    have KK : P2vKeepL B m.mem n6.mem mlW := by
      have := K4.trans K6'; rw [m3] at this; exact this.wider (by decide)
    refine ⟨n6, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans P6.steps)))), E5.fr F P6.fr,
      fun x hx => by rw [P6.fr x hx, m5, f4 x hx, m3], KK, P6.st,
      R4.of fun q hq => by rw [P6.regs q (by revert hq; revert q; decide), k5 q (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide)],
      by rw [P6.regs _ (by decide), k5 _ (by decide) (by decide) (by decide), rk4 _ (by decide),
        k3 _ (by decide) (by decide), hs5], M.keep KK, hV, ptDbl2_lt _⟩

theorem dec_ofNat2 (S : Word) (c : Nat) : S + BitVec.ofNat 32 (c + 1) + 0xFFFFFFFF = S + BitVec.ofNat 32 c := by
  rw [BitVec.add_assoc, ofNat_dec]

set_option maxHeartbeats 32000000 in
/-- **One pass of the main loop**, from 0x9F0 with `k + 1` positions left:
position `k`, as `mlIter2` computes it. -/
theorem ml2_body {B r3 r4 : Word} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} {k : Nat} {st : Pt2 × Bool}
    {m : Machine} (F : Fr B 0x3590) (E : MlEnv m.mem) (s : St m.mem P2V m 0x9F0 (reg m)) (R : GH2 B m r3 r4 k)
    (hs5 : reg m (21 : Fin 32) = if st.2 then 1 else 0) (M : GM2 B m.mem T0 T1 D0 D1)
    (A : ptF m.mem B 0x980 = st.1) (hl : Pt2Lt st.1) (hk : k + 1 ≤ 0x101) :
    (mlIter2 T0 T1 D0 D1 k st = none ∧ Panics m) ∨
    (∃ st', mlIter2 T0 T1 D0 D1 k st = some st' ∧
      ∃ m', Steps m m' ∧ MlEnv m'.mem ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧ P2vKeepL B m.mem m'.mem mlW ∧
        St m'.mem P2V m' (if k = 0 then 0xB00 else 0x9F0) (reg m') ∧ (k ≠ 0 → GH2 B m' r3 r4 (k - 1)) ∧
        reg m' sp = B + 0x21A0 ∧ reg m' (3 : Fin 32) = r3 ∧ reg m' (4 : Fin 32) = r4 ∧
        reg m' (21 : Fin 32) = (if st'.2 then 1 else 0) ∧ GM2 B m'.mem T0 T1 D0 D1 ∧
        ptF m'.mem B 0x980 = st'.1 ∧ Pt2Lt st'.1) := by
  obtain ⟨n1, c1, E1, fr1, K1, s1, R1, h21, M1, A1, l1⟩ := ml2_dbl F E s R hs5 M A hl
  have C := E1.C.self
  obtain ⟨n2, c2, u2⟩ := s1.block mlB0 C mlB0_end ⟨trivial, trivial, trivial⟩
  have s2 : St n1.mem P2V n2 0xA30 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have k2 : ∀ q : Fin 32, q ≠ (18 : Fin 32) → q ≠ (19 : Fin 32) → reg n2 q = reg n1 q := fun q h0 h1 => by
    rw [u2.regs, runBlock_reg _ _ _ q s1.zero (by simp [mlB0, BInstr.dst, h0, h1])]
  have r18 : reg n2 (18 : Fin 32) = BitVec.ofNat 32 0 := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, mlB0, upd, ↓reduceIte, aluEval]; rw [s1.zero]; rfl
  have r19 : reg n2 (19 : Fin 32) = BitVec.ofNat 32 k := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, mlB0, upd, ↓reduceIte, aluEval]; rw [R1.s1]
    exact ofNat_dec k
  obtain ⟨n3, c3, u3⟩ := s2.block mlHd C mlHd_end ⟨trivial, trivial, trivial⟩
  have s3 : St n1.mem P2V n3 0xA36 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  have k3 : ∀ q : Fin 32, q ≠ a0 → reg n3 q = reg n2 q := fun q h => by
    rw [u3.regs, runBlock_reg _ _ _ q s2.zero (by simp [mlHd, BInstr.dst, h])]
  have a03 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 (0x10E8 + k + 0x108 * 0) := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, mlHd, upd, ↓reduceIte, aluEval]
    rw [r18, k2 _ (by decide) (by decide), k2 _ (by decide) (by decide), R1.s6, R1.s7]
    exact ofNat_mul_add (B + 0x21A0) 0 (0x10E8 + k) 0x108 (by omega) (by decide) (by decide)
  obtain ⟨n4, d4, u4⟩ := s3.notTaken C 0xA3A p2v_at_a36 (by decide)
    (by rw [k3 _ (by decide), r18, k3 _ (by decide), k2 _ (by decide) (by decide), R1.s0]; decide)
  have e4 : reg n4 = reg n3 := funext u4.regs
  have s4 : St n4.mem P2V n4 0xA3A (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n1.mem := u4.mem
  have G4 : GR2 B n4 r3 r4 k := by
    have h : ∀ q : Fin 32, q ≠ a0 → q ≠ (18 : Fin 32) → q ≠ (19 : Fin 32) → reg n4 q = reg n1 q := fun q h0 h1 h2 => by
      rw [e4, k3 q h0, k2 q h1 h2]
    exact ⟨by rw [h _ (by decide) (by decide) (by decide), R1.sp], by rw [h _ (by decide) (by decide) (by decide), R1.g3],
      by rw [h _ (by decide) (by decide) (by decide), R1.g4], by rw [h _ (by decide) (by decide) (by decide), R1.s0],
      by rw [h _ (by decide) (by decide) (by decide), R1.s1], by rw [e4, k3 _ (by decide), r19],
      by rw [h _ (by decide) (by decide) (by decide), R1.s4], by rw [h _ (by decide) (by decide) (by decide), R1.s6],
      by rw [h _ (by decide) (by decide) (by decide), R1.s7], by rw [h _ (by decide) (by decide) (by decide), R1.s8],
      by rw [h _ (by decide) (by decide) (by decide), R1.s9], by rw [h _ (by decide) (by decide) (by decide), R1.s10],
      by rw [h _ (by decide) (by decide) (by decide), R1.s11]⟩
  have E4 : MlEnv n4.mem := by rw [m4]; exact E1
  unfold mlIter2
  have P0 := ml2_pair (j := 0) (st := (if st.2 then ptDbl2 st.1 else st.1, st.2)) F E4 s4 G4
    (by rw [e4, k3 _ (by decide), k2 _ (by decide) (by decide), h21])
    (by rw [e4, k3 _ (by decide), r18]) (by rw [e4, a03]) (by rw [m4]; exact M1) (by rw [m4]; exact A1) l1
    (by decide) hk
  simp only [ite_true] at P0
  rcases P0 with ⟨hn, hp⟩ | ⟨st1, h1, n5, c5, E5, fr5, K5, s5, G5, r21, r18', a05, M5, A5, l5⟩
  · left; rw [hn]
    exact ⟨rfl, Panics.of_steps (c1.trans (c2.trans (c3.trans (.single d4)))) hp⟩
  rw [h1, Option.bind_some]
  have P1 := ml2_pair (j := 1) (st := st1) F E5 s5 G5 r21 r18' a05 M5 A5 l5 (by decide) hk
  simp only [Nat.one_ne_zero, ite_false] at P1
  rcases P1 with ⟨hn, hp⟩ | ⟨st2, h2, n6, c6, E6, fr6, K6, s6, G6, r21', -, -, M6, A6, l6⟩
  · left; rw [hn]
    exact ⟨rfl, Panics.of_steps (c1.trans (c2.trans (c3.trans (.cons d4 c5)))) hp⟩
  right
  refine ⟨st2, h2, ?_⟩
  obtain ⟨n7, c7, u7⟩ := s6.block mlE E6.C.self mlE_end ⟨trivial, trivial, trivial⟩
  have s7 : St n6.mem P2V n7 0xAFC (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
  have k7 : ∀ q : Fin 32, q ≠ (23 : Fin 32) → q ≠ (9 : Fin 32) → reg n7 q = reg n6 q := fun q h0 h1 => by
    rw [u7.regs, runBlock_reg _ _ _ q s6.zero (by simp [mlE, BInstr.dst, h0, h1])]
  have r9 : reg n7 (9 : Fin 32) = BitVec.ofNat 32 k := by
    rw [u7.regs]; simp +decide only [runBlock, BInstr.run, mlE, upd, ↓reduceIte, aluEval]
    rw [G6.s3]; exact BitVec.zero_add _
  have st : Steps m n7 := c1.trans (c2.trans (c3.trans (.cons d4 (c5.trans (c6.trans c7)))))
  have k7' : ∀ q : Fin 32, q.val ∈ [2, 3, 4] → reg n7 q = reg n6 q := fun q hq =>
    k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  have KK : P2vKeepL B m.mem n6.mem mlW := by
    rw [m4] at K5; exact ((K1.trans K5).trans K6).wider (by decide)
  have fr : ∀ x, P2vR B x → n6.mem x = m.mem x := fun x hx => by rw [fr6 x hx, fr5 x hx, m4, fr1 x hx]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    obtain ⟨n8, d8, u8⟩ := s7.notTaken E6.C.self 0xB00 p2v_at_afc (by decide)
      (by rw [k7 _ (by decide) (by decide), G6.s3, s7.zero]; decide)
    exact ⟨n8, st.trans (.single d8), by rw [u8.mem]; exact E6, fun x hx => by rw [u8.mem, fr x hx],
      by rw [u8.mem]; exact KK, ⟨u8.pc, rfl, fun _ => rfl⟩, fun h => absurd rfl h,
      by rw [u8.regs, k7' sp (by decide), G6.sp],
      by rw [u8.regs, k7' _ (by decide), G6.g3], by rw [u8.regs, k7' _ (by decide), G6.g4],
      by rw [u8.regs, k7 _ (by decide) (by decide), r21'], by rw [u8.mem]; exact M6,
      by rw [u8.mem]; exact A6, l6⟩
  · obtain ⟨n8, d8, u8⟩ := s7.taken E6.C.self 0x9F0 p2v_at_afc (by decide)
      (by rw [k7 _ (by decide) (by decide), G6.s3, s7.zero]; simp only [branchTaken]
          exact bne_iff_ne.2 (Pv.ofNat_ne0 hk0 (by omega)))
    have r23 : reg n7 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x10E8 + (k - 1)) := by
      rw [u7.regs]; simp +decide only [runBlock, BInstr.run, mlE, upd, ↓reduceIte, aluEval]
      rw [G6.s7, show 0x10E8 + k = 0x10E8 + (k - 1) + 1 by omega]; exact dec_ofNat2 _ _
    rw [ite_eq_right (by omega)]
    refine ⟨n8, st.trans (.single d8), by rw [u8.mem]; exact E6, fun x hx => by rw [u8.mem, fr x hx],
      by rw [u8.mem]; exact KK, ⟨u8.pc, rfl, fun _ => rfl⟩, fun _ => ?_, by rw [u8.regs, k7' sp (by decide), G6.sp],
      by rw [u8.regs, k7' _ (by decide), G6.g3], by rw [u8.regs, k7' _ (by decide), G6.g4],
      by rw [u8.regs, k7 _ (by decide) (by decide), r21'], by rw [u8.mem]; exact M6,
      by rw [u8.mem]; exact A6, l6⟩
    exact ⟨by rw [u8.regs, k7 _ (by decide) (by decide), G6.sp], by rw [u8.regs, k7 _ (by decide) (by decide), G6.g3],
      by rw [u8.regs, k7 _ (by decide) (by decide), G6.g4], by rw [u8.regs, k7 _ (by decide) (by decide), G6.s0],
      by rw [u8.regs, r9, show k - 1 + 1 = k by omega], by rw [u8.regs, k7 _ (by decide) (by decide), G6.s4],
      by rw [u8.regs, k7 _ (by decide) (by decide), G6.s6], by rw [u8.regs, r23],
      by rw [u8.regs, k7 _ (by decide) (by decide), G6.s8], by rw [u8.regs, k7 _ (by decide) (by decide), G6.s9],
      by rw [u8.regs, k7 _ (by decide) (by decide), G6.s10], by rw [u8.regs, k7 _ (by decide) (by decide), G6.s11]⟩

/-- **The main loop**, from its head at 0x9F0 with `k + 1` positions left to
its exit at 0xB00, as `mlLoop2` computes it. -/
theorem ml2_loop {B r3 r4 : Word} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} (F : Fr B 0x3590) :
    ∀ k {m : Machine} {st : Pt2 × Bool}, MlEnv m.mem → St m.mem P2V m 0x9F0 (reg m) → GH2 B m r3 r4 k →
      reg m (21 : Fin 32) = (if st.2 then 1 else 0) → GM2 B m.mem T0 T1 D0 D1 → ptF m.mem B 0x980 = st.1 →
      Pt2Lt st.1 → k + 1 ≤ 0x101 →
      (mlLoop2 T0 T1 D0 D1 (k + 1) st = none ∧ Panics m) ∨
      (∃ st', mlLoop2 T0 T1 D0 D1 (k + 1) st = some st' ∧
        ∃ m', Steps m m' ∧ MlEnv m'.mem ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧ P2vKeepL B m.mem m'.mem mlW ∧
          St m'.mem P2V m' 0xB00 (reg m') ∧ reg m' sp = B + 0x21A0 ∧ reg m' (3 : Fin 32) = r3 ∧
          reg m' (4 : Fin 32) = r4 ∧ reg m' (21 : Fin 32) = (if st'.2 then 1 else 0) ∧
          GM2 B m'.mem T0 T1 D0 D1 ∧ ptF m'.mem B 0x980 = st'.1 ∧ Pt2Lt st'.1)
  | k, m, st, E, s, R, hs5, M, A, hl, hk => by
    rcases ml2_body F E s R hs5 M A hl hk with
      ⟨hn, hp⟩ | ⟨st1, h1, n1, c1, E1, fr1, K1, s1, G1, sp1, g31, g41, r21, M1, A1, l1⟩
    · left; simp only [mlLoop2, hn, Option.bind_none]; exact ⟨trivial, hp⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      right
      exact ⟨st1, by simp only [mlLoop2, h1, Option.bind_some], n1, c1, E1, fr1, K1, s1, sp1, g31, g41, r21, M1, A1, l1⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [ite_eq_right (by omega)] at s1
      have G1' := G1 (by omega)
      rw [show k' + 1 - 1 = k' by omega] at G1'
      rcases ml2_loop F k' E1 s1 G1' r21 M1 A1 l1 (by omega) with ⟨hn, hp⟩ | ⟨st2, h2, n2, c2, rest⟩
      · left; simp only [mlLoop2, h1, Option.bind_some]
        exact ⟨by simpa [mlLoop2] using hn, Panics.of_steps c1 hp⟩
      · right
        refine ⟨st2, by simp only [mlLoop2, h1, Option.bind_some]; simpa [mlLoop2] using h2, n2, c1.trans c2, ?_⟩
        obtain ⟨E2, fr2, K2, rest⟩ := rest
        exact ⟨E2, fun x hx => by rw [fr2 x hx, fr1 x hx], (K1.trans K2).wider (by decide), rest⟩

end C3.RV32.P2v
