import C3BootProofs.Proofs.SvEcMl

/-!
# `sigstore::verify`: the P-256 check's main loop, by position

One position of the main loop, from 0x195C: double the accumulator once it
has an entry, step the two pairs, and move to the next position. The loop
runs from the longest wNAF's last position down to position 0 and leaves at
0x1A72, as `mlLoop2` does. It follows `Pv384G2.lean`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

/-- The registers the main loop keeps at every position. -/
structure GX2 (B : Word) (m : Machine) (r3 r4 r18 r19 r26 : Word) : Prop where
  sp : reg m sp = B + 0x21A0
  g3 : reg m (3 : Fin 32) = r3
  g4 : reg m (4 : Fin 32) = r4
  s2 : reg m (18 : Fin 32) = r18
  s3 : reg m (19 : Fin 32) = r19
  s4 : reg m (20 : Fin 32) = 0x60
  s5 : reg m (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40
  s8 : reg m (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60
  s10 : reg m (26 : Fin 32) = r26
  s11 : reg m (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20

theorem GR2.x {B r3 r4 r18 r19 r25 r26 : Word} {m : Machine} {k : Nat} (R : GR2 B m r3 r4 r18 r19 r25 r26 k) :
    GX2 B m r3 r4 r18 r19 r26 :=
  ⟨R.sp, R.g3, R.g4, R.s2, R.s3, R.s4, R.s5, R.s8, R.s10, R.s11⟩

theorem GX2.of {B r3 r4 r18 r19 r26 : Word} {m m' : Machine} (X : GX2 B m r3 r4 r18 r19 r26)
    (h : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 24, 26, 27] → reg m' q = reg m q) :
    GX2 B m' r3 r4 r18 r19 r26 :=
  ⟨by rw [h RV32.sp (by decide), X.sp], by rw [h _ (by decide), X.g3], by rw [h _ (by decide), X.g4],
    by rw [h _ (by decide), X.s2], by rw [h _ (by decide), X.s3], by rw [h _ (by decide), X.s4],
    by rw [h _ (by decide), X.s5], by rw [h _ (by decide), X.s8], by rw [h _ (by decide), X.s10],
    by rw [h _ (by decide), X.s11]⟩

theorem GX2.gr {B r3 r4 r18 r19 r25 r26 : Word} {m : Machine} {k : Nat} (X : GX2 B m r3 r4 r18 r19 r26)
    (h9 : reg m (9 : Fin 32) = BitVec.ofNat 32 (k + 1))
    (h22 : reg m (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x1024 + k)) (h25 : reg m (25 : Fin 32) = r25) :
    GR2 B m r3 r4 r18 r19 r25 r26 k :=
  ⟨X.sp, X.g3, X.g4, h9, X.s2, X.s3, X.s4, X.s5, h22, X.s8, h25, X.s10, X.s11⟩

theorem ofNat_succ_dec (k : Nat) : BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF = BitVec.ofNat 32 k := by
  have := ltl_dec_ofNat (k := k) 0
  rwa [show (0 : Word) + BitVec.ofNat 32 (k + 1) = BitVec.ofNat 32 (k + 1) from BitVec.zero_add _,
    show (0 : Word) + BitVec.ofNat 32 k = BitVec.ofNat 32 k from BitVec.zero_add _] at this

theorem mlW_dup {L : List (Nat × Nat)} (h : ∀ p ∈ L, p ∈ mlW) :
    ∀ p ∈ L, ∃ q ∈ mlW, q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2 :=
  fun p hp => ⟨p, h p hp, Nat.le_refl _, Nat.le_refl _⟩

def mlI0 : List BInstr := [.aluImm .and a0 (8 : Fin 32) 0x1]
theorem mlI0_end : blockEnd sigstoreVerifyCode 0x195C mlI0 = some 0x1960 := by decide
def mlD0 : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .lui a1 0x1000,
  .aluImm .add a1 a1 0x480, .alu .add a1 a1 sp]
theorem mlD0_end : blockEnd sigstoreVerifyCode 0x1962 mlD0 = some 0x1972 := by decide
def mlD1 : List BInstr := [.lui a0 0x1000, .aluImm .add a0 a0 0x480, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF,
  .aluImm .add a1 a1 0x221, .aluImm .add a2 x0 0x60]
theorem mlD1_end : blockEnd sigstoreVerifyCode 0x197A mlD1 = some 0x198E := by decide
def mlI1 : List BInstr := [.aluImm .add (23 : Fin 32) x0 0x0, .aluImm .add (25 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]
theorem mlI1_end : blockEnd sigstoreVerifyCode 0x1996 mlI1 = some 0x199C := by decide
def mlE : List BInstr := [.aluImm .add (22 : Fin 32) (22 : Fin 32) 0xFFFFFFFF, .alu .add (9 : Fin 32) x0 (25 : Fin 32)]
theorem mlE_end : blockEnd sigstoreVerifyCode 0x1A6A mlE = some 0x1A6E := by decide

set_option maxHeartbeats 16000000 in
/-- **The doubling**, from 0x195C to 0x1996: once the accumulator has an
entry, double it into the scratch point at 0xA20 and copy it back. -/
theorem ml2_dbl {B r3 r4 r18 r19 r25 r26 : Word} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} {k : Nat} {P : Pt2}
    {b : Bool} {m : Machine} (F : Fr B 0x3830) (E : MlEnv m.mem) (s : St m.mem SV m 0x195C (reg m))
    (R : GR2 B m r3 r4 r18 r19 r25 r26 k) (hs0 : reg m (8 : Fin 32) = if b then 1 else 0)
    (M : GM2 B m.mem T0 T1 D0 D1) (A : ptF m.mem B 0x1480 = P) (hl : Pt2Lt P) :
    ∃ m', Steps m m' ∧ MlEnv m'.mem ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ SvKeepL B m.mem m'.mem mlW ∧
      St m'.mem SV m' 0x1996 (reg m') ∧ GR2 B m' r3 r4 r18 r19 r25 r26 k ∧
      reg m' (8 : Fin 32) = (if b then 1 else 0) ∧ GM2 B m'.mem T0 T1 D0 D1 ∧
      ptF m'.mem B 0x1480 = (if b then ptDbl2 P else P) ∧ Pt2Lt (if b then ptDbl2 P else P) := by
  have C := E.C.self
  have hz := s.zero
  obtain ⟨n0, c0, u0⟩ := s.block mlI0 C mlI0_end ⟨trivial, trivial⟩
  have s0 : St m.mem SV n0 0x1960 (reg n0) := ⟨u0.pc, u0.mem, fun _ => rfl⟩
  have k0 : ∀ q : Fin 32, q ≠ a0 → reg n0 q = reg m q := fun q h =>
    by rw [u0.regs, runBlock_reg _ _ _ q hz (by simp [mlI0, BInstr.dst, h])]
  have a00 : reg n0 a0 = if b then 1 else 0 := by
    rw [u0.regs]; simp +decide only [runBlock, BInstr.run, mlI0, upd, ↓reduceIte, aluEval]; rw [hs0]; cases b <;> rfl
  cases b
  · -- no entry yet: no doubling
    obtain ⟨n1, d1, u1⟩ := s0.taken C 0x1996 sv_at_1960 (by decide) (by rw [a00, s0.zero]; rfl)
    have m1 : n1.mem = m.mem := u1.mem
    refine ⟨n1, c0.trans (.cons d1 (.refl _)), by rw [m1]; exact E, fun x _ => by rw [m1],
      (SvKeepL.same m1).wider (fun p hp => by simp at hp), ⟨u1.pc, rfl, fun _ => rfl⟩,
      R.of fun q hq => by rw [u1.regs q, k0 q (by revert hq; revert q; decide)],
      by rw [u1.regs, k0 _ (by decide), hs0], by rw [m1]; exact M, by rw [m1]; exact A, hl⟩
  · obtain ⟨n1, d1, u1⟩ := s0.notTaken C 0x1962 sv_at_1960 (by decide) (by rw [a00, s0.zero]; rfl)
    obtain ⟨n2, c2, u2⟩ := u1.self.block mlD0 C mlD0_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    have s2 : St m.mem SV n2 0x1972 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
    have k2 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg n2 q = reg m q := fun q h0 h1 => by
      rw [u2.regs, runBlock_reg _ _ _ q u1.self.zero (by simp [mlD0, BInstr.dst, h0, h1]), u1.regs, k0 q h0]
    have sp2 : reg n2 sp = B + 0x21A0 := by rw [k2 _ (by decide) (by decide), R.sp]
    have a02 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [u2.regs]; simp +decide only [runBlock, BInstr.run, mlD0, upd, ↓reduceIte]
      rw [u1.regs, k0 _ (by decide), R.sp]; simp only [aluEval]; exact sp_a20 _
    have a12 : reg n2 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
      rw [u2.regs]; simp +decide only [runBlock, BInstr.run, mlD0, upd, ↓reduceIte]
      rw [u1.regs, k0 _ (by decide), R.sp]; simp only [aluEval]; exact sp_1480 _
    obtain ⟨n3, c3, s3, sp3, rk3, V3, K3, f3⟩ := sv_pd2F (co := 0xA20) (cs := 0x1480) F E.C E.PC s2 sv_at_1972
      sv_at_1976 (by decide) (by decide) sp2 a02 a12 (by decide) (by decide) (by decide) (by decide) A hl
    have E3 : MlEnv n3.mem := E.fr F f3
    obtain ⟨n4, c4, u4⟩ := s3.block mlD1 E3.C.self mlD1_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have s4 : St n4.mem SV n4 0x198E (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have k4 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n4 q = reg n3 q := fun q h0 h1 h2 => by
      rw [u4.regs, runBlock_reg _ _ _ q s3.zero (by simp [mlD1, BInstr.dst, h0, h1, h2])]
    have a04 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
      rw [u4.regs]; simp +decide only [runBlock, BInstr.run, mlD1, upd, ↓reduceIte]; rw [sp3]; simp only [aluEval]
      exact sp_1480 _
    have a14 : reg n4 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [u4.regs]; simp +decide only [runBlock, BInstr.run, mlD1, upd, ↓reduceIte]; rw [sp3]; simp only [aluEval]
      exact sp_a20 _
    have a24 : reg n4 a2 = BitVec.ofNat 32 0x60 := by
      rw [u4.regs]; simp +decide only [runBlock, BInstr.run, mlD1, upd, ↓reduceIte]
    have sp4 : reg n4 sp = B + 0x21A0 := by rw [k4 _ (by decide) (by decide) (by decide), sp3]
    have E4 : MlEnv n4.mem := by rw [m4]; exact E3
    obtain ⟨n5, P5, K5, X5⟩ := sv_mc (c := 0x1480) (d := 0xA20) (N := 0x60) F E4.C s4 sv_at_198e sv_at_1992
      (by decide) (by decide) sp4 a04 a14 a24 (by decide) (by decide) (by decide)
    have E5 : MlEnv n5.mem := E4.fr F P5.fr
    have V5 : ptF n5.mem B 0x1480 = ptDbl2 P := by
      rw [ptF_cp X5 (c := 0xA20) (by decide) (by decide) (by decide), m4, V3]
    have K5' : SvKeepL B n3.mem n5.mem [(0x1480, 0x60)] := by rw [← m4]; exact SvKeepL.of K5
    have KK : SvKeepL B m.mem n5.mem mlW := (K3.trans K5').wider (mlW_dup fun p hp => by simpa [mlW] using hp)
    have rr : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 24, 25, 26, 27] → reg n5 q = reg m q :=
      fun q hq => by
        rw [P5.regs q (by revert hq; revert q; decide), k4 q (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
        by_cases h : q = sp
        · subst h; rw [sp3, R.sp]
        · rw [rk3 q (by revert hq h; revert q; decide), k2 q (by revert hq; revert q; decide)
            (by revert hq; revert q; decide)]
    exact ⟨n5, c0.trans (.cons d1 (c2.trans (c3.trans (c4.trans P5.steps)))), E5,
      fun x hx => by rw [P5.fr x hx, m4, f3 x hx], KK, P5.st,
      R.of fun q hq => rr q (by revert hq; revert q; decide), by rw [rr _ (by decide), hs0], M.keep KK, V5,
      ptDbl2_lt P⟩

set_option maxHeartbeats 32000000 in
/-- **One position of the main loop**, from 0x195C to 0x1A6E: the doubling
and the two pairs, as `mlIter2` does. -/
theorem ml2_iter {B r3 r4 r18 r19 r25 r26 : Word} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} {k : Nat}
    {st : Pt2 × Bool} {m : Machine} (F : Fr B 0x3830) (E : MlEnv m.mem) (s : St m.mem SV m 0x195C (reg m))
    (R : GR2 B m r3 r4 r18 r19 r25 r26 k) (hs0 : reg m (8 : Fin 32) = if st.2 then 1 else 0)
    (M : GM2 B m.mem T0 T1 D0 D1) (A : ptF m.mem B 0x1480 = st.1) (hl : Pt2Lt st.1) (hk : k + 1 ≤ 0x101) :
    (mlIter2 T0 T1 D0 D1 k st = none ∧ Panics m) ∨
    (∃ st', mlIter2 T0 T1 D0 D1 k st = some st' ∧
      ∃ m', Steps m m' ∧ MlEnv m'.mem ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ SvKeepL B m.mem m'.mem mlW ∧
        St m'.mem SV m' 0x1A6E (reg m') ∧ GX2 B m' r3 r4 r18 r19 r26 ∧
        reg m' (9 : Fin 32) = BitVec.ofNat 32 k ∧ reg m' (25 : Fin 32) = BitVec.ofNat 32 k ∧
        reg m' (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x1023 + k) ∧
        reg m' (8 : Fin 32) = (if st'.2 then 1 else 0) ∧
        GM2 B m'.mem T0 T1 D0 D1 ∧ ptF m'.mem B 0x1480 = st'.1 ∧ Pt2Lt st'.1) := by
  obtain ⟨P, b⟩ := st
  obtain ⟨n1, c1, E1, fr1, K1, s1, R1, r81, M1, A1, l1⟩ := ml2_dbl F E s R hs0 M A hl
  have C := E1.C.self
  obtain ⟨n2, c2, u2⟩ := s1.block mlI1 C mlI1_end ⟨trivial, trivial, trivial⟩
  have s2 : St n1.mem SV n2 0x199C (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have k2 : ∀ q : Fin 32, q ≠ (23 : Fin 32) → q ≠ (25 : Fin 32) → reg n2 q = reg n1 q := fun q h1 h2 => by
    rw [u2.regs, runBlock_reg _ _ _ q s1.zero (by simp [mlI1, BInstr.dst, h1, h2])]
  have r232 : reg n2 (23 : Fin 32) = BitVec.ofNat 32 0 := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, mlI1, upd, ↓reduceIte, aluEval]; rw [s1.zero]; rfl
  have r252 : reg n2 (25 : Fin 32) = BitVec.ofNat 32 k := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, mlI1, upd, ↓reduceIte, aluEval]; rw [R1.s1]
    exact ofNat_succ_dec k
  obtain ⟨n3, c3, u3⟩ := s2.block mlHd C mlHd_end ⟨trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n1.mem := u3.mem
  have s3 : St n3.mem SV n3 0x19A6 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have k3 : ∀ q : Fin 32, q ≠ a0 → reg n3 q = reg n2 q := fun q h =>
    by rw [u3.regs, runBlock_reg _ _ _ q s2.zero (by simp [mlHd, BInstr.dst, h])]
  have a03 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 (0x1024 + k + 0x108 * 0) := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, mlHd, upd, ↓reduceIte, aluEval]
    rw [r232, s2.zero, k2 _ (by decide) (by decide), R1.s6, BitVec.zero_mul, BitVec.zero_add]; rfl
  have R3 : GR2 B n3 r3 r4 r18 r19 (BitVec.ofNat 32 k) r26 k :=
    (R1.x.of fun q hq => by rw [k3 q (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)]).gr
      (by rw [k3 _ (by decide), k2 _ (by decide) (by decide), R1.s1])
      (by rw [k3 _ (by decide), k2 _ (by decide) (by decide), R1.s6]) (by rw [k3 _ (by decide), r252])
  have E3 : MlEnv n3.mem := by rw [m3]; exact E1
  have M3 : GM2 B n3.mem T0 T1 D0 D1 := by rw [m3]; exact M1
  have A3 : ptF n3.mem B 0x1480 = (if b then ptDbl2 P else P, b).1 := by rw [m3]; exact A1
  have t3 : Steps m n3 := c1.trans (c2.trans c3)
  rcases ml2_pair (j := 0) (st := (if b then ptDbl2 P else P, b)) F E3 s3 R3
      (by rw [k3 _ (by decide), k2 _ (by decide) (by decide), r81]) (by rw [k3 _ (by decide), r232]) a03 M3 A3 l1
      (by decide) hk with ⟨hn, hp⟩ | ⟨st1, h1, n4, c4, E4, fr4, K4, s4, R4, r84, r234, a04, M4, A4, l4⟩
  · have hn' : mlPair2 T0 D0 k (if b then ptDbl2 P else P, b) = none := hn
    exact .inl ⟨by show (mlPair2 T0 D0 k _).bind _ = none; rw [hn']; rfl, Panics.of_steps t3 hp⟩
  have h1' : mlPair2 T0 D0 k (if b then ptDbl2 P else P, b) = some st1 := h1
  rcases ml2_pair (j := 1) (st := st1) F E4 s4 R4 r84 r234 a04 M4 A4 l4 (by decide) hk with
    ⟨hn, hp⟩ | ⟨st2, h2, n5, c5, E5, fr5, K5, s5, R5, r85, r235, a05, M5, A5, l5⟩
  · have hn' : mlPair2 T1 D1 k st1 = none := hn
    exact .inl ⟨by show (mlPair2 T0 D0 k _).bind _ = none; rw [h1']; exact hn', Panics.of_steps (t3.trans c4) hp⟩
  have h2' : mlPair2 T1 D1 k st1 = some st2 := h2
  refine .inr ⟨st2, by show (mlPair2 T0 D0 k _).bind _ = _; rw [h1']; exact h2', ?_⟩
  -- the pair loop ends
  have C5 := E5.C.self
  obtain ⟨n6, c6, u6⟩ := s5.block mlA C5 mlA_end ⟨trivial, trivial⟩
  have s6 : St n5.mem SV n6 0x19A8 (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
  have k6 : ∀ q : Fin 32, q ≠ a1 → reg n6 q = reg n5 q := fun q h =>
    by rw [u6.regs, runBlock_reg _ _ _ q s5.zero (by simp [mlA, BInstr.dst, h])]
  have a16 : reg n6 a1 = 2 := by
    rw [u6.regs]; simp +decide only [runBlock, BInstr.run, mlA, upd, ↓reduceIte, aluEval]; rw [s5.zero]; rfl
  obtain ⟨n7, d7, u7⟩ := s6.taken C5 0x1A6A sv_at_19a8 (by decide)
    (by rw [k6 _ (by decide), r235, a16]; rfl)
  obtain ⟨n8, c8, u8⟩ := u7.self.block mlE C5 mlE_end ⟨trivial, trivial, trivial⟩
  have m8 : n8.mem = n5.mem := u8.mem
  have k8 : ∀ q : Fin 32, q ≠ (22 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ a1 → reg n8 q = reg n5 q := fun q h1 h2 h3 => by
    rw [u8.regs, runBlock_reg _ _ _ q u7.self.zero (by simp [mlE, BInstr.dst, h1, h2]), u7.regs, k6 q h3]
  have r228 : reg n8 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x1023 + k) := by
    rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlE, upd, ↓reduceIte, aluEval]
    rw [u7.regs, k6 _ (by decide), R5.s6, show 0x1024 + k = 0x1023 + k + 1 by omega]
    exact ltl_dec_ofNat _
  have r258 : reg n8 (25 : Fin 32) = BitVec.ofNat 32 k := by rw [k8 _ (by decide) (by decide) (by decide), R5.s9]
  have r98 : reg n8 (9 : Fin 32) = BitVec.ofNat 32 k := by
    rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlE, upd, ↓reduceIte, aluEval]
    rw [u7.regs, k6 _ (by decide), R5.s9]; exact BitVec.zero_add _
  have K4' : SvKeepL B n1.mem n4.mem mlW := by rw [← m3]; exact K4
  refine ⟨n8, t3.trans (c4.trans (c5.trans (c6.trans (.cons d7 c8)))), by rw [m8]; exact E5,
    fun x hx => by rw [m8, fr5 x hx, fr4 x hx, m3, fr1 x hx], ?_, ⟨u8.pc, rfl, fun _ => rfl⟩,
    R5.x.of fun q hq => k8 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide),
    r98, r258, r228, by rw [k8 _ (by decide) (by decide) (by decide), r85], by rw [m8]; exact M5,
    by rw [m8]; exact A5, l5⟩
  rw [m8]
  exact ((K1.trans K4').trans K5).wider (mlW_dup fun p hp => by
    simp only [List.mem_append, or_self] at hp; exact hp)

set_option maxHeartbeats 16000000 in
/-- **The main loop**, from 0x195C at position `k` to 0x1A72: positions
`k` down to 0, as `mlLoop2` does. -/
theorem ml2_loop {B r3 r4 r18 r19 r26 : Word} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} (F : Fr B 0x3830) :
    ∀ (k : Nat) {r25 : Word} {st : Pt2 × Bool} {m : Machine}, MlEnv m.mem → St m.mem SV m 0x195C (reg m) →
      GR2 B m r3 r4 r18 r19 r25 r26 k → reg m (8 : Fin 32) = (if st.2 then 1 else 0) →
      GM2 B m.mem T0 T1 D0 D1 → ptF m.mem B 0x1480 = st.1 → Pt2Lt st.1 → k + 1 ≤ 0x101 →
      (mlLoop2 T0 T1 D0 D1 (k + 1) st = none ∧ Panics m) ∨
      (∃ st', mlLoop2 T0 T1 D0 D1 (k + 1) st = some st' ∧
        ∃ m', Steps m m' ∧ MlEnv m'.mem ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ SvKeepL B m.mem m'.mem mlW ∧
          St m'.mem SV m' 0x1A72 (reg m') ∧ GX2 B m' r3 r4 r18 r19 r26 ∧
          reg m' (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1023 ∧
          reg m' (8 : Fin 32) = (if st'.2 then 1 else 0) ∧
          GM2 B m'.mem T0 T1 D0 D1 ∧ ptF m'.mem B 0x1480 = st'.1 ∧ Pt2Lt st'.1) := by
  intro k
  induction k with
  | zero =>
    intro r25 st m E s R hs0 M A hl hk
    rcases ml2_iter F E s R hs0 M A hl hk with
      ⟨hn, hp⟩ | ⟨st1, h1, n1, c1, E1, fr1, K1, s1, X1, r91, r251, r221, r81, M1, A1, l1⟩
    · exact .inl ⟨by show (mlIter2 T0 T1 D0 D1 0 st).bind _ = none; rw [hn]; rfl, hp⟩
    refine .inr ⟨st1, by show (mlIter2 T0 T1 D0 D1 0 st).bind _ = _; rw [h1]; rfl, ?_⟩
    obtain ⟨n2, d2, u2⟩ := s1.notTaken E1.C.self 0x1A72 sv_at_1a6e (by decide) (by rw [r251, s1.zero]; rfl)
    have m2 : n2.mem = n1.mem := u2.mem
    exact ⟨n2, c1.trans (.cons d2 (.refl _)), by rw [m2]; exact E1, fun x hx => by rw [m2, fr1 x hx],
      by rw [m2]; exact K1, ⟨u2.pc, rfl, fun _ => rfl⟩, X1.of fun q _ => u2.regs q, by rw [u2.regs, r221]; try rfl,
      by rw [u2.regs, r81], by rw [m2]; exact M1, by rw [m2]; exact A1, l1⟩
  | succ k ih =>
    intro r25 st m E s R hs0 M A hl hk
    rcases ml2_iter F E s R hs0 M A hl hk with
      ⟨hn, hp⟩ | ⟨st1, h1, n1, c1, E1, fr1, K1, s1, X1, r91, r251, r221, r81, M1, A1, l1⟩
    · exact .inl ⟨by show (mlIter2 T0 T1 D0 D1 (k + 1) st).bind _ = none; rw [hn]; rfl, hp⟩
    obtain ⟨n2, d2, u2⟩ := s1.taken E1.C.self 0x195C sv_at_1a6e (by decide)
      (by
        rw [r251, s1.zero]
        exact br_bne_t fun e => by
          have := congrArg BitVec.toNat e
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          exact Nat.succ_ne_zero k (this.trans rfl))
    have m2 : n2.mem = n1.mem := u2.mem
    have s2 : St n2.mem SV n2 0x195C (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
    have R2 : GR2 B n2 r3 r4 r18 r19 (BitVec.ofNat 32 (k + 1)) r26 k :=
      (X1.of fun q _ => u2.regs q).gr (by rw [u2.regs, r91])
        (by rw [u2.regs, r221, show 0x1023 + (k + 1) = 0x1024 + k by omega]) (by rw [u2.regs, r251])
    rcases ih (st := st1) (by rw [m2]; exact E1) s2 R2 (by rw [u2.regs, r81]) (by rw [m2]; exact M1)
        (by rw [m2]; exact A1) l1 (by omega) with
      ⟨hn, hp⟩ | ⟨st2, h2, n3, c3, E3, fr3, K3, s3, X3, r223, r83, M3, A3, l3⟩
    · exact .inl ⟨by show (mlIter2 T0 T1 D0 D1 (k + 1) st).bind _ = none; rw [h1]; exact hn,
        Panics.of_steps (c1.trans (.cons d2 (.refl _))) hp⟩
    have K1' : SvKeepL B m.mem n2.mem mlW := by rw [m2]; exact K1
    exact .inr ⟨st2, by show (mlIter2 T0 T1 D0 D1 (k + 1) st).bind _ = _; rw [h1]; exact h2, n3,
      c1.trans (.cons d2 c3), E3, fun x hx => by rw [fr3 x hx, m2, fr1 x hx],
      (K1'.trans K3).wider (mlW_dup fun p hp => by simp only [List.mem_append, or_self] at hp; exact hp),
      s3, X3, r223, r83, M3, A3, l3⟩

end C3.RV32.Sv
