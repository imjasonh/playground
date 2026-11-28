import C3BootProofs.Proofs.P2vEcW
import C3BootProofs.Proofs.Pv384G1

/-!
# `p256VerifyPrehash`: one pair's step of the main loop

The wrappers the main loop of `u₁·G + u₂·Q` calls, and the proof of one
pair's step: read the pair's wNAF digit at the current position, and add
the table entry it names, or its negation, to the accumulator at offset
0x980. It follows `Pv384G1.lean`, whose code has the same shape.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Sv

set_option maxRecDepth 100000

theorem P2vKeepL.wider {B : Word} {M M' : Word → BitVec 8} {L L' : List (Nat × Nat)} (K : P2vKeepL B M M' L)
    (h : ∀ p ∈ L, ∃ q ∈ L', q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) : P2vKeepL B M M' L' := fun e he hL =>
  K e he fun p hp => by
    obtain ⟨q, hq, h1, h2⟩ := h p hp
    have := hL q hq; omega

/-- **The panic at 0x10D8**: a failed bounds check on a table index. -/
theorem p2v_panic_10d8 {B : Word} {n : Machine} (F : Fr B 0x3590) (E : P2vCode n.mem)
    (s : St n.mem P2V n 0x10D8 (reg n)) (rsp : reg n sp = B + 0x21A0) : Panics n := by
  have FS : Fr (B + 0x21A0) 0x13F0 := F.sub (c := 0x21A0) (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x10DA) [.aluImm .add a1 x0 0x8] E.self (by decide) ⟨trivial, trivial⟩
  have s1 : St n.mem P2V n1 0x10DA (reg n1) := ⟨u1.pc, u1.mem.trans (by simp only [runBlock, BInstr.run]), fun _ => rfl⟩
  have sp1 : reg n1 sp = B + 0x21A0 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; exact rsp
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := s1.callRa E.self p2v_at_10da p2v_at_10de
    (cb := BitVec.ofNat 32 panicBoundsCheckAddress) (by decide) (by decide)
  exact Panics.of_steps (c1.trans c2) (panicBoundsCheck_panics n2 (by rw [mem2]; exact E.K.panic) pc2
    (by rw [regs2, upd_ne (by decide) (by decide), sp1]; exact FS.room (by decide)))

set_option maxHeartbeats 8000000 in
/-- **A call to the P-256 field's `neg`** of the value at offset `cb`, into
offset `co`. -/
theorem p2v_neg2F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co cb : Nat}
    (F : Fr B 0x3590) (C : P2vCode M) (PC : P2vPtCode M)
    (hn : CodeIn M (BitVec.ofNat 32 p256FieldNegAddress) p256FieldNegCode)
    (hz : CodeIn M (BitVec.ofNat 32 p256ZeroAddress) p256ZeroData) (st : St M P2V n off (reg n))
    (h1 : fetchRel p256VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P2V + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 p256FieldNegAddress)
    (hev : (P2V + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cb)
    (hco : co + 32 ≤ 0x13F0) (hcb : cb + 32 ≤ 0x13F0) (aco : co % 4 = 0) (acb : cb % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem P2V n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 = subGen 0 (accV M (B + 0x21A0 + BitVec.ofNat 32 cb) 8) ∧
      P2vKeepL B M n'.mem [(co, 32)] ∧ (∀ x, P2vR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x13F0 := F.sub (c := 0x21A0) (by decide) (by decide)
  have EN : FSEnv n1.mem (BitVec.ofNat 32 p256FieldNegAddress + 0x12) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 co)
      (BitVec.ofNat 32 p256ZeroAddress) (B + 0x21A0 + BitVec.ofNat 32 cb) := by
    rw [mem1]
    refine ⟨by decide, ?_, ?_, ?_, by rw [hS]; omega, p2v_al F (by omega) aco, by decide, p2v_al F (by omega) acb,
      by rw [hS]; omega, by rw [p2v_at F _ (by omega)]; omega,
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowN (k := 0xB4) (by decide) (by decide) hco,
      FS.sepHi hco (by decide) (by decide),
      by rw [show B + 0x21A0 + (0xFFFFFF4C : Word) = B + BitVec.ofNat 32 0x20EC from p2v_spX B 0xB4 (by decide)]
         exact (F.bufData (by decide) (by decide) (by decide)).symm,
      FS.lowN (k := 0xB4) (by decide) (by decide) hcb⟩
    · exact codeIn_eq PC.sub (by decide)
    · exact codeIn_eq PC.si (by decide)
    · exact codeIn_eq C.K.bsub (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, V2, f2⟩ := p256FieldNeg_correct n1 (by decide) (by rw [mem1]; exact hn) EN
    (by rw [mem1]; exact hz) pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1 sp (by decide), rsp])
  rw [mem1, limbVal_wordsAt, limbVal_wordsAt] at V2
  have e1 : B + 0x21A0 + 0xFFFFFF4C = B + BitVec.ofNat 32 0x20EC := p2v_spX B 0xB4 (by decide)
  rw [mem1, e1] at f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_, V2,
    fun e he hL => ?_, fun x hx => f2 x (p2vR_spX hx (by decide) (by decide) (by decide)) (p2vR_hi hx hco)⟩
  · have hq' := hq
    rw [k2 q (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide)
      (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide)
      (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide)
      (by revert hq'; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [← p2v_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

/-- The code and constants the main loop needs. -/
structure MlEnv (M : Word → BitVec 8) : Prop where
  C : P2vCode M
  PC : P2vPtCode M
  ng : CodeIn M (BitVec.ofNat 32 p256FieldNegAddress) p256FieldNegCode
  z : CodeIn M (BitVec.ofNat 32 p256ZeroAddress) p256ZeroData

theorem MlEnv.fr {B : Word} {M M' : Word → BitVec 8} (E : MlEnv M) (F : Fr B 0x3590)
    (h : ∀ x, P2vR B x → M' x = M x) : MlEnv M' :=
  ⟨E.C.fr F h, E.PC.p2v F h, codeIn_p2v F h E.ng (by decide) (by decide), F.dataIn h E.z (by decide) (by decide)⟩

/-- The tables and the digits, which the main loop reads and does not
change. -/
structure GM2 (B : Word) (M : Word → BitVec 8) (T0 T1 : Nat → Pt2) (D0 D1 : List Nat) : Prop where
  t0 : ∀ j, j < 8 → ptF M B (0x300 + 0x60 * j) = T0 j
  t1 : ∀ j, j < 8 → ptF M B (0x600 + 0x60 * j) = T1 j
  tl : ∀ j, j < 8 → Pt2Lt (T0 j) ∧ Pt2Lt (T1 j)
  d0 : memBytes M (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = D0
  d1 : memBytes M (B + 0x21A0 + BitVec.ofNat 32 0x11F0) 0x101 = D1

/-- What the main loop may write: scratch at 0xC80 and the accumulator at
0x980. -/
abbrev mlW : List (Nat × Nat) := [(0xC80, 0x60), (0x980, 0x60)]

theorem GM2.keep {B : Word} {M M' : Word → BitVec 8} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat}
    (G : GM2 B M T0 T1 D0 D1) (K : P2vKeepL B M M' mlW) : GM2 B M' T0 T1 D0 D1 :=
  ⟨fun j hj => (K.pt (by omega) (fun p hp => .inl (by
      simp only [mlW, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega))).trans (G.t0 j hj),
    fun j hj => (K.pt (by omega) (fun p hp => .inl (by
      simp only [mlW, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega))).trans (G.t1 j hj), G.tl,
    (K.mb (by decide) (by decide)).trans G.d0, (K.mb (by decide) (by decide)).trans G.d1⟩

/-- The registers the main loop keeps at position `k`. -/
structure GR2 (B : Word) (m : Machine) (r3 r4 : Word) (k : Nat) : Prop where
  sp : reg m sp = B + 0x21A0
  g3 : reg m (3 : Fin 32) = r3
  g4 : reg m (4 : Fin 32) = r4
  s0 : reg m (8 : Fin 32) = 2
  s1 : reg m (9 : Fin 32) = BitVec.ofNat 32 (k + 1)
  s3 : reg m (19 : Fin 32) = BitVec.ofNat 32 k
  s4 : reg m (20 : Fin 32) = 0x60
  s6 : reg m (22 : Fin 32) = 0x108
  s7 : reg m (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x10E8 + k)
  s8 : reg m (24 : Fin 32) = 0x101
  s9 : reg m (25 : Fin 32) = 0x300
  s10 : reg m (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x300
  s11 : reg m (27 : Fin 32) = 0x10

theorem GR2.of {B : Word} {m m' : Machine} {r3 r4 : Word} {k : Nat} (R : GR2 B m r3 r4 k)
    (h : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 19, 20, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) :
    GR2 B m' r3 r4 k :=
  ⟨by rw [h RV32.sp (by decide), R.sp], by rw [h _ (by decide), R.g3], by rw [h _ (by decide), R.g4],
    by rw [h _ (by decide), R.s0], by rw [h _ (by decide), R.s1], by rw [h _ (by decide), R.s3],
    by rw [h _ (by decide), R.s4], by rw [h _ (by decide), R.s6],
    by rw [h _ (by decide), R.s7], by rw [h _ (by decide), R.s8], by rw [h _ (by decide), R.s9],
    by rw [h _ (by decide), R.s10], by rw [h _ (by decide), R.s11]⟩

theorem keepL2 {m m' : Machine}
    (h : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) :
    ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 19, 20, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
  fun q hq => h q (by revert hq; revert q; decide)

theorem keepS2 {B : Word} {m m' : Machine} (h1 : reg m' sp = B + 0x21A0) (h0 : reg m sp = B + 0x21A0)
    (h : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) :
    ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 19, 20, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q := fun q hq => by
  by_cases e : q = sp
  · subst e; rw [h1, h0]
  · exact h q (by revert hq e; revert q; decide)

theorem ptF_eq {M : Word → BitVec 8} {B : Word} {c : Nat} {P : Pt2} (h : ptF M B c = P) :
    accV M (B + 0x21A0 + BitVec.ofNat 32 c) 8 = P.1 ∧ accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x20)) 8 = P.2.1 ∧
      accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x40)) 8 = P.2.2 := by
  subst h; exact ⟨rfl, rfl, rfl⟩

theorem sp_lit (S : Word) (a b c : Nat) (h : (BitVec.ofNat 32 a + BitVec.ofNat 32 b : Word) = BitVec.ofNat 32 c) :
    S + BitVec.ofNat 32 a + BitVec.ofNat 32 b = S + BitVec.ofNat 32 c := by
  rw [BitVec.add_assoc, h]

def mlTl : List BInstr := [.aluImm .add (21 : Fin 32) x0 0x1]
theorem mlTl_end : blockEnd p256VerifyPrehashCode 0xAF4 mlTl = some 0xAF6 := by decide
def mlHd : List BInstr := [.alu .mul a0 (18 : Fin 32) (22 : Fin 32), .alu .add a0 a0 (23 : Fin 32)]
theorem mlHd_end : blockEnd p256VerifyPrehashCode 0xA30 mlHd = some 0xA36 := by decide

set_option maxHeartbeats 16000000 in
/-- The end of a pair's step that adds an entry, from 0xAEC: add the point
at offset `cr` to the accumulator, mark the accumulator, and move to the
next pair. -/
theorem ml2_tail {B r3 r4 : Word} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} {k j cr : Nat} {Q acc : Pt2}
    {m : Machine} (F : Fr B 0x3590) (E : MlEnv m.mem) (s : St m.mem P2V m 0xAEC (reg m)) (R : GR2 B m r3 r4 k)
    (h18 : reg m (18 : Fin 32) = BitVec.ofNat 32 (j + 1)) (ha0 : reg m a0 = B + 0x21A0 + BitVec.ofNat 32 0x980)
    (ha1 : reg m a1 = B + 0x21A0 + BitVec.ofNat 32 cr) (hcr : cr + 96 ≤ 0x13F0) (acr : cr % 4 = 0)
    (hQ : ptF m.mem B cr = Q) (hQl : Pt2Lt Q) (A : ptF m.mem B 0x980 = acc) (hl : Pt2Lt acc)
    (M : GM2 B m.mem T0 T1 D0 D1) (hj : j < 2) (hk : k + 1 ≤ 0x101) :
    ∃ m', Steps m m' ∧ MlEnv m'.mem ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧ P2vKeepL B m.mem m'.mem mlW ∧
      St m'.mem P2V m' (if j = 0 then 0xA3A else 0xAF8) (reg m') ∧ GR2 B m' r3 r4 k ∧
      reg m' (21 : Fin 32) = 1 ∧ reg m' (18 : Fin 32) = BitVec.ofNat 32 (j + 1) ∧
      reg m' a0 = B + 0x21A0 + BitVec.ofNat 32 (0x10E8 + k + 0x108 * (j + 1)) ∧
      GM2 B m'.mem T0 T1 D0 D1 ∧ ptF m'.mem B 0x980 = ptAdd2 acc Q := by
  obtain ⟨n1, c1, s1, sp1, rk1, V1, K1, f1⟩ := p2v_pa2F (cl := 0x980) (cr := cr) F E.C E.PC s p2v_at_aec p2v_at_af0
    (by decide) (by decide) R.sp ha0 ha1 (by decide) hcr (by decide) acr A hQ hl hQl
  have E1 : MlEnv n1.mem := E.fr F f1
  have K1' : P2vKeepL B m.mem n1.mem mlW := K1.wider (by decide)
  have R1 : GR2 B n1 r3 r4 k := R.of (keepS2 sp1 R.sp rk1)
  obtain ⟨n2, c2, u2⟩ := s1.block mlTl E1.C.self mlTl_end ⟨trivial, trivial⟩
  have s2 : St n1.mem P2V n2 0xAF6 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have k2 : ∀ q : Fin 32, q ≠ (21 : Fin 32) → reg n2 q = reg n1 q := fun q h =>
    by rw [u2.regs, runBlock_reg _ _ _ q s1.zero (by simp [mlTl, BInstr.dst, h])]
  have r21 : reg n2 (21 : Fin 32) = 1 := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, mlTl, upd, ↓reduceIte, aluEval]; rw [s1.zero]; rfl
  obtain ⟨n3, d3, u3⟩ := s2.jump E1.C.self p2v_at_af6 (off' := 0xA30) (by decide) (by rw [s2.pc]; decide)
  have s3 : St n1.mem P2V n3 0xA30 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  obtain ⟨n4, c4, u4⟩ := s3.block mlHd E1.C.self mlHd_end ⟨trivial, trivial, trivial⟩
  have s4 : St n1.mem P2V n4 0xA36 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
  have k4 : ∀ q : Fin 32, q ≠ a0 → reg n4 q = reg n3 q := fun q h =>
    by rw [u4.regs, runBlock_reg _ _ _ q s3.zero (by simp [mlHd, BInstr.dst, h])]
  have r18 : reg n3 (18 : Fin 32) = BitVec.ofNat 32 (j + 1) := by
    rw [u3.regs, k2 _ (by decide), rk1 _ (by decide), h18]
  have r22 : reg n3 (22 : Fin 32) = 0x108 := by rw [u3.regs, k2 _ (by decide), R1.s6]
  have r23 : reg n3 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x10E8 + k) := by
    rw [u3.regs, k2 _ (by decide), R1.s7]
  have a04 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 (0x10E8 + k + 0x108 * (j + 1)) := by
    rw [u4.regs]; simp +decide only [runBlock, BInstr.run, mlHd, upd, ↓reduceIte, aluEval]
    rw [r18, r22, r23]; exact ofNat_mul_add (B + 0x21A0) (j + 1) (0x10E8 + k) 0x108 (by omega) (by decide) (by omega)
  have R4 : GR2 B n4 r3 r4 k := R1.of fun q hq => by
    rw [k4 q (by revert hq; revert q; decide), u3.regs, k2 q (by revert hq; revert q; decide)]
  have r18' : reg n4 (18 : Fin 32) = BitVec.ofNat 32 (j + 1) := by rw [k4 _ (by decide), r18]
  have r21' : reg n4 (21 : Fin 32) = 1 := by rw [k4 _ (by decide), u3.regs, r21]
  have M1 : GM2 B n1.mem T0 T1 D0 D1 := M.keep K1'
  by_cases hj0 : j = 0
  · subst hj0
    obtain ⟨n5, d5, u5⟩ := s4.notTaken E1.C.self 0xA3A p2v_at_a36 (by decide)
      (by rw [r18', R4.s0]; decide)
    refine ⟨n5, c1.trans (c2.trans (.cons d3 (c4.trans (.single d5)))), by rw [u5.mem]; exact E1,
      fun x hx => by rw [u5.mem, f1 x hx], by rw [u5.mem]; exact K1', ⟨u5.pc, rfl, fun _ => rfl⟩,
      R4.of fun q _ => u5.regs q, by rw [u5.regs, r21'], by rw [u5.regs, r18'], by rw [u5.regs, a04],
      by rw [u5.mem]; exact M1, by rw [u5.mem]; exact V1⟩
  · obtain rfl : j = 1 := by omega
    obtain ⟨n5, d5, u5⟩ := s4.taken E1.C.self 0xAF8 p2v_at_a36 (by decide)
      (by rw [r18', R4.s0]; decide)
    refine ⟨n5, c1.trans (c2.trans (.cons d3 (c4.trans (.single d5)))), by rw [u5.mem]; exact E1,
      fun x hx => by rw [u5.mem, f1 x hx], by rw [u5.mem]; exact K1', ⟨u5.pc, rfl, fun _ => rfl⟩,
      R4.of fun q _ => u5.regs q, by rw [u5.regs, r21'], by rw [u5.regs, r18'], by rw [u5.regs, a04],
      by rw [u5.mem]; exact M1, by rw [u5.mem]; exact V1⟩

def mlZ : List BInstr := [.aluImm .add a0 a0 0x108, .aluImm .add (18 : Fin 32) (18 : Fin 32) 0x1]
theorem mlZ_end : blockEnd p256VerifyPrehashCode 0xA44 mlZ = some 0xA4A := by decide
def mlN : List BInstr := [.alu .mul a1 (18 : Fin 32) (25 : Fin 32), .aluImm .sll a0 a2 0x18,
  .aluImm .sra a0 a0 0x18, .aluImm .add (18 : Fin 32) (18 : Fin 32) 0x1, .alu .add a1 a1 (26 : Fin 32)]
theorem mlN_end : blockEnd p256VerifyPrehashCode 0xA50 mlN = some 0xA5E := by decide
def mlP : List BInstr := [.aluImm .srl a0 a2 0x1]
theorem mlP_end : blockEnd p256VerifyPrehashCode 0xA62 mlP = some 0xA66 := by decide
def mlP2 : List BInstr := [.alu .mul a0 a0 (20 : Fin 32), .alu .add a1 a1 a0, .aluImm .add a0 sp 0x7FF,
  .aluImm .add a0 a0 0x181]
theorem mlP2_end : blockEnd p256VerifyPrehashCode 0xA6A mlP2 = some 0xA78 := by decide
def mlG : List BInstr := [.alu .sub a0 x0 a2, .aluImm .sll a0 a0 0x18, .aluImm .sra a0 a0 0x18,
  .alu .div a0 a0 (8 : Fin 32), .aluImm .and a2 a0 0xFF, .aluImm .sll a0 a0 0x18, .aluImm .sra a0 a0 0x18,
  .aluImm .add a3 x0 0x8]
theorem mlG_end : blockEnd p256VerifyPrehashCode 0xA7A mlG = some 0xA90 := by decide
def mlG2 : List BInstr := [.alu .mul (21 : Fin 32) a0 (20 : Fin 32), .alu .add (21 : Fin 32) (21 : Fin 32) a1,
  .aluImm .add a1 (21 : Fin 32) 0x20, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x4A1]
theorem mlG2_end : blockEnd p256VerifyPrehashCode 0xA94 mlG2 = some 0xAA6 := by decide
def mlG3 : List BInstr := [.aluImm .add a1 (21 : Fin 32) 0x40, .aluImm .add a2 x0 0x20, .aluImm .add a0 sp 0x7FF,
  .aluImm .add a0 a0 0x4C1]
theorem mlG3_end : blockEnd p256VerifyPrehashCode 0xAAE mlG3 = some 0xABE := by decide
def mlG4 : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481, .aluImm .add a2 x0 0x20,
  .alu .add a1 x0 (21 : Fin 32)]
theorem mlG4_end : blockEnd p256VerifyPrehashCode 0xAC6 mlG4 = some 0xAD4 := by decide
def mlG5 : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x181, .aluImm .add a1 sp 0x7FF,
  .aluImm .add a1 a1 0x481]
theorem mlG5_end : blockEnd p256VerifyPrehashCode 0xADC mlG5 = some 0xAEC := by decide

theorem dig_byte2 {B : Word} {M : Word → BitVec 8} {D0 D1 : List Nat} {k j : Nat}
    (h0 : memBytes M (B + 0x21A0 + BitVec.ofNat 32 0x10E8) 0x101 = D0)
    (h1 : memBytes M (B + 0x21A0 + BitVec.ofNat 32 0x11F0) 0x101 = D1) (hj : j < 2) (hk : k + 1 ≤ 0x101) :
    (M (B + 0x21A0 + BitVec.ofNat 32 (0x10E8 + k + 0x108 * j))).toNat = (if j = 0 then D0 else D1).getD k 0 := by
  by_cases hj0 : j = 0
  · subst hj0
    rw [ite_eq_left rfl, ← h0, memBytes_getD (by omega), add_ofNat_assoc, show 0x10E8 + k + 0x108 * 0 = 0x10E8 + k by omega]
  · obtain rfl : j = 1 := by omega
    rw [ite_eq_right (by decide), ← h1, memBytes_getD (by omega), add_ofNat_assoc,
      show 0x10E8 + k + 0x108 * 1 = 0x11F0 + k by omega]

theorem sp_980 (S : Word) : S + 0x7FF + 0x181 = S + BitVec.ofNat 32 0x980 := by rw [BitVec.add_assoc]; rfl
theorem sp_c80 (S : Word) : S + 0x7FF + 0x481 = S + BitVec.ofNat 32 0xC80 := by rw [BitVec.add_assoc]; rfl
theorem sp_ca0 (S : Word) : S + 0x7FF + 0x4A1 = S + BitVec.ofNat 32 0xCA0 := by rw [BitVec.add_assoc]; rfl
theorem sp_cc0 (S : Word) : S + 0x7FF + 0x4C1 = S + BitVec.ofNat 32 0xCC0 := by rw [BitVec.add_assoc]; rfl

set_option maxHeartbeats 64000000 in
/-- **One pair's step**, from 0xA3A: read the digit byte of pair `j` at
position `k` and act on it as `mlPair2` does. -/
theorem ml2_pair {B r3 r4 : Word} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} {k j : Nat} {st : Pt2 × Bool}
    {m : Machine} (F : Fr B 0x3590) (E : MlEnv m.mem) (s : St m.mem P2V m 0xA3A (reg m)) (R : GR2 B m r3 r4 k)
    (hs5 : reg m (21 : Fin 32) = if st.2 then 1 else 0) (h2 : reg m (18 : Fin 32) = BitVec.ofNat 32 j)
    (ha0 : reg m a0 = B + 0x21A0 + BitVec.ofNat 32 (0x10E8 + k + 0x108 * j)) (M : GM2 B m.mem T0 T1 D0 D1)
    (A : ptF m.mem B 0x980 = st.1) (hl : Pt2Lt st.1) (hj : j < 2) (hk : k + 1 ≤ 0x101) :
    (mlPair2 (if j = 0 then T0 else T1) (if j = 0 then D0 else D1) k st = none ∧ Panics m) ∨
    (∃ st', mlPair2 (if j = 0 then T0 else T1) (if j = 0 then D0 else D1) k st = some st' ∧
      ∃ m', Steps m m' ∧ MlEnv m'.mem ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧ P2vKeepL B m.mem m'.mem mlW ∧
        St m'.mem P2V m' (if j = 0 then 0xA3A else 0xAF8) (reg m') ∧ GR2 B m' r3 r4 k ∧
        reg m' (21 : Fin 32) = (if st'.2 then 1 else 0) ∧ reg m' (18 : Fin 32) = BitVec.ofNat 32 (j + 1) ∧
        reg m' a0 = B + 0x21A0 + BitVec.ofNat 32 (0x10E8 + k + 0x108 * (j + 1)) ∧
        GM2 B m'.mem T0 T1 D0 D1 ∧ ptF m'.mem B 0x980 = st'.1 ∧ Pt2Lt st'.1) := by
  have C := E.C.self
  -- the bounds check on the position passes
  obtain ⟨n1, d1, u1⟩ := s.notTaken C 0xA3E p2v_at_a3a (by decide)
    (by rw [R.s8, R.s1]; simp only [branchTaken]; rw [show (0x101 : Word) = BitVec.ofNat 32 0x101 from rfl,
      Pv.ult_ofNat (by decide) (by omega)]; simp only [decide_eq_false_iff_not]; omega)
  have s1 : St m.mem P2V n1 0xA3E (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have e1 : reg n1 = reg m := funext u1.regs
  -- the digit byte
  obtain ⟨b, hb⟩ : ∃ b, m.mem (B + 0x21A0 + BitVec.ofNat 32 (0x10E8 + k + 0x108 * j)) = b := ⟨_, rfl⟩
  have hbv : b.toNat = (if j = 0 then D0 else D1).getD k 0 := by rw [← hb]; exact dig_byte2 M.d0 M.d1 hj hk
  obtain ⟨n2, d2, u2⟩ := s1.lbu C p2v_at_a3e (off' := 0xA42) (by decide)
  have s2 : St m.mem P2V n2 0xA42 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have a22 : reg n2 a2 = b.zeroExtend 32 := by
    rw [u2.regs, upd_same (by decide), e1, ha0, add_lit_zero, hb]
  have k2 : ∀ q : Fin 32, q ≠ a2 → reg n2 q = reg m q := fun q h => by
    rw [u2.regs, updz s1.zero h, e1]
  have R2 : GR2 B n2 r3 r4 k := R.of fun q hq => k2 q (by revert hq; revert q; decide)
  unfold mlPair2
  rw [ite_eq_right (by omega)]
  unfold mlAdd2
  rw [← hbv]
  by_cases hb0 : b.toNat = 0
  · -- a zero digit: skip
    rw [ite_eq_left hb0]
    obtain ⟨n3, d3, u3⟩ := s2.notTaken C 0xA44 p2v_at_a42 (by decide)
      (by rw [a22, s2.zero]; simp only [branchTaken]; rw [zext_ne0]; simp [hb0])
    have s3 : St m.mem P2V n3 0xA44 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
    obtain ⟨n4, c4, u4⟩ := s3.block mlZ C mlZ_end ⟨trivial, trivial, trivial⟩
    have s4 : St m.mem P2V n4 0xA4A (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
    have k4 : ∀ q : Fin 32, q ≠ a0 → q ≠ (18 : Fin 32) → q ≠ a2 → reg n4 q = reg m q := fun q h0 h18 h2' => by
      rw [u4.regs, runBlock_reg _ _ _ q s3.zero (by simp [mlZ, BInstr.dst, h0, h18]), u3.regs, k2 q h2']
    have a04 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 (0x10E8 + k + 0x108 * (j + 1)) := by
      rw [u4.regs]; simp +decide only [runBlock, BInstr.run, mlZ, upd, ↓reduceIte, aluEval]
      rw [u3.regs, k2 _ (by decide), ha0, show (0x108 : Word) = BitVec.ofNat 32 0x108 from rfl, add_ofNat_assoc,
        show 0x10E8 + k + 0x108 * j + 0x108 = 0x10E8 + k + 0x108 * (j + 1) by omega]
    have r18 : reg n4 (18 : Fin 32) = BitVec.ofNat 32 (j + 1) := by
      rw [u4.regs]; simp +decide only [runBlock, BInstr.run, mlZ, upd, ↓reduceIte, aluEval]
      rw [u3.regs, k2 _ (by decide), h2, show (1 : Word) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
    have R4 : GR2 B n4 r3 r4 k := R.of fun q hq => k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)
    have r21 : reg n4 (21 : Fin 32) = if st.2 then 1 else 0 := by rw [k4 _ (by decide) (by decide) (by decide), hs5]
    refine .inr ⟨st, rfl, ?_⟩
    by_cases hj0 : j = 0
    · subst hj0
      obtain ⟨n5, d5, u5⟩ := s4.notTaken C 0xA4E p2v_at_a4a (by decide) (by rw [r18, R4.s0]; decide)
      have s5 : St m.mem P2V n5 0xA4E (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
      obtain ⟨n6, d6, u6⟩ := s5.jump C p2v_at_a4e (off' := 0xA3A) (by decide) (by rw [s5.pc]; decide)
      refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (.single d6))))), by rw [u6.mem]; exact E,
        fun x hx => by rw [u6.mem], fun e _ _ => by rw [u6.mem], ⟨u6.pc, rfl, fun _ => rfl⟩,
        R4.of fun q _ => by rw [u6.regs, u5.regs],
        by rw [u6.regs, u5.regs, r21], by rw [u6.regs, u5.regs, r18], by rw [u6.regs, u5.regs, a04],
        by rw [u6.mem]; exact M, by rw [u6.mem]; exact A, hl⟩
    · obtain rfl : j = 1 := by omega
      obtain ⟨n5, d5, u5⟩ := s4.taken C 0xAF8 p2v_at_a4a (by decide) (by rw [r18, R4.s0]; decide)
      refine ⟨n5, .cons d1 (.cons d2 (.cons d3 (c4.trans (.single d5)))), by rw [u5.mem]; exact E,
        fun x hx => by rw [u5.mem], fun e _ _ => by rw [u5.mem], ⟨u5.pc, rfl, fun _ => rfl⟩,
        R4.of fun q _ => by rw [u5.regs],
        by rw [u5.regs, r21], by rw [u5.regs, r18], by rw [u5.regs, a04], by rw [u5.mem]; exact M,
        by rw [u5.mem]; exact A, hl⟩
  · rw [ite_eq_right hb0]
    obtain ⟨n3, d3, u3⟩ := s2.taken C 0xA50 p2v_at_a42 (by decide)
      (by rw [a22, s2.zero]; simp only [branchTaken]; rw [zext_ne0]; simp [hb0])
    have s3 : St m.mem P2V n3 0xA50 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
    have e3 : reg n3 = reg n2 := funext u3.regs
    obtain ⟨n4, c4, u4⟩ := s3.block mlN C mlN_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    have s4 : St m.mem P2V n4 0xA5E (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
    have k4 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ (18 : Fin 32) → reg n4 q = reg n2 q := fun q h0 h1 h18 => by
      rw [u4.regs, runBlock_reg _ _ _ q s3.zero (by simp [mlN, BInstr.dst, h0, h1, h18]), e3]
    have a14 : reg n4 a1 = B + 0x21A0 + BitVec.ofNat 32 (0x300 + 0x300 * j) := by
      rw [u4.regs]; simp +decide only [runBlock, BInstr.run, mlN, upd, ↓reduceIte]
      rw [e3, k2 _ (by decide), k2 _ (by decide), k2 _ (by decide), h2, R.s9, R.s10]
      exact ofNat_mul_add (B + 0x21A0) j 0x300 0x300 (by omega) (by decide) (by omega)
    have a04 : reg n4 a0 = sx8 (b.zeroExtend 32) := by
      rw [u4.regs]; simp +decide only [runBlock, BInstr.run, mlN, upd, ↓reduceIte]; rw [e3, a22]
    have r18 : reg n4 (18 : Fin 32) = BitVec.ofNat 32 (j + 1) := by
      rw [u4.regs]; simp +decide only [runBlock, BInstr.run, mlN, upd, ↓reduceIte, aluEval]
      rw [e3, k2 _ (by decide), h2, show (1 : Word) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
    have a24 : reg n4 a2 = b.zeroExtend 32 := by rw [k4 _ (by decide) (by decide) (by decide), a22]
    have R4 : GR2 B n4 r3 r4 k := R2.of fun q hq => k4 q (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    have hT : ∀ i, i < 8 → ptF m.mem B (0x300 + 0x300 * j + 0x60 * i) = (if j = 0 then T0 else T1) i ∧
        Pt2Lt ((if j = 0 then T0 else T1) i) := fun i hi => by
      by_cases hj0 : j = 0
      · subst hj0; rw [ite_eq_left rfl, show 0x300 + 0x300 * 0 + 0x60 * i = 0x300 + 0x60 * i by omega]
        exact ⟨M.t0 i hi, (M.tl i hi).1⟩
      · obtain rfl : j = 1 := by omega
        rw [ite_eq_right (by decide), show 0x300 + 0x300 * 1 + 0x60 * i = 0x600 + 0x60 * i by omega]
        exact ⟨M.t1 i hi, (M.tl i hi).2⟩
    by_cases hneg : 128 ≤ b.toNat
    · rw [ite_eq_right (by omega)]
      obtain ⟨n5, d5, u5⟩ := s4.taken C 0xA7A p2v_at_a5e (by decide)
        (by rw [s4.zero, a04, dig_bge]; simp [hneg])
      have s5 : St m.mem P2V n5 0xA7A (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
      have e5 : reg n5 = reg n4 := funext u5.regs
      obtain ⟨n6, c6, u6⟩ := s5.block mlG C mlG_end
        ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
      have s6 : St m.mem P2V n6 0xA90 (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
      have k6 : ∀ q : Fin 32, q ≠ a0 → q ≠ a2 → q ≠ a3 → reg n6 q = reg n4 q := fun q h0 h2' h3 => by
        rw [u6.regs, runBlock_reg _ _ _ q s5.zero (by simp [mlG, BInstr.dst, h0, h2', h3]), e5]
      have a26 : reg n6 a2 = aluEval .and (negIdx b) 0xFF := by
        rw [u6.regs]; simp +decide only [runBlock, BInstr.run, mlG, upd, ↓reduceIte]
        rw [e5, s4.zero, a24, R4.s0]; rfl
      have a06 : reg n6 a0 = sx8 (negIdx b) := by
        rw [u6.regs]; simp +decide only [runBlock, BInstr.run, mlG, upd, ↓reduceIte]
        rw [e5, s4.zero, a24, R4.s0]; rfl
      have a36 : reg n6 a3 = 8 := by
        rw [u6.regs]; simp +decide only [runBlock, BInstr.run, mlG, upd, ↓reduceIte]
      obtain ⟨dn1, dn2⟩ := dig_neg b hneg
      by_cases hbad : b.toNat = 128 ∨ 8 ≤ (256 - b.toNat) / 2
      · rw [ite_eq_left hbad]
        obtain ⟨n7, d7, u7⟩ := s6.taken C 0x10D8 p2v_at_a90 (by decide)
          (by rw [a26, a36, dn1]; simp [hbad])
        refine .inl ⟨rfl, Panics.of_steps (.cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (c6.trans (.single d7)))))))
          (p2v_panic_10d8 F (by rw [u7.mem]; exact E.C) ⟨u7.pc, rfl, fun _ => rfl⟩ ?_)⟩
        rw [u7.regs, k6 _ (by decide) (by decide) (by decide), R4.sp]
      · rw [ite_eq_right hbad]
        have hix : (256 - b.toNat) / 2 < 8 := by omega
        obtain ⟨n7, d7, u7⟩ := s6.notTaken C 0xA94 p2v_at_a90 (by decide)
          (by rw [a26, a36, dn1]; simp [hbad])
        have s7 : St m.mem P2V n7 0xA94 (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
        have e7 : reg n7 = reg n6 := funext u7.regs
        have a07 : reg n7 a0 = BitVec.ofNat 32 ((256 - b.toNat) / 2) := by rw [e7, a06]; exact dn2 hbad
        -- the entry, and the scratch copy of its negation
        obtain ⟨ix, hix'⟩ : ∃ ix, (256 - b.toNat) / 2 = ix := ⟨_, rfl⟩
        rw [hix'] at a07 hix
        rw [hix']
        obtain ⟨hQ, hQl⟩ := hT ix hix
        obtain ⟨q1, q2, q3⟩ := ptF_eq hQ
        obtain ⟨n8, c8, u8⟩ := s7.block mlG2 C mlG2_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
        have s8 : St m.mem P2V n8 0xAA6 (reg n8) := ⟨u8.pc, u8.mem, fun _ => rfl⟩
        have k8 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ (21 : Fin 32) → q ≠ a2 → q ≠ a3 → reg n8 q = reg n4 q :=
          fun q h0 h1 h21 h2' h3 => by
            rw [u8.regs, runBlock_reg _ _ _ q s7.zero (by simp [mlG2, BInstr.dst, h0, h1, h21]), e7, k6 q h0 h2' h3]
        have a06' : reg n6 a0 = BitVec.ofNat 32 ix := by rw [← a07, e7]
        have r21 : reg n8 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x300 + 0x300 * j + 0x60 * ix) := by
          rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlG2, upd, ↓reduceIte]
          rw [e7, a06', k6 _ (by decide) (by decide) (by decide), k6 _ (by decide) (by decide) (by decide), a14, R4.s4]
          simp only [aluEval]
          exact ofNat_mul_add (B + 0x21A0) ix (0x300 + 0x300 * j) 0x60 (by omega) (by decide) (by omega)
        have a18 : reg n8 a1 = B + 0x21A0 + BitVec.ofNat 32 (0x300 + 0x300 * j + 0x60 * ix + 0x20) := by
          rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlG2, upd, ↓reduceIte]
          rw [e7, a06', k6 _ (by decide) (by decide) (by decide), k6 _ (by decide) (by decide) (by decide), a14, R4.s4]
          simp only [aluEval]
          rw [show (0x60 : Word) = BitVec.ofNat 32 0x60 from rfl,
            ofNat_mul_add (B + 0x21A0) ix (0x300 + 0x300 * j) 0x60 (by omega) (by decide) (by omega),
            show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, add_ofNat_assoc]
        have a08 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0xCA0 := by
          rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlG2, upd, ↓reduceIte]
          rw [e7, k6 _ (by decide) (by decide) (by decide), R4.sp]; simp only [aluEval]; exact sp_ca0 _
        have R8 : GR2 B n8 r3 r4 k := R4.of fun q hq => k8 q (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide)
        have s8' : St n8.mem P2V n8 0xAA6 (reg n8) := ⟨s8.pc, rfl, fun _ => rfl⟩
        obtain ⟨n9, c9, s9, sp9, rk9, V9, K9, f9⟩ := p2v_neg2F (co := 0xCA0)
          (cb := 0x300 + 0x300 * j + 0x60 * ix + 0x20) F (by rw [s8.mem]; exact E.C) (by rw [s8.mem]; exact E.PC)
          (by rw [s8.mem]; exact E.ng) (by rw [s8.mem]; exact E.z) s8' p2v_at_aa6 p2v_at_aaa (by decide) (by decide)
          R8.sp a08 a18 (by decide) (by omega) (by decide) (by omega)
        rw [s8.mem, q2] at V9
        have E9 : MlEnv n9.mem := E.fr F (by rw [← s8.mem]; exact f9)
        obtain ⟨n10, c10, u10⟩ := s9.block mlG3 E9.C.self mlG3_end ⟨trivial, trivial, trivial, trivial, trivial⟩
        have s10 : St n9.mem P2V n10 0xABE (reg n10) := ⟨u10.pc, u10.mem, fun _ => rfl⟩
        have R9 : GR2 B n9 r3 r4 k := R8.of (keepS2 sp9 R8.sp rk9)
        have k10 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n10 q = reg n9 q := fun q h0 h1 h2' => by
          rw [u10.regs, runBlock_reg _ _ _ q s9.zero (by simp [mlG3, BInstr.dst, h0, h1, h2'])]
        have r21' : reg n9 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x300 + 0x300 * j + 0x60 * ix) := by
          rw [rk9 _ (by decide), r21]
        have E10 : P2vCode n10.mem := by rw [s10.mem]; exact E9.C
        have s10' : St n10.mem P2V n10 0xABE (reg n10) := ⟨s10.pc, rfl, fun _ => rfl⟩
        obtain ⟨n11, P11, K11, V11⟩ := p2v_mc F E10 s10' p2v_at_abe p2v_at_ac2 (by decide) (by decide)
          (by rw [k10 _ (by decide) (by decide) (by decide), R9.sp])
          (by rw [u10.regs]; simp +decide only [runBlock, BInstr.run, mlG3, upd, ↓reduceIte]
              rw [R9.sp]; simp only [aluEval]; exact sp_cc0 _)
          (by rw [u10.regs]; simp +decide only [runBlock, BInstr.run, mlG3, upd, ↓reduceIte]
              rw [r21']; simp only [aluEval]
              rw [show (0x40 : Word) = BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc])
          (by rw [u10.regs]; simp +decide only [runBlock, BInstr.run, mlG3, upd, ↓reduceIte, aluEval]; try rfl)
          (c := 0xCC0) (d := 0x300 + 0x300 * j + 0x60 * ix + 0x40) (N := 0x20)
          (by decide) (by omega) (by omega)
        have E11 : MlEnv n11.mem := E9.fr F (by rw [← s10.mem]; exact P11.fr)
        have R11 : GR2 B n11 r3 r4 k := R9.of fun q hq => by
          rw [P11.regs q (by revert hq; revert q; decide), k10 q (by revert hq; revert q; decide)
            (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
        have r21'' : reg n11 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x300 + 0x300 * j + 0x60 * ix) := by
          rw [P11.regs _ (by decide), k10 _ (by decide) (by decide) (by decide), r21']
        obtain ⟨n12, c12, u12⟩ := P11.st.block mlG4 E11.C.self mlG4_end ⟨trivial, trivial, trivial, trivial, trivial⟩
        have s12 : St n11.mem P2V n12 0xAD4 (reg n12) := ⟨u12.pc, u12.mem, fun _ => rfl⟩
        have k12 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n12 q = reg n11 q := fun q h0 h1 h2' => by
          rw [u12.regs, runBlock_reg _ _ _ q P11.st.zero (by simp [mlG4, BInstr.dst, h0, h1, h2'])]
        have E12 : P2vCode n12.mem := by rw [s12.mem]; exact E11.C
        have s12' : St n12.mem P2V n12 0xAD4 (reg n12) := ⟨s12.pc, rfl, fun _ => rfl⟩
        obtain ⟨n13, P13, K13, V13⟩ := p2v_mc F E12 s12' p2v_at_ad4 p2v_at_ad8 (by decide) (by decide)
          (by rw [k12 _ (by decide) (by decide) (by decide), R11.sp])
          (by rw [u12.regs]; simp +decide only [runBlock, BInstr.run, mlG4, upd, ↓reduceIte]
              rw [R11.sp]; simp only [aluEval]; exact sp_c80 _)
          (by rw [u12.regs]; simp +decide only [runBlock, BInstr.run, mlG4, upd, ↓reduceIte]
              rw [r21'']; simp only [aluEval]; exact BitVec.zero_add _)
          (by rw [u12.regs]; simp +decide only [runBlock, BInstr.run, mlG4, upd, ↓reduceIte, aluEval]; try rfl)
          (c := 0xC80) (d := 0x300 + 0x300 * j + 0x60 * ix) (N := 0x20)
          (by decide) (by omega) (by omega)
        have E13 : MlEnv n13.mem := E11.fr F (by rw [← s12.mem]; exact P13.fr)
        have R13 : GR2 B n13 r3 r4 k := R11.of fun q hq => by
          rw [P13.regs q (by revert hq; revert q; decide), k12 q (by revert hq; revert q; decide)
            (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
        obtain ⟨n14, c14, u14⟩ := P13.st.block mlG5 E13.C.self mlG5_end ⟨trivial, trivial, trivial, trivial, trivial⟩
        have s14 : St n14.mem P2V n14 0xAEC (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
        have k14 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg n14 q = reg n13 q := fun q h0 h1 => by
          rw [u14.regs, runBlock_reg _ _ _ q P13.st.zero (by simp [mlG5, BInstr.dst, h0, h1])]
        have m14 : n14.mem = n13.mem := u14.mem
        have E14 : MlEnv n14.mem := by rw [m14]; exact E13
        -- the negated entry at 0xC80
        have mm : n10.mem = n9.mem := s10.mem
        have m12 : n12.mem = n11.mem := s12.mem
        have hx : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) 8 = ((if j = 0 then T0 else T1) ix).1 := by
          rw [m14, ← q1, accV_S 8 fun q hq => V13 q (by omega), m12, K11.acc (by omega) (by omega), mm,
            K9.acc (by omega) (by simp; omega), s8.mem]
        have hy : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + 0x20)) 8 =
            subGen 0 ((if j = 0 then T0 else T1) ix).2.1 := by
          rw [m14, ← V9, K13.acc (by omega) (by omega), m12, K11.acc (by omega) (by omega), mm]
        have hz : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC80 + 0x40)) 8 = ((if j = 0 then T0 else T1) ix).2.2 := by
          rw [m14, ← q3, K13.acc (by omega) (by omega), m12, accV_S 8 fun q hq => V11 q (by omega), mm,
            K9.acc (by omega) (by simp; omega), s8.mem]
        have hQ' : ptF n14.mem B 0xC80 = negPt2 ((if j = 0 then T0 else T1) ix) := by
          unfold ptF negPt2; rw [hx, hy, hz]
        have K11' : P2vKeepL B n9.mem n11.mem [(0xCC0, 0x20)] := by rw [← mm]; exact P2vKeepL.of K11
        have K13' : P2vKeepL B n11.mem n13.mem [(0xC80, 0x20)] := by rw [← m12]; exact P2vKeepL.of K13
        have KK0 : P2vKeepL B m.mem n14.mem [(0xCA0, 32), (0xCC0, 0x20), (0xC80, 0x20)] := by
          have := (K9.trans K11').trans K13'
          rw [s8.mem] at this; rw [m14]; exact this
        have KK : P2vKeepL B m.mem n14.mem mlW := KK0.wider (by decide)
        have A' : ptF n14.mem B 0x980 = st.1 := by rw [KK0.pt (by decide) (by decide), A]
        have M' : GM2 B n14.mem T0 T1 D0 D1 := M.keep KK
        have r18'' : reg n14 (18 : Fin 32) = BitVec.ofNat 32 (j + 1) := by
          rw [k14 _ (by decide) (by decide), P13.regs _ (by decide), k12 _ (by decide) (by decide) (by decide),
            P11.regs _ (by decide), k10 _ (by decide) (by decide) (by decide), rk9 _ (by decide),
            k8 _ (by decide) (by decide) (by decide) (by decide) (by decide), r18]
        obtain ⟨n15, c15, E15, fr15, K15, s15, R15, r21f, r18f, a0f, M15, V15⟩ :=
          ml2_tail (j := j) (k := k) F E14 s14 (R13.of fun q hq => k14 q (by revert hq; revert q; decide)
            (by revert hq; revert q; decide)) r18''
            (by rw [u14.regs]; simp +decide only [runBlock, BInstr.run, mlG5, upd, ↓reduceIte]
                rw [R13.sp]; simp only [aluEval]; exact sp_980 _)
            (by rw [u14.regs]; simp +decide only [runBlock, BInstr.run, mlG5, upd, ↓reduceIte]
                rw [R13.sp]; simp only [aluEval]; exact sp_c80 _)
            (by decide) (by decide) hQ' (negPt2_lt hQl) A' hl M' hj hk
        refine .inr ⟨_, rfl, n15, .cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (c6.trans (.cons d7 (c8.trans
          (c9.trans (c10.trans (P11.steps.trans (c12.trans (P13.steps.trans (c14.trans c15))))))))))))), E15,
          fun x hx => by rw [fr15 x hx, m14, P13.fr x hx, m12, P11.fr x hx, mm, f9 x hx, s8.mem],
          (KK.trans K15).wider (by decide), s15, R15, by rw [r21f]; rfl, r18f, a0f, M15, V15, ptAdd2_lt _ _⟩
    · rw [ite_eq_left (by omega)]
      obtain ⟨n5, d5, u5⟩ := s4.notTaken C 0xA62 p2v_at_a5e (by decide)
        (by rw [s4.zero, a04, dig_bge]; simp [hneg, hb0])
      have s5 : St m.mem P2V n5 0xA62 (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
      have e5 : reg n5 = reg n4 := funext u5.regs
      obtain ⟨n6, c6, u6⟩ := s5.block mlP C mlP_end ⟨trivial, trivial⟩
      have s6 : St m.mem P2V n6 0xA66 (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
      have k6 : ∀ q : Fin 32, q ≠ a0 → reg n6 q = reg n4 q := fun q h0 => by
        rw [u6.regs, runBlock_reg _ _ _ q s5.zero (by simp [mlP, BInstr.dst, h0]), e5]
      have a06 : reg n6 a0 = BitVec.ofNat 32 (b.toNat / 2) := by
        rw [u6.regs]; simp +decide only [runBlock, BInstr.run, mlP, upd, ↓reduceIte]; rw [e5, a24]
        exact (dig_pos b).1
      by_cases h16 : 16 ≤ b.toNat
      · rw [ite_eq_left h16]
        obtain ⟨n7, d7, u7⟩ := s6.taken C 0x10D8 p2v_at_a66 (by decide)
          (by rw [k6 _ (by decide), k6 _ (by decide), a24, R4.s11, (dig_pos b).2]; simp [h16])
        refine .inl ⟨rfl, Panics.of_steps (.cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (c6.trans (.single d7)))))))
          (p2v_panic_10d8 F (by rw [u7.mem]; exact E.C) ⟨u7.pc, rfl, fun _ => rfl⟩ ?_)⟩
        rw [u7.regs, k6 _ (by decide), R4.sp]
      · rw [ite_eq_right h16]
        obtain ⟨n7, d7, u7⟩ := s6.notTaken C 0xA6A p2v_at_a66 (by decide)
          (by rw [k6 _ (by decide), k6 _ (by decide), a24, R4.s11, (dig_pos b).2]; simp [h16])
        have s7 : St m.mem P2V n7 0xA6A (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
        have e7 : reg n7 = reg n6 := funext u7.regs
        obtain ⟨n8, c8, u8⟩ := s7.block mlP2 C mlP2_end ⟨trivial, trivial, trivial, trivial, trivial⟩
        have s8 : St m.mem P2V n8 0xA78 (reg n8) := ⟨u8.pc, u8.mem, fun _ => rfl⟩
        have k8 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg n8 q = reg n4 q := fun q h0 h1 => by
          rw [u8.regs, runBlock_reg _ _ _ q s7.zero (by simp [mlP2, BInstr.dst, h0, h1]), e7, k6 q h0]
        have a18 : reg n8 a1 = B + 0x21A0 + BitVec.ofNat 32 (0x300 + 0x300 * j + 0x60 * (b.toNat / 2)) := by
          rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlP2, upd, ↓reduceIte]
          rw [e7, a06, k6 _ (by decide), k6 _ (by decide), a14, R4.s4]; simp only [aluEval]
          exact ofNat_add_mul (B + 0x21A0) (0x300 + 0x300 * j) (b.toNat / 2) 0x60 (by omega) (by decide) (by omega)
        have a08 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
          rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlP2, upd, ↓reduceIte]
          rw [e7, k6 _ (by decide), R4.sp]; simp only [aluEval]; exact sp_980 _
        obtain ⟨n9, d9, u9⟩ := s8.jump C p2v_at_a78 (off' := 0xAEC) (by decide) (by rw [s8.pc]; decide)
        have s9 : St n9.mem P2V n9 0xAEC (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
        have e9 : reg n9 = reg n8 := funext u9.regs
        obtain ⟨hQ, hQl⟩ := hT (b.toNat / 2) (by omega)
        have E9 : MlEnv n9.mem := by rw [u9.mem]; exact E
        obtain ⟨n10, c10, E10, fr10, K10, s10, R10, r21, r18', a010, M10, V10⟩ :=
          ml2_tail (j := j) (k := k) F E9 s9 (R4.of fun q hq => by
            rw [e9, k8 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)])
            (by rw [e9, k8 _ (by decide) (by decide), r18]) (by rw [e9, a08]) (by rw [e9, a18]) (by omega)
            (by omega) (by rw [u9.mem]; exact hQ) hQl (by rw [u9.mem]; exact A) hl
            (by rw [u9.mem]; exact M) hj hk
        refine .inr ⟨_, rfl, n10, .cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (c6.trans (.cons d7 (c8.trans
          (.cons d9 c10)))))))), E10, fun x hx => by rw [fr10 x hx, u9.mem], by rw [u9.mem] at K10; exact K10,
          s10, R10, by rw [r21]; rfl, r18', a010, M10, V10, ptAdd2_lt _ _⟩

end C3.RV32.P2v
