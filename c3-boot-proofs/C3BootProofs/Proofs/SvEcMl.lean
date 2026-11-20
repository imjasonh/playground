import C3BootProofs.Proofs.SvEcW
import C3BootProofs.Proofs.P256Neg
import C3BootProofs.Proofs.Pv384G1

/-!
# `sigstore::verify`: the P-256 check's main loop

The model of the main loop of the linear combination `u₁·G + u₂·Q`, the
wrappers its steps call, and the proof of one pair's step: read the pair's
wNAF digit at the current position, and add the table entry it names, or its
negation, to the accumulator at offset 0x1480. It follows `Pv384G1.lean`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

/-- A table entry with its `y` coordinate negated, as the field's `neg` does. -/
def negPt2 (P : Pt2) : Pt2 := (P.1, subGen 0 P.2.1, P.2.2)

theorem negPt2_lt {P : Pt2} (h : Pt2Lt P) : Pt2Lt (negPt2 P) := by
  refine ⟨h.1, ?_, h.2.2⟩
  show subGen 0 P.2.1 < p256
  rw [subGen_field (by decide) h.2.1]; exact Nat.mod_lt _ (by decide)

/-- What the loop does with the digit byte `b` of a pair whose table is `T`:
`some none` to skip it, `some (some acc')` to add an entry, and `none` when a
bounds check fails. -/
def mlAdd2 (T : Nat → Pt2) (acc : Pt2) (b : Nat) : Option (Option Pt2) :=
  if b = 0 then some none
  else if b < 128 then (if 16 ≤ b then none else some (some (ptAdd2 acc (T (b / 2)))))
  else if b = 128 ∨ 8 ≤ (256 - b) / 2 then none
  else some (some (ptAdd2 acc (negPt2 (T ((256 - b) / 2)))))

/-- The step for one pair at position `k`: the accumulator and whether it
has had an entry added. -/
def mlPair2 (T : Nat → Pt2) (D : List Nat) (k : Nat) (st : Pt2 × Bool) : Option (Pt2 × Bool) :=
  if 0x101 < k + 1 then some st
  else match mlAdd2 T st.1 (D.getD k 0) with
    | none => none
    | some none => some st
    | some (some a) => some (a, true)

/-- One position of the main loop: double the accumulator once it has an
entry, then step the two pairs. -/
def mlIter2 (T0 T1 : Nat → Pt2) (D0 D1 : List Nat) (k : Nat) (st : Pt2 × Bool) : Option (Pt2 × Bool) :=
  (mlPair2 T0 D0 k (if st.2 then ptDbl2 st.1 else st.1, st.2)).bind (mlPair2 T1 D1 k)

/-- The main loop from position `k - 1` down to 0. -/
def mlLoop2 (T0 T1 : Nat → Pt2) (D0 D1 : List Nat) : Nat → Pt2 × Bool → Option (Pt2 × Bool)
  | 0, st => some st
  | k + 1, st => (mlIter2 T0 T1 D0 D1 k st).bind (mlLoop2 T0 T1 D0 D1 k)

/-- **The panic at 0x1E52**: a failed bounds check on a table index. -/
theorem sv_panic_1e52 {B : Word} {n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem)
    (s : St n.mem SV n 0x1E52 (reg n)) (rsp : reg n sp = B + 0x21A0) : Panics n := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x1E54) [.aluImm .add a1 x0 0x8] E.self (by decide) ⟨trivial, trivial⟩
  have s1 : St n.mem SV n1 0x1E54 (reg n1) := ⟨u1.pc, u1.mem.trans (by simp only [runBlock, BInstr.run]), fun _ => rfl⟩
  have sp1 : reg n1 sp = B + 0x21A0 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; exact rsp
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := s1.callRa E.self sv_at_1e54 sv_at_1e58
    (cb := BitVec.ofNat 32 panicBoundsCheckAddress) (by decide) (by decide)
  exact Panics.of_steps (c1.trans c2) (panicBoundsCheck_panics n2 (by rw [mem2]; exact E.K.panic) pc2
    (by rw [regs2, upd_ne (by decide) (by decide), sp1]; exact FS.room (by decide)))

set_option maxHeartbeats 8000000 in
/-- **A call to the P-256 field's `neg`** of the value at offset `cb`, into
offset `co`. -/
theorem sv_neg2F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co cb : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (PC : SvPtCode M)
    (hn : CodeIn M (BitVec.ofNat 32 p256FieldNegAddress) p256FieldNegCode)
    (hz : CodeIn M (BitVec.ofNat 32 p256ZeroAddress) p256ZeroData) (st : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 p256FieldNegAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cb)
    (hco : co + 32 ≤ 0x1690) (hcb : cb + 32 ≤ 0x1690) (aco : co % 4 = 0) (acb : cb % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 = subGen 0 (accV M (B + 0x21A0 + BitVec.ofNat 32 cb) 8) ∧
      SvKeepL B M n'.mem [(co, 32)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have EN : FSEnv n1.mem (BitVec.ofNat 32 p256FieldNegAddress + 0x12) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 co)
      (BitVec.ofNat 32 p256ZeroAddress) (B + 0x21A0 + BitVec.ofNat 32 cb) := by
    rw [mem1]
    refine ⟨by decide, ?_, ?_, ?_, by rw [hS]; omega, sv_al F (by omega) aco, by decide, sv_al F (by omega) acb,
      by rw [hS]; omega, by rw [sv_at F _ (by omega)]; omega,
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowN (k := 0xB4) (by decide) (by decide) hco,
      FS.sepHi hco (by decide) (by decide),
      by rw [show B + 0x21A0 + (0xFFFFFF4C : Word) = B + BitVec.ofNat 32 0x20EC from sv_spX B 0xB4 (by decide)]
         exact (F.bufData (by decide) (by decide) (by decide)).symm,
      FS.lowN (k := 0xB4) (by decide) (by decide) hcb⟩
    · rw [show BitVec.ofNat 32 p256FieldNegAddress + 0x12 = BitVec.ofNat 32 fieldSubAddress by decide]; exact PC.sub
    · rw [show BitVec.ofNat 32 p256FieldNegAddress + 0x12 + 0xFFFFFB24 = BitVec.ofNat 32 subInnerAddress by decide]
      exact PC.si
    · rw [show siBsub (BitVec.ofNat 32 p256FieldNegAddress + 0x12 + 0xFFFFFB24) = BSUB by decide]; exact C.K.bsub
  obtain ⟨n2, c2, pc2, sp2, k2, V2, f2⟩ := p256FieldNeg_correct n1 (by decide) (by rw [mem1]; exact hn) EN
    (by rw [mem1]; exact hz) pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1 sp (by decide), rsp])
  rw [mem1, limbVal_wordsAt, limbVal_wordsAt] at V2
  have e1 : B + 0x21A0 + 0xFFFFFF4C = B + BitVec.ofNat 32 0x20EC := sv_spX B 0xB4 (by decide)
  rw [mem1, e1] at f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_, V2,
    fun e he hL => ?_, fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx hco)⟩
  · have hq' := hq
    rw [k2 q (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide)
      (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide)
      (by revert hq'; revert q; decide) (by revert hq'; revert q; decide) (by revert hq'; revert q; decide)
      (by revert hq'; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

/-- The code and constants the main loop needs. -/
structure MlEnv (M : Word → BitVec 8) : Prop where
  C : SvCode M
  PC : SvPtCode M
  ng : CodeIn M (BitVec.ofNat 32 p256FieldNegAddress) p256FieldNegCode
  z : CodeIn M (BitVec.ofNat 32 p256ZeroAddress) p256ZeroData

theorem MlEnv.fr {B : Word} {M M' : Word → BitVec 8} (E : MlEnv M) (F : Fr B 0x3830)
    (h : ∀ x, SvR B x → M' x = M x) : MlEnv M' :=
  ⟨E.C.fr F h, E.PC.sv F h, codeIn_sv F h E.ng (by decide) (by decide), F.dataIn h E.z (by decide) (by decide)⟩

/-- The tables and the digits, which the main loop reads and does not
change. -/
structure GM2 (B : Word) (M : Word → BitVec 8) (T0 T1 : Nat → Pt2) (D0 D1 : List Nat) : Prop where
  t0 : ∀ j, j < 8 → ptF M B (0x420 + 0x60 * j) = T0 j
  t1 : ∀ j, j < 8 → ptF M B (0x720 + 0x60 * j) = T1 j
  tl : ∀ j, j < 8 → Pt2Lt (T0 j) ∧ Pt2Lt (T1 j)
  d0 : memBytes M (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = D0
  d1 : memBytes M (B + 0x21A0 + BitVec.ofNat 32 0x112C) 0x101 = D1

/-- What the main loop may write: scratch at 0xA20 and the accumulator at
0x1480. -/
abbrev mlW : List (Nat × Nat) := [(0xA20, 0x60), (0x1480, 0x60)]

theorem GM2.keep {B : Word} {M M' : Word → BitVec 8} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat}
    (G : GM2 B M T0 T1 D0 D1) (K : SvKeepL B M M' mlW) : GM2 B M' T0 T1 D0 D1 :=
  ⟨fun j hj => (K.pt (by omega) (fun p hp => .inl (by
      simp only [mlW, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega))).trans (G.t0 j hj),
    fun j hj => (K.pt (by omega) (fun p hp => .inl (by
      simp only [mlW, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega))).trans (G.t1 j hj), G.tl,
    (K.mb (by decide) (by decide)).trans G.d0, (K.mb (by decide) (by decide)).trans G.d1⟩

/-- The registers the main loop keeps at position `k`. -/
structure GR2 (B : Word) (m : Machine) (r3 r4 r18 r19 r26 : Word) (k : Nat) : Prop where
  sp : reg m sp = B + 0x21A0
  g3 : reg m (3 : Fin 32) = r3
  g4 : reg m (4 : Fin 32) = r4
  s1 : reg m (9 : Fin 32) = BitVec.ofNat 32 (k + 1)
  s2 : reg m (18 : Fin 32) = r18
  s3 : reg m (19 : Fin 32) = r19
  s4 : reg m (20 : Fin 32) = 0x60
  s5 : reg m (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40
  s6 : reg m (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x1024 + k)
  s8 : reg m (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60
  s10 : reg m (26 : Fin 32) = r26
  s11 : reg m (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20

theorem GR2.of {B r3 r4 r18 r19 r26 : Word} {m m' : Machine} {k : Nat} (R : GR2 B m r3 r4 r18 r19 r26 k)
    (h : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 18, 19, 20, 21, 22, 24, 26, 27] → reg m' q = reg m q) :
    GR2 B m' r3 r4 r18 r19 r26 k :=
  ⟨by rw [h RV32.sp (by decide), R.sp], by rw [h _ (by decide), R.g3], by rw [h _ (by decide), R.g4],
    by rw [h _ (by decide), R.s1], by rw [h _ (by decide), R.s2], by rw [h _ (by decide), R.s3],
    by rw [h _ (by decide), R.s4], by rw [h _ (by decide), R.s5], by rw [h _ (by decide), R.s6],
    by rw [h _ (by decide), R.s8], by rw [h _ (by decide), R.s10], by rw [h _ (by decide), R.s11]⟩

theorem keepL2 {m m' : Machine}
    (h : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) :
    ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 18, 19, 20, 21, 22, 24, 26, 27] → reg m' q = reg m q :=
  fun q hq => h q (by revert hq; revert q; decide)

theorem ptF_eq {M : Word → BitVec 8} {B : Word} {c : Nat} {P : Pt2} (h : ptF M B c = P) :
    accV M (B + 0x21A0 + BitVec.ofNat 32 c) 8 = P.1 ∧ accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x20)) 8 = P.2.1 ∧
      accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x40)) 8 = P.2.2 := by
  subst h; exact ⟨rfl, rfl, rfl⟩

def mlTl : List BInstr := [.aluImm .add (8 : Fin 32) x0 0x1]
theorem mlTl_end : blockEnd sigstoreVerifyCode 0x1A66 mlTl = some 0x1A68 := by decide
def mlHd : List BInstr := [.aluImm .add a0 x0 0x108, .alu .mul a0 (23 : Fin 32) a0, .alu .add a0 a0 (22 : Fin 32)]
theorem mlHd_end : blockEnd sigstoreVerifyCode 0x199C mlHd = some 0x19A6 := by decide

set_option maxHeartbeats 16000000 in
/-- The end of a pair's step that adds an entry, from 0x1A5E: add the point
at offset `cr` to the accumulator, mark it, and move to the next pair. -/
theorem ml2_tail {B r3 r4 r18 r19 r26 : Word} {k j cr : Nat} {Q acc : Pt2}
    {m : Machine} (F : Fr B 0x3830) (E : MlEnv m.mem) (s : St m.mem SV m 0x1A5E (reg m))
    (R : GR2 B m r3 r4 r18 r19 r26 k)
    (h23 : reg m (23 : Fin 32) = BitVec.ofNat 32 (j + 1)) (ha0 : reg m a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480)
    (ha1 : reg m a1 = B + 0x21A0 + BitVec.ofNat 32 cr) (hcr : cr + 96 ≤ 0x1690) (acr : cr % 4 = 0)
    (hQ : ptF m.mem B cr = Q) (hQl : Pt2Lt Q) (A : ptF m.mem B 0x1480 = acc) (hl : Pt2Lt acc)
    (hj : j < 2) (hk : k + 1 ≤ 0x101) :
    ∃ m', Steps m m' ∧ MlEnv m'.mem ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ SvKeepL B m.mem m'.mem mlW ∧
      St m'.mem SV m' 0x19A6 (reg m') ∧ GR2 B m' r3 r4 r18 r19 r26 k ∧
      reg m' (8 : Fin 32) = 1 ∧ reg m' (23 : Fin 32) = BitVec.ofNat 32 (j + 1) ∧
      reg m' a0 = B + 0x21A0 + BitVec.ofNat 32 (0x1024 + k + 0x108 * (j + 1)) ∧
      ptF m'.mem B 0x1480 = ptAdd2 acc Q := by
  obtain ⟨n1, c1, s1, sp1, rk1, V1, K1, f1⟩ := sv_pa2F (cl := 0x1480) (cr := cr) F E.C E.PC s sv_at_1a5e sv_at_1a62
    (by decide) (by decide) R.sp ha0 ha1 (by decide) hcr (by decide) acr A hQ hl hQl
  have E1 : MlEnv n1.mem := E.fr F f1
  obtain ⟨n2, c2, u2⟩ := s1.block mlTl E1.C.self mlTl_end ⟨trivial, trivial⟩
  have s2 : St n1.mem SV n2 0x1A68 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have k2 : ∀ q : Fin 32, q ≠ (8 : Fin 32) → reg n2 q = reg n1 q := fun q h =>
    by rw [u2.regs, runBlock_reg _ _ _ q s1.zero (by simp [mlTl, BInstr.dst, h])]
  have r8 : reg n2 (8 : Fin 32) = 1 := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, mlTl, upd, ↓reduceIte, aluEval]; rw [s1.zero]; rfl
  obtain ⟨n3, d3, u3⟩ := s2.jump E1.C.self sv_at_1a68 (off' := 0x199C) (by decide) (by rw [s2.pc]; decide)
  have s3 : St n1.mem SV n3 0x199C (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  obtain ⟨n4, c4, u4⟩ := s3.block mlHd E1.C.self mlHd_end ⟨trivial, trivial, trivial, trivial⟩
  have s4 : St n1.mem SV n4 0x19A6 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
  have k4 : ∀ q : Fin 32, q ≠ a0 → reg n4 q = reg n3 q := fun q h =>
    by rw [u4.regs, runBlock_reg _ _ _ q s3.zero (by simp [mlHd, BInstr.dst, h])]
  have R1 : GR2 B n1 r3 r4 r18 r19 r26 k := R.of fun q hq => by
    by_cases h : q = sp
    · subst h; rw [sp1, R.sp]
    · exact rk1 q (by revert hq h; revert q; decide)
  have r23 : reg n3 (23 : Fin 32) = BitVec.ofNat 32 (j + 1) := by
    rw [u3.regs, k2 _ (by decide), rk1 _ (by decide), h23]
  have r22 : reg n3 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x1024 + k) := by
    rw [u3.regs, k2 _ (by decide), R1.s6]
  have a04 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 (0x1024 + k + 0x108 * (j + 1)) := by
    rw [u4.regs]; simp +decide only [runBlock, BInstr.run, mlHd, upd, ↓reduceIte, aluEval]
    rw [r23, r22, s3.zero, show (0 : Word) + 0x108 = BitVec.ofNat 32 0x108 from rfl]
    exact ofNat_mul_add (B + 0x21A0) (j + 1) (0x1024 + k) 0x108 (by omega) (by decide) (by omega)
  have R4 : GR2 B n4 r3 r4 r18 r19 r26 k := R1.of fun q hq => by
    rw [k4 q (by revert hq; revert q; decide), u3.regs, k2 q (by revert hq; revert q; decide)]
  have m4 : n4.mem = n1.mem := by rw [u4.mem]; simp only [runBlock, BInstr.run, mlHd]
  refine ⟨n4, c1.trans (c2.trans (.cons d3 c4)), by rw [m4]; exact E1,
    fun x hx => by rw [m4, f1 x hx], ?_, ⟨u4.pc, rfl, fun _ => rfl⟩, R4,
    by rw [k4 _ (by decide), u3.regs, r8], by rw [k4 _ (by decide), r23], a04, by rw [m4]; exact V1⟩
  rw [m4]; exact K1.wider (by simp)

def mlA : List BInstr := [.aluImm .add a1 x0 0x2]
theorem mlA_end : blockEnd sigstoreVerifyCode 0x19A6 mlA = some 0x19A8 := by decide
def mlB : List BInstr := [.aluImm .add a1 x0 0x101]
theorem mlB_end : blockEnd sigstoreVerifyCode 0x19AC mlB = some 0x19B0 := by decide
def mlZ : List BInstr := [.aluImm .add a0 a0 0x108, .aluImm .add (23 : Fin 32) (23 : Fin 32) 0x1]
theorem mlZ_end : blockEnd sigstoreVerifyCode 0x19BA mlZ = some 0x19C0 := by decide
def mlN : List BInstr := [.aluImm .add a0 x0 0x300, .alu .mul a1 (23 : Fin 32) a0, .aluImm .sll a0 a2 0x18,
  .aluImm .sra a0 a0 0x18, .aluImm .add (23 : Fin 32) (23 : Fin 32) 0x1, .aluImm .add a3 sp 0x420, .alu .add a1 a1 a3]
theorem mlN_end : blockEnd sigstoreVerifyCode 0x19C2 mlN = some 0x19D8 := by decide
def mlP : List BInstr := [.aluImm .srl a0 a2 0x1, .aluImm .add a3 x0 0x10]
theorem mlP_end : blockEnd sigstoreVerifyCode 0x19DC mlP = some 0x19E2 := by decide
def mlP2 : List BInstr := [.alu .mul a0 a0 (20 : Fin 32), .alu .add a1 a1 a0, .lui a0 0x1000, .aluImm .add a0 a0 0x480,
  .alu .add a0 a0 sp]
theorem mlP2_end : blockEnd sigstoreVerifyCode 0x19E6 mlP2 = some 0x19F4 := by decide
def mlG : List BInstr := [.alu .sub a0 x0 a2, .aluImm .sll a0 a0 0x18, .aluImm .sra a0 a0 0x18, .aluImm .add a2 x0 0x2,
  .alu .div a0 a0 a2, .aluImm .and a2 a0 0xFF, .aluImm .sll a0 a0 0x18, .aluImm .sra a0 a0 0x18, .aluImm .add a3 x0 0x8]
theorem mlG_end : blockEnd sigstoreVerifyCode 0x19F6 mlG = some 0x1A0E := by decide
def mlG2 : List BInstr := [.alu .mul (8 : Fin 32) a0 (20 : Fin 32), .alu .add (8 : Fin 32) (8 : Fin 32) a1,
  .aluImm .add a1 (8 : Fin 32) 0x20, .alu .add a0 x0 (21 : Fin 32)]
theorem mlG2_end : blockEnd sigstoreVerifyCode 0x1A12 mlG2 = some 0x1A1E := by decide
def mlG3 : List BInstr := [.aluImm .add a1 (8 : Fin 32) 0x40, .aluImm .add a2 x0 0x20, .alu .add a0 x0 (24 : Fin 32)]
theorem mlG3_end : blockEnd sigstoreVerifyCode 0x1A26 mlG3 = some 0x1A30 := by decide
def mlG4 : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .aluImm .add a2 x0 0x20,
  .alu .add a1 x0 (8 : Fin 32)]
theorem mlG4_end : blockEnd sigstoreVerifyCode 0x1A38 mlG4 = some 0x1A46 := by decide
def mlG5 : List BInstr := [.lui a0 0x1000, .aluImm .add a0 a0 0x480, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF,
  .aluImm .add a1 a1 0x221]
theorem mlG5_end : blockEnd sigstoreVerifyCode 0x1A4E mlG5 = some 0x1A5E := by decide

theorem dig_byte2 {B : Word} {M : Word → BitVec 8} {D0 D1 : List Nat} {k j : Nat}
    (h0 : memBytes M (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = D0)
    (h1 : memBytes M (B + 0x21A0 + BitVec.ofNat 32 0x112C) 0x101 = D1) (hj : j < 2) (hk : k + 1 ≤ 0x101) :
    (M (B + 0x21A0 + BitVec.ofNat 32 (0x1024 + k + 0x108 * j))).toNat = (if j = 0 then D0 else D1).getD k 0 := by
  by_cases hj0 : j = 0
  · subst hj0
    rw [ite_eq_left rfl, ← h0, memBytes_getD (by omega), add_ofNat_assoc, show 0x1024 + k + 0x108 * 0 = 0x1024 + k by omega]
  · obtain rfl : j = 1 := by omega
    rw [ite_eq_right (by decide), ← h1, memBytes_getD (by omega), add_ofNat_assoc,
      show 0x1024 + k + 0x108 * 1 = 0x112C + k by omega]

theorem sp_a20 (S : Word) : S + 0x7FF + 0x221 = S + BitVec.ofNat 32 0xA20 := by
  rw [BitVec.add_assoc]; rfl

theorem sp_1480 (S : Word) : (0x1000 : Word) + 0x480 + S = S + BitVec.ofNat 32 0x1480 := by
  rw [BitVec.add_comm]; rfl

set_option maxHeartbeats 64000000 in
/-- **One pair's step**, from 0x19A6: read the digit byte of pair `j` at
position `k` and act on it as `mlPair2` does. -/
theorem ml2_pair {B r3 r4 r18 r19 r26 : Word} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} {k j : Nat} {st : Pt2 × Bool}
    {m : Machine} (F : Fr B 0x3830) (E : MlEnv m.mem) (s : St m.mem SV m 0x19A6 (reg m))
    (R : GR2 B m r3 r4 r18 r19 r26 k) (hs0 : reg m (8 : Fin 32) = if st.2 then 1 else 0)
    (h23 : reg m (23 : Fin 32) = BitVec.ofNat 32 j)
    (ha0 : reg m a0 = B + 0x21A0 + BitVec.ofNat 32 (0x1024 + k + 0x108 * j)) (M : GM2 B m.mem T0 T1 D0 D1)
    (A : ptF m.mem B 0x1480 = st.1) (hl : Pt2Lt st.1) (hj : j < 2) (hk : k + 1 ≤ 0x101) :
    (mlPair2 (if j = 0 then T0 else T1) (if j = 0 then D0 else D1) k st = none ∧ Panics m) ∨
    (∃ st', mlPair2 (if j = 0 then T0 else T1) (if j = 0 then D0 else D1) k st = some st' ∧
      ∃ m', Steps m m' ∧ MlEnv m'.mem ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ SvKeepL B m.mem m'.mem mlW ∧
        St m'.mem SV m' 0x19A6 (reg m') ∧ GR2 B m' r3 r4 r18 r19 r26 k ∧
        reg m' (8 : Fin 32) = (if st'.2 then 1 else 0) ∧ reg m' (23 : Fin 32) = BitVec.ofNat 32 (j + 1) ∧
        reg m' a0 = B + 0x21A0 + BitVec.ofNat 32 (0x1024 + k + 0x108 * (j + 1)) ∧
        GM2 B m'.mem T0 T1 D0 D1 ∧ ptF m'.mem B 0x1480 = st'.1 ∧ Pt2Lt st'.1) := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have C := E.C.self
  have hz := s.zero
  -- `j` isn't 2
  obtain ⟨n0, c0, u0⟩ := s.block mlA C mlA_end ⟨trivial, trivial⟩
  have s0 : St m.mem SV n0 0x19A8 (reg n0) := ⟨u0.pc, u0.mem, fun _ => rfl⟩
  have k0 : ∀ q : Fin 32, q ≠ a1 → reg n0 q = reg m q := fun q h =>
    by rw [u0.regs, runBlock_reg _ _ _ q hz (by simp [mlA, BInstr.dst, h])]
  have a10 : reg n0 a1 = 2 := by
    rw [u0.regs]; simp +decide only [runBlock, BInstr.run, mlA, upd, ↓reduceIte, aluEval]; rw [hz]; rfl
  obtain ⟨n1, d1, u1⟩ := s0.notTaken C 0x19AC sv_at_19a8 (by decide)
    (by rw [k0 _ (by decide), h23, a10]; exact br_beq_f fun e => by
          have := congrArg BitVec.toNat e
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show (2 : Word).toNat = 2 from rfl] at this
          omega)
  obtain ⟨n1', c1', u1'⟩ := u1.self.block mlB C mlB_end ⟨trivial, trivial⟩
  have s1 : St m.mem SV n1' 0x19B0 (reg n1') := ⟨u1'.pc, u1'.mem, fun _ => rfl⟩
  have e1 : ∀ q : Fin 32, q ≠ a1 → reg n1' q = reg m q := fun q h => by
    rw [u1'.regs, runBlock_reg _ _ _ q u1.self.zero (by simp [mlB, BInstr.dst, h]), u1.regs, k0 q h]
  have a11 : reg n1' a1 = 0x101 := by
    rw [u1'.regs]; simp +decide only [runBlock, BInstr.run, mlB, upd, ↓reduceIte, aluEval]; rw [u1.regs, k0 _ (by decide), hz]; rfl
  -- the bounds check on the position passes
  obtain ⟨n2, d2, u2⟩ := s1.notTaken C 0x19B4 sv_at_19b0 (by decide)
    (by rw [a11, e1 _ (by decide), R.s1]; simp only [branchTaken]; rw [show (0x101 : Word) = BitVec.ofNat 32 0x101 from rfl,
      Pv.ult_ofNat (by decide) (by omega)]; simp only [decide_eq_false_iff_not]; omega)
  have s2 : St m.mem SV n2 0x19B4 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have e2 : ∀ q : Fin 32, q ≠ a1 → reg n2 q = reg m q := fun q h => by rw [u2.regs, e1 q h]
  -- the digit byte
  obtain ⟨b, hb⟩ : ∃ b, m.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1024 + k + 0x108 * j)) = b := ⟨_, rfl⟩
  have hbv : b.toNat = (if j = 0 then D0 else D1).getD k 0 := by rw [← hb]; exact dig_byte2 M.d0 M.d1 hj hk
  obtain ⟨n3, d3, u3⟩ := s2.lbu C sv_at_19b4 (off' := 0x19B8) (by decide)
  have s3 : St m.mem SV n3 0x19B8 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  have a23 : reg n3 a2 = b.zeroExtend 32 := by
    rw [u3.regs, upd_same (by decide), e2 _ (by decide), ha0, add_lit_zero, hb]
  have k3 : ∀ q : Fin 32, q ≠ a1 → q ≠ a2 → reg n3 q = reg m q := fun q h1 h2 => by
    rw [u3.regs, updz s2.zero h2, e2 q h1]
  have R3 : GR2 B n3 r3 r4 r18 r19 r26 k := R.of fun q hq => k3 q (by revert hq; revert q; decide)
    (by revert hq; revert q; decide)
  unfold mlPair2
  rw [ite_eq_right (by omega)]
  unfold mlAdd2
  rw [← hbv]
  by_cases hb0 : b.toNat = 0
  · -- a zero digit: skip
    rw [ite_eq_left hb0]
    obtain ⟨n4, d4, u4⟩ := s3.notTaken C 0x19BA sv_at_19b8 (by decide)
      (by rw [a23, s3.zero]; simp only [branchTaken]; rw [zext_ne0]; simp [hb0])
    obtain ⟨n5, c5, u5⟩ := u4.self.block mlZ C mlZ_end ⟨trivial, trivial, trivial⟩
    have s5 : St m.mem SV n5 0x19C0 (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
    have k5 : ∀ q : Fin 32, q ≠ a0 → q ≠ (23 : Fin 32) → q ≠ a1 → q ≠ a2 → reg n5 q = reg m q := fun q h0 h23' h1 h2 => by
      rw [u5.regs, runBlock_reg _ _ _ q u4.self.zero (by simp [mlZ, BInstr.dst, h0, h23']), u4.regs, k3 q h1 h2]
    have a05 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 (0x1024 + k + 0x108 * (j + 1)) := by
      rw [u5.regs]; simp +decide only [runBlock, BInstr.run, mlZ, upd, ↓reduceIte, aluEval]
      rw [u4.regs, k3 _ (by decide) (by decide), ha0, show (0x108 : Word) = BitVec.ofNat 32 0x108 from rfl,
        add_ofNat_assoc, show 0x1024 + k + 0x108 * j + 0x108 = 0x1024 + k + 0x108 * (j + 1) by omega]
    have r23 : reg n5 (23 : Fin 32) = BitVec.ofNat 32 (j + 1) := by
      rw [u5.regs]; simp +decide only [runBlock, BInstr.run, mlZ, upd, ↓reduceIte, aluEval]
      rw [u4.regs, k3 _ (by decide) (by decide), h23, show (1 : Word) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
    have R5 : GR2 B n5 r3 r4 r18 r19 r26 k := R.of fun q hq => k5 q (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    obtain ⟨n6, d6, u6⟩ := s5.jump C sv_at_19c0 (off' := 0x19A6) (by decide) (by rw [s5.pc]; decide)
    refine .inr ⟨st, rfl, n6, c0.trans (.cons d1 (c1'.trans (.cons d2 (.cons d3 (.cons d4 (c5.trans (.single d6))))))),
      by rw [u6.mem]; exact E, fun x _ => by rw [u6.mem], fun e _ _ => by rw [u6.mem],
      ⟨u6.pc, rfl, fun _ => rfl⟩, R5.of fun q _ => u6.regs q,
      by rw [u6.regs, k5 _ (by decide) (by decide) (by decide) (by decide), hs0], by rw [u6.regs, r23],
      by rw [u6.regs, a05], by rw [u6.mem]; exact M, by rw [u6.mem]; exact A, hl⟩
  · rw [ite_eq_right hb0]
    obtain ⟨n4, d4, u4⟩ := s3.taken C 0x19C2 sv_at_19b8 (by decide)
      (by rw [a23, s3.zero]; simp only [branchTaken]; rw [zext_ne0]; simp [hb0])
    have s4 : St m.mem SV n4 0x19C2 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
    have e4 : reg n4 = reg n3 := funext u4.regs
    obtain ⟨n5, c5, u5⟩ := s4.block mlN C mlN_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    have s5 : St m.mem SV n5 0x19D8 (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
    have k5 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ (23 : Fin 32) → q ≠ a3 → reg n5 q = reg n3 q := fun q h0 h1 h23' h3 => by
      rw [u5.regs, runBlock_reg _ _ _ q s4.zero (by simp [mlN, BInstr.dst, h0, h1, h23', h3]), e4]
    have a15 : reg n5 a1 = B + 0x21A0 + BitVec.ofNat 32 (0x420 + 0x300 * j) := by
      rw [u5.regs]; simp +decide only [runBlock, BInstr.run, mlN, upd, ↓reduceIte]
      simp only [e4, k3 (23 : Fin 32) (by decide) (by decide), k3 sp (by decide) (by decide),
        k3 0 (by decide) (by decide), h23, R.sp, hz, aluEval]
      rw [show (0 : Word) + 0x300 = BitVec.ofNat 32 0x300 from rfl,
        show B + 0x21A0 + (0x420 : Word) = B + 0x21A0 + BitVec.ofNat 32 0x420 from rfl]
      exact ofNat_mul_add (B + 0x21A0) j 0x420 0x300 (by omega) (by decide) (by omega)
    have a05 : reg n5 a0 = sx8 (b.zeroExtend 32) := by
      rw [u5.regs]; simp +decide only [runBlock, BInstr.run, mlN, upd, ↓reduceIte]; rw [e4, a23]
    have r23 : reg n5 (23 : Fin 32) = BitVec.ofNat 32 (j + 1) := by
      rw [u5.regs]; simp +decide only [runBlock, BInstr.run, mlN, upd, ↓reduceIte, aluEval]
      rw [e4, k3 _ (by decide) (by decide), h23, show (1 : Word) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
    have a25 : reg n5 a2 = b.zeroExtend 32 := by rw [k5 _ (by decide) (by decide) (by decide) (by decide), a23]
    have R5 : GR2 B n5 r3 r4 r18 r19 r26 k := R3.of fun q hq => k5 q (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    have hT : ∀ i, i < 8 → ptF m.mem B (0x420 + 0x300 * j + 0x60 * i) = (if j = 0 then T0 else T1) i ∧
        Pt2Lt ((if j = 0 then T0 else T1) i) := fun i hi => by
      by_cases hj0 : j = 0
      · subst hj0; rw [ite_eq_left rfl, show 0x420 + 0x300 * 0 + 0x60 * i = 0x420 + 0x60 * i by omega]
        exact ⟨M.t0 i hi, (M.tl i hi).1⟩
      · obtain rfl : j = 1 := by omega
        rw [ite_eq_right (by decide), show 0x420 + 0x300 * 1 + 0x60 * i = 0x720 + 0x60 * i by omega]
        exact ⟨M.t1 i hi, (M.tl i hi).2⟩
    by_cases hneg : 128 ≤ b.toNat
    · rw [ite_eq_right (by omega)]
      obtain ⟨n6, d6, u6⟩ := s5.taken C 0x19F6 sv_at_19d8 (by decide)
        (by rw [s5.zero, a05, dig_bge]; simp [hneg])
      have s6 : St m.mem SV n6 0x19F6 (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
      have e6 : reg n6 = reg n5 := funext u6.regs
      obtain ⟨n7, c7, u7⟩ := s6.block mlG C mlG_end
        ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
      have s7 : St m.mem SV n7 0x1A0E (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
      have k7 : ∀ q : Fin 32, q ≠ a0 → q ≠ a2 → q ≠ a3 → reg n7 q = reg n5 q := fun q h0 h2' h3 => by
        rw [u7.regs, runBlock_reg _ _ _ q s6.zero (by simp [mlG, BInstr.dst, h0, h2', h3]), e6]
      have a27 : reg n7 a2 = aluEval .and (negIdx b) 0xFF := by
        rw [u7.regs]; simp +decide only [runBlock, BInstr.run, mlG, upd, ↓reduceIte]
        rw [e6, s5.zero, a25]; rfl
      have a07 : reg n7 a0 = sx8 (negIdx b) := by
        rw [u7.regs]; simp +decide only [runBlock, BInstr.run, mlG, upd, ↓reduceIte]
        rw [e6, s5.zero, a25]; rfl
      have a37 : reg n7 a3 = 8 := by
        rw [u7.regs]; simp +decide only [runBlock, BInstr.run, mlG, upd, ↓reduceIte]
      obtain ⟨dn1, dn2⟩ := dig_neg b hneg
      by_cases hbad : b.toNat = 128 ∨ 8 ≤ (256 - b.toNat) / 2
      · rw [ite_eq_left hbad]
        obtain ⟨n8, d8, u8⟩ := s7.taken C 0x1E52 sv_at_1a0e (by decide)
          (by rw [a27, a37, dn1]; simp [hbad])
        refine .inl ⟨rfl, Panics.of_steps (c0.trans (.cons d1 (c1'.trans (.cons d2 (.cons d3 (.cons d4 (c5.trans
          (.cons d6 (c7.trans (.single d8)))))))))) (sv_panic_1e52 F (by rw [u8.mem]; exact E.C) ⟨u8.pc, rfl, fun _ => rfl⟩ ?_)⟩
        rw [u8.regs, k7 _ (by decide) (by decide) (by decide), R5.sp]
      · rw [ite_eq_right hbad]
        have hix : (256 - b.toNat) / 2 < 8 := by omega
        obtain ⟨n8, d8, u8⟩ := s7.notTaken C 0x1A12 sv_at_1a0e (by decide)
          (by rw [a27, a37, dn1]; simp [hbad])
        have s8 : St m.mem SV n8 0x1A12 (reg n8) := ⟨u8.pc, u8.mem, fun _ => rfl⟩
        have e8 : reg n8 = reg n7 := funext u8.regs
        obtain ⟨ix, hix'⟩ : ∃ ix, (256 - b.toNat) / 2 = ix := ⟨_, rfl⟩
        have a07' : reg n7 a0 = BitVec.ofNat 32 ix := by rw [a07, ← hix']; exact dn2 hbad
        have a08 : reg n8 a0 = BitVec.ofNat 32 ix := by rw [e8, a07']
        rw [hix'] at hix
        rw [hix']
        obtain ⟨hQ, hQl⟩ := hT ix hix
        obtain ⟨q1, q2, q3⟩ := ptF_eq hQ
        obtain ⟨n9, c9, u9⟩ := s8.block mlG2 C mlG2_end ⟨trivial, trivial, trivial, trivial, trivial⟩
        have s9 : St m.mem SV n9 0x1A1E (reg n9) := ⟨u9.pc, u9.mem, fun _ => rfl⟩
        have k9 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ (8 : Fin 32) → q ≠ a2 → q ≠ a3 → reg n9 q = reg n5 q :=
          fun q h0 h1 h8 h2' h3 => by
            rw [u9.regs, runBlock_reg _ _ _ q s8.zero (by simp [mlG2, BInstr.dst, h0, h1, h8]), e8, k7 q h0 h2' h3]
        have r8 : reg n9 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x420 + 0x300 * j + 0x60 * ix) := by
          rw [u9.regs]; simp +decide only [runBlock, BInstr.run, mlG2, upd, ↓reduceIte]
          simp only [e8, a07', k7 (20 : Fin 32) (by decide) (by decide) (by decide), k7 a1 (by decide) (by decide) (by decide),
            a15, R5.s4, aluEval]
          exact ofNat_mul_add (B + 0x21A0) ix (0x420 + 0x300 * j) 0x60 (by omega) (by decide) (by omega)
        have a19 : reg n9 a1 = B + 0x21A0 + BitVec.ofNat 32 (0x420 + 0x300 * j + 0x60 * ix + 0x20) := by
          rw [u9.regs]; simp +decide only [runBlock, BInstr.run, mlG2, upd, ↓reduceIte]
          simp only [e8, a07', k7 (20 : Fin 32) (by decide) (by decide) (by decide), k7 a1 (by decide) (by decide) (by decide),
            a15, R5.s4, aluEval]
          rw [show (0x60 : Word) = BitVec.ofNat 32 0x60 from rfl,
            ofNat_mul_add (B + 0x21A0) ix (0x420 + 0x300 * j) 0x60 (by omega) (by decide) (by omega),
            show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, add_ofNat_assoc]
        have a09 : reg n9 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
          rw [u9.regs]; simp +decide only [runBlock, BInstr.run, mlG2, upd, ↓reduceIte]
          simp only [e8, k7 (21 : Fin 32) (by decide) (by decide) (by decide), R5.s5, aluEval]; exact BitVec.zero_add _
        have R9 : GR2 B n9 r3 r4 r18 r19 r26 k := R5.of fun q hq => k9 q (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide)
        have s9' : St n9.mem SV n9 0x1A1E (reg n9) := ⟨s9.pc, rfl, fun _ => rfl⟩
        obtain ⟨n10, c10, s10, sp10, rk10, V10, K10, f10⟩ := sv_neg2F (co := 0xA40)
          (cb := 0x420 + 0x300 * j + 0x60 * ix + 0x20) F (by rw [s9.mem]; exact E.C) (by rw [s9.mem]; exact E.PC)
          (by rw [s9.mem]; exact E.ng) (by rw [s9.mem]; exact E.z) s9' sv_at_1a1e sv_at_1a22 (by decide) (by decide) R9.sp
          a09 a19 (by decide) (by omega) (by decide) (by omega)
        rw [s9.mem, q2] at V10
        have E10 : MlEnv n10.mem := (E.fr F (by rw [← s9.mem]; exact f10))
        obtain ⟨n11, c11, u11⟩ := s10.block mlG3 E10.C.self mlG3_end ⟨trivial, trivial, trivial, trivial⟩
        have s11 : St n10.mem SV n11 0x1A30 (reg n11) := ⟨u11.pc, u11.mem, fun _ => rfl⟩
        have R10 : GR2 B n10 r3 r4 r18 r19 r26 k := R9.of fun q hq => by
          by_cases h : q = sp
          · subst h; rw [sp10, R9.sp]
          · exact rk10 q (by revert hq h; revert q; decide)
        have k11 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n11 q = reg n10 q := fun q h0 h1 h2' => by
          rw [u11.regs, runBlock_reg _ _ _ q s10.zero (by simp [mlG3, BInstr.dst, h0, h1, h2'])]
        have r8' : reg n10 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x420 + 0x300 * j + 0x60 * ix) := by
          rw [rk10 _ (by decide), r8]
        have E11 : SvCode n11.mem := by rw [s11.mem]; exact E10.C
        have s11' : St n11.mem SV n11 0x1A30 (reg n11) := ⟨s11.pc, rfl, fun _ => rfl⟩
        obtain ⟨n12, P12, K12, V12⟩ := sv_mc F E11 s11' sv_at_1a30 sv_at_1a34 (by decide) (by decide)
          (by rw [k11 _ (by decide) (by decide) (by decide), R10.sp])
          (by rw [u11.regs]; simp +decide only [runBlock, BInstr.run, mlG3, upd, ↓reduceIte]
              simp only [R10.s8, aluEval]; exact BitVec.zero_add _)
          (by rw [u11.regs]; simp +decide only [runBlock, BInstr.run, mlG3, upd, ↓reduceIte]
              rw [r8']; simp only [aluEval]
              rw [show (0x40 : Word) = BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc])
          (by rw [u11.regs]; simp +decide only [runBlock, BInstr.run, mlG3, upd, ↓reduceIte, aluEval]; try rfl)
          (c := 0xA60) (d := 0x420 + 0x300 * j + 0x60 * ix + 0x40) (N := 0x20)
          (by decide) (by omega) (by omega)
        have E12 : MlEnv n12.mem := E10.fr F (by rw [← s11.mem]; exact P12.fr)
        have R12 : GR2 B n12 r3 r4 r18 r19 r26 k := R10.of fun q hq => by
          rw [P12.regs q (by revert hq; revert q; decide), k11 q (by revert hq; revert q; decide)
            (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
        have r8'' : reg n12 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x420 + 0x300 * j + 0x60 * ix) := by
          rw [P12.regs _ (by decide), k11 _ (by decide) (by decide) (by decide), r8']
        obtain ⟨n13, c13, u13⟩ := P12.st.block mlG4 E12.C.self mlG4_end ⟨trivial, trivial, trivial, trivial, trivial⟩
        have s13 : St n12.mem SV n13 0x1A46 (reg n13) := ⟨u13.pc, u13.mem, fun _ => rfl⟩
        have k13 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n13 q = reg n12 q := fun q h0 h1 h2' => by
          rw [u13.regs, runBlock_reg _ _ _ q P12.st.zero (by simp [mlG4, BInstr.dst, h0, h1, h2'])]
        have E13 : SvCode n13.mem := by rw [s13.mem]; exact E12.C
        have s13' : St n13.mem SV n13 0x1A46 (reg n13) := ⟨s13.pc, rfl, fun _ => rfl⟩
        obtain ⟨n14, P14, K14, V14⟩ := sv_mc F E13 s13' sv_at_1a46 sv_at_1a4a (by decide) (by decide)
          (by rw [k13 _ (by decide) (by decide) (by decide), R12.sp])
          (by rw [u13.regs]; simp +decide only [runBlock, BInstr.run, mlG4, upd, ↓reduceIte]
              rw [R12.sp]; simp only [aluEval]; exact sp_a20 _)
          (by rw [u13.regs]; simp +decide only [runBlock, BInstr.run, mlG4, upd, ↓reduceIte]
              simp only [r8'', aluEval]; exact BitVec.zero_add _)
          (by rw [u13.regs]; simp +decide only [runBlock, BInstr.run, mlG4, upd, ↓reduceIte, aluEval]; try rfl)
          (c := 0xA20) (d := 0x420 + 0x300 * j + 0x60 * ix) (N := 0x20)
          (by decide) (by omega) (by omega)
        have E14 : MlEnv n14.mem := E12.fr F (by rw [← s13.mem]; exact P14.fr)
        have R14 : GR2 B n14 r3 r4 r18 r19 r26 k := R12.of fun q hq => by
          rw [P14.regs q (by revert hq; revert q; decide), k13 q (by revert hq; revert q; decide)
            (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
        obtain ⟨n15, c15, u15⟩ := P14.st.block mlG5 E14.C.self mlG5_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
        have s15 : St n15.mem SV n15 0x1A5E (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
        have k15 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg n15 q = reg n14 q := fun q h0 h1 => by
          rw [u15.regs, runBlock_reg _ _ _ q P14.st.zero (by simp [mlG5, BInstr.dst, h0, h1])]
        have m15 : n15.mem = n14.mem := by rw [u15.mem]; simp only [runBlock, BInstr.run, mlG5]
        have E15 : MlEnv n15.mem := by rw [m15]; exact E14
        have m11 : n11.mem = n10.mem := s11.mem
        have m13 : n13.mem = n12.mem := s13.mem
        -- the negated entry at 0xA20
        have hx : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = ((if j = 0 then T0 else T1) ix).1 := by
          rw [m15, ← q1, accV_S 8 fun q hq => V14 q (by omega), m13, K12.acc (by omega) (by omega), m11,
            K10.acc (by omega) (by simp; omega), s9.mem]
        have hy : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA20 + 0x20)) 8 =
            subGen 0 ((if j = 0 then T0 else T1) ix).2.1 := by
          rw [m15, ← V10, K14.acc (by omega) (by omega), m13, K12.acc (by omega) (by omega), m11]
        have hz' : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA20 + 0x40)) 8 = ((if j = 0 then T0 else T1) ix).2.2 := by
          rw [m15, ← q3, K14.acc (by omega) (by omega), m13, accV_S 8 fun q hq => V12 q (by omega), m11,
            K10.acc (by omega) (by simp; omega), s9.mem]
        have hQ' : ptF n15.mem B 0xA20 = negPt2 ((if j = 0 then T0 else T1) ix) := by
          unfold ptF negPt2; rw [hx, hy, hz']
        have K12' : SvKeepL B n10.mem n12.mem [(0xA60, 0x20)] := by rw [← m11]; exact SvKeepL.of K12
        have K14' : SvKeepL B n12.mem n14.mem [(0xA20, 0x20)] := by rw [← m13]; exact SvKeepL.of K14
        have KK0 : SvKeepL B m.mem n15.mem [(0xA40, 32), (0xA60, 0x20), (0xA20, 0x20)] := by
          have := (K10.trans K12').trans K14'
          rw [s9.mem] at this; rw [m15]; exact this
        have KK : SvKeepL B m.mem n15.mem mlW := KK0.wider (by simp)
        have A' : ptF n15.mem B 0x1480 = st.1 := by
          rw [(KK0.pt (by decide) (by simp)), A]
        have M' : GM2 B n15.mem T0 T1 D0 D1 := M.keep KK
        have r23' : reg n15 (23 : Fin 32) = BitVec.ofNat 32 (j + 1) := by
          rw [k15 _ (by decide) (by decide), P14.regs _ (by decide), k13 _ (by decide) (by decide) (by decide),
            P12.regs _ (by decide), k11 _ (by decide) (by decide) (by decide), rk10 _ (by decide),
            k9 _ (by decide) (by decide) (by decide) (by decide) (by decide), r23]
        obtain ⟨n16, c16, E16, fr16, K16, s16, R16, r8f, r23f, a0f, V16⟩ :=
          ml2_tail (j := j) (k := k) F E15 s15 (R14.of fun q hq => k15 q (by revert hq; revert q; decide)
            (by revert hq; revert q; decide)) r23'
            (by rw [u15.regs]; simp +decide only [runBlock, BInstr.run, mlG5, upd, ↓reduceIte]
                rw [R14.sp]; simp only [aluEval]; exact sp_1480 _)
            (by rw [u15.regs]; simp +decide only [runBlock, BInstr.run, mlG5, upd, ↓reduceIte]
                rw [R14.sp]; simp only [aluEval]; exact sp_a20 _)
            (by decide) (by decide) hQ' (negPt2_lt hQl) A' hl hj hk
        refine .inr ⟨_, rfl, n16, c0.trans (.cons d1 (c1'.trans (.cons d2 (.cons d3 (.cons d4 (c5.trans (.cons d6
          (c7.trans (.cons d8 (c9.trans (c10.trans (c11.trans (P12.steps.trans (c13.trans (P14.steps.trans
          (c15.trans c16)))))))))))))))), E16,
          fun x hx => by rw [fr16 x hx, m15, P14.fr x hx, m13, P12.fr x hx, m11, f10 x hx, s9.mem], ?_, s16, R16,
          by rw [r8f]; rfl, r23f, a0f, M'.keep K16, V16, ptAdd2_lt _ _⟩
        exact (KK.trans K16).wider (by simp)
    · rw [ite_eq_left (by omega)]
      obtain ⟨n6, d6, u6⟩ := s5.notTaken C 0x19DC sv_at_19d8 (by decide)
        (by rw [s5.zero, a05, dig_bge]; simp [hneg, hb0])
      have s6 : St m.mem SV n6 0x19DC (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
      have e6 : reg n6 = reg n5 := funext u6.regs
      obtain ⟨n7, c7, u7⟩ := s6.block mlP C mlP_end ⟨trivial, trivial, trivial⟩
      have s7 : St m.mem SV n7 0x19E2 (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
      have k7 : ∀ q : Fin 32, q ≠ a0 → q ≠ a3 → reg n7 q = reg n5 q := fun q h0 h3 => by
        rw [u7.regs, runBlock_reg _ _ _ q s6.zero (by simp [mlP, BInstr.dst, h0, h3]), e6]
      have a07 : reg n7 a0 = BitVec.ofNat 32 (b.toNat / 2) := by
        rw [u7.regs]; simp +decide only [runBlock, BInstr.run, mlP, upd, ↓reduceIte]; rw [e6, a25]
        exact (dig_pos b).1
      have a37 : reg n7 a3 = 0x10 := by
        rw [u7.regs]; simp +decide only [runBlock, BInstr.run, mlP, upd, ↓reduceIte]
      by_cases h16 : 16 ≤ b.toNat
      · rw [ite_eq_left h16]
        obtain ⟨n8, d8, u8⟩ := s7.taken C 0x1E52 sv_at_19e2 (by decide)
          (by rw [k7 _ (by decide) (by decide), a25, a37, (dig_pos b).2]; simp [h16])
        refine .inl ⟨rfl, Panics.of_steps (c0.trans (.cons d1 (c1'.trans (.cons d2 (.cons d3 (.cons d4 (c5.trans
          (.cons d6 (c7.trans (.single d8)))))))))) (sv_panic_1e52 F (by rw [u8.mem]; exact E.C) ⟨u8.pc, rfl, fun _ => rfl⟩ ?_)⟩
        rw [u8.regs, k7 _ (by decide) (by decide), R5.sp]
      · rw [ite_eq_right h16]
        obtain ⟨n8, d8, u8⟩ := s7.notTaken C 0x19E6 sv_at_19e2 (by decide)
          (by rw [k7 _ (by decide) (by decide), a25, a37, (dig_pos b).2]; simp [h16])
        have s8 : St m.mem SV n8 0x19E6 (reg n8) := ⟨u8.pc, u8.mem, fun _ => rfl⟩
        have e8 : reg n8 = reg n7 := funext u8.regs
        obtain ⟨n9, c9, u9⟩ := s8.block mlP2 C mlP2_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
        have s9 : St m.mem SV n9 0x19F4 (reg n9) := ⟨u9.pc, u9.mem, fun _ => rfl⟩
        have k9 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a3 → reg n9 q = reg n5 q := fun q h0 h1 h3 => by
          rw [u9.regs, runBlock_reg _ _ _ q s8.zero (by simp [mlP2, BInstr.dst, h0, h1]), e8, k7 q h0 h3]
        have a19 : reg n9 a1 = B + 0x21A0 + BitVec.ofNat 32 (0x420 + 0x300 * j + 0x60 * (b.toNat / 2)) := by
          rw [u9.regs]; simp +decide only [runBlock, BInstr.run, mlP2, upd, ↓reduceIte]
          rw [e8, a07, k7 _ (by decide) (by decide), k7 _ (by decide) (by decide), a15, R5.s4]; simp only [aluEval]
          exact ofNat_add_mul (B + 0x21A0) (0x420 + 0x300 * j) (b.toNat / 2) 0x60 (by omega) (by decide) (by omega)
        have a09 : reg n9 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
          rw [u9.regs]; simp +decide only [runBlock, BInstr.run, mlP2, upd, ↓reduceIte]
          rw [e8, k7 _ (by decide) (by decide), R5.sp]; simp only [aluEval]; exact sp_1480 _
        obtain ⟨n10, d10, u10⟩ := s9.jump C sv_at_19f4 (off' := 0x1A5E) (by decide) (by rw [s9.pc]; decide)
        have s10 : St n10.mem SV n10 0x1A5E (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
        have e10 : reg n10 = reg n9 := funext u10.regs
        obtain ⟨hQ, hQl⟩ := hT (b.toNat / 2) (by omega)
        have E10 : MlEnv n10.mem := by rw [u10.mem]; exact E
        obtain ⟨n11, c11, E11, fr11, K11, s11, R11, r8f, r23f, a0f, V11⟩ :=
          ml2_tail (j := j) (k := k) F E10 s10 (R5.of fun q hq => by
            rw [e10, k9 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
              (by revert hq; revert q; decide)])
            (by rw [e10, k9 _ (by decide) (by decide) (by decide), r23]) (by rw [e10, a09]) (by rw [e10, a19]) (by omega)
            (by omega) (by rw [u10.mem]; exact hQ) hQl (by rw [u10.mem]; exact A) hl hj hk
        refine .inr ⟨_, rfl, n11, c0.trans (.cons d1 (c1'.trans (.cons d2 (.cons d3 (.cons d4 (c5.trans (.cons d6
          (c7.trans (.cons d8 (c9.trans (.cons d10 c11))))))))))), E11, fun x hx => by rw [fr11 x hx, u10.mem], ?_,
          s11, R11, by rw [r8f]; rfl, r23f, a0f, (by rw [u10.mem] at K11; exact M.keep K11), V11, ptAdd2_lt _ _⟩
        rw [u10.mem] at K11; exact K11

end C3.RV32.Sv
