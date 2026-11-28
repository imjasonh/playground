import C3BootProofs.Proofs.Pv384Lib5

/-!
# `p384_verify_prehash`: one digit of the main loop

The model of the main loop of the linear combination `u₁·G + u₂·Q`, and
the proof of its step for one pair: read the pair's wNAF digit at the
current position, and add the table entry it names, or its negation, to the
accumulator.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- A table entry with its `y` coordinate negated. -/
def negPt (P : Pt) : Pt := (P.1, negY P.2.1, P.2.2)

/-- What the loop does with the digit byte `b` of a pair whose table is `T`:
`some none` to skip it, `some (some acc')` to add an entry, and `none` when a
bounds check fails. -/
def mlAdd (T : Nat → Pt) (acc : Pt) (b : Nat) : Option (Option Pt) :=
  if b = 0 then some none
  else if b < 128 then (if 16 ≤ b then none else some (some (ptAddT acc (T (b / 2)))))
  else if b = 128 ∨ 8 ≤ (256 - b) / 2 then none
  else some (some (ptAddT acc (negPt (T ((256 - b) / 2)))))

/-- The step for one pair at position `k`: the accumulator and whether it
has had an entry added. -/
def mlPair (T : Nat → Pt) (D : List Nat) (k : Nat) (st : Pt × Bool) : Option (Pt × Bool) :=
  if 0x181 < k + 1 then some st
  else match mlAdd T st.1 (D.getD k 0) with
    | none => none
    | some none => some st
    | some (some a) => some (a, true)

/-- One position of the main loop: double the accumulator once it has an
entry, then step the two pairs. -/
def mlIter (T0 T1 : Nat → Pt) (D0 D1 : List Nat) (k : Nat) (st : Pt × Bool) : Option (Pt × Bool) :=
  (mlPair T0 D0 k (if st.2 then ptDblT st.1 else st.1, st.2)).bind (mlPair T1 D1 k)

/-- The main loop from position `k - 1` down to 0. -/
def mlLoop (T0 T1 : Nat → Pt) (D0 D1 : List Nat) : Nat → Pt × Bool → Option (Pt × Bool)
  | 0, st => some st
  | k + 1, st => (mlIter T0 T1 D0 D1 k st).bind (mlLoop T0 T1 D0 D1 k)

abbrev sx8 (a : Word) : Word := aluEval .sra (aluEval .sll a 0x18) 0x18

theorem dig_bge : ∀ b : BitVec 8,
    branchTaken .bge 0 (sx8 (b.zeroExtend 32)) = decide (b.toNat = 0 ∨ 128 ≤ b.toNat) := by decide

theorem dig_pos : ∀ b : BitVec 8,
    aluEval .srl (b.zeroExtend 32) 1 = BitVec.ofNat 32 (b.toNat / 2) ∧
    branchTaken .bgeu (b.zeroExtend 32) 0x10 = decide (16 ≤ b.toNat) := by decide

/-- The index the loop computes from a negative digit byte. -/
def negIdx (b : BitVec 8) : Word := aluEval .div (sx8 (aluEval .sub 0 (b.zeroExtend 32))) 2

theorem dig_neg : ∀ b : BitVec 8, 128 ≤ b.toNat →
    branchTaken .bgeu (aluEval .and (negIdx b) 0xFF) 8 = decide (b.toNat = 128 ∨ 8 ≤ (256 - b.toNat) / 2) ∧
    (¬ (b.toNat = 128 ∨ 8 ≤ (256 - b.toNat) / 2) → sx8 (negIdx b) = BitVec.ofNat 32 ((256 - b.toNat) / 2)) := by
  decide

theorem zext_ne0 : ∀ b : BitVec 8, (b.zeroExtend 32 != (0 : Word)) = decide (b.toNat ≠ 0) := by decide

/-- The tables, the digits, and the order in Montgomery form `r`, which the
main loop reads and does not change. -/
structure GM (B : Word) (M : Word → BitVec 8) (T0 T1 : Nat → Pt) (D0 D1 : List Nat) (RM : Nat) : Prop where
  t0 : ∀ j, j < 8 → ptV M B (0x450 + 0x90 * j) = T0 j
  t1 : ∀ j, j < 8 → ptV M B (0x8D0 + 0x90 * j) = T1 j
  tl : ∀ j, j < 8 → PtLt (T0 j) ∧ PtLt (T1 j)
  d0 : memBytes M (B + 0x420 + BitVec.ofNat 32 0x1928) 0x181 = D0
  d1 : memBytes M (B + 0x420 + BitVec.ofNat 32 0x1AB0) 0x181 = D1
  rm : accV M (B + 0x420 + BitVec.ofNat 32 0x1B0) 12 = RM

theorem ptV_keep {B : Word} {M M' : Word → BitVec 8} {c w d : Nat} (K : PvKeep B M M' c w) (hd : d + 0x90 ≤ 0x1D4C)
    (h : d + 0x90 ≤ c ∨ c + w ≤ d) : ptV M' B d = ptV M B d := by
  unfold ptV
  rw [K.acc (k := 12) (by omega) (by omega), K.acc (k := 12) (by omega) (by omega), K.acc (k := 12) (by omega) (by omega)]

/-- The main loop writes only the accumulator at 0xE10 and scratch from
0x1294 to 0x1324. -/
theorem GM.keep {B : Word} {M M' : Word → BitVec 8} {T0 T1 : Nat → Pt} {D0 D1 : List Nat} {RM : Nat}
    (G : GM B M T0 T1 D0 D1 RM) {c w : Nat} (K : PvKeep B M M' c w)
    (h : (0x1294 ≤ c ∧ c + w ≤ 0x1324) ∨ (0xE10 ≤ c ∧ c + w ≤ 0xEA0)) : GM B M' T0 T1 D0 D1 RM :=
  ⟨fun j hj => (ptV_keep K (by omega) (by omega)).trans (G.t0 j hj),
    fun j hj => (ptV_keep K (by omega) (by omega)).trans (G.t1 j hj), G.tl,
    (memBytes_keep K (by decide) (by omega)).trans G.d0, (memBytes_keep K (by decide) (by omega)).trans G.d1,
    (K.acc (k := 12) (by decide) (by omega)).trans G.rm⟩

/-- The registers the main loop keeps, at position `k` with the accumulator
state `st`. -/
structure GR (B : Word) (m : Machine) (r3 r4 : Word) (k : Nat) : Prop where
  sp : reg m sp = B + 0x420
  g3 : reg m (3 : Fin 32) = r3
  g4 : reg m (4 : Fin 32) = r4
  s0 : reg m (8 : Fin 32) = 2
  s1 : reg m (9 : Fin 32) = BitVec.ofNat 32 (k + 1)
  s3 : reg m (19 : Fin 32) = BitVec.ofNat 32 k
  s4 : reg m (20 : Fin 32) = 0x90
  s6 : reg m (22 : Fin 32) = 0x188
  s7 : reg m (23 : Fin 32) = B + 0x420 + BitVec.ofNat 32 (0x1928 + k)
  s8 : reg m (24 : Fin 32) = 0x181
  s9 : reg m (25 : Fin 32) = 0x480
  s10 : reg m (26 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0x450
  s11 : reg m (27 : Fin 32) = 0x10

theorem GR.of {B : Word} {m m' : Machine} {r3 r4 : Word} {k : Nat} (R : GR B m r3 r4 k)
    (h : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 19, 20, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) :
    GR B m' r3 r4 k :=
  ⟨by rw [h RV32.sp (by decide), R.sp], by rw [h _ (by decide), R.g3], by rw [h _ (by decide), R.g4],
    by rw [h _ (by decide), R.s0], by rw [h _ (by decide), R.s1], by rw [h _ (by decide), R.s3],
    by rw [h _ (by decide), R.s4], by rw [h _ (by decide), R.s6],
    by rw [h _ (by decide), R.s7], by rw [h _ (by decide), R.s8], by rw [h _ (by decide), R.s9],
    by rw [h _ (by decide), R.s10], by rw [h _ (by decide), R.s11]⟩

def pvP11e0 : List BInstr := [.aluImm .add a1 x0 0x8]
theorem pvP11e0_end : blockEnd p384VerifyPrehashCode 0x11E0 pvP11e0 = some 0x11E2 := by decide

/-- The panic at 0x11E0: a failed bounds check on a table index. -/
theorem pv_panic11e0 {B : Word} {m : Machine} (F : Fr B 0x21A0) (E : PvEnv m.mem)
    (s : St m.mem PV m 0x11E0 (reg m)) (hsp : reg m sp = B + 0x420) : Panics m := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  obtain ⟨m1, c1, u1⟩ := s.block pvP11e0 E.C.self pvP11e0_end ⟨trivial, trivial⟩
  have s1 : St m.mem PV m1 0x11E2 (reg m1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have sp1 : reg m1 sp = B + 0x420 := by
    rw [u1.regs, runBlock_reg _ _ _ sp s.zero (by decide)]; exact hsp
  obtain ⟨n1, c2, pc2, mem2, regs2⟩ := s1.callRa E.C.self pv_at_11e2 pv_at_11e6
    (cb := BitVec.ofNat 32 panicBoundsCheckAddress) (by decide) (by decide)
  refine Panics.of_steps (c1.trans c2) (panicBoundsCheck_panics n1 (by rw [mem2]; exact E.C.K.panic) pc2 ?_)
  rw [regs2, upd_ne (by decide) (by decide), sp1]; exact FS.room (by decide)

theorem keepL {m m' : Machine}
    (h : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) :
    ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 19, 20, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
  fun q hq => h q (by revert hq; revert q; decide)

theorem ptV_eq {M : Word → BitVec 8} {B : Word} {c : Nat} {P : Pt} (h : ptV M B c = P) :
    accV M (B + 0x420 + BitVec.ofNat 32 c) 12 = P.1 ∧ accV M (B + 0x420 + BitVec.ofNat 32 (c + 0x30)) 12 = P.2.1 ∧
      accV M (B + 0x420 + BitVec.ofNat 32 (c + 0x60)) 12 = P.2.2 := by
  subst h; exact ⟨rfl, rfl, rfl⟩

theorem ofNat_mul_add (S : Word) (j c d : Nat) (h : c + d * j < 2 ^ 32) (hd : d < 2 ^ 32) (hj : j < 2 ^ 32) :
    BitVec.ofNat 32 j * BitVec.ofNat 32 d + (S + BitVec.ofNat 32 c) = S + BitVec.ofNat 32 (c + d * j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt h, Nat.mul_comm j d]
  omega

def pvGbe2 : List BInstr := [.aluImm .add (21 : Fin 32) x0 0x1]
theorem pvGbe2_end : blockEnd p384VerifyPrehashCode 0xBE2 pvGbe2 = some 0xBE4 := by decide
def pvGb1e : List BInstr := [.alu .mul a0 (18 : Fin 32) (22 : Fin 32), .alu .add a0 a0 (23 : Fin 32)]
theorem pvGb1e_end : blockEnd p384VerifyPrehashCode 0xB1E pvGb1e = some 0xB24 := by decide

set_option maxHeartbeats 16000000 in
/-- The end of a pair's step that adds an entry, from 0xBDA: add the point
at offset `cr` to the accumulator, mark the accumulator, and move to the
next pair. -/
theorem ml_tail {B r3 r4 : Word} {T0 T1 : Nat → Pt} {D0 D1 : List Nat} {RM k j cr : Nat} {Q acc : Pt}
    {m : Machine} (F : Fr B 0x21A0) (E : PvEnv6 m.mem) (s : St m.mem PV m 0xBDA (reg m)) (R : GR B m r3 r4 k)
    (h2 : reg m (18 : Fin 32) = BitVec.ofNat 32 (j + 1)) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 0xE10)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cr) (hcr : cr + 144 ≤ 0x1D4C) (acr : cr % 4 = 0)
    (hd : cr + 144 ≤ 0xE10 ∨ 0xEA0 ≤ cr) (hQ : ptV m.mem B cr = Q) (hQl : PtLt Q)
    (A : ptV m.mem B 0xE10 = acc) (hl : PtLt acc) (M : GM B m.mem T0 T1 D0 D1 RM) (hj : j < 2) (hk : k + 1 ≤ 0x181) :
    ∃ m', Steps m m' ∧ PvEnv6 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
      St m'.mem PV m' (if j = 0 then 0xB28 else 0xBE6) (reg m') ∧ GR B m' r3 r4 k ∧
      reg m' (21 : Fin 32) = 1 ∧ reg m' (18 : Fin 32) = BitVec.ofNat 32 (j + 1) ∧
      reg m' a0 = B + 0x420 + BitVec.ofNat 32 (0x1928 + k + 0x188 * (j + 1)) ∧
      GM B m'.mem T0 T1 D0 D1 RM ∧ ptV m'.mem B 0xE10 = ptAddT acc Q := by
  obtain ⟨q1, q2, q3⟩ := ptV_eq hQ
  obtain ⟨a1', a2', a3'⟩ := ptV_eq A
  obtain ⟨n1, P1, K1, V1⟩ := pv_pa F E.E.E s pv_at_bda pv_at_bde (by decide) (by decide) R.sp ha0 ha1 (by decide)
    hcr (by decide) acr (by rw [a1']; exact hl.1) (by rw [a2']; exact hl.2.1) (by rw [a3']; exact hl.2.2)
    (by rw [q1]; exact hQl.1) (by rw [q2]; exact hQl.2.1) (by rw [q3]; exact hQl.2.2)
  rw [a1', a2', a3', q1, q2, q3] at V1
  have E1 : PvEnv6 n1.mem := E.fr F P1.fr
  have s1 := P1.st
  obtain ⟨n2, c2, u2⟩ := s1.block pvGbe2 E1.E.E.E.E.C.self pvGbe2_end ⟨trivial, trivial⟩
  have s2 : St n1.mem PV n2 0xBE4 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have k2 : ∀ q : Fin 32, q ≠ (21 : Fin 32) → reg n2 q = reg n1 q := fun q h =>
    by rw [u2.regs, runBlock_reg _ _ _ q s1.zero (by simp [pvGbe2, BInstr.dst, h])]
  have r21 : reg n2 (21 : Fin 32) = 1 := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, pvGbe2, upd, ↓reduceIte, aluEval]; rw [s1.zero]; rfl
  obtain ⟨n3, d3, u3⟩ := s2.jump E1.E.E.E.E.C.self pv_at_be4 (off' := 0xB1E) (by decide) (by rw [s2.pc]; decide)
  have s3 : St n1.mem PV n3 0xB1E (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  obtain ⟨n4, c4, u4⟩ := s3.block pvGb1e E1.E.E.E.E.C.self pvGb1e_end ⟨trivial, trivial, trivial⟩
  have s4 : St n1.mem PV n4 0xB24 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
  have k4 : ∀ q : Fin 32, q ≠ a0 → reg n4 q = reg n3 q := fun q h =>
    by rw [u4.regs, runBlock_reg _ _ _ q s3.zero (by simp [pvGb1e, BInstr.dst, h])]
  have R1 := R.of (keepL P1.regs)
  have r18 : reg n3 (18 : Fin 32) = BitVec.ofNat 32 (j + 1) := by
    rw [u3.regs, k2 _ (by decide), P1.regs _ (by decide), h2]
  have r22 : reg n3 (22 : Fin 32) = 0x188 := by rw [u3.regs, k2 _ (by decide), R1.s6]
  have r23 : reg n3 (23 : Fin 32) = B + 0x420 + BitVec.ofNat 32 (0x1928 + k) := by
    rw [u3.regs, k2 _ (by decide), R1.s7]
  have a04 : reg n4 a0 = B + 0x420 + BitVec.ofNat 32 (0x1928 + k + 0x188 * (j + 1)) := by
    rw [u4.regs]; simp +decide only [runBlock, BInstr.run, pvGb1e, upd, ↓reduceIte, aluEval]
    rw [r18, r22, r23]; exact ofNat_mul_add (B + 0x420) (j + 1) (0x1928 + k) 0x188 (by omega) (by decide) (by omega)
  have R4 : GR B n4 r3 r4 k := R1.of fun q hq => by
    rw [k4 q (by revert hq; revert q; decide), u3.regs, k2 q (by revert hq; revert q; decide)]
  have r18' : reg n4 (18 : Fin 32) = BitVec.ofNat 32 (j + 1) := by rw [k4 _ (by decide), r18]
  have r21' : reg n4 (21 : Fin 32) = 1 := by rw [k4 _ (by decide), u3.regs, r21]
  have M1 : GM B n1.mem T0 T1 D0 D1 RM := M.keep K1 (.inr ⟨by decide, by decide⟩)
  by_cases hj0 : j = 0
  · subst hj0
    obtain ⟨n5, d5, u5⟩ := s4.notTaken E1.E.E.E.E.C.self 0xB28 pv_at_b24 (by decide)
      (by rw [r18', R4.s0]; decide)
    refine ⟨n5, P1.steps.trans (c2.trans (.cons d3 (c4.trans (.single d5)))), by rw [u5.mem]; exact E1,
      fun x hx => by rw [u5.mem, P1.fr x hx], ⟨u5.pc, rfl, fun _ => rfl⟩, R4.of fun q _ => u5.regs q,
      by rw [u5.regs, r21'], by rw [u5.regs, r18'], by rw [u5.regs, a04], by rw [u5.mem]; exact M1,
      by rw [u5.mem]; exact V1⟩
  · obtain rfl : j = 1 := by omega
    obtain ⟨n5, d5, u5⟩ := s4.taken E1.E.E.E.E.C.self 0xBE6 pv_at_b24 (by decide)
      (by rw [r18', R4.s0]; decide)
    refine ⟨n5, P1.steps.trans (c2.trans (.cons d3 (c4.trans (.single d5)))), by rw [u5.mem]; exact E1,
      fun x hx => by rw [u5.mem, P1.fr x hx], ⟨u5.pc, rfl, fun _ => rfl⟩, R4.of fun q _ => u5.regs q,
      by rw [u5.regs, r21'], by rw [u5.regs, r18'], by rw [u5.regs, a04], by rw [u5.mem]; exact M1,
      by rw [u5.mem]; exact V1⟩

def pvGb32 : List BInstr := [.aluImm .add a0 a0 0x188, .aluImm .add (18 : Fin 32) (18 : Fin 32) 0x1]
theorem pvGb32_end : blockEnd p384VerifyPrehashCode 0xB32 pvGb32 = some 0xB38 := by decide
def pvGb3e : List BInstr := [.alu .mul a1 (18 : Fin 32) (25 : Fin 32), .aluImm .sll a0 a2 0x18,
  .aluImm .sra a0 a0 0x18, .aluImm .add (18 : Fin 32) (18 : Fin 32) 0x1, .alu .add a1 a1 (26 : Fin 32)]
theorem pvGb3e_end : blockEnd p384VerifyPrehashCode 0xB3E pvGb3e = some 0xB4C := by decide
def pvGb50 : List BInstr := [.aluImm .srl a0 a2 0x1]
theorem pvGb50_end : blockEnd p384VerifyPrehashCode 0xB50 pvGb50 = some 0xB54 := by decide
def pvGb58 : List BInstr := [.alu .mul a0 a0 (20 : Fin 32), .alu .add a1 a1 a0, .aluImm .add a0 sp 0x7FF,
  .aluImm .add a0 a0 0x611]
theorem pvGb58_end : blockEnd p384VerifyPrehashCode 0xB58 pvGb58 = some 0xB66 := by decide
def pvGb68 : List BInstr := [.alu .sub a0 x0 a2, .aluImm .sll a0 a0 0x18, .aluImm .sra a0 a0 0x18,
  .alu .div a0 a0 (8 : Fin 32), .aluImm .and a2 a0 0xFF, .aluImm .sll a0 a0 0x18, .aluImm .sra a0 a0 0x18,
  .aluImm .add a3 x0 0x8]
theorem pvGb68_end : blockEnd p384VerifyPrehashCode 0xB68 pvGb68 = some 0xB7E := by decide
def pvGb82 : List BInstr := [.alu .mul (21 : Fin 32) a0 (20 : Fin 32), .alu .add (21 : Fin 32) (21 : Fin 32) a1,
  .aluImm .add a1 (21 : Fin 32) 0x30, .lui a0 0x1000, .aluImm .add a0 a0 0x2C4, .alu .add a0 a0 sp]
theorem pvGb82_end : blockEnd p384VerifyPrehashCode 0xB82 pvGb82 = some 0xB94 := by decide
def pvGb9c : List BInstr := [.aluImm .add a1 (21 : Fin 32) 0x60, .aluImm .add a2 x0 0x30, .lui a0 0x1000,
  .aluImm .add a0 a0 0x2F4, .alu .add a0 a0 sp]
theorem pvGb9c_end : blockEnd p384VerifyPrehashCode 0xB9C pvGb9c = some 0xBAC := by decide
def pvGbb4 : List BInstr := [.lui a0 0x1000, .aluImm .add a0 a0 0x294, .alu .add a0 a0 sp, .aluImm .add a2 x0 0x30,
  .alu .add a1 x0 (21 : Fin 32)]
theorem pvGbb4_end : blockEnd p384VerifyPrehashCode 0xBB4 pvGbb4 = some 0xBC2 := by decide
def pvGbca : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x611, .lui a1 0x1000,
  .aluImm .add a1 a1 0x294, .alu .add a1 a1 sp]
theorem pvGbca_end : blockEnd p384VerifyPrehashCode 0xBCA pvGbca = some 0xBDA := by decide

theorem ult_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    BitVec.ult (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat_add_mul (S : Word) (c y d : Nat) (h : c + d * y < 2 ^ 32) (hd : d < 2 ^ 32) (hy : y < 2 ^ 32) :
    S + BitVec.ofNat 32 c + BitVec.ofNat 32 y * BitVec.ofNat 32 d = S + BitVec.ofNat 32 (c + d * y) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt h, Nat.mul_comm y d]
  omega

theorem sp_e10 (S : Word) : S + 0x7FF + 0x611 = S + BitVec.ofNat 32 0xE10 := by
  rw [BitVec.add_assoc]; rfl

theorem sp_lui (S : Word) (c : Nat) (hc : 0x1000 + c < 2 ^ 32) :
    (0x1000 : Word) + BitVec.ofNat 32 c + S = S + BitVec.ofNat 32 (0x1000 + c) := by
  rw [BitVec.add_comm, show (0x1000 : Word) = BitVec.ofNat 32 0x1000 from rfl, BitVec.ofNat_add_ofNat]

theorem dig_byte {B : Word} {M : Word → BitVec 8} {D0 D1 : List Nat} {k j : Nat}
    (h0 : memBytes M (B + 0x420 + BitVec.ofNat 32 0x1928) 0x181 = D0)
    (h1 : memBytes M (B + 0x420 + BitVec.ofNat 32 0x1AB0) 0x181 = D1) (hj : j < 2) (hk : k + 1 ≤ 0x181) :
    (M (B + 0x420 + BitVec.ofNat 32 (0x1928 + k + 0x188 * j))).toNat = (if j = 0 then D0 else D1).getD k 0 := by
  by_cases hj0 : j = 0
  · subst hj0
    rw [ite_eq_left rfl, ← h0, memBytes_getD (by omega), add_ofNat_assoc, show 0x1928 + k + 0x188 * 0 = 0x1928 + k by omega]
  · obtain rfl : j = 1 := by omega
    rw [ite_eq_right (by decide), ← h1, memBytes_getD (by omega), add_ofNat_assoc,
      show 0x1928 + k + 0x188 * 1 = 0x1AB0 + k by omega]

set_option maxHeartbeats 64000000 in
/-- **One pair's step**, from 0xB28: read the digit byte of pair `j` at
position `k` and act on it as `mlPair` does. -/
theorem ml_pair {B r3 r4 : Word} {T0 T1 : Nat → Pt} {D0 D1 : List Nat} {RM k j : Nat} {st : Pt × Bool}
    {m : Machine} (F : Fr B 0x21A0) (E : PvEnv6 m.mem) (s : St m.mem PV m 0xB28 (reg m)) (R : GR B m r3 r4 k)
    (hs5 : reg m (21 : Fin 32) = if st.2 then 1 else 0) (h2 : reg m (18 : Fin 32) = BitVec.ofNat 32 j)
    (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 (0x1928 + k + 0x188 * j)) (M : GM B m.mem T0 T1 D0 D1 RM)
    (A : ptV m.mem B 0xE10 = st.1) (hl : PtLt st.1) (hj : j < 2) (hk : k + 1 ≤ 0x181) :
    (mlPair (if j = 0 then T0 else T1) (if j = 0 then D0 else D1) k st = none ∧ Panics m) ∨
    (∃ st', mlPair (if j = 0 then T0 else T1) (if j = 0 then D0 else D1) k st = some st' ∧
      ∃ m', Steps m m' ∧ PvEnv6 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
        St m'.mem PV m' (if j = 0 then 0xB28 else 0xBE6) (reg m') ∧ GR B m' r3 r4 k ∧
        reg m' (21 : Fin 32) = (if st'.2 then 1 else 0) ∧ reg m' (18 : Fin 32) = BitVec.ofNat 32 (j + 1) ∧
        reg m' a0 = B + 0x420 + BitVec.ofNat 32 (0x1928 + k + 0x188 * (j + 1)) ∧
        GM B m'.mem T0 T1 D0 D1 RM ∧ ptV m'.mem B 0xE10 = st'.1 ∧ PtLt st'.1) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have C := E.E.E.E.E.C.self
  -- the bounds check on the position passes
  obtain ⟨n1, d1, u1⟩ := s.notTaken C 0xB2C pv_at_b28 (by decide)
    (by rw [R.s8, R.s1]; simp only [branchTaken]; rw [show (0x181 : Word) = BitVec.ofNat 32 0x181 from rfl,
      ult_ofNat (by decide) (by omega)]; simp only [decide_eq_false_iff_not]; omega)
  have s1 : St m.mem PV n1 0xB2C (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have e1 : reg n1 = reg m := funext u1.regs
  -- the digit byte
  obtain ⟨b, hb⟩ : ∃ b, m.mem (B + 0x420 + BitVec.ofNat 32 (0x1928 + k + 0x188 * j)) = b := ⟨_, rfl⟩
  have hbv : b.toNat = (if j = 0 then D0 else D1).getD k 0 := by rw [← hb]; exact dig_byte M.d0 M.d1 hj hk
  obtain ⟨n2, d2, u2⟩ := s1.lbu C pv_at_b2c (off' := 0xB30) (by decide)
  have s2 : St m.mem PV n2 0xB30 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have a22 : reg n2 a2 = b.zeroExtend 32 := by
    rw [u2.regs, upd_same (by decide), e1, ha0, add_lit_zero, hb]
  have k2 : ∀ q : Fin 32, q ≠ a2 → reg n2 q = reg m q := fun q h => by
    rw [u2.regs, updz s1.zero h, e1]
  have R2 : GR B n2 r3 r4 k := R.of fun q hq => k2 q (by revert hq; revert q; decide)
  unfold mlPair
  rw [ite_eq_right (by omega)]
  unfold mlAdd
  rw [← hbv]
  by_cases hb0 : b.toNat = 0
  · -- a zero digit: skip
    rw [ite_eq_left hb0]
    obtain ⟨n3, d3, u3⟩ := s2.notTaken C 0xB32 pv_at_b30 (by decide)
      (by rw [a22, s2.zero]; simp only [branchTaken]; rw [zext_ne0]; simp [hb0])
    have s3 : St m.mem PV n3 0xB32 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
    obtain ⟨n4, c4, u4⟩ := s3.block pvGb32 C pvGb32_end ⟨trivial, trivial, trivial⟩
    have s4 : St m.mem PV n4 0xB38 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
    have k4 : ∀ q : Fin 32, q ≠ a0 → q ≠ (18 : Fin 32) → q ≠ a2 → reg n4 q = reg m q := fun q h0 h18 h2' => by
      rw [u4.regs, runBlock_reg _ _ _ q s3.zero (by simp [pvGb32, BInstr.dst, h0, h18]), u3.regs, k2 q h2']
    have a04 : reg n4 a0 = B + 0x420 + BitVec.ofNat 32 (0x1928 + k + 0x188 * (j + 1)) := by
      rw [u4.regs]; simp +decide only [runBlock, BInstr.run, pvGb32, upd, ↓reduceIte, aluEval]
      rw [u3.regs, k2 _ (by decide), ha0, show (0x188 : Word) = BitVec.ofNat 32 0x188 from rfl, add_ofNat_assoc,
        show 0x1928 + k + 0x188 * j + 0x188 = 0x1928 + k + 0x188 * (j + 1) by omega]
    have r18 : reg n4 (18 : Fin 32) = BitVec.ofNat 32 (j + 1) := by
      rw [u4.regs]; simp +decide only [runBlock, BInstr.run, pvGb32, upd, ↓reduceIte, aluEval]
      rw [u3.regs, k2 _ (by decide), h2, show (1 : Word) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
    have R4 : GR B n4 r3 r4 k := R.of fun q hq => k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)
    have r21 : reg n4 (21 : Fin 32) = if st.2 then 1 else 0 := by rw [k4 _ (by decide) (by decide) (by decide), hs5]
    refine .inr ⟨st, rfl, ?_⟩
    by_cases hj0 : j = 0
    · subst hj0
      obtain ⟨n5, d5, u5⟩ := s4.notTaken C 0xB3C pv_at_b38 (by decide) (by rw [r18, R4.s0]; decide)
      have s5 : St m.mem PV n5 0xB3C (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
      obtain ⟨n6, d6, u6⟩ := s5.jump C pv_at_b3c (off' := 0xB28) (by decide) (by rw [s5.pc]; decide)
      refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (.single d6))))), by rw [u6.mem]; exact E,
        fun x hx => by rw [u6.mem], ⟨u6.pc, rfl, fun _ => rfl⟩, R4.of fun q _ => by rw [u6.regs, u5.regs],
        by rw [u6.regs, u5.regs, r21], by rw [u6.regs, u5.regs, r18], by rw [u6.regs, u5.regs, a04],
        by rw [u6.mem]; exact M, by rw [u6.mem]; exact A, hl⟩
    · obtain rfl : j = 1 := by omega
      obtain ⟨n5, d5, u5⟩ := s4.taken C 0xBE6 pv_at_b38 (by decide) (by rw [r18, R4.s0]; decide)
      refine ⟨n5, .cons d1 (.cons d2 (.cons d3 (c4.trans (.single d5)))), by rw [u5.mem]; exact E,
        fun x hx => by rw [u5.mem], ⟨u5.pc, rfl, fun _ => rfl⟩, R4.of fun q _ => by rw [u5.regs],
        by rw [u5.regs, r21], by rw [u5.regs, r18], by rw [u5.regs, a04], by rw [u5.mem]; exact M,
        by rw [u5.mem]; exact A, hl⟩
  · rw [ite_eq_right hb0]
    obtain ⟨n3, d3, u3⟩ := s2.taken C 0xB3E pv_at_b30 (by decide)
      (by rw [a22, s2.zero]; simp only [branchTaken]; rw [zext_ne0]; simp [hb0])
    have s3 : St m.mem PV n3 0xB3E (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
    have e3 : reg n3 = reg n2 := funext u3.regs
    obtain ⟨n4, c4, u4⟩ := s3.block pvGb3e C pvGb3e_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    have s4 : St m.mem PV n4 0xB4C (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
    have k4 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ (18 : Fin 32) → reg n4 q = reg n2 q := fun q h0 h1 h18 => by
      rw [u4.regs, runBlock_reg _ _ _ q s3.zero (by simp [pvGb3e, BInstr.dst, h0, h1, h18]), e3]
    have a14 : reg n4 a1 = B + 0x420 + BitVec.ofNat 32 (0x450 + 0x480 * j) := by
      rw [u4.regs]; simp +decide only [runBlock, BInstr.run, pvGb3e, upd, ↓reduceIte]
      rw [e3, k2 _ (by decide), k2 _ (by decide), k2 _ (by decide), h2, R.s9, R.s10]
      exact ofNat_mul_add (B + 0x420) j 0x450 0x480 (by omega) (by decide) (by omega)
    have a04 : reg n4 a0 = sx8 (b.zeroExtend 32) := by
      rw [u4.regs]; simp +decide only [runBlock, BInstr.run, pvGb3e, upd, ↓reduceIte]; rw [e3, a22]
    have r18 : reg n4 (18 : Fin 32) = BitVec.ofNat 32 (j + 1) := by
      rw [u4.regs]; simp +decide only [runBlock, BInstr.run, pvGb3e, upd, ↓reduceIte, aluEval]
      rw [e3, k2 _ (by decide), h2, show (1 : Word) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
    have a24 : reg n4 a2 = b.zeroExtend 32 := by rw [k4 _ (by decide) (by decide) (by decide), a22]
    have R4 : GR B n4 r3 r4 k := R2.of fun q hq => k4 q (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    have hT : ∀ i, i < 8 → ptV m.mem B (0x450 + 0x480 * j + 0x90 * i) = (if j = 0 then T0 else T1) i ∧
        PtLt ((if j = 0 then T0 else T1) i) := fun i hi => by
      by_cases hj0 : j = 0
      · subst hj0; rw [ite_eq_left rfl, show 0x450 + 0x480 * 0 + 0x90 * i = 0x450 + 0x90 * i by omega]
        exact ⟨M.t0 i hi, (M.tl i hi).1⟩
      · obtain rfl : j = 1 := by omega
        rw [ite_eq_right (by decide), show 0x450 + 0x480 * 1 + 0x90 * i = 0x8D0 + 0x90 * i by omega]
        exact ⟨M.t1 i hi, (M.tl i hi).2⟩
    by_cases hneg : 128 ≤ b.toNat
    · rw [ite_eq_right (by omega)]
      obtain ⟨n5, d5, u5⟩ := s4.taken C 0xB68 pv_at_b4c (by decide)
        (by rw [s4.zero, a04, dig_bge]; simp [hneg])
      have s5 : St m.mem PV n5 0xB68 (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
      have e5 : reg n5 = reg n4 := funext u5.regs
      obtain ⟨n6, c6, u6⟩ := s5.block pvGb68 C pvGb68_end
        ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
      have s6 : St m.mem PV n6 0xB7E (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
      have k6 : ∀ q : Fin 32, q ≠ a0 → q ≠ a2 → q ≠ a3 → reg n6 q = reg n4 q := fun q h0 h2' h3 => by
        rw [u6.regs, runBlock_reg _ _ _ q s5.zero (by simp [pvGb68, BInstr.dst, h0, h2', h3]), e5]
      have a26 : reg n6 a2 = aluEval .and (negIdx b) 0xFF := by
        rw [u6.regs]; simp +decide only [runBlock, BInstr.run, pvGb68, upd, ↓reduceIte]
        rw [e5, s4.zero, a24, R4.s0]; rfl
      have a06 : reg n6 a0 = sx8 (negIdx b) := by
        rw [u6.regs]; simp +decide only [runBlock, BInstr.run, pvGb68, upd, ↓reduceIte]
        rw [e5, s4.zero, a24, R4.s0]; rfl
      have a36 : reg n6 a3 = 8 := by
        rw [u6.regs]; simp +decide only [runBlock, BInstr.run, pvGb68, upd, ↓reduceIte]
      obtain ⟨dn1, dn2⟩ := dig_neg b hneg
      by_cases hbad : b.toNat = 128 ∨ 8 ≤ (256 - b.toNat) / 2
      · rw [ite_eq_left hbad]
        obtain ⟨n7, d7, u7⟩ := s6.taken C 0x11E0 pv_at_b7e (by decide)
          (by rw [a26, a36, dn1]; simp [hbad])
        refine .inl ⟨rfl, Panics.of_steps (.cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (c6.trans (.single d7)))))))
          (pv_panic11e0 F (by rw [u7.mem]; exact E.E.E.E.E) ⟨u7.pc, rfl, fun _ => rfl⟩ ?_)⟩
        rw [u7.regs, k6 _ (by decide) (by decide) (by decide), R4.sp]
      · rw [ite_eq_right hbad]
        have hix : (256 - b.toNat) / 2 < 8 := by omega
        obtain ⟨n7, d7, u7⟩ := s6.notTaken C 0xB82 pv_at_b7e (by decide)
          (by rw [a26, a36, dn1]; simp [hbad])
        have s7 : St m.mem PV n7 0xB82 (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
        have e7 : reg n7 = reg n6 := funext u7.regs
        have a07 : reg n7 a0 = BitVec.ofNat 32 ((256 - b.toNat) / 2) := by rw [e7, a06]; exact dn2 hbad
        -- the entry, and the scratch copy of its negation
        obtain ⟨ix, hix'⟩ : ∃ ix, (256 - b.toNat) / 2 = ix := ⟨_, rfl⟩
        rw [hix'] at a07 hix
        rw [hix']
        obtain ⟨hQ, hQl⟩ := hT ix hix
        obtain ⟨q1, q2, q3⟩ := ptV_eq hQ
        obtain ⟨n8, c8, u8⟩ := s7.block pvGb82 C pvGb82_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
        have s8 : St m.mem PV n8 0xB94 (reg n8) := ⟨u8.pc, u8.mem, fun _ => rfl⟩
        have k8 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ (21 : Fin 32) → q ≠ a2 → q ≠ a3 → reg n8 q = reg n4 q :=
          fun q h0 h1 h21 h2' h3 => by
            rw [u8.regs, runBlock_reg _ _ _ q s7.zero (by simp [pvGb82, BInstr.dst, h0, h1, h21]), e7, k6 q h0 h2' h3]
        have ee : 0x450 + 0x480 * j + 0x90 * ix + 0x90 ≤ 0xD50 := by omega
        have a06' : reg n6 a0 = BitVec.ofNat 32 ix := by rw [← a07, e7]
        have r21 : reg n8 (21 : Fin 32) = B + 0x420 + BitVec.ofNat 32 (0x450 + 0x480 * j + 0x90 * ix) := by
          rw [u8.regs]; simp +decide only [runBlock, BInstr.run, pvGb82, upd, ↓reduceIte]
          rw [e7, a06', k6 _ (by decide) (by decide) (by decide), k6 _ (by decide) (by decide) (by decide), a14, R4.s4]
          simp only [aluEval]
          exact ofNat_mul_add (B + 0x420) ix (0x450 + 0x480 * j) 0x90 (by omega) (by decide) (by omega)
        have a18 : reg n8 a1 = B + 0x420 + BitVec.ofNat 32 (0x450 + 0x480 * j + 0x90 * ix + 0x30) := by
          rw [u8.regs]; simp +decide only [runBlock, BInstr.run, pvGb82, upd, ↓reduceIte]
          rw [e7, a06', k6 _ (by decide) (by decide) (by decide), k6 _ (by decide) (by decide) (by decide), a14, R4.s4]
          simp only [aluEval]
          rw [show (0x90 : Word) = BitVec.ofNat 32 0x90 from rfl,
            ofNat_mul_add (B + 0x420) ix (0x450 + 0x480 * j) 0x90 (by omega) (by decide) (by omega),
            show (0x30 : Word) = BitVec.ofNat 32 0x30 from rfl, add_ofNat_assoc]
        have a08 : reg n8 a0 = B + 0x420 + BitVec.ofNat 32 0x12C4 := by
          rw [u8.regs]; simp +decide only [runBlock, BInstr.run, pvGb82, upd, ↓reduceIte]
          rw [e7, k6 _ (by decide) (by decide) (by decide), R4.sp]; simp only [aluEval]
          rw [BitVec.add_comm]; rfl
        have R8 : GR B n8 r3 r4 k := R4.of fun q hq => k8 q (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide)
        have E8 : PvEnv6 n8.mem := by rw [s8.mem]; exact E
        have s8' : St n8.mem PV n8 0xB94 (reg n8) := ⟨s8.pc, rfl, fun _ => rfl⟩
        obtain ⟨n9, P9, K9, V9⟩ := pv_neg F E8 s8' pv_at_b94 pv_at_b98 (by decide) (by decide) R8.sp a08 a18
          (by decide) (by omega) (by decide) (by omega)
        rw [s8.mem, q2] at V9
        have E9 : PvEnv6 n9.mem := E8.fr F P9.fr
        obtain ⟨n10, c10, u10⟩ := P9.st.block pvGb9c E9.E.E.E.E.C.self pvGb9c_end
          ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
        have s10 : St n9.mem PV n10 0xBAC (reg n10) := ⟨u10.pc, u10.mem, fun _ => rfl⟩
        have R9 := R8.of (keepL P9.regs)
        have k10 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n10 q = reg n9 q := fun q h0 h1 h2' => by
          rw [u10.regs, runBlock_reg _ _ _ q P9.st.zero (by simp [pvGb9c, BInstr.dst, h0, h1, h2'])]
        have r21' : reg n9 (21 : Fin 32) = B + 0x420 + BitVec.ofNat 32 (0x450 + 0x480 * j + 0x90 * ix) := by
          rw [P9.regs _ (by decide), r21]
        have E10 : PvEnv6 n10.mem := by rw [s10.mem]; exact E9
        have s10' : St n10.mem PV n10 0xBAC (reg n10) := ⟨s10.pc, rfl, fun _ => rfl⟩
        obtain ⟨n11, P11, K11, V11⟩ := pv_mc F E10.E.E.E.E s10' pv_at_bac pv_at_bb0 (by decide) (by decide)
          (by rw [k10 _ (by decide) (by decide) (by decide), R9.sp])
          (by rw [u10.regs]; simp +decide only [runBlock, BInstr.run, pvGb9c, upd, ↓reduceIte]
              rw [P9.regs sp (by decide), R8.sp]; simp only [aluEval]; rw [BitVec.add_comm]; rfl)
          (by rw [u10.regs]; simp +decide only [runBlock, BInstr.run, pvGb9c, upd, ↓reduceIte]
              rw [r21']; simp only [aluEval]
              rw [show (0x60 : Word) = BitVec.ofNat 32 0x60 from rfl, add_ofNat_assoc])
          (by rw [u10.regs]; simp +decide only [runBlock, BInstr.run, pvGb9c, upd, ↓reduceIte])
          (c := 0x12F4) (d := 0x450 + 0x480 * j + 0x90 * ix + 0x60) (N := 0x30)
          (by decide) (by omega) (by omega)
        have E11 : PvEnv6 n11.mem := E10.fr F P11.fr
        have R11 : GR B n11 r3 r4 k := R9.of fun q hq => by
          rw [P11.regs q (by revert hq; revert q; decide), k10 q (by revert hq; revert q; decide)
            (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
        have r21'' : reg n11 (21 : Fin 32) = B + 0x420 + BitVec.ofNat 32 (0x450 + 0x480 * j + 0x90 * ix) := by
          rw [P11.regs _ (by decide), k10 _ (by decide) (by decide) (by decide), r21']
        obtain ⟨n12, c12, u12⟩ := P11.st.block pvGbb4 E11.E.E.E.E.C.self pvGbb4_end
          ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
        have s12 : St n11.mem PV n12 0xBC2 (reg n12) := ⟨u12.pc, u12.mem, fun _ => rfl⟩
        have k12 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n12 q = reg n11 q := fun q h0 h1 h2' => by
          rw [u12.regs, runBlock_reg _ _ _ q P11.st.zero (by simp [pvGbb4, BInstr.dst, h0, h1, h2'])]
        have E12 : PvEnv6 n12.mem := by rw [s12.mem]; exact E11
        have s12' : St n12.mem PV n12 0xBC2 (reg n12) := ⟨s12.pc, rfl, fun _ => rfl⟩
        obtain ⟨n13, P13, K13, V13⟩ := pv_mc F E12.E.E.E.E s12' pv_at_bc2 pv_at_bc6 (by decide) (by decide)
          (by rw [k12 _ (by decide) (by decide) (by decide), R11.sp])
          (by rw [u12.regs]; simp +decide only [runBlock, BInstr.run, pvGbb4, upd, ↓reduceIte]
              rw [R11.sp]; simp only [aluEval]; rw [BitVec.add_comm]; rfl)
          (by rw [u12.regs]; simp +decide only [runBlock, BInstr.run, pvGbb4, upd, ↓reduceIte]
              rw [r21'']; simp only [aluEval]; exact BitVec.zero_add _)
          (by rw [u12.regs]; simp +decide only [runBlock, BInstr.run, pvGbb4, upd, ↓reduceIte])
          (c := 0x1294) (d := 0x450 + 0x480 * j + 0x90 * ix) (N := 0x30)
          (by decide) (by omega) (by omega)
        have E13 : PvEnv6 n13.mem := E12.fr F P13.fr
        have R13 : GR B n13 r3 r4 k := R11.of fun q hq => by
          rw [P13.regs q (by revert hq; revert q; decide), k12 q (by revert hq; revert q; decide)
            (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
        obtain ⟨n14, c14, u14⟩ := P13.st.block pvGbca E13.E.E.E.E.C.self pvGbca_end
          ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
        have s14 : St n14.mem PV n14 0xBDA (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
        have k14 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg n14 q = reg n13 q := fun q h0 h1 => by
          rw [u14.regs, runBlock_reg _ _ _ q P13.st.zero (by simp [pvGbca, BInstr.dst, h0, h1])]
        have m14 : n14.mem = n13.mem := u14.mem
        have E14 : PvEnv6 n14.mem := by rw [m14]; exact E13
        -- the negated entry at 0x1294
        have mm : n10.mem = n9.mem := s10.mem
        have m12 : n12.mem = n11.mem := s12.mem
        have hx : accV n14.mem (B + 0x420 + BitVec.ofNat 32 0x1294) 12 = ((if j = 0 then T0 else T1) ix).1 := by
          rw [m14, ← q1, accV_S 12 fun q hq => V13 q (by omega), m12, K11.acc (by omega) (by omega), mm,
            K9.acc (by omega) (by omega), s8.mem]
        have hy : accV n14.mem (B + 0x420 + BitVec.ofNat 32 (0x1294 + 0x30)) 12 =
            negY ((if j = 0 then T0 else T1) ix).2.1 := by
          rw [m14, ← V9, K13.acc (by omega) (by omega), m12, K11.acc (by omega) (by omega), mm]
        have hz : accV n14.mem (B + 0x420 + BitVec.ofNat 32 (0x1294 + 0x60)) 12 = ((if j = 0 then T0 else T1) ix).2.2 := by
          rw [m14, ← q3, K13.acc (by omega) (by omega), m12, accV_S 12 fun q hq => V11 q (by omega), mm,
            K9.acc (by omega) (by omega), s8.mem]
        have hQ' : ptV n14.mem B 0x1294 = negPt ((if j = 0 then T0 else T1) ix) := by
          unfold ptV negPt; rw [hx, hy, hz]
        have A' : ptV n14.mem B 0xE10 = st.1 := by
          rw [m14, ptV_keep K13 (by decide) (by decide), m12, ptV_keep K11 (by decide) (by decide), mm,
            ptV_keep K9 (by decide) (by decide), s8.mem, A]
        have M' : GM B n14.mem T0 T1 D0 D1 RM := by
          rw [m14]; refine (((M.keep (M := m.mem) (M' := n9.mem) (by rw [← s8.mem]; exact K9)
            (.inl ⟨by decide, by decide⟩)).keep (M' := n11.mem) (by rw [← mm]; exact K11)
            (.inl ⟨by decide, by decide⟩)).keep (M' := n13.mem) (by rw [← m12]; exact K13)
            (.inl ⟨by decide, by decide⟩))
        have r18'' : reg n14 (18 : Fin 32) = BitVec.ofNat 32 (j + 1) := by
          rw [k14 _ (by decide) (by decide), P13.regs _ (by decide), k12 _ (by decide) (by decide) (by decide),
            P11.regs _ (by decide), k10 _ (by decide) (by decide) (by decide), P9.regs _ (by decide),
            k8 _ (by decide) (by decide) (by decide) (by decide) (by decide), r18]
        obtain ⟨n15, c15, E15, fr15, s15, R15, r21f, r18f, a0f, M15, V15⟩ :=
          ml_tail (j := j) (k := k) F E14 s14 (R13.of fun q hq => k14 q (by revert hq; revert q; decide)
            (by revert hq; revert q; decide)) r18''
            (by rw [u14.regs]; simp +decide only [runBlock, BInstr.run, pvGbca, upd, ↓reduceIte]
                rw [R13.sp]; simp only [aluEval]; exact sp_e10 _)
            (by rw [u14.regs]; simp +decide only [runBlock, BInstr.run, pvGbca, upd, ↓reduceIte]
                rw [R13.sp]; simp only [aluEval]; rw [BitVec.add_comm]; rfl)
            (by decide) (by decide) (by decide) hQ' ⟨hQl.1, negY_lt hQl.2.1, hQl.2.2⟩ A' hl M' hj hk
        refine .inr ⟨_, rfl, n15, .cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (c6.trans (.cons d7 (c8.trans
          (P9.steps.trans (c10.trans (P11.steps.trans (c12.trans (P13.steps.trans (c14.trans c15))))))))))))), E15,
          fun x hx => by rw [fr15 x hx, m14, P13.fr x hx, m12, P11.fr x hx, mm, P9.fr x hx, s8.mem], s15, R15,
          by rw [r21f]; rfl, r18f, a0f, M15, V15, ptAddT_lt _ _⟩
    · rw [ite_eq_left (by omega)]
      obtain ⟨n5, d5, u5⟩ := s4.notTaken C 0xB50 pv_at_b4c (by decide)
        (by rw [s4.zero, a04, dig_bge]; simp [hneg, hb0])
      have s5 : St m.mem PV n5 0xB50 (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
      have e5 : reg n5 = reg n4 := funext u5.regs
      obtain ⟨n6, c6, u6⟩ := s5.block pvGb50 C pvGb50_end ⟨trivial, trivial⟩
      have s6 : St m.mem PV n6 0xB54 (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
      have k6 : ∀ q : Fin 32, q ≠ a0 → reg n6 q = reg n4 q := fun q h0 => by
        rw [u6.regs, runBlock_reg _ _ _ q s5.zero (by simp [pvGb50, BInstr.dst, h0]), e5]
      have a06 : reg n6 a0 = BitVec.ofNat 32 (b.toNat / 2) := by
        rw [u6.regs]; simp +decide only [runBlock, BInstr.run, pvGb50, upd, ↓reduceIte]; rw [e5, a24]
        exact (dig_pos b).1
      by_cases h16 : 16 ≤ b.toNat
      · rw [ite_eq_left h16]
        obtain ⟨n7, d7, u7⟩ := s6.taken C 0x11E0 pv_at_b54 (by decide)
          (by rw [k6 _ (by decide), k6 _ (by decide), a24, R4.s11, (dig_pos b).2]; simp [h16])
        refine .inl ⟨rfl, Panics.of_steps (.cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (c6.trans (.single d7)))))))
          (pv_panic11e0 F (by rw [u7.mem]; exact E.E.E.E.E) ⟨u7.pc, rfl, fun _ => rfl⟩ ?_)⟩
        rw [u7.regs, k6 _ (by decide), R4.sp]
      · rw [ite_eq_right h16]
        obtain ⟨n7, d7, u7⟩ := s6.notTaken C 0xB58 pv_at_b54 (by decide)
          (by rw [k6 _ (by decide), k6 _ (by decide), a24, R4.s11, (dig_pos b).2]; simp [h16])
        have s7 : St m.mem PV n7 0xB58 (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
        have e7 : reg n7 = reg n6 := funext u7.regs
        obtain ⟨n8, c8, u8⟩ := s7.block pvGb58 C pvGb58_end ⟨trivial, trivial, trivial, trivial, trivial⟩
        have s8 : St m.mem PV n8 0xB66 (reg n8) := ⟨u8.pc, u8.mem, fun _ => rfl⟩
        have k8 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg n8 q = reg n4 q := fun q h0 h1 => by
          rw [u8.regs, runBlock_reg _ _ _ q s7.zero (by simp [pvGb58, BInstr.dst, h0, h1]), e7, k6 q h0]
        have a18 : reg n8 a1 = B + 0x420 + BitVec.ofNat 32 (0x450 + 0x480 * j + 0x90 * (b.toNat / 2)) := by
          rw [u8.regs]; simp +decide only [runBlock, BInstr.run, pvGb58, upd, ↓reduceIte]
          rw [e7, a06, k6 _ (by decide), k6 _ (by decide), a14, R4.s4]; simp only [aluEval]
          exact ofNat_add_mul (B + 0x420) (0x450 + 0x480 * j) (b.toNat / 2) 0x90 (by omega) (by decide) (by omega)
        have a08 : reg n8 a0 = B + 0x420 + BitVec.ofNat 32 0xE10 := by
          rw [u8.regs]; simp +decide only [runBlock, BInstr.run, pvGb58, upd, ↓reduceIte]
          rw [e7, k6 _ (by decide), R4.sp]; simp only [aluEval]; exact sp_e10 _
        obtain ⟨n9, d9, u9⟩ := s8.jump C pv_at_b66 (off' := 0xBDA) (by decide) (by rw [s8.pc]; decide)
        have s9 : St n9.mem PV n9 0xBDA (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
        have e9 : reg n9 = reg n8 := funext u9.regs
        obtain ⟨hQ, hQl⟩ := hT (b.toNat / 2) (by omega)
        have E9 : PvEnv6 n9.mem := by rw [u9.mem]; exact E
        obtain ⟨n10, c10, E10, fr10, s10, R10, r21, r18', a010, M10, V10⟩ :=
          ml_tail (j := j) (k := k) F E9 s9 (R4.of fun q hq => by
            rw [e9, k8 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)])
            (by rw [e9, k8 _ (by decide) (by decide), r18]) (by rw [e9, a08]) (by rw [e9, a18]) (by omega)
            (by omega) (by omega) (by rw [u9.mem]; exact hQ) hQl (by rw [u9.mem]; exact A) hl
            (by rw [u9.mem]; exact M) hj hk
        refine .inr ⟨_, rfl, n10, .cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (c6.trans (.cons d7 (c8.trans
          (.cons d9 c10)))))))), E10, fun x hx => by rw [fr10 x hx, u9.mem], s10, R10, by rw [r21]; rfl, r18', a010,
          M10, V10, ptAddT_lt _ _⟩

end C3.RV32.Pv
