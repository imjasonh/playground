import C3BootProofs.Proofs.SliceEq
import C3BootProofs.Proofs.Arr32Eq
import C3BootProofs.Proofs.CheckpointLine
import C3BootProofs.Proofs.Block

/-!
# Steps toward a postcondition

`WP code base Q M off f` says that a machine at offset `off` of `code` at
`base`, with memory `M` and registers `f`, runs to a machine whose pc,
memory, and registers satisfy `Q`. Each lemma here reduces `WP` at one
instruction to `WP` at the next, so a proof of a function walks its code
from the entry and each step leaves the next state as the goal. A call
leaves the machine at the callee's entry, for the callee's theorem, and
`WP.resume` picks the walk up again after it returns.

The JSON proofs use this file.
-/

namespace C3.RV32

/-- `M` with the little-endian halfword at `a` set to the low half of `v`,
as `sh` sets it. -/
def memStore16 (M : Word → BitVec 8) (a : Word) (v : Word) : Word → BitVec 8 :=
  memStore8 (memStore8 M a (v.extractLsb' 0 8)) (a + 1) (v.extractLsb' 8 8)

theorem CodeIn.store16 {M : Word → BitVec 8} {base a : Word} {code : List Nat} {v : Word}
    (hc : CodeIn M base code) (h : Sep a 2 base code.length) :
    CodeIn (memStore16 M a v) base code := by
  unfold memStore16
  have h0 : Sep a 1 base code.length := by
    have := h.shift (c := 0) (by decide)
    rwa [add_ofNat_zero] at this
  exact (hc.store8 h0).store8 (h.shift (c := 1) (by decide))

/-- What a function's caller sees when it returns: the pc, the memory, and
the registers. -/
abbrev Post := Word → (Word → BitVec 8) → (Fin 32 → Word) → Prop

/-- From offset `off` of `code` at `base`, with memory `M` and registers
`f`, the machine runs to a state that satisfies `Q`. -/
def WP (code : List Nat) (base : Word) (Q : Post) (M : Word → BitVec 8) (off : Nat)
    (f : Fin 32 → Word) : Prop :=
  base.toNat % 2 = 0 → CodeIn M base code → ∀ m, St M base m off f →
    ∃ m', Steps m m' ∧ Q m'.pc m'.mem (reg m')

theorem ofNat_next (off : Nat) (l : Word) : BitVec.ofNat 32 off + l = BitVec.ofNat 32 (off + l.toNat) := by
  rw [← ofNat_add_ofNat, ofNat_toNat_self]

theorem ofNat_target (off : Nat) (o : Word) :
    BitVec.ofNat 32 off + o = BitVec.ofNat 32 ((off + o.toNat) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_add_mod]

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat}
  {f : Fin 32 → Word}

/-- A machine at the entry of `code` runs to `Q`. -/
theorem WP.run {m : Machine} (k : WP code base Q m.mem 0 (reg m)) (hb : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base code) (hpc : m.pc = base) : ∃ m', Steps m m' ∧ Q m'.pc m'.mem (reg m') :=
  k hb hc m ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩

/-- After a call returns to offset `off`, the walk goes on from there. -/
theorem WP.resume {m1 m2 : Machine} {g : Fin 32 → Word} (c : Steps m1 m2)
    (hpc : m2.pc = base + BitVec.ofNat 32 off) (hg : ∀ r, reg m2 r = g r) (hb : base.toNat % 2 = 0)
    (hc : CodeIn m2.mem base code) (k : WP code base Q m2.mem off g) :
    ∃ m', Steps m1 m' ∧ Q m'.pc m'.mem (reg m') := by
  obtain ⟨m', c', q'⟩ := k hb hc m2 ⟨hpc, rfl, hg⟩
  exact ⟨m', c.trans c', q'⟩

theorem WP.congr {g : Fin 32 → Word} (h : ∀ r, f r = g r) (k : WP code base Q M off g) :
    WP code base Q M off f := by
  rw [show f = g from funext h]; exact k

theorem WP.zero (k : f 0 = 0 → WP code base Q M off f) : WP code base Q M off f :=
  fun hb hc m s => k s.zero hb hc m s

theorem WP.aluImm {op : AluOp} {rd rs1 : Fin 32} {imm l : Word}
    (h : fetchRel code off = some (.aluImm op rd rs1 imm, l))
    (k : WP code base Q M (off + l.toNat) (upd f rd (aluEval op (f rs1) imm))) : WP code base Q M off f := by
  intro hb hc m s
  obtain ⟨m1, e1, s1⟩ := s.aluImm hc h (ofNat_next off l)
  obtain ⟨m2, c2, q2⟩ := k hb hc m1 s1
  exact ⟨m2, .cons e1 c2, q2⟩

theorem WP.alu {op : AluOp} {rd rs1 rs2 : Fin 32} {l : Word}
    (h : fetchRel code off = some (.alu op rd rs1 rs2, l))
    (k : WP code base Q M (off + l.toNat) (upd f rd (aluEval op (f rs1) (f rs2)))) : WP code base Q M off f := by
  intro hb hc m s
  obtain ⟨m1, e1, s1⟩ := s.alu hc h (ofNat_next off l)
  obtain ⟨m2, c2, q2⟩ := k hb hc m1 s1
  exact ⟨m2, .cons e1 c2, q2⟩

theorem WP.lui {rd : Fin 32} {imm l : Word} (h : fetchRel code off = some (.lui rd imm, l))
    (k : WP code base Q M (off + l.toNat) (upd f rd imm)) : WP code base Q M off f := by
  intro hb hc m s
  obtain ⟨m1, e1, s1⟩ := s.lui hc h (ofNat_next off l)
  obtain ⟨m2, c2, q2⟩ := k hb hc m1 s1
  exact ⟨m2, .cons e1 c2, q2⟩

theorem WP.lbu {rd rs1 : Fin 32} {o l : Word} (h : fetchRel code off = some (.load .lbu rd rs1 o, l))
    (k : WP code base Q M (off + l.toNat) (upd f rd ((M (f rs1 + o)).zeroExtend 32))) :
    WP code base Q M off f := by
  intro hb hc m s
  obtain ⟨m1, e1, s1⟩ := s.lbu hc h (ofNat_next off l)
  obtain ⟨m2, c2, q2⟩ := k hb hc m1 s1
  exact ⟨m2, .cons e1 c2, q2⟩

theorem WP.lw {rd rs1 : Fin 32} {o l : Word} (h : fetchRel code off = some (.load .lw rd rs1 o, l))
    (ha : (f rs1 + o).toNat % 4 = 0)
    (k : WP code base Q M (off + l.toNat) (upd f rd (memLoad32 M (f rs1 + o)))) : WP code base Q M off f := by
  intro hb hc m s
  obtain ⟨m1, e1, s1⟩ := s.lw hc h (ofNat_next off l) ha
  obtain ⟨m2, c2, q2⟩ := k hb hc m1 s1
  exact ⟨m2, .cons e1 c2, q2⟩

theorem WP.sw {rs1 rs2 : Fin 32} {o l : Word} (h : fetchRel code off = some (.store .sw rs1 rs2 o, l))
    (ha : (f rs1 + o).toNat % 4 = 0) (hs : Sep (f rs1 + o) 4 base code.length)
    (k : WP code base Q (memStore32 M (f rs1 + o) (f rs2)) (off + l.toNat) f) : WP code base Q M off f := by
  intro hb hc m s
  obtain ⟨m1, e1, s1⟩ := s.sw hc h (ofNat_next off l) ha
  obtain ⟨m2, c2, q2⟩ := k hb (hc.store32 hs) m1 s1
  exact ⟨m2, .cons e1 c2, q2⟩

theorem WP.sb {rs1 rs2 : Fin 32} {o l : Word} (h : fetchRel code off = some (.store .sb rs1 rs2 o, l))
    (hs : Sep (f rs1 + o) 1 base code.length)
    (k : WP code base Q (memStore8 M (f rs1 + o) ((f rs2).extractLsb' 0 8)) (off + l.toNat) f) :
    WP code base Q M off f := by
  intro hb hc m s
  obtain ⟨m1, e1, s1⟩ := s.sb hc h (ofNat_next off l)
  obtain ⟨m2, c2, q2⟩ := k hb (hc.store8 hs) m1 s1
  exact ⟨m2, .cons e1 c2, q2⟩

theorem WP.sh {rs1 rs2 : Fin 32} {o l : Word} (h : fetchRel code off = some (.store .sh rs1 rs2 o, l))
    (ha : (f rs1 + o).toNat % 2 = 0) (hs : Sep (f rs1 + o) 2 base code.length)
    (k : WP code base Q (memStore16 M (f rs1 + o) (f rs2)) (off + l.toNat) f) :
    WP code base Q M off f := by
  intro hb hc m s
  obtain ⟨m1, e1, s1⟩ := s.sh hc h (ofNat_next off l) ha
  obtain ⟨m2, c2, q2⟩ := k hb (hc.store16 hs) m1 (by unfold memStore16; exact s1)
  exact ⟨m2, .cons e1 c2, q2⟩

theorem WP.auipc {rd : Fin 32} {imm l : Word} (h : fetchRel code off = some (.auipc rd imm, l))
    (k : WP code base Q M (off + l.toNat) (upd f rd (base + BitVec.ofNat 32 off + imm))) :
    WP code base Q M off f := by
  intro hb hc m s
  obtain ⟨m1, e1, s1⟩ := s.auipc hc h (ofNat_next off l)
  obtain ⟨m2, c2, q2⟩ := k hb hc m1 s1
  exact ⟨m2, .cons e1 c2, q2⟩

theorem WP.branch {op : BranchOp} {rs1 rs2 : Fin 32} {o l : Word}
    (h : fetchRel code off = some (.branch op rs1 rs2 o, l))
    (kt : branchTaken op (f rs1) (f rs2) = true → WP code base Q M ((off + o.toNat) % 2 ^ 32) f)
    (kf : branchTaken op (f rs1) (f rs2) = false → WP code base Q M (off + l.toNat) f) :
    WP code base Q M off f := by
  intro hb hc m s
  cases e : branchTaken op (f rs1) (f rs2)
  · obtain ⟨m1, e1, s1⟩ := s.notTaken hc _ h (ofNat_next off l) e
    obtain ⟨m2, c2, q2⟩ := kf e hb hc m1 s1
    exact ⟨m2, .cons e1 c2, q2⟩
  · obtain ⟨m1, e1, s1⟩ := s.taken hc _ h (ofNat_target off o) e
    obtain ⟨m2, c2, q2⟩ := kt e hb hc m1 s1
    exact ⟨m2, .cons e1 c2, q2⟩

theorem WP.jal {o l : Word} (h : fetchRel code off = some (.jal 0 o, l))
    (hev : (off + o.toNat) % 2 ^ 32 % 2 = 0)
    (k : WP code base Q M ((off + o.toNat) % 2 ^ 32) f) : WP code base Q M off f := by
  intro hb hc m s
  obtain ⟨m1, e1, s1⟩ := s.jump hc h (ofNat_target off o) (by
    rw [s.pc, BitVec.add_assoc, ofNat_target]; exact even_bit0 (even_at base hb _ hev))
  obtain ⟨m2, c2, q2⟩ := k hb hc m1 s1
  exact ⟨m2, .cons e1 c2, q2⟩

/-- The return: `jalr x0, o(rs1)`. -/
theorem WP.ret {rs1 : Fin 32} {o l : Word} (h : fetchRel code off = some (.jalr 0 rs1 o, l))
    (k : Q ((f rs1 + o) &&& ~~~1) M f) : WP code base Q M off f := by
  intro _ hc m s
  obtain ⟨m1, e1, pc1, mem1, regs1⟩ := s.jalr hc h
  refine ⟨m1, .single e1, ?_⟩
  rw [pc1, mem1, show reg m1 = f from funext regs1]; exact k

/-- A call, `auipc ra` and `jalr ra`: the machine is at the callee's entry
with `ra` set to the instruction after the call. -/
theorem WP.call {hi lo : Word} (h1 : fetchRel code off = some (.auipc ra hi, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (k : ∀ m1 : Machine, m1.pc = (base + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 → m1.mem = M →
      (∀ r, reg m1 r = upd f ra (base + BitVec.ofNat 32 (off + 8)) r) → base.toNat % 2 = 0 →
      CodeIn M base code → ∃ m', Steps m1 m' ∧ Q m'.pc m'.mem (reg m')) :
    WP code base Q M off f := by
  intro hb hc m s
  obtain ⟨m1, e1, t1⟩ := s.auipc hc h1 (off' := off + 4) (ofNat_add_ofNat off 4)
  obtain ⟨m2, e2, pc2, mem2, regs2⟩ := t1.call hc h2
  have hL : base + BitVec.ofNat 32 (off + 4) + 4 = base + BitVec.ofNat 32 (off + 8) := by
    rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  obtain ⟨m3, c3, q3⟩ := k m2 (by rw [pc2]; simp +decide only [upd_app, ↓reduceIte]) mem2 (fun r => by
    rw [regs2, hL]
    by_cases hr : r.val = 0
    · simp [upd, hr]
    · by_cases h : r = ra
      · subst h; simp [upd]
      · simp [upd, hr, h]) hb hc
  exact ⟨m3, .cons e1 (.cons e2 c3), q3⟩

end

theorem beq_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a == BitVec.ofNat 32 b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; rw [beq_iff_eq.mpr rfl, decide_eq_true rfl]
  · rw [decide_eq_false h]
    exact beq_eq_false_iff_ne.mpr fun e => h (by
      have := congrArg BitVec.toNat e; rwa [ofNat_tn ha, ofNat_tn hb] at this)

theorem br_beq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    branchTaken .beq (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = decide (a = b) := beq_ofNat ha hb

theorem br_bne {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    branchTaken .bne (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = !decide (a = b) := by
  show (!(BitVec.ofNat 32 a == BitVec.ofNat 32 b)) = _
  rw [beq_ofNat ha hb]

theorem br_beq0 {a : Nat} (ha : a < 2 ^ 32) :
    branchTaken .beq (BitVec.ofNat 32 a) 0 = decide (a = 0) := br_beq ha (by decide)

theorem br_bne0 {a : Nat} (ha : a < 2 ^ 32) :
    branchTaken .bne (BitVec.ofNat 32 a) 0 = !decide (a = 0) := br_bne ha (by decide)

theorem br_bltu {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    branchTaken .bltu (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = decide (a < b) := by
  simp only [branchTaken, BitVec.ult, ofNat_tn ha, ofNat_tn hb]

theorem br_bgeu {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    branchTaken .bgeu (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = !decide (a < b) := by
  simp only [branchTaken, BitVec.ult, ofNat_tn ha, ofNat_tn hb]

theorem sub_ofNat_le {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, ofNat_tn ha, ofNat_tn (by omega), BitVec.toNat_ofNat]
  omega

theorem sub_ofNat_gt {a b : Nat} (h : a < b) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b).toNat = 2 ^ 32 - (b - a) := by
  rw [BitVec.toNat_sub, ofNat_tn hb, ofNat_tn (by omega)]
  omega

theorem ones_and (x : Word) : (0xFFFFFFFF : Word) &&& x = x := by
  have h : ∀ i : Fin 32, (0xFFFFFFFF : Word).getLsbD i.val = true := by decide
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, h ⟨i, hi⟩, Bool.true_and]

theorem one_add_ofNat (i : Nat) : (1 : Word) + BitVec.ofNat 32 i = BitVec.ofNat 32 (i + 1) := by
  rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat, Nat.add_comm]

theorem memBytes_drop (M : Word → BitVec 8) :
    ∀ (k : Nat) (p : Word) (n : Nat), (memBytes M p n).drop k = memBytes M (p + BitVec.ofNat 32 k) (n - k)
  | 0, p, n => by rw [List.drop_zero, add_ofNat_zero, Nat.sub_zero]
  | k + 1, p, 0 => by rw [memBytes_zero, List.drop_nil, Nat.zero_sub, memBytes_zero]
  | k + 1, p, n + 1 => by
    rw [memBytes_succ, List.drop_succ_cons, memBytes_drop M k (p + 1) n, Nat.add_sub_add_right,
      BitVec.add_assoc, one_add_ofNat]

/-- Registers after a call: `cl` holds whatever the callee left, and the
rest keep their values from `f`. -/
def clob (f : Fin 32 → Word) (m : Machine) (cl : List (Fin 32)) : Fin 32 → Word :=
  fun r => if r ∈ cl then reg m r else f r

theorem clob_app (f : Fin 32 → Word) (m : Machine) (cl : List (Fin 32)) (r : Fin 32) :
    clob f m cl r = if r ∈ cl then reg m r else f r := rfl

theorem ite_val_zero {f : Fin 32 → Word} {r : Fin 32} (hz : f 0 = 0) :
    (if r.val = 0 then (0 : Word) else f r) = f r := by
  by_cases h : r.val = 0
  · rw [if_pos h, ← hz, show r = 0 from Fin.ext h]
  · rw [if_neg h]

theorem upd_upd_same (f : Fin 32 → Word) (rd : Fin 32) (v w : Word) :
    upd (upd f rd v) rd w = upd f rd w := by
  funext r
  simp only [upd_app]
  by_cases h0 : r.val = 0
  · simp only [h0, ↓reduceIte]
  · by_cases h : r = rd <;> simp only [h0, h, ↓reduceIte]

/-- Reads registers out of a chain of `upd`s. -/
macro "rsimp" : tactic => `(tactic| simp +decide only [upd_app, clob_app, ↓reduceIte])

/-- `rsimp` in a hypothesis. -/
macro "rsimp" " at " h:ident : tactic =>
  `(tactic| simp +decide only [upd_app, clob_app, ↓reduceIte] at $h:ident)

/-- Reduces the literal offsets that a step leaves, and the register
reads inside the new register values. -/
macro "wn" : tactic => `(tactic| try simp +decide only [upd_app, clob_app, upd_upd_same, ↓reduceIte,
  Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, BitVec.reduceToNat])

end C3.RV32
