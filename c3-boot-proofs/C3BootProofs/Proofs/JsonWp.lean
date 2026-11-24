import C3BootProofs.Proofs.SliceEq
import C3BootProofs.Proofs.Arr32Eq
import C3BootProofs.Proofs.CheckpointLine
import C3BootProofs.Proofs.Block
import C3BootProofs.Proofs.ImageHelpers
import C3BootProofs.Proofs.Outlined
import C3BootProofs.Proofs.CondNeg12

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

theorem not_dec_true {p : Prop} [Decidable p] (h : (!decide p) = true) : ¬p := fun hp => by
  rw [decide_eq_true hp] at h; cases h

theorem not_dec_false {p : Prop} [Decidable p] (h : (!decide p) = false) : p := by
  cases hd : decide p with
  | true => exact of_decide_eq_true hd
  | false => rw [hd] at h; cases h

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

theorem jones_and (x : Word) : (0xFFFFFFFF : Word) &&& x = x := by
  have h : ∀ i : Fin 32, (0xFFFFFFFF : Word).getLsbD i.val = true := by decide
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, h ⟨i, hi⟩, Bool.true_and]

theorem one_add_ofNat (i : Nat) : (1 : Word) + BitVec.ofNat 32 i = BitVec.ofNat 32 (i + 1) := by
  rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat, Nat.add_comm]

theorem jmemBytes_drop (M : Word → BitVec 8) :
    ∀ (k : Nat) (p : Word) (n : Nat), (memBytes M p n).drop k = memBytes M (p + BitVec.ofNat 32 k) (n - k)
  | 0, p, n => by rw [List.drop_zero, add_ofNat_zero, Nat.sub_zero]
  | k + 1, p, 0 => by rw [memBytes_zero, List.drop_nil, Nat.zero_sub, memBytes_zero]
  | k + 1, p, n + 1 => by
    rw [memBytes_succ, List.drop_succ_cons, jmemBytes_drop M k (p + 1) n, Nat.add_sub_add_right,
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
  · simp only [h, ↓reduceIte]; rw [← hz, show r = 0 from Fin.ext h]
  · simp only [h, ↓reduceIte]

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

theorem keepUpd {f g0 : Fin 32 → Word} {cl : List (Fin 32)} {rd : Fin 32} {v : Word} (hz : f 0 = 0)
    (hrd : rd ∈ cl) (hfr : ∀ x, x ∉ cl → f x = g0 x) : ∀ x, x ∉ cl → upd f rd v x = g0 x := by
  intro x hx
  have hne : x ≠ rd := fun e => hx (by rw [e]; exact hrd)
  rw [upd_ne' hne hz]
  exact hfr x hx

/-- Proves `∀ x, x ∉ cl → g x = g0 x` for `g` a chain of `upd`s, each to a
register in `cl`, over a register file that the context says it of. -/
macro "keep" : tactic =>
  `(tactic| ((repeat refine keepUpd (by first | rfl | assumption) (by decide) ?_); try assumption))

/-- Reduces the literal offsets that a step leaves, and the register
reads inside the new register values. -/
macro "wn" : tactic => `(tactic| try simp +decide only [upd_app, clob_app, upd_upd_same, ↓reduceIte,
  Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, BitVec.reduceToNat])

abbrev t2 : Fin 32 := 7

/-- `~a + b` is `b - a - 1` when `a < b`. -/
theorem not_add_ofNat {a b : Nat} (h : a < b) (hb : b < 2 ^ 32) :
    aluEval .add (aluEval .xor (BitVec.ofNat 32 a) 0xFFFFFFFF) (BitVec.ofNat 32 b) =
      BitVec.ofNat 32 (b - a - 1) := by
  have hx := xor_ones_toNat (BitVec.ofNat 32 a)
  rw [ofNat_tn (by omega)] at hx
  apply BitVec.eq_of_toNat_eq
  rw [ev_add, BitVec.toNat_add, ofNat_tn hb, ofNat_tn (by omega)]
  omega

theorem add_ofNat_ne_self (out : Word) {k : Nat} (h0 : 0 < k) (hk : k < 2 ^ 32) :
    out + BitVec.ofNat 32 k ≠ out := by
  have := add_ofNat_ne out (c := k) (d := 0) hk (by decide) (by omega)
  rwa [add_ofNat_zero] at this

theorem sep_byte {x out : Word} {n j : Nat} (h : Sep x 1 out n) (hj : j < n) :
    x ≠ out + BitVec.ofNat 32 j := by
  have := h 0 (by decide) j hj
  rwa [add_ofNat_zero] at this

/-- `out` holds `Ok(v)` (`some v`) or `Err(TufError::Json)` (`none`) as
a `Result<usize, TufError>`: the tag byte at `out`, the error byte after
it, and the value in the word at `out + 4`. No byte outside the 8 at `out`
changed. -/
def UsizeRes (M M' : Word → BitVec 8) (out : Word) : Option Nat → Prop
  | some v => (∀ x, Sep x 1 out 8 → M' x = M x) ∧ M' out = 0 ∧ memLoad32 M' (out + 4) = BitVec.ofNat 32 v
  | none => (∀ x, Sep x 1 out 8 → M' x = M x) ∧ M' out = 1 ∧ M' (out + 1) = 0x20

theorem sep_byte0 {x out : Word} {n : Nat} (h : Sep x 1 out n) (hn : 0 < n) : x ≠ out := by
  have := sep_byte h hn; rwa [add_ofNat_zero] at this

theorem sep_byte1 {x out : Word} {n : Nat} (h : Sep x 1 out n) (hn : 1 < n) : x ≠ out + 1 :=
  sep_byte h hn

theorem ne_add_one (out : Word) : out + 1 ≠ out := add_ofNat_ne_self out (k := 1) (by decide) (by decide)

theorem usizeRes_ok (M : Word → BitVec 8) (out : Word) (v : Nat) :
    UsizeRes M (memStore8 (memStore32 M (out + 4) (BitVec.ofNat 32 v)) out 0) out (some v) := by
  have h4 : Sep out 1 (out + 4) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 4) (k := 4) (Or.inl (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  refine ⟨fun x hx => ?_, memStore8_same _ _ _, ?_⟩
  · rw [memStore8_ne (sep_byte0 hx (by decide)), memStore32_get_sep]
    intro i hi j hj e
    obtain rfl : j = 0 := by omega
    rw [add_ofNat_zero, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc] at e
    exact sep_byte hx (j := 4 + i) (by omega) e.symm
  · rw [memLoad32_store8_sep h4, memLoad32_store32_same]

theorem usizeRes_err (M : Word → BitVec 8) (out : Word) :
    UsizeRes M (memStore8 (memStore8 M (out + 1) 0x20) out 1) out none := by
  refine ⟨fun x hx => ?_, memStore8_same _ _ _, ?_⟩
  · rw [memStore8_ne (sep_byte0 hx (by decide)), memStore8_ne (sep_byte1 hx (by decide))]
  · rw [memStore8_ne (ne_add_one out), memStore8_same]

theorem usizeRes_err16 (M : Word → BitVec 8) (out : Word) : UsizeRes M (memStore16 M out 0x2001) out none := by
  unfold memStore16
  refine ⟨fun x hx => ?_, ?_, memStore8_same _ _ _⟩
  · rw [memStore8_ne (sep_byte1 hx (by decide)), memStore8_ne (sep_byte0 hx (by decide))]
  · rw [memStore8_ne (Ne.symm (ne_add_one out)), memStore8_same]
    rfl

end C3.RV32
