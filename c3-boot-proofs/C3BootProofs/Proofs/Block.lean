import C3BootProofs.Proofs.Outlined
import C3BootProofs.Proofs.ReaderU32

/-!
# Straight-line blocks

`St.block` runs a list of instructions that fall through (ALU operations,
`lui`, word and byte loads, and word and byte stores) as one step of a
proof. `blockEnd` checks, by `decide`, that the code holds the list at an
offset, `runBlock` gives memory and registers after it, and `BlockOk` collects
what each instruction needs: an aligned word access, and a store apart from
the code.
-/

namespace C3.RV32

abbrev s5 : Fin 32 := 21
abbrev s6 : Fin 32 := 22
abbrev s7 : Fin 32 := 23
abbrev s8 : Fin 32 := 24
abbrev s9 : Fin 32 := 25
abbrev s10 : Fin 32 := 26
abbrev s11 : Fin 32 := 27

/-- An instruction that falls through to the next. -/
inductive BInstr where
  | aluImm (op : AluOp) (rd rs1 : Fin 32) (imm : Word)
  | alu (op : AluOp) (rd rs1 rs2 : Fin 32)
  | lui (rd : Fin 32) (imm : Word)
  | lw (rd rs1 : Fin 32) (o : Word)
  | lbu (rd rs1 : Fin 32) (o : Word)
  | sw (rs1 rs2 : Fin 32) (o : Word)
  | sb (rs1 rs2 : Fin 32) (o : Word)

def BInstr.toInstr : BInstr → Instr
  | .aluImm op rd rs1 imm => .aluImm op rd rs1 imm
  | .alu op rd rs1 rs2 => .alu op rd rs1 rs2
  | .lui rd imm => .lui rd imm
  | .lw rd rs1 o => .load .lw rd rs1 o
  | .lbu rd rs1 o => .load .lbu rd rs1 o
  | .sw rs1 rs2 o => .store .sw rs1 rs2 o
  | .sb rs1 rs2 o => .store .sb rs1 rs2 o

/-- Memory and registers. -/
abbrev BState := (Word → BitVec 8) × (Fin 32 → Word)

def BInstr.run : BInstr → BState → BState
  | .aluImm op rd rs1 imm, (M, f) => (M, upd f rd (aluEval op (f rs1) imm))
  | .alu op rd rs1 rs2, (M, f) => (M, upd f rd (aluEval op (f rs1) (f rs2)))
  | .lui rd imm, (M, f) => (M, upd f rd imm)
  | .lw rd rs1 o, (M, f) => (M, upd f rd (memLoad32 M (f rs1 + o)))
  | .lbu rd rs1 o, (M, f) => (M, upd f rd ((M (f rs1 + o)).zeroExtend 32))
  | .sw rs1 rs2 o, (M, f) => (memStore32 M (f rs1 + o) (f rs2), f)
  | .sb rs1 rs2 o, (M, f) => (memStore8 M (f rs1 + o) ((f rs2).extractLsb' 0 8), f)

def runBlock : List BInstr → BState → BState
  | [], s => s
  | i :: is, s => runBlock is (i.run s)

theorem runBlock_append : ∀ (a b : List BInstr) (s : BState), runBlock (a ++ b) s = runBlock b (runBlock a s)
  | [], _, _ => rfl
  | i :: a, b, s => runBlock_append a b (i.run s)

/-- What one instruction needs: aligned word accesses, and stores apart from
the `len` bytes of code at `base`. -/
def BInstr.ok (base : Word) (len : Nat) : BInstr → BState → Prop
  | .lw _ rs1 o, (_, f) => (f rs1 + o).toNat % 4 = 0
  | .sw rs1 _ o, (_, f) => (f rs1 + o).toNat % 4 = 0 ∧ Sep (f rs1 + o) 4 base len
  | .sb rs1 _ o, (_, f) => Sep (f rs1 + o) 1 base len
  | _, _ => True

def BlockOk (base : Word) (len : Nat) : List BInstr → BState → Prop
  | [], _ => True
  | i :: is, s => i.ok base len s ∧ BlockOk base len is (i.run s)

/-- The offset after `is`, when `code` holds them from `off`. -/
def blockEnd (code : List Nat) : Nat → List BInstr → Option Nat
  | off, [] => some off
  | off, i :: is =>
    match fetchRel code off with
    | some (j, l) => if j = i.toInstr then blockEnd code (off + l.toNat) is else none
    | none => none

theorem CodeIn.run {M : Word → BitVec 8} {base : Word} {code : List Nat} {f : Fin 32 → Word}
    (i : BInstr) (hc : CodeIn M base code) (hok : i.ok base code.length (M, f)) :
    CodeIn (i.run (M, f)).1 base code := by
  cases i <;> simp only [BInstr.run] <;> try exact hc
  · exact hc.store32 hok.2
  · exact hc.store8 hok

theorem St.step1 {M : Word → BitVec 8} {base : Word} {code : List Nat} {m : Machine} {off : Nat}
    {f : Fin 32 → Word} (s : St M base m off f) (hc : CodeIn M base code) (i : BInstr) {l : Word}
    (hf : fetchRel code off = some (i.toInstr, l)) (hok : i.ok base code.length (M, f)) :
    ∃ m', step m = some m' ∧ St (i.run (M, f)).1 base m' (off + l.toNat) (i.run (M, f)).2 := by
  have hn : BitVec.ofNat 32 off + l = BitVec.ofNat 32 (off + l.toNat) := by
    rw [← ofNat_add_ofNat, ofNat_toNat_self]
  cases i with
  | aluImm op rd rs1 imm => exact s.aluImm hc hf hn
  | alu op rd rs1 rs2 => exact s.alu hc hf hn
  | lui rd imm => exact s.lui hc hf hn
  | lw rd rs1 o => exact s.lw hc hf hn hok
  | lbu rd rs1 o => exact s.lbu hc hf hn
  | sw rs1 rs2 o => exact s.sw hc hf hn hok.1
  | sb rs1 rs2 o => exact s.sb hc hf hn

theorem updz {f : Fin 32 → Word} {rd r : Fin 32} {v : Word} (hz : f 0 = 0) (h : r ≠ rd) :
    upd f rd v r = f r := by
  by_cases h0 : r.val = 0
  · have : r = 0 := Fin.ext h0
    subst this; simp [upd, hz]
  · simp [upd, h0, h]

/-- The register a block instruction writes, if any. -/
def BInstr.dst : BInstr → Option (Fin 32)
  | .aluImm _ rd _ _ => some rd
  | .alu _ rd _ _ => some rd
  | .lui rd _ => some rd
  | .lw rd _ _ => some rd
  | .lbu rd _ _ => some rd
  | .sw _ _ _ => none
  | .sb _ _ _ => none

theorem runBlock_reg : ∀ (is : List BInstr) (M : Word → BitVec 8) (f : Fin 32 → Word) (q : Fin 32),
    f 0 = 0 → q ∉ is.filterMap BInstr.dst → (runBlock is (M, f)).2 q = f q
  | [], _, _, _, _, _ => rfl
  | i :: is, M, f, q, hz, hq => by
    cases i with
    | aluImm op rd rs1 imm =>
      have h1 : q ≠ rd := fun e => hq (by rw [e, List.filterMap_cons]; exact List.mem_cons_self)
      have h2 : q ∉ is.filterMap BInstr.dst := fun h => hq (by rw [List.filterMap_cons]; exact List.mem_cons_of_mem _ h)
      exact (runBlock_reg is M _ q (upd_zero _ _ _) h2).trans (updz hz h1)
    | alu op rd rs1 rs2 =>
      have h1 : q ≠ rd := fun e => hq (by rw [e, List.filterMap_cons]; exact List.mem_cons_self)
      have h2 : q ∉ is.filterMap BInstr.dst := fun h => hq (by rw [List.filterMap_cons]; exact List.mem_cons_of_mem _ h)
      exact (runBlock_reg is M _ q (upd_zero _ _ _) h2).trans (updz hz h1)
    | lui rd imm =>
      have h1 : q ≠ rd := fun e => hq (by rw [e, List.filterMap_cons]; exact List.mem_cons_self)
      have h2 : q ∉ is.filterMap BInstr.dst := fun h => hq (by rw [List.filterMap_cons]; exact List.mem_cons_of_mem _ h)
      exact (runBlock_reg is M _ q (upd_zero _ _ _) h2).trans (updz hz h1)
    | lw rd rs1 o =>
      have h1 : q ≠ rd := fun e => hq (by rw [e, List.filterMap_cons]; exact List.mem_cons_self)
      have h2 : q ∉ is.filterMap BInstr.dst := fun h => hq (by rw [List.filterMap_cons]; exact List.mem_cons_of_mem _ h)
      exact (runBlock_reg is _ _ q (upd_zero _ _ _) h2).trans (updz hz h1)
    | lbu rd rs1 o =>
      have h1 : q ≠ rd := fun e => hq (by rw [e, List.filterMap_cons]; exact List.mem_cons_self)
      have h2 : q ∉ is.filterMap BInstr.dst := fun h => hq (by rw [List.filterMap_cons]; exact List.mem_cons_of_mem _ h)
      exact (runBlock_reg is _ _ q (upd_zero _ _ _) h2).trans (updz hz h1)
    | sw rs1 rs2 o =>
      exact runBlock_reg is _ f q hz (fun h => hq (by rw [List.filterMap_cons]; exact h))
    | sb rs1 rs2 o =>
      exact runBlock_reg is _ f q hz (fun h => hq (by rw [List.filterMap_cons]; exact h))

/-- **A block runs as one step.** -/
theorem St.block {base : Word} {code : List Nat} :
    ∀ (is : List BInstr) {M : Word → BitVec 8} {m : Machine} {off off' : Nat} {f : Fin 32 → Word},
      St M base m off f → CodeIn M base code → blockEnd code off is = some off' →
      BlockOk base code.length is (M, f) →
      ∃ m', Steps m m' ∧ St (runBlock is (M, f)).1 base m' off' (runBlock is (M, f)).2
  | [], M, m, off, off', f, s, _, he, _ => by
    simp only [blockEnd, Option.some.injEq] at he
    subst he; exact ⟨m, .refl _, s⟩
  | i :: is, M, m, off, off', f, s, hc, he, hok => by
    simp only [blockEnd] at he
    split at he
    · rename_i j l hf
      split at he
      · rename_i hj
        subst hj
        obtain ⟨m1, e1, t1⟩ := s.step1 hc i hf hok.1
        have hc1 := CodeIn.run i hc hok.1
        obtain ⟨m2, c2, t2⟩ := St.block is t1 hc1 he hok.2
        exact ⟨m2, .cons e1 c2, t2⟩
      · cases he
    · cases he

/-- Stores of each register of `ps` at its offset from `sp`, in order: a
prologue's register saves. -/
def saveBlock (ps : List (Fin 32 × Word)) : List BInstr := ps.map fun p => .sw sp p.1 p.2

/-- Loads of each register of `ps` from its offset from `sp`, in order: an
epilogue's register restores. -/
def restoreBlock (ps : List (Fin 32 × Word)) : List BInstr := ps.map fun p => .lw p.1 sp p.2

theorem saveBlock_run (f : Fin 32 → Word) :
    ∀ (ps : List (Fin 32 × Word)) (M : Word → BitVec 8), runBlock (saveBlock ps) (M, f) = (saveMem M (f sp) f ps, f)
  | [], _ => rfl
  | (_, _) :: ps, _ => saveBlock_run f ps _

theorem saveBlock_ok {base : Word} {len : Nat} (f : Fin 32 → Word) :
    ∀ (ps : List (Fin 32 × Word)) (M : Word → BitVec 8),
      (∀ p ∈ ps, (f sp + p.2).toNat % 4 = 0 ∧ Sep (f sp + p.2) 4 base len) → BlockOk base len (saveBlock ps) (M, f)
  | [], _, _ => trivial
  | (r, o) :: ps, _, h => ⟨h (r, o) List.mem_cons_self,
      saveBlock_ok f ps _ fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

theorem restoreBlock_run (M : Word → BitVec 8) (G : Word) :
    ∀ (ps : List (Fin 32 × Word)) (f : Fin 32 → Word), f sp = G → (∀ p ∈ ps, p.1 ≠ sp) →
      runBlock (restoreBlock ps) (M, f) = (M, restoreRegs M G f ps)
  | [], _, _, _ => rfl
  | (r, o) :: ps, f, hG, h => by
    have hr : r ≠ sp := h (r, o) List.mem_cons_self
    have e : upd f r (memLoad32 M (f sp + o)) sp = G := by
      rw [← hG]; exact upd_ne (by decide) (Ne.symm hr)
    show runBlock (restoreBlock ps) (M, upd f r (memLoad32 M (f sp + o))) = _
    rw [restoreBlock_run M G ps _ e fun q hq => h q (List.mem_cons_of_mem _ hq), hG]
    rfl

theorem restoreBlock_ok {base : Word} {len : Nat} (M : Word → BitVec 8) (G : Word) :
    ∀ (ps : List (Fin 32 × Word)) (f : Fin 32 → Word), f sp = G → (∀ p ∈ ps, p.1 ≠ sp) →
      (∀ p ∈ ps, (G + p.2).toNat % 4 = 0) → BlockOk base len (restoreBlock ps) (M, f)
  | [], _, _, _, _ => trivial
  | (r, o) :: ps, f, hG, h, ha => by
    have hr : r ≠ sp := h (r, o) List.mem_cons_self
    refine ⟨by show (f sp + o).toNat % 4 = 0; rw [hG]; exact ha (r, o) List.mem_cons_self, ?_⟩
    refine restoreBlock_ok M G ps _ ?_ (fun q hq => h q (List.mem_cons_of_mem _ hq))
      (fun q hq => ha q (List.mem_cons_of_mem _ hq))
    show upd f r (memLoad32 M (f sp + o)) sp = G
    rw [← hG]; exact upd_ne (by decide) (Ne.symm hr)

end C3.RV32
