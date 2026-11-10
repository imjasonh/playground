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

end C3.RV32
