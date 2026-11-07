/-
TRUSTED. Changes to this file need human review.

What a program means. `Program.trace` is the reference every compiler
theorem is stated against.
-/
import VerifiedFw.Lang.Syntax

namespace VerifiedFw.Lang

open VerifiedFw.RiscV (Word Event)

def BinOp.eval : BinOp → Word → Word → Word
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => a <<< (b.toNat % 32)
  | .shr, a, b => a >>> (b.toNat % 32)
  | .ltu, a, b => if a < b then 1 else 0

def Expr.eval (g : Nat → Word) : Expr → Word
  | .const c => c
  | .var i => g i
  | .bin op a b => op.eval (a.eval g) (b.eval g)

structure State where
  vars : Nat → Word
  /-- Device stores so far, oldest first. -/
  trace : List Event

def Stmt.run : Stmt → State → State
  | .skip, s => s
  | .assign i e, s => { s with vars := fun j => if j = i then e.eval s.vars else s.vars j }
  | .store a e, s => { s with trace := s.trace ++ [⟨a, e.eval s.vars⟩] }
  | .seq a b, s => b.run (a.run s)
  | .ite c t e, s => if c.eval s.vars ≠ 0 then t.run s else e.run s
  | .loop n body, s => Nat.repeat body.run n s

def State.init : State := ⟨fun _ => 0, []⟩

/-- Every device store the program makes, in order. -/
def Program.trace (p : Program) : List Event := (p.body.run State.init).trace

end VerifiedFw.Lang
