/-
TRUSTED. Changes to this file need human review.

The firmware language, version 0: 32-bit globals, expressions, device stores,
`if`, and loops that run a fixed number of times. Every program terminates, and
its meaning is the list of device stores it makes.
-/
import VerifiedFw.RiscV.Machine

namespace VerifiedFw.Lang

open VerifiedFw.RiscV (Word Event)

inductive BinOp where
  | add | sub | and | or | xor
  /-- Shift left by the low five bits of the right operand. -/
  | shl
  /-- Logical shift right by the low five bits of the right operand. -/
  | shr
  /-- Unsigned less-than: 1 if true, otherwise 0. -/
  | ltu
  deriving DecidableEq, Repr

inductive Expr where
  | const (c : Word)
  /-- The global with this index. -/
  | var (i : Nat)
  | bin (op : BinOp) (a b : Expr)
  deriving DecidableEq, Repr

inductive Stmt where
  | skip
  /-- Sets a global. -/
  | assign (i : Nat) (e : Expr)
  /-- Writes a value to a device register. -/
  | store (addr : Word) (e : Expr)
  | seq (a b : Stmt)
  /-- Runs `t` when `c` isn't zero, otherwise `e`. -/
  | ite (c : Expr) (t e : Stmt)
  /-- Runs `body` exactly `n` times. -/
  | loop (n : Nat) (body : Stmt)
  deriving DecidableEq, Repr

structure Program where
  /-- How many globals the program uses. Globals start at zero. -/
  globals : Nat
  body : Stmt
  deriving Repr

end VerifiedFw.Lang
