/-
A program for QEMU's `virt` board that prints over the UART, then stops QEMU.
CI runs the compiled image and checks the UART output against `trace`.
-/
import VerifiedFw.Targets

namespace VerifiedFw.Examples

open VerifiedFw.RiscV VerifiedFw.Lang VerifiedFw.Targets.QemuVirt

def seqs : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: ss => .seq s (seqs ss)

def putc (c : Char) : Stmt := .store uartTx (.const (.ofNat 32 c.toNat))

def print (s : String) : Stmt := seqs (s.toList.map putc)

/-- Prints the digits 0 through 9, with a `*` after each odd one, using global 0
as the counter. -/
def counter : Program where
  globals := 1
  body := seqs [
    print "verified-fw: ",
    .loop 10 (seqs [
      .store uartTx (.bin .add (.var 0) (.const 0x30)),
      .ite (.bin .and (.var 0) (.const 1)) (putc '*') .skip,
      .assign 0 (.bin .add (.var 0) (.const 1))]),
    putc '\n',
    .store finisher (.const finishPass)]

/-- What the UART should print: the low byte of every store to it. -/
def uartText (trace : List Event) : String :=
  String.ofList ((trace.filter (·.addr == uartTx)).map fun e => Char.ofNat (e.val.toNat % 256))

end VerifiedFw.Examples
