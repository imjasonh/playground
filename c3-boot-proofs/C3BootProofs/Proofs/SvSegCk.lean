import C3BootProofs.Proofs.SvCkpt
import C3BootProofs.Proofs.SvSeg

/-!
# `sigstore::verify`: slices of the checkpoint's lines

A newline that `nlScan` finds splits a slice into the line before it and the
rest after it.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3

theorem SvIn.nlRest {B p : Word} {n i : Nat} {M : Word → BitVec 8} (h : SvIn B p n)
    (hs : nlScan M p 0 n = some i) : SvIn B (p + BitVec.ofNat 32 (i + 1)) (n - (i + 1)) :=
  h.drop (by have := nlScan_lt n 0 i hs; omega)

theorem SvIn.nlLine {B p : Word} {n i : Nat} {M : Word → BitVec 8} (h : SvIn B p n)
    (hs : nlScan M p 0 n = some i) : SvIn B p i :=
  h.shrink (by have := nlScan_lt n 0 i hs; omega)

end C3.RV32.Sv
