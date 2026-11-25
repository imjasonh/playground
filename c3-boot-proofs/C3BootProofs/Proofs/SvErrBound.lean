import C3BootProofs.Proofs.IsSha256
import C3BootProofs.Proofs.ListsOid
import C3BootProofs.Proofs.IntegerIs

/-!
# `sigstore::verify`: the error codes its callees return

`sigstore::verify` reports a failure as one byte at `out + 1`, and its
caller indexes a table of 0x27 entries with it. The byte always comes from a
callee's `Error`, a `derErrByte`, or a constant. These lemmas bound each
reader's error byte, and `sv_eb` picks the one that applies.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32

theorem derErrByte_lt (e : DerError) : (derErrByte e).toNat < 0x27 := by
  cases e <;> decide

theorem derScalarOf_err_lt {N : Nat} {L : Bytes} {rp : Word} {r : Except DerError DerTlv} {b : BitVec 8}
    (h : derScalarOf N L rp r = .error b) : b.toNat < 0x27 := by
  unfold derScalarOf at h
  revert h
  repeat' split
  all_goals intro h
  all_goals first
    | (simp only [reduceCtorEq] at h)
    | (simp only [Except.error.injEq] at h; subst h; first | decide | exact derErrByte_lt _)

theorem ecdsaSigOf_err_lt {N : Nat} {M : Word → BitVec 8} {p : Word} {n : Nat} {b : BitVec 8}
    (h : ecdsaSigOf N M p n = .error b) : b.toNat < 0x27 := by
  unfold ecdsaSigOf at h
  revert h
  repeat' split
  all_goals intro h
  all_goals first
    | (simp only [reduceCtorEq] at h)
    | (simp only [Except.error.injEq] at h; subst h
       first | decide | exact derErrByte_lt _ | exact derScalarOf_err_lt (by assumption))

theorem derAlgOf_err_lt {M : Word → BitVec 8} {p : Word} {n : Nat} {b : BitVec 8}
    (h : derAlgOf M p n = .error b) : b.toNat < 0x27 := by
  unfold derAlgOf at h
  revert h
  repeat' split
  all_goals intro h
  all_goals first
    | (simp only [reduceCtorEq] at h)
    | (simp only [Except.error.injEq] at h; subst h; first | decide | exact derErrByte_lt _)

theorem isSha256Of_err_lt {M : Word → BitVec 8} {p : Word} {n : Nat} {b : BitVec 8}
    (h : isSha256Of M p n = .error b) : b.toNat < 0x27 := by
  unfold isSha256Of at h
  revert h
  repeat' split
  all_goals intro h
  all_goals first
    | (simp only [reduceCtorEq] at h)
    | (simp only [Except.error.injEq] at h; subst h; exact derAlgOf_err_lt (by assumption))

theorem listsOidLoop_err_lt {M : Word → BitVec 8} {oid : Bytes} :
    ∀ {k : Nat} {p : Word} {n : Nat} {b : BitVec 8}, listsOidLoop M oid k p n = .error b → b.toNat < 0x27
  | 0, _, _, _, h => by simp only [listsOidLoop, reduceCtorEq] at h
  | k + 1, p, n, b, h => by
    unfold listsOidLoop at h
    revert h
    repeat' split
    all_goals intro h
    all_goals first
      | (simp only [reduceCtorEq] at h)
      | (simp only [Except.error.injEq] at h; subst h; exact derErrByte_lt _)
      | exact listsOidLoop_err_lt h

theorem listsOidOf_err_lt {M : Word → BitVec 8} {p : Word} {n : Nat} {oid : Bytes} {b : BitVec 8}
    (h : listsOidOf M p n oid = .error b) : b.toNat < 0x27 := listsOidLoop_err_lt h

theorem derIntIsOf_err_lt {M : Word → BitVec 8} {L : Bytes} {rp : Word} {r : Except DerError DerTlv}
    {v b : BitVec 8} (h : derIntIsOf M L rp r v = .error b) : b.toNat < 0x27 := by
  unfold derIntIsOf at h
  revert h
  repeat' split
  all_goals intro h
  all_goals first
    | (simp only [reduceCtorEq] at h)
    | (simp only [Except.error.injEq] at h; subst h; exact derErrByte_lt _)

/-- Closes `b.toNat < 0x27` for the error byte `b` of the call whose result
is `h`. -/
syntax "sv_eb " term : tactic

macro_rules
  | `(tactic| sv_eb $h) => `(tactic| first
    | exact derErrByte_lt _
    | decide
    | exact ecdsaSigOf_err_lt $h
    | exact derAlgOf_err_lt $h
    | exact isSha256Of_err_lt $h
    | exact listsOidOf_err_lt $h
    | exact derIntIsOf_err_lt $h
    | exact derScalarOf_err_lt $h)

end C3.RV32.Sv
