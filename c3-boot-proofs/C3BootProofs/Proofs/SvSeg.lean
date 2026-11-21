import C3BootProofs.Proofs.SvCongr

/-!
# `sigstore::verify`: lemmas for composing stages

The composed segments (`scripts/svseg.py`, `scripts/gen-sv-p256*.py`) carry
an error return of a later stage back to the segment's start.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3

theorem SvErrRet.pre {B out : Word} {v : Nat → Word} {n0 n1 : Machine} (h : Steps n0 n1)
    (h3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32)) (h4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32))
    (hm : ∀ x, SvR B x → n1.mem x = n0.mem x) (e : SvErrRet B out v n1) : SvErrRet B out v n0 := by
  obtain ⟨n', s, pc, sp', sv, r3, r4, o, m⟩ := e
  exact ⟨n', h.trans s, pc, sp', sv, r3.trans h3, r4.trans h4, o, fun x hx h1 h2 => (m x hx h1 h2).trans (hm x hx)⟩

/-- A word inside a byte range copied from `M'`. -/
theorem memLoad32_of_range {M M' : Word → BitVec 8} {S src : Word} {c n d : Nat}
    (h : ∀ j, j < n → M (S + BitVec.ofNat 32 (c + j)) = M' (src + BitVec.ofNat 32 j)) (hd : d + 4 ≤ n) :
    memLoad32 M (S + BitVec.ofNat 32 (c + d)) = memLoad32 M' (src + BitVec.ofNat 32 d) :=
  memLoad32_congr2 fun j hj => by
    rw [add_ofNat_assoc, add_ofNat_assoc, Nat.add_assoc]; exact h (d + j) (by omega)

end C3.RV32.Sv
