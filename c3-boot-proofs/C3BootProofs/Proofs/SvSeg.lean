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

/-- `f` applied `k` times: a loop variable after `k` iterations. It is
`Nat.rec`, so the kernel unfolds `svIter f (k + 1) a` to `svIter f k (f a)`
in one step. -/
noncomputable def svIter {α : Type} (f : α → α) (k : Nat) (a : α) : α :=
  Nat.rec (motive := fun _ => α → α) (fun a => a) (fun _ ih a => ih (f a)) k a

theorem svIter_zero {α : Type} (f : α → α) (a : α) : svIter f 0 a = a := rfl

theorem svIter_succ {α : Type} (f : α → α) (k : Nat) (a : α) : svIter f (k + 1) a = svIter f k (f a) := rfl

/-- `k` steps of `R` from `a` to `b`: the states of a loop whose step depends
on what it reads. It is `Nat.rec`, like `svIter`. -/
def svChain {α : Type} (R : α → α → Prop) (k : Nat) (a b : α) : Prop :=
  Nat.rec (motive := fun _ => α → Prop) (fun a => a = b) (fun _ ih a => ∃ m, R a m ∧ ih m) k a

theorem svChain.nil {α : Type} {R : α → α → Prop} {a : α} : svChain R 0 a a := rfl

theorem svChain.cons {α : Type} {R : α → α → Prop} {k : Nat} {a m b : α} (h : R a m) (c : svChain R k m b) :
    svChain R (k + 1) a b := ⟨m, h, c⟩

/-- What is left of a slice after an element of at least two bytes. -/
theorem svRem_le {r : Word} {a N : Nat} (h2 : 2 ≤ a) (ha : a ≤ r.toNat) (hN : r.toNat ≤ N + 1) :
    (r - BitVec.ofNat 32 a).toNat ≤ N := by
  have hr := r.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at *
  omega

theorem svRem_zero {r : Word} (h : r.toNat ≤ 0) : r = 0 := BitVec.eq_of_toNat_eq (by simp; omega)

/-- A word inside a byte range copied from `M'`. -/
theorem memLoad32_of_range {M M' : Word → BitVec 8} {S src : Word} {c n d : Nat}
    (h : ∀ j, j < n → M (S + BitVec.ofNat 32 (c + j)) = M' (src + BitVec.ofNat 32 j)) (hd : d + 4 ≤ n) :
    memLoad32 M (S + BitVec.ofNat 32 (c + d)) = memLoad32 M' (src + BitVec.ofNat 32 d) :=
  memLoad32_congr2 fun j hj => by
    rw [add_ofNat_assoc, add_ofNat_assoc, Nat.add_assoc]; exact h (d + j) (by omega)

end C3.RV32.Sv
