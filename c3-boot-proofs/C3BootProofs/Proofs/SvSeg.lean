import C3BootProofs.Proofs.SvCongr
import C3BootProofs.Proofs.CondNeg12

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

/-- A part of a loop's state that each step moves by `d`. -/
theorem svIter_add {α : Type} {F : α → α} (g : α → Word) {d : Nat} (h : ∀ s, g (F s) = g s + BitVec.ofNat 32 d) :
    ∀ (i : Nat) (s : α), g (svIter F i s) = g s + BitVec.ofNat 32 (i * d)
  | 0, s => by rw [svIter_zero, Nat.zero_mul]; exact (BitVec.add_zero _).symm
  | i + 1, s => by
    rw [svIter_succ, svIter_add g h i (F s), h s, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.succ_mul, Nat.add_comm d]

/-- A part of a loop's state that each step lowers by 1. -/
theorem svIter_dec1 {α : Type} {F : α → α} (g : α → Word) (h : ∀ s, g (F s) = g s + BitVec.ofNat 32 0xFFFFFFFF) :
    ∀ (i : Nat) (s : α), g (svIter F i s) = g s - BitVec.ofNat 32 i
  | 0, s => by rw [svIter_zero]; exact (BitVec.sub_zero _).symm
  | i + 1, s => by
    rw [svIter_succ, svIter_dec1 g h i (F s), h s]
    bv_omega

theorem svSub_toNat {c : Word} {i : Nat} (h : i ≤ c.toNat) : (c - BitVec.ofNat 32 i).toNat = c.toNat - i := by
  bv_omega

theorem svSub_self_toNat (c : Word) : c - BitVec.ofNat 32 c.toNat = 0 := by
  bv_omega

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

/-- What is left of a slice after a line and its newline. -/
theorem svRem_le1 {r : Word} {a N : Nat} (h1 : 1 ≤ a) (ha : a ≤ r.toNat) (hN : r.toNat ≤ N + 1) :
    (BitVec.ofNat 32 r.toNat - BitVec.ofNat 32 a).toNat ≤ N := by
  bv_omega

theorem svSubOfNat_toNat {r : Word} {a : Nat} (ha : a ≤ r.toNat) :
    (BitVec.ofNat 32 r.toNat - BitVec.ofNat 32 a).toNat = r.toNat - a := by
  bv_omega

theorem svSubNat_toNat {n a : Nat} (hn : n < 2 ^ 32) (ha : a ≤ n) :
    (BitVec.ofNat 32 n - BitVec.ofNat 32 a).toNat = n - a := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega : a < 2 ^ 32)]
  omega

theorem SvIn.len_lt {B p : Word} {n : Nat} (h : SvIn B p n) : n < 2 ^ 31 := by
  have := h.lo; omega

/-- `c - r - 1` in the form the code computes it, `~r + c`, when `r < c`. -/
theorem svNotAdd_le {r c : Word} (h : r.toNat < c.toNat) :
    (aluEval .xor r (BitVec.ofNat 32 0xFFFFFFFF) + c).toNat ≤ c.toNat := by
  have hx : (aluEval .xor r (BitVec.ofNat 32 0xFFFFFFFF)).toNat + r.toNat = 2 ^ 32 - 1 := xor_ones_toNat r
  have hc := c.isLt
  rw [BitVec.toNat_add]
  simp only [Nat.reducePow] at *
  omega

theorem svRem_zero {r : Word} (h : r.toNat ≤ 0) : r = 0 := BitVec.eq_of_toNat_eq (by simp; omega)

/-- A counter that starts at `c0`, that each step moves by `d`, and that isn't
0 after any of the first `N` steps. -/
theorem svCnt_ne {α : Type} {F : α → α} {s : α} {N : Nat} (g : α → Word) (c0 : Word) (d : Nat)
    (h : ∀ s, g (F s) = g s + BitVec.ofNat 32 d) (hs : g s = c0) (hN : ∀ i, i < N → c0 + BitVec.ofNat 32 (i * d) ≠ 0)
    {i : Nat} (hi : i < N) {c' : Word} (hc : c' = g (svIter F i s)) : c' ≠ 0 := by
  rw [hc, svIter_add g h, hs]; exact hN i hi

/-- A counter that starts at `c0`, that each step moves by `d`, and that is 0
after `N` steps. -/
theorem svCnt_zero {α : Type} {F : α → α} {s : α} {N : Nat} (g : α → Word) (c0 : Word) (d : Nat)
    (h : ∀ s, g (F s) = g s + BitVec.ofNat 32 d) (hs : g s = c0) (hN : c0 + BitVec.ofNat 32 (N * d) = 0)
    {c' : Word} (hc : c' = g (svIter F N s)) : c' = 0 := by
  rw [hc, svIter_add g h, hs]; exact hN

/-- What a DER element leaves of a slice is shorter than the slice. -/
theorem svRem_elem {rp rl : Word} {M : Word → BitVec 8} {tag : Nat} {t : DerTlv} {N : Nat}
    (ht : derElement tag (memBytes M rp rl.toNat) = .ok t) (hN : rl.toNat ≤ N + 1) :
    (rl - BitVec.ofNat 32 (t.header + t.len)).toNat ≤ N := by
  rw [rest_len ht]; have := derElement_header ht; omega

/-- A slice without its first `k` bytes, its length written as the code
computes it: adding `2 ^ 32 - k`. -/
theorem SvIn.dropLit {B p : Word} {n k : Nat} (h : SvIn B p n) (hk : k ≤ n) (hk0 : 0 < k) :
    SvIn B (p + BitVec.ofNat 32 k) (BitVec.ofNat 32 n + BitVec.ofNat 32 (0x100000000 - k)).toNat := by
  have := h.fit
  have e : (BitVec.ofNat 32 n + BitVec.ofNat 32 (0x100000000 - k)).toNat = n - k := by bv_omega
  rw [e]; exact h.drop hk

theorem svSll2 (y : Word) : aluEval .sll y (BitVec.ofNat 32 2) = BitVec.ofNat 32 (y.toNat * 4) := by
  show y <<< ((BitVec.ofNat 32 2).toNat % 32) = _
  rw [show (BitVec.ofNat 32 2).toNat % 32 = 2 from rfl]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]

/-- What follows the byte at `c` in a slice, in whole groups of four. -/
theorem SvIn.afterSep {B p L c : Word} {k : Nat} (S : SvIn B p L.toNat) (hk : k < L.toNat)
    (hc : c = BitVec.ofNat 32 0x0 + BitVec.ofNat 32 (k * 1)) :
    SvIn B (p + (c + BitVec.ofNat 32 0x1)) (((L - (c + BitVec.ofNat 32 0x1)) >>> 2).toNat * 4) := by
  subst hc
  have hf := S.fit
  rw [show p + (BitVec.ofNat 32 0x0 + BitVec.ofNat 32 (k * 1) + BitVec.ofNat 32 0x1) = p + BitVec.ofNat 32 (k + 1) by
    bv_omega]
  exact (S.drop (k := k + 1) (by omega)).shrink (by bv_omega)

/-- The bytes before the one at `c` in a slice. -/
theorem SvIn.beforeSep {B p L c : Word} {k : Nat} (S : SvIn B p L.toNat) (hk : k < L.toNat)
    (hc : c = BitVec.ofNat 32 0x0 + BitVec.ofNat 32 (k * 1)) : SvIn B p c.toNat := by
  subst hc
  have hf := S.fit
  exact S.shrink (by bv_omega)

/-- What follows the byte at `c` in a slice. -/
theorem SvIn.afterSepAll {B p L c : Word} {k : Nat} (S : SvIn B p L.toNat) (hk : k < L.toNat)
    (hc : c = BitVec.ofNat 32 0x0 + BitVec.ofNat 32 (k * 1)) :
    SvIn B (p + (c + BitVec.ofNat 32 0x1)) (L - (c + BitVec.ofNat 32 0x1)).toNat := by
  subst hc
  have hf := S.fit
  rw [show p + (BitVec.ofNat 32 0x0 + BitVec.ofNat 32 (k * 1) + BitVec.ofNat 32 0x1) = p + BitVec.ofNat 32 (k + 1) by
    bv_omega, show (L - (BitVec.ofNat 32 0x0 + BitVec.ofNat 32 (k * 1) + BitVec.ofNat 32 0x1)).toNat = L.toNat - (k + 1) by
    bv_omega]
  exact S.drop (k := k + 1) (by omega)

/-- A word inside a byte range copied from `M'`. -/
theorem memLoad32_of_range {M M' : Word → BitVec 8} {S src : Word} {c n d : Nat}
    (h : ∀ j, j < n → M (S + BitVec.ofNat 32 (c + j)) = M' (src + BitVec.ofNat 32 j)) (hd : d + 4 ≤ n) :
    memLoad32 M (S + BitVec.ofNat 32 (c + d)) = memLoad32 M' (src + BitVec.ofNat 32 d) :=
  memLoad32_congr2 fun j hj => by
    rw [add_ofNat_assoc, add_ofNat_assoc, Nat.add_assoc]; exact h (d + j) (by omega)

end C3.RV32.Sv
