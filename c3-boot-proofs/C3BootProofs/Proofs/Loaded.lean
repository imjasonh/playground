import C3BootProofs.Proof.Step

/-!
# Byte lists at fixed addresses

`Proofs/LoadedImage` describes the memory that the ROM loader leaves as a
list of pieces, each a byte list at its link address. This file holds what
that description needs and doesn't depend on the image: `PiecesIn`, which
says memory holds every piece, `piecesOk`, a check that the pieces are
sorted, don't overlap, and end below 2^32, and `piecesIn_mem`, which builds
a memory that holds pieces that pass the check, so a hypothesis
`PiecesIn M L` is never vacuous. `PiecesIn.congr` carries the hypothesis to
memory that agrees on the pieces' addresses, and `CodeIn.sub` reads a piece
that lies inside another.
-/

namespace C3.RV32

/-- Memory `M` holds every piece of `L`, each a byte list at its address. -/
def PiecesIn (M : Word → BitVec 8) (L : List (Nat × List Nat)) : Prop :=
  ∀ k (h : k < L.length), CodeIn M (BitVec.ofNat 32 L[k].1) L[k].2

/-- The pieces of `L` are in address order, don't overlap, and end at or
below 2^32. -/
def piecesOk : List (Nat × List Nat) → Bool
  | [] => true
  | [p] => decide (p.1 + p.2.length ≤ 2 ^ 32)
  | p :: q :: l => decide (p.1 + p.2.length ≤ q.1) && piecesOk (q :: l)

/-- Every piece of `L` lies inside the range `[lo, hi)` or `[lo', hi')`. -/
def piecesWithin (lo hi lo' hi' : Nat) (L : List (Nat × List Nat)) : Bool :=
  L.all fun p => (decide (lo ≤ p.1) && decide (p.1 + p.2.length ≤ hi)) ||
    (decide (lo' ≤ p.1) && decide (p.1 + p.2.length ≤ hi'))

/-- A memory that holds the pieces of `L`, and 0 elsewhere. -/
def piecesMem : List (Nat × List Nat) → Word → BitVec 8
  | [] => fun _ => 0
  | p :: l => fun x =>
    if p.1 ≤ x.toNat ∧ x.toNat < p.1 + p.2.length then byteAt p.2 (x.toNat - p.1) else piecesMem l x

theorem pieces_ok_tail {p : Nat × List Nat} {l : List (Nat × List Nat)} (h : piecesOk (p :: l) = true) :
    piecesOk l = true := by
  cases l with
  | nil => rfl
  | cons q l => simp only [piecesOk, Bool.and_eq_true] at h; exact h.2

theorem pieces_ok_end : ∀ {p : Nat × List Nat} {l : List (Nat × List Nat)}, piecesOk (p :: l) = true →
    p.1 + p.2.length ≤ 2 ^ 32
  | p, [], h => by simpa only [piecesOk, decide_eq_true_eq] using h
  | p, q :: l, h => by
    simp only [piecesOk, Bool.and_eq_true, decide_eq_true_eq] at h
    have := pieces_ok_end h.2
    omega

theorem pieces_ok_before : ∀ {p : Nat × List Nat} {l : List (Nat × List Nat)}, piecesOk (p :: l) = true →
    ∀ k (hk : k < l.length), p.1 + p.2.length ≤ l[k].1
  | _, [], _, k, hk => absurd hk (Nat.not_lt_zero k)
  | p, q :: l, h, k, hk => by
    have h' := h
    simp only [piecesOk, Bool.and_eq_true, decide_eq_true_eq] at h'
    cases k with
    | zero => exact h'.1
    | succ k =>
      have := pieces_ok_before h'.2 k (by simp only [List.length_cons] at hk; omega)
      simp only [List.getElem_cons_succ]
      omega

theorem pieces_ok_all : ∀ {L : List (Nat × List Nat)}, piecesOk L = true →
    ∀ k (hk : k < L.length), L[k].1 + L[k].2.length ≤ 2 ^ 32
  | [], _, k, hk => absurd hk (Nat.not_lt_zero k)
  | p :: l, h, k, hk => by
    cases k with
    | zero => exact pieces_ok_end h
    | succ k =>
      simp only [List.getElem_cons_succ]
      exact pieces_ok_all (pieces_ok_tail h) k (by simp only [List.length_cons] at hk; omega)

theorem pieces_addr {a i : Nat} (h : a + i < 2 ^ 32) :
    (BitVec.ofNat 32 a + BitVec.ofNat 32 i).toNat = a + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-- Pieces that pass `piecesOk` fit in one memory. -/
theorem piecesIn_mem : ∀ {L : List (Nat × List Nat)}, piecesOk L = true → PiecesIn (piecesMem L) L
  | [], _, k, hk, _, _ => absurd hk (Nat.not_lt_zero k)
  | p :: l, h, k, hk, i, hi => by
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at hi ⊢
      have e := pieces_addr (a := p.1) (i := i) (by have := pieces_ok_end h; omega)
      simp only [piecesMem]
      rw [ite_eq_left (by rw [e]; exact ⟨Nat.le_add_right _ _, by omega⟩), e, Nat.add_sub_cancel_left]
    | succ k =>
      have hk' : k < l.length := by simp only [List.length_cons] at hk; omega
      simp only [List.getElem_cons_succ] at hi ⊢
      have e := pieces_addr (a := l[k].1) (i := i) (by have := pieces_ok_all (pieces_ok_tail h) k hk'; omega)
      have hb := pieces_ok_before h k hk'
      simp only [piecesMem]
      rw [ite_eq_right (fun hc => by rw [e] at hc; have := hc.2; omega)]
      exact piecesIn_mem (pieces_ok_tail h) k hk' i hi

theorem pieces_within {lo hi lo' hi' : Nat} {L : List (Nat × List Nat)}
    (h : piecesWithin lo hi lo' hi' L = true) (k : Nat) (hk : k < L.length) :
    (lo ≤ L[k].1 ∧ L[k].1 + L[k].2.length ≤ hi) ∨ (lo' ≤ L[k].1 ∧ L[k].1 + L[k].2.length ≤ hi') := by
  have := List.all_eq_true.mp h L[k] (List.getElem_mem hk)
  simpa only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] using this

/-- `PiecesIn` carries over to memory that agrees on the ranges that hold
the pieces. -/
theorem PiecesIn.congr {M M' : Word → BitVec 8} {L : List (Nat × List Nat)} {lo hi lo' hi' : Nat}
    (h : PiecesIn M L) (hw : piecesWithin lo hi lo' hi' L = true) (hb : hi ≤ 2 ^ 32) (hb' : hi' ≤ 2 ^ 32)
    (hx : ∀ x : Word, (lo ≤ x.toNat ∧ x.toNat < hi) ∨ (lo' ≤ x.toNat ∧ x.toNat < hi') → M' x = M x) :
    PiecesIn M' L := fun k hk i hil => by
  have hr := pieces_within hw k hk
  have e := pieces_addr (a := L[k].1) (i := i) (by omega)
  have hx' : (lo ≤ (BitVec.ofNat 32 L[k].1 + BitVec.ofNat 32 i).toNat ∧
      (BitVec.ofNat 32 L[k].1 + BitVec.ofNat 32 i).toNat < hi) ∨
      (lo' ≤ (BitVec.ofNat 32 L[k].1 + BitVec.ofNat 32 i).toNat ∧
      (BitVec.ofNat 32 L[k].1 + BitVec.ofNat 32 i).toNat < hi') := by
    rw [e]
    rcases hr with hr | hr
    · exact .inl ⟨by omega, by omega⟩
    · exact .inr ⟨by omega, by omega⟩
  rw [hx _ hx']
  exact h k hk i hil

/-- A byte list that lies inside a piece, at offset `o`. -/
theorem CodeIn.sub {M : Word → BitVec 8} {a : Nat} {big small : List Nat} (h : CodeIn M (BitVec.ofNat 32 a) big)
    (o : Nat) (hl : o + small.length ≤ big.length) (hs : small = (big.drop o).take small.length) :
    CodeIn M (BitVec.ofNat 32 (a + o)) small := fun i hi => by
  have e : BitVec.ofNat 32 (a + o) + BitVec.ofNat 32 i = BitVec.ofNat 32 a + BitVec.ofNat 32 (o + i) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e, h (o + i) (by omega)]
  unfold byteAt
  conv => rhs; rw [hs]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hi,
    List.getElem?_drop]

end C3.RV32
