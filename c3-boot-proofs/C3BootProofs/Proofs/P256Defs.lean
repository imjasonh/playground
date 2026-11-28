import C3BootProofs.Proofs.P256Batch
import C3BootProofs.Proofs.P256PtDouble
import C3BootProofs.Proofs.PointAdd
import C3BootProofs.Proofs.P256Scalar
import C3BootProofs.Proofs.P256Neg
import C3BootProofs.Proofs.Pv384Lib4
import C3BootProofs.Image.Bootloader
import C3BootProofs.Image.BootloaderData5

/-!
# The P-256 check's models

The values that the P-256 check computes, as the machine-code proofs of
`p256VerifyPrehash` state them and the models in `Models/` read them: points
in projective Montgomery coordinates, the tables of odd multiples, the main
loop of the linear combination `u₁·G + u₂·Q`, and the two inversions.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

/-- The first 32 bytes of `L`, each cut to a byte. -/
def b32 (L : Bytes) : Bytes := (List.range 32).map fun j => (BitVec.ofNat 8 (L.getD j 0)).toNat

/-- A P-256 point in projective Montgomery coordinates. -/
abbrev Pt2 := Nat × Nat × Nat

/-- Each coordinate is below the field's modulus. -/
def Pt2Lt (P : Pt2) : Prop := P.1 < p256 ∧ P.2.1 < p256 ∧ P.2.2 < p256

/-- The compiled point addition. -/
def ptAdd2 (P Q : Pt2) : Pt2 := ptAddSpec bMont P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2

/-- The compiled point doubling. -/
def ptDbl2 (P : Pt2) : Pt2 := p2Dbl bMont P.1 P.2.1 P.2.2

theorem ptAdd2_lt (P Q : Pt2) : Pt2Lt (ptAdd2 P Q) := by
  unfold Pt2Lt ptAdd2 ptAddSpec
  simp only [C3.RV32.fm, C3.RV32.fa, C3.RV32.fs, C3.RV32.fd]
  exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

theorem ptDbl2_lt (P : Pt2) : Pt2Lt (ptDbl2 P) := by
  unfold Pt2Lt ptDbl2 p2Dbl
  simp only [C3.RV32.fm, C3.RV32.fa, C3.RV32.fs, C3.RV32.fd]
  exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

/-- The table of odd multiples `P, 3P, 5P, …` the check builds: entry `j` is
`P + j·2P`. -/
def tbl2 (P : Pt2) : Nat → Pt2
  | 0 => P
  | j + 1 => ptAdd2 (tbl2 P j) (ptDbl2 P)

theorem tbl2_lt {P : Pt2} (h : Pt2Lt P) : ∀ j, Pt2Lt (tbl2 P j)
  | 0 => h
  | _ + 1 => ptAdd2_lt _ _

/-- The point the frame holds at offset `c`. -/
def ptF (M : Word → BitVec 8) (B : Word) (c : Nat) : Pt2 :=
  (accV M (B + 0x21A0 + BitVec.ofNat 32 c) 8, accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x20)) 8,
    accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x40)) 8)

theorem add_lit40 (S : Word) (c : Nat) : S + BitVec.ofNat 32 c + 0x40 = S + BitVec.ofNat 32 (c + 0x40) :=
  add_ofNat_assoc S c 0x40

/-- The value of `n` limbs whose `j`th is `f j`. -/
def limbSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => limbSum f n + f n * 2 ^ (32 * n)

theorem accV_of_toNats {M : Word → BitVec 8} {p : Word} {f : Nat → Nat} :
    ∀ n, (∀ j, j < n → (memLoad32 M (p + BitVec.ofNat 32 (4 * j))).toNat = f j) → accV M p n = limbSum f n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [accV, limbSum]
    rw [accV_of_toNats n fun j hj => h j (by omega), h n (by omega)]

/-- What `<Scalar as Mul>::mul` leaves for the product `X` of its operands. -/
abbrev psmVal (X : Nat) : Nat := limbSum (psmOut (psmProd X)) 8

/-- A table entry with its `y` coordinate negated, as the field's `neg` does. -/
def negPt2 (P : Pt2) : Pt2 := (P.1, subGen 0 P.2.1, P.2.2)

theorem negPt2_lt {P : Pt2} (h : Pt2Lt P) : Pt2Lt (negPt2 P) := by
  refine ⟨h.1, ?_, h.2.2⟩
  show subGen 0 P.2.1 < p256
  rw [subGen_field (by decide) h.2.1]; exact Nat.mod_lt _ (by decide)

/-- What the loop does with the digit byte `b` of a pair whose table is `T`:
`some none` to skip it, `some (some acc')` to add an entry, and `none` when a
bounds check fails. -/
def mlAdd2 (T : Nat → Pt2) (acc : Pt2) (b : Nat) : Option (Option Pt2) :=
  if b = 0 then some none
  else if b < 128 then (if 16 ≤ b then none else some (some (ptAdd2 acc (T (b / 2)))))
  else if b = 128 ∨ 8 ≤ (256 - b) / 2 then none
  else some (some (ptAdd2 acc (negPt2 (T ((256 - b) / 2)))))

/-- The step for one pair at position `k`: the accumulator and whether it
has had an entry added. -/
def mlPair2 (T : Nat → Pt2) (D : List Nat) (k : Nat) (st : Pt2 × Bool) : Option (Pt2 × Bool) :=
  if 0x101 < k + 1 then some st
  else match mlAdd2 T st.1 (D.getD k 0) with
    | none => none
    | some none => some st
    | some (some a) => some (a, true)

/-- One position of the main loop: double the accumulator once it has an
entry, then step the two pairs. -/
def mlIter2 (T0 T1 : Nat → Pt2) (D0 D1 : List Nat) (k : Nat) (st : Pt2 × Bool) : Option (Pt2 × Bool) :=
  (mlPair2 T0 D0 k (if st.2 then ptDbl2 st.1 else st.1, st.2)).bind (mlPair2 T1 D1 k)

/-- The main loop from position `k - 1` down to 0. -/
def mlLoop2 (T0 T1 : Nat → Pt2) (D0 D1 : List Nat) : Nat → Pt2 × Bool → Option (Pt2 × Bool)
  | 0, st => some st
  | k + 1, st => (mlIter2 T0 T1 D0 D1 k st).bind (mlLoop2 T0 T1 D0 D1 k)

/-- `wnafGo` on a number of `L` bits writes at most `L + 1 - pos` digits
from bit `pos`. -/
theorem wnafGo_len {N L : Nat} (hN : N < 2 ^ L) :
    ∀ fuel pos carry, carry ≤ 1 → pos ≤ L → (wnafGo N L fuel pos carry).length ≤ L + 1 - pos := by
  intro fuel
  induction fuel with
  | zero => intro pos carry _ _; simp only [wnafGo, List.length_nil]; exact Nat.zero_le _
  | succ fuel ih =>
    intro pos carry hc hp
    simp only [wnafGo]
    by_cases hlt : pos < L
    · rw [ite_eq_left hlt]
      by_cases he : (carry + N / 2 ^ pos % 32) % 2 = 0
      · rw [ite_eq_left he, List.length_cons]
        have := ih (pos + 1) carry hc hlt
        omega
      · rw [ite_eq_right he]
        have hb : pos + 1 = L → N / 2 ^ pos < 2 := fun h => by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos pos)]
          rw [← h, Nat.pow_succ] at hN; omega
        have hm : N / 2 ^ pos % 32 ≤ N / 2 ^ pos := Nat.mod_le _ _
        by_cases hw : carry + N / 2 ^ pos % 32 < 16
        · simp only [hw, ↓reduceIte, Nat.sub_zero, List.length_append, List.length_cons, List.length_replicate]
          have := ih (pos + min 5 (L - pos)) 0 (Nat.zero_le _) (by omega)
          omega
        · have hne : pos + 1 ≠ L := fun h => hw (by have := hb h; omega)
          simp only [hw, ↓reduceIte, List.length_append, List.length_cons, List.length_replicate]
          have := ih (pos + min 5 (L - 1 - pos)) 1 (Nat.le_refl _) (by omega)
          omega
    · rw [ite_eq_right hlt]
      split
      · simp only [List.length_nil]; exact Nat.zero_le _
      · simp only [List.length_cons, List.length_nil]; omega

/-- The point at infinity, as the image keeps it, in Montgomery form. -/
def idPt2 : Pt2 :=
  (dataVal p256IdentityData 0 8, dataVal p256IdentityData 0x20 8, dataVal p256IdentityData 0x40 8)

set_option exponentiation.threshold 600 in
theorem idPt2_lt : Pt2Lt idPt2 := by unfold idPt2 Pt2Lt p256; decide

/-- The main loop from the point at infinity over `L` positions. -/
def mlMain2 (T0 T1 : Nat → Pt2) (D0 D1 : List Nat) (L : Nat) : Option (Pt2 × Bool) :=
  mlLoop2 T0 T1 D0 D1 L (idPt2, false)

/-- The inversion of `s`'s starting state: `f` is the order `n`, `g` is `s`, `d` is 0, `e` is 1, and
591 divsteps are left. -/
def p256Iv0 (M0 : Word → BitVec 8) (es : Bytes) : Iv :=
  ⟨1, (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 : Int), (beNat (b32 es) : Int), 0, (accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 : Int), 0x24F⟩

/-- The inversion of `Z`'s starting state: `f` is the prime `p`, `g` is `Z`, `d` is 0, `e` is `R²`, and
591 divsteps are left. -/
def p256Zv0 (M0 : Word → BitVec 8) (Z : Nat) : Iv :=
  ⟨1, (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 : Int), (Z : Int), 0, (accV M0 (BitVec.ofNat 32 (img% p256R2Address)) 8 : Int), 0x24F⟩

/-- The inversion of `s`'s state after its 10 batches. -/
def p256Sf (M0 : Word → BitVec 8) (es : Bytes) : Iv :=
  ivLoop8 (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) 10 (p256Iv0 M0 es)

/-- The inversion of `Z`'s state after its 10 batches. -/
def p256Sz (M0 : Word → BitVec 8) (Z : Nat) : Iv :=
  zvLoop (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) 10 (p256Zv0 M0 Z)

end C3.RV32.Sv
