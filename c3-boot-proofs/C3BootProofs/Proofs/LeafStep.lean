import C3BootProofs.Proofs.DerTlv

/-!
# Step helpers for small leaf functions

Lemmas that the TUF, string, and flash leaf proofs share: a register that an
instruction writes or keeps, registers kept across a run, branch conditions
as `Nat` comparisons, and word and byte conversions.
-/

namespace C3.RV32

/-- A write to a register outside `K` keeps the registers in `K`. -/
theorem ls_keep {K : Fin 32 → Bool} {f g : Fin 32 → Word} {rd : Fin 32} (hrd : K rd = false) (hz : f 0 = 0)
    (v : Word) (kk : ∀ q, K q = true → f q = g q) : ∀ q, K q = true → upd f rd v q = g q := fun q hq => by
  have hne : q ≠ rd := fun e => by subst e; rw [hrd] at hq; exact Bool.false_ne_true hq
  rw [upd_ne' hne hz]; exact kk q hq

/-- A word is the `BitVec.ofNat` of its value. -/
theorem ls_ofNat_toNat (x : Word) : BitVec.ofNat 32 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

/-- A byte apart from a range isn't at an offset inside it. -/
theorem ls_sep_ne {a x : Word} {n i : Nat} (h : Sep a n x 1) (hi : i < n) : x ≠ a + BitVec.ofNat 32 i :=
  fun e => h i hi 0 (by decide) (by rw [← e]; exact (BitVec.add_zero x).symm)

/-- The low byte of a word that holds a byte value. -/
theorem ls_byte {e : Nat} (he : e < 256) : (BitVec.ofNat 32 e).extractLsb' 0 8 = BitVec.ofNat 8 e := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ls_r0 (n : Machine) : reg n 0 = 0 := rfl

/-- The value of `BitVec.ofNat 32 c` when `c` fits. -/
theorem ls_ofNat_toNat_lt {c : Nat} (h : c < 2 ^ 32) : (BitVec.ofNat 32 c).toNat = c := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ls_ult (a b : Word) : branchTaken .bltu a b = decide (a.toNat < b.toNat) := rfl

theorem ls_uge (a b : Word) : branchTaken .bgeu a b = !decide (a.toNat < b.toNat) := rfl

/-- The register a step wrote holds the value written. -/
theorem ls_get {M : Word → BitVec 8} {base : Word} {n p : Machine} {off : Nat} {rd : Fin 32} {v : Word}
    (u : St M base n off (upd (reg p) rd v)) (h : rd.val ≠ 0) : reg n rd = v := by
  rw [u.regs, upd_app, if_neg h, if_pos rfl]

/-- A register a step didn't write keeps its value. -/
theorem ls_oth {M : Word → BitVec 8} {base : Word} {n p : Machine} {off : Nat} {rd : Fin 32} {v : Word}
    (u : St M base n off (upd (reg p) rd v)) {r : Fin 32} (h : r ≠ rd) : reg n r = reg p r := by
  rw [u.regs]; exact upd_ne' h rfl

/-- A step that writes a register outside `K` keeps the registers in `K`. -/
theorem ls_kst {K : Fin 32 → Bool} {M : Word → BitVec 8} {base : Word} {n p m : Machine} {off : Nat}
    {rd : Fin 32} {v : Word} (u : St M base n off (upd (reg p) rd v)) (hrd : K rd = false)
    (kk : ∀ q, K q = true → reg p q = reg m q) : ∀ q, K q = true → reg n q = reg m q :=
  fun q hq => by
    rw [ls_oth u (fun e => by subst e; rw [hrd] at hq; exact Bool.false_ne_true hq)]; exact kk q hq

/-- A step that writes no register keeps the registers in `K`. -/
theorem ls_kbr {K : Fin 32 → Bool} {M : Word → BitVec 8} {base : Word} {n p m : Machine} {off : Nat}
    (u : St M base n off (reg p)) (kk : ∀ q, K q = true → reg p q = reg m q) :
    ∀ q, K q = true → reg n q = reg m q :=
  fun q hq => (u.regs q).trans (kk q hq)

theorem ls_add_lit (x : Word) (c : Nat) : x + BitVec.ofNat 32 c = BitVec.ofNat 32 (x.toNat + c) := by
  conv => lhs; rw [← ls_ofNat_toNat x]
  exact ofNat_add_ofNat _ _

/-- A jump target at an even offset from an even base is even. -/
theorem ls_even {base : Word} (hbase : base.toNat % 2 = 0) (a : Nat) (o : Word) (b : Nat)
    (h : BitVec.ofNat 32 a + o = BitVec.ofNat 32 b) (hb : b % 2 = 0) :
    (base + BitVec.ofNat 32 a + o).getLsbD 0 = false := by
  rw [BitVec.add_assoc, h]; exact even_bit0 (even_at base hbase b hb)

theorem ls_ones_bit : ∀ i : Fin 32, (0 - 1 : Word).getLsbD i.val = true := by decide

theorem ls_ones_and (x : Word) : (0 - 1 : Word) &&& x = x :=
  BitVec.eq_of_getLsbD_eq fun i hi => by rw [BitVec.getLsbD_and, ls_ones_bit ⟨i, hi⟩, Bool.true_and]

/-- `sltu` then `sub` from zero gives a mask of all ones or all zeros, so
an `and` with it selects `x` or 0. -/
theorem ls_mask (p : Prop) [Decidable p] (x : Word) :
    (0 - (if p then (1 : Word) else 0)) &&& x = if p then x else 0 := by
  by_cases h : p
  · rw [if_pos h, if_pos h, ls_ones_and]
  · rw [if_neg h, if_neg h]; exact BitVec.zero_and

end C3.RV32
