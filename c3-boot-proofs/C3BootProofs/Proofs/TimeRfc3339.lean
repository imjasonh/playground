import C3BootProofs.Proofs.GeneralizedTime
import C3BootProofs.Proofs.MemcpyAny
import C3BootProofs.Spec.Tuf

/-!
# `time::rfc3339`, as compiled

`c3_verify::time::rfc3339` reads a four-digit year with `digits::<4>`,
checks the separators of `-MM-DDTHH:MM:SS` while it copies the ten digits
into a buffer, calls `date_time` on that buffer, and then accepts `Z` alone
or `.`, digits that `all_ascii_digit` checks, and `Z`.
`timeRfc3339_correct` matches it to `Spec.Tuf`'s `rfc3339`.
-/

namespace C3.RV32

open C3.Image

abbrev RFC : Word := BitVec.ofNat 32 timeRfc3339Address

section
set_option maxRecDepth 20000
theorem rfc_at_0 : fetchRel timeRfc3339Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFA0, 2) := by decide
theorem rfc_at_1a : fetchRel timeRfc3339Code 0x1A = some (.auipc ra 0x0, 4) := by decide
theorem rfc_at_1e : fetchRel timeRfc3339Code 0x1E = some (.jalr ra ra 0x114, 4) := by decide
theorem rfc_at_22 : fetchRel timeRfc3339Code 0x22 = some (.load .lbu a0 sp 0x18, 4) := by decide
theorem rfc_at_26 : fetchRel timeRfc3339Code 0x26 = some (.branch .beq a0 x0 0x12, 2) := by decide
theorem rfc_at_36 : fetchRel timeRfc3339Code 0x36 = some (.jal x0 0xA6, 2) := by decide
theorem rfc_at_3e : fetchRel timeRfc3339Code 0x3E = some (.store .sh sp x0 0x14, 4) := by decide
theorem rfc_at_66 : fetchRel timeRfc3339Code 0x66 = some (.branch .beq a2 x0 0x30, 2) := by decide
theorem rfc_at_68 : fetchRel timeRfc3339Code 0x68 = some (.branch .beq a5 x0 0x6A, 2) := by decide
theorem rfc_at_6a : fetchRel timeRfc3339Code 0x6A = some (.branch .blt a5 a6 0x68, 4) := by decide
theorem rfc_at_76 : fetchRel timeRfc3339Code 0x76 = some (.branch .bne a4 (8 : Fin 32) 0x5C, 4) := by decide
theorem rfc_at_94 : fetchRel timeRfc3339Code 0x94 = some (.branch .bne a2 x0 0xFFFFFFD4, 2) := by decide
theorem rfc_at_a2 : fetchRel timeRfc3339Code 0xA2 = some (.auipc ra 0x0, 4) := by decide
theorem rfc_at_a6 : fetchRel timeRfc3339Code 0xA6 = some (.jalr ra ra 0xF6, 4) := by decide
theorem rfc_at_aa : fetchRel timeRfc3339Code 0xAA = some (.load .lbu a0 sp 0x18, 4) := by decide
theorem rfc_at_ae : fetchRel timeRfc3339Code 0xAE = some (.branch .bne a0 x0 0xFFFFFF7A, 2) := by decide
theorem rfc_at_b0 : fetchRel timeRfc3339Code 0xB0 = some (.aluImm .add a0 x0 0xF, 2) := by decide
theorem rfc_at_b2 : fetchRel timeRfc3339Code 0xB2 = some (.branch .beq (18 : Fin 32) a0 0x6E, 4) := by decide
theorem rfc_at_c6 : fetchRel timeRfc3339Code 0xC6 = some (.branch .beq a2 x0 0x28, 2) := by decide
theorem rfc_at_c8 : fetchRel timeRfc3339Code 0xC8 = some (.aluImm .add a1 a1 0xFFFFFFA6, 4) := by decide
theorem rfc_at_cc : fetchRel timeRfc3339Code 0xCC = some (.branch .bne a1 x0 0x54, 2) := by decide
theorem rfc_at_ce : fetchRel timeRfc3339Code 0xCE = some (.branch .beq a0 x0 0x48, 2) := by decide
theorem rfc_at_d0 : fetchRel timeRfc3339Code 0xD0 = some (.jal x0 0x50, 2) := by decide
theorem rfc_at_d8 : fetchRel timeRfc3339Code 0xD8 = some (.store .sh (21 : Fin 32) a0 0x0, 4) := by decide
theorem rfc_at_ea : fetchRel timeRfc3339Code 0xEA = some (.aluImm .add sp sp 0x60, 2) := by decide
theorem rfc_at_ec : fetchRel timeRfc3339Code 0xEC = some (.jalr x0 ra 0x0, 2) := by decide
theorem rfc_at_ee : fetchRel timeRfc3339Code 0xEE = some (.branch .beq a0 x0 0x32, 2) := by decide
theorem rfc_at_f0 : fetchRel timeRfc3339Code 0xF0 = some (.aluImm .add a0 (18 : Fin 32) 0xFFFFFFEF, 4) := by decide
theorem rfc_at_f4 : fetchRel timeRfc3339Code 0xF4 = some (.branch .beq a0 x0 0x2C, 2) := by decide
theorem rfc_at_102 : fetchRel timeRfc3339Code 0x102 = some (.branch .bne a1 x0 0x1E, 2) := by decide
theorem rfc_at_10a : fetchRel timeRfc3339Code 0x10A = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem rfc_at_10e : fetchRel timeRfc3339Code 0x10E = some (.jalr ra ra 0x3E4, 4) := by decide
theorem rfc_at_112 : fetchRel timeRfc3339Code 0x112 = some (.branch .beq a0 x0 0xE, 2) := by decide
theorem rfc_at_114 : fetchRel timeRfc3339Code 0x114 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem rfc_at_11e : fetchRel timeRfc3339Code 0x11E = some (.jal x0 0xA, 2) := by decide
theorem rfc_at_128 : fetchRel timeRfc3339Code 0x128 = some (.store .sb (21 : Fin 32) a0 0x0, 4) := by decide
theorem rfc_at_12c : fetchRel timeRfc3339Code 0x12C = some (.jal x0 0xFFFFFFB0, 2) := by decide
end

/-- What `rfc3339` accepts after the seconds. -/
def rfcTail (zone : Bytes) (t : Nat) : Option Nat :=
  match zone with
  | [0x5A] => pure t
  | 0x2E :: fz =>
    match fz.reverse with
    | 0x5A :: frac => require (!frac.isEmpty && frac.all C3.isDigit) >>= fun _ => pure t
    | _ => none
  | _ => none

/-- What `rfc3339` does after the year. -/
def rfcRest (year : Nat) (rest : Bytes) : Option Nat :=
  match rest with
  | 0x2D :: m1 :: m2 :: 0x2D :: d1 :: d2 :: 0x54 :: h1 :: h2 :: 0x3A :: n1 :: n2 :: 0x3A :: s1 :: s2 :: zone => do
    let (t, _) ← readDateTime year [m1, m2, d1, d2, h1, h2, n1, n2, s1, s2]
    rfcTail zone t
  | _ => none

theorem rfc3339_eq (text : Bytes) :
    rfc3339 text = (readDigits 4 text).bind fun yr => rfcRest yr.1 yr.2 := by
  unfold rfc3339
  rcases readDigits 4 text with _ | ⟨y, r⟩
  · rfl
  · rfl

theorem rfcRest_long (y : Nat) (b : Nat → Nat) (zone : Bytes) :
    rfcRest y (b 0 :: b 1 :: b 2 :: b 3 :: b 4 :: b 5 :: b 6 :: b 7 :: b 8 :: b 9 :: b 10 :: b 11 :: b 12 ::
      b 13 :: b 14 :: zone) =
    if b 0 = 0x2D ∧ b 3 = 0x2D ∧ b 6 = 0x54 ∧ b 9 = 0x3A ∧ b 12 = 0x3A then
      (readDateTime y [b 1, b 2, b 4, b 5, b 7, b 8, b 10, b 11, b 13, b 14]).bind fun tr => rfcTail zone tr.1
    else none := by
  by_cases h : b 0 = 0x2D ∧ b 3 = 0x2D ∧ b 6 = 0x54 ∧ b 9 = 0x3A ∧ b 12 = 0x3A
  · rw [if_pos h]
    obtain ⟨h0, h3, h6, h9, h12⟩ := h
    rw [h0, h3, h6, h9, h12]
    show (do let (t, _) ← readDateTime y [b 1, b 2, b 4, b 5, b 7, b 8, b 10, b 11, b 13, b 14]; rfcTail zone t) = _
    rcases readDateTime y [b 1, b 2, b 4, b 5, b 7, b 8, b 10, b 11, b 13, b 14] with _ | ⟨t, r2⟩
    · rfl
    · rfl
  · rw [if_neg h]
    unfold rfcRest
    split
    · next heq =>
      simp only [List.cons.injEq] at heq
      exact absurd ⟨heq.1, heq.2.2.2.1, heq.2.2.2.2.2.2.1, heq.2.2.2.2.2.2.2.2.2.1,
        heq.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ h
    · rfl

theorem rfcRest_short (y : Nat) (rest : Bytes) (h : rest.length < 15) : rfcRest y rest = none := by
  unfold rfcRest
  split
  · simp only [List.length_cons] at h; omega
  · rfl

/-- The separators of `-MM-DDTHH:MM:SS`, at every third byte. -/
def sepB (k : Nat) : Nat := [0x2D, 0x2D, 0x54, 0x3A, 0x3A].getD k 0

/-- The `L` bytes at `q` are at least 15 long and have the separators. -/
def sepOk (M : Word → BitVec 8) (q : Word) (L : Nat) : Prop :=
  15 ≤ L ∧ ∀ k, k < 5 → (M (q + BitVec.ofNat 32 (3 * k))).toNat = sepB k

/-- Where the `i`th of the ten digits is, after the year. -/
def cIdx (i : Nat) : Nat := 3 * (i / 2) + 1 + i % 2

/-- The ten digits of `-MM-DDTHH:MM:SS` at `q`. -/
def compactOf (M : Word → BitVec 8) (q : Word) : Bytes :=
  (List.range 10).map fun i => (M (q + BitVec.ofNat 32 (cIdx i))).toNat

theorem rfcRest_mem (M : Word → BitVec 8) (q : Word) (L y : Nat) :
    (sepOk M q L → rfcRest y (memBytes M q L) =
      (readDateTime y (compactOf M q)).bind fun tr => rfcTail (memBytes M (q + BitVec.ofNat 32 15) (L - 15)) tr.1) ∧
    (¬ sepOk M q L → rfcRest y (memBytes M q L) = none) := by
  by_cases hL : 15 ≤ L
  · obtain ⟨j, rfl⟩ : ∃ j, L = 15 + j := ⟨L - 15, by omega⟩
    rw [memBytes_split, show 15 + j - 15 = j by omega]
    have e15 : memBytes M q 15 = (List.range 15).map fun i => (M (q + BitVec.ofNat 32 i)).toNat := rfl
    rw [e15]
    rw [show ∀ l : Bytes, (List.range 15).map (fun i => (M (q + BitVec.ofNat 32 i)).toNat) ++ l =
      (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 0 :: (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 1 ::
      (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 2 :: (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 3 ::
      (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 4 :: (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 5 ::
      (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 6 :: (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 7 ::
      (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 8 :: (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 9 ::
      (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 10 :: (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 11 ::
      (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 12 :: (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 13 ::
      (fun i => (M (q + BitVec.ofNat 32 i)).toNat) 14 :: l from fun _ => rfl,
      rfcRest_long y (fun i => (M (q + BitVec.ofNat 32 i)).toNat)]
    have hc : compactOf M q = [(M (q + BitVec.ofNat 32 1)).toNat, (M (q + BitVec.ofNat 32 2)).toNat,
        (M (q + BitVec.ofNat 32 4)).toNat, (M (q + BitVec.ofNat 32 5)).toNat, (M (q + BitVec.ofNat 32 7)).toNat,
        (M (q + BitVec.ofNat 32 8)).toNat, (M (q + BitVec.ofNat 32 10)).toNat, (M (q + BitVec.ofNat 32 11)).toNat,
        (M (q + BitVec.ofNat 32 13)).toNat, (M (q + BitVec.ofNat 32 14)).toNat] := rfl
    rw [hc]
    have hs : sepOk M q (15 + j) ↔ ((M (q + BitVec.ofNat 32 0)).toNat = 0x2D ∧ (M (q + BitVec.ofNat 32 3)).toNat = 0x2D ∧
        (M (q + BitVec.ofNat 32 6)).toNat = 0x54 ∧ (M (q + BitVec.ofNat 32 9)).toNat = 0x3A ∧
        (M (q + BitVec.ofNat 32 12)).toNat = 0x3A) := by
      constructor
      · intro h
        exact ⟨h.2 0 (by decide), h.2 1 (by decide), h.2 2 (by decide), h.2 3 (by decide), h.2 4 (by decide)⟩
      · rintro ⟨h0, h1, h2, h3, h4⟩
        refine ⟨by omega, fun k hk => ?_⟩
        match k, hk with
        | 0, _ => exact h0
        | 1, _ => exact h1
        | 2, _ => exact h2
        | 3, _ => exact h3
        | 4, _ => exact h4
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [if_pos (hs.mp h)]
    · rw [if_neg (fun h' => h (hs.mpr h'))]
  · exact ⟨fun h => absurd h.1 hL, fun _ => rfcRest_short y _ (by rw [memBytes_length]; omega)⟩

/-- The bytes after the seconds that `rfc3339` accepts: `Z` alone, or `.`,
one or more digits, and `Z`. -/
def rfcOk (M : Word → BitVec 8) (q : Word) (L : Nat) : Prop :=
  (L = 1 ∧ (M q).toNat = 0x5A) ∨
  (3 ≤ L ∧ (M q).toNat = 0x2E ∧ (M (q + BitVec.ofNat 32 (L - 1))).toNat = 0x5A ∧
    (∀ i, i < L - 2 → 48 ≤ (M (q + BitVec.ofNat 32 (1 + i))).toNat ∧ (M (q + BitVec.ofNat 32 (1 + i))).toNat ≤ 57))

theorem rfcTail_mem (M : Word → BitVec 8) (q : Word) (L t : Nat) :
    (rfcOk M q L → rfcTail (memBytes M q L) t = some t) ∧ (¬ rfcOk M q L → rfcTail (memBytes M q L) t = none) := by
  rcases L with _ | k
  · exact ⟨fun h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega, fun _ => rfl⟩
  rw [memBytes_succ]
  obtain ⟨b, hb⟩ : ∃ b, (M q).toNat = b := ⟨_, rfl⟩
  rw [hb]
  by_cases hZ : b = 0x5A
  · subst hZ
    rcases k with _ | k
    · refine ⟨fun _ => rfl, fun h => absurd (.inl ⟨rfl, hb⟩) h⟩
    · rw [memBytes_succ]
      refine ⟨fun h => ?_, fun _ => rfl⟩
      rcases h with ⟨h, _⟩ | ⟨_, h, _⟩
      · omega
      · rw [hb] at h; cases h
  by_cases hD : b = 0x2E
  · subst hD
    rcases k with _ | j
    · refine ⟨fun h => ?_, fun _ => rfl⟩
      rcases h with ⟨_, h⟩ | ⟨h, _⟩
      · rw [hb] at h; cases h
      · omega
    rw [memBytes_snoc]
    simp only [rfcTail]
    rw [List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    rw [show q + 1 + BitVec.ofNat 32 j = q + BitVec.ofNat 32 (j + 1 + 1 - 1) by
      rw [show j + 1 + 1 - 1 = 1 + j by omega, ← add_ofNat_assoc]; rfl]
    obtain ⟨z, hz⟩ : ∃ z, (M (q + BitVec.ofNat 32 (j + 1 + 1 - 1))).toNat = z := ⟨_, rfl⟩
    rw [hz]
    by_cases hz5 : z = 0x5A
    · subst hz5
      simp only [require, bind, Option.bind, pure]
      rcases j with _ | j
      · simp only [memBytes_zero, List.reverse_nil, List.isEmpty_nil, Bool.not_true, Bool.false_and,
          Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun h => ?_, fun _ => trivial⟩
        rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      have hall := memBytes_all M (q + 1) (j + 1) (fun d => 48 ≤ d && d ≤ 57)
      rw [List.all_reverse]
      have hne : (memBytes M (q + 1) (j + 1)).reverse.isEmpty = false := by
        rw [memBytes_snoc, List.reverse_append]; rfl
      rw [hne]
      have hq1 : ∀ i, q + 1 + BitVec.ofNat 32 i = q + BitVec.ofNat 32 (1 + i) := fun i => by
        rw [← add_ofNat_assoc]; rfl
      simp only [hq1] at hall
      have hdig : (memBytes M (q + 1) (j + 1)).all C3.isDigit = true ↔
          ∀ i, i < j + 1 + 1 + 1 - 2 → 48 ≤ (M (q + BitVec.ofNat 32 (1 + i))).toNat ∧
            (M (q + BitVec.ofNat 32 (1 + i))).toNat ≤ 57 := by
        rw [show C3.isDigit = (fun d => 48 ≤ d && d ≤ 57) from rfl, hall, show j + 1 + 1 + 1 - 2 = j + 1 by omega]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
      by_cases hA : (memBytes M (q + 1) (j + 1)).all C3.isDigit = true
      · rw [hA]
        exact ⟨fun _ => rfl, fun h => absurd (.inr ⟨by omega, hb, hz, hdig.mp hA⟩) h⟩
      · have hA' : (memBytes M (q + 1) (j + 1)).all C3.isDigit = false := Bool.eq_false_iff.mpr hA
        rw [hA']
        refine ⟨fun h => ?_, fun _ => rfl⟩
        rcases h with ⟨h, _⟩ | ⟨_, _, _, h⟩
        · omega
        · exact absurd (hdig.mpr h) hA
    · refine ⟨fun h => ?_, fun _ => ?_⟩
      · rcases h with ⟨h, _⟩ | ⟨_, _, h, _⟩
        · omega
        · rw [hz] at h; exact absurd h hz5
      · split
        · next frac heq => exact absurd (List.cons.inj heq).1 hz5
        · rfl
  · refine ⟨fun h => ?_, fun _ => ?_⟩
    · rcases h with ⟨_, h⟩ | ⟨_, h, _⟩
      · rw [hb] at h; exact absurd h hZ
      · rw [hb] at h; exact absurd h hD
    · simp only [rfcTail]
      split
      · next heq => exact absurd (List.cons.inj heq).1 hZ
      · next fz heq => exact absurd (List.cons.inj heq).1 hD
      · rfl

theorem rfc_blt3 (a : Nat) (ha : a < 2 ^ 31) : branchTaken .blt (BitVec.ofNat 32 a) 3 = decide (a < 3) := by
  unfold branchTaken
  rw [BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat, show (3 : Word).toNat = 3 from rfl]
  rw [Nat.mod_eq_of_lt (by omega)]
  by_cases h : a < 3
  · simp [h]; omega
  · simp [h]; omega

theorem rfc_bne_byte (b c : BitVec 8) :
    branchTaken .bne (b.zeroExtend 32) (c.zeroExtend 32) = !decide (b = c) := by
  unfold branchTaken
  by_cases h : b = c
  · subst h; simp
  · have : b.zeroExtend 32 ≠ c.zeroExtend 32 := fun e => h (BitVec.eq_of_toNat_eq (by
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_setWidth] at this
      rwa [Nat.mod_eq_of_lt (by have := b.isLt; omega), Nat.mod_eq_of_lt (by have := c.isLt; omega)] at this))
    simp [h, this]

theorem memStore32_bytes (M : Word → BitVec 8) (a v : Word) :
    memStore32 M a v a = v.extractLsb' 0 8 ∧ memStore32 M a v (a + 1) = v.extractLsb' 8 8 ∧
      memStore32 M a v (a + 2) = v.extractLsb' 16 8 ∧ memStore32 M a v (a + 3) = v.extractLsb' 24 8 := by
  have n : ∀ i j : Nat, i < 4 → j < 4 → i ≠ j → a + BitVec.ofNat 32 i ≠ a + BitVec.ofNat 32 j :=
    fun i j hi hj h => add_ofNat_ne a (by omega) (by omega) h
  have n0 : ∀ j : Nat, 0 < j → j < 4 → a ≠ a + BitVec.ofNat 32 j := fun j h1 h2 e =>
    n 0 j (by omega) h2 (by omega) (by rw [add_ofNat_zero]; exact e)
  unfold memStore32
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [memStore8_ne (x := a) (a := a + 3) (n0 3 (by omega) (by omega)),
      memStore8_ne (x := a) (a := a + 2) (n0 2 (by omega) (by omega)),
      memStore8_ne (x := a) (a := a + 1) (n0 1 (by omega) (by omega)), memStore8_same]
  · rw [memStore8_ne (x := a + 1) (a := a + 3) (n 1 3 (by omega) (by omega) (by omega)),
      memStore8_ne (x := a + 1) (a := a + 2) (n 1 2 (by omega) (by omega) (by omega)), memStore8_same]
  · rw [memStore8_ne (x := a + 2) (a := a + 3) (n 2 3 (by omega) (by omega) (by omega)), memStore8_same]
  · rw [memStore8_same]

theorem ze_lo8 (b : BitVec 8) : (b.zeroExtend 32).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]; omega

abbrev rfcPs : List (Fin 32 × Word) :=
  [(ra, 0x5C), ((8 : Fin 32), 0x58), ((9 : Fin 32), 0x54), ((18 : Fin 32), 0x50), ((19 : Fin 32), 0x4C),
    ((20 : Fin 32), 0x48), ((21 : Fin 32), 0x44)]

def rfcA : List BInstr :=
  [.alu .add (21 : Fin 32) x0 a0, .sw sp a1 0x4, .sw sp a2 0x8, .aluImm .add a0 sp 0x18, .aluImm .add a1 sp 0x4]
def rfcE28 : List BInstr :=
  [.lbu a0 sp 0x19, .aluImm .add a1 x0 0x1, .sb (21 : Fin 32) a1 0x0, .sb (21 : Fin 32) a0 0x1]
def rfcB : List BInstr :=
  [.lw a1 sp 0x1C, .sw sp x0 0xC, .sw sp x0 0x10]
def rfcC : List BInstr :=
  [.aluImm .add a0 sp 0x28, .lui a2 0x3A543000, .aluImm .add a3 x0 0x3A, .aluImm .add a2 a2 0xFFFFFD2D,
    .lw (9 : Fin 32) sp 0x4, .lw (18 : Fin 32) sp 0x8, .sw sp a2 0x28, .sb sp a3 0x2C, .sw sp x0 0x30,
    .sw sp x0 0x34, .aluImm .add a2 x0 0xA, .aluImm .add a3 sp 0xC, .aluImm .add a6 x0 0x3,
    .alu .add a5 x0 (18 : Fin 32)]
def rfcL1 : List BInstr :=
  [.lbu (8 : Fin 32) a0 0x0, .lbu a4 (9 : Fin 32) 0x0]
def rfcL2 : List BInstr :=
  [.lbu a4 (9 : Fin 32) 0x1, .lbu (8 : Fin 32) (9 : Fin 32) 0x2, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0x3,
    .aluImm .add a5 a5 0xFFFFFFFD, .aluImm .add a0 a0 0x1, .aluImm .add a2 a2 0xFFFFFFFE, .sb a3 a4 0x0,
    .sb a3 (8 : Fin 32) 0x1, .aluImm .add a3 a3 0x2]
def rfcD : List BInstr :=
  [.aluImm .add a0 sp 0xC, .aluImm .add a2 x0 0xA, .sw sp a0 0x3C, .sw sp a2 0x40, .aluImm .add a0 sp 0x18,
    .aluImm .add a2 sp 0x3C]
def rfcE : List BInstr :=
  [.lbu a1 (9 : Fin 32) 0x0, .lw (20 : Fin 32) sp 0x20, .lw (19 : Fin 32) sp 0x24, .aluImm .add a2 a1 0xFFFFFFD2,
    .aluImm .add a0 (18 : Fin 32) 0xFFFFFFF0]
def rfcK : List BInstr :=
  [.lui a0 0x2000, .aluImm .add a0 a0 0xFFFFF901]
def rfcF : List BInstr :=
  [.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x1, .alu .add a0 a0 (9 : Fin 32), .lbu a1 a0 0x0,
    .aluImm .add a1 a1 0xFFFFFFA6]
def rfcG : List BInstr :=
  [.sw sp (9 : Fin 32) 0x18, .sw sp a0 0x1C, .aluImm .add a0 sp 0x18]
def rfcOkB : List BInstr :=
  [.sw (21 : Fin 32) (20 : Fin 32) 0x8, .sw (21 : Fin 32) (19 : Fin 32) 0xC]
def rfcBad : List BInstr :=
  [.aluImm .add a0 x0 0x19, .sb (21 : Fin 32) a0 0x1, .aluImm .add a0 x0 0x1]

section
set_option maxRecDepth 20000
theorem rfcSave_end : blockEnd timeRfc3339Code 2 (saveBlock rfcPs) = some 0x10 := by decide
theorem rfcRestore_end : blockEnd timeRfc3339Code 0xDC (restoreBlock rfcPs) = some 0xEA := by decide
theorem rfcA_end : blockEnd timeRfc3339Code 0x10 rfcA = some 0x1A := by decide
theorem rfcE28_end : blockEnd timeRfc3339Code 0x28 rfcE28 = some 0x36 := by decide
theorem rfcB_end : blockEnd timeRfc3339Code 0x38 rfcB = some 0x3E := by decide
theorem rfcC_end : blockEnd timeRfc3339Code 0x42 rfcC = some 0x66 := by decide
theorem rfcL1_end : blockEnd timeRfc3339Code 0x6E rfcL1 = some 0x76 := by decide
theorem rfcL2_end : blockEnd timeRfc3339Code 0x7A rfcL2 = some 0x94 := by decide
theorem rfcD_end : blockEnd timeRfc3339Code 0x96 rfcD = some 0xA2 := by decide
theorem rfcE_end : blockEnd timeRfc3339Code 0xB6 rfcE = some 0xC6 := by decide
theorem rfcK_end : blockEnd timeRfc3339Code 0xD2 rfcK = some 0xD8 := by decide
theorem rfcF_end : blockEnd timeRfc3339Code 0xF6 rfcF = some 0x102 := by decide
theorem rfcG_end : blockEnd timeRfc3339Code 0x104 rfcG = some 0x10A := by decide
theorem rfcOkB_end : blockEnd timeRfc3339Code 0x116 rfcOkB = some 0x11E := by decide
theorem rfcBad_end : blockEnd timeRfc3339Code 0x120 rfcBad = some 0x128 := by decide
end

/-- What `timeRfc3339_correct` concludes about the machine `m'` it returns
with. -/
abbrev rfcPost (m m' : Machine) (sp0 out p retAddr H : Word) (n : Nat) : Prop :=
  Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
    (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
    (∀ t, rfc3339 (memBytes m.mem p n) = some t → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
      memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
      memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32)) ∧
    (rfc3339 (memBytes m.mem p n) = none → m'.mem out = 1 ∧ m'.mem (out + 1) = 0x19) ∧
    ∀ x, Sep H 0x90 x 1 → Sep out 16 x 1 → m'.mem x = m.mem x

/-- The machine `nn` at offset `off`, after `k` turns of the loop that
checks the separators and copies the digits of the `L` bytes at `q` to
`G + 0xC`. -/
structure RfcInv (m : Machine) (Ms : Word → BitVec 8) (G H out q : Word) (L v k off : Nat)
    (Mt : Word → BitVec 8) (nn : Machine) : Prop where
  st : St Mt RFC nn off (reg nn)
  pre : Steps m nn
  fr : ∀ x, Sep H 0x90 x 1 → Mt x = m.mem x
  sv : ∀ c', 0x74 ≤ c' → c' < 0x90 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')
  sep : ∀ j, j < 5 → Mt (G + BitVec.ofNat 32 (0x28 + j)) = BitVec.ofNat 8 (sepB j)
  cmp : ∀ i, i < 2 * k → Mt (G + BitVec.ofNat 32 (0xC + i)) = m.mem (q + BitVec.ofNat 32 (cIdx i))
  seen : ∀ j, j < k → (m.mem (q + BitVec.ofNat 32 (3 * j))).toNat = sepB j
  hL : 3 * k ≤ L
  rsp : reg nn sp = G
  r21 : reg nn 21 = out
  ra1 : reg nn a1 = BitVec.ofNat 32 v
  ra0 : reg nn a0 = G + BitVec.ofNat 32 (0x28 + k)
  ra2 : reg nn a2 = BitVec.ofNat 32 (10 - 2 * k)
  ra3 : reg nn a3 = G + BitVec.ofNat 32 (0xC + 2 * k)
  ra5 : reg nn a5 = BitVec.ofNat 32 (L - 3 * k)
  ra6 : reg nn a6 = 3
  r9 : reg nn 9 = q + BitVec.ofNat 32 (3 * k)
  r18 : reg nn 18 = BitVec.ofNat 32 L
  kk : ∀ r, r.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nn r = reg m r

theorem RfcInv.move {m : Machine} {Ms : Word → BitVec 8} {G H out q : Word} {L v k off off' : Nat}
    {Mt : Word → BitVec 8} {nn nn' : Machine} (I : RfcInv m Ms G H out q L v k off Mt nn)
    (s : St Mt RFC nn' off' (reg nn)) (d : Steps nn nn') : RfcInv m Ms G H out q L v k off' Mt nn' :=
  { st := s.self, pre := I.pre.trans d, fr := I.fr, sv := I.sv, sep := I.sep, cmp := I.cmp, seen := I.seen,
    hL := I.hL, rsp := by rw [s.regs]; exact I.rsp, r21 := by rw [s.regs]; exact I.r21,
    ra1 := by rw [s.regs]; exact I.ra1, ra0 := by rw [s.regs]; exact I.ra0, ra2 := by rw [s.regs]; exact I.ra2,
    ra3 := by rw [s.regs]; exact I.ra3, ra5 := by rw [s.regs]; exact I.ra5, ra6 := by rw [s.regs]; exact I.ra6,
    r9 := by rw [s.regs]; exact I.r9, r18 := by rw [s.regs]; exact I.r18,
    kk := fun r hr => by rw [s.regs]; exact I.kk r hr }

theorem rfc_wsub (a d : Nat) (c : Word) (hc : c.toNat = 2 ^ 32 - d) (h1 : d ≤ a) (h2 : a < 2 ^ 32) (h3 : 0 < d) :
    aluEval .add (BitVec.ofNat 32 a) c = BitVec.ofNat 32 (a - d) := by
  apply BitVec.eq_of_toNat_eq; rw [dn_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hc]; omega

theorem rfc_addk (a : Word) (j k : Nat) (c : Word) (hc : c.toNat = k) :
    aluEval .add (a + BitVec.ofNat 32 j) c = a + BitVec.ofNat 32 (j + k) := by
  rw [← add_ofNat_assoc, ← hc, ofNat_toNat_self]; rfl

theorem rfc_add1 (a : Word) (j : Nat) : a + BitVec.ofNat 32 j + 1 = a + BitVec.ofNat 32 (j + 1) :=
  add_ofNat_assoc a j 1

theorem rfc_add2 (a : Word) (j : Nat) : a + BitVec.ofNat 32 j + 2 = a + BitVec.ofNat 32 (j + 2) :=
  add_ofNat_assoc a j 2

theorem rfc_beq15 (a : Nat) (ha : a < 2 ^ 32) : branchTaken .beq (BitVec.ofNat 32 a) 15 = decide (a = 15) := by
  simp only [branchTaken]
  by_cases h : a = 15
  · subst h; rfl
  · rw [decide_eq_false h]
    exact beq_eq_false_iff_ne.mpr fun e => h (by
      have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, show (15 : Word).toNat = 15 from rfl] at this; omega)

theorem rfc_sepB_lt : ∀ j, j < 5 → sepB j < 256 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `time::rfc3339`**: for the `n` bytes at `p`, it writes
`rfc3339`'s answer to the `Result<u64, Error>` at `out`: the tag 0 and the
time as two words at `out + 8`, or the tag 1 and `BadTime` (0x19). It returns
with `sp` and the callee-saved registers restored and writes only `out` and
the 0x90 bytes of stack below `sp`, its own frame and `date_time`'s. -/
theorem timeRfc3339_correct (m : Machine) {sp0 out p retAddr : Word} {n : Nat}
    (hcR : CodeIn m.mem RFC timeRfc3339Code) (hcD : CodeIn m.mem DT dateTimeCode)
    (hcT : CodeIn m.mem TD timeDigits2Code) (hcF : CodeIn m.mem TD4 timeDigits4Code)
    (hcA : CodeIn m.mem AAD allAsciiDigitCode) (hpc : m.pc = RFC) (ha0 : reg m a0 = out) (ha1 : reg m a1 = p)
    (ha2 : reg m a2 = BitVec.ofNat 32 n) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) (hsa : sp0.toNat % 4 = 0) (hsl : 0x90 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (how : out.toNat + 16 ≤ 0x40000000) (hoa : out.toNat % 4 = 0) (hpw : p.toNat + n + 4 ≤ 0x40000000)
    (sOG : Sep out 16 (sp0 + 0xFFFFFF70) 0x90) (sPG : Sep p (n + 4) (sp0 + 0xFFFFFF70) 0x90) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ t, rfc3339 (memBytes m.mem p n) = some t → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
        memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
        memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32)) ∧
      (rfc3339 (memBytes m.mem p n) = none → m'.mem out = 1 ∧ m'.mem (out + 1) = 0x19) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF70) 0x90 x 1 → Sep out 16 x 1 → m'.mem x = m.mem x := by
  obtain ⟨H, hH⟩ : ∃ H, sp0 + 0xFFFFFF70 = H := ⟨_, rfl⟩
  rw [hH] at sOG sPG ⊢
  suffices hP : ∃ m', rfcPost m m' sp0 out p retAddr H n from hP
  have hHn : H.toNat = sp0.toNat - 0x90 := by
    rw [← hH, BitVec.toNat_add, show (0xFFFFFF70 : Word).toNat = 2 ^ 32 - 0x90 from rfl]; have := sp0.isLt; omega
  have hHc : ∀ c, c ≤ 0x90 → (H + BitVec.ofNat 32 c).toNat = H.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hHa : H.toNat % 4 = 0 := by omega
  obtain ⟨G, hG⟩ : ∃ G, H + BitVec.ofNat 32 0x30 = G := ⟨_, rfl⟩
  have hGn : G.toNat = H.toNat + 0x30 := by rw [← hG]; exact hHc _ (by decide)
  have hGa : G.toNat % 4 = 0 := by omega
  have eGk : ∀ k, G + BitVec.ofNat 32 k = H + BitVec.ofNat 32 (0x30 + k) := fun k => by rw [← hG, add_ofNat_assoc]
  have eGS : G + 0x60 = sp0 := by
    rw [show (0x60 : Word) = BitVec.ofNat 32 0x60 from rfl, eGk, ← hH, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eG0 : G + 0xFFFFFFD0 = H := by
    rw [← hG, BitVec.add_assoc]; exact BitVec.add_zero H
  have offs : ∀ {c n e k : Nat}, c + n ≤ e ∨ e + k ≤ c → c + n ≤ 0x90 → e + k ≤ 0x90 →
      Sep (H + BitVec.ofNat 32 c) n (H + BitVec.ofNat 32 e) k := fun h h1 h2 => sep_offsets H h (by omega) (by omega)
  have inH : ∀ {c l : Nat} {x : Word}, Sep H 0x90 x 1 → c + l ≤ 0x90 → Sep (H + BitVec.ofNat 32 c) l x 1 :=
    fun hx h => (hx.symm.subR h).symm
  have hiH : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep H 0x90 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have cd : ∀ {M' : Word → BitVec 8} {c : Word} {code : List Nat}, CodeIn m.mem c code → 0x40000000 ≤ c.toNat →
      c.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep H 0x90 x 1 → M' x = m.mem x) → CodeIn M' c code :=
    fun hc h1 h2 hM i hi' => by rw [hM _ (hiH _ (dn_code_hi h1 h2 hi'))]; exact hc i hi'
  have hRn : RFC.toNat = (img% timeRfc3339Address) := by decide
  have cdR : ∀ {M' : Word → BitVec 8}, (∀ x, Sep H 0x90 x 1 → M' x = m.mem x) → CodeIn M' RFC timeRfc3339Code :=
    fun hM => cd hcR (by rw [hRn]; decide) (by rw [hRn]; decide) hM
  have hiC : ∀ {c l : Nat} {a : Word} {len : Nat}, c + l ≤ 0x90 → 0x40000000 ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 →
      Sep (H + BitVec.ofNat 32 c) l a len := fun h h1 h2 => sep_of_le (by rw [hHc _ (by omega)]; omega) h2
  have st0 : St m.mem RFC m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hcR rfc_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFA0) sp = G := by
    simp +decide only [upd, ↓reduceIte]; rw [hsp, ← hG, ← hH, BitVec.add_assoc]; rfl
  have slotO : ∀ o : Word, G + o = H + BitVec.ofNat 32 (0x30 + o.toNat) := fun o => by
    rw [← eGk, ofNat_toNat_self]
  have slotC : ∀ o : Word, o.toNat ≤ 0x5C → Sep (G + o) 4 RFC timeRfc3339Code.length := fun o ho => by
    rw [slotO]; exact hiC (by omega) (by rw [hRn]; decide) (by rw [hRn]; decide)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock rfcPs) u1 hcR rfcSave_end (saveBlock_ok _ rfcPs _ fun q hq => by
      rw [sp1]
      simp only [rfcPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add hGa (by decide), slotC _ (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem G (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFA0)) rfcPs = Ms :=
    ⟨_, rfl⟩
  rw [hMs] at u2
  have IMs : ∀ x, Sep H 0x90 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside rfcPs fun q hq => by
      simp only [rfcPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (rw [slotO]; exact inH hx (by decide))
  have slots : ∀ r o, (r, o) ∈ rfcPs → memLoad32 Ms (G + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [rfcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot rfcPs _ hm (by
      simp only [rfcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        decide),
      upd_ne (by
        simp only [rfcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          decide) hr]
  have hc2 : CodeIn Ms RFC timeRfc3339Code := cdR IMs
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = G := by rw [u2.regs]; exact sp1
  -- the exits
  have hpsp : ∀ p ∈ rfcPs, p.1 ≠ sp := by decide
  have sOC : ∀ {c l : Nat}, c + l ≤ 16 → Sep (out + BitVec.ofNat 32 c) l RFC timeRfc3339Code.length :=
    fun {c l} h => by
      have e : (out + BitVec.ofNat 32 c).toNat = out.toNat + c := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact sep_of_le (by rw [e, hRn]; omega) (by rw [hRn]; decide)
  have tailDC : ∀ {Mt : Word → BitVec 8} {nn : Machine}, St Mt RFC nn 0xDC (reg nn) →
      CodeIn Mt RFC timeRfc3339Code → reg nn sp = G →
      (∀ c', 0x74 ≤ c' → c' < 0x90 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      ∃ nn', Steps nn nn' ∧ nn'.pc = retAddr ∧ reg nn' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn' q = reg m q) ∧
        nn'.mem = Mt := by
    intro Mt nn st hct rsp hsl' hK
    have slotT : ∀ o : Word, 0x44 ≤ o.toNat → o.toNat + 4 ≤ 0x60 →
        memLoad32 Mt (G + o) = memLoad32 Ms (G + o) := fun o h1 h2 => by
      rw [slotO]; apply memLoad32_congr; intro j hj
      rw [add_ofNat_assoc, hsl' _ (by omega) (by omega)]
    obtain ⟨n2, c2', u2'⟩ := St.block (restoreBlock rfcPs) st hct rfcRestore_end
      (restoreBlock_ok Mt G rfcPs (reg nn) rsp hpsp fun q hq => by
        simp only [rfcPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hGa (by decide))
    simp only [restoreBlock_run Mt G rfcPs (reg nn) rsp hpsp] at u2'
    have rsp' : restoreRegs Mt G (reg nn) rfcPs sp = G := by
      rw [restoreRegs_sp _ _ _ _ hpsp]; exact rsp
    obtain ⟨n3, d3, u3⟩ := u2'.aluImm hct rfc_at_ea (off' := 0xEC) (by decide)
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hct rfc_at_ec
    have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
        restoreRegs Mt G f ps q = f q := by
      intro f ps q hq0
      induction ps generalizing f with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro h
        simp only [restoreRegs]
        rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
    have hslot : ∀ r o, (r, o) ∈ rfcPs → reg n4 r = reg m r := fun r o hm => by
      rw [regs4]
      simp only [rfcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
        rw [slotT _ (by decide) (by decide)]; exact slots _ _ (by decide)
    refine ⟨n4, c2'.trans (.cons d3 (.single d4)), ?_, ?_, fun q hq => ?_, ?_⟩
    · rw [pc4, ← regs4, hslot ra 0x5C (by decide), hra, add_lit_zero, hret]
    · rw [regs4]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [rsp', eGS]
    · rcases (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
          q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27]) q hq with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | hL
      · exact hslot _ 0x5C (by decide)
      · exact hslot _ 0x58 (by decide)
      · exact hslot _ 0x54 (by decide)
      · exact hslot _ 0x50 (by decide)
      · exact hslot _ 0x4C (by decide)
      · exact hslot _ 0x48 (by decide)
      · exact hslot _ 0x44 (by decide)
      · obtain ⟨hv, hs, hps⟩ : q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ rfcPs, p.1 ≠ q) := by revert hL; revert q; decide
        rw [regs4, upd_ne hv hs, rr _ _ q hv hps, hK q hL]
    · rw [mem4]
  have tail128 : ∀ {Mt : Word → BitVec 8} {nn : Machine} {v : Word}, St Mt RFC nn 0x128 (reg nn) →
      CodeIn Mt RFC timeRfc3339Code → reg nn sp = G → reg nn 21 = out → reg nn a0 = v →
      (∀ c', 0x74 ≤ c' → c' < 0x90 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      ∃ nn', Steps nn nn' ∧ nn'.pc = retAddr ∧ reg nn' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn' q = reg m q) ∧
        nn'.mem = memStore8 Mt out (v.extractLsb' 0 8) := by
    intro Mt nn v st hct rsp r21 ra0 hsl' hK
    obtain ⟨n1, d1, u1⟩ := st.sb hct rfc_at_128 (off' := 0x12C) (by decide)
    rw [r21, add_lit_zero, ra0] at u1
    have hct1 : CodeIn (memStore8 Mt out (v.extractLsb' 0 8)) RFC timeRfc3339Code := by
      have := sOC (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this; exact hct.store8 this
    obtain ⟨n2, d2, u2⟩ := u1.jump hct1 rfc_at_12c (off' := 0xDC) (by decide) (by rw [u1.pc]; decide)
    obtain ⟨n3, c3, pc3, sp3, K3, mem3⟩ := tailDC u2.self hct1 (by rw [u2.regs, rsp])
      (fun c' h1 h2 => by
        have hne : H + BitVec.ofNat 32 c' ≠ out := by
          have := sOG.sub (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this
          exact dn_sep1 (this.subR (c := c') (l := 1) (by omega))
        rw [memStore8_ne hne, hsl' c' h1 h2])
      (fun q hq => by rw [u2.regs, hK q hq])
    exact ⟨n3, .cons d1 (.cons d2 c3), pc3, sp3, K3, mem3⟩
  have o01 : out + 1 ≠ out := add_one_ne out
  have xo0 : ∀ {x : Word}, Sep out 16 x 1 → x ≠ out := fun hx => by
    have := hx.sub (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this; exact dn_sep1 this
  have xo1 : ∀ {x : Word}, Sep out 16 x 1 → x ≠ out + 1 := fun hx => dn_sep1 (hx.sub (c := 1) (l := 1) (by decide))
  have so1 : Sep (out + 1) 1 RFC timeRfc3339Code.length := sOC (c := 1) (l := 1) (by decide)
  have so0 : Sep out 1 RFC timeRfc3339Code.length := by
    have := sOC (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
  have sv1 : ∀ {Mt : Word → BitVec 8} {a : Word} {b : BitVec 8}, (a = out ∨ a = out + 1) →
      (∀ c', 0x74 ≤ c' → c' < 0x90 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      ∀ c', 0x74 ≤ c' → c' < 0x90 → memStore8 Mt a b (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
    fun {Mt a b} ha hS c' h1 h2 => by
      have hne : H + BitVec.ofNat 32 c' ≠ a := by
        rcases ha with rfl | rfl
        · have := sOG.sub (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this
          exact dn_sep1 (this.subR (c := c') (l := 1) (by omega))
        · exact dn_sep1 ((sOG.sub (c := 1) (l := 1) (by decide)).subR (c := c') (l := 1) (by omega))
      rw [memStore8_ne hne, hS c' h1 h2]
  -- `BadTime` from 0x120
  have fin120 : ∀ {Mt : Word → BitVec 8} {nn : Machine}, Steps m nn → St Mt RFC nn 0x120 (reg nn) →
      (∀ x, Sep H 0x90 x 1 → Mt x = m.mem x) →
      (∀ c', 0x74 ≤ c' → c' < 0x90 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      reg nn sp = G → reg nn 21 = out →
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      rfc3339 (memBytes m.mem p n) = none → ∃ m', rfcPost m m' sp0 out p retAddr H n := by
    intro Mt nn pre st hI hS rsp r21 hK hspec
    have hct := cdR hI
    obtain ⟨n1, c1, u1⟩ := St.block rfcBad st hct rfcBad_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, rfcBad, upd_app, ↓reduceIte, and_true, true_and]
      rw [r21]; exact so1)
    have eM : (runBlock rfcBad (Mt, reg nn)).1 = memStore8 Mt (out + 1) 0x19 := by
      simp +decide only [runBlock, BInstr.run, rfcBad, upd_app, ↓reduceIte]; rw [r21, st.zero]; rfl
    rw [eM] at u1
    have hct1 : CodeIn (memStore8 Mt (out + 1) 0x19) RFC timeRfc3339Code := hct.store8 so1
    have K1 : ∀ q, q ≠ a0 → (runBlock rfcBad (Mt, reg nn)).2 q = reg nn q := fun q hq => by
      have hd : q ∉ rfcBad.filterMap BInstr.dst := by
        simp only [rfcBad, List.filterMap_cons, List.filterMap_nil, BInstr.dst, List.mem_cons, List.mem_nil_iff,
          or_false, or_self]; exact hq
      exact runBlock_reg _ _ _ q st.zero hd
    obtain ⟨n2, c2', pc2, sp2', K2, mem2⟩ := tail128 (v := 1) u1.self hct1
      (by rw [u1.regs, K1 sp (by decide), rsp]) (by rw [u1.regs, K1 21 (by decide), r21])
      (by rw [u1.regs]; simp +decide only [runBlock, BInstr.run, rfcBad, upd_app, ↓reduceIte])
      (sv1 (.inr rfl) hS) (fun q hq => by rw [u1.regs, K1 q (by revert hq; revert q; decide), hK q hq])
    refine ⟨n2, pre.trans (c1.trans c2'), pc2, sp2', K2, fun t h => (by rw [hspec] at h; cases h),
      fun _ => ⟨?_, ?_⟩, fun x hx hx1 => ?_⟩
    · rw [mem2]; exact memStore8_same _ _ _
    · rw [mem2, memStore8_ne o01, memStore8_same]
    · rw [mem2, memStore8_ne (xo0 hx1), memStore8_ne (xo1 hx1), hI x hx]
  -- `BadTime` from a callee's result at `G + 0x18`
  have fin28 : ∀ {Mt : Word → BitVec 8} {nn : Machine}, Steps m nn → St Mt RFC nn 0x28 (reg nn) →
      (∀ x, Sep H 0x90 x 1 → Mt x = m.mem x) →
      (∀ c', 0x74 ≤ c' → c' < 0x90 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      reg nn sp = G → reg nn 21 = out →
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      rfc3339 (memBytes m.mem p n) = none → Mt (G + 0x18 + 1) = 0x19 →
      ∃ m', rfcPost m m' sp0 out p retAddr H n := by
    intro Mt nn pre st hI hS rsp r21 hK hspec h19
    have hct := cdR hI
    obtain ⟨n1, c1, u1⟩ := St.block rfcE28 st hct rfcE28_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, rfcE28, upd_app, ↓reduceIte, and_true, true_and]
      rw [r21, add_lit_zero]; exact ⟨so0, so1⟩)
    have eM : (runBlock rfcE28 (Mt, reg nn)).1 = memStore8 (memStore8 Mt out 1) (out + 1) 0x19 := by
      simp +decide only [runBlock, BInstr.run, rfcE28, upd_app, ↓reduceIte]
      rw [r21, add_lit_zero, rsp, show G + 0x19 = G + 0x18 + 1 by rw [BitVec.add_assoc]; rfl, h19]; rfl
    rw [eM] at u1
    have hct1 : CodeIn (memStore8 (memStore8 Mt out 1) (out + 1) 0x19) RFC timeRfc3339Code :=
      (hct.store8 so0).store8 so1
    have K1 : ∀ q, q.val ∉ [10, 11] → (runBlock rfcE28 (Mt, reg nn)).2 q = reg nn q := fun q hq => by
      have hd : q ∉ rfcE28.filterMap BInstr.dst := by
        simp only [rfcE28, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
      exact runBlock_reg _ _ _ q st.zero hd
    obtain ⟨n2, d2, u2⟩ := u1.jump hct1 rfc_at_36 (off' := 0xDC) (by decide) (by rw [u1.pc]; decide)
    obtain ⟨n3, c3, pc3, sp3, K3, mem3⟩ := tailDC u2.self hct1 (by rw [u2.regs, K1 sp (by decide), rsp])
      (sv1 (.inr rfl) (sv1 (.inl rfl) hS))
      (fun q hq => by rw [u2.regs, K1 q (by revert hq; revert q; decide), hK q hq])
    refine ⟨n3, pre.trans (c1.trans (.cons d2 c3)), pc3, sp3, K3, fun t h => (by rw [hspec] at h; cases h),
      fun _ => ⟨?_, ?_⟩, fun x hx hx1 => ?_⟩
    · rw [mem3, memStore8_ne o01.symm, memStore8_same]
    · rw [mem3, memStore8_same]
    · rw [mem3, memStore8_ne (xo1 hx1), memStore8_ne (xo0 hx1), hI x hx]
  -- `BadTime` from the separator loop, at 0xD2
  have finD2 : ∀ {Mt : Word → BitVec 8} {nn : Machine}, Steps m nn → St Mt RFC nn 0xD2 (reg nn) →
      (∀ x, Sep H 0x90 x 1 → Mt x = m.mem x) →
      (∀ c', 0x74 ≤ c' → c' < 0x90 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      reg nn sp = G → reg nn 21 = out →
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      rfc3339 (memBytes m.mem p n) = none → ∃ m', rfcPost m m' sp0 out p retAddr H n := by
    intro Mt nn pre st hI hS rsp r21 hK hspec
    have hct := cdR hI
    obtain ⟨n1, c1, u1⟩ := St.block rfcK st hct rfcK_end (by simp only [BlockOk, BInstr.ok, rfcK, and_self])
    have a01 : (runBlock rfcK (Mt, reg nn)).2 a0 = 0x1901 := by
      simp +decide only [runBlock, BInstr.run, rfcK, upd_app, ↓reduceIte]
    have K1 : ∀ q, q ≠ a0 → (runBlock rfcK (Mt, reg nn)).2 q = reg nn q := fun q hq => by
      have hd : q ∉ rfcK.filterMap BInstr.dst := by
        simp only [rfcK, List.filterMap_cons, List.filterMap_nil, BInstr.dst, List.mem_cons, List.mem_nil_iff,
          or_false, or_self]; exact hq
      exact runBlock_reg _ _ _ q st.zero hd
    have u1' : St Mt RFC n1 0xD8 (runBlock rfcK (Mt, reg nn)).2 := ⟨u1.pc, by rw [u1.mem]; rfl, u1.regs⟩
    obtain ⟨n2, d2, u2⟩ := u1'.sh hct rfc_at_d8 (off' := 0xDC) (by decide)
      (by rw [K1 21 (by decide), r21, add_lit_zero]; omega)
    rw [K1 21 (by decide), r21, add_lit_zero, a01] at u2
    have e1 : (0x1901 : Word).extractLsb' 0 8 = 1 := by decide
    have e2 : (0x1901 : Word).extractLsb' 8 8 = 0x19 := by decide
    rw [e1, e2] at u2
    have hct2 : CodeIn (memStore8 (memStore8 Mt out 1) (out + 1) 0x19) RFC timeRfc3339Code :=
      (hct.store8 so0).store8 so1
    obtain ⟨n3, c3, pc3, sp3, K3, mem3⟩ := tailDC u2.self hct2 (by rw [u2.regs, K1 sp (by decide), rsp])
      (sv1 (.inr rfl) (sv1 (.inl rfl) hS))
      (fun q hq => by rw [u2.regs, K1 q (by revert hq; revert q; decide), hK q hq])
    refine ⟨n3, pre.trans (c1.trans (.cons d2 c3)), pc3, sp3, K3, fun t h => (by rw [hspec] at h; cases h),
      fun _ => ⟨?_, ?_⟩, fun x hx hx1 => ?_⟩
    · rw [mem3, memStore8_ne o01.symm, memStore8_same]
    · rw [mem3, memStore8_same]
    · rw [mem3, memStore8_ne (xo1 hx1), memStore8_ne (xo0 hx1), hI x hx]
  -- the time stored, from 0x116
  have s0_8 : Sep out 1 (out + 8) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 8) (k := 4) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have s0_12 : Sep out 1 (out + 0xC) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 0xC) (k := 4) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have s12_8 : Sep (out + 0xC) 4 (out + 8) 4 := sep_offsets out (c := 0xC) (n := 4) (d := 8) (k := 4) (by omega)
    (by omega) (by omega)
  have sx8 : ∀ {x : Word}, Sep out 16 x 1 → Sep (out + 8) 4 x 1 := fun hx => hx.sub (c := 8) (l := 4) (by decide)
  have sx12 : ∀ {x : Word}, Sep out 16 x 1 → Sep (out + 0xC) 4 x 1 := fun hx => hx.sub (c := 0xC) (l := 4) (by decide)
  have sHo : ∀ {c' : Nat}, c' < 0x90 → Sep out 16 (H + BitVec.ofNat 32 c') 1 := fun {c'} h => sOG.subR (c := c') (l := 1) h
  have so8 : (out + 8).toNat % 4 = 0 := by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have so12 : (out + 0xC).toNat % 4 = 0 := by
    rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have finOk : ∀ {Mt : Word → BitVec 8} {nn : Machine} {t : Nat}, Steps m nn → St Mt RFC nn 0x116 (reg nn) →
      (∀ x, Sep H 0x90 x 1 → Mt x = m.mem x) →
      (∀ c', 0x74 ≤ c' → c' < 0x90 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      reg nn sp = G → reg nn 21 = out →
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) → reg nn a0 = 0 →
      reg nn 20 = BitVec.ofNat 32 (t % 2 ^ 32) → reg nn 19 = BitVec.ofNat 32 (t / 2 ^ 32) →
      t < 2 ^ 64 → rfc3339 (memBytes m.mem p n) = some t →
      ∃ m', rfcPost m m' sp0 out p retAddr H n := by
    intro Mt nn t pre st hI hS rsp r21 hK ra0 rs4 rs3 ht hspec
    have hct := cdR hI
    obtain ⟨n1, c1, u1⟩ := St.block rfcOkB st hct rfcOkB_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, rfcOkB, and_true]
      rw [r21]; exact ⟨⟨so8, sOC (c := 8) (l := 4) (by decide)⟩, so12, sOC (c := 0xC) (l := 4) (by decide)⟩)
    have eM : (runBlock rfcOkB (Mt, reg nn)).1 = memStore32 (memStore32 Mt (out + 8) (BitVec.ofNat 32 (t % 2 ^ 32)))
        (out + 0xC) (BitVec.ofNat 32 (t / 2 ^ 32)) := by
      simp +decide only [runBlock, BInstr.run, rfcOkB]; rw [r21, rs4, rs3]
    have K1 : ∀ q, (runBlock rfcOkB (Mt, reg nn)).2 q = reg nn q := fun q => by
      simp only [runBlock, BInstr.run, rfcOkB]
    rw [eM] at u1
    have hct1 : CodeIn (memStore32 (memStore32 Mt (out + 8) (BitVec.ofNat 32 (t % 2 ^ 32))) (out + 0xC)
        (BitVec.ofNat 32 (t / 2 ^ 32))) RFC timeRfc3339Code :=
      (hct.store32 (sOC (c := 8) (l := 4) (by decide))).store32 (sOC (c := 0xC) (l := 4) (by decide))
    obtain ⟨n2, d2, u2⟩ := u1.jump hct1 rfc_at_11e (off' := 0x128) (by decide) (by rw [u1.pc]; decide)
    obtain ⟨n3, c3, pc3, sp3', K3', mem3⟩ := tail128 (v := 0) u2.self hct1 (by rw [u2.regs, K1, rsp])
      (by rw [u2.regs, K1, r21]) (by rw [u2.regs, K1, ra0])
      (fun c' h1 h2 => by rw [memStore32_get_sep (sx12 (sHo h2)), memStore32_get_sep (sx8 (sHo h2)), hS c' h1 h2])
      (fun q hq => by rw [u2.regs, K1, hK q hq])
    have hE : ∀ t', rfc3339 (memBytes m.mem p n) = some t' → t' = t := fun t' h => by
      rw [hspec] at h; cases h; rfl
    refine ⟨n3, pre.trans (c1.trans (.cons d2 c3)), pc3, sp3', K3', fun t' h => ?_,
      fun h => (by rw [hspec] at h; cases h), fun x hx hx1 => ?_⟩
    · obtain rfl := hE t' h
      refine ⟨ht, by rw [mem3]; exact memStore8_same _ _ _, ?_, ?_⟩
      · rw [mem3, memLoad32_store8_sep s0_8, memLoad32_store32_sep s12_8, memLoad32_store32_same]
      · rw [mem3, memLoad32_store8_sep s0_12, memLoad32_store32_same]
    · rw [mem3, memStore8_ne (xo0 hx1), memStore32_get_sep (sx12 hx1), memStore32_get_sep (sx8 hx1), hI x hx]
  have iter : ∀ {q : Word} {L v k : Nat} {Mt : Word → BitVec 8} {nn : Machine}, k < 5 → L < 2 ^ 30 →
      Sep q L H 0x90 → rfc3339 (memBytes m.mem p n) = rfcRest v (memBytes m.mem q L) →
      RfcInv m Ms G H out q L v k 0x68 Mt nn →
      (∃ m', rfcPost m m' sp0 out p retAddr H n) ∨
        ∃ Mt' nn', RfcInv m Ms G H out q L v (k + 1) (if k + 1 = 5 then 0x96 else 0x68) Mt' nn' := by
    intro q L v k Mt nn hk hLb sQH hred I
    have hct := cdR I.fr
    have hz := I.st.zero
    have notSep : ¬ sepOk m.mem q L → rfc3339 (memBytes m.mem p n) = none := fun h => by
      rw [hred]; exact (rfcRest_mem m.mem q L v).2 h
    have rq : ∀ i, i < L → Mt (q + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i) := fun i hi =>
      I.fr _ (sQH.sub (c := i) (l := 1) (by omega)).symm
    by_cases h0 : L - 3 * k = 0
    · obtain ⟨n1, d1, u1⟩ := I.st.taken hct 0xD2 rfc_at_68 (by decide)
        (by rw [I.ra5, hz, dn_beq0 _ (by omega)]; exact decide_eq_true h0)
      left
      exact finD2 (I.pre.trans (.single d1)) u1.self I.fr I.sv (by rw [u1.regs, I.rsp]) (by rw [u1.regs, I.r21])
        (fun r hr => by rw [u1.regs, I.kk r hr]) (notSep fun ⟨h15, _⟩ => by omega)
    obtain ⟨n1, d1, u1⟩ := I.st.notTaken hct 0x6A rfc_at_68 (by decide)
      (by rw [I.ra5, hz, dn_beq0 _ (by omega)]; exact decide_eq_false h0)
    by_cases h3 : L - 3 * k < 3
    · obtain ⟨n2, d2, u2⟩ := u1.taken hct 0xD2 rfc_at_6a (by decide)
        (by rw [I.ra5, I.ra6, rfc_blt3 _ (by omega)]; exact decide_eq_true h3)
      left
      exact finD2 (I.pre.trans (.cons d1 (.single d2))) u2.self I.fr I.sv (by rw [u2.regs, I.rsp])
        (by rw [u2.regs, I.r21]) (fun r hr => by rw [u2.regs, I.kk r hr]) (notSep fun ⟨h15, _⟩ => by omega)
    obtain ⟨n2, d2, u2⟩ := u1.notTaken hct 0x6E rfc_at_6a (by decide)
      (by rw [I.ra5, I.ra6, rfc_blt3 _ (by omega)]; exact decide_eq_false h3)
    obtain ⟨n3, c3, u3⟩ := St.block rfcL1 u2 hct rfcL1_end (by simp only [BlockOk, BInstr.ok, rfcL1, and_self])
    have K3 : ∀ r, r.val ∉ [8, 14] → (runBlock rfcL1 (Mt, reg nn)).2 r = reg nn r := fun r hr => by
      have hd : r ∉ rfcL1.filterMap BInstr.dst := by
        simp only [rfcL1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hr; revert r; decide
      exact runBlock_reg _ _ _ r hz hd
    have e8 : (runBlock rfcL1 (Mt, reg nn)).2 8 = (BitVec.ofNat 8 (sepB k)).zeroExtend 32 := by
      simp +decide only [runBlock, BInstr.run, rfcL1, upd_app, ↓reduceIte]
      rw [I.ra0, add_lit_zero, I.sep k hk]
    have e14 : (runBlock rfcL1 (Mt, reg nn)).2 a4 = (m.mem (q + BitVec.ofNat 32 (3 * k))).zeroExtend 32 := by
      simp +decide only [runBlock, BInstr.run, rfcL1, upd_app, ↓reduceIte]
      rw [I.r9, add_lit_zero, rq _ (by omega)]
    have hu3 : St Mt RFC n3 0x76 (runBlock rfcL1 (Mt, reg nn)).2 := ⟨u3.pc, by rw [u3.mem]; rfl, u3.regs⟩
    by_cases hs : m.mem (q + BitVec.ofNat 32 (3 * k)) = BitVec.ofNat 8 (sepB k)
    rotate_left
    · obtain ⟨n4, d4, u4⟩ := hu3.taken hct 0xD2 rfc_at_76 (by decide)
        (by rw [e14, e8, rfc_bne_byte]; simp only [hs, decide_false, Bool.not_false])
      left
      refine finD2 (I.pre.trans (.cons d1 (.cons d2 (c3.trans (.single d4))))) u4.self I.fr I.sv
        (by rw [u4.regs, K3 sp (by decide), I.rsp]) (by rw [u4.regs, K3 21 (by decide), I.r21])
        (fun r hr => by rw [u4.regs, K3 r (by revert hr; revert r; decide), I.kk r hr])
        (notSep fun ⟨_, hall⟩ => hs ?_)
      apply BitVec.eq_of_toNat_eq
      rw [hall k hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rfc_sepB_lt k hk)]
    obtain ⟨n4, d4, u4⟩ := hu3.notTaken hct 0x7A rfc_at_76 (by decide)
      (by rw [e14, e8, rfc_bne_byte]; simp only [hs, decide_true, Bool.not_true])
    have r4 : ∀ r, reg n4 r = (runBlock rfcL1 (Mt, reg nn)).2 r := u4.regs
    have a3v : reg n4 a3 = G + BitVec.ofNat 32 (0xC + 2 * k) := by rw [r4, K3 a3 (by decide), I.ra3]
    have s1v : reg n4 9 = q + BitVec.ofNat 32 (3 * k) := by rw [r4, K3 9 (by decide), I.r9]
    have hz4 : reg n4 0 = 0 := u4.self.zero
    obtain ⟨n5, c5, u5⟩ := St.block rfcL2 u4.self hct rfcL2_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, rfcL2, upd_app, ↓reduceIte, and_true, true_and]
      rw [a3v, add_lit_zero, eGk, rfc_add1]
      exact ⟨hiC (by omega) (by rw [hRn]; decide) (by rw [hRn]; decide),
        hiC (by omega) (by rw [hRn]; decide) (by rw [hRn]; decide)⟩)
    have K5 : ∀ r, r.val ∉ [8, 9, 10, 12, 13, 14, 15] → (runBlock rfcL2 (Mt, reg n4)).2 r = reg n4 r :=
      fun r hr => by
        have hd : r ∉ rfcL2.filterMap BInstr.dst := by
          simp only [rfcL2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hr; revert r; decide
        exact runBlock_reg _ _ _ r hz4 hd
    have R4 : ∀ r, r.val ∉ [8, 9, 10, 12, 13, 14, 15] → (runBlock rfcL2 (Mt, reg n4)).2 r = reg nn r :=
      fun r hr => by rw [K5 r hr, r4, K3 r (by revert hr; revert r; decide)]
    have v9 : (runBlock rfcL2 (Mt, reg n4)).2 9 = q + BitVec.ofNat 32 (3 * (k + 1)) := by
      simp +decide only [runBlock, BInstr.run, rfcL2, upd_app, ↓reduceIte]
      rw [s1v, rfc_addk _ _ 3 (3 : Word) rfl, show 3 * k + 3 = 3 * (k + 1) by omega]
    have v15 : (runBlock rfcL2 (Mt, reg n4)).2 a5 = BitVec.ofNat 32 (L - 3 * (k + 1)) := by
      simp +decide only [runBlock, BInstr.run, rfcL2, upd_app, ↓reduceIte]
      rw [r4, K3 a5 (by decide), I.ra5, rfc_wsub (L - 3 * k) 3 0xFFFFFFFD rfl (by omega) (by omega) (by omega),
        show L - 3 * k - 3 = L - 3 * (k + 1) by omega]
    have v10 : (runBlock rfcL2 (Mt, reg n4)).2 a0 = G + BitVec.ofNat 32 (0x28 + (k + 1)) := by
      simp +decide only [runBlock, BInstr.run, rfcL2, upd_app, ↓reduceIte]
      rw [r4, K3 a0 (by decide), I.ra0, rfc_addk _ _ 1 (1 : Word) rfl, Nat.add_assoc]
    have v12 : (runBlock rfcL2 (Mt, reg n4)).2 a2 = BitVec.ofNat 32 (10 - 2 * (k + 1)) := by
      simp +decide only [runBlock, BInstr.run, rfcL2, upd_app, ↓reduceIte]
      rw [r4, K3 a2 (by decide), I.ra2, rfc_wsub (10 - 2 * k) 2 0xFFFFFFFE rfl (by omega) (by omega) (by omega),
        show 10 - 2 * k - 2 = 10 - 2 * (k + 1) by omega]
    have v13 : (runBlock rfcL2 (Mt, reg n4)).2 a3 = G + BitVec.ofNat 32 (0xC + 2 * (k + 1)) := by
      simp +decide only [runBlock, BInstr.run, rfcL2, upd_app, ↓reduceIte]
      rw [a3v, rfc_addk _ _ 2 (2 : Word) rfl, show 0xC + 2 * k + 2 = 0xC + 2 * (k + 1) by omega]
    obtain ⟨Mt5, hMt5⟩ : ∃ M', memStore8 (memStore8 Mt (G + BitVec.ofNat 32 (0xC + 2 * k))
        (m.mem (q + BitVec.ofNat 32 (3 * k + 1)))) (G + BitVec.ofNat 32 (0xC + 2 * k + 1))
        (m.mem (q + BitVec.ofNat 32 (3 * k + 2))) = M' := ⟨_, rfl⟩
    have eM5 : (runBlock rfcL2 (Mt, reg n4)).1 = Mt5 := by
      rw [← hMt5]
      simp +decide only [runBlock, BInstr.run, rfcL2, upd_app, ↓reduceIte]
      rw [a3v, s1v, add_lit_zero]
      simp only [rfc_add1, rfc_add2, ze_lo8]
      rw [rq (3 * k + 1) (by omega), rq (3 * k + 2) (by omega)]
    have u5' : St Mt5 RFC n5 0x94 (reg n5) := ⟨u5.pc, by rw [u5.mem, eM5], fun _ => rfl⟩
    have M5ne : ∀ x, x ≠ G + BitVec.ofNat 32 (0xC + 2 * k) → x ≠ G + BitVec.ofNat 32 (0xC + 2 * k + 1) →
        Mt5 x = Mt x := fun x h1 h2 => by rw [← hMt5, memStore8_ne h2, memStore8_ne h1]
    have fr5 : ∀ x, Sep H 0x90 x 1 → Mt5 x = m.mem x := fun x hx => by
      rw [M5ne x (by rw [eGk]; exact dn_sep1 (inH hx (by omega))) (by rw [eGk]; exact dn_sep1 (inH hx (by omega))),
        I.fr x hx]
    have J : RfcInv m Ms G H out q L v (k + 1) 0x94 Mt5 n5 :=
      { st := u5', pre := I.pre.trans (.cons d1 (.cons d2 (c3.trans (.cons d4 c5)))), fr := fr5,
        sv := fun c' h1 h2 => by
          rw [M5ne _ (by rw [eGk]; exact add_ofNat_ne H (by omega) (by omega) (by omega))
            (by rw [eGk]; exact add_ofNat_ne H (by omega) (by omega) (by omega)), I.sv c' h1 h2]
        sep := fun j hj => by
          rw [M5ne _ (add_ofNat_ne G (by omega) (by omega) (by omega)) (add_ofNat_ne G (by omega) (by omega) (by omega)),
            I.sep j hj]
        cmp := fun i hi => by
          by_cases hi' : i < 2 * k
          · rw [M5ne _ (add_ofNat_ne G (by omega) (by omega) (by omega))
              (add_ofNat_ne G (by omega) (by omega) (by omega)), I.cmp i hi']
          · by_cases he : i = 2 * k
            · subst he
              rw [← hMt5, memStore8_ne (add_ofNat_ne G (by omega) (by omega) (by omega)), memStore8_same,
                show cIdx (2 * k) = 3 * k + 1 by unfold cIdx; omega]
            · obtain rfl : i = 2 * k + 1 := by omega
              rw [← Nat.add_assoc, ← hMt5, memStore8_same, show cIdx (2 * k + 1) = 3 * k + 2 by unfold cIdx; omega]
        seen := fun j hj => by
          by_cases hj' : j < k
          · exact I.seen j hj'
          · obtain rfl : j = k := by omega
            rw [hs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rfc_sepB_lt j hk)]
        hL := by omega
        rsp := by rw [u5.regs, R4 sp (by decide), I.rsp]
        r21 := by rw [u5.regs, R4 21 (by decide), I.r21]
        ra1 := by rw [u5.regs, R4 a1 (by decide), I.ra1]
        ra0 := by rw [u5.regs, v10]
        ra2 := by rw [u5.regs, v12]
        ra3 := by rw [u5.regs, v13]
        ra5 := by rw [u5.regs, v15]
        ra6 := by rw [u5.regs, R4 a6 (by decide), I.ra6]
        r9 := by rw [u5.regs, v9]
        r18 := by rw [u5.regs, R4 18 (by decide), I.r18]
        kk := fun r hr => by rw [u5.regs, R4 r (by revert hr; revert r; decide), I.kk r hr] }
    have hct5 := cdR fr5
    by_cases hk4 : k + 1 = 5
    · obtain ⟨n6, d6, u6⟩ := u5'.notTaken hct5 0x96 rfc_at_94 (by decide) (by rw [J.ra2, J.st.zero, hk4]; decide)
      right; refine ⟨Mt5, n6, ?_⟩; rw [if_pos hk4]; exact J.move u6 (.single d6)
    · obtain ⟨n6, d6, u6⟩ := u5'.taken hct5 0x68 rfc_at_94 (by decide)
        (by rw [J.ra2, J.st.zero, dn_bne0 _ (by omega), Bool.not_eq_true']; exact decide_eq_false (by omega))
      right; refine ⟨Mt5, n6, ?_⟩; rw [if_neg hk4]; exact J.move u6 (.single d6)
  have loop : ∀ {q : Word} {L v : Nat}, L < 2 ^ 30 → Sep q L H 0x90 →
      rfc3339 (memBytes m.mem p n) = rfcRest v (memBytes m.mem q L) →
      ∀ j k Mt nn, k + j = 5 → RfcInv m Ms G H out q L v k (if k = 5 then 0x96 else 0x68) Mt nn →
      (∃ m', rfcPost m m' sp0 out p retAddr H n) ∨ ∃ Mt' nn', RfcInv m Ms G H out q L v 5 0x96 Mt' nn' := by
    intro q L v hLb sQH hred j
    induction j with
    | zero =>
      intro k Mt nn hk I
      obtain rfl : k = 5 := by omega
      rw [if_pos rfl] at I
      exact .inr ⟨Mt, nn, I⟩
    | succ j ih =>
      intro k Mt nn hk I
      rw [if_neg (by omega)] at I
      rcases iter (by omega) hLb sQH hred I with h | ⟨Mt', nn', I'⟩
      · exact .inl h
      · exact ih (k + 1) Mt' nn' (by omega) I'
  -- frame helpers for offsets from `G`
  have sGw : ∀ {o : Word} {l : Nat} {x : Word}, o.toNat + l ≤ 0x60 → Sep H 0x90 x 1 → Sep (G + o) l x 1 :=
    fun h hx => by rw [slotO]; exact inH hx (by omega)
  have sGv : ∀ {o : Word} {l c' : Nat}, o.toNat + l ≤ 0x44 → 0x74 ≤ c' → c' < 0x90 →
      Sep (G + o) l (H + BitVec.ofNat 32 c') 1 := fun h1 h2 h3 => by
    rw [slotO]; exact offs (by omega) (by omega) (by omega)
  have sGG : ∀ {o o' : Word} {l l' : Nat}, o.toNat + l ≤ o'.toNat ∨ o'.toNat + l' ≤ o.toNat → o.toNat + l ≤ 0x60 →
      o'.toNat + l' ≤ 0x60 → Sep (G + o) l (G + o') l' := fun h1 h2 h3 => by
    rw [slotO, slotO]; exact offs (by omega) (by omega) (by omega)
  have sGX : ∀ {o : Word} {l : Nat} {a : Word} {len : Nat}, o.toNat + l ≤ 0x60 → 0x40000000 ≤ a.toNat →
      a.toNat + len ≤ 2 ^ 32 → Sep (G + o) l a len :=
    fun h1 h2 h3 => by rw [slotO]; exact hiC (by omega) h2 h3
  have sGC : ∀ {o : Word} {l : Nat}, o.toNat + l ≤ 0x60 → Sep (G + o) l RFC timeRfc3339Code.length :=
    fun h1 => sGX h1 (by rw [hRn]; decide) (by rw [hRn]; decide)
  have hPm : ∀ {Mx : Word → BitVec 8}, (∀ x, Sep H 0x90 x 1 → Mx x = m.mem x) →
      ∀ i, i < n + 4 → Mx (p + BitVec.ofNat 32 i) = m.mem (p + BitVec.ofNat 32 i) := fun hM i hi =>
    hM _ (sPG.symm.subR (c := i) (l := 1) (by omega))
  -- 0x10: the slice at `G + 4`, then `digits::<4>` into `G + 0x18`
  obtain ⟨m3, c3, u3⟩ := St.block rfcA u2.self hc2 rfcA_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, rfcA, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp2]
    exact ⟨⟨aligned_add hGa (by decide), sGC (by decide)⟩, aligned_add hGa (by decide), sGC (by decide)⟩)
  obtain ⟨Ma, hMa⟩ : ∃ Ma, memStore32 (memStore32 Ms (G + 4) p) (G + 8) (BitVec.ofNat 32 n) = Ma := ⟨_, rfl⟩
  have eMa : (runBlock rfcA (Ms, reg m2)).1 = Ma := by
    simp +decide only [runBlock, BInstr.run, rfcA, upd_app, ↓reduceIte]
    rw [sp2, r2 a1 (by decide), ha1, r2 a2 (by decide), ha2, ← hMa]
  have u3' : St Ma RFC m3 0x1A (reg m3) := ⟨u3.pc, by rw [u3.mem, eMa], fun _ => rfl⟩
  have v3 : reg m3 a0 = G + 0x18 ∧ reg m3 a1 = G + 4 ∧ reg m3 21 = out := by
    simp +decide only [u3.regs, runBlock, BInstr.run, rfcA, upd_app, ↓reduceIte]
    rw [sp2, r2 a0 (by decide), ha0, u2.self.zero]
    exact ⟨rfl, rfl, zw _⟩
  have K3 : ∀ q, q.val ∉ [21, 10, 11] → reg m3 q = reg m2 q := fun q hq => by
    have hd : q ∉ rfcA.filterMap BInstr.dst := by
      simp only [rfcA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [u3.regs, runBlock_reg _ _ _ q u2.self.zero hd]
  have IMa : ∀ x, Sep H 0x90 x 1 → Ma x = m.mem x := fun x hx => by
    rw [← hMa, memStore32_get_sep (sGw (o := 8) (by decide) hx), memStore32_get_sep (sGw (o := 4) (by decide) hx),
      IMs x hx]
  have SMa : ∀ c', 0x74 ≤ c' → c' < 0x90 → Ma (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
    fun c' h1 h2 => by
      rw [← hMa, memStore32_get_sep (sGv (o := 8) (by decide) h1 h2), memStore32_get_sep (sGv (o := 4) (by decide) h1 h2)]
  have hp4 : memBytes Ma p 4 = memBytes m.mem p 4 := by
    have := dn_memBytes_eq (hPm IMa) (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3'.callRa (cdR IMa) rfc_at_1a rfc_at_1e (cb := TD4) (by decide) (by decide)
  have r4 := PEnv.reg1 regs4 u3'.zero
  have hTD4n : TD4.toNat = (img% timeDigits4Address) := by decide
  have e44 : G + 4 + 4 = G + 8 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m5, c5, pc5, mem5, K5⟩ := timeDigits4_correct m4 (base := TD4) (out := G + 0x18) (d := G + 4) (p := p)
    (n := n) (retAddr := RFC + BitVec.ofNat 32 (0x1A + 8)) (by decide)
    (by rw [mem4]; exact cd hcF (by rw [hTD4n]; decide) (by rw [hTD4n]; decide) IMa) pc4
    (by rw [r4 a0 (by decide), v3.1]) (by rw [r4 a1 (by decide), v3.2.1]) (aligned_add hGa (by decide))
    (aligned_add hGa (by decide)) (by omega)
    (by rw [mem4, ← hMa, memLoad32_store32_sep (sGG (o := 8) (o' := 4) (by decide) (by decide) (by decide)),
      memLoad32_store32_same])
    (by rw [mem4, e44, ← hMa, memLoad32_store32_same])
    (sGX (o := 0x18) (l := 8) (by decide) (by decide) (by decide)) (sGX (o := 4) (l := 8) (by decide) (by decide) (by decide))
    (by
      have := (sPG.symm.sub (c := 0x34) (l := 8) (by decide)).subR (c := 0) (l := 4) (by omega)
      rwa [add_ofNat_zero, show H + BitVec.ofNat 32 0x34 = G + 4 from (eGk 4).symm] at this)
    (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at RFC (by decide) _ (by decide)))
  obtain ⟨Md, hMd⟩ : ∃ Md, digits4Mem Ma (G + 0x18) (G + 4) p n = Md := ⟨_, rfl⟩
  rw [mem4, hMd] at mem5
  have IMd : ∀ x, Sep H 0x90 x 1 → Md x = m.mem x := fun x hx => by
    rw [← hMd, digits4Mem_frame (sGw (o := 0x18) (by decide) hx) (sGw (o := 4) (by decide) hx), IMa x hx]
  have SMd : ∀ c', 0x74 ≤ c' → c' < 0x90 → Md (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
    fun c' h1 h2 => by
      rw [← hMd, digits4Mem_frame (sGv (o := 0x18) (by decide) h1 h2) (sGv (o := 4) (by decide) h1 h2),
        SMa c' h1 h2]
  have hc5 := cdR IMd
  have kk5 : ∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg m5 q = reg m q := fun q hq => by
    rw [K5 q (by revert hq; revert q; decide), r4 q (by revert hq; revert q; decide),
      K3 q (by revert hq; revert q; decide), r2 q (by revert hq; revert q; decide)]
  have sp5 : reg m5 sp = G := by rw [K5 sp (by decide), r4 sp (by decide), K3 sp (by decide), sp2]
  have r21_5 : reg m5 21 = out := by rw [K5 21 (by decide), r4 21 (by decide), v3.2.2]
  have pre5 : Steps m m5 := .cons d1 (c2.trans (c3.trans (c4.trans c5)))
  -- 0x22: the tag of `digits::<4>`'s result
  have u5 : St Md RFC m5 0x22 (reg m5) := ⟨by rw [pc5], mem5, fun _ => rfl⟩
  obtain ⟨m6, d6, u6⟩ := u5.lbu hc5 rfc_at_22 (off' := 0x26) (by decide)
  have a06 : reg m6 a0 = (Md (G + 0x18)).zeroExtend 32 := by
    rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5]
  have K6 : ∀ q, q ≠ a0 → reg m6 q = reg m5 q := fun q hq => by rw [u6.regs, upd_ne' hq u5.zero]
  by_cases hE : n < 4 ∨ readDigits 4 (memBytes m.mem p 4) = none
  · obtain ⟨e1, e19⟩ := digits4Mem_err (M := Ma) (out := G + 0x18) (d := G + 4) (p := p) (n := n) (by rwa [hp4])
    rw [hMd] at e1 e19
    obtain ⟨m7, d7, u7⟩ := u6.self.notTaken hc5 0x28 rfc_at_26 (by decide) (by rw [a06, e1, u6.self.zero]; rfl)
    have hy0 : readDigits 4 (memBytes m.mem p n) = none := by
      by_cases h4 : 4 ≤ n
      · rcases hE with h | h
        · omega
        · rw [readDigits4_mem m.mem p h4, h]; rfl
      · exact readDigits_short 4 _ (by rw [memBytes_length]; omega)
    exact fin28 (pre5.trans (.cons d6 (.single d7))) u7.self IMd SMd (by rw [u7.regs, K6 sp (by decide), sp5])
      (by rw [u7.regs, K6 21 (by decide), r21_5])
      (fun q hq => by rw [u7.regs, K6 q (by revert hq; revert q; decide), kk5 q hq])
      (by rw [rfc3339_eq, hy0]; rfl) e19
  obtain ⟨⟨v, r⟩, hR⟩ : ∃ vr, readDigits 4 (memBytes m.mem p 4) = some vr := by
    cases h : readDigits 4 (memBytes m.mem p 4) with
    | none => exact absurd (.inr h) hE
    | some vr => exact ⟨vr, rfl⟩
  have hn4 : 4 ≤ n := by
    rcases Nat.lt_or_ge n 4 with h | h
    · exact absurd (.inl h) hE
    · exact h
  have hy : readDigits 4 (memBytes m.mem p n) = some (v, memBytes m.mem (p + 4) (n - 4)) := by
    rw [readDigits4_mem m.mem p hn4, hR]; rfl
  have hv : v < 10 ^ 4 := (readDigits_rest m.mem 4 p 4 v r (by decide) hR).2
  have hred0 : rfc3339 (memBytes m.mem p n) = rfcRest v (memBytes m.mem (p + 4) (n - 4)) := by
    rw [rfc3339_eq, hy]; rfl
  obtain ⟨t0, tv, tp, tn⟩ := digits4Mem_ok (M := Ma) (out := G + 0x18) (d := G + 4) hn4 (by rw [hp4]; exact hR)
    (sGG (o := 0x18) (o' := 4) (by decide) (by decide) (by decide))
  rw [hMd] at t0 tv tp tn
  rw [e44] at tn
  obtain ⟨m7, d7, u7⟩ := u6.self.taken hc5 0x38 rfc_at_26 (by decide) (by rw [a06, t0, u6.self.zero]; rfl)
  have sp7 : reg m7 sp = G := by rw [u7.regs, K6 sp (by decide), sp5]
  -- 0x38: the year, and zeros over the compact buffer
  obtain ⟨m8, c8, u8⟩ := St.block rfcB u7.self hc5 rfcB_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, rfcB, upd_app, ↓reduceIte, and_true]
    rw [sp7]
    exact ⟨aligned_add hGa (by decide), ⟨aligned_add hGa (by decide), sGC (by decide)⟩, aligned_add hGa (by decide),
      sGC (by decide)⟩)
  obtain ⟨Mb, hMb⟩ : ∃ Mb, memStore32 (memStore32 Md (G + 0xC) 0) (G + 0x10) 0 = Mb := ⟨_, rfl⟩
  have eMb : (runBlock rfcB (Md, reg m7)).1 = Mb := by
    simp +decide only [runBlock, BInstr.run, rfcB, upd_app, ↓reduceIte]; rw [sp7, ← hMb]
  have u8' : St Mb RFC m8 0x3E (reg m8) := ⟨u8.pc, by rw [u8.mem, eMb], fun _ => rfl⟩
  have a1_8 : reg m8 a1 = BitVec.ofNat 32 v := by
    rw [u8.regs]; simp +decide only [runBlock, BInstr.run, rfcB, upd_app, ↓reduceIte]
    rw [sp7, show G + 0x1C = G + 0x18 + 4 by rw [BitVec.add_assoc]; rfl, tv]
  have K8 : ∀ q, q ≠ a1 → reg m8 q = reg m7 q := fun q hq => by
    have hd : q ∉ rfcB.filterMap BInstr.dst := by
      simp only [rfcB, List.filterMap_cons, List.filterMap_nil, BInstr.dst, List.mem_cons, List.mem_nil_iff,
        or_false]; exact hq
    rw [u8.regs, runBlock_reg _ _ _ q u7.self.zero hd]
  have sp8 : reg m8 sp = G := by rw [K8 sp (by decide), sp7]
  have IMb : ∀ x, Sep H 0x90 x 1 → Mb x = m.mem x := fun x hx => by
    rw [← hMb, memStore32_get_sep (sGw (o := 0x10) (by decide) hx), memStore32_get_sep (sGw (o := 0xC) (by decide) hx),
      IMd x hx]
  -- 0x3E
  obtain ⟨m9, d9, u9⟩ := u8'.sh (cdR IMb) rfc_at_3e (off' := 0x42) (by decide)
    (by rw [sp8]; have := aligned_add hGa (k := 0x14) (by decide); show (G + BitVec.ofNat 32 0x14).toNat % 2 = 0; omega)
  obtain ⟨Mc, hMc⟩ : ∃ Mc, memStore8 (memStore8 Mb (G + 0x14) 0) (G + 0x15) 0 = Mc := ⟨_, rfl⟩
  have u9' : St Mc RFC m9 0x42 (reg m9) := by
    have e : memStore8 (memStore8 Mb (reg m8 sp + 0x14) ((reg m8 x0).extractLsb' 0 8)) (reg m8 sp + 0x14 + 1)
        ((reg m8 x0).extractLsb' 8 8) = Mc := by
      rw [sp8, u8'.zero, BitVec.add_assoc, ← hMc]; rfl
    exact ⟨u9.pc, by rw [u9.mem, e], fun _ => rfl⟩
  have r9 : ∀ q, reg m9 q = reg m8 q := u9.regs
  have IMc : ∀ x, Sep H 0x90 x 1 → Mc x = m.mem x := fun x hx => by
    rw [← hMc, memStore8_ne (dn_sep1 (sGw (o := 0x15) (by decide) hx)), memStore8_ne (dn_sep1 (sGw (o := 0x14) (by decide) hx)),
      IMb x hx]
  have hc9 := cdR IMc
  have sp9 : reg m9 sp = G := by rw [r9, sp8]
  have lc4 : memLoad32 Mc (G + 4) = p + 4 := by
    rw [← hMc, memLoad32_store8_sep (sGG (o := 0x15) (o' := 4) (by decide) (by decide) (by decide)),
      memLoad32_store8_sep (sGG (o := 0x14) (o' := 4) (by decide) (by decide) (by decide)), ← hMb,
      memLoad32_store32_sep (sGG (o := 0x10) (o' := 4) (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (sGG (o := 0xC) (o' := 4) (by decide) (by decide) (by decide)), tp]
  have lc8 : memLoad32 Mc (G + 8) = BitVec.ofNat 32 (n - 4) := by
    rw [← hMc, memLoad32_store8_sep (sGG (o := 0x15) (o' := 8) (by decide) (by decide) (by decide)),
      memLoad32_store8_sep (sGG (o := 0x14) (o' := 8) (by decide) (by decide) (by decide)), ← hMb,
      memLoad32_store32_sep (sGG (o := 0x10) (o' := 8) (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (sGG (o := 0xC) (o' := 8) (by decide) (by decide) (by decide)), tn]
  -- 0x42: the separators at `G + 0x28`, and the loop's registers
  obtain ⟨m10, c10, u10⟩ := St.block rfcC u9' hc9 rfcC_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, rfcC, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp9]
    exact ⟨aligned_add hGa (by decide), aligned_add hGa (by decide), ⟨aligned_add hGa (by decide), sGC (by decide)⟩,
      sGC (by decide), ⟨aligned_add hGa (by decide), sGC (by decide)⟩, aligned_add hGa (by decide), sGC (by decide)⟩)
  obtain ⟨Me, hMe⟩ : ∃ Me, memStore32 (memStore32 (memStore8 (memStore32 Mc (G + 0x28) 0x3A542D2D) (G + 0x2C) 0x3A)
      (G + 0x30) 0) (G + 0x34) 0 = Me := ⟨_, rfl⟩
  have eMe : (runBlock rfcC (Mc, reg m9)).1 = Me := by
    simp +decide only [runBlock, BInstr.run, rfcC, upd_app, ↓reduceIte]; rw [sp9, ← hMe]; rfl
  have u10' : St Me RFC m10 0x66 (reg m10) := ⟨u10.pc, by rw [u10.mem, eMe], fun _ => rfl⟩
  have R10 : ∀ q, reg m10 q = (runBlock rfcC (Mc, reg m9)).2 q := u10.regs
  have K10 : ∀ q, q.val ∉ [10, 12, 13, 9, 18, 14, 15, 16] → reg m10 q = reg m9 q := fun q hq => by
    have hd : q ∉ rfcC.filterMap BInstr.dst := by
      simp only [rfcC, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [R10, runBlock_reg _ _ _ q u9'.zero hd]
  have a2_10 : reg m10 a2 = 10 := by
    rw [R10]; simp +decide only [runBlock, BInstr.run, rfcC, upd_app, ↓reduceIte]
  have IMe : ∀ x, Sep H 0x90 x 1 → Me x = m.mem x := fun x hx => by
    rw [← hMe, memStore32_get_sep (sGw (o := 0x34) (by decide) hx), memStore32_get_sep (sGw (o := 0x30) (by decide) hx),
      memStore8_ne (dn_sep1 (sGw (o := 0x2C) (by decide) hx)), memStore32_get_sep (sGw (o := 0x28) (by decide) hx),
      IMc x hx]
  obtain ⟨m11, d11, u11⟩ := u10'.notTaken (cdR IMe) 0x68 rfc_at_66 (by decide) (by rw [a2_10, u10'.zero]; rfl)
  have SMe : ∀ c', 0x74 ≤ c' → c' < 0x90 → Me (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
    fun c' h1 h2 => by
      rw [← hMe, memStore32_get_sep (sGv (o := 0x34) (by decide) h1 h2), memStore32_get_sep (sGv (o := 0x30) (by decide) h1 h2),
        memStore8_ne (dn_sep1 (sGv (o := 0x2C) (by decide) h1 h2)), memStore32_get_sep (sGv (o := 0x28) (by decide) h1 h2),
        ← hMc, memStore8_ne (dn_sep1 (sGv (o := 0x15) (by decide) h1 h2)),
        memStore8_ne (dn_sep1 (sGv (o := 0x14) (by decide) h1 h2)), ← hMb,
        memStore32_get_sep (sGv (o := 0x10) (by decide) h1 h2), memStore32_get_sep (sGv (o := 0xC) (by decide) h1 h2),
        SMd c' h1 h2]
  have peel : ∀ j, j < 5 → Me (G + BitVec.ofNat 32 (0x28 + j)) =
      memStore8 (memStore32 Mc (G + 0x28) 0x3A542D2D) (G + 0x2C) 0x3A (G + BitVec.ofNat 32 (0x28 + j)) := by
    intro j hj
    have hj' : (BitVec.ofNat 32 (0x28 + j)).toNat = 0x28 + j := by rw [BitVec.toNat_ofNat]; omega
    rw [← hMe, memStore32_get_sep (sGG (o := 0x34) (l := 4) (l' := 1) (by rw [hj']; right; show 0x28 + j + 1 ≤ 0x34; omega)
        (by decide) (by rw [hj']; show 0x28 + j + 1 ≤ 0x60; omega)),
      memStore32_get_sep (sGG (o := 0x30) (l := 4) (l' := 1) (by rw [hj']; right; show 0x28 + j + 1 ≤ 0x30; omega)
        (by decide) (by rw [hj']; show 0x28 + j + 1 ≤ 0x60; omega))]
  have n2C : ∀ j, j < 4 → memStore8 (memStore32 Mc (G + 0x28) 0x3A542D2D) (G + 0x2C) 0x3A (G + BitVec.ofNat 32 (0x28 + j)) =
      memStore32 Mc (G + 0x28) 0x3A542D2D (G + BitVec.ofNat 32 (0x28 + j)) := by
    intro j hj
    have hj' : (BitVec.ofNat 32 (0x28 + j)).toNat = 0x28 + j := by rw [BitVec.toNat_ofNat]; omega
    exact memStore8_ne (dn_sep1 (sGG (o := 0x2C) (l := 1) (l' := 1) (by rw [hj']; right; show 0x28 + j + 1 ≤ 0x2C; omega)
      (by decide) (by rw [hj']; show 0x28 + j + 1 ≤ 0x60; omega)))
  have hsep0 : ∀ j, j < 5 → Me (G + BitVec.ofNat 32 (0x28 + j)) = BitVec.ofNat 8 (sepB j) := by
    intro j hj
    rw [peel j hj]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [n2C 0 (by decide)]; exact (memStore32_bytes Mc (G + 0x28) 0x3A542D2D).1.trans (by decide)
    · rw [n2C 1 (by decide), ← add_ofNat_assoc]; exact (memStore32_bytes Mc (G + 0x28) 0x3A542D2D).2.1.trans (by decide)
    · rw [n2C 2 (by decide), ← add_ofNat_assoc]; exact (memStore32_bytes Mc (G + 0x28) 0x3A542D2D).2.2.1.trans (by decide)
    · rw [n2C 3 (by decide), ← add_ofNat_assoc]; exact (memStore32_bytes Mc (G + 0x28) 0x3A542D2D).2.2.2.trans (by decide)
    · exact (memStore8_same _ _ _).trans (by decide)
  have R11 : ∀ q, reg m11 q = reg m10 q := u11.regs
  have I0 : RfcInv m Ms G H out (p + 4) (n - 4) v 0 (if 0 = 5 then 0x96 else 0x68) Me m11 := by
    rw [if_neg (by decide)]
    exact {
      st := u11.self
      pre := pre5.trans (.cons d6 (.cons d7 (c8.trans (.cons d9 (c10.trans (.single d11))))))
      fr := IMe, sv := SMe, sep := hsep0
      cmp := fun i hi => absurd hi (by omega)
      seen := fun j hj => absurd hj (by omega)
      hL := by omega
      rsp := by rw [R11, K10 sp (by decide), sp9]
      r21 := by rw [R11, K10 21 (by decide), r9, K8 21 (by decide), u7.regs, K6 21 (by decide), r21_5]
      ra1 := by rw [R11, K10 a1 (by decide), r9, a1_8]
      ra0 := by rw [R11, R10]; simp +decide only [runBlock, BInstr.run, rfcC, upd_app, ↓reduceIte]; rw [sp9]; rfl
      ra2 := by rw [R11, a2_10]; rfl
      ra3 := by rw [R11, R10]; simp +decide only [runBlock, BInstr.run, rfcC, upd_app, ↓reduceIte]; rw [sp9]; rfl
      ra5 := by rw [R11, R10]; simp +decide only [runBlock, BInstr.run, rfcC, upd_app, ↓reduceIte]; rw [sp9, lc8]; exact zw _
      ra6 := by rw [R11, R10]; simp +decide only [runBlock, BInstr.run, rfcC, upd_app, ↓reduceIte]
      r9 := by rw [R11, R10]; simp +decide only [runBlock, BInstr.run, rfcC, upd_app, ↓reduceIte]; rw [sp9, lc4, show 3 * 0 = 0 from rfl, add_ofNat_zero]
      r18 := by rw [R11, R10]; simp +decide only [runBlock, BInstr.run, rfcC, upd_app, ↓reduceIte]; rw [sp9, lc8]
      kk := fun q hq => by
        rw [R11, K10 q (by revert hq; revert q; decide), r9, K8 q (by revert hq; revert q; decide), u7.regs,
          K6 q (by revert hq; revert q; decide), kk5 q hq] }
  have sQH : Sep (p + 4) (n - 4) H 0x90 := sPG.sub (c := 4) (l := n - 4) (by omega)
  rcases loop (q := p + 4) (L := n - 4) (v := v) (by omega) sQH hred0 5 0 Me m11 rfl I0 with h | ⟨Mt, nn, I5⟩
  · exact h
  obtain ⟨q, hq⟩ : ∃ q, p + 4 = q := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, n - 4 = L := ⟨_, rfl⟩
  rw [hq, hLd] at I5 sQH hred0
  have hLb : L < 2 ^ 30 := by omega
  have hsep : sepOk m.mem q L := ⟨by have := I5.hL; omega, fun k hk => I5.seen k hk⟩
  have hred := hred0.trans ((rfcRest_mem m.mem q L v).1 hsep)
  have hc96 := cdR I5.fr
  -- 0x96: the slice of the ten digits at `G + 0x3C`, then `date_time`
  obtain ⟨m12, c12, u12⟩ := St.block rfcD I5.st hc96 rfcD_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, rfcD, upd_app, ↓reduceIte, and_true, true_and]
    rw [I5.rsp]
    exact ⟨⟨aligned_add hGa (by decide), sGC (by decide)⟩, aligned_add hGa (by decide), sGC (by decide)⟩)
  obtain ⟨Mf, hMf⟩ : ∃ Mf, memStore32 (memStore32 Mt (G + 0x3C) (G + 0xC)) (G + 0x40) 10 = Mf := ⟨_, rfl⟩
  have eMf : (runBlock rfcD (Mt, reg nn)).1 = Mf := by
    simp +decide only [runBlock, BInstr.run, rfcD, upd_app, ↓reduceIte]; rw [I5.rsp, ← hMf]; rfl
  have u12' : St Mf RFC m12 0xA2 (reg m12) := ⟨u12.pc, by rw [u12.mem, eMf], fun _ => rfl⟩
  have R12 : ∀ q, reg m12 q = (runBlock rfcD (Mt, reg nn)).2 q := u12.regs
  have v12 : reg m12 a0 = G + 0x18 ∧ reg m12 a1 = BitVec.ofNat 32 v ∧ reg m12 a2 = G + 0x3C := by
    simp +decide only [R12, runBlock, BInstr.run, rfcD, upd_app, ↓reduceIte]
    rw [I5.rsp, I5.ra1]; exact ⟨rfl, rfl, rfl⟩
  have K12 : ∀ q, q.val ∉ [10, 12] → reg m12 q = reg nn q := fun q hq => by
    have hd : q ∉ rfcD.filterMap BInstr.dst := by
      simp only [rfcD, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [R12, runBlock_reg _ _ _ q I5.st.zero hd]
  have IMf : ∀ x, Sep H 0x90 x 1 → Mf x = m.mem x := fun x hx => by
    rw [← hMf, memStore32_get_sep (sGw (o := 0x40) (by decide) hx), memStore32_get_sep (sGw (o := 0x3C) (by decide) hx),
      I5.fr x hx]
  have SMf : ∀ c', 0x74 ≤ c' → c' < 0x90 → Mf (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
    fun c' h1 h2 => by
      rw [← hMf, memStore32_get_sep (sGv (o := 0x40) (by decide) h1 h2),
        memStore32_get_sep (sGv (o := 0x3C) (by decide) h1 h2), I5.sv c' h1 h2]
  obtain ⟨m13, c13, pc13, mem13, regs13⟩ := u12'.callRa (cdR IMf) rfc_at_a2 rfc_at_a6 (cb := DT) (by decide)
    (by decide)
  have r13 := PEnv.reg1 regs13 u12'.zero
  have hDTn : DT.toNat = (img% dateTimeAddress) := by decide
  have hTDn : TD.toNat = (img% timeDigits2Address) := by decide
  have hGo : ∀ o, o ≤ 0x60 → (G + BitVec.ofNat 32 o).toNat = G.toNat + o := fun o h => by
    rw [eGk, hHc _ (by omega)]; omega
  have sGH : ∀ {o : Word} {l : Nat}, o.toNat + l ≤ 0x60 → Sep (G + o) l H 0x30 := fun {o l} h => by
    rw [slotO]
    have := offs (c := 0x30 + o.toNat) (n := l) (e := 0) (k := 0x30) (Or.inr (by omega)) (by omega) (by decide)
    rwa [add_ofNat_zero] at this
  have e3C4 : G + 0x3C + 4 = G + 0x40 := by rw [BitVec.add_assoc]; rfl
  have hcmp : memBytes Mf (G + 0xC) 10 = compactOf m.mem q := by
    show (List.range 10).map _ = (List.range 10).map _
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have hi' : (BitVec.ofNat 32 (0xC + i)).toNat = 0xC + i := by rw [BitVec.toNat_ofNat]; omega
    have e : G + 0xC + BitVec.ofNat 32 i = G + BitVec.ofNat 32 (0xC + i) := add_ofNat_assoc G 0xC i
    rw [e, ← hMf, memStore32_get_sep (sGG (o := 0x40) (l := 4) (l' := 1)
        (by rw [hi']; right; show 0xC + i + 1 ≤ 0x40; omega) (by decide) (by rw [hi']; show 0xC + i + 1 ≤ 0x60; omega)),
      memStore32_get_sep (sGG (o := 0x3C) (l := 4) (l' := 1)
        (by rw [hi']; right; show 0xC + i + 1 ≤ 0x3C; omega) (by decide) (by rw [hi']; show 0xC + i + 1 ≤ 0x60; omega)),
      I5.cmp i (by omega)]
  obtain ⟨m14, c14, pc14, sp14, K14, hS14, hN14, fr14⟩ := dateTime_correct m13 (sp0 := G) (out := G + 0x18)
    (d := G + 0x3C) (p := G + 0xC) (Y := BitVec.ofNat 32 v) (retAddr := RFC + BitVec.ofNat 32 (0xA2 + 8)) (n := 10)
    (by rw [mem13]; exact cd hcD (by rw [hDTn]; decide) (by rw [hDTn]; decide) IMf)
    (by rw [mem13]; exact cd hcT (by rw [hTDn]; decide) (by rw [hTDn]; decide) IMf) pc13
    (by rw [r13 a0 (by decide), v12.1]) (by rw [r13 a1 (by decide), v12.2.1]) (by rw [r13 a2 (by decide), v12.2.2])
    (by rw [regs13]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at RFC (by decide) _ (by decide)))
    (by rw [r13 sp (by decide), K12 sp (by decide), I5.rsp]) hGa (by omega) (by omega)
    (by show (G + BitVec.ofNat 32 0x18).toNat + 16 ≤ 0x40000000; rw [hGo _ (by decide)]; omega)
    (aligned_add hGa (by decide))
    (by show (G + BitVec.ofNat 32 0x3C).toNat + 8 ≤ 0x40000000; rw [hGo _ (by decide)]; omega)
    (aligned_add hGa (by decide)) (by decide)
    (by rw [mem13, ← hMf, memLoad32_store32_sep (sGG (o := 0x40) (o' := 0x3C) (by decide) (by decide) (by decide)),
      memLoad32_store32_same])
    (by rw [mem13, e3C4, ← hMf, memLoad32_store32_same]; rfl)
    (by rw [eG0]; exact sGH (by decide)) (by rw [eG0]; exact sGH (by decide))
    (sGG (by decide) (by decide) (by decide))
    (by rw [eG0]; exact sGH (by decide)) (sGG (by decide) (by decide) (by decide))
    (sGG (by decide) (by decide) (by decide))
  rw [mem13, hcmp] at hS14 hN14
  rw [mem13] at fr14
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2 ^ 32)] at hS14 hN14
  -- back from `date_time`
  have I14 : ∀ x, Sep H 0x90 x 1 → m14.mem x = m.mem x := fun x hx => by
    have h1 : Sep (G + 0xFFFFFFD0) 0x30 x 1 := by
      rw [eG0]; have := inH (c := 0) (l := 0x30) hx (by decide); rwa [add_ofNat_zero] at this
    rw [fr14 x h1 (sGw (o := 0x18) (by decide) hx) (sGw (o := 0x3C) (by decide) hx), IMf x hx]
  have S14 : ∀ c', 0x74 ≤ c' → c' < 0x90 → m14.mem (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
    fun c' h1 h2 => by
      have e1 : Sep (G + 0xFFFFFFD0) 0x30 (H + BitVec.ofNat 32 c') 1 := by
        rw [eG0]; have := offs (c := 0) (n := 0x30) (e := c') (k := 1) (by omega) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      rw [fr14 _ e1 (sGv (o := 0x18) (by decide) h1 h2) (sGv (o := 0x3C) (by decide) h1 h2), SMf c' h1 h2]
  have hc14 := cdR I14
  have u14 : St m14.mem RFC m14 0xAA (reg m14) := ⟨by rw [pc14], rfl, fun _ => rfl⟩
  have kk14 : ∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27, 9, 18, 21] → reg m14 q = reg nn q := fun q hq => by
    rw [K14 q (by revert hq; revert q; decide), r13 q (by revert hq; revert q; decide),
      K12 q (by revert hq; revert q; decide)]
  have pre14 : Steps m m14 := I5.pre.trans (c12.trans (c13.trans c14))
  obtain ⟨m15, d15, u15⟩ := u14.lbu hc14 rfc_at_aa (off' := 0xAE) (by decide)
  have a015 : reg m15 a0 = (m14.mem (G + 0x18)).zeroExtend 32 := by
    rw [u15.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp14]
  have K15 : ∀ q, q ≠ a0 → reg m15 q = reg m14 q := fun q hq => by rw [u15.regs, upd_ne' hq u14.zero]
  have kk15 : ∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg m15 q = reg m q := fun q hq => by
    rw [K15 q (by revert hq; revert q; decide), kk14 q (by revert hq; revert q; decide), I5.kk q hq]
  have sp15 : reg m15 sp = G := by rw [K15 sp (by decide), sp14]
  have r21_15 : reg m15 21 = out := by rw [K15 21 (by decide), kk14 21 (by decide), I5.r21]
  cases hd : readDateTime v (compactOf m.mem q) with
  | none =>
    obtain ⟨t1, t19⟩ := hN14 hd
    obtain ⟨m16, d16, u16⟩ := u15.self.taken hc14 0x28 rfc_at_ae (by decide) (by rw [a015, t1, u15.self.zero]; rfl)
    exact fin28 (pre14.trans (.cons d15 (.single d16))) u16.self I14 S14 (by rw [u16.regs, sp15])
      (by rw [u16.regs, r21_15]) (fun q hq => by rw [u16.regs, kk15 q hq]) (by rw [hred, hd]; rfl) t19
  | some tr =>
  obtain ⟨t, rest2⟩ := tr
  obtain ⟨ht, t0', tlo, thi, -, -, -⟩ := hS14 t rest2 hd
  obtain ⟨m16, d16, u16⟩ := u15.self.notTaken hc14 0xB0 rfc_at_ae (by decide) (by rw [a015, t0', u15.self.zero]; rfl)
  have pre16 : Steps m m16 := pre14.trans (.cons d15 (.single d16))
  have hspecT : rfc3339 (memBytes m.mem p n) = rfcTail (memBytes m.mem (q + BitVec.ofNat 32 15) (L - 15)) t := by
    rw [hred, hd]; rfl
  have hT := rfcTail_mem m.mem (q + BitVec.ofNat 32 15) (L - 15) t
  have hQm : ∀ {Mx : Word → BitVec 8}, (∀ x, Sep H 0x90 x 1 → Mx x = m.mem x) →
      ∀ i, i < L → Mx (q + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i) := fun hM i hi =>
    hM _ (sQH.symm.subR (c := i) (l := 1) (by omega))
  have k16 : ∀ r, r ≠ a0 → reg m16 r = reg m14 r := fun r hr => by rw [u16.regs, K15 r hr]
  have bad : ∀ {Mx : Word → BitVec 8} {nx : Machine}, Steps m nx → St Mx RFC nx 0x120 (reg nx) →
      (∀ x, Sep H 0x90 x 1 → Mx x = m.mem x) →
      (∀ c', 0x74 ≤ c' → c' < 0x90 → Mx (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      (∀ r, r.val ∈ [2, 3, 4, 21, 22, 23, 24, 25, 26, 27] → reg nx r = reg m14 r) →
      ¬ rfcOk m.mem (q + BitVec.ofNat 32 15) (L - 15) → ∃ m', rfcPost m m' sp0 out p retAddr H n :=
    fun pre st hI hS hk hno =>
      fin120 pre st hI hS (by rw [hk sp (by decide), sp14]) (by rw [hk 21 (by decide), kk14 21 (by decide), I5.r21])
        (fun r hr => by
          rw [hk r (by revert hr; revert r; decide), kk14 r (by revert hr; revert r; decide), I5.kk r hr])
        (by rw [hspecT]; exact hT.2 hno)
  have good : ∀ {Mx : Word → BitVec 8} {nx : Machine}, Steps m nx → St Mx RFC nx 0x116 (reg nx) →
      (∀ x, Sep H 0x90 x 1 → Mx x = m.mem x) →
      (∀ c', 0x74 ≤ c' → c' < 0x90 → Mx (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      (∀ r, r.val ∈ [2, 3, 4, 21, 22, 23, 24, 25, 26, 27] → reg nx r = reg m14 r) → reg nx a0 = 0 →
      reg nx 20 = BitVec.ofNat 32 (t % 2 ^ 32) → reg nx 19 = BitVec.ofNat 32 (t / 2 ^ 32) →
      rfcOk m.mem (q + BitVec.ofNat 32 15) (L - 15) → ∃ m', rfcPost m m' sp0 out p retAddr H n :=
    fun pre st hI hS hk h0 h20 h19 hok =>
      finOk pre st hI hS (by rw [hk sp (by decide), sp14]) (by rw [hk 21 (by decide), kk14 21 (by decide), I5.r21])
        (fun r hr => by
          rw [hk r (by revert hr; revert r; decide), kk14 r (by revert hr; revert r; decide), I5.kk r hr])
        h0 h20 h19 ht (by rw [hspecT]; exact hT.1 hok)
  -- 0xB0: is the rest empty?
  obtain ⟨m17, d17, u17⟩ := u16.self.aluImm hc14 rfc_at_b0 (off' := 0xB2) (by decide)
  have k17 : ∀ r, r.val ∈ [2, 3, 4, 9, 18, 21, 22, 23, 24, 25, 26, 27] → reg m17 r = reg m14 r := fun r hr => by
    rw [u17.regs, upd_ne' (by revert hr; revert r; decide) u16.self.zero, k16 r (by revert hr; revert r; decide)]
  have a017 : reg m17 a0 = 15 := by rw [u17.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u16.self.zero]; rfl
  have s2_17 : reg m17 18 = BitVec.ofNat 32 L := by rw [k17 18 (by decide), kk14 18 (by decide), I5.r18]
  have pre17 : Steps m m17 := pre16.trans (.single d17)
  by_cases hL15 : L = 15
  · obtain ⟨m18, d18, u18⟩ := u17.self.taken hc14 0x120 rfc_at_b2 (by decide) (by
      rw [s2_17, a017, rfc_beq15 _ (by omega)]; exact decide_eq_true hL15)
    exact bad (pre17.trans (.single d18)) u18.self I14 S14 (fun r hr => by rw [u18.regs, k17 r (by
      revert hr; revert r; decide)]) (fun h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega)
  obtain ⟨m18, d18, u18⟩ := u17.self.notTaken hc14 0xB6 rfc_at_b2 (by decide) (by
    rw [s2_17, a017, rfc_beq15 _ (by omega)]; exact decide_eq_false hL15)
  have hL16 : 16 ≤ L := by have := I5.hL; omega
  -- 0xB6: the byte after the seconds, and the time
  have sp18 : reg m18 sp = G := by rw [u18.regs, k17 sp (by decide), sp14]
  have s1_18 : reg m18 9 = q + BitVec.ofNat 32 15 := by rw [u18.regs, k17 9 (by decide), kk14 9 (by decide), I5.r9]
  obtain ⟨m19, c19, u19⟩ := St.block rfcE u18.self hc14 rfcE_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, rfcE, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp18]
    exact ⟨aligned_add hGa (by decide), aligned_add hGa (by decide)⟩)
  have R19 : ∀ r, reg m19 r = (runBlock rfcE (m14.mem, reg m18)).2 r := u19.regs
  have u19' : St m14.mem RFC m19 0xC6 (reg m19) := ⟨u19.pc, by rw [u19.mem]; rfl, fun _ => rfl⟩
  have bz : m14.mem (q + BitVec.ofNat 32 15) = m.mem (q + BitVec.ofNat 32 15) := hQm I14 15 (by omega)
  have e20 : G + 0x20 = G + 0x18 + 8 := by rw [BitVec.add_assoc]; rfl
  have e24 : G + 0x24 = G + 0x18 + 0xC := by rw [BitVec.add_assoc]; rfl
  have v19 : reg m19 a2 = aluEval .add ((m.mem (q + BitVec.ofNat 32 15)).zeroExtend 32) 0xFFFFFFD2 ∧
      reg m19 a1 = (m.mem (q + BitVec.ofNat 32 15)).zeroExtend 32 ∧
      reg m19 20 = BitVec.ofNat 32 (t % 2 ^ 32) ∧ reg m19 19 = BitVec.ofNat 32 (t / 2 ^ 32) ∧
      reg m19 a0 = BitVec.ofNat 32 (L - 16) := by
    simp +decide only [R19, runBlock, BInstr.run, rfcE, upd_app, ↓reduceIte]
    simp only [add_lit_zero]
    rw [sp18, s1_18, bz, e20, e24, tlo, thi, u18.regs, k17 18 (by decide), kk14 18 (by decide), I5.r18]
    exact ⟨rfl, rfl, rfl, rfl, rfc_wsub L 16 _ rfl hL16 (by omega) (by decide)⟩
  obtain ⟨v19a2, v19a1, v19s4, v19s3, v19a0⟩ := v19
  have k19 : ∀ r, r.val ∈ [2, 3, 4, 9, 18, 21, 22, 23, 24, 25, 26, 27] → reg m19 r = reg m14 r := fun r hr => by
    have hd' : r ∉ rfcE.filterMap BInstr.dst := by
      simp only [rfcE, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hr; revert r; decide
    rw [R19, runBlock_reg _ _ _ r u18.self.zero hd', u18.regs, k17 r hr]
  have pre19 : Steps m m19 := pre17.trans (.cons d18 c19)
  have hb15 : (m.mem (q + BitVec.ofNat 32 15)).toNat < 256 := (m.mem _).isLt
  by_cases hdot : (m.mem (q + BitVec.ofNat 32 15)).toNat = 0x2E
  rotate_left
  · -- `Z` alone
    obtain ⟨m20, d20, u20⟩ := u19'.notTaken hc14 0xC8 rfc_at_c6 (by decide) (by
      rw [v19a2, u19'.zero, gnt_isDot]; exact decide_eq_false hdot)
    obtain ⟨m21, d21, u21⟩ := u20.self.aluImm hc14 rfc_at_c8 (off' := 0xCC) (by decide)
    have a121 : reg m21 a1 = aluEval .add ((m.mem (q + BitVec.ofNat 32 15)).zeroExtend 32) 0xFFFFFFA6 := by
      rw [u21.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u20.regs, v19a1]
    have k21 : ∀ r, r ≠ a1 → reg m21 r = reg m19 r := fun r hr => by
      rw [u21.regs, upd_ne' hr u20.self.zero, u20.regs]
    have pre21 : Steps m m21 := pre19.trans (.cons d20 (.single d21))
    by_cases hz : (m.mem (q + BitVec.ofNat 32 15)).toNat = 0x5A
    rotate_left
    · obtain ⟨m22, d22, u22⟩ := u21.self.taken hc14 0x120 rfc_at_cc (by decide) (by
        rw [a121, u21.self.zero, gnt_isZ, decide_eq_false hz]; rfl)
      exact bad (pre21.trans (.single d22)) u22.self I14 S14
        (fun r hr => by rw [u22.regs, k21 r (by revert hr; revert r; decide), k19 r (by revert hr; revert r; decide)])
        (fun h => by
          rcases h with ⟨_, h⟩ | ⟨_, h, _⟩
          · exact hz h
          · exact hdot h)
    obtain ⟨m22, d22, u22⟩ := u21.self.notTaken hc14 0xCE rfc_at_cc (by decide) (by
      rw [a121, u21.self.zero, gnt_isZ, decide_eq_true hz]; rfl)
    have a022 : reg m22 a0 = BitVec.ofNat 32 (L - 16) := by rw [u22.regs, k21 a0 (by decide), v19a0]
    by_cases hL16' : L - 16 = 0
    · obtain ⟨m23, d23, u23⟩ := u22.self.taken hc14 0x116 rfc_at_ce (by decide) (by
        rw [a022, u22.self.zero, dn_beq0 _ (by omega)]; exact decide_eq_true hL16')
      exact good (pre21.trans (.cons d22 (.single d23))) u23.self I14 S14
        (fun r hr => by
          rw [u23.regs, u22.regs, k21 r (by revert hr; revert r; decide), k19 r (by revert hr; revert r; decide)])
        (by rw [u23.regs, a022, hL16']; rfl)
        (by rw [u23.regs, u22.regs, k21 20 (by decide), v19s4])
        (by rw [u23.regs, u22.regs, k21 19 (by decide), v19s3])
        (.inl ⟨by omega, hz⟩)
    obtain ⟨m23, d23, u23⟩ := u22.self.notTaken hc14 0xD0 rfc_at_ce (by decide) (by
      rw [a022, u22.self.zero, dn_beq0 _ (by omega)]; exact decide_eq_false hL16')
    obtain ⟨m24, d24, u24⟩ := u23.self.jump hc14 rfc_at_d0 (off' := 0x120) (by decide) (by rw [u23.self.pc]; decide)
    exact bad (pre21.trans (.cons d22 (.cons d23 (.single d24)))) u24.self I14 S14
      (fun r hr => by
        rw [u24.regs, u23.regs, u22.regs, k21 r (by revert hr; revert r; decide),
          k19 r (by revert hr; revert r; decide)])
      (fun h => by
        rcases h with ⟨h, _⟩ | ⟨_, h, _⟩
        · omega
        · exact hdot h)
  -- `.`, digits, and `Z`
  obtain ⟨m20, d20, u20⟩ := u19'.taken hc14 0xEE rfc_at_c6 (by decide) (by
    rw [v19a2, u19'.zero, gnt_isDot]; exact decide_eq_true hdot)
  have pre20 : Steps m m20 := pre19.trans (.single d20)
  by_cases hL16' : L - 16 = 0
  · obtain ⟨m21, d21, u21⟩ := u20.self.taken hc14 0x120 rfc_at_ee (by decide) (by
      rw [u20.regs, v19a0, u20.self.zero, dn_beq0 _ (by omega)]; exact decide_eq_true hL16')
    exact bad (pre20.trans (.single d21)) u21.self I14 S14
      (fun r hr => by rw [u21.regs, u20.regs, k19 r (by revert hr; revert r; decide)])
      (fun h => by
        rcases h with ⟨_, h⟩ | ⟨h, _⟩
        · rw [hdot] at h; cases h
        · omega)
  obtain ⟨m21, d21, u21⟩ := u20.self.notTaken hc14 0xF0 rfc_at_ee (by decide) (by
    rw [u20.regs, v19a0, u20.self.zero, dn_beq0 _ (by omega)]; exact decide_eq_false hL16')
  obtain ⟨m22, d22, u22⟩ := u21.self.aluImm hc14 rfc_at_f0 (off' := 0xF4) (by decide)
  have a022 : reg m22 a0 = BitVec.ofNat 32 (L - 17) := by
    rw [u22.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [u21.regs, u20.regs, k19 18 (by decide), kk14 18 (by decide), I5.r18]
    exact rfc_wsub L 17 _ rfl (by omega) (by omega) (by decide)
  have k22 : ∀ r, r ≠ a0 → reg m22 r = reg m19 r := fun r hr => by
    rw [u22.regs, upd_ne' hr u21.self.zero, u21.regs, u20.regs]
  have pre22 : Steps m m22 := pre20.trans (.cons d21 (.single d22))
  by_cases hL17 : L - 17 = 0
  · obtain ⟨m23, d23, u23⟩ := u22.self.taken hc14 0x120 rfc_at_f4 (by decide) (by
      rw [a022, u22.self.zero, dn_beq0 _ (by omega)]; exact decide_eq_true hL17)
    exact bad (pre22.trans (.single d23)) u23.self I14 S14
      (fun r hr => by rw [u23.regs, k22 r (by revert hr; revert r; decide), k19 r (by revert hr; revert r; decide)])
      (fun h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega)
  obtain ⟨m23, d23, u23⟩ := u22.self.notTaken hc14 0xF6 rfc_at_f4 (by decide) (by
    rw [a022, u22.self.zero, dn_beq0 _ (by omega)]; exact decide_eq_false hL17)
  sorry

end C3.RV32
