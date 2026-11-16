import C3BootProofs.Proofs.DateTime

/-!
# `time::generalized_time`, as compiled

`c3_verify::time::generalized_time` reads a four-digit year with an inlined
`digits::<4>`, calls `date_time` for the rest, and then accepts `Z` alone or
a fraction of digits not ending in `0` followed by `Z`.
`generalizedTime_correct` matches it to `Spec.Time`'s `generalizedTime`.
-/

namespace C3.RV32

open C3.Image

abbrev GNT : Word := BitVec.ofNat 32 generalizedTimeAddress

section
set_option maxRecDepth 20000
theorem gnt_at_0 : fetchRel generalizedTimeCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem gnt_at_2 : fetchRel generalizedTimeCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem gnt_at_4 : fetchRel generalizedTimeCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem gnt_at_6 : fetchRel generalizedTimeCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem gnt_at_8 : fetchRel generalizedTimeCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem gnt_at_a : fetchRel generalizedTimeCode 0xA = some (.aluImm .add a4 x0 0x4, 2) := by decide
theorem gnt_at_c : fetchRel generalizedTimeCode 0xC = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem gnt_at_e : fetchRel generalizedTimeCode 0xE = some (.branch .bltu a2 a4 0x4A, 4) := by decide
theorem gnt_at_12 : fetchRel generalizedTimeCode 0x12 = some (.aluImm .add (9 : Fin 32) x0 0x0, 2) := by decide
theorem gnt_at_14 : fetchRel generalizedTimeCode 0x14 = some (.aluImm .add a0 a1 0x4, 4) := by decide
theorem gnt_at_18 : fetchRel generalizedTimeCode 0x18 = some (.aluImm .add a2 a2 0xFFFFFFFC, 2) := by decide
theorem gnt_at_1a : fetchRel generalizedTimeCode 0x1A = some (.store .sw sp a0 0x8, 2) := by decide
theorem gnt_at_1c : fetchRel generalizedTimeCode 0x1C = some (.store .sw sp a2 0xC, 2) := by decide
theorem gnt_at_1e : fetchRel generalizedTimeCode 0x1E = some (.aluImm .add a0 x0 0xF6, 4) := by decide
theorem gnt_at_22 : fetchRel generalizedTimeCode 0x22 = some (.aluImm .add a2 x0 0xA, 2) := by decide
theorem gnt_at_24 : fetchRel generalizedTimeCode 0x24 = some (.branch .beq a4 x0 0x4C, 2) := by decide
theorem gnt_at_26 : fetchRel generalizedTimeCode 0x26 = some (.load .lbu (8 : Fin 32) a1 0x0, 4) := by decide
theorem gnt_at_2a : fetchRel generalizedTimeCode 0x2A = some (.aluImm .add a5 (8 : Fin 32) 0xFFFFFFC6, 4) := by decide
theorem gnt_at_2e : fetchRel generalizedTimeCode 0x2E = some (.aluImm .and a5 a5 0xFF, 4) := by decide
theorem gnt_at_32 : fetchRel generalizedTimeCode 0x32 = some (.branch .bltu a5 a0 0x26, 4) := by decide
theorem gnt_at_36 : fetchRel generalizedTimeCode 0x36 = some (.alu .mulhu a3 (9 : Fin 32) a2, 4) := by decide
theorem gnt_at_3a : fetchRel generalizedTimeCode 0x3A = some (.aluImm .add a5 x0 0x6, 2) := by decide
theorem gnt_at_3c : fetchRel generalizedTimeCode 0x3C = some (.branch .bne a3 x0 0x1E, 2) := by decide
theorem gnt_at_3e : fetchRel generalizedTimeCode 0x3E = some (.alu .mul a3 (9 : Fin 32) a2, 4) := by decide
theorem gnt_at_42 : fetchRel generalizedTimeCode 0x42 = some (.aluImm .add (9 : Fin 32) (8 : Fin 32) 0xFFFFFFD0, 4) := by decide
theorem gnt_at_46 : fetchRel generalizedTimeCode 0x46 = some (.aluImm .and (9 : Fin 32) (9 : Fin 32) 0xFF, 4) := by decide
theorem gnt_at_4a : fetchRel generalizedTimeCode 0x4A = some (.alu .add (9 : Fin 32) (9 : Fin 32) a3, 2) := by decide
theorem gnt_at_4c : fetchRel generalizedTimeCode 0x4C = some (.alu .sltu a3 (9 : Fin 32) a3, 4) := by decide
theorem gnt_at_50 : fetchRel generalizedTimeCode 0x50 = some (.aluImm .add a1 a1 0x1, 2) := by decide
theorem gnt_at_52 : fetchRel generalizedTimeCode 0x52 = some (.aluImm .add a4 a4 0xFFFFFFFF, 2) := by decide
theorem gnt_at_54 : fetchRel generalizedTimeCode 0x54 = some (.branch .beq a3 x0 0xFFFFFFD0, 2) := by decide
theorem gnt_at_56 : fetchRel generalizedTimeCode 0x56 = some (.jal x0 0x4, 2) := by decide
theorem gnt_at_58 : fetchRel generalizedTimeCode 0x58 = some (.aluImm .add a5 x0 0x19, 2) := by decide
theorem gnt_at_5a : fetchRel generalizedTimeCode 0x5A = some (.store .sb (18 : Fin 32) a5 0x1, 4) := by decide
theorem gnt_at_5e : fetchRel generalizedTimeCode 0x5E = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem gnt_at_60 : fetchRel generalizedTimeCode 0x60 = some (.store .sb (18 : Fin 32) a2 0x0, 4) := by decide
theorem gnt_at_64 : fetchRel generalizedTimeCode 0x64 = some (.load .lw ra sp 0x2C, 2) := by decide
theorem gnt_at_66 : fetchRel generalizedTimeCode 0x66 = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem gnt_at_68 : fetchRel generalizedTimeCode 0x68 = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem gnt_at_6a : fetchRel generalizedTimeCode 0x6A = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem gnt_at_6c : fetchRel generalizedTimeCode 0x6C = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem gnt_at_6e : fetchRel generalizedTimeCode 0x6E = some (.jalr x0 ra 0x0, 2) := by decide
theorem gnt_at_70 : fetchRel generalizedTimeCode 0x70 = some (.aluImm .add a0 sp 0x10, 2) := by decide
theorem gnt_at_72 : fetchRel generalizedTimeCode 0x72 = some (.aluImm .add a2 sp 0x8, 2) := by decide
theorem gnt_at_74 : fetchRel generalizedTimeCode 0x74 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem gnt_at_76 : fetchRel generalizedTimeCode 0x76 = some (.auipc ra 0x0, 4) := by decide
theorem gnt_at_7a : fetchRel generalizedTimeCode 0x7A = some (.jalr ra ra 0xE0, 4) := by decide
theorem gnt_at_7e : fetchRel generalizedTimeCode 0x7E = some (.load .lbu a0 sp 0x10, 4) := by decide
theorem gnt_at_82 : fetchRel generalizedTimeCode 0x82 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem gnt_at_84 : fetchRel generalizedTimeCode 0x84 = some (.load .lbu a5 sp 0x11, 4) := by decide
theorem gnt_at_88 : fetchRel generalizedTimeCode 0x88 = some (.jal x0 0xFFFFFFD2, 2) := by decide
theorem gnt_at_8a : fetchRel generalizedTimeCode 0x8A = some (.load .lw a3 sp 0xC, 2) := by decide
theorem gnt_at_8c : fetchRel generalizedTimeCode 0x8C = some (.branch .beq a3 x0 0x66, 2) := by decide
theorem gnt_at_8e : fetchRel generalizedTimeCode 0x8E = some (.load .lw a4 sp 0x8, 2) := by decide
theorem gnt_at_90 : fetchRel generalizedTimeCode 0x90 = some (.load .lbu a5 a4 0x0, 4) := by decide
theorem gnt_at_94 : fetchRel generalizedTimeCode 0x94 = some (.load .lw a1 sp 0x18, 2) := by decide
theorem gnt_at_96 : fetchRel generalizedTimeCode 0x96 = some (.load .lw a0 sp 0x1C, 2) := by decide
theorem gnt_at_98 : fetchRel generalizedTimeCode 0x98 = some (.aluImm .add (9 : Fin 32) a5 0xFFFFFFD2, 4) := by decide
theorem gnt_at_9c : fetchRel generalizedTimeCode 0x9C = some (.aluImm .add a2 a3 0xFFFFFFFF, 4) := by decide
theorem gnt_at_a0 : fetchRel generalizedTimeCode 0xA0 = some (.branch .beq (9 : Fin 32) x0 0x12, 2) := by decide
theorem gnt_at_a2 : fetchRel generalizedTimeCode 0xA2 = some (.aluImm .add a3 a5 0xFFFFFFA6, 4) := by decide
theorem gnt_at_a6 : fetchRel generalizedTimeCode 0xA6 = some (.branch .bne a3 x0 0x4C, 2) := by decide
theorem gnt_at_a8 : fetchRel generalizedTimeCode 0xA8 = some (.branch .bne a2 x0 0x4A, 2) := by decide
theorem gnt_at_aa : fetchRel generalizedTimeCode 0xAA = some (.alu .add a3 x0 (18 : Fin 32), 2) := by decide
theorem gnt_at_ac : fetchRel generalizedTimeCode 0xAC = some (.store .sw a3 a1 0x8, 2) := by decide
theorem gnt_at_ae : fetchRel generalizedTimeCode 0xAE = some (.store .sw a3 a0 0xC, 2) := by decide
theorem gnt_at_b0 : fetchRel generalizedTimeCode 0xB0 = some (.jal x0 0xFFFFFFB0, 2) := by decide
theorem gnt_at_b2 : fetchRel generalizedTimeCode 0xB2 = some (.branch .beq a2 x0 0x40, 2) := by decide
theorem gnt_at_b4 : fetchRel generalizedTimeCode 0xB4 = some (.aluImm .add a4 a4 0x1, 2) := by decide
theorem gnt_at_b6 : fetchRel generalizedTimeCode 0xB6 = some (.aluImm .add a2 a3 0xFFFFFFFE, 4) := by decide
theorem gnt_at_ba : fetchRel generalizedTimeCode 0xBA = some (.alu .add a6 a4 a2, 4) := by decide
theorem gnt_at_be : fetchRel generalizedTimeCode 0xBE = some (.load .lbu a3 a6 0x0, 4) := by decide
theorem gnt_at_c2 : fetchRel generalizedTimeCode 0xC2 = some (.aluImm .add a3 a3 0xFFFFFFA6, 4) := by decide
theorem gnt_at_c6 : fetchRel generalizedTimeCode 0xC6 = some (.branch .bne a3 x0 0x2C, 2) := by decide
theorem gnt_at_c8 : fetchRel generalizedTimeCode 0xC8 = some (.aluImm .add a5 x0 0xA, 2) := by decide
theorem gnt_at_ca : fetchRel generalizedTimeCode 0xCA = some (.alu .add a3 x0 a2, 2) := by decide
theorem gnt_at_cc : fetchRel generalizedTimeCode 0xCC = some (.branch .beq a3 x0 0x14, 2) := by decide
theorem gnt_at_ce : fetchRel generalizedTimeCode 0xCE = some (.load .lbu (9 : Fin 32) a4 0x0, 4) := by decide
theorem gnt_at_d2 : fetchRel generalizedTimeCode 0xD2 = some (.aluImm .add a4 a4 0x1, 2) := by decide
theorem gnt_at_d4 : fetchRel generalizedTimeCode 0xD4 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFD0, 4) := by decide
theorem gnt_at_d8 : fetchRel generalizedTimeCode 0xD8 = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem gnt_at_da : fetchRel generalizedTimeCode 0xDA = some (.branch .bgeu (9 : Fin 32) a5 0x18, 4) := by decide
theorem gnt_at_de : fetchRel generalizedTimeCode 0xDE = some (.jal x0 0xFFFFFFEE, 2) := by decide
theorem gnt_at_e0 : fetchRel generalizedTimeCode 0xE0 = some (.branch .beq a2 x0 0x12, 2) := by decide
theorem gnt_at_e2 : fetchRel generalizedTimeCode 0xE2 = some (.aluImm .add a6 a6 0xFFFFFFFF, 2) := by decide
theorem gnt_at_e4 : fetchRel generalizedTimeCode 0xE4 = some (.branch .beq a6 x0 0xE, 4) := by decide
theorem gnt_at_e8 : fetchRel generalizedTimeCode 0xE8 = some (.load .lbu a2 a6 0x0, 4) := by decide
theorem gnt_at_ec : fetchRel generalizedTimeCode 0xEC = some (.aluImm .add a2 a2 0xFFFFFFD0, 4) := by decide
theorem gnt_at_f0 : fetchRel generalizedTimeCode 0xF0 = some (.branch .bne a2 x0 0xA, 2) := by decide
theorem gnt_at_f2 : fetchRel generalizedTimeCode 0xF2 = some (.aluImm .add a0 x0 0x19, 2) := by decide
theorem gnt_at_f4 : fetchRel generalizedTimeCode 0xF4 = some (.store .sb (18 : Fin 32) a0 0x1, 4) := by decide
theorem gnt_at_f8 : fetchRel generalizedTimeCode 0xF8 = some (.jal x0 0xFFFFFF66, 2) := by decide
theorem gnt_at_fa : fetchRel generalizedTimeCode 0xFA = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem gnt_at_fc : fetchRel generalizedTimeCode 0xFC = some (.jal x0 0xFFFFFFAE, 2) := by decide

end

def gntY1 : List BInstr :=
  [.lbu (8 : Fin 32) a1 0x0, .aluImm .add a5 (8 : Fin 32) 0xFFFFFFC6, .aluImm .and a5 a5 0xFF]
def gntY2 : List BInstr :=
  [.alu .mulhu a3 (9 : Fin 32) a2, .aluImm .add a5 x0 0x6]
def gntY3 : List BInstr :=
  [.alu .mul a3 (9 : Fin 32) a2, .aluImm .add (9 : Fin 32) (8 : Fin 32) 0xFFFFFFD0, .aluImm .and (9 : Fin 32) (9 : Fin 32) 0xFF, .alu .add (9 : Fin 32) (9 : Fin 32) a3, .alu .sltu a3 (9 : Fin 32) a3, .aluImm .add a1 a1 0x1, .aluImm .add a4 a4 0xFFFFFFFF]
def gntF1 : List BInstr :=
  [.lbu (9 : Fin 32) a4 0x0, .aluImm .add a4 a4 0x1, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFD0, .aluImm .add a3 a3 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem gntY1_end : blockEnd generalizedTimeCode 0x26 gntY1 = some 0x32 := by decide
theorem gntY2_end : blockEnd generalizedTimeCode 0x36 gntY2 = some 0x3C := by decide
theorem gntY3_end : blockEnd generalizedTimeCode 0x3E gntY3 = some 0x54 := by decide
theorem gntF1_end : blockEnd generalizedTimeCode 0xCE gntF1 = some 0xDA := by decide
end

/-- What `generalizedTime` accepts after the date and time. -/
def gtTail (rest : Bytes) (t : Nat) : Option Nat :=
  match rest with
  | [0x5A] => pure t
  | 0x2E :: fz =>
    match fz.reverse with
    | 0x5A :: frac =>
      require (!frac.isEmpty && frac.all (fun d => 48 ≤ d && d ≤ 57) && frac.head? != some 48) >>= fun _ => pure t
    | _ => none
  | _ => none

theorem generalizedTime_eq (content : Bytes) :
    generalizedTime content = (readDigits 4 content).bind fun yr =>
      (readDateTime yr.1 yr.2).bind fun tr => gtTail tr.2 tr.1 := by
  unfold generalizedTime gtTail
  simp only [bind, Option.bind]
  rcases readDigits 4 content with _ | ⟨y, r⟩
  · rfl
  · dsimp only
    rcases readDateTime y r with _ | ⟨t, r2⟩
    · rfl
    · rfl

theorem readDigits_succ_mem (M : Word → BitVec 8) (q : Word) (k m : Nat) :
    readDigits (k + 1) (memBytes M q (m + 1)) =
      if 48 ≤ (M q).toNat ∧ (M q).toNat ≤ 57 then
        (readDigits k (memBytes M (q + 1) m)).map fun vr => (((M q).toNat - 48) * 10 ^ k + vr.1, vr.2)
      else none := by
  rw [memBytes_succ]
  simp only [readDigits, require, bind, Option.bind, pure]
  by_cases h : 48 ≤ (M q).toNat ∧ (M q).toNat ≤ 57
  · have e : (48 ≤ (M q).toNat && (M q).toNat ≤ 57) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact h
    rw [if_pos h]
    simp only [e, ↓reduceIte]
    rcases readDigits k (memBytes M (q + 1) m) with _ | ⟨v, r⟩ <;> rfl
  · have e : (48 ≤ (M q).toNat && (M q).toNat ≤ 57) = false := Bool.eq_false_iff.mpr fun he => h (by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at he; exact he)
    rw [if_neg h]
    simp only [e, Bool.false_eq_true, ↓reduceIte]

theorem readDigits_short (k : Nat) (l : Bytes) (h : l.length < k) : readDigits k l = none := by
  induction k generalizing l with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      simp only [readDigits, require, bind, Option.bind, pure]
      rw [ih l (by simp at h; omega)]
      split <;> rfl

/-- The bytes after the date and time that `generalizedTime` accepts: `Z`
alone, or `.`, one or more digits not ending in `0`, and `Z`. -/
def gtOk (M : Word → BitVec 8) (q : Word) (L : Nat) : Prop :=
  (L = 1 ∧ (M q).toNat = 0x5A) ∨
  (3 ≤ L ∧ (M q).toNat = 0x2E ∧ (M (q + BitVec.ofNat 32 (L - 1))).toNat = 0x5A ∧
    (∀ i, i < L - 2 → 48 ≤ (M (q + BitVec.ofNat 32 (1 + i))).toNat ∧ (M (q + BitVec.ofNat 32 (1 + i))).toNat ≤ 57) ∧
    (M (q + BitVec.ofNat 32 (L - 2))).toNat ≠ 0x30)

theorem memBytes_snoc (M : Word → BitVec 8) (q : Word) (j : Nat) :
    memBytes M q (j + 1) = memBytes M q j ++ [(M (q + BitVec.ofNat 32 j)).toNat] := by
  rw [memBytes_split, memBytes_succ, memBytes_zero]

theorem memBytes_all (M : Word → BitVec 8) (q : Word) (j : Nat) (f : Nat → Bool) :
    (memBytes M q j).all f = true ↔ ∀ i, i < j → f (M (q + BitVec.ofNat 32 i)).toNat = true := by
  unfold memBytes
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply]

theorem gtTail_mem (M : Word → BitVec 8) (q : Word) (L t : Nat) :
    (gtOk M q L → gtTail (memBytes M q L) t = some t) ∧ (¬ gtOk M q L → gtTail (memBytes M q L) t = none) := by
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
    simp only [gtTail]
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
      have hhd : (memBytes M (q + 1) (j + 1)).reverse.head? = some (M (q + BitVec.ofNat 32 (j + 1 + 1 + 1 - 2))).toNat := by
        rw [memBytes_snoc, List.reverse_append]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.head?_cons]
        rw [show j + 1 + 1 + 1 - 2 = 1 + j by omega, ← add_ofNat_assoc]; rfl
      have hne : (memBytes M (q + 1) (j + 1)).reverse.isEmpty = false := by
        rw [memBytes_snoc, List.reverse_append]; rfl
      rw [hhd, hne]
      obtain ⟨w, hw⟩ : ∃ w, (M (q + BitVec.ofNat 32 (j + 1 + 1 + 1 - 2))).toNat = w := ⟨_, rfl⟩
      rw [hw]
      have hq1 : ∀ i, q + 1 + BitVec.ofNat 32 i = q + BitVec.ofNat 32 (1 + i) := fun i => by
        rw [← add_ofNat_assoc]; rfl
      simp only [hq1] at hall
      have hdig : (memBytes M (q + 1) (j + 1)).all (fun d => 48 ≤ d && d ≤ 57) = true ↔
          ∀ i, i < j + 1 + 1 + 1 - 2 → 48 ≤ (M (q + BitVec.ofNat 32 (1 + i))).toNat ∧
            (M (q + BitVec.ofNat 32 (1 + i))).toNat ≤ 57 := by
        rw [hall, show j + 1 + 1 + 1 - 2 = j + 1 by omega]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
      by_cases hA : (memBytes M (q + 1) (j + 1)).all (fun d => 48 ≤ d && d ≤ 57) = true
      · by_cases hw0 : w = 48
        · have hc : ((!false && true) && (some w != some 48)) = false := by rw [hw0]; rfl
          rw [hA, hc]
          refine ⟨fun h => ?_, fun _ => rfl⟩
          rcases h with ⟨h, _⟩ | ⟨_, _, _, _, h⟩
          · omega
          · rw [hw] at h; exact absurd hw0 h
        · have hc : ((!false && true) && (some w != some 48)) = true := by
            simp only [Bool.not_false, Bool.true_and, bne_iff_ne, ne_eq, Option.some.injEq]; exact hw0
          rw [hA, hc]
          refine ⟨fun _ => rfl, fun h => absurd (.inr ⟨by omega, hb, hz, hdig.mp hA, by rw [hw]; exact hw0⟩) h⟩
      · have hA' : (memBytes M (q + 1) (j + 1)).all (fun d => 48 ≤ d && d ≤ 57) = false := Bool.eq_false_iff.mpr hA
        rw [hA']
        refine ⟨fun h => ?_, fun _ => rfl⟩
        rcases h with ⟨h, _⟩ | ⟨_, _, _, h, _⟩
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
    · simp only [gtTail]
      split
      · next heq => exact absurd (List.cons.inj heq).1 hZ
      · next fz heq => exact absurd (List.cons.inj heq).1 hD
      · rfl

abbrev gntPs : List (Fin 32 × Word) :=
  [(ra, 0x2C), ((8 : Fin 32), 0x28), ((9 : Fin 32), 0x24), ((18 : Fin 32), 0x20)]

def gntA : List BInstr :=
  [.aluImm .add a4 x0 0x4, .alu .add (18 : Fin 32) x0 a0]
def gntB : List BInstr :=
  [.aluImm .add (9 : Fin 32) x0 0x0, .aluImm .add a0 a1 0x4, .aluImm .add a2 a2 0xFFFFFFFC, .sw sp a0 0x8, .sw sp a2 0xC, .aluImm .add a0 x0 0xF6, .aluImm .add a2 x0 0xA]
def gntC : List BInstr :=
  [.aluImm .add a0 sp 0x10, .aluImm .add a2 sp 0x8, .alu .add a1 x0 (9 : Fin 32)]
def gntD : List BInstr :=
  [.lw a3 sp 0xC]
def gntE : List BInstr :=
  [.lw a4 sp 0x8, .lbu a5 a4 0x0, .lw a1 sp 0x18, .lw a0 sp 0x1C, .aluImm .add (9 : Fin 32) a5 0xFFFFFFD2, .aluImm .add a2 a3 0xFFFFFFFF]
def gntF : List BInstr :=
  [.alu .add a3 x0 (18 : Fin 32), .sw a3 a1 0x8, .sw a3 a0 0xC]
def gntG : List BInstr :=
  [.aluImm .add a4 a4 0x1, .aluImm .add a2 a3 0xFFFFFFFE, .alu .add a6 a4 a2, .lbu a3 a6 0x0, .aluImm .add a3 a3 0xFFFFFFA6]
def gntH : List BInstr :=
  [.aluImm .add a5 x0 0xA, .alu .add a3 x0 a2]
def gntI : List BInstr :=
  [.lbu a2 a6 0x0, .aluImm .add a2 a2 0xFFFFFFD0]
def gntT5A : List BInstr :=
  [.sb (18 : Fin 32) a5 0x1, .aluImm .add a2 x0 0x1]
def gntTF2 : List BInstr :=
  [.aluImm .add a0 x0 0x19, .sb (18 : Fin 32) a0 0x1]

section
set_option maxRecDepth 20000
theorem gntA_end : blockEnd generalizedTimeCode 0xA gntA = some 0xE := by decide
theorem gntB_end : blockEnd generalizedTimeCode 0x12 gntB = some 0x24 := by decide
theorem gntC_end : blockEnd generalizedTimeCode 0x70 gntC = some 0x76 := by decide
theorem gntD_end : blockEnd generalizedTimeCode 0x8A gntD = some 0x8C := by decide
theorem gntE_end : blockEnd generalizedTimeCode 0x8E gntE = some 0xA0 := by decide
theorem gntF_end : blockEnd generalizedTimeCode 0xAA gntF = some 0xB0 := by decide
theorem gntG_end : blockEnd generalizedTimeCode 0xB4 gntG = some 0xC6 := by decide
theorem gntH_end : blockEnd generalizedTimeCode 0xC8 gntH = some 0xCC := by decide
theorem gntI_end : blockEnd generalizedTimeCode 0xE8 gntI = some 0xF0 := by decide
theorem gntT5A_end : blockEnd generalizedTimeCode 0x5A gntT5A = some 0x60 := by decide
theorem gntTF2_end : blockEnd generalizedTimeCode 0xF2 gntTF2 = some 0xF8 := by decide
theorem gntSave_end : blockEnd generalizedTimeCode 2 (saveBlock gntPs) = some 0xA := by decide
theorem gntRestore_end : blockEnd generalizedTimeCode 0x64 (restoreBlock gntPs) = some 0x6C := by decide
end

theorem gnt_dig : ∀ b : BitVec 8, branchTaken .bgeu (aluEval .add (b.zeroExtend 32) 0xFFFFFFD0) 10 =
    !(decide (48 ≤ b.toNat ∧ b.toNat ≤ 57)) := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The inlined `digits::<4>` loop from 0x24: on to 0x70 with the year in
`s1`, or to the `BadTime` exit at 0x58. -/
theorem gnt_year {M : Word → BitVec 8} (hc : CodeIn M GNT generalizedTimeCode) : ∀ k, k ≤ 4 →
    ∀ {nn : Machine} {acc m : Nat} {q : Word}, St M GNT nn 0x24 (reg nn) → reg nn a4 = BitVec.ofNat 32 k →
    reg nn a1 = q → reg nn 9 = BitVec.ofNat 32 acc → acc < 10 ^ (4 - k) → reg nn a0 = 0xF6 →
    reg nn a2 = BitVec.ofNat 32 10 → k ≤ m →
    (readDigits k (memBytes M q m) = none → ∃ nn', Steps nn nn' ∧ St M GNT nn' 0x58 (reg nn') ∧
      ∀ r, r.val ∉ [8, 9, 11, 13, 14, 15] → reg nn' r = reg nn r) ∧
    (∀ v rest, readDigits k (memBytes M q m) = some (v, rest) → ∃ nn', Steps nn nn' ∧ St M GNT nn' 0x70 (reg nn') ∧
      reg nn' 9 = BitVec.ofNat 32 (acc * 10 ^ k + v) ∧ ∀ r, r.val ∉ [8, 9, 11, 13, 14, 15] → reg nn' r = reg nn r) := by
  intro k
  induction k with
  | zero =>
    intro _ nn acc m q st r14 r11 r9 hacc r10 r12 _
    obtain ⟨n1, d1, u1⟩ := st.taken hc 0x70 gnt_at_24 (by decide) (by rw [r14, st.zero]; rfl)
    refine ⟨fun h => (by simp only [readDigits] at h; cases h), fun v rest h => ?_⟩
    simp only [readDigits] at h; cases h
    exact ⟨n1, .single d1, u1.self, by rw [u1.regs, r9, Nat.pow_zero, Nat.mul_one, Nat.add_zero], fun r _ => u1.regs r⟩
  | succ k ih =>
    intro hk nn acc m q st r14 r11 r9 hacc r10 r12 hm
    have hz := st.zero
    have hk0 : (BitVec.ofNat 32 (k + 1) == (0 : Word)) = false := beq_eq_false_iff_ne.mpr fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this; omega
    obtain ⟨n1, d1, u1⟩ := st.notTaken hc 0x26 gnt_at_24 (by decide) (by
      rw [r14, hz]; exact hk0)
    obtain ⟨n2, c2, u2⟩ := St.block gntY1 u1.self hc gntY1_end (by simp only [BlockOk, BInstr.ok, gntY1, and_self])
    have R2 : ∀ r, reg n2 r = (runBlock gntY1 (M, reg n1)).2 r := u2.regs
    have u2' : St M GNT n2 0x32 (reg n2) := ⟨u2.pc, by rw [u2.mem]; rfl, fun _ => rfl⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hspec := readDigits_succ_mem M q k m'
    have v2a5 : reg n2 a5 = aluEval .and (aluEval .add ((M q).zeroExtend 32) 0xFFFFFFC6) 0xFF := by
      rw [R2]; simp +decide only [runBlock, BInstr.run, gntY1, upd_app, ↓reduceIte]; rw [u1.regs, r11, add_lit_zero]
    have v2s0 : reg n2 8 = (M q).zeroExtend 32 := by
      rw [R2]; simp +decide only [runBlock, BInstr.run, gntY1, upd_app, ↓reduceIte]; rw [u1.regs, r11, add_lit_zero]
    have K2 : ∀ r, r.val ∉ [8, 15] → reg n2 r = reg nn r := fun r hr => by
      have hd : r ∉ gntY1.filterMap BInstr.dst := by
        simp only [gntY1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
        revert hr; revert r; decide
      rw [R2, runBlock_reg _ _ _ r u1.self.zero hd, u1.regs]
    by_cases hd : 48 ≤ (M q).toNat ∧ (M q).toNat ≤ 57
    · have hdig : isDigit (M q) = true := decide_eq_true hd
      obtain ⟨n3, d3, u3⟩ := u2'.notTaken hc 0x36 gnt_at_32 (by decide) (by
        rw [v2a5, K2 _ (by decide), r10, td_digit, hdig]; rfl)
      obtain ⟨n4, c4, u4⟩ := St.block gntY2 u3.self hc gntY2_end (by simp only [BlockOk, BInstr.ok, gntY2, and_self])
      have R4 : ∀ r, reg n4 r = (runBlock gntY2 (M, reg n3)).2 r := u4.regs
      have u4' : St M GNT n4 0x3C (reg n4) := ⟨u4.pc, by rw [u4.mem]; rfl, fun _ => rfl⟩
      have hacc' : acc < 10 ^ (4 - (k + 1)) := hacc
      have h10 : acc < 10000 :=
        Nat.lt_of_lt_of_le hacc' (show 10 ^ (4 - (k + 1)) ≤ 10 ^ 4 from Nat.pow_le_pow_right (by decide) (by omega))
      have v4a3 : reg n4 a3 = 0 := by
        rw [R4]; simp +decide only [runBlock, BInstr.run, gntY2, upd_app, ↓reduceIte]
        simp only [u3.regs]; rw [K2 9 (by decide), K2 a2 (by decide), r9, r12, dn_mulhuN _ _ (by omega) (by decide)]
        rw [Nat.div_eq_of_lt (show acc * 10 < 4294967296 by omega)]; rfl
      obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc 0x3E gnt_at_3c (by decide) (by rw [v4a3, u4'.zero]; rfl)
      obtain ⟨n6, c6, u6⟩ := St.block gntY3 u5.self hc gntY3_end (by simp only [BlockOk, BInstr.ok, gntY3, and_self])
      have R6 : ∀ r, reg n6 r = (runBlock gntY3 (M, reg n5)).2 r := u6.regs
      have u6' : St M GNT n6 0x54 (reg n6) := ⟨u6.pc, by rw [u6.mem]; rfl, fun _ => rfl⟩
      have r9_5 : reg n5 9 = BitVec.ofNat 32 acc := by
        rw [u5.regs, R4, runBlock_reg _ _ _ _ u3.self.zero (by decide), u3.regs, K2 _ (by decide), r9]
      have r12_5 : reg n5 a2 = BitVec.ofNat 32 10 := by
        rw [u5.regs, R4, runBlock_reg _ _ _ _ u3.self.zero (by decide), u3.regs, K2 _ (by decide), r12]
      have r8_5 : reg n5 8 = (M q).zeroExtend 32 := by
        rw [u5.regs, R4, runBlock_reg _ _ _ _ u3.self.zero (by decide), u3.regs, v2s0]
      have r11_5 : reg n5 a1 = q := by
        rw [u5.regs, R4, runBlock_reg _ _ _ _ u3.self.zero (by decide), u3.regs, K2 _ (by decide), r11]
      have r14_5 : reg n5 a4 = BitVec.ofNat 32 (k + 1) := by
        rw [u5.regs, R4, runBlock_reg _ _ _ _ u3.self.zero (by decide), u3.regs, K2 _ (by decide), r14]
      have hdv : (M q).toNat - 48 < 10 := by omega
      have v6s1 : reg n6 9 = BitVec.ofNat 32 (acc * 10 + ((M q).toNat - 48)) := by
        rw [R6]; simp +decide only [runBlock, BInstr.run, gntY3, upd_app, ↓reduceIte]
        rw [r9_5, r12_5, r8_5, td_val _ hdig, dn_mulN, dn_addN]
        exact dn_ofNat_congr (by omega)
      have v6a3 : reg n6 a3 = 0 := by
        rw [R6]; simp +decide only [runBlock, BInstr.run, gntY3, upd_app, ↓reduceIte]
        rw [r9_5, r12_5, r8_5, td_val _ hdig, dn_mulN, dn_addN, dn_sltuN _ _ (by omega) (by omega),
          show acc * 10 % 4294967296 = acc * 10 from Nat.mod_eq_of_lt (by omega),
          show ((M q).toNat - 48 + acc * 10) % 4294967296 = (M q).toNat - 48 + acc * 10 from Nat.mod_eq_of_lt (by omega),
          if_neg (by omega)]; rfl
      have v6a1 : reg n6 a1 = q + 1 := by
        rw [R6]; simp +decide only [runBlock, BInstr.run, gntY3, upd_app, ↓reduceIte]; rw [r11_5]; rfl
      have v6a4 : reg n6 a4 = BitVec.ofNat 32 k := by
        rw [R6]; simp +decide only [runBlock, BInstr.run, gntY3, upd_app, ↓reduceIte]; rw [r14_5]
        exact BitVec.eq_of_toNat_eq (by
          rw [dn_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (4294967295 : Word).toNat = 4294967295
            from rfl]; omega)
      have K6 : ∀ r, r.val ∉ [8, 9, 11, 13, 14, 15] → reg n6 r = reg nn r := fun r hr => by
        have hd6 : r ∉ gntY3.filterMap BInstr.dst := by
          simp only [gntY3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
          revert hr; revert r; decide
        have hd4 : r ∉ gntY2.filterMap BInstr.dst := by
          simp only [gntY2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
          revert hr; revert r; decide
        rw [R6, runBlock_reg _ _ _ r u5.self.zero hd6, u5.regs, R4, runBlock_reg _ _ _ r u3.self.zero hd4, u3.regs,
          K2 r (by revert hr; revert r; decide)]
      obtain ⟨n7, d7, u7⟩ := u6'.taken hc 0x24 gnt_at_54 (by decide) (by rw [v6a3, u6'.zero]; rfl)
      have pre : Steps nn n7 :=
        .cons d1 (c2.trans (.cons d3 (c4.trans (.cons d5 (c6.trans (.single d7))))))
      have hacc2 : acc * 10 + ((M q).toNat - 48) < 10 ^ (4 - k) := by
        have e : 10 ^ (4 - k) = 10 ^ (4 - (k + 1)) * 10 := by
          rw [← Nat.pow_succ]; congr 1; omega
        calc acc * 10 + ((M q).toNat - 48) < (acc + 1) * 10 := by omega
          _ ≤ 10 ^ (4 - (k + 1)) * 10 := Nat.mul_le_mul_right _ hacc'
          _ = 10 ^ (4 - k) := e.symm
      obtain ⟨ihN, ihS⟩ := ih (by omega) u7.self (by rw [u7.regs, v6a4]) (by rw [u7.regs, v6a1])
        (by rw [u7.regs, v6s1]) hacc2 (by rw [u7.regs, K6 _ (by decide), r10])
        (by rw [u7.regs, K6 _ (by decide), r12]) (m := m') (by omega)
      rw [if_pos hd] at hspec
      refine ⟨fun h => ?_, fun v rest h => ?_⟩
      · rw [hspec] at h
        cases hk' : readDigits k (memBytes M (q + 1) m') with
        | some vr => rw [hk'] at h; cases h
        | none =>
          obtain ⟨nf, cf, uf, Kf⟩ := ihN hk'
          exact ⟨nf, pre.trans cf, uf, fun r hr => by rw [Kf r hr, u7.regs, K6 r hr]⟩
      · rw [hspec] at h
        cases hk' : readDigits k (memBytes M (q + 1) m') with
        | none => rw [hk'] at h; cases h
        | some vr =>
          rw [hk'] at h
          obtain ⟨v', r'⟩ := vr
          simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hv, _⟩ := h
          obtain ⟨nf, cf, uf, sf, Kf⟩ := ihS v' r' hk'
          refine ⟨nf, pre.trans cf, uf, ?_, fun r hr => by rw [Kf r hr, u7.regs, K6 r hr]⟩
          rw [sf, ← hv, Nat.pow_succ, Nat.add_mul, Nat.add_assoc, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ k)]
    · have hdig : isDigit (M q) = false := decide_eq_false hd
      obtain ⟨n3, d3, u3⟩ := u2'.taken hc 0x58 gnt_at_32 (by decide) (by
        rw [v2a5, K2 _ (by decide), r10, td_digit, hdig]; rfl)
      rw [if_neg hd] at hspec
      exact ⟨fun _ => ⟨n3, .cons d1 (c2.trans (.single d3)), u3.self, fun r hr => by
        rw [u3.regs, K2 r (by revert hr; revert r; decide)]⟩,
        fun v rest h => by rw [hspec] at h; cases h⟩

set_option maxRecDepth 20000 in
/-- The fraction loop from 0xCC: on to 0xE0 when the `c` bytes at `ptr` are
all digits, and to the `BadTime` exit at 0xF2 when one isn't. -/
theorem gnt_frac {M : Word → BitVec 8} (hc : CodeIn M GNT generalizedTimeCode) : ∀ c,
    ∀ {nn : Machine} {ptr : Word}, St M GNT nn 0xCC (reg nn) → reg nn a3 = BitVec.ofNat 32 c → reg nn a4 = ptr →
    reg nn a5 = BitVec.ofNat 32 10 → c < 2 ^ 32 →
    ((∀ i, i < c → 48 ≤ (M (ptr + BitVec.ofNat 32 i)).toNat ∧ (M (ptr + BitVec.ofNat 32 i)).toNat ≤ 57) →
      ∃ nn', Steps nn nn' ∧ St M GNT nn' 0xE0 (reg nn') ∧ ∀ r, r.val ∉ [9, 13, 14] → reg nn' r = reg nn r) ∧
    (¬ (∀ i, i < c → 48 ≤ (M (ptr + BitVec.ofNat 32 i)).toNat ∧ (M (ptr + BitVec.ofNat 32 i)).toNat ≤ 57) →
      ∃ nn', Steps nn nn' ∧ St M GNT nn' 0xF2 (reg nn') ∧ ∀ r, r.val ∉ [9, 13, 14] → reg nn' r = reg nn r) := by
  intro c
  induction c with
  | zero =>
    intro nn ptr st r13 r14 r15 _
    obtain ⟨n1, d1, u1⟩ := st.taken hc 0xE0 gnt_at_cc (by decide) (by rw [r13, st.zero]; rfl)
    exact ⟨fun _ => ⟨n1, .single d1, u1.self, fun r _ => u1.regs r⟩, fun h => absurd (fun i hi => absurd hi
      (Nat.not_lt_zero i)) h⟩
  | succ c ih =>
    intro nn ptr st r13 r14 r15 hcl
    have hz := st.zero
    have hc0 : (BitVec.ofNat 32 (c + 1) == (0 : Word)) = false := beq_eq_false_iff_ne.mpr fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this; omega
    obtain ⟨n1, d1, u1⟩ := st.notTaken hc 0xCE gnt_at_cc (by decide) (by rw [r13, hz]; exact hc0)
    obtain ⟨n2, c2, u2⟩ := St.block gntF1 u1.self hc gntF1_end (by simp only [BlockOk, BInstr.ok, gntF1, and_self])
    have R2 : ∀ r, reg n2 r = (runBlock gntF1 (M, reg n1)).2 r := u2.regs
    have u2' : St M GNT n2 0xDA (reg n2) := ⟨u2.pc, by rw [u2.mem]; rfl, fun _ => rfl⟩
    have v9 : reg n2 9 = aluEval .add ((M ptr).zeroExtend 32) 0xFFFFFFD0 := by
      rw [R2]; simp +decide only [runBlock, BInstr.run, gntF1, upd_app, ↓reduceIte]; rw [u1.regs, r14, add_lit_zero]
    have v14 : reg n2 a4 = ptr + 1 := by
      rw [R2]; simp +decide only [runBlock, BInstr.run, gntF1, upd_app, ↓reduceIte]; rw [u1.regs, r14]; rfl
    have v13 : reg n2 a3 = BitVec.ofNat 32 c := by
      rw [R2]; simp +decide only [runBlock, BInstr.run, gntF1, upd_app, ↓reduceIte]; rw [u1.regs, r13]
      exact BitVec.eq_of_toNat_eq (by
        rw [dn_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (4294967295 : Word).toNat = 4294967295 from rfl]
        omega)
    have K2 : ∀ r, r.val ∉ [9, 13, 14] → reg n2 r = reg nn r := fun r hr => by
      have hd : r ∉ gntF1.filterMap BInstr.dst := by
        simp only [gntF1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
        revert hr; revert r; decide
      rw [R2, runBlock_reg _ _ _ r u1.self.zero hd, u1.regs]
    have v15 : reg n2 a5 = BitVec.ofNat 32 10 := by rw [K2 _ (by decide), r15]
    have h0 : ptr + BitVec.ofNat 32 0 = ptr := add_ofNat_zero ptr
    by_cases hd : 48 ≤ (M ptr).toNat ∧ (M ptr).toNat ≤ 57
    · obtain ⟨n3, d3, u3⟩ := u2'.notTaken hc 0xDE gnt_at_da (by decide) (by
        rw [v9, v15, show (BitVec.ofNat 32 10 : Word) = 10 from rfl, gnt_dig, decide_eq_true hd]; rfl)
      obtain ⟨n4, d4, u4⟩ := u3.self.jump hc gnt_at_de (off' := 0xCC) (by decide) (by rw [u3.pc]; decide)
      obtain ⟨ihA, ihB⟩ := ih (ptr := ptr + 1) u4.self (by rw [u4.regs, u3.regs, v13]) (by rw [u4.regs, u3.regs, v14])
        (by rw [u4.regs, u3.regs, v15]) (by omega)
      have pre : Steps nn n4 := .cons d1 (c2.trans (.cons d3 (.single d4)))
      have shift : ∀ i, ptr + 1 + BitVec.ofNat 32 i = ptr + BitVec.ofNat 32 (i + 1) := fun i => by
        rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc, Nat.add_comm]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨nf, cf, uf, Kf⟩ := ihA fun i hi => by rw [shift]; exact h (i + 1) (by omega)
        exact ⟨nf, pre.trans cf, uf, fun r hr => by rw [Kf r hr, u4.regs, u3.regs, K2 r hr]⟩
      · have h' : ¬ (∀ i, i < c → 48 ≤ (M (ptr + 1 + BitVec.ofNat 32 i)).toNat ∧
            (M (ptr + 1 + BitVec.ofNat 32 i)).toNat ≤ 57) := fun hh => h fun i hi => by
          rcases i with _ | i
          · rw [h0]; exact hd
          · rw [← shift]; exact hh i (by omega)
        obtain ⟨nf, cf, uf, Kf⟩ := ihB h'
        exact ⟨nf, pre.trans cf, uf, fun r hr => by rw [Kf r hr, u4.regs, u3.regs, K2 r hr]⟩
    · obtain ⟨n3, d3, u3⟩ := u2'.taken hc 0xF2 gnt_at_da (by decide) (by
        rw [v9, v15, show (BitVec.ofNat 32 10 : Word) = 10 from rfl, gnt_dig, decide_eq_false hd]; rfl)
      exact ⟨fun h => absurd (by rw [← h0]; exact h 0 (by omega)) hd,
        fun _ => ⟨n3, .cons d1 (c2.trans (.single d3)), u3.self, fun r hr => by rw [u3.regs, K2 r hr]⟩⟩

theorem readDigits_rest (M : Word → BitVec 8) : ∀ k (q : Word) (m v : Nat) (r : Bytes), k ≤ m →
    readDigits k (memBytes M q m) = some (v, r) → r = memBytes M (q + BitVec.ofNat 32 k) (m - k) ∧ v < 10 ^ k := by
  intro k
  induction k with
  | zero =>
    intro q m v r _ h
    simp only [readDigits] at h; cases h
    exact ⟨by rw [add_ofNat_zero, Nat.sub_zero], by decide⟩
  | succ k ih =>
    intro q m v r hm h
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [readDigits_succ_mem] at h
    split at h
    · rename_i hd
      cases hk : readDigits k (memBytes M (q + 1) m') with
      | none => rw [hk] at h; cases h
      | some vr =>
        rw [hk] at h
        obtain ⟨v', r'⟩ := vr
        simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hv, hr⟩ := h
        obtain ⟨e1, e2⟩ := ih (q + 1) m' v' r' (by omega) hk
        refine ⟨by rw [← hr, e1, show q + 1 + BitVec.ofNat 32 k = q + BitVec.ofNat 32 (k + 1) by
          rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc, Nat.add_comm]]; congr 1; omega, ?_⟩
        rw [← hv, Nat.pow_succ]
        have : (M q).toNat - 48 ≤ 9 := by omega
        calc ((M q).toNat - 48) * 10 ^ k + v' < ((M q).toNat - 48) * 10 ^ k + 10 ^ k := by omega
          _ = ((M q).toNat - 48 + 1) * 10 ^ k := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ 10 * 10 ^ k := Nat.mul_le_mul_right _ (by omega)
          _ = 10 ^ k * 10 := Nat.mul_comm _ _
    · cases h



theorem gnt_isDot : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFFD2) 0 = decide (b.toNat = 0x2E) := by decide
theorem gnt_isZ : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFFA6) 0 = !decide (b.toNat = 0x5A) := by decide
theorem gnt_is0 : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFFD0) 0 = !decide (b.toNat = 0x30) := by decide
theorem dn_beq0 (a : Nat) (ha : a < 2 ^ 32) : branchTaken .beq (BitVec.ofNat 32 a) 0 = decide (a = 0) := by
  simp only [branchTaken]
  by_cases h : a = 0
  · subst h; rfl
  · rw [decide_eq_false h]
    exact beq_eq_false_iff_ne.mpr fun e => h (by
      have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this; omega)
theorem dn_bne0 (a : Nat) (ha : a < 2 ^ 32) : branchTaken .bne (BitVec.ofNat 32 a) 0 = !decide (a = 0) := by
  have := dn_beq0 a ha
  simp only [branchTaken] at this ⊢
  rw [bne, this]

theorem dn_sub4 (k : Nat) (h2 : 4 ≤ k) (hk : k < 2 ^ 32) :
    BitVec.ofNat 32 k + 0xFFFFFFFC = BitVec.ofNat 32 (k - 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFC : Word).toNat = 4294967292 from rfl]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `time::generalized_time`**: for the `n` bytes at `p`, it
writes `generalizedTime`'s answer to the `Result<u64, Error>` at `out`: the
tag 0 and the time as two words at `out + 8`, or the tag 1 and `BadTime`
(0x19). It returns with `sp` and the callee-saved registers restored and
writes only `out` and the 0x60 bytes of stack below `sp`, its own frame and
`date_time`'s. -/
theorem generalizedTime_correct (m : Machine) {sp0 out p retAddr : Word} {n : Nat}
    (hcG : CodeIn m.mem GNT generalizedTimeCode) (hcD : CodeIn m.mem DT dateTimeCode)
    (hcT : CodeIn m.mem TD timeDigits2Code) (hpc : m.pc = GNT) (ha0 : reg m a0 = out) (ha1 : reg m a1 = p)
    (ha2 : reg m a2 = BitVec.ofNat 32 n) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) (hsa : sp0.toNat % 4 = 0) (hsl : 0x60 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (how : out.toNat + 16 ≤ 0x40000000) (hoa : out.toNat % 4 = 0) (hn : n < 2 ^ 32)
    (hpw : p.toNat + n + 14 ≤ 0x40000000) (hp0 : 0 < p.toNat)
    (sOG : Sep out 16 (sp0 + 0xFFFFFFA0) 0x60) (sPG : Sep p (n + 14) (sp0 + 0xFFFFFFA0) 0x60) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ t, generalizedTime (memBytes m.mem p n) = some t → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
        memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
        memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32)) ∧
      (generalizedTime (memBytes m.mem p n) = none → m'.mem out = 1 ∧ m'.mem (out + 1) = 0x19) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → Sep out 16 x 1 → m'.mem x = m.mem x := by
  obtain ⟨H, hH⟩ : ∃ H, sp0 + 0xFFFFFFA0 = H := ⟨_, rfl⟩
  rw [hH] at sOG sPG ⊢
  have hHn : H.toNat = sp0.toNat - 0x60 := by
    rw [← hH, BitVec.toNat_add, show (0xFFFFFFA0 : Word).toNat = 2 ^ 32 - 0x60 from rfl]; have := sp0.isLt; omega
  have hHc : ∀ c, c ≤ 0x60 → (H + BitVec.ofNat 32 c).toNat = H.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hHa : H.toNat % 4 = 0 := by omega
  obtain ⟨G, hG⟩ : ∃ G, H + BitVec.ofNat 32 0x30 = G := ⟨_, rfl⟩
  have hGn : G.toNat = H.toNat + 0x30 := by rw [← hG]; exact hHc _ (by decide)
  have hGa : G.toNat % 4 = 0 := by omega
  have eGk : ∀ k, G + BitVec.ofNat 32 k = H + BitVec.ofNat 32 (0x30 + k) := fun k => by rw [← hG, add_ofNat_assoc]
  have eGS : G + 0x30 = sp0 := by
    rw [show (0x30 : Word) = BitVec.ofNat 32 0x30 from rfl, eGk, ← hH, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eG0 : G + 0xFFFFFFD0 = H := by
    rw [← hG, BitVec.add_assoc]; exact BitVec.add_zero H
  have offs : ∀ {c n e k : Nat}, c + n ≤ e ∨ e + k ≤ c → c + n ≤ 0x60 → e + k ≤ 0x60 →
      Sep (H + BitVec.ofNat 32 c) n (H + BitVec.ofNat 32 e) k := fun h h1 h2 => sep_offsets H h (by omega) (by omega)
  have inH : ∀ {c l : Nat} {x : Word}, Sep H 0x60 x 1 → c + l ≤ 0x60 → Sep (H + BitVec.ofNat 32 c) l x 1 :=
    fun hx h => (hx.symm.subR h).symm
  have hiH : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep H 0x60 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have cd : ∀ {M' : Word → BitVec 8} {c : Word} {code : List Nat}, CodeIn m.mem c code → 0x40000000 ≤ c.toNat →
      c.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep H 0x60 x 1 → M' x = m.mem x) → CodeIn M' c code :=
    fun hc h1 h2 hM i hi' => by rw [hM _ (hiH _ (dn_code_hi h1 h2 hi'))]; exact hc i hi'
  have hGTn : GNT.toNat = 0x403a8a72 := by decide
  have cdG : ∀ {M' : Word → BitVec 8}, (∀ x, Sep H 0x60 x 1 → M' x = m.mem x) → CodeIn M' GNT generalizedTimeCode :=
    fun hM => cd hcG (by rw [hGTn]; decide) (by rw [hGTn]; decide) hM
  have hiC : ∀ {c l : Nat} {a : Word} {len : Nat}, c + l ≤ 0x60 → 0x40000000 ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 →
      Sep (H + BitVec.ofNat 32 c) l a len := fun h h1 h2 => sep_of_le (by rw [hHc _ (by omega)]; omega) h2
  have st0 : St m.mem GNT m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hcG gnt_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0) sp = G := by
    simp +decide only [upd, ↓reduceIte]; rw [hsp, ← hG, ← hH, BitVec.add_assoc]; rfl
  have slotO : ∀ o : Word, G + o = H + BitVec.ofNat 32 (0x30 + o.toNat) := fun o => by
    rw [← eGk, ofNat_toNat_self]
  have slotC : ∀ o : Word, o.toNat ≤ 0x2C → Sep (G + o) 4 GNT generalizedTimeCode.length := fun o ho => by
    rw [slotO]; exact hiC (by omega) (by rw [hGTn]; decide) (by rw [hGTn]; decide)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock gntPs) u1 hcG gntSave_end (saveBlock_ok _ gntPs _ fun q hq => by
      rw [sp1]
      simp only [gntPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> exact ⟨aligned_add hGa (by decide), slotC _ (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem G (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) gntPs = Ms :=
    ⟨_, rfl⟩
  rw [hMs] at u2
  have IMs : ∀ x, Sep H 0x60 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside gntPs fun q hq => by
      simp only [gntPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> (rw [slotO]; exact inH hx (by decide))
  have slots : ∀ r o, (r, o) ∈ gntPs → memLoad32 Ms (G + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [gntPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot gntPs _ hm (by
      simp only [gntPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide), upd_ne (by
        simp only [gntPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hr]
  have hc2 : CodeIn Ms GNT generalizedTimeCode := cdG IMs
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = G := by rw [u2.regs]; exact sp1
  -- the exits
  have hpsp : ∀ p ∈ gntPs, p.1 ≠ sp := by decide
  have sOC : ∀ {c l : Nat}, c + l ≤ 16 → Sep (out + BitVec.ofNat 32 c) l GNT generalizedTimeCode.length :=
    fun {c l} h => by
      have e : (out + BitVec.ofNat 32 c).toNat = out.toNat + c := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact sep_of_le (by rw [e, hGTn]; omega) (by rw [hGTn]; decide)
  have tail60 : ∀ {Mt : Word → BitVec 8} {nn : Machine} {v : Word}, St Mt GNT nn 0x60 (reg nn) →
      CodeIn Mt GNT generalizedTimeCode → reg nn sp = G → reg nn 18 = out → reg nn a2 = v →
      (∀ c', 0x50 ≤ c' → c' < 0x60 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      (∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      ∃ nn', Steps nn nn' ∧ nn'.pc = retAddr ∧ reg nn' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn' q = reg m q) ∧
        nn'.mem = memStore8 Mt out (v.extractLsb' 0 8) := by
    intro Mt nn v st hct rsp r18 ra2 hsl' hK
    obtain ⟨n1, d1, u1⟩ := st.sb hct gnt_at_60 (off' := 0x64) (by decide)
    rw [r18, add_lit_zero, ra2] at u1
    have hct1 : CodeIn (memStore8 Mt out (v.extractLsb' 0 8)) GNT generalizedTimeCode := by
      have := sOC (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this; exact hct.store8 this
    have slotT : ∀ o : Word, 0x20 ≤ o.toNat → o.toNat + 4 ≤ 0x30 →
        memLoad32 (memStore8 Mt out (v.extractLsb' 0 8)) (G + o) = memLoad32 Ms (G + o) := fun o h1 h2 => by
      rw [slotO]; apply memLoad32_congr; intro j hj
      rw [add_ofNat_assoc, memStore8_ne (by
        have := sOG.sub (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this
        exact dn_sep1 (this.subR (c := 0x30 + o.toNat + j) (l := 1) (by omega))), hsl' _ (by omega) (by omega)]
    obtain ⟨n2, c2', u2'⟩ := St.block (restoreBlock gntPs) u1 hct1 gntRestore_end
      (restoreBlock_ok (memStore8 Mt out (v.extractLsb' 0 8)) G gntPs (reg nn) rsp hpsp fun q hq => by
        simp only [gntPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> exact aligned_add hGa (by decide))
    simp only [restoreBlock_run (memStore8 Mt out (v.extractLsb' 0 8)) G gntPs (reg nn) rsp hpsp] at u2'
    have rsp' : restoreRegs (memStore8 Mt out (v.extractLsb' 0 8)) G (reg nn) gntPs sp = G := by
      rw [restoreRegs_sp _ _ _ _ hpsp]; exact rsp
    obtain ⟨n3, d3, u3⟩ := u2'.aluImm hct1 gnt_at_6c (off' := 0x6E) (by decide)
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hct1 gnt_at_6e
    have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
        restoreRegs (memStore8 Mt out (v.extractLsb' 0 8)) G f ps q = f q := by
      intro f ps q hq0
      induction ps generalizing f with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro h
        simp only [restoreRegs]
        rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
    have hslot : ∀ r o, (r, o) ∈ gntPs → reg n4 r = reg m r := fun r o hm => by
      rw [regs4]
      simp only [gntPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
        rw [slotT _ (by decide) (by decide)]; exact slots _ _ (by decide)
    refine ⟨n4, .cons d1 (c2'.trans (.cons d3 (.single d4))), ?_, ?_, fun q hq => ?_, ?_⟩
    · rw [pc4, ← regs4, hslot ra 0x2C (by decide), hra, add_lit_zero, hret]
    · rw [regs4]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [rsp', eGS]
    · rcases (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
          q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27]) q hq with rfl | rfl | rfl | rfl | hL
      · exact hslot _ 0x2C (by decide)
      · exact hslot _ 0x28 (by decide)
      · exact hslot _ 0x24 (by decide)
      · exact hslot _ 0x20 (by decide)
      · obtain ⟨hv, hs, hps⟩ : q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ gntPs, p.1 ≠ q) := by revert hL; revert q; decide
        rw [regs4, upd_ne hv hs, rr _ _ q hv hps, hK q hL]
    · rw [mem4]
  have o01 : out + 1 ≠ out := by
    have := sep_offsets out (c := 0) (n := 1) (d := 1) (k := 1) (by omega) (by omega) (by omega)
    rw [add_ofNat_zero] at this; exact dn_sep1 this
  have xo0 : ∀ {x : Word}, Sep out 16 x 1 → x ≠ out := fun hx => by
    have := hx.sub (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this; exact dn_sep1 this
  have xo1 : ∀ {x : Word}, Sep out 16 x 1 → x ≠ out + 1 := fun hx => dn_sep1 (hx.sub (c := 1) (l := 1) (by decide))
  have so1 : Sep (out + 1) 1 GNT generalizedTimeCode.length := sOC (c := 1) (l := 1) (by decide)
  have slot1 : ∀ {Mt : Word → BitVec 8} {b : BitVec 8},
      (∀ c', 0x50 ≤ c' → c' < 0x60 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      ∀ c', 0x50 ≤ c' → c' < 0x60 → memStore8 Mt (out + 1) b (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
    fun hS c' h1 h2 => by
      have hne : H + BitVec.ofNat 32 c' ≠ out + 1 := by
        have := sOG.sub (c := 1) (l := 1) (by decide)
        exact dn_sep1 (this.subR (c := c') (l := 1) (by omega))
      rw [memStore8_ne hne, hS c' h1 h2]
  -- `BadTime` out of 0x5A, with the code in `a5`
  have fin5A : ∀ {Mt : Word → BitVec 8} {nn : Machine} {v : Word}, Steps m nn → St Mt GNT nn 0x5A (reg nn) →
      (∀ x, Sep H 0x60 x 1 → Mt x = m.mem x) →
      (∀ c', 0x50 ≤ c' → c' < 0x60 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      reg nn sp = G → reg nn 18 = out →
      (∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      generalizedTime (memBytes m.mem p n) = none → reg nn a5 = v → v.extractLsb' 0 8 = 0x19 →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t, generalizedTime (memBytes m.mem p n) = some t → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
          memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32)) ∧
        (generalizedTime (memBytes m.mem p n) = none → m'.mem out = 1 ∧ m'.mem (out + 1) = 0x19) ∧
        ∀ x, Sep H 0x60 x 1 → Sep out 16 x 1 → m'.mem x = m.mem x := by
    intro Mt nn v pre st hI hS rsp r18 hK hspec ra5 hv
    have hct := cdG hI
    obtain ⟨n1, c1, u1⟩ := St.block gntT5A st hct gntT5A_end (by
      simp +decide only [BlockOk, BInstr.ok, gntT5A, and_true, true_and]; rw [r18]; exact so1)
    have R1 : ∀ q, reg n1 q = (runBlock gntT5A (Mt, reg nn)).2 q := u1.regs
    have eM : (runBlock gntT5A (Mt, reg nn)).1 = memStore8 Mt (out + 1) (v.extractLsb' 0 8) := by
      simp +decide only [runBlock, BInstr.run, gntT5A]; rw [r18, ra5]
    rw [eM] at u1
    have u1' : St (memStore8 Mt (out + 1) (v.extractLsb' 0 8)) GNT n1 0x60 (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
    obtain ⟨n2, c2, pc2, sp2, K2, mem2⟩ := tail60 (v := 1) u1' (hct.store8 so1)
      (by rw [R1]; simp +decide only [runBlock, BInstr.run, gntT5A, upd_app, ↓reduceIte]; exact rsp)
      (by rw [R1]; simp +decide only [runBlock, BInstr.run, gntT5A, upd_app, ↓reduceIte]; exact r18)
      (by rw [R1]; simp +decide only [runBlock, BInstr.run, gntT5A, upd_app, ↓reduceIte]; rw [st.zero]; rfl)
      (slot1 hS)
      (fun q hq => by
        have hd : q ∉ gntT5A.filterMap BInstr.dst := by
          simp only [gntT5A, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
          revert hq; revert q; decide
        rw [R1, runBlock_reg _ _ _ q st.zero hd, hK q hq])
    rw [hv] at mem2
    have hE : ∀ t, generalizedTime (memBytes m.mem p n) = some t → False := fun t h => by rw [hspec] at h; cases h
    refine ⟨n2, pre.trans (c1.trans c2), pc2, sp2, K2, fun t h => (hE t h).elim, fun _ => ⟨?_, ?_⟩,
      fun x hx hx1 => ?_⟩
    · rw [mem2]; exact memStore8_same _ _ _
    · rw [mem2, memStore8_ne o01, memStore8_same]
    · rw [mem2, memStore8_ne (xo0 hx1), memStore8_ne (xo1 hx1), hI x hx]
  have fin58 : ∀ {Mt : Word → BitVec 8} {nn : Machine}, Steps m nn → St Mt GNT nn 0x58 (reg nn) →
      (∀ x, Sep H 0x60 x 1 → Mt x = m.mem x) →
      (∀ c', 0x50 ≤ c' → c' < 0x60 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      reg nn sp = G → reg nn 18 = out →
      (∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      generalizedTime (memBytes m.mem p n) = none →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t, generalizedTime (memBytes m.mem p n) = some t → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
          memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32)) ∧
        (generalizedTime (memBytes m.mem p n) = none → m'.mem out = 1 ∧ m'.mem (out + 1) = 0x19) ∧
        ∀ x, Sep H 0x60 x 1 → Sep out 16 x 1 → m'.mem x = m.mem x := by
    intro Mt nn pre st hI hS rsp r18 hK hspec
    obtain ⟨n1, d1, u1⟩ := st.aluImm (cdG hI) gnt_at_58 (off' := 0x5A) (by decide)
    exact fin5A (v := 0x19) (pre.trans (.single d1)) u1.self hI hS
      (by rw [u1.regs, upd_ne' (by decide) st.zero, rsp]) (by rw [u1.regs, upd_ne' (by decide) st.zero, r18])
      (fun q hq => by rw [u1.regs, upd_ne' (by revert hq; revert q; decide) st.zero, hK q hq]) hspec
      (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [st.zero]; rfl) (by decide)
  have finF2 : ∀ {Mt : Word → BitVec 8} {nn : Machine}, Steps m nn → St Mt GNT nn 0xF2 (reg nn) →
      (∀ x, Sep H 0x60 x 1 → Mt x = m.mem x) →
      (∀ c', 0x50 ≤ c' → c' < 0x60 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      reg nn sp = G → reg nn 18 = out →
      (∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      generalizedTime (memBytes m.mem p n) = none →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t, generalizedTime (memBytes m.mem p n) = some t → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
          memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32)) ∧
        (generalizedTime (memBytes m.mem p n) = none → m'.mem out = 1 ∧ m'.mem (out + 1) = 0x19) ∧
        ∀ x, Sep H 0x60 x 1 → Sep out 16 x 1 → m'.mem x = m.mem x := by
    intro Mt nn pre st hI hS rsp r18 hK hspec
    have hct := cdG hI
    obtain ⟨n1, c1, u1⟩ := St.block gntTF2 st hct gntTF2_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, gntTF2, upd_app, ↓reduceIte, and_true, true_and]
      rw [r18]; exact so1)
    have R1 : ∀ q, reg n1 q = (runBlock gntTF2 (Mt, reg nn)).2 q := u1.regs
    have eM : (runBlock gntTF2 (Mt, reg nn)).1 = memStore8 Mt (out + 1) 0x19 := by
      simp +decide only [runBlock, BInstr.run, gntTF2, upd_app, ↓reduceIte]; rw [r18, st.zero]; rfl
    rw [eM] at u1
    have hct1 := hct.store8 (v := 0x19) so1
    obtain ⟨n2, d2, u2⟩ := u1.jump hct1 gnt_at_f8 (off' := 0x5E) (by decide) (by rw [u1.pc]; decide)
    obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hct1 gnt_at_5e (off' := 0x60) (by decide)
    have K3 : ∀ q, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg nn q := fun q hq => by
      have hd : q ∉ gntTF2.filterMap BInstr.dst := by
        simp only [gntTF2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
        revert hq; revert q; decide
      rw [u3.regs, upd_ne' (by revert hq; revert q; decide) u2.self.zero, u2.regs, runBlock_reg _ _ _ q st.zero hd]
    obtain ⟨n4, c4, pc4, sp4, K4, mem4⟩ := tail60 (v := 1) u3.self hct1 (by rw [K3 sp (by decide), rsp])
      (by rw [K3 18 (by decide), r18]) (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.self.zero]; rfl)
      (slot1 hS) (fun q hq => by rw [K3 q (by revert hq; revert q; decide), hK q hq])
    have hE : ∀ t, generalizedTime (memBytes m.mem p n) = some t → False := fun t h => by rw [hspec] at h; cases h
    refine ⟨n4, pre.trans (c1.trans (.cons d2 (.cons d3 c4))), pc4, sp4, K4, fun t h => (hE t h).elim,
      fun _ => ⟨?_, ?_⟩, fun x hx hx1 => ?_⟩
    · rw [mem4]; exact memStore8_same _ _ _
    · rw [mem4, memStore8_ne o01, memStore8_same]
    · rw [mem4, memStore8_ne (xo0 hx1), memStore8_ne (xo1 hx1), hI x hx]
  -- the time stored, from 0xAA
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
  have sHo : ∀ {c' : Nat}, c' < 0x60 → Sep out 16 (H + BitVec.ofNat 32 c') 1 := fun {c'} h => sOG.subR (c := c') (l := 1) h
  have so8 : (out + 8).toNat % 4 = 0 := by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have so12 : (out + 0xC).toNat % 4 = 0 := by
    rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have finOk : ∀ {Mt : Word → BitVec 8} {nn : Machine} {t : Nat}, Steps m nn → St Mt GNT nn 0xAA (reg nn) →
      (∀ x, Sep H 0x60 x 1 → Mt x = m.mem x) →
      (∀ c', 0x50 ≤ c' → c' < 0x60 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      reg nn sp = G → reg nn 18 = out →
      (∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      reg nn a2 = 0 → reg nn a1 = BitVec.ofNat 32 (t % 2 ^ 32) → reg nn a0 = BitVec.ofNat 32 (t / 2 ^ 32) →
      t < 2 ^ 64 → generalizedTime (memBytes m.mem p n) = some t →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t, generalizedTime (memBytes m.mem p n) = some t → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
          memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32)) ∧
        (generalizedTime (memBytes m.mem p n) = none → m'.mem out = 1 ∧ m'.mem (out + 1) = 0x19) ∧
        ∀ x, Sep H 0x60 x 1 → Sep out 16 x 1 → m'.mem x = m.mem x := by
    intro Mt nn t pre st hI hS rsp r18 hK ra2 ra1 ra0 ht hspec
    have hct := cdG hI
    obtain ⟨n1, c1, u1⟩ := St.block gntF st hct gntF_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, gntF, upd_app, ↓reduceIte, and_true, true_and]
      rw [st.zero, dn_z, r18]; exact ⟨⟨so8, sOC (c := 8) (l := 4) (by decide)⟩, so12, sOC (c := 0xC) (l := 4) (by decide)⟩)
    have R1 : ∀ q, reg n1 q = (runBlock gntF (Mt, reg nn)).2 q := u1.regs
    have eM : (runBlock gntF (Mt, reg nn)).1 = memStore32 (memStore32 Mt (out + 8) (BitVec.ofNat 32 (t % 2 ^ 32)))
        (out + 0xC) (BitVec.ofNat 32 (t / 2 ^ 32)) := by
      simp +decide only [runBlock, BInstr.run, gntF, upd_app, ↓reduceIte]; rw [st.zero, dn_z, r18, ra1, ra0]
    rw [eM] at u1
    have hct1 : CodeIn (memStore32 (memStore32 Mt (out + 8) (BitVec.ofNat 32 (t % 2 ^ 32))) (out + 0xC)
        (BitVec.ofNat 32 (t / 2 ^ 32))) GNT generalizedTimeCode :=
      (hct.store32 (sOC (c := 8) (l := 4) (by decide))).store32 (sOC (c := 0xC) (l := 4) (by decide))
    obtain ⟨n2, d2, u2⟩ := u1.jump hct1 gnt_at_b0 (off' := 0x60) (by decide) (by rw [u1.pc]; decide)
    have K1 : ∀ q, q ≠ a3 → reg n2 q = reg nn q := fun q hq => by
      have hd : q ∉ gntF.filterMap BInstr.dst := by
        simp only [gntF, List.filterMap_cons, List.filterMap_nil, BInstr.dst, List.mem_cons, List.mem_nil_iff,
          or_false]; exact hq
      rw [u2.regs, runBlock_reg _ _ _ q st.zero hd]
    obtain ⟨n3, c3, pc3, sp3', K3', mem3⟩ := tail60 (v := 0) u2.self hct1 (by rw [K1 sp (by decide), rsp])
      (by rw [K1 18 (by decide), r18]) (by rw [K1 a2 (by decide), ra2])
      (fun c' h1 h2 => by rw [memStore32_get_sep (sx12 (sHo h2)), memStore32_get_sep (sx8 (sHo h2)), hS c' h1 h2])
      (fun q hq => by rw [K1 q (by revert hq; revert q; decide), hK q hq])
    have hE : ∀ t', generalizedTime (memBytes m.mem p n) = some t' → t' = t := fun t' h => by
      rw [hspec] at h; cases h; rfl
    have hN : generalizedTime (memBytes m.mem p n) = none → False := fun h => by rw [hspec] at h; cases h
    refine ⟨n3, pre.trans (c1.trans (.cons d2 c3)), pc3, sp3', K3', fun t' h => ?_, fun h => (hN h).elim,
      fun x hx hx1 => ?_⟩
    · obtain rfl := hE t' h
      refine ⟨ht, by rw [mem3]; exact memStore8_same _ _ _, ?_, ?_⟩
      · rw [mem3, memLoad32_store8_sep s0_8, memLoad32_store32_sep s12_8, memLoad32_store32_same]
      · rw [mem3, memLoad32_store8_sep s0_12, memLoad32_store32_same]
    · rw [mem3, memStore8_ne (xo0 hx1), memStore32_get_sep (sx12 hx1), memStore32_get_sep (sx8 hx1), hI x hx]
  -- 0xA: the length check
  obtain ⟨m3, c3, u3⟩ := St.block gntA u2.self hc2 gntA_end (by simp only [BlockOk, BInstr.ok, gntA, and_self])
  have R3 : ∀ q, reg m3 q = (runBlock gntA (Ms, reg m2)).2 q := u3.regs
  have u3' : St Ms GNT m3 0xE (reg m3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  have v3a4 : reg m3 a4 = BitVec.ofNat 32 4 := by
    rw [R3]; simp +decide only [runBlock, BInstr.run, gntA, upd_app, ↓reduceIte]; rw [u2.self.zero]; rfl
  have v318 : reg m3 18 = out := by
    rw [R3]; simp +decide only [runBlock, BInstr.run, gntA, upd_app, ↓reduceIte]; rw [r2 _ (by decide), ha0]
    exact zw _
  have K3 : ∀ q, q.val ∉ [14, 18] → reg m3 q = reg m2 q := fun q hq => by
    have hd : q ∉ gntA.filterMap BInstr.dst := by
      simp only [gntA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [R3, runBlock_reg _ _ _ q u2.self.zero hd]
  have kk3 : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m3 q = reg m q := fun q hq => by
    rw [K3 q (by revert hq; revert q; decide), r2 q (by revert hq; revert q; decide)]
  have sp3 : reg m3 sp = G := by rw [K3 sp (by decide), sp2]
  have IMs0 : ∀ c', 0x50 ≤ c' → c' < 0x60 → Ms (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
    fun _ _ _ => rfl
  have pre3 : Steps m m3 := .cons d1 (c2.trans c3)
  have hspec := generalizedTime_eq (memBytes m.mem p n)
  by_cases hn4 : n < 4
  · obtain ⟨m4, d4, u4⟩ := u3'.taken hc2 0x58 gnt_at_e (by decide) (by
      rw [K3 a2 (by decide), r2 a2 (by decide), ha2, v3a4, show (BitVec.ofNat 32 4 : Word) = BitVec.ofNat 32 4 from rfl,
        dn_bltu _ _ (by omega) (by decide)]; exact decide_eq_true hn4)
    exact fin58 (pre3.trans (.single d4)) u4.self IMs IMs0 (by rw [u4.regs, sp3]) (by rw [u4.regs, v318])
      (fun q hq => by rw [u4.regs, kk3 q hq])
      (by rw [hspec, readDigits_short 4 _ (by rw [memBytes_length]; exact hn4)]; rfl)
  obtain ⟨m4, d4, u4⟩ := u3'.notTaken hc2 0x12 gnt_at_e (by decide) (by
    rw [K3 a2 (by decide), r2 a2 (by decide), ha2, v3a4, dn_bltu _ _ (by omega) (by decide)]
    exact decide_eq_false hn4)
  -- 0x12: the reader for `date_time` at `G + 8`, over the bytes after the year
  have hG8 : (G + 8).toNat % 4 = 0 := by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eGk, hHc _ (by decide)]; omega
  have hGC : (G + 0xC).toNat % 4 = 0 := by
    rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, eGk, hHc _ (by decide)]; omega
  have sG8 : Sep (G + 8) 4 GNT generalizedTimeCode.length := by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eGk]; exact hiC (by decide) (by rw [hGTn]; decide)
      (by rw [hGTn]; decide)
  have sGC : Sep (G + 0xC) 4 GNT generalizedTimeCode.length := by
    rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, eGk]; exact hiC (by decide) (by rw [hGTn]; decide)
      (by rw [hGTn]; decide)
  have r4 : ∀ q, reg m4 q = reg m3 q := u4.regs
  obtain ⟨m5, c5, u5⟩ := St.block gntB u4.self hc2 gntB_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, gntB, upd_app, ↓reduceIte, and_true, true_and]
    rw [r4, sp3]; exact ⟨⟨hG8, sG8⟩, hGC, sGC⟩)
  have R5 : ∀ q, reg m5 q = (runBlock gntB (Ms, reg m4)).2 q := u5.regs
  obtain ⟨Mb, hMb⟩ : ∃ Mb, memStore32 (memStore32 Ms (G + 8) (p + 4)) (G + 0xC) (BitVec.ofNat 32 (n - 4)) = Mb :=
    ⟨_, rfl⟩
  have eMb : (runBlock gntB (Ms, reg m4)).1 = Mb := by
    simp +decide only [runBlock, BInstr.run, gntB, upd_app, ↓reduceIte]
    simp only [r4]
    rw [sp3, K3 a1 (by decide), r2 a1 (by decide), ha1, K3 a2 (by decide), r2 a2 (by decide), ha2, ev_add, ev_add,
      dn_sub4 n (by omega) hn, ← hMb]
  have u5' : St Mb GNT m5 0x24 (reg m5) := ⟨u5.pc, by rw [u5.mem, eMb], fun _ => rfl⟩
  have sG8x : ∀ {x : Word}, Sep H 0x60 x 1 → Sep (G + 8) 4 x 1 := fun hx => by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eGk]; exact inH hx (by decide)
  have sGCx : ∀ {x : Word}, Sep H 0x60 x 1 → Sep (G + 0xC) 4 x 1 := fun hx => by
    rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, eGk]; exact inH hx (by decide)
  have IMb : ∀ x, Sep H 0x60 x 1 → Mb x = m.mem x := fun x hx => by
    rw [← hMb, memStore32_get_sep (sGCx hx), memStore32_get_sep (sG8x hx), IMs x hx]
  have SMb : ∀ c', 0x50 ≤ c' → c' < 0x60 → Mb (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
    fun c' h1 h2 => by
      have e1 : Sep (G + 0xC) 4 (H + BitVec.ofNat 32 c') 1 := by
        rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, eGk]; exact offs (by omega) (by omega) (by omega)
      have e2 : Sep (G + 8) 4 (H + BitVec.ofNat 32 c') 1 := by
        rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eGk]; exact offs (by omega) (by omega) (by omega)
      rw [← hMb, memStore32_get_sep e1, memStore32_get_sep e2]
  have hc5 := cdG IMb
  have K5 : ∀ q, q.val ∉ [9, 10, 12] → reg m5 q = reg m3 q := fun q hq => by
    have hd : q ∉ gntB.filterMap BInstr.dst := by
      simp only [gntB, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [R5, runBlock_reg _ _ _ q u4.self.zero hd, r4]
  have v5 : reg m5 9 = BitVec.ofNat 32 0 ∧ reg m5 a0 = 0xF6 ∧ reg m5 a2 = BitVec.ofNat 32 10 := by
    refine ⟨?_, ?_, ?_⟩ <;>
      (simp +decide only [R5, runBlock, BInstr.run, gntB, upd_app, ↓reduceIte]; try rw [u4.self.zero]) <;> rfl
  have pre5 : Steps m m5 := pre3.trans (.cons d4 c5)
  -- the bytes `p` through `p + n + 14`, as the code reads them, are the input's
  have hPm : ∀ {Mx : Word → BitVec 8}, (∀ x, Sep H 0x60 x 1 → Mx x = m.mem x) →
      ∀ i, i < n + 14 → Mx (p + BitVec.ofNat 32 i) = m.mem (p + BitVec.ofNat 32 i) := fun hM i hi =>
    hM _ (sPG.symm.subR (c := i) (l := 1) (by omega))
  have hmb : memBytes Mb p n = memBytes m.mem p n := by
    have := dn_memBytes_eq (hPm IMb) (c := 0) (l := n) (by omega); rwa [add_ofNat_zero] at this
  -- the year
  obtain ⟨yN, yS⟩ := gnt_year hc5 4 (Nat.le_refl 4) (m := n) u5' (by rw [K5 _ (by decide), v3a4])
    (by rw [K5 _ (by decide), K3 _ (by decide), r2 _ (by decide), ha1]) v5.1 (by decide) v5.2.1 v5.2.2 (by omega)
  rw [hmb] at yN yS
  cases hy : readDigits 4 (memBytes m.mem p n) with
  | none =>
    obtain ⟨m6, c6, u6, K6⟩ := yN hy
    exact fin58 (pre5.trans c6) u6 IMb SMb (by rw [K6 sp (by decide), K5 sp (by decide), sp3])
      (by rw [K6 18 (by decide), K5 18 (by decide), v318])
      (fun q hq => by rw [K6 q (by revert hq; revert q; decide), K5 q (by revert hq; revert q; decide), kk3 q hq])
      (by rw [hspec, hy]; rfl)
  | some yr =>
  obtain ⟨v, rest⟩ := yr
  obtain ⟨m6, c6, u6, v6, K6⟩ := yS v rest hy
  obtain ⟨hrest, hv⟩ := readDigits_rest m.mem 4 p n v rest (by omega) hy
  rw [Nat.zero_mul, Nat.zero_add] at v6
  have K6' : ∀ q, q.val ∉ [8, 9, 10, 11, 12, 13, 14, 15] → reg m6 q = reg m3 q := fun q hq => by
    rw [K6 q (by revert hq; revert q; decide), K5 q (by revert hq; revert q; decide)]
  -- 0x70: call `date_time` with the year, the reader at `G + 8`, and its result at `G + 0x10`
  obtain ⟨m7, c7, u7⟩ := St.block gntC u6 hc5 gntC_end (by simp only [BlockOk, BInstr.ok, gntC, and_self])
  have R7 : ∀ q, reg m7 q = (runBlock gntC (Mb, reg m6)).2 q := u7.regs
  have u7' : St Mb GNT m7 0x76 (reg m7) := ⟨u7.pc, by rw [u7.mem]; rfl, fun _ => rfl⟩
  have sp6 : reg m6 sp = G := by rw [K6' sp (by decide), sp3]
  have v7 : reg m7 a0 = G + 0x10 ∧ reg m7 a2 = G + 8 ∧ reg m7 a1 = BitVec.ofNat 32 v := by
    simp +decide only [R7, runBlock, BInstr.run, gntC, upd_app, ↓reduceIte]
    rw [sp6, v6]; simp only [ev_add, zw, and_self]
  have K7 : ∀ q, q.val ∉ [10, 11, 12] → reg m7 q = reg m6 q := fun q hq => by
    have hd : q ∉ gntC.filterMap BInstr.dst := by
      simp only [gntC, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [R7, runBlock_reg _ _ _ q u6.zero hd]
  obtain ⟨m8, c8, pc8, mem8, regs8⟩ := u7'.callRa hc5 gnt_at_76 gnt_at_7a (cb := DT) (by decide) (by decide)
  have r8 := PEnv.reg1 regs8 u7'.zero
  have hDTn : DT.toNat = 0x403a8bc8 := by decide
  have hTDn : TD.toNat = 0x403a8de4 := by decide
  have eG : ∀ k, k ≤ 0x30 → (G + BitVec.ofNat 32 k).toNat = G.toNat + k := fun k hk => by
    rw [eGk, hHc _ (by omega)]; omega
  have sGH : ∀ {c l : Nat}, 0x30 ≤ c → c + l ≤ 0x60 → Sep (H + BitVec.ofNat 32 c) l H 0x30 := fun h1 h2 => by
    have := offs (c := _) (n := _) (e := 0) (k := 0x30) (Or.inr (by omega : 0 + 0x30 ≤ _)) h2 (by decide)
    rwa [add_ofNat_zero] at this
  have sGC8 : Sep (G + 0xC) 4 (G + 8) 4 := by
    rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, show (8 : Word) = BitVec.ofNat 32 8 from rfl, eGk, eGk]
    exact offs (by omega) (by omega) (by omega)
  have e8_4 : G + 8 + 4 = G + 0xC := by rw [BitVec.add_assoc]; rfl
  have sP4 : Sep (p + BitVec.ofNat 32 4) (n - 4) H 0x60 := sPG.sub (by omega)
  have sP4' : Sep (p + BitVec.ofNat 32 4) 10 H 0x60 := sPG.sub (by omega)
  obtain ⟨m9, c9, pc9, sp9, K9, hS9, hN9, fr9⟩ := dateTime_correct m8 (sp0 := G) (out := G + 0x10) (d := G + 8)
    (p := p + 4) (Y := BitVec.ofNat 32 v) (retAddr := GNT + BitVec.ofNat 32 (0x76 + 8)) (n := n - 4)
    (by rw [mem8]; exact cd hcD (by rw [hDTn]; decide) (by rw [hDTn]; decide) IMb)
    (by rw [mem8]; exact cd hcT (by rw [hTDn]; decide) (by rw [hTDn]; decide) IMb) pc8
    (by rw [r8 a0 (by decide), v7.1]) (by rw [r8 a1 (by decide), v7.2.2]) (by rw [r8 a2 (by decide), v7.2.1])
    (by rw [regs8]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at GNT (by decide) _ (by decide)))
    (by rw [r8 sp (by decide), K7 sp (by decide), sp6]) hGa (by omega) (by omega)
    (by rw [show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl, eG _ (by decide)]; omega)
    (by rw [show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl, eG _ (by decide)]; omega)
    (by rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eG _ (by decide)]; omega) hG8 (by omega)
    (by rw [mem8, ← hMb, memLoad32_store32_sep sGC8, memLoad32_store32_same])
    (by rw [mem8, e8_4, ← hMb, memLoad32_store32_same])
    (by rw [eG0, show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl, eGk]; exact sGH (by omega) (by omega))
    (by rw [eG0, show (8 : Word) = BitVec.ofNat 32 8 from rfl, eGk]; exact sGH (by omega) (by omega))
    (by rw [show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl, show (8 : Word) = BitVec.ofNat 32 8 from rfl, eGk,
      eGk]; exact offs (by omega) (by omega) (by omega))
    (by rw [eG0]; have := sP4.subR (c := 0) (l := 0x30) (by omega); rwa [add_ofNat_zero] at this)
    (by rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eGk]; exact sP4.subR (by omega))
    (by rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eGk]; exact (sP4'.subR (c := 0x38) (l := 8) (by omega)).symm)
  rw [mem8] at hS9 hN9 fr9
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2 ^ 32)] at hS9 hN9
  have hmb4 : memBytes Mb (p + 4) (n - 4) = memBytes m.mem (p + 4) (n - 4) :=
    dn_memBytes_eq (hPm IMb) (c := 4) (l := n - 4) (by omega)
  rw [hmb4] at hS9 hN9
  -- back from `date_time`
  have hfr9 : ∀ x, Sep H 0x60 x 1 → Sep (G + 0xFFFFFFD0) 0x30 x 1 ∧ Sep (G + 0x10) 16 x 1 ∧ Sep (G + 8) 8 x 1 :=
    fun x hx => ⟨by rw [eG0]; have := inH (c := 0) (l := 0x30) hx (by decide); rwa [add_ofNat_zero] at this,
      by rw [show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl, eGk]; exact inH hx (by decide),
      by rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eGk]; exact inH hx (by decide)⟩
  have I9 : ∀ x, Sep H 0x60 x 1 → m9.mem x = m.mem x := fun x hx => by
    obtain ⟨h1, h2, h3⟩ := hfr9 x hx; rw [fr9 x h1 h2 h3, IMb x hx]
  have S9 : ∀ c', 0x50 ≤ c' → c' < 0x60 → m9.mem (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
    fun c' h1 h2 => by
      have e1 : Sep (G + 0xFFFFFFD0) 0x30 (H + BitVec.ofNat 32 c') 1 := by
        rw [eG0]; have := offs (c := 0) (n := 0x30) (e := c') (k := 1) (by omega) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      have e2 : Sep (G + 0x10) 16 (H + BitVec.ofNat 32 c') 1 := by
        rw [show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl, eGk]; exact offs (by omega) (by omega) (by omega)
      have e3 : Sep (G + 8) 8 (H + BitVec.ofNat 32 c') 1 := by
        rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eGk]; exact offs (by omega) (by omega) (by omega)
      rw [fr9 _ e1 e2 e3, SMb c' h1 h2]
  have hc9 := cdG I9
  have u9 : St m9.mem GNT m9 0x7E (reg m9) := ⟨by rw [pc9], rfl, fun _ => rfl⟩
  have K9' : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m9 q = reg m6 q := fun q hq => by
    rw [K9 q (by revert hq; revert q; decide), r8 q (by revert hq; revert q; decide),
      K7 q (by revert hq; revert q; decide)]
  have sp9' : reg m9 sp = G := sp9
  have r18_9 : reg m9 18 = out := by rw [K9' 18 (by decide), K6' 18 (by decide), v318]
  have kk9 : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m9 q = reg m q := fun q hq => by
    rw [K9' q (by revert hq; revert q; decide), K6' q (by revert hq; revert q; decide), kk3 q hq]
  have pre9 : Steps m m9 := pre5.trans (c6.trans (c7.trans (c8.trans c9)))
  obtain ⟨m10, d10, u10⟩ := u9.lbu hc9 gnt_at_7e (off' := 0x82) (by decide)
  have a010 : reg m10 a0 = (m9.mem (G + 0x10)).zeroExtend 32 := by
    rw [u10.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp9']
  have K10 : ∀ q, q ≠ a0 → reg m10 q = reg m9 q := fun q hq => by rw [u10.regs, upd_ne' hq u9.zero]
  have hrest' : rest = memBytes m.mem (p + 4) (n - 4) := hrest
  cases hd : readDateTime v (memBytes m.mem (p + 4) (n - 4)) with
  | none =>
    obtain ⟨t1, t19⟩ := hN9 hd
    obtain ⟨m11, d11, u11⟩ := u10.self.notTaken hc9 0x84 gnt_at_82 (by decide) (by rw [a010, t1, u10.self.zero]; rfl)
    obtain ⟨m12, d12, u12⟩ := u11.self.lbu hc9 gnt_at_84 (off' := 0x88) (by decide)
    obtain ⟨m13, d13, u13⟩ := u12.self.jump hc9 gnt_at_88 (off' := 0x5A) (by decide) (by rw [u12.pc]; decide)
    have K13 : ∀ q, q ≠ a0 → q ≠ a5 → reg m13 q = reg m9 q := fun q h0 h5 => by
      rw [u13.regs, u12.regs, upd_ne' h5 u11.self.zero, u11.regs, K10 q h0]
    exact fin5A (v := (m9.mem (G + 0x11)).zeroExtend 32) (pre9.trans (.cons d10 (.cons d11 (.cons d12 (.single d13)))))
      u13.self I9 S9 (by rw [K13 sp (by decide) (by decide), sp9']) (by rw [K13 18 (by decide) (by decide), r18_9])
      (fun q hq => by rw [K13 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), kk9 q hq])
      (by rw [hspec, hy]; simp only [Option.bind]; rw [hrest', hd])
      (by rw [u13.regs, u12.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u11.regs, K10 sp (by decide), sp9'])
      (by rw [show G + 0x11 = G + 0x10 + 1 by rw [BitVec.add_assoc]; rfl, t19]; rfl)
  | some tr =>
  obtain ⟨t, rest2⟩ := tr
  obtain ⟨ht, t0, tlo, thi, hr2, hq, hL⟩ := hS9 t rest2 hd
  obtain ⟨m11, d11, u11⟩ := u10.self.taken hc9 0x8A gnt_at_82 (by decide) (by rw [a010, t0, u10.self.zero]; rfl)
  -- the bytes after the date and time
  generalize hqd : p + 4 + 10 = q at hr2 hq
  have hq4 : q = p + BitVec.ofNat 32 14 := by rw [← hqd, BitVec.add_assoc]; rfl
  generalize hLd : n - 4 - 10 = L at hr2 hL
  have hspecT : generalizedTime (memBytes m.mem p n) = gtTail (memBytes m.mem q L) t := by
    rw [hspec, hy]; simp only [Option.bind]; rw [hrest', hd]; dsimp only
    rw [hr2, hq4, dn_memBytes_eq (hPm IMb) (c := 14) (l := L) (by omega)]
  have hT := gtTail_mem m.mem q L t
  have kk11 : ∀ r, r.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m11 r = reg m9 r := fun r hr => by
    rw [u11.regs, K10 r (by revert hr; revert r; decide)]
  have bad : ∀ {nn : Machine}, Steps m nn → St m9.mem GNT nn 0xF2 (reg nn) →
      (∀ r, r.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn r = reg m9 r) → ¬ gtOk m.mem q L →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t, generalizedTime (memBytes m.mem p n) = some t → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
          memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32)) ∧
        (generalizedTime (memBytes m.mem p n) = none → m'.mem out = 1 ∧ m'.mem (out + 1) = 0x19) ∧
        ∀ x, Sep H 0x60 x 1 → Sep out 16 x 1 → m'.mem x = m.mem x := fun pre st hk hno =>
    finF2 pre st I9 S9 (by rw [hk sp (by decide), sp9']) (by rw [hk 18 (by decide), r18_9])
      (fun r hr => by rw [hk r (by revert hr; revert r; decide), kk9 r hr]) (by rw [hspecT]; exact hT.2 hno)
  have good : ∀ {nn : Machine}, Steps m nn → St m9.mem GNT nn 0xAA (reg nn) →
      (∀ r, r.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn r = reg m9 r) → reg nn a2 = 0 →
      reg nn a1 = BitVec.ofNat 32 (t % 2 ^ 32) → reg nn a0 = BitVec.ofNat 32 (t / 2 ^ 32) → gtOk m.mem q L →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t, generalizedTime (memBytes m.mem p n) = some t → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
          memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32)) ∧
        (generalizedTime (memBytes m.mem p n) = none → m'.mem out = 1 ∧ m'.mem (out + 1) = 0x19) ∧
        ∀ x, Sep H 0x60 x 1 → Sep out 16 x 1 → m'.mem x = m.mem x := fun pre st hk r12 r11 r10 hok =>
    finOk pre st I9 S9 (by rw [hk sp (by decide), sp9']) (by rw [hk 18 (by decide), r18_9])
      (fun r hr => by rw [hk r (by revert hr; revert r; decide), kk9 r hr]) r12 r11 r10 ht
      (by rw [hspecT]; exact hT.1 hok)
  have hLb : L < 2 ^ 32 := by omega
  have pre11 : Steps m m11 := pre9.trans (.cons d10 (.single d11))
  -- 0x8A: the length of the rest
  obtain ⟨m12, c12, u12⟩ := St.block gntD u11.self hc9 gntD_end (by
    simp +decide only [BlockOk, BInstr.ok, gntD, and_true]; rw [kk11 sp (by decide), sp9']; exact hGC)
  have u12' : St m9.mem GNT m12 0x8C (reg m12) := ⟨u12.pc, by rw [u12.mem]; rfl, fun _ => rfl⟩
  have v12 : reg m12 a3 = BitVec.ofNat 32 L := by
    rw [u12.regs]; simp +decide only [runBlock, BInstr.run, gntD, upd_app, ↓reduceIte]
    rw [kk11 sp (by decide), sp9', ← e8_4, hL]
  have kk12 : ∀ r, r.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m12 r = reg m9 r := fun r hr => by
    have hd' : r ∉ gntD.filterMap BInstr.dst := by
      simp only [gntD, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hr; revert r; decide
    rw [u12.regs, runBlock_reg _ _ _ r u11.self.zero hd', kk11 r hr]
  have pre12 : Steps m m12 := pre11.trans c12
  by_cases hL0 : L = 0
  · obtain ⟨m13, d13, u13⟩ := u12'.taken hc9 0xF2 gnt_at_8c (by decide) (by
      rw [v12, u12'.zero, dn_beq0 _ hLb]; exact decide_eq_true hL0)
    exact bad (pre12.trans (.single d13)) u13.self (fun r hr => by rw [u13.regs, kk12 r hr])
      (fun h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega)
  obtain ⟨m13, d13, u13⟩ := u12'.notTaken hc9 0x8E gnt_at_8c (by decide) (by
    rw [v12, u12'.zero, dn_beq0 _ hLb]; exact decide_eq_false hL0)
  -- 0x8E: the first byte after the time, and the time itself
  have hGk : ∀ k, k ≤ 0x30 → k % 4 = 0 → (G + BitVec.ofNat 32 k).toNat % 4 = 0 := fun k hk h4 => by
    rw [eG k hk]; omega
  obtain ⟨m14, c14, u14⟩ := St.block gntE u13.self hc9 gntE_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, gntE, upd_app, ↓reduceIte, and_true, true_and]
    rw [u13.regs, kk12 sp (by decide), sp9']
    exact ⟨hG8, hGk 0x18 (by decide) (by decide), hGk 0x1C (by decide) (by decide)⟩)
  have R14 : ∀ r, reg m14 r = (runBlock gntE (m9.mem, reg m13)).2 r := u14.regs
  have u14' : St m9.mem GNT m14 0xA0 (reg m14) := ⟨u14.pc, by rw [u14.mem]; rfl, fun _ => rfl⟩
  have sq : ∀ i, i < L → Sep H 0x60 (q + BitVec.ofNat 32 i) 1 := fun i hi => by
    rw [hq4, add_ofNat_assoc]; exact sPG.symm.subR (c := 14 + i) (l := 1) (by omega)
  have bq : ∀ i, i < L → m9.mem (q + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i) := fun i hi =>
    I9 _ (sq i hi)
  have bq0 : m9.mem q = m.mem q := by have := bq 0 (by omega); rwa [add_ofNat_zero] at this
  have e18 : G + 0x18 = G + 0x10 + 8 := by rw [BitVec.add_assoc]; rfl
  have e1C : G + 0x1C = G + 0x10 + 0xC := by rw [BitVec.add_assoc]; rfl
  have v14 : reg m14 a4 = q ∧ reg m14 a5 = (m.mem q).zeroExtend 32 ∧ reg m14 a1 = BitVec.ofNat 32 (t % 2 ^ 32) ∧
      reg m14 a0 = BitVec.ofNat 32 (t / 2 ^ 32) ∧
      reg m14 9 = aluEval .add ((m.mem q).zeroExtend 32) 0xFFFFFFD2 ∧ reg m14 a2 = BitVec.ofNat 32 (L - 1) := by
    simp +decide only [R14, runBlock, BInstr.run, gntE, upd_app, ↓reduceIte]
    simp only [u13.regs]
    rw [kk12 sp (by decide), sp9', hq, add_lit_zero, bq0, e18, e1C, tlo, thi, v12]
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    exact BitVec.eq_of_toNat_eq (by
      rw [dn_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (4294967295 : Word).toNat = 4294967295 from rfl]; omega)
  obtain ⟨v14a4, v14a5, v14a1, v14a0, v14s1, v14a2⟩ := v14
  have kk14 : ∀ r, r.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m14 r = reg m9 r := fun r hr => by
    have hd' : r ∉ gntE.filterMap BInstr.dst := by
      simp only [gntE, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hr; revert r; decide
    rw [R14, runBlock_reg _ _ _ r u13.self.zero hd', u13.regs, kk12 r hr]
  have pre14 : Steps m m14 := pre12.trans (.cons d13 c14)
  by_cases hdot : (m.mem q).toNat = 0x2E
  · obtain ⟨m15, d15, u15⟩ := u14'.taken hc9 0xB2 gnt_at_a0 (by decide) (by
      rw [v14s1, u14'.zero, gnt_isDot]; exact decide_eq_true hdot)
    have r15 : ∀ r, reg m15 r = reg m14 r := u15.regs
    by_cases hL1 : L - 1 = 0
    · obtain ⟨m16, d16, u16⟩ := u15.self.taken hc9 0xF2 gnt_at_b2 (by decide) (by
        rw [r15, v14a2, u15.self.zero, dn_beq0 _ (by omega)]; exact decide_eq_true hL1)
      exact bad (pre14.trans (.cons d15 (.single d16))) u16.self (fun r hr => by rw [u16.regs, r15, kk14 r hr])
        (fun h => by rcases h with ⟨_, h⟩ | ⟨h, _⟩ <;> omega)
    obtain ⟨m16, d16, u16⟩ := u15.self.notTaken hc9 0xB4 gnt_at_b2 (by decide) (by
      rw [r15, v14a2, u15.self.zero, dn_beq0 _ (by omega)]; exact decide_eq_false hL1)
    -- 0xB4: the last byte must be `Z`
    obtain ⟨m17, c17, u17⟩ := St.block gntG u16.self hc9 gntG_end (by
      simp only [BlockOk, BInstr.ok, gntG, and_self])
    have R17 : ∀ r, reg m17 r = (runBlock gntG (m9.mem, reg m16)).2 r := u17.regs
    have u17' : St m9.mem GNT m17 0xC6 (reg m17) := ⟨u17.pc, by rw [u17.mem]; rfl, fun _ => rfl⟩
    have eL1 : q + 1 + BitVec.ofNat 32 (L - 2) = q + BitVec.ofNat 32 (L - 1) := by
      rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]; congr 2; omega
    have hL2v : aluEval .add (BitVec.ofNat 32 L) 0xFFFFFFFE = BitVec.ofNat 32 (L - 2) :=
      BitVec.eq_of_toNat_eq (by
        rw [dn_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFE : Word).toNat = 4294967294 from rfl]
        omega)
    have v17 : reg m17 a4 = q + 1 ∧ reg m17 a2 = BitVec.ofNat 32 (L - 2) ∧ reg m17 a6 = q + BitVec.ofNat 32 (L - 1) ∧
        reg m17 a3 = aluEval .add ((m.mem (q + BitVec.ofNat 32 (L - 1))).zeroExtend 32) 0xFFFFFFA6 := by
      simp +decide only [R17, runBlock, BInstr.run, gntG, upd_app, ↓reduceIte]
      simp only [u16.regs, r15]
      have hm3 : reg m14 a3 = BitVec.ofNat 32 L := by
        rw [R14, runBlock_reg _ _ _ _ u13.self.zero (by decide), u13.regs, v12]
      rw [v14a4, hm3, hL2v]; simp only [ev_add]
      rw [eL1, add_lit_zero, bq _ (by omega)]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
    obtain ⟨v17a4, v17a2, v17a6, v17a3⟩ := v17
    have kk17 : ∀ r, r.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m17 r = reg m9 r := fun r hr => by
      have hd' : r ∉ gntG.filterMap BInstr.dst := by
        simp only [gntG, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hr; revert r; decide
      rw [R17, runBlock_reg _ _ _ r u16.self.zero hd', u16.regs, r15, kk14 r hr]
    have pre17 : Steps m m17 := pre14.trans (.cons d15 (.cons d16 c17))
    by_cases hz : (m.mem (q + BitVec.ofNat 32 (L - 1))).toNat = 0x5A
    rotate_left
    · obtain ⟨m18, d18, u18⟩ := u17'.taken hc9 0xF2 gnt_at_c6 (by decide) (by
        rw [v17a3, u17'.zero, gnt_isZ, decide_eq_false hz]; rfl)
      exact bad (pre17.trans (.single d18)) u18.self (fun r hr => by rw [u18.regs, kk17 r hr])
        (fun h => by
          rcases h with ⟨h, _⟩ | ⟨_, _, h, _⟩
          · omega
          · exact hz h)
    obtain ⟨m18, d18, u18⟩ := u17'.notTaken hc9 0xC8 gnt_at_c6 (by decide) (by
      rw [v17a3, u17'.zero, gnt_isZ, decide_eq_true hz]; rfl)
    obtain ⟨m19, c19, u19⟩ := St.block gntH u18.self hc9 gntH_end (by simp only [BlockOk, BInstr.ok, gntH, and_self])
    have R19 : ∀ r, reg m19 r = (runBlock gntH (m9.mem, reg m18)).2 r := u19.regs
    have u19' : St m9.mem GNT m19 0xCC (reg m19) := ⟨u19.pc, by rw [u19.mem]; rfl, fun _ => rfl⟩
    have v19 : reg m19 a3 = BitVec.ofNat 32 (L - 2) ∧ reg m19 a4 = q + 1 ∧ reg m19 a5 = BitVec.ofNat 32 10 := by
      simp +decide only [R19, runBlock, BInstr.run, gntH, upd_app, ↓reduceIte]
      simp only [u18.regs]; rw [v17a2, v17a4]; (try rw [u17'.zero]); (try simp only [dn_z])
      refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial
    have K19 : ∀ r, r.val ∉ [13, 15] → reg m19 r = reg m17 r := fun r hr => by
      have hd' : r ∉ gntH.filterMap BInstr.dst := by
        simp only [gntH, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hr; revert r; decide
      rw [R19, runBlock_reg _ _ _ r u18.self.zero hd', u18.regs]
    have pre19 : Steps m m19 := pre17.trans (.cons d18 c19)
    -- the fraction digits
    have hdig : (∀ i, i < L - 2 → 48 ≤ (m9.mem (q + 1 + BitVec.ofNat 32 i)).toNat ∧
        (m9.mem (q + 1 + BitVec.ofNat 32 i)).toNat ≤ 57) ↔ (∀ i, i < L - 2 →
        48 ≤ (m.mem (q + BitVec.ofNat 32 (1 + i))).toNat ∧ (m.mem (q + BitVec.ofNat 32 (1 + i))).toNat ≤ 57) := by
      have e : ∀ i, i < L - 2 → m9.mem (q + 1 + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 (1 + i)) :=
        fun i hi => by
          rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]; exact bq _ (by omega)
      exact ⟨fun h i hi => by rw [← e i hi]; exact h i hi, fun h i hi => by rw [e i hi]; exact h i hi⟩
    obtain ⟨fA, fB⟩ := gnt_frac hc9 (L - 2) u19' v19.1 v19.2.1 v19.2.2 (by omega)
    by_cases hall : ∀ i, i < L - 2 → 48 ≤ (m.mem (q + BitVec.ofNat 32 (1 + i))).toNat ∧
        (m.mem (q + BitVec.ofNat 32 (1 + i))).toNat ≤ 57
    rotate_left
    · obtain ⟨m20, c20, u20, K20⟩ := fB (fun h => hall (hdig.mp h))
      exact bad (pre19.trans c20) u20 (fun r hr => by
          rw [K20 r (by revert hr; revert r; decide), K19 r (by revert hr; revert r; decide), kk17 r hr])
        (fun h => by
          rcases h with ⟨h, _⟩ | ⟨_, _, _, h, _⟩
          · omega
          · exact hall h)
    obtain ⟨m20, c20, u20, K20⟩ := fA (hdig.mpr hall)
    have K20' : ∀ r, r.val ∉ [9, 13, 14, 15] → reg m20 r = reg m17 r := fun r hr => by
      rw [K20 r (by revert hr; revert r; decide), K19 r (by revert hr; revert r; decide)]
    have pre20 : Steps m m20 := pre19.trans c20
    by_cases hL2 : L - 2 = 0
    · obtain ⟨m21, d21, u21⟩ := u20.taken hc9 0xF2 gnt_at_e0 (by decide) (by
        rw [K20' a2 (by decide), v17a2, u20.zero, dn_beq0 _ (by omega)]; exact decide_eq_true hL2)
      exact bad (pre20.trans (.single d21)) u21.self (fun r hr => by
          rw [u21.regs, K20' r (by revert hr; revert r; decide), kk17 r hr])
        (fun h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega)
    obtain ⟨m21, d21, u21⟩ := u20.notTaken hc9 0xE2 gnt_at_e0 (by decide) (by
      rw [K20' a2 (by decide), v17a2, u20.zero, dn_beq0 _ (by omega)]; exact decide_eq_false hL2)
    obtain ⟨m22, d22, u22⟩ := u21.self.aluImm hc9 gnt_at_e2 (off' := 0xE4) (by decide)
    have eL2' : BitVec.ofNat 32 (L - 1) + 0xFFFFFFFF = BitVec.ofNat 32 (L - 2) := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295
        from rfl]; omega)
    have eL2 : q + BitVec.ofNat 32 (L - 1) + 0xFFFFFFFF = q + BitVec.ofNat 32 (L - 2) := by
      rw [BitVec.add_assoc, eL2']
    have v22 : reg m22 a6 = q + BitVec.ofNat 32 (L - 2) := by
      rw [u22.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u21.regs, K20' a6 (by decide), v17a6, ev_add, eL2]
    have hq2n : (q + BitVec.ofNat 32 (L - 2)).toNat ≠ 0 := by
      rw [hq4, add_ofNat_assoc, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    obtain ⟨m23, d23, u23⟩ := u22.self.notTaken hc9 0xE8 gnt_at_e4 (by decide) (by
      rw [v22, u22.self.zero]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]
      intro e; exact hq2n (by rw [e]; rfl))
    obtain ⟨m24, c24, u24⟩ := St.block gntI u23.self hc9 gntI_end (by simp only [BlockOk, BInstr.ok, gntI, and_self])
    have R24 : ∀ r, reg m24 r = (runBlock gntI (m9.mem, reg m23)).2 r := u24.regs
    have u24' : St m9.mem GNT m24 0xF0 (reg m24) := ⟨u24.pc, by rw [u24.mem]; rfl, fun _ => rfl⟩
    have v24 : reg m24 a2 = aluEval .add ((m.mem (q + BitVec.ofNat 32 (L - 2))).zeroExtend 32) 0xFFFFFFD0 := by
      simp +decide only [R24, runBlock, BInstr.run, gntI, upd_app, ↓reduceIte]
      rw [u23.regs, v22, add_lit_zero, bq _ (by omega)]
    have kk24 : ∀ r, r.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m24 r = reg m9 r := fun r hr => by
      have hd' : r ∉ gntI.filterMap BInstr.dst := by
        simp only [gntI, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hr; revert r; decide
      rw [R24, runBlock_reg _ _ _ r u23.self.zero hd', u23.regs, u22.regs,
        upd_ne' (by revert hr; revert r; decide) u21.self.zero, u21.regs,
        K20' r (by revert hr; revert r; decide), kk17 r hr]
    have pre24 : Steps m m24 := pre20.trans (.cons d21 (.cons d22 (.cons d23 c24)))
    by_cases h0 : (m.mem (q + BitVec.ofNat 32 (L - 2))).toNat = 0x30
    · obtain ⟨m25, d25, u25⟩ := u24'.notTaken hc9 0xF2 gnt_at_f0 (by decide) (by
        rw [v24, u24'.zero, gnt_is0, decide_eq_true h0]; rfl)
      exact bad (pre24.trans (.single d25)) u25.self (fun r hr => by rw [u25.regs, kk24 r hr])
        (fun h => by
          rcases h with ⟨h, _⟩ | ⟨_, _, _, _, h⟩
          · omega
          · exact h h0)
    obtain ⟨m25, d25, u25⟩ := u24'.taken hc9 0xFA gnt_at_f0 (by decide) (by
      rw [v24, u24'.zero, gnt_is0, decide_eq_false h0]; rfl)
    obtain ⟨m26, d26, u26⟩ := u25.self.aluImm hc9 gnt_at_fa (off' := 0xFC) (by decide)
    obtain ⟨m27, d27, u27⟩ := u26.self.jump hc9 gnt_at_fc (off' := 0xAA) (by decide) (by rw [u26.pc]; decide)
    have K27 : ∀ r, r ≠ a2 → reg m27 r = reg m24 r := fun r hr => by
      rw [u27.regs, u26.regs, upd_ne' hr u25.self.zero, u25.regs]
    have r24a1 : reg m24 a1 = BitVec.ofNat 32 (t % 2 ^ 32) := by
      rw [R24, runBlock_reg _ _ _ _ u23.self.zero (by decide), u23.regs, u22.regs, upd_ne' (by decide) u21.self.zero,
        u21.regs, K20' a1 (by decide), R17, runBlock_reg _ _ _ _ u16.self.zero (by decide), u16.regs, r15, v14a1]
    have r24a0 : reg m24 a0 = BitVec.ofNat 32 (t / 2 ^ 32) := by
      rw [R24, runBlock_reg _ _ _ _ u23.self.zero (by decide), u23.regs, u22.regs, upd_ne' (by decide) u21.self.zero,
        u21.regs, K20' a0 (by decide), R17, runBlock_reg _ _ _ _ u16.self.zero (by decide), u16.regs, r15, v14a0]
    exact good (pre24.trans (.cons d25 (.cons d26 (.single d27)))) u27.self
      (fun r hr => by rw [K27 r (by revert hr; revert r; decide), kk24 r hr])
      (by rw [u27.regs, u26.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u25.self.zero]; rfl)
      (by rw [K27 a1 (by decide), r24a1]) (by rw [K27 a0 (by decide), r24a0])
      (.inr ⟨by omega, hdot, hz, hall, h0⟩)
  -- not `.`: `Z` alone
  obtain ⟨m15, d15, u15⟩ := u14'.notTaken hc9 0xA2 gnt_at_a0 (by decide) (by
    rw [v14s1, u14'.zero, gnt_isDot]; exact decide_eq_false hdot)
  obtain ⟨m16, d16, u16⟩ := u15.self.aluImm hc9 gnt_at_a2 (off' := 0xA6) (by decide)
  have v16 : reg m16 a3 = aluEval .add ((m.mem q).zeroExtend 32) 0xFFFFFFA6 := by
    rw [u16.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u15.regs, v14a5]
  have K16 : ∀ r, r ≠ a3 → reg m16 r = reg m14 r := fun r hr => by
    rw [u16.regs, upd_ne' hr u15.self.zero, u15.regs]
  by_cases hZ : (m.mem q).toNat = 0x5A
  rotate_left
  · obtain ⟨m17, d17, u17⟩ := u16.self.taken hc9 0xF2 gnt_at_a6 (by decide) (by
      rw [v16, u16.self.zero, gnt_isZ, decide_eq_false hZ]; rfl)
    exact bad (pre14.trans (.cons d15 (.cons d16 (.single d17)))) u17.self
      (fun r hr => by rw [u17.regs, K16 r (by revert hr; revert r; decide), kk14 r hr])
      (fun h => by
        rcases h with ⟨_, h⟩ | ⟨_, h, _⟩
        · exact hZ h
        · exact hdot h)
  obtain ⟨m17, d17, u17⟩ := u16.self.notTaken hc9 0xA8 gnt_at_a6 (by decide) (by
    rw [v16, u16.self.zero, gnt_isZ, decide_eq_true hZ]; rfl)
  by_cases hL1 : L - 1 = 0
  rotate_left
  · obtain ⟨m18, d18, u18⟩ := u17.self.taken hc9 0xF2 gnt_at_a8 (by decide) (by
      rw [u17.regs, K16 a2 (by decide), v14a2, u17.self.zero, dn_bne0 _ (by omega), decide_eq_false hL1]; rfl)
    exact bad (pre14.trans (.cons d15 (.cons d16 (.cons d17 (.single d18))))) u18.self
      (fun r hr => by rw [u18.regs, u17.regs, K16 r (by revert hr; revert r; decide), kk14 r hr])
      (fun h => by
        rcases h with ⟨h, _⟩ | ⟨_, h, _⟩
        · omega
        · exact hdot h)
  obtain ⟨m18, d18, u18⟩ := u17.self.notTaken hc9 0xAA gnt_at_a8 (by decide) (by
    rw [u17.regs, K16 a2 (by decide), v14a2, u17.self.zero, dn_bne0 _ (by omega), decide_eq_true hL1]; rfl)
  exact good (pre14.trans (.cons d15 (.cons d16 (.cons d17 (.single d18))))) u18.self
    (fun r hr => by rw [u18.regs, u17.regs, K16 r (by revert hr; revert r; decide), kk14 r hr])
    (by rw [u18.regs, u17.regs, K16 a2 (by decide), v14a2, hL1]; rfl)
    (by rw [u18.regs, u17.regs, K16 a1 (by decide), v14a1]) (by rw [u18.regs, u17.regs, K16 a0 (by decide), v14a0])
    (.inl ⟨by omega, hZ⟩)


end C3.RV32
