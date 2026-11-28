import C3BootProofs.Proofs.AllAsciiDigit

/-!
# `time::generalized_time`, as compiled

`c3_verify::time::generalized_time` reads a four-digit year with
`digits::<4>`, calls `date_time` for the rest, and then accepts `Z` alone or
`.`, digits that `all_ascii_digit` checks and that don't end in `0`, and `Z`.
`generalizedTime_correct` matches it to `Spec.Time`'s `generalizedTime`.
-/

namespace C3.RV32

open C3.Image

abbrev GNT : Word := BitVec.ofNat 32 generalizedTimeAddress

section
set_option maxRecDepth 20000
theorem gnt_at_0 : fetchRel generalizedTimeCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem gnt_at_18 : fetchRel generalizedTimeCode 0x18 = some (.auipc ra 0x0, 4) := by decide
theorem gnt_at_1c : fetchRel generalizedTimeCode 0x1C = some (.jalr ra ra 0xFFFFFA30, 4) := by decide
theorem gnt_at_20 : fetchRel generalizedTimeCode 0x20 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem gnt_at_24 : fetchRel generalizedTimeCode 0x24 = some (.branch .bne a0 x0 0x16, 2) := by decide
theorem gnt_at_2c : fetchRel generalizedTimeCode 0x2C = some (.auipc ra 0x0, 4) := by decide
theorem gnt_at_30 : fetchRel generalizedTimeCode 0x30 = some (.jalr ra ra 0xFFFFFA86, 4) := by decide
theorem gnt_at_34 : fetchRel generalizedTimeCode 0x34 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem gnt_at_38 : fetchRel generalizedTimeCode 0x38 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem gnt_at_3a : fetchRel generalizedTimeCode 0x3A = some (.load .lbu a0 sp 0x9, 4) := by decide
theorem gnt_at_3e : fetchRel generalizedTimeCode 0x3E = some (.jal x0 0x68, 2) := by decide
theorem gnt_at_40 : fetchRel generalizedTimeCode 0x40 = some (.load .lw a0 sp 0x4, 2) := by decide
theorem gnt_at_42 : fetchRel generalizedTimeCode 0x42 = some (.branch .beq a0 x0 0x62, 2) := by decide
theorem gnt_at_56 : fetchRel generalizedTimeCode 0x56 = some (.branch .beq a4 x0 0x14, 2) := by decide
theorem gnt_at_58 : fetchRel generalizedTimeCode 0x58 = some (.aluImm .add a0 a3 0xFFFFFFA6, 4) := by decide
theorem gnt_at_5c : fetchRel generalizedTimeCode 0x5C = some (.branch .bne a0 x0 0x48, 2) := by decide
theorem gnt_at_5e : fetchRel generalizedTimeCode 0x5E = some (.branch .bne a2 x0 0x46, 2) := by decide
theorem gnt_at_68 : fetchRel generalizedTimeCode 0x68 = some (.jal x0 0x44, 2) := by decide
theorem gnt_at_6a : fetchRel generalizedTimeCode 0x6A = some (.branch .beq a2 x0 0x3A, 2) := by decide
theorem gnt_at_7e : fetchRel generalizedTimeCode 0x7E = some (.branch .bne a0 x0 0x26, 2) := by decide
theorem gnt_at_86 : fetchRel generalizedTimeCode 0x86 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem gnt_at_8a : fetchRel generalizedTimeCode 0x8A = some (.jalr ra ra 0xFFFFFD82, 4) := by decide
theorem gnt_at_8e : fetchRel generalizedTimeCode 0x8E = some (.branch .beq a0 x0 0x16, 2) := by decide
theorem gnt_at_90 : fetchRel generalizedTimeCode 0x90 = some (.branch .beq (20 : Fin 32) x0 0x14, 4) := by decide
theorem gnt_at_94 : fetchRel generalizedTimeCode 0x94 = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem gnt_at_96 : fetchRel generalizedTimeCode 0x96 = some (.branch .beq (19 : Fin 32) x0 0xE, 4) := by decide
theorem gnt_at_a2 : fetchRel generalizedTimeCode 0xA2 = some (.branch .bne a0 x0 0xFFFFFFBE, 2) := by decide
theorem gnt_at_a4 : fetchRel generalizedTimeCode 0xA4 = some (.aluImm .add a0 x0 0x19, 2) := by decide
theorem gnt_at_a6 : fetchRel generalizedTimeCode 0xA6 = some (.store .sb (8 : Fin 32) a0 0x1, 4) := by decide
theorem gnt_at_aa : fetchRel generalizedTimeCode 0xAA = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem gnt_at_ac : fetchRel generalizedTimeCode 0xAC = some (.store .sb (8 : Fin 32) a0 0x0, 4) := by decide
theorem gnt_at_bc : fetchRel generalizedTimeCode 0xBC = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem gnt_at_be : fetchRel generalizedTimeCode 0xBE = some (.jalr x0 ra 0x0, 2) := by decide
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

abbrev gntPs : List (Fin 32 × Word) :=
  [(ra, 0x2C), ((8 : Fin 32), 0x28), ((9 : Fin 32), 0x24), ((18 : Fin 32), 0x20), ((19 : Fin 32), 0x1C),
    ((20 : Fin 32), 0x18)]

def gntA : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a0, .sw sp a1 0x0, .sw sp a2 0x4, .aluImm .add a0 sp 0x8, .alu .add a1 x0 sp]
def gntB : List BInstr :=
  [.lw a1 sp 0xC, .aluImm .add a0 sp 0x8, .alu .add a2 x0 sp]
def gntC : List BInstr :=
  [.lw a1 sp 0x0, .lbu a3 a1 0x0, .lw (9 : Fin 32) sp 0x10, .lw (18 : Fin 32) sp 0x14,
    .aluImm .add a4 a3 0xFFFFFFD2, .aluImm .add a2 a0 0xFFFFFFFF]
def gntD : List BInstr :=
  [.aluImm .add a1 a1 0x1, .aluImm .add (20 : Fin 32) a0 0xFFFFFFFE, .alu .add (19 : Fin 32) a1 (20 : Fin 32),
    .lbu a0 (19 : Fin 32) 0x0, .aluImm .add a0 a0 0xFFFFFFA6]
def gntE : List BInstr :=
  [.sw sp a1 0x8, .sw sp (19 : Fin 32) 0xC, .aluImm .add a0 sp 0x8]
def gntF : List BInstr :=
  [.lbu a0 (19 : Fin 32) 0x0, .aluImm .add a0 a0 0xFFFFFFD0]
def gntOk : List BInstr :=
  [.aluImm .add a0 x0 0x0, .sw (8 : Fin 32) (9 : Fin 32) 0x8, .sw (8 : Fin 32) (18 : Fin 32) 0xC]

section
set_option maxRecDepth 20000
theorem gntA_end : blockEnd generalizedTimeCode 0xE gntA = some 0x18 := by decide
theorem gntB_end : blockEnd generalizedTimeCode 0x26 gntB = some 0x2C := by decide
theorem gntC_end : blockEnd generalizedTimeCode 0x44 gntC = some 0x56 := by decide
theorem gntD_end : blockEnd generalizedTimeCode 0x6C gntD = some 0x7E := by decide
theorem gntE_end : blockEnd generalizedTimeCode 0x80 gntE = some 0x86 := by decide
theorem gntF_end : blockEnd generalizedTimeCode 0x9A gntF = some 0xA2 := by decide
theorem gntOk_end : blockEnd generalizedTimeCode 0x60 gntOk = some 0x68 := by decide
theorem gntSave_end : blockEnd generalizedTimeCode 2 (saveBlock gntPs) = some 0xE := by decide
theorem gntRestore_end : blockEnd generalizedTimeCode 0xB0 (restoreBlock gntPs) = some 0xBC := by decide
end

/-- What `generalizedTime_correct` concludes about the machine `m'` it
returns with. -/
abbrev gntPost (m m' : Machine) (sp0 out p retAddr H : Word) (n : Nat) : Prop :=
  Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
    (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
    (∀ t, generalizedTime (memBytes m.mem p n) = some t → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
      memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
      memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32)) ∧
    (generalizedTime (memBytes m.mem p n) = none → m'.mem out = 1 ∧ m'.mem (out + 1) = 0x19) ∧
    ∀ x, Sep H 0x60 x 1 → Sep out 16 x 1 → m'.mem x = m.mem x

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
    (hcT : CodeIn m.mem TD timeDigits2Code) (hcF : CodeIn m.mem TD4 timeDigits4Code)
    (hcA : CodeIn m.mem AAD allAsciiDigitCode) (hpc : m.pc = GNT) (ha0 : reg m a0 = out) (ha1 : reg m a1 = p)
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
  suffices hP : ∃ m', gntPost m m' sp0 out p retAddr H n from hP
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
  have hGTn : GNT.toNat = (img% generalizedTimeAddress) := by decide
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
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add hGa (by decide), slotC _ (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem G (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) gntPs = Ms :=
    ⟨_, rfl⟩
  rw [hMs] at u2
  have IMs : ∀ x, Sep H 0x60 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside gntPs fun q hq => by
      simp only [gntPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> (rw [slotO]; exact inH hx (by decide))
  have slots : ∀ r o, (r, o) ∈ gntPs → memLoad32 Ms (G + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [gntPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot gntPs _ hm (by
      simp only [gntPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide),
      upd_ne (by
        simp only [gntPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hr]
  have hc2 : CodeIn Ms GNT generalizedTimeCode := cdG IMs
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = G := by rw [u2.regs]; exact sp1
  -- the exits
  have hpsp : ∀ p ∈ gntPs, p.1 ≠ sp := by decide
  have sOC : ∀ {c l : Nat}, c + l ≤ 16 → Sep (out + BitVec.ofNat 32 c) l GNT generalizedTimeCode.length :=
    fun {c l} h => by
      have e : (out + BitVec.ofNat 32 c).toNat = out.toNat + c := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact sep_of_le (by rw [e, hGTn]; omega) (by rw [hGTn]; decide)
  have tailAC : ∀ {Mt : Word → BitVec 8} {nn : Machine} {v : Word}, St Mt GNT nn 0xAC (reg nn) →
      CodeIn Mt GNT generalizedTimeCode → reg nn sp = G → reg nn 8 = out → reg nn a0 = v →
      (∀ c', 0x48 ≤ c' → c' < 0x60 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      (∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      ∃ nn', Steps nn nn' ∧ nn'.pc = retAddr ∧ reg nn' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn' q = reg m q) ∧
        nn'.mem = memStore8 Mt out (v.extractLsb' 0 8) := by
    intro Mt nn v st hct rsp r8 ra0 hsl' hK
    obtain ⟨n1, d1, u1⟩ := st.sb hct gnt_at_ac (off' := 0xB0) (by decide)
    rw [r8, add_lit_zero, ra0] at u1
    have hct1 : CodeIn (memStore8 Mt out (v.extractLsb' 0 8)) GNT generalizedTimeCode := by
      have := sOC (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this; exact hct.store8 this
    have slotT : ∀ o : Word, 0x18 ≤ o.toNat → o.toNat + 4 ≤ 0x30 →
        memLoad32 (memStore8 Mt out (v.extractLsb' 0 8)) (G + o) = memLoad32 Ms (G + o) := fun o h1 h2 => by
      rw [slotO]; apply memLoad32_congr; intro j hj
      rw [add_ofNat_assoc, memStore8_ne (by
        have := sOG.sub (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this
        exact dn_sep1 (this.subR (c := 0x30 + o.toNat + j) (l := 1) (by omega))), hsl' _ (by omega) (by omega)]
    obtain ⟨n2, c2', u2'⟩ := St.block (restoreBlock gntPs) u1 hct1 gntRestore_end
      (restoreBlock_ok (memStore8 Mt out (v.extractLsb' 0 8)) G gntPs (reg nn) rsp hpsp fun q hq => by
        simp only [gntPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hGa (by decide))
    simp only [restoreBlock_run (memStore8 Mt out (v.extractLsb' 0 8)) G gntPs (reg nn) rsp hpsp] at u2'
    have rsp' : restoreRegs (memStore8 Mt out (v.extractLsb' 0 8)) G (reg nn) gntPs sp = G := by
      rw [restoreRegs_sp _ _ _ _ hpsp]; exact rsp
    obtain ⟨n3, d3, u3⟩ := u2'.aluImm hct1 gnt_at_bc (off' := 0xBE) (by decide)
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hct1 gnt_at_be
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
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
        rw [slotT _ (by decide) (by decide)]; exact slots _ _ (by decide)
    refine ⟨n4, .cons d1 (c2'.trans (.cons d3 (.single d4))), ?_, ?_, fun q hq => ?_, ?_⟩
    · rw [pc4, ← regs4, hslot ra 0x2C (by decide), hra, add_lit_zero, hret]
    · rw [regs4]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [rsp', eGS]
    · rcases (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
          q = (20 : Fin 32) ∨ q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27]) q hq with
        rfl | rfl | rfl | rfl | rfl | rfl | hL
      · exact hslot _ 0x2C (by decide)
      · exact hslot _ 0x28 (by decide)
      · exact hslot _ 0x24 (by decide)
      · exact hslot _ 0x20 (by decide)
      · exact hslot _ 0x1C (by decide)
      · exact hslot _ 0x18 (by decide)
      · obtain ⟨hv, hs, hps⟩ : q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ gntPs, p.1 ≠ q) := by revert hL; revert q; decide
        rw [regs4, upd_ne hv hs, rr _ _ q hv hps, hK q hL]
    · rw [mem4]
  have o01 : out + 1 ≠ out := add_one_ne out
  have xo0 : ∀ {x : Word}, Sep out 16 x 1 → x ≠ out := fun hx => by
    have := hx.sub (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this; exact dn_sep1 this
  have xo1 : ∀ {x : Word}, Sep out 16 x 1 → x ≠ out + 1 := fun hx => dn_sep1 (hx.sub (c := 1) (l := 1) (by decide))
  have so1 : Sep (out + 1) 1 GNT generalizedTimeCode.length := sOC (c := 1) (l := 1) (by decide)
  have slot1 : ∀ {Mt : Word → BitVec 8} {b : BitVec 8},
      (∀ c', 0x48 ≤ c' → c' < 0x60 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      ∀ c', 0x48 ≤ c' → c' < 0x60 → memStore8 Mt (out + 1) b (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
    fun hS c' h1 h2 => by
      have hne : H + BitVec.ofNat 32 c' ≠ out + 1 := by
        have := sOG.sub (c := 1) (l := 1) (by decide)
        exact dn_sep1 (this.subR (c := c') (l := 1) (by omega))
      rw [memStore8_ne hne, hS c' h1 h2]
  -- `BadTime` out of 0xA6, with the code in `a0`
  have finA6 : ∀ {Mt : Word → BitVec 8} {nn : Machine} {v : Word}, Steps m nn → St Mt GNT nn 0xA6 (reg nn) →
      (∀ x, Sep H 0x60 x 1 → Mt x = m.mem x) →
      (∀ c', 0x48 ≤ c' → c' < 0x60 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      reg nn sp = G → reg nn 8 = out →
      (∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      generalizedTime (memBytes m.mem p n) = none → reg nn a0 = v → v.extractLsb' 0 8 = 0x19 →
      ∃ m', gntPost m m' sp0 out p retAddr H n := by
    intro Mt nn v pre st hI hS rsp r8 hK hspec ra0 hv
    have hct := cdG hI
    obtain ⟨n1, d1, u1⟩ := st.sb hct gnt_at_a6 (off' := 0xAA) (by decide)
    rw [r8, ra0, hv] at u1
    have hct1 := hct.store8 (v := 0x19) so1
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hct1 gnt_at_aa (off' := 0xAC) (by decide)
    obtain ⟨n3, c3, pc3, sp3, K3, mem3⟩ := tailAC (v := 1) u2.self hct1
      (by rw [u2.regs, upd_ne' (by decide) st.zero, rsp]) (by rw [u2.regs, upd_ne' (by decide) st.zero, r8])
      (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [st.zero]; rfl)
      (slot1 hS) (fun q hq => by rw [u2.regs, upd_ne' (by revert hq; revert q; decide) st.zero, hK q hq])
    have hE : ∀ t, generalizedTime (memBytes m.mem p n) = some t → False := fun t h => by rw [hspec] at h; cases h
    refine ⟨n3, pre.trans (.cons d1 (.cons d2 c3)), pc3, sp3, K3, fun t h => (hE t h).elim,
      fun _ => ⟨?_, ?_⟩, fun x hx hx1 => ?_⟩
    · rw [mem3]; exact memStore8_same _ _ _
    · rw [mem3, memStore8_ne o01, memStore8_same]
    · rw [mem3, memStore8_ne (xo0 hx1), memStore8_ne (xo1 hx1), hI x hx]
  have finA4 : ∀ {Mt : Word → BitVec 8} {nn : Machine}, Steps m nn → St Mt GNT nn 0xA4 (reg nn) →
      (∀ x, Sep H 0x60 x 1 → Mt x = m.mem x) →
      (∀ c', 0x48 ≤ c' → c' < 0x60 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      reg nn sp = G → reg nn 8 = out →
      (∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      generalizedTime (memBytes m.mem p n) = none → ∃ m', gntPost m m' sp0 out p retAddr H n := by
    intro Mt nn pre st hI hS rsp r8 hK hspec
    obtain ⟨n1, d1, u1⟩ := st.aluImm (cdG hI) gnt_at_a4 (off' := 0xA6) (by decide)
    exact finA6 (v := 0x19) (pre.trans (.single d1)) u1.self hI hS
      (by rw [u1.regs, upd_ne' (by decide) st.zero, rsp]) (by rw [u1.regs, upd_ne' (by decide) st.zero, r8])
      (fun q hq => by rw [u1.regs, upd_ne' (by revert hq; revert q; decide) st.zero, hK q hq]) hspec
      (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [st.zero]; rfl) (by decide)
  -- `BadTime` from a callee's result at `G + 8`
  have fin3A : ∀ {Mt : Word → BitVec 8} {nn : Machine}, Steps m nn → St Mt GNT nn 0x3A (reg nn) →
      (∀ x, Sep H 0x60 x 1 → Mt x = m.mem x) →
      (∀ c', 0x48 ≤ c' → c' < 0x60 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      reg nn sp = G → reg nn 8 = out →
      (∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      generalizedTime (memBytes m.mem p n) = none → Mt (G + 8 + 1) = 0x19 →
      ∃ m', gntPost m m' sp0 out p retAddr H n := by
    intro Mt nn pre st hI hS rsp r8 hK hspec h19
    have hct := cdG hI
    obtain ⟨n1, d1, u1⟩ := st.lbu hct gnt_at_3a (off' := 0x3E) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.self.jump hct gnt_at_3e (off' := 0xA6) (by decide) (by rw [u1.pc]; decide)
    have K2 : ∀ q, q ≠ a0 → reg n2 q = reg nn q := fun q h0 => by
      rw [u2.regs, u1.regs, upd_ne' h0 st.zero]
    exact finA6 (v := (Mt (G + 9)).zeroExtend 32) (pre.trans (.cons d1 (.single d2))) u2.self hI hS
      (by rw [K2 sp (by decide), rsp]) (by rw [K2 8 (by decide), r8])
      (fun q hq => by rw [K2 q (by revert hq; revert q; decide), hK q hq]) hspec
      (by rw [u2.regs, u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp])
      (by rw [show G + 9 = G + 8 + 1 by rw [BitVec.add_assoc]; rfl, h19]; rfl)
  -- the time stored, from 0x60
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
  have finOk : ∀ {Mt : Word → BitVec 8} {nn : Machine} {t : Nat}, Steps m nn → St Mt GNT nn 0x60 (reg nn) →
      (∀ x, Sep H 0x60 x 1 → Mt x = m.mem x) →
      (∀ c', 0x48 ≤ c' → c' < 0x60 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      reg nn sp = G → reg nn 8 = out →
      (∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      reg nn 9 = BitVec.ofNat 32 (t % 2 ^ 32) → reg nn 18 = BitVec.ofNat 32 (t / 2 ^ 32) →
      t < 2 ^ 64 → generalizedTime (memBytes m.mem p n) = some t →
      ∃ m', gntPost m m' sp0 out p retAddr H n := by
    intro Mt nn t pre st hI hS rsp r8 hK rs1 rs2 ht hspec
    have hct := cdG hI
    obtain ⟨n1, c1, u1⟩ := St.block gntOk st hct gntOk_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, gntOk, upd_app, ↓reduceIte, and_true, true_and]
      rw [r8]; exact ⟨⟨so8, sOC (c := 8) (l := 4) (by decide)⟩, so12, sOC (c := 0xC) (l := 4) (by decide)⟩)
    have R1 : ∀ q, reg n1 q = (runBlock gntOk (Mt, reg nn)).2 q := u1.regs
    have eM : (runBlock gntOk (Mt, reg nn)).1 = memStore32 (memStore32 Mt (out + 8) (BitVec.ofNat 32 (t % 2 ^ 32)))
        (out + 0xC) (BitVec.ofNat 32 (t / 2 ^ 32)) := by
      simp +decide only [runBlock, BInstr.run, gntOk, upd_app, ↓reduceIte]; rw [r8, rs1, rs2]
    rw [eM] at u1
    have hct1 : CodeIn (memStore32 (memStore32 Mt (out + 8) (BitVec.ofNat 32 (t % 2 ^ 32))) (out + 0xC)
        (BitVec.ofNat 32 (t / 2 ^ 32))) GNT generalizedTimeCode :=
      (hct.store32 (sOC (c := 8) (l := 4) (by decide))).store32 (sOC (c := 0xC) (l := 4) (by decide))
    obtain ⟨n2, d2, u2⟩ := u1.jump hct1 gnt_at_68 (off' := 0xAC) (by decide) (by rw [u1.pc]; decide)
    have K1 : ∀ q, q ≠ a0 → reg n2 q = reg nn q := fun q hq => by
      have hd : q ∉ gntOk.filterMap BInstr.dst := by
        simp only [gntOk, List.filterMap_cons, List.filterMap_nil, BInstr.dst, List.mem_cons, List.mem_nil_iff,
          or_false]; exact hq
      rw [u2.regs, runBlock_reg _ _ _ q st.zero hd]
    obtain ⟨n3, c3, pc3, sp3', K3', mem3⟩ := tailAC (v := 0) u2.self hct1 (by rw [K1 sp (by decide), rsp])
      (by rw [K1 8 (by decide), r8])
      (by rw [u2.regs]; simp +decide only [runBlock, BInstr.run, gntOk, upd_app, ↓reduceIte]; rw [st.zero]; rfl)
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
  -- 0xE: the slice `(p, n)` at `G`, and a call to `digits::<4>` with its result at `G + 8`
  have hG4 : (G + 4).toNat % 4 = 0 := aligned_add hGa (by decide)
  have hG8 : (G + 8).toNat % 4 = 0 := aligned_add hGa (by decide)
  have hGC : (G + 0xC).toNat % 4 = 0 := aligned_add hGa (by decide)
  obtain ⟨m3, c3, u3⟩ := St.block gntA u2.self hc2 gntA_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, gntA, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp2]
    exact ⟨⟨aligned_add hGa (by decide), slotC _ (by decide)⟩, hG4, slotC _ (by decide)⟩)
  have R3 : ∀ q, reg m3 q = (runBlock gntA (Ms, reg m2)).2 q := u3.regs
  obtain ⟨Ma, hMa⟩ : ∃ Ma, memStore32 (memStore32 Ms G p) (G + 4) (BitVec.ofNat 32 n) = Ma := ⟨_, rfl⟩
  have eMa : (runBlock gntA (Ms, reg m2)).1 = Ma := by
    simp +decide only [runBlock, BInstr.run, gntA, upd_app, ↓reduceIte]
    rw [sp2, r2 a1 (by decide), ha1, r2 a2 (by decide), ha2, add_lit_zero, ← hMa]
  have u3' : St Ma GNT m3 0x18 (reg m3) := ⟨u3.pc, by rw [u3.mem, eMa], fun _ => rfl⟩
  have v3 : reg m3 a0 = G + 8 ∧ reg m3 a1 = G ∧ reg m3 8 = out := by
    simp +decide only [R3, runBlock, BInstr.run, gntA, upd_app, ↓reduceIte]
    rw [sp2, r2 a0 (by decide), ha0, u2.self.zero]
    exact ⟨rfl, zw _, zw _⟩
  have K3 : ∀ q, q.val ∉ [8, 10, 11] → reg m3 q = reg m2 q := fun q hq => by
    have hd : q ∉ gntA.filterMap BInstr.dst := by
      simp only [gntA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [R3, runBlock_reg _ _ _ q u2.self.zero hd]
  have eG4 : G + 4 = H + BitVec.ofNat 32 0x34 := eGk 4
  have eG8 : G + 8 = H + BitVec.ofNat 32 0x38 := eGk 8
  have eGC : G + 0xC = H + BitVec.ofNat 32 0x3C := eGk 0xC
  have sGx4 : ∀ {x : Word}, Sep H 0x60 x 1 → Sep (G + 4) 4 x 1 := fun hx => by rw [eG4]; exact inH hx (by decide)
  have sGx8 : ∀ {x : Word}, Sep H 0x60 x 1 → Sep (G + 8) 4 x 1 := fun hx => by rw [eG8]; exact inH hx (by decide)
  have sGx88 : ∀ {x : Word}, Sep H 0x60 x 1 → Sep (G + 8) 8 x 1 := fun hx => by rw [eG8]; exact inH hx (by decide)
  have sGx816 : ∀ {x : Word}, Sep H 0x60 x 1 → Sep (G + 8) 16 x 1 := fun hx => by
    rw [eG8]; exact inH hx (by decide)
  have sGxC : ∀ {x : Word}, Sep H 0x60 x 1 → Sep (G + 0xC) 4 x 1 := fun hx => by rw [eGC]; exact inH hx (by decide)
  have sG0x4 : ∀ {x : Word}, Sep H 0x60 x 1 → Sep G 4 x 1 := fun hx => by rw [← hG]; exact inH hx (by decide)
  have sG0x8 : ∀ {x : Word}, Sep H 0x60 x 1 → Sep G 8 x 1 := fun hx => by rw [← hG]; exact inH hx (by decide)
  have sGo : ∀ {c l c' : Nat}, c + l ≤ 0x30 → (0x30 + c + l ≤ c' ∨ c' + 1 ≤ 0x30 + c) → c' < 0x60 →
      Sep (G + BitVec.ofNat 32 c) l (H + BitVec.ofNat 32 c') 1 := fun h1 h2 h3 => by
    rw [eGk]; exact offs (by omega) (by omega) (by omega)
  have sG0o : ∀ {l c' : Nat}, l ≤ 0x30 → (0x30 + l ≤ c' ∨ c' + 1 ≤ 0x30) → c' < 0x60 →
      Sep G l (H + BitVec.ofNat 32 c') 1 := fun h1 h2 h3 => by
    rw [← hG]; exact offs (by omega) (by omega) (by omega)
  have IMa : ∀ x, Sep H 0x60 x 1 → Ma x = m.mem x := fun x hx => by
    rw [← hMa, memStore32_get_sep (sGx4 hx), memStore32_get_sep (sG0x4 hx), IMs x hx]
  have SMa : ∀ c', 0x48 ≤ c' → c' < 0x60 → Ma (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
    fun c' h1 h2 => by
      have e1 : Sep (G + 4) 4 (H + BitVec.ofNat 32 c') 1 := sGo (c := 4) (l := 4) (by decide) (by omega) h2
      have e2 : Sep G 4 (H + BitVec.ofNat 32 c') 1 := sG0o (by decide) (by omega) h2
      rw [← hMa, memStore32_get_sep e1, memStore32_get_sep e2]
  have hPm : ∀ {Mx : Word → BitVec 8}, (∀ x, Sep H 0x60 x 1 → Mx x = m.mem x) →
      ∀ i, i < n + 14 → Mx (p + BitVec.ofNat 32 i) = m.mem (p + BitVec.ofNat 32 i) := fun hM i hi =>
    hM _ (sPG.symm.subR (c := i) (l := 1) (by omega))
  have hp4 : memBytes Ma p 4 = memBytes m.mem p 4 := by
    have := dn_memBytes_eq (hPm IMa) (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3'.callRa (cdG IMa) gnt_at_18 gnt_at_1c (cb := TD4) (by decide) (by decide)
  have r4 := PEnv.reg1 regs4 u3'.zero
  have hTD4n : TD4.toNat = (img% timeDigits4Address) := by decide
  have sGG4 : Sep (G + 4) 4 G 4 := by
    rw [eG4, ← hG]; exact offs (by omega) (by omega) (by omega)
  have sG8G : Sep (G + 8) 8 G 8 := by
    rw [eG8, ← hG]; exact offs (by omega) (by omega) (by omega)
  obtain ⟨m5, c5, pc5, mem5, K5⟩ := timeDigits4_correct m4 (base := TD4) (out := G + 8) (d := G) (p := p) (n := n)
    (retAddr := GNT + BitVec.ofNat 32 (0x18 + 8)) (by decide)
    (by rw [mem4]; exact cd hcF (by rw [hTD4n]; decide) (by rw [hTD4n]; decide) IMa) pc4
    (by rw [r4 a0 (by decide), v3.1]) (by rw [r4 a1 (by decide), v3.2.1]) hGa hG8 hn
    (by rw [mem4, ← hMa, memLoad32_store32_sep sGG4, memLoad32_store32_same])
    (by rw [mem4, ← hMa, memLoad32_store32_same])
    (by rw [eG8]; exact hiC (by decide) (by rw [hTD4n]; decide) (by rw [hTD4n]; decide))
    (by rw [← hG]; exact hiC (by decide) (by rw [hTD4n]; decide) (by rw [hTD4n]; decide))
    (by
      have := (sPG.symm.sub (c := 0x30) (l := 8) (by decide)).subR (c := 0) (l := 4) (by omega)
      rwa [add_ofNat_zero, hG] at this)
    (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at GNT (by decide) _ (by decide)))
  obtain ⟨Md, hMd⟩ : ∃ Md, digits4Mem Ma (G + 8) G p n = Md := ⟨_, rfl⟩
  rw [mem4, hMd] at mem5
  have IMd : ∀ x, Sep H 0x60 x 1 → Md x = m.mem x := fun x hx => by
    rw [← hMd, digits4Mem_frame (sGx88 hx) (sG0x8 hx), IMa x hx]
  have SMd : ∀ c', 0x48 ≤ c' → c' < 0x60 → Md (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
    fun c' h1 h2 => by
      have e1 : Sep (G + 8) 8 (H + BitVec.ofNat 32 c') 1 := sGo (c := 8) (l := 8) (by decide) (by omega) h2
      have e2 : Sep G 8 (H + BitVec.ofNat 32 c') 1 := sG0o (by decide) (by omega) h2
      rw [← hMd, digits4Mem_frame e1 e2, SMa c' h1 h2]
  have hc5 := cdG IMd
  have kk5 : ∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg m5 q = reg m q := fun q hq => by
    rw [K5 q (by revert hq; revert q; decide), r4 q (by revert hq; revert q; decide),
      K3 q (by revert hq; revert q; decide), r2 q (by revert hq; revert q; decide)]
  have sp5 : reg m5 sp = G := by rw [K5 sp (by decide), r4 sp (by decide), K3 sp (by decide), sp2]
  have r8_5 : reg m5 8 = out := by rw [K5 8 (by decide), r4 8 (by decide), v3.2.2]
  have hspec := generalizedTime_eq (memBytes m.mem p n)
  have pre5 : Steps m m5 := .cons d1 (c2.trans (c3.trans (c4.trans c5)))
  -- 0x20: the tag of `digits::<4>`'s result
  have u5 : St Md GNT m5 0x20 (reg m5) := ⟨by rw [pc5], mem5, fun _ => rfl⟩
  obtain ⟨m6, d6, u6⟩ := u5.lbu hc5 gnt_at_20 (off' := 0x24) (by decide)
  have a06 : reg m6 a0 = (Md (G + 8)).zeroExtend 32 := by
    rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5]
  have K6 : ∀ q, q ≠ a0 → reg m6 q = reg m5 q := fun q hq => by rw [u6.regs, upd_ne' hq u5.zero]
  by_cases hE : n < 4 ∨ readDigits 4 (memBytes m.mem p 4) = none
  · obtain ⟨e1, e19⟩ := digits4Mem_err (M := Ma) (out := G + 8) (d := G) (p := p) (n := n) (by rwa [hp4])
    rw [hMd] at e1 e19
    obtain ⟨m7, d7, u7⟩ := u6.self.taken hc5 0x3A gnt_at_24 (by decide) (by rw [a06, e1, u6.self.zero]; rfl)
    have hy0 : readDigits 4 (memBytes m.mem p n) = none := by
      by_cases h4 : 4 ≤ n
      · rcases hE with h | h
        · omega
        · rw [readDigits4_mem m.mem p h4, h]; rfl
      · exact readDigits_short 4 _ (by rw [memBytes_length]; omega)
    exact fin3A (pre5.trans (.cons d6 (.single d7))) u7.self IMd SMd (by rw [u7.regs, K6 sp (by decide), sp5])
      (by rw [u7.regs, K6 8 (by decide), r8_5])
      (fun q hq => by rw [u7.regs, K6 q (by revert hq; revert q; decide), kk5 q hq])
      (by rw [hspec, hy0]; rfl) e19
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
  obtain ⟨t0, tv, tp, tn⟩ := digits4Mem_ok (M := Ma) (out := G + 8) (d := G) hn4 (by rw [hp4]; exact hR) sG8G
  rw [hMd] at t0 tv tp tn
  obtain ⟨m7, d7, u7⟩ := u6.self.notTaken hc5 0x26 gnt_at_24 (by decide) (by rw [a06, t0, u6.self.zero]; rfl)
  have sp7 : reg m7 sp = G := by rw [u7.regs, K6 sp (by decide), sp5]
  -- 0x26: `date_time` with the year, the reader at `G`, and its result at `G + 8`
  obtain ⟨m8, c8, u8⟩ := St.block gntB u7.self hc5 gntB_end (by
    simp +decide only [BlockOk, BInstr.ok, gntB, and_true]; rw [sp7]; exact hGC)
  have R8 : ∀ q, reg m8 q = (runBlock gntB (Md, reg m7)).2 q := u8.regs
  have u8' : St Md GNT m8 0x2C (reg m8) := ⟨u8.pc, by rw [u8.mem]; rfl, fun _ => rfl⟩
  have e8_4 : G + 8 + 4 = G + 0xC := by rw [BitVec.add_assoc]; rfl
  have v8 : reg m8 a0 = G + 8 ∧ reg m8 a1 = BitVec.ofNat 32 v ∧ reg m8 a2 = G := by
    simp +decide only [R8, runBlock, BInstr.run, gntB, upd_app, ↓reduceIte]
    rw [sp7]; refine ⟨rfl, ?_, BitVec.zero_add G⟩; rw [← e8_4, tv]
  have K8 : ∀ q, q.val ∉ [10, 11, 12] → reg m8 q = reg m7 q := fun q hq => by
    have hd : q ∉ gntB.filterMap BInstr.dst := by
      simp only [gntB, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [R8, runBlock_reg _ _ _ q u7.self.zero hd]
  obtain ⟨m9, c9, pc9, mem9, regs9⟩ := u8'.callRa hc5 gnt_at_2c gnt_at_30 (cb := DT) (by decide) (by decide)
  have r9 := PEnv.reg1 regs9 u8'.zero
  have hDTn : DT.toNat = (img% dateTimeAddress) := by decide
  have hTDn : TD.toNat = (img% timeDigits2Address) := by decide
  have hG8n : (G + 8).toNat = G.toNat + 8 := by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have offs0 : ∀ {c l : Nat}, 0x30 ≤ c → c + l ≤ 0x60 → Sep (H + BitVec.ofNat 32 c) l H 0x30 := fun h1 h2 => by
    have := offs (c := _) (n := _) (e := 0) (k := 0x30) (Or.inr (by omega : 0 + 0x30 ≤ _)) h2 (by decide)
    rwa [add_ofNat_zero] at this
  have sP4 : Sep (p + BitVec.ofNat 32 4) (n - 4) H 0x60 := sPG.sub (by omega)
  have sP4' : Sep (p + BitVec.ofNat 32 4) 10 H 0x60 := sPG.sub (by omega)
  obtain ⟨m10, c10, pc10, sp10, K10, hS10, hN10, fr10⟩ := dateTime_correct m9 (sp0 := G) (out := G + 8) (d := G)
    (p := p + 4) (Y := BitVec.ofNat 32 v) (retAddr := GNT + BitVec.ofNat 32 (0x2C + 8)) (n := n - 4)
    (by rw [mem9]; exact cd hcD (by rw [hDTn]; decide) (by rw [hDTn]; decide) IMd)
    (by rw [mem9]; exact cd hcT (by rw [hTDn]; decide) (by rw [hTDn]; decide) IMd) pc9
    (by rw [r9 a0 (by decide), v8.1]) (by rw [r9 a1 (by decide), v8.2.1]) (by rw [r9 a2 (by decide), v8.2.2])
    (by rw [regs9]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at GNT (by decide) _ (by decide)))
    (by rw [r9 sp (by decide), K8 sp (by decide), sp7]) hGa (by omega) (by omega) (by omega) hG8
    (by omega) hGa (by omega)
    (by rw [mem9]; exact tp) (by rw [mem9]; exact tn)
    (by rw [eG0, eG8]; exact offs0 (by omega) (by omega))
    (by rw [eG0, ← hG]; exact offs0 (by omega) (by omega))
    (by rw [eG8, ← hG]; exact offs (by omega) (by omega) (by omega))
    (by rw [eG0]; have := sP4.subR (c := 0) (l := 0x30) (by omega); rwa [add_ofNat_zero] at this)
    (by rw [← hG]; exact sP4.subR (by omega))
    (by rw [← hG]; exact (sP4'.subR (c := 0x30) (l := 8) (by omega)).symm)
  rw [mem9] at hS10 hN10 fr10
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2 ^ 32)] at hS10 hN10
  have hmb4 : memBytes Md (p + 4) (n - 4) = memBytes m.mem (p + 4) (n - 4) :=
    dn_memBytes_eq (hPm IMd) (c := 4) (l := n - 4) (by omega)
  rw [hmb4] at hS10 hN10
  -- back from `date_time`
  have I10 : ∀ x, Sep H 0x60 x 1 → m10.mem x = m.mem x := fun x hx => by
    have h1 : Sep (G + 0xFFFFFFD0) 0x30 x 1 := by
      rw [eG0]; have := inH (c := 0) (l := 0x30) hx (by decide); rwa [add_ofNat_zero] at this
    rw [fr10 x h1 (sGx816 hx) (sG0x8 hx), IMd x hx]
  have S10 : ∀ c', 0x48 ≤ c' → c' < 0x60 → m10.mem (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
    fun c' h1 h2 => by
      have e1 : Sep (G + 0xFFFFFFD0) 0x30 (H + BitVec.ofNat 32 c') 1 := by
        rw [eG0]; have := offs (c := 0) (n := 0x30) (e := c') (k := 1) (by omega) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      have e2 : Sep (G + 8) 16 (H + BitVec.ofNat 32 c') 1 := sGo (c := 8) (l := 16) (by decide) (by omega) h2
      have e3 : Sep G 8 (H + BitVec.ofNat 32 c') 1 := sG0o (by decide) (by omega) h2
      rw [fr10 _ e1 e2 e3, SMd c' h1 h2]
  have hc10 := cdG I10
  have u10 : St m10.mem GNT m10 0x34 (reg m10) := ⟨by rw [pc10], rfl, fun _ => rfl⟩
  have kk10 : ∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg m10 q = reg m q := fun q hq => by
    rw [K10 q (by revert hq; revert q; decide), r9 q (by revert hq; revert q; decide),
      K8 q (by revert hq; revert q; decide), u7.regs, K6 q (by revert hq; revert q; decide), kk5 q hq]
  have r8_10 : reg m10 8 = out := by
    rw [K10 8 (by decide), r9 8 (by decide), K8 8 (by decide), u7.regs, K6 8 (by decide), r8_5]
  have pre10 : Steps m m10 := pre5.trans (.cons d6 (.cons d7 (c8.trans (c9.trans c10))))
  obtain ⟨m11, d11, u11⟩ := u10.lbu hc10 gnt_at_34 (off' := 0x38) (by decide)
  have a011 : reg m11 a0 = (m10.mem (G + 8)).zeroExtend 32 := by
    rw [u11.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp10]
  have K11 : ∀ q, q ≠ a0 → reg m11 q = reg m10 q := fun q hq => by rw [u11.regs, upd_ne' hq u10.zero]
  cases hd : readDateTime v (memBytes m.mem (p + 4) (n - 4)) with
  | none =>
    obtain ⟨t1, t19⟩ := hN10 hd
    obtain ⟨m12, d12, u12⟩ := u11.self.notTaken hc10 0x3A gnt_at_38 (by decide) (by rw [a011, t1, u11.self.zero]; rfl)
    exact fin3A (pre10.trans (.cons d11 (.single d12))) u12.self I10 S10
      (by rw [u12.regs, K11 sp (by decide), sp10]) (by rw [u12.regs, K11 8 (by decide), r8_10])
      (fun q hq => by rw [u12.regs, K11 q (by revert hq; revert q; decide), kk10 q hq])
      (by rw [hspec, hy]; simp only [Option.bind]; rw [hd]) t19
  | some tr =>
  obtain ⟨t, rest2⟩ := tr
  obtain ⟨ht, t0', tlo, thi, hr2, hq, hL⟩ := hS10 t rest2 hd
  obtain ⟨m12, d12, u12⟩ := u11.self.taken hc10 0x40 gnt_at_38 (by decide) (by rw [a011, t0', u11.self.zero]; rfl)
  -- the bytes after the date and time
  generalize hqd : p + 4 + 10 = q at hr2 hq
  have hq4 : q = p + BitVec.ofNat 32 14 := by rw [← hqd, BitVec.add_assoc]; rfl
  generalize hLd : n - 4 - 10 = L at hr2 hL
  have hspecT : generalizedTime (memBytes m.mem p n) = gtTail (memBytes m.mem q L) t := by
    rw [hspec, hy]; simp only [Option.bind]; rw [hd]; dsimp only
    rw [hr2, hq4, dn_memBytes_eq (hPm IMd) (c := 14) (l := L) (by omega)]
  have hT := gtTail_mem m.mem q L t
  have pre12 : Steps m m12 := pre10.trans (.cons d11 (.single d12))
  have kb12 : ∀ r, r.val ∈ [2, 3, 4, 8, 21, 22, 23, 24, 25, 26, 27] → reg m12 r = reg m10 r := fun r hr => by
    rw [u12.regs, K11 r (by revert hr; revert r; decide)]
  have bad : ∀ {Mt : Word → BitVec 8} {nn : Machine}, Steps m nn → St Mt GNT nn 0xA4 (reg nn) →
      (∀ x, Sep H 0x60 x 1 → Mt x = m.mem x) →
      (∀ c', 0x48 ≤ c' → c' < 0x60 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      (∀ r, r.val ∈ [2, 3, 4, 8, 21, 22, 23, 24, 25, 26, 27] → reg nn r = reg m10 r) → ¬ gtOk m.mem q L →
      ∃ m', gntPost m m' sp0 out p retAddr H n := fun pre st hI hS hk hno =>
    finA4 pre st hI hS (by rw [hk sp (by decide), sp10]) (by rw [hk 8 (by decide), r8_10])
      (fun r hr => by rw [hk r (by revert hr; revert r; decide), kk10 r hr]) (by rw [hspecT]; exact hT.2 hno)
  have good : ∀ {Mt : Word → BitVec 8} {nn : Machine}, Steps m nn → St Mt GNT nn 0x60 (reg nn) →
      (∀ x, Sep H 0x60 x 1 → Mt x = m.mem x) →
      (∀ c', 0x48 ≤ c' → c' < 0x60 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      (∀ r, r.val ∈ [2, 3, 4, 8, 21, 22, 23, 24, 25, 26, 27] → reg nn r = reg m10 r) →
      reg nn 9 = BitVec.ofNat 32 (t % 2 ^ 32) → reg nn 18 = BitVec.ofNat 32 (t / 2 ^ 32) → gtOk m.mem q L →
      ∃ m', gntPost m m' sp0 out p retAddr H n := fun pre st hI hS hk r9' r18' hok =>
    finOk pre st hI hS (by rw [hk sp (by decide), sp10]) (by rw [hk 8 (by decide), r8_10])
      (fun r hr => by rw [hk r (by revert hr; revert r; decide), kk10 r hr]) r9' r18' ht
      (by rw [hspecT]; exact hT.1 hok)
  have hLb : L < 2 ^ 32 := by omega
  -- 0x40: the length of the rest
  obtain ⟨m13, d13, u13⟩ := u12.self.lw hc10 gnt_at_40 (off' := 0x42) (by decide)
    (by rw [kb12 sp (by decide), sp10]; exact hG4)
  have a013 : reg m13 a0 = BitVec.ofNat 32 L := by
    rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [kb12 sp (by decide), sp10, hL]
  have kb13 : ∀ r, r.val ∈ [2, 3, 4, 8, 21, 22, 23, 24, 25, 26, 27] → reg m13 r = reg m10 r := fun r hr => by
    rw [u13.regs, upd_ne' (by revert hr; revert r; decide) u12.self.zero, kb12 r hr]
  have pre13 : Steps m m13 := pre12.trans (.single d13)
  by_cases hL0 : L = 0
  · obtain ⟨m14, d14, u14⟩ := u13.self.taken hc10 0xA4 gnt_at_42 (by decide) (by
      rw [a013, u13.self.zero, dn_beq0 _ hLb]; exact decide_eq_true hL0)
    exact bad (pre13.trans (.single d14)) u14.self I10 S10 (fun r hr => by rw [u14.regs, kb13 r hr])
      (fun h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega)
  obtain ⟨m14, d14, u14⟩ := u13.self.notTaken hc10 0x44 gnt_at_42 (by decide) (by
    rw [a013, u13.self.zero, dn_beq0 _ hLb]; exact decide_eq_false hL0)
  -- 0x44: the first byte after the time, and the time itself
  have sq : ∀ i, i < L → Sep H 0x60 (q + BitVec.ofNat 32 i) 1 := fun i hi => by
    rw [hq4, add_ofNat_assoc]; exact sPG.symm.subR (c := 14 + i) (l := 1) (by omega)
  have bq : ∀ i, i < L → m10.mem (q + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i) := fun i hi =>
    I10 _ (sq i hi)
  have bq0 : m10.mem q = m.mem q := by have := bq 0 (by omega); rwa [add_ofNat_zero] at this
  have sp14 : reg m14 sp = G := by rw [u14.regs, kb13 sp (by decide), sp10]
  have a014 : reg m14 a0 = BitVec.ofNat 32 L := by rw [u14.regs, a013]
  obtain ⟨m15, c15, u15⟩ := St.block gntC u14.self hc10 gntC_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, gntC, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp14]
    exact ⟨aligned_add hGa (by decide), aligned_add hGa (by decide), aligned_add hGa (by decide)⟩)
  have R15 : ∀ r, reg m15 r = (runBlock gntC (m10.mem, reg m14)).2 r := u15.regs
  have u15' : St m10.mem GNT m15 0x56 (reg m15) := ⟨u15.pc, by rw [u15.mem]; rfl, fun _ => rfl⟩
  have e10 : G + 0x10 = G + 8 + 8 := by rw [BitVec.add_assoc]; rfl
  have e14 : G + 0x14 = G + 8 + 0xC := by rw [BitVec.add_assoc]; rfl
  have v15 : reg m15 a1 = q ∧ reg m15 a3 = (m.mem q).zeroExtend 32 ∧ reg m15 9 = BitVec.ofNat 32 (t % 2 ^ 32) ∧
      reg m15 18 = BitVec.ofNat 32 (t / 2 ^ 32) ∧
      reg m15 a4 = aluEval .add ((m.mem q).zeroExtend 32) 0xFFFFFFD2 ∧ reg m15 a2 = BitVec.ofNat 32 (L - 1) ∧
      reg m15 a0 = BitVec.ofNat 32 L := by
    simp +decide only [R15, runBlock, BInstr.run, gntC, upd_app, ↓reduceIte]
    simp only [add_lit_zero]
    rw [sp14, hq, bq0, e10, e14, tlo, thi, a014]
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
    exact BitVec.eq_of_toNat_eq (by
      rw [dn_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (4294967295 : Word).toNat = 4294967295 from rfl]; omega)
  obtain ⟨v15a1, v15a3, v15s1, v15s2, v15a4, v15a2, v15a0⟩ := v15
  have kb15 : ∀ r, r.val ∈ [2, 3, 4, 8, 21, 22, 23, 24, 25, 26, 27] → reg m15 r = reg m10 r := fun r hr => by
    have hd' : r ∉ gntC.filterMap BInstr.dst := by
      simp only [gntC, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hr; revert r; decide
    rw [R15, runBlock_reg _ _ _ r u14.self.zero hd', u14.regs, kb13 r hr]
  have pre15 : Steps m m15 := pre13.trans (.cons d14 c15)
  by_cases hdot : (m.mem q).toNat = 0x2E
  · obtain ⟨m16, d16, u16⟩ := u15'.taken hc10 0x6A gnt_at_56 (by decide) (by
      rw [v15a4, u15'.zero, gnt_isDot]; exact decide_eq_true hdot)
    by_cases hL1 : L - 1 = 0
    · obtain ⟨m17, d17, u17⟩ := u16.self.taken hc10 0xA4 gnt_at_6a (by decide) (by
        rw [u16.regs, v15a2, u16.self.zero, dn_beq0 _ (by omega)]; exact decide_eq_true hL1)
      exact bad (pre15.trans (.cons d16 (.single d17))) u17.self I10 S10
        (fun r hr => by rw [u17.regs, u16.regs, kb15 r hr])
        (fun h => by rcases h with ⟨_, h⟩ | ⟨h, _⟩ <;> omega)
    obtain ⟨m17, d17, u17⟩ := u16.self.notTaken hc10 0x6C gnt_at_6a (by decide) (by
      rw [u16.regs, v15a2, u16.self.zero, dn_beq0 _ (by omega)]; exact decide_eq_false hL1)
    -- 0x6C: the last byte must be `Z`
    obtain ⟨m18, c18, u18⟩ := St.block gntD u17.self hc10 gntD_end (by
      simp only [BlockOk, BInstr.ok, gntD, and_self])
    have R18 : ∀ r, reg m18 r = (runBlock gntD (m10.mem, reg m17)).2 r := u18.regs
    have u18' : St m10.mem GNT m18 0x7E (reg m18) := ⟨u18.pc, by rw [u18.mem]; rfl, fun _ => rfl⟩
    have eL1 : q + 1 + BitVec.ofNat 32 (L - 2) = q + BitVec.ofNat 32 (L - 1) := by
      rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]; congr 2; omega
    have hL2v : aluEval .add (BitVec.ofNat 32 L) 0xFFFFFFFE = BitVec.ofNat 32 (L - 2) :=
      BitVec.eq_of_toNat_eq (by
        rw [dn_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFE : Word).toNat = 4294967294 from rfl]
        omega)
    have r17 : ∀ r, reg m17 r = reg m15 r := fun r => by rw [u17.regs, u16.regs]
    have v18 : reg m18 a1 = q + 1 ∧ reg m18 20 = BitVec.ofNat 32 (L - 2) ∧
        reg m18 19 = q + 1 + BitVec.ofNat 32 (L - 2) ∧
        reg m18 a0 = aluEval .add ((m.mem (q + BitVec.ofNat 32 (L - 1))).zeroExtend 32) 0xFFFFFFA6 := by
      simp +decide only [R18, runBlock, BInstr.run, gntD, upd_app, ↓reduceIte]
      simp only [r17]
      rw [v15a1, v15a0, hL2v]; simp only [ev_add]
      rw [add_lit_zero, eL1, bq _ (by omega)]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
    obtain ⟨v18a1, v18s4, v18s3, v18a0⟩ := v18
    have kb18 : ∀ r, r.val ∈ [2, 3, 4, 8, 21, 22, 23, 24, 25, 26, 27] → reg m18 r = reg m10 r := fun r hr => by
      have hd' : r ∉ gntD.filterMap BInstr.dst := by
        simp only [gntD, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hr; revert r; decide
      rw [R18, runBlock_reg _ _ _ r u17.self.zero hd', r17, kb15 r hr]
    have k18 : ∀ r, r.val ∈ [9, 18] → reg m18 r = reg m15 r := fun r hr => by
      have hd' : r ∉ gntD.filterMap BInstr.dst := by
        simp only [gntD, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hr; revert r; decide
      rw [R18, runBlock_reg _ _ _ r u17.self.zero hd', r17]
    have pre18 : Steps m m18 := pre15.trans (.cons d16 (.cons d17 c18))
    by_cases hz : (m.mem (q + BitVec.ofNat 32 (L - 1))).toNat = 0x5A
    rotate_left
    · obtain ⟨m19, d19, u19⟩ := u18'.taken hc10 0xA4 gnt_at_7e (by decide) (by
        rw [v18a0, u18'.zero, gnt_isZ, decide_eq_false hz]; rfl)
      exact bad (pre18.trans (.single d19)) u19.self I10 S10 (fun r hr => by rw [u19.regs, kb18 r hr])
        (fun h => by
          rcases h with ⟨h, _⟩ | ⟨_, _, h, _⟩
          · omega
          · exact hz h)
    obtain ⟨m19, d19, u19⟩ := u18'.notTaken hc10 0x80 gnt_at_7e (by decide) (by
      rw [v18a0, u18'.zero, gnt_isZ, decide_eq_true hz]; rfl)
    -- 0x80: the fraction's reader at `G + 8`, and `all_ascii_digit`
    have sp19 : reg m19 sp = G := by rw [u19.regs, kb18 sp (by decide), sp10]
    have a19 : reg m19 a1 = q + 1 := by rw [u19.regs, v18a1]
    have s3_19 : reg m19 19 = q + 1 + BitVec.ofNat 32 (L - 2) := by rw [u19.regs, v18s3]
    obtain ⟨m20, c20, u20⟩ := St.block gntE u19.self hc10 gntE_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, gntE, and_true]
      rw [sp19]
      exact ⟨⟨hG8, slotC _ (by decide)⟩, hGC, slotC _ (by decide)⟩)
    have R20 : ∀ r, reg m20 r = (runBlock gntE (m10.mem, reg m19)).2 r := u20.regs
    obtain ⟨Me, hMe⟩ : ∃ Me, memStore32 (memStore32 m10.mem (G + 8) (q + 1)) (G + 0xC)
        (q + 1 + BitVec.ofNat 32 (L - 2)) = Me := ⟨_, rfl⟩
    have eMe : (runBlock gntE (m10.mem, reg m19)).1 = Me := by
      simp +decide only [runBlock, BInstr.run, gntE]
      rw [sp19, a19, s3_19, ← hMe]
    have u20' : St Me GNT m20 0x86 (reg m20) := ⟨u20.pc, by rw [u20.mem, eMe], fun _ => rfl⟩
    have IMe : ∀ x, Sep H 0x60 x 1 → Me x = m.mem x := fun x hx => by
      rw [← hMe, memStore32_get_sep (sGxC hx), memStore32_get_sep (sGx8 hx), I10 x hx]
    have SMe : ∀ c', 0x48 ≤ c' → c' < 0x60 → Me (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
      fun c' h1 h2 => by
        have e1 : Sep (G + 0xC) 4 (H + BitVec.ofNat 32 c') 1 := sGo (c := 0xC) (l := 4) (by decide) (by omega) h2
        have e2 : Sep (G + 8) 4 (H + BitVec.ofNat 32 c') 1 := sGo (c := 8) (l := 4) (by decide) (by omega) h2
        rw [← hMe, memStore32_get_sep e1, memStore32_get_sep e2, S10 c' h1 h2]
    have a020 : reg m20 a0 = G + 8 := by
      rw [R20]; simp +decide only [runBlock, BInstr.run, gntE, upd_app, ↓reduceIte]; rw [sp19]; rfl
    have kb20 : ∀ r, r ≠ a0 → reg m20 r = reg m19 r := fun r hr => by
      have hd' : r ∉ gntE.filterMap BInstr.dst := by
        simp only [gntE, List.filterMap_cons, List.filterMap_nil, BInstr.dst, List.mem_cons, List.mem_nil_iff,
          or_false]; exact hr
      rw [R20, runBlock_reg _ _ _ r u19.self.zero hd']
    obtain ⟨m21, c21, pc21, mem21, regs21⟩ := u20'.callRa (cdG IMe) gnt_at_86 gnt_at_8a (cb := AAD) (by decide)
      (by decide)
    have r21 := PEnv.reg1 regs21 u20'.zero
    have hAADn : AAD.toNat = (img% allAsciiDigitAddress) := by decide
    have sGC8 : Sep (G + 0xC) 4 (G + 8) 4 := by rw [eGC, eG8]; exact offs (by omega) (by omega) (by omega)
    have sIP : Sep (G + 8) 4 (q + 1) (L - 2) := by
      rw [eG8, hq4, show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]
      exact (sPG.sub (c := 14 + 1) (l := L - 2) (by omega)).symm.sub (c := 0x38) (l := 4) (by omega)
    obtain ⟨m22, c22, pc22, a022, K22, F22⟩ := allAsciiDigit_correct m21 (base := AAD) (it := G + 8) (p := q + 1)
      (L := L - 2) (retAddr := GNT + BitVec.ofNat 32 (0x86 + 8)) (by decide)
      (by rw [mem21]; exact cd hcA (by rw [hAADn]; decide) (by rw [hAADn]; decide) IMe) pc21
      (by rw [r21 a0 (by decide), a020]) hG8
      (by rw [mem21, ← hMe, memLoad32_store32_sep sGC8, memLoad32_store32_same])
      (by rw [mem21, e8_4, ← hMe, memLoad32_store32_same]) (by omega)
      (by rw [eG8]; exact hiC (by decide) (by rw [hAADn]; decide) (by rw [hAADn]; decide)) sIP
      (by rw [regs21]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at GNT (by decide) _ (by decide)))
    rw [mem21] at a022 F22
    have IM22 : ∀ x, Sep H 0x60 x 1 → m22.mem x = m.mem x := fun x hx => by rw [F22 x (sGx8 hx), IMe x hx]
    have SM22 : ∀ c', 0x48 ≤ c' → c' < 0x60 → m22.mem (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c') :=
      fun c' h1 h2 => by
        have e2 : Sep (G + 8) 4 (H + BitVec.ofNat 32 c') 1 := sGo (c := 8) (l := 4) (by decide) (by omega) h2
        rw [F22 _ e2, SMe c' h1 h2]
    have hc22 := cdG IM22
    have u22 : St m22.mem GNT m22 0x8E (reg m22) := ⟨by rw [pc22], rfl, fun _ => rfl⟩
    have k22 : ∀ r, r.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m22 r = reg m18 r :=
      fun r hr => by
        rw [K22 r (by revert hr; revert r; decide), r21 r (by revert hr; revert r; decide),
          kb20 r (by revert hr; revert r; decide), u19.regs]
    have hdigE : (memBytes Me (q + 1) (L - 2)).all (fun d => 48 ≤ d && d ≤ 57) = true ↔
        ∀ i, i < L - 2 → 48 ≤ (m.mem (q + BitVec.ofNat 32 (1 + i))).toNat ∧
          (m.mem (q + BitVec.ofNat 32 (1 + i))).toNat ≤ 57 := by
      rw [memBytes_all]
      have e : ∀ i, i < L - 2 → Me (q + 1 + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 (1 + i)) :=
        fun i hi => by
          rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]; exact IMe _ (sq _ (by omega))
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun h i hi => by rw [← e i hi]; exact h i hi, fun h i hi => by rw [e i hi]; exact h i hi⟩
    have pre22 : Steps m m22 := pre18.trans (.cons d19 (c20.trans (c21.trans c22)))
    by_cases hall : ∀ i, i < L - 2 → 48 ≤ (m.mem (q + BitVec.ofNat 32 (1 + i))).toNat ∧
        (m.mem (q + BitVec.ofNat 32 (1 + i))).toNat ≤ 57
    rotate_left
    · have h0 : reg m22 a0 = 0 := by rw [a022, if_neg (fun h => hall (hdigE.mp h))]
      obtain ⟨m23, d23, u23⟩ := u22.taken hc22 0xA4 gnt_at_8e (by decide) (by rw [h0, u22.zero]; rfl)
      exact bad (pre22.trans (.single d23)) u23.self IM22 SM22
        (fun r hr => by rw [u23.regs, k22 r (by revert hr; revert r; decide), kb18 r hr])
        (fun h => by
          rcases h with ⟨h, _⟩ | ⟨_, _, _, h, _⟩
          · omega
          · exact hall h)
    have h1 : reg m22 a0 = 1 := by rw [a022, if_pos (hdigE.mpr hall)]
    obtain ⟨m23, d23, u23⟩ := u22.notTaken hc22 0x90 gnt_at_8e (by decide) (by rw [h1, u22.zero]; rfl)
    by_cases hL2 : L - 2 = 0
    · obtain ⟨m24, d24, u24⟩ := u23.self.taken hc22 0xA4 gnt_at_90 (by decide) (by
        rw [u23.regs, k22 20 (by decide), v18s4, u23.self.zero, dn_beq0 _ (by omega)]; exact decide_eq_true hL2)
      exact bad (pre22.trans (.cons d23 (.single d24))) u24.self IM22 SM22
        (fun r hr => by rw [u24.regs, u23.regs, k22 r (by revert hr; revert r; decide), kb18 r hr])
        (fun h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega)
    obtain ⟨m24, d24, u24⟩ := u23.self.notTaken hc22 0x94 gnt_at_90 (by decide) (by
      rw [u23.regs, k22 20 (by decide), v18s4, u23.self.zero, dn_beq0 _ (by omega)]; exact decide_eq_false hL2)
    obtain ⟨m25, d25, u25⟩ := u24.self.aluImm hc22 gnt_at_94 (off' := 0x96) (by decide)
    have eL2 : q + 1 + BitVec.ofNat 32 (L - 2) + 0xFFFFFFFF = q + BitVec.ofNat 32 (L - 2) := by
      rw [BitVec.add_assoc q 1, BitVec.add_comm 1, BitVec.add_assoc, BitVec.add_assoc,
        show (1 : Word) + 0xFFFFFFFF = 0 from rfl, add_lit_zero]
    have s3_25 : reg m25 19 = q + BitVec.ofNat 32 (L - 2) := by
      rw [u25.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u24.regs, u23.regs, k22 19 (by decide), v18s3, ev_add, eL2]
    have hq2n : (q + BitVec.ofNat 32 (L - 2)).toNat ≠ 0 := by
      rw [hq4, add_ofNat_assoc, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    obtain ⟨m26, d26, u26⟩ := u25.self.notTaken hc22 0x9A gnt_at_96 (by decide) (by
      rw [s3_25, u25.self.zero]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]
      intro e; exact hq2n (by rw [e]; rfl))
    obtain ⟨m27, c27, u27⟩ := St.block gntF u26.self hc22 gntF_end (by simp only [BlockOk, BInstr.ok, gntF, and_self])
    have R27 : ∀ r, reg m27 r = (runBlock gntF (m22.mem, reg m26)).2 r := u27.regs
    have u27' : St m22.mem GNT m27 0xA2 (reg m27) := ⟨u27.pc, by rw [u27.mem]; rfl, fun _ => rfl⟩
    have v27 : reg m27 a0 = aluEval .add ((m.mem (q + BitVec.ofNat 32 (L - 2))).zeroExtend 32) 0xFFFFFFD0 := by
      simp +decide only [R27, runBlock, BInstr.run, gntF, upd_app, ↓reduceIte]
      rw [u26.regs, s3_25, add_lit_zero, IM22 _ (sq _ (by omega))]
    have k27 : ∀ r, r.val ∈ [2, 3, 4, 8, 9, 18, 21, 22, 23, 24, 25, 26, 27] → reg m27 r = reg m22 r := fun r hr => by
      have hd' : r ∉ gntF.filterMap BInstr.dst := by
        simp only [gntF, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hr; revert r; decide
      rw [R27, runBlock_reg _ _ _ r u26.self.zero hd', u26.regs, u25.regs,
        upd_ne' (by revert hr; revert r; decide) u24.self.zero, u24.regs, u23.regs]
    have pre27 : Steps m m27 := pre22.trans (.cons d23 (.cons d24 (.cons d25 (.cons d26 c27))))
    by_cases h0 : (m.mem (q + BitVec.ofNat 32 (L - 2))).toNat = 0x30
    · obtain ⟨m28, d28, u28⟩ := u27'.notTaken hc22 0xA4 gnt_at_a2 (by decide) (by
        rw [v27, u27'.zero, gnt_is0, decide_eq_true h0]; rfl)
      exact bad (pre27.trans (.single d28)) u28.self IM22 SM22
        (fun r hr => by
          rw [u28.regs, k27 r (by revert hr; revert r; decide), k22 r (by revert hr; revert r; decide), kb18 r hr])
        (fun h => by
          rcases h with ⟨h, _⟩ | ⟨_, _, _, _, h⟩
          · omega
          · exact h h0)
    obtain ⟨m28, d28, u28⟩ := u27'.taken hc22 0x60 gnt_at_a2 (by decide) (by
      rw [v27, u27'.zero, gnt_is0, decide_eq_false h0]; rfl)
    exact good (pre27.trans (.single d28)) u28.self IM22 SM22
      (fun r hr => by
        rw [u28.regs, k27 r (by revert hr; revert r; decide), k22 r (by revert hr; revert r; decide), kb18 r hr])
      (by rw [u28.regs, k27 9 (by decide), k22 9 (by decide), k18 9 (by decide), v15s1])
      (by rw [u28.regs, k27 18 (by decide), k22 18 (by decide), k18 18 (by decide), v15s2])
      (.inr ⟨by omega, hdot, hz, hall, h0⟩)
  -- not `.`: `Z` alone
  obtain ⟨m16, d16, u16⟩ := u15'.notTaken hc10 0x58 gnt_at_56 (by decide) (by
    rw [v15a4, u15'.zero, gnt_isDot]; exact decide_eq_false hdot)
  obtain ⟨m17, d17, u17⟩ := u16.self.aluImm hc10 gnt_at_58 (off' := 0x5C) (by decide)
  have v17 : reg m17 a0 = aluEval .add ((m.mem q).zeroExtend 32) 0xFFFFFFA6 := by
    rw [u17.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u16.regs, v15a3]
  have K17 : ∀ r, r ≠ a0 → reg m17 r = reg m15 r := fun r hr => by
    rw [u17.regs, upd_ne' hr u16.self.zero, u16.regs]
  by_cases hZ : (m.mem q).toNat = 0x5A
  rotate_left
  · obtain ⟨m18, d18, u18⟩ := u17.self.taken hc10 0xA4 gnt_at_5c (by decide) (by
      rw [v17, u17.self.zero, gnt_isZ, decide_eq_false hZ]; rfl)
    exact bad (pre15.trans (.cons d16 (.cons d17 (.single d18)))) u18.self I10 S10
      (fun r hr => by rw [u18.regs, K17 r (by revert hr; revert r; decide), kb15 r hr])
      (fun h => by
        rcases h with ⟨_, h⟩ | ⟨_, h, _⟩
        · exact hZ h
        · exact hdot h)
  obtain ⟨m18, d18, u18⟩ := u17.self.notTaken hc10 0x5E gnt_at_5c (by decide) (by
    rw [v17, u17.self.zero, gnt_isZ, decide_eq_true hZ]; rfl)
  by_cases hL1 : L - 1 = 0
  rotate_left
  · obtain ⟨m19, d19, u19⟩ := u18.self.taken hc10 0xA4 gnt_at_5e (by decide) (by
      rw [u18.regs, K17 a2 (by decide), v15a2, u18.self.zero, dn_bne0 _ (by omega), decide_eq_false hL1]; rfl)
    exact bad (pre15.trans (.cons d16 (.cons d17 (.cons d18 (.single d19))))) u19.self I10 S10
      (fun r hr => by rw [u19.regs, u18.regs, K17 r (by revert hr; revert r; decide), kb15 r hr])
      (fun h => by
        rcases h with ⟨h, _⟩ | ⟨_, h, _⟩
        · omega
        · exact hdot h)
  obtain ⟨m19, d19, u19⟩ := u18.self.notTaken hc10 0x60 gnt_at_5e (by decide) (by
    rw [u18.regs, K17 a2 (by decide), v15a2, u18.self.zero, dn_bne0 _ (by omega), decide_eq_true hL1]; rfl)
  exact good (pre15.trans (.cons d16 (.cons d17 (.cons d18 (.single d19))))) u19.self I10 S10
    (fun r hr => by rw [u19.regs, u18.regs, K17 r (by revert hr; revert r; decide), kb15 r hr])
    (by rw [u19.regs, u18.regs, K17 9 (by decide), v15s1]) (by rw [u19.regs, u18.regs, K17 18 (by decide), v15s2])
    (.inl ⟨by omega, hZ⟩)

end C3.RV32
