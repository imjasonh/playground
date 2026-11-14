import C3BootProofs.Proofs.CondNeg12

/-!
# `Int<2>::abs_sign`, as compiled

`crypto_bigint`'s `abs_sign` returns a two-limb signed integer's magnitude
and its sign. The compiled code copies `x` to its stack, negates it limb by
limb into a second buffer with a carry, takes the sign from the high word's
top bit, and selects the negation or `x` limb by limb with the masking of
`Uint<12>::select`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem ab_at_0 : fetchRel absSign2Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem ab_at_2 : fetchRel absSign2Code 0x2 = some (.store .sw sp x0 0x10, 2) := by decide
theorem ab_at_4 : fetchRel absSign2Code 0x4 = some (.store .sw sp x0 0x14, 2) := by decide
theorem ab_at_6 : fetchRel absSign2Code 0x6 = some (.aluImm .add a2 sp 0x10, 2) := by decide
theorem ab_at_8 : fetchRel absSign2Code 0x8 = some (.aluImm .add a3 x0 0x2, 2) := by decide
theorem ab_at_a : fetchRel absSign2Code 0xA = some (.alu .add a4 x0 a1, 2) := by decide
theorem ab_at_c : fetchRel absSign2Code 0xC = some (.branch .beq a3 x0 0xE, 2) := by decide
theorem ab_at_e : fetchRel absSign2Code 0xE = some (.load .lw a5 a4 0x0, 2) := by decide
theorem ab_at_10 : fetchRel absSign2Code 0x10 = some (.aluImm .add a4 a4 0x4, 2) := by decide
theorem ab_at_12 : fetchRel absSign2Code 0x12 = some (.store .sw a2 a5 0x0, 2) := by decide
theorem ab_at_14 : fetchRel absSign2Code 0x14 = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem ab_at_16 : fetchRel absSign2Code 0x16 = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem ab_at_18 : fetchRel absSign2Code 0x18 = some (.branch .bne a3 x0 0xFFFFFFF6, 2) := by decide
theorem ab_at_1a : fetchRel absSign2Code 0x1A = some (.aluImm .add (17 : Fin 32) x0 0x0, 2) := by decide
theorem ab_at_1c : fetchRel absSign2Code 0x1C = some (.load .lw a6 sp 0x14, 2) := by decide
theorem ab_at_1e : fetchRel absSign2Code 0x1E = some (.store .sw sp x0 0x8, 2) := by decide
theorem ab_at_20 : fetchRel absSign2Code 0x20 = some (.store .sw sp x0 0xC, 2) := by decide
theorem ab_at_22 : fetchRel absSign2Code 0x22 = some (.aluImm .add a3 x0 0x1, 2) := by decide
theorem ab_at_24 : fetchRel absSign2Code 0x24 = some (.aluImm .add (5 : Fin 32) sp 0x8, 4) := by decide
theorem ab_at_28 : fetchRel absSign2Code 0x28 = some (.aluImm .add a5 x0 0x2, 2) := by decide
theorem ab_at_2a : fetchRel absSign2Code 0x2A = some (.alu .add a2 x0 a1, 2) := by decide
theorem ab_at_2c : fetchRel absSign2Code 0x2C = some (.branch .beq a5 x0 0x1E, 2) := by decide
theorem ab_at_2e : fetchRel absSign2Code 0x2E = some (.load .lw a4 a2 0x0, 2) := by decide
theorem ab_at_30 : fetchRel absSign2Code 0x30 = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem ab_at_32 : fetchRel absSign2Code 0x32 = some (.aluImm .xor a4 a4 0xFFFFFFFF, 4) := by decide
theorem ab_at_36 : fetchRel absSign2Code 0x36 = some (.alu .add a4 a4 a3, 2) := by decide
theorem ab_at_38 : fetchRel absSign2Code 0x38 = some (.alu .sltu a3 a4 a3, 4) := by decide
theorem ab_at_3c : fetchRel absSign2Code 0x3C = some (.store .sw (5 : Fin 32) a4 0x0, 4) := by decide
theorem ab_at_40 : fetchRel absSign2Code 0x40 = some (.aluImm .add (5 : Fin 32) (5 : Fin 32) 0x4, 2) := by decide
theorem ab_at_42 : fetchRel absSign2Code 0x42 = some (.alu .add a3 a3 (17 : Fin 32), 2) := by decide
theorem ab_at_44 : fetchRel absSign2Code 0x44 = some (.aluImm .add a5 a5 0xFFFFFFFF, 2) := by decide
theorem ab_at_46 : fetchRel absSign2Code 0x46 = some (.aluImm .add (17 : Fin 32) x0 0x0, 2) := by decide
theorem ab_at_48 : fetchRel absSign2Code 0x48 = some (.branch .bne a5 x0 0xFFFFFFE6, 2) := by decide
theorem ab_at_4a : fetchRel absSign2Code 0x4A = some (.aluImm .srl (17 : Fin 32) a6 0x1F, 4) := by decide
theorem ab_at_4e : fetchRel absSign2Code 0x4E = some (.store .sw sp x0 0x10, 2) := by decide
theorem ab_at_50 : fetchRel absSign2Code 0x50 = some (.store .sw sp x0 0x14, 2) := by decide
theorem ab_at_52 : fetchRel absSign2Code 0x52 = some (.aluImm .add (5 : Fin 32) sp 0x8, 4) := by decide
theorem ab_at_56 : fetchRel absSign2Code 0x56 = some (.aluImm .add (6 : Fin 32) sp 0x10, 4) := by decide
theorem ab_at_5a : fetchRel absSign2Code 0x5A = some (.aluImm .add a5 x0 0x2, 2) := by decide
theorem ab_at_5c : fetchRel absSign2Code 0x5C = some (.aluImm .add a6 sp 0x1F, 4) := by decide
theorem ab_at_60 : fetchRel absSign2Code 0x60 = some (.branch .beq a5 x0 0x28, 2) := by decide
theorem ab_at_62 : fetchRel absSign2Code 0x62 = some (.load .lw a2 a1 0x0, 2) := by decide
theorem ab_at_64 : fetchRel absSign2Code 0x64 = some (.store .sb sp (17 : Fin 32) 0x1F, 4) := by decide
theorem ab_at_68 : fetchRel absSign2Code 0x68 = some (.load .lw a3 (5 : Fin 32) 0x0, 4) := by decide
theorem ab_at_6c : fetchRel absSign2Code 0x6C = some (.load .lbu a4 sp 0x1F, 4) := by decide
theorem ab_at_70 : fetchRel absSign2Code 0x70 = some (.alu .xor a3 a3 a2, 2) := by decide
theorem ab_at_72 : fetchRel absSign2Code 0x72 = some (.alu .sub a4 x0 a4, 4) := by decide
theorem ab_at_76 : fetchRel absSign2Code 0x76 = some (.alu .and a3 a3 a4, 2) := by decide
theorem ab_at_78 : fetchRel absSign2Code 0x78 = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem ab_at_7a : fetchRel absSign2Code 0x7A = some (.alu .xor a2 a2 a3, 2) := by decide
theorem ab_at_7c : fetchRel absSign2Code 0x7C = some (.aluImm .add (5 : Fin 32) (5 : Fin 32) 0x4, 2) := by decide
theorem ab_at_7e : fetchRel absSign2Code 0x7E = some (.store .sw (6 : Fin 32) a2 0x0, 4) := by decide
theorem ab_at_82 : fetchRel absSign2Code 0x82 = some (.aluImm .add (6 : Fin 32) (6 : Fin 32) 0x4, 2) := by decide
theorem ab_at_84 : fetchRel absSign2Code 0x84 = some (.aluImm .add a5 a5 0xFFFFFFFF, 2) := by decide
theorem ab_at_86 : fetchRel absSign2Code 0x86 = some (.branch .bne a5 x0 0xFFFFFFDC, 2) := by decide
theorem ab_at_88 : fetchRel absSign2Code 0x88 = some (.load .lw a1 sp 0x10, 2) := by decide
theorem ab_at_8a : fetchRel absSign2Code 0x8A = some (.load .lw a2 sp 0x14, 2) := by decide
theorem ab_at_8c : fetchRel absSign2Code 0x8C = some (.store .sw a0 a1 0x0, 2) := by decide
theorem ab_at_8e : fetchRel absSign2Code 0x8E = some (.store .sw a0 a2 0x4, 2) := by decide
theorem ab_at_90 : fetchRel absSign2Code 0x90 = some (.store .sb a0 (17 : Fin 32) 0x8, 4) := by decide
theorem ab_at_94 : fetchRel absSign2Code 0x94 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem ab_at_96 : fetchRel absSign2Code 0x96 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- From 0 to 0xC: the frame, the copy buffer zeroed, and the copy loop's
pointers. -/
def abPro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFE0, .sw sp x0 0x10, .sw sp x0 0x14, .aluImm .add a2 sp 0x10, .aluImm .add a3 x0 0x2,
   .alu .add a4 x0 a1]

/-- One limb of the copy, from 0xE to 0x18. -/
def abCp : List BInstr :=
  [.lw a5 a4 0x0, .aluImm .add a4 a4 0x4, .sw a2 a5 0x0, .aluImm .add a2 a2 0x4, .aluImm .add a3 a3 0xFFFFFFFF]

/-- From 0x1A to 0x2C: the high word, the negation buffer zeroed, and the
negation loop's carry and pointers. -/
def abMid : List BInstr :=
  [.aluImm .add (17 : Fin 32) x0 0x0, .lw a6 sp 0x14, .sw sp x0 0x8, .sw sp x0 0xC, .aluImm .add a3 x0 0x1,
   .aluImm .add (5 : Fin 32) sp 0x8, .aluImm .add a5 x0 0x2, .alu .add a2 x0 a1]

/-- One limb of the negation, from 0x2E to 0x48. -/
def abNg : List BInstr :=
  [.lw a4 a2 0x0, .aluImm .add a2 a2 0x4, .aluImm .xor a4 a4 0xFFFFFFFF, .alu .add a4 a4 a3, .alu .sltu a3 a4 a3,
   .sw (5 : Fin 32) a4 0x0, .aluImm .add (5 : Fin 32) (5 : Fin 32) 0x4, .alu .add a3 a3 (17 : Fin 32),
   .aluImm .add a5 a5 0xFFFFFFFF, .aluImm .add (17 : Fin 32) x0 0x0]

/-- From 0x4A to 0x60: the sign, the result buffer zeroed, and the select
loop's pointers. -/
def abSet : List BInstr :=
  [.aluImm .srl (17 : Fin 32) a6 0x1F, .sw sp x0 0x10, .sw sp x0 0x14, .aluImm .add (5 : Fin 32) sp 0x8,
   .aluImm .add (6 : Fin 32) sp 0x10, .aluImm .add a5 x0 0x2, .aluImm .add a6 sp 0x1F]

/-- One limb of the select, from 0x62 to 0x86. -/
def abSel : List BInstr :=
  [.lw a2 a1 0x0, .sb sp (17 : Fin 32) 0x1F, .lw a3 (5 : Fin 32) 0x0, .lbu a4 sp 0x1F, .alu .xor a3 a3 a2,
   .alu .sub a4 x0 a4, .alu .and a3 a3 a4, .aluImm .add a1 a1 0x4, .alu .xor a2 a2 a3,
   .aluImm .add (5 : Fin 32) (5 : Fin 32) 0x4, .sw (6 : Fin 32) a2 0x0, .aluImm .add (6 : Fin 32) (6 : Fin 32) 0x4,
   .aluImm .add a5 a5 0xFFFFFFFF]

/-- From 0x88 to 0x96: the result and the sign byte out, and the frame's
release. -/
def abEpi : List BInstr :=
  [.lw a1 sp 0x10, .lw a2 sp 0x14, .sw a0 a1 0x0, .sw a0 a2 0x4, .sb a0 (17 : Fin 32) 0x8, .aluImm .add sp sp 0x20]

section
set_option maxRecDepth 20000
theorem abPro_end : blockEnd absSign2Code 0 abPro = some 0xC := by decide
theorem abCp_end : blockEnd absSign2Code 0xE abCp = some 0x18 := by decide
theorem abMid_end : blockEnd absSign2Code 0x1A abMid = some 0x2C := by decide
theorem abNg_end : blockEnd absSign2Code 0x2E abNg = some 0x48 := by decide
theorem abSet_end : blockEnd absSign2Code 0x4A abSet = some 0x60 := by decide
theorem abSel_end : blockEnd absSign2Code 0x62 abSel = some 0x86 := by decide
theorem abEpi_end : blockEnd absSign2Code 0x88 abEpi = some 0x96 := by decide
end

def abCpKeep (q : Fin 32) : Bool := q.val ∉ [0, 12, 13, 14, 15]

set_option maxRecDepth 20000 in
theorem abCp_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock abCp (M, f)).1 = memStore32 M (f a2 + 0) (memLoad32 M (f a4 + 0)) ∧
    (runBlock abCp (M, f)).2 a4 = f a4 + 4 ∧ (runBlock abCp (M, f)).2 a2 = f a2 + 4 ∧
    (runBlock abCp (M, f)).2 a3 = f a3 + 0xFFFFFFFF ∧
    ∀ q, abCpKeep q = true → (runBlock abCp (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, abCp, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 4
  have h0 : q.val ≠ 0 := fun e => absurd (show abCpKeep q = false by unfold abCpKeep; simp [e]) (by rw [hq]; decide)
  simp only [h0, ite_false, pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a3) hq rfl, pkeep_ne (r := a4) hq rfl,
    pkeep_ne (r := a5) hq rfl]
  all_goals first | trivial | rfl

set_option maxRecDepth 20000 in
theorem abCp_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h14 : (f a4 + 0).toNat % 4 = 0) (h12 : (f a2 + 0).toNat % 4 = 0) (hs : Sep (f a2 + 0) 4 base len) :
    BlockOk base len abCp (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, abCp, upd_app, ↓reduceIte, and_true, true_and]
  exact ⟨h14, h12, hs⟩

def abNgKeep (q : Fin 32) : Bool := q.val ∉ [0, 5, 12, 13, 14, 15, 17]

set_option maxRecDepth 20000 in
theorem abNg_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock abNg (M, f)).1 = memStore32 M (f 5 + 0) (negW (memLoad32 M (f a2 + 0)) (f a3)) ∧
    (runBlock abNg (M, f)).2 a3 =
      aluEval .add (aluEval .sltu (negW (memLoad32 M (f a2 + 0)) (f a3)) (f a3)) (f 17) ∧
    (runBlock abNg (M, f)).2 a2 = f a2 + 4 ∧ (runBlock abNg (M, f)).2 5 = f 5 + 4 ∧
    (runBlock abNg (M, f)).2 a5 = f a5 + 0xFFFFFFFF ∧ (runBlock abNg (M, f)).2 17 = 0 ∧
    ∀ q, abNgKeep q = true → (runBlock abNg (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, abNg, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 6
  have h0 : q.val ≠ 0 := fun e => absurd (show abNgKeep q = false by unfold abNgKeep; simp [e]) (by rw [hq]; decide)
  simp only [h0, ite_false, pkeep_ne (r := 5) hq rfl, pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a3) hq rfl,
    pkeep_ne (r := a4) hq rfl, pkeep_ne (r := a5) hq rfl, pkeep_ne (r := 17) hq rfl]
  all_goals first | trivial | rfl

set_option maxRecDepth 20000 in
theorem abNg_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h12 : (f a2 + 0).toNat % 4 = 0) (h5 : (f 5 + 0).toNat % 4 = 0) (hs : Sep (f 5 + 0) 4 base len) :
    BlockOk base len abNg (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, abNg, upd_app, ↓reduceIte, and_true, true_and]
  exact ⟨h12, h5, hs⟩

def abSelKeep (q : Fin 32) : Bool := q.val ∉ [0, 5, 6, 11, 12, 13, 14, 15]

set_option maxRecDepth 20000 in
theorem abSel_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock abSel (M, f)).1 = memStore32 (memStore8 M (f sp + 0x1F) ((f 17).extractLsb' 0 8)) (f 6 + 0)
      (selWord (memLoad32 M (f a1 + 0)) (memLoad32 (memStore8 M (f sp + 0x1F) ((f 17).extractLsb' 0 8)) (f 5 + 0))
        ((memStore8 M (f sp + 0x1F) ((f 17).extractLsb' 0 8) (f sp + 0x1F)).zeroExtend 32)) ∧
    (runBlock abSel (M, f)).2 a1 = f a1 + 4 ∧ (runBlock abSel (M, f)).2 5 = f 5 + 4 ∧
    (runBlock abSel (M, f)).2 6 = f 6 + 4 ∧ (runBlock abSel (M, f)).2 a5 = f a5 + 0xFFFFFFFF ∧
    ∀ q, abSelKeep q = true → (runBlock abSel (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, abSel, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 5
  have h0 : q.val ≠ 0 := fun e => absurd (show abSelKeep q = false by unfold abSelKeep; simp [e]) (by rw [hq]; decide)
  simp only [h0, ite_false, pkeep_ne (r := 5) hq rfl, pkeep_ne (r := 6) hq rfl, pkeep_ne (r := a1) hq rfl,
    pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a3) hq rfl, pkeep_ne (r := a4) hq rfl, pkeep_ne (r := a5) hq rfl]
  all_goals first | trivial | rfl

set_option maxRecDepth 20000 in
theorem abSel_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h11 : (f a1 + 0).toNat % 4 = 0) (hb : Sep (f sp + 0x1F) 1 base len) (h5 : (f 5 + 0).toNat % 4 = 0)
    (h6 : (f 6 + 0).toNat % 4 = 0) (hs : Sep (f 6 + 0) 4 base len) :
    BlockOk base len abSel (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, abSel, upd_app, ↓reduceIte, and_true, true_and]
  exact ⟨h11, hb, h5, h6, hs⟩

/-- **One limb of the copy**, from 0xE. -/
theorem ab_cp_iter {M : Word → BitVec 8} {P B xp : Word} {n : Machine} {i : Nat}
    (s : St M P n 0xE (reg n)) (hc : CodeIn M P absSign2Code) (hi : i < 2) (hB : B.toNat % 4 = 0)
    (hxp : xp.toNat % 4 = 0) (sC : Sep (B + BitVec.ofNat 32 (4 * i)) 4 P absSign2Code.length)
    (r14 : reg n a4 = xp + BitVec.ofNat 32 (4 * i)) (r12 : reg n a2 = B + BitVec.ofNat 32 (4 * i))
    (r13 : reg n a3 = BitVec.ofNat 32 (2 - i)) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (B + BitVec.ofNat 32 (4 * i)) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))))
        P n' (if i + 1 < 2 then 0xE else 0x1A) (reg n') ∧
      reg n' a4 = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a2 = B + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' a3 = BitVec.ofNat 32 (2 - (i + 1)) ∧
      ∀ q, abCpKeep q = true → reg n' q = reg n q := by
  obtain ⟨E1, E14, E12, E13, Ek⟩ := abCp_run (M := M) (f := reg n)
  obtain ⟨n1, c1, u1⟩ := St.block abCp s hc abCp_end
    (abCp_ok (by rw [r14, add_lit_zero]; exact aligned_add hxp (by omega))
      (by rw [r12, add_lit_zero]; exact aligned_add hB (by omega)) (by rw [r12, add_lit_zero]; exact sC))
  rw [E1, r12, r14, add_lit_zero, add_lit_zero] at u1
  have hc1 := CodeIn.store32 (v := memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) hc sC
  have ea3 : reg n1 a3 = BitVec.ofNat 32 (2 - (i + 1)) := by rw [u1.regs, E13, r13, cnt2_dec i hi]
  have hb : branchTaken .bne (reg n1 a3) (reg n1 x0) = decide (i + 1 < 2) := by
    rw [ea3, u1.self.zero]; exact cnt2_ne i hi
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a4 = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a2 = B + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n2 a3 = BitVec.ofNat 32 (2 - (i + 1)) ∧ ∀ q, abCpKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, u1.regs, E14, r14, ptr4], by rw [h2, u1.regs, E12, r12, ptr4], by rw [h2, ea3],
      fun q hq => by rw [h2, u1.regs, Ek q hq]⟩
  by_cases hl : i + 1 < 2
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0xE ab_at_18 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x1A ab_at_18 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- **One limb of the negation**, from 0x2E. -/
theorem ab_ng_iter {M : Word → BitVec 8} {P B xp c : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x2E (reg n)) (hc : CodeIn M P absSign2Code) (hi : i < 2) (hB : B.toNat % 4 = 0)
    (hxp : xp.toNat % 4 = 0) (sC : Sep (B + BitVec.ofNat 32 (4 * i)) 4 P absSign2Code.length)
    (r12 : reg n a2 = xp + BitVec.ofNat 32 (4 * i)) (r5 : reg n 5 = B + BitVec.ofNat 32 (4 * i))
    (r15 : reg n a5 = BitVec.ofNat 32 (2 - i)) (r13 : reg n a3 = c) (r17 : reg n 17 = 0) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (B + BitVec.ofNat 32 (4 * i)) (negW (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) c))
        P n' (if i + 1 < 2 then 0x2E else 0x4A) (reg n') ∧
      reg n' a3 = aluEval .sltu (negW (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) c) c ∧
      reg n' a2 = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' 5 = B + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' a5 = BitVec.ofNat 32 (2 - (i + 1)) ∧ reg n' 17 = 0 ∧
      ∀ q, abNgKeep q = true → reg n' q = reg n q := by
  obtain ⟨E1, E13, E12, E5, E15, E17, Ek⟩ := abNg_run (M := M) (f := reg n)
  obtain ⟨n1, c1, u1⟩ := St.block abNg s hc abNg_end
    (abNg_ok (by rw [r12, add_lit_zero]; exact aligned_add hxp (by omega))
      (by rw [r5, add_lit_zero]; exact aligned_add hB (by omega)) (by rw [r5, add_lit_zero]; exact sC))
  rw [E1, r5, r12, r13, add_lit_zero, add_lit_zero] at u1
  rw [r12, r13, r17, add_lit_zero] at E13
  have hc1 := CodeIn.store32 (v := negW (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) c) hc sC
  have ea5 : reg n1 a5 = BitVec.ofNat 32 (2 - (i + 1)) := by rw [u1.regs, E15, r15, cnt2_dec i hi]
  have hb : branchTaken .bne (reg n1 a5) (reg n1 x0) = decide (i + 1 < 2) := by
    rw [ea5, u1.self.zero]; exact cnt2_ne i hi
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a3 = aluEval .sltu (negW (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) c) c ∧
      reg n2 a2 = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 5 = B + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n2 a5 = BitVec.ofNat 32 (2 - (i + 1)) ∧ reg n2 17 = 0 ∧
      ∀ q, abNgKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, u1.regs, E13]; exact BitVec.add_zero _, by rw [h2, u1.regs, E12, r12, ptr4],
      by rw [h2, u1.regs, E5, r5, ptr4], by rw [h2, ea5], by rw [h2, u1.regs, E17],
      fun q hq => by rw [h2, u1.regs, Ek q hq]⟩
  by_cases hl : i + 1 < 2
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0x2E ab_at_48 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x4A ab_at_48 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- **One limb of the select**, from 0x62: limb `i` of `x` or of its
negation at `N` to the buffer at `D`. -/
theorem ab_sel_iter {M : Word → BitVec 8} {P G N D xp s : Word} {n : Machine} {i : Nat}
    (st : St M P n 0x62 (reg n)) (hc : CodeIn M P absSign2Code) (hi : i < 2) (hss : s = 0 ∨ s = 1)
    (hN : N.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hxp : xp.toNat % 4 = 0)
    (sNb : Sep (G + 0x1F) 1 (N + BitVec.ofNat 32 (4 * i)) 4)
    (sC1 : Sep (G + 0x1F) 1 P absSign2Code.length) (sC2 : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P absSign2Code.length)
    (rsp : reg n sp = G) (r11 : reg n a1 = xp + BitVec.ofNat 32 (4 * i)) (r5 : reg n 5 = N + BitVec.ofNat 32 (4 * i))
    (r6 : reg n 6 = D + BitVec.ofNat 32 (4 * i)) (r15 : reg n a5 = BitVec.ofNat 32 (2 - i)) (r17 : reg n 17 = s) :
    ∃ n', Steps n n' ∧
      St (memStore32 (memStore8 M (G + 0x1F) (s.extractLsb' 0 8)) (D + BitVec.ofNat 32 (4 * i))
          (if s = 1 then memLoad32 M (N + BitVec.ofNat 32 (4 * i)) else memLoad32 M (xp + BitVec.ofNat 32 (4 * i))))
        P n' (if i + 1 < 2 then 0x62 else 0x88) (reg n') ∧
      reg n' a1 = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' 5 = N + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' 6 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a5 = BitVec.ofNat 32 (2 - (i + 1)) ∧
      ∀ q, abSelKeep q = true → reg n' q = reg n q := by
  obtain ⟨E1, E11, E5, E6, E15, Ek⟩ := abSel_run (M := M) (f := reg n)
  obtain ⟨n1, c1, u1⟩ := St.block abSel st hc abSel_end
    (abSel_ok (by rw [r11, add_lit_zero]; exact aligned_add hxp (by omega)) (by rw [rsp]; exact sC1)
      (by rw [r5, add_lit_zero]; exact aligned_add hN (by omega))
      (by rw [r6, add_lit_zero]; exact aligned_add hD (by omega)) (by rw [r6, add_lit_zero]; exact sC2))
  rw [E1, rsp, r17, r11, r5, r6, add_lit_zero, add_lit_zero, add_lit_zero, memLoad32_store8_sep sNb,
    choice_byte M _ s hss, selWord_eq _ _ s hss] at u1
  have hc1 := CodeIn.store32 (v := if s = 1 then memLoad32 M (N + BitVec.ofNat 32 (4 * i))
    else memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) (CodeIn.store8 (v := s.extractLsb' 0 8) hc sC1) sC2
  have ea5 : reg n1 a5 = BitVec.ofNat 32 (2 - (i + 1)) := by rw [u1.regs, E15, r15, cnt2_dec i hi]
  have hb : branchTaken .bne (reg n1 a5) (reg n1 x0) = decide (i + 1 < 2) := by
    rw [ea5, u1.self.zero]; exact cnt2_ne i hi
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a1 = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 5 = N + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n2 6 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a5 = BitVec.ofNat 32 (2 - (i + 1)) ∧
      ∀ q, abSelKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, u1.regs, E11, r11, ptr4], by rw [h2, u1.regs, E5, r5, ptr4],
      by rw [h2, u1.regs, E6, r6, ptr4], by rw [h2, ea5], fun q hq => by rw [h2, u1.regs, Ek q hq]⟩
  by_cases hl : i + 1 < 2
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0x62 ab_at_86 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x88 ab_at_86 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

theorem ab_sign01 (x : Word) : aluEval .srl x 0x1F = 0 ∨ aluEval .srl x 0x1F = 1 := by
  have h : (aluEval .srl x 0x1F).toNat = x.toNat / 2 ^ 31 := by
    show (x >>> 31).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hx := x.isLt
  rcases (by omega : (aluEval .srl x 0x1F).toNat = 0 ∨ (aluEval .srl x 0x1F).toNat = 1) with e | e
  · exact .inl (BitVec.eq_of_toNat_eq e)
  · exact .inr (BitVec.eq_of_toNat_eq e)

theorem ab_sign_val (x : Word) : (aluEval .srl x 0x1F).toNat = x.toNat / 2 ^ 31 := by
  show (x >>> 31).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `Int<2>::abs_sign`**, called with the result at `out` and
a two-limb signed integer `x` at `xp`, stores `|x|` as two limbs at `out`
and the sign (1 when `x` is negative) as the byte at `out + 8`. It returns
with `sp` and every register but `a1` through `a7`, `t0`, and `t1` as they
were, and changes no memory outside the 0x20 bytes below `sp` and the 9
bytes at `out`. -/
theorem absSign2_correct (m : Machine) {P sp0 out xp retAddr : Word}
    (hc : CodeIn m.mem P absSign2Code) (hpc : m.pc = P) (hsp : reg m sp = sp0)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hs4 : sp0.toNat % 4 = 0) (hs32 : 0x20 ≤ sp0.toNat) (hxp : xp.toNat % 4 = 0) (hout : out.toNat % 4 = 0)
    (sFC : Sep (sp0 + 0xFFFFFFE0) 0x20 P absSign2Code.length) (sOC : Sep out 9 P absSign2Code.length)
    (sXF : Sep xp 8 (sp0 + 0xFFFFFFE0) 0x20) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∉ [5, 6, 11, 12, 13, 14, 15, 16, 17] → reg m' q = reg m q) ∧
      limbVal (wordsAt m'.mem out 2) =
        (if limbVal (wordsAt m.mem xp 2) < 2 ^ 63 then limbVal (wordsAt m.mem xp 2)
         else 2 ^ 64 - limbVal (wordsAt m.mem xp 2)) ∧
      (m'.mem (out + 8)).toNat = (if limbVal (wordsAt m.mem xp 2) < 2 ^ 63 then 0 else 1) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 → Sep out 9 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hGd⟩ : ∃ G, sp0 + 0xFFFFFFE0 = G := ⟨_, rfl⟩
  rw [hGd] at sFC sXF ⊢
  have hGa : G.toNat % 4 = 0 := by rw [← hGd]; exact aligned_add hs4 (k := 0xFFFFFFE0) (by decide)
  have hGw : G.toNat + 0x20 = sp0.toNat := by
    rw [← hGd, BitVec.toNat_add]
    have : (0xFFFFFFE0 : Word).toNat = 0xFFFFFFE0 := rfl
    rw [this]; have := sp0.isLt; omega
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have sG : ∀ c l, c + l ≤ 0x20 → Sep (G + BitVec.ofNat 32 c) l P absSign2Code.length := fun c l h => sFC.sub h
  have aG : ∀ c, c % 4 = 0 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h => aligned_add hGa h
  -- the prologue
  obtain ⟨n1, c1, u1⟩ := St.block abPro s0 hc abPro_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, abPro, upd_app, ↓reduceIte, and_true, true_and]
    rw [show aluEval AluOp.add (reg m sp) 0xFFFFFFE0 = G by rw [hsp, ← hGd]; rfl]
    exact ⟨⟨aG 0x10 (by decide), sG 0x10 4 (by decide)⟩, aG 0x14 (by decide), sG 0x14 4 (by decide)⟩)
  simp only [runBlock, BInstr.run, abPro] at u1
  simp +decide only [upd_app, ↓reduceIte] at u1
  rw [show aluEval AluOp.add (reg m sp) 0xFFFFFFE0 = G by rw [hsp, ← hGd]; rfl] at u1
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 m.mem (G + 0x10) 0) (G + 0x14) 0 = M1 := ⟨_, rfl⟩
  rw [hM1] at u1
  have hc1 : CodeIn M1 P absSign2Code := by
    rw [← hM1]; exact (hc.store32 (sG 0x10 4 (by decide))).store32 (sG 0x14 4 (by decide))
  have g1 : ∀ q, reg n1 q = _ := u1.regs
  have x13 : reg n1 a3 = 2 := by rw [g1]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0xE ab_at_c (by decide) (by rw [x13, u1.self.zero]; decide)
  have k12 : ∀ q, q.val ≠ 0 → q ≠ sp → q ≠ a2 → q ≠ a3 → q ≠ a4 → reg n2 q = reg m q := fun q h0 h1 h2 h3 h4 => by
    rw [u2.regs, g1]; simp only [upd_app, h0, h1, h2, h3, h4, ite_false]
  have fr1 : ∀ x, Sep G 0x20 x 1 → M1 x = m.mem x := fun x hx => by
    have h1 : Sep (G + 0x14) 4 x 1 := hx.sub (c := 0x14) (l := 4) (by decide)
    have h0 : Sep (G + 0x10) 4 x 1 := hx.sub (c := 0x10) (l := 4) (by decide)
    rw [← hM1, memStore32_get_sep h1, memStore32_get_sep h0]
  -- the copy of `x` to `G + 0x10`
  have sX : ∀ i, i < 2 → Sep G 0x20 (xp + BitVec.ofNat 32 (4 * i)) 4 := fun i hi => sXF.symm.subR (by omega)
  obtain ⟨n3, c3, u3, e14, e12, e13, k3⟩ := ab_cp_iter (i := 0) (B := G + 0x10) (xp := xp) u2.self hc1 (by decide)
    (aG 0x10 (by decide)) hxp (by rw [u2_slot0]; exact sG 0x10 4 (by decide))
    (by
      rw [u2.regs, g1]; simp +decide only [upd_app, ↓reduceIte]; rw [ha1]
      exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm)
    (by rw [u2.regs, g1]; simp +decide only [upd_app, ↓reduceIte]; exact (add_ofNat_zero _).symm)
    (by rw [u2.regs, x13]; rfl)
  rw [show (if 0 + 1 < 2 then 0xE else 0x1A : Nat) = 0xE from rfl, u2_slot0, u2_slot0] at u3
  rw [u2_slot1] at e14 e12
  have lx0 : memLoad32 M1 xp = memLoad32 m.mem xp := load_frame fr1 (by have := sX 0 (by decide); rwa [u2_slot0] at this)
  rw [lx0] at u3
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 M1 (G + 0x10) (memLoad32 m.mem xp) = M2 := ⟨_, rfl⟩
  rw [hM2] at u3
  have hc2 : CodeIn M2 P absSign2Code := by rw [← hM2]; exact hc1.store32 (sG 0x10 4 (by decide))
  have fr2 : ∀ x, Sep G 0x20 x 1 → M2 x = m.mem x := fun x hx => by
    have h0 : Sep (G + 0x10) 4 x 1 := hx.sub (c := 0x10) (l := 4) (by decide)
    rw [← hM2, memStore32_get_sep h0, fr1 x hx]
  have g14 : G + 0x10 + 4 = G + 0x14 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n4, c4, u4, -, -, -, k4⟩ := ab_cp_iter (i := 1) (B := G + 0x10) (xp := xp) u3 hc2 (by decide)
    (aG 0x10 (by decide)) hxp (by rw [u2_slot1', g14]; exact sG 0x14 4 (by decide)) e14 e12 e13
  rw [show (if 1 + 1 < 2 then 0xE else 0x1A : Nat) = 0x1A from rfl, u2_slot1', u2_slot1', g14] at u4
  have lx1 : memLoad32 M2 (xp + 4) = memLoad32 m.mem (xp + 4) := load_frame fr2 (sX 1 (by decide))
  rw [lx1] at u4
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 M2 (G + 0x14) (memLoad32 m.mem (xp + 4)) = M3 := ⟨_, rfl⟩
  rw [hM3] at u4
  have s14 : Sep (G + 0x14) 4 P absSign2Code.length := sG 0x14 4 (by decide)
  have hc3 : CodeIn M3 P absSign2Code := by rw [← hM3]; exact hc2.store32 s14
  have fr3 : ∀ x, Sep G 0x20 x 1 → M3 x = m.mem x := fun x hx => by
    have h0 : Sep (G + 0x14) 4 x 1 := hx.sub (c := 0x14) (l := 4) (by decide)
    rw [← hM3, memStore32_get_sep h0, fr2 x hx]
  have k34 : ∀ q, abCpKeep q = true → reg n4 q = reg n2 q := fun q hq => by rw [k4 q hq, k3 q hq]
  have sp2 : reg n2 sp = G := by rw [u2.regs, g1]; simp +decide only [upd_app, ↓reduceIte]
  have sp4 : reg n4 sp = G := by rw [k34 sp rfl, sp2]
  have r11_4 : reg n4 a1 = xp := by
    rw [k34 a1 rfl, k12 a1 (by decide) (by decide) (by decide) (by decide) (by decide), ha1]
  -- the high word, and the negation buffer zeroed
  have s08 : Sep (G + 8) 4 P absSign2Code.length := sG 8 4 (by decide)
  have s0C : Sep (G + 0xC) 4 P absSign2Code.length := sG 0xC 4 (by decide)
  obtain ⟨n5, c5, u5⟩ := St.block abMid u4 hc3 abMid_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, abMid, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp4]
    exact ⟨aG 0x14 (by decide), ⟨aG 8 (by decide), s08⟩, aG 0xC (by decide), s0C⟩)
  simp only [runBlock, BInstr.run, abMid] at u5
  simp +decide only [upd_app, ↓reduceIte] at u5
  rw [sp4, r11_4] at u5
  have x14 : memLoad32 M3 (G + 0x14) = memLoad32 m.mem (xp + 4) := by rw [← hM3, memLoad32_store32_same]
  rw [x14] at u5
  obtain ⟨M4, hM4⟩ : ∃ M4, memStore32 (memStore32 M3 (G + 8) 0) (G + 0xC) 0 = M4 := ⟨_, rfl⟩
  rw [hM4] at u5
  have hc4 : CodeIn M4 P absSign2Code := by rw [← hM4]; exact (hc3.store32 s08).store32 s0C
  have fr4 : ∀ x, Sep G 0x20 x 1 → M4 x = m.mem x := fun x hx => by
    have h1 : Sep (G + 0xC) 4 x 1 := hx.sub (c := 0xC) (l := 4) (by decide)
    have h0 : Sep (G + 8) 4 x 1 := hx.sub (c := 8) (l := 4) (by decide)
    rw [← hM4, memStore32_get_sep h1, memStore32_get_sep h0, fr3 x hx]
  have g5 : ∀ q, reg n5 q = _ := u5.regs
  have x15 : reg n5 a5 = 2 := by rw [g5]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc4 0x2E ab_at_2c (by decide) (by rw [x15, u5.self.zero]; decide)
  have v6 : ∀ q, reg n6 q = reg n5 q := u6.regs
  -- the negation into `G + 8`
  have g8C : G + 8 + 4 = G + 0xC := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n7, c7, u7, e13, e12, e5, e15, e17, k7⟩ := ab_ng_iter (i := 0) (B := G + 8) (xp := xp) (c := 1) u6.self hc4
    (by decide) (aG 8 (by decide)) hxp (by rw [u2_slot0]; exact s08)
    (by rw [v6, g5]; simp +decide only [upd_app, ↓reduceIte]; exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm)
    (by rw [v6, g5]; simp +decide only [upd_app, ↓reduceIte]; exact (add_ofNat_zero _).symm)
    (by rw [v6, x15]; rfl) (by rw [v6, g5]; simp +decide only [upd_app, ↓reduceIte, aluEval]; try rfl)
    (by rw [v6, g5]; simp +decide only [upd_app, ↓reduceIte, aluEval]; try rfl)
  rw [show (if 0 + 1 < 2 then 0x2E else 0x4A : Nat) = 0x2E from rfl, u2_slot0, u2_slot0] at u7
  rw [u2_slot0] at e13
  rw [u2_slot1] at e12 e5
  have lx0' : memLoad32 M4 xp = memLoad32 m.mem xp := load_frame fr4 (by have := sX 0 (by decide); rwa [u2_slot0] at this)
  rw [lx0'] at u7 e13
  obtain ⟨M5, hM5⟩ : ∃ M5, memStore32 M4 (G + 8) (negW (memLoad32 m.mem xp) 1) = M5 := ⟨_, rfl⟩
  rw [hM5] at u7
  have hc5 : CodeIn M5 P absSign2Code := by rw [← hM5]; exact hc4.store32 s08
  have fr5 : ∀ x, Sep G 0x20 x 1 → M5 x = m.mem x := fun x hx => by
    have h0 : Sep (G + 8) 4 x 1 := hx.sub (c := 8) (l := 4) (by decide)
    rw [← hM5, memStore32_get_sep h0, fr4 x hx]
  obtain ⟨n8, c8, u8, e13', -, -, -, -, k8⟩ := ab_ng_iter (i := 1) (B := G + 8) (xp := xp) u7 hc5 (by decide)
    (aG 8 (by decide)) hxp (by rw [u2_slot1', g8C]; exact s0C) e12 e5 e15 e13 e17
  rw [show (if 1 + 1 < 2 then 0x2E else 0x4A : Nat) = 0x4A from rfl, u2_slot1', u2_slot1', g8C] at u8
  rw [u2_slot1'] at e13'
  have lx1' : memLoad32 M5 (xp + 4) = memLoad32 m.mem (xp + 4) := load_frame fr5 (sX 1 (by decide))
  rw [lx1'] at u8 e13'
  obtain ⟨M6, hM6⟩ : ∃ M6, memStore32 M5 (G + 0xC) (negW (memLoad32 m.mem (xp + 4))
      (aluEval .sltu (negW (memLoad32 m.mem xp) 1) 1)) = M6 := ⟨_, rfl⟩
  rw [hM6] at u8
  have hc6 : CodeIn M6 P absSign2Code := by rw [← hM6]; exact hc5.store32 s0C
  have fr6 : ∀ x, Sep G 0x20 x 1 → M6 x = m.mem x := fun x hx => by
    have h0 : Sep (G + 0xC) 4 x 1 := hx.sub (c := 0xC) (l := 4) (by decide)
    rw [← hM6, memStore32_get_sep h0, fr5 x hx]
  have k58 : ∀ q, abNgKeep q = true → reg n8 q = reg n5 q := fun q hq => by rw [k8 q hq, k7 q hq, v6]
  have k25 : ∀ q, q.val ≠ 0 → q ≠ (17 : Fin 32) → q ≠ a6 → q ≠ a3 → q ≠ (5 : Fin 32) → q ≠ a5 → q ≠ a2 →
      reg n5 q = reg n4 q := fun q h0 h1 h2 h3 h4 h5 h6 => by
    rw [g5]; simp only [upd_app, h0, h1, h2, h3, h4, h5, h6, ite_false]
  have sp8 : reg n8 sp = G := by
    rw [k58 sp rfl, k25 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp4]
  have r16_8 : reg n8 a6 = memLoad32 m.mem (xp + 4) := by
    rw [k58 a6 rfl, g5]; simp +decide only [upd_app, ↓reduceIte]
  -- the sign, and the result buffer zeroed
  have s10 : Sep (G + 0x10) 4 P absSign2Code.length := sG 0x10 4 (by decide)
  obtain ⟨n9, c9, u9⟩ := St.block abSet u8 hc6 abSet_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, abSet, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp8]
    exact ⟨⟨aG 0x10 (by decide), s10⟩, aG 0x14 (by decide), s14⟩)
  simp only [runBlock, BInstr.run, abSet] at u9
  simp +decide only [upd_app, ↓reduceIte] at u9
  rw [sp8, r16_8] at u9
  obtain ⟨M7, hM7⟩ : ∃ M7, memStore32 (memStore32 M6 (G + 0x10) 0) (G + 0x14) 0 = M7 := ⟨_, rfl⟩
  rw [hM7] at u9
  have hc7 : CodeIn M7 P absSign2Code := by rw [← hM7]; exact (hc6.store32 s10).store32 s14
  have fr7 : ∀ x, Sep G 0x20 x 1 → M7 x = m.mem x := fun x hx => by
    have h1 : Sep (G + 0x14) 4 x 1 := hx.sub (c := 0x14) (l := 4) (by decide)
    have h0 : Sep (G + 0x10) 4 x 1 := hx.sub (c := 0x10) (l := 4) (by decide)
    rw [← hM7, memStore32_get_sep h1, memStore32_get_sep h0, fr6 x hx]
  have g9 : ∀ q, reg n9 q = _ := u9.regs
  have x15' : reg n9 a5 = 2 := by rw [g9]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨n10, d10, u10⟩ := u9.self.notTaken hc7 0x62 ab_at_60 (by decide) (by rw [x15', u9.self.zero]; decide)
  have v10 : ∀ q, reg n10 q = reg n9 q := u10.regs
  obtain ⟨s, hs⟩ : ∃ s, aluEval .srl (memLoad32 m.mem (xp + 4)) 0x1F = s := ⟨_, rfl⟩
  have hss : s = 0 ∨ s = 1 := hs ▸ ab_sign01 _
  -- the select into `G + 0x10`
  have s1F : Sep (G + 0x1F) 1 P absSign2Code.length := sG 0x1F 1 (by decide)
  have sb1 : ∀ c, c + 4 ≤ 0x1F → Sep (G + 0x1F) 1 (G + BitVec.ofNat 32 c) 4 := fun c hc =>
    sep_offsets G (c := 0x1F) (n := 1) (d := c) (k := 4) (.inr hc) (by decide) (by omega)
  obtain ⟨n11, c11, u11, f11, f5, f6, f15, k11⟩ := ab_sel_iter (i := 0) (G := G) (N := G + 8) (D := G + 0x10)
    (xp := xp) (s := s) u10.self hc7 (by decide) hss (aG 8 (by decide)) (aG 0x10 (by decide)) hxp
    (by rw [u2_slot0]; exact sb1 8 (by decide)) s1F (by rw [u2_slot0]; exact s10)
    (by rw [v10, g9]; simp +decide only [upd_app, ↓reduceIte]; exact sp8)
    (by
      rw [v10, g9]; simp +decide only [upd_app, ↓reduceIte]
      rw [k58 a1 rfl, k25 a1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        r11_4]; exact (add_ofNat_zero _).symm)
    (by rw [v10, g9]; simp +decide only [upd_app, ↓reduceIte]; exact (add_ofNat_zero _).symm)
    (by rw [v10, g9]; simp +decide only [upd_app, ↓reduceIte]; exact (add_ofNat_zero _).symm)
    (by rw [v10, x15']; rfl) (by rw [v10, g9]; simp +decide only [upd_app, ↓reduceIte]; exact hs)
  rw [show (if 0 + 1 < 2 then 0x62 else 0x88 : Nat) = 0x62 from rfl, u2_slot0, u2_slot0, u2_slot0] at u11
  rw [u2_slot1] at f11 f5 f6
  -- the words the first pass selects from
  have sGG : ∀ a b : Nat, a + 4 ≤ b ∨ b + 4 ≤ a → a + 4 ≤ 0x20 → b + 4 ≤ 0x20 →
      Sep (G + BitVec.ofNat 32 a) 4 (G + BitVec.ofNat 32 b) 4 := fun a b h ha hb => sep_offsets G h (by omega) (by omega)
  have n0v : memLoad32 M7 (G + 8) = negW (memLoad32 m.mem xp) 1 := by
    have h14 : Sep (G + 0x14) 4 (G + 8) 4 := sGG 0x14 8 (by decide) (by decide) (by decide)
    have h10 : Sep (G + 0x10) 4 (G + 8) 4 := sGG 0x10 8 (by decide) (by decide) (by decide)
    have h0C : Sep (G + 0xC) 4 (G + 8) 4 := sGG 0xC 8 (by decide) (by decide) (by decide)
    rw [← hM7, memLoad32_store32_sep h14, memLoad32_store32_sep h10, ← hM6, memLoad32_store32_sep h0C, ← hM5,
      memLoad32_store32_same]
  have x0v : memLoad32 M7 xp = memLoad32 m.mem xp := load_frame fr7 (by have := sX 0 (by decide); rwa [u2_slot0] at this)
  rw [n0v, x0v] at u11
  obtain ⟨w0, hw0⟩ : ∃ w0, (if s = 1 then negW (memLoad32 m.mem xp) 1 else memLoad32 m.mem xp) = w0 := ⟨_, rfl⟩
  rw [hw0] at u11
  obtain ⟨M8, hM8⟩ : ∃ M8, memStore32 (memStore8 M7 (G + 0x1F) (s.extractLsb' 0 8)) (G + 0x10) w0 = M8 := ⟨_, rfl⟩
  rw [hM8] at u11
  have hc8 : CodeIn M8 P absSign2Code := by rw [← hM8]; exact (hc7.store8 s1F).store32 s10
  have ne1F : ∀ x, Sep G 0x20 x 1 → x ≠ G + 0x1F := fun x hx e => by
    have := hx.point (i := 0x1F) (j := 0) (by decide) (by decide)
    rw [add_ofNat_zero] at this; exact this e.symm
  have fr8 : ∀ x, Sep G 0x20 x 1 → M8 x = m.mem x := fun x hx => by
    have h0 : Sep (G + 0x10) 4 x 1 := hx.sub (c := 0x10) (l := 4) (by decide)
    rw [← hM8, memStore32_get_sep h0, memStore8_ne (ne1F x hx), fr7 x hx]
  have g14' : G + 0x10 + 4 = G + 0x14 := g14
  obtain ⟨n12, c12, u12, -, -, -, -, k12'⟩ := ab_sel_iter (i := 1) (G := G) (N := G + 8) (D := G + 0x10)
    (xp := xp) (s := s) u11 hc8 (by decide) hss (aG 8 (by decide)) (aG 0x10 (by decide)) hxp
    (by rw [u2_slot1', g8C]; exact sb1 0xC (by decide)) s1F (by rw [u2_slot1', g14]; exact s14)
    (by rw [k11 sp rfl, v10, g9]; simp +decide only [upd_app, ↓reduceIte]; exact sp8) f11 f5 f6 f15
    (by rw [k11 17 rfl, v10, g9]; simp +decide only [upd_app, ↓reduceIte]; exact hs)
  rw [show (if 1 + 1 < 2 then 0x62 else 0x88 : Nat) = 0x88 from rfl, u2_slot1', u2_slot1', u2_slot1', g8C, g14] at u12
  have n1v : memLoad32 M8 (G + 0xC) = negW (memLoad32 m.mem (xp + 4)) (aluEval .sltu (negW (memLoad32 m.mem xp) 1) 1) := by
    have h10 : Sep (G + 0x10) 4 (G + 0xC) 4 := sGG 0x10 0xC (by decide) (by decide) (by decide)
    have hb : Sep (G + 0x1F) 1 (G + 0xC) 4 := sb1 0xC (by decide)
    have h14 : Sep (G + 0x14) 4 (G + 0xC) 4 := sGG 0x14 0xC (by decide) (by decide) (by decide)
    have h10' : Sep (G + 0x10) 4 (G + 0xC) 4 := h10
    rw [← hM8, memLoad32_store32_sep h10, memLoad32_store8_sep hb, ← hM7, memLoad32_store32_sep h14,
      memLoad32_store32_sep h10', ← hM6, memLoad32_store32_same]
  have x1v : memLoad32 M8 (xp + 4) = memLoad32 m.mem (xp + 4) := load_frame fr8 (sX 1 (by decide))
  rw [n1v, x1v] at u12
  obtain ⟨w1, hw1⟩ : ∃ w1, (if s = 1 then negW (memLoad32 m.mem (xp + 4))
      (aluEval .sltu (negW (memLoad32 m.mem xp) 1) 1) else memLoad32 m.mem (xp + 4)) = w1 := ⟨_, rfl⟩
  rw [hw1] at u12
  obtain ⟨M9, hM9⟩ : ∃ M9, memStore32 (memStore8 M8 (G + 0x1F) (s.extractLsb' 0 8)) (G + 0x14) w1 = M9 := ⟨_, rfl⟩
  rw [hM9] at u12
  have hc9 : CodeIn M9 P absSign2Code := by rw [← hM9]; exact (hc8.store8 s1F).store32 s14
  have fr9 : ∀ x, Sep G 0x20 x 1 → M9 x = m.mem x := fun x hx => by
    have h0 : Sep (G + 0x14) 4 x 1 := hx.sub (c := 0x14) (l := 4) (by decide)
    rw [← hM9, memStore32_get_sep h0, memStore8_ne (ne1F x hx), fr8 x hx]
  -- registers through the loops
  have kAll : ∀ q, q.val ∉ [0, 2, 5, 6, 11, 12, 13, 14, 15, 16, 17] → reg n12 q = reg m q := fun q hq => by
    have ne : ∀ w : Fin 32, w.val ∈ [0, 2, 5, 6, 11, 12, 13, 14, 15, 16, 17] → q ≠ w := fun w hw e => hq (e ▸ hw)
    have h0 : q.val ≠ 0 := fun e => hq (by rw [e]; decide)
    have kS : abSelKeep q = true := by
      unfold abSelKeep; simp only [List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq] at hq ⊢; omega
    have kN : abNgKeep q = true := by
      unfold abNgKeep; simp only [List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq] at hq ⊢; omega
    have kC : abCpKeep q = true := by
      unfold abCpKeep; simp only [List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq] at hq ⊢; omega
    rw [k12' q kS, k11 q kS, v10, g9]
    simp only [upd_app, h0, ne 17 (by decide), ne 5 (by decide), ne 6 (by decide), ne a5 (by decide),
      ne a6 (by decide), ite_false]
    rw [k58 q kN, k25 q h0 (ne 17 (by decide)) (ne a6 (by decide)) (ne a3 (by decide)) (ne 5 (by decide))
      (ne a5 (by decide)) (ne a2 (by decide)), k34 q kC,
      k12 q h0 (ne sp (by decide)) (ne a2 (by decide)) (ne a3 (by decide)) (ne a4 (by decide))]
  have sp12 : reg n12 sp = G := by
    rw [k12' sp rfl, k11 sp rfl, v10, g9]; simp +decide only [upd_app, ↓reduceIte]; exact sp8
  have r10_12 : reg n12 a0 = out := by rw [kAll a0 (by decide), ha0]
  have r17_12 : reg n12 17 = s := by rw [k12' 17 rfl, k11 17 rfl, v10, g9]; simp +decide only [upd_app, ↓reduceIte]; exact hs
  -- the epilogue
  have sO0 : Sep out 4 P absSign2Code.length := by
    have := sOC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have sO4 : Sep (out + 4) 4 P absSign2Code.length := sOC.sub (c := 4) (l := 4) (by decide)
  have sO8 : Sep (out + 8) 1 P absSign2Code.length := sOC.sub (c := 8) (l := 1) (by decide)
  obtain ⟨n13, c13, u13⟩ := St.block abEpi u12 hc9 abEpi_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, abEpi, upd_app, ↓reduceIte, and_true]
    rw [sp12, r10_12, add_lit_zero]
    exact ⟨aG 0x10 (by decide), aG 0x14 (by decide), ⟨hout, sO0⟩, ⟨aligned_add hout (k := 4) (by decide), sO4⟩, sO8⟩)
  simp only [runBlock, BInstr.run, abEpi] at u13
  simp +decide only [upd_app, ↓reduceIte] at u13
  rw [sp12, r10_12, r17_12, add_lit_zero] at u13
  have m10 : memLoad32 M9 (G + 0x10) = w0 := by
    have h14 : Sep (G + 0x14) 4 (G + 0x10) 4 := sGG 0x14 0x10 (by decide) (by decide) (by decide)
    have hb : Sep (G + 0x1F) 1 (G + 0x10) 4 := sb1 0x10 (by decide)
    rw [← hM9, memLoad32_store32_sep h14, memLoad32_store8_sep hb, ← hM8, memLoad32_store32_same]
  have m14 : memLoad32 M9 (G + 0x14) = w1 := by rw [← hM9, memLoad32_store32_same]
  rw [m10, m14] at u13
  have hc13 := ((hc9.store32 (v := w0) sO0).store32 (v := w1) sO4).store8 (v := s.extractLsb' 0 8) sO8
  obtain ⟨n14, d14, pc14, mem14, regs14⟩ := u13.jalr hc13 ab_at_96
  have spF : G + 0x20 = sp0 := by rw [← hGd, BitVec.add_assoc]; exact BitVec.add_zero _
  have e2 : ∀ M, accV M out 2 = (memLoad32 M out).toNat + (memLoad32 M (out + 4)).toNat * 2 ^ 32 := fun M => by
    rw [accV_succ1, accV_succ1]
    simp only [u2_slot0, u2_slot1']
    rw [show accV M out 0 = 0 from rfl]
    omega
  have e2x : accV m.mem xp 2 = (memLoad32 m.mem xp).toNat + (memLoad32 m.mem (xp + 4)).toNat * 2 ^ 32 := by
    rw [accV_succ1, accV_succ1]
    simp only [u2_slot0, u2_slot1']
    rw [show accV m.mem xp 0 = 0 from rfl]
    omega
  have sOO : Sep (out + 4) 4 out 4 := by
    have := sep_offsets out (c := 4) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have sB0 : Sep (out + 8) 1 out 4 := by
    have := sep_offsets out (c := 8) (n := 1) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have sB4 : Sep (out + 8) 1 (out + 4) 4 :=
    sep_offsets out (c := 8) (n := 1) (d := 4) (k := 4) (.inr (by decide)) (by decide) (by decide)
  have o0 : memLoad32 n14.mem out = w0 := by
    rw [mem14, memLoad32_store8_sep sB0, memLoad32_store32_sep sOO, memLoad32_store32_same]
  have o1 : memLoad32 n14.mem (out + 4) = w1 := by
    rw [mem14, memLoad32_store8_sep sB4, memLoad32_store32_same]
  have ob : n14.mem (out + 8) = s.extractLsb' 0 8 := by rw [mem14]; exact memStore8_same _ _ _
  have hsv := ab_sign_val (memLoad32 m.mem (xp + 4))
  rw [hs] at hsv
  refine ⟨n14, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (.cons d6 (c7.trans (c8.trans (c9.trans (.cons d10
    (c11.trans (c12.trans (c13.trans (.single d14))))))))))))), ?_, ?_, fun q hq => ?_, ?_, ?_, fun x hx ho => ?_⟩
  · rw [pc14]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, kAll ra (by decide), hra, hret]
  · rw [regs14]; simp +decide only [upd_app, ↓reduceIte]; exact spF
  · by_cases hsq : q = sp
    · subst hsq; rw [regs14, hsp]; simp +decide only [upd_app, ↓reduceIte]; exact spF
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact (show reg n14 0 = 0 from rfl).trans (show reg m 0 = 0 from rfl).symm
    have ne : ∀ w : Fin 32, w.val ∈ [5, 6, 11, 12, 13, 14, 15, 16, 17] → q ≠ w := fun w hw e => hq (e ▸ hw)
    rw [regs14]
    simp only [upd_app, h0, hsq, ne a1 (by decide), ne a2 (by decide), ite_false]
    exact kAll q (by
      intro hm; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm hq
      have : q.val ≠ 2 := fun e => hsq (Fin.ext e)
      omega)
  · rw [limbVal_wordsAt, limbVal_wordsAt, e2, e2x, o0, o1, ← hw0, ← hw1]
    have nc0 := negW_carry (memLoad32 m.mem xp) 1
    have nc1 := negW_carry (memLoad32 m.mem (xp + 4)) (aluEval .sltu (negW (memLoad32 m.mem xp) 1) 1)
    have xo0 := xor_ones_toNat (memLoad32 m.mem xp)
    have xo1 := xor_ones_toNat (memLoad32 m.mem (xp + 4))
    have b0 := (memLoad32 m.mem xp).isLt
    have b1 := (memLoad32 m.mem (xp + 4)).isLt
    have b2 := (negW (memLoad32 m.mem xp) 1).isLt
    have b3 := (negW (memLoad32 m.mem (xp + 4)) (aluEval .sltu (negW (memLoad32 m.mem xp) 1) 1)).isLt
    have l1 := sltu_le1 (negW (memLoad32 m.mem xp) 1) 1
    have l2 := sltu_le1 (negW (memLoad32 m.mem (xp + 4)) (aluEval .sltu (negW (memLoad32 m.mem xp) 1) 1))
      (aluEval .sltu (negW (memLoad32 m.mem xp) 1) 1)
    have one : (1 : Word).toNat = 1 := rfl
    rw [one] at nc0
    rcases hss with rfl | rfl
    · rw [ite_eq_right (by decide), ite_eq_right (by decide)]
      have : (0 : Word).toNat = 0 := rfl
      rw [this] at hsv
      rw [ite_eq_left (by omega)]
    · rw [ite_eq_left rfl, ite_eq_left rfl]
      have : (1 : Word).toNat = 1 := rfl
      rw [this] at hsv
      rw [ite_eq_right (by omega)]
      generalize (negW (memLoad32 m.mem xp) 1).toNat = n0 at nc0 b2 ⊢
      generalize (negW (memLoad32 m.mem (xp + 4)) (aluEval .sltu (negW (memLoad32 m.mem xp) 1) 1)).toNat = n1 at nc1 b3 ⊢
      generalize (aluEval .sltu (negW (memLoad32 m.mem (xp + 4)) (aluEval .sltu (negW (memLoad32 m.mem xp) 1) 1))
        (aluEval .sltu (negW (memLoad32 m.mem xp) 1) 1)).toNat = cc2 at nc1 l2
      generalize (aluEval .sltu (negW (memLoad32 m.mem xp) 1) 1).toNat = cc1 at nc0 nc1 l1 l2
      generalize (aluEval .xor (memLoad32 m.mem xp) 0xFFFFFFFF).toNat = X0 at nc0 xo0
      generalize (aluEval .xor (memLoad32 m.mem (xp + 4)) 0xFFFFFFFF).toNat = X1 at nc1 xo1
      generalize (memLoad32 m.mem xp).toNat = x0 at xo0 b0 ⊢
      generalize (memLoad32 m.mem (xp + 4)).toNat = x1 at xo1 b1 hsv ⊢
      omega
  · rw [limbVal_wordsAt, e2x, ob]
    rcases hss with rfl | rfl
    · have : (0 : Word).toNat = 0 := rfl
      rw [this] at hsv
      rw [ite_eq_left (by omega)]; rfl
    · have : (1 : Word).toNat = 1 := rfl
      rw [this] at hsv
      rw [ite_eq_right (by omega)]; rfl
  · have h0 : Sep out 4 x 1 := by have := ho.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    have h4 : Sep (out + 4) 4 x 1 := ho.sub (c := 4) (l := 4) (by decide)
    have h8 : x ≠ out + 8 := fun e => by
      have := ho.point (i := 8) (j := 0) (by decide) (by decide)
      rw [add_ofNat_zero] at this; exact this e.symm
    rw [mem14, memStore8_ne h8, memStore32_get_sep h4, memStore32_get_sep h0, fr9 x hx]

end C3.RV32
