import C3BootProofs.Proofs.UintEq
import C3BootProofs.Proofs.P384Neg
import C3BootProofs.Proofs.P384Sub
import C3BootProofs.Proofs.DerTlv
import C3BootProofs.Proofs.DerOid

/-!
# Constant-time equality of `crypto_bigint` values, as compiled

`<[Limb] as CtEq>::ct_eq` ANDs a mask of each pair of limbs' equality into
an accumulator. `Uint<12>::ct_eq` splits each operand at limb 12 with
`UintRef::split_at`, compares the heads, and checks that both (empty) tails
are zero with `UintRef::is_zero`, which negates the proved `is_nonzero`.
`Choice::not` flips the low bit and tail-calls `black_box`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem uiz_at_0 : fetchRel uintRefIsZeroCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem uiz_at_2 : fetchRel uintRefIsZeroCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem uiz_at_4 : fetchRel uintRefIsZeroCode 0x4 = some (.auipc ra 0x0, 4) := by decide
theorem uiz_at_8 : fetchRel uintRefIsZeroCode 0x8 = some (.jalr ra ra 0x16, 4) := by decide
theorem uiz_at_c : fetchRel uintRefIsZeroCode 0xC = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem uiz_at_10 : fetchRel uintRefIsZeroCode 0x10 = some (.aluImm .xor a0 a0 0x1, 4) := by decide
theorem uiz_at_14 : fetchRel uintRefIsZeroCode 0x14 = some (.load .lw ra sp 0xC, 2) := by decide
theorem uiz_at_16 : fetchRel uintRefIsZeroCode 0x16 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem uiz_at_18 : fetchRel uintRefIsZeroCode 0x18 = some (.jalr x0 ra 0x0, 2) := by decide
theorem cnot_at_0 : fetchRel choiceNotCode 0x0 = some (.aluImm .xor a0 a0 0xFFFFFFFF, 4) := by decide
theorem cnot_at_4 : fetchRel choiceNotCode 0x4 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem cnot_at_6 : fetchRel choiceNotCode 0x6 = some (.auipc (6 : Fin 32) 0xFFFFC000, 4) := by decide
theorem cnot_at_a : fetchRel choiceNotCode 0xA = some (.jalr x0 (6 : Fin 32) 0xFFFFFDE8, 4) := by decide
theorem spl_at_0 : fetchRel splitAt12Code 0x0 = some (.aluImm .add a2 x0 0xC, 2) := by decide
theorem spl_at_2 : fetchRel splitAt12Code 0x2 = some (.aluImm .add a3 a1 0x30, 4) := by decide
theorem spl_at_6 : fetchRel splitAt12Code 0x6 = some (.store .sw a0 a1 0x0, 2) := by decide
theorem spl_at_8 : fetchRel splitAt12Code 0x8 = some (.store .sw a0 a2 0x4, 2) := by decide
theorem spl_at_a : fetchRel splitAt12Code 0xA = some (.store .sw a0 a3 0x8, 2) := by decide
theorem spl_at_c : fetchRel splitAt12Code 0xC = some (.store .sw a0 x0 0xC, 4) := by decide
theorem spl_at_10 : fetchRel splitAt12Code 0x10 = some (.jalr x0 ra 0x0, 2) := by decide
theorem lce_at_0 : fetchRel limbCtEqCode 0x0 = some (.branch .bne a1 a3 0x2C, 4) := by decide
theorem lce_at_4 : fetchRel limbCtEqCode 0x4 = some (.aluImm .add a3 x0 0x1, 2) := by decide
theorem lce_at_6 : fetchRel limbCtEqCode 0x6 = some (.branch .beq a1 x0 0x1C, 2) := by decide
theorem lce_at_8 : fetchRel limbCtEqCode 0x8 = some (.load .lw a4 a0 0x0, 2) := by decide
theorem lce_at_a : fetchRel limbCtEqCode 0xA = some (.load .lw a5 a2 0x0, 2) := by decide
theorem lce_at_c : fetchRel limbCtEqCode 0xC = some (.alu .xor a4 a4 a5, 2) := by decide
theorem lce_at_e : fetchRel limbCtEqCode 0xE = some (.aluImm .sltu a4 a4 0x1, 4) := by decide
theorem lce_at_12 : fetchRel limbCtEqCode 0x12 = some (.aluImm .add a4 a4 0xFFFFFFFF, 2) := by decide
theorem lce_at_14 : fetchRel limbCtEqCode 0x14 = some (.aluImm .xor a4 a4 0xFFFFFFFF, 4) := by decide
theorem lce_at_18 : fetchRel limbCtEqCode 0x18 = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem lce_at_1a : fetchRel limbCtEqCode 0x1A = some (.alu .and a3 a3 a4, 2) := by decide
theorem lce_at_1c : fetchRel limbCtEqCode 0x1C = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem lce_at_1e : fetchRel limbCtEqCode 0x1E = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem lce_at_20 : fetchRel limbCtEqCode 0x20 = some (.branch .bne a1 x0 0xFFFFFFE8, 2) := by decide
theorem lce_at_22 : fetchRel limbCtEqCode 0x22 = some (.aluImm .xor a0 a3 0x1, 4) := by decide
theorem lce_at_26 : fetchRel limbCtEqCode 0x26 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem lce_at_2a : fetchRel limbCtEqCode 0x2A = some (.jal x0 0x4, 2) := by decide
theorem lce_at_2c : fetchRel limbCtEqCode 0x2C = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem lce_at_2e : fetchRel limbCtEqCode 0x2E = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem lce_at_32 : fetchRel limbCtEqCode 0x32 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem lce_at_34 : fetchRel limbCtEqCode 0x34 = some (.aluImm .xor a0 a0 0xFFFFFFFF, 4) := by decide
theorem lce_at_38 : fetchRel limbCtEqCode 0x38 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem lce_at_3a : fetchRel limbCtEqCode 0x3A = some (.jalr x0 ra 0x0, 2) := by decide
theorem uce_at_0 : fetchRel uint12CtEqCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem uce_at_2 : fetchRel uint12CtEqCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem uce_at_4 : fetchRel uint12CtEqCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem uce_at_6 : fetchRel uint12CtEqCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem uce_at_8 : fetchRel uint12CtEqCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem uce_at_a : fetchRel uint12CtEqCode 0xA = some (.store .sw sp (19 : Fin 32) 0x1C, 2) := by decide
theorem uce_at_c : fetchRel uint12CtEqCode 0xC = some (.store .sw sp (20 : Fin 32) 0x18, 2) := by decide
theorem uce_at_e : fetchRel uint12CtEqCode 0xE = some (.store .sw sp (21 : Fin 32) 0x14, 2) := by decide
theorem uce_at_10 : fetchRel uint12CtEqCode 0x10 = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem uce_at_12 : fetchRel uint12CtEqCode 0x12 = some (.alu .add a1 x0 a0, 2) := by decide
theorem uce_at_14 : fetchRel uint12CtEqCode 0x14 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem uce_at_16 : fetchRel uint12CtEqCode 0x16 = some (.auipc ra 0x0, 4) := by decide
theorem uce_at_1a : fetchRel uint12CtEqCode 0x1A = some (.jalr ra ra 0x6A, 4) := by decide
theorem uce_at_1e : fetchRel uint12CtEqCode 0x1E = some (.load .lw (9 : Fin 32) sp 0x4, 2) := by decide
theorem uce_at_20 : fetchRel uint12CtEqCode 0x20 = some (.load .lw (18 : Fin 32) sp 0x8, 2) := by decide
theorem uce_at_22 : fetchRel uint12CtEqCode 0x22 = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem uce_at_24 : fetchRel uint12CtEqCode 0x24 = some (.load .lw (20 : Fin 32) sp 0x10, 2) := by decide
theorem uce_at_26 : fetchRel uint12CtEqCode 0x26 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem uce_at_28 : fetchRel uint12CtEqCode 0x28 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem uce_at_2a : fetchRel uint12CtEqCode 0x2A = some (.auipc ra 0x0, 4) := by decide
theorem uce_at_2e : fetchRel uint12CtEqCode 0x2E = some (.jalr ra ra 0x56, 4) := by decide
theorem uce_at_32 : fetchRel uint12CtEqCode 0x32 = some (.load .lw a2 sp 0x4, 2) := by decide
theorem uce_at_34 : fetchRel uint12CtEqCode 0x34 = some (.load .lw a3 sp 0x8, 2) := by decide
theorem uce_at_36 : fetchRel uint12CtEqCode 0x36 = some (.load .lw (8 : Fin 32) sp 0xC, 2) := by decide
theorem uce_at_38 : fetchRel uint12CtEqCode 0x38 = some (.load .lw (21 : Fin 32) sp 0x10, 2) := by decide
theorem uce_at_3a : fetchRel uint12CtEqCode 0x3A = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem uce_at_3c : fetchRel uint12CtEqCode 0x3C = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem uce_at_3e : fetchRel uint12CtEqCode 0x3E = some (.auipc ra 0xFFFFA000, 4) := by decide
theorem uce_at_42 : fetchRel uint12CtEqCode 0x42 = some (.jalr ra ra 0xFFFFFD7E, 4) := by decide
theorem uce_at_46 : fetchRel uint12CtEqCode 0x46 = some (.aluImm .and (9 : Fin 32) a0 0xFF, 4) := by decide
theorem uce_at_4a : fetchRel uint12CtEqCode 0x4A = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem uce_at_4c : fetchRel uint12CtEqCode 0x4C = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem uce_at_4e : fetchRel uint12CtEqCode 0x4E = some (.auipc ra 0xFFFED000, 4) := by decide
theorem uce_at_52 : fetchRel uint12CtEqCode 0x52 = some (.jalr ra ra 0x566, 4) := by decide
theorem uce_at_56 : fetchRel uint12CtEqCode 0x56 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem uce_at_5a : fetchRel uint12CtEqCode 0x5A = some (.alu .and (9 : Fin 32) (9 : Fin 32) a0, 2) := by decide
theorem uce_at_5c : fetchRel uint12CtEqCode 0x5C = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem uce_at_5e : fetchRel uint12CtEqCode 0x5E = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem uce_at_60 : fetchRel uint12CtEqCode 0x60 = some (.auipc ra 0xFFFED000, 4) := by decide
theorem uce_at_64 : fetchRel uint12CtEqCode 0x64 = some (.jalr ra ra 0x554, 4) := by decide
theorem uce_at_68 : fetchRel uint12CtEqCode 0x68 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem uce_at_6c : fetchRel uint12CtEqCode 0x6C = some (.alu .and a0 a0 (9 : Fin 32), 2) := by decide
theorem uce_at_6e : fetchRel uint12CtEqCode 0x6E = some (.load .lw ra sp 0x2C, 2) := by decide
theorem uce_at_70 : fetchRel uint12CtEqCode 0x70 = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem uce_at_72 : fetchRel uint12CtEqCode 0x72 = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem uce_at_74 : fetchRel uint12CtEqCode 0x74 = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem uce_at_76 : fetchRel uint12CtEqCode 0x76 = some (.load .lw (19 : Fin 32) sp 0x1C, 2) := by decide
theorem uce_at_78 : fetchRel uint12CtEqCode 0x78 = some (.load .lw (20 : Fin 32) sp 0x18, 2) := by decide
theorem uce_at_7a : fetchRel uint12CtEqCode 0x7A = some (.load .lw (21 : Fin 32) sp 0x14, 2) := by decide
theorem uce_at_7c : fetchRel uint12CtEqCode 0x7C = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem uce_at_7e : fetchRel uint12CtEqCode 0x7E = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- One pair of limbs, from 0x8 to the branch at 0x20. -/
def lceBody : List BInstr :=
  [.lw a4 a0 0x0, .lw a5 a2 0x0, .alu .xor a4 a4 a5, .aluImm .sltu a4 a4 0x1, .aluImm .add a4 a4 0xFFFFFFFF,
   .aluImm .xor a4 a4 0xFFFFFFFF, .aluImm .add a0 a0 0x4, .alu .and a3 a3 a4, .aluImm .add a2 a2 0x4,
   .aluImm .add a1 a1 0xFFFFFFFF]

/-- From 0x2E to the return: 1 for a zero argument, else 0. -/
def lceFin : List BInstr :=
  [.aluImm .sltu a0 a0 0x1, .aluImm .add a0 a0 0xFFFFFFFF, .aluImm .xor a0 a0 0xFFFFFFFF, .aluImm .and a0 a0 0x1]

section
set_option maxRecDepth 20000
theorem lceBody_end : blockEnd limbCtEqCode 0x8 lceBody = some 0x20 := by decide
theorem lceFin_end : blockEnd limbCtEqCode 0x2E lceFin = some 0x3A := by decide
end

/-- The mask of one limb pair: all ones when they are equal, else zero. -/
theorem lce_mask (x y : Word) : aluEval .xor (aluEval .add (aluEval .sltu (aluEval .xor x y) 1) 0xFFFFFFFF) 0xFFFFFFFF =
    if x = y then 0xFFFFFFFF else 0 := by
  rw [sltu1]
  by_cases h : x = y
  · subst h
    rw [ite_eq_left (show aluEval .xor x x = 0 from BitVec.xor_self), ite_eq_left rfl]; rfl
  · have h' : aluEval .xor x y ≠ 0 := fun e => h (BitVec.xor_eq_zero_iff.mp e)
    rw [ite_eq_right h', ite_eq_right h]; rfl

theorem lce_fin (w : Word) :
    aluEval .and (aluEval .xor (aluEval .add (aluEval .sltu w 1) 0xFFFFFFFF) 0xFFFFFFFF) 1 = if w = 0 then 1 else 0 := by
  rw [sltu1]
  by_cases h : w = 0
  · rw [ite_eq_left h]; rfl
  · rw [ite_eq_right h]; rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `<[Limb] as CtEq>::ct_eq`**: 1 when the `n` limbs at `p`
and the `n'` at `q` have the same length and the same values, and 0
otherwise. It writes no memory. -/
theorem limbCtEq_correct (m : Machine) {base retAddr p q : Word} {n n' : Nat} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base limbCtEqCode) (hpc : m.pc = base) (ha0 : reg m a0 = p)
    (ha1 : reg m a1 = BitVec.ofNat 32 n) (ha2 : reg m a2 = q) (ha3 : reg m a3 = BitVec.ofNat 32 n')
    (hn : n < 2 ^ 32) (hn' : n' < 2 ^ 32) (hp : p.toNat % 4 = 0) (hq : q.toNat % 4 = 0)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if n = n' ∧ ∀ i : Nat, i < n → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (q + BitVec.ofNat 32 (4 * i)) then 1 else 0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- the tail from 0x2E with `w` in `a0`
  have fin : ∀ {n1 : Machine}, St m.mem base n1 0x2E (reg n1) →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n1 r = reg m r) →
      ∃ m', Steps n1 m' ∧ m'.pc = retAddr ∧ reg m' a0 = (if reg n1 a0 = 0 then 1 else 0) ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
    intro n1 s hk
    obtain ⟨n2, c2, u2⟩ := St.block lceFin s hc lceFin_end (by simp [BlockOk, BInstr.ok, lceFin])
    simp only [runBlock, BInstr.run, lceFin] at u2
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc lce_at_3a
    refine ⟨n3, c2.trans (.single d3), ?_, ?_, fun r h0 h1 h2 h3 h4 h5 => ?_, mem3⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]
      rw [hk ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), add_lit_zero, hra, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [lce_fin]
    · rw [regs3]
      by_cases hq0 : r.val = 0
      · have : r = 0 := Fin.ext hq0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, hq0, h0, ite_false]; exact hk r h0 h1 h2 h3 h4 h5
  -- the loop, from limb `i` with `k` left, the accumulator 1 while all limbs agree
  have loop : ∀ k i, i + k = n → 0 < k → ∀ {n1 : Machine}, St m.mem base n1 0x8 (reg n1) →
      reg n1 a0 = p + BitVec.ofNat 32 (4 * i) → reg n1 a2 = q + BitVec.ofNat 32 (4 * i) →
      reg n1 a1 = BitVec.ofNat 32 k →
      reg n1 a3 = (if ∀ j : Nat, j < i → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * j)) =
        memLoad32 m.mem (q + BitVec.ofNat 32 (4 * j)) then 1 else 0) →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n1 r = reg m r) →
      ∃ n', Steps n1 n' ∧ St m.mem base n' 0x22 (reg n') ∧
        reg n' a3 = (if ∀ j : Nat, j < n → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * j)) =
          memLoad32 m.mem (q + BitVec.ofNat 32 (4 * j)) then 1 else 0) ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n' r = reg m r) := by
    intro k
    induction k with
    | zero => intro i _ hk; exact absurd hk (Nat.lt_irrefl 0)
    | succ k ih =>
      intro i hik _ n1 s r0 r2 r1 r3 hk
      obtain ⟨n2, c2, u2⟩ := St.block lceBody s hc lceBody_end (by
        simp +decide only [BlockOk, BInstr.ok, BInstr.run, lceBody, upd_app, ↓reduceIte, and_true]
        rw [r0, r2, add_lit_zero, add_lit_zero]
        exact ⟨aligned_add hp (by omega), aligned_add hq (by omega)⟩)
      simp only [runBlock, BInstr.run, lceBody] at u2
      have g2 : ∀ r, reg n2 r = _ := u2.regs
      have hacc : reg n2 a3 = (if ∀ j : Nat, j < i + 1 → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * j)) =
          memLoad32 m.mem (q + BitVec.ofNat 32 (4 * j)) then 1 else 0) := by
        rw [g2]; simp +decide only [upd_app, ↓reduceIte]
        rw [r0, r2, r3, add_lit_zero, add_lit_zero, lce_mask]
        by_cases he : memLoad32 m.mem (p + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (q + BitVec.ofNat 32 (4 * i))
        · rw [ite_eq_left he, show ∀ w : Word, aluEval .and w 0xFFFFFFFF = w from and_ones]
          by_cases hall : ∀ j : Nat, j < i → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * j)) =
              memLoad32 m.mem (q + BitVec.ofNat 32 (4 * j))
          · have hB : ∀ j : Nat, j < i + 1 → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * j)) =
                memLoad32 m.mem (q + BitVec.ofNat 32 (4 * j)) := fun j hj => by
              rcases Nat.lt_or_ge j i with h | h
              · exact hall j h
              · have : j = i := by omega
                subst this; exact he
            rw [ite_eq_left hall, ite_eq_left hB]
          · have hB : ¬ ∀ j : Nat, j < i + 1 → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * j)) =
                memLoad32 m.mem (q + BitVec.ofNat 32 (4 * j)) := fun h => hall (fun j hj => h j (by omega))
            rw [ite_eq_right hall, ite_eq_right hB]
        · have hB : ¬ ∀ j : Nat, j < i + 1 → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * j)) =
              memLoad32 m.mem (q + BitVec.ofNat 32 (4 * j)) := fun h => he (h i (Nat.lt_succ_self i))
          rw [ite_eq_right he, ite_eq_right hB]
          exact (BitVec.and_zero : _ &&& (0 : Word) = 0)
      have r21 : reg n2 a1 = BitVec.ofNat 32 k := by
        rw [g2]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, ev_add]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, ofNat_tn (by omega), ofNat_tn (by omega)]
        show (k + 1 + 4294967295) % 2 ^ 32 = k; omega
      have keep2 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n2 r = reg m r :=
        fun r h0' h1' h2' h3' h4' h5' => by
          rw [g2]
          by_cases h0 : r.val = 0
          · have : r = 0 := Fin.ext h0
            subst this; simp [upd]; exact hz.symm
          simp only [upd_app, h0, h0', h1', h2', h3', h4', h5', ite_false]; exact hk r h0' h1' h2' h3' h4' h5'
      have adv : ∀ b : Word, b + BitVec.ofNat 32 (4 * i) + 4 = b + BitVec.ofNat 32 (4 * (i + 1)) := fun b => by
        rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]; congr 2
      by_cases hk0 : k = 0
      · subst hk0
        obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0x22 lce_at_20 (by decide) (by rw [r21, u2.self.zero]; decide)
        exact ⟨n3, c2.trans (.single d3), u3.self, by rw [u3.regs, hacc, show i + 1 = n by omega],
          fun r h0' h1' h2' h3' h4' h5' => by rw [u3.regs]; exact keep2 r h0' h1' h2' h3' h4' h5'⟩
      · obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x8 lce_at_20 (by decide) (by
          rw [r21, u2.self.zero]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
          have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this; exact hk0 this)
        obtain ⟨n', c', h1, h2, h3⟩ := ih (i + 1) (by omega) (by omega) u3.self
          (by rw [u3.regs, g2]; simp +decide only [upd_app, ↓reduceIte]; rw [r0, ev_add, adv])
          (by rw [u3.regs, g2]; simp +decide only [upd_app, ↓reduceIte]; rw [r2, ev_add, adv])
          (by rw [u3.regs, r21]) (by rw [u3.regs, hacc])
          (fun r h0' h1' h2' h3' h4' h5' => by rw [u3.regs]; exact keep2 r h0' h1' h2' h3' h4' h5')
        exact ⟨n', c2.trans (.cons d3 c'), h1, h2, h3⟩
  -- 0x22 to 0x2E: `a0` is 0 exactly when every limb agreed
  have mid : ∀ {n1 : Machine} {b : Bool}, St m.mem base n1 0x22 (reg n1) → reg n1 a3 = (if b then 1 else 0) →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n1 r = reg m r) →
      ∃ n', Steps n1 n' ∧ St m.mem base n' 0x2E (reg n') ∧ (reg n' a0 = 0 ↔ b = true) ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n' r = reg m r) := by
    intro n1 b s r3 hk
    obtain ⟨n2, d2, u2⟩ := s.aluImm hc lce_at_22 (off' := 0x26) (by decide)
    obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hc lce_at_26 (off' := 0x2A) (by decide)
    obtain ⟨n4, d4, u4⟩ := u3.self.jump hc lce_at_2a (off' := 0x2E) (by decide) (by
      rw [u3.pc, show base + BitVec.ofNat 32 0x2A + 0x4 = base + BitVec.ofNat 32 0x2E by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at base hP 0x2E (by decide)))
    refine ⟨n4, .cons d2 (.cons d3 (.single d4)), u4.self, ?_, fun r h0 h1 h2 h3 h4 h5 => ?_⟩
    · rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.regs]
      simp +decide only [upd_app, ↓reduceIte]; rw [r3]
      cases b <;> decide
    · rw [u4.regs, u3.regs, updz u2.self.zero h0, u2.regs, updz s.zero h0]; exact hk r h0 h1 h2 h3 h4 h5
  by_cases hnn : n = n'
  · subst hnn
    obtain ⟨n1, d1, u1⟩ := s0.notTaken hc 0x4 lce_at_0 (by decide) (by
      rw [ha1, ha3]; simp only [branchTaken, bne_self_eq_false])
    obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hc lce_at_4 (off' := 0x6) (by decide)
    have k2 : ∀ r, r ≠ a3 → reg n2 r = reg m r := fun r h => by rw [u2.regs, updz u1.self.zero h, u1.regs]
    have a32 : reg n2 a3 = 1 := by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u1.self.zero]; rfl
    by_cases hn0 : n = 0
    · subst hn0
      obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x22 lce_at_6 (by decide) (by
        rw [k2 a1 (by decide), ha1, u2.self.zero]; decide)
      obtain ⟨n4, c4, u4, z4, k4⟩ := mid (b := true) u3.self (by rw [u3.regs, a32]; rfl)
        (fun r h0 h1 h2 h3 h4 h5 => by rw [u3.regs, k2 r h3])
      obtain ⟨m', c', h1, h2, h3, h4⟩ := fin u4 k4
      refine ⟨m', .cons d1 (.cons d2 (.cons d3 (c4.trans c'))), h1, ?_, h3, h4⟩
      rw [h2, ite_eq_left (z4.mpr rfl), ite_eq_left ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩]
    · obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0x8 lce_at_6 (by decide) (by
        rw [k2 a1 (by decide), ha1, u2.self.zero]
        simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; intro h
        have := congrArg BitVec.toNat h; rw [ofNat_tn hn] at this; change n = 0 at this; exact hn0 this)
      obtain ⟨n4, c4, s4, r4, k4⟩ := loop n 0 (by omega) (by omega) u3.self
        (by rw [u3.regs, k2 a0 (by decide), ha0, add_ofNat_zero])
        (by rw [u3.regs, k2 a2 (by decide), ha2, add_ofNat_zero])
        (by rw [u3.regs, k2 a1 (by decide), ha1])
        (by rw [u3.regs, a32, ite_eq_left (fun j hj => absurd hj (Nat.not_lt_zero j))])
        (fun r h0 h1 h2 h3 h4 h5 => by rw [u3.regs, k2 r h3])
      obtain ⟨n5, c5, u5, z5, k5⟩ := mid (b := decide (∀ j : Nat, j < n → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * j)) =
          memLoad32 m.mem (q + BitVec.ofNat 32 (4 * j)))) s4 (by
        rw [r4]
        by_cases hall : ∀ j : Nat, j < n → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * j)) =
            memLoad32 m.mem (q + BitVec.ofNat 32 (4 * j))
        · rw [ite_eq_left hall, decide_eq_true hall]; rfl
        · rw [ite_eq_right hall, decide_eq_false hall]; rfl) k4
      obtain ⟨m', c', h1, h2, h3, h4⟩ := fin u5 k5
      refine ⟨m', .cons d1 (.cons d2 (.cons d3 (c4.trans (c5.trans c')))), h1, ?_, h3, h4⟩
      rw [h2]
      by_cases hall : ∀ j : Nat, j < n → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * j)) =
          memLoad32 m.mem (q + BitVec.ofNat 32 (4 * j))
      · rw [ite_eq_left (z5.mpr (decide_eq_true hall)), ite_eq_left ⟨rfl, hall⟩]
      · rw [ite_eq_right (fun h => hall (of_decide_eq_true (z5.mp h))), ite_eq_right (fun h => hall h.2)]
  · obtain ⟨n1, d1, u1⟩ := s0.taken hc 0x2C lce_at_0 (by decide) (by
      rw [ha1, ha3]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
      have := congrArg BitVec.toNat h; rw [ofNat_tn hn, ofNat_tn hn'] at this; exact hnn this)
    obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hc lce_at_2c (off' := 0x2E) (by decide)
    obtain ⟨m', c', h1, h2, h3, h4⟩ := fin u2.self (fun r h0 _ _ _ _ _ => by rw [u2.regs, updz u1.self.zero h0, u1.regs])
    refine ⟨m', .cons d1 (.cons d2 c'), h1, ?_, h3, h4⟩
    rw [h2, ite_eq_right (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u1.self.zero]; decide),
      ite_eq_right (fun h => hnn h.1)]

/-- What `UintRef::split_at` at limb 12 stores at `out`: a head of 12 limbs
at `p` and an empty tail at `p + 48`. -/
def split12Mem (M : Word → BitVec 8) (out p : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 M out p) (out + 4) 12) (out + 8) (p + 0x30)) (out + 0xC) 0

/-- `split_at (.238)`'s body, from 0x0 to the return at 0x10. -/
def splBody : List BInstr :=
  [.aluImm .add a2 x0 0xC, .aluImm .add a3 a1 0x30, .sw a0 a1 0x0, .sw a0 a2 0x4, .sw a0 a3 0x8, .sw a0 x0 0xC]

section
set_option maxRecDepth 20000
theorem splBody_end : blockEnd splitAt12Code 0x0 splBody = some 0x10 := by decide
end

set_option maxRecDepth 20000 in
/-- **The compiled `UintRef::split_at (.238)`**: it stores `split12Mem` at
`out`. -/
theorem splitAt12_correct (m : Machine) {base retAddr out p : Word} (hc : CodeIn m.mem base splitAt12Code)
    (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = p) (hout : out.toNat % 4 = 0)
    (hsep : Sep out 16 base splitAt12Code.length) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = split12Mem m.mem out p ∧
      (∀ r, r ≠ a2 → r ≠ a3 → reg m' r = reg m r) := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hok : BlockOk base splitAt12Code.length splBody (m.mem, reg m) := by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, splBody, upd_app, ↓reduceIte, and_true, true_and]
    rw [ha0, add_lit_zero]
    exact ⟨⟨hout, hsep.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h⟩,
      ⟨aligned_add hout (by decide), hsep.sub (c := 4) (l := 4) (by decide)⟩,
      ⟨aligned_add hout (by decide), hsep.sub (c := 8) (l := 4) (by decide)⟩,
      ⟨aligned_add hout (by decide), hsep.sub (c := 0xC) (l := 4) (by decide)⟩⟩
  obtain ⟨m1, c1, u1⟩ := St.block splBody s0 hc splBody_end hok
  have hc1 := hc.runBlock splBody hok
  simp only [runBlock, BInstr.run, splBody] at u1 hc1
  obtain ⟨m2, d2, pc2, mem2, regs2⟩ := u1.jalr hc1 spl_at_10
  refine ⟨m2, c1.trans (.single d2), ?_, ?_, fun r h2 h3 => ?_⟩
  · rw [pc2]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, hra, hret]
  · rw [mem2]; simp +decide only [upd_app, ↓reduceIte]
    rw [ha0, ha1, hz, add_lit_zero, ev_add, zw]; rfl
  · rw [regs2]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, h0, h2, h3, ite_false]

/-- **The compiled `Choice::not (.164)`**: for a choice of 0 or 1 in `a0`,
it returns the other through `black_box`, which writes the byte below `sp`. -/
theorem choiceNot_correct (m : Machine) {P retAddr c : Word} (hP : P.toNat % 2 = 0)
    (hc : CodeIn m.mem P choiceNotCode) (hb : CodeIn m.mem (P + 0xFFFFBDEE) blackBoxU8Code) (hpc : m.pc = P)
    (ha0 : reg m a0 = c) (hcv : c.toNat ≤ 1) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsep : Sep (reg m sp + 0xFFFFFFFF) 1 (P + 0xFFFFBDEE) blackBoxU8Code.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' a0 = BitVec.ofNat 32 (1 - c.toNat) ∧
      (∀ q, q ≠ a0 → q ≠ t1 → reg m' q = reg m q) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFFF) 1 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc cnot_at_0 (off' := 4) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hc cnot_at_4 (off' := 6) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.auipc hc cnot_at_6 (off' := 0xA) (by decide)
  obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.self.jalr hc cnot_at_a
  have k3 : ∀ q, q ≠ a0 → q ≠ t1 → reg n3 q = reg m q := fun q h0 ht => by
    rw [u3.regs, updz u2.self.zero ht, u2.regs, updz u1.self.zero h0, u1.regs, updz hz h0]
  have v3 : reg n3 a0 = BitVec.ofNat 32 (1 - c.toNat) := by
    rw [u3.regs, upd_ne (by decide) (by decide), u2.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]
    have e := (ofNat_toNat_self c).symm
    rcases (by omega : c.toNat = 0 ∨ c.toNat = 1) with h | h <;> rw [e, h] <;> rfl
  have pcB : n4.pc = P + 0xFFFFBDEE := by
    rw [pc4, u3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [show P + BitVec.ofNat 32 6 + 0xFFFFC000 + 0xFFFFFDE8 = P + 0xFFFFBDEE by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at P hP 0xFFFFBDEE (by decide))
  obtain ⟨m5, c5, pc5, a05, k5, f5⟩ := blackBoxU8_correct n4 (by rw [mem4]; exact hb) pcB
    (by rw [regs4, k3 ra (by decide) (by decide), hra]) hret
    (by rw [regs4, k3 sp (by decide) (by decide)]; exact hsep)
  refine ⟨m5, .cons d1 (.cons d2 (.cons d3 (.cons d4 c5))), pc5, ?_, fun q h0 ht => ?_, fun x hx => ?_⟩
  · rw [a05, regs4, v3]
    rcases (by omega : c.toNat = 0 ∨ c.toNat = 1) with h | h <;> rw [h] <;> rfl
  · rw [k5 q h0, regs4, k3 q h0 ht]
  · rw [f5 x (by rw [regs4, k3 sp (by decide) (by decide)]; exact hx), mem4]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `UintRef::is_zero`**: 1 when all `len` words at `ptr` are
zero, and 0 otherwise, through the proved `is_nonzero`. It writes only the
0x14 bytes of stack below `sp`. -/
theorem uintRefIsZero_correct (m : Machine) {P retAddr ptr sp0 : Word} {len : Nat} (hP : P.toNat % 2 = 0)
    (hc : CodeIn m.mem P uintRefIsZeroCode) (hn : CodeIn m.mem (P + 0x1A) uintRefIsNonzeroCode)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (hsa : sp0.toNat % 4 = 0)
    (ha0 : reg m a0 = ptr) (ha1 : reg m a1 = BitVec.ofNat 32 len) (hlen : len < 2 ^ 32) (hptr : ptr.toNat % 4 = 0)
    (sFC : Sep (sp0 + 0xFFFFFFEC) 0x14 P uintRefIsZeroCode.length)
    (sFN : Sep (sp0 + 0xFFFFFFEC) 0x14 (P + 0x1A) uintRefIsNonzeroCode.length)
    (sPF : Sep ptr (4 * len) (sp0 + 0xFFFFFFEC) 0x14)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      reg m' a0 = (if ∀ i : Nat, i < len → memLoad32 m.mem (ptr + BitVec.ofNat 32 (4 * i)) = 0 then 1 else 0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m' r = reg m r) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFEC) 0x14 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFF0 = F := ⟨_, rfl⟩
  have hFG : sp0 + 0xFFFFFFEC = F + 0xFFFFFFFC := by rw [← hF, BitVec.add_assoc]; rfl
  rw [hFG] at sFC sFN sPF ⊢
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hsa (k := 0xFFFFFFF0) (by decide)
  have eS : F + 0x10 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hslot : Sep (F + 0xC) 4 P uintRefIsZeroCode.length := by
    rw [show F + 0xC = F + 0xFFFFFFFC + BitVec.ofNat 32 0x10 by rw [BitVec.add_assoc]; rfl]
    exact sFC.sub (by decide)
  have sslot : ∀ x, Sep (F + 0xFFFFFFFC) 0x14 x 1 → Sep (F + 0xC) 4 x 1 := fun x hx => by
    rw [show F + 0xC = F + 0xFFFFFFFC + BitVec.ofNat 32 0x10 by rw [BitVec.add_assoc]; rfl]
    exact hx.sub (by decide)
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc uiz_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨n2, d2, u2⟩ := u1.sw hc uiz_at_2 (off' := 4) (by decide) (by rw [sp1]; exact aligned_add hFa (by decide))
  rw [sp1] at u2
  have hc2 := hc.store32 (v := upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0) ra) hslot
  have hn2 : CodeIn (memStore32 m.mem (F + 0xC) (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0) ra))
      (P + 0x1A) uintRefIsNonzeroCode := hn.store32 (by
    rw [show F + 0xC = F + 0xFFFFFFFC + BitVec.ofNat 32 0x10 by rw [BitVec.add_assoc]; rfl]
    exact sFN.sub (by decide))
  obtain ⟨n3, c3, pc3, mem3, regs3⟩ := u2.self.callRa hc2 uiz_at_4 uiz_at_8 (cb := P + 0x1A)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP 0x1A (by decide))
  have r3 := PEnv.reg1 regs3 u2.self.zero
  have k2 : ∀ q, q ≠ sp → reg n2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp3 : reg n3 sp = F := by rw [r3 sp (by decide), u2.regs, sp1]
  obtain ⟨n4, c4, pc4, a04, k4, f4⟩ := uintRefIsNonzero_correct n3 (ptr := ptr) (len := len)
    (retAddr := P + BitVec.ofNat 32 0xC) (by rw [mem3]; exact hn2)
    pc3 (by rw [r3 a0 (by decide), k2 a0 (by decide), ha0]) (by rw [r3 a1 (by decide), k2 a1 (by decide), ha1]) hlen hptr
    (by rw [sp3]; exact hFa) (by rw [sp3]; exact sFN.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
    (by rw [regs3]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P hP 0xC (by decide)))
  rw [mem3] at f4 a04
  rw [sp3] at f4
  have eW : ∀ i, i < len → memLoad32 (memStore32 m.mem (F + 0xC) (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0) ra))
      (ptr + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (ptr + BitVec.ofNat 32 (4 * i)) := fun i hi =>
    memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      exact memStore32_get_sep (sslot _ (sPF.symm.subR (c := 4 * i + j) (l := 1) (by omega)))
  have a04' : reg n4 a0 = (if ∀ i : Nat, i < len → memLoad32 m.mem (ptr + BitVec.ofNat 32 (4 * i)) = 0
      then 0 else 1) := by
    rw [a04]
    by_cases hall : ∀ i : Nat, i < len → memLoad32 m.mem (ptr + BitVec.ofNat 32 (4 * i)) = 0
    · rw [ite_eq_left (fun i hi => by rw [eW i hi]; exact hall i hi), ite_eq_left hall]
    · rw [ite_eq_right (fun h => hall (fun i hi => by rw [← eW i hi]; exact h i hi)), ite_eq_right hall]
  have sF4 : ∀ x, Sep (F + 0xFFFFFFFC) 0x14 x 1 → Sep (F + 0xFFFFFFFC) 4 x 1 := fun x hx =>
    hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h
  have hc4 : CodeIn n4.mem P uintRefIsZeroCode := fun i hi => by
    rw [f4 _ (sF4 _ (sFC.subR (c := i) (l := 1) (by omega)))]; exact hc2 i hi
  have u4 : St n4.mem P n4 0xC (reg n4) := ⟨pc4, rfl, fun _ => rfl⟩
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc4 uiz_at_c (off' := 0x10) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.self.aluImm hc4 uiz_at_10 (off' := 0x14) (by decide)
  have sp4 : reg n4 sp = F := by
    rw [k4 sp (by decide) (by decide) (by decide) (by decide), sp3]
  have sp6 : reg n6 sp = F := by rw [u6.regs, updz u5.self.zero (by decide), u5.regs, updz u4.zero (by decide), sp4]
  obtain ⟨n7, d7, u7⟩ := u6.self.lw hc4 uiz_at_14 (off' := 0x16) (by decide)
    (by rw [sp6]; exact aligned_add hFa (by decide))
  have eslot : memLoad32 n4.mem (F + 0xC) = reg m ra := by
    rw [memLoad32_congr (M := memStore32 m.mem (F + 0xC) (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0) ra))
      fun j hj => f4 _ (by
        rw [show F + 0xC = F + 0xFFFFFFFC + BitVec.ofNat 32 0x10 by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]
        exact sep_offsets _ (c := 0) (n := 4) (d := 0x10 + j) (k := 1) (.inl (by omega)) (by omega) (by omega) |>
          fun h => by rwa [add_ofNat_zero] at h),
      memLoad32_store32_same]
    simp +decide only [upd_app, ↓reduceIte]
  obtain ⟨n8, d8, u8⟩ := u7.self.aluImm hc4 uiz_at_16 (off' := 0x18) (by decide)
  obtain ⟨n9, d9, pc9, mem9, regs9⟩ := u8.self.jalr hc4 uiz_at_18
  have ra8 : reg n8 ra = reg m ra := by
    rw [u8.regs, updz u7.self.zero (by decide), u7.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [sp6]; exact eslot
  refine ⟨n9, .cons d1 (.cons d2 (c3.trans (c4.trans (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.single d9)))))))),
    ?_, ?_, ?_, fun r h0 h1 h2 h3 => ?_, fun x hx => ?_⟩
  · rw [pc9, ra8, add_lit_zero, hra, hret]
  · rw [regs9, u8.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [u7.regs, updz u6.self.zero (by decide), sp6, ev_add]; exact eS
  · rw [regs9, u8.regs, updz u7.self.zero (by decide), u7.regs, updz u6.self.zero (by decide), u6.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [a04']
    by_cases hall : ∀ i : Nat, i < len → memLoad32 m.mem (ptr + BitVec.ofNat 32 (4 * i)) = 0
    · rw [ite_eq_left hall, ite_eq_left hall]; rfl
    · rw [ite_eq_right hall, ite_eq_right hall]; rfl
  · by_cases hs : r = sp
    · subst hs
      rw [regs9, u8.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u7.regs, updz u6.self.zero (by decide), sp6, ev_add, hsp, ← eS]
    by_cases hr : r = ra
    · subst hr; rw [regs9, ra8]
    rw [regs9, u8.regs, updz u7.self.zero hs, u7.regs, updz u6.self.zero hr, u6.regs, updz u5.self.zero h0,
      u5.regs, updz u4.zero h0, k4 r h0 h1 h2 h3, r3 r hr, k2 r hs]
  · rw [mem9, f4 x (sF4 x hx), memStore32_get_sep (sslot x hx)]

theorem split12_out {M : Word → BitVec 8} {out p x : Word} (hx : Sep out 16 x 1) : split12Mem M out p x = M x := by
  simp only [split12Mem]
  rw [memStore32_get_sep (a := out + 0xC) (hx.sub (c := 0xC) (l := 4) (by decide)),
    memStore32_get_sep (a := out + 8) (hx.sub (c := 8) (l := 4) (by decide)),
    memStore32_get_sep (a := out + 4) (hx.sub (c := 4) (l := 4) (by decide)),
    memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)]

theorem split12_ld (M : Word → BitVec 8) (out p : Word) :
    memLoad32 (split12Mem M out p) out = p ∧ memLoad32 (split12Mem M out p) (out + 4) = 12 ∧
    memLoad32 (split12Mem M out p) (out + 8) = p + 0x30 ∧ memLoad32 (split12Mem M out p) (out + 0xC) = 0 := by
  have s : ∀ c d : Nat, c + 4 ≤ d ∨ d + 4 ≤ c → d + 4 ≤ 2 ^ 32 → c + 4 ≤ 2 ^ 32 →
      Sep (out + BitVec.ofNat 32 c) 4 (out + BitVec.ofNat 32 d) 4 := fun c d h h1 h2 =>
    sep_offsets out (c := c) (n := 4) (d := d) (k := 4) h h2 h1
  simp only [split12Mem]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [memLoad32_store32_sep (a := out + 0xC) (b := out) (by have := s 0xC 0 (.inr (by decide)) (by decide) (by decide); rwa [add_ofNat_zero] at this),
      memLoad32_store32_sep (a := out + 8) (b := out) (by have := s 8 0 (.inr (by decide)) (by decide) (by decide); rwa [add_ofNat_zero] at this),
      memLoad32_store32_sep (a := out + 4) (b := out) (by have := s 4 0 (.inr (by decide)) (by decide) (by decide); rwa [add_ofNat_zero] at this),
      memLoad32_store32_same]
  · rw [memLoad32_store32_sep (a := out + 0xC) (b := out + 4) (s 0xC 4 (.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_sep (a := out + 8) (b := out + 4) (s 8 4 (.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_same]
  · rw [memLoad32_store32_sep (a := out + 0xC) (b := out + 8) (s 0xC 8 (.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_same]
  · rw [memLoad32_store32_same]

/-- The registers `Uint<12>::ct_eq` saves, and where in its frame. -/
abbrev ucePs : List (Fin 32 × Word) :=
  [(ra, 0x2C), ((8 : Fin 32), 0x28), ((9 : Fin 32), 0x24), ((18 : Fin 32), 0x20), ((19 : Fin 32), 0x1C),
   ((20 : Fin 32), 0x18), ((21 : Fin 32), 0x14)]

def uceMov1 : List BInstr := [.alu .add (8 : Fin 32) x0 a1, .alu .add a1 x0 a0, .aluImm .add a0 sp 0x4]
def uceLd1 : List BInstr :=
  [.lw (9 : Fin 32) sp 0x4, .lw (18 : Fin 32) sp 0x8, .lw (19 : Fin 32) sp 0xC, .lw (20 : Fin 32) sp 0x10,
   .aluImm .add a0 sp 0x4, .alu .add a1 x0 (8 : Fin 32)]
def uceLd2 : List BInstr :=
  [.lw a2 sp 0x4, .lw a3 sp 0x8, .lw (8 : Fin 32) sp 0xC, .lw (21 : Fin 32) sp 0x10,
   .alu .add a0 x0 (9 : Fin 32), .alu .add a1 x0 (18 : Fin 32)]
def uceMid1 : List BInstr := [.aluImm .and (9 : Fin 32) a0 0xFF, .alu .add a0 x0 (19 : Fin 32), .alu .add a1 x0 (20 : Fin 32)]
def uceMid2 : List BInstr :=
  [.aluImm .and a0 a0 0xFF, .alu .and (9 : Fin 32) (9 : Fin 32) a0, .alu .add a0 x0 (8 : Fin 32),
   .alu .add a1 x0 (21 : Fin 32)]
def uceFin : List BInstr := [.aluImm .and a0 a0 0xFF, .alu .and a0 a0 (9 : Fin 32)]

section
set_option maxRecDepth 20000
theorem uceSave_end : blockEnd uint12CtEqCode 2 (saveBlock ucePs) = some 0x10 := by decide
theorem uceMov1_end : blockEnd uint12CtEqCode 0x10 uceMov1 = some 0x16 := by decide
theorem uceLd1_end : blockEnd uint12CtEqCode 0x1E uceLd1 = some 0x2A := by decide
theorem uceLd2_end : blockEnd uint12CtEqCode 0x32 uceLd2 = some 0x3E := by decide
theorem uceMid1_end : blockEnd uint12CtEqCode 0x46 uceMid1 = some 0x4E := by decide
theorem uceMid2_end : blockEnd uint12CtEqCode 0x56 uceMid2 = some 0x60 := by decide
theorem uceFin_end : blockEnd uint12CtEqCode 0x68 uceFin = some 0x6E := by decide
theorem uceRestore_end : blockEnd uint12CtEqCode 0x6E (restoreBlock ucePs) = some 0x7C := by decide
end

/-- Where `Uint<12>::ct_eq` runs: its code and its callees', its stack region
of 0x44 bytes below `sp0` (its 0x30-byte frame and `is_zero`'s 0x14 below
it), and the operands at `pa` and `pb`, apart from what each must not touch. -/
structure UCEEnv (M : Word → BitVec 8) (P sp0 pa pb : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P uint12CtEqCode
  spl : CodeIn M (P + 0x80) splitAt12Code
  lce : CodeIn M (P + 0xFFFF9DBC) limbCtEqCode
  uiz : CodeIn M (P + 0xFFFEF3C4) uintRefIsZeroCode
  unz : CodeIn M (P + 0xFFFEF3C4 + 0x1A) uintRefIsNonzeroCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x44 ≤ sp0.toNat
  hpa : pa.toNat % 4 = 0
  hpb : pb.toNat % 4 = 0
  sRC : Sep (sp0 + 0xFFFFFFBC) 0x44 P uint12CtEqCode.length
  sRS : Sep (sp0 + 0xFFFFFFBC) 0x44 (P + 0x80) splitAt12Code.length
  sRL : Sep (sp0 + 0xFFFFFFBC) 0x44 (P + 0xFFFF9DBC) limbCtEqCode.length
  sRZ : Sep (sp0 + 0xFFFFFFBC) 0x44 (P + 0xFFFEF3C4) uintRefIsZeroCode.length
  sRN : Sep (sp0 + 0xFFFFFFBC) 0x44 (P + 0xFFFEF3C4 + 0x1A) uintRefIsNonzeroCode.length
  sAR : Sep pa 48 (sp0 + 0xFFFFFFBC) 0x44
  sBR : Sep pb 48 (sp0 + 0xFFFFFFBC) 0x44

/-- A restore leaves the registers it doesn't load. -/
theorem restoreRegs_ne (M : Word → BitVec 8) (G : Word) :
    ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), f 0 = 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs M G f ps q = f q
  | f, [], q, _, _ => rfl
  | f, (r, o) :: ps, q, hz, h => by
    simp only [restoreRegs]
    rw [restoreRegs_ne M G _ ps q (by simp [upd]) (fun p hm => h p (List.mem_cons_of_mem _ hm))]
    exact updz hz (h (r, o) List.mem_cons_self).symm

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `Uint<12>::ct_eq`**: 1 when the 12 limbs at `pa` equal
those at `pb`, and 0 otherwise. It restores `sp`, `ra`, and `s0` through
`s5`, and writes only its 0x44-byte stack region. -/
theorem uint12CtEq_correct (m : Machine) {P sp0 pa pb retAddr : Word} (env : UCEEnv m.mem P sp0 pa pb)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = pa) (ha1 : reg m a1 = pb)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      reg m' a0 = (if ∀ i : Nat, i < 12 → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i)) then 1 else 0) ∧
      (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFBC) 0x44 x 1 → m'.mem x = m.mem x := by
  obtain ⟨R, hR⟩ : ∃ R, sp0 + 0xFFFFFFBC = R := ⟨_, rfl⟩
  have sRC := env.sRC; have sRS := env.sRS; have sRL := env.sRL; have sRZ := env.sRZ; have sRN := env.sRN
  have sAR := env.sAR; have sBR := env.sBR
  rw [hR] at sRC sRS sRL sRZ sRN sAR sBR ⊢
  have hRa : R.toNat % 4 = 0 := by rw [← hR]; exact aligned_add env.hsp (k := 0xFFFFFFBC) (by decide)
  have hRw : R.toNat + 0x44 = sp0.toNat := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFFFBC : Word).toNat = 4294967228 from rfl]
    have := sp0.isLt; have := env.hS; omega
  obtain ⟨F, hF⟩ : ∃ F, R + 0x14 = F := ⟨_, rfl⟩
  have hFsp : sp0 + 0xFFFFFFD0 = F := by rw [← hF, ← hR, BitVec.add_assoc]; rfl
  have eS : F + 0x30 = sp0 := by rw [← hFsp, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hRa (k := 0x14) (by decide)
  -- offsets in the region
  have inR : ∀ {c : Nat}, c < 0x30 → F + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x14 + c) := fun hc => by
    rw [← hF, show (0x14 : Word) = BitVec.ofNat 32 0x14 from rfl, add_ofNat_assoc]
  have sRF : ∀ {b : Word} {k : Nat}, Sep R 0x44 b k → Sep F 0x30 b k := fun h => by
    rw [← hF]; exact h.sub (c := 0x14) (l := 0x30) (by decide)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep R 0x44 b code'.length → (∀ x, Sep R 0x44 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod uce_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hFsp]
  have slotSep : ∀ o : Word, 0x14 ≤ o.toNat → o.toNat + 4 ≤ 0x30 → Sep (F + o) 4 P uint12CtEqCode.length := fun o h1 h2 => by
    have := (sRF sRC).sub (c := o.toNat) (l := 4) (by omega); rwa [ofNat_toNat_self] at this
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock ucePs) u1 env.cod uceSave_end (saveBlock_ok _ ucePs _ fun p hp => by
    rw [sp1]
    simp only [ucePs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨fr_al' hFa (by decide), slotSep _ (by decide) (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) ucePs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep F 0x30 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside ucePs fun p hp => by
      simp only [ucePs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact frm_sep' hx (by decide)
  have hslv : ∀ r o, (r, o) ∈ ucePs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [ucePs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  -- registers no step of the function writes
  have nw : ∀ q : Fin 32, oidKeep q = true → q ≠ ra → q ≠ sp → q.val ∉ [8, 9, 18, 19, 20, 21] → Prop :=
    fun _ _ _ _ _ => True
  have hcS : CodeIn Msv P uint12CtEqCode := cIn env.cod sRC (fun x hx => frSv x (sRF hx))
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs, sp1]
  obtain ⟨m3, c3, u3⟩ := St.block uceMov1 u2.self hcS uceMov1_end (by simp [BlockOk, BInstr.ok, uceMov1])
  simp only [runBlock, BInstr.run, uceMov1] at u3
  have v3 : reg m3 8 = pb ∧ reg m3 a1 = pa ∧ reg m3 a0 = F + 4 ∧ reg m3 sp = F := by
    rw [u3.regs, u3.regs, u3.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [r2 a1 (by decide), r2 a0 (by decide), r2 0 (by decide), hz, ha1, ha0, sp2, ev_add, ev_add, zw, zw]
    exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨v38, v3a1, v3a0, v3sp⟩ := v3
  have k3 : ∀ q, q ≠ 8 → q ≠ a1 → q ≠ a0 → q ≠ sp → reg m3 q = reg m q := fun q h8 h1 h0 hs => by
    rw [u3.regs, updz (by simp [upd]) h0, updz (by simp [upd]) h1, updz u2.self.zero h8, r2 q hs]
  have hSp : CodeIn Msv (P + 0x80) splitAt12Code := cIn env.spl sRS (fun x hx => frSv x (sRF hx))
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hcS uce_at_16 uce_at_1a (cb := P + 0x80)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x80 (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have hF4 : F + 4 = F + BitVec.ofNat 32 4 := rfl
  have sOut : Sep (F + 4) 16 (P + 0x80) splitAt12Code.length := by rw [hF4]; exact (sRF sRS).sub (by decide)
  obtain ⟨m5, c5, pc5, mem5, k5⟩ := splitAt12_correct m4 (out := F + 4) (p := pa) (by rw [mem4]; exact hSp) pc4
    (by rw [r4 a0 (by decide), v3a0]) (by rw [r4 a1 (by decide), v3a1]) (by rw [hF4]; exact aligned_add hFa (by decide))
    sOut (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP 0x1E (by decide)))
  rw [mem4] at mem5
  -- the first split's result
  obtain ⟨l0, l1, l2, l3⟩ := split12_ld Msv (F + 4) pa
  have hc5 : CodeIn (split12Mem Msv (F + 4) pa) P uint12CtEqCode := fun i hi => by
    rw [split12_out (by rw [hF4]; exact ((sRF sRC).subR (c := i) (l := 1) (by omega)).sub (by decide))]
    exact hcS i hi
  have u5 : St (split12Mem Msv (F + 4) pa) P m5 0x1E (reg m5) := ⟨by rw [pc5], mem5, fun _ => rfl⟩
  have K5 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ ra → reg m5 q = reg m3 q := fun q h2 h3 hr => by rw [k5 q h2 h3, r4 q hr]
  have sp5 : reg m5 sp = F := by rw [K5 sp (by decide) (by decide) (by decide), v3sp]
  have hal : ∀ c : Word, c.toNat % 4 = 0 → (reg m5 sp + c).toNat % 4 = 0 := fun c hc => by
    rw [sp5]; exact fr_al' hFa hc
  obtain ⟨m6, c6, u6⟩ := St.block uceLd1 u5 hc5 uceLd1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, uceLd1, upd_app, ↓reduceIte, and_true]
    exact ⟨hal 4 (by decide), hal 8 (by decide), hal 0xC (by decide), hal 0x10 (by decide)⟩)
  simp only [runBlock, BInstr.run, uceLd1] at u6
  have e8 : F + 8 = F + 4 + 4 := by rw [BitVec.add_assoc]; rfl
  have eC : F + 0xC = F + 4 + 8 := by rw [BitVec.add_assoc]; rfl
  have e10 : F + 0x10 = F + 4 + 0xC := by rw [BitVec.add_assoc]; rfl
  have v6 : reg m6 9 = pa ∧ reg m6 18 = 12 ∧ reg m6 19 = pa + 0x30 ∧ reg m6 20 = 0 ∧ reg m6 a0 = F + 4 ∧
      reg m6 a1 = pb ∧ reg m6 sp = F := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5]; exact l0
    · rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5, e8]; exact l1
    · rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5, eC]; exact l2
    · rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5, e10]; exact l3
    · rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5, ev_add]
    · rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [K5 8 (by decide) (by decide) (by decide), v38]
      exact zw pb
    · rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp5
  obtain ⟨v69, v618, v619, v620, v6a0, v6a1, v6sp⟩ := v6
  have k6 : ∀ q, q ≠ 9 → q ≠ 18 → q ≠ 19 → q ≠ 20 → q ≠ a0 → q ≠ a1 → reg m6 q = reg m5 q :=
    fun q h9 h18 h19 h20 h0 h1 => by
      rw [u6.regs]
      by_cases hq0 : q.val = 0
      · have : q = 0 := Fin.ext hq0
        subst this; simp [upd]; exact u5.zero.symm
      simp only [upd_app, hq0, h9, h18, h19, h20, h0, h1, ite_false]
  have hSp5 : CodeIn (split12Mem Msv (F + 4) pa) (P + 0x80) splitAt12Code := fun i hi => by
    rw [split12_out (by rw [hF4]; exact ((sRF sRS).subR (c := i) (l := 1) (by omega)).sub (by decide))]
    exact hSp i hi
  obtain ⟨m7, c7, pc7, mem7, regs7⟩ := u6.self.callRa hc5 uce_at_2a uce_at_2e (cb := P + 0x80)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x80 (by decide))
  have r7 := PEnv.reg1 regs7 u6.self.zero
  obtain ⟨m8, c8, pc8, mem8, k8⟩ := splitAt12_correct m7 (out := F + 4) (p := pb) (by rw [mem7]; exact hSp5) pc7
    (by rw [r7 a0 (by decide), v6a0]) (by rw [r7 a1 (by decide), v6a1]) (by rw [hF4]; exact aligned_add hFa (by decide))
    sOut (by rw [regs7]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP 0x32 (by decide)))
  rw [mem7] at mem8
  obtain ⟨l0', l1', l2', l3'⟩ := split12_ld (split12Mem Msv (F + 4) pa) (F + 4) pb
  have outF4 : ∀ x, Sep R 0x44 x 1 → Sep (F + 4) 16 x 1 := fun x hx => by
    rw [hF4]; exact (sRF hx).sub (by decide)
  have M2out : ∀ x, Sep R 0x44 x 1 → split12Mem (split12Mem Msv (F + 4) pa) (F + 4) pb x = m.mem x := fun x hx => by
    rw [split12_out (outF4 x hx), split12_out (outF4 x hx), frSv x (sRF hx)]
  obtain ⟨M2, hM2⟩ : ∃ M2, split12Mem (split12Mem Msv (F + 4) pa) (F + 4) pb = M2 := ⟨_, rfl⟩
  rw [hM2] at mem8 l0' l1' l2' l3' M2out
  have hc8 : CodeIn M2 P uint12CtEqCode := fun i hi => by rw [M2out _ (sRC.subR (c := i) (l := 1) (by omega))]; exact env.cod i hi
  have u8 : St M2 P m8 0x32 (reg m8) := ⟨by rw [pc8], mem8, fun _ => rfl⟩
  have K8 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ ra → reg m8 q = reg m6 q := fun q h2 h3 hr => by rw [k8 q h2 h3, r7 q hr]
  have sp8 : reg m8 sp = F := by rw [K8 sp (by decide) (by decide) (by decide), v6sp]
  have hal8 : ∀ c : Word, c.toNat % 4 = 0 → (reg m8 sp + c).toNat % 4 = 0 := fun c hc => by
    rw [sp8]; exact fr_al' hFa hc
  obtain ⟨m9, c9, u9⟩ := St.block uceLd2 u8 hc8 uceLd2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, uceLd2, upd_app, ↓reduceIte, and_true]
    exact ⟨hal8 4 (by decide), hal8 8 (by decide), hal8 0xC (by decide), hal8 0x10 (by decide)⟩)
  simp only [runBlock, BInstr.run, uceLd2] at u9
  have v9 : reg m9 a2 = pb ∧ reg m9 a3 = 12 ∧ reg m9 8 = pb + 0x30 ∧ reg m9 21 = 0 ∧ reg m9 a0 = pa ∧
      reg m9 a1 = 12 ∧ reg m9 sp = F ∧ reg m9 19 = pa + 0x30 ∧ reg m9 20 = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp8]; exact l0'
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp8, e8]; exact l1'
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp8, eC]; exact l2'
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp8, e10]; exact l3'
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [K8 9 (by decide) (by decide) (by decide), v69]; exact zw pa
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [K8 18 (by decide) (by decide) (by decide), v618]; exact zw _
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp8
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [K8 19 (by decide) (by decide) (by decide), v619]
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [K8 20 (by decide) (by decide) (by decide), v620]
  obtain ⟨v9a2, v9a3, v98, v921, v9a0, v9a1, v9sp, v919, v920⟩ := v9
  have k9 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ 8 → q ≠ 21 → q ≠ a0 → q ≠ a1 → reg m9 q = reg m8 q :=
    fun q h2 h3 h8 h21 h0 h1 => by
      rw [u9.regs]
      by_cases hq0 : q.val = 0
      · have : q = 0 := Fin.ext hq0
        subst this; simp [upd]; exact u8.zero.symm
      simp only [upd_app, hq0, h2, h3, h8, h21, h0, h1, ite_false]
  -- the limbs compared
  have hLc : CodeIn M2 (P + 0xFFFF9DBC) limbCtEqCode := fun i hi => by
    rw [M2out _ (sRL.subR (c := i) (l := 1) (by omega))]; exact env.lce i hi
  obtain ⟨m10, c10, pc10, mem10, regs10⟩ := u9.self.callRa hc8 uce_at_3e uce_at_42 (cb := P + 0xFFFF9DBC)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFF9DBC (by decide))
  have r10 := PEnv.reg1 regs10 u9.self.zero
  obtain ⟨m11, c11, pc11, a011, k11, mem11⟩ := limbCtEq_correct m10 (p := pa) (q := pb) (n := 12) (n' := 12)
    (retAddr := P + BitVec.ofNat 32 0x46) (even_at P env.hP 0xFFFF9DBC (by decide)) (by rw [mem10]; exact hLc) pc10
    (by rw [r10 a0 (by decide), v9a0]) (by rw [r10 a1 (by decide), v9a1]; rfl) (by rw [r10 a2 (by decide), v9a2])
    (by rw [r10 a3 (by decide), v9a3]; rfl) (by decide) (by decide) env.hpa env.hpb
    (by rw [regs10]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP 0x46 (by decide)))
  rw [mem10] at mem11 a011
  have eLim : ∀ b : Word, Sep b 48 R 0x44 → ∀ i : Nat, i < 12 →
      memLoad32 M2 (b + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (b + BitVec.ofNat 32 (4 * i)) :=
    fun b hb i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact M2out _ (hb.symm.subR (c := 4 * i + j) (l := 1) (by omega))
  have a011' : reg m11 a0 = if ∀ i : Nat, i < 12 → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
      memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i)) then 1 else 0 := by
    rw [a011]
    by_cases h : ∀ i : Nat, i < 12 → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
      memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i))
    · rw [ite_eq_left (show 12 = 12 ∧ ∀ i : Nat, i < 12 → memLoad32 M2 (pa + BitVec.ofNat 32 (4 * i)) =
        memLoad32 M2 (pb + BitVec.ofNat 32 (4 * i)) from ⟨rfl, fun i hi => by rw [eLim pa sAR i hi, eLim pb sBR i hi]; exact h i hi⟩),
        ite_eq_left h]
    · rw [ite_eq_right (show ¬ (12 = 12 ∧ ∀ i : Nat, i < 12 → memLoad32 M2 (pa + BitVec.ofNat 32 (4 * i)) =
        memLoad32 M2 (pb + BitVec.ofNat 32 (4 * i))) from fun hh => h (fun i hi => by
          rw [← eLim pa sAR i hi, ← eLim pb sBR i hi]; exact hh.2 i hi)), ite_eq_right h]
  have rIs : ∀ c : Nat, (if ∀ i : Nat, i < c → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
      memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i)) then (1 : Word) else 0).toNat ≤ 1 := fun c => by
    split <;> decide
  -- the saved registers' slots, above `is_zero`'s 0x14 bytes
  have slot : ∀ {Mx : Word → BitVec 8}, (∀ x, Sep R 0x14 x 1 → Mx x = M2 x) →
      ∀ r o, (r, o) ∈ ucePs → memLoad32 Mx (F + o) = reg m r := fun {Mx} hMx r o h => by
    have ho : 0x14 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x30 := by
      simp only [ucePs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    have e : F + o + BitVec.ofNat 32 j = R + BitVec.ofNat 32 (0x14 + o.toNat + j) := by
      conv => lhs; rw [← ofNat_toNat_self o]
      rw [← hF, show (0x14 : Word) = BitVec.ofNat 32 0x14 from rfl, add_ofNat_assoc, add_ofNat_assoc, Nat.add_assoc]
    have e2 : F + o + BitVec.ofNat 32 j = F + 4 + BitVec.ofNat 32 (o.toNat + j - 4) := by
      conv => lhs; rw [← ofNat_toNat_self o]
      rw [hF4, add_ofNat_assoc, add_ofNat_assoc, show 4 + (o.toNat + j - 4) = o.toNat + j by omega]
    have sR : Sep R 0x14 (F + o + BitVec.ofNat 32 j) 1 := by
      have := sep_offsets R (c := 0) (n := 0x14) (d := 0x14 + o.toNat + j) (k := 1) (.inl (by omega)) (by omega)
        (by omega)
      rw [add_ofNat_zero] at this; rw [e]; exact this
    have sS : Sep (F + 4) 16 (F + o + BitVec.ofNat 32 j) 1 := by
      have := sep_offsets (F + 4) (c := 0) (n := 16) (d := o.toNat + j - 4) (k := 1) (.inl (by omega)) (by omega)
        (by omega)
      rw [add_ofNat_zero] at this; rw [e2]; exact this
    rw [hMx _ sR, ← hM2, split12_out sS, split12_out sS]
  have sp11 : reg m11 sp = F := by
    rw [k11 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r10 sp (by decide),
      k9 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp8]
  have u11 : St M2 P m11 0x46 (reg m11) := ⟨by rw [pc11], mem11, fun _ => rfl⟩
  have R11 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ ra → q ≠ 8 → q ≠ 21 →
      reg m11 q = reg m8 q := fun q h0 h1 h2 h3 h4 h5 hr h8 h21 => by
    rw [k11 q h0 h1 h2 h3 h4 h5, r10 q hr, k9 q h2 h3 h8 h21 h0 h1]
  obtain ⟨m12, c12, u12⟩ := St.block uceMid1 u11 hc8 uceMid1_end (by simp [BlockOk, BInstr.ok, uceMid1])
  simp only [runBlock, BInstr.run, uceMid1] at u12
  have and_ff : ∀ c : Nat, (if c = 0 then (1 : Word) else 0) = aluEval .and (if c = 0 then (1 : Word) else 0) 0xFF :=
    fun c => by split <;> rfl
  have hZ : CodeIn M2 (P + 0xFFFEF3C4) uintRefIsZeroCode := fun i hi => by
    rw [M2out _ (sRZ.subR (c := i) (l := 1) (by omega))]; exact env.uiz i hi
  have hN : CodeIn M2 (P + 0xFFFEF3C4 + 0x1A) uintRefIsNonzeroCode := fun i hi => by
    rw [M2out _ (sRN.subR (c := i) (l := 1) (by omega))]; exact env.unz i hi
  have eR : F + 0xFFFFFFEC = R := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero R
  have sZ0 : Sep R 0x14 (P + 0xFFFEF3C4) uintRefIsZeroCode.length := by
    have := sRZ.sub (c := 0) (l := 0x14) (by decide); rwa [add_ofNat_zero] at this
  have sN0 : Sep R 0x14 (P + 0xFFFEF3C4 + 0x1A) uintRefIsNonzeroCode.length := by
    have := sRN.sub (c := 0) (l := 0x14) (by decide); rwa [add_ofNat_zero] at this
  have v12 : reg m12 9 = aluEval .and (reg m11 a0) 0xFF ∧ reg m12 a0 = pa + 0x30 ∧ reg m12 a1 = 0 ∧ reg m12 sp = F := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [u12.regs] <;> simp +decide only [upd_app, ↓reduceIte]
    · rw [R11 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        K8 19 (by decide) (by decide) (by decide), v619]; exact zw _
    · rw [R11 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        K8 20 (by decide) (by decide) (by decide), v620]; rfl
    · exact sp11
  obtain ⟨v129, v12a0, v12a1, v12sp⟩ := v12
  obtain ⟨m13, c13, pc13, mem13, regs13⟩ := u12.self.callRa hc8 uce_at_4e uce_at_52 (cb := P + 0xFFFEF3C4)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFEF3C4 (by decide))
  have r13 := PEnv.reg1 regs13 u12.self.zero
  obtain ⟨m14, c14, pc14, sp14, a014, k14, f14⟩ := uintRefIsZero_correct m13 (ptr := pa + 0x30) (len := 0) (sp0 := F)
    (retAddr := P + BitVec.ofNat 32 0x56) (even_at P env.hP 0xFFFEF3C4 (by decide)) (by rw [mem13]; exact hZ)
    (by rw [mem13]; exact hN) pc13 (by rw [r13 sp (by decide), v12sp]) hFa
    (by rw [r13 a0 (by decide), v12a0]) (by rw [r13 a1 (by decide), v12a1]; rfl) (by decide)
    (aligned_add env.hpa (by decide)) (by rw [eR]; exact sZ0) (by rw [eR]; exact sN0)
    (fun i hi => absurd hi (by omega)) (by rw [regs13]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP 0x56 (by decide)))
  rw [mem13, eR] at f14
  have sub14 : ∀ {b : Word} {k : Nat}, Sep R 0x44 b k → Sep R 0x14 b k := fun h => by
    have := h.sub (c := 0) (l := 0x14) (by decide); rwa [add_ofNat_zero] at this
  have hc14 : CodeIn m14.mem P uint12CtEqCode := fun i hi => by
    rw [f14 _ (sub14 (sRC.subR (c := i) (l := 1) (by omega)))]
    exact hc8 i hi
  have u14 : St m14.mem P m14 0x56 (reg m14) := ⟨by rw [pc14], rfl, fun _ => rfl⟩
  have R14 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → reg m14 q = reg m12 q := fun q h0 h1 h2 h3 hr => by
    rw [k14 q h0 h1 h2 h3, r13 q hr]
  obtain ⟨m15, c15, u15⟩ := St.block uceMid2 u14 hc14 uceMid2_end (by simp [BlockOk, BInstr.ok, uceMid2])
  simp only [runBlock, BInstr.run, uceMid2] at u15
  have r12 : ∀ q, q ≠ 9 → q ≠ a0 → q ≠ a1 → reg m12 q = reg m11 q := fun q h9 h0 h1 => by
    rw [u12.regs]
    by_cases hq0 : q.val = 0
    · have : q = 0 := Fin.ext hq0
      subst this; simp [upd]; exact u11.zero.symm
    simp only [upd_app, hq0, h9, h0, h1, ite_false]
  have v15 : reg m15 9 = aluEval .and (aluEval .and (reg m11 a0) 0xFF) (aluEval .and 1 0xFF) ∧
      reg m15 a0 = pb + 0x30 ∧ reg m15 a1 = 0 ∧ reg m15 sp = F := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [u15.regs] <;> simp +decide only [upd_app, ↓reduceIte]
    · rw [R14 9 (by decide) (by decide) (by decide) (by decide) (by decide), v129, a014]
      rw [ite_eq_left (fun i hi => absurd hi (Nat.not_lt_zero i))]
    · rw [R14 8 (by decide) (by decide) (by decide) (by decide) (by decide), r12 8 (by decide) (by decide) (by decide),
        k11 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r10 8 (by decide), v98]
      exact zw _
    · rw [R14 21 (by decide) (by decide) (by decide) (by decide) (by decide), r12 21 (by decide) (by decide) (by decide),
        k11 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r10 21 (by decide), v921]; rfl
    · rw [R14 sp (by decide) (by decide) (by decide) (by decide) (by decide), v12sp]
  obtain ⟨v159, v15a0, v15a1, v15sp⟩ := v15
  have r15 : ∀ q, q ≠ 9 → q ≠ a0 → q ≠ a1 → reg m15 q = reg m14 q := fun q h9 h0 h1 => by
    rw [u15.regs]
    by_cases hq0 : q.val = 0
    · have : q = 0 := Fin.ext hq0
      subst this; simp [upd]; exact u14.zero.symm
    simp only [upd_app, hq0, h9, h0, h1, ite_false]
  have hZ14 : CodeIn m14.mem (P + 0xFFFEF3C4) uintRefIsZeroCode := fun i hi => by
    rw [f14 _ (sub14 (sRZ.subR (c := i) (l := 1) (by omega)))]; exact hZ i hi
  have hN14 : CodeIn m14.mem (P + 0xFFFEF3C4 + 0x1A) uintRefIsNonzeroCode := fun i hi => by
    rw [f14 _ (sub14 (sRN.subR (c := i) (l := 1) (by omega)))]; exact hN i hi
  obtain ⟨m16, c16, pc16, mem16, regs16⟩ := u15.self.callRa hc14 uce_at_60 uce_at_64 (cb := P + 0xFFFEF3C4)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFEF3C4 (by decide))
  have r16 := PEnv.reg1 regs16 u15.self.zero
  obtain ⟨m17, c17, pc17, sp17, a017, k17, f17⟩ := uintRefIsZero_correct m16 (ptr := pb + 0x30) (len := 0) (sp0 := F)
    (retAddr := P + BitVec.ofNat 32 0x68) (even_at P env.hP 0xFFFEF3C4 (by decide)) (by rw [mem16]; exact hZ14)
    (by rw [mem16]; exact hN14) pc16 (by rw [r16 sp (by decide), v15sp]) hFa
    (by rw [r16 a0 (by decide), v15a0]) (by rw [r16 a1 (by decide), v15a1]; rfl) (by decide)
    (aligned_add env.hpb (by decide)) (by rw [eR]; exact sZ0) (by rw [eR]; exact sN0)
    (fun i hi => absurd hi (by omega)) (by rw [regs16]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP 0x68 (by decide)))
  rw [mem16, eR] at f17
  -- memory after the second call agrees with `M2` outside `is_zero`'s bytes
  have f17' : ∀ x, Sep R 0x14 x 1 → m17.mem x = M2 x := fun x hx => by rw [f17 x hx, f14 x hx]
  have hc17 : CodeIn m17.mem P uint12CtEqCode := fun i hi => by
    rw [f17' _ (sub14 (sRC.subR (c := i) (l := 1) (by omega)))]; exact hc8 i hi
  have u17 : St m17.mem P m17 0x68 (reg m17) := ⟨by rw [pc17], rfl, fun _ => rfl⟩
  obtain ⟨m18, c18, u18⟩ := St.block uceFin u17 hc17 uceFin_end (by simp [BlockOk, BInstr.ok, uceFin])
  simp only [runBlock, BInstr.run, uceFin] at u18
  have R17 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → reg m17 q = reg m15 q := fun q h0 h1 h2 h3 hr => by
    rw [k17 q h0 h1 h2 h3, r16 q hr]
  have sp18 : reg m18 sp = F := by
    rw [u18.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [R17 sp (by decide) (by decide) (by decide) (by decide) (by decide), v15sp]
  have va18 : reg m18 a0 = if ∀ i : Nat, i < 12 → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
      memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i)) then 1 else 0 := by
    rw [u18.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [a017, ite_eq_left (fun i hi => absurd hi (Nat.not_lt_zero i)),
      R17 9 (by decide) (by decide) (by decide) (by decide) (by decide), v159, a011']
    split <;> rfl
  obtain ⟨m19, c19, u19⟩ := St.block (restoreBlock ucePs) u18.self hc17 uceRestore_end
    (restoreBlock_ok _ F ucePs (reg m18) sp18 (by decide) fun p hp => by
      simp only [ucePs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact fr_al' hFa (by decide))
  simp only [restoreBlock_run m17.mem F ucePs (reg m18) sp18 (by decide)] at u19
  obtain ⟨m20, d20, u20⟩ := u19.aluImm hc17 uce_at_7c (off' := 0x7E) (by decide)
  obtain ⟨m21, d21, pc21, mem21, regs21⟩ := u20.jalr hc17 uce_at_7e
  have hsl := slot f17'
  have rsp19 : restoreRegs m17.mem F (reg m18) ucePs sp = F := by
    rw [restoreRegs_sp _ _ _ _ (by decide)]; exact sp18
  refine ⟨m21, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (c11.trans (c12.trans (c13.trans (c14.trans (c15.trans (c16.trans (c17.trans (c18.trans (c19.trans
    (.cons d20 (.single d21)))))))))))))))))))), ?_, ?_, ?_, fun q hq => ?_, fun x hx => ?_⟩
  · rw [pc21]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [hsl ra 0x2C (by decide), hra, add_lit_zero, hret]
  · rw [regs21]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp19, ev_add, eS]
  · rw [regs21]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]; exact va18
  · by_cases hs : q = sp
    · subst hs; rw [regs21]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp19, ev_add, eS, hsp]
    have rz : restoreRegs m17.mem F (reg m18) ucePs 0 = 0 := by
      rw [restoreRegs_ne _ _ _ _ _ u18.self.zero (by decide)]; exact u18.self.zero
    by_cases hin : q.val ∈ [1, 8, 9, 18, 19, 20, 21]
    · have h7 : q = ra ∨ q = 8 ∨ q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 20 ∨ q = 21 := by revert hin; revert q; decide
      rcases h7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · rw [regs21]; simp +decide only [upd_app, ↓reduceIte]
        simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
        first
          | exact hsl _ 0x2C (by decide) | exact hsl _ 0x28 (by decide) | exact hsl _ 0x24 (by decide)
          | exact hsl _ 0x20 (by decide) | exact hsl _ 0x1C (by decide) | exact hsl _ 0x18 (by decide)
          | exact hsl _ 0x14 (by decide)
    have key : ∀ q : Fin 32, oidKeep q = true → q.val ∉ [1, 8, 9, 18, 19, 20, 21] → q ≠ sp →
        ∀ r : Fin 32, r.val ∈ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21] → q ≠ r := by
      decide
    have nq := key q hq hin hs
    rw [regs21, updz rz hs, restoreRegs_ne _ _ _ _ _ u18.self.zero (fun p hp => by
      simp only [ucePs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (nq _ (by decide)).symm)]
    rw [u18.regs, updz (by simp [upd]) (nq a0 (by decide)), updz u17.zero (nq a0 (by decide)), R17 q (nq a0 (by decide)) (nq a1 (by decide)) (nq a2 (by decide))
      (nq a3 (by decide)) (nq ra (by decide)), r15 q (nq 9 (by decide)) (nq a0 (by decide)) (nq a1 (by decide)),
      R14 q (nq a0 (by decide)) (nq a1 (by decide)) (nq a2 (by decide)) (nq a3 (by decide)) (nq ra (by decide)),
      r12 q (nq 9 (by decide)) (nq a0 (by decide)) (nq a1 (by decide)),
      R11 q (nq a0 (by decide)) (nq a1 (by decide)) (nq a2 (by decide)) (nq a3 (by decide)) (nq a4 (by decide))
        (nq a5 (by decide)) (nq ra (by decide)) (nq 8 (by decide)) (nq 21 (by decide)),
      K8 q (nq a2 (by decide)) (nq a3 (by decide)) (nq ra (by decide)),
      k6 q (nq 9 (by decide)) (nq 18 (by decide)) (nq 19 (by decide)) (nq 20 (by decide)) (nq a0 (by decide))
        (nq a1 (by decide)),
      K5 q (nq a2 (by decide)) (nq a3 (by decide)) (nq ra (by decide)),
      k3 q (nq 8 (by decide)) (nq a1 (by decide)) (nq a0 (by decide)) hs]
  · rw [mem21, f17' x (sub14 hx), M2out x hx]

end C3.RV32
