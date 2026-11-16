import C3BootProofs.Proofs.P384FromRepr
import C3BootProofs.Proofs.LincombShiftMod12

/-!
# `fill_limbs_from_be_slice_truncated`, as compiled

`crypto_bigint`'s big-endian decoder keeps the last `⌈bits / 8⌉` bytes of its
input and fills limb `k` from the up to four bytes that end `4 k` bytes before
the input's end: it zeroes a stack word, copies the bytes into its low end,
loads the word, and swaps its bytes. These theorems cover precisions that are
a multiple of 32 bits and fit the limbs, the only ones the image passes.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem fl_at_0 : fetchRel fillLimbsBeTruncCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem fl_at_2 : fetchRel fillLimbsBeTruncCode 0x2 = some (.store .sw sp (8 : Fin 32) 0x1C, 2) := by decide
theorem fl_at_4 : fetchRel fillLimbsBeTruncCode 0x4 = some (.store .sw sp (9 : Fin 32) 0x18, 2) := by decide
theorem fl_at_6 : fetchRel fillLimbsBeTruncCode 0x6 = some (.store .sw sp (18 : Fin 32) 0x14, 2) := by decide
theorem fl_at_8 : fetchRel fillLimbsBeTruncCode 0x8 = some (.store .sw sp (19 : Fin 32) 0x10, 2) := by decide
theorem fl_at_a : fetchRel fillLimbsBeTruncCode 0xA = some (.aluImm .sll a5 a3 0x5, 4) := by decide
theorem fl_at_e : fetchRel fillLimbsBeTruncCode 0xE = some (.branch .bgeu a5 a4 0x8, 4) := by decide
theorem fl_at_12 : fetchRel fillLimbsBeTruncCode 0x12 = some (.aluImm .add a0 x0 0x3, 2) := by decide
theorem fl_at_14 : fetchRel fillLimbsBeTruncCode 0x14 = some (.jal x0 0xE4, 2) := by decide
theorem fl_at_16 : fetchRel fillLimbsBeTruncCode 0x16 = some (.aluImm .and a5 a4 0x7, 4) := by decide
theorem fl_at_1a : fetchRel fillLimbsBeTruncCode 0x1A = some (.aluImm .add a5 a5 0x7, 2) := by decide
theorem fl_at_1c : fetchRel fillLimbsBeTruncCode 0x1C = some (.aluImm .srl (9 : Fin 32) a4 0x3, 4) := by decide
theorem fl_at_20 : fetchRel fillLimbsBeTruncCode 0x20 = some (.aluImm .srl a5 a5 0x3, 2) := by decide
theorem fl_at_22 : fetchRel fillLimbsBeTruncCode 0x22 = some (.alu .add a5 a5 (9 : Fin 32), 2) := by decide
theorem fl_at_24 : fetchRel fillLimbsBeTruncCode 0x24 = some (.alu .add a6 x0 a1, 2) := by decide
theorem fl_at_26 : fetchRel fillLimbsBeTruncCode 0x26 = some (.branch .bltu a1 a5 0x6, 4) := by decide
theorem fl_at_2a : fetchRel fillLimbsBeTruncCode 0x2A = some (.alu .add a6 x0 a5, 2) := by decide
theorem fl_at_2c : fetchRel fillLimbsBeTruncCode 0x2C = some (.aluImm .add a5 a6 0x3, 4) := by decide
theorem fl_at_30 : fetchRel fillLimbsBeTruncCode 0x30 = some (.aluImm .srl a5 a5 0x2, 2) := by decide
theorem fl_at_32 : fetchRel fillLimbsBeTruncCode 0x32 = some (.aluImm .sltu (8 : Fin 32) a6 0x1, 4) := by decide
theorem fl_at_36 : fetchRel fillLimbsBeTruncCode 0x36 = some (.alu .add (9 : Fin 32) x0 a3, 2) := by decide
theorem fl_at_38 : fetchRel fillLimbsBeTruncCode 0x38 = some (.branch .bltu a3 a5 0x6, 4) := by decide
theorem fl_at_3c : fetchRel fillLimbsBeTruncCode 0x3C = some (.alu .add (9 : Fin 32) x0 a5, 2) := by decide
theorem fl_at_3e : fetchRel fillLimbsBeTruncCode 0x3E = some (.aluImm .add (28 : Fin 32) x0 0x0, 2) := by decide
theorem fl_at_40 : fetchRel fillLimbsBeTruncCode 0x40 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem fl_at_42 : fetchRel fillLimbsBeTruncCode 0x42 = some (.alu .add a1 a1 a0, 2) := by decide
theorem fl_at_44 : fetchRel fillLimbsBeTruncCode 0x44 = some (.alu .and (17 : Fin 32) (8 : Fin 32) (9 : Fin 32), 4) := by decide
theorem fl_at_48 : fetchRel fillLimbsBeTruncCode 0x48 = some (.aluImm .add (5 : Fin 32) x0 0x4, 2) := by decide
theorem fl_at_4a : fetchRel fillLimbsBeTruncCode 0x4A = some (.aluImm .add (6 : Fin 32) x0 0x5, 2) := by decide
theorem fl_at_4c : fetchRel fillLimbsBeTruncCode 0x4C = some (.lui (7 : Fin 32) 0x10000, 2) := by decide
theorem fl_at_4e : fetchRel fillLimbsBeTruncCode 0x4E = some (.aluImm .add (7 : Fin 32) (7 : Fin 32) 0xFFFFFF00, 4) := by decide
theorem fl_at_52 : fetchRel fillLimbsBeTruncCode 0x52 = some (.aluImm .add (29 : Fin 32) x0 0x3, 2) := by decide
theorem fl_at_54 : fetchRel fillLimbsBeTruncCode 0x54 = some (.aluImm .add (19 : Fin 32) sp 0xC, 4) := by decide
theorem fl_at_58 : fetchRel fillLimbsBeTruncCode 0x58 = some (.alu .add (30 : Fin 32) x0 a6, 2) := by decide
theorem fl_at_5a : fetchRel fillLimbsBeTruncCode 0x5A = some (.alu .add a0 x0 (30 : Fin 32), 2) := by decide
theorem fl_at_5c : fetchRel fillLimbsBeTruncCode 0x5C = some (.branch .bltu (30 : Fin 32) (5 : Fin 32) 0x6, 4) := by decide
theorem fl_at_60 : fetchRel fillLimbsBeTruncCode 0x60 = some (.aluImm .add a0 x0 0x4, 2) := by decide
theorem fl_at_62 : fetchRel fillLimbsBeTruncCode 0x62 = some (.branch .beq (28 : Fin 32) (17 : Fin 32) 0x72, 4) := by decide
theorem fl_at_66 : fetchRel fillLimbsBeTruncCode 0x66 = some (.aluImm .sll (31 : Fin 32) (28 : Fin 32) 0x2, 4) := by decide
theorem fl_at_6a : fetchRel fillLimbsBeTruncCode 0x6A = some (.alu .sub (8 : Fin 32) a6 (31 : Fin 32), 4) := by decide
theorem fl_at_6e : fetchRel fillLimbsBeTruncCode 0x6E = some (.aluImm .add (18 : Fin 32) (8 : Fin 32) 0xFFFFFFFC, 4) := by decide
theorem fl_at_72 : fetchRel fillLimbsBeTruncCode 0x72 = some (.alu .sltu (9 : Fin 32) (8 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fl_at_76 : fetchRel fillLimbsBeTruncCode 0x76 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem fl_at_78 : fetchRel fillLimbsBeTruncCode 0x78 = some (.alu .and (9 : Fin 32) (9 : Fin 32) (18 : Fin 32), 4) := by decide
theorem fl_at_7c : fetchRel fillLimbsBeTruncCode 0x7C = some (.alu .sub (9 : Fin 32) (8 : Fin 32) (9 : Fin 32), 4) := by decide
theorem fl_at_80 : fetchRel fillLimbsBeTruncCode 0x80 = some (.branch .bgeu (9 : Fin 32) (6 : Fin 32) 0x84, 4) := by decide
theorem fl_at_84 : fetchRel fillLimbsBeTruncCode 0x84 = some (.alu .sub (8 : Fin 32) x0 a0, 4) := by decide
theorem fl_at_88 : fetchRel fillLimbsBeTruncCode 0x88 = some (.alu .add (31 : Fin 32) (31 : Fin 32) a2, 2) := by decide
theorem fl_at_8a : fetchRel fillLimbsBeTruncCode 0x8A = some (.aluImm .add (28 : Fin 32) (28 : Fin 32) 0x1, 2) := by decide
theorem fl_at_8c : fetchRel fillLimbsBeTruncCode 0x8C = some (.alu .sub a0 (5 : Fin 32) (9 : Fin 32), 4) := by decide
theorem fl_at_90 : fetchRel fillLimbsBeTruncCode 0x90 = some (.store .sw sp x0 0xC, 2) := by decide
theorem fl_at_92 : fetchRel fillLimbsBeTruncCode 0x92 = some (.branch .beq (8 : Fin 32) x0 0x1C, 2) := by decide
theorem fl_at_94 : fetchRel fillLimbsBeTruncCode 0x94 = some (.branch .bltu (29 : Fin 32) a0 0x7C, 4) := by decide
theorem fl_at_98 : fetchRel fillLimbsBeTruncCode 0x98 = some (.alu .add (9 : Fin 32) a1 (8 : Fin 32), 4) := by decide
theorem fl_at_9c : fetchRel fillLimbsBeTruncCode 0x9C = some (.load .lbu (9 : Fin 32) (9 : Fin 32) 0x0, 4) := by decide
theorem fl_at_a0 : fetchRel fillLimbsBeTruncCode 0xA0 = some (.alu .add a5 (19 : Fin 32) a0, 4) := by decide
theorem fl_at_a4 : fetchRel fillLimbsBeTruncCode 0xA4 = some (.store .sb a5 (9 : Fin 32) 0x0, 4) := by decide
theorem fl_at_a8 : fetchRel fillLimbsBeTruncCode 0xA8 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem fl_at_aa : fetchRel fillLimbsBeTruncCode 0xAA = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x1, 2) := by decide
theorem fl_at_ac : fetchRel fillLimbsBeTruncCode 0xAC = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE8, 2) := by decide
theorem fl_at_ae : fetchRel fillLimbsBeTruncCode 0xAE = some (.load .lw a0 sp 0xC, 2) := by decide
theorem fl_at_b0 : fetchRel fillLimbsBeTruncCode 0xB0 = some (.aluImm .srl a5 a0 0x8, 4) := by decide
theorem fl_at_b4 : fetchRel fillLimbsBeTruncCode 0xB4 = some (.aluImm .srl (8 : Fin 32) a0 0x18, 4) := by decide
theorem fl_at_b8 : fetchRel fillLimbsBeTruncCode 0xB8 = some (.alu .and (9 : Fin 32) a0 (7 : Fin 32), 4) := by decide
theorem fl_at_bc : fetchRel fillLimbsBeTruncCode 0xBC = some (.aluImm .sll a0 a0 0x18, 2) := by decide
theorem fl_at_be : fetchRel fillLimbsBeTruncCode 0xBE = some (.alu .and a5 a5 (7 : Fin 32), 4) := by decide
theorem fl_at_c2 : fetchRel fillLimbsBeTruncCode 0xC2 = some (.aluImm .sll (9 : Fin 32) (9 : Fin 32) 0x8, 2) := by decide
theorem fl_at_c4 : fetchRel fillLimbsBeTruncCode 0xC4 = some (.alu .or a5 a5 (8 : Fin 32), 2) := by decide
theorem fl_at_c6 : fetchRel fillLimbsBeTruncCode 0xC6 = some (.alu .or a0 a0 (9 : Fin 32), 2) := by decide
theorem fl_at_c8 : fetchRel fillLimbsBeTruncCode 0xC8 = some (.alu .or a0 a0 a5, 2) := by decide
theorem fl_at_ca : fetchRel fillLimbsBeTruncCode 0xCA = some (.store .sw (31 : Fin 32) a0 0x0, 4) := by decide
theorem fl_at_ce : fetchRel fillLimbsBeTruncCode 0xCE = some (.aluImm .add a1 a1 0xFFFFFFFC, 2) := by decide
theorem fl_at_d0 : fetchRel fillLimbsBeTruncCode 0xD0 = some (.aluImm .add (30 : Fin 32) (30 : Fin 32) 0xFFFFFFFC, 2) := by decide
theorem fl_at_d2 : fetchRel fillLimbsBeTruncCode 0xD2 = some (.jal x0 0xFFFFFF88, 2) := by decide
theorem fl_at_d4 : fetchRel fillLimbsBeTruncCode 0xD4 = some (.aluImm .and a1 a4 0x1F, 4) := by decide
theorem fl_at_d8 : fetchRel fillLimbsBeTruncCode 0xD8 = some (.aluImm .add a0 x0 0xFF, 4) := by decide
theorem fl_at_dc : fetchRel fillLimbsBeTruncCode 0xDC = some (.branch .beq a1 x0 0x1C, 2) := by decide
theorem fl_at_de : fetchRel fillLimbsBeTruncCode 0xDE = some (.aluImm .srl a4 a4 0x5, 2) := by decide
theorem fl_at_e0 : fetchRel fillLimbsBeTruncCode 0xE0 = some (.branch .bgeu a4 a3 0x3A, 4) := by decide
theorem fl_at_e4 : fetchRel fillLimbsBeTruncCode 0xE4 = some (.aluImm .sll a4 a4 0x2, 2) := by decide
theorem fl_at_e6 : fetchRel fillLimbsBeTruncCode 0xE6 = some (.alu .add a2 a2 a4, 2) := by decide
theorem fl_at_e8 : fetchRel fillLimbsBeTruncCode 0xE8 = some (.load .lw a3 a2 0x0, 2) := by decide
theorem fl_at_ea : fetchRel fillLimbsBeTruncCode 0xEA = some (.alu .sub a1 x0 a1, 4) := by decide
theorem fl_at_ee : fetchRel fillLimbsBeTruncCode 0xEE = some (.alu .sll a3 a3 a1, 4) := by decide
theorem fl_at_f2 : fetchRel fillLimbsBeTruncCode 0xF2 = some (.alu .srl a1 a3 a1, 4) := by decide
theorem fl_at_f6 : fetchRel fillLimbsBeTruncCode 0xF6 = some (.store .sw a2 a1 0x0, 2) := by decide
theorem fl_at_f8 : fetchRel fillLimbsBeTruncCode 0xF8 = some (.load .lw (8 : Fin 32) sp 0x1C, 2) := by decide
theorem fl_at_fa : fetchRel fillLimbsBeTruncCode 0xFA = some (.load .lw (9 : Fin 32) sp 0x18, 2) := by decide
theorem fl_at_fc : fetchRel fillLimbsBeTruncCode 0xFC = some (.load .lw (18 : Fin 32) sp 0x14, 2) := by decide
theorem fl_at_fe : fetchRel fillLimbsBeTruncCode 0xFE = some (.load .lw (19 : Fin 32) sp 0x10, 2) := by decide
theorem fl_at_100 : fetchRel fillLimbsBeTruncCode 0x100 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem fl_at_102 : fetchRel fillLimbsBeTruncCode 0x102 = some (.jalr x0 ra 0x0, 2) := by decide
theorem fl_at_104 : fetchRel fillLimbsBeTruncCode 0x104 = some (.aluImm .add a0 x0 0x2A, 4) := by decide
theorem fl_at_108 : fetchRel fillLimbsBeTruncCode 0x108 = some (.auipc ra 0x0, 4) := by decide
theorem fl_at_10c : fetchRel fillLimbsBeTruncCode 0x10C = some (.jalr ra ra 0xFFFFFC8C, 4) := by decide
theorem fl_at_110 : fetchRel fillLimbsBeTruncCode 0x110 = some (.aluImm .add a1 x0 0x4, 2) := by decide
theorem fl_at_112 : fetchRel fillLimbsBeTruncCode 0x112 = some (.auipc ra 0x0, 4) := by decide
theorem fl_at_116 : fetchRel fillLimbsBeTruncCode 0x116 = some (.jalr ra ra 0xFFFFFC72, 4) := by decide
theorem fl_at_11a : fetchRel fillLimbsBeTruncCode 0x11A = some (.alu .add a0 x0 a4, 2) := by decide
theorem fl_at_11c : fetchRel fillLimbsBeTruncCode 0x11C = some (.alu .add a1 x0 a3, 2) := by decide
theorem fl_at_11e : fetchRel fillLimbsBeTruncCode 0x11E = some (.auipc ra 0x0, 4) := by decide
theorem fl_at_122 : fetchRel fillLimbsBeTruncCode 0x122 = some (.jalr ra ra 0xFFFFFC66, 4) := by decide
end

/-- The byte-copy loop's body, from 0x98 to its branch at 0xAC. -/
def flCopy : List BInstr :=
  [.alu .add (9 : Fin 32) a1 (8 : Fin 32), .lbu (9 : Fin 32) (9 : Fin 32) 0, .alu .add a5 (19 : Fin 32) a0,
   .sb a5 (9 : Fin 32) 0, .aluImm .add a0 a0 1, .aluImm .add (8 : Fin 32) (8 : Fin 32) 1]

section
set_option maxRecDepth 20000
theorem flCopy_end : blockEnd fillLimbsBeTruncCode 0x98 flCopy = some 0xAC := by decide
end

/-- The stack word's bytes once the copy is done: `4 - c` zeros, then the `c`
input bytes that end at `E`. -/
def flTemp (M : Word → BitVec 8) (E : Word) (c i : Nat) : BitVec 8 :=
  if i + c < 4 then 0 else M (E - BitVec.ofNat 32 c + BitVec.ofNat 32 (i + c - 4))

abbrev FL : Word := BitVec.ofNat 32 fillLimbsBeTruncAddress

theorem fl_cnt_succ {r : Nat} (h1 : 1 ≤ r) (h2 : r < 2 ^ 32) :
    aluEval .add (BitVec.ofNat 32 (2 ^ 32 - r)) 1 = BitVec.ofNat 32 (2 ^ 32 - (r - 1)) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 (2 ^ 32 - r) + 1).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
  omega

theorem fl_src {E : Word} {c r : Nat} (h1 : r ≤ c) (h2 : c < 2 ^ 32) :
    E + BitVec.ofNat 32 (2 ^ 32 - r) = E - BitVec.ofNat 32 c + BitVec.ofNat 32 (c - r) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  have := E.isLt
  omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The copy loop from 0x94, with `r` of the chunk's `c` bytes left: it
copies the bytes that end at `E` into the low end of the stack word at `Tm`. -/
theorem fl_copy {Mb : Word → BitVec 8} {E Tm : Word} {c : Nat}
    (hc : ∀ Mx : Word → BitVec 8, (∀ x, Sep Tm 4 x 1 → Mx x = Mb x) → CodeIn Mx FL fillLimbsBeTruncCode)
    (hTw : Tm.toNat + 4 ≤ 0x40000000) (hc4 : c ≤ 4)
    (hsrc : ∀ i, i < c → Sep (E - BitVec.ofNat 32 c + BitVec.ofNat 32 i) 1 Tm 4) :
    ∀ r (n : Machine) (Mx : Word → BitVec 8), r ≤ c → 0 < r →
      St Mx FL n 0x94 (reg n) → (∀ x, Sep Tm 4 x 1 → Mx x = Mb x) →
      (∀ i, i < 4 - r → Mx (Tm + BitVec.ofNat 32 i) = flTemp Mb E c i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (2 ^ 32 - r) → reg n a0 = BitVec.ofNat 32 (4 - r) → reg n a1 = E →
      reg n (19 : Fin 32) = Tm → reg n (29 : Fin 32) = 3 →
      ∃ n' Mf, Steps n n' ∧ St Mf FL n' 0xAE (reg n') ∧ (∀ x, Sep Tm 4 x 1 → Mf x = Mb x) ∧
        (∀ i, i < 4 → Mf (Tm + BitVec.ofNat 32 i) = flTemp Mb E c i) ∧
        ∀ q, q ≠ a0 → q ≠ a5 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  intro r
  induction r with
  | zero => intro _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ r ih =>
    intro n Mx hrc _ st hag hpre h8 ha0 ha1 h19 h29
    have hcx := hc Mx hag
    have hz := st.zero
    obtain ⟨n0, d0, u0⟩ := st.notTaken hcx 0x98 fl_at_94 (by decide) (by
      simp only [branchTaken]; rw [h29, ha0]
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_lt]
      show (4 - (r + 1)) % 2 ^ 32 ≤ 3; omega)
    have hcx0 := hc Mx hag
    have hTi : Sep (Tm + BitVec.ofNat 32 (4 - (r + 1))) 1 FL fillLimbsBeTruncCode.length :=
      sep_of_le (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, show FL.toNat = 0x403ad524 by decide]; omega)
        (by decide)
    obtain ⟨n1, c1, u1⟩ := St.block flCopy u0.self hcx0 flCopy_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, flCopy, upd_app, ↓reduceIte, and_true, true_and]
      rw [u0.regs, u0.regs, h19, ha0, add_lit_zero]; exact hTi)
    have esrc : E + BitVec.ofNat 32 (2 ^ 32 - (r + 1)) = E - BitVec.ofNat 32 c + BitVec.ofNat 32 (c - (r + 1)) :=
      fl_src (by omega) (by omega)
    have hv : Mx (E + BitVec.ofNat 32 (2 ^ 32 - (r + 1))) = Mb (E - BitVec.ofNat 32 c + BitVec.ofNat 32 (c - (r + 1))) := by
      rw [esrc]; exact hag _ (hsrc (c - (r + 1)) (by omega)).symm
    have eM : (runBlock flCopy (Mx, reg n0)).1 =
        memStore8 Mx (Tm + BitVec.ofNat 32 (4 - (r + 1))) (Mb (E - BitVec.ofNat 32 c + BitVec.ofNat 32 (c - (r + 1)))) := by
      simp +decide only [runBlock, BInstr.run, flCopy, upd_app, ↓reduceIte]
      rw [u0.regs, u0.regs, u0.regs, u0.regs, h19, ha0, ha1, h8, add_lit_zero, add_lit_zero, uo_ext_zext]
      exact congrArg _ hv
    have R1 : ∀ q, reg n1 q = (runBlock flCopy (Mx, reg n0)).2 q := u1.regs
    obtain ⟨M1, hM1⟩ : ∃ M1, memStore8 Mx (Tm + BitVec.ofNat 32 (4 - (r + 1)))
        (Mb (E - BitVec.ofNat 32 c + BitVec.ofNat 32 (c - (r + 1)))) = M1 := ⟨_, rfl⟩
    rw [hM1] at eM
    have u1' : St M1 FL n1 0xAC (reg n1) := ⟨u1.pc, by rw [u1.mem, eM], fun _ => rfl⟩
    have hag1 : ∀ x, Sep Tm 4 x 1 → M1 x = Mb x := fun x hx => by
      rw [← hM1, memStore8_ne (sep1_ne (hx.sub (c := 4 - (r + 1)) (l := 1) (by omega))), hag x hx]
    have hpre1 : ∀ i, i < 4 - r → M1 (Tm + BitVec.ofNat 32 i) = flTemp Mb E c i := fun i hi => by
      rw [← hM1]
      by_cases hir : i = 4 - (r + 1)
      · subst hir; rw [memStore8_same]; unfold flTemp
        rw [ite_eq_right (by omega), show 4 - (r + 1) + c - 4 = c - (r + 1) by omega]
      · rw [memStore8_ne (sep1_ne (sep_offsets Tm (c := 4 - (r + 1)) (n := 1) (d := i) (k := 1) (by omega)
          (by omega) (by omega))), hpre i (by omega)]
    have hc1 := hc M1 hag1
    have s81 : reg n1 (8 : Fin 32) = BitVec.ofNat 32 (2 ^ 32 - r) := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, flCopy, upd_app, ↓reduceIte]; rw [u0.regs, h8]
      exact (fl_cnt_succ (by omega) (by omega)).trans (by rw [Nat.add_sub_cancel])
    have a01 : reg n1 a0 = BitVec.ofNat 32 (4 - r) := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, flCopy, upd_app, ↓reduceIte]; rw [u0.regs, ha0]
      show BitVec.ofNat 32 (4 - (r + 1)) + BitVec.ofNat 32 1 = _
      rw [ofNat_add_ofNat, show 4 - (r + 1) + 1 = 4 - r by omega]
    have K1 : ∀ q, q ≠ a0 → q ≠ a5 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n1 q = reg n q :=
      fun q h0 h5 h8 h9 => by
        rw [R1, runBlock_reg _ _ _ q u0.self.zero (by
          simp only [flCopy, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h5, h8, h9]), u0.regs]
    by_cases hr : r = 0
    · subst hr
      obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc1 0xAE fl_at_ac (by decide) (by
        simp only [branchTaken]; rw [s81, u1'.zero]; decide)
      exact ⟨n2, M1, .cons d0 (c1.trans (.single d2)), u2.self, hag1, hpre1,
        fun q h0 h5 h8 h9 => by rw [u2.regs, K1 q h0 h5 h8 h9]⟩
    · obtain ⟨n2, d2, u2⟩ := u1'.taken hc1 0x94 fl_at_ac (by decide) (by
        simp only [branchTaken, s81, u1'.zero, bne_iff_ne, ne_eq]
        intro h; have := ofNat_inj (c := 2 ^ 32 - r) (d := 0) (by omega) (by decide) h; omega)
      obtain ⟨n3, Mf, c3, u3, hag3, hb3, K3⟩ := ih n2 M1 (by omega) (by omega) u2.self hag1 hpre1
        (by rw [u2.regs, s81]) (by rw [u2.regs, a01])
        (by rw [u2.regs, K1 _ (by decide) (by decide) (by decide) (by decide), ha1])
        (by rw [u2.regs, K1 _ (by decide) (by decide) (by decide) (by decide), h19])
        (by rw [u2.regs, K1 _ (by decide) (by decide) (by decide) (by decide), h29])
      exact ⟨n3, Mf, .cons d0 (c1.trans (.cons d2 c3)), u3, hag3, hb3,
        fun q h0 h5 h8 h9 => by rw [K3 q h0 h5 h8 h9, u2.regs, K1 q h0 h5 h8 h9]⟩

theorem beNat_zeros (k : Nat) (l : Bytes) : beNat (List.replicate k 0 ++ l) = beNat l := by
  rw [beNat_append]
  have : beNat (List.replicate k 0) = 0 := by
    unfold beNat
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ', List.foldl_append, ih]; rfl
  rw [this, Nat.zero_mul, Nat.zero_add]

theorem fl_bytes {Mf Mb : Word → BitVec 8} {Tm E : Word} {c : Nat} (hc : c ≤ 4)
    (h : ∀ i, i < 4 → Mf (Tm + BitVec.ofNat 32 i) = flTemp Mb E c i) :
    memBytes Mf Tm 4 = List.replicate (4 - c) 0 ++ memBytes Mb (E - BitVec.ofNat 32 c) c := by
  apply List.ext_getElem
  · rw [memBytes_length, List.length_append, List.length_replicate, memBytes_length]; omega
  · intro i h1 h2
    rw [memBytes_length] at h1
    simp only [memBytes, List.getElem_map, List.getElem_range]
    rw [h i h1, List.getElem_append]
    unfold flTemp
    by_cases hi : i < 4 - c
    · rw [dite_eq_left (by rw [List.length_replicate]; exact hi), List.getElem_replicate, ite_eq_left (by omega)]; rfl
    · rw [dite_eq_right (by rw [List.length_replicate]; exact hi), ite_eq_right (by omega)]
      simp only [List.getElem_map, List.getElem_range, List.length_replicate]
      rw [show i + c - 4 = i - (4 - c) by omega]

theorem fl_bswap (x : Word) :
    aluEval .or (aluEval .or (aluEval .sll x 0x18) (aluEval .sll (aluEval .and x 0xFF00) 0x8))
      (aluEval .or (aluEval .and (aluEval .srl x 0x8) 0xFF00) (aluEval .srl x 0x18)) = bswap32 x := by
  show ((x <<< 24) ||| ((x &&& 0xFF00) <<< 8)) ||| (((x >>> 8) &&& 0xFF00) ||| (x >>> 24)) = _
  unfold bswap32
  rw [BitVec.or_comm _ (x >>> 24), BitVec.or_comm (x <<< 24), BitVec.or_comm (_ ||| x <<< 24) (x >>> 24 ||| _),
    ← BitVec.or_assoc]

theorem fl_c {d : Nat} (h1 : 1 ≤ d) (h2 : d < 2 ^ 32) :
    aluEval .sub (BitVec.ofNat 32 d) (aluEval .and (aluEval .add (aluEval .sltu (BitVec.ofNat 32 d)
      (aluEval .add (BitVec.ofNat 32 d) 0xFFFFFFFC)) 0xFFFFFFFF) (aluEval .add (BitVec.ofNat 32 d) 0xFFFFFFFC)) =
      BitVec.ofNat 32 (min 4 d) := by
  have hs2 : (aluEval .add (BitVec.ofNat 32 d) 0xFFFFFFFC).toNat = (d + (2 ^ 32 - 4)) % 2 ^ 32 := by
    show (BitVec.ofNat 32 d + 0xFFFFFFFC).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0xFFFFFFFC : Word).toNat = 2 ^ 32 - 4 from rfl,
      Nat.mod_eq_of_lt h2]
  generalize aluEval .add (BitVec.ofNat 32 d) 0xFFFFFFFC = s2 at hs2 ⊢
  by_cases hd : d < 4
  · have hlt : aluEval .sltu (BitVec.ofNat 32 d) s2 = 1 := by
      show (if (BitVec.ofNat 32 d).ult s2 then (1 : Word) else 0) = 1
      rw [ite_eq_left]
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; rw [hs2]; omega
    rw [hlt, show aluEval .add (1 : Word) 0xFFFFFFFF = 0 from rfl,
      show aluEval .and (0 : Word) s2 = 0 from BitVec.zero_and,
      show aluEval .sub (BitVec.ofNat 32 d) 0 = BitVec.ofNat 32 d from BitVec.sub_zero _]
    congr 1; omega
  · have hlt : aluEval .sltu (BitVec.ofNat 32 d) s2 = 0 := by
      show (if (BitVec.ofNat 32 d).ult s2 then (1 : Word) else 0) = 0
      rw [ite_eq_right]
      simp only [BitVec.ult, BitVec.toNat_ofNat]; rw [hs2]; simp only [decide_eq_true_eq]; omega
    rw [hlt, show aluEval .add (0 : Word) 0xFFFFFFFF = 0xFFFFFFFF from rfl,
      show aluEval .and (0xFFFFFFFF : Word) s2 = s2 from (BitVec.and_comm _ _).trans (and_ones s2)]
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 d - s2).toNat = _
    rw [BitVec.toNat_sub, hs2, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

theorem fl_sub4 (X : Word) {j : Nat} (_h : j + 4 < 2 ^ 32) :
    aluEval .add (X - BitVec.ofNat 32 j) 0xFFFFFFFC = X - BitVec.ofNat 32 (j + 4) := by
  apply BitVec.eq_of_toNat_eq
  show (X - BitVec.ofNat 32 j + 0xFFFFFFFC).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (0xFFFFFFFC : Word).toNat = 2 ^ 32 - 4 from rfl]
  have := X.isLt
  omega

theorem fl_ofNat_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem fl_neg {c : Nat} (h1 : 1 ≤ c) (h2 : c ≤ 4) :
    aluEval .sub 0 (BitVec.ofNat 32 c) = BitVec.ofNat 32 (2 ^ 32 - c) := by
  apply BitVec.eq_of_toNat_eq
  show (0 - BitVec.ofNat 32 c).toNat = _
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl]
  omega

/-- The limb loop's head, from 0x5A to 0x62: `a0` gets the chunk's length. -/
theorem fl_head {M : Word → BitVec 8} {n : Machine} (st : St M FL n 0x5A (reg n))
    (hc : CodeIn M FL fillLimbsBeTruncCode) (h5 : reg n (5 : Fin 32) = 4) :
    ∃ n', Steps n n' ∧ St M FL n' 0x62 (reg n') ∧ (∀ q, q ≠ a0 → reg n' q = reg n q) ∧
      ∀ d, 1 ≤ d → d < 2 ^ 32 → reg n (30 : Fin 32) = BitVec.ofNat 32 d → reg n' a0 = BitVec.ofNat 32 (min 4 d) := by
  obtain ⟨n1, d1, u1⟩ := st.alu hc fl_at_5a (off' := 0x5C) (by decide)
  have hz := st.zero
  by_cases hb : (reg n (30 : Fin 32)).ult (reg n (5 : Fin 32)) = true
  · obtain ⟨n2, d2, u2⟩ := u1.taken hc 0x62 fl_at_5c (by decide) (by
      simp only [branchTaken]; simp +decide only [upd_app, ↓reduceIte]; exact hb)
    refine ⟨n2, .cons d1 (.single d2), u2.self, fun q hq => by rw [u2.regs]; exact updz hz hq,
      fun d h1 h2 h30 => ?_⟩
    rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [h30, show reg n x0 = 0 from hz]
    rw [h30, h5] at hb
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq, Nat.mod_eq_of_lt h2] at hb
    show (0 : Word) + BitVec.ofNat 32 d = _
    have h4 : (4 : Word).toNat = 4 := rfl
    exact (BitVec.zero_add (BitVec.ofNat 32 d)).trans (congrArg _ (by show d = min 4 d; omega))
  · obtain ⟨n2, d2, u2⟩ := u1.notTaken hc 0x60 fl_at_5c (by decide) (by
      simp only [branchTaken]; simp +decide only [upd_app, ↓reduceIte]; simpa using hb)
    obtain ⟨n3, d3, u3⟩ := u2.aluImm hc fl_at_60 (off' := 0x62) (by decide)
    refine ⟨n3, .cons d1 (.cons d2 (.single d3)), u3.self, fun q hq => ?_, fun d h1 h2 h30 => ?_⟩
    · rw [u3.regs, updz u2.zero hq]; exact updz hz hq
    · rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [h30, h5] at hb
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2] at hb
      rw [show aluEval .add (0 : Word) 4 = BitVec.ofNat 32 4 from rfl]
      have h4 : (4 : Word).toNat = 4 := rfl
      congr 1; simp only [decide_eq_true_eq] at hb; omega

theorem fl_beq_false {a b : Word} (h : a ≠ b) : (a == b) = false := by
  cases hab : (a == b) with
  | false => rfl
  | true => exact absurd (beq_iff_eq.mp hab) h

theorem fl_subsub (X : Word) {a b : Nat} (_h : a + b < 2 ^ 32) :
    X - BitVec.ofNat 32 a - BitVec.ofNat 32 b = X - BitVec.ofNat 32 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  have := X.isLt; omega

theorem fl_subadd (X : Word) {a b : Nat} (h : b ≤ a) (_ha : a < 2 ^ 32) :
    X - BitVec.ofNat 32 a + BitVec.ofNat 32 b = X - BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  have := X.isLt; omega

/-- Byte `i` of limb `k`'s chunk, as an offset into the `m` input bytes. -/
theorem fl_srcE (E0 : Word) {m k i : Nat} (hkm : 4 * k < m) (hm : m < 2 ^ 30) (hi : i < min 4 (m - 4 * k)) :
    E0 - BitVec.ofNat 32 (4 * k) - BitVec.ofNat 32 (min 4 (m - 4 * k)) + BitVec.ofNat 32 i =
      E0 - BitVec.ofNat 32 m + BitVec.ofNat 32 (m - 4 * k - min 4 (m - 4 * k) + i) := by
  rw [fl_subsub E0 (by omega), fl_subadd E0 (by omega) (by omega), fl_subadd E0 (by omega) (by omega)]
  congr 2; omega

def flMid : List BInstr :=
  [.aluImm .sll (31 : Fin 32) (28 : Fin 32) 2, .alu .sub (8 : Fin 32) a6 (31 : Fin 32),
   .aluImm .add (18 : Fin 32) (8 : Fin 32) 0xFFFFFFFC, .alu .sltu (9 : Fin 32) (8 : Fin 32) (18 : Fin 32),
   .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, .alu .and (9 : Fin 32) (9 : Fin 32) (18 : Fin 32),
   .alu .sub (9 : Fin 32) (8 : Fin 32) (9 : Fin 32)]
def flSet : List BInstr :=
  [.alu .sub (8 : Fin 32) x0 a0, .alu .add (31 : Fin 32) (31 : Fin 32) a2, .aluImm .add (28 : Fin 32) (28 : Fin 32) 1,
   .alu .sub a0 (5 : Fin 32) (9 : Fin 32), .sw sp x0 0xC]
def flStore : List BInstr :=
  [.lw a0 sp 0xC, .aluImm .srl a5 a0 0x8, .aluImm .srl (8 : Fin 32) a0 0x18, .alu .and (9 : Fin 32) a0 (7 : Fin 32),
   .aluImm .sll a0 a0 0x18, .alu .and a5 a5 (7 : Fin 32), .aluImm .sll (9 : Fin 32) (9 : Fin 32) 0x8,
   .alu .or a5 a5 (8 : Fin 32), .alu .or a0 a0 (9 : Fin 32), .alu .or a0 a0 a5, .sw (31 : Fin 32) a0 0,
   .aluImm .add a1 a1 0xFFFFFFFC, .aluImm .add (30 : Fin 32) (30 : Fin 32) 0xFFFFFFFC]

section
set_option maxRecDepth 20000
theorem flMid_end : blockEnd fillLimbsBeTruncCode 0x66 flMid = some 0x80 := by decide
theorem flSet_end : blockEnd fillLimbsBeTruncCode 0x84 flSet = some 0x92 := by decide
theorem flStore_end : blockEnd fillLimbsBeTruncCode 0xAE flStore = some 0xD2 := by decide
end

/-- Limb `k`'s chunk: `min 4 (m - 4 k)` bytes, ending `4 k` bytes before `E0`. -/
abbrev flLen (m k : Nat) : Nat := min 4 (m - 4 * k)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- The limb loop from 0x5A, with `r` of the `K = ⌈m / 4⌉` limbs left after
the first `k`: limb `k` gets the big-endian value of its chunk of the `m`
bytes that end at `E0`. -/
theorem fl_outer {Mb : Word → BitVec 8} {E0 Lp G : Word} {m K : Nat}
    (hc : ∀ Mx : Word → BitVec 8, (∀ x, Sep (G + 0xC) 4 x 1 → Sep Lp (4 * K) x 1 → Mx x = Mb x) →
      CodeIn Mx FL fillLimbsBeTruncCode)
    (hK : K = (m + 3) / 4) (hm : m < 2 ^ 30) (hE : m ≤ E0.toNat)
    (hGw : G.toNat + 0x10 ≤ 0x40000000) (hGa : G.toNat % 4 = 0) (hLw : Lp.toNat + 4 * K ≤ 0x40000000)
    (hLa : Lp.toNat % 4 = 0) (sIT : Sep (E0 - BitVec.ofNat 32 m) m (G + 0xC) 4)
    (sIL : Sep (E0 - BitVec.ofNat 32 m) m Lp (4 * K)) (sTL : Sep (G + 0xC) 4 Lp (4 * K)) :
    ∀ r k (n : Machine) (Mx : Word → BitVec 8), k + r = K →
      St Mx FL n 0x5A (reg n) → (∀ x, Sep (G + 0xC) 4 x 1 → Sep Lp (4 * K) x 1 → Mx x = Mb x) →
      (∀ q, q < k → (memLoad32 Mx (Lp + BitVec.ofNat 32 (4 * q))).toNat =
        beNat (memBytes Mb (E0 - BitVec.ofNat 32 (4 * q) - BitVec.ofNat 32 (flLen m q)) (flLen m q))) →
      reg n (28 : Fin 32) = BitVec.ofNat 32 k → reg n (30 : Fin 32) = BitVec.ofNat 32 m - BitVec.ofNat 32 (4 * k) →
      reg n (17 : Fin 32) = BitVec.ofNat 32 K → reg n a6 = BitVec.ofNat 32 m →
      reg n a1 = E0 - BitVec.ofNat 32 (4 * k) → reg n (5 : Fin 32) = 4 → reg n (6 : Fin 32) = 5 →
      reg n (7 : Fin 32) = 0xFF00 → reg n (29 : Fin 32) = 3 → reg n (19 : Fin 32) = G + 0xC → reg n a2 = Lp →
      reg n sp = G →
      ∃ n' Mf, Steps n n' ∧ St Mf FL n' 0xD4 (reg n') ∧
        (∀ x, Sep (G + 0xC) 4 x 1 → Sep Lp (4 * K) x 1 → Mf x = Mb x) ∧
        (∀ q, q < K → (memLoad32 Mf (Lp + BitVec.ofNat 32 (4 * q))).toNat =
          beNat (memBytes Mb (E0 - BitVec.ofNat 32 (4 * q) - BitVec.ofNat 32 (flLen m q)) (flLen m q))) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a5 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) →
          q ≠ (28 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → reg n' q = reg n q := by
  intro r
  induction r with
  | zero =>
    intro k n Mx hk st hag hl h28 h30 h17 _ _ h5 _ _ _ _ _ _
    have hcx := hc Mx hag
    obtain ⟨n1, c1, u1, K1, _⟩ := fl_head st hcx h5
    obtain ⟨n2, d2, u2⟩ := u1.taken hcx 0xD4 fl_at_62 (by decide) (by
      simp only [branchTaken]; rw [K1 _ (by decide), K1 _ (by decide), h28, h17, show k = K by omega]; exact beq_iff_eq.mpr rfl)
    exact ⟨n2, Mx, c1.trans (.single d2), u2.self, hag, fun q hq => hl q (by omega),
      fun q h0 _ _ _ _ _ _ _ _ => by rw [u2.regs, K1 q h0]⟩
  | succ r ih =>
    intro k n Mx hk st hag hl h28 h30 h17 h16 ha1 h5 h6 h7 h29 h19 ha2 hsp
    have hcx := hc Mx hag
    have hz := st.zero
    have hkm : 4 * k < m := by omega
    have hd : reg n (30 : Fin 32) = BitVec.ofNat 32 (m - 4 * k) := by rw [h30, fl_ofNat_sub (by omega) (by omega)]
    obtain ⟨n1, c1, u1, K1, A1⟩ := fl_head st hcx h5
    have a01 := A1 (m - 4 * k) (by omega) (by omega) hd
    have r1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := K1
    obtain ⟨n2, d2, u2⟩ := u1.notTaken hcx 0x66 fl_at_62 (by decide) (by
      simp only [branchTaken]; rw [r1 _ (by decide), r1 _ (by decide), h28, h17]
      exact fl_beq_false fun h => by have := ofNat_inj (c := k) (d := K) (by omega) (by omega) h; omega)
    obtain ⟨n3, c3, u3⟩ := St.block flMid u2.self hcx flMid_end (by
      simp only [BlockOk, BInstr.ok, flMid]; exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩)
    have R3 : ∀ q, reg n3 q = (runBlock flMid (Mx, reg n2)).2 q := u3.regs
    have u3' : St Mx FL n3 0x80 (reg n3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
    have r2 : ∀ q, q ≠ a0 → reg n2 q = reg n q := fun q h => by rw [u2.regs, r1 q h]
    have hsll : aluEval .sll (BitVec.ofNat 32 k) 2 = BitVec.ofNat 32 (4 * k) := by
      apply BitVec.eq_of_toNat_eq
      show (BitVec.ofNat 32 k <<< (2 % 32)).toNat = _
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      show k % 2 ^ 32 * 4 % 2 ^ 32 = 4 * k % 2 ^ 32; omega
    have e8 : aluEval .sub (BitVec.ofNat 32 m) (BitVec.ofNat 32 (4 * k)) = BitVec.ofNat 32 (m - 4 * k) :=
      fl_ofNat_sub (by omega) (by omega)
    have s13 : reg n3 (9 : Fin 32) = BitVec.ofNat 32 (flLen m k) := by
      rw [R3]; simp +decide only [runBlock, BInstr.run, flMid, upd_app, ↓reduceIte]
      rw [r2 _ (by decide), r2 _ (by decide), h28, h16, hsll, e8]; exact fl_c (by omega) (by omega)
    have K3 : ∀ q, q ≠ (31 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (18 : Fin 32) → q ≠ (9 : Fin 32) →
        reg n3 q = reg n2 q := fun q h31 h8 h18 h9 => by
      rw [R3]; refine runBlock_reg _ _ _ q u2.zero ?_
      simp only [flMid, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h31, h8, h18, h9]
    have t63 : reg n3 (31 : Fin 32) = BitVec.ofNat 32 (4 * k) := by
      rw [R3]; simp +decide only [runBlock, BInstr.run, flMid, upd_app, ↓reduceIte]; rw [r2 _ (by decide), h28, hsll]
    have hc4 : flLen m k ≤ 4 := Nat.min_le_left _ _
    have hcm : flLen m k ≤ m - 4 * k := Nat.min_le_right _ _
    have hc1 : 1 ≤ flLen m k := by unfold flLen; omega
    have hult : (BitVec.ofNat 32 (flLen m k)).ult 5 = true := by
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; show flLen m k % 2 ^ 32 < 5; omega
    obtain ⟨n4, d4, u4⟩ := u3'.notTaken hcx 0x84 fl_at_80 (by decide) (by
      simp only [branchTaken]; rw [s13, K3 _ (by decide) (by decide) (by decide) (by decide), r2 _ (by decide), h6,
        hult]; rfl)
    have Tm4 : (G + 0xC).toNat % 4 = 0 := aligned_add hGa (k := 0xC) (by decide)
    have hT : (G + 0xC).toNat = G.toNat + 12 := by
      show (G + BitVec.ofNat 32 12).toNat = _; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hTc : Sep (G + 0xC) 4 FL fillLimbsBeTruncCode.length :=
      sep_of_le (by rw [BitVec.toNat_add, show FL.toNat = 0x403ad524 by decide]; have : (0xC : Word).toNat = 0xC := rfl
                    omega) (by decide)
    obtain ⟨n5, c5, u5⟩ := St.block flSet u4.self hcx flSet_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, flSet, upd_app, ↓reduceIte, and_true, true_and]
      rw [u4.regs, K3 _ (by decide) (by decide) (by decide) (by decide), r2 _ (by decide), hsp]
      exact ⟨Tm4, hTc⟩)
    have R5 : ∀ q, reg n5 q = (runBlock flSet (Mx, reg n4)).2 q := u5.regs
    have M5e : (runBlock flSet (Mx, reg n4)).1 = memStore32 Mx (G + 0xC) 0 := by
      simp +decide only [runBlock, BInstr.run, flSet, upd_app, ↓reduceIte]
      rw [u4.regs, K3 _ (by decide) (by decide) (by decide) (by decide), r2 _ (by decide), hsp]
    obtain ⟨M5, hM5⟩ : ∃ M5, memStore32 Mx (G + 0xC) 0 = M5 := ⟨_, rfl⟩
    rw [hM5] at M5e
    have u5' : St M5 FL n5 0x92 (reg n5) := ⟨u5.pc, by rw [u5.mem, M5e], fun _ => rfl⟩
    have hag5 : ∀ x, Sep (G + 0xC) 4 x 1 → M5 x = Mx x := fun x hx => by
      rw [← hM5, memStore32_get_sep hx]
    have hag5' : ∀ x, Sep (G + 0xC) 4 x 1 → Sep Lp (4 * K) x 1 → M5 x = Mb x := fun x h1 h2 => by
      rw [hag5 x h1, hag x h1 h2]
    have hc5 := hc M5 hag5'
    have r4 : ∀ q, q ≠ a0 → q ≠ (31 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (18 : Fin 32) → q ≠ (9 : Fin 32) →
        reg n4 q = reg n q := fun q h0 h31 h8 h18 h9 => by
      rw [u4.regs, K3 q h31 h8 h18 h9, r2 q h0]
    have a04 : reg n4 a0 = BitVec.ofNat 32 (flLen m k) := by
      rw [u4.regs, K3 _ (by decide) (by decide) (by decide) (by decide), u2.regs, a01]
    have s05 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 (2 ^ 32 - flLen m k) := by
      rw [R5]; simp +decide only [runBlock, BInstr.run, flSet, upd_app, ↓reduceIte]
      rw [u4.self.zero, a04]; exact fl_neg hc1 hc4
    have a05 : reg n5 a0 = BitVec.ofNat 32 (4 - flLen m k) := by
      rw [R5]; simp +decide only [runBlock, BInstr.run, flSet, upd_app, ↓reduceIte]
      rw [u4.regs, K3 _ (by decide) (by decide) (by decide) (by decide), r2 _ (by decide), h5,
        u4.regs, s13]
      exact fl_ofNat_sub hc4 (by decide)
    have t65 : reg n5 (31 : Fin 32) = Lp + BitVec.ofNat 32 (4 * k) := by
      rw [R5]; simp +decide only [runBlock, BInstr.run, flSet, upd_app, ↓reduceIte]
      rw [u4.regs, t63, u4.regs, K3 _ (by decide) (by decide) (by decide) (by decide), r2 _ (by decide), ha2]
      exact BitVec.add_comm _ _
    have t35 : reg n5 (28 : Fin 32) = BitVec.ofNat 32 (k + 1) := by
      rw [R5]; simp +decide only [runBlock, BInstr.run, flSet, upd_app, ↓reduceIte]
      rw [u4.regs, K3 _ (by decide) (by decide) (by decide) (by decide), r2 _ (by decide), h28]
      exact ofNat_add_ofNat k 1
    have K5 : ∀ q, q ≠ (8 : Fin 32) → q ≠ (31 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ a0 → reg n5 q = reg n4 q :=
      fun q h8 h31 h28 h0 => by
        rw [R5]; refine runBlock_reg _ _ _ q u4.self.zero ?_
        simp only [flSet, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h8, h31, h28, h0]
    have r5 : ∀ q, q ≠ a0 → q ≠ (31 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (18 : Fin 32) → q ≠ (9 : Fin 32) →
        q ≠ (28 : Fin 32) → reg n5 q = reg n q := fun q h0 h31 h8 h18 h9 h28 => by
      rw [K5 q h8 h31 h28 h0, r4 q h0 h31 h8 h18 h9]
    obtain ⟨n6, d6, u6⟩ := u5'.notTaken hc5 0x94 fl_at_92 (by decide) (by
      simp only [branchTaken]; rw [s05, u5'.zero]
      exact fl_beq_false fun h => by
        have := ofNat_inj (c := 2 ^ 32 - flLen m k) (d := 0) (by omega) (by decide) h; omega)
    -- the chunk's bytes
    have hsrcE : ∀ i, i < flLen m k → E0 - BitVec.ofNat 32 (4 * k) - BitVec.ofNat 32 (flLen m k) + BitVec.ofNat 32 i =
        E0 - BitVec.ofNat 32 m + BitVec.ofNat 32 (m - 4 * k - flLen m k + i) := fun i hi => fl_srcE E0 hkm hm hi
    have inI : ∀ i, i < flLen m k → ∀ {a : Word} {l : Nat}, Sep (E0 - BitVec.ofNat 32 m) m a l →
        Sep (E0 - BitVec.ofNat 32 (4 * k) - BitVec.ofNat 32 (flLen m k) + BitVec.ofNat 32 i) 1 a l :=
      fun i hi a l h => by rw [hsrcE i hi]; exact h.sub (by omega)
    obtain ⟨n7, M7, c7, u7, hag7, hb7, K7⟩ := fl_copy (Mb := M5) (E := E0 - BitVec.ofNat 32 (4 * k))
      (Tm := G + 0xC) (c := flLen m k) (fun My hMy => hc My fun x h1 h2 => by rw [hMy x h1, hag5' x h1 h2])
      (by rw [hT]; omega) hc4
      (fun i hi => inI i hi sIT) (flLen m k) n6 M5 (Nat.le_refl _) hc1 u6.self (fun _ _ => rfl)
      (fun i hi => by
        rw [← hM5]; unfold flTemp; rw [ite_eq_left (by omega)]
        rw [store32_byte _ _ _ i (by omega)]
        apply BitVec.eq_of_toNat_eq; rw [byte_toNat, show (0 : Word).toNat = 0 from rfl, Nat.zero_div]; rfl)
      (by rw [u6.regs, s05]) (by rw [u6.regs, a05])
      (by rw [u6.regs, r5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ha1])
      (by rw [u6.regs, r5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h19])
      (by rw [u6.regs, r5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h29])
    have hag7' : ∀ x, Sep (G + 0xC) 4 x 1 → Sep Lp (4 * K) x 1 → M7 x = Mb x := fun x h1 h2 => by
      rw [hag7 x h1, hag5' x h1 h2]
    have hc7 := hc M7 hag7'
    have r7 : ∀ q, q ≠ a0 → q ≠ a5 → q ≠ (31 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (18 : Fin 32) →
        q ≠ (9 : Fin 32) → q ≠ (28 : Fin 32) → reg n7 q = reg n q := fun q h0 h5 h31 h8 h18 h9 h28 => by
      rw [K7 q h0 h5 h8 h9, u6.regs, r5 q h0 h31 h8 h18 h9 h28]
    have hLk : (Lp + BitVec.ofNat 32 (4 * k)).toNat = Lp.toNat + 4 * k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    obtain ⟨n8, c8, u8⟩ := St.block flStore u7 hc7 flStore_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, flStore, upd_app, ↓reduceIte, and_true, true_and]
      rw [r7 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsp,
        K7 _ (by decide) (by decide) (by decide) (by decide), u6.regs, t65, add_lit_zero]
      exact ⟨by rw [show G + 0xC = G + BitVec.ofNat 32 0xC from rfl]; exact aligned_add hGa (by decide),
        aligned_add hLa (by omega),
        sep_of_le (by rw [hLk, show FL.toNat = 0x403ad524 by decide]; omega) (by decide)⟩)
    have hW : (bswap32 (memLoad32 M7 (G + 0xC))).toNat =
        beNat (memBytes Mb (E0 - BitVec.ofNat 32 (4 * k) - BitVec.ofNat 32 (flLen m k)) (flLen m k)) := by
      rw [frp_bswap_toNat, fl_bytes hc4 hb7, beNat_zeros]
      exact congrArg beNat (memBytes_congr fun i hi => hag5' _ (inI i hi sIT).symm (inI i hi sIL).symm)
    have M8e : (runBlock flStore (M7, reg n7)).1 =
        memStore32 M7 (Lp + BitVec.ofNat 32 (4 * k)) (bswap32 (memLoad32 M7 (G + 0xC))) := by
      simp +decide only [runBlock, BInstr.run, flStore, upd_app, ↓reduceIte]
      rw [r7 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsp,
        K7 _ (by decide) (by decide) (by decide) (by decide), u6.regs, t65, add_lit_zero,
        r7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h7]
      exact congrArg _ (fl_bswap _)
    have R8 : ∀ q, reg n8 q = (runBlock flStore (M7, reg n7)).2 q := u8.regs
    obtain ⟨M8, hM8⟩ : ∃ M8, memStore32 M7 (Lp + BitVec.ofNat 32 (4 * k)) (bswap32 (memLoad32 M7 (G + 0xC))) = M8 :=
      ⟨_, rfl⟩
    rw [hM8] at M8e
    have u8' : St M8 FL n8 0xD2 (reg n8) := ⟨u8.pc, by rw [u8.mem, M8e], fun _ => rfl⟩
    have hag8 : ∀ x, Sep (G + 0xC) 4 x 1 → Sep Lp (4 * K) x 1 → M8 x = Mb x := fun x h1 h2 => by
      rw [← hM8, memStore32_get_sep (h2.sub (c := 4 * k) (l := 4) (by omega)), hag7' x h1 h2]
    have hc8 := hc M8 hag8
    obtain ⟨n9, d9, u9⟩ := u8'.jump hc8 fl_at_d2 (off' := 0x5A) (by decide) (by rw [u8'.pc]; decide)
    have hl8 : ∀ q, q < k + 1 → (memLoad32 M8 (Lp + BitVec.ofNat 32 (4 * q))).toNat =
        beNat (memBytes Mb (E0 - BitVec.ofNat 32 (4 * q) - BitVec.ofNat 32 (flLen m q)) (flLen m q)) := fun q hq => by
      rw [← hM8]
      by_cases hqk : q = k
      · subst hqk; rw [memLoad32_store32_same]; exact hW
      · rw [memLoad32_store32_sep (sep_offsets Lp (c := 4 * k) (n := 4) (d := 4 * q) (k := 4) (by omega) (by omega)
          (by omega)), ← hl q (by omega)]
        exact congrArg BitVec.toNat (load_frame (acc := G + 0xC) (n := 4) (fun x hx => by rw [hag7 x hx, hag5 x hx])
          (sTL.subR (c := 4 * q) (l := 4) (by omega)))
    have K8 : ∀ q, q ≠ a0 → q ≠ a5 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ a1 → q ≠ (30 : Fin 32) →
        reg n8 q = reg n7 q := fun q h0 h5 h8 h9 h1 h30 => by
      rw [R8]; refine runBlock_reg _ _ _ q u7.zero ?_
      simp only [flStore, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h5, h8, h9, h1, h30]
    have r9 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a5 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) →
        q ≠ (28 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → reg n9 q = reg n q :=
      fun q h0 h1 h5 h8 h9 h18 h28 h30 h31 => by
        rw [u9.regs, K8 q h0 h5 h8 h9 h1 h30, r7 q h0 h5 h31 h8 h18 h9 h28]
    have a19 : reg n9 a1 = E0 - BitVec.ofNat 32 (4 * (k + 1)) := by
      rw [u9.regs, R8]; simp +decide only [runBlock, BInstr.run, flStore, upd_app, ↓reduceIte]
      rw [r7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ha1,
        fl_sub4 E0 (by omega), show 4 * k + 4 = 4 * (k + 1) by omega]
    have t59 : reg n9 (30 : Fin 32) = BitVec.ofNat 32 m - BitVec.ofNat 32 (4 * (k + 1)) := by
      rw [u9.regs, R8]; simp +decide only [runBlock, BInstr.run, flStore, upd_app, ↓reduceIte]
      rw [r7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h30,
        fl_sub4 _ (by omega), show 4 * k + 4 = 4 * (k + 1) by omega]
    have t39 : reg n9 (28 : Fin 32) = BitVec.ofNat 32 (k + 1) := by
      rw [u9.regs, K8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        K7 _ (by decide) (by decide) (by decide) (by decide), u6.regs, t35]
    obtain ⟨n10, Mf, c10, u10, hag10, hl10, K10⟩ := ih (k + 1) n9 M8 (by omega) u9.self hag8 hl8 t39 t59
      (by rw [r9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h17])
      (by rw [r9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h16]) a19
      (by rw [r9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h5])
      (by rw [r9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h6])
      (by rw [r9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h7])
      (by rw [r9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h29])
      (by rw [r9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h19])
      (by rw [r9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), ha2])
      (by rw [r9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hsp])
    exact ⟨n10, Mf, c1.trans (.cons d2 (c3.trans (.cons d4 (c5.trans (.cons d6 (c7.trans (c8.trans
      (.cons d9 c10)))))))), u10, hag10, hl10, fun q h0 h1 h5 h8 h9 h18 h28 h30 h31 => by
        rw [K10 q h0 h1 h5 h8 h9 h18 h28 h30 h31, r9 q h0 h1 h5 h8 h9 h18 h28 h30 h31]⟩

abbrev flPs : List (Fin 32 × Word) :=
  [((8 : Fin 32), 0x1C), ((9 : Fin 32), 0x18), ((18 : Fin 32), 0x14), ((19 : Fin 32), 0x10)]

def flPre : List BInstr :=
  [.aluImm .and a5 a4 0x7, .aluImm .add a5 a5 0x7, .aluImm .srl (9 : Fin 32) a4 0x3, .aluImm .srl a5 a5 0x3,
   .alu .add a5 a5 (9 : Fin 32), .alu .add a6 x0 a1]
def flPre2 : List BInstr :=
  [.aluImm .add a5 a6 0x3, .aluImm .srl a5 a5 0x2, .aluImm .sltu (8 : Fin 32) a6 0x1, .alu .add (9 : Fin 32) x0 a3]
def flPre3 : List BInstr :=
  [.aluImm .add (28 : Fin 32) x0 0, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, .alu .add a1 a1 a0,
   .alu .and (17 : Fin 32) (8 : Fin 32) (9 : Fin 32), .aluImm .add (5 : Fin 32) x0 0x4, .aluImm .add (6 : Fin 32) x0 0x5,
   .lui (7 : Fin 32) 0x10000, .aluImm .add (7 : Fin 32) (7 : Fin 32) 0xFFFFFF00, .aluImm .add (29 : Fin 32) x0 0x3,
   .aluImm .add (19 : Fin 32) sp 0xC, .alu .add (30 : Fin 32) x0 a6]
def flEnd : List BInstr := [.aluImm .and a1 a4 0x1F, .aluImm .add a0 x0 0xFF]

section
set_option maxRecDepth 20000
theorem flSave_end : blockEnd fillLimbsBeTruncCode 2 (saveBlock flPs) = some 0xA := by decide
theorem flPre_end : blockEnd fillLimbsBeTruncCode 0x16 flPre = some 0x26 := by decide
theorem flPre2_end : blockEnd fillLimbsBeTruncCode 0x2C flPre2 = some 0x38 := by decide
theorem flPre3_end : blockEnd fillLimbsBeTruncCode 0x3E flPre3 = some 0x5A := by decide
theorem flEnd_end : blockEnd fillLimbsBeTruncCode 0xD4 flEnd = some 0xDC := by decide
theorem flRestore_end : blockEnd fillLimbsBeTruncCode 0xF8 (restoreBlock flPs) = some 0x100 := by decide
end

theorem fl_bytes8 {bits : Nat} (h : bits % 32 = 0) (hb : bits < 2 ^ 32) :
    aluEval .add (aluEval .srl (aluEval .add (aluEval .and (BitVec.ofNat 32 bits) 0x7) 0x7) 0x3)
      (aluEval .srl (BitVec.ofNat 32 bits) 0x3) = BitVec.ofNat 32 (bits / 8) := by
  have h7 : aluEval .and (BitVec.ofNat 32 bits) 0x7 = 0 := by
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 bits &&& 7).toNat = 0
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (7 : Word).toNat = 2 ^ 3 - 1 from rfl,
      Nat.mod_eq_of_lt hb, and_pow_sub_one]
    omega
  rw [h7, show aluEval .srl (aluEval .add (0 : Word) 0x7) 0x3 = 0 from rfl]
  apply BitVec.eq_of_toNat_eq
  show (0 + BitVec.ofNat 32 bits >>> (3 % 32)).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  show (0 + bits % 2 ^ 32 / 2 ^ 3) % 2 ^ 32 = bits / 8 % 2 ^ 32
  omega

theorem fl_limbs4 {mm : Nat} (h : mm < 2 ^ 30) :
    aluEval .srl (aluEval .add (BitVec.ofNat 32 mm) 0x3) 0x2 = BitVec.ofNat 32 ((mm + 3) / 4) := by
  apply BitVec.eq_of_toNat_eq
  show ((BitVec.ofNat 32 mm + 3) >>> (2 % 32)).toNat = _
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, show (3 : Word).toNat = 3 from rfl]
  show (mm % 2 ^ 32 + 3) % 2 ^ 32 / 2 ^ 2 = (mm + 3) / 4 % 2 ^ 32
  omega

theorem fl_mask {mm : Nat} (h : mm < 2 ^ 30) :
    aluEval .and (aluEval .add (aluEval .sltu (BitVec.ofNat 32 mm) 0x1) 0xFFFFFFFF) (BitVec.ofNat 32 ((mm + 3) / 4)) =
      BitVec.ofNat 32 ((mm + 3) / 4) := by
  by_cases h0 : mm = 0
  · subst h0; decide
  · have hs : aluEval .sltu (BitVec.ofNat 32 mm) 0x1 = 0 := by
      show (if (BitVec.ofNat 32 mm).ult 1 then (1 : Word) else 0) = 0
      rw [ite_eq_right]
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
      show ¬ mm % 2 ^ 32 < 1; omega
    rw [hs, show aluEval .add (0 : Word) 0xFFFFFFFF = 0xFFFFFFFF from rfl]
    exact (BitVec.and_comm _ _).trans (and_ones _)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- **The compiled `fill_limbs_from_be_slice_truncated`**, for a precision
`bits` that is a multiple of 32 and fits the `L` limbs at `Lp`: it keeps the
last `mm = min n (bits / 8)` of the `n` bytes at `b`, and for each
`q < ⌈mm / 4⌉` stores in limb `q` the big-endian value of the up to four bytes
that end `4 q` bytes before the input's end. It returns `Ok` (0xFF in `a0`),
restores `sp` and the callee-saved registers, and writes only those limbs and
the 0x20 bytes of stack below `sp`. -/
theorem fillLimbs_correct (m : Machine) {sp0 b Lp retAddr : Word} {n L bits mm : Nat}
    (hc : CodeIn m.mem FL fillLimbsBeTruncCode) (hpc : m.pc = FL) (ha0 : reg m a0 = b)
    (ha1 : reg m a1 = BitVec.ofNat 32 n) (ha2 : reg m a2 = Lp) (ha3 : reg m a3 = BitVec.ofNat 32 L)
    (ha4 : reg m a4 = BitVec.ofNat 32 bits) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) (hbits : bits % 32 = 0) (hbL : bits ≤ 32 * L) (hL : L < 2 ^ 25)
    (hmm : mm = min n (bits / 8)) (hbn : b.toNat + n < 2 ^ 32)
    (hsa : sp0.toNat % 4 = 0) (hsl : 0x20 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (hLw : Lp.toNat + 4 * L ≤ 0x40000000) (hLa : Lp.toNat % 4 = 0)
    (sIF : Sep b n (sp0 + 0xFFFFFFE0) 0x20) (sIL : Sep b n Lp (4 * L))
    (sFL : Sep (sp0 + 0xFFFFFFE0) 0x20 Lp (4 * L)) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ reg m' a0 = 0xFF ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ q, q < (mm + 3) / 4 → (memLoad32 m'.mem (Lp + BitVec.ofNat 32 (4 * q))).toNat =
        beNat (memBytes m.mem (b + BitVec.ofNat 32 n - BitVec.ofNat 32 (4 * q) - BitVec.ofNat 32 (flLen mm q))
          (flLen mm q))) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 → Sep Lp (4 * ((mm + 3) / 4)) x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFE0 = G := ⟨_, rfl⟩
  rw [hG] at sIF sFL ⊢
  have hGn : G.toNat = sp0.toNat - 0x20 := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFFE0 : Word).toNat = 2 ^ 32 - 0x20 from rfl]; have := sp0.isLt; omega
  have hGa : G.toNat % 4 = 0 := by omega
  have hGc : ∀ c, c ≤ 0x20 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hFLn : FL.toNat = 0x403ad524 := by decide
  have hiC : ∀ {c l : Nat}, c + l ≤ 0x20 → Sep (G + BitVec.ofNat 32 c) l FL fillLimbsBeTruncCode.length :=
    fun h => sep_of_le (by rw [hGc _ (by omega), hFLn]; omega) (by decide)
  obtain ⟨K, hK⟩ : ∃ K, K = (mm + 3) / 4 := ⟨_, rfl⟩
  rw [← hK]
  have hmmB : mm ≤ bits / 8 := by rw [hmm]; exact Nat.min_le_right _ _
  have hmmn : mm ≤ n := by rw [hmm]; exact Nat.min_le_left _ _
  have hKL : K ≤ L := by omega
  have hm30 : mm < 2 ^ 30 := by omega
  have st0 : St m.mem FL m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hc fl_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) sp = G := by
    simp +decide only [upd, ↓reduceIte]; rw [hsp]; exact hG
  have slotO : ∀ o : Word, 0x10 ≤ o.toNat → o.toNat + 4 ≤ 0x20 → G + o = G + BitVec.ofNat 32 o.toNat :=
    fun o _ _ => by rw [ofNat_toNat_self]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock flPs) u1 hc flSave_end (saveBlock_ok _ flPs _ fun q hq => by
      rw [sp1]
      simp only [flPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add hGa (by decide), by rw [slotO _ (by decide) (by decide)]; exact hiC (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem G (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0)) flPs = Ms :=
    ⟨_, rfl⟩
  rw [hMs] at u2
  have IMs : ∀ x, Sep G 0x20 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside flPs fun q hq => by
      simp only [flPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;>
        (rw [slotO _ (by decide) (by decide)]; exact hx.sub (by decide))
  have slots : ∀ r o, (r, o) ∈ flPs → memLoad32 Ms (G + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [flPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot flPs _ hm (by
      simp only [flPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide), upd_ne (by
        simp only [flPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hr]
  have Mhi : ∀ x : Word, 0x40000000 ≤ x.toNat → Ms x = m.mem x := fun x hx =>
    IMs x (sep_of_le (by omega) (by have := x.isLt; omega))
  have hc2 : CodeIn Ms FL fillLimbsBeTruncCode := fun i hi => by
    rw [Mhi _ (code_hi (b := FL) (by rw [hFLn]; decide) (by rw [hFLn]; decide) hi)]; exact hc i hi
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = G := by rw [u2.regs]; exact sp1
  -- the precision check
  obtain ⟨m3, d3, u3⟩ := u2.self.aluImm hc2 fl_at_a (off' := 0xE) (by decide)
  have a53 : upd (reg m2) a5 (aluEval .sll (reg m2 a3) 0x5) a5 = BitVec.ofNat 32 (32 * L) := by
    simp +decide only [upd_app, ↓reduceIte]; rw [r2 _ (by decide), ha3]
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 L <<< (5 % 32)).toNat = _
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    show L % 2 ^ 32 * 2 ^ 5 % 2 ^ 32 = 32 * L % 2 ^ 32; omega
  obtain ⟨m4, d4, u4⟩ := u3.taken hc2 0x16 fl_at_e (by decide) (by
    simp only [branchTaken]; rw [a53]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 _ (by decide), ha4]
    simp only [BitVec.ult, BitVec.toNat_ofNat, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      Nat.not_lt]
    omega)
  have r4 : ∀ q, q ≠ a5 → q ≠ sp → reg m4 q = reg m q := fun q h5 hs => by
    rw [u4.regs, updz u2.self.zero h5, r2 q hs]
  have hc4 := hc2
  obtain ⟨m5, c5, u5⟩ := St.block flPre u4.self hc4 flPre_end (by
    simp only [BlockOk, BInstr.ok, flPre]; exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩)
  have R5 : ∀ q, reg m5 q = (runBlock flPre (Ms, reg m4)).2 q := u5.regs
  have u5' : St Ms FL m5 0x26 (reg m5) := ⟨u5.pc, by rw [u5.mem]; rfl, fun _ => rfl⟩
  have a55 : reg m5 a5 = BitVec.ofNat 32 (bits / 8) := by
    rw [R5]; simp +decide only [runBlock, BInstr.run, flPre, upd_app, ↓reduceIte]
    rw [r4 a4 (by decide) (by decide), ha4]; exact fl_bytes8 hbits (by omega)
  have a65 : reg m5 a6 = BitVec.ofNat 32 n := by
    rw [R5]; simp +decide only [runBlock, BInstr.run, flPre, upd_app, ↓reduceIte]
    rw [r4 a1 (by decide) (by decide), ha1]; exact BitVec.zero_add _
  have K5 : ∀ q, q ≠ a5 → q ≠ (9 : Fin 32) → q ≠ a6 → reg m5 q = reg m4 q := fun q h5 h9 h6 => by
    rw [R5]; refine runBlock_reg _ _ _ q u4.self.zero ?_
    simp only [flPre, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h5, h9, h6]
  -- `a6 = min n (bits / 8)`
  have hn32 : n < 2 ^ 32 := by omega
  have hB32 : bits / 8 < 2 ^ 32 := by omega
  have pre6 : ∃ m6, Steps m5 m6 ∧ St Ms FL m6 0x2C (reg m6) ∧ reg m6 a6 = BitVec.ofNat 32 mm ∧
      ∀ q, q ≠ a6 → reg m6 q = reg m5 q := by
    by_cases hb : n < bits / 8
    · obtain ⟨m6, d6, u6⟩ := u5'.taken hc4 0x2C fl_at_26 (by decide) (by
        simp only [branchTaken]; rw [K5 a1 (by decide) (by decide) (by decide), r4 a1 (by decide) (by decide), ha1,
          a55]
        simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq, Nat.mod_eq_of_lt hn32, Nat.mod_eq_of_lt hB32]
        exact hb)
      exact ⟨m6, .single d6, u6.self, by rw [u6.regs, a65, hmm, Nat.min_eq_left (by omega)],
        fun q _ => by rw [u6.regs]⟩
    · obtain ⟨m6, d6, u6⟩ := u5'.notTaken hc4 0x2A fl_at_26 (by decide) (by
        simp only [branchTaken]; rw [K5 a1 (by decide) (by decide) (by decide), r4 a1 (by decide) (by decide), ha1,
          a55]
        simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.mod_eq_of_lt hn32,
          Nat.mod_eq_of_lt hB32]
        exact hb)
      obtain ⟨m7, d7, u7⟩ := u6.alu hc4 fl_at_2a (off' := 0x2C) (by decide)
      refine ⟨m7, .cons d6 (.single d7), u7.self, ?_, fun q hq => ?_⟩
      · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u5'.zero, a55, hmm, Nat.min_eq_right (by omega)]
        exact BitVec.zero_add _
      · rw [u7.regs, updz u6.zero hq]
  obtain ⟨m6, c6, u6, a66, K6⟩ := pre6
  have r6 : ∀ q, q ≠ a5 → q ≠ (9 : Fin 32) → q ≠ a6 → q ≠ sp → reg m6 q = reg m q := fun q h5 h9 h6 hs => by
    rw [K6 q h6, K5 q h5 h9 h6, r4 q h5 hs]
  obtain ⟨m7, c7, u7⟩ := St.block flPre2 u6 hc4 flPre2_end (by
    simp only [BlockOk, BInstr.ok, flPre2]; exact ⟨trivial, trivial, trivial, trivial, trivial⟩)
  have R7 : ∀ q, reg m7 q = (runBlock flPre2 (Ms, reg m6)).2 q := u7.regs
  have u7' : St Ms FL m7 0x38 (reg m7) := ⟨u7.pc, by rw [u7.mem]; rfl, fun _ => rfl⟩
  have a57 : reg m7 a5 = BitVec.ofNat 32 K := by
    rw [R7]; simp +decide only [runBlock, BInstr.run, flPre2, upd_app, ↓reduceIte]; rw [a66, hK]; exact fl_limbs4 hm30
  have hL32 : L < 2 ^ 32 := by omega
  have hK32 : K < 2 ^ 32 := by omega
  obtain ⟨m8, d8, u8⟩ := u7'.notTaken hc4 0x3C fl_at_38 (by decide) (by
    simp only [branchTaken]; rw [a57, R7]; simp +decide only [runBlock, BInstr.run, flPre2, upd_app, ↓reduceIte]
    rw [r6 _ (by decide) (by decide) (by decide) (by decide), ha3]
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.mod_eq_of_lt hL32, Nat.mod_eq_of_lt hK32]
    omega)
  obtain ⟨m9, d9, u9⟩ := u8.alu hc4 fl_at_3c (off' := 0x3E) (by decide)
  obtain ⟨m10, c10, u10⟩ := St.block flPre3 u9.self hc4 flPre3_end (by
    simp only [BlockOk, BInstr.ok, flPre3]
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩)
  have R10 : ∀ q, reg m10 q = (runBlock flPre3 (Ms, reg m9)).2 q := u10.regs
  have u10' : St Ms FL m10 0x5A (reg m10) := ⟨u10.pc, by rw [u10.mem]; rfl, fun _ => rfl⟩
  have r9 : ∀ q, reg m9 q = upd (reg m7) (9 : Fin 32) (aluEval .add (reg m7 x0) (reg m7 a5)) q := u9.regs
  have s99 : reg m9 (9 : Fin 32) = BitVec.ofNat 32 K := by
    rw [r9]; simp +decide only [upd_app, ↓reduceIte]; rw [u7'.zero, a57]; exact BitVec.zero_add _
  have K9 : ∀ q, q ≠ a5 → q ≠ (9 : Fin 32) → q ≠ a6 → q ≠ sp → q ≠ (8 : Fin 32) → reg m9 q = reg m q :=
    fun q h5 h9 h6 hs h8 => by
      rw [r9, updz u7'.zero h9, R7, runBlock_reg _ _ _ q u6.zero (by
        simp only [flPre2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h5, h8, h9]), r6 q h5 h9 h6 hs]
  have s89 : reg m9 (8 : Fin 32) = aluEval .sltu (BitVec.ofNat 32 mm) 0x1 := by
    rw [r9, updz u7'.zero (by decide), R7]; simp +decide only [runBlock, BInstr.run, flPre2, upd_app, ↓reduceIte]
    rw [a66]
  have a69 : reg m9 a6 = BitVec.ofNat 32 mm := by
    rw [r9, updz u7'.zero (by decide), R7]; simp +decide only [runBlock, BInstr.run, flPre2, upd_app, ↓reduceIte]
    exact a66
  have sp4 : reg m4 sp = G := by rw [u4.regs, updz u2.self.zero (by decide), sp2]
  have sp9 : reg m9 sp = G := by
    rw [r9, updz u7'.zero (by decide), R7, runBlock_reg _ _ _ sp u6.zero (by
      simp only [flPre2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; decide), K6 sp (by decide),
      K5 sp (by decide) (by decide) (by decide), sp4]
  have hE0 : (b + BitVec.ofNat 32 n).toNat = b.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have g10 : reg m10 (28 : Fin 32) = BitVec.ofNat 32 0 ∧
      reg m10 (30 : Fin 32) = BitVec.ofNat 32 mm - BitVec.ofNat 32 (4 * 0) ∧ reg m10 (17 : Fin 32) = BitVec.ofNat 32 K ∧
      reg m10 a6 = BitVec.ofNat 32 mm ∧ reg m10 a1 = b + BitVec.ofNat 32 n - BitVec.ofNat 32 (4 * 0) ∧
      reg m10 (5 : Fin 32) = 4 ∧ reg m10 (6 : Fin 32) = 5 ∧ reg m10 (7 : Fin 32) = 0xFF00 ∧
      reg m10 (29 : Fin 32) = 3 ∧ reg m10 (19 : Fin 32) = G + 0xC ∧ reg m10 a2 = Lp ∧ reg m10 sp = G := by
    simp only [R10]; simp +decide only [runBlock, BInstr.run, flPre3, upd_app, ↓reduceIte]
    rw [a69, s89, s99, K9 a1 (by decide) (by decide) (by decide) (by decide) (by decide), ha1,
      K9 a0 (by decide) (by decide) (by decide) (by decide) (by decide), ha0,
      K9 a2 (by decide) (by decide) (by decide) (by decide) (by decide), ha2, sp9]
    refine ⟨by rw [u9.self.zero]; rfl, ?_, by rw [hK]; exact fl_mask hm30, rfl, ?_, trivial, trivial, trivial, trivial,
      rfl, rfl, rfl⟩
    · exact (BitVec.zero_add _).trans (BitVec.sub_zero _).symm
    · exact (BitVec.add_comm _ _).trans (BitVec.sub_zero _).symm
  obtain ⟨g28, g30, g17, g16, g11, g5, g6, g7, g29, g19, g12, g2⟩ := g10
  have eIn : b + BitVec.ofNat 32 n - BitVec.ofNat 32 mm = b + BitVec.ofNat 32 (n - mm) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    have := b.isLt; omega
  have sIT : Sep (b + BitVec.ofNat 32 n - BitVec.ofNat 32 mm) mm (G + 0xC) 4 := by
    rw [eIn]; exact (sIF.sub (c := n - mm) (l := mm) (by omega)).subR (c := 0xC) (l := 4) (by omega)
  have sIL' : Sep (b + BitVec.ofNat 32 n - BitVec.ofNat 32 mm) mm Lp (4 * K) := by
    rw [eIn]
    have := (sIL.sub (c := n - mm) (l := mm) (by omega)).subR (c := 0) (l := 4 * K) (by omega)
    rwa [add_ofNat_zero] at this
  have sTL : Sep (G + 0xC) 4 Lp (4 * K) := by
    have := (sFL.sub (c := 0xC) (l := 4) (by omega)).subR (c := 0) (l := 4 * K) (by omega)
    rwa [add_ofNat_zero] at this
  have hGlo : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (G + 0xC) 4 x 1 := fun x hx =>
    sep_of_le (by show (G + BitVec.ofNat 32 0xC).toNat + 4 ≤ _; rw [hGc _ (by omega)]; omega)
      (by have := x.isLt; omega)
  have hLlo : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep Lp (4 * K) x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  obtain ⟨n11, Mf, c11, u11, hagF, hlF, KF⟩ := fl_outer (Mb := Ms) (E0 := b + BitVec.ofNat 32 n) (Lp := Lp) (G := G)
    (m := mm) (K := K)
    (fun Mx hMx => fun i hi => by
      have hx := code_hi (b := FL) (by rw [hFLn]; decide) (by rw [hFLn]; decide) hi
      rw [hMx _ (hGlo _ hx) (hLlo _ hx)]; exact hc2 i hi)
    hK hm30 (by rw [hE0]; omega) (by omega) hGa (by omega) hLa sIT sIL' sTL K 0 m10 Ms (by omega) u10'
    (fun _ _ _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _)) g28 g30 g17 g16 g11 g5 g6 g7 g29 g19 g12 g2
  -- registers the body leaves alone
  have keep : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 14, 20, 21, 22, 23, 24, 25, 26, 27] → reg n11 q = reg m q := by
    intro q hq
    obtain ⟨h0, h1, h5, h8, h9, h18, h28, h30, h31, h17, h5', h6, h7, h29, h19, hsp', h16, hq0⟩ :=
      (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 14, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a5 ∧
        q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ (18 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧
        q ≠ (31 : Fin 32) ∧ q ≠ (17 : Fin 32) ∧ q ≠ (5 : Fin 32) ∧ q ≠ (6 : Fin 32) ∧ q ≠ (7 : Fin 32) ∧
        q ≠ (29 : Fin 32) ∧ q ≠ (19 : Fin 32) ∧ q ≠ sp ∧ q ≠ a6 ∧ q.val ≠ 0) q hq
    rw [KF q h0 h1 h5 h8 h9 h18 h28 h30 h31, R10, runBlock_reg _ _ _ q u9.self.zero (by
      simp only [flPre3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      simp [h28, h8, h1, h17, h5', h6, h7, h29, h19, h30]), K9 q h5 h9 h16 hsp' h8]
  have sp11 : reg n11 sp = G := by
    rw [KF sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), R10, runBlock_reg _ _ _ sp u9.self.zero (by
        simp only [flPre3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; decide), sp9]
  have hcF : CodeIn Mf FL fillLimbsBeTruncCode := fun i hi => by
    have hx := code_hi (b := FL) (by rw [hFLn]; decide) (by rw [hFLn]; decide) hi
    rw [hagF _ (hGlo _ hx) (hLlo _ hx)]; exact hc2 i hi
  obtain ⟨n12, c12, u12⟩ := St.block flEnd u11 hcF flEnd_end (by
    simp only [BlockOk, BInstr.ok, flEnd]; exact ⟨trivial, trivial, trivial⟩)
  have R12 : ∀ q, reg n12 q = (runBlock flEnd (Mf, reg n11)).2 q := u12.regs
  have u12' : St Mf FL n12 0xDC (reg n12) := ⟨u12.pc, by rw [u12.mem]; rfl, fun _ => rfl⟩
  have hbits32 : bits < 2 ^ 32 := by omega
  have a112 : reg n12 a1 = 0 := by
    rw [R12]; simp +decide only [runBlock, BInstr.run, flEnd, upd_app, ↓reduceIte]
    rw [keep a4 (by decide), ha4]
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 bits &&& 0x1F).toNat = 0
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (0x1F : Word).toNat = 2 ^ 5 - 1 from rfl,
      Nat.mod_eq_of_lt hbits32, and_pow_sub_one]
    omega
  obtain ⟨n13, d13, u13⟩ := u12'.taken hcF 0xF8 fl_at_dc (by decide) (by
    simp only [branchTaken]; rw [a112, u12'.zero]; decide)
  have K13 : ∀ q, q ≠ a0 → q ≠ a1 → reg n13 q = reg n11 q := fun q h0 h1 => by
    rw [u13.regs, R12]; refine runBlock_reg _ _ _ q u11.zero ?_
    simp only [flEnd, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1]
  have sp13 : reg n13 sp = G := by rw [K13 sp (by decide) (by decide), sp11]
  have hpsp : ∀ p ∈ flPs, p.1 ≠ sp := by decide
  obtain ⟨n14, c14, u14⟩ := St.block (restoreBlock flPs) u13.self hcF flRestore_end
    (restoreBlock_ok Mf G flPs (reg n13) sp13 hpsp fun q hq => by
      simp only [flPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> exact aligned_add hGa (by decide))
  simp only [restoreBlock_run Mf G flPs (reg n13) sp13 hpsp] at u14
  have rsp : restoreRegs Mf G (reg n13) flPs sp = G := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp13
  obtain ⟨n15, d15, u15⟩ := u14.aluImm hcF fl_at_100 (off' := 0x102) (by decide)
  obtain ⟨n16, d16, pc16, mem16, regs16⟩ := u15.jalr hcF fl_at_102
  have sLG : Sep Lp (4 * K) G 0x20 := by
    have := sFL.symm.sub (c := 0) (l := 4 * K) (by omega); rwa [add_ofNat_zero] at this
  have slot : ∀ o : Word, 0x10 ≤ o.toNat → o.toNat + 4 ≤ 0x20 → memLoad32 Mf (G + o) = memLoad32 Ms (G + o) :=
    fun o h1 h2 => by
      rw [slotO o h1 h2]
      apply memLoad32_congr; intro j hj
      rw [add_ofNat_assoc]
      exact hagF _ (sep_offsets G (c := 0xC) (n := 4) (d := o.toNat + j) (k := 1) (by omega) (by omega) (by omega))
        (sLG.subR (c := o.toNat + j) (l := 1) (by omega))
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs Mf G f ps q = f q := by
    intro f ps q hq0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
  have hIn : ∀ q, q < K → ∀ i, i < flLen mm q →
      Sep G 0x20 (b + BitVec.ofNat 32 n - BitVec.ofNat 32 (4 * q) - BitVec.ofNat 32 (flLen mm q) +
        BitVec.ofNat 32 i) 1 := fun q hq i hi => by
    rw [fl_srcE (b + BitVec.ofNat 32 n) (by omega) hm30 hi, eIn, add_ofNat_assoc]
    exact (sIF.sub (by unfold flLen at hi; omega)).symm
  have hslot : ∀ r o, (r, o) ∈ flPs → reg n16 r = reg m r := fun r o hm => by
    rw [regs16]
    simp only [flPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
      rw [slot _ (by decide) (by decide)]; exact slots _ _ (by decide)
  refine ⟨n16, .cons d1 (c2.trans (.cons d3 (.cons d4 (c5.trans (c6.trans (c7.trans (.cons d8 (.cons d9
    (c10.trans (c11.trans (c12.trans (.cons d13 (c14.trans (.cons d15 (.single d16))))))))))))))), ?_, ?_, ?_,
    fun q hq => ?_, fun q hq => ?_, fun x hx hl => ?_⟩
  · rw [pc16]; simp +decide only [upd, ↓reduceIte]
    rw [rr _ _ ra (by decide) (by decide), K13 ra (by decide) (by decide), keep ra (by decide), hra, add_lit_zero, hret]
  · rw [regs16]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [rsp, ← hG, BitVec.add_assoc]; exact BitVec.add_zero _
  · rw [regs16]; simp +decide only [upd, ↓reduceIte]
    rw [rr _ _ a0 (by decide) (by decide), u13.regs, R12]
    simp +decide only [runBlock, BInstr.run, flEnd, upd_app, ↓reduceIte]
  · rcases (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
        (q.val ∈ [1, 3, 4, 14, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ flPs, p.1 ≠ q) ∧
          q ≠ a0 ∧ q ≠ a1)) q hq with rfl | rfl | rfl | rfl | ⟨h1, h0, hsp', hps, h0', h1'⟩
    · exact hslot _ 0x1C (by decide)
    · exact hslot _ 0x18 (by decide)
    · exact hslot _ 0x14 (by decide)
    · exact hslot _ 0x10 (by decide)
    · rw [regs16, upd_ne h0 hsp', rr _ _ q h0 hps, K13 q h0' h1', keep q h1]
  · rw [mem16, hlF q hq]
    exact congrArg beNat (memBytes_congr fun i hi => IMs _ (hIn q hq i hi))
  · rw [mem16, hagF x (hx.sub (c := 0xC) (l := 4) (by omega)) hl, IMs x hx]

end C3.RV32

