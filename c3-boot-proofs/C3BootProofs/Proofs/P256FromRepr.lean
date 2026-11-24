import C3BootProofs.Proofs.P384FromRepr
import C3BootProofs.Proofs.P256Retrieve
import C3BootProofs.Proofs.MontMul8

/-!
# P-256's field `from_repr`, as compiled

`<p256 FieldElement as PrimeField>::from_repr` is P-384's for 8 limbs: it
reads 32 big-endian bytes into limbs through a stack word, compares them with
the modulus by a chain of `borrowing_sub` calls, converts them to Montgomery
form with `mul_montgomery_form::<8>` against `R² mod p` 0x40 bytes past the
modulus, and keeps the product or zero by the comparison with
`conditional_select`. The choice goes in the byte after the 8 limbs.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem frq_at_0 : fetchRel p256FromReprCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF80, 2) := by decide
theorem frq_at_2 : fetchRel p256FromReprCode 0x2 = some (.store .sw sp ra 0x7C, 2) := by decide
theorem frq_at_4 : fetchRel p256FromReprCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x78, 2) := by decide
theorem frq_at_6 : fetchRel p256FromReprCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x74, 2) := by decide
theorem frq_at_8 : fetchRel p256FromReprCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x70, 2) := by decide
theorem frq_at_a : fetchRel p256FromReprCode 0xA = some (.store .sw sp (19 : Fin 32) 0x6C, 2) := by decide
theorem frq_at_c : fetchRel p256FromReprCode 0xC = some (.store .sw sp (20 : Fin 32) 0x68, 2) := by decide
theorem frq_at_e : fetchRel p256FromReprCode 0xE = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem frq_at_10 : fetchRel p256FromReprCode 0x10 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem frq_at_12 : fetchRel p256FromReprCode 0x12 = some (.aluImm .add a0 sp 0x28, 2) := by decide
theorem frq_at_14 : fetchRel p256FromReprCode 0x14 = some (.auipc ra 0x7000, 4) := by decide
theorem frq_at_18 : fetchRel p256FromReprCode 0x18 = some (.jalr ra ra 0xFFFFFF18, 4) := by decide
theorem frq_at_1c : fetchRel p256FromReprCode 0x1C = some (.aluImm .add a0 sp 0x48, 2) := by decide
theorem frq_at_1e : fetchRel p256FromReprCode 0x1E = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem frq_at_22 : fetchRel p256FromReprCode 0x22 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem frq_at_24 : fetchRel p256FromReprCode 0x24 = some (.aluImm .add (19 : Fin 32) sp 0x48, 4) := by decide
theorem frq_at_28 : fetchRel p256FromReprCode 0x28 = some (.auipc ra 0xE000, 4) := by decide
theorem frq_at_2c : fetchRel p256FromReprCode 0x2C = some (.jalr ra ra 0xFFFFFFD0, 4) := by decide
theorem frq_at_30 : fetchRel p256FromReprCode 0x30 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem frq_at_32 : fetchRel p256FromReprCode 0x32 = some (.store .sw sp x0 0x4, 2) := by decide
theorem frq_at_34 : fetchRel p256FromReprCode 0x34 = some (.lui a2 0x10000, 2) := by decide
theorem frq_at_36 : fetchRel p256FromReprCode 0x36 = some (.aluImm .add a6 x0 0x8, 2) := by decide
theorem frq_at_38 : fetchRel p256FromReprCode 0x38 = some (.aluImm .add a1 a2 0xFFFFFF00, 4) := by decide
theorem frq_at_3c : fetchRel p256FromReprCode 0x3C = some (.branch .beq a6 x0 0x48, 4) := by decide
theorem frq_at_40 : fetchRel p256FromReprCode 0x40 = some (.aluImm .add a3 sp 0x4, 2) := by decide
theorem frq_at_42 : fetchRel p256FromReprCode 0x42 = some (.aluImm .add a4 x0 0x4, 2) := by decide
theorem frq_at_44 : fetchRel p256FromReprCode 0x44 = some (.alu .add a5 x0 (9 : Fin 32), 2) := by decide
theorem frq_at_46 : fetchRel p256FromReprCode 0x46 = some (.branch .beq a4 x0 0x12, 2) := by decide
theorem frq_at_48 : fetchRel p256FromReprCode 0x48 = some (.load .lbu a2 a5 0x0, 4) := by decide
theorem frq_at_4c : fetchRel p256FromReprCode 0x4C = some (.aluImm .add a5 a5 0x1, 2) := by decide
theorem frq_at_4e : fetchRel p256FromReprCode 0x4E = some (.store .sb a3 a2 0x0, 4) := by decide
theorem frq_at_52 : fetchRel p256FromReprCode 0x52 = some (.aluImm .add a3 a3 0x1, 2) := by decide
theorem frq_at_54 : fetchRel p256FromReprCode 0x54 = some (.aluImm .add a4 a4 0xFFFFFFFF, 2) := by decide
theorem frq_at_56 : fetchRel p256FromReprCode 0x56 = some (.branch .bne a4 x0 0xFFFFFFF2, 2) := by decide
theorem frq_at_58 : fetchRel p256FromReprCode 0x58 = some (.load .lw a3 sp 0x4, 2) := by decide
theorem frq_at_5a : fetchRel p256FromReprCode 0x5A = some (.aluImm .xor a4 a0 0x7, 4) := by decide
theorem frq_at_5e : fetchRel p256FromReprCode 0x5E = some (.aluImm .srl a5 a3 0x8, 4) := by decide
theorem frq_at_62 : fetchRel p256FromReprCode 0x62 = some (.aluImm .srl (8 : Fin 32) a3 0x18, 4) := by decide
theorem frq_at_66 : fetchRel p256FromReprCode 0x66 = some (.alu .and a5 a5 a1, 2) := by decide
theorem frq_at_68 : fetchRel p256FromReprCode 0x68 = some (.alu .or a5 a5 (8 : Fin 32), 2) := by decide
theorem frq_at_6a : fetchRel p256FromReprCode 0x6A = some (.alu .and a2 a3 a1, 4) := by decide
theorem frq_at_6e : fetchRel p256FromReprCode 0x6E = some (.aluImm .sll a3 a3 0x18, 2) := by decide
theorem frq_at_70 : fetchRel p256FromReprCode 0x70 = some (.aluImm .sll a2 a2 0x8, 2) := by decide
theorem frq_at_72 : fetchRel p256FromReprCode 0x72 = some (.alu .or a2 a2 a3, 2) := by decide
theorem frq_at_74 : fetchRel p256FromReprCode 0x74 = some (.aluImm .sll a4 a4 0x2, 2) := by decide
theorem frq_at_76 : fetchRel p256FromReprCode 0x76 = some (.alu .add a4 a4 (19 : Fin 32), 2) := by decide
theorem frq_at_78 : fetchRel p256FromReprCode 0x78 = some (.alu .or a2 a2 a5, 2) := by decide
theorem frq_at_7a : fetchRel p256FromReprCode 0x7A = some (.store .sw a4 a2 0x0, 2) := by decide
theorem frq_at_7c : fetchRel p256FromReprCode 0x7C = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem frq_at_7e : fetchRel p256FromReprCode 0x7E = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem frq_at_80 : fetchRel p256FromReprCode 0x80 = some (.branch .bne a0 a6 0xFFFFFFC0, 4) := by decide
theorem frq_at_84 : fetchRel p256FromReprCode 0x84 = some (.aluImm .add (19 : Fin 32) x0 0x0, 2) := by decide
theorem frq_at_86 : fetchRel p256FromReprCode 0x86 = some (.aluImm .add (20 : Fin 32) sp 0x48, 4) := by decide
theorem frq_at_8a : fetchRel p256FromReprCode 0x8A = some (.lui (9 : Fin 32) 0x3FCC5000, 4) := by decide
theorem frq_at_8e : fetchRel p256FromReprCode 0x8E = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFB38, 4) := by decide
theorem frq_at_92 : fetchRel p256FromReprCode 0x92 = some (.aluImm .add (8 : Fin 32) x0 0x8, 2) := by decide
theorem frq_at_94 : fetchRel p256FromReprCode 0x94 = some (.branch .beq (8 : Fin 32) x0 0x1C, 2) := by decide
theorem frq_at_96 : fetchRel p256FromReprCode 0x96 = some (.load .lw a0 (20 : Fin 32) 0x0, 4) := by decide
theorem frq_at_9a : fetchRel p256FromReprCode 0x9A = some (.load .lw a1 (9 : Fin 32) 0x0, 2) := by decide
theorem frq_at_9c : fetchRel p256FromReprCode 0x9C = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem frq_at_9e : fetchRel p256FromReprCode 0x9E = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem frq_at_a2 : fetchRel p256FromReprCode 0xA2 = some (.jalr ra ra 0xFFFFFA94, 4) := by decide
theorem frq_at_a6 : fetchRel p256FromReprCode 0xA6 = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem frq_at_a8 : fetchRel p256FromReprCode 0xA8 = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4, 2) := by decide
theorem frq_at_aa : fetchRel p256FromReprCode 0xAA = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem frq_at_ac : fetchRel p256FromReprCode 0xAC = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem frq_at_ae : fetchRel p256FromReprCode 0xAE = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE8, 2) := by decide
theorem frq_at_b0 : fetchRel p256FromReprCode 0xB0 = some (.lui (8 : Fin 32) 0x3FCC5000, 4) := by decide
theorem frq_at_b4 : fetchRel p256FromReprCode 0xB4 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFB38, 4) := by decide
theorem frq_at_b8 : fetchRel p256FromReprCode 0xB8 = some (.aluImm .add a0 (8 : Fin 32) 0x20, 4) := by decide
theorem frq_at_bc : fetchRel p256FromReprCode 0xBC = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem frq_at_be : fetchRel p256FromReprCode 0xBE = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem frq_at_c2 : fetchRel p256FromReprCode 0xC2 = some (.jalr ra ra 0x3C0, 4) := by decide
theorem frq_at_c6 : fetchRel p256FromReprCode 0xC6 = some (.aluImm .add a1 sp 0x68, 2) := by decide
theorem frq_at_c8 : fetchRel p256FromReprCode 0xC8 = some (.aluImm .and (9 : Fin 32) a0 0xFF, 4) := by decide
theorem frq_at_cc : fetchRel p256FromReprCode 0xCC = some (.alu .add a0 x0 a1, 2) := by decide
theorem frq_at_ce : fetchRel p256FromReprCode 0xCE = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem frq_at_d0 : fetchRel p256FromReprCode 0xD0 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem frq_at_d4 : fetchRel p256FromReprCode 0xD4 = some (.jalr ra ra 0x3AE, 4) := by decide
theorem frq_at_d8 : fetchRel p256FromReprCode 0xD8 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem frq_at_dc : fetchRel p256FromReprCode 0xDC = some (.aluImm .xor a0 a0 0xFFFFFFFF, 4) := by decide
theorem frq_at_e0 : fetchRel p256FromReprCode 0xE0 = some (.alu .and a0 (19 : Fin 32) a0, 4) := by decide
theorem frq_at_e4 : fetchRel p256FromReprCode 0xE4 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem frq_at_e6 : fetchRel p256FromReprCode 0xE6 = some (.alu .or (9 : Fin 32) (9 : Fin 32) a0, 2) := by decide
theorem frq_at_e8 : fetchRel p256FromReprCode 0xE8 = some (.aluImm .add a2 (8 : Fin 32) 0x40, 4) := by decide
theorem frq_at_ec : fetchRel p256FromReprCode 0xEC = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem frq_at_ee : fetchRel p256FromReprCode 0xEE = some (.aluImm .add a1 sp 0x48, 2) := by decide
theorem frq_at_f0 : fetchRel p256FromReprCode 0xF0 = some (.aluImm .add a4 x0 0x1, 2) := by decide
theorem frq_at_f2 : fetchRel p256FromReprCode 0xF2 = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem frq_at_f4 : fetchRel p256FromReprCode 0xF4 = some (.auipc ra 0xA000, 4) := by decide
theorem frq_at_f8 : fetchRel p256FromReprCode 0xF8 = some (.jalr ra ra 0x25C, 4) := by decide
theorem frq_at_fc : fetchRel p256FromReprCode 0xFC = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem frq_at_fe : fetchRel p256FromReprCode 0xFE = some (.auipc ra 0x7000, 4) := by decide
theorem frq_at_102 : fetchRel p256FromReprCode 0x102 = some (.jalr ra ra 0xFFFFFE58, 4) := by decide
theorem frq_at_106 : fetchRel p256FromReprCode 0x106 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem frq_at_108 : fetchRel p256FromReprCode 0x108 = some (.store .sb sp a0 0x24, 4) := by decide
theorem frq_at_10c : fetchRel p256FromReprCode 0x10C = some (.aluImm .add a0 sp 0x28, 2) := by decide
theorem frq_at_10e : fetchRel p256FromReprCode 0x10E = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem frq_at_112 : fetchRel p256FromReprCode 0x112 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem frq_at_114 : fetchRel p256FromReprCode 0x114 = some (.auipc ra 0xE000, 4) := by decide
theorem frq_at_118 : fetchRel p256FromReprCode 0x118 = some (.jalr ra ra 0xFFFFFEE4, 4) := by decide
theorem frq_at_11c : fetchRel p256FromReprCode 0x11C = some (.aluImm .and a3 (8 : Fin 32) 0xFF, 4) := by decide
theorem frq_at_120 : fetchRel p256FromReprCode 0x120 = some (.aluImm .add a1 sp 0x28, 2) := by decide
theorem frq_at_122 : fetchRel p256FromReprCode 0x122 = some (.aluImm .add a2 sp 0x4, 2) := by decide
theorem frq_at_124 : fetchRel p256FromReprCode 0x124 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem frq_at_126 : fetchRel p256FromReprCode 0x126 = some (.auipc ra 0xB000, 4) := by decide
theorem frq_at_12a : fetchRel p256FromReprCode 0x12A = some (.jalr ra ra 0xFFFFFCFC, 4) := by decide
theorem frq_at_12e : fetchRel p256FromReprCode 0x12E = some (.store .sb (18 : Fin 32) (8 : Fin 32) 0x20, 4) := by decide
theorem frq_at_132 : fetchRel p256FromReprCode 0x132 = some (.load .lw ra sp 0x7C, 2) := by decide
theorem frq_at_134 : fetchRel p256FromReprCode 0x134 = some (.load .lw (8 : Fin 32) sp 0x78, 2) := by decide
theorem frq_at_136 : fetchRel p256FromReprCode 0x136 = some (.load .lw (9 : Fin 32) sp 0x74, 2) := by decide
theorem frq_at_138 : fetchRel p256FromReprCode 0x138 = some (.load .lw (18 : Fin 32) sp 0x70, 2) := by decide
theorem frq_at_13a : fetchRel p256FromReprCode 0x13A = some (.load .lw (19 : Fin 32) sp 0x6C, 2) := by decide
theorem frq_at_13c : fetchRel p256FromReprCode 0x13C = some (.load .lw (20 : Fin 32) sp 0x68, 2) := by decide
theorem frq_at_13e : fetchRel p256FromReprCode 0x13E = some (.aluImm .add sp sp 0x80, 2) := by decide
theorem frq_at_140 : fetchRel p256FromReprCode 0x140 = some (.jalr x0 ra 0x0, 2) := by decide
end

abbrev FRQ : Word := BitVec.ofNat 32 p256FromReprAddress

/-- The inner loop's body, from 0x48 to its branch at 0x56: copy one byte. -/
def frqInner : List BInstr :=
  [.lbu a2 a5 0, .aluImm .add a5 a5 1, .sb a3 a2 0, .aluImm .add a3 a3 1, .aluImm .add a4 a4 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem frqInner_end : blockEnd p256FromReprCode 0x48 frqInner = some 0x56 := by decide
end

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The byte loop from 0x48, with `k` of the four bytes left after the
first `j`: it copies the bytes at `src` to the word at `T`, one at a time. -/
theorem frq_inner {Mb : Word → BitVec 8} {src T : Word}
    (hc : ∀ Mx : Word → BitVec 8, (∀ x, Sep T 4 x 1 → Mx x = Mb x) → CodeIn Mx FRQ p256FromReprCode)
    (hsT : Sep src 4 T 4) (hTw : T.toNat + 4 ≤ 0x40000000) :
    ∀ k j (n : Machine) (Mx : Word → BitVec 8), j + k = 4 → 0 < k →
      St Mx FRQ n 0x48 (reg n) → (∀ x, Sep T 4 x 1 → Mx x = Mb x) →
      (∀ i, i < j → Mx (T + BitVec.ofNat 32 i) = Mb (src + BitVec.ofNat 32 i)) →
      reg n a4 = BitVec.ofNat 32 k → reg n a3 = T + BitVec.ofNat 32 j → reg n a5 = src + BitVec.ofNat 32 j →
      ∃ n' Mf, Steps n n' ∧ St Mf FRQ n' 0x58 (reg n') ∧ (∀ x, Sep T 4 x 1 → Mf x = Mb x) ∧
        (∀ i, i < 4 → Mf (T + BitVec.ofNat 32 i) = Mb (src + BitVec.ofNat 32 i)) ∧
        ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro j n Mx hjk _ st hag hj ha4 ha3 ha5
    have hcx := hc Mx hag
    have hz := st.zero
    have hTj : Sep (T + BitVec.ofNat 32 j) 1 FRQ p256FromReprCode.length :=
      sep_of_le (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, show FRQ.toNat = (img% p256FromReprAddress) by decide]; omega)
        (by decide)
    obtain ⟨n1, c1, u1⟩ := St.block frqInner st hcx frqInner_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, frqInner, upd_app, ↓reduceIte, and_true, true_and]
      rw [ha3, add_lit_zero]; exact hTj)
    have eM : (runBlock frqInner (Mx, reg n)).1 =
        memStore8 Mx (T + BitVec.ofNat 32 j) (Mb (src + BitVec.ofNat 32 j)) := by
      simp +decide only [runBlock, BInstr.run, frqInner, upd_app, ↓reduceIte]
      rw [ha3, ha5, add_lit_zero, add_lit_zero, uo_ext_zext,
        hag _ (hsT.sub (c := j) (l := 1) (by omega)).symm]
    have R1 : ∀ q, reg n1 q = (runBlock frqInner (Mx, reg n)).2 q := u1.regs
    have u1' : St (memStore8 Mx (T + BitVec.ofNat 32 j) (Mb (src + BitVec.ofNat 32 j))) FRQ n1 0x56 (reg n1) :=
      ⟨u1.pc, by rw [u1.mem, eM], fun _ => rfl⟩
    have hag' : ∀ x, Sep T 4 x 1 → memStore8 Mx (T + BitVec.ofNat 32 j) (Mb (src + BitVec.ofNat 32 j)) x = Mb x :=
      fun x hx => by rw [memStore8_ne (sep1_ne (hx.sub (c := j) (l := 1) (by omega))), hag x hx]
    have hj' : ∀ i, i < j + 1 → memStore8 Mx (T + BitVec.ofNat 32 j) (Mb (src + BitVec.ofNat 32 j))
        (T + BitVec.ofNat 32 i) = Mb (src + BitVec.ofNat 32 i) := fun i hi => by
      by_cases hij : i = j
      · subst hij; exact memStore8_same _ _ _
      · rw [memStore8_ne (sep1_ne (sep_offsets T (c := j) (n := 1) (d := i) (k := 1) (by omega) (by omega)
          (by omega))), hj i (by omega)]
    have hcx' := hc _ hag'
    have a41 : reg n1 a4 = BitVec.ofNat 32 k := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frqInner, upd_app, ↓reduceIte]; rw [ha4]
      exact frp_ofNat_dec k
    have a31 : reg n1 a3 = T + BitVec.ofNat 32 (j + 1) := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frqInner, upd_app, ↓reduceIte]; rw [ha3]
      exact add_ofNat_assoc T j 1
    have a51 : reg n1 a5 = src + BitVec.ofNat 32 (j + 1) := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frqInner, upd_app, ↓reduceIte]; rw [ha5]
      exact add_ofNat_assoc src j 1
    have K1 : ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n1 r = reg n r := fun r h2 h3 h4 h5 => by
      rw [R1]; refine runBlock_reg _ _ _ r hz ?_
      simp only [frqInner, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      simp [h2, h3, h4, h5]
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n2, d2, u2⟩ := u1'.notTaken hcx' 0x58 frq_at_56 (by decide) (by
        simp only [branchTaken]; rw [a41, u1'.zero]; decide)
      have hj4 : j + 1 = 4 := by omega
      rw [hj4] at hj'
      exact ⟨n2, _, c1.trans (.single d2), u2.self, hag', hj',
        fun r h2 h3 h4 h5 => by rw [u2.regs, K1 r h2 h3 h4 h5]⟩
    · obtain ⟨n2, d2, u2⟩ := u1'.taken hcx' 0x48 frq_at_56 (by decide) (by
        simp only [branchTaken, a41, u1'.zero, bne_iff_ne, ne_eq]
        intro h; exact hk (by have := ofNat_inj (c := k) (d := 0) (by omega) (by decide) h; omega))
      obtain ⟨n3, Mf, c3, u3, hag3, hb3, K3⟩ := ih (j + 1) n2 _ (by omega) (by omega) u2.self hag' hj'
        (by rw [u2.regs, a41]) (by rw [u2.regs, a31]) (by rw [u2.regs, a51])
      exact ⟨n3, Mf, c1.trans (.cons d2 c3), u3, hag3, hb3,
        fun r h2 h3 h4 h5 => by rw [K3 r h2 h3 h4 h5, u2.regs, K1 r h2 h3 h4 h5]⟩

/-- From 0x40 to the inner loop: point at the stack word and the input. -/
def frqOuterA : List BInstr := [.aluImm .add a3 sp 4, .aluImm .add a4 x0 4, .alu .add a5 x0 (9 : Fin 32)]

/-- From 0x58 to the outer branch at 0x80: load the word, swap its bytes,
store it as limb `7 - i`, and advance. -/
def frqOuterB : List BInstr :=
  [.lw a3 sp 4, .aluImm .xor a4 a0 7, .aluImm .srl a5 a3 0x8, .aluImm .srl (8 : Fin 32) a3 0x18,
   .alu .and a5 a5 a1, .alu .or a5 a5 (8 : Fin 32), .alu .and a2 a3 a1, .aluImm .sll a3 a3 0x18,
   .aluImm .sll a2 a2 0x8, .alu .or a2 a2 a3, .aluImm .sll a4 a4 0x2, .alu .add a4 a4 (19 : Fin 32),
   .alu .or a2 a2 a5, .sw a4 a2 0, .aluImm .add a0 a0 1, .aluImm .add (9 : Fin 32) (9 : Fin 32) 4]

section
set_option maxRecDepth 20000
theorem frqOuterA_end : blockEnd p256FromReprCode 0x40 frqOuterA = some 0x46 := by decide
theorem frqOuterB_end : blockEnd p256FromReprCode 0x58 frqOuterB = some 0x80 := by decide
end

theorem frq_swap (x : Word) :
    aluEval .or (aluEval .or (aluEval .sll (aluEval .and x 0xFF00) 0x8) (aluEval .sll x 0x18))
      (aluEval .or (aluEval .and (aluEval .srl x 0x8) 0xFF00) (aluEval .srl x 0x18)) = bswap32 x := by
  show (((x &&& 0xFF00) <<< 8) ||| (x <<< 24)) ||| (((x >>> 8) &&& 0xFF00) ||| (x >>> 24)) = _
  unfold bswap32
  rw [BitVec.or_comm _ (x >>> 24), BitVec.or_comm (_ ||| x <<< 24) (x >>> 24 ||| _), ← BitVec.or_assoc]

theorem frq_xor7 : ∀ i : Fin 8, BitVec.ofNat 32 i.val ^^^ 7 = BitVec.ofNat 32 (7 - i.val) := by decide

theorem frq_limbAddr (X : Word) {i : Nat} (hi : i < 8) :
    aluEval .add (aluEval .sll (aluEval .xor (BitVec.ofNat 32 i) 7) 2) X + 0 = X + BitVec.ofNat 32 (4 * (7 - i)) := by
  rw [add_lit_zero]
  show ((BitVec.ofNat 32 i ^^^ 7) <<< (2 % 32)) + X = _
  rw [frq_xor7 ⟨i, hi⟩, BitVec.add_comm]; congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  show (7 - i) % 2 ^ 32 * 2 ^ 2 % 2 ^ 32 = 4 * (7 - i) % 2 ^ 32
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- The outer loop from 0x40, with `k` limbs left after the first `i`: limb
`7 - i` at `X` gets the big-endian word at `inp + 4 i`, through the stack
word at `T`. -/
theorem frq_outer {Mb : Word → BitVec 8} {inp T X G : Word}
    (hc : ∀ Mx : Word → BitVec 8, (∀ x, Sep T 4 x 1 → Sep X 32 x 1 → Mx x = Mb x) → CodeIn Mx FRQ p256FromReprCode)
    (hT : G + 4 = T) (hiT : Sep inp 32 T 4) (hiX : Sep inp 32 X 32) (hTX : Sep T 4 X 32)
    (hTw : T.toNat + 4 ≤ 0x40000000) (hXw : X.toNat + 32 ≤ 0x40000000) (hTa : T.toNat % 4 = 0)
    (hXa : X.toNat % 4 = 0) :
    ∀ k i (n : Machine) (Mx : Word → BitVec 8), i + k = 8 → 0 < k →
      St Mx FRQ n 0x40 (reg n) → (∀ x, Sep T 4 x 1 → Sep X 32 x 1 → Mx x = Mb x) →
      (∀ q, q < i → memLoad32 Mx (X + BitVec.ofNat 32 (4 * (7 - q))) =
        bswap32 (memLoad32 Mb (inp + BitVec.ofNat 32 (4 * q)))) →
      reg n a0 = BitVec.ofNat 32 i → reg n (9 : Fin 32) = inp + BitVec.ofNat 32 (4 * i) → reg n sp = G →
      reg n a6 = 8 → reg n a1 = 0xFF00 → reg n (19 : Fin 32) = X →
      ∃ n' Mf, Steps n n' ∧ St Mf FRQ n' 0x84 (reg n') ∧ (∀ x, Sep T 4 x 1 → Sep X 32 x 1 → Mf x = Mb x) ∧
        (∀ q, q < 8 → memLoad32 Mf (X + BitVec.ofNat 32 (4 * (7 - q))) =
          bswap32 (memLoad32 Mb (inp + BitVec.ofNat 32 (4 * q)))) ∧
        ∀ r, r ≠ a0 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ (8 : Fin 32) → r ≠ (9 : Fin 32) → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro i n Mx hik _ st hag hl ha0 hs1 hsp ha6 ha1 h19
    have hcx := hc Mx hag
    have hz := st.zero
    obtain ⟨n1, c1, u1⟩ := St.block frqOuterA st hcx frqOuterA_end (by
      simp only [BlockOk, BInstr.ok, frqOuterA]; exact ⟨trivial, trivial, trivial, trivial⟩)
    have R1 : ∀ q, reg n1 q = (runBlock frqOuterA (Mx, reg n)).2 q := u1.regs
    have u1' : St Mx FRQ n1 0x46 (reg n1) := ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩
    have a41 : reg n1 a4 = 4 := by rw [R1]; simp +decide only [runBlock, BInstr.run, frqOuterA, upd_app, ↓reduceIte]
    have a31 : reg n1 a3 = T := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frqOuterA, upd_app, ↓reduceIte]; rw [hsp, ← hT]; rfl
    have a51 : reg n1 a5 = inp + BitVec.ofNat 32 (4 * i) := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frqOuterA, upd_app, ↓reduceIte]; rw [hs1]
      exact BitVec.zero_add _
    have K1 : ∀ r, r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n1 r = reg n r := fun r h3 h4 h5 => by
      rw [R1]; refine runBlock_reg _ _ _ r hz ?_
      simp only [frqOuterA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      simp [h3, h4, h5]
    obtain ⟨n2, d2, u2⟩ := u1'.notTaken hcx 0x48 frq_at_46 (by decide) (by
      simp only [branchTaken]; rw [a41, u1'.zero]; decide)
    have hsrcT : Sep (inp + BitVec.ofNat 32 (4 * i)) 4 T 4 := hiT.sub (c := 4 * i) (l := 4) (by omega)
    obtain ⟨n3, M3, c3, u3, hag3, hb3, K3⟩ := frq_inner (Mb := Mx) (src := inp + BitVec.ofNat 32 (4 * i)) (T := T)
      (fun My hMy => hc My fun x h1 h2 => by rw [hMy x h1, hag x h1 h2]) hsrcT hTw 4 0 n2 Mx (by omega) (by omega)
      u2.self (fun _ _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _)) (by rw [u2.regs, a41]; rfl)
      (by rw [u2.regs, a31, add_ofNat_zero]) (by rw [u2.regs, a51, add_ofNat_zero])
    have hag3' : ∀ x, Sep T 4 x 1 → Sep X 32 x 1 → M3 x = Mb x := fun x h1 h2 => by rw [hag3 x h1, hag x h1 h2]
    have hc3 := hc M3 hag3'
    have hw : memLoad32 M3 T = memLoad32 Mb (inp + BitVec.ofNat 32 (4 * i)) := by
      apply memLoad32_congr2; intro j hj; rw [hb3 j hj, hag _ (hsrcT.sub (c := j) (l := 1) (by omega)).symm
        (by rw [add_ofNat_assoc]; exact (hiX.sub (c := 4 * i + j) (l := 1) (by omega)).symm)]
    have r3 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → reg n3 q = reg n q := fun q h2 h3 h4 h5 => by
      rw [K3 q h2 h3 h4 h5, u2.regs, K1 q h3 h4 h5]
    have hX7 : Sep (X + BitVec.ofNat 32 (4 * (7 - i))) 4 FRQ p256FromReprCode.length :=
      sep_of_le (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, show FRQ.toNat = (img% p256FromReprAddress) by decide]; omega)
        (by decide)
    obtain ⟨n4, c4, u4⟩ := St.block frqOuterB u3 hc3 frqOuterB_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, frqOuterB, upd_app, ↓reduceIte, and_true, true_and]
      rw [r3 sp (by decide) (by decide) (by decide) (by decide), hsp, hT,
        r3 a0 (by decide) (by decide) (by decide) (by decide), ha0, r3 _ (by decide) (by decide) (by decide) (by decide),
        h19, frq_limbAddr X (by omega)]
      exact ⟨hTa, aligned_add hXa (by omega), hX7⟩)
    have M4e : (runBlock frqOuterB (M3, reg n3)).1 =
        memStore32 M3 (X + BitVec.ofNat 32 (4 * (7 - i))) (bswap32 (memLoad32 Mb (inp + BitVec.ofNat 32 (4 * i)))) := by
      simp +decide only [runBlock, BInstr.run, frqOuterB, upd_app, ↓reduceIte]
      rw [r3 sp (by decide) (by decide) (by decide) (by decide), hsp, hT,
        r3 a0 (by decide) (by decide) (by decide) (by decide), ha0, r3 _ (by decide) (by decide) (by decide) (by decide),
        h19, r3 a1 (by decide) (by decide) (by decide) (by decide), ha1, frq_limbAddr X (by omega)]
      congr 1
      rw [hw]; exact frq_swap _
    have R4 : ∀ q, reg n4 q = (runBlock frqOuterB (M3, reg n3)).2 q := u4.regs
    obtain ⟨M4, hM4⟩ : ∃ M4, memStore32 M3 (X + BitVec.ofNat 32 (4 * (7 - i)))
        (bswap32 (memLoad32 Mb (inp + BitVec.ofNat 32 (4 * i)))) = M4 := ⟨_, rfl⟩
    rw [hM4] at M4e
    have u4' : St M4 FRQ n4 0x80 (reg n4) := ⟨u4.pc, by rw [u4.mem, M4e], fun _ => rfl⟩
    have hag4 : ∀ x, Sep T 4 x 1 → Sep X 32 x 1 → M4 x = Mb x := fun x h1 h2 => by
      rw [← hM4, memStore32_get_sep (h2.sub (c := 4 * (7 - i)) (l := 4) (by omega)), hag3' x h1 h2]
    have hl4 : ∀ q, q < i + 1 → memLoad32 M4 (X + BitVec.ofNat 32 (4 * (7 - q))) =
        bswap32 (memLoad32 Mb (inp + BitVec.ofNat 32 (4 * q))) := fun q hq => by
      rw [← hM4]
      by_cases hqi : q = i
      · subst hqi; exact memLoad32_store32_same _ _ _
      · rw [memLoad32_store32_sep (sep_offsets X (c := 4 * (7 - i)) (n := 4) (d := 4 * (7 - q)) (k := 4)
          (by omega) (by omega) (by omega)), ← hl q (by omega)]
        exact load_frame hag3 (hTX.subR (c := 4 * (7 - q)) (l := 4) (by omega))
    have hc4 := hc M4 hag4
    have a04 : reg n4 a0 = BitVec.ofNat 32 (i + 1) := by
      rw [R4]; simp +decide only [runBlock, BInstr.run, frqOuterB, upd_app, ↓reduceIte]
      rw [r3 a0 (by decide) (by decide) (by decide) (by decide), ha0]; exact ofNat_add_ofNat i 1
    have s14 : reg n4 (9 : Fin 32) = inp + BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [R4]; simp +decide only [runBlock, BInstr.run, frqOuterB, upd_app, ↓reduceIte]
      rw [r3 _ (by decide) (by decide) (by decide) (by decide), hs1]
      show inp + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc, show 4 * i + 4 = 4 * (i + 1) by omega]
    have a64 : reg n4 a6 = 8 := by
      rw [R4]; simp +decide only [runBlock, BInstr.run, frqOuterB, upd_app, ↓reduceIte]
      rw [r3 _ (by decide) (by decide) (by decide) (by decide), ha6]
    have K4 : ∀ r, r ≠ a0 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ (8 : Fin 32) → r ≠ (9 : Fin 32) →
        reg n4 r = reg n r := fun r h0 h2 h3 h4 h5 h8 h9 => by
      rw [R4, runBlock_reg _ _ _ r u3.zero (by
        simp only [frqOuterB, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
        simp [h0, h2, h3, h4, h5, h8, h9]), r3 r h2 h3 h4 h5]
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x84 frq_at_80 (by decide) (by
        simp only [branchTaken]; rw [a04, a64, show i + 1 = 8 by omega]; rfl)
      have hi8 : i + 1 = 8 := by omega
      rw [hi8] at hl4
      exact ⟨n5, M4, c1.trans (.cons d2 (c3.trans (c4.trans (.single d5)))), u5.self, hag4, hl4,
        fun r h0 h2 h3 h4 h5 h8 h9 => by rw [u5.regs, K4 r h0 h2 h3 h4 h5 h8 h9]⟩
    · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x40 frq_at_80 (by decide) (by
        simp only [branchTaken, a04, a64, bne_iff_ne, ne_eq]
        intro h; have := ofNat_inj (c := i + 1) (d := 8) (by omega) (by decide) h; omega)
      obtain ⟨n6, Mf, c6, u6, hag6, hb6, K6⟩ := ih (i + 1) n5 M4 (by omega) (by omega) u5.self hag4 hl4
        (by rw [u5.regs, a04]) (by rw [u5.regs, s14])
        (by rw [u5.regs, K4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsp])
        (by rw [u5.regs, a64])
        (by rw [u5.regs, K4 a1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ha1])
        (by rw [u5.regs, K4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h19])
      exact ⟨n6, Mf, c1.trans (.cons d2 (c3.trans (c4.trans (.cons d5 c6)))), u6, hag6, hb6,
        fun r h0 h2 h3 h4 h5 h8 h9 => by rw [K6 r h0 h2 h3 h4 h5 h8 h9, u5.regs, K4 r h0 h2 h3 h4 h5 h8 h9]⟩

/-- From 0x96 to the call: load limb `j` of the input and of the modulus. -/
def frqCmpA : List BInstr := [.lw a0 (20 : Fin 32) 0, .lw a1 (9 : Fin 32) 0, .alu .add a2 x0 (19 : Fin 32)]

/-- From 0xA6 to the branch at 0xAE: keep the borrow and advance. -/
def frqCmpB : List BInstr :=
  [.alu .add (19 : Fin 32) x0 a1, .aluImm .add (20 : Fin 32) (20 : Fin 32) 4, .aluImm .add (9 : Fin 32) (9 : Fin 32) 4,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem frqCmpA_end : blockEnd p256FromReprCode 0x96 frqCmpA = some 0x9E := by decide
theorem frqCmpB_end : blockEnd p256FromReprCode 0xA6 frqCmpB = some 0xAE := by decide
end

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- The comparison loop from 0x96, with `k` limbs left after the first `j`:
`borrowing_sub` runs down the limbs of `X` and `N` and leaves the borrow in
`s3`. It writes only the word below `G`, where `borrowing_sub` keeps a
temporary. -/
theorem frq_cmp {Mb : Word → BitVec 8} {X N G : Word}
    (hc : ∀ Mx : Word → BitVec 8, (∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → Mx x = Mb x) → CodeIn Mx FRQ p256FromReprCode)
    (hb : ∀ Mx : Word → BitVec 8, (∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → Mx x = Mb x) →
      CodeIn Mx (BitVec.ofNat 32 borrowingSubAddress) borrowingSubCode)
    (hGa : G.toNat % 4 = 0) (hGl : 4 ≤ G.toNat) (hGw : G.toNat ≤ 0x40000000) (hXa : X.toNat % 4 = 0)
    (hNa : N.toNat % 4 = 0) (sXF : Sep X 32 (G + 0xFFFFFFFC) 4) (sNF : Sep N 32 (G + 0xFFFFFFFC) 4) :
    ∀ k j (n : Machine) (Mx : Word → BitVec 8) (b : Word), j + k = 8 → 0 < k →
      St Mx FRQ n 0x96 (reg n) → (∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → Mx x = Mb x) →
      reg n (19 : Fin 32) = b → (b = 0 ∨ b = 0xFFFFFFFF) →
      (∃ D, D < 2 ^ (32 * j) ∧ D + accV Mb N j = accV Mb X j + 2 ^ (32 * j) * maskBit b) →
      reg n (20 : Fin 32) = X + BitVec.ofNat 32 (4 * j) → reg n (9 : Fin 32) = N + BitVec.ofNat 32 (4 * j) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 k → reg n sp = G →
      ∃ n' Mf b', Steps n n' ∧ St Mf FRQ n' 0xB0 (reg n') ∧ (∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → Mf x = Mb x) ∧
        reg n' (19 : Fin 32) = b' ∧ (b' = 0 ∨ b' = 0xFFFFFFFF) ∧
        (∃ D, D < 2 ^ (32 * 8) ∧ D + accV Mb N 8 = accV Mb X 8 + 2 ^ (32 * 8) * maskBit b') ∧
        ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ ra → r ≠ (8 : Fin 32) → r ≠ (9 : Fin 32) →
          r ≠ (19 : Fin 32) → r ≠ (20 : Fin 32) → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro j n Mx b hjk _ st hag hb19 hbm ⟨D, hD, hinv⟩ h20 h9 h8 hsp
    have hcx := hc Mx hag
    have hz := st.zero
    obtain ⟨n1, c1, u1⟩ := St.block frqCmpA st hcx frqCmpA_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, frqCmpA, upd_app, ↓reduceIte, and_true]
      rw [h20, h9, add_lit_zero, add_lit_zero]
      exact ⟨aligned_add hXa (by omega), aligned_add hNa (by omega)⟩)
    have R1 : ∀ q, reg n1 q = (runBlock frqCmpA (Mx, reg n)).2 q := u1.regs
    have u1' : St Mx FRQ n1 0x9E (reg n1) := ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩
    obtain ⟨l, hl⟩ : ∃ l, memLoad32 Mb (X + BitVec.ofNat 32 (4 * j)) = l := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, memLoad32 Mb (N + BitVec.ofNat 32 (4 * j)) = r := ⟨_, rfl⟩
    have a01 : reg n1 a0 = l := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frqCmpA, upd_app, ↓reduceIte]
      rw [h20, add_lit_zero, ← hl]; exact load_frame hag (sXF.sub (c := 4 * j) (l := 4) (by omega)).symm
    have a11 : reg n1 a1 = r := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frqCmpA, upd_app, ↓reduceIte]
      rw [h9, add_lit_zero, ← hr]; exact load_frame hag (sNF.sub (c := 4 * j) (l := 4) (by omega)).symm
    have a21 : reg n1 a2 = b := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frqCmpA, upd_app, ↓reduceIte]
      rw [hb19]; exact BitVec.zero_add _
    have K1 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n1 q = reg n q := fun q h0 h1 h2 => by
      rw [R1]; refine runBlock_reg _ _ _ q hz ?_
      simp only [frqCmpA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      simp [h0, h1, h2]
    have hsepB : Sep (G + 0xFFFFFFFC) 4 (BitVec.ofNat 32 borrowingSubAddress) borrowingSubCode.length :=
      sep_of_le (by
        rw [BitVec.toNat_add, show (0xFFFFFFFC : Word).toNat = 2 ^ 32 - 4 from rfl,
          show (BitVec.ofNat 32 borrowingSubAddress).toNat = (img% borrowingSubAddress) by decide]; omega) (by decide)
    obtain ⟨n2, c2, u2, a02, a12, sp2, K2, mem2⟩ := u1'.bsubCall hcx (hb Mx hag) (by decide) frq_at_9e frq_at_a2
      (by decide) (by decide) (by rw [K1 sp (by decide) (by decide) (by decide), hsp]) hGa hsepB
    rw [a01, a11, a21] at a02 a12
    have hag2 : ∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → n2.mem x = Mb x := fun x hx => by rw [mem2 x hx, hag x hx]
    have hc2 := hc _ hag2
    obtain ⟨n3, c3, u3⟩ := St.block frqCmpB u2 hc2 frqCmpB_end (by
      simp only [BlockOk, BInstr.ok, frqCmpB]; exact ⟨trivial, trivial, trivial, trivial, trivial⟩)
    have R3 : ∀ q, reg n3 q = (runBlock frqCmpB (n2.mem, reg n2)).2 q := u3.regs
    have u3' : St n2.mem FRQ n3 0xAE (reg n3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
    have K2' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n2 q = reg n q :=
      fun q h0 h1 h2 h3 h4 hr => by rw [K2 q h0 h1 h2 h3 h4 hr, K1 q h0 h1 h2]
    obtain ⟨hval, hbm'⟩ := bsub_val l r b hbm
    have b3 : reg n3 (19 : Fin 32) = bsubB l r (bsubD l r b) := by
      rw [R3]; simp +decide only [runBlock, BInstr.run, frqCmpB, upd_app, ↓reduceIte]; rw [a12]; exact BitVec.zero_add _
    have x3 : reg n3 (20 : Fin 32) = X + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [R3]; simp +decide only [runBlock, BInstr.run, frqCmpB, upd_app, ↓reduceIte]
      rw [K2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h20]
      show X + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc, show 4 * j + 4 = 4 * (j + 1) by omega]
    have n3' : reg n3 (9 : Fin 32) = N + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [R3]; simp +decide only [runBlock, BInstr.run, frqCmpB, upd_app, ↓reduceIte]
      rw [K2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h9]
      show N + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc, show 4 * j + 4 = 4 * (j + 1) by omega]
    have c83 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 k := by
      rw [R3]; simp +decide only [runBlock, BInstr.run, frqCmpB, upd_app, ↓reduceIte]
      rw [K2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h8]
      exact frp_ofNat_dec k
    have K3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) →
        q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) → reg n3 q = reg n q := fun q h0 h1 h2 h3 h4 hr h8 h9 h19 h20 => by
      rw [R3, runBlock_reg _ _ _ q u2.zero (by
        simp only [frqCmpB, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
        simp [h8, h9, h19, h20]), K2' q h0 h1 h2 h3 h4 hr]
    obtain ⟨e1, e2⟩ := frp_chain hD hinv hval (bsubD l r b).isLt
    have hD' : D + (bsubD l r b).toNat * 2 ^ (32 * j) < 2 ^ (32 * (j + 1)) := by rw [pow32_succ]; exact e1
    have hinv' : D + (bsubD l r b).toNat * 2 ^ (32 * j) + accV Mb N (j + 1) =
        accV Mb X (j + 1) + 2 ^ (32 * (j + 1)) * maskBit (bsubB l r (bsubD l r b)) := by
      rw [accV_succ1, accV_succ1, hl, hr, pow32_succ]; exact e2
    clear e1 e2
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n4, d4, u4⟩ := u3'.notTaken hc2 0xB0 frq_at_ae (by decide) (by
        simp only [branchTaken]; rw [c83, u3'.zero]; decide)
      have hj : j + 1 = 8 := by omega
      rw [hj] at hD' hinv'
      exact ⟨n4, n2.mem, _, c1.trans (c2.trans (c3.trans (.single d4))), u4.self, hag2, by rw [u4.regs, b3], hbm',
        ⟨_, hD', hinv'⟩, fun q h0 h1 h2 h3 h4 hr h8 h9 h19 h20 => by rw [u4.regs, K3 q h0 h1 h2 h3 h4 hr h8 h9 h19 h20]⟩
    · obtain ⟨n4, d4, u4⟩ := u3'.taken hc2 0x96 frq_at_ae (by decide) (by
        simp only [branchTaken, c83, u3'.zero, bne_iff_ne, ne_eq]
        intro h; exact hk (by have := ofNat_inj (c := k) (d := 0) (by omega) (by decide) h; omega))
      obtain ⟨n5, Mf, b', c5, u5, hag5, hb5, hbm5, inv5, K5⟩ := ih (j + 1) n4 n2.mem _ (by omega) (by omega) u4.self
        hag2 (by rw [u4.regs, b3]) hbm' ⟨_, hD', hinv'⟩ (by rw [u4.regs, x3]) (by rw [u4.regs, n3']) (by rw [u4.regs, c83])
        (by rw [u4.regs, K3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), hsp])
      exact ⟨n5, Mf, b', c1.trans (c2.trans (c3.trans (.cons d4 c5))), u5, hag5, hb5, hbm5, inv5,
        fun q h0 h1 h2 h3 h4 hr h8 h9 h19 h20 => by
          rw [K5 q h0 h1 h2 h3 h4 hr h8 h9 h19 h20, u4.regs, K3 q h0 h1 h2 h3 h4 hr h8 h9 h19 h20]⟩

abbrev frqPs : List (Fin 32 × Word) :=
  [(ra, 0x7C), ((8 : Fin 32), 0x78), ((9 : Fin 32), 0x74), ((18 : Fin 32), 0x70), ((19 : Fin 32), 0x6C),
   ((20 : Fin 32), 0x68)]

def frqPro : List BInstr := [.alu .add (9 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0x28]
def frqSet1 : List BInstr :=
  [.aluImm .add a0 sp 0x48, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0, .aluImm .add (19 : Fin 32) sp 0x48]
def frqSet2 : List BInstr :=
  [.aluImm .add a0 x0 0, .sw sp x0 4, .lui a2 0x10000, .aluImm .add a6 x0 8, .aluImm .add a1 a2 0xFFFFFF00]

section
set_option maxRecDepth 20000
theorem frqSave_end : blockEnd p256FromReprCode 2 (saveBlock frqPs) = some 0xE := by decide
theorem frqPro_end : blockEnd p256FromReprCode 0xE frqPro = some 0x14 := by decide
theorem frqSet1_end : blockEnd p256FromReprCode 0x1C frqSet1 = some 0x28 := by decide
theorem frqSet2_end : blockEnd p256FromReprCode 0x30 frqSet2 = some 0x3C := by decide
end

/-- The function's stack, `S = sp0 - 0x140` up to `sp0`: its frame at
`S + 0xC0` and the callees' frames below it. -/
theorem frq_S (sp0 : Word) (h : 0x140 ≤ sp0.toNat) :
    (sp0 + 0xFFFFFEC0).toNat = sp0.toNat - 0x140 ∧ sp0 + 0xFFFFFF80 = sp0 + 0xFFFFFEC0 + BitVec.ofNat 32 0xC0 := by
  refine ⟨?_, by rw [BitVec.add_assoc]; rfl⟩
  rw [BitVec.toNat_add, show (0xFFFFFEC0 : Word).toNat = 2 ^ 32 - 0x140 from rfl]; have := sp0.isLt; omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- **The prologue**, from the entry to the byte loop at 0x42: save the
registers, zero the stack array and the limbs with `Array::default` and
`memset`, and zero the stack word. It writes only the 0x140 bytes of stack
below `sp0`. -/
theorem frq_pro (m : Machine) {sp0 out inp : Word} (hcF : CodeIn m.mem FRQ p256FromReprCode)
    (hZ : CodeIn m.mem (BitVec.ofNat 32 shaZero32Address) shaZero32Code)
    (hMS : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode)
    (hMB : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode)
    (hMZ : CodeIn m.mem (BitVec.ofNat 32 memsetAddress) memsetCode)
    (hpc : m.pc = FRQ) (ha0 : reg m a0 = out) (ha1 : reg m a1 = inp) (hsp : reg m sp = sp0)
    (hsp16 : sp0.toNat % 16 = 0) (hspl : 0x140 ≤ sp0.toNat) (hspw : sp0.toNat ≤ 0x40000000) :
    ∃ n M Ms, Steps m n ∧ St M FRQ n 0x40 (reg n) ∧
      (∀ x, Sep (sp0 + 0xFFFFFEC0) 0x140 x 1 → M x = m.mem x) ∧
      (∀ i, i < 0x18 → M (sp0 + 0xFFFFFEC0 + BitVec.ofNat 32 (0x128 + i)) =
        Ms (sp0 + 0xFFFFFEC0 + BitVec.ofNat 32 (0x128 + i))) ∧
      (∀ r o, (r, o) ∈ frqPs → memLoad32 Ms (sp0 + 0xFFFFFF80 + o) = reg m r) ∧
      reg n sp = sp0 + 0xFFFFFF80 ∧ reg n a0 = BitVec.ofNat 32 0 ∧ reg n (9 : Fin 32) = inp + BitVec.ofNat 32 (4 * 0) ∧
      reg n a6 = 8 ∧ reg n a1 = 0xFF00 ∧
      reg n (19 : Fin 32) = sp0 + 0xFFFFFEC0 + BitVec.ofNat 32 0x108 ∧ reg n (18 : Fin 32) = out ∧
      ∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg n q = reg m q := by
  obtain ⟨hSn, hGS⟩ := frq_S sp0 hspl
  obtain ⟨S, hS⟩ : ∃ S, sp0 + 0xFFFFFEC0 = S := ⟨_, rfl⟩
  rw [hS] at hSn hGS ⊢
  rw [hGS]
  have hSc : ∀ c, c ≤ 0x140 → (S + BitVec.ofNat 32 c).toNat = S.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hSa : S.toNat % 16 = 0 := by omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x140 → d + k ≤ 0x140 →
      Sep (S + BitVec.ofNat 32 c) n (S + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets S h (by omega) (by omega)
  have inS : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x140 → Sep S 0x140 x 1 → Sep (S + BitVec.ofNat 32 c) l x 1 :=
    fun h hx => hx.sub h
  have hi : ∀ {c l : Nat} (b : Word) (k : Nat), c + l ≤ 0x140 → 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (S + BitVec.ofNat 32 c) l b k := fun b k h h1 h2 => sep_of_le (by rw [hSc _ (by omega)]; omega) h2
  have Shi : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep S 0x140 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hFRn : FRQ.toNat = (img% p256FromReprAddress) := by decide
  have Gc : ∀ c, S + BitVec.ofNat 32 0xC0 + BitVec.ofNat 32 c = S + BitVec.ofNat 32 (0xC0 + c) :=
    fun c => add_ofNat_assoc _ _ _
  have st0 : St m.mem FRQ m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hcF frq_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF80) sp = S + BitVec.ofNat 32 0xC0 := by
    simp +decide only [upd, ↓reduceIte]; rw [hsp]; exact hGS
  have slotO : ∀ o : Word, 0x68 ≤ o.toNat → o.toNat + 4 ≤ 0x80 →
      S + BitVec.ofNat 32 0xC0 + o = S + BitVec.ofNat 32 (0xC0 + o.toNat) := fun o _ _ => by
    rw [← Gc, ofNat_toNat_self]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock frqPs) u1 hcF frqSave_end (saveBlock_ok _ frqPs _ fun q hq => by
      rw [sp1]
      simp only [frqPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add (aligned_add (by omega) (by decide)) (by decide),
          by rw [slotO _ (by decide) (by decide)]; exact hi _ _ (by decide) (by rw [hFRn]; decide) (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem (S + BitVec.ofNat 32 0xC0) (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF80))
      frqPs = Ms := ⟨_, rfl⟩
  rw [hMs] at u2
  have IMs : ∀ x, Sep S 0x140 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside frqPs fun q hq => by
      simp only [frqPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
        (rw [slotO _ (by decide) (by decide)]; exact inS (by decide) hx)
  have slots : ∀ r o, (r, o) ∈ frqPs → memLoad32 Ms (S + BitVec.ofNat 32 0xC0 + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [frqPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot frqPs _ hm (by
      simp only [frqPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide),
      upd_ne (by
        simp only [frqPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hr]
  have cd : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep S 0x140 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc h1 h2 hM i hi => by rw [hM _ (Shi _ (code_hi h1 h2 hi))]; exact hc i hi
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = S + BitVec.ofNat 32 0xC0 := by rw [u2.regs]; exact sp1
  have hc2 := cd hcF (by rw [hFRn]; decide) (by rw [hFRn]; decide) IMs
  obtain ⟨m3, c3, u3⟩ := St.block frqPro u2.self hc2 frqPro_end (by
    simp only [BlockOk, BInstr.ok, frqPro]; exact ⟨trivial, trivial, trivial, trivial⟩)
  have R3 : ∀ q, reg m3 q = (runBlock frqPro (Ms, reg m2)).2 q := u3.regs
  have u3' : St Ms FRQ m3 0x14 (reg m3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  have s03 : reg m3 (9 : Fin 32) = inp := by
    rw [R3]; simp +decide only [runBlock, BInstr.run, frqPro, upd_app, ↓reduceIte]
    rw [r2 a1 (by decide), ha1]; exact BitVec.zero_add _
  have s23 : reg m3 (18 : Fin 32) = out := by
    rw [R3]; simp +decide only [runBlock, BInstr.run, frqPro, upd_app, ↓reduceIte]
    rw [r2 a0 (by decide), ha0]; exact BitVec.zero_add _
  have a03 : reg m3 a0 = S + BitVec.ofNat 32 0xE8 := by
    rw [R3]; simp +decide only [runBlock, BInstr.run, frqPro, upd_app, ↓reduceIte]
    rw [sp2]; exact Gc 0x28
  have sp3 : reg m3 sp = S + BitVec.ofNat 32 0xC0 := by
    rw [R3]; simp +decide only [runBlock, BInstr.run, frqPro, upd_app, ↓reduceIte]; exact sp2
  have K3 : ∀ q, q ≠ sp → q ≠ a0 → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) → reg m3 q = reg m q := fun q h2 h0 h8 h18 => by
    rw [R3]; refine (runBlock_reg _ _ _ q u2.self.zero ?_).trans (r2 q h2)
    simp only [frqPro, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h8, h18]
  -- `Array::default`
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3'.callRa hc2 frq_at_14 frq_at_18
    (show FRQ + BitVec.ofNat 32 0x14 + 0x7000 + 0xFFFFFF18 = BitVec.ofNat 32 shaZero32Address by decide) (by decide)
  have r4 : ∀ q, q ≠ ra → reg m4 q = reg m3 q := fun q h => by rw [regs4]; exact updz u3'.zero h
  have eZ : S + BitVec.ofNat 32 0xC0 + 0xFFFFFFC0 = S + BitVec.ofNat 32 0x80 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m5, c5, pc5, sp5, K5, fr5⟩ := shaZero32_correct m4 (d := S + BitVec.ofNat 32 0xE8)
    (T := S + BitVec.ofNat 32 0xC0) (retAddr := FRQ + BitVec.ofNat 32 (0x14 + 8))
    (by rw [mem4]; exact cd hZ (by decide) (by decide) IMs)
    (by rw [mem4]; exact cd hMS (by decide) (by decide) IMs)
    (by rw [mem4]; exact cd hMB (by decide) (by decide) IMs)
    pc4 (by rw [r4 a0 (by decide), a03]) (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at FRQ (by decide) _ (by omega))) (by rw [r4 sp (by decide), sp3])
    (by rw [hSc _ (by omega)]; omega) (by rw [hSc _ (by omega)]; omega) (by rw [hSc _ (by omega)]; omega)
    (by rw [hSc _ (by omega)]; omega) (by rw [eZ]; exact offs (by omega) (by omega) (by omega))
  rw [eZ, mem4] at fr5
  have M5 : ∀ x, Sep S 0x140 x 1 → m5.mem x = m.mem x := fun x hx => by
    rw [fr5 x (inS (by omega) hx), fillBytes_sep (inS (c := 0xE8) (l := 32) (by omega) hx) (Nat.le_refl _), IMs x hx]
  have V5 : ∀ i, i < 0x18 → m5.mem (S + BitVec.ofNat 32 (0x128 + i)) = Ms (S + BitVec.ofNat 32 (0x128 + i)) :=
    fun i hi => by
      rw [fr5 _ (offs (by omega) (by omega) (by omega)), fillBytes_sep (offs (by omega) (by omega) (by omega))
        (Nat.le_refl _)]
  have k5 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m5 q = reg m3 q :=
    fun q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 => by
      rw [K5 q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13, r4 q h14]
  have hc5 := cd hcF (by rw [hFRn]; decide) (by rw [hFRn]; decide) M5
  have u5 : St m5.mem FRQ m5 0x1C (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have sp5' : reg m5 sp = S + BitVec.ofNat 32 0xC0 := by
    rw [k5 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp3]
  obtain ⟨m6, c6, u6⟩ := St.block frqSet1 u5 hc5 frqSet1_end (by
    simp only [BlockOk, BInstr.ok, frqSet1]; exact ⟨trivial, trivial, trivial, trivial, trivial⟩)
  have R6 : ∀ q, reg m6 q = (runBlock frqSet1 (m5.mem, reg m5)).2 q := u6.regs
  have u6' : St m5.mem FRQ m6 0x28 (reg m6) := ⟨u6.pc, by rw [u6.mem]; rfl, fun _ => rfl⟩
  have K6 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (19 : Fin 32) → reg m6 q = reg m5 q := fun q h0 h1 h2 h19 => by
    rw [R6]; refine runBlock_reg _ _ _ q u5.zero ?_
    simp only [frqSet1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2, h19]
  have eX : S + BitVec.ofNat 32 0xC0 + 0x48 = S + BitVec.ofNat 32 0x108 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m7, c7, u7, _, K7⟩ := u6'.memsetW (B := BitVec.ofNat 32 memsetAddress) (w := 8)
    (dst := S + BitVec.ofNat 32 0x108) (by decide) hc5 (cd hMZ (by decide) (by decide) M5) frq_at_28 frq_at_2c
    (by decide) (by decide) (by decide) (by rw [hSc _ (by omega)]; omega) (by decide)
    (aligned_add (by omega) (by decide)) (hi _ _ (by omega) (by decide) (by decide))
    (by rw [R6]; simp +decide only [runBlock, BInstr.run, frqSet1, upd_app, ↓reduceIte]; rw [sp5']; exact eX)
    (by rw [R6]; simp +decide only [runBlock, BInstr.run, frqSet1, upd_app, ↓reduceIte])
    (by rw [R6]; simp +decide only [runBlock, BInstr.run, frqSet1, upd_app, ↓reduceIte])
  obtain ⟨M7, hM7⟩ : ∃ M7, fillWords m5.mem (S + BitVec.ofNat 32 0x108) 0 8 = M7 := ⟨_, rfl⟩
  rw [hM7] at u7
  have M7o : ∀ x, Sep (S + BitVec.ofNat 32 0x108) 32 x 1 → M7 x = m5.mem x := fun x hx => by
    rw [← hM7]; exact fillWords_outside 8 hx
  have hc7 : CodeIn M7 FRQ p256FromReprCode := cd hcF (by rw [hFRn]; decide) (by rw [hFRn]; decide) fun x hx => by
    rw [M7o x (inS (by omega) hx), M5 x hx]
  have r7 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ a0 → q ≠ a1 → q ≠ (19 : Fin 32) →
      reg m7 q = reg m5 q := fun q h2 h3 h4 h5 h6 hr h0 h1 h19 => by
    rw [K7 q h2 h3 h4 h5 h6 hr, K6 q h0 h1 h2 h19]
  have sp7 : reg m7 sp = S + BitVec.ofNat 32 0xC0 := by
    rw [r7 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), sp5']
  have s37 : reg m7 (19 : Fin 32) = S + BitVec.ofNat 32 0x108 := by
    rw [K7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), R6]
    simp +decide only [runBlock, BInstr.run, frqSet1, upd_app, ↓reduceIte]; rw [sp5']; exact eX
  have eT : S + BitVec.ofNat 32 0xC0 + 4 = S + BitVec.ofNat 32 0xC4 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m8, c8, u8⟩ := St.block frqSet2 u7 hc7 frqSet2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, frqSet2, upd_app, ↓reduceIte, and_true]
    rw [sp7, eT]
    exact ⟨trivial, aligned_add (by omega) (by decide), hi _ _ (by omega) (by rw [hFRn]; decide) (by decide)⟩)
  have R8 : ∀ q, reg m8 q = (runBlock frqSet2 (M7, reg m7)).2 q := u8.regs
  have M8e : (runBlock frqSet2 (M7, reg m7)).1 = memStore32 M7 (S + BitVec.ofNat 32 0xC4) 0 := by
    simp +decide only [runBlock, BInstr.run, frqSet2, upd_app, ↓reduceIte]; rw [sp7, eT]
  obtain ⟨M8, hM8⟩ : ∃ M8, memStore32 M7 (S + BitVec.ofNat 32 0xC4) 0 = M8 := ⟨_, rfl⟩
  rw [hM8] at M8e
  have u8' : St M8 FRQ m8 0x3C (reg m8) := ⟨u8.pc, by rw [u8.mem, M8e], fun _ => rfl⟩
  have M8o : ∀ x, Sep S 0x140 x 1 → M8 x = m.mem x := fun x hx => by
    rw [← hM8, memStore32_get_sep (inS (by omega) hx), M7o x (inS (by omega) hx), M5 x hx]
  have hc8 := cd hcF (by rw [hFRn]; decide) (by rw [hFRn]; decide) M8o
  have K8 : ∀ q, q ≠ a0 → q ≠ a6 → q ≠ a2 → q ≠ a1 → q ≠ a3 → reg m8 q = reg m7 q :=
    fun q h0 h6 h2 h1 _ => by
      rw [R8]; refine runBlock_reg _ _ _ q u7.zero ?_
      simp only [frqSet2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h6, h2, h1]
  have a68 : reg m8 a6 = 8 := by rw [R8]; simp +decide only [runBlock, BInstr.run, frqSet2, upd_app, ↓reduceIte]
  obtain ⟨m9, d9, u9⟩ := u8'.notTaken hc8 0x40 frq_at_3c (by decide) (by
    simp only [branchTaken]; rw [a68, u8'.zero]; decide)
  have g9 : ∀ q, reg m9 q = reg m8 q := u9.regs
  refine ⟨m9, M8, Ms, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans
    (.single d9)))))))), u9.self, M8o, fun i hi => ?_, slots, ?_, ?_, ?_, by rw [g9, a68], ?_, ?_, ?_,
    fun q hq => ?_⟩
  · rw [← hM8, memStore32_get_sep (offs (by omega) (by omega) (by omega)),
      M7o _ (offs (by omega) (by omega) (by omega)), V5 i hi]
  · rw [g9, K8 sp (by decide) (by decide) (by decide) (by decide) (by decide), sp7]
  · rw [g9, R8]; simp +decide only [runBlock, BInstr.run, frqSet2, upd_app, ↓reduceIte]; rw [u7.zero]; rfl
  · rw [g9, K8 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      r7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), s03, add_ofNat_zero]
  · rw [g9, R8]; simp +decide only [runBlock, BInstr.run, frqSet2, upd_app, ↓reduceIte]
  · rw [g9, K8 _ (by decide) (by decide) (by decide) (by decide) (by decide), s37]
  · rw [g9, K8 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      r7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), s23]
  · obtain ⟨h0, h6, h2, h3, h17, h1, h4, h5, hr, h19, h7, ht0, ht1, h7', h28, h29, h30, hsp', h8, h18⟩ :=
      (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a0 ∧ q ≠ a6 ∧ q ≠ a2 ∧ q ≠ a3 ∧
        q ≠ (17 : Fin 32) ∧ q ≠ a1 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ ra ∧ q ≠ (19 : Fin 32) ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧
        q ≠ (7 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ sp ∧ q ≠ (9 : Fin 32) ∧
        q ≠ (18 : Fin 32)) q hq
    rw [g9, K8 q h0 h6 h2 h1 h3, r7 q h2 h3 h4 h5 h6 hr h0 h1 h19,
      k5 q h1 h2 h3 h4 h5 h6 h7 ht0 ht1 h7' h28 h29 h30 hr, K3 q hsp' h0 h8 h18]

/-- The code P-256's `from_repr` runs, where the image loads it, and the two
facts about the modulus data that its Montgomery multiplication needs. -/
structure FRQEnv (M : Word → BitVec 8) : Prop where
  fr : CodeIn M FRQ p256FromReprCode
  za : CodeIn M (BitVec.ofNat 32 shaZero32Address) shaZero32Code
  ms : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  cs : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cb : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  bs : CodeIn M (BitVec.ofNat 32 borrowingSubAddress) borrowingSubCode
  nz : CodeIn M (BitVec.ofNat 32 uintRefIsNonzeroAddress) uintRefIsNonzeroCode
  mm : CodeIn M (BitVec.ofNat 32 mulMont8Address) mulMont8Code
  sel : CodeIn M (BitVec.ofNat 32 uintSelect8Address) uintSelect8Code
  bb : CodeIn M (BitVec.ofNat 32 blackBoxU8Address) blackBoxU8Code
  csel : CodeIn M (BitVec.ofNat 32 condSelect256Address) condSelect256Code
  sca : CodeIn M (BitVec.ofNat 32 sliceCtAssignAddress) sliceCtAssignCode
  nlo : memLoad32 M p256Np = 0xFFFFFFFF
  r2lt : accV M (p256Np + 0x40) 8 < accV M p256Np 8

def frqT1 : List BInstr :=
  [.lui (8 : Fin 32) 0x3FCC5000, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFB38, .aluImm .add a0 (8 : Fin 32) 0x20,
   .aluImm .add a1 x0 0]
def frqT2 : List BInstr :=
  [.aluImm .add a1 sp 0x68, .aluImm .and (9 : Fin 32) a0 0xFF, .alu .add a0 x0 a1, .aluImm .add a1 x0 0]
def frqT3 : List BInstr :=
  [.aluImm .and a0 a0 0xFF, .aluImm .xor a0 a0 0xFFFFFFFF, .alu .and a0 (19 : Fin 32) a0, .aluImm .and a0 a0 1,
   .alu .or (9 : Fin 32) (9 : Fin 32) a0, .aluImm .add a2 (8 : Fin 32) 0x40, .aluImm .add a0 sp 4,
   .aluImm .add a1 sp 0x48, .aluImm .add a4 x0 1, .alu .add a3 x0 (8 : Fin 32)]

section
set_option maxRecDepth 20000
theorem frqT1_end : blockEnd p256FromReprCode 0xB0 frqT1 = some 0xBE := by decide
theorem frqT2_end : blockEnd p256FromReprCode 0xC6 frqT2 = some 0xD0 := by decide
theorem frqT3_end : blockEnd p256FromReprCode 0xD8 frqT3 = some 0xF4 := by decide
end

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- From 0xB0 to 0xFC: the two `is_nonzero` calls on no words return 0, so
the choice is the comparison's borrow bit, in `s1`; then
`mul_montgomery_form::<8>` puts the limbs at `X = S + 0x108` times `R²` in
Montgomery form at `T = S + 0xC4`. -/
theorem frq_tailA {M0 : Word → BitVec 8} (E : FRQEnv M0) (n : Machine) {S b : Word}
    (st : St n.mem FRQ n 0xB0 (reg n)) (hf : ∀ x, Sep S 0x140 x 1 → n.mem x = M0 x)
    (hSa : S.toNat % 16 = 0) (hSw : S.toNat + 0x140 ≤ 0x40000000) (sSN : Sep S 0x140 p256Np 0x60)
    (hsp : reg n sp = S + BitVec.ofNat 32 0xC0) (h19 : reg n (19 : Fin 32) = b) :
    ∃ n', Steps n n' ∧ St n'.mem FRQ n' 0xFC (reg n') ∧
      (∀ x, Sep S 0xC0 x 1 → Sep (S + BitVec.ofNat 32 0xC4) 32 x 1 → n'.mem x = n.mem x) ∧
      accV n'.mem (S + BitVec.ofNat 32 0xC4) 8 < accV M0 p256Np 8 ∧
      accV n'.mem (S + BitVec.ofNat 32 0xC4) 8 * 2 ^ 256 % accV M0 p256Np 8 =
        accV n.mem (S + BitVec.ofNat 32 0x108) 8 * accV M0 (p256Np + 0x40) 8 % accV M0 p256Np 8 ∧
      reg n' sp = S + BitVec.ofNat 32 0xC0 ∧ reg n' (9 : Fin 32) = b &&& 1 ∧
      ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q := by
  have hSc : ∀ c, c ≤ 0x140 → (S + BitVec.ofNat 32 c).toNat = S.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x140 → d + k ≤ 0x140 →
      Sep (S + BitVec.ofNat 32 c) n (S + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets S h (by omega) (by omega)
  have inS : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x140 → Sep S 0x140 x 1 → Sep (S + BitVec.ofNat 32 c) l x 1 :=
    fun h hx => hx.sub h
  have hi : ∀ {c l : Nat} (b : Word) (k : Nat), c + l ≤ 0x140 → 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (S + BitVec.ofNat 32 c) l b k := fun b k h h1 h2 => sep_of_le (by rw [hSc _ (by omega)]; omega) h2
  have Shi : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep S 0x140 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hFRn : FRQ.toNat = (img% p256FromReprAddress) := by decide
  have cd : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep S 0x140 x 1 → M' x = M0 x) → CodeIn M' b code :=
    fun hc h1 h2 hM i hi => by rw [hM _ (Shi _ (code_hi h1 h2 hi))]; exact hc i hi
  have eF4 : S + BitVec.ofNat 32 0xC0 + 0xFFFFFFFC = S + BitVec.ofNat 32 0xBC := by rw [BitVec.add_assoc]; rfl
  have Gc : ∀ c, S + BitVec.ofNat 32 0xC0 + BitVec.ofNat 32 c = S + BitVec.ofNat 32 (0xC0 + c) :=
    fun c => add_ofNat_assoc _ _ _
  have hGa : (S + BitVec.ofNat 32 0xC0).toNat % 4 = 0 := aligned_add (by omega) (by decide)
  have hc0 := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) hf
  obtain ⟨n1, c1, u1⟩ := St.block frqT1 st hc0 frqT1_end (by
    simp only [BlockOk, BInstr.ok, frqT1]; exact ⟨trivial, trivial, trivial, trivial, trivial⟩)
  have R1 : ∀ q, reg n1 q = (runBlock frqT1 (n.mem, reg n)).2 q := u1.regs
  have u1' : St n.mem FRQ n1 0xBE (reg n1) := ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩
  have s01 : reg n1 (8 : Fin 32) = p256Np := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, frqT1, upd_app, ↓reduceIte]
  have K1 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ (8 : Fin 32) → reg n1 q = reg n q := fun q h0 h1 h8 => by
    rw [R1]; refine runBlock_reg _ _ _ q st.zero ?_
    simp only [frqT1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h8]
  have hsepZ : Sep (S + BitVec.ofNat 32 0xBC) 4 (BitVec.ofNat 32 uintRefIsNonzeroAddress)
      uintRefIsNonzeroCode.length := hi _ _ (by omega) (by decide) (by decide)
  obtain ⟨n2, c2, u2, a02, K2, mem2⟩ := u1'.nzCall0 (ptr := p256Np + 0x20) hc0 (cd E.nz (by decide) (by decide) hf) frq_at_be frq_at_c2
    (by decide) (by decide) (by rw [R1]; simp +decide only [runBlock, BInstr.run, frqT1, upd_app, ↓reduceIte])
    (by rw [R1]; simp +decide only [runBlock, BInstr.run, frqT1, upd_app, ↓reduceIte]) (by decide)
    (by rw [K1 sp (by decide) (by decide) (by decide), hsp]) hGa (by rw [eF4]; exact hsepZ)
  rw [eF4] at mem2
  have M2 : ∀ x, Sep S 0x140 x 1 → n2.mem x = M0 x := fun x hx => by
    rw [mem2 x (inS (by omega) hx), hf x hx]
  have hc2 := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) M2
  obtain ⟨n3, c3, u3⟩ := St.block frqT2 u2 hc2 frqT2_end (by
    simp only [BlockOk, BInstr.ok, frqT2]; exact ⟨trivial, trivial, trivial, trivial, trivial⟩)
  have R3 : ∀ q, reg n3 q = (runBlock frqT2 (n2.mem, reg n2)).2 q := u3.regs
  have u3' : St n2.mem FRQ n3 0xD0 (reg n3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  have r2 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → q ≠ (8 : Fin 32) → reg n2 q = reg n q :=
    fun q h0 h1 h2 h3 hr h8 => by rw [K2 q h0 h1 h2 h3 hr, K1 q h0 h1 h8]
  have sp2 : reg n2 sp = S + BitVec.ofNat 32 0xC0 := by
    rw [r2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsp]
  have K3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ (9 : Fin 32) → reg n3 q = reg n2 q := fun q h0 h1 h9 => by
    rw [R3]; refine runBlock_reg _ _ _ q u2.zero ?_
    simp only [frqT2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h9]
  obtain ⟨n4, c4, u4, a04, K4, mem4⟩ := u3'.nzCall0 (ptr := S + BitVec.ofNat 32 0x128) hc2 (cd E.nz (by decide) (by decide) M2) frq_at_d0 frq_at_d4
    (by decide) (by decide) (by
      rw [R3]; simp +decide only [runBlock, BInstr.run, frqT2, upd_app, ↓reduceIte]
      rw [sp2]; exact (BitVec.zero_add _).trans (Gc 0x68))
    (by rw [R3]; simp +decide only [runBlock, BInstr.run, frqT2, upd_app, ↓reduceIte])
    (aligned_add (by omega) (by decide))
    (by rw [K3 sp (by decide) (by decide) (by decide), sp2]) hGa (by rw [eF4]; exact hsepZ)
  rw [eF4] at mem4
  have M4 : ∀ x, Sep S 0x140 x 1 → n4.mem x = M0 x := fun x hx => by
    rw [mem4 x (inS (by omega) hx), M2 x hx]
  have hc4 := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) M4
  have s14 : reg n4 (9 : Fin 32) = 0 := by
    rw [K4 _ (by decide) (by decide) (by decide) (by decide) (by decide), R3]
    simp +decide only [runBlock, BInstr.run, frqT2, upd_app, ↓reduceIte]; rw [a02]; rfl
  have r4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) →
      reg n4 q = reg n q := fun q h0 h1 h2 h3 hr h8 h9 => by
    rw [K4 q h0 h1 h2 h3 hr, K3 q h0 h1 h9, r2 q h0 h1 h2 h3 hr h8]
  have sp4 : reg n4 sp = S + BitVec.ofNat 32 0xC0 := by
    rw [r4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsp]
  have s04 : reg n4 (8 : Fin 32) = p256Np := by
    rw [K4 _ (by decide) (by decide) (by decide) (by decide) (by decide), K3 _ (by decide) (by decide) (by decide),
      K2 _ (by decide) (by decide) (by decide) (by decide) (by decide), s01]
  obtain ⟨n5, c5, u5⟩ := St.block frqT3 u4 hc4 frqT3_end (by
    simp only [BlockOk, BInstr.ok, frqT3]
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩)
  have R5 : ∀ q, reg n5 q = (runBlock frqT3 (n4.mem, reg n4)).2 q := u5.regs
  have u5' : St n4.mem FRQ n5 0xF4 (reg n5) := ⟨u5.pc, by rw [u5.mem]; rfl, fun _ => rfl⟩
  have s15 : reg n5 (9 : Fin 32) = b &&& 1 := by
    rw [R5]; simp +decide only [runBlock, BInstr.run, frqT3, upd_app, ↓reduceIte]
    rw [s14, a04, r4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h19]
    show (0 : Word) ||| ((b &&& (((0 : Word) &&& 0xFF) ^^^ 0xFFFFFFFF)) &&& 1) = b &&& 1
    rw [show ((0 : Word) &&& 0xFF) ^^^ 0xFFFFFFFF = 0xFFFFFFFF by decide, and_ones]; exact BitVec.zero_or
  have K5 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (9 : Fin 32) → reg n5 q = reg n4 q :=
    fun q h0 h1 h2 h3 h4 h9 => by
      rw [R5]; refine runBlock_reg _ _ _ q u4.zero ?_
      simp only [frqT3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2, h3, h4, h9]
  have rv5 : reg n5 a0 = S + BitVec.ofNat 32 0xC4 ∧ reg n5 a1 = S + BitVec.ofNat 32 0x108 ∧
      reg n5 a2 = p256Np + 0x40 ∧ reg n5 a3 = p256Np ∧ reg n5 a4 = 1 := by
    simp only [R5]; simp +decide only [runBlock, BInstr.run, frqT3, upd_app, ↓reduceIte]
    rw [sp4, s04]
    exact ⟨Gc 4, Gc 0x48, rfl, BitVec.zero_add _, trivial⟩
  -- `mul_montgomery_form::<8>`
  obtain ⟨m6, c6, pc6, mem6, regs6⟩ := u5'.callRa hc4 frq_at_f4 frq_at_f8
    (show FRQ + BitVec.ofNat 32 0xF4 + 0xA000 + 0x25C = BitVec.ofNat 32 mulMont8Address by decide) (by decide)
  have r6 : ∀ q, q ≠ ra → reg m6 q = reg n5 q := PEnv.reg1 regs6 u5'.zero
  have M6 : ∀ x, Sep S 0x140 x 1 → m6.mem x = M0 x := fun x hx => by rw [mem6]; exact M4 x hx
  have eS : S + BitVec.ofNat 32 0xC0 + 0xFFFFFF40 = S := by rw [BitVec.add_assoc]; exact BitVec.add_zero S
  have o0 : ∀ {d k : Nat}, 0xC0 ≤ d → d + k ≤ 0x140 → Sep S 0xC0 (S + BitVec.ofNat 32 d) k := fun h1 h2 => by
    have := offs (c := 0) (n := 0xC0) (.inl h1) (by omega) h2; rwa [add_ofNat_zero] at this
  have h0hi : ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 → Sep S 0xC0 b k :=
    fun b k h1 h2 => by have := hi (c := 0) (l := 0xC0) b k (by omega) h1 h2; rwa [add_ofNat_zero] at this
  have sNS : Sep p256Np 32 S 0xC0 := by
    have := (sSN.symm.sub (c := 0) (l := 32) (by omega)).subR (c := 0) (l := 0xC0) (by omega)
    rwa [add_ofNat_zero, add_ofNat_zero] at this
  have sYS : Sep (p256Np + 0x40) 32 S 0xC0 := by
    have := (sSN.symm.sub (c := 0x40) (l := 32) (by omega)).subR (c := 0) (l := 0xC0) (by omega)
    rwa [add_ofNat_zero] at this
  have hP : BitVec.ofNat 32 mulMont12Address = BitVec.ofNat 32 mulMont12Address := rfl
  have EM : MMEnv8 m6.mem (BitVec.ofNat 32 mulMont8Address) (S + BitVec.ofNat 32 0xC0) (S + BitVec.ofNat 32 0xC4)
      (S + BitVec.ofNat 32 0x108) (p256Np + 0x40) p256Np := by
    refine ⟨by decide, cd E.mm (by decide) (by decide) M6,
      by rw [show BitVec.ofNat 32 mulMont8Address + 0x3CA8 = BitVec.ofNat 32 memsetAddress by decide]
         exact cd E.ms (by decide) (by decide) M6,
      by rw [show mmBsub8 (BitVec.ofNat 32 mulMont8Address) = BitVec.ofNat 32 borrowingSubAddress by decide]
         exact cd E.bs (by decide) (by decide) M6,
      by rw [show BitVec.ofNat 32 mulMont8Address + 0x18E = BitVec.ofNat 32 uintSelect8Address by decide]
         exact cd E.sel (by decide) (by decide) M6,
      by rw [show BitVec.ofNat 32 mulMont8Address + 0x3D10 = BitVec.ofNat 32 memcpyStubAddress by decide]
         exact cd E.cs (by decide) (by decide) M6,
      by rw [show BitVec.ofNat 32 mulMont8Address + 0x3D18 = BitVec.ofNat 32 memcpyStubAddress + 8 by decide]
         exact cd E.cb (by decide) (by decide) M6,
      hGa, by rw [hSc _ (by omega)]; omega, aligned_add (by omega) (by decide), aligned_add (by omega) (by decide),
      by decide, by decide, by rw [hSc _ (by omega)]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try rw [eS])
    all_goals first
      | exact h0hi _ _ (by decide) (by decide)
      | exact (o0 (by omega) (by omega)).symm
      | exact hi _ _ (by omega) (by decide) (by decide)
      | exact sYS
      | exact sNS
  obtain ⟨ha5, hb5, hc5, hd5, he5⟩ := rv5
  have NT : ∀ {M : Word → BitVec 8} {b : Word} {l : Nat}, (∀ x, Sep S 0x140 x 1 → M x = M0 x) →
      Sep S 0x140 b (4 * l) → accV M b l = accV M0 b l := fun hM hs =>
    accV_congr _ fun i hi => memLoad32_congr fun j hj => hM _ (hs.subR (c := 4 * i + j) (l := 1) (by omega)) |>
      fun h => by rw [← add_ofNat_assoc] at h; exact h
  have sNS' : Sep S 0x140 p256Np (4 * 8) := sSN.subR (c := 0) (l := 32) (by omega) |> fun h => by
    rwa [add_ofNat_zero] at h
  have sYS' : Sep S 0x140 (p256Np + 0x40) (4 * 8) := sSN.subR (c := 0x40) (l := 32) (by omega)
  obtain ⟨m7, c7, pc7, sp7, hlt7, heq7, fr7, K7⟩ := mulMont8_correct m6 (retAddr := FRQ + BitVec.ofNat 32 (0xF4 + 8)) EM pc6
    (by rw [r6 a0 (by decide), ha5]) (by rw [r6 a1 (by decide), hb5]) (by rw [r6 a2 (by decide), hc5])
    (by rw [r6 a3 (by decide), hd5]) (by rw [r6 a4 (by decide), he5])
    (by rw [regs6]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at FRQ (by decide) _ (by decide)))
    (by rw [r6 sp (by decide), K5 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp4])
    (by
      rw [load_frame (n := 0x140) (acc := S) (M0 := M0) M6 (sSN.subR (c := 0) (l := 4) (by omega) |> fun h => by
        rwa [add_ofNat_zero] at h), E.nlo]; decide)
    (by rw [NT M6 sYS', NT M6 sNS']; exact E.r2lt)
  rw [NT M6 sNS', NT M6 sYS'] at heq7
  rw [NT M6 sNS'] at hlt7
  rw [eS] at fr7
  have hX : accV m6.mem (S + BitVec.ofNat 32 0x108) 8 = accV n.mem (S + BitVec.ofNat 32 0x108) 8 := by
    rw [mem6]
    apply accV_congr; intro i hi; apply memLoad32_congr; intro j hj
    have hs : Sep (S + BitVec.ofNat 32 0xBC) 4 (S + BitVec.ofNat 32 0x108 + BitVec.ofNat 32 (4 * i) +
        BitVec.ofNat 32 j) 1 := by
      rw [add_ofNat_assoc, add_ofNat_assoc]; exact offs (by omega) (by omega) (by omega)
    rw [mem4 _ hs, mem2 _ hs]
  rw [hX] at heq7
  have u7 : St m7.mem FRQ m7 0xFC (reg m7) := ⟨by rw [pc7], rfl, fun _ => rfl⟩
  refine ⟨m7, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans c7))))), u7, fun x h1 h2 => ?_, hlt7,
    heq7, sp7, ?_, fun q hq => ?_⟩
  · rw [fr7 x h1 h2, mem6, mem4 x (h1.sub (c := 0xBC) (l := 4) (by omega)),
      mem2 x (h1.sub (c := 0xBC) (l := 4) (by omega))]
  · rw [K7 _ (by decide), r6 _ (by decide), s15]
  · have h' : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq ⊢; omega
    obtain ⟨h0, h1, h2, h3, h4, h9, hr, h8⟩ := (by decide : ∀ q : Fin 32,
      q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧
        q ≠ (9 : Fin 32) ∧ q ≠ ra ∧ q ≠ (8 : Fin 32)) q hq
    rw [K7 q h', r6 q hr, K5 q h0 h1 h2 h3 h4 h9, r4 q h0 h1 h2 h3 hr h8 h9]

def frqT5 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a0, .sb sp a0 0x24, .aluImm .add a0 sp 0x28, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0]
def frqT6 : List BInstr :=
  [.aluImm .and a3 (8 : Fin 32) 0xFF, .aluImm .add a1 sp 0x28, .aluImm .add a2 sp 4, .alu .add a0 x0 (18 : Fin 32)]

section
set_option maxRecDepth 20000
theorem frqT4_end : blockEnd p256FromReprCode 0xFC [.alu .add a0 x0 (9 : Fin 32)] = some 0xFE := by decide
theorem frqT5_end : blockEnd p256FromReprCode 0x106 frqT5 = some 0x114 := by decide
theorem frqT6_end : blockEnd p256FromReprCode 0x11C frqT6 = some 0x126 := by decide
theorem frqRestore_end : blockEnd p256FromReprCode 0x132 (restoreBlock frqPs) = some 0x13E := by decide
end

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- From 0xFC to the return: `black_box` passes the choice `c` through,
`conditional_select` writes to `out` the limbs at `T = S + 0xC4` when `c` is
1 and the zeros that `memset` put at `S + 0xE8` when it is 0, the choice
goes in the byte after them, and the epilogue restores the saved registers
and returns. -/
theorem frq_tailB {M0 : Word → BitVec 8} (E : FRQEnv M0) (n : Machine) {S out c : Word}
    (st : St n.mem FRQ n 0xFC (reg n)) (hf : ∀ x, Sep S 0x140 x 1 → n.mem x = M0 x)
    (hSa : S.toNat % 16 = 0) (hSw : S.toNat + 0x140 ≤ 0x40000000) (how : out.toNat + 33 ≤ 0x40000000)
    (sOS : Sep out 33 S 0x140) (hsp : reg n sp = S + BitVec.ofNat 32 0xC0) (h9 : reg n (9 : Fin 32) = c)
    (hc : c = 0 ∨ c = 1) (h18 : reg n (18 : Fin 32) = out)
    (hret : memLoad32 n.mem (S + BitVec.ofNat 32 0xC0 + 0x7C) &&& ~~~1 =
      memLoad32 n.mem (S + BitVec.ofNat 32 0xC0 + 0x7C)) :
    ∃ n', Steps n n' ∧ n'.pc = memLoad32 n.mem (S + BitVec.ofNat 32 0xC0 + 0x7C) ∧
      reg n' sp = S + BitVec.ofNat 32 0x140 ∧
      (∀ r o, (r, o) ∈ frqPs → reg n' r = memLoad32 n.mem (S + BitVec.ofNat 32 0xC0 + o)) ∧
      (∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (∀ i, i < 8 → memLoad32 n'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 n.mem (S + BitVec.ofNat 32 0xC4 + BitVec.ofNat 32 (4 * i)) else 0) ∧
      n'.mem (out + 0x20) = c.extractLsb' 0 8 ∧
      ∀ x, Sep S 0x140 x 1 → Sep out 33 x 1 → n'.mem x = n.mem x := by
  have hSc : ∀ c, c ≤ 0x140 → (S + BitVec.ofNat 32 c).toNat = S.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x140 → d + k ≤ 0x140 →
      Sep (S + BitVec.ofNat 32 c) n (S + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets S h (by omega) (by omega)
  have inS : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x140 → Sep S 0x140 x 1 → Sep (S + BitVec.ofNat 32 c) l x 1 :=
    fun h hx => hx.sub h
  have hi : ∀ {c l : Nat} (b : Word) (k : Nat), c + l ≤ 0x140 → 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (S + BitVec.ofNat 32 c) l b k := fun b k h h1 h2 => sep_of_le (by rw [hSc _ (by omega)]; omega) h2
  have ohi : ∀ {c l : Nat} (b : Word) (k : Nat), c + l ≤ 33 → 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (out + BitVec.ofNat 32 c) l b k := fun b k h h1 h2 =>
    sep_of_le (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) h2
  have Shi : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep S 0x140 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have Ohi : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep out 33 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hFRn : FRQ.toNat = (img% p256FromReprAddress) := by decide
  have cd : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep S 0x140 x 1 → Sep out 33 x 1 → M' x = M0 x) → CodeIn M' b code :=
    fun hc h1 h2 hM i hi => by rw [hM _ (Shi _ (code_hi h1 h2 hi)) (Ohi _ (code_hi h1 h2 hi))]; exact hc i hi
  have Gc : ∀ c, S + BitVec.ofNat 32 0xC0 + BitVec.ofNat 32 c = S + BitVec.ofNat 32 (0xC0 + c) :=
    fun c => add_ofNat_assoc _ _ _
  have hGa : (S + BitVec.ofNat 32 0xC0).toNat % 4 = 0 := aligned_add (by omega) (by decide)
  have hf' : ∀ x, Sep S 0x140 x 1 → Sep out 33 x 1 → n.mem x = M0 x := fun x hx _ => hf x hx
  have hc0 := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) hf'
  obtain ⟨n1, c1, u1⟩ := St.block [.alu .add a0 x0 (9 : Fin 32)] st hc0 frqT4_end (by
    simp only [BlockOk, BInstr.ok]; exact ⟨trivial, trivial⟩)
  have u1' : St n.mem FRQ n1 0xFE (reg n1) := ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩
  have R1 : ∀ q, reg n1 q = (runBlock [.alu .add a0 x0 (9 : Fin 32)] (n.mem, reg n)).2 q := u1.regs
  have K1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q h0 => by
    rw [R1]; refine runBlock_reg _ _ _ q st.zero ?_
    simp only [List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0]
  -- `black_box`
  obtain ⟨m2, c2, pc2, mem2, regs2⟩ := u1'.callRa hc0 frq_at_fe frq_at_102
    (show FRQ + BitVec.ofNat 32 0xFE + 0x7000 + 0xFFFFFE58 = BitVec.ofNat 32 blackBoxU8Address by decide) (by decide)
  have r2 : ∀ q, q ≠ ra → reg m2 q = reg n1 q := PEnv.reg1 regs2 u1'.zero
  have sp2 : reg m2 sp = S + BitVec.ofNat 32 0xC0 := by rw [r2 sp (by decide), K1 sp (by decide), hsp]
  have eB : S + BitVec.ofNat 32 0xC0 + 0xFFFFFFFF = S + BitVec.ofNat 32 0xBF := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m3, c3, pc3, a03, K3, mem3⟩ := blackBoxU8_correct m2 (retAddr := FRQ + BitVec.ofNat 32 (0xFE + 8))
    (by rw [mem2]; exact cd E.bb (by decide) (by decide) hf') pc2
    (by rw [regs2]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at FRQ (by decide) _ (by decide)))
    (by rw [sp2, eB]; exact hi _ _ (by omega) (by decide) (by decide))
  rw [sp2, eB, mem2] at mem3
  rw [r2 a0 (by decide), R1] at a03
  simp only [runBlock, BInstr.run] at a03
  have a03' : reg m3 a0 = c := by
    rw [a03]; simp +decide only [upd_app, ↓reduceIte]; rw [h9]
    exact (congrArg (fun w => (w.extractLsb' 0 8).zeroExtend 32) (BitVec.zero_add c)).trans (frp_c8 hc)
  have M3 : ∀ x, Sep S 0x140 x 1 → Sep out 33 x 1 → m3.mem x = M0 x := fun x hx ho => by
    rw [mem3 x (inS (by omega) hx), hf x hx]
  have hc3 := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) M3
  have u3 : St m3.mem FRQ m3 0x106 (reg m3) := ⟨by rw [pc3], rfl, fun _ => rfl⟩
  have r3 : ∀ q, q ≠ a0 → q ≠ ra → reg m3 q = reg n q := fun q h0 hr => by
    rw [K3 q h0, r2 q hr, K1 q h0]
  have sp3 : reg m3 sp = S + BitVec.ofNat 32 0xC0 := by rw [r3 sp (by decide) (by decide), hsp]
  have e34 : S + BitVec.ofNat 32 0xC0 + 0x24 = S + BitVec.ofNat 32 0xE4 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n4, c4, u4⟩ := St.block frqT5 u3 hc3 frqT5_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, frqT5, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp3, e34]; exact hi _ _ (by omega) (by rw [hFRn]; decide) (by decide))
  have R4 : ∀ q, reg n4 q = (runBlock frqT5 (m3.mem, reg m3)).2 q := u4.regs
  have M4e : (runBlock frqT5 (m3.mem, reg m3)).1 = memStore8 m3.mem (S + BitVec.ofNat 32 0xE4) (c.extractLsb' 0 8) := by
    simp +decide only [runBlock, BInstr.run, frqT5, upd_app, ↓reduceIte]; rw [sp3, e34, a03']
  obtain ⟨M4, hM4⟩ : ∃ M4, memStore8 m3.mem (S + BitVec.ofNat 32 0xE4) (c.extractLsb' 0 8) = M4 := ⟨_, rfl⟩
  rw [hM4] at M4e
  have u4' : St M4 FRQ n4 0x114 (reg n4) := ⟨u4.pc, by rw [u4.mem, M4e], fun _ => rfl⟩
  have M4o : ∀ x, Sep (S + BitVec.ofNat 32 0xE4) 1 x 1 → M4 x = m3.mem x := fun x hx => by
    rw [← hM4, memStore8_ne (sep1_ne hx)]
  have hc4 : CodeIn M4 FRQ p256FromReprCode := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide)
    fun x hx ho => by rw [M4o x (inS (by omega) hx), M3 x hx ho]
  have K4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (8 : Fin 32) → reg n4 q = reg m3 q := fun q h0 h1 h2 h8 => by
    rw [R4]; refine runBlock_reg _ _ _ q u3.zero ?_
    simp only [frqT5, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2, h8]
  have s04 : reg n4 (8 : Fin 32) = c := by
    rw [R4]; simp +decide only [runBlock, BInstr.run, frqT5, upd_app, ↓reduceIte]; rw [a03']; exact BitVec.zero_add _
  have sp4 : reg n4 sp = S + BitVec.ofNat 32 0xC0 := by
    rw [K4 sp (by decide) (by decide) (by decide) (by decide), sp3]
  obtain ⟨n5, c5, u5, _, K5⟩ := u4'.memsetW (B := BitVec.ofNat 32 memsetAddress) (w := 8)
    (dst := S + BitVec.ofNat 32 0xE8) (by decide) hc4
    (cd (M' := M4) E.ms (by decide) (by decide) fun x hx ho => by rw [M4o x (inS (by omega) hx), M3 x hx ho])
    frq_at_114 frq_at_118 (by decide) (by decide) (by decide) (by rw [hSc _ (by omega)]; omega) (by decide)
    (aligned_add (by omega) (by decide)) (hi _ _ (by omega) (by decide) (by decide))
    (by rw [R4]; simp +decide only [runBlock, BInstr.run, frqT5, upd_app, ↓reduceIte]; rw [sp3]; exact Gc 0x28)
    (by rw [R4]; simp +decide only [runBlock, BInstr.run, frqT5, upd_app, ↓reduceIte])
    (by rw [R4]; simp +decide only [runBlock, BInstr.run, frqT5, upd_app, ↓reduceIte])
  obtain ⟨M5, hM5⟩ : ∃ M5, fillWords M4 (S + BitVec.ofNat 32 0xE8) 0 8 = M5 := ⟨_, rfl⟩
  rw [hM5] at u5
  have M5o : ∀ x, Sep (S + BitVec.ofNat 32 0xE8) 32 x 1 → M5 x = M4 x := fun x hx => by
    rw [← hM5]; exact fillWords_outside 8 hx
  have M5' : ∀ x, Sep S 0x140 x 1 → Sep out 33 x 1 → M5 x = M0 x := fun x hx ho => by
    rw [M5o x (inS (by omega) hx), M4o x (inS (by omega) hx), M3 x hx ho]
  have hc5 := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) M5'
  have r5 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ a0 → q ≠ a1 → q ≠ (8 : Fin 32) →
      reg n5 q = reg n q := fun q h2 h3 h4 h5 h6 hr h0 h1 h8 => by
    rw [K5 q h2 h3 h4 h5 h6 hr, K4 q h0 h1 h2 h8, r3 q h0 hr]
  have sp5 : reg n5 sp = S + BitVec.ofNat 32 0xC0 := by
    rw [r5 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hsp]
  obtain ⟨n6, c6, u6⟩ := St.block frqT6 u5 hc5 frqT6_end (by
    simp only [BlockOk, BInstr.ok, frqT6]; exact ⟨trivial, trivial, trivial, trivial, trivial⟩)
  have R6 : ∀ q, reg n6 q = (runBlock frqT6 (M5, reg n5)).2 q := u6.regs
  have u6' : St M5 FRQ n6 0x126 (reg n6) := ⟨u6.pc, by rw [u6.mem]; rfl, fun _ => rfl⟩
  have K6 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg n6 q = reg n5 q := fun q h0 h1 h2 h3 => by
    rw [R6]; refine runBlock_reg _ _ _ q u5.zero ?_
    simp only [frqT6, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2, h3]
  have rv6 : reg n6 a0 = out ∧ reg n6 a1 = S + BitVec.ofNat 32 0xE8 ∧ reg n6 a2 = S + BitVec.ofNat 32 0xC4 ∧
      reg n6 a3 = c := by
    simp only [R6]; simp +decide only [runBlock, BInstr.run, frqT6, upd_app, ↓reduceIte]
    rw [sp5, r5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h18, K5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s04]
    refine ⟨BitVec.zero_add _, Gc 0x28, Gc 4, ?_⟩
    rcases hc with rfl | rfl <;> decide
  obtain ⟨ha6, hb6, hc6, hd6⟩ := rv6
  -- `conditional_select`
  obtain ⟨m7, c7, pc7, mem7, regs7⟩ := u6'.callRa hc5 frq_at_126 frq_at_12a
    (show FRQ + BitVec.ofNat 32 0x126 + 0xB000 + 0xFFFFFCFC = BitVec.ofNat 32 condSelect256Address by decide)
    (by decide)
  have r7 : ∀ q, q ≠ ra → reg m7 q = reg n6 q := PEnv.reg1 regs7 u6'.zero
  have M7 : ∀ x, Sep S 0x140 x 1 → Sep out 33 x 1 → m7.mem x = M0 x := fun x hx ho => by rw [mem7]; exact M5' x hx ho
  have eC : S + BitVec.ofNat 32 0xC0 + 0xFFFFFFB0 = S + BitVec.ofNat 32 0x70 := by rw [BitVec.add_assoc]; rfl
  have oS : ∀ {c l : Nat} {d k : Nat}, c + l ≤ 33 → d + k ≤ 0x140 → Sep (out + BitVec.ofNat 32 c) l
      (S + BitVec.ofNat 32 d) k := fun h1 h2 => (sOS.sub (c := _) (l := _) h1).subR h2
  have oS0 : ∀ {d k : Nat}, d + k ≤ 0x140 → Sep out 32 (S + BitVec.ofNat 32 d) k := fun h => by
    have := oS (c := 0) (l := 32) (by omega) h; rwa [add_ofNat_zero] at this
  have ohi0 : ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 → Sep out 32 b k := fun b k h1 h2 => by
    have := ohi (c := 0) (l := 32) b k (by omega) h1 h2; rwa [add_ofNat_zero] at this
  have EC : CS2Env m7.mem (BitVec.ofNat 32 condSelect256Address) (S + BitVec.ofNat 32 0xC0) out
      (S + BitVec.ofNat 32 0xE8) (S + BitVec.ofNat 32 0xC4) := by
    refine ⟨by decide, cd E.csel (by decide) (by decide) M7,
      by rw [show BitVec.ofNat 32 condSelect256Address + 0x323E = BitVec.ofNat 32 memcpyStubAddress by decide]
         exact cd E.cs (by decide) (by decide) M7,
      by rw [show BitVec.ofNat 32 condSelect256Address + 0x323E + 8 = BitVec.ofNat 32 memcpyStubAddress + 8 by decide]
         exact cd E.cb (by decide) (by decide) M7,
      by rw [show BitVec.ofNat 32 condSelect256Address + 0xFFFFC076 = BitVec.ofNat 32 sliceCtAssignAddress by decide]
         exact cd E.sca (by decide) (by decide) M7,
      hGa, by rw [hSc _ (by omega)]; omega, aligned_add (by omega) (by decide), by rw [hSc _ (by omega)]; omega,
      by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try rw [eC])
    all_goals first
      | exact hi _ _ (by omega) (by decide) (by decide)
      | exact ohi0 _ _ (by decide) (by decide)
      | exact oS0 (by omega)
      | exact offs (by omega) (by omega) (by omega)
  obtain ⟨m8, c8, pc8, sp8, w8, K8, fr8⟩ := condSelect256_correct m7 (retAddr := FRQ + BitVec.ofNat 32 (0x126 + 8))
    EC pc7 (by rw [r7 sp (by decide), K6 sp (by decide) (by decide) (by decide) (by decide), sp5])
    (by rw [r7 a0 (by decide), ha6]) (by rw [r7 a1 (by decide), hb6]) (by rw [r7 a2 (by decide), hc6])
    (by rw [r7 a3 (by decide), hd6]) hc (by rw [regs7]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at FRQ (by decide) _ (by decide)))
  rw [eC, mem7] at fr8
  rw [mem7] at w8
  have hc8 : CodeIn m8.mem FRQ p256FromReprCode := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide)
    fun x hx ho => by rw [fr8 x (inS (by omega) hx) (ho.sub (c := 0) (l := 32) (by omega) |> fun h => by
      rwa [add_ofNat_zero] at h), M5' x hx ho]
  have u8 : St m8.mem FRQ m8 0x12E (reg m8) := ⟨by rw [pc8], rfl, fun _ => rfl⟩
  have r8 : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m8 q = reg n6 q := fun q hq => by
    rw [K8 q (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq ⊢; omega), r7 q (by
      intro h; subst h; simp at hq)]
  obtain ⟨m9, d9, u9⟩ := u8.sb hc8 frq_at_12e (off' := 0x132) (by decide)
  have e9 : reg m8 (18 : Fin 32) + 0x20 = out + BitVec.ofNat 32 0x20 := by
    rw [r8 _ (by decide), K6 _ (by decide) (by decide) (by decide) (by decide),
      r5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h18]; rfl
  have c9 : (reg m8 (8 : Fin 32)).extractLsb' 0 8 = c.extractLsb' 0 8 := by
    rw [r8 _ (by decide), K6 _ (by decide) (by decide) (by decide) (by decide),
      K5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s04]
  rw [e9, c9] at u9
  obtain ⟨M9, hM9⟩ : ∃ M9, memStore8 m8.mem (out + BitVec.ofNat 32 0x20) (c.extractLsb' 0 8) = M9 := ⟨_, rfl⟩
  rw [hM9] at u9
  have o30 : ∀ x, Sep (out + BitVec.ofNat 32 0x20) 1 x 1 → M9 x = m8.mem x := fun x hx => by
    rw [← hM9, memStore8_ne (sep1_ne hx)]
  -- what the writes since 0xFE leave alone
  have ag9 : ∀ x, Sep (S + BitVec.ofNat 32 0x70) 0x98 x 1 → Sep out 33 x 1 → M9 x = n.mem x := fun x hx ho => by
    rw [o30 x (ho.sub (c := 0x20) (l := 1) (by omega)),
      fr8 x (hx.sub (c := 0) (l := 0x50) (by omega) |> fun h => by rwa [add_ofNat_zero] at h)
        (ho.sub (c := 0) (l := 32) (by omega) |> fun h => by rwa [add_ofNat_zero] at h),
      M5o x (by have := hx.sub (c := 0x78) (l := 32) (by omega); rwa [add_ofNat_assoc] at this),
      M4o x (by have := hx.sub (c := 0x74) (l := 1) (by omega); rwa [add_ofNat_assoc] at this),
      mem3 x (by have := hx.sub (c := 0x4F) (l := 1) (by omega); rwa [add_ofNat_assoc] at this)]
  have hc9 : CodeIn M9 FRQ p256FromReprCode := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide)
    fun x hx ho => by rw [ag9 x (inS (by omega) hx) ho, hf x hx]
  have slot : ∀ o : Word, 0x68 ≤ o.toNat → o.toNat + 4 ≤ 0x80 → memLoad32 M9 (S + BitVec.ofNat 32 0xC0 + o) =
      memLoad32 n.mem (S + BitVec.ofNat 32 0xC0 + o) := fun o hb1 hb2 => by
    have e : S + BitVec.ofNat 32 0xC0 + o = S + BitVec.ofNat 32 (0xC0 + o.toNat) := by rw [← Gc, ofNat_toNat_self]
    rw [e]
    apply memLoad32_congr; intro j hj
    rw [add_ofNat_assoc]
    exact ag9 _ (offs (by omega) (by omega) (by omega))
      (oS (c := 0) (l := 33) (d := 0xC0 + o.toNat + j) (k := 1) (by omega) (by omega) |>
        fun h => by rw [add_ofNat_zero] at h; exact h)
  have sp9 : reg m8 sp = S + BitVec.ofNat 32 0xC0 := sp8
  have hpsp : ∀ p ∈ frqPs, p.1 ≠ sp := by decide
  obtain ⟨n10, c10, u10⟩ := St.block (restoreBlock frqPs) u9 hc9 frqRestore_end
    (restoreBlock_ok M9 (S + BitVec.ofNat 32 0xC0) frqPs (reg m8) sp9 hpsp fun q hq => by
      simp only [frqPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hGa (by decide))
  simp only [restoreBlock_run M9 (S + BitVec.ofNat 32 0xC0) frqPs (reg m8) sp9 hpsp] at u10
  have rsp : restoreRegs M9 (S + BitVec.ofNat 32 0xC0) (reg m8) frqPs sp = S + BitVec.ofNat 32 0xC0 := by
    rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp9
  obtain ⟨n11, d11, u11⟩ := u10.aluImm hc9 frq_at_13e (off' := 0x140) (by decide)
  obtain ⟨n12, d12, pc12, mem12, regs12⟩ := u11.jalr hc9 frq_at_140
  have rra : restoreRegs M9 (S + BitVec.ofNat 32 0xC0) (reg m8) frqPs ra =
      memLoad32 n.mem (S + BitVec.ofNat 32 0xC0 + 0x7C) := by
    simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
    exact slot _ (by decide) (by decide)
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs M9 (S + BitVec.ofNat 32 0xC0) f ps q = f q := by
    intro f ps q hq0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
  refine ⟨n12, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (.cons d9
    (c10.trans (.cons d11 (.single d12))))))))))), ?_, ?_, fun r o hm => ?_, fun q hq => ?_, fun i hi => ?_, ?_,
    fun x hx ho => ?_⟩
  · rw [pc12]; simp +decide only [upd, ↓reduceIte]; rw [rra, add_lit_zero, hret]
  · rw [regs12]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [rsp, BitVec.add_assoc]; rfl
  · rw [regs12]
    simp only [frqPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
      exact slot _ (by decide) (by decide)
  · obtain ⟨h0, hsp', hps, h0', h1, h2, h3, h4, h5, h6, hr, h8⟩ := (by decide : ∀ q : Fin 32,
      q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ frqPs, p.1 ≠ q) ∧ q ≠ a0 ∧ q ≠ a1 ∧
        q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ ra ∧ q ≠ (8 : Fin 32)) q hq
    rw [regs12, upd_ne h0 hsp', rr _ _ q h0 hps,
      r8 q (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq ⊢; omega), K6 q h0' h1 h2 h3,
      r5 q h2 h3 h4 h5 h6 hr h0' h1 h8]
  · rw [mem12, ← hM9, memLoad32_congr (M := m8.mem) fun j hj => memStore8_ne (sep1_ne (by
        rw [add_ofNat_assoc]
        exact sep_offsets out (c := 0x20) (n := 1) (d := 4 * i + j) (k := 1) (by omega) (by omega) (by omega))),
      w8 i hi]
    by_cases h1 : c = 1
    · rw [ite_eq_left h1, ite_eq_left h1]
      apply memLoad32_congr; intro j hj; rw [add_ofNat_assoc, add_ofNat_assoc]
      have hT : Sep (S + BitVec.ofNat 32 0xE8) 32 (S + BitVec.ofNat 32 (0xC4 + (4 * i + j))) 1 :=
        offs (by omega) (by omega) (by omega)
      rw [M5o _ hT, M4o _ (offs (by omega) (by omega) (by omega)), mem3 _ (offs (by omega) (by omega) (by omega))]
    · rw [ite_eq_right h1, ite_eq_right h1, ← hM5]
      exact fillWords_load 8 i hi (by rw [hSc _ (by omega)]; omega)
  · rw [mem12, ← hM9]; exact memStore8_same _ _ _
  · rw [mem12, ag9 x (inS (by omega) hx) ho]

def frqCmp0 : List BInstr :=
  [.aluImm .add (19 : Fin 32) x0 0, .aluImm .add (20 : Fin 32) sp 0x48, .lui (9 : Fin 32) 0x3FCC5000,
   .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFB38, .aluImm .add (8 : Fin 32) x0 8]

section
set_option maxRecDepth 20000
theorem frqCmp0_end : blockEnd p256FromReprCode 0x84 frqCmp0 = some 0x94 := by decide
end

set_option exponentiation.threshold 400 in
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- **The compiled `<p256 FieldElement as PrimeField>::from_repr`.** For the
32 bytes at `inp`, read as a big-endian number `x`, and the field modulus `p`
that the image keeps at `p256Np`: when `x < p` it writes to `out` the limbs
of the number `r < p` with `r · 2^256 ≡ x · R2 (mod p)`, where `R2` is the
number the image keeps 0x40 bytes past the modulus, and 1 to the byte after
them; otherwise it writes zero limbs and a 0 byte. It returns with `sp` and
the callee-saved registers restored and writes only `out` and the 0x140
bytes of stack below `sp`. -/
theorem p256FromRepr_correct (m : Machine) {sp0 out inp retAddr : Word} (E : FRQEnv m.mem)
    (hpc : m.pc = FRQ) (ha0 : reg m a0 = out) (ha1 : reg m a1 = inp) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) (hsp16 : sp0.toNat % 16 = 0)
    (hspl : 0x140 ≤ sp0.toNat) (hspw : sp0.toNat ≤ 0x40000000) (how : out.toNat + 33 ≤ 0x40000000)
    (sOS : Sep out 33 (sp0 + 0xFFFFFEC0) 0x140) (sIS : Sep inp 32 (sp0 + 0xFFFFFEC0) 0x140)
    (sSN : Sep (sp0 + 0xFFFFFEC0) 0x140 p256Np 0x60) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (beNat (memBytes m.mem inp 32) < accV m.mem p256Np 8 →
        m'.mem (out + 0x20) = 1 ∧ accV m'.mem out 8 < accV m.mem p256Np 8 ∧
        accV m'.mem out 8 * 2 ^ 256 % accV m.mem p256Np 8 =
          beNat (memBytes m.mem inp 32) * accV m.mem (p256Np + 0x40) 8 % accV m.mem p256Np 8) ∧
      (accV m.mem p256Np 8 ≤ beNat (memBytes m.mem inp 32) → m'.mem (out + 0x20) = 0 ∧ accV m'.mem out 8 = 0) ∧
      ∀ x, Sep (sp0 + 0xFFFFFEC0) 0x140 x 1 → Sep out 33 x 1 → m'.mem x = m.mem x := by
  obtain ⟨n1, M1, Ms, c1, u1, M1o, V1, slots, sp1, a01, s01, a61, a11, h191, s21, k1⟩ :=
    frq_pro m E.fr E.za E.cs E.cb E.ms hpc ha0 ha1 hsp hsp16 hspl hspw
  obtain ⟨hSn, hGS⟩ := frq_S sp0 hspl
  obtain ⟨S, hS⟩ : ∃ S, sp0 + 0xFFFFFEC0 = S := ⟨_, rfl⟩
  rw [hS] at hSn hGS M1o V1 sOS sIS sSN h191 ⊢
  rw [hGS] at slots sp1
  have hSa : S.toNat % 16 = 0 := by omega
  have hSw : S.toNat + 0x140 ≤ 0x40000000 := by omega
  have hSc : ∀ c, c ≤ 0x140 → (S + BitVec.ofNat 32 c).toNat = S.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x140 → d + k ≤ 0x140 →
      Sep (S + BitVec.ofNat 32 c) n (S + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets S h (by omega) (by omega)
  have inS : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x140 → Sep S 0x140 x 1 → Sep (S + BitVec.ofNat 32 c) l x 1 :=
    fun h hx => hx.sub h
  have hi : ∀ {c l : Nat} (b : Word) (k : Nat), c + l ≤ 0x140 → 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (S + BitVec.ofNat 32 c) l b k := fun b k h h1 h2 => sep_of_le (by rw [hSc _ (by omega)]; omega) h2
  have Shi : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep S 0x140 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hFRn : FRQ.toNat = (img% p256FromReprAddress) := by decide
  have Gc : ∀ c, S + BitVec.ofNat 32 0xC0 + BitVec.ofNat 32 c = S + BitVec.ofNat 32 (0xC0 + c) :=
    fun c => add_ofNat_assoc _ _ _
  have cdx : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → (∀ x, 0x40000000 ≤ x.toNat → M' x = m.mem x) → CodeIn M' b code :=
    fun hc h1 h2 hM i hi => by rw [hM _ (code_hi h1 h2 hi)]; exact hc i hi
  have iS : ∀ {c : Nat}, c + 1 ≤ 32 → Sep S 0x140 (inp + BitVec.ofNat 32 c) 1 := fun h => (sIS.sub h).symm
  -- the byte loop
  obtain ⟨n2, M2, c2, u2, M2o, hl2, k2⟩ := frq_outer (Mb := M1) (inp := inp) (T := S + BitVec.ofNat 32 0xC4)
    (X := S + BitVec.ofNat 32 0x108) (G := S + BitVec.ofNat 32 0xC0)
    (fun Mx hMx => cdx E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) fun x hx => by
      rw [hMx x (hi (c := 0xC4) (l := 4) x 1 (by omega) hx (by have := x.isLt; omega))
        (hi (c := 0x108) (l := 32) x 1 (by omega) hx (by have := x.isLt; omega)), M1o x (Shi x hx)])
    (Gc 4) (sIS.subR (by omega)) (sIS.subR (by omega)) (offs (by omega) (by omega) (by omega))
    (by rw [hSc _ (by omega)]; omega) (by rw [hSc _ (by omega)]; omega) (aligned_add (by omega) (by decide))
    (aligned_add (by omega) (by decide)) 8 0 n1 M1 (by omega) (by omega) u1 (fun _ _ _ => rfl)
    (fun _ h => absurd h (Nat.not_lt_zero _)) a01 s01 sp1 a61 a11 h191
  have M2m : ∀ x, Sep S 0x140 x 1 → M2 x = m.mem x := fun x hx => by
    rw [M2o x (inS (by omega) hx) (inS (by omega) hx), M1o x hx]
  have M2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M2 x = m.mem x := fun x hx => M2m x (Shi x hx)
  have hc2 : CodeIn M2 FRQ p256FromReprCode := cdx E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) M2hi
  -- set up the comparison
  obtain ⟨n3, c3, u3⟩ := St.block frqCmp0 u2 hc2 frqCmp0_end (by
    simp only [BlockOk, BInstr.ok, frqCmp0]; exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩)
  have R3 : ∀ q, reg n3 q = (runBlock frqCmp0 (M2, reg n2)).2 q := u3.regs
  have u3' : St M2 FRQ n3 0x94 (reg n3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  have r2 : ∀ q, q ≠ a0 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) →
      reg n2 q = reg n1 q := k2
  have sp2 : reg n2 sp = S + BitVec.ofNat 32 0xC0 := by
    rw [r2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp1]
  have K3 : ∀ q, q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) → reg n3 q = reg n2 q :=
    fun q h8 h9 h19 h20 => by
      rw [R3]; refine runBlock_reg _ _ _ q u2.zero ?_
      simp only [frqCmp0, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h8, h9, h19, h20]
  have s03 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 8 := by
    rw [R3]; simp +decide only [runBlock, BInstr.run, frqCmp0, upd_app, ↓reduceIte]
  obtain ⟨n3', d3, u3''⟩ := u3'.notTaken hc2 0x96 frq_at_94 (by decide) (by
    simp only [branchTaken]; rw [s03, u3'.zero]; decide)
  have eF4 : S + BitVec.ofNat 32 0xC0 + 0xFFFFFFFC = S + BitVec.ofNat 32 0xBC := by rw [BitVec.add_assoc]; rfl
  have sNS : Sep p256Np 32 S 0x140 := sSN.symm.sub (c := 0) (l := 32) (by omega) |> fun h => by
    rwa [add_ofNat_zero] at h
  obtain ⟨n4, M4, b', c4, u4, M4o, hb4, hbm4, ⟨D, hD, hinv⟩, k4⟩ := frq_cmp (Mb := M2) (X := S + BitVec.ofNat 32 0x108)
    (N := p256Np) (G := S + BitVec.ofNat 32 0xC0)
    (fun Mx hMx => cdx E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) fun x hx => by
      rw [hMx x (by rw [eF4]; exact hi (c := 0xBC) (l := 4) x 1 (by omega) hx (by have := x.isLt; omega)), M2hi x hx])
    (fun Mx hMx => cdx E.bs (by decide) (by decide) fun x hx => by
      rw [hMx x (by rw [eF4]; exact hi (c := 0xBC) (l := 4) x 1 (by omega) hx (by have := x.isLt; omega)), M2hi x hx])
    (aligned_add (by omega) (by decide)) (by rw [hSc _ (by omega)]; omega) (by rw [hSc _ (by omega)]; omega)
    (aligned_add (by omega) (by decide)) (by decide) (by rw [eF4]; exact offs (by omega) (by omega) (by omega))
    (by rw [eF4]; exact sNS.subR (by omega))
    8 0 n3' M2 0 (by omega) (by omega) u3''.self (fun _ _ => rfl)
    (by rw [u3''.regs, R3]; simp +decide only [runBlock, BInstr.run, frqCmp0, upd_app, ↓reduceIte]; rw [u2.zero]; rfl)
    (.inl rfl)
    ⟨0, Nat.one_pos, by show 0 + 0 = 0 + 1 * maskBit 0; rfl⟩
    (by rw [u3''.regs, R3]; simp +decide only [runBlock, BInstr.run, frqCmp0, upd_app, ↓reduceIte]; rw [sp2]
        exact (Gc 0x48).trans (by rw [add_ofNat_zero]))
    (by rw [u3''.regs, R3]; simp +decide only [runBlock, BInstr.run, frqCmp0, upd_app, ↓reduceIte])
    (by rw [u3''.regs, s03])
    (by rw [u3''.regs, K3 sp (by decide) (by decide) (by decide) (by decide), sp2])
  have e4 : n4.mem = M4 := u4.mem
  subst e4
  rw [eF4] at M4o
  have u4' : St n4.mem FRQ n4 0xB0 (reg n4) := u4
  have M4m : ∀ x, Sep S 0x140 x 1 → n4.mem x = m.mem x := fun x hx => by
    rw [M4o x (inS (by omega) hx), M2m x hx]
  have r4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) →
      q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ a5 → reg n4 q = reg n1 q :=
    fun q h0 h1 h2 h3 h4 hr h8 h9 h19 h20 h5 => by
      rw [k4 q h0 h1 h2 h3 h4 hr h8 h9 h19 h20, u3''.regs, K3 q h8 h9 h19 h20, r2 q h0 h2 h3 h4 h5 h8 h9]
  have sp4 : reg n4 sp = S + BitVec.ofNat 32 0xC0 := by
    rw [r4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), sp1]
  -- `is_nonzero`, `is_nonzero`, and the Montgomery multiplication
  obtain ⟨n5, c5, u5, fr5, lt5, eq5, sp5, s15, k5⟩ := frq_tailA E n4 u4' M4m hSa hSw sSN sp4 hb4
  have M5m : ∀ x, Sep S 0x140 x 1 → n5.mem x = m.mem x := fun x hx => by
    rw [fr5 x (by have := hx.sub (c := 0) (l := 0xC0) (by omega); rwa [add_ofNat_zero] at this) (inS (by omega) hx),
      M4m x hx]
  -- the slots the epilogue reads
  have SL : ∀ o : Word, 0x68 ≤ o.toNat → o.toNat + 4 ≤ 0x80 →
      memLoad32 n5.mem (S + BitVec.ofNat 32 0xC0 + o) = memLoad32 Ms (S + BitVec.ofNat 32 0xC0 + o) := fun o h1 h2 => by
    have e : S + BitVec.ofNat 32 0xC0 + o = S + BitVec.ofNat 32 (0xC0 + o.toNat) := by rw [← Gc, ofNat_toNat_self]
    rw [e]
    apply memLoad32_congr; intro j hj
    rw [add_ofNat_assoc]
    have hy : Sep S 0xC0 (S + BitVec.ofNat 32 (0xC0 + o.toNat + j)) 1 := by
      have := offs (c := 0) (n := 0xC0) (d := 0xC0 + o.toNat + j) (k := 1) (by omega) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    rw [fr5 _ hy (offs (by omega) (by omega) (by omega)), M4o _ (offs (by omega) (by omega) (by omega)),
      M2o _ (offs (by omega) (by omega) (by omega)) (offs (by omega) (by omega) (by omega)),
      show 0xC0 + o.toNat + j = 0x128 + (o.toNat - 0x68 + j) by omega, V1 _ (by omega)]
  have hra5 : memLoad32 n5.mem (S + BitVec.ofNat 32 0xC0 + 0x7C) = retAddr := by
    rw [SL _ (by decide) (by decide), slots ra _ (by decide), hra]
  have hc' : b' &&& 1 = 0 ∨ b' &&& 1 = 1 := by rcases hbm4 with rfl | rfl <;> decide
  have h185 : reg n5 (18 : Fin 32) = out := by
    rw [k5 _ (by decide), r4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), s21]
  obtain ⟨n6, c6, pc6, sp6, rr6, k6, w6, b6, fr6⟩ := frq_tailB E n5 u5 M5m hSa hSw how sOS sp5 s15 hc' h185
    (by rw [hra5]; exact hret)
  -- the input's value and the comparison's borrow
  have hX2 : accV M2 (S + BitVec.ofNat 32 0x108) 8 = beNat (memBytes m.mem inp 32) :=
    frp_be m.mem M2 inp 8 _ fun q hq => by
      rw [show 8 - 1 - q = 7 - q by omega, hl2 q hq, memLoad32_congr (M := m.mem) (M' := M1)
        (b := inp + BitVec.ofNat 32 (4 * q)) fun j hj => by rw [add_ofNat_assoc]; exact M1o _ (iS (by omega))]
  have hX4 : accV n4.mem (S + BitVec.ofNat 32 0x108) 8 = beNat (memBytes m.mem inp 32) := by
    rw [← hX2]; apply accV_congr; intro i hi; apply memLoad32_congr; intro j hj
    rw [add_ofNat_assoc, add_ofNat_assoc]; exact M4o _ (offs (by omega) (by omega) (by omega))
  have hN2 : accV M2 p256Np 8 = accV m.mem p256Np 8 := by
    apply accV_congr; intro i hi; apply memLoad32_congr; intro j hj
    rw [add_ofNat_assoc]; exact M2m _ (sSN.subR (c := 4 * i + j) (l := 1) (by omega))
  rw [hN2, hX2] at hinv
  have hmb := frp_borrow hD (mb_le1 b') hinv
  rw [hX4] at eq5
  have eOut : ∀ v : Word, b' &&& 1 = v → (v = 1 → accV n6.mem out 8 = accV n5.mem (S + BitVec.ofNat 32 0xC4) 8) ∧
      (v = 0 → accV n6.mem out 8 = 0) := fun v hv => by
    refine ⟨fun h1 => accV_congr2 8 fun i hi => by rw [w6 i hi, ite_eq_left (by rw [hv, h1])], fun h0 =>
      accV_zero 8 fun i hi => by rw [w6 i hi, ite_eq_right (by rw [hv, h0]; decide)]⟩
  refine ⟨n6, c1.trans (c2.trans (c3.trans (.cons d3 (c4.trans (c5.trans c6))))), by rw [pc6, hra5], ?_,
    fun q hq => ?_, fun hlt => ?_, fun hge => ?_, fun x hx ho => ?_⟩
  · rw [sp6, ← hS, BitVec.add_assoc, show (0xFFFFFEC0 : Word) + BitVec.ofNat 32 0x140 = 0 by decide]
    exact BitVec.add_zero _
  · have hs : ∀ (r : Fin 32) (o : Word), (r, o) ∈ frqPs → reg n6 r = reg m r := fun r o hm => by
      have hb : 0x68 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x80 := by
        simp only [frqPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      rw [rr6 r o hm, SL o hb.1 hb.2, slots r o hm]
    have key : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨
        (q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧
          q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ ra ∧ q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧
          q ≠ (19 : Fin 32) ∧ q ≠ (20 : Fin 32) ∧ q ≠ a5) := by decide
    rcases key q hq with rfl | rfl | rfl | rfl | rfl | ⟨h1, h2, h0, h1', h2', h3, h4, hr, h8, h9, h19, h20, h5⟩
    · exact hs _ 0x78 (by decide)
    · exact hs _ 0x74 (by decide)
    · exact hs _ 0x70 (by decide)
    · exact hs _ 0x6C (by decide)
    · exact hs _ 0x68 (by decide)
    · rw [k6 q h1, k5 q h2, r4 q h0 h1' h2' h3 h4 hr h8 h9 h19 h20 h5, k1 q h1]
  · rw [ite_eq_left hlt] at hmb
    have hb1 : b' = 0xFFFFFFFF := by
      rcases hbm4 with rfl | rfl
      · exact absurd hmb (by decide)
      · rfl
    subst hb1
    refine ⟨by rw [b6]; decide, ?_, ?_⟩
    · rw [(eOut 1 (by decide)).1 rfl]; exact lt5
    · rw [(eOut 1 (by decide)).1 rfl]; exact eq5
  · rw [ite_eq_right (by omega)] at hmb
    have hb0 : b' = 0 := by
      rcases hbm4 with rfl | rfl
      · rfl
      · exact absurd hmb (by decide)
    subst hb0
    exact ⟨by rw [b6]; decide, (eOut 0 (by decide)).2 rfl⟩
  · rw [fr6 x hx ho, M5m x hx]

end C3.RV32
