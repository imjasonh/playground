import C3BootProofs.Proofs.ToBeBytes
import C3BootProofs.Proofs.CondSelect
import C3BootProofs.Proofs.MontMul12Main
import C3BootProofs.Proofs.ParseSpec
import C3BootProofs.Spec.Ecdsa

/-!
# P-384's field `from_repr`, as compiled

`<p384 FieldElement as PrimeField>::from_repr` reads 48 big-endian bytes into
12 limbs, four bytes at a time through a stack word, compares the limbs with
the field modulus by a chain of `borrowing_sub` calls, and converts them to
Montgomery form with `mul_montgomery_form::<12>` against `R² mod p`, which the
image keeps 0x60 bytes past the modulus. `conditional_select` keeps the
product when the input is below the modulus and zero otherwise, and the
choice goes in the byte after the 12 limbs.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem frp_at_0 : fetchRel p384FromReprCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF50, 2) := by decide
theorem frp_at_2 : fetchRel p384FromReprCode 0x2 = some (.store .sw sp ra 0xAC, 2) := by decide
theorem frp_at_4 : fetchRel p384FromReprCode 0x4 = some (.store .sw sp (8 : Fin 32) 0xA8, 2) := by decide
theorem frp_at_6 : fetchRel p384FromReprCode 0x6 = some (.store .sw sp (9 : Fin 32) 0xA4, 2) := by decide
theorem frp_at_8 : fetchRel p384FromReprCode 0x8 = some (.store .sw sp (18 : Fin 32) 0xA0, 2) := by decide
theorem frp_at_a : fetchRel p384FromReprCode 0xA = some (.store .sw sp (19 : Fin 32) 0x9C, 2) := by decide
theorem frp_at_c : fetchRel p384FromReprCode 0xC = some (.store .sw sp (20 : Fin 32) 0x98, 2) := by decide
theorem frp_at_e : fetchRel p384FromReprCode 0xE = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem frp_at_10 : fetchRel p384FromReprCode 0x10 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem frp_at_12 : fetchRel p384FromReprCode 0x12 = some (.aluImm .add a0 sp 0x38, 2) := by decide
theorem frp_at_14 : fetchRel p384FromReprCode 0x14 = some (.auipc ra 0xA000, 4) := by decide
theorem frp_at_18 : fetchRel p384FromReprCode 0x18 = some (.jalr ra ra 0xFFFFFB5A, 4) := by decide
theorem frp_at_1c : fetchRel p384FromReprCode 0x1C = some (.aluImm .add a0 sp 0x68, 2) := by decide
theorem frp_at_1e : fetchRel p384FromReprCode 0x1E = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem frp_at_22 : fetchRel p384FromReprCode 0x22 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem frp_at_24 : fetchRel p384FromReprCode 0x24 = some (.aluImm .add (19 : Fin 32) sp 0x68, 4) := by decide
theorem frp_at_28 : fetchRel p384FromReprCode 0x28 = some (.auipc ra 0x11000, 4) := by decide
theorem frp_at_2c : fetchRel p384FromReprCode 0x2C = some (.jalr ra ra 0xFFFFFC3C, 4) := by decide
theorem frp_at_30 : fetchRel p384FromReprCode 0x30 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem frp_at_32 : fetchRel p384FromReprCode 0x32 = some (.store .sw sp x0 0x4, 2) := by decide
theorem frp_at_34 : fetchRel p384FromReprCode 0x34 = some (.aluImm .add a6 x0 0xC, 2) := by decide
theorem frp_at_36 : fetchRel p384FromReprCode 0x36 = some (.lui a2 0x10000, 2) := by decide
theorem frp_at_38 : fetchRel p384FromReprCode 0x38 = some (.aluImm .add a3 a2 0xFFFFFF00, 4) := by decide
theorem frp_at_3c : fetchRel p384FromReprCode 0x3C = some (.aluImm .add (17 : Fin 32) x0 0xB, 2) := by decide
theorem frp_at_3e : fetchRel p384FromReprCode 0x3E = some (.branch .beq a6 x0 0x48, 4) := by decide
theorem frp_at_42 : fetchRel p384FromReprCode 0x42 = some (.aluImm .add a4 sp 0x4, 2) := by decide
theorem frp_at_44 : fetchRel p384FromReprCode 0x44 = some (.aluImm .add a5 x0 0x4, 2) := by decide
theorem frp_at_46 : fetchRel p384FromReprCode 0x46 = some (.alu .add (9 : Fin 32) x0 (8 : Fin 32), 2) := by decide
theorem frp_at_48 : fetchRel p384FromReprCode 0x48 = some (.branch .beq a5 x0 0x12, 2) := by decide
theorem frp_at_4a : fetchRel p384FromReprCode 0x4A = some (.load .lbu a1 (9 : Fin 32) 0x0, 4) := by decide
theorem frp_at_4e : fetchRel p384FromReprCode 0x4E = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x1, 2) := by decide
theorem frp_at_50 : fetchRel p384FromReprCode 0x50 = some (.store .sb a4 a1 0x0, 4) := by decide
theorem frp_at_54 : fetchRel p384FromReprCode 0x54 = some (.aluImm .add a4 a4 0x1, 2) := by decide
theorem frp_at_56 : fetchRel p384FromReprCode 0x56 = some (.aluImm .add a5 a5 0xFFFFFFFF, 2) := by decide
theorem frp_at_58 : fetchRel p384FromReprCode 0x58 = some (.branch .bne a5 x0 0xFFFFFFF2, 2) := by decide
theorem frp_at_5a : fetchRel p384FromReprCode 0x5A = some (.load .lw a4 sp 0x4, 2) := by decide
theorem frp_at_5c : fetchRel p384FromReprCode 0x5C = some (.alu .sub a5 (17 : Fin 32) a0, 4) := by decide
theorem frp_at_60 : fetchRel p384FromReprCode 0x60 = some (.aluImm .srl (9 : Fin 32) a4 0x8, 4) := by decide
theorem frp_at_64 : fetchRel p384FromReprCode 0x64 = some (.aluImm .srl a1 a4 0x18, 4) := by decide
theorem frp_at_68 : fetchRel p384FromReprCode 0x68 = some (.alu .and (9 : Fin 32) (9 : Fin 32) a3, 2) := by decide
theorem frp_at_6a : fetchRel p384FromReprCode 0x6A = some (.alu .or a1 a1 (9 : Fin 32), 2) := by decide
theorem frp_at_6c : fetchRel p384FromReprCode 0x6C = some (.alu .and a2 a4 a3, 4) := by decide
theorem frp_at_70 : fetchRel p384FromReprCode 0x70 = some (.aluImm .sll a4 a4 0x18, 2) := by decide
theorem frp_at_72 : fetchRel p384FromReprCode 0x72 = some (.aluImm .sll a2 a2 0x8, 2) := by decide
theorem frp_at_74 : fetchRel p384FromReprCode 0x74 = some (.alu .or a2 a2 a4, 2) := by decide
theorem frp_at_76 : fetchRel p384FromReprCode 0x76 = some (.aluImm .sll a5 a5 0x2, 2) := by decide
theorem frp_at_78 : fetchRel p384FromReprCode 0x78 = some (.alu .add a5 a5 (19 : Fin 32), 2) := by decide
theorem frp_at_7a : fetchRel p384FromReprCode 0x7A = some (.alu .or a1 a1 a2, 2) := by decide
theorem frp_at_7c : fetchRel p384FromReprCode 0x7C = some (.store .sw a5 a1 0x0, 2) := by decide
theorem frp_at_7e : fetchRel p384FromReprCode 0x7E = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem frp_at_80 : fetchRel p384FromReprCode 0x80 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem frp_at_82 : fetchRel p384FromReprCode 0x82 = some (.branch .bne a0 a6 0xFFFFFFC0, 4) := by decide
theorem frp_at_86 : fetchRel p384FromReprCode 0x86 = some (.aluImm .add (19 : Fin 32) x0 0x0, 2) := by decide
theorem frp_at_88 : fetchRel p384FromReprCode 0x88 = some (.aluImm .add (20 : Fin 32) sp 0x68, 4) := by decide
theorem frp_at_8c : fetchRel p384FromReprCode 0x8C = some (.lui (9 : Fin 32) 0x3FCC5000, 4) := by decide
theorem frp_at_90 : fetchRel p384FromReprCode 0x90 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFCF4, 4) := by decide
theorem frp_at_94 : fetchRel p384FromReprCode 0x94 = some (.aluImm .add (8 : Fin 32) x0 0xC, 2) := by decide
theorem frp_at_96 : fetchRel p384FromReprCode 0x96 = some (.branch .beq (8 : Fin 32) x0 0x1C, 2) := by decide
theorem frp_at_98 : fetchRel p384FromReprCode 0x98 = some (.load .lw a0 (20 : Fin 32) 0x0, 4) := by decide
theorem frp_at_9c : fetchRel p384FromReprCode 0x9C = some (.load .lw a1 (9 : Fin 32) 0x0, 2) := by decide
theorem frp_at_9e : fetchRel p384FromReprCode 0x9E = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem frp_at_a0 : fetchRel p384FromReprCode 0xA0 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem frp_at_a4 : fetchRel p384FromReprCode 0xA4 = some (.jalr ra ra 0xFFFFF8EE, 4) := by decide
theorem frp_at_a8 : fetchRel p384FromReprCode 0xA8 = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem frp_at_aa : fetchRel p384FromReprCode 0xAA = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4, 2) := by decide
theorem frp_at_ac : fetchRel p384FromReprCode 0xAC = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem frp_at_ae : fetchRel p384FromReprCode 0xAE = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem frp_at_b0 : fetchRel p384FromReprCode 0xB0 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE8, 2) := by decide
theorem frp_at_b2 : fetchRel p384FromReprCode 0xB2 = some (.lui (8 : Fin 32) 0x3FCC5000, 4) := by decide
theorem frp_at_b6 : fetchRel p384FromReprCode 0xB6 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFCF4, 4) := by decide
theorem frp_at_ba : fetchRel p384FromReprCode 0xBA = some (.aluImm .add a0 (8 : Fin 32) 0x30, 4) := by decide
theorem frp_at_be : fetchRel p384FromReprCode 0xBE = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem frp_at_c0 : fetchRel p384FromReprCode 0xC0 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem frp_at_c4 : fetchRel p384FromReprCode 0xC4 = some (.jalr ra ra 0x21A, 4) := by decide
theorem frp_at_c8 : fetchRel p384FromReprCode 0xC8 = some (.aluImm .add a1 sp 0x98, 2) := by decide
theorem frp_at_ca : fetchRel p384FromReprCode 0xCA = some (.aluImm .and (9 : Fin 32) a0 0xFF, 4) := by decide
theorem frp_at_ce : fetchRel p384FromReprCode 0xCE = some (.alu .add a0 x0 a1, 2) := by decide
theorem frp_at_d0 : fetchRel p384FromReprCode 0xD0 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem frp_at_d2 : fetchRel p384FromReprCode 0xD2 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem frp_at_d6 : fetchRel p384FromReprCode 0xD6 = some (.jalr ra ra 0x208, 4) := by decide
theorem frp_at_da : fetchRel p384FromReprCode 0xDA = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem frp_at_de : fetchRel p384FromReprCode 0xDE = some (.aluImm .xor a0 a0 0xFFFFFFFF, 4) := by decide
theorem frp_at_e2 : fetchRel p384FromReprCode 0xE2 = some (.alu .and a0 (19 : Fin 32) a0, 4) := by decide
theorem frp_at_e6 : fetchRel p384FromReprCode 0xE6 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem frp_at_e8 : fetchRel p384FromReprCode 0xE8 = some (.alu .or (9 : Fin 32) (9 : Fin 32) a0, 2) := by decide
theorem frp_at_ea : fetchRel p384FromReprCode 0xEA = some (.aluImm .add a2 (8 : Fin 32) 0x60, 4) := by decide
theorem frp_at_ee : fetchRel p384FromReprCode 0xEE = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem frp_at_f0 : fetchRel p384FromReprCode 0xF0 = some (.aluImm .add a1 sp 0x68, 2) := by decide
theorem frp_at_f2 : fetchRel p384FromReprCode 0xF2 = some (.aluImm .add a4 x0 0x1, 2) := by decide
theorem frp_at_f4 : fetchRel p384FromReprCode 0xF4 = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem frp_at_f6 : fetchRel p384FromReprCode 0xF6 = some (.auipc ra 0xF000, 4) := by decide
theorem frp_at_fa : fetchRel p384FromReprCode 0xFA = some (.jalr ra ra 0x62, 4) := by decide
theorem frp_at_fe : fetchRel p384FromReprCode 0xFE = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem frp_at_100 : fetchRel p384FromReprCode 0x100 = some (.auipc ra 0xA000, 4) := by decide
theorem frp_at_104 : fetchRel p384FromReprCode 0x104 = some (.jalr ra ra 0xFFFFFAC2, 4) := by decide
theorem frp_at_108 : fetchRel p384FromReprCode 0x108 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem frp_at_10a : fetchRel p384FromReprCode 0x10A = some (.store .sb sp a0 0x34, 4) := by decide
theorem frp_at_10e : fetchRel p384FromReprCode 0x10E = some (.aluImm .add a0 sp 0x38, 2) := by decide
theorem frp_at_110 : fetchRel p384FromReprCode 0x110 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem frp_at_114 : fetchRel p384FromReprCode 0x114 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem frp_at_116 : fetchRel p384FromReprCode 0x116 = some (.auipc ra 0x11000, 4) := by decide
theorem frp_at_11a : fetchRel p384FromReprCode 0x11A = some (.jalr ra ra 0xFFFFFB4E, 4) := by decide
theorem frp_at_11e : fetchRel p384FromReprCode 0x11E = some (.aluImm .and a3 (8 : Fin 32) 0xFF, 4) := by decide
theorem frp_at_122 : fetchRel p384FromReprCode 0x122 = some (.aluImm .add a1 sp 0x38, 2) := by decide
theorem frp_at_124 : fetchRel p384FromReprCode 0x124 = some (.aluImm .add a2 sp 0x4, 2) := by decide
theorem frp_at_126 : fetchRel p384FromReprCode 0x126 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem frp_at_128 : fetchRel p384FromReprCode 0x128 = some (.auipc ra 0x10000, 4) := by decide
theorem frp_at_12c : fetchRel p384FromReprCode 0x12C = some (.jalr ra ra 0xFFFFFB8A, 4) := by decide
theorem frp_at_130 : fetchRel p384FromReprCode 0x130 = some (.store .sb (18 : Fin 32) (8 : Fin 32) 0x30, 4) := by decide
theorem frp_at_134 : fetchRel p384FromReprCode 0x134 = some (.load .lw ra sp 0xAC, 2) := by decide
theorem frp_at_136 : fetchRel p384FromReprCode 0x136 = some (.load .lw (8 : Fin 32) sp 0xA8, 2) := by decide
theorem frp_at_138 : fetchRel p384FromReprCode 0x138 = some (.load .lw (9 : Fin 32) sp 0xA4, 2) := by decide
theorem frp_at_13a : fetchRel p384FromReprCode 0x13A = some (.load .lw (18 : Fin 32) sp 0xA0, 2) := by decide
theorem frp_at_13c : fetchRel p384FromReprCode 0x13C = some (.load .lw (19 : Fin 32) sp 0x9C, 2) := by decide
theorem frp_at_13e : fetchRel p384FromReprCode 0x13E = some (.load .lw (20 : Fin 32) sp 0x98, 2) := by decide
theorem frp_at_140 : fetchRel p384FromReprCode 0x140 = some (.aluImm .add sp sp 0xB0, 2) := by decide
theorem frp_at_142 : fetchRel p384FromReprCode 0x142 = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem sep1_ne {a x : Word} (h : Sep a 1 x 1) : x ≠ a := fun e =>
  h 0 (by omega) 0 (by omega) (by rw [add_ofNat_zero, add_ofNat_zero, e])

/-- The inner loop's body, from 0x4A to its branch at 0x58: copy one byte. -/
def frpInner : List BInstr :=
  [.lbu a1 (9 : Fin 32) 0, .aluImm .add (9 : Fin 32) (9 : Fin 32) 1, .sb a4 a1 0, .aluImm .add a4 a4 1,
   .aluImm .add a5 a5 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem frpInner_end : blockEnd p384FromReprCode 0x4A frpInner = some 0x58 := by decide
end

abbrev FRP : Word := BitVec.ofNat 32 p384FromReprAddress

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The byte loop from 0x4A, with `k` of the four bytes left after the
first `j`: it copies the bytes at `src` to the word at `T`, one at a time. -/
theorem frp_inner {Mb : Word → BitVec 8} {src T : Word}
    (hc : ∀ Mx : Word → BitVec 8, (∀ x, Sep T 4 x 1 → Mx x = Mb x) → CodeIn Mx FRP p384FromReprCode)
    (hsT : Sep src 4 T 4) (hTw : T.toNat + 4 ≤ 0x40000000) :
    ∀ k j (n : Machine) (Mx : Word → BitVec 8), j + k = 4 → 0 < k →
      St Mx FRP n 0x4A (reg n) → (∀ x, Sep T 4 x 1 → Mx x = Mb x) →
      (∀ i, i < j → Mx (T + BitVec.ofNat 32 i) = Mb (src + BitVec.ofNat 32 i)) →
      reg n a5 = BitVec.ofNat 32 k → reg n a4 = T + BitVec.ofNat 32 j → reg n (9 : Fin 32) = src + BitVec.ofNat 32 j →
      ∃ n' Mf, Steps n n' ∧ St Mf FRP n' 0x5A (reg n') ∧ (∀ x, Sep T 4 x 1 → Mf x = Mb x) ∧
        (∀ i, i < 4 → Mf (T + BitVec.ofNat 32 i) = Mb (src + BitVec.ofNat 32 i)) ∧
        ∀ r, r ≠ a1 → r ≠ a4 → r ≠ a5 → r ≠ (9 : Fin 32) → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro j n Mx hjk _ st hag hj ha5 ha4 hs1
    have hcx := hc Mx hag
    have hz := st.zero
    have hTj : Sep (T + BitVec.ofNat 32 j) 1 FRP p384FromReprCode.length :=
      sep_of_le (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, show FRP.toNat = (img% p384FromReprAddress) by decide]; omega)
        (by decide)
    obtain ⟨n1, c1, u1⟩ := St.block frpInner st hcx frpInner_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, frpInner, upd_app, ↓reduceIte, and_true, true_and]
      rw [ha4, add_lit_zero]; exact hTj)
    have eM : (runBlock frpInner (Mx, reg n)).1 =
        memStore8 Mx (T + BitVec.ofNat 32 j) (Mb (src + BitVec.ofNat 32 j)) := by
      simp +decide only [runBlock, BInstr.run, frpInner, upd_app, ↓reduceIte]
      rw [ha4, hs1, add_lit_zero, add_lit_zero, uo_ext_zext,
        hag _ (hsT.sub (c := j) (l := 1) (by omega)).symm]
    have R1 : ∀ q, reg n1 q = (runBlock frpInner (Mx, reg n)).2 q := u1.regs
    have u1' : St (memStore8 Mx (T + BitVec.ofNat 32 j) (Mb (src + BitVec.ofNat 32 j))) FRP n1 0x58 (reg n1) :=
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
    have a51 : reg n1 a5 = BitVec.ofNat 32 k := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frpInner, upd_app, ↓reduceIte]; rw [ha5]
      apply BitVec.eq_of_toNat_eq
      show (BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF).toNat = _
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl]
      omega
    have a41 : reg n1 a4 = T + BitVec.ofNat 32 (j + 1) := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frpInner, upd_app, ↓reduceIte]; rw [ha4]
      exact add_ofNat_assoc T j 1
    have s11 : reg n1 (9 : Fin 32) = src + BitVec.ofNat 32 (j + 1) := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frpInner, upd_app, ↓reduceIte]; rw [hs1]
      exact add_ofNat_assoc src j 1
    have K1 : ∀ r, r ≠ a1 → r ≠ a4 → r ≠ a5 → r ≠ (9 : Fin 32) → reg n1 r = reg n r := fun r h1 h4 h5 h9 => by
      rw [R1]; refine runBlock_reg _ _ _ r hz ?_
      simp only [frpInner, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      simp [h1, h4, h5, h9]
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n2, d2, u2⟩ := u1'.notTaken hcx' 0x5A frp_at_58 (by decide) (by
        simp only [branchTaken]; rw [a51, u1'.zero]; decide)
      have hj4 : j + 1 = 4 := by omega
      rw [hj4] at hj'
      exact ⟨n2, _, c1.trans (.single d2), u2.self, hag', hj',
        fun r h1 h4 h5 h9 => by rw [u2.regs, K1 r h1 h4 h5 h9]⟩
    · obtain ⟨n2, d2, u2⟩ := u1'.taken hcx' 0x4A frp_at_58 (by decide) (by
        simp only [branchTaken, a51, u1'.zero, bne_iff_ne, ne_eq]
        intro h; exact hk (by have := ofNat_inj (c := k) (d := 0) (by omega) (by decide) h; omega))
      obtain ⟨n3, Mf, c3, u3, hag3, hb3, K3⟩ := ih (j + 1) n2 _ (by omega) (by omega) u2.self hag' hj'
        (by rw [u2.regs, a51]) (by rw [u2.regs, a41]) (by rw [u2.regs, s11])
      exact ⟨n3, Mf, c1.trans (.cons d2 c3), u3, hag3, hb3,
        fun r h1 h4 h5 h9 => by rw [K3 r h1 h4 h5 h9, u2.regs, K1 r h1 h4 h5 h9]⟩

/-- From 0x42 to the inner loop: point at the stack word and the input. -/
def frpOuterA : List BInstr := [.aluImm .add a4 sp 4, .aluImm .add a5 x0 4, .alu .add (9 : Fin 32) x0 (8 : Fin 32)]

/-- From 0x5A to the outer branch at 0x82: load the word, swap its bytes,
store it as limb `11 - i`, and advance. -/
def frpOuterB : List BInstr :=
  [.lw a4 sp 4, .alu .sub a5 (17 : Fin 32) a0, .aluImm .srl (9 : Fin 32) a4 0x8, .aluImm .srl a1 a4 0x18,
   .alu .and (9 : Fin 32) (9 : Fin 32) a3, .alu .or a1 a1 (9 : Fin 32), .alu .and a2 a4 a3, .aluImm .sll a4 a4 0x18,
   .aluImm .sll a2 a2 0x8, .alu .or a2 a2 a4, .aluImm .sll a5 a5 0x2, .alu .add a5 a5 (19 : Fin 32),
   .alu .or a1 a1 a2, .sw a5 a1 0, .aluImm .add a0 a0 1, .aluImm .add (8 : Fin 32) (8 : Fin 32) 4]

section
set_option maxRecDepth 20000
theorem frpOuterA_end : blockEnd p384FromReprCode 0x42 frpOuterA = some 0x48 := by decide
theorem frpOuterB_end : blockEnd p384FromReprCode 0x5A frpOuterB = some 0x82 := by decide
end

theorem frp_swap (x : Word) :
    aluEval .or (aluEval .or (aluEval .srl x 0x18) (aluEval .and (aluEval .srl x 0x8) 0xFF00))
      (aluEval .or (aluEval .sll (aluEval .and x 0xFF00) 0x8) (aluEval .sll x 0x18)) = bswap32 x := by
  show (x >>> 24 ||| ((x >>> 8) &&& 0xFF00)) ||| (((x &&& 0xFF00) <<< 8) ||| (x <<< 24)) = _
  unfold bswap32; rw [← BitVec.or_assoc]

theorem frp_limbAddr (X : Word) {i : Nat} (hi : i < 12) :
    aluEval .add (aluEval .sll (aluEval .sub 11 (BitVec.ofNat 32 i)) 2) X + 0 = X + BitVec.ofNat 32 (4 * (11 - i)) := by
  rw [add_lit_zero]
  show (((11 : Word) - BitVec.ofNat 32 i) <<< (2 % 32)) + X = _
  rw [BitVec.add_comm]; congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  show (2 ^ 32 - i % 2 ^ 32 + 11 % 2 ^ 32) % 2 ^ 32 * 2 ^ 2 % 2 ^ 32 = 4 * (11 - i) % 2 ^ 32
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- The outer loop from 0x42, with `k` limbs left after the first `i`: limb
`11 - i` at `X` gets the big-endian word at `inp + 4 i`, through the stack
word at `T`. -/
theorem frp_outer {Mb : Word → BitVec 8} {inp T X G : Word}
    (hc : ∀ Mx : Word → BitVec 8, (∀ x, Sep T 4 x 1 → Sep X 48 x 1 → Mx x = Mb x) → CodeIn Mx FRP p384FromReprCode)
    (hT : G + 4 = T) (hiT : Sep inp 48 T 4) (hiX : Sep inp 48 X 48) (hTX : Sep T 4 X 48)
    (hTw : T.toNat + 4 ≤ 0x40000000) (hXw : X.toNat + 48 ≤ 0x40000000) (hTa : T.toNat % 4 = 0)
    (hXa : X.toNat % 4 = 0) :
    ∀ k i (n : Machine) (Mx : Word → BitVec 8), i + k = 12 → 0 < k →
      St Mx FRP n 0x42 (reg n) → (∀ x, Sep T 4 x 1 → Sep X 48 x 1 → Mx x = Mb x) →
      (∀ q, q < i → memLoad32 Mx (X + BitVec.ofNat 32 (4 * (11 - q))) =
        bswap32 (memLoad32 Mb (inp + BitVec.ofNat 32 (4 * q)))) →
      reg n a0 = BitVec.ofNat 32 i → reg n (8 : Fin 32) = inp + BitVec.ofNat 32 (4 * i) → reg n sp = G →
      reg n a6 = 12 → reg n a3 = 0xFF00 → reg n (17 : Fin 32) = 11 → reg n (19 : Fin 32) = X →
      ∃ n' Mf, Steps n n' ∧ St Mf FRP n' 0x86 (reg n') ∧ (∀ x, Sep T 4 x 1 → Sep X 48 x 1 → Mf x = Mb x) ∧
        (∀ q, q < 12 → memLoad32 Mf (X + BitVec.ofNat 32 (4 * (11 - q))) =
          bswap32 (memLoad32 Mb (inp + BitVec.ofNat 32 (4 * q)))) ∧
        ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a4 → r ≠ a5 → r ≠ (8 : Fin 32) → r ≠ (9 : Fin 32) → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro i n Mx hik _ st hag hl ha0 hs0 hsp ha6 ha3 h17 h19
    have hcx := hc Mx hag
    have hz := st.zero
    obtain ⟨n1, c1, u1⟩ := St.block frpOuterA st hcx frpOuterA_end (by
      simp only [BlockOk, BInstr.ok, frpOuterA]; exact ⟨trivial, trivial, trivial, trivial⟩)
    have R1 : ∀ q, reg n1 q = (runBlock frpOuterA (Mx, reg n)).2 q := u1.regs
    have u1' : St Mx FRP n1 0x48 (reg n1) := ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩
    have a51 : reg n1 a5 = 4 := by rw [R1]; simp +decide only [runBlock, BInstr.run, frpOuterA, upd_app, ↓reduceIte]
    have a41 : reg n1 a4 = T := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frpOuterA, upd_app, ↓reduceIte]; rw [hsp, ← hT]; rfl
    have s11 : reg n1 (9 : Fin 32) = inp + BitVec.ofNat 32 (4 * i) := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frpOuterA, upd_app, ↓reduceIte]; rw [hs0]
      exact BitVec.zero_add _
    have K1 : ∀ r, r ≠ a4 → r ≠ a5 → r ≠ (9 : Fin 32) → reg n1 r = reg n r := fun r h4 h5 h9 => by
      rw [R1]; refine runBlock_reg _ _ _ r hz ?_
      simp only [frpOuterA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      simp [h4, h5, h9]
    obtain ⟨n2, d2, u2⟩ := u1'.notTaken hcx 0x4A frp_at_48 (by decide) (by
      simp only [branchTaken]; rw [a51, u1'.zero]; decide)
    have hsrcT : Sep (inp + BitVec.ofNat 32 (4 * i)) 4 T 4 := hiT.sub (c := 4 * i) (l := 4) (by omega)
    obtain ⟨n3, M3, c3, u3, hag3, hb3, K3⟩ := frp_inner (Mb := Mx) (src := inp + BitVec.ofNat 32 (4 * i)) (T := T)
      (fun My hMy => hc My fun x h1 h2 => by rw [hMy x h1, hag x h1 h2]) hsrcT hTw 4 0 n2 Mx (by omega) (by omega)
      u2.self (fun _ _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _)) (by rw [u2.regs, a51]; rfl)
      (by rw [u2.regs, a41, add_ofNat_zero]) (by rw [u2.regs, s11, add_ofNat_zero])
    have hag3' : ∀ x, Sep T 4 x 1 → Sep X 48 x 1 → M3 x = Mb x := fun x h1 h2 => by rw [hag3 x h1, hag x h1 h2]
    have hc3 := hc M3 hag3'
    -- the swapped word and its slot
    have hw : memLoad32 M3 T = memLoad32 Mb (inp + BitVec.ofNat 32 (4 * i)) := by
      apply memLoad32_congr2; intro j hj; rw [hb3 j hj, hag _ (hsrcT.sub (c := j) (l := 1) (by omega)).symm
        (by rw [add_ofNat_assoc]; exact (hiX.sub (c := 4 * i + j) (l := 1) (by omega)).symm)]
    have r3 : ∀ q, q ≠ a1 → q ≠ a4 → q ≠ a5 → q ≠ (9 : Fin 32) → reg n3 q = reg n q := fun q h1 h4 h5 h9 => by
      rw [K3 q h1 h4 h5 h9, u2.regs, K1 q h4 h5 h9]
    have hX11 : Sep (X + BitVec.ofNat 32 (4 * (11 - i))) 4 FRP p384FromReprCode.length :=
      sep_of_le (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, show FRP.toNat = (img% p384FromReprAddress) by decide]; omega)
        (by decide)
    obtain ⟨n4, c4, u4⟩ := St.block frpOuterB u3 hc3 frpOuterB_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, frpOuterB, upd_app, ↓reduceIte, and_true, true_and]
      rw [r3 sp (by decide) (by decide) (by decide) (by decide), hsp, hT,
        r3 a0 (by decide) (by decide) (by decide) (by decide), ha0, r3 _ (by decide) (by decide) (by decide) (by decide),
        h17, r3 _ (by decide) (by decide) (by decide) (by decide), h19, frp_limbAddr X (by omega)]
      exact ⟨hTa, aligned_add hXa (by omega), hX11⟩)
    have M4e : (runBlock frpOuterB (M3, reg n3)).1 =
        memStore32 M3 (X + BitVec.ofNat 32 (4 * (11 - i))) (bswap32 (memLoad32 Mb (inp + BitVec.ofNat 32 (4 * i)))) := by
      simp +decide only [runBlock, BInstr.run, frpOuterB, upd_app, ↓reduceIte]
      rw [r3 sp (by decide) (by decide) (by decide) (by decide), hsp, hT,
        r3 a0 (by decide) (by decide) (by decide) (by decide), ha0, r3 _ (by decide) (by decide) (by decide) (by decide),
        h17, r3 _ (by decide) (by decide) (by decide) (by decide), h19, r3 a3 (by decide) (by decide) (by decide) (by decide),
        ha3, frp_limbAddr X (by omega)]
      congr 1
      rw [hw]; exact frp_swap _
    have R4 : ∀ q, reg n4 q = (runBlock frpOuterB (M3, reg n3)).2 q := u4.regs
    obtain ⟨M4, hM4⟩ : ∃ M4, memStore32 M3 (X + BitVec.ofNat 32 (4 * (11 - i)))
        (bswap32 (memLoad32 Mb (inp + BitVec.ofNat 32 (4 * i)))) = M4 := ⟨_, rfl⟩
    rw [hM4] at M4e
    have u4' : St M4 FRP n4 0x82 (reg n4) := ⟨u4.pc, by rw [u4.mem, M4e], fun _ => rfl⟩
    have hag4 : ∀ x, Sep T 4 x 1 → Sep X 48 x 1 → M4 x = Mb x := fun x h1 h2 => by
      rw [← hM4, memStore32_get_sep (h2.sub (c := 4 * (11 - i)) (l := 4) (by omega)), hag3' x h1 h2]
    have hl4 : ∀ q, q < i + 1 → memLoad32 M4 (X + BitVec.ofNat 32 (4 * (11 - q))) =
        bswap32 (memLoad32 Mb (inp + BitVec.ofNat 32 (4 * q))) := fun q hq => by
      rw [← hM4]
      by_cases hqi : q = i
      · subst hqi; exact memLoad32_store32_same _ _ _
      · rw [memLoad32_store32_sep (sep_offsets X (c := 4 * (11 - i)) (n := 4) (d := 4 * (11 - q)) (k := 4)
          (by omega) (by omega) (by omega)), ← hl q (by omega)]
        exact load_frame hag3 (hTX.subR (c := 4 * (11 - q)) (l := 4) (by omega))
    have hc4 := hc M4 hag4
    have a04 : reg n4 a0 = BitVec.ofNat 32 (i + 1) := by
      rw [R4]; simp +decide only [runBlock, BInstr.run, frpOuterB, upd_app, ↓reduceIte]
      rw [r3 a0 (by decide) (by decide) (by decide) (by decide), ha0]; exact ofNat_add_ofNat i 1
    have s04 : reg n4 (8 : Fin 32) = inp + BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [R4]; simp +decide only [runBlock, BInstr.run, frpOuterB, upd_app, ↓reduceIte]
      rw [r3 _ (by decide) (by decide) (by decide) (by decide), hs0]
      show inp + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc, show 4 * i + 4 = 4 * (i + 1) by omega]
    have a64 : reg n4 a6 = 12 := by
      rw [R4]; simp +decide only [runBlock, BInstr.run, frpOuterB, upd_app, ↓reduceIte]
      rw [r3 _ (by decide) (by decide) (by decide) (by decide), ha6]
    have K4 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a4 → r ≠ a5 → r ≠ (8 : Fin 32) → r ≠ (9 : Fin 32) →
        reg n4 r = reg n r := fun r h0 h1 h2 h4 h5 h8 h9 => by
      rw [R4, runBlock_reg _ _ _ r u3.zero (by
        simp only [frpOuterB, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
        simp [h0, h1, h2, h4, h5, h8, h9]), r3 r h1 h4 h5 h9]
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x86 frp_at_82 (by decide) (by
        simp only [branchTaken]; rw [a04, a64, show i + 1 = 12 by omega]; rfl)
      have hi12 : i + 1 = 12 := by omega
      rw [hi12] at hl4
      exact ⟨n5, M4, c1.trans (.cons d2 (c3.trans (c4.trans (.single d5)))), u5.self, hag4, hl4,
        fun r h0 h1 h2 h4 h5 h8 h9 => by rw [u5.regs, K4 r h0 h1 h2 h4 h5 h8 h9]⟩
    · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x42 frp_at_82 (by decide) (by
        simp only [branchTaken, a04, a64, bne_iff_ne, ne_eq]
        intro h; have := ofNat_inj (c := i + 1) (d := 12) (by omega) (by decide) h; omega)
      obtain ⟨n6, Mf, c6, u6, hag6, hb6, K6⟩ := ih (i + 1) n5 M4 (by omega) (by omega) u5.self hag4 hl4
        (by rw [u5.regs, a04]) (by rw [u5.regs, s04])
        (by rw [u5.regs, K4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsp])
        (by rw [u5.regs, a64])
        (by rw [u5.regs, K4 a3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ha3])
        (by rw [u5.regs, K4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h17])
        (by rw [u5.regs, K4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h19])
      exact ⟨n6, Mf, c1.trans (.cons d2 (c3.trans (c4.trans (.cons d5 c6)))), u6, hag6, hb6,
        fun r h0 h1 h2 h4 h5 h8 h9 => by rw [K6 r h0 h1 h2 h4 h5 h8 h9, u5.regs, K4 r h0 h1 h2 h4 h5 h8 h9]⟩

/-- From 0x98 to the call: load limb `j` of the input and of the modulus. -/
def frpCmpA : List BInstr := [.lw a0 (20 : Fin 32) 0, .lw a1 (9 : Fin 32) 0, .alu .add a2 x0 (19 : Fin 32)]

/-- From 0xA8 to the branch at 0xB0: keep the borrow and advance. -/
def frpCmpB : List BInstr :=
  [.alu .add (19 : Fin 32) x0 a1, .aluImm .add (20 : Fin 32) (20 : Fin 32) 4, .aluImm .add (9 : Fin 32) (9 : Fin 32) 4,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem frpCmpA_end : blockEnd p384FromReprCode 0x98 frpCmpA = some 0xA0 := by decide
theorem frpCmpB_end : blockEnd p384FromReprCode 0xA8 frpCmpB = some 0xB0 := by decide
end

/-- One limb of a borrow chain: the running difference stays below the
limbs' range and the invariant `D + N = A + 2^(32 j) · borrow` carries over. -/
theorem frp_chain {A Nn D l r d mb mb' P : Nat} (hD : D < P) (hinv : D + Nn = A + P * mb)
    (hv : d + r + mb = l + 2 ^ 32 * mb') (hd : d < 2 ^ 32) :
    D + d * P < P * 2 ^ 32 ∧ (D + d * P) + (Nn + r * P) = (A + l * P) + P * 2 ^ 32 * mb' := by
  have h1 : d * P + P ≤ 2 ^ 32 * P := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hd
  have h2 : (d + r + mb) * P = (l + 2 ^ 32 * mb') * P := by rw [hv]
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.mul_assoc] at h2
  constructor
  · omega
  · rw [Nat.mul_comm P (2 ^ 32), Nat.mul_assoc, Nat.mul_comm mb' P, Nat.mul_comm mb P] at *; omega

/-- The borrow out of a chain over `n` limbs is set exactly when the first
operand is below the second. -/
theorem frp_borrow {A Nn D n mb : Nat} (hD : D < 2 ^ (32 * n)) (hm : mb ≤ 1)
    (hinv : D + Nn = A + 2 ^ (32 * n) * mb) : mb = if A < Nn then 1 else 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl
  · rw [ite_eq_right (by omega)]
  · rw [ite_eq_left (by omega)]

theorem frp_ofNat_dec (k : Nat) :
    aluEval .add (BitVec.ofNat 32 (k + 1)) 0xFFFFFFFF = BitVec.ofNat 32 k := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl]
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- The comparison loop from 0x98, with `k` limbs left after the first `j`:
`borrowing_sub` runs down the limbs of `X` and `N` and leaves the borrow in
`s3`. It writes only the word below `G`, where `borrowing_sub` keeps a
temporary. -/
theorem frp_cmp {Mb : Word → BitVec 8} {X N G : Word}
    (hc : ∀ Mx : Word → BitVec 8, (∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → Mx x = Mb x) → CodeIn Mx FRP p384FromReprCode)
    (hb : ∀ Mx : Word → BitVec 8, (∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → Mx x = Mb x) →
      CodeIn Mx (BitVec.ofNat 32 borrowingSubAddress) borrowingSubCode)
    (hGa : G.toNat % 4 = 0) (hGl : 4 ≤ G.toNat) (hGw : G.toNat ≤ 0x40000000) (hXa : X.toNat % 4 = 0)
    (hNa : N.toNat % 4 = 0) (sXF : Sep X 48 (G + 0xFFFFFFFC) 4) (sNF : Sep N 48 (G + 0xFFFFFFFC) 4) :
    ∀ k j (n : Machine) (Mx : Word → BitVec 8) (b : Word), j + k = 12 → 0 < k →
      St Mx FRP n 0x98 (reg n) → (∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → Mx x = Mb x) →
      reg n (19 : Fin 32) = b → (b = 0 ∨ b = 0xFFFFFFFF) →
      (∃ D, D < 2 ^ (32 * j) ∧ D + accV Mb N j = accV Mb X j + 2 ^ (32 * j) * maskBit b) →
      reg n (20 : Fin 32) = X + BitVec.ofNat 32 (4 * j) → reg n (9 : Fin 32) = N + BitVec.ofNat 32 (4 * j) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 k → reg n sp = G →
      ∃ n' Mf b', Steps n n' ∧ St Mf FRP n' 0xB2 (reg n') ∧ (∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → Mf x = Mb x) ∧
        reg n' (19 : Fin 32) = b' ∧ (b' = 0 ∨ b' = 0xFFFFFFFF) ∧
        (∃ D, D < 2 ^ (32 * 12) ∧ D + accV Mb N 12 = accV Mb X 12 + 2 ^ (32 * 12) * maskBit b') ∧
        ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ ra → r ≠ (8 : Fin 32) → r ≠ (9 : Fin 32) →
          r ≠ (19 : Fin 32) → r ≠ (20 : Fin 32) → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro j n Mx b hjk _ st hag hb19 hbm ⟨D, hD, hinv⟩ h20 h9 h8 hsp
    have hcx := hc Mx hag
    have hz := st.zero
    obtain ⟨n1, c1, u1⟩ := St.block frpCmpA st hcx frpCmpA_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, frpCmpA, upd_app, ↓reduceIte, and_true]
      rw [h20, h9, add_lit_zero, add_lit_zero]
      exact ⟨aligned_add hXa (by omega), aligned_add hNa (by omega)⟩)
    have R1 : ∀ q, reg n1 q = (runBlock frpCmpA (Mx, reg n)).2 q := u1.regs
    have u1' : St Mx FRP n1 0xA0 (reg n1) := ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩
    obtain ⟨l, hl⟩ : ∃ l, memLoad32 Mb (X + BitVec.ofNat 32 (4 * j)) = l := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, memLoad32 Mb (N + BitVec.ofNat 32 (4 * j)) = r := ⟨_, rfl⟩
    have a01 : reg n1 a0 = l := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frpCmpA, upd_app, ↓reduceIte]
      rw [h20, add_lit_zero, ← hl]; exact load_frame hag (sXF.sub (c := 4 * j) (l := 4) (by omega)).symm
    have a11 : reg n1 a1 = r := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frpCmpA, upd_app, ↓reduceIte]
      rw [h9, add_lit_zero, ← hr]; exact load_frame hag (sNF.sub (c := 4 * j) (l := 4) (by omega)).symm
    have a21 : reg n1 a2 = b := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, frpCmpA, upd_app, ↓reduceIte]
      rw [hb19]; exact BitVec.zero_add _
    have K1 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n1 q = reg n q := fun q h0 h1 h2 => by
      rw [R1]; refine runBlock_reg _ _ _ q hz ?_
      simp only [frpCmpA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      simp [h0, h1, h2]
    have hsepB : Sep (G + 0xFFFFFFFC) 4 (BitVec.ofNat 32 borrowingSubAddress) borrowingSubCode.length :=
      sep_of_le (by
        rw [BitVec.toNat_add, show (0xFFFFFFFC : Word).toNat = 2 ^ 32 - 4 from rfl,
          show (BitVec.ofNat 32 borrowingSubAddress).toNat = (img% borrowingSubAddress) by decide]; omega) (by decide)
    obtain ⟨n2, c2, u2, a02, a12, sp2, K2, mem2⟩ := u1'.bsubCall hcx (hb Mx hag) (by decide) frp_at_a0 frp_at_a4
      (by decide) (by decide) (by rw [K1 sp (by decide) (by decide) (by decide), hsp]) hGa hsepB
    rw [a01, a11, a21] at a02 a12
    have hag2 : ∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → n2.mem x = Mb x := fun x hx => by rw [mem2 x hx, hag x hx]
    have hc2 := hc _ hag2
    obtain ⟨n3, c3, u3⟩ := St.block frpCmpB u2 hc2 frpCmpB_end (by
      simp only [BlockOk, BInstr.ok, frpCmpB]; exact ⟨trivial, trivial, trivial, trivial, trivial⟩)
    have R3 : ∀ q, reg n3 q = (runBlock frpCmpB (n2.mem, reg n2)).2 q := u3.regs
    have u3' : St n2.mem FRP n3 0xB0 (reg n3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
    have K2' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n2 q = reg n q :=
      fun q h0 h1 h2 h3 h4 hr => by rw [K2 q h0 h1 h2 h3 h4 hr, K1 q h0 h1 h2]
    obtain ⟨hval, hbm'⟩ := bsub_val l r b hbm
    have b3 : reg n3 (19 : Fin 32) = bsubB l r (bsubD l r b) := by
      rw [R3]; simp +decide only [runBlock, BInstr.run, frpCmpB, upd_app, ↓reduceIte]; rw [a12]; exact BitVec.zero_add _
    have x3 : reg n3 (20 : Fin 32) = X + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [R3]; simp +decide only [runBlock, BInstr.run, frpCmpB, upd_app, ↓reduceIte]
      rw [K2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h20]
      show X + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc, show 4 * j + 4 = 4 * (j + 1) by omega]
    have n3' : reg n3 (9 : Fin 32) = N + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [R3]; simp +decide only [runBlock, BInstr.run, frpCmpB, upd_app, ↓reduceIte]
      rw [K2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h9]
      show N + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc, show 4 * j + 4 = 4 * (j + 1) by omega]
    have c83 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 k := by
      rw [R3]; simp +decide only [runBlock, BInstr.run, frpCmpB, upd_app, ↓reduceIte]
      rw [K2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h8]
      exact frp_ofNat_dec k
    have K3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) →
        q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) → reg n3 q = reg n q := fun q h0 h1 h2 h3 h4 hr h8 h9 h19 h20 => by
      rw [R3, runBlock_reg _ _ _ q u2.zero (by
        simp only [frpCmpB, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
        simp [h8, h9, h19, h20]), K2' q h0 h1 h2 h3 h4 hr]
    obtain ⟨e1, e2⟩ := frp_chain hD hinv hval (bsubD l r b).isLt
    have hD' : D + (bsubD l r b).toNat * 2 ^ (32 * j) < 2 ^ (32 * (j + 1)) := by rw [pow32_succ]; exact e1
    have hinv' : D + (bsubD l r b).toNat * 2 ^ (32 * j) + accV Mb N (j + 1) =
        accV Mb X (j + 1) + 2 ^ (32 * (j + 1)) * maskBit (bsubB l r (bsubD l r b)) := by
      rw [accV_succ1, accV_succ1, hl, hr, pow32_succ]; exact e2
    clear e1 e2
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n4, d4, u4⟩ := u3'.notTaken hc2 0xB2 frp_at_b0 (by decide) (by
        simp only [branchTaken]; rw [c83, u3'.zero]; decide)
      have hj : j + 1 = 12 := by omega
      rw [hj] at hD' hinv'
      exact ⟨n4, n2.mem, _, c1.trans (c2.trans (c3.trans (.single d4))), u4.self, hag2, by rw [u4.regs, b3], hbm',
        ⟨_, hD', hinv'⟩, fun q h0 h1 h2 h3 h4 hr h8 h9 h19 h20 => by rw [u4.regs, K3 q h0 h1 h2 h3 h4 hr h8 h9 h19 h20]⟩
    · obtain ⟨n4, d4, u4⟩ := u3'.taken hc2 0x98 frp_at_b0 (by decide) (by
        simp only [branchTaken, c83, u3'.zero, bne_iff_ne, ne_eq]
        intro h; exact hk (by have := ofNat_inj (c := k) (d := 0) (by omega) (by decide) h; omega))
      obtain ⟨n5, Mf, b', c5, u5, hag5, hb5, hbm5, inv5, K5⟩ := ih (j + 1) n4 n2.mem _ (by omega) (by omega) u4.self
        hag2 (by rw [u4.regs, b3]) hbm' ⟨_, hD', hinv'⟩ (by rw [u4.regs, x3]) (by rw [u4.regs, n3']) (by rw [u4.regs, c83])
        (by rw [u4.regs, K3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), hsp])
      exact ⟨n5, Mf, b', c1.trans (c2.trans (c3.trans (.cons d4 c5))), u5, hag5, hb5, hbm5, inv5,
        fun q h0 h1 h2 h3 h4 hr h8 h9 h19 h20 => by
          rw [K5 q h0 h1 h2 h3 h4 hr h8 h9 h19 h20, u4.regs, K3 q h0 h1 h2 h3 h4 hr h8 h9 h19 h20]⟩

abbrev frpPs : List (Fin 32 × Word) :=
  [(ra, 0xAC), ((8 : Fin 32), 0xA8), ((9 : Fin 32), 0xA4), ((18 : Fin 32), 0xA0), ((19 : Fin 32), 0x9C),
   ((20 : Fin 32), 0x98)]

def frpPro : List BInstr := [.alu .add (8 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0x38]
def frpSet1 : List BInstr :=
  [.aluImm .add a0 sp 0x68, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0, .aluImm .add (19 : Fin 32) sp 0x68]
def frpSet2 : List BInstr :=
  [.aluImm .add a0 x0 0, .sw sp x0 4, .aluImm .add a6 x0 0xC, .lui a2 0x10000, .aluImm .add a3 a2 0xFFFFFF00,
   .aluImm .add (17 : Fin 32) x0 0xB]

section
set_option maxRecDepth 20000
theorem frpSave_end : blockEnd p384FromReprCode 2 (saveBlock frpPs) = some 0xE := by decide
theorem frpPro_end : blockEnd p384FromReprCode 0xE frpPro = some 0x14 := by decide
theorem frpSet1_end : blockEnd p384FromReprCode 0x1C frpSet1 = some 0x28 := by decide
theorem frpSet2_end : blockEnd p384FromReprCode 0x30 frpSet2 = some 0x3E := by decide
end

/-- The function's stack, `S = sp0 - 0x1A0` up to `sp0`: its frame at
`S + 0xF0` and the callees' frames below it. -/
theorem frp_S (sp0 : Word) (h : 0x1A0 ≤ sp0.toNat) :
    (sp0 + 0xFFFFFE60).toNat = sp0.toNat - 0x1A0 ∧ sp0 + 0xFFFFFF50 = sp0 + 0xFFFFFE60 + BitVec.ofNat 32 0xF0 := by
  refine ⟨?_, by rw [BitVec.add_assoc]; rfl⟩
  rw [BitVec.toNat_add, show (0xFFFFFE60 : Word).toNat = 2 ^ 32 - 0x1A0 from rfl]; have := sp0.isLt; omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- **The prologue**, from the entry to the byte loop at 0x42: save the
registers, zero the stack array and the limbs with `Array::default` and
`memset`, and zero the stack word. It writes only the 0x1A0 bytes of stack
below `sp0`. -/
theorem frp_pro (m : Machine) {sp0 out inp : Word} (hcF : CodeIn m.mem FRP p384FromReprCode)
    (hZ : CodeIn m.mem (BitVec.ofNat 32 zeroArray48Address) zeroArray48Code)
    (hMS : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode)
    (hMB : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode)
    (hMZ : CodeIn m.mem (BitVec.ofNat 32 memsetAddress) memsetCode)
    (hpc : m.pc = FRP) (ha0 : reg m a0 = out) (ha1 : reg m a1 = inp) (hsp : reg m sp = sp0)
    (hsp16 : sp0.toNat % 16 = 0) (hspl : 0x1A0 ≤ sp0.toNat) (hspw : sp0.toNat ≤ 0x40000000) :
    ∃ n M Ms, Steps m n ∧ St M FRP n 0x42 (reg n) ∧
      (∀ x, Sep (sp0 + 0xFFFFFE60) 0x1A0 x 1 → M x = m.mem x) ∧
      (∀ i, i < 0x18 → M (sp0 + 0xFFFFFE60 + BitVec.ofNat 32 (0x188 + i)) =
        Ms (sp0 + 0xFFFFFE60 + BitVec.ofNat 32 (0x188 + i))) ∧
      (∀ r o, (r, o) ∈ frpPs → memLoad32 Ms (sp0 + 0xFFFFFF50 + o) = reg m r) ∧
      reg n sp = sp0 + 0xFFFFFF50 ∧ reg n a0 = BitVec.ofNat 32 0 ∧ reg n (8 : Fin 32) = inp + BitVec.ofNat 32 (4 * 0) ∧
      reg n a6 = 12 ∧ reg n a3 = 0xFF00 ∧ reg n (17 : Fin 32) = 11 ∧
      reg n (19 : Fin 32) = sp0 + 0xFFFFFE60 + BitVec.ofNat 32 0x158 ∧ reg n (18 : Fin 32) = out ∧
      ∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg n q = reg m q := by
  obtain ⟨hSn, hGS⟩ := frp_S sp0 hspl
  obtain ⟨S, hS⟩ : ∃ S, sp0 + 0xFFFFFE60 = S := ⟨_, rfl⟩
  rw [hS] at hSn hGS ⊢
  rw [hGS]
  have hSc : ∀ c, c ≤ 0x1A0 → (S + BitVec.ofNat 32 c).toNat = S.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hSa : S.toNat % 16 = 0 := by omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x1A0 → d + k ≤ 0x1A0 →
      Sep (S + BitVec.ofNat 32 c) n (S + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets S h (by omega) (by omega)
  have inS : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x1A0 → Sep S 0x1A0 x 1 → Sep (S + BitVec.ofNat 32 c) l x 1 :=
    fun h hx => hx.sub h
  have hi : ∀ {c l : Nat} (b : Word) (k : Nat), c + l ≤ 0x1A0 → 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (S + BitVec.ofNat 32 c) l b k := fun b k h h1 h2 => sep_of_le (by rw [hSc _ (by omega)]; omega) h2
  have Shi : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep S 0x1A0 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hFRn : FRP.toNat = (img% p384FromReprAddress) := by decide
  have Gc : ∀ c, S + BitVec.ofNat 32 0xF0 + BitVec.ofNat 32 c = S + BitVec.ofNat 32 (0xF0 + c) :=
    fun c => add_ofNat_assoc _ _ _
  have st0 : St m.mem FRP m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hcF frp_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF50) sp = S + BitVec.ofNat 32 0xF0 := by
    simp +decide only [upd, ↓reduceIte]; rw [hsp]; exact hGS
  have slotO : ∀ o : Word, 0x98 ≤ o.toNat → o.toNat + 4 ≤ 0xB0 →
      S + BitVec.ofNat 32 0xF0 + o = S + BitVec.ofNat 32 (0xF0 + o.toNat) := fun o _ _ => by
    rw [← Gc, ofNat_toNat_self]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock frpPs) u1 hcF frpSave_end (saveBlock_ok _ frpPs _ fun q hq => by
      rw [sp1]
      simp only [frpPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add (aligned_add (by omega) (by decide)) (by decide),
          by rw [slotO _ (by decide) (by decide)]; exact hi _ _ (by decide) (by rw [hFRn]; decide) (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem (S + BitVec.ofNat 32 0xF0) (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF50))
      frpPs = Ms := ⟨_, rfl⟩
  rw [hMs] at u2
  have IMs : ∀ x, Sep S 0x1A0 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside frpPs fun q hq => by
      simp only [frpPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
        (rw [slotO _ (by decide) (by decide)]; exact inS (by decide) hx)
  have slots : ∀ r o, (r, o) ∈ frpPs → memLoad32 Ms (S + BitVec.ofNat 32 0xF0 + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [frpPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot frpPs _ hm (by
      simp only [frpPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide),
      upd_ne (by
        simp only [frpPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hr]
  have cd : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep S 0x1A0 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc h1 h2 hM i hi => by rw [hM _ (Shi _ (code_hi h1 h2 hi))]; exact hc i hi
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = S + BitVec.ofNat 32 0xF0 := by rw [u2.regs]; exact sp1
  have hc2 := cd hcF (by rw [hFRn]; decide) (by rw [hFRn]; decide) IMs
  obtain ⟨m3, c3, u3⟩ := St.block frpPro u2.self hc2 frpPro_end (by
    simp only [BlockOk, BInstr.ok, frpPro]; exact ⟨trivial, trivial, trivial, trivial⟩)
  have R3 : ∀ q, reg m3 q = (runBlock frpPro (Ms, reg m2)).2 q := u3.regs
  have u3' : St Ms FRP m3 0x14 (reg m3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  have s03 : reg m3 (8 : Fin 32) = inp := by
    rw [R3]; simp +decide only [runBlock, BInstr.run, frpPro, upd_app, ↓reduceIte]
    rw [r2 a1 (by decide), ha1]; exact BitVec.zero_add _
  have s23 : reg m3 (18 : Fin 32) = out := by
    rw [R3]; simp +decide only [runBlock, BInstr.run, frpPro, upd_app, ↓reduceIte]
    rw [r2 a0 (by decide), ha0]; exact BitVec.zero_add _
  have a03 : reg m3 a0 = S + BitVec.ofNat 32 0x128 := by
    rw [R3]; simp +decide only [runBlock, BInstr.run, frpPro, upd_app, ↓reduceIte]
    rw [sp2]; exact Gc 0x38
  have sp3 : reg m3 sp = S + BitVec.ofNat 32 0xF0 := by
    rw [R3]; simp +decide only [runBlock, BInstr.run, frpPro, upd_app, ↓reduceIte]; exact sp2
  have K3 : ∀ q, q ≠ sp → q ≠ a0 → q ≠ (8 : Fin 32) → q ≠ (18 : Fin 32) → reg m3 q = reg m q := fun q h2 h0 h8 h18 => by
    rw [R3]; refine (runBlock_reg _ _ _ q u2.self.zero ?_).trans (r2 q h2)
    simp only [frpPro, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h8, h18]
  -- `Array::default`
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3'.callRa hc2 frp_at_14 frp_at_18
    (show FRP + BitVec.ofNat 32 0x14 + 0xA000 + 0xFFFFFB5A = BitVec.ofNat 32 zeroArray48Address by decide) (by decide)
  have r4 : ∀ q, q ≠ ra → reg m4 q = reg m3 q := fun q h => by rw [regs4]; exact updz u3'.zero h
  have eZ : S + BitVec.ofNat 32 0xF0 + 0xFFFFFFB0 = S + BitVec.ofNat 32 0xA0 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m5, c5, pc5, sp5, K5, fr5⟩ := zeroArray48_correct m4 (d := S + BitVec.ofNat 32 0x128)
    (T := S + BitVec.ofNat 32 0xF0) (retAddr := FRP + BitVec.ofNat 32 (0x14 + 8))
    (by rw [mem4]; exact cd hZ (by decide) (by decide) IMs)
    (by rw [mem4]; exact cd hMS (by decide) (by decide) IMs)
    (by rw [mem4]; exact cd hMB (by decide) (by decide) IMs)
    pc4 (by rw [r4 a0 (by decide), a03]) (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at FRP (by decide) _ (by omega))) (by rw [r4 sp (by decide), sp3])
    (by rw [hSc _ (by omega)]; omega) (by rw [hSc _ (by omega)]; omega) (by rw [hSc _ (by omega)]; omega)
    (by rw [hSc _ (by omega)]; omega) (by rw [eZ]; exact offs (by omega) (by omega) (by omega))
  rw [eZ, mem4] at fr5
  have M5 : ∀ x, Sep S 0x1A0 x 1 → m5.mem x = m.mem x := fun x hx => by
    rw [fr5 x (inS (by omega) hx), fillBytes_sep (inS (c := 0x128) (l := 48) (by omega) hx) (Nat.le_refl _), IMs x hx]
  have V5 : ∀ i, i < 0x18 → m5.mem (S + BitVec.ofNat 32 (0x188 + i)) = Ms (S + BitVec.ofNat 32 (0x188 + i)) :=
    fun i hi => by
      rw [fr5 _ (offs (by omega) (by omega) (by omega)), fillBytes_sep (offs (by omega) (by omega) (by omega))
        (Nat.le_refl _)]
  have k5 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m5 q = reg m3 q :=
    fun q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 => by
      rw [K5 q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13, r4 q h14]
  have hc5 := cd hcF (by rw [hFRn]; decide) (by rw [hFRn]; decide) M5
  have u5 : St m5.mem FRP m5 0x1C (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have sp5' : reg m5 sp = S + BitVec.ofNat 32 0xF0 := by
    rw [k5 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp3]
  obtain ⟨m6, c6, u6⟩ := St.block frpSet1 u5 hc5 frpSet1_end (by
    simp only [BlockOk, BInstr.ok, frpSet1]; exact ⟨trivial, trivial, trivial, trivial, trivial⟩)
  have R6 : ∀ q, reg m6 q = (runBlock frpSet1 (m5.mem, reg m5)).2 q := u6.regs
  have u6' : St m5.mem FRP m6 0x28 (reg m6) := ⟨u6.pc, by rw [u6.mem]; rfl, fun _ => rfl⟩
  have K6 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (19 : Fin 32) → reg m6 q = reg m5 q := fun q h0 h1 h2 h19 => by
    rw [R6]; refine runBlock_reg _ _ _ q u5.zero ?_
    simp only [frpSet1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2, h19]
  have eX : S + BitVec.ofNat 32 0xF0 + 0x68 = S + BitVec.ofNat 32 0x158 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m7, c7, u7, _, K7⟩ := u6'.memsetW (B := BitVec.ofNat 32 memsetAddress) (w := 12)
    (dst := S + BitVec.ofNat 32 0x158) (by decide) hc5 (cd hMZ (by decide) (by decide) M5) frp_at_28 frp_at_2c
    (by decide) (by decide) (by decide) (by rw [hSc _ (by omega)]; omega) (by decide)
    (aligned_add (by omega) (by decide)) (hi _ _ (by omega) (by decide) (by decide))
    (by rw [R6]; simp +decide only [runBlock, BInstr.run, frpSet1, upd_app, ↓reduceIte]; rw [sp5']; exact eX)
    (by rw [R6]; simp +decide only [runBlock, BInstr.run, frpSet1, upd_app, ↓reduceIte])
    (by rw [R6]; simp +decide only [runBlock, BInstr.run, frpSet1, upd_app, ↓reduceIte])
  obtain ⟨M7, hM7⟩ : ∃ M7, fillWords m5.mem (S + BitVec.ofNat 32 0x158) 0 12 = M7 := ⟨_, rfl⟩
  rw [hM7] at u7
  have M7o : ∀ x, Sep (S + BitVec.ofNat 32 0x158) 48 x 1 → M7 x = m5.mem x := fun x hx => by
    rw [← hM7]; exact fillWords_outside 12 hx
  have hc7 : CodeIn M7 FRP p384FromReprCode := cd hcF (by rw [hFRn]; decide) (by rw [hFRn]; decide) fun x hx => by
    rw [M7o x (inS (by omega) hx), M5 x hx]
  have r7 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ a0 → q ≠ a1 → q ≠ (19 : Fin 32) →
      reg m7 q = reg m5 q := fun q h2 h3 h4 h5 h6 hr h0 h1 h19 => by
    rw [K7 q h2 h3 h4 h5 h6 hr, K6 q h0 h1 h2 h19]
  have sp7 : reg m7 sp = S + BitVec.ofNat 32 0xF0 := by
    rw [r7 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), sp5']
  have s37 : reg m7 (19 : Fin 32) = S + BitVec.ofNat 32 0x158 := by
    rw [K7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), R6]
    simp +decide only [runBlock, BInstr.run, frpSet1, upd_app, ↓reduceIte]; rw [sp5']; exact eX
  have eT : S + BitVec.ofNat 32 0xF0 + 4 = S + BitVec.ofNat 32 0xF4 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m8, c8, u8⟩ := St.block frpSet2 u7 hc7 frpSet2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, frpSet2, upd_app, ↓reduceIte, and_true]
    rw [sp7, eT]
    exact ⟨trivial, aligned_add (by omega) (by decide), hi _ _ (by omega) (by rw [hFRn]; decide) (by decide)⟩)
  have R8 : ∀ q, reg m8 q = (runBlock frpSet2 (M7, reg m7)).2 q := u8.regs
  have M8e : (runBlock frpSet2 (M7, reg m7)).1 = memStore32 M7 (S + BitVec.ofNat 32 0xF4) 0 := by
    simp +decide only [runBlock, BInstr.run, frpSet2, upd_app, ↓reduceIte]; rw [sp7, eT]
  obtain ⟨M8, hM8⟩ : ∃ M8, memStore32 M7 (S + BitVec.ofNat 32 0xF4) 0 = M8 := ⟨_, rfl⟩
  rw [hM8] at M8e
  have u8' : St M8 FRP m8 0x3E (reg m8) := ⟨u8.pc, by rw [u8.mem, M8e], fun _ => rfl⟩
  have M8o : ∀ x, Sep S 0x1A0 x 1 → M8 x = m.mem x := fun x hx => by
    rw [← hM8, memStore32_get_sep (inS (by omega) hx), M7o x (inS (by omega) hx), M5 x hx]
  have hc8 := cd hcF (by rw [hFRn]; decide) (by rw [hFRn]; decide) M8o
  have K8 : ∀ q, q ≠ a0 → q ≠ a6 → q ≠ a2 → q ≠ a3 → q ≠ (17 : Fin 32) → reg m8 q = reg m7 q :=
    fun q h0 h6 h2 h3 h17 => by
      rw [R8]; refine runBlock_reg _ _ _ q u7.zero ?_
      simp only [frpSet2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h6, h2, h3, h17]
  have a68 : reg m8 a6 = 12 := by rw [R8]; simp +decide only [runBlock, BInstr.run, frpSet2, upd_app, ↓reduceIte]
  obtain ⟨m9, d9, u9⟩ := u8'.notTaken hc8 0x42 frp_at_3e (by decide) (by
    simp only [branchTaken]; rw [a68, u8'.zero]; decide)
  have g9 : ∀ q, reg m9 q = reg m8 q := u9.regs
  refine ⟨m9, M8, Ms, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans
    (.single d9)))))))), u9.self, M8o, fun i hi => ?_, slots, ?_, ?_, ?_, by rw [g9, a68], ?_, ?_, ?_, ?_,
    fun q hq => ?_⟩
  · rw [← hM8, memStore32_get_sep (offs (by omega) (by omega) (by omega)),
      M7o _ (offs (by omega) (by omega) (by omega)), V5 i hi]
  · rw [g9, K8 sp (by decide) (by decide) (by decide) (by decide) (by decide), sp7]
  · rw [g9, R8]; simp +decide only [runBlock, BInstr.run, frpSet2, upd_app, ↓reduceIte]; rw [u7.zero]; rfl
  · rw [g9, K8 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      r7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), s03, add_ofNat_zero]
  · rw [g9, R8]; simp +decide only [runBlock, BInstr.run, frpSet2, upd_app, ↓reduceIte]
  · rw [g9, R8]; simp +decide only [runBlock, BInstr.run, frpSet2, upd_app, ↓reduceIte]
  · rw [g9, K8 _ (by decide) (by decide) (by decide) (by decide) (by decide), s37]
  · rw [g9, K8 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      r7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), s23]
  · obtain ⟨h0, h6, h2, h3, h17, h1, h4, h5, hr, h19, h7, ht0, ht1, h7', h28, h29, h30, hsp', h8, h18⟩ :=
      (by decide : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ a0 ∧ q ≠ a6 ∧ q ≠ a2 ∧ q ≠ a3 ∧
        q ≠ (17 : Fin 32) ∧ q ≠ a1 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ ra ∧ q ≠ (19 : Fin 32) ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧
        q ≠ (7 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ sp ∧ q ≠ (8 : Fin 32) ∧
        q ≠ (18 : Fin 32)) q hq
    rw [g9, K8 q h0 h6 h2 h3 h17, r7 q h2 h3 h4 h5 h6 hr h0 h1 h19,
      k5 q h1 h2 h3 h4 h5 h6 h7 ht0 ht1 h7' h28 h29 h30 hr, K3 q hsp' h0 h8 h18]

/-- Where the image keeps P-384's field modulus; `R² mod p` is 0x60 bytes on. -/
abbrev p384Np : Word := (img% p384ModulusAddress)

/-- The code `from_repr` runs, where the image loads it, and the two facts
about the modulus data that its Montgomery multiplication needs. -/
structure FRPEnv (M : Word → BitVec 8) : Prop where
  fr : CodeIn M FRP p384FromReprCode
  za : CodeIn M (BitVec.ofNat 32 zeroArray48Address) zeroArray48Code
  ms : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  cs : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cb : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  bs : CodeIn M (BitVec.ofNat 32 borrowingSubAddress) borrowingSubCode
  nz : CodeIn M (BitVec.ofNat 32 uintRefIsNonzeroAddress) uintRefIsNonzeroCode
  mm : CodeIn M (BitVec.ofNat 32 mulMont12Address) mulMont12Code
  sel : CodeIn M (BitVec.ofNat 32 uintSelect12Address) uintSelect12Code
  bb : CodeIn M (BitVec.ofNat 32 blackBoxU8Address) blackBoxU8Code
  csel : CodeIn M (BitVec.ofNat 32 condSelect384Address) condSelect384Code
  cta : CodeIn M (BitVec.ofNat 32 uint12CtAssignAddress) uint12CtAssignCode
  sca : CodeIn M (BitVec.ofNat 32 sliceCtAssignAddress) sliceCtAssignCode
  nlo : memLoad32 M p384Np = 0xFFFFFFFF
  r2lt : accV M (p384Np + 0x60) 12 < accV M p384Np 12

/-- A call to `UintRef::is_nonzero` on no words: it returns 0. -/
theorem St.nzCall0 {Mx : Word → BitVec 8} {P F ptr : Word} {code : List Nat} {m : Machine} {off : Nat}
    {f : Fin 32 → Word} {imm o : Word} (s : St Mx P m off f) (hc : CodeIn Mx P code)
    (hb : CodeIn Mx (BitVec.ofNat 32 uintRefIsNonzeroAddress) uintRefIsNonzeroCode)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hcb : P + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 uintRefIsNonzeroAddress)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (ha0 : f a0 = ptr) (ha1 : f a1 = 0)
    (hptr : ptr.toNat % 4 = 0) (hsp : f sp = F) (hF : F.toNat % 4 = 0)
    (hsep : Sep (F + 0xFFFFFFFC) 4 (BitVec.ofNat 32 uintRefIsNonzeroAddress) uintRefIsNonzeroCode.length) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧ reg m' a0 = 0 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → reg m' q = f q) ∧
      ∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → m'.mem x = Mx x := by
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hcb (by decide)
  have r1 : ∀ q, q ≠ ra → reg m1 q = f q := PEnv.reg1 regs1 s.zero
  obtain ⟨m2, c2, pc2, a02, fr2, mem2⟩ := uintRefIsNonzero_correct m1 (len := 0) (ptr := ptr)
    (by rw [mem1]; exact hb) pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]; rfl) (by decide)
    hptr (by rw [r1 sp (by decide), hsp]; exact hF) (by rw [r1 sp (by decide), hsp]; exact hsep)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl)
  rw [r1 sp (by decide), hsp, mem1] at mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, ?_, fun q q0 q1 q2 q3 qr => ?_, mem2⟩
  · rw [a02, ite_eq_left (fun i h => absurd h (Nat.not_lt_zero _))]
  · rw [fr2 q q0 q1 q2 q3, r1 q qr]

def frpT1 : List BInstr :=
  [.lui (8 : Fin 32) 0x3FCC5000, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFCF4, .aluImm .add a0 (8 : Fin 32) 0x30,
   .aluImm .add a1 x0 0]
def frpT2 : List BInstr :=
  [.aluImm .add a1 sp 0x98, .aluImm .and (9 : Fin 32) a0 0xFF, .alu .add a0 x0 a1, .aluImm .add a1 x0 0]
def frpT3 : List BInstr :=
  [.aluImm .and a0 a0 0xFF, .aluImm .xor a0 a0 0xFFFFFFFF, .alu .and a0 (19 : Fin 32) a0, .aluImm .and a0 a0 1,
   .alu .or (9 : Fin 32) (9 : Fin 32) a0, .aluImm .add a2 (8 : Fin 32) 0x60, .aluImm .add a0 sp 4,
   .aluImm .add a1 sp 0x68, .aluImm .add a4 x0 1, .alu .add a3 x0 (8 : Fin 32)]

section
set_option maxRecDepth 20000
theorem frpT1_end : blockEnd p384FromReprCode 0xB2 frpT1 = some 0xC0 := by decide
theorem frpT2_end : blockEnd p384FromReprCode 0xC8 frpT2 = some 0xD2 := by decide
theorem frpT3_end : blockEnd p384FromReprCode 0xDA frpT3 = some 0xF6 := by decide
end

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- From 0xB2 to 0xFE: the two `is_nonzero` calls on no words return 0, so
the choice is the comparison's borrow bit, in `s1`; then
`mul_montgomery_form::<12>` puts the limbs at `X = S + 0x158` times `R²` in
Montgomery form at `T = S + 0xF4`. -/
theorem frp_tailA {M0 : Word → BitVec 8} (E : FRPEnv M0) (n : Machine) {S b : Word}
    (st : St n.mem FRP n 0xB2 (reg n)) (hf : ∀ x, Sep S 0x1A0 x 1 → n.mem x = M0 x)
    (hSa : S.toNat % 16 = 0) (hSw : S.toNat + 0x1A0 ≤ 0x40000000) (sSN : Sep S 0x1A0 p384Np 0x90)
    (hsp : reg n sp = S + BitVec.ofNat 32 0xF0) (h19 : reg n (19 : Fin 32) = b) :
    ∃ n', Steps n n' ∧ St n'.mem FRP n' 0xFE (reg n') ∧
      (∀ x, Sep S 0xF0 x 1 → Sep (S + BitVec.ofNat 32 0xF4) 48 x 1 → n'.mem x = n.mem x) ∧
      accV n'.mem (S + BitVec.ofNat 32 0xF4) 12 < accV M0 p384Np 12 ∧
      accV n'.mem (S + BitVec.ofNat 32 0xF4) 12 * 2 ^ 384 % accV M0 p384Np 12 =
        accV n.mem (S + BitVec.ofNat 32 0x158) 12 * accV M0 (p384Np + 0x60) 12 % accV M0 p384Np 12 ∧
      reg n' sp = S + BitVec.ofNat 32 0xF0 ∧ reg n' (9 : Fin 32) = b &&& 1 ∧
      ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q := by
  have hSc : ∀ c, c ≤ 0x1A0 → (S + BitVec.ofNat 32 c).toNat = S.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x1A0 → d + k ≤ 0x1A0 →
      Sep (S + BitVec.ofNat 32 c) n (S + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets S h (by omega) (by omega)
  have inS : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x1A0 → Sep S 0x1A0 x 1 → Sep (S + BitVec.ofNat 32 c) l x 1 :=
    fun h hx => hx.sub h
  have hi : ∀ {c l : Nat} (b : Word) (k : Nat), c + l ≤ 0x1A0 → 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (S + BitVec.ofNat 32 c) l b k := fun b k h h1 h2 => sep_of_le (by rw [hSc _ (by omega)]; omega) h2
  have Shi : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep S 0x1A0 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hFRn : FRP.toNat = (img% p384FromReprAddress) := by decide
  have cd : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep S 0x1A0 x 1 → M' x = M0 x) → CodeIn M' b code :=
    fun hc h1 h2 hM i hi => by rw [hM _ (Shi _ (code_hi h1 h2 hi))]; exact hc i hi
  have eF4 : S + BitVec.ofNat 32 0xF0 + 0xFFFFFFFC = S + BitVec.ofNat 32 0xEC := by rw [BitVec.add_assoc]; rfl
  have Gc : ∀ c, S + BitVec.ofNat 32 0xF0 + BitVec.ofNat 32 c = S + BitVec.ofNat 32 (0xF0 + c) :=
    fun c => add_ofNat_assoc _ _ _
  have hGa : (S + BitVec.ofNat 32 0xF0).toNat % 4 = 0 := aligned_add (by omega) (by decide)
  have hc0 := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) hf
  obtain ⟨n1, c1, u1⟩ := St.block frpT1 st hc0 frpT1_end (by
    simp only [BlockOk, BInstr.ok, frpT1]; exact ⟨trivial, trivial, trivial, trivial, trivial⟩)
  have R1 : ∀ q, reg n1 q = (runBlock frpT1 (n.mem, reg n)).2 q := u1.regs
  have u1' : St n.mem FRP n1 0xC0 (reg n1) := ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩
  have s01 : reg n1 (8 : Fin 32) = p384Np := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, frpT1, upd_app, ↓reduceIte]
  have K1 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ (8 : Fin 32) → reg n1 q = reg n q := fun q h0 h1 h8 => by
    rw [R1]; refine runBlock_reg _ _ _ q st.zero ?_
    simp only [frpT1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h8]
  have hsepZ : Sep (S + BitVec.ofNat 32 0xEC) 4 (BitVec.ofNat 32 uintRefIsNonzeroAddress)
      uintRefIsNonzeroCode.length := hi _ _ (by omega) (by decide) (by decide)
  obtain ⟨n2, c2, u2, a02, K2, mem2⟩ := u1'.nzCall0 (ptr := p384Np + 0x30) hc0 (cd E.nz (by decide) (by decide) hf) frp_at_c0 frp_at_c4
    (by decide) (by decide) (by rw [R1]; simp +decide only [runBlock, BInstr.run, frpT1, upd_app, ↓reduceIte])
    (by rw [R1]; simp +decide only [runBlock, BInstr.run, frpT1, upd_app, ↓reduceIte]) (by decide)
    (by rw [K1 sp (by decide) (by decide) (by decide), hsp]) hGa (by rw [eF4]; exact hsepZ)
  rw [eF4] at mem2
  have M2 : ∀ x, Sep S 0x1A0 x 1 → n2.mem x = M0 x := fun x hx => by
    rw [mem2 x (inS (by omega) hx), hf x hx]
  have hc2 := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) M2
  obtain ⟨n3, c3, u3⟩ := St.block frpT2 u2 hc2 frpT2_end (by
    simp only [BlockOk, BInstr.ok, frpT2]; exact ⟨trivial, trivial, trivial, trivial, trivial⟩)
  have R3 : ∀ q, reg n3 q = (runBlock frpT2 (n2.mem, reg n2)).2 q := u3.regs
  have u3' : St n2.mem FRP n3 0xD2 (reg n3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  have r2 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → q ≠ (8 : Fin 32) → reg n2 q = reg n q :=
    fun q h0 h1 h2 h3 hr h8 => by rw [K2 q h0 h1 h2 h3 hr, K1 q h0 h1 h8]
  have sp2 : reg n2 sp = S + BitVec.ofNat 32 0xF0 := by
    rw [r2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsp]
  have K3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ (9 : Fin 32) → reg n3 q = reg n2 q := fun q h0 h1 h9 => by
    rw [R3]; refine runBlock_reg _ _ _ q u2.zero ?_
    simp only [frpT2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h9]
  obtain ⟨n4, c4, u4, a04, K4, mem4⟩ := u3'.nzCall0 (ptr := S + BitVec.ofNat 32 0x188) hc2 (cd E.nz (by decide) (by decide) M2) frp_at_d2 frp_at_d6
    (by decide) (by decide) (by
      rw [R3]; simp +decide only [runBlock, BInstr.run, frpT2, upd_app, ↓reduceIte]
      rw [sp2]; exact (BitVec.zero_add _).trans (Gc 0x98))
    (by rw [R3]; simp +decide only [runBlock, BInstr.run, frpT2, upd_app, ↓reduceIte])
    (aligned_add (by omega) (by decide))
    (by rw [K3 sp (by decide) (by decide) (by decide), sp2]) hGa (by rw [eF4]; exact hsepZ)
  rw [eF4] at mem4
  have M4 : ∀ x, Sep S 0x1A0 x 1 → n4.mem x = M0 x := fun x hx => by
    rw [mem4 x (inS (by omega) hx), M2 x hx]
  have hc4 := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) M4
  have s14 : reg n4 (9 : Fin 32) = 0 := by
    rw [K4 _ (by decide) (by decide) (by decide) (by decide) (by decide), R3]
    simp +decide only [runBlock, BInstr.run, frpT2, upd_app, ↓reduceIte]; rw [a02]; rfl
  have r4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) →
      reg n4 q = reg n q := fun q h0 h1 h2 h3 hr h8 h9 => by
    rw [K4 q h0 h1 h2 h3 hr, K3 q h0 h1 h9, r2 q h0 h1 h2 h3 hr h8]
  have sp4 : reg n4 sp = S + BitVec.ofNat 32 0xF0 := by
    rw [r4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsp]
  have s04 : reg n4 (8 : Fin 32) = p384Np := by
    rw [K4 _ (by decide) (by decide) (by decide) (by decide) (by decide), K3 _ (by decide) (by decide) (by decide),
      K2 _ (by decide) (by decide) (by decide) (by decide) (by decide), s01]
  obtain ⟨n5, c5, u5⟩ := St.block frpT3 u4 hc4 frpT3_end (by
    simp only [BlockOk, BInstr.ok, frpT3]
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩)
  have R5 : ∀ q, reg n5 q = (runBlock frpT3 (n4.mem, reg n4)).2 q := u5.regs
  have u5' : St n4.mem FRP n5 0xF6 (reg n5) := ⟨u5.pc, by rw [u5.mem]; rfl, fun _ => rfl⟩
  have s15 : reg n5 (9 : Fin 32) = b &&& 1 := by
    rw [R5]; simp +decide only [runBlock, BInstr.run, frpT3, upd_app, ↓reduceIte]
    rw [s14, a04, r4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h19]
    show (0 : Word) ||| ((b &&& (((0 : Word) &&& 0xFF) ^^^ 0xFFFFFFFF)) &&& 1) = b &&& 1
    rw [show ((0 : Word) &&& 0xFF) ^^^ 0xFFFFFFFF = 0xFFFFFFFF by decide, and_ones]; exact BitVec.zero_or
  have K5 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (9 : Fin 32) → reg n5 q = reg n4 q :=
    fun q h0 h1 h2 h3 h4 h9 => by
      rw [R5]; refine runBlock_reg _ _ _ q u4.zero ?_
      simp only [frpT3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2, h3, h4, h9]
  have rv5 : reg n5 a0 = S + BitVec.ofNat 32 0xF4 ∧ reg n5 a1 = S + BitVec.ofNat 32 0x158 ∧
      reg n5 a2 = p384Np + 0x60 ∧ reg n5 a3 = p384Np ∧ reg n5 a4 = 1 := by
    simp only [R5]; simp +decide only [runBlock, BInstr.run, frpT3, upd_app, ↓reduceIte]
    rw [sp4, s04]
    exact ⟨Gc 4, Gc 0x68, rfl, BitVec.zero_add _, trivial⟩
  -- `mul_montgomery_form::<12>`
  obtain ⟨m6, c6, pc6, mem6, regs6⟩ := u5'.callRa hc4 frp_at_f6 frp_at_fa
    (show FRP + BitVec.ofNat 32 0xF6 + 0xF000 + 0x62 = BitVec.ofNat 32 mulMont12Address by decide) (by decide)
  have r6 : ∀ q, q ≠ ra → reg m6 q = reg n5 q := PEnv.reg1 regs6 u5'.zero
  have M6 : ∀ x, Sep S 0x1A0 x 1 → m6.mem x = M0 x := fun x hx => by rw [mem6]; exact M4 x hx
  have eS : S + BitVec.ofNat 32 0xF0 + 0xFFFFFF10 = S := by rw [BitVec.add_assoc]; exact BitVec.add_zero S
  have o0 : ∀ {d k : Nat}, 0xF0 ≤ d → d + k ≤ 0x1A0 → Sep S 0xF0 (S + BitVec.ofNat 32 d) k := fun h1 h2 => by
    have := offs (c := 0) (n := 0xF0) (.inl h1) (by omega) h2; rwa [add_ofNat_zero] at this
  have h0hi : ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 → Sep S 0xF0 b k :=
    fun b k h1 h2 => by have := hi (c := 0) (l := 0xF0) b k (by omega) h1 h2; rwa [add_ofNat_zero] at this
  have sNS : Sep p384Np 48 S 0xF0 := by
    have := (sSN.symm.sub (c := 0) (l := 48) (by omega)).subR (c := 0) (l := 0xF0) (by omega)
    rwa [add_ofNat_zero, add_ofNat_zero] at this
  have sYS : Sep (p384Np + 0x60) 48 S 0xF0 := by
    have := (sSN.symm.sub (c := 0x60) (l := 48) (by omega)).subR (c := 0) (l := 0xF0) (by omega)
    rwa [add_ofNat_zero] at this
  have hP : BitVec.ofNat 32 mulMont12Address = BitVec.ofNat 32 mulMont12Address := rfl
  have EM : MMEnv m6.mem (BitVec.ofNat 32 mulMont12Address) (S + BitVec.ofNat 32 0xF0) (S + BitVec.ofNat 32 0xF4)
      (S + BitVec.ofNat 32 0x158) (p384Np + 0x60) p384Np := by
    refine ⟨by decide, cd E.mm (by decide) (by decide) M6,
      by rw [show BitVec.ofNat 32 mulMont12Address + 0x1B0C = BitVec.ofNat 32 memsetAddress by decide]
         exact cd E.ms (by decide) (by decide) M6,
      by rw [show mmBsub (BitVec.ofNat 32 mulMont12Address) = BitVec.ofNat 32 borrowingSubAddress by decide]
         exact cd E.bs (by decide) (by decide) M6,
      by rw [show BitVec.ofNat 32 mulMont12Address + 0x18E = BitVec.ofNat 32 uintSelect12Address by decide]
         exact cd E.sel (by decide) (by decide) M6,
      by rw [show BitVec.ofNat 32 mulMont12Address + 0x1B74 = BitVec.ofNat 32 memcpyStubAddress by decide]
         exact cd E.cs (by decide) (by decide) M6,
      by rw [show BitVec.ofNat 32 mulMont12Address + 0x1B7C = BitVec.ofNat 32 memcpyStubAddress + 8 by decide]
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
  have NT : ∀ {M : Word → BitVec 8} {b : Word} {l : Nat}, (∀ x, Sep S 0x1A0 x 1 → M x = M0 x) →
      Sep S 0x1A0 b (4 * l) → accV M b l = accV M0 b l := fun hM hs =>
    accV_congr _ fun i hi => memLoad32_congr fun j hj => hM _ (hs.subR (c := 4 * i + j) (l := 1) (by omega)) |>
      fun h => by rw [← add_ofNat_assoc] at h; exact h
  have sNS' : Sep S 0x1A0 p384Np (4 * 12) := sSN.subR (c := 0) (l := 48) (by omega) |> fun h => by
    rwa [add_ofNat_zero] at h
  have sYS' : Sep S 0x1A0 (p384Np + 0x60) (4 * 12) := sSN.subR (c := 0x60) (l := 48) (by omega)
  obtain ⟨m7, c7, pc7, sp7, hlt7, heq7, fr7, K7⟩ := mulMont12_correct m6 (retAddr := FRP + BitVec.ofNat 32 (0xF6 + 8)) EM pc6
    (by rw [r6 a0 (by decide), ha5]) (by rw [r6 a1 (by decide), hb5]) (by rw [r6 a2 (by decide), hc5])
    (by rw [r6 a3 (by decide), hd5]) (by rw [r6 a4 (by decide), he5])
    (by rw [regs6]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at FRP (by decide) _ (by decide)))
    (by rw [r6 sp (by decide), K5 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp4])
    (by
      rw [load_frame (n := 0x1A0) (acc := S) (M0 := M0) M6 (sSN.subR (c := 0) (l := 4) (by omega) |> fun h => by
        rwa [add_ofNat_zero] at h), E.nlo]; decide)
    (by rw [NT M6 sYS', NT M6 sNS']; exact E.r2lt)
  rw [NT M6 sNS', NT M6 sYS'] at heq7
  rw [NT M6 sNS'] at hlt7
  rw [eS] at fr7
  have hX : accV m6.mem (S + BitVec.ofNat 32 0x158) 12 = accV n.mem (S + BitVec.ofNat 32 0x158) 12 := by
    rw [mem6]
    apply accV_congr; intro i hi; apply memLoad32_congr; intro j hj
    have hs : Sep (S + BitVec.ofNat 32 0xEC) 4 (S + BitVec.ofNat 32 0x158 + BitVec.ofNat 32 (4 * i) +
        BitVec.ofNat 32 j) 1 := by
      rw [add_ofNat_assoc, add_ofNat_assoc]; exact offs (by omega) (by omega) (by omega)
    rw [mem4 _ hs, mem2 _ hs]
  rw [hX] at heq7
  have u7 : St m7.mem FRP m7 0xFE (reg m7) := ⟨by rw [pc7], rfl, fun _ => rfl⟩
  refine ⟨m7, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans c7))))), u7, fun x h1 h2 => ?_, hlt7,
    heq7, sp7, ?_, fun q hq => ?_⟩
  · rw [fr7 x h1 h2, mem6, mem4 x (h1.sub (c := 0xEC) (l := 4) (by omega)),
      mem2 x (h1.sub (c := 0xEC) (l := 4) (by omega))]
  · rw [K7 _ (by decide), r6 _ (by decide), s15]
  · have h' : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq ⊢; omega
    obtain ⟨h0, h1, h2, h3, h4, h9, hr, h8⟩ := (by decide : ∀ q : Fin 32,
      q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧
        q ≠ (9 : Fin 32) ∧ q ≠ ra ∧ q ≠ (8 : Fin 32)) q hq
    rw [K7 q h', r6 q hr, K5 q h0 h1 h2 h3 h4 h9, r4 q h0 h1 h2 h3 hr h8 h9]

def frpT5 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a0, .sb sp a0 0x34, .aluImm .add a0 sp 0x38, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0]
def frpT6 : List BInstr :=
  [.aluImm .and a3 (8 : Fin 32) 0xFF, .aluImm .add a1 sp 0x38, .aluImm .add a2 sp 4, .alu .add a0 x0 (18 : Fin 32)]

section
set_option maxRecDepth 20000
theorem frpT4_end : blockEnd p384FromReprCode 0xFE [.alu .add a0 x0 (9 : Fin 32)] = some 0x100 := by decide
theorem frpT5_end : blockEnd p384FromReprCode 0x108 frpT5 = some 0x116 := by decide
theorem frpT6_end : blockEnd p384FromReprCode 0x11E frpT6 = some 0x128 := by decide
theorem frpRestore_end : blockEnd p384FromReprCode 0x134 (restoreBlock frpPs) = some 0x140 := by decide
end

theorem frp_c8 {c : Word} (hc : c = 0 ∨ c = 1) : ((c.extractLsb' 0 8).zeroExtend 32) = c := by
  rcases hc with rfl | rfl <;> decide

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- From 0xFE to the return: `black_box` passes the choice `c` through,
`conditional_select` writes to `out` the limbs at `T = S + 0xF4` when `c` is
1 and the zeros that `memset` put at `S + 0x128` when it is 0, the choice
goes in the byte after them, and the epilogue restores the saved registers
and returns. -/
theorem frp_tailB {M0 : Word → BitVec 8} (E : FRPEnv M0) (n : Machine) {S out c : Word}
    (st : St n.mem FRP n 0xFE (reg n)) (hf : ∀ x, Sep S 0x1A0 x 1 → n.mem x = M0 x)
    (hSa : S.toNat % 16 = 0) (hSw : S.toNat + 0x1A0 ≤ 0x40000000) (how : out.toNat + 49 ≤ 0x40000000)
    (sOS : Sep out 49 S 0x1A0) (hsp : reg n sp = S + BitVec.ofNat 32 0xF0) (h9 : reg n (9 : Fin 32) = c)
    (hc : c = 0 ∨ c = 1) (h18 : reg n (18 : Fin 32) = out)
    (hret : memLoad32 n.mem (S + BitVec.ofNat 32 0xF0 + 0xAC) &&& ~~~1 =
      memLoad32 n.mem (S + BitVec.ofNat 32 0xF0 + 0xAC)) :
    ∃ n', Steps n n' ∧ n'.pc = memLoad32 n.mem (S + BitVec.ofNat 32 0xF0 + 0xAC) ∧
      reg n' sp = S + BitVec.ofNat 32 0x1A0 ∧
      (∀ r o, (r, o) ∈ frpPs → reg n' r = memLoad32 n.mem (S + BitVec.ofNat 32 0xF0 + o)) ∧
      (∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (∀ i, i < 12 → memLoad32 n'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 n.mem (S + BitVec.ofNat 32 0xF4 + BitVec.ofNat 32 (4 * i)) else 0) ∧
      n'.mem (out + 0x30) = c.extractLsb' 0 8 ∧
      ∀ x, Sep S 0x1A0 x 1 → Sep out 49 x 1 → n'.mem x = n.mem x := by
  have hSc : ∀ c, c ≤ 0x1A0 → (S + BitVec.ofNat 32 c).toNat = S.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x1A0 → d + k ≤ 0x1A0 →
      Sep (S + BitVec.ofNat 32 c) n (S + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets S h (by omega) (by omega)
  have inS : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x1A0 → Sep S 0x1A0 x 1 → Sep (S + BitVec.ofNat 32 c) l x 1 :=
    fun h hx => hx.sub h
  have hi : ∀ {c l : Nat} (b : Word) (k : Nat), c + l ≤ 0x1A0 → 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (S + BitVec.ofNat 32 c) l b k := fun b k h h1 h2 => sep_of_le (by rw [hSc _ (by omega)]; omega) h2
  have ohi : ∀ {c l : Nat} (b : Word) (k : Nat), c + l ≤ 49 → 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (out + BitVec.ofNat 32 c) l b k := fun b k h h1 h2 =>
    sep_of_le (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) h2
  have Shi : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep S 0x1A0 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have Ohi : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep out 49 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hFRn : FRP.toNat = (img% p384FromReprAddress) := by decide
  have cd : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep S 0x1A0 x 1 → Sep out 49 x 1 → M' x = M0 x) → CodeIn M' b code :=
    fun hc h1 h2 hM i hi => by rw [hM _ (Shi _ (code_hi h1 h2 hi)) (Ohi _ (code_hi h1 h2 hi))]; exact hc i hi
  have Gc : ∀ c, S + BitVec.ofNat 32 0xF0 + BitVec.ofNat 32 c = S + BitVec.ofNat 32 (0xF0 + c) :=
    fun c => add_ofNat_assoc _ _ _
  have hGa : (S + BitVec.ofNat 32 0xF0).toNat % 4 = 0 := aligned_add (by omega) (by decide)
  have hf' : ∀ x, Sep S 0x1A0 x 1 → Sep out 49 x 1 → n.mem x = M0 x := fun x hx _ => hf x hx
  have hc0 := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) hf'
  obtain ⟨n1, c1, u1⟩ := St.block [.alu .add a0 x0 (9 : Fin 32)] st hc0 frpT4_end (by
    simp only [BlockOk, BInstr.ok]; exact ⟨trivial, trivial⟩)
  have u1' : St n.mem FRP n1 0x100 (reg n1) := ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩
  have R1 : ∀ q, reg n1 q = (runBlock [.alu .add a0 x0 (9 : Fin 32)] (n.mem, reg n)).2 q := u1.regs
  have K1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q h0 => by
    rw [R1]; refine runBlock_reg _ _ _ q st.zero ?_
    simp only [List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0]
  -- `black_box`
  obtain ⟨m2, c2, pc2, mem2, regs2⟩ := u1'.callRa hc0 frp_at_100 frp_at_104
    (show FRP + BitVec.ofNat 32 0x100 + 0xA000 + 0xFFFFFAC2 = BitVec.ofNat 32 blackBoxU8Address by decide) (by decide)
  have r2 : ∀ q, q ≠ ra → reg m2 q = reg n1 q := PEnv.reg1 regs2 u1'.zero
  have sp2 : reg m2 sp = S + BitVec.ofNat 32 0xF0 := by rw [r2 sp (by decide), K1 sp (by decide), hsp]
  have eB : S + BitVec.ofNat 32 0xF0 + 0xFFFFFFFF = S + BitVec.ofNat 32 0xEF := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m3, c3, pc3, a03, K3, mem3⟩ := blackBoxU8_correct m2 (retAddr := FRP + BitVec.ofNat 32 (0x100 + 8))
    (by rw [mem2]; exact cd E.bb (by decide) (by decide) hf') pc2
    (by rw [regs2]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at FRP (by decide) _ (by decide)))
    (by rw [sp2, eB]; exact hi _ _ (by omega) (by decide) (by decide))
  rw [sp2, eB, mem2] at mem3
  rw [r2 a0 (by decide), R1] at a03
  simp only [runBlock, BInstr.run] at a03
  have a03' : reg m3 a0 = c := by
    rw [a03]; simp +decide only [upd_app, ↓reduceIte]; rw [h9]
    exact (congrArg (fun w => (w.extractLsb' 0 8).zeroExtend 32) (BitVec.zero_add c)).trans (frp_c8 hc)
  have M3 : ∀ x, Sep S 0x1A0 x 1 → Sep out 49 x 1 → m3.mem x = M0 x := fun x hx ho => by
    rw [mem3 x (inS (by omega) hx), hf x hx]
  have hc3 := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) M3
  have u3 : St m3.mem FRP m3 0x108 (reg m3) := ⟨by rw [pc3], rfl, fun _ => rfl⟩
  have r3 : ∀ q, q ≠ a0 → q ≠ ra → reg m3 q = reg n q := fun q h0 hr => by
    rw [K3 q h0, r2 q hr, K1 q h0]
  have sp3 : reg m3 sp = S + BitVec.ofNat 32 0xF0 := by rw [r3 sp (by decide) (by decide), hsp]
  have e34 : S + BitVec.ofNat 32 0xF0 + 0x34 = S + BitVec.ofNat 32 0x124 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n4, c4, u4⟩ := St.block frpT5 u3 hc3 frpT5_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, frpT5, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp3, e34]; exact hi _ _ (by omega) (by rw [hFRn]; decide) (by decide))
  have R4 : ∀ q, reg n4 q = (runBlock frpT5 (m3.mem, reg m3)).2 q := u4.regs
  have M4e : (runBlock frpT5 (m3.mem, reg m3)).1 = memStore8 m3.mem (S + BitVec.ofNat 32 0x124) (c.extractLsb' 0 8) := by
    simp +decide only [runBlock, BInstr.run, frpT5, upd_app, ↓reduceIte]; rw [sp3, e34, a03']
  obtain ⟨M4, hM4⟩ : ∃ M4, memStore8 m3.mem (S + BitVec.ofNat 32 0x124) (c.extractLsb' 0 8) = M4 := ⟨_, rfl⟩
  rw [hM4] at M4e
  have u4' : St M4 FRP n4 0x116 (reg n4) := ⟨u4.pc, by rw [u4.mem, M4e], fun _ => rfl⟩
  have M4o : ∀ x, Sep (S + BitVec.ofNat 32 0x124) 1 x 1 → M4 x = m3.mem x := fun x hx => by
    rw [← hM4, memStore8_ne (sep1_ne hx)]
  have hc4 : CodeIn M4 FRP p384FromReprCode := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide)
    fun x hx ho => by rw [M4o x (inS (by omega) hx), M3 x hx ho]
  have K4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (8 : Fin 32) → reg n4 q = reg m3 q := fun q h0 h1 h2 h8 => by
    rw [R4]; refine runBlock_reg _ _ _ q u3.zero ?_
    simp only [frpT5, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2, h8]
  have s04 : reg n4 (8 : Fin 32) = c := by
    rw [R4]; simp +decide only [runBlock, BInstr.run, frpT5, upd_app, ↓reduceIte]; rw [a03']; exact BitVec.zero_add _
  have sp4 : reg n4 sp = S + BitVec.ofNat 32 0xF0 := by
    rw [K4 sp (by decide) (by decide) (by decide) (by decide), sp3]
  obtain ⟨n5, c5, u5, _, K5⟩ := u4'.memsetW (B := BitVec.ofNat 32 memsetAddress) (w := 12)
    (dst := S + BitVec.ofNat 32 0x128) (by decide) hc4
    (cd (M' := M4) E.ms (by decide) (by decide) fun x hx ho => by rw [M4o x (inS (by omega) hx), M3 x hx ho])
    frp_at_116 frp_at_11a (by decide) (by decide) (by decide) (by rw [hSc _ (by omega)]; omega) (by decide)
    (aligned_add (by omega) (by decide)) (hi _ _ (by omega) (by decide) (by decide))
    (by rw [R4]; simp +decide only [runBlock, BInstr.run, frpT5, upd_app, ↓reduceIte]; rw [sp3]; exact Gc 0x38)
    (by rw [R4]; simp +decide only [runBlock, BInstr.run, frpT5, upd_app, ↓reduceIte])
    (by rw [R4]; simp +decide only [runBlock, BInstr.run, frpT5, upd_app, ↓reduceIte])
  obtain ⟨M5, hM5⟩ : ∃ M5, fillWords M4 (S + BitVec.ofNat 32 0x128) 0 12 = M5 := ⟨_, rfl⟩
  rw [hM5] at u5
  have M5o : ∀ x, Sep (S + BitVec.ofNat 32 0x128) 48 x 1 → M5 x = M4 x := fun x hx => by
    rw [← hM5]; exact fillWords_outside 12 hx
  have M5' : ∀ x, Sep S 0x1A0 x 1 → Sep out 49 x 1 → M5 x = M0 x := fun x hx ho => by
    rw [M5o x (inS (by omega) hx), M4o x (inS (by omega) hx), M3 x hx ho]
  have hc5 := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) M5'
  have r5 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ a0 → q ≠ a1 → q ≠ (8 : Fin 32) →
      reg n5 q = reg n q := fun q h2 h3 h4 h5 h6 hr h0 h1 h8 => by
    rw [K5 q h2 h3 h4 h5 h6 hr, K4 q h0 h1 h2 h8, r3 q h0 hr]
  have sp5 : reg n5 sp = S + BitVec.ofNat 32 0xF0 := by
    rw [r5 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hsp]
  obtain ⟨n6, c6, u6⟩ := St.block frpT6 u5 hc5 frpT6_end (by
    simp only [BlockOk, BInstr.ok, frpT6]; exact ⟨trivial, trivial, trivial, trivial, trivial⟩)
  have R6 : ∀ q, reg n6 q = (runBlock frpT6 (M5, reg n5)).2 q := u6.regs
  have u6' : St M5 FRP n6 0x128 (reg n6) := ⟨u6.pc, by rw [u6.mem]; rfl, fun _ => rfl⟩
  have K6 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg n6 q = reg n5 q := fun q h0 h1 h2 h3 => by
    rw [R6]; refine runBlock_reg _ _ _ q u5.zero ?_
    simp only [frpT6, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0, h1, h2, h3]
  have rv6 : reg n6 a0 = out ∧ reg n6 a1 = S + BitVec.ofNat 32 0x128 ∧ reg n6 a2 = S + BitVec.ofNat 32 0xF4 ∧
      reg n6 a3 = c := by
    simp only [R6]; simp +decide only [runBlock, BInstr.run, frpT6, upd_app, ↓reduceIte]
    rw [sp5, r5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h18, K5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s04]
    refine ⟨BitVec.zero_add _, Gc 0x38, Gc 4, ?_⟩
    rcases hc with rfl | rfl <;> decide
  obtain ⟨ha6, hb6, hc6, hd6⟩ := rv6
  -- `conditional_select`
  obtain ⟨m7, c7, pc7, mem7, regs7⟩ := u6'.callRa hc5 frp_at_128 frp_at_12c
    (show FRP + BitVec.ofNat 32 0x128 + 0x10000 + 0xFFFFFB8A = BitVec.ofNat 32 condSelect384Address by decide)
    (by decide)
  have r7 : ∀ q, q ≠ ra → reg m7 q = reg n6 q := PEnv.reg1 regs7 u6'.zero
  have M7 : ∀ x, Sep S 0x1A0 x 1 → Sep out 49 x 1 → m7.mem x = M0 x := fun x hx ho => by rw [mem7]; exact M5' x hx ho
  have eC : S + BitVec.ofNat 32 0xF0 + 0xFFFFFFA0 = S + BitVec.ofNat 32 0x90 := by rw [BitVec.add_assoc]; rfl
  have oS : ∀ {c l : Nat} {d k : Nat}, c + l ≤ 49 → d + k ≤ 0x1A0 → Sep (out + BitVec.ofNat 32 c) l
      (S + BitVec.ofNat 32 d) k := fun h1 h2 => (sOS.sub (c := _) (l := _) h1).subR h2
  have oS0 : ∀ {d k : Nat}, d + k ≤ 0x1A0 → Sep out 48 (S + BitVec.ofNat 32 d) k := fun h => by
    have := oS (c := 0) (l := 48) (by omega) h; rwa [add_ofNat_zero] at this
  have ohi0 : ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 → Sep out 48 b k := fun b k h1 h2 => by
    have := ohi (c := 0) (l := 48) b k (by omega) h1 h2; rwa [add_ofNat_zero] at this
  have EC : CSEnv m7.mem (BitVec.ofNat 32 condSelect384Address) (S + BitVec.ofNat 32 0xF0) out
      (S + BitVec.ofNat 32 0x128) (S + BitVec.ofNat 32 0xF4) := by
    refine ⟨by decide, cd E.csel (by decide) (by decide) M7,
      by rw [show BitVec.ofNat 32 condSelect384Address + 0x101A = BitVec.ofNat 32 memcpyStubAddress by decide]
         exact cd E.cs (by decide) (by decide) M7,
      by rw [show BitVec.ofNat 32 condSelect384Address + 0x101A + 8 = BitVec.ofNat 32 memcpyStubAddress + 8 by decide]
         exact cd E.cb (by decide) (by decide) M7,
      by rw [show BitVec.ofNat 32 condSelect384Address + 0x2EC = BitVec.ofNat 32 uint12CtAssignAddress by decide]
         exact cd E.cta (by decide) (by decide) M7,
      by rw [show BitVec.ofNat 32 condSelect384Address + 0x2EC + 0xFFFF9B66 = BitVec.ofNat 32 sliceCtAssignAddress
           by decide]
         exact cd E.sca (by decide) (by decide) M7,
      hGa, by rw [hSc _ (by omega)]; omega, aligned_add (by omega) (by decide), by rw [hSc _ (by omega)]; omega,
      by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try rw [eC])
    all_goals first
      | exact hi _ _ (by omega) (by decide) (by decide)
      | exact ohi0 _ _ (by decide) (by decide)
      | exact oS0 (by omega)
      | exact offs (by omega) (by omega) (by omega)
  obtain ⟨m8, c8, pc8, sp8, w8, K8, fr8⟩ := condSelect384_correct m7 (retAddr := FRP + BitVec.ofNat 32 (0x128 + 8))
    EC pc7 (by rw [r7 sp (by decide), K6 sp (by decide) (by decide) (by decide) (by decide), sp5])
    (by rw [r7 a0 (by decide), ha6]) (by rw [r7 a1 (by decide), hb6]) (by rw [r7 a2 (by decide), hc6])
    (by rw [r7 a3 (by decide), hd6]) hc (by rw [regs7]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at FRP (by decide) _ (by decide)))
  rw [eC, mem7] at fr8
  rw [mem7] at w8
  have hc8 : CodeIn m8.mem FRP p384FromReprCode := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide)
    fun x hx ho => by rw [fr8 x (inS (by omega) hx) (ho.sub (c := 0) (l := 48) (by omega) |> fun h => by
      rwa [add_ofNat_zero] at h), M5' x hx ho]
  have u8 : St m8.mem FRP m8 0x130 (reg m8) := ⟨by rw [pc8], rfl, fun _ => rfl⟩
  have r8 : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m8 q = reg n6 q := fun q hq => by
    rw [K8 q (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq ⊢; omega), r7 q (by
      intro h; subst h; simp at hq)]
  obtain ⟨m9, d9, u9⟩ := u8.sb hc8 frp_at_130 (off' := 0x134) (by decide)
  have e9 : reg m8 (18 : Fin 32) + 0x30 = out + BitVec.ofNat 32 0x30 := by
    rw [r8 _ (by decide), K6 _ (by decide) (by decide) (by decide) (by decide),
      r5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h18]; rfl
  have c9 : (reg m8 (8 : Fin 32)).extractLsb' 0 8 = c.extractLsb' 0 8 := by
    rw [r8 _ (by decide), K6 _ (by decide) (by decide) (by decide) (by decide),
      K5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s04]
  rw [e9, c9] at u9
  obtain ⟨M9, hM9⟩ : ∃ M9, memStore8 m8.mem (out + BitVec.ofNat 32 0x30) (c.extractLsb' 0 8) = M9 := ⟨_, rfl⟩
  rw [hM9] at u9
  have o30 : ∀ x, Sep (out + BitVec.ofNat 32 0x30) 1 x 1 → M9 x = m8.mem x := fun x hx => by
    rw [← hM9, memStore8_ne (sep1_ne hx)]
  -- what the writes since 0xFE leave alone
  have ag9 : ∀ x, Sep (S + BitVec.ofNat 32 0x90) 0xC8 x 1 → Sep out 49 x 1 → M9 x = n.mem x := fun x hx ho => by
    rw [o30 x (ho.sub (c := 0x30) (l := 1) (by omega)),
      fr8 x (hx.sub (c := 0) (l := 0x60) (by omega) |> fun h => by rwa [add_ofNat_zero] at h)
        (ho.sub (c := 0) (l := 48) (by omega) |> fun h => by rwa [add_ofNat_zero] at h),
      M5o x (by have := hx.sub (c := 0x98) (l := 48) (by omega); rwa [add_ofNat_assoc] at this),
      M4o x (by have := hx.sub (c := 0x94) (l := 1) (by omega); rwa [add_ofNat_assoc] at this),
      mem3 x (by have := hx.sub (c := 0x5F) (l := 1) (by omega); rwa [add_ofNat_assoc] at this)]
  have hc9 : CodeIn M9 FRP p384FromReprCode := cd E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide)
    fun x hx ho => by rw [ag9 x (inS (by omega) hx) ho, hf x hx]
  have slot : ∀ o : Word, 0x98 ≤ o.toNat → o.toNat + 4 ≤ 0xB0 → memLoad32 M9 (S + BitVec.ofNat 32 0xF0 + o) =
      memLoad32 n.mem (S + BitVec.ofNat 32 0xF0 + o) := fun o hb1 hb2 => by
    have e : S + BitVec.ofNat 32 0xF0 + o = S + BitVec.ofNat 32 (0xF0 + o.toNat) := by rw [← Gc, ofNat_toNat_self]
    rw [e]
    apply memLoad32_congr; intro j hj
    rw [add_ofNat_assoc]
    exact ag9 _ (offs (by omega) (by omega) (by omega))
      (oS (c := 0) (l := 49) (d := 0xF0 + o.toNat + j) (k := 1) (by omega) (by omega) |>
        fun h => by rw [add_ofNat_zero] at h; exact h)
  have sp9 : reg m8 sp = S + BitVec.ofNat 32 0xF0 := sp8
  have hpsp : ∀ p ∈ frpPs, p.1 ≠ sp := by decide
  obtain ⟨n10, c10, u10⟩ := St.block (restoreBlock frpPs) u9 hc9 frpRestore_end
    (restoreBlock_ok M9 (S + BitVec.ofNat 32 0xF0) frpPs (reg m8) sp9 hpsp fun q hq => by
      simp only [frpPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hGa (by decide))
  simp only [restoreBlock_run M9 (S + BitVec.ofNat 32 0xF0) frpPs (reg m8) sp9 hpsp] at u10
  have rsp : restoreRegs M9 (S + BitVec.ofNat 32 0xF0) (reg m8) frpPs sp = S + BitVec.ofNat 32 0xF0 := by
    rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp9
  obtain ⟨n11, d11, u11⟩ := u10.aluImm hc9 frp_at_140 (off' := 0x142) (by decide)
  obtain ⟨n12, d12, pc12, mem12, regs12⟩ := u11.jalr hc9 frp_at_142
  have rra : restoreRegs M9 (S + BitVec.ofNat 32 0xF0) (reg m8) frpPs ra =
      memLoad32 n.mem (S + BitVec.ofNat 32 0xF0 + 0xAC) := by
    simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
    exact slot _ (by decide) (by decide)
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs M9 (S + BitVec.ofNat 32 0xF0) f ps q = f q := by
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
    simp only [frpPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
      exact slot _ (by decide) (by decide)
  · obtain ⟨h0, hsp', hps, h0', h1, h2, h3, h4, h5, h6, hr, h8⟩ := (by decide : ∀ q : Fin 32,
      q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ frpPs, p.1 ≠ q) ∧ q ≠ a0 ∧ q ≠ a1 ∧
        q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ ra ∧ q ≠ (8 : Fin 32)) q hq
    rw [regs12, upd_ne h0 hsp', rr _ _ q h0 hps,
      r8 q (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq ⊢; omega), K6 q h0' h1 h2 h3,
      r5 q h2 h3 h4 h5 h6 hr h0' h1 h8]
  · rw [mem12, ← hM9, memLoad32_congr (M := m8.mem) fun j hj => memStore8_ne (sep1_ne (by
        rw [add_ofNat_assoc]
        exact sep_offsets out (c := 0x30) (n := 1) (d := 4 * i + j) (k := 1) (by omega) (by omega) (by omega))),
      w8 i hi]
    by_cases h1 : c = 1
    · rw [ite_eq_left h1, ite_eq_left h1]
      apply memLoad32_congr; intro j hj; rw [add_ofNat_assoc, add_ofNat_assoc]
      have hT : Sep (S + BitVec.ofNat 32 0x128) 48 (S + BitVec.ofNat 32 (0xF4 + (4 * i + j))) 1 :=
        offs (by omega) (by omega) (by omega)
      rw [M5o _ hT, M4o _ (offs (by omega) (by omega) (by omega)), mem3 _ (offs (by omega) (by omega) (by omega))]
    · rw [ite_eq_right h1, ite_eq_right h1, ← hM5]
      exact fillWords_load 12 i hi (by rw [hSc _ (by omega)]; omega)
  · rw [mem12, ← hM9]; exact memStore8_same _ _ _
  · rw [mem12, ag9 x (inS (by omega) hx) ho]

theorem frp_word_bytes (y : Word) : y.toNat = (y.extractLsb' 0 8).toNat + (y.extractLsb' 8 8).toNat * 256 +
    (y.extractLsb' 16 8).toNat * 65536 + (y.extractLsb' 24 8).toNat * 16777216 := by
  rw [byte_toNat, byte_toNat, byte_toNat, byte_toNat]
  have := y.isLt
  simp only [Nat.pow_zero, Nat.div_one]
  omega

set_option maxRecDepth 20000 in
theorem frp_bswap_toNat (M : Word → BitVec 8) (a : Word) :
    (bswap32 (memLoad32 M a)).toNat = beNat (memBytes M a 4) := by
  have e : beNat (memBytes M a 4) = (((0 * 256 + (M (a + BitVec.ofNat 32 0)).toNat) * 256 +
      (M (a + 1)).toNat) * 256 + (M (a + 2)).toNat) * 256 + (M (a + 3)).toNat := rfl
  rw [e, add_ofNat_zero, frp_word_bytes, bswap32_byte _ 0 (by decide), bswap32_byte _ 1 (by decide),
    bswap32_byte _ 2 (by decide), bswap32_byte _ 3 (by decide)]
  simp only [byte_toNat, memLoad32_toNat]
  have h0 : (M a).toNat < 256 := (M a).isLt
  have h1 : (M (a + 1)).toNat < 256 := (M (a + 1)).isLt
  have h2 : (M (a + 2)).toNat < 256 := (M (a + 2)).isLt
  have h3 : (M (a + 3)).toNat < 256 := (M (a + 3)).isLt
  simp only [le32, Nat.reduceSub, Nat.reduceMul, Nat.reducePow]
  clear e
  generalize (M a).toNat = x0 at h0 ⊢
  generalize (M (a + 1)).toNat = x1 at h1 ⊢
  generalize (M (a + 2)).toNat = x2 at h2 ⊢
  generalize (M (a + 3)).toNat = x3 at h3 ⊢
  have d1 : (x0 + 256 * (x1 + 256 * (x2 + 256 * x3))) / 256 = x1 + 256 * (x2 + 256 * x3) := by omega
  have d2 : (x0 + 256 * (x1 + 256 * (x2 + 256 * x3))) / 65536 = x2 + 256 * x3 := by omega
  have d3 : (x0 + 256 * (x1 + 256 * (x2 + 256 * x3))) / 16777216 = x3 := by omega
  rw [d1, d2, d3, Nat.div_one, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]
  clear d1 d2 d3
  omega

theorem beNat_append (l1 l2 : Bytes) : beNat (l1 ++ l2) = beNat l1 * 256 ^ l2.length + beNat l2 := by
  unfold beNat
  rw [List.foldl_append]
  generalize List.foldl (fun acc x => acc * 256 + x) 0 l1 = a
  induction l2 generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (0 * 256 + b), Nat.pow_succ]
    generalize 256 ^ l.length = P
    rw [Nat.add_mul, Nat.mul_assoc a 256 P, Nat.mul_comm 256 P, Nat.zero_mul, Nat.zero_add]
    omega

theorem accV_low (M : Word → BitVec 8) (X : Word) (n : Nat) :
    accV M X (1 + n) = (memLoad32 M X).toNat + 2 ^ 32 * accV M (X + BitVec.ofNat 32 4) n := by
  rw [accV_split M X 1 n]
  simp [accV]

/-- Limbs stored from the most significant down, each the big-endian word of
four input bytes, add up to the bytes' big-endian value. -/
theorem frp_be (M L : Word → BitVec 8) (inp : Word) :
    ∀ n (X : Word), (∀ q, q < n → memLoad32 L (X + BitVec.ofNat 32 (4 * (n - 1 - q))) =
      bswap32 (memLoad32 M (inp + BitVec.ofNat 32 (4 * q)))) → accV L X n = beNat (memBytes M inp (4 * n))
  | 0, _, _ => rfl
  | n + 1, X, h => by
    rw [Nat.add_comm n 1, accV_low, frp_be M L inp n (X + BitVec.ofNat 32 4) fun q hq => by
        rw [add_ofNat_assoc, show 4 + 4 * (n - 1 - q) = 4 * (n + 1 - 1 - q) by omega]; exact h q (by omega),
      show 4 * (1 + n) = 4 * n + 4 by omega, memBytes_split, beNat_append, memBytes_length]
    have h0 := h n (by omega)
    rw [show 4 * (n + 1 - 1 - n) = 0 by omega, add_ofNat_zero] at h0
    rw [h0, frp_bswap_toNat]
    omega

def frpCmp0 : List BInstr :=
  [.aluImm .add (19 : Fin 32) x0 0, .aluImm .add (20 : Fin 32) sp 0x68, .lui (9 : Fin 32) 0x3FCC5000,
   .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFCF4, .aluImm .add (8 : Fin 32) x0 0xC]

section
set_option maxRecDepth 20000
theorem frpCmp0_end : blockEnd p384FromReprCode 0x86 frpCmp0 = some 0x96 := by decide
end

set_option exponentiation.threshold 400 in
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- **The compiled `<p384 FieldElement as PrimeField>::from_repr`.** For the
48 bytes at `inp`, read as a big-endian number `x`, and the field modulus `p`
that the image keeps at `p384Np`: when `x < p` it writes to `out` the limbs
of the number `r < p` with `r · 2^384 ≡ x · R2 (mod p)`, where `R2` is the
number the image keeps 0x60 bytes past the modulus, and 1 to the byte after
them; otherwise it writes zero limbs and a 0 byte. It returns with `sp` and
the callee-saved registers restored and writes only `out` and the 0x1A0
bytes of stack below `sp`. -/
theorem p384FromRepr_correct (m : Machine) {sp0 out inp retAddr : Word} (E : FRPEnv m.mem)
    (hpc : m.pc = FRP) (ha0 : reg m a0 = out) (ha1 : reg m a1 = inp) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) (hsp16 : sp0.toNat % 16 = 0)
    (hspl : 0x1A0 ≤ sp0.toNat) (hspw : sp0.toNat ≤ 0x40000000) (how : out.toNat + 49 ≤ 0x40000000)
    (sOS : Sep out 49 (sp0 + 0xFFFFFE60) 0x1A0) (sIS : Sep inp 48 (sp0 + 0xFFFFFE60) 0x1A0)
    (sSN : Sep (sp0 + 0xFFFFFE60) 0x1A0 p384Np 0x90) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (beNat (memBytes m.mem inp 48) < accV m.mem p384Np 12 →
        m'.mem (out + 0x30) = 1 ∧ accV m'.mem out 12 < accV m.mem p384Np 12 ∧
        accV m'.mem out 12 * 2 ^ 384 % accV m.mem p384Np 12 =
          beNat (memBytes m.mem inp 48) * accV m.mem (p384Np + 0x60) 12 % accV m.mem p384Np 12) ∧
      (accV m.mem p384Np 12 ≤ beNat (memBytes m.mem inp 48) → m'.mem (out + 0x30) = 0 ∧ accV m'.mem out 12 = 0) ∧
      ∀ x, Sep (sp0 + 0xFFFFFE60) 0x1A0 x 1 → Sep out 49 x 1 → m'.mem x = m.mem x := by
  obtain ⟨n1, M1, Ms, c1, u1, M1o, V1, slots, sp1, a01, s01, a61, a31, h171, h191, s21, k1⟩ :=
    frp_pro m E.fr E.za E.cs E.cb E.ms hpc ha0 ha1 hsp hsp16 hspl hspw
  obtain ⟨hSn, hGS⟩ := frp_S sp0 hspl
  obtain ⟨S, hS⟩ : ∃ S, sp0 + 0xFFFFFE60 = S := ⟨_, rfl⟩
  rw [hS] at hSn hGS M1o V1 sOS sIS sSN h191 ⊢
  rw [hGS] at slots sp1
  have hSa : S.toNat % 16 = 0 := by omega
  have hSw : S.toNat + 0x1A0 ≤ 0x40000000 := by omega
  have hSc : ∀ c, c ≤ 0x1A0 → (S + BitVec.ofNat 32 c).toNat = S.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x1A0 → d + k ≤ 0x1A0 →
      Sep (S + BitVec.ofNat 32 c) n (S + BitVec.ofNat 32 d) k := fun h h1 h2 => sep_offsets S h (by omega) (by omega)
  have inS : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x1A0 → Sep S 0x1A0 x 1 → Sep (S + BitVec.ofNat 32 c) l x 1 :=
    fun h hx => hx.sub h
  have hi : ∀ {c l : Nat} (b : Word) (k : Nat), c + l ≤ 0x1A0 → 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (S + BitVec.ofNat 32 c) l b k := fun b k h h1 h2 => sep_of_le (by rw [hSc _ (by omega)]; omega) h2
  have Shi : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep S 0x1A0 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hFRn : FRP.toNat = (img% p384FromReprAddress) := by decide
  have Gc : ∀ c, S + BitVec.ofNat 32 0xF0 + BitVec.ofNat 32 c = S + BitVec.ofNat 32 (0xF0 + c) :=
    fun c => add_ofNat_assoc _ _ _
  have cdx : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → (∀ x, 0x40000000 ≤ x.toNat → M' x = m.mem x) → CodeIn M' b code :=
    fun hc h1 h2 hM i hi => by rw [hM _ (code_hi h1 h2 hi)]; exact hc i hi
  have iS : ∀ {c : Nat}, c + 1 ≤ 48 → Sep S 0x1A0 (inp + BitVec.ofNat 32 c) 1 := fun h => (sIS.sub h).symm
  -- the byte loop
  obtain ⟨n2, M2, c2, u2, M2o, hl2, k2⟩ := frp_outer (Mb := M1) (inp := inp) (T := S + BitVec.ofNat 32 0xF4)
    (X := S + BitVec.ofNat 32 0x158) (G := S + BitVec.ofNat 32 0xF0)
    (fun Mx hMx => cdx E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) fun x hx => by
      rw [hMx x (hi (c := 0xF4) (l := 4) x 1 (by omega) hx (by have := x.isLt; omega))
        (hi (c := 0x158) (l := 48) x 1 (by omega) hx (by have := x.isLt; omega)), M1o x (Shi x hx)])
    (Gc 4) (sIS.subR (by omega)) (sIS.subR (by omega)) (offs (by omega) (by omega) (by omega))
    (by rw [hSc _ (by omega)]; omega) (by rw [hSc _ (by omega)]; omega) (aligned_add (by omega) (by decide))
    (aligned_add (by omega) (by decide)) 12 0 n1 M1 (by omega) (by omega) u1 (fun _ _ _ => rfl)
    (fun _ h => absurd h (Nat.not_lt_zero _)) a01 s01 sp1 a61 a31 h171 h191
  have M2m : ∀ x, Sep S 0x1A0 x 1 → M2 x = m.mem x := fun x hx => by
    rw [M2o x (inS (by omega) hx) (inS (by omega) hx), M1o x hx]
  have M2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M2 x = m.mem x := fun x hx => M2m x (Shi x hx)
  have hc2 : CodeIn M2 FRP p384FromReprCode := cdx E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) M2hi
  -- set up the comparison
  obtain ⟨n3, c3, u3⟩ := St.block frpCmp0 u2 hc2 frpCmp0_end (by
    simp only [BlockOk, BInstr.ok, frpCmp0]; exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩)
  have R3 : ∀ q, reg n3 q = (runBlock frpCmp0 (M2, reg n2)).2 q := u3.regs
  have u3' : St M2 FRP n3 0x96 (reg n3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  have r2 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a4 → q ≠ a5 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) →
      reg n2 q = reg n1 q := k2
  have sp2 : reg n2 sp = S + BitVec.ofNat 32 0xF0 := by
    rw [r2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp1]
  have K3 : ∀ q, q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) → reg n3 q = reg n2 q :=
    fun q h8 h9 h19 h20 => by
      rw [R3]; refine runBlock_reg _ _ _ q u2.zero ?_
      simp only [frpCmp0, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h8, h9, h19, h20]
  have s03 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 12 := by
    rw [R3]; simp +decide only [runBlock, BInstr.run, frpCmp0, upd_app, ↓reduceIte]
  obtain ⟨n3', d3, u3''⟩ := u3'.notTaken hc2 0x98 frp_at_96 (by decide) (by
    simp only [branchTaken]; rw [s03, u3'.zero]; decide)
  have eF4 : S + BitVec.ofNat 32 0xF0 + 0xFFFFFFFC = S + BitVec.ofNat 32 0xEC := by rw [BitVec.add_assoc]; rfl
  have sNS : Sep p384Np 48 S 0x1A0 := sSN.symm.sub (c := 0) (l := 48) (by omega) |> fun h => by
    rwa [add_ofNat_zero] at h
  obtain ⟨n4, M4, b', c4, u4, M4o, hb4, hbm4, ⟨D, hD, hinv⟩, k4⟩ := frp_cmp (Mb := M2) (X := S + BitVec.ofNat 32 0x158)
    (N := p384Np) (G := S + BitVec.ofNat 32 0xF0)
    (fun Mx hMx => cdx E.fr (by rw [hFRn]; decide) (by rw [hFRn]; decide) fun x hx => by
      rw [hMx x (by rw [eF4]; exact hi (c := 0xEC) (l := 4) x 1 (by omega) hx (by have := x.isLt; omega)), M2hi x hx])
    (fun Mx hMx => cdx E.bs (by decide) (by decide) fun x hx => by
      rw [hMx x (by rw [eF4]; exact hi (c := 0xEC) (l := 4) x 1 (by omega) hx (by have := x.isLt; omega)), M2hi x hx])
    (aligned_add (by omega) (by decide)) (by rw [hSc _ (by omega)]; omega) (by rw [hSc _ (by omega)]; omega)
    (aligned_add (by omega) (by decide)) (by decide) (by rw [eF4]; exact offs (by omega) (by omega) (by omega))
    (by rw [eF4]; exact sNS.subR (by omega))
    12 0 n3' M2 0 (by omega) (by omega) u3''.self (fun _ _ => rfl)
    (by rw [u3''.regs, R3]; simp +decide only [runBlock, BInstr.run, frpCmp0, upd_app, ↓reduceIte]; rw [u2.zero]; rfl)
    (.inl rfl)
    ⟨0, Nat.one_pos, by show 0 + 0 = 0 + 1 * maskBit 0; rfl⟩
    (by rw [u3''.regs, R3]; simp +decide only [runBlock, BInstr.run, frpCmp0, upd_app, ↓reduceIte]; rw [sp2]
        exact (Gc 0x68).trans (by rw [add_ofNat_zero]))
    (by rw [u3''.regs, R3]; simp +decide only [runBlock, BInstr.run, frpCmp0, upd_app, ↓reduceIte])
    (by rw [u3''.regs, s03])
    (by rw [u3''.regs, K3 sp (by decide) (by decide) (by decide) (by decide), sp2])
  have e4 : n4.mem = M4 := u4.mem
  subst e4
  rw [eF4] at M4o
  have u4' : St n4.mem FRP n4 0xB2 (reg n4) := u4
  have M4m : ∀ x, Sep S 0x1A0 x 1 → n4.mem x = m.mem x := fun x hx => by
    rw [M4o x (inS (by omega) hx), M2m x hx]
  have r4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) →
      q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ a5 → reg n4 q = reg n1 q :=
    fun q h0 h1 h2 h3 h4 hr h8 h9 h19 h20 h5 => by
      rw [k4 q h0 h1 h2 h3 h4 hr h8 h9 h19 h20, u3''.regs, K3 q h8 h9 h19 h20, r2 q h0 h1 h2 h4 h5 h8 h9]
  have sp4 : reg n4 sp = S + BitVec.ofNat 32 0xF0 := by
    rw [r4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), sp1]
  -- `is_nonzero`, `is_nonzero`, and the Montgomery multiplication
  obtain ⟨n5, c5, u5, fr5, lt5, eq5, sp5, s15, k5⟩ := frp_tailA E n4 u4' M4m hSa hSw sSN sp4 hb4
  have M5m : ∀ x, Sep S 0x1A0 x 1 → n5.mem x = m.mem x := fun x hx => by
    rw [fr5 x (by have := hx.sub (c := 0) (l := 0xF0) (by omega); rwa [add_ofNat_zero] at this) (inS (by omega) hx),
      M4m x hx]
  -- the slots the epilogue reads
  have SL : ∀ o : Word, 0x98 ≤ o.toNat → o.toNat + 4 ≤ 0xB0 →
      memLoad32 n5.mem (S + BitVec.ofNat 32 0xF0 + o) = memLoad32 Ms (S + BitVec.ofNat 32 0xF0 + o) := fun o h1 h2 => by
    have e : S + BitVec.ofNat 32 0xF0 + o = S + BitVec.ofNat 32 (0xF0 + o.toNat) := by rw [← Gc, ofNat_toNat_self]
    rw [e]
    apply memLoad32_congr; intro j hj
    rw [add_ofNat_assoc]
    have hy : Sep S 0xF0 (S + BitVec.ofNat 32 (0xF0 + o.toNat + j)) 1 := by
      have := offs (c := 0) (n := 0xF0) (d := 0xF0 + o.toNat + j) (k := 1) (by omega) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    rw [fr5 _ hy (offs (by omega) (by omega) (by omega)), M4o _ (offs (by omega) (by omega) (by omega)),
      M2o _ (offs (by omega) (by omega) (by omega)) (offs (by omega) (by omega) (by omega)),
      show 0xF0 + o.toNat + j = 0x188 + (o.toNat - 0x98 + j) by omega, V1 _ (by omega)]
  have hra5 : memLoad32 n5.mem (S + BitVec.ofNat 32 0xF0 + 0xAC) = retAddr := by
    rw [SL _ (by decide) (by decide), slots ra _ (by decide), hra]
  have hc' : b' &&& 1 = 0 ∨ b' &&& 1 = 1 := by rcases hbm4 with rfl | rfl <;> decide
  have h185 : reg n5 (18 : Fin 32) = out := by
    rw [k5 _ (by decide), r4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), s21]
  obtain ⟨n6, c6, pc6, sp6, rr6, k6, w6, b6, fr6⟩ := frp_tailB E n5 u5 M5m hSa hSw how sOS sp5 s15 hc' h185
    (by rw [hra5]; exact hret)
  -- the input's value and the comparison's borrow
  have hX2 : accV M2 (S + BitVec.ofNat 32 0x158) 12 = beNat (memBytes m.mem inp 48) :=
    frp_be m.mem M2 inp 12 _ fun q hq => by
      rw [show 12 - 1 - q = 11 - q by omega, hl2 q hq, memLoad32_congr (M := m.mem) (M' := M1)
        (b := inp + BitVec.ofNat 32 (4 * q)) fun j hj => by rw [add_ofNat_assoc]; exact M1o _ (iS (by omega))]
  have hX4 : accV n4.mem (S + BitVec.ofNat 32 0x158) 12 = beNat (memBytes m.mem inp 48) := by
    rw [← hX2]; apply accV_congr; intro i hi; apply memLoad32_congr; intro j hj
    rw [add_ofNat_assoc, add_ofNat_assoc]; exact M4o _ (offs (by omega) (by omega) (by omega))
  have hN2 : accV M2 p384Np 12 = accV m.mem p384Np 12 := by
    apply accV_congr; intro i hi; apply memLoad32_congr; intro j hj
    rw [add_ofNat_assoc]; exact M2m _ (sSN.subR (c := 4 * i + j) (l := 1) (by omega))
  rw [hN2, hX2] at hinv
  have hmb := frp_borrow hD (mb_le1 b') hinv
  rw [hX4] at eq5
  have eOut : ∀ v : Word, b' &&& 1 = v → (v = 1 → accV n6.mem out 12 = accV n5.mem (S + BitVec.ofNat 32 0xF4) 12) ∧
      (v = 0 → accV n6.mem out 12 = 0) := fun v hv => by
    refine ⟨fun h1 => accV_congr2 12 fun i hi => by rw [w6 i hi, ite_eq_left (by rw [hv, h1])], fun h0 =>
      accV_zero 12 fun i hi => by rw [w6 i hi, ite_eq_right (by rw [hv, h0]; decide)]⟩
  refine ⟨n6, c1.trans (c2.trans (c3.trans (.cons d3 (c4.trans (c5.trans c6))))), by rw [pc6, hra5], ?_,
    fun q hq => ?_, fun hlt => ?_, fun hge => ?_, fun x hx ho => ?_⟩
  · rw [sp6, ← hS, BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 0x1A0 = 0 by decide]
    exact BitVec.add_zero _
  · have hs : ∀ (r : Fin 32) (o : Word), (r, o) ∈ frpPs → reg n6 r = reg m r := fun r o hm => by
      have hb : 0x98 ≤ o.toNat ∧ o.toNat + 4 ≤ 0xB0 := by
        simp only [frpPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      rw [rr6 r o hm, SL o hb.1 hb.2, slots r o hm]
    have key : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨
        (q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧
          q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ ra ∧ q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧
          q ≠ (19 : Fin 32) ∧ q ≠ (20 : Fin 32) ∧ q ≠ a5) := by decide
    rcases key q hq with rfl | rfl | rfl | rfl | rfl | ⟨h1, h2, h0, h1', h2', h3, h4, hr, h8, h9, h19, h20, h5⟩
    · exact hs _ 0xA8 (by decide)
    · exact hs _ 0xA4 (by decide)
    · exact hs _ 0xA0 (by decide)
    · exact hs _ 0x9C (by decide)
    · exact hs _ 0x98 (by decide)
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
