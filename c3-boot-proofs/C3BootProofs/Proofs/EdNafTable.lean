import C3BootProofs.Proofs.Ed25519PkOk
import C3BootProofs.Proofs.AsProjNiels
import C3BootProofs.Proofs.EdNiels
import C3BootProofs.Proofs.EdCall

/-!
# `NafLookupTable5::<ProjectiveNielsPoint>::from`, as compiled

`from` builds the table `[A, 3A, 5A, …, 15A]` in projective Niels form: the
first entry is `A.as_projective_niels()`, and each next one adds `2A` to
the last through `EdwardsPoint + ProjectiveNielsPoint`, `as_extended`, and
`as_projective_niels`. The specification is the Rust source's loop over the
field operations on limb lists.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem nt_at_0 : fetchRel nafTableFromCode 0x0 = some (.aluImm .add sp sp 0xFFFFF860, 4) := by decide
theorem nt_at_4 : fetchRel nafTableFromCode 0x4 = some (.aluImm .add a2 sp 0x780, 4) := by decide
theorem nt_at_8 : fetchRel nafTableFromCode 0x8 = some (.store .sw a2 ra 0x1C, 4) := by decide
theorem nt_at_c : fetchRel nafTableFromCode 0xC = some (.store .sw a2 (8 : Fin 32) 0x18, 2) := by decide
theorem nt_at_e : fetchRel nafTableFromCode 0xE = some (.store .sw a2 (9 : Fin 32) 0x14, 2) := by decide
theorem nt_at_10 : fetchRel nafTableFromCode 0x10 = some (.store .sw a2 (18 : Fin 32) 0x10, 4) := by decide
theorem nt_at_14 : fetchRel nafTableFromCode 0x14 = some (.store .sw a2 (19 : Fin 32) 0xC, 4) := by decide
theorem nt_at_18 : fetchRel nafTableFromCode 0x18 = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem nt_at_1a : fetchRel nafTableFromCode 0x1A = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem nt_at_1c : fetchRel nafTableFromCode 0x1C = some (.aluImm .add a0 sp 0x6EC, 4) := by decide
theorem nt_at_20 : fetchRel nafTableFromCode 0x20 = some (.auipc ra 0x0, 4) := by decide
theorem nt_at_24 : fetchRel nafTableFromCode 0x24 = some (.jalr ra ra 0xFFFFFE42, 4) := by decide
theorem nt_at_28 : fetchRel nafTableFromCode 0x28 = some (.aluImm .add (8 : Fin 32) sp 0x1EC, 2) := by decide
theorem nt_at_2a : fetchRel nafTableFromCode 0x2A = some (.aluImm .add (9 : Fin 32) x0 0x8, 2) := by decide
theorem nt_at_2c : fetchRel nafTableFromCode 0x2C = some (.branch .beq (9 : Fin 32) x0 0x1C, 2) := by decide
theorem nt_at_2e : fetchRel nafTableFromCode 0x2E = some (.aluImm .add a1 sp 0x6EC, 4) := by decide
theorem nt_at_32 : fetchRel nafTableFromCode 0x32 = some (.aluImm .add a2 x0 0xA0, 4) := by decide
theorem nt_at_36 : fetchRel nafTableFromCode 0x36 = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem nt_at_38 : fetchRel nafTableFromCode 0x38 = some (.auipc ra 0x4000, 4) := by decide
theorem nt_at_3c : fetchRel nafTableFromCode 0x3C = some (.jalr ra ra 0x12C, 4) := by decide
theorem nt_at_40 : fetchRel nafTableFromCode 0x40 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xA0, 4) := by decide
theorem nt_at_44 : fetchRel nafTableFromCode 0x44 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem nt_at_46 : fetchRel nafTableFromCode 0x46 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFE8, 2) := by decide
theorem nt_at_48 : fetchRel nafTableFromCode 0x48 = some (.aluImm .add a1 (19 : Fin 32) 0x28, 4) := by decide
theorem nt_at_4c : fetchRel nafTableFromCode 0x4C = some (.aluImm .add a0 sp 0x174, 2) := by decide
theorem nt_at_4e : fetchRel nafTableFromCode 0x4E = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem nt_at_52 : fetchRel nafTableFromCode 0x52 = some (.auipc ra 0x4000, 4) := by decide
theorem nt_at_56 : fetchRel nafTableFromCode 0x56 = some (.jalr ra ra 0x112, 4) := by decide
theorem nt_at_5a : fetchRel nafTableFromCode 0x5A = some (.aluImm .add a1 (19 : Fin 32) 0x50, 4) := by decide
theorem nt_at_5e : fetchRel nafTableFromCode 0x5E = some (.aluImm .add a0 sp 0x19C, 2) := by decide
theorem nt_at_60 : fetchRel nafTableFromCode 0x60 = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem nt_at_64 : fetchRel nafTableFromCode 0x64 = some (.auipc ra 0x4000, 4) := by decide
theorem nt_at_68 : fetchRel nafTableFromCode 0x68 = some (.jalr ra ra 0x100, 4) := by decide
theorem nt_at_6c : fetchRel nafTableFromCode 0x6C = some (.aluImm .add a0 sp 0x14C, 2) := by decide
theorem nt_at_6e : fetchRel nafTableFromCode 0x6E = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem nt_at_72 : fetchRel nafTableFromCode 0x72 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem nt_at_74 : fetchRel nafTableFromCode 0x74 = some (.auipc ra 0x4000, 4) := by decide
theorem nt_at_78 : fetchRel nafTableFromCode 0x78 = some (.jalr ra ra 0xF0, 4) := by decide
theorem nt_at_7c : fetchRel nafTableFromCode 0x7C = some (.aluImm .add a0 sp 0x6EC, 4) := by decide
theorem nt_at_80 : fetchRel nafTableFromCode 0x80 = some (.aluImm .add a1 sp 0x14C, 2) := by decide
theorem nt_at_82 : fetchRel nafTableFromCode 0x82 = some (.auipc ra 0x0, 4) := by decide
theorem nt_at_86 : fetchRel nafTableFromCode 0x86 = some (.jalr ra ra 0xFFFFFCE6, 4) := by decide
theorem nt_at_8a : fetchRel nafTableFromCode 0x8A = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem nt_at_8c : fetchRel nafTableFromCode 0x8C = some (.aluImm .add a1 sp 0x6EC, 4) := by decide
theorem nt_at_90 : fetchRel nafTableFromCode 0x90 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem nt_at_94 : fetchRel nafTableFromCode 0x94 = some (.jalr ra ra 0x6F2, 4) := by decide
theorem nt_at_98 : fetchRel nafTableFromCode 0x98 = some (.aluImm .add (9 : Fin 32) sp 0x1EC, 2) := by decide
theorem nt_at_9a : fetchRel nafTableFromCode 0x9A = some (.aluImm .add (8 : Fin 32) x0 0x7, 2) := by decide
theorem nt_at_9c : fetchRel nafTableFromCode 0x9C = some (.branch .beq (8 : Fin 32) x0 0x44, 2) := by decide
theorem nt_at_9e : fetchRel nafTableFromCode 0x9E = some (.aluImm .add a0 sp 0x6EC, 4) := by decide
theorem nt_at_a2 : fetchRel nafTableFromCode 0xA2 = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem nt_at_a4 : fetchRel nafTableFromCode 0xA4 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem nt_at_a6 : fetchRel nafTableFromCode 0xA6 = some (.auipc ra 0x0, 4) := by decide
theorem nt_at_aa : fetchRel nafTableFromCode 0xAA = some (.jalr ra ra 0xFFFFFB98, 4) := by decide
theorem nt_at_ae : fetchRel nafTableFromCode 0xAE = some (.aluImm .add a0 sp 0x14C, 2) := by decide
theorem nt_at_b0 : fetchRel nafTableFromCode 0xB0 = some (.aluImm .add a1 sp 0x6EC, 4) := by decide
theorem nt_at_b4 : fetchRel nafTableFromCode 0xB4 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem nt_at_b8 : fetchRel nafTableFromCode 0xB8 = some (.jalr ra ra 0x6CE, 4) := by decide
theorem nt_at_bc : fetchRel nafTableFromCode 0xBC = some (.aluImm .add a0 sp 0xAC, 2) := by decide
theorem nt_at_be : fetchRel nafTableFromCode 0xBE = some (.aluImm .add a1 sp 0x14C, 2) := by decide
theorem nt_at_c0 : fetchRel nafTableFromCode 0xC0 = some (.auipc ra 0x0, 4) := by decide
theorem nt_at_c4 : fetchRel nafTableFromCode 0xC4 = some (.jalr ra ra 0xFFFFFDA2, 4) := by decide
theorem nt_at_c8 : fetchRel nafTableFromCode 0xC8 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xA0, 4) := by decide
theorem nt_at_cc : fetchRel nafTableFromCode 0xCC = some (.aluImm .add a1 sp 0xAC, 2) := by decide
theorem nt_at_ce : fetchRel nafTableFromCode 0xCE = some (.aluImm .add a2 x0 0xA0, 4) := by decide
theorem nt_at_d2 : fetchRel nafTableFromCode 0xD2 = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem nt_at_d4 : fetchRel nafTableFromCode 0xD4 = some (.auipc ra 0x4000, 4) := by decide
theorem nt_at_d8 : fetchRel nafTableFromCode 0xD8 = some (.jalr ra ra 0x90, 4) := by decide
theorem nt_at_dc : fetchRel nafTableFromCode 0xDC = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem nt_at_de : fetchRel nafTableFromCode 0xDE = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFC0, 2) := by decide
theorem nt_at_e0 : fetchRel nafTableFromCode 0xE0 = some (.aluImm .add a1 sp 0x1EC, 2) := by decide
theorem nt_at_e2 : fetchRel nafTableFromCode 0xE2 = some (.aluImm .add a2 x0 0x500, 4) := by decide
theorem nt_at_e6 : fetchRel nafTableFromCode 0xE6 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem nt_at_e8 : fetchRel nafTableFromCode 0xE8 = some (.auipc ra 0x4000, 4) := by decide
theorem nt_at_ec : fetchRel nafTableFromCode 0xEC = some (.jalr ra ra 0x7C, 4) := by decide
theorem nt_at_f0 : fetchRel nafTableFromCode 0xF0 = some (.aluImm .add a0 sp 0x780, 4) := by decide
theorem nt_at_f4 : fetchRel nafTableFromCode 0xF4 = some (.load .lw ra a0 0x1C, 4) := by decide
theorem nt_at_f8 : fetchRel nafTableFromCode 0xF8 = some (.load .lw (8 : Fin 32) a0 0x18, 2) := by decide
theorem nt_at_fa : fetchRel nafTableFromCode 0xFA = some (.load .lw (9 : Fin 32) a0 0x14, 2) := by decide
theorem nt_at_fc : fetchRel nafTableFromCode 0xFC = some (.load .lw (18 : Fin 32) a0 0x10, 4) := by decide
theorem nt_at_100 : fetchRel nafTableFromCode 0x100 = some (.load .lw (19 : Fin 32) a0 0xC, 4) := by decide
theorem nt_at_104 : fetchRel nafTableFromCode 0x104 = some (.aluImm .add sp sp 0x7A0, 4) := by decide
theorem nt_at_108 : fetchRel nafTableFromCode 0x108 = some (.jalr x0 ra 0x0, 2) := by decide
end

abbrev NTF : Word := BitVec.ofNat 32 nafTableFromAddress

/-- A point's four coordinates, as limb lists. -/
abbrev Pt := List Nat × List Nat × List Nat × List Nat

theorem wl_red (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 : Nat) :
    wl (feReduceSpec z0 z1 z2 z3 z4 z5 z6 z7 z8 z9) = feReduceSpec z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 := by
  simp only [wl, ofW, limbF, feReduceSpec, List.getD_cons_succ, List.getD_cons_zero, BitVec.toNat_ofNat, Nat.mod_mod]

theorem wl_mulL (a b : List Nat) : wl (mulL a b) = mulL a b := wl_red ..
theorem wl_subL (a b : List Nat) : wl (subL a b) = subL a b := wl_red ..

theorem ofW_get (x : Nat → Word) : ∀ i, i < 10 → BitVec.ofNat 32 (ofW x)[i]! = x i
  | 0, _ => w_ofNat_toNat _
  | 1, _ => w_ofNat_toNat _
  | 2, _ => w_ofNat_toNat _
  | 3, _ => w_ofNat_toNat _
  | 4, _ => w_ofNat_toNat _
  | 5, _ => w_ofNat_toNat _
  | 6, _ => w_ofNat_toNat _
  | 7, _ => w_ofNat_toNat _
  | 8, _ => w_ofNat_toNat _
  | 9, _ => w_ofNat_toNat _
  | n + 10, h => absurd h (by omega)

theorem subL_ofW (x y : Nat → Word) : feSubSpec x y = subL (ofW x) (ofW y) :=
  feSubSpec_ext (fun i hi => (ofW_get x i hi).symm) (fun i hi => (ofW_get y i hi).symm)

theorem ofW_subW (x y : Nat → Word) : ofW (feSubW x y) = subL (ofW x) (ofW y) := by
  show wl (feSubSpec x y) = _
  rw [subL_ofW, wl_subL]

theorem mulL_ofW (x y : Nat → Word) :
    mulL (ofW x) (ofW y) = feMulSpec (x 0).toNat (x 1).toNat (x 2).toNat (x 3).toNat (x 4).toNat (x 5).toNat
      (x 6).toNat (x 7).toNat (x 8).toNat (x 9).toNat (y 0).toNat (y 1).toNat (y 2).toNat (y 3).toNat (y 4).toNat
      (y 5).toNat (y 6).toNat (y 7).toNat (y 8).toNat (y 9).toNat := by
  simp only [mulL, ofW, List.getD_cons_succ, List.getD_cons_zero]

theorem ofW_mulW (x y : Nat → Word) : ofW (feMulW x y) = mulL (ofW x) (ofW y) := by
  rw [← wl_mulL, mulL_ofW]; rfl

theorem ofW_addW (x y : Nat → Word) : ofW (feAddW x y) = addL (ofW x) (ofW y) := by
  simp only [ofW, feAddW, addL, BitVec.toNat_add]; rfl

theorem ofW_limbs (M : Word → BitVec 8) (a : Word) : ofW (limbs M a) = feW M a := rfl

/-- `EdwardsPoint + ProjectiveNielsPoint` on limb lists, in the Rust
source's order: the completed point's `X`, `Y`, `Z`, and `T`. -/
def addNL (P N : Pt) : Pt :=
  let PP := mulL (addL P.2.1 P.1) N.1
  let MM := mulL (subL P.2.1 P.1) N.2.1
  let TT := mulL P.2.2.2 N.2.2.2
  let ZZ := mulL P.2.2.1 N.2.2.1
  (subL PP MM, addL PP MM, addL (addL ZZ ZZ) TT, subL (addL ZZ ZZ) TT)

/-- `as_projective_niels` on limb lists, with `2d` as `d2`. -/
def nielsL (P : Pt) (d2 : List Nat) : Pt := (addL P.2.1 P.1, subL P.2.1 P.1, P.2.2.1, mulL P.2.2.2 d2)

/-- `CompletedPoint::as_extended` on limb lists. -/
def extL (C : Pt) : Pt := (mulL C.1 C.2.2.2, mulL C.2.1 C.2.2.1, mulL C.2.2.1 C.2.2.2, mulL C.1 C.2.1)

/-- The table `from` builds for `A`: entry `i` is `(2i + 1) A` in projective
Niels form, as the Rust source computes it. -/
def nafTab (A : Pt) (d2 : List Nat) : Nat → Pt
  | 0 => nielsL A d2
  | i + 1 => nielsL (extL (addNL (extL (edDoubleSpec A.1 A.2.1 A.2.2.1)) (nafTab A d2 i))) d2

/-- The four coordinates of a point at `a`. -/
def ptAt (M : Word → BitVec 8) (a : Word) : Pt :=
  (feW M a, feW M (a + BitVec.ofNat 32 40), feW M (a + BitVec.ofNat 32 80), feW M (a + BitVec.ofNat 32 120))

/-- Niels addition's theorem, restated over limb lists. -/
theorem ean_pt {M M' : Word → BitVec 8} {out ep np : Word}
    (h : ∀ i, i < 10 →
        limbs M' out i = feSubW (eanPP M ep np) (eanMM M ep np) i ∧
        limbs M' (out + 0x28) i = feAddW (eanPP M ep np) (eanMM M ep np) i ∧
        limbs M' (out + 0x50) i = feAddW (eanZZ2 M ep np) (eanTT M ep np) i ∧
        limbs M' (out + 0x78) i = feSubW (eanZZ2 M ep np) (eanTT M ep np) i) :
    ptAt M' out = addNL (ptAt M ep) (ptAt M np) := by
  have e0 := feW_limbs_ofW fun i hi => (h i hi).1
  have e1 := feW_limbs_ofW fun i hi => (h i hi).2.1
  have e2 := feW_limbs_ofW fun i hi => (h i hi).2.2.1
  have e3 := feW_limbs_ofW fun i hi => (h i hi).2.2.2
  simp only [eanPP, eanMM, eanZZ2, eanTT, ofW_subW, ofW_addW, ofW_mulW, ofW_limbs] at e0 e1 e2 e3
  unfold ptAt addNL
  rw [show out + BitVec.ofNat 32 40 = out + 0x28 from rfl, show out + BitVec.ofNat 32 80 = out + 0x50 from rfl,
    show out + BitVec.ofNat 32 120 = out + 0x78 from rfl, e0, e1, e2, e3]
  rfl

/-- `as_projective_niels`'s theorem, restated over limb lists. -/
theorem apn_pt {M M' : Word → BitVec 8} {out ip : Word}
    (h0 : ∀ i, i < 10 → memLoad32 M' (out + BitVec.ofNat 32 (4 * i)) =
      memLoad32 M (ip + 0x28 + BitVec.ofNat 32 (4 * i)) + memLoad32 M (ip + BitVec.ofNat 32 (4 * i)))
    (h1 : (wordsAt M' (out + 0x28) 10).map BitVec.toNat =
      feSubSpec (fun i => memLoad32 M (ip + 0x28 + BitVec.ofNat 32 (4 * i))) (fun i => memLoad32 M (ip + BitVec.ofNat 32 (4 * i))))
    (h2 : ∀ j, j < 40 → M' (out + 0x50 + BitVec.ofNat 32 j) = M (ip + 0x50 + BitVec.ofNat 32 j))
    (h3 : (wordsAt M' (out + 0x78) 10).map BitVec.toNat = feMulAt M (ip + 0x78) apnD) :
    ptAt M' out = nielsL (ptAt M ip) (feW M apnD) := by
  unfold ptAt nielsL
  rw [show out + BitVec.ofNat 32 40 = out + 0x28 from rfl, show out + BitVec.ofNat 32 80 = out + 0x50 from rfl,
    show out + BitVec.ofNat 32 120 = out + 0x78 from rfl, show ip + BitVec.ofNat 32 40 = ip + 0x28 from rfl,
    show ip + BitVec.ofNat 32 80 = ip + 0x50 from rfl, show ip + BitVec.ofNat 32 120 = ip + 0x78 from rfl,
    feW_add h0, feW_sub h1, feW_of_words h3, feMulAt_eq,
    feW_eq2 (M := M) (M' := M') (a := out + 0x50) (b := ip + 0x50) fun i hi => vk_ld2 fun j hj => by
      rw [add_ofNat_assoc, add_ofNat_assoc]; exact h2 _ (by omega)]

theorem St.callApn {M : Word → BitVec 8} {P : Word} {code : List Nat} {nm : Machine} {off : Nat}
    (s : St M P nm off (reg nm)) (hc : CodeIn M P code) {imm o cb : Word}
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = cb) (hev : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (env : APNEnv M cb (reg nm sp) (reg nm a0) (reg nm a1)) :
    ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = reg nm sp ∧
      (∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nm' q = reg nm q) ∧
      ptAt nm'.mem (reg nm a0) = nielsL (ptAt M (reg nm a1)) (feW M apnD) ∧
      ∀ x, Sep (reg nm sp + 0xFFFFFEC0) 0x140 x 1 → Sep (reg nm a0) 0xA0 x 1 → nm'.mem x = M x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb env.hP
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w0, w1, w2, w3, f2⟩ := asProjNiels_correct n1 (by rw [mem1]; exact env) pc1
    (r1 sp (by decide)) (r1 a0 (by decide)) (r1 a1 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev)
  rw [mem1] at w0 w1 w2 w3 f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)],
    apn_pt w0 w1 w2 w3, f2⟩

theorem St.callEan {M : Word → BitVec 8} {P : Word} {code : List Nat} {nm : Machine} {off : Nat}
    (s : St M P nm off (reg nm)) (hc : CodeIn M P code) {imm o cb : Word}
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = cb) (hev : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (env : EANEnv M cb (reg nm sp) (reg nm a0) (reg nm a1) (reg nm a2)) :
    ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = reg nm sp ∧
      (∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nm' q = reg nm q) ∧
      ptAt nm'.mem (reg nm a0) = addNL (ptAt M (reg nm a1)) (ptAt M (reg nm a2)) ∧
      ∀ x, Sep (reg nm sp + 0xFFFFFD90) 0x270 x 1 → Sep (reg nm a0) 0xA0 x 1 → nm'.mem x = M x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb env.hP
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w, f2⟩ := edAddNiels_correct n1 (by rw [mem1]; exact env) pc1
    (r1 sp (by decide)) (r1 a0 (by decide)) (r1 a1 (by decide)) (r1 a2 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev)
  rw [mem1] at w f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)],
    ean_pt w, f2⟩

end C3.RV32
