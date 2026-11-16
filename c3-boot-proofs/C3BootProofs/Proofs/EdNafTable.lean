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

/-! ## The frame invariant -/

/-- The code `from` runs and its callees'. -/
structure NtEnv (M : Word → BitVec 8) : Prop where
  cod : CodeIn M NTF nafTableFromCode
  apn : CodeIn M (BitVec.ofNat 32 asProjNielsAddress) asProjNielsCode
  ean : CodeIn M (BitVec.ofNat 32 edAddNielsAddress) edAddNielsCode
  ext : CodeIn M (BitVec.ofNat 32 asExtendedAddress) asExtendedCode
  dbl : CodeIn M (BitVec.ofNat 32 edDoubleAddress) edDoubleCode
  add : CodeIn M (BitVec.ofNat 32 feAddAddress) feAddCode
  sub : CodeIn M (BitVec.ofNat 32 feSubAddress) feSubCode
  mul : CodeIn M (BitVec.ofNat 32 feMulAddress) feMulCode
  red : CodeIn M (BitVec.ofNat 32 feReduceAddress) feReduceCode
  sq : CodeIn M (BitVec.ofNat 32 feSquareAddress) feSquareCode
  sqi : CodeIn M (BitVec.ofNat 32 feSquareInnerAddress) feSquareInnerCode
  mcs : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  mcb : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode

/-- `from`'s stack: 0xA10 bytes at `R`, with its own frame from `R + 0x270`. -/
structure NtCtx (M0 : Word → BitVec 8) (R : Word) : Prop where
  E : NtEnv M0
  hR : R.toNat % 4 = 0
  hRw : R.toNat + 0xA10 ≤ 0x40000000

section Ctx
variable {M0 : Word → BitVec 8} {R : Word}

theorem NtCtx.toNat_off (C : NtCtx M0 R) {c : Nat} (h : c ≤ 0xA10) : (R + BitVec.ofNat 32 c).toNat = R.toNat + c := by
  have := C.hRw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem NtCtx.code (C : NtCtx M0 R) {M : Word → BitVec 8} (hM : ∀ x, Sep R 0xA10 x 1 → M x = M0 x) {b : Word}
    {code : List Nat} (hc : CodeIn M0 b code) (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + code.length ≤ 2 ^ 32) :
    CodeIn M b code :=
  hc.hi (fun x hx => hM x (sep_of_le (by have := C.hRw; omega) (by have := x.isLt; omega))) hb hbl

theorem NtCtx.hiSep (C : NtCtx M0 R) {c l : Nat} (h : c + l ≤ 0xA10) {b : Word} {k : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + k ≤ 2 ^ 32) : Sep (R + BitVec.ofNat 32 c) l b k :=
  sep_of_le (by rw [C.toNat_off (by omega)]; have := C.hRw; omega) hbl

theorem NtCtx.offs (_ : NtCtx M0 R) {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c) (hc : c + n ≤ 0xA10)
    (hd : d + k ≤ 0xA10) : Sep (R + BitVec.ofNat 32 c) n (R + BitVec.ofNat 32 d) k :=
  sep_offsets R h (by omega) (by omega)

theorem NtCtx.inR (_ : NtCtx M0 R) {c l : Nat} (h : c + l ≤ 0xA10) {x : Word} (hx : Sep R 0xA10 x 1) :
    Sep (R + BitVec.ofNat 32 c) l x 1 := (hx.symm.subR h).symm

theorem NtCtx.even (_ : NtCtx M0 R) (k : Nat) (hk : k % 2 = 0) : (NTF + BitVec.ofNat 32 k).toNat % 2 = 0 :=
  even_at NTF (by decide) k hk

end Ctx

/-- Between calls: `sp` at `R + 0x270`, `s2` and `s3` holding the table's
and the point's addresses, the other callee-saved registers as on entry,
memory outside the stack as on entry, and the saved registers' slots as
after the prologue. -/
structure NtSt (M0 Ms : Word → BitVec 8) (R out A : Word) (r0 : Fin 32 → Word) (M : Word → BitVec 8) (n : Machine)
    (off : Nat) : Prop where
  st : St M NTF n off (reg n)
  hsp : reg n sp = R + BitVec.ofNat 32 0x270
  hs2 : reg n (18 : Fin 32) = out
  hs3 : reg n (19 : Fin 32) = A
  keep : ∀ q : Fin 32, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] → reg n q = r0 q
  agree : ∀ x, Sep R 0xA10 x 1 → M x = M0 x
  slots : ∀ c, 0x9FC ≤ c → c < 0xA10 → M (R + BitVec.ofNat 32 c) = Ms (R + BitVec.ofNat 32 c)

section Calls
variable {M0 Ms M : Word → BitVec 8} {R out A : Word} {r0 : Fin 32 → Word} {n : Machine}

theorem NtSt.after {off : Nat} (D : NtSt M0 Ms R out A r0 M n off) {M' : Word → BitVec 8} {n' : Machine} {off' : Nat}
    (u : St M' NTF n' off' (reg n')) (hsp : reg n' sp = reg n sp)
    (hk : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q)
    {P : Word → Prop} (hfr : ∀ x, P x → M' x = M x) (h1 : ∀ x, Sep R 0xA10 x 1 → P x)
    (h2 : ∀ c, 0x9FC ≤ c → c < 0xA10 → P (R + BitVec.ofNat 32 c)) : NtSt M0 Ms R out A r0 M' n' off' :=
  ⟨u, by rw [hsp, D.hsp], by rw [hk _ (by decide), D.hs2], by rw [hk _ (by decide), D.hs3],
    fun q hq => by rw [hk q (by revert hq; revert q; decide), D.keep q hq],
    fun x hx => by rw [hfr x (h1 x hx), D.agree x hx], fun c c1 c2 => by rw [hfr _ (h2 c c1 c2), D.slots c c1 c2]⟩

theorem NtSt.code {off : Nat} (C : NtCtx M0 R) (D : NtSt M0 Ms R out A r0 M n off) {b : Word} {code : List Nat}
    (hc : CodeIn M0 b code) (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + code.length ≤ 2 ^ 32) : CodeIn M b code :=
  C.code D.agree hc hb hbl

set_option maxRecDepth 20000 in
/-- A `memcpy` into the frame at `R + k`. -/
theorem NtSt.mc {off : Nat} (C : NtCtx M0 R) (D : NtSt M0 Ms R out A r0 M n off) {imm o : Word}
    (h1 : fetchRel nafTableFromCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel nafTableFromCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : NTF + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 memcpyStubAddress) (hev : off % 2 = 0)
    {k N : Nat} {src : Word} (hk1 : 0x270 ≤ k) (hk2 : k + N ≤ 0x9FC)
    (ha0 : reg n a0 = R + BitVec.ofNat 32 k) (ha1 : reg n a1 = src) (ha2 : reg n a2 = BitVec.ofNat 32 N)
    (hsF : Sep src N (R + BitVec.ofNat 32 0x260) 16) (hsep : Sep (R + BitVec.ofNat 32 k) N src N)
    (hsw : src.toNat + N < 2 ^ 32) :
    ∃ n', Steps n n' ∧ NtSt M0 Ms R out A r0 n'.mem n' (off + 8) ∧
      (∀ x, Sep (R + BitVec.ofNat 32 0x260) 16 x 1 → n'.mem x = copyBytes M (R + BitVec.ofNat 32 k) src N x) ∧
      ∀ q : Fin 32, q.val ∈ [8, 9, 18, 19] → reg n' q = reg n q := by
  have hc : CodeIn M NTF nafTableFromCode := D.code C C.E.cod (by decide) (by decide)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa (cb := BitVec.ofNat 32 memcpyStubAddress) hc h1 h2 hb
    (by decide)
  have r1 := PEnv.reg1 regs1 D.st.zero
  have eF : R + BitVec.ofNat 32 0x270 + 0xFFFFFFF0 = R + BitVec.ofNat 32 0x260 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n2, c2, pc2, sp2, _, f2, k2⟩ := memcpy_correct n1 (BitVec.ofNat 32 memcpyStubAddress)
    (NTF + BitVec.ofNat 32 (off + 8)) (R + BitVec.ofNat 32 k) src N
    (fun i hi => by rw [mem1]; exact D.code C C.E.mcs (by decide) (by decide) i hi) (by decide) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ (C.even _ (by omega)))
    (by
      rw [mem1, r1 sp (by decide), D.hsp, eF]
      exact { code := D.code C C.E.mcb (by decide) (by decide)
              hDC := C.hiSep (by omega) (by decide) (by decide)
              hFC := C.hiSep (by decide) (by decide) (by decide)
              hdF := C.offs (Or.inr (by omega)) (by omega) (by decide)
              hsF := hsF
              hsep := hsep
              hF := aligned_add C.hR (by decide)
              hFw := by rw [C.toNat_off (by decide)]; have := C.hRw; omega
              hdw := by rw [C.toNat_off (by omega)]; have := C.hRw; omega
              hsw := hsw })
  rw [mem1, r1 sp (by decide), D.hsp, eF] at f2
  have kq : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  refine ⟨n2, c1.trans c2, D.after (P := fun x => Sep (R + BitVec.ofNat 32 0x260) 16 x 1 ∧
      Sep (R + BitVec.ofNat 32 k) N x 1) ⟨by rw [pc2], rfl, fun _ => rfl⟩
      (by rw [sp2, r1 sp (by decide)]) (fun q hq => kq q (by revert hq; revert q; decide))
      (fun x hx => by rw [f2 x hx.1, copyBytes_sep hx.2 (Nat.le_refl _)])
      (fun x hx => ⟨C.inR (by decide) hx, C.inR (by omega) hx⟩)
      (fun c c1 c2 => ⟨C.offs (Or.inl (by omega)) (by decide) (by omega), C.offs (Or.inl (by omega)) (by omega) (by omega)⟩),
    f2, fun q hq => kq q (by revert hq; revert q; decide)⟩

set_option maxRecDepth 20000 in
/-- A call of `as_projective_niels` from `ip` into the frame at `R + k`. -/
theorem NtSt.apn {off : Nat} (C : NtCtx M0 R) (D : NtSt M0 Ms R out A r0 M n off) {imm o : Word}
    (h1 : fetchRel nafTableFromCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel nafTableFromCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : NTF + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 asProjNielsAddress) (hev : off % 2 = 0)
    {k : Nat} {ip : Word} (hk : k % 4 = 0) (hk1 : 0x270 ≤ k) (hk2 : k + 0xA0 ≤ 0x9FC)
    (ha0 : reg n a0 = R + BitVec.ofNat 32 k) (ha1 : reg n a1 = ip) (hip : ip.toNat % 4 = 0) (hiw : ip.toNat + 0xA0 < 2 ^ 32)
    (sIG : Sep ip 0xA0 (R + BitVec.ofNat 32 0x130) 0x140) (sIO : Sep ip 0xA0 (R + BitVec.ofNat 32 k) 0xA0)
    (sD : Sep apnD 40 R 0xA10) :
    ∃ n', Steps n n' ∧ NtSt M0 Ms R out A r0 n'.mem n' (off + 8) ∧
      ptAt n'.mem (R + BitVec.ofNat 32 k) = nielsL (ptAt M ip) (feW M apnD) ∧
      (∀ q : Fin 32, q.val ∈ [8, 9, 18, 19] → reg n' q = reg n q) ∧
      ∀ x, Sep (R + BitVec.ofNat 32 0x130) 0x140 x 1 → Sep (R + BitVec.ofNat 32 k) 0xA0 x 1 → n'.mem x = M x := by
  have hc : CodeIn M NTF nafTableFromCode := D.code C C.E.cod (by decide) (by decide)
  have eS : R + BitVec.ofNat 32 0x270 + 0xFFFFFEC0 = R + BitVec.ofNat 32 0x130 := by rw [BitVec.add_assoc]; rfl
  have env : APNEnv M (BitVec.ofNat 32 asProjNielsAddress) (reg n sp) (reg n a0) (reg n a1) := by
    rw [D.hsp, ha0, ha1]
    exact { hP := by decide
            cod := D.code C C.E.apn (by decide) (by decide)
            add := by rw [show (BitVec.ofNat 32 asProjNielsAddress : Word) + 0xFFFFE57A = BitVec.ofNat 32 feAddAddress by decide]
                      exact D.code C C.E.add (by decide) (by decide)
            addS := by rw [show (BitVec.ofNat 32 asProjNielsAddress : Word) + 0xFFFFE57A + 0x5D88 =
                        BitVec.ofNat 32 memcpyStubAddress by decide]; exact D.code C C.E.mcs (by decide) (by decide)
            addB := by rw [show (BitVec.ofNat 32 asProjNielsAddress : Word) + 0xFFFFE57A + 0x5D90 =
                        BitVec.ofNat 32 memcpyStubAddress + 8 by decide]; exact D.code C C.E.mcb (by decide) (by decide)
            sub := by rw [show (BitVec.ofNat 32 asProjNielsAddress : Word) + 0xFFFFE5C8 = BitVec.ofNat 32 feSubAddress by decide]
                      exact D.code C C.E.sub (by decide) (by decide)
            subR := by rw [show (BitVec.ofNat 32 asProjNielsAddress : Word) + 0xFFFFE5C8 + 0xFFFFF72E =
                        BitVec.ofNat 32 feReduceAddress by decide]; exact D.code C C.E.red (by decide) (by decide)
            mcs := by rw [show (BitVec.ofNat 32 asProjNielsAddress : Word) + 0x4302 = BitVec.ofNat 32 memcpyStubAddress by decide]
                      exact D.code C C.E.mcs (by decide) (by decide)
            mcb := by rw [show (BitVec.ofNat 32 asProjNielsAddress : Word) + 0x430A =
                        BitVec.ofNat 32 memcpyStubAddress + 8 by decide]; exact D.code C C.E.mcb (by decide) (by decide)
            mul := by rw [show (BitVec.ofNat 32 asProjNielsAddress : Word) + 0xFFFFD206 = BitVec.ofNat 32 feMulAddress by decide]
                      exact D.code C C.E.mul (by decide) (by decide)
            mulR := by rw [show (BitVec.ofNat 32 asProjNielsAddress : Word) + 0xFFFFD206 + 0xAF0 =
                        BitVec.ofNat 32 feReduceAddress by decide]; exact D.code C C.E.red (by decide) (by decide)
            hsp := aligned_add C.hR (by decide)
            hS := by rw [C.toNat_off (by decide)]; omega
            hout := aligned_add C.hR hk
            hip := hip
            how := by rw [C.toNat_off (by omega)]; have := C.hRw; omega
            hiw := hiw
            sGC := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGA := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGAS := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGAB := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGS := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGSR := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGU := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGB := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGM := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGMR := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sOC := C.hiSep (by omega) (by decide) (by decide)
            sOA := C.hiSep (by omega) (by decide) (by decide)
            sOAB := C.hiSep (by omega) (by decide) (by decide)
            sOS := C.hiSep (by omega) (by decide) (by decide)
            sOSR := C.hiSep (by omega) (by decide) (by decide)
            sOU := C.hiSep (by omega) (by decide) (by decide)
            sOB := C.hiSep (by omega) (by decide) (by decide)
            sOM := C.hiSep (by omega) (by decide) (by decide)
            sOMR := C.hiSep (by omega) (by decide) (by decide)
            sOG := by rw [eS]; exact C.offs (Or.inr (by omega)) (by omega) (by decide)
            sIG := by rw [eS]; exact sIG
            sIO := sIO
            sDG := by rw [eS]; exact sD.subR (by decide)
            sDO := sD.subR (by omega) }
  obtain ⟨n2, c2, u2, sp2, k2, w2, f2⟩ := D.st.callApn hc h1 h2 hb (C.even _ (by omega)) env
  rw [ha0, ha1] at w2
  rw [D.hsp, eS, ha0] at f2
  refine ⟨n2, c2, D.after (P := fun x => Sep (R + BitVec.ofNat 32 0x130) 0x140 x 1 ∧
      Sep (R + BitVec.ofNat 32 k) 0xA0 x 1) u2 sp2
      (fun q hq => k2 q (by revert hq; revert q; decide)) (fun x hx => f2 x hx.1 hx.2)
      (fun x hx => ⟨C.inR (by decide) hx, C.inR (by omega) hx⟩)
      (fun c c1 c2 => ⟨C.offs (Or.inl (by omega)) (by decide) (by omega), C.offs (Or.inl (by omega)) (by omega) (by omega)⟩),
    w2, fun q hq => k2 q (by revert hq; revert q; decide), f2⟩

set_option maxRecDepth 20000 in
theorem NtCtx.eanCode (C : NtCtx M0 R) {c l : Nat} (h : c + l ≤ 0xA10) :
    EanCode (BitVec.ofNat 32 edAddNielsAddress) (R + BitVec.ofNat 32 c) l :=
  ⟨C.hiSep h (by decide) (by decide), C.hiSep h (by decide) (by decide), C.hiSep h (by decide) (by decide),
    C.hiSep h (by decide) (by decide), C.hiSep h (by decide) (by decide), C.hiSep h (by decide) (by decide),
    C.hiSep h (by decide) (by decide), C.hiSep h (by decide) (by decide)⟩

set_option maxRecDepth 20000 in
/-- A call of `EdwardsPoint + ProjectiveNielsPoint` on frame operands. -/
theorem NtSt.ean {off : Nat} (C : NtCtx M0 R) (D : NtSt M0 Ms R out A r0 M n off) {imm o : Word}
    (h1 : fetchRel nafTableFromCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel nafTableFromCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : NTF + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 edAddNielsAddress) (hev : off % 2 = 0)
    {k e p : Nat} (hk : k % 4 = 0) (he : e % 4 = 0) (hp : p % 4 = 0) (hk1 : 0x270 ≤ k) (hk2 : k + 0xA0 ≤ 0x9FC)
    (he1 : 0x270 ≤ e) (he2 : e + 0xA0 ≤ 0x9FC) (hp1 : 0x270 ≤ p) (hp2 : p + 0xA0 ≤ 0x9FC)
    (hke : k + 0xA0 ≤ e ∨ e + 0xA0 ≤ k) (hkp : k + 0xA0 ≤ p ∨ p + 0xA0 ≤ k)
    (ha0 : reg n a0 = R + BitVec.ofNat 32 k) (ha1 : reg n a1 = R + BitVec.ofNat 32 e)
    (ha2 : reg n a2 = R + BitVec.ofNat 32 p) :
    ∃ n', Steps n n' ∧ NtSt M0 Ms R out A r0 n'.mem n' (off + 8) ∧
      ptAt n'.mem (R + BitVec.ofNat 32 k) = addNL (ptAt M (R + BitVec.ofNat 32 e)) (ptAt M (R + BitVec.ofNat 32 p)) ∧
      (∀ q : Fin 32, q.val ∈ [8, 9, 18, 19] → reg n' q = reg n q) ∧
      ∀ x, Sep R 0x270 x 1 → Sep (R + BitVec.ofNat 32 k) 0xA0 x 1 → n'.mem x = M x := by
  have hc : CodeIn M NTF nafTableFromCode := D.code C C.E.cod (by decide) (by decide)
  have eS : R + BitVec.ofNat 32 0x270 + 0xFFFFFD90 = R := by rw [BitVec.add_assoc]; exact BitVec.add_zero R
  have r0' : ∀ {l : Nat}, l ≤ 0xA10 → ∀ {d kk : Nat}, l ≤ d → d + kk ≤ 0xA10 → Sep R l (R + BitVec.ofNat 32 d) kk :=
    fun {l} hl {d kk} h1 h2 => by
      have := C.offs (c := 0) (n := l) (d := d) (k := kk) (Or.inl (by omega)) (by omega) h2; rwa [add_ofNat_zero] at this
  have env : EANEnv M (BitVec.ofNat 32 edAddNielsAddress) (reg n sp) (reg n a0) (reg n a1) (reg n a2) := by
    rw [D.hsp, ha0, ha1, ha2]
    exact { hP := by decide
            cod := D.code C C.E.ean (by decide) (by decide)
            add := by rw [show (BitVec.ofNat 32 edAddNielsAddress : Word) + 0xFFFFE79E = BitVec.ofNat 32 feAddAddress by decide]
                      exact D.code C C.E.add (by decide) (by decide)
            addS := by rw [show (BitVec.ofNat 32 edAddNielsAddress : Word) + 0xFFFFE79E + 0x5D88 =
                        BitVec.ofNat 32 memcpyStubAddress by decide]; exact D.code C C.E.mcs (by decide) (by decide)
            addB := by rw [show (BitVec.ofNat 32 edAddNielsAddress : Word) + 0xFFFFE79E + 0x5D90 =
                        BitVec.ofNat 32 memcpyStubAddress + 8 by decide]; exact D.code C C.E.mcb (by decide) (by decide)
            sub := by rw [show (BitVec.ofNat 32 edAddNielsAddress : Word) + 0xFFFFE7EC = BitVec.ofNat 32 feSubAddress by decide]
                      exact D.code C C.E.sub (by decide) (by decide)
            subR := by rw [show (BitVec.ofNat 32 edAddNielsAddress : Word) + 0xFFFFE7EC + 0xFFFFF72E =
                        BitVec.ofNat 32 feReduceAddress by decide]; exact D.code C C.E.red (by decide) (by decide)
            mul := by rw [show (BitVec.ofNat 32 edAddNielsAddress : Word) + 0xFFFFD42A = BitVec.ofNat 32 feMulAddress by decide]
                      exact D.code C C.E.mul (by decide) (by decide)
            mulR := by rw [show (BitVec.ofNat 32 edAddNielsAddress : Word) + 0xFFFFD42A + 0xAF0 =
                        BitVec.ofNat 32 feReduceAddress by decide]; exact D.code C C.E.red (by decide) (by decide)
            hsp := aligned_add C.hR (by decide)
            hS := by rw [C.toNat_off (by decide)]; omega
            hout := aligned_add C.hR hk
            hep := aligned_add C.hR he
            hnp := aligned_add C.hR hp
            how := by rw [C.toNat_off (by omega)]; have := C.hRw; omega
            hew := by rw [C.toNat_off (by omega)]; have := C.hRw; omega
            hnw := by rw [C.toNat_off (by omega)]; have := C.hRw; omega
            sG := by rw [eS]; have := C.eanCode (c := 0) (l := 0x270) (by decide); rwa [add_ofNat_zero] at this
            sO := C.eanCode (by omega)
            sOG := by rw [eS]; exact (r0' (by decide) hk1 (by omega)).symm
            sEG := by rw [eS]; exact (r0' (by decide) he1 (by omega)).symm
            sNG := by rw [eS]; exact (r0' (by decide) hp1 (by omega)).symm
            sEO := C.offs (by omega) (by omega) (by omega)
            sNO := C.offs (by omega) (by omega) (by omega) }
  obtain ⟨n2, c2, u2, sp2, k2, w2, f2⟩ := D.st.callEan hc h1 h2 hb (C.even _ (by omega)) env
  rw [ha0, ha1, ha2] at w2
  rw [D.hsp, eS, ha0] at f2
  refine ⟨n2, c2, D.after (P := fun x => Sep R 0x270 x 1 ∧ Sep (R + BitVec.ofNat 32 k) 0xA0 x 1) u2 sp2
      (fun q hq => k2 q (by revert hq; revert q; decide)) (fun x hx => f2 x hx.1 hx.2)
      (fun x hx => ⟨by have := C.inR (c := 0) (l := 0x270) (by decide) hx; rwa [add_ofNat_zero] at this,
        C.inR (by omega) hx⟩)
      (fun c c1 c2 => ⟨r0' (by decide) (by omega) (by omega), C.offs (Or.inl (by omega)) (by omega) (by omega)⟩),
    w2, fun q hq => k2 q (by revert hq; revert q; decide), f2⟩

set_option maxRecDepth 20000 in
/-- A call of `ProjectivePoint::double` on frame operands. -/
theorem NtSt.dbl {off : Nat} (C : NtCtx M0 R) (D : NtSt M0 Ms R out A r0 M n off) {imm o : Word}
    (h1 : fetchRel nafTableFromCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel nafTableFromCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : NTF + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 edDoubleAddress) (hev : off % 2 = 0)
    {k j : Nat} (hk : k % 4 = 0) (hj : j % 4 = 0) (hk1 : 0x270 ≤ k) (hk2 : k + 0xA0 ≤ 0x9FC)
    (hj1 : 0x270 ≤ j) (hj2 : j + 120 ≤ 0x9FC)
    (ha0 : reg n a0 = R + BitVec.ofNat 32 k) (ha1 : reg n a1 = R + BitVec.ofNat 32 j) :
    ∃ n', Steps n n' ∧ NtSt M0 Ms R out A r0 n'.mem n' (off + 8) ∧
      ptAt n'.mem (R + BitVec.ofNat 32 k) = edDoubleSpec (feW M (R + BitVec.ofNat 32 j))
        (feW M (R + BitVec.ofNat 32 j + 0x28)) (feW M (R + BitVec.ofNat 32 j + 0x50)) ∧
      (∀ q : Fin 32, q.val ∈ [8, 9, 18, 19] → reg n' q = reg n q) ∧
      ∀ x, Sep (R + BitVec.ofNat 32 0x60) 0x210 x 1 → Sep (R + BitVec.ofNat 32 k) 160 x 1 → n'.mem x = M x := by
  have hc : CodeIn M NTF nafTableFromCode := D.code C C.E.cod (by decide) (by decide)
  have eS : R + BitVec.ofNat 32 0x270 + 0xFFFFFDF0 = R + BitVec.ofNat 32 0x60 := by rw [BitVec.add_assoc]; rfl
  have env : EdDblEnv M (BitVec.ofNat 32 edDoubleAddress) (reg n sp + 0xFFFFFDF0) (reg n a0) (reg n a1) := by
    rw [D.hsp, ha0, ha1, eS]
    exact { hP := by decide
            code := D.code C C.E.dbl (by decide) (by decide)
            sq := by rw [show (BitVec.ofNat 32 edDoubleAddress : Word) + 0xFFFFE164 = BitVec.ofNat 32 feSquareAddress by decide]
                     exact D.code C C.E.sq (by decide) (by decide)
            sqi := by rw [show (BitVec.ofNat 32 edDoubleAddress : Word) + 0xFFFFE18A = BitVec.ofNat 32 feSquareInnerAddress by
                        decide]; exact D.code C C.E.sqi (by decide) (by decide)
            red := by rw [show (BitVec.ofNat 32 edDoubleAddress : Word) + 0xFFFFDDF0 = BitVec.ofNat 32 feReduceAddress by decide]
                      exact D.code C C.E.red (by decide) (by decide)
            add := by rw [show (BitVec.ofNat 32 edDoubleAddress : Word) + 0xFFFFE674 = BitVec.ofNat 32 feAddAddress by decide]
                      exact D.code C C.E.add (by decide) (by decide)
            sub := by rw [show (BitVec.ofNat 32 edDoubleAddress : Word) + 0xFFFFE6C2 = BitVec.ofNat 32 feSubAddress by decide]
                      exact D.code C C.E.sub (by decide) (by decide)
            mcS := by rw [show (BitVec.ofNat 32 edDoubleAddress : Word) + 0x43FC = BitVec.ofNat 32 memcpyStubAddress by decide]
                      exact D.code C C.E.mcs (by decide) (by decide)
            mcB := by rw [show (BitVec.ofNat 32 edDoubleAddress : Word) + 0x4404 = BitVec.ofNat 32 memcpyStubAddress + 8 by
                        decide]; exact D.code C C.E.mcb (by decide) (by decide)
            hG := aligned_add C.hR (by decide)
            hGt := by rw [C.toNat_off (by decide)]; have := C.hRw; omega
            hout := aligned_add C.hR hk
            hot := by rw [C.toNat_off (by omega)]; have := C.hRw; omega
            hsf := aligned_add C.hR hj
            hst := by rw [C.toNat_off (by omega)]; have := C.hRw; omega
            sGC := C.hiSep (by decide) (by decide) (by decide)
            sGQ := C.hiSep (by decide) (by decide) (by decide)
            sGI := C.hiSep (by decide) (by decide) (by decide)
            sGR := C.hiSep (by decide) (by decide) (by decide)
            sGA := C.hiSep (by decide) (by decide) (by decide)
            sGS := C.hiSep (by decide) (by decide) (by decide)
            sGM := C.hiSep (by decide) (by decide) (by decide)
            sGB := C.hiSep (by decide) (by decide) (by decide)
            sOC := C.hiSep (by omega) (by decide) (by decide)
            sOQ := C.hiSep (by omega) (by decide) (by decide)
            sOI := C.hiSep (by omega) (by decide) (by decide)
            sOR := C.hiSep (by omega) (by decide) (by decide)
            sOA := C.hiSep (by omega) (by decide) (by decide)
            sOS := C.hiSep (by omega) (by decide) (by decide)
            sOM := C.hiSep (by omega) (by decide) (by decide)
            sOB := C.hiSep (by omega) (by decide) (by decide)
            sOG := C.offs (Or.inr (by omega)) (by omega) (by decide)
            sFG := C.offs (Or.inr (by omega)) (by omega) (by decide) }
  obtain ⟨n2, c2, u2, sp2, k2, w2, f2⟩ := D.st.callEdDouble hc h1 h2 hb (C.even _ (by omega)) env
  rw [ha0, ha1] at w2
  rw [D.hsp, eS, ha0] at f2
  refine ⟨n2, c2, D.after (P := fun x => Sep (R + BitVec.ofNat 32 0x60) 0x210 x 1 ∧ Sep (R + BitVec.ofNat 32 k) 160 x 1)
      u2 sp2 (fun q hq => k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide))
      (fun x hx => f2 x hx.1 hx.2) (fun x hx => ⟨C.inR (by decide) hx, C.inR (by omega) hx⟩)
      (fun c c1 c2 => ⟨C.offs (Or.inl (by omega)) (by decide) (by omega), C.offs (Or.inl (by omega)) (by omega) (by omega)⟩),
    ?_, fun q hq => k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), f2⟩
  unfold ptAt; rw [w2]; rfl

set_option maxRecDepth 20000 in
/-- A call of `CompletedPoint::as_extended` on frame operands. -/
theorem NtSt.ext {off : Nat} (C : NtCtx M0 R) (D : NtSt M0 Ms R out A r0 M n off) {imm o : Word}
    (h1 : fetchRel nafTableFromCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel nafTableFromCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : NTF + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 asExtendedAddress) (hev : off % 2 = 0)
    {k j : Nat} (hk : k % 4 = 0) (hj : j % 4 = 0) (hk1 : 0x270 ≤ k) (hk2 : k + 0xA0 ≤ 0x9FC)
    (hj1 : 0x270 ≤ j) (hj2 : j + 0xA0 ≤ 0x9FC) (hkj : k + 0xA0 ≤ j ∨ j + 0xA0 ≤ k)
    (ha0 : reg n a0 = R + BitVec.ofNat 32 k) (ha1 : reg n a1 = R + BitVec.ofNat 32 j) :
    ∃ n', Steps n n' ∧ NtSt M0 Ms R out A r0 n'.mem n' (off + 8) ∧
      ptAt n'.mem (R + BitVec.ofNat 32 k) = extL (ptAt M (R + BitVec.ofNat 32 j)) ∧
      (∀ q : Fin 32, q.val ∈ [8, 9, 18, 19] → reg n' q = reg n q) ∧
      ∀ x, Sep (R + BitVec.ofNat 32 0x110) 0x160 x 1 → Sep (R + BitVec.ofNat 32 k) 160 x 1 → n'.mem x = M x := by
  have hc : CodeIn M NTF nafTableFromCode := D.code C C.E.cod (by decide) (by decide)
  have eS : axR (R + BitVec.ofNat 32 0x270) = R + BitVec.ofNat 32 0x110 := by
    unfold axR; rw [BitVec.add_assoc]; rfl
  have env : AxEnv M (BitVec.ofNat 32 asExtendedAddress) (reg n sp) (reg n a0) (reg n a1) := by
    rw [D.hsp, ha0, ha1]
    exact { hP := by decide
            code := D.code C C.E.ext (by decide) (by decide)
            mul := by rw [show (BitVec.ofNat 32 asExtendedAddress : Word) + 0xFFFFD8E6 = BitVec.ofNat 32 feMulAddress by decide]
                      exact D.code C C.E.mul (by decide) (by decide)
            red := by rw [show (BitVec.ofNat 32 asExtendedAddress : Word) + 0xFFFFE3D6 = BitVec.ofNat 32 feReduceAddress by
                        decide]; exact D.code C C.E.red (by decide) (by decide)
            hsp := aligned_add C.hR (by decide)
            hS := by rw [C.toNat_off (by decide)]; omega
            hout := aligned_add C.hR hk
            hcp := aligned_add C.hR hj
            sC := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sM := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sR := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            oR := by rw [eS]; exact C.offs (Or.inr (by omega)) (by omega) (by decide)
            cR := by rw [eS]; exact C.offs (Or.inr (by omega)) (by omega) (by decide)
            oCp := C.offs hkj (by omega) (by omega)
            oC := C.hiSep (by omega) (by decide) (by decide)
            oM := C.hiSep (by omega) (by decide) (by decide)
            oRd := C.hiSep (by omega) (by decide) (by decide) }
  obtain ⟨n2, c2, u2, sp2, k2, w0, w1, w2, w3, f2⟩ := D.st.callAsExt hc h1 h2 hb (C.even _ (by omega)) env
  rw [ha0, ha1] at w0 w1 w2 w3
  rw [D.hsp, eS, ha0] at f2
  refine ⟨n2, c2, D.after (P := fun x => Sep (R + BitVec.ofNat 32 0x110) 0x160 x 1 ∧ Sep (R + BitVec.ofNat 32 k) 160 x 1)
      u2 sp2 (fun q hq => k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide))
      (fun x hx => f2 x hx.1 hx.2) (fun x hx => ⟨C.inR (by decide) hx, C.inR (by omega) hx⟩)
      (fun c c1 c2 => ⟨C.offs (Or.inl (by omega)) (by decide) (by omega), C.offs (Or.inl (by omega)) (by omega) (by omega)⟩),
    ?_, fun q hq => k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), f2⟩
  unfold ptAt extL
  rw [show R + BitVec.ofNat 32 k + BitVec.ofNat 32 40 = R + BitVec.ofNat 32 k + 0x28 from rfl,
    show R + BitVec.ofNat 32 k + BitVec.ofNat 32 80 = R + BitVec.ofNat 32 k + 0x50 from rfl,
    show R + BitVec.ofNat 32 k + BitVec.ofNat 32 120 = R + BitVec.ofNat 32 k + 0x78 from rfl, w0, w1, w2, w3]
  rfl

end Calls

theorem ptAt_frame {M M' : Word → BitVec 8} {a : Word} (h : ∀ j, j < 160 → M' (a + BitVec.ofNat 32 j) = M (a + BitVec.ofNat 32 j)) :
    ptAt M' a = ptAt M a := by
  have fw : ∀ c, c + 40 ≤ 160 → feW M' (a + BitVec.ofNat 32 c) = feW M (a + BitVec.ofNat 32 c) := fun c hc =>
    feW_frame fun i hi => memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc, add_ofNat_assoc]; exact h _ (by omega)
  unfold ptAt
  have f0 := fw 0 (by decide); rw [add_ofNat_zero] at f0
  rw [f0, fw 40 (by decide), fw 80 (by decide), fw 120 (by decide)]

theorem ptAt_copy {M : Word → BitVec 8} {d s : Word} {N c : Nat} (h : c + 160 ≤ N) (hN : N < 2 ^ 32) :
    ptAt (copyBytes M d s N) (d + BitVec.ofNat 32 c) = ptAt M (s + BitVec.ofNat 32 c) := by
  unfold ptAt
  rw [spk, spk, spk, spk, spk, spk, feW_copyAt (by omega) hN, feW_copyAt (c := c + 40) (by omega) hN,
    feW_copyAt (c := c + 80) (by omega) hN, feW_copyAt (c := c + 120) (by omega) hN]

section Steps
variable {M0 Ms M : Word → BitVec 8} {R out A : Word} {r0 : Fin 32 → Word} {n : Machine}

/-- A step that writes a register `from` doesn't track. -/
theorem NtSt.step {off : Nat} (D : NtSt M0 Ms R out A r0 M n off) {n' : Machine} {off' : Nat} {rd : Fin 32} {v : Word}
    (u : St M NTF n' off' (upd (reg n) rd v)) (hrd : rd.val ∉ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) :
    NtSt M0 Ms R out A r0 M n' off' :=
  D.after (P := fun _ => True) u.self (u.upd_ne D.st.zero sp (fun e => hrd (by rw [← e]; decide)))
    (fun q hq => u.upd_ne D.st.zero q (fun e => hrd (by rw [← e]; exact List.mem_cons_of_mem _ hq)))
    (fun _ _ => rfl) (fun _ _ => trivial) (fun _ _ _ => trivial)

theorem NtSt.jmp' {off : Nat} (D : NtSt M0 Ms R out A r0 M n off) {n' : Machine} {off' : Nat}
    (u : St M NTF n' off' (reg n)) : NtSt M0 Ms R out A r0 M n' off' :=
  D.after (P := fun _ => True) u.self (u.regs sp) (fun q _ => u.regs q) (fun _ _ => rfl) (fun _ _ => trivial)
    (fun _ _ _ => trivial)

end Steps

theorem nt_bne : ∀ t : Fin 8, 0 < t.val → branchTaken .bne (BitVec.ofNat 32 t.val) 0 = true := by decide
theorem nt_dec : ∀ t : Fin 8, aluEval .add (BitVec.ofNat 32 (t.val + 1)) 0xFFFFFFFF = BitVec.ofNat 32 t.val := by decide

section Loops
variable {M0 Ms : Word → BitVec 8} {R out A : Word} {r0 : Fin 32 → Word}

/-- After a frame `memcpy`, a point that doesn't overlap the copy or the
scratch keeps its value. -/
theorem pt_keep {M M' : Word → BitVec 8} (C : NtCtx M0 R) {k N a : Nat} {src : Word}
    (f : ∀ x, Sep (R + BitVec.ofNat 32 0x260) 16 x 1 → M' x = copyBytes M (R + BitVec.ofNat 32 k) src N x)
    (h1 : 0x270 ≤ a) (h2 : a + 160 ≤ 0xA10) (h3 : k + N ≤ a ∨ a + 160 ≤ k) (h4 : k + N ≤ 0xA10) :
    ptAt M' (R + BitVec.ofNat 32 a) = ptAt M (R + BitVec.ofNat 32 a) :=
  ptAt_frame fun j hj => by
    rw [spk, f _ (C.offs (Or.inl (by omega)) (by decide) (by omega)),
      copyBytes_sep (C.offs (by omega) h4 (by omega)) (Nat.le_refl _)]

/-- After a frame `memcpy` of 160 bytes from `R + s`, the copy holds the
source point. -/
theorem pt_copied {M M' : Word → BitVec 8} (C : NtCtx M0 R) {k s : Nat}
    (f : ∀ x, Sep (R + BitVec.ofNat 32 0x260) 16 x 1 → M' x = copyBytes M (R + BitVec.ofNat 32 k) (R + BitVec.ofNat 32 s) 0xA0 x)
    (h1 : 0x270 ≤ k) (h2 : k + 160 ≤ 0xA10) :
    ptAt M' (R + BitVec.ofNat 32 k) = ptAt M (R + BitVec.ofNat 32 s) := by
  have e := ptAt_copy (M := M) (d := R + BitVec.ofNat 32 k) (s := R + BitVec.ofNat 32 s) (N := 0xA0) (c := 0)
    (by decide) (by decide)
  rw [add_ofNat_zero, add_ofNat_zero] at e
  rw [← e]
  exact ptAt_frame fun j hj => by rw [spk, f _ (C.offs (Or.inl (by omega)) (by decide) (by omega))]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The loop at 0x2E that fills the table with copies of the Niels form of
`A`; only entry 0 survives the second loop. -/
theorem nt_loop1 (C : NtCtx M0 R) {N : Pt} :
    ∀ t, ∀ {j : Nat} {M : Word → BitVec 8} {n : Machine}, j + t = 8 → 0 < t → NtSt M0 Ms R out A r0 M n 0x2E →
      reg n (8 : Fin 32) = R + BitVec.ofNat 32 (0x45C + 160 * j) → reg n (9 : Fin 32) = BitVec.ofNat 32 t →
      ptAt M (R + BitVec.ofNat 32 0x95C) = N → (0 < j → ptAt M (R + BitVec.ofNat 32 0x45C) = N) →
      ∃ n', Steps n n' ∧ NtSt M0 Ms R out A r0 n'.mem n' 0x48 ∧ ptAt n'.mem (R + BitVec.ofNat 32 0x45C) = N ∧
        ptAt n'.mem (R + BitVec.ofNat 32 0x95C) = N
  | 0, _, _, _, _, h, _, _, _, _, _ => absurd h (by decide)
  | t + 1, j, M, n, hjt, _, D, hs0, hs1, hN, h0 => by
    have hc : CodeIn M NTF nafTableFromCode := D.code C C.E.cod (by decide) (by decide)
    obtain ⟨n1, d1, u1⟩ := D.st.aluImm hc nt_at_2e (off' := 0x32) (by decide)
    have D1 := D.step u1 (by decide)
    obtain ⟨n2, d2, u2⟩ := D1.st.aluImm hc nt_at_32 (off' := 0x36) (by decide)
    have D2 := D1.step u2 (by decide)
    obtain ⟨n3, d3, u3⟩ := D2.st.alu hc nt_at_36 (off' := 0x38) (by decide)
    have D3 := D2.step u3 (by decide)
    have r3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n3 q = reg n q := fun q h0 h1 h2 => by
      rw [u3.upd_ne D2.st.zero q h0, u2.upd_ne D1.st.zero q h2, u1.upd_ne D.st.zero q h1]
    obtain ⟨n4, c4, D4, f4, k4⟩ := D3.mc C nt_at_38 nt_at_3c (by decide) (by decide) (k := 0x45C + 160 * j)
      (src := R + BitVec.ofNat 32 0x95C) (N := 0xA0) (by omega) (by omega)
      (by rw [u3.upd_eq (by decide), D2.st.zero, u2.upd_ne D1.st.zero _ (by decide), u1.upd_ne D.st.zero _ (by decide), hs0]
          exact BitVec.zero_add _)
      (by rw [u3.upd_ne D2.st.zero _ (by decide), u2.upd_ne D1.st.zero _ (by decide), u1.upd_eq (by decide), D.hsp]
          exact add_sp R rfl)
      (by rw [u3.upd_ne D2.st.zero _ (by decide), u2.upd_eq (by decide), D1.st.zero]; rfl)
      (C.offs (Or.inr (by decide)) (by decide) (by decide)) (C.offs (Or.inl (by omega)) (by omega) (by decide))
      (by rw [C.toNat_off (by decide)]; have := C.hRw; omega)
    have hc4 : CodeIn n4.mem NTF nafTableFromCode := D4.code C C.E.cod (by decide) (by decide)
    obtain ⟨n5, d5, u5⟩ := D4.st.aluImm hc4 nt_at_40 (off' := 0x44) (by decide)
    have D5 := D4.step u5 (by decide)
    obtain ⟨n6, d6, u6⟩ := D5.st.aluImm hc4 nt_at_44 (off' := 0x46) (by decide)
    have D6 := D5.step u6 (by decide)
    have s0_6 : reg n6 (8 : Fin 32) = R + BitVec.ofNat 32 (0x45C + 160 * (j + 1)) := by
      rw [u6.upd_ne D5.st.zero _ (by decide), u5.upd_eq (by decide), k4 _ (by decide),
        r3 _ (by decide) (by decide) (by decide), hs0]
      exact add_sp R (b := 160) (by omega)
    have s1_6 : reg n6 (9 : Fin 32) = BitVec.ofNat 32 t := by
      rw [u6.upd_eq (by decide), u5.upd_ne D4.st.zero _ (by decide), k4 _ (by decide),
        r3 _ (by decide) (by decide) (by decide), hs1]
      exact nt_dec ⟨t, by omega⟩
    have hN' : ptAt n4.mem (R + BitVec.ofNat 32 0x95C) = N := by
      rw [pt_keep C f4 (by decide) (by decide) (Or.inl (by omega)) (by omega), hN]
    have hE : ptAt n4.mem (R + BitVec.ofNat 32 (0x45C + 160 * j)) = N := by
      rw [pt_copied C f4 (by omega) (by omega), hN]
    have h0' : ptAt n4.mem (R + BitVec.ofNat 32 0x45C) = N := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact hE
      · rw [pt_keep C f4 (by decide) (by decide) (Or.inr (by omega)) (by omega), h0 hj]
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · obtain ⟨n7, d7, u7⟩ := D6.st.notTaken hc4 0x48 nt_at_46 (by decide) (by rw [s1_6, D6.st.zero]; decide)
      exact ⟨n7, .cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (.cons d6 (.single d7)))))),
        by rw [u7.mem]; exact D6.jmp' u7, by rw [u7.mem]; exact h0', by rw [u7.mem]; exact hN'⟩
    · obtain ⟨n7, d7, u7⟩ := D6.st.taken hc4 0x2E nt_at_46 (by decide)
        (by rw [s1_6, D6.st.zero]; exact nt_bne ⟨t, by omega⟩ ht)
      obtain ⟨n', c', D', e0, e1⟩ := nt_loop1 C t (j := j + 1) (by omega) ht (D6.jmp' u7)
        (by rw [u7.regs, s0_6]) (by rw [u7.regs, s1_6]) hN' (fun _ => h0')
      exact ⟨n', .cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (.cons d6 (.cons d7 c')))))), D', e0, e1⟩

/-- After a call whose frame is two regions of `from`'s stack, a point apart
from both keeps its value. -/
theorem pt_keep2 {M M' : Word → BitVec 8} (C : NtCtx M0 R) {c1 l1 c2 l2 a : Nat}
    (f : ∀ x, Sep (R + BitVec.ofNat 32 c1) l1 x 1 → Sep (R + BitVec.ofNat 32 c2) l2 x 1 → M' x = M x)
    (h1 : c1 + l1 ≤ a ∨ a + 160 ≤ c1) (h2 : c2 + l2 ≤ a ∨ a + 160 ≤ c2) (h3 : a + 160 ≤ 0xA10)
    (h4 : c1 + l1 ≤ 0xA10) (h5 : c2 + l2 ≤ 0xA10) :
    ptAt M' (R + BitVec.ofNat 32 a) = ptAt M (R + BitVec.ofNat 32 a) :=
  ptAt_frame fun j hj => by
    rw [spk, f _ (C.offs (by omega) h4 (by omega)) (C.offs (by omega) h5 (by omega))]

theorem nt_apnD {M : Word → BitVec 8} (hM : ∀ x, Sep R 0xA10 x 1 → M x = M0 x) (sD : Sep apnD 40 R 0xA10) :
    feW M apnD = feW M0 apnD :=
  feW_frame fun i hi => memLoad32_congr fun q hq => by
    rw [add_ofNat_assoc]; exact hM _ (sD.sub (c := 4 * i + q) (l := 1) (by omega)).symm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The loop at 0x9E: entry `j + 1` is the Niels form of `2A` plus entry
`j`, through `as_extended`. -/
theorem nt_loop2 (C : NtCtx M0 R) {Ap A2 : Pt} (hA2 : A2 = extL (edDoubleSpec Ap.1 Ap.2.1 Ap.2.2.1))
    (sD : Sep apnD 40 R 0xA10) :
    ∀ t, ∀ {j : Nat} {M : Word → BitVec 8} {n : Machine}, j + t = 7 → 0 < t → NtSt M0 Ms R out A r0 M n 0x9E →
      reg n (9 : Fin 32) = R + BitVec.ofNat 32 (0x45C + 160 * j) → reg n (8 : Fin 32) = BitVec.ofNat 32 t →
      ptAt M (R + BitVec.ofNat 32 0x27C) = A2 →
      (∀ i, i ≤ j → ptAt M (R + BitVec.ofNat 32 (0x45C + 160 * i)) = nafTab Ap (feW M0 apnD) i) →
      ∃ n', Steps n n' ∧ NtSt M0 Ms R out A r0 n'.mem n' 0xE0 ∧
        ∀ i, i < 8 → ptAt n'.mem (R + BitVec.ofNat 32 (0x45C + 160 * i)) = nafTab Ap (feW M0 apnD) i
  | 0, _, _, _, _, h, _, _, _, _, _ => absurd h (by decide)
  | t + 1, j, M, n, hjt, _, D, hs1, hs0, hA, hT => by
    have hc : CodeIn M NTF nafTableFromCode := D.code C C.E.cod (by decide) (by decide)
    obtain ⟨n1, d1, u1⟩ := D.st.aluImm hc nt_at_9e (off' := 0xA2) (by decide)
    have D1 := D.step u1 (by decide)
    obtain ⟨n2, d2, u2⟩ := D1.st.aluImm hc nt_at_a2 (off' := 0xA4) (by decide)
    have D2 := D1.step u2 (by decide)
    obtain ⟨n3, d3, u3⟩ := D2.st.alu hc nt_at_a4 (off' := 0xA6) (by decide)
    have D3 := D2.step u3 (by decide)
    have r3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n3 q = reg n q := fun q h0 h1 h2 => by
      rw [u3.upd_ne D2.st.zero q h2, u2.upd_ne D1.st.zero q h1, u1.upd_ne D.st.zero q h0]
    obtain ⟨n4, c4, D4, w4, k4, f4⟩ := D3.ean C nt_at_a6 nt_at_aa (by decide) (by decide) (k := 0x95C) (e := 0x27C)
      (p := 0x45C + 160 * j) (by decide) (by decide) (by omega) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (Or.inr (by decide)) (Or.inr (by omega))
      (by rw [u3.upd_ne D2.st.zero _ (by decide), u2.upd_ne D1.st.zero _ (by decide), u1.upd_eq (by decide), D.hsp]
          exact add_sp R rfl)
      (by rw [u3.upd_ne D2.st.zero _ (by decide), u2.upd_eq (by decide), u1.upd_ne D.st.zero _ (by decide), D.hsp]
          exact add_sp R rfl)
      (by rw [u3.upd_eq (by decide), D2.st.zero, u2.upd_ne D1.st.zero _ (by decide), u1.upd_ne D.st.zero _ (by decide), hs1]
          exact BitVec.zero_add _)
    rw [hA, hT j (Nat.le_refl _)] at w4
    have hc4 : CodeIn n4.mem NTF nafTableFromCode := D4.code C C.E.cod (by decide) (by decide)
    obtain ⟨n5, d5, u5⟩ := D4.st.aluImm hc4 nt_at_ae (off' := 0xB0) (by decide)
    have D5 := D4.step u5 (by decide)
    obtain ⟨n6, d6, u6⟩ := D5.st.aluImm hc4 nt_at_b0 (off' := 0xB4) (by decide)
    have D6 := D5.step u6 (by decide)
    obtain ⟨n7, c7, D7, w7, k7, f7⟩ := D6.ext C nt_at_b4 nt_at_b8 (by decide) (by decide) (k := 0x3BC) (j := 0x95C)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
      (by rw [u6.upd_ne D5.st.zero _ (by decide), u5.upd_eq (by decide), D4.hsp]; exact add_sp R rfl)
      (by rw [u6.upd_eq (by decide), u5.upd_ne D4.st.zero _ (by decide), D4.hsp]; exact add_sp R rfl)
    rw [w4] at w7
    have hc7 : CodeIn n7.mem NTF nafTableFromCode := D7.code C C.E.cod (by decide) (by decide)
    obtain ⟨n8, d8, u8⟩ := D7.st.aluImm hc7 nt_at_bc (off' := 0xBE) (by decide)
    have D8 := D7.step u8 (by decide)
    obtain ⟨n9, d9, u9⟩ := D8.st.aluImm hc7 nt_at_be (off' := 0xC0) (by decide)
    have D9 := D8.step u9 (by decide)
    obtain ⟨n10, c10, D10, w10, k10, f10⟩ := D9.apn C nt_at_c0 nt_at_c4 (by decide) (by decide) (k := 0x31C)
      (ip := R + BitVec.ofNat 32 0x3BC) (by decide) (by decide) (by decide)
      (by rw [u9.upd_ne D8.st.zero _ (by decide), u8.upd_eq (by decide), D7.hsp]; exact add_sp R rfl)
      (by rw [u9.upd_eq (by decide), u8.upd_ne D7.st.zero _ (by decide), D7.hsp]; exact add_sp R rfl)
      (aligned_add C.hR (by decide)) (by rw [C.toNat_off (by decide)]; have := C.hRw; omega)
      (C.offs (Or.inr (by decide)) (by decide) (by decide)) (C.offs (Or.inr (by decide)) (by decide) (by decide)) sD
    rw [w7, nt_apnD D7.agree sD] at w10
    have hc10 : CodeIn n10.mem NTF nafTableFromCode := D10.code C C.E.cod (by decide) (by decide)
    obtain ⟨n11, d11, u11⟩ := D10.st.aluImm hc10 nt_at_c8 (off' := 0xCC) (by decide)
    have D11 := D10.step u11 (by decide)
    obtain ⟨n12, d12, u12⟩ := D11.st.aluImm hc10 nt_at_cc (off' := 0xCE) (by decide)
    have D12 := D11.step u12 (by decide)
    obtain ⟨n13, d13, u13⟩ := D12.st.aluImm hc10 nt_at_ce (off' := 0xD2) (by decide)
    have D13 := D12.step u13 (by decide)
    obtain ⟨n14, d14, u14⟩ := D13.st.alu hc10 nt_at_d2 (off' := 0xD4) (by decide)
    have D14 := D13.step u14 (by decide)
    have s1_11 : reg n11 (9 : Fin 32) = R + BitVec.ofNat 32 (0x45C + 160 * (j + 1)) := by
      rw [u11.upd_eq (by decide), k10 _ (by decide), u9.upd_ne D8.st.zero _ (by decide), u8.upd_ne D7.st.zero _ (by decide),
        k7 _ (by decide), u6.upd_ne D5.st.zero _ (by decide), u5.upd_ne D4.st.zero _ (by decide), k4 _ (by decide),
        r3 _ (by decide) (by decide) (by decide), hs1]
      exact add_sp R (b := 160) (by omega)
    obtain ⟨n15, c15, D15, f15, k15⟩ := D14.mc C nt_at_d4 nt_at_d8 (by decide) (by decide) (k := 0x45C + 160 * (j + 1))
      (src := R + BitVec.ofNat 32 0x31C) (N := 0xA0) (by omega) (by omega)
      (by rw [u14.upd_eq (by decide), D13.st.zero, u13.upd_ne D12.st.zero _ (by decide), u12.upd_ne D11.st.zero _ (by decide),
          s1_11]; exact BitVec.zero_add _)
      (by rw [u14.upd_ne D13.st.zero _ (by decide), u13.upd_ne D12.st.zero _ (by decide), u12.upd_eq (by decide),
          u11.upd_ne D10.st.zero _ (by decide), D10.hsp]; exact add_sp R rfl)
      (by rw [u14.upd_ne D13.st.zero _ (by decide), u13.upd_eq (by decide), D12.st.zero]; rfl)
      (C.offs (Or.inr (by decide)) (by decide) (by decide)) (C.offs (Or.inr (by omega)) (by omega) (by decide))
      (by rw [C.toNat_off (by decide)]; have := C.hRw; omega)
    have hc15 : CodeIn n15.mem NTF nafTableFromCode := D15.code C C.E.cod (by decide) (by decide)
    obtain ⟨n16, d16, u16⟩ := D15.st.aluImm hc15 nt_at_dc (off' := 0xDE) (by decide)
    have D16 := D15.step u16 (by decide)
    have s0_16 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 t := by
      rw [u16.upd_eq (by decide), k15 _ (by decide), u14.upd_ne D13.st.zero _ (by decide),
        u13.upd_ne D12.st.zero _ (by decide), u12.upd_ne D11.st.zero _ (by decide), u11.upd_ne D10.st.zero _ (by decide),
        k10 _ (by decide), u9.upd_ne D8.st.zero _ (by decide), u8.upd_ne D7.st.zero _ (by decide), k7 _ (by decide),
        u6.upd_ne D5.st.zero _ (by decide), u5.upd_ne D4.st.zero _ (by decide), k4 _ (by decide),
        r3 _ (by decide) (by decide) (by decide), hs0]
      exact nt_dec ⟨t, by omega⟩
    have s1_16 : reg n16 (9 : Fin 32) = R + BitVec.ofNat 32 (0x45C + 160 * (j + 1)) := by
      rw [u16.upd_ne D15.st.zero _ (by decide), k15 _ (by decide), u14.upd_ne D13.st.zero _ (by decide),
        u13.upd_ne D12.st.zero _ (by decide), u12.upd_ne D11.st.zero _ (by decide), s1_11]
    -- the points the loop keeps
    have keepA : ptAt n15.mem (R + BitVec.ofNat 32 0x27C) = A2 := by
      rw [pt_keep C f15 (by decide) (by decide) (Or.inr (by omega)) (by omega),
        pt_keep2 C f10 (Or.inl (by decide)) (Or.inr (by decide)) (by decide) (by decide) (by decide),
        pt_keep2 C f7 (Or.inl (by decide)) (Or.inr (by decide)) (by decide) (by decide) (by decide),
        pt_keep2 C (c1 := 0) (fun x h1 h2 => f4 x (by rwa [add_ofNat_zero] at h1) h2) (Or.inl (by decide))
          (Or.inr (by decide)) (by decide) (by decide) (by decide), hA]
    have keepT : ∀ i, i ≤ j → ptAt n15.mem (R + BitVec.ofNat 32 (0x45C + 160 * i)) = nafTab Ap (feW M0 apnD) i :=
      fun i hi => by
        rw [pt_keep C f15 (by omega) (by omega) (Or.inr (by omega)) (by omega),
          pt_keep2 C f10 (Or.inl (by omega)) (Or.inl (by omega)) (by omega) (by decide) (by decide),
          pt_keep2 C f7 (Or.inl (by omega)) (Or.inl (by omega)) (by omega) (by decide) (by decide),
          pt_keep2 C (c1 := 0) (fun x h1 h2 => f4 x (by rwa [add_ofNat_zero] at h1) h2) (Or.inl (by omega))
            (Or.inr (by omega)) (by omega) (by decide) (by decide), hT i hi]
    have newT : ptAt n15.mem (R + BitVec.ofNat 32 (0x45C + 160 * (j + 1))) = nafTab Ap (feW M0 apnD) (j + 1) := by
      rw [pt_copied C f15 (by omega) (by omega), w10, hA2]; rfl
    have hT' : ∀ i, i ≤ j + 1 → ptAt n15.mem (R + BitVec.ofNat 32 (0x45C + 160 * i)) = nafTab Ap (feW M0 apnD) i :=
      fun i hi => by
        rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact keepT i (by omega)
        · rw [show i = j + 1 by omega]; exact newT
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · obtain ⟨n17, d17, u17⟩ := D16.st.notTaken hc15 0xE0 nt_at_de (by decide) (by rw [s0_16, D16.st.zero]; decide)
      refine ⟨n17, .cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (.cons d6 (c7.trans (.cons d8 (.cons d9 (c10.trans (.cons d11 (.cons d12 (.cons d13 (.cons d14 (c15.trans (.cons d16 (.single d17)))))))))))))))),
        by rw [u17.mem]; exact D16.jmp' u17, fun i hi => by rw [u17.mem]; exact hT' i (by omega)⟩
    · obtain ⟨n17, d17, u17⟩ := D16.st.taken hc15 0x9E nt_at_de (by decide)
        (by rw [s0_16, D16.st.zero]; exact nt_bne ⟨t, by omega⟩ ht)
      obtain ⟨n', c', D', e⟩ := nt_loop2 C hA2 sD t (j := j + 1) (by omega) ht (D16.jmp' u17)
        (by rw [u17.regs, s1_16]) (by rw [u17.regs, s0_16]) keepA hT'
      exact ⟨n', .cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (.cons d6 (c7.trans (.cons d8 (.cons d9 (c10.trans (.cons d11 (.cons d12 (.cons d13 (.cons d14 (c15.trans (.cons d16 (.cons d17 c')))))))))))))))), D', e⟩

end Loops

end C3.RV32
