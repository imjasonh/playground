import C3BootProofs.Proofs.FeCall
import C3BootProofs.Proofs.FePow2k
import C3BootProofs.Proofs.EdNiels
import C3BootProofs.Proofs.AsProjNiels
import C3BootProofs.Proofs.EcdsaSig

/-!
# `FieldElement2625::pow22501`, as compiled

`pow22501` raises a field element to `2^250 - 1` through a fixed chain of
`square`, `pow2k`, and `mul` calls, and also returns `x^11`, the chain's
fourth value. Its 21 calls each go through a call lemma below.
-/

namespace C3.RV32

open C3.Image

/-- The limbs `square` stores for operand limbs `x`. -/
def feSqW (x : Nat → Word) : Nat → Word := fun i =>
  BitVec.ofNat 32 ((feSquareSpec (x 0).toNat (x 1).toNat (x 2).toNat (x 3).toNat (x 4).toNat (x 5).toNat
    (x 6).toNat (x 7).toNat (x 8).toNat (x 9).toNat).getD i 0)

/-- The limbs `pow2k` stores for operand limbs `x`. -/
def pow2kW (k : Nat) (x : Nat → Word) : Nat → Word := fun i =>
  BitVec.ofNat 32 ((sqIter k [(x 0).toNat, (x 1).toNat, (x 2).toNat, (x 3).toNat, (x 4).toNat, (x 5).toNat,
    (x 6).toNat, (x 7).toNat, (x 8).toNat, (x 9).toNat]).getD i 0)

theorem limbs_of_feW {M : Word → BitVec 8} {a : Word} {L : List Nat} (h : feW M a = L) :
    ∀ i, i < 10 → limbs M a i = BitVec.ofNat 32 (L.getD i 0) := by
  intro i hi
  rw [← h]
  have e : ∀ j, j < 10 → (feW M a).getD j 0 = (limbs M a j).toNat := fun j hj => by
    match j, hj with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl
    | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl
  rw [e i hi]; exact (ofNat_toNat_self _).symm

theorem feSqW_congr {x x' : Nat → Word} (hx : ∀ i, i < 10 → x i = x' i) : feSqW x = feSqW x' := by
  funext i
  unfold feSqW
  rw [hx 0 (by decide), hx 1 (by decide), hx 2 (by decide), hx 3 (by decide), hx 4 (by decide), hx 5 (by decide),
    hx 6 (by decide), hx 7 (by decide), hx 8 (by decide), hx 9 (by decide)]

theorem pow2kW_congr {k : Nat} {x x' : Nat → Word} (hx : ∀ i, i < 10 → x i = x' i) : pow2kW k x = pow2kW k x' := by
  funext i
  unfold pow2kW
  rw [hx 0 (by decide), hx 1 (by decide), hx 2 (by decide), hx 3 (by decide), hx 4 (by decide), hx 5 (by decide),
    hx 6 (by decide), hx 7 (by decide), hx 8 (by decide), hx 9 (by decide)]

theorem St.callFeSquare {M : Word → BitVec 8} {P : Word} {code : List Nat} {nm : Machine} {off : Nat}
    (s : St M P nm off (reg nm)) (hc : CodeIn M P code) {imm o cb : Word}
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = cb) (hev : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (env : FeSquareEnv M cb (reg nm sp) (reg nm a0) (reg nm a1)) :
    ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = reg nm sp ∧
      (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
      (∀ i, i < 10 → limbs nm'.mem (reg nm a0) i = feSqW (limbs M (reg nm a1)) i) ∧
      ∀ x, Sep (reg nm sp + 0xFFFFFF50) 0xB0 x 1 → Sep (reg nm a0) 40 x 1 → nm'.mem x = M x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb env.hP
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feSquare_correct n1 (by rw [mem1]; exact env) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev) (r1 sp (by decide))
  rw [mem1] at w2 f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hk hr => by rw [k2 q hk, r1 q hr], fun i hi => ?_, f2⟩
  rw [limbs_of_wordsAt w2 i hi]; rfl

theorem St.callFePow2k {M : Word → BitVec 8} {P : Word} {code : List Nat} {nm : Machine} {off : Nat} {k : Nat}
    (s : St M P nm off (reg nm)) (hc : CodeIn M P code) {imm o cb G : Word}
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = cb) (hev : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hk0 : 0 < k) (hk1 : k < 2 ^ 32) (hka : reg nm a2 = BitVec.ofNat 32 k)
    (hsp : reg nm sp = G + 0x110) (env : FpkEnv M cb G (reg nm a0) (reg nm a1)) :
    ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = reg nm sp ∧
      (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
      (∀ i, i < 10 → limbs nm'.mem (reg nm a0) i = pow2kW k (limbs M (reg nm a1)) i) ∧
      ∀ x, Sep G 0x110 x 1 → Sep (reg nm a0) 40 x 1 → nm'.mem x = M x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb env.hP
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := fePow2k_correct n1 (by rw [mem1]; exact env) hk0 hk1 pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (by rw [r1 a2 (by decide), hka]) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev) (by rw [r1 sp (by decide), hsp])
  rw [mem1] at w2 f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, hsp],
    fun q hk hr => by rw [k2 q hk, r1 q hr], fun i hi => ?_, f2⟩
  rw [limbs_of_feW w2 i hi]; rfl

abbrev pwPs : List (Fin 32 × Word) := [(ra, 0xC), ((8 : Fin 32), 0x8), ((9 : Fin 32), 0x4)]

section
set_option maxRecDepth 20000
theorem pw_at_0 : fetchRel pow22501Code 0x0 = some (.aluImm .add sp sp 0xFFFFFCF0, 4) := by decide
theorem pw_at_4 : fetchRel pow22501Code 0x4 = some (.aluImm .add a2 sp 0x300, 2) := by decide
theorem pw_at_6 : fetchRel pow22501Code 0x6 = some (.store .sw a2 ra 0xC, 4) := by decide
theorem pw_at_a : fetchRel pow22501Code 0xA = some (.store .sw a2 (8 : Fin 32) 0x8, 2) := by decide
theorem pw_at_c : fetchRel pow22501Code 0xC = some (.store .sw a2 (9 : Fin 32) 0x4, 2) := by decide
theorem pw_at_e : fetchRel pow22501Code 0xE = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem pw_at_10 : fetchRel pow22501Code 0x10 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem pw_at_12 : fetchRel pow22501Code 0x12 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem pw_at_14 : fetchRel pow22501Code 0x14 = some (.auipc ra 0x0, 4) := by decide
theorem pw_at_18 : fetchRel pow22501Code 0x18 = some (.jalr ra ra 0x194, 4) := by decide
theorem pw_at_1c : fetchRel pow22501Code 0x1C = some (.aluImm .add a0 sp 0x2DC, 2) := by decide
theorem pw_at_1e : fetchRel pow22501Code 0x1E = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem pw_at_20 : fetchRel pow22501Code 0x20 = some (.auipc ra 0x0, 4) := by decide
theorem pw_at_24 : fetchRel pow22501Code 0x24 = some (.jalr ra ra 0x188, 4) := by decide
theorem pw_at_28 : fetchRel pow22501Code 0x28 = some (.aluImm .add a0 sp 0x34, 2) := by decide
theorem pw_at_2a : fetchRel pow22501Code 0x2A = some (.aluImm .add a1 sp 0x2DC, 2) := by decide
theorem pw_at_2c : fetchRel pow22501Code 0x2C = some (.auipc ra 0x0, 4) := by decide
theorem pw_at_30 : fetchRel pow22501Code 0x30 = some (.jalr ra ra 0x17C, 4) := by decide
theorem pw_at_34 : fetchRel pow22501Code 0x34 = some (.aluImm .add a0 sp 0x5C, 2) := by decide
theorem pw_at_36 : fetchRel pow22501Code 0x36 = some (.aluImm .add a2 sp 0x34, 2) := by decide
theorem pw_at_38 : fetchRel pow22501Code 0x38 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem pw_at_3a : fetchRel pow22501Code 0x3A = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pw_at_3e : fetchRel pow22501Code 0x3E = some (.jalr ra ra 0x30A, 4) := by decide
theorem pw_at_42 : fetchRel pow22501Code 0x42 = some (.aluImm .add a0 sp 0x84, 2) := by decide
theorem pw_at_44 : fetchRel pow22501Code 0x44 = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem pw_at_46 : fetchRel pow22501Code 0x46 = some (.aluImm .add a2 sp 0x5C, 2) := by decide
theorem pw_at_48 : fetchRel pow22501Code 0x48 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pw_at_4c : fetchRel pow22501Code 0x4C = some (.jalr ra ra 0x2FC, 4) := by decide
theorem pw_at_50 : fetchRel pow22501Code 0x50 = some (.aluImm .add a0 sp 0xAC, 2) := by decide
theorem pw_at_52 : fetchRel pow22501Code 0x52 = some (.aluImm .add a1 sp 0x84, 2) := by decide
theorem pw_at_54 : fetchRel pow22501Code 0x54 = some (.auipc ra 0x0, 4) := by decide
theorem pw_at_58 : fetchRel pow22501Code 0x58 = some (.jalr ra ra 0x154, 4) := by decide
theorem pw_at_5c : fetchRel pow22501Code 0x5C = some (.aluImm .add a0 sp 0xD4, 2) := by decide
theorem pw_at_5e : fetchRel pow22501Code 0x5E = some (.aluImm .add a1 sp 0x5C, 2) := by decide
theorem pw_at_60 : fetchRel pow22501Code 0x60 = some (.aluImm .add a2 sp 0xAC, 2) := by decide
theorem pw_at_62 : fetchRel pow22501Code 0x62 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pw_at_66 : fetchRel pow22501Code 0x66 = some (.jalr ra ra 0x2E2, 4) := by decide
theorem pw_at_6a : fetchRel pow22501Code 0x6A = some (.aluImm .add a0 sp 0xFC, 2) := by decide
theorem pw_at_6c : fetchRel pow22501Code 0x6C = some (.aluImm .add a1 sp 0xD4, 2) := by decide
theorem pw_at_6e : fetchRel pow22501Code 0x6E = some (.aluImm .add a2 x0 0x5, 2) := by decide
theorem pw_at_70 : fetchRel pow22501Code 0x70 = some (.auipc ra 0x0, 4) := by decide
theorem pw_at_74 : fetchRel pow22501Code 0x74 = some (.jalr ra ra 0xE6, 4) := by decide
theorem pw_at_78 : fetchRel pow22501Code 0x78 = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem pw_at_7a : fetchRel pow22501Code 0x7A = some (.aluImm .add a1 sp 0xFC, 2) := by decide
theorem pw_at_7c : fetchRel pow22501Code 0x7C = some (.aluImm .add a2 sp 0xD4, 2) := by decide
theorem pw_at_7e : fetchRel pow22501Code 0x7E = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pw_at_82 : fetchRel pow22501Code 0x82 = some (.jalr ra ra 0x2C6, 4) := by decide
theorem pw_at_86 : fetchRel pow22501Code 0x86 = some (.aluImm .add a0 sp 0x14C, 2) := by decide
theorem pw_at_88 : fetchRel pow22501Code 0x88 = some (.aluImm .add a1 sp 0x124, 2) := by decide
theorem pw_at_8a : fetchRel pow22501Code 0x8A = some (.aluImm .add a2 x0 0xA, 2) := by decide
theorem pw_at_8c : fetchRel pow22501Code 0x8C = some (.auipc ra 0x0, 4) := by decide
theorem pw_at_90 : fetchRel pow22501Code 0x90 = some (.jalr ra ra 0xCA, 4) := by decide
theorem pw_at_94 : fetchRel pow22501Code 0x94 = some (.aluImm .add a0 sp 0x174, 2) := by decide
theorem pw_at_96 : fetchRel pow22501Code 0x96 = some (.aluImm .add a1 sp 0x14C, 2) := by decide
theorem pw_at_98 : fetchRel pow22501Code 0x98 = some (.aluImm .add a2 sp 0x124, 2) := by decide
theorem pw_at_9a : fetchRel pow22501Code 0x9A = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pw_at_9e : fetchRel pow22501Code 0x9E = some (.jalr ra ra 0x2AA, 4) := by decide
theorem pw_at_a2 : fetchRel pow22501Code 0xA2 = some (.aluImm .add a0 sp 0x19C, 2) := by decide
theorem pw_at_a4 : fetchRel pow22501Code 0xA4 = some (.aluImm .add a1 sp 0x174, 2) := by decide
theorem pw_at_a6 : fetchRel pow22501Code 0xA6 = some (.aluImm .add a2 x0 0x14, 2) := by decide
theorem pw_at_a8 : fetchRel pow22501Code 0xA8 = some (.auipc ra 0x0, 4) := by decide
theorem pw_at_ac : fetchRel pow22501Code 0xAC = some (.jalr ra ra 0xAE, 4) := by decide
theorem pw_at_b0 : fetchRel pow22501Code 0xB0 = some (.aluImm .add a0 sp 0x1C4, 2) := by decide
theorem pw_at_b2 : fetchRel pow22501Code 0xB2 = some (.aluImm .add a1 sp 0x19C, 2) := by decide
theorem pw_at_b4 : fetchRel pow22501Code 0xB4 = some (.aluImm .add a2 sp 0x174, 2) := by decide
theorem pw_at_b6 : fetchRel pow22501Code 0xB6 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pw_at_ba : fetchRel pow22501Code 0xBA = some (.jalr ra ra 0x28E, 4) := by decide
theorem pw_at_be : fetchRel pow22501Code 0xBE = some (.aluImm .add a0 sp 0x1EC, 2) := by decide
theorem pw_at_c0 : fetchRel pow22501Code 0xC0 = some (.aluImm .add a1 sp 0x1C4, 2) := by decide
theorem pw_at_c2 : fetchRel pow22501Code 0xC2 = some (.aluImm .add a2 x0 0xA, 2) := by decide
theorem pw_at_c4 : fetchRel pow22501Code 0xC4 = some (.auipc ra 0x0, 4) := by decide
theorem pw_at_c8 : fetchRel pow22501Code 0xC8 = some (.jalr ra ra 0x92, 4) := by decide
theorem pw_at_cc : fetchRel pow22501Code 0xCC = some (.aluImm .add a0 sp 0x214, 2) := by decide
theorem pw_at_ce : fetchRel pow22501Code 0xCE = some (.aluImm .add a1 sp 0x1EC, 2) := by decide
theorem pw_at_d0 : fetchRel pow22501Code 0xD0 = some (.aluImm .add a2 sp 0x124, 2) := by decide
theorem pw_at_d2 : fetchRel pow22501Code 0xD2 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pw_at_d6 : fetchRel pow22501Code 0xD6 = some (.jalr ra ra 0x272, 4) := by decide
theorem pw_at_da : fetchRel pow22501Code 0xDA = some (.aluImm .add a0 sp 0x23C, 2) := by decide
theorem pw_at_dc : fetchRel pow22501Code 0xDC = some (.aluImm .add a1 sp 0x214, 2) := by decide
theorem pw_at_de : fetchRel pow22501Code 0xDE = some (.aluImm .add a2 x0 0x32, 4) := by decide
theorem pw_at_e2 : fetchRel pow22501Code 0xE2 = some (.auipc ra 0x0, 4) := by decide
theorem pw_at_e6 : fetchRel pow22501Code 0xE6 = some (.jalr ra ra 0x74, 4) := by decide
theorem pw_at_ea : fetchRel pow22501Code 0xEA = some (.aluImm .add a0 sp 0x264, 2) := by decide
theorem pw_at_ec : fetchRel pow22501Code 0xEC = some (.aluImm .add a1 sp 0x23C, 2) := by decide
theorem pw_at_ee : fetchRel pow22501Code 0xEE = some (.aluImm .add a2 sp 0x214, 2) := by decide
theorem pw_at_f0 : fetchRel pow22501Code 0xF0 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pw_at_f4 : fetchRel pow22501Code 0xF4 = some (.jalr ra ra 0x254, 4) := by decide
theorem pw_at_f8 : fetchRel pow22501Code 0xF8 = some (.aluImm .add a0 sp 0x28C, 2) := by decide
theorem pw_at_fa : fetchRel pow22501Code 0xFA = some (.aluImm .add a1 sp 0x264, 2) := by decide
theorem pw_at_fc : fetchRel pow22501Code 0xFC = some (.aluImm .add a2 x0 0x64, 4) := by decide
theorem pw_at_100 : fetchRel pow22501Code 0x100 = some (.auipc ra 0x0, 4) := by decide
theorem pw_at_104 : fetchRel pow22501Code 0x104 = some (.jalr ra ra 0x56, 4) := by decide
theorem pw_at_108 : fetchRel pow22501Code 0x108 = some (.aluImm .add a0 sp 0x2B4, 2) := by decide
theorem pw_at_10a : fetchRel pow22501Code 0x10A = some (.aluImm .add a1 sp 0x28C, 2) := by decide
theorem pw_at_10c : fetchRel pow22501Code 0x10C = some (.aluImm .add a2 sp 0x264, 2) := by decide
theorem pw_at_10e : fetchRel pow22501Code 0x10E = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pw_at_112 : fetchRel pow22501Code 0x112 = some (.jalr ra ra 0x236, 4) := by decide
theorem pw_at_116 : fetchRel pow22501Code 0x116 = some (.aluImm .add a0 sp 0x2DC, 2) := by decide
theorem pw_at_118 : fetchRel pow22501Code 0x118 = some (.aluImm .add a1 sp 0x2B4, 2) := by decide
theorem pw_at_11a : fetchRel pow22501Code 0x11A = some (.aluImm .add a2 x0 0x32, 4) := by decide
theorem pw_at_11e : fetchRel pow22501Code 0x11E = some (.auipc ra 0x0, 4) := by decide
theorem pw_at_122 : fetchRel pow22501Code 0x122 = some (.jalr ra ra 0x38, 4) := by decide
theorem pw_at_126 : fetchRel pow22501Code 0x126 = some (.aluImm .add a1 sp 0x2DC, 2) := by decide
theorem pw_at_128 : fetchRel pow22501Code 0x128 = some (.aluImm .add a2 sp 0x214, 2) := by decide
theorem pw_at_12a : fetchRel pow22501Code 0x12A = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem pw_at_12c : fetchRel pow22501Code 0x12C = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pw_at_130 : fetchRel pow22501Code 0x130 = some (.jalr ra ra 0x218, 4) := by decide
theorem pw_at_134 : fetchRel pow22501Code 0x134 = some (.aluImm .add a0 (8 : Fin 32) 0x28, 4) := by decide
theorem pw_at_138 : fetchRel pow22501Code 0x138 = some (.aluImm .add a1 sp 0x84, 2) := by decide
theorem pw_at_13a : fetchRel pow22501Code 0x13A = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem pw_at_13e : fetchRel pow22501Code 0x13E = some (.auipc ra 0x6000, 4) := by decide
theorem pw_at_142 : fetchRel pow22501Code 0x142 = some (.jalr ra ra 0x302, 4) := by decide
theorem pw_at_146 : fetchRel pow22501Code 0x146 = some (.aluImm .add a0 sp 0x300, 2) := by decide
theorem pw_at_148 : fetchRel pow22501Code 0x148 = some (.load .lw ra a0 0xC, 4) := by decide
theorem pw_at_14c : fetchRel pow22501Code 0x14C = some (.load .lw (8 : Fin 32) a0 0x8, 2) := by decide
theorem pw_at_14e : fetchRel pow22501Code 0x14E = some (.load .lw (9 : Fin 32) a0 0x4, 2) := by decide
theorem pw_at_150 : fetchRel pow22501Code 0x150 = some (.aluImm .add sp sp 0x310, 4) := by decide
theorem pw_at_154 : fetchRel pow22501Code 0x154 = some (.jalr x0 ra 0x0, 2) := by decide
theorem pwSave_end : blockEnd pow22501Code 6 (saveBlockR a2 pwPs) = some 0xE := by decide
theorem pwRestore_end : blockEnd pow22501Code 0x148 (restoreBlockR a0 pwPs) = some 0x150 := by decide
end

/-- `b` and the `n` bytes after it are apart from `pow22501`'s code and every
function it calls, at each address its calls reach them by. -/
structure PwCode (P b : Word) (n : Nat) : Prop where
  c : Sep b n P pow22501Code.length
  sq : Sep b n (P + 0x1A8) feSquareCode.length
  sqi : Sep b n (P + 0x1A8 + 0x26) feSquareInnerCode.length
  sqR : Sep b n (P + 0x1A8 + 0xFFFFFC8C) feReduceCode.length
  m : Sep b n (P + 0xFFFFF344) feMulCode.length
  mR : Sep b n (P + 0xFFFFF344 + 0xAF0) feReduceCode.length
  pk : Sep b n (P + 0x156) fePow2kCode.length
  pkS : Sep b n (P + 0x156 + 0x52) feSquareCode.length
  pkI : Sep b n (P + 0x156 + 0x78) feSquareInnerCode.length
  pkR : Sep b n (P + 0x156 + 0xFFFFFCDE) feReduceCode.length
  pkMS : Sep b n (P + 0x156 + 0x62EA) memcpyStubCode.length
  pkMB : Sep b n (P + 0x156 + 0x62F2) memcpyBodyCode.length
  mcS : Sep b n (P + 0x6440) memcpyStubCode.length
  mcB : Sep b n (P + 0x6440 + 8) memcpyBodyCode.length

theorem PwCode.sub {P b : Word} {n : Nat} (h : PwCode P b n) {c l : Nat} (hl : c + l ≤ n) :
    PwCode P (b + BitVec.ofNat 32 c) l :=
  ⟨h.c.sub hl, h.sq.sub hl, h.sqi.sub hl, h.sqR.sub hl, h.m.sub hl, h.mR.sub hl, h.pk.sub hl, h.pkS.sub hl,
    h.pkI.sub hl, h.pkR.sub hl, h.pkMS.sub hl, h.pkMB.sub hl, h.mcS.sub hl, h.mcB.sub hl⟩

/-- Where `pow22501` runs: its code and its callees', the 0x450 bytes of
stack below `sp0`, the operand at `xp`, and the result pair's 0x50 bytes at
`out`, apart from what each must not touch. -/
structure PWEnv (M : Word → BitVec 8) (P sp0 out xp : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P pow22501Code
  sq : CodeIn M (P + 0x1A8) feSquareCode
  sqi : CodeIn M (P + 0x1A8 + 0x26) feSquareInnerCode
  sqR : CodeIn M (P + 0x1A8 + 0xFFFFFC8C) feReduceCode
  mul : CodeIn M (P + 0xFFFFF344) feMulCode
  mulR : CodeIn M (P + 0xFFFFF344 + 0xAF0) feReduceCode
  pk : CodeIn M (P + 0x156) fePow2kCode
  pkS : CodeIn M (P + 0x156 + 0x52) feSquareCode
  pkI : CodeIn M (P + 0x156 + 0x78) feSquareInnerCode
  pkR : CodeIn M (P + 0x156 + 0xFFFFFCDE) feReduceCode
  pkMS : CodeIn M (P + 0x156 + 0x62EA) memcpyStubCode
  pkMB : CodeIn M (P + 0x156 + 0x62F2) memcpyBodyCode
  mcS : CodeIn M (P + 0x6440) memcpyStubCode
  mcB : CodeIn M (P + 0x6440 + 8) memcpyBodyCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x450 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hxp : xp.toNat % 4 = 0
  how : out.toNat + 0x50 < 2 ^ 32
  sG : PwCode P (sp0 + 0xFFFFFBB0) 0x450
  sO : PwCode P out 0x50
  sOG : Sep out 0x50 (sp0 + 0xFFFFFBB0) 0x450
  sXG : Sep xp 40 (sp0 + 0xFFFFFBB0) 0x450
  sXO : Sep xp 40 out 0x50

/-- The registers `pow22501` keeps across its calls: `sp` at its frame, the
result and operand pointers in `s0` and `s1`, and the rest as the caller
left them. -/
def PwRegs (m nm : Machine) (F out xp : Word) : Prop :=
  reg nm sp = F ∧ reg nm 8 = out ∧ reg nm 9 = xp ∧
    ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nm q = reg m q

theorem PwRegs.tr {m nm nm' : Machine} {F out xp : Word} (h : PwRegs m nm F out xp)
    (k : ∀ q, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nm' q = reg nm q) :
    PwRegs m nm' F out xp :=
  ⟨by rw [k sp (by decide)]; exact h.1, by rw [k 8 (by decide)]; exact h.2.1, by rw [k 9 (by decide)]; exact h.2.2.1,
    fun q hq => by rw [k q (by revert hq; revert q; decide)]; exact h.2.2.2 q hq⟩

/-! The chain, named after the Rust source's `t0` through `t19`. -/

def pwT0 (x : Nat → Word) : Nat → Word := feSqW x
def pwT0s (x : Nat → Word) : Nat → Word := feSqW (pwT0 x)
def pwT1 (x : Nat → Word) : Nat → Word := feSqW (pwT0s x)
def pwT2 (x : Nat → Word) : Nat → Word := feMulW x (pwT1 x)
def pwT3 (x : Nat → Word) : Nat → Word := feMulW (pwT0 x) (pwT2 x)
def pwT4 (x : Nat → Word) : Nat → Word := feSqW (pwT3 x)
def pwT5 (x : Nat → Word) : Nat → Word := feMulW (pwT2 x) (pwT4 x)
def pwT6 (x : Nat → Word) : Nat → Word := pow2kW 5 (pwT5 x)
def pwT7 (x : Nat → Word) : Nat → Word := feMulW (pwT6 x) (pwT5 x)
def pwT8 (x : Nat → Word) : Nat → Word := pow2kW 10 (pwT7 x)
def pwT9 (x : Nat → Word) : Nat → Word := feMulW (pwT8 x) (pwT7 x)
def pwT10 (x : Nat → Word) : Nat → Word := pow2kW 20 (pwT9 x)
def pwT11 (x : Nat → Word) : Nat → Word := feMulW (pwT10 x) (pwT9 x)
def pwT12 (x : Nat → Word) : Nat → Word := pow2kW 10 (pwT11 x)
def pwT13 (x : Nat → Word) : Nat → Word := feMulW (pwT12 x) (pwT7 x)
def pwT14 (x : Nat → Word) : Nat → Word := pow2kW 50 (pwT13 x)
def pwT15 (x : Nat → Word) : Nat → Word := feMulW (pwT14 x) (pwT13 x)
def pwT16 (x : Nat → Word) : Nat → Word := pow2kW 100 (pwT15 x)
def pwT17 (x : Nat → Word) : Nat → Word := feMulW (pwT16 x) (pwT15 x)
def pwT18 (x : Nat → Word) : Nat → Word := pow2kW 50 (pwT17 x)
def pwT19 (x : Nat → Word) : Nat → Word := feMulW (pwT18 x) (pwT13 x)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The compiled `FieldElement2625::pow22501`**: from the operand's limbs at
`xp`, it stores at `out` the limbs of `t19 = x^(2^250 - 1)` and at
`out + 0x28` those of `t3 = x^11`, each as the field operations compute
them. -/
theorem pow22501_correct (m : Machine) {P sp0 out xp retAddr : Word} (env : PWEnv m.mem P sp0 out xp)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ i, i < 10 → limbs m'.mem out i = pwT19 (limbs m.mem xp) i ∧
        limbs m'.mem (out + 0x28) i = pwT3 (limbs m.mem xp) i) ∧
      ∀ x, Sep (sp0 + 0xFFFFFBB0) 0x450 x 1 → Sep out 0x50 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFBB0 = G := ⟨_, rfl⟩
  have sG := env.sG; have sOG := env.sOG; have sXG := env.sXG
  rw [hG] at sG sOG sXG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFCF0 = F := ⟨_, rfl⟩
  have hGF : G + BitVec.ofNat 32 0x140 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFBB0) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hGF]; exact aligned_add hGa (k := 0x140) (by decide)
  have hGw : G.toNat + 0x450 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFBB0 : Word).toNat = 4294966192 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFn : F.toNat = G.toNat + 0x140 := by rw [← hGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have gw : G.toNat + 0x450 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have eS : F + 0x310 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x140 + k) := fun k => by rw [← hGF, add_ofNat_assoc]
  have eFm : F + 0xFFFFFEC0 = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
  have eFs : F + 0xFFFFFF50 = G + BitVec.ofNat 32 0x90 := by rw [← hGF, BitVec.add_assoc]; rfl
  have eFc : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x130 := by rw [← hGF, BitVec.add_assoc]; rfl
  have eA : F + 0x300 = G + BitVec.ofNat 32 0x440 := by rw [← hGF, BitVec.add_assoc]; rfl
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x450 → d + k ≤ 0x450 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have g0 : ∀ {a : Word} {n : Nat}, Sep a n G 0x450 → Sep a n G 0x140 := fun h => by
    have := h.subR (c := 0) (l := 0x140) (by decide); rwa [add_ofNat_zero] at this
  have g0' : ∀ {b : Word} {l : Nat}, Sep G 0x450 b l → Sep G 0x140 b l := fun h => by
    have := h.sub (c := 0) (l := 0x140) (by decide); rwa [add_ofNat_zero] at this
  have zg : ∀ {z : Word}, Sep G 0x450 z 1 → Sep G 0x140 z 1 := fun h => by
    have := h.sub (c := 0) (l := 0x140) (by decide); rwa [add_ofNat_zero] at this
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x450 b code'.length → Sep out 0x50 b code'.length →
      (∀ x, Sep G 0x450 x 1 → Sep out 0x50 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs ho hM i hi => by
      rw [hM _ (hs.subR (c := i) (l := 1) (by omega)) (ho.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have tS : ∀ c, c + 40 ≤ 0x304 → Sep (F + BitVec.ofNat 32 c) 40 G 0x140 := fun c h => by
    rw [eFk]; have := offs (c := 0x140 + c) (n := 40) (d := 0) (k := 0x140) (.inr (by omega)) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have tC : ∀ c, c + 40 ≤ 0x304 → PwCode P (F + BitVec.ofNat 32 c) 40 := fun c h => by
    rw [eFk]; exact sG.sub (by omega)
  have tA : ∀ c, c % 4 = 0 → (F + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h => aligned_add hFa h
  have tW : ∀ c, c + 40 ≤ 0x304 → (F + BitVec.ofNat 32 c).toNat + 40 < 2 ^ 32 := fun c h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := sp0.isLt; omega
  have tIn : ∀ c, c + 40 ≤ 0x304 → ∀ z, Sep G 0x450 z 1 → Sep out 0x50 z 1 → Sep (F + BitVec.ofNat 32 c) 40 z 1 :=
    fun c h z hz _ => by rw [eFk]; exact hz.sub (by omega)
  have tT : ∀ c d, c + 40 ≤ d ∨ d + 40 ≤ c → c + 40 ≤ 0x304 → d + 40 ≤ 0x304 →
      Sep (F + BitVec.ofNat 32 c) 40 (F + BitVec.ofNat 32 d) 40 := fun c d h h1 h2 => by
    rw [eFk, eFk]; exact offs (by omega) (by omega) (by omega)
  have tSl : ∀ c k, c + 40 ≤ 0x304 → 0x444 ≤ k → k < 0x450 → Sep (F + BitVec.ofNat 32 c) 40 (G + BitVec.ofNat 32 k) 1 :=
    fun c k h h1 h2 => by rw [eFk]; exact offs (.inl (by omega)) (by omega) (by omega)
  have tO : ∀ c k, c + 40 ≤ 0x304 → k + 40 ≤ 0x50 → Sep (F + BitVec.ofNat 32 c) 40 (out + BitVec.ofNat 32 k) 40 :=
    fun c k h1 h2 => by rw [eFk]; exact ((sOG.sub (c := k) (l := 40) h2).subR (c := 0x140 + c) (l := 40) (by omega)).symm
  have tO0 : ∀ c, c + 40 ≤ 0x304 → Sep (F + BitVec.ofNat 32 c) 40 out 40 := fun c h => by
    have := tO c 0 h (by decide); rwa [add_ofNat_zero] at this
  have oS : ∀ k, k + 40 ≤ 0x50 → Sep (out + BitVec.ofNat 32 k) 40 G 0x140 := fun k h => g0 (sOG.sub h)
  have oC0 : PwCode P out 40 := by have := env.sO.sub (c := 0) (l := 40) (by decide); rwa [add_ofNat_zero] at this
  have oS0 : Sep out 40 G 0x140 := by have := oS 0 (by decide); rwa [add_ofNat_zero] at this
  have oIn0 : ∀ z, Sep G 0x450 z 1 → Sep out 0x50 z 1 → Sep out 40 z 1 := fun z _ hz => by
    have := hz.sub (c := 0) (l := 40) (by decide); rwa [add_ofNat_zero] at this
  have oSl0 : ∀ j, j < 0x450 → Sep out 40 (G + BitVec.ofNat 32 j) 1 := fun j hj => by
    have := (sOG.sub (c := 0) (l := 40) (by decide)).subR (c := j) (l := 1) (by omega); rwa [add_ofNat_zero] at this
  have xS0 : Sep xp 40 G 0x140 := g0 sXG
  have xpK : ∀ {M : Word → BitVec 8}, (∀ z, Sep G 0x450 z 1 → Sep out 0x50 z 1 → M z = m.mem z) →
      ∀ i, i < 10 → limbs M xp i = limbs m.mem xp i :=
    fun hM i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      exact hM _ (sXG.sub (c := 4 * i + j) (l := 1) (by omega)).symm (env.sXO.sub (c := 4 * i + j) (l := 1) (by omega)).symm
  have pers : ∀ {M M' : Word → BitVec 8} {o a : Word}, (∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → M' z = M z) →
      Sep a 40 G 0x140 → Sep a 40 o 40 → ∀ i, i < 10 → limbs M' a i = limbs M a i :=
    fun hM h1 h2 i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      exact hM _ (h1.sub (c := 4 * i + j) (l := 1) (by omega)).symm (h2.sub (c := 4 * i + j) (l := 1) (by omega)).symm
  have tP : ∀ {M M' : Word → BitVec 8} {o : Word} (c : Nat), (∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → M' z = M z) →
      c + 40 ≤ 0x304 → Sep (F + BitVec.ofNat 32 c) 40 o 40 → ∀ i, i < 10 →
      limbs M' (F + BitVec.ofNat 32 c) i = limbs M (F + BitVec.ofNat 32 c) i :=
    fun c hM hc ho i hi => pers hM (tS c hc) ho i hi
  have gk : ∀ k, 0x140 ≤ k → k < 0x450 → Sep G 0x140 (G + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    have := offs (c := 0) (n := 0x140) (d := k) (k := 1) (.inl (by omega)) (by decide) (by omega)
    rwa [add_ofNat_zero] at this
  have invStep : ∀ {M M' : Word → BitVec 8} {o : Word}, (∀ z, Sep G 0x450 z 1 → Sep out 0x50 z 1 → M z = m.mem z) →
      (∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → M' z = M z) →
      (∀ z, Sep G 0x450 z 1 → Sep out 0x50 z 1 → Sep o 40 z 1) →
      ∀ z, Sep G 0x450 z 1 → Sep out 0x50 z 1 → M' z = m.mem z :=
    fun hI hM ho z h1 h2 => by rw [hM z (zg h1) (ho z h1 h2), hI z h1 h2]
  have mulCall : ∀ {M : Word → BitVec 8} {nm : Machine} {off : Nat} {imm o' : Word} (o x y : Word),
      St M P nm off (reg nm) → CodeIn M P pow22501Code →
      (∀ z, Sep G 0x450 z 1 → Sep out 0x50 z 1 → M z = m.mem z) →
      fetchRel pow22501Code off = some (.auipc ra imm, 4) →
      fetchRel pow22501Code (off + 4) = some (.jalr ra ra o', 4) →
      P + BitVec.ofNat 32 off + imm + o' = P + 0xFFFFF344 → (off + 8) % 2 = 0 →
      reg nm sp = F → reg nm a0 = o → reg nm a1 = x → reg nm a2 = y →
      o.toNat % 4 = 0 → x.toNat % 4 = 0 → y.toNat % 4 = 0 → PwCode P o 40 →
      Sep o 40 G 0x140 → Sep x 40 G 0x140 → Sep y 40 G 0x140 →
      ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = F ∧
        (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
        (∀ i, i < 10 → limbs nm'.mem o i = feMulW (limbs M x) (limbs M y) i) ∧
        ∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → nm'.mem z = M z := by
    intro M nm off imm o' o x y s hc hI h1 h2 hb hev hs e0 e1 e2 hoa hxa hya hoc soG sxG syG
    have e : FeMEnv M (P + 0xFFFFF344) (reg nm sp) (reg nm a0) (reg nm a1) (reg nm a2) := by
      rw [hs, e0, e1, e2]
      exact ⟨even_at P env.hP 0xFFFFF344 (by decide), cIn env.mul sG.m env.sO.m hI, cIn env.mulR sG.mR env.sO.mR hI,
        hFa, by omega, hoa, hxa, hya, by rw [eFm]; exact g0' sG.m, by rw [eFm]; exact g0' sG.mR, hoc.m, hoc.mR,
        by rw [eFm]; exact soG, by rw [eFm]; exact sxG, by rw [eFm]; exact syG⟩
    obtain ⟨n1, c1, u1, sp1, k1, w1, f1⟩ := s.callFeMul hc h1 h2 hb (even_at P env.hP (off + 8) hev) e
    rw [e0, e1, e2] at w1; rw [hs, e0, eFm] at f1
    exact ⟨n1, c1, u1, by rw [sp1, hs], k1, w1, f1⟩
  have sqCall : ∀ {M : Word → BitVec 8} {nm : Machine} {off : Nat} {imm o' : Word} (o x : Word),
      St M P nm off (reg nm) → CodeIn M P pow22501Code →
      (∀ z, Sep G 0x450 z 1 → Sep out 0x50 z 1 → M z = m.mem z) →
      fetchRel pow22501Code off = some (.auipc ra imm, 4) →
      fetchRel pow22501Code (off + 4) = some (.jalr ra ra o', 4) →
      P + BitVec.ofNat 32 off + imm + o' = P + 0x1A8 → (off + 8) % 2 = 0 →
      reg nm sp = F → reg nm a0 = o → reg nm a1 = x →
      o.toNat % 4 = 0 → x.toNat % 4 = 0 → PwCode P o 40 → Sep o 40 G 0x140 → Sep x 40 G 0x140 →
      ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = F ∧
        (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
        (∀ i, i < 10 → limbs nm'.mem o i = feSqW (limbs M x) i) ∧
        ∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → nm'.mem z = M z := by
    intro M nm off imm o' o x s hc hI h1 h2 hb hev hs e0 e1 hoa hxa hoc soG sxG
    have e : FeSquareEnv M (P + 0x1A8) (reg nm sp) (reg nm a0) (reg nm a1) := by
      rw [hs, e0, e1]
      exact ⟨even_at P env.hP 0x1A8 (by decide), cIn env.sq sG.sq env.sO.sq hI, cIn env.sqi sG.sqi env.sO.sqi hI,
        cIn env.sqR sG.sqR env.sO.sqR hI, hFa, by omega, hoa, hxa, by rw [eFs]; exact sG.sq.sub (by decide),
        by rw [eFs]; exact sG.sqi.sub (by decide), by rw [eFs]; exact sG.sqR.sub (by decide), hoc.sq, hoc.sqR,
        by rw [eFs]; exact soG.subR (by decide), by rw [eFs]; exact sxG.subR (by decide)⟩
    obtain ⟨n1, c1, u1, sp1, k1, w1, f1⟩ := s.callFeSquare hc h1 h2 hb (even_at P env.hP (off + 8) hev) e
    rw [e0, e1] at w1; rw [hs, e0, eFs] at f1
    exact ⟨n1, c1, u1, by rw [sp1, hs], k1, w1, fun z hz ho => f1 z (hz.sub (by decide)) ho⟩
  have pkCall : ∀ {M : Word → BitVec 8} {nm : Machine} {off : Nat} {imm o' : Word} (k : Nat) (o x : Word),
      St M P nm off (reg nm) → CodeIn M P pow22501Code →
      (∀ z, Sep G 0x450 z 1 → Sep out 0x50 z 1 → M z = m.mem z) →
      fetchRel pow22501Code off = some (.auipc ra imm, 4) →
      fetchRel pow22501Code (off + 4) = some (.jalr ra ra o', 4) →
      P + BitVec.ofNat 32 off + imm + o' = P + 0x156 → (off + 8) % 2 = 0 → 0 < k → k < 2 ^ 32 →
      reg nm sp = F → reg nm a0 = o → reg nm a1 = x → reg nm a2 = BitVec.ofNat 32 k →
      o.toNat + 40 < 2 ^ 32 → o.toNat % 4 = 0 → x.toNat % 4 = 0 → PwCode P o 40 →
      Sep o 40 G 0x140 → Sep x 40 G 0x140 →
      ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = F ∧
        (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
        (∀ i, i < 10 → limbs nm'.mem o i = pow2kW k (limbs M x) i) ∧
        ∀ z, Sep G 0x140 z 1 → Sep o 40 z 1 → nm'.mem z = M z := by
    intro M nm off imm o' k o x s hc hI h1 h2 hb hev hk0 hk1 hs e0 e1 e2 hot hoa hxa hoc soG sxG
    have e : FpkEnv M (P + 0x156) (G + BitVec.ofNat 32 0x30) (reg nm a0) (reg nm a1) := by
      rw [e0, e1]
      exact ⟨even_at P env.hP 0x156 (by decide), cIn env.pk sG.pk env.sO.pk hI, cIn env.pkS sG.pkS env.sO.pkS hI,
        cIn env.pkI sG.pkI env.sO.pkI hI, cIn env.pkR sG.pkR env.sO.pkR hI, cIn env.pkMS sG.pkMS env.sO.pkMS hI,
        cIn env.pkMB sG.pkMB env.sO.pkMB hI, aligned_add hGa (by decide),
        by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega, hoa, hot, hxa,
        sG.pk.sub (by decide), sG.pkS.sub (by decide), sG.pkI.sub (by decide), sG.pkR.sub (by decide),
        sG.pkMS.sub (by decide), sG.pkMB.sub (by decide), hoc.pk, hoc.pkMB, soG.subR (by decide), sxG.subR (by decide)⟩
    obtain ⟨n1, c1, u1, sp1, k1, w1, f1⟩ := s.callFePow2k hc h1 h2 hb (even_at P env.hP (off + 8) hev) hk0 hk1 e2
      (by rw [hs, ← hGF, BitVec.add_assoc]; rfl) e
    rw [e0, e1] at w1; rw [e0] at f1
    exact ⟨n1, c1, u1, by rw [sp1, hs], k1, w1, fun z hz ho => f1 z (hz.sub (by decide)) ho⟩
  -- the prologue
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod pw_at_0 (off' := 4) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.aluImm env.cod pw_at_4 (off' := 6) (by decide)
  have r2 : ∀ q, q.val ≠ 0 → q ≠ sp → q ≠ a2 → reg m2 q = reg m q := fun q hv hs h3 => by
    rw [u2.regs, upd_ne hv h3, upd_ne hv hs]
  have sp2 : reg m2 sp = F := by
    rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  have a2v : reg m2 a2 = G + BitVec.ofNat 32 0x440 := by
    rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, ev_add, hsp, hF, eA]
  have slA : ∀ (o : Word), 4 ≤ o.toNat → o.toNat + 4 ≤ 0x10 → ∀ {b : Word} {l : Nat}, Sep G 0x450 b l →
      Sep (G + BitVec.ofNat 32 0x440 + o) 4 b l := fun o h1 h2 b l h => by
    rw [← ofNat_toNat_self o, add_ofNat_assoc]; exact h.sub (by omega)
  obtain ⟨m3a, cp3, u3a⟩ := St.block (saveBlockR a2 pwPs) u2.self env.cod pwSave_end
    (saveBlockR_ok a2 _ pwPs _ fun p hp => by
      rw [a2v]
      simp only [pwPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl <;>
        exact ⟨aligned_add (aligned_add hGa (k := 0x440) (by decide)) (by decide), slA _ (by decide) (by decide) sG.c⟩)
  simp only [saveBlockR_run] at u3a
  rw [a2v] at u3a
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (G + BitVec.ofNat 32 0x440) (reg m2) pwPs = Msv := ⟨_, rfl⟩
  rw [hMsv] at u3a
  have frSv : ∀ x, Sep G 0x450 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside pwPs fun p hp => by
      simp only [pwPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> exact slA _ (by decide) (by decide) hx
  have hslv : ∀ r o, (r, o) ∈ pwPs → memLoad32 Msv (G + BitVec.ofNat 32 0x440 + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [pwPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      exact r2 _ (by decide) (by decide) (by decide)
  have inv0 : ∀ z, Sep G 0x450 z 1 → Sep out 0x50 z 1 → Msv z = m.mem z := fun z h _ => frSv z h
  have hcS : CodeIn Msv P pow22501Code := cIn env.cod sG.c env.sO.c inv0
  obtain ⟨m3, cp4, u3⟩ := St.block [.alu .add (9 : Fin 32) x0 a1, .alu .add (8 : Fin 32) x0 a0] u3a.self hcS
    (off' := 0x12) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  have R3 : PwRegs m m3 F out xp := by
    refine ⟨?_, ?_, ?_, fun q hq => ?_⟩
    · rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u3a.regs, sp2]
    · rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte, u3a.regs]
      rw [ev_add, r2 a0 (by decide) (by decide) (by decide), ha0]; first | exact zw _ | (rw [u2.self.zero]; exact zw _)
    · rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte, u3a.regs]
      rw [ev_add, r2 a1 (by decide) (by decide) (by decide), ha1]; first | exact zw _ | (rw [u2.self.zero]; exact zw _)
    · have h : q.val ≠ 0 ∧ q ≠ 9 ∧ q ≠ 8 ∧ q ≠ sp ∧ q ≠ a2 := by revert hq; revert q; decide
      rw [u3.regs, upd_ne h.1 h.2.2.1, upd_ne h.1 h.2.1, u3a.regs, r2 q h.1 h.2.2.2.1 h.2.2.2.2]
  have slot0 : ∀ k, 0x444 ≤ k → k < 0x450 → Msv (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun _ _ _ => rfl
  -- call 1: sq -> pwT0
  obtain ⟨b1, cb1, ub1⟩ := St.block [.aluImm .add a0 sp 0xC] u3.self hcS
    (off' := 0x14) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub1
  have rb1 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b1 q = reg m3 q := fun q hv h0 h1 h2 => by
    rw [ub1.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n1, c1, u1, sp1, k1, w1, f1⟩ := sqCall (F + BitVec.ofNat 32 0xC) xp ub1.self hcS inv0
    pw_at_14 pw_at_18 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb1 sp (by decide) (by decide) (by decide) (by decide)]; exact R3.1)
    (by rw [ub1.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R3.1, R3.2.1, R3.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u3.self.zero]; first | rfl | exact zw _))
    (by rw [ub1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [u3a.regs, r2 a1 (by decide) (by decide) (by decide), ha1])
    (tA 0xC (by decide)) (env.hxp) (tC 0xC (by decide)) (tS 0xC (by decide)) (xS0)
  have inv1 := invStep inv0 f1 (tIn 0xC (by decide))
  have hc1 : CodeIn n1.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv1
  have slot1 : ∀ k, 0x444 ≤ k → k < 0x450 → n1.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f1 _ (gk k (by omega) h2) (tSl 0xC k (by decide) h1 h2)).trans (slot0 k h1 h2)
  have R1 : PwRegs m n1 F out xp := R3.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k1 q h.2.2.2.2.2 h.2.2.2.2.1, rb1 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V1 : ∀ i, i < 10 → limbs n1.mem (F + BitVec.ofNat 32 0xC) i = pwT0 (limbs m.mem xp) i := fun i hi => by
    rw [w1 i hi, feSqW_congr (x' := limbs m.mem xp) (xpK inv0)]
    all_goals rfl
  -- call 2: sq -> pwT0s
  obtain ⟨b2, cb2, ub2⟩ := St.block [.aluImm .add a0 sp 0x2DC, .aluImm .add a1 sp 0xC] u1.self hc1
    (off' := 0x20) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub2
  have rb2 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b2 q = reg n1 q := fun q hv h0 h1 h2 => by
    rw [ub2.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n2, c2, u2, sp2, k2, w2, f2⟩ := sqCall (F + BitVec.ofNat 32 0x2DC) (F + BitVec.ofNat 32 0xC) ub2.self hc1 inv1
    pw_at_20 pw_at_24 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb2 sp (by decide) (by decide) (by decide) (by decide)]; exact R1.1)
    (by rw [ub2.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R1.1, R1.2.1, R1.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u1.self.zero]; first | rfl | exact zw _))
    (by rw [ub2.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R1.1, R1.2.1, R1.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u1.self.zero]; first | rfl | exact zw _))
    (tA 0x2DC (by decide)) (tA 0xC (by decide)) (tC 0x2DC (by decide)) (tS 0x2DC (by decide)) (tS 0xC (by decide))
  have inv2 := invStep inv1 f2 (tIn 0x2DC (by decide))
  have hc2 : CodeIn n2.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv2
  have slot2 : ∀ k, 0x444 ≤ k → k < 0x450 → n2.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f2 _ (gk k (by omega) h2) (tSl 0x2DC k (by decide) h1 h2)).trans (slot1 k h1 h2)
  have R2 : PwRegs m n2 F out xp := R1.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k2 q h.2.2.2.2.2 h.2.2.2.2.1, rb2 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V2 : ∀ i, i < 10 → limbs n2.mem (F + BitVec.ofNat 32 0x2DC) i = pwT0s (limbs m.mem xp) i := fun i hi => by
    rw [w2 i hi, feSqW_congr (x' := pwT0 (limbs m.mem xp)) (fun l hl => V1 l hl)]
    all_goals rfl
  -- call 3: sq -> pwT1
  obtain ⟨b3, cb3, ub3⟩ := St.block [.aluImm .add a0 sp 0x34, .aluImm .add a1 sp 0x2DC] u2.self hc2
    (off' := 0x2C) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub3
  have rb3 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b3 q = reg n2 q := fun q hv h0 h1 h2 => by
    rw [ub3.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n3, c3, u3, sp3, k3, w3, f3⟩ := sqCall (F + BitVec.ofNat 32 0x34) (F + BitVec.ofNat 32 0x2DC) ub3.self hc2 inv2
    pw_at_2c pw_at_30 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb3 sp (by decide) (by decide) (by decide) (by decide)]; exact R2.1)
    (by rw [ub3.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R2.1, R2.2.1, R2.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u2.self.zero]; first | rfl | exact zw _))
    (by rw [ub3.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R2.1, R2.2.1, R2.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u2.self.zero]; first | rfl | exact zw _))
    (tA 0x34 (by decide)) (tA 0x2DC (by decide)) (tC 0x34 (by decide)) (tS 0x34 (by decide)) (tS 0x2DC (by decide))
  have inv3 := invStep inv2 f3 (tIn 0x34 (by decide))
  have hc3 : CodeIn n3.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv3
  have slot3 : ∀ k, 0x444 ≤ k → k < 0x450 → n3.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f3 _ (gk k (by omega) h2) (tSl 0x34 k (by decide) h1 h2)).trans (slot2 k h1 h2)
  have R3 : PwRegs m n3 F out xp := R2.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k3 q h.2.2.2.2.2 h.2.2.2.2.1, rb3 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V3 : ∀ i, i < 10 → limbs n3.mem (F + BitVec.ofNat 32 0x34) i = pwT1 (limbs m.mem xp) i := fun i hi => by
    rw [w3 i hi, feSqW_congr (x' := pwT0s (limbs m.mem xp)) (fun l hl => V2 l hl)]
    all_goals rfl
  -- call 4: mul -> pwT2
  obtain ⟨b4, cb4, ub4⟩ := St.block [.aluImm .add a0 sp 0x5C, .aluImm .add a2 sp 0x34, .alu .add a1 x0 (9 : Fin 32)] u3.self hc3
    (off' := 0x3A) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub4
  have rb4 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b4 q = reg n3 q := fun q hv h0 h1 h2 => by
    rw [ub4.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n4, c4, u4, sp4, k4, w4, f4⟩ := mulCall (F + BitVec.ofNat 32 0x5C) xp (F + BitVec.ofNat 32 0x34) ub4.self hc3 inv3
    pw_at_3a pw_at_3e (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb4 sp (by decide) (by decide) (by decide) (by decide)]; exact R3.1)
    (by rw [ub4.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R3.1, R3.2.1, R3.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u3.self.zero]; first | rfl | exact zw _))
    (by rw [ub4.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R3.1, R3.2.1, R3.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u3.self.zero]; first | rfl | exact zw _))
    (by rw [ub4.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R3.1, R3.2.1, R3.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u3.self.zero]; first | rfl | exact zw _))
    (tA 0x5C (by decide)) (env.hxp) (tA 0x34 (by decide)) (tC 0x5C (by decide)) (tS 0x5C (by decide)) (xS0) (tS 0x34 (by decide))
  have inv4 := invStep inv3 f4 (tIn 0x5C (by decide))
  have hc4 : CodeIn n4.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv4
  have slot4 : ∀ k, 0x444 ≤ k → k < 0x450 → n4.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f4 _ (gk k (by omega) h2) (tSl 0x5C k (by decide) h1 h2)).trans (slot3 k h1 h2)
  have R4 : PwRegs m n4 F out xp := R3.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k4 q h.2.2.2.2.2 h.2.2.2.2.1, rb4 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V4 : ∀ i, i < 10 → limbs n4.mem (F + BitVec.ofNat 32 0x5C) i = pwT2 (limbs m.mem xp) i := fun i hi => by
    rw [w4 i hi, feMulW_congr (x' := limbs m.mem xp) (y' := pwT1 (limbs m.mem xp))
      (xpK inv3)
      (fun l hl => V3 l hl)]
    all_goals rfl
  -- call 5: mul -> pwT3
  obtain ⟨b5, cb5, ub5⟩ := St.block [.aluImm .add a0 sp 0x84, .aluImm .add a1 sp 0xC, .aluImm .add a2 sp 0x5C] u4.self hc4
    (off' := 0x48) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub5
  have rb5 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b5 q = reg n4 q := fun q hv h0 h1 h2 => by
    rw [ub5.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n5, c5, u5, sp5, k5, w5, f5⟩ := mulCall (F + BitVec.ofNat 32 0x84) (F + BitVec.ofNat 32 0xC) (F + BitVec.ofNat 32 0x5C) ub5.self hc4 inv4
    pw_at_48 pw_at_4c (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb5 sp (by decide) (by decide) (by decide) (by decide)]; exact R4.1)
    (by rw [ub5.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R4.1, R4.2.1, R4.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u4.self.zero]; first | rfl | exact zw _))
    (by rw [ub5.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R4.1, R4.2.1, R4.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u4.self.zero]; first | rfl | exact zw _))
    (by rw [ub5.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R4.1, R4.2.1, R4.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u4.self.zero]; first | rfl | exact zw _))
    (tA 0x84 (by decide)) (tA 0xC (by decide)) (tA 0x5C (by decide)) (tC 0x84 (by decide)) (tS 0x84 (by decide)) (tS 0xC (by decide)) (tS 0x5C (by decide))
  have inv5 := invStep inv4 f5 (tIn 0x84 (by decide))
  have hc5 : CodeIn n5.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv5
  have slot5 : ∀ k, 0x444 ≤ k → k < 0x450 → n5.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f5 _ (gk k (by omega) h2) (tSl 0x84 k (by decide) h1 h2)).trans (slot4 k h1 h2)
  have R5 : PwRegs m n5 F out xp := R4.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k5 q h.2.2.2.2.2 h.2.2.2.2.1, rb5 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V5 : ∀ i, i < 10 → limbs n5.mem (F + BitVec.ofNat 32 0x84) i = pwT3 (limbs m.mem xp) i := fun i hi => by
    rw [w5 i hi, feMulW_congr (x' := pwT0 (limbs m.mem xp)) (y' := pwT2 (limbs m.mem xp))
      (fun l hl => by
        rw [tP 0xC f4 (by decide) (tT 0xC 0x5C (.inl (by decide)) (by decide) (by decide)) l hl, tP 0xC f3 (by decide) (tT 0xC 0x34 (.inl (by decide)) (by decide) (by decide)) l hl, tP 0xC f2 (by decide) (tT 0xC 0x2DC (.inl (by decide)) (by decide) (by decide)) l hl]
        exact V1 l hl)
      (fun l hl => V4 l hl)]
    all_goals rfl
  -- call 6: sq -> pwT4
  obtain ⟨b6, cb6, ub6⟩ := St.block [.aluImm .add a0 sp 0xAC, .aluImm .add a1 sp 0x84] u5.self hc5
    (off' := 0x54) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub6
  have rb6 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b6 q = reg n5 q := fun q hv h0 h1 h2 => by
    rw [ub6.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n6, c6, u6, sp6, k6, w6, f6⟩ := sqCall (F + BitVec.ofNat 32 0xAC) (F + BitVec.ofNat 32 0x84) ub6.self hc5 inv5
    pw_at_54 pw_at_58 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb6 sp (by decide) (by decide) (by decide) (by decide)]; exact R5.1)
    (by rw [ub6.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R5.1, R5.2.1, R5.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u5.self.zero]; first | rfl | exact zw _))
    (by rw [ub6.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R5.1, R5.2.1, R5.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u5.self.zero]; first | rfl | exact zw _))
    (tA 0xAC (by decide)) (tA 0x84 (by decide)) (tC 0xAC (by decide)) (tS 0xAC (by decide)) (tS 0x84 (by decide))
  have inv6 := invStep inv5 f6 (tIn 0xAC (by decide))
  have hc6 : CodeIn n6.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv6
  have slot6 : ∀ k, 0x444 ≤ k → k < 0x450 → n6.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f6 _ (gk k (by omega) h2) (tSl 0xAC k (by decide) h1 h2)).trans (slot5 k h1 h2)
  have R6 : PwRegs m n6 F out xp := R5.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k6 q h.2.2.2.2.2 h.2.2.2.2.1, rb6 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V6 : ∀ i, i < 10 → limbs n6.mem (F + BitVec.ofNat 32 0xAC) i = pwT4 (limbs m.mem xp) i := fun i hi => by
    rw [w6 i hi, feSqW_congr (x' := pwT3 (limbs m.mem xp)) (fun l hl => V5 l hl)]
    all_goals rfl
  -- call 7: mul -> pwT5
  obtain ⟨b7, cb7, ub7⟩ := St.block [.aluImm .add a0 sp 0xD4, .aluImm .add a1 sp 0x5C, .aluImm .add a2 sp 0xAC] u6.self hc6
    (off' := 0x62) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub7
  have rb7 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b7 q = reg n6 q := fun q hv h0 h1 h2 => by
    rw [ub7.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n7, c7, u7, sp7, k7, w7, f7⟩ := mulCall (F + BitVec.ofNat 32 0xD4) (F + BitVec.ofNat 32 0x5C) (F + BitVec.ofNat 32 0xAC) ub7.self hc6 inv6
    pw_at_62 pw_at_66 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb7 sp (by decide) (by decide) (by decide) (by decide)]; exact R6.1)
    (by rw [ub7.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R6.1, R6.2.1, R6.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u6.self.zero]; first | rfl | exact zw _))
    (by rw [ub7.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R6.1, R6.2.1, R6.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u6.self.zero]; first | rfl | exact zw _))
    (by rw [ub7.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R6.1, R6.2.1, R6.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u6.self.zero]; first | rfl | exact zw _))
    (tA 0xD4 (by decide)) (tA 0x5C (by decide)) (tA 0xAC (by decide)) (tC 0xD4 (by decide)) (tS 0xD4 (by decide)) (tS 0x5C (by decide)) (tS 0xAC (by decide))
  have inv7 := invStep inv6 f7 (tIn 0xD4 (by decide))
  have hc7 : CodeIn n7.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv7
  have slot7 : ∀ k, 0x444 ≤ k → k < 0x450 → n7.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f7 _ (gk k (by omega) h2) (tSl 0xD4 k (by decide) h1 h2)).trans (slot6 k h1 h2)
  have R7 : PwRegs m n7 F out xp := R6.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k7 q h.2.2.2.2.2 h.2.2.2.2.1, rb7 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V7 : ∀ i, i < 10 → limbs n7.mem (F + BitVec.ofNat 32 0xD4) i = pwT5 (limbs m.mem xp) i := fun i hi => by
    rw [w7 i hi, feMulW_congr (x' := pwT2 (limbs m.mem xp)) (y' := pwT4 (limbs m.mem xp))
      (fun l hl => by
        rw [tP 0x5C f6 (by decide) (tT 0x5C 0xAC (.inl (by decide)) (by decide) (by decide)) l hl, tP 0x5C f5 (by decide) (tT 0x5C 0x84 (.inl (by decide)) (by decide) (by decide)) l hl]
        exact V4 l hl)
      (fun l hl => V6 l hl)]
    all_goals rfl
  -- call 8: pk -> pwT6
  obtain ⟨b8, cb8, ub8⟩ := St.block [.aluImm .add a0 sp 0xFC, .aluImm .add a1 sp 0xD4, .aluImm .add a2 x0 0x5] u7.self hc7
    (off' := 0x70) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub8
  have rb8 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b8 q = reg n7 q := fun q hv h0 h1 h2 => by
    rw [ub8.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n8, c8, u8, sp8, k8, w8, f8⟩ := pkCall 5 (F + BitVec.ofNat 32 0xFC) (F + BitVec.ofNat 32 0xD4) ub8.self hc7 inv7
    pw_at_70 pw_at_74 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (by decide) (by decide)
    (by rw [rb8 sp (by decide) (by decide) (by decide) (by decide)]; exact R7.1)
    (by rw [ub8.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R7.1, R7.2.1, R7.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u7.self.zero]; first | rfl | exact zw _))
    (by rw [ub8.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R7.1, R7.2.1, R7.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u7.self.zero]; first | rfl | exact zw _))
    (by rw [ub8.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R7.1, R7.2.1, R7.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u7.self.zero]; first | rfl | exact zw _))
    (tW 0xFC (by decide)) (tA 0xFC (by decide)) (tA 0xD4 (by decide)) (tC 0xFC (by decide)) (tS 0xFC (by decide)) (tS 0xD4 (by decide))
  have inv8 := invStep inv7 f8 (tIn 0xFC (by decide))
  have hc8 : CodeIn n8.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv8
  have slot8 : ∀ k, 0x444 ≤ k → k < 0x450 → n8.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f8 _ (gk k (by omega) h2) (tSl 0xFC k (by decide) h1 h2)).trans (slot7 k h1 h2)
  have R8 : PwRegs m n8 F out xp := R7.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k8 q h.2.2.2.2.2 h.2.2.2.2.1, rb8 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V8 : ∀ i, i < 10 → limbs n8.mem (F + BitVec.ofNat 32 0xFC) i = pwT6 (limbs m.mem xp) i := fun i hi => by
    rw [w8 i hi, pow2kW_congr (x' := pwT5 (limbs m.mem xp)) (fun l hl => V7 l hl)]
    all_goals rfl
  -- call 9: mul -> pwT7
  obtain ⟨b9, cb9, ub9⟩ := St.block [.aluImm .add a0 sp 0x124, .aluImm .add a1 sp 0xFC, .aluImm .add a2 sp 0xD4] u8.self hc8
    (off' := 0x7E) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub9
  have rb9 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b9 q = reg n8 q := fun q hv h0 h1 h2 => by
    rw [ub9.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n9, c9, u9, sp9, k9, w9, f9⟩ := mulCall (F + BitVec.ofNat 32 0x124) (F + BitVec.ofNat 32 0xFC) (F + BitVec.ofNat 32 0xD4) ub9.self hc8 inv8
    pw_at_7e pw_at_82 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb9 sp (by decide) (by decide) (by decide) (by decide)]; exact R8.1)
    (by rw [ub9.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R8.1, R8.2.1, R8.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u8.self.zero]; first | rfl | exact zw _))
    (by rw [ub9.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R8.1, R8.2.1, R8.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u8.self.zero]; first | rfl | exact zw _))
    (by rw [ub9.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R8.1, R8.2.1, R8.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u8.self.zero]; first | rfl | exact zw _))
    (tA 0x124 (by decide)) (tA 0xFC (by decide)) (tA 0xD4 (by decide)) (tC 0x124 (by decide)) (tS 0x124 (by decide)) (tS 0xFC (by decide)) (tS 0xD4 (by decide))
  have inv9 := invStep inv8 f9 (tIn 0x124 (by decide))
  have hc9 : CodeIn n9.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv9
  have slot9 : ∀ k, 0x444 ≤ k → k < 0x450 → n9.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f9 _ (gk k (by omega) h2) (tSl 0x124 k (by decide) h1 h2)).trans (slot8 k h1 h2)
  have R9 : PwRegs m n9 F out xp := R8.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k9 q h.2.2.2.2.2 h.2.2.2.2.1, rb9 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V9 : ∀ i, i < 10 → limbs n9.mem (F + BitVec.ofNat 32 0x124) i = pwT7 (limbs m.mem xp) i := fun i hi => by
    rw [w9 i hi, feMulW_congr (x' := pwT6 (limbs m.mem xp)) (y' := pwT5 (limbs m.mem xp))
      (fun l hl => V8 l hl)
      (fun l hl => by
        rw [tP 0xD4 f8 (by decide) (tT 0xD4 0xFC (.inl (by decide)) (by decide) (by decide)) l hl]
        exact V7 l hl)]
    all_goals rfl
  -- call 10: pk -> pwT8
  obtain ⟨b10, cb10, ub10⟩ := St.block [.aluImm .add a0 sp 0x14C, .aluImm .add a1 sp 0x124, .aluImm .add a2 x0 0xA] u9.self hc9
    (off' := 0x8C) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub10
  have rb10 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b10 q = reg n9 q := fun q hv h0 h1 h2 => by
    rw [ub10.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n10, c10, u10, sp10, k10, w10, f10⟩ := pkCall 10 (F + BitVec.ofNat 32 0x14C) (F + BitVec.ofNat 32 0x124) ub10.self hc9 inv9
    pw_at_8c pw_at_90 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (by decide) (by decide)
    (by rw [rb10 sp (by decide) (by decide) (by decide) (by decide)]; exact R9.1)
    (by rw [ub10.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R9.1, R9.2.1, R9.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u9.self.zero]; first | rfl | exact zw _))
    (by rw [ub10.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R9.1, R9.2.1, R9.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u9.self.zero]; first | rfl | exact zw _))
    (by rw [ub10.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R9.1, R9.2.1, R9.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u9.self.zero]; first | rfl | exact zw _))
    (tW 0x14C (by decide)) (tA 0x14C (by decide)) (tA 0x124 (by decide)) (tC 0x14C (by decide)) (tS 0x14C (by decide)) (tS 0x124 (by decide))
  have inv10 := invStep inv9 f10 (tIn 0x14C (by decide))
  have hc10 : CodeIn n10.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv10
  have slot10 : ∀ k, 0x444 ≤ k → k < 0x450 → n10.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f10 _ (gk k (by omega) h2) (tSl 0x14C k (by decide) h1 h2)).trans (slot9 k h1 h2)
  have R10 : PwRegs m n10 F out xp := R9.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k10 q h.2.2.2.2.2 h.2.2.2.2.1, rb10 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V10 : ∀ i, i < 10 → limbs n10.mem (F + BitVec.ofNat 32 0x14C) i = pwT8 (limbs m.mem xp) i := fun i hi => by
    rw [w10 i hi, pow2kW_congr (x' := pwT7 (limbs m.mem xp)) (fun l hl => V9 l hl)]
    all_goals rfl
  -- call 11: mul -> pwT9
  obtain ⟨b11, cb11, ub11⟩ := St.block [.aluImm .add a0 sp 0x174, .aluImm .add a1 sp 0x14C, .aluImm .add a2 sp 0x124] u10.self hc10
    (off' := 0x9A) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub11
  have rb11 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b11 q = reg n10 q := fun q hv h0 h1 h2 => by
    rw [ub11.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n11, c11, u11, sp11, k11, w11, f11⟩ := mulCall (F + BitVec.ofNat 32 0x174) (F + BitVec.ofNat 32 0x14C) (F + BitVec.ofNat 32 0x124) ub11.self hc10 inv10
    pw_at_9a pw_at_9e (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb11 sp (by decide) (by decide) (by decide) (by decide)]; exact R10.1)
    (by rw [ub11.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R10.1, R10.2.1, R10.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u10.self.zero]; first | rfl | exact zw _))
    (by rw [ub11.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R10.1, R10.2.1, R10.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u10.self.zero]; first | rfl | exact zw _))
    (by rw [ub11.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R10.1, R10.2.1, R10.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u10.self.zero]; first | rfl | exact zw _))
    (tA 0x174 (by decide)) (tA 0x14C (by decide)) (tA 0x124 (by decide)) (tC 0x174 (by decide)) (tS 0x174 (by decide)) (tS 0x14C (by decide)) (tS 0x124 (by decide))
  have inv11 := invStep inv10 f11 (tIn 0x174 (by decide))
  have hc11 : CodeIn n11.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv11
  have slot11 : ∀ k, 0x444 ≤ k → k < 0x450 → n11.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f11 _ (gk k (by omega) h2) (tSl 0x174 k (by decide) h1 h2)).trans (slot10 k h1 h2)
  have R11 : PwRegs m n11 F out xp := R10.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k11 q h.2.2.2.2.2 h.2.2.2.2.1, rb11 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V11 : ∀ i, i < 10 → limbs n11.mem (F + BitVec.ofNat 32 0x174) i = pwT9 (limbs m.mem xp) i := fun i hi => by
    rw [w11 i hi, feMulW_congr (x' := pwT8 (limbs m.mem xp)) (y' := pwT7 (limbs m.mem xp))
      (fun l hl => V10 l hl)
      (fun l hl => by
        rw [tP 0x124 f10 (by decide) (tT 0x124 0x14C (.inl (by decide)) (by decide) (by decide)) l hl]
        exact V9 l hl)]
    all_goals rfl
  -- call 12: pk -> pwT10
  obtain ⟨b12, cb12, ub12⟩ := St.block [.aluImm .add a0 sp 0x19C, .aluImm .add a1 sp 0x174, .aluImm .add a2 x0 0x14] u11.self hc11
    (off' := 0xA8) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub12
  have rb12 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b12 q = reg n11 q := fun q hv h0 h1 h2 => by
    rw [ub12.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n12, c12, u12, sp12, k12, w12, f12⟩ := pkCall 20 (F + BitVec.ofNat 32 0x19C) (F + BitVec.ofNat 32 0x174) ub12.self hc11 inv11
    pw_at_a8 pw_at_ac (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (by decide) (by decide)
    (by rw [rb12 sp (by decide) (by decide) (by decide) (by decide)]; exact R11.1)
    (by rw [ub12.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R11.1, R11.2.1, R11.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u11.self.zero]; first | rfl | exact zw _))
    (by rw [ub12.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R11.1, R11.2.1, R11.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u11.self.zero]; first | rfl | exact zw _))
    (by rw [ub12.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R11.1, R11.2.1, R11.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u11.self.zero]; first | rfl | exact zw _))
    (tW 0x19C (by decide)) (tA 0x19C (by decide)) (tA 0x174 (by decide)) (tC 0x19C (by decide)) (tS 0x19C (by decide)) (tS 0x174 (by decide))
  have inv12 := invStep inv11 f12 (tIn 0x19C (by decide))
  have hc12 : CodeIn n12.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv12
  have slot12 : ∀ k, 0x444 ≤ k → k < 0x450 → n12.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f12 _ (gk k (by omega) h2) (tSl 0x19C k (by decide) h1 h2)).trans (slot11 k h1 h2)
  have R12 : PwRegs m n12 F out xp := R11.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k12 q h.2.2.2.2.2 h.2.2.2.2.1, rb12 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V12 : ∀ i, i < 10 → limbs n12.mem (F + BitVec.ofNat 32 0x19C) i = pwT10 (limbs m.mem xp) i := fun i hi => by
    rw [w12 i hi, pow2kW_congr (x' := pwT9 (limbs m.mem xp)) (fun l hl => V11 l hl)]
    all_goals rfl
  -- call 13: mul -> pwT11
  obtain ⟨b13, cb13, ub13⟩ := St.block [.aluImm .add a0 sp 0x1C4, .aluImm .add a1 sp 0x19C, .aluImm .add a2 sp 0x174] u12.self hc12
    (off' := 0xB6) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub13
  have rb13 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b13 q = reg n12 q := fun q hv h0 h1 h2 => by
    rw [ub13.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n13, c13, u13, sp13, k13, w13, f13⟩ := mulCall (F + BitVec.ofNat 32 0x1C4) (F + BitVec.ofNat 32 0x19C) (F + BitVec.ofNat 32 0x174) ub13.self hc12 inv12
    pw_at_b6 pw_at_ba (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb13 sp (by decide) (by decide) (by decide) (by decide)]; exact R12.1)
    (by rw [ub13.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R12.1, R12.2.1, R12.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u12.self.zero]; first | rfl | exact zw _))
    (by rw [ub13.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R12.1, R12.2.1, R12.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u12.self.zero]; first | rfl | exact zw _))
    (by rw [ub13.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R12.1, R12.2.1, R12.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u12.self.zero]; first | rfl | exact zw _))
    (tA 0x1C4 (by decide)) (tA 0x19C (by decide)) (tA 0x174 (by decide)) (tC 0x1C4 (by decide)) (tS 0x1C4 (by decide)) (tS 0x19C (by decide)) (tS 0x174 (by decide))
  have inv13 := invStep inv12 f13 (tIn 0x1C4 (by decide))
  have hc13 : CodeIn n13.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv13
  have slot13 : ∀ k, 0x444 ≤ k → k < 0x450 → n13.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f13 _ (gk k (by omega) h2) (tSl 0x1C4 k (by decide) h1 h2)).trans (slot12 k h1 h2)
  have R13 : PwRegs m n13 F out xp := R12.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k13 q h.2.2.2.2.2 h.2.2.2.2.1, rb13 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V13 : ∀ i, i < 10 → limbs n13.mem (F + BitVec.ofNat 32 0x1C4) i = pwT11 (limbs m.mem xp) i := fun i hi => by
    rw [w13 i hi, feMulW_congr (x' := pwT10 (limbs m.mem xp)) (y' := pwT9 (limbs m.mem xp))
      (fun l hl => V12 l hl)
      (fun l hl => by
        rw [tP 0x174 f12 (by decide) (tT 0x174 0x19C (.inl (by decide)) (by decide) (by decide)) l hl]
        exact V11 l hl)]
    all_goals rfl
  -- call 14: pk -> pwT12
  obtain ⟨b14, cb14, ub14⟩ := St.block [.aluImm .add a0 sp 0x1EC, .aluImm .add a1 sp 0x1C4, .aluImm .add a2 x0 0xA] u13.self hc13
    (off' := 0xC4) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub14
  have rb14 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b14 q = reg n13 q := fun q hv h0 h1 h2 => by
    rw [ub14.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n14, c14, u14, sp14, k14, w14, f14⟩ := pkCall 10 (F + BitVec.ofNat 32 0x1EC) (F + BitVec.ofNat 32 0x1C4) ub14.self hc13 inv13
    pw_at_c4 pw_at_c8 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (by decide) (by decide)
    (by rw [rb14 sp (by decide) (by decide) (by decide) (by decide)]; exact R13.1)
    (by rw [ub14.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R13.1, R13.2.1, R13.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u13.self.zero]; first | rfl | exact zw _))
    (by rw [ub14.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R13.1, R13.2.1, R13.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u13.self.zero]; first | rfl | exact zw _))
    (by rw [ub14.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R13.1, R13.2.1, R13.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u13.self.zero]; first | rfl | exact zw _))
    (tW 0x1EC (by decide)) (tA 0x1EC (by decide)) (tA 0x1C4 (by decide)) (tC 0x1EC (by decide)) (tS 0x1EC (by decide)) (tS 0x1C4 (by decide))
  have inv14 := invStep inv13 f14 (tIn 0x1EC (by decide))
  have hc14 : CodeIn n14.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv14
  have slot14 : ∀ k, 0x444 ≤ k → k < 0x450 → n14.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f14 _ (gk k (by omega) h2) (tSl 0x1EC k (by decide) h1 h2)).trans (slot13 k h1 h2)
  have R14 : PwRegs m n14 F out xp := R13.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k14 q h.2.2.2.2.2 h.2.2.2.2.1, rb14 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V14 : ∀ i, i < 10 → limbs n14.mem (F + BitVec.ofNat 32 0x1EC) i = pwT12 (limbs m.mem xp) i := fun i hi => by
    rw [w14 i hi, pow2kW_congr (x' := pwT11 (limbs m.mem xp)) (fun l hl => V13 l hl)]
    all_goals rfl
  -- call 15: mul -> pwT13
  obtain ⟨b15, cb15, ub15⟩ := St.block [.aluImm .add a0 sp 0x214, .aluImm .add a1 sp 0x1EC, .aluImm .add a2 sp 0x124] u14.self hc14
    (off' := 0xD2) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub15
  have rb15 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b15 q = reg n14 q := fun q hv h0 h1 h2 => by
    rw [ub15.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n15, c15, u15, sp15, k15, w15, f15⟩ := mulCall (F + BitVec.ofNat 32 0x214) (F + BitVec.ofNat 32 0x1EC) (F + BitVec.ofNat 32 0x124) ub15.self hc14 inv14
    pw_at_d2 pw_at_d6 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb15 sp (by decide) (by decide) (by decide) (by decide)]; exact R14.1)
    (by rw [ub15.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R14.1, R14.2.1, R14.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u14.self.zero]; first | rfl | exact zw _))
    (by rw [ub15.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R14.1, R14.2.1, R14.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u14.self.zero]; first | rfl | exact zw _))
    (by rw [ub15.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R14.1, R14.2.1, R14.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u14.self.zero]; first | rfl | exact zw _))
    (tA 0x214 (by decide)) (tA 0x1EC (by decide)) (tA 0x124 (by decide)) (tC 0x214 (by decide)) (tS 0x214 (by decide)) (tS 0x1EC (by decide)) (tS 0x124 (by decide))
  have inv15 := invStep inv14 f15 (tIn 0x214 (by decide))
  have hc15 : CodeIn n15.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv15
  have slot15 : ∀ k, 0x444 ≤ k → k < 0x450 → n15.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f15 _ (gk k (by omega) h2) (tSl 0x214 k (by decide) h1 h2)).trans (slot14 k h1 h2)
  have R15 : PwRegs m n15 F out xp := R14.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k15 q h.2.2.2.2.2 h.2.2.2.2.1, rb15 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V15 : ∀ i, i < 10 → limbs n15.mem (F + BitVec.ofNat 32 0x214) i = pwT13 (limbs m.mem xp) i := fun i hi => by
    rw [w15 i hi, feMulW_congr (x' := pwT12 (limbs m.mem xp)) (y' := pwT7 (limbs m.mem xp))
      (fun l hl => V14 l hl)
      (fun l hl => by
        rw [tP 0x124 f14 (by decide) (tT 0x124 0x1EC (.inl (by decide)) (by decide) (by decide)) l hl, tP 0x124 f13 (by decide) (tT 0x124 0x1C4 (.inl (by decide)) (by decide) (by decide)) l hl, tP 0x124 f12 (by decide) (tT 0x124 0x19C (.inl (by decide)) (by decide) (by decide)) l hl, tP 0x124 f11 (by decide) (tT 0x124 0x174 (.inl (by decide)) (by decide) (by decide)) l hl, tP 0x124 f10 (by decide) (tT 0x124 0x14C (.inl (by decide)) (by decide) (by decide)) l hl]
        exact V9 l hl)]
    all_goals rfl
  -- call 16: pk -> pwT14
  obtain ⟨b16, cb16, ub16⟩ := St.block [.aluImm .add a0 sp 0x23C, .aluImm .add a1 sp 0x214, .aluImm .add a2 x0 0x32] u15.self hc15
    (off' := 0xE2) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub16
  have rb16 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b16 q = reg n15 q := fun q hv h0 h1 h2 => by
    rw [ub16.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n16, c16, u16, sp16, k16, w16, f16⟩ := pkCall 50 (F + BitVec.ofNat 32 0x23C) (F + BitVec.ofNat 32 0x214) ub16.self hc15 inv15
    pw_at_e2 pw_at_e6 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (by decide) (by decide)
    (by rw [rb16 sp (by decide) (by decide) (by decide) (by decide)]; exact R15.1)
    (by rw [ub16.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R15.1, R15.2.1, R15.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u15.self.zero]; first | rfl | exact zw _))
    (by rw [ub16.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R15.1, R15.2.1, R15.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u15.self.zero]; first | rfl | exact zw _))
    (by rw [ub16.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R15.1, R15.2.1, R15.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u15.self.zero]; first | rfl | exact zw _))
    (tW 0x23C (by decide)) (tA 0x23C (by decide)) (tA 0x214 (by decide)) (tC 0x23C (by decide)) (tS 0x23C (by decide)) (tS 0x214 (by decide))
  have inv16 := invStep inv15 f16 (tIn 0x23C (by decide))
  have hc16 : CodeIn n16.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv16
  have slot16 : ∀ k, 0x444 ≤ k → k < 0x450 → n16.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f16 _ (gk k (by omega) h2) (tSl 0x23C k (by decide) h1 h2)).trans (slot15 k h1 h2)
  have R16 : PwRegs m n16 F out xp := R15.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k16 q h.2.2.2.2.2 h.2.2.2.2.1, rb16 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V16 : ∀ i, i < 10 → limbs n16.mem (F + BitVec.ofNat 32 0x23C) i = pwT14 (limbs m.mem xp) i := fun i hi => by
    rw [w16 i hi, pow2kW_congr (x' := pwT13 (limbs m.mem xp)) (fun l hl => V15 l hl)]
    all_goals rfl
  -- call 17: mul -> pwT15
  obtain ⟨b17, cb17, ub17⟩ := St.block [.aluImm .add a0 sp 0x264, .aluImm .add a1 sp 0x23C, .aluImm .add a2 sp 0x214] u16.self hc16
    (off' := 0xF0) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub17
  have rb17 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b17 q = reg n16 q := fun q hv h0 h1 h2 => by
    rw [ub17.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n17, c17, u17, sp17, k17, w17, f17⟩ := mulCall (F + BitVec.ofNat 32 0x264) (F + BitVec.ofNat 32 0x23C) (F + BitVec.ofNat 32 0x214) ub17.self hc16 inv16
    pw_at_f0 pw_at_f4 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb17 sp (by decide) (by decide) (by decide) (by decide)]; exact R16.1)
    (by rw [ub17.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R16.1, R16.2.1, R16.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u16.self.zero]; first | rfl | exact zw _))
    (by rw [ub17.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R16.1, R16.2.1, R16.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u16.self.zero]; first | rfl | exact zw _))
    (by rw [ub17.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R16.1, R16.2.1, R16.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u16.self.zero]; first | rfl | exact zw _))
    (tA 0x264 (by decide)) (tA 0x23C (by decide)) (tA 0x214 (by decide)) (tC 0x264 (by decide)) (tS 0x264 (by decide)) (tS 0x23C (by decide)) (tS 0x214 (by decide))
  have inv17 := invStep inv16 f17 (tIn 0x264 (by decide))
  have hc17 : CodeIn n17.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv17
  have slot17 : ∀ k, 0x444 ≤ k → k < 0x450 → n17.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f17 _ (gk k (by omega) h2) (tSl 0x264 k (by decide) h1 h2)).trans (slot16 k h1 h2)
  have R17 : PwRegs m n17 F out xp := R16.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k17 q h.2.2.2.2.2 h.2.2.2.2.1, rb17 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V17 : ∀ i, i < 10 → limbs n17.mem (F + BitVec.ofNat 32 0x264) i = pwT15 (limbs m.mem xp) i := fun i hi => by
    rw [w17 i hi, feMulW_congr (x' := pwT14 (limbs m.mem xp)) (y' := pwT13 (limbs m.mem xp))
      (fun l hl => V16 l hl)
      (fun l hl => by
        rw [tP 0x214 f16 (by decide) (tT 0x214 0x23C (.inl (by decide)) (by decide) (by decide)) l hl]
        exact V15 l hl)]
    all_goals rfl
  -- call 18: pk -> pwT16
  obtain ⟨b18, cb18, ub18⟩ := St.block [.aluImm .add a0 sp 0x28C, .aluImm .add a1 sp 0x264, .aluImm .add a2 x0 0x64] u17.self hc17
    (off' := 0x100) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub18
  have rb18 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b18 q = reg n17 q := fun q hv h0 h1 h2 => by
    rw [ub18.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n18, c18, u18, sp18, k18, w18, f18⟩ := pkCall 100 (F + BitVec.ofNat 32 0x28C) (F + BitVec.ofNat 32 0x264) ub18.self hc17 inv17
    pw_at_100 pw_at_104 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (by decide) (by decide)
    (by rw [rb18 sp (by decide) (by decide) (by decide) (by decide)]; exact R17.1)
    (by rw [ub18.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R17.1, R17.2.1, R17.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u17.self.zero]; first | rfl | exact zw _))
    (by rw [ub18.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R17.1, R17.2.1, R17.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u17.self.zero]; first | rfl | exact zw _))
    (by rw [ub18.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R17.1, R17.2.1, R17.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u17.self.zero]; first | rfl | exact zw _))
    (tW 0x28C (by decide)) (tA 0x28C (by decide)) (tA 0x264 (by decide)) (tC 0x28C (by decide)) (tS 0x28C (by decide)) (tS 0x264 (by decide))
  have inv18 := invStep inv17 f18 (tIn 0x28C (by decide))
  have hc18 : CodeIn n18.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv18
  have slot18 : ∀ k, 0x444 ≤ k → k < 0x450 → n18.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f18 _ (gk k (by omega) h2) (tSl 0x28C k (by decide) h1 h2)).trans (slot17 k h1 h2)
  have R18 : PwRegs m n18 F out xp := R17.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k18 q h.2.2.2.2.2 h.2.2.2.2.1, rb18 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V18 : ∀ i, i < 10 → limbs n18.mem (F + BitVec.ofNat 32 0x28C) i = pwT16 (limbs m.mem xp) i := fun i hi => by
    rw [w18 i hi, pow2kW_congr (x' := pwT15 (limbs m.mem xp)) (fun l hl => V17 l hl)]
    all_goals rfl
  -- call 19: mul -> pwT17
  obtain ⟨b19, cb19, ub19⟩ := St.block [.aluImm .add a0 sp 0x2B4, .aluImm .add a1 sp 0x28C, .aluImm .add a2 sp 0x264] u18.self hc18
    (off' := 0x10E) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub19
  have rb19 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b19 q = reg n18 q := fun q hv h0 h1 h2 => by
    rw [ub19.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n19, c19, u19, sp19, k19, w19, f19⟩ := mulCall (F + BitVec.ofNat 32 0x2B4) (F + BitVec.ofNat 32 0x28C) (F + BitVec.ofNat 32 0x264) ub19.self hc18 inv18
    pw_at_10e pw_at_112 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb19 sp (by decide) (by decide) (by decide) (by decide)]; exact R18.1)
    (by rw [ub19.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R18.1, R18.2.1, R18.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u18.self.zero]; first | rfl | exact zw _))
    (by rw [ub19.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R18.1, R18.2.1, R18.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u18.self.zero]; first | rfl | exact zw _))
    (by rw [ub19.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R18.1, R18.2.1, R18.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u18.self.zero]; first | rfl | exact zw _))
    (tA 0x2B4 (by decide)) (tA 0x28C (by decide)) (tA 0x264 (by decide)) (tC 0x2B4 (by decide)) (tS 0x2B4 (by decide)) (tS 0x28C (by decide)) (tS 0x264 (by decide))
  have inv19 := invStep inv18 f19 (tIn 0x2B4 (by decide))
  have hc19 : CodeIn n19.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv19
  have slot19 : ∀ k, 0x444 ≤ k → k < 0x450 → n19.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f19 _ (gk k (by omega) h2) (tSl 0x2B4 k (by decide) h1 h2)).trans (slot18 k h1 h2)
  have R19 : PwRegs m n19 F out xp := R18.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k19 q h.2.2.2.2.2 h.2.2.2.2.1, rb19 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V19 : ∀ i, i < 10 → limbs n19.mem (F + BitVec.ofNat 32 0x2B4) i = pwT17 (limbs m.mem xp) i := fun i hi => by
    rw [w19 i hi, feMulW_congr (x' := pwT16 (limbs m.mem xp)) (y' := pwT15 (limbs m.mem xp))
      (fun l hl => V18 l hl)
      (fun l hl => by
        rw [tP 0x264 f18 (by decide) (tT 0x264 0x28C (.inl (by decide)) (by decide) (by decide)) l hl]
        exact V17 l hl)]
    all_goals rfl
  -- call 20: pk -> pwT18
  obtain ⟨b20, cb20, ub20⟩ := St.block [.aluImm .add a0 sp 0x2DC, .aluImm .add a1 sp 0x2B4, .aluImm .add a2 x0 0x32] u19.self hc19
    (off' := 0x11E) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub20
  have rb20 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b20 q = reg n19 q := fun q hv h0 h1 h2 => by
    rw [ub20.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n20, c20, u20, sp20, k20, w20, f20⟩ := pkCall 50 (F + BitVec.ofNat 32 0x2DC) (F + BitVec.ofNat 32 0x2B4) ub20.self hc19 inv19
    pw_at_11e pw_at_122 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (by decide) (by decide)
    (by rw [rb20 sp (by decide) (by decide) (by decide) (by decide)]; exact R19.1)
    (by rw [ub20.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R19.1, R19.2.1, R19.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u19.self.zero]; first | rfl | exact zw _))
    (by rw [ub20.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R19.1, R19.2.1, R19.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u19.self.zero]; first | rfl | exact zw _))
    (by rw [ub20.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R19.1, R19.2.1, R19.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u19.self.zero]; first | rfl | exact zw _))
    (tW 0x2DC (by decide)) (tA 0x2DC (by decide)) (tA 0x2B4 (by decide)) (tC 0x2DC (by decide)) (tS 0x2DC (by decide)) (tS 0x2B4 (by decide))
  have inv20 := invStep inv19 f20 (tIn 0x2DC (by decide))
  have hc20 : CodeIn n20.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv20
  have slot20 : ∀ k, 0x444 ≤ k → k < 0x450 → n20.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f20 _ (gk k (by omega) h2) (tSl 0x2DC k (by decide) h1 h2)).trans (slot19 k h1 h2)
  have R20 : PwRegs m n20 F out xp := R19.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k20 q h.2.2.2.2.2 h.2.2.2.2.1, rb20 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V20 : ∀ i, i < 10 → limbs n20.mem (F + BitVec.ofNat 32 0x2DC) i = pwT18 (limbs m.mem xp) i := fun i hi => by
    rw [w20 i hi, pow2kW_congr (x' := pwT17 (limbs m.mem xp)) (fun l hl => V19 l hl)]
    all_goals rfl
  -- call 21: mul -> pwT19
  obtain ⟨b21, cb21, ub21⟩ := St.block [.aluImm .add a1 sp 0x2DC, .aluImm .add a2 sp 0x214, .alu .add a0 x0 (8 : Fin 32)] u20.self hc20
    (off' := 0x12C) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub21
  have rb21 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b21 q = reg n20 q := fun q hv h0 h1 h2 => by
    rw [ub21.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n21, c21, u21, sp21, k21, w21, f21⟩ := mulCall out (F + BitVec.ofNat 32 0x2DC) (F + BitVec.ofNat 32 0x214) ub21.self hc20 inv20
    pw_at_12c pw_at_130 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [rb21 sp (by decide) (by decide) (by decide) (by decide)]; exact R20.1)
    (by rw [ub21.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R20.1, R20.2.1, R20.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u20.self.zero]; first | rfl | exact zw _))
    (by rw [ub21.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R20.1, R20.2.1, R20.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u20.self.zero]; first | rfl | exact zw _))
    (by rw [ub21.regs]; simp +decide only [upd_app, ↓reduceIte]; all_goals (try simp only [ev_add, R20.1, R20.2.1, R20.2.2.1])
        all_goals first | rfl | exact zw _ | (rw [u20.self.zero]; first | rfl | exact zw _))
    (env.hout) (tA 0x2DC (by decide)) (tA 0x214 (by decide)) (oC0) (oS0) (tS 0x2DC (by decide)) (tS 0x214 (by decide))
  have inv21 := invStep inv20 f21 (oIn0)
  have hc21 : CodeIn n21.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv21
  have slot21 : ∀ k, 0x444 ≤ k → k < 0x450 → n21.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => (f21 _ (gk k (by omega) h2) (oSl0 k (by omega))).trans (slot20 k h1 h2)
  have R21 : PwRegs m n21 F out xp := R20.tr fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ feMKeep q = true := by revert hq; revert q; decide
    rw [k21 q h.2.2.2.2.2 h.2.2.2.2.1, rb21 q h.1 h.2.1 h.2.2.1 h.2.2.2.1]
  have V21 : ∀ i, i < 10 → limbs n21.mem out i = pwT19 (limbs m.mem xp) i := fun i hi => by
    rw [w21 i hi, feMulW_congr (x' := pwT18 (limbs m.mem xp)) (y' := pwT13 (limbs m.mem xp))
      (fun l hl => V20 l hl)
      (fun l hl => by
        rw [tP 0x214 f20 (by decide) (tT 0x214 0x2DC (.inl (by decide)) (by decide) (by decide)) l hl, tP 0x214 f19 (by decide) (tT 0x214 0x2B4 (.inl (by decide)) (by decide) (by decide)) l hl, tP 0x214 f18 (by decide) (tT 0x214 0x28C (.inl (by decide)) (by decide) (by decide)) l hl, tP 0x214 f17 (by decide) (tT 0x214 0x264 (.inl (by decide)) (by decide) (by decide)) l hl, tP 0x214 f16 (by decide) (tT 0x214 0x23C (.inl (by decide)) (by decide) (by decide)) l hl]
        exact V15 l hl)]
    all_goals rfl
  have T3 : ∀ i, i < 10 → limbs n21.mem (F + BitVec.ofNat 32 0x84) i = pwT3 (limbs m.mem xp) i := fun i hi => by
    rw [tP 0x84 f21 (by decide) (tO0 0x84 (by decide)) i hi, tP 0x84 f20 (by decide) (tT 0x84 0x2DC (.inl (by decide)) (by decide) (by decide)) i hi, tP 0x84 f19 (by decide) (tT 0x84 0x2B4 (.inl (by decide)) (by decide) (by decide)) i hi, tP 0x84 f18 (by decide) (tT 0x84 0x28C (.inl (by decide)) (by decide) (by decide)) i hi, tP 0x84 f17 (by decide) (tT 0x84 0x264 (.inl (by decide)) (by decide) (by decide)) i hi, tP 0x84 f16 (by decide) (tT 0x84 0x23C (.inl (by decide)) (by decide) (by decide)) i hi, tP 0x84 f15 (by decide) (tT 0x84 0x214 (.inl (by decide)) (by decide) (by decide)) i hi, tP 0x84 f14 (by decide) (tT 0x84 0x1EC (.inl (by decide)) (by decide) (by decide)) i hi, tP 0x84 f13 (by decide) (tT 0x84 0x1C4 (.inl (by decide)) (by decide) (by decide)) i hi, tP 0x84 f12 (by decide) (tT 0x84 0x19C (.inl (by decide)) (by decide) (by decide)) i hi, tP 0x84 f11 (by decide) (tT 0x84 0x174 (.inl (by decide)) (by decide) (by decide)) i hi, tP 0x84 f10 (by decide) (tT 0x84 0x14C (.inl (by decide)) (by decide) (by decide)) i hi, tP 0x84 f9 (by decide) (tT 0x84 0x124 (.inl (by decide)) (by decide) (by decide)) i hi, tP 0x84 f8 (by decide) (tT 0x84 0xFC (.inl (by decide)) (by decide) (by decide)) i hi, tP 0x84 f7 (by decide) (tT 0x84 0xD4 (.inl (by decide)) (by decide) (by decide)) i hi, tP 0x84 f6 (by decide) (tT 0x84 0xAC (.inl (by decide)) (by decide) (by decide)) i hi]
    exact V5 i hi

  have oW28 : (out + 0x28).toNat + 40 < 2 ^ 32 := by
    rw [BitVec.toNat_add, show (0x28 : Word).toNat = 0x28 from rfl]; have := env.how; omega
  have oT0' : ∀ t, t < 40 → Sep (out + 0x28) 40 (out + BitVec.ofNat 32 t) 1 := fun t ht =>
    sep_offsets out (c := 0x28) (n := 40) (d := t) (k := 1) (.inr (by omega)) (by decide) (by omega)
  -- `memcpy(out + 0x28, t3, 40)`
  obtain ⟨b22, cb22, ub22⟩ := St.block [.aluImm .add a0 (8 : Fin 32) 0x28, .aluImm .add a1 sp 0x84,
    .aluImm .add a2 x0 0x28] u21.self hc21 (off' := 0x13E) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at ub22
  have rb22 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg b22 q = reg n21 q := fun q hv h0 h1 h2 => by
    rw [ub22.regs]; simp only [upd_ne hv h0, upd_ne hv h1, upd_ne hv h2]
  obtain ⟨n22a, c22a, pc22a, mem22a, regs22a⟩ := ub22.self.callRa hc21 pw_at_13e pw_at_142 (cb := P + 0x6440)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x6440 (by decide))
  have r22 := PEnv.reg1 regs22a ub22.self.zero
  have sp22a : reg n22a sp = F := by
    rw [r22 sp (by decide), rb22 sp (by decide) (by decide) (by decide) (by decide)]; exact R21.1
  obtain ⟨n22, c22, pc22, sp22, a022, f22, k22⟩ := memcpy_correct n22a (P + 0x6440) (P + BitVec.ofNat 32 (0x13E + 8))
    (out + 0x28) (F + BitVec.ofNat 32 0x84) 40 (by show CodeIn n22a.mem _ _; rw [mem22a]; exact cIn env.mcS sG.mcS env.sO.mcS inv21)
    (even_at P env.hP 0x6440 (by decide)) pc22a
    (by rw [r22 a0 (by decide), ub22.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [R21.2.1]; rfl)
    (by rw [r22 a1 (by decide), ub22.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [R21.1]; rfl)
    (by rw [r22 a2 (by decide), ub22.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [regs22a]; simp +decide [upd]) (even_clear _ (even_at P env.hP (0x13E + 8) (by decide)))
    (by
      rw [mem22a, sp22a, eFc]
      exact ⟨cIn env.mcB sG.mcB env.sO.mcB inv21, env.sO.mcB.sub (by decide), sG.mcB.sub (by decide),
        (sOG.sub (c := 0x28) (l := 40) (by decide)).subR (by decide),
        by rw [eFk]; exact offs (.inr (by omega)) (by decide) (by decide),
        (tO 0x84 0x28 (by decide) (by decide)).symm, aligned_add hGa (by decide),
        by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega, oW28, tW 0x84 (by decide)⟩)
  rw [mem22a, sp22a, eFc] at f22
  have frm : ∀ z, Sep G 0x140 z 1 → Sep (G + BitVec.ofNat 32 0x130) 16 z 1 := fun z h => h.sub (by decide)
  have inv22 : ∀ z, Sep G 0x450 z 1 → Sep out 0x50 z 1 → n22.mem z = m.mem z := fun z h1 h2 => by
    rw [f22 z (frm z (zg h1)), copyBytes_sep (dst := out + 0x28) (n := 40) (h2.sub (by decide)) (Nat.le_refl _),
      inv21 z h1 h2]
  have hc22 : CodeIn n22.mem P pow22501Code := cIn env.cod sG.c env.sO.c inv22
  have slot22 : ∀ k, 0x444 ≤ k → k < 0x450 → n22.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => by
      rw [f22 _ (frm _ (gk k (by omega) h2)), copyBytes_sep (dst := out + 0x28) (n := 40)
        ((sOG.sub (c := 0x28) (l := 40) (by decide)).subR (c := k) (l := 1) (by omega)) (Nat.le_refl _)]
      exact slot21 k h1 h2
  have R22 : PwRegs m n22 F out xp := R21.tr fun q hq => by
    by_cases hs : q = sp
    · subst hs; rw [sp22, sp22a]; exact R21.1.symm
    have h : q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧
        q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ ra ∧ q.val ≠ 0 ∧ q ≠ a0 := by
      revert hq; revert q; decide
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h15, h16, h17⟩ := h
    rw [k22 q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hs, r22 q h15, rb22 q h16 h17 h1 h2]
  have OUT : ∀ i, i < 10 → limbs n22.mem out i = pwT19 (limbs m.mem xp) i := fun i hi => by
    rw [← V21 i hi]
    exact memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, f22 _ (frm _ (oS0.sub (c := 4 * i + j) (l := 1) (by omega)).symm),
        copyBytes_sep (dst := out + 0x28) (n := 40) (oT0' (4 * i + j) (by omega)) (Nat.le_refl _)]
  have OUT3 : ∀ i, i < 10 → limbs n22.mem (out + 0x28) i = pwT3 (limbs m.mem xp) i := fun i hi => by
    rw [← T3 i hi]
    exact memLoad32_congr2 fun j hj => by
      rw [add_ofNat_assoc (out + 0x28) (4 * i) j, add_ofNat_assoc (F + BitVec.ofNat 32 0x84) (4 * i) j,
        f22 (out + 0x28 + BitVec.ofNat 32 (4 * i + j))
          (frm _ ((oS 0x28 (by decide)).sub (c := 4 * i + j) (l := 1) (by omega)).symm),
        apnCopyIn (by omega) (by decide)]
  -- the epilogue, from 0x146
  have u22 : St n22.mem P n22 0x146 (reg n22) := ⟨by rw [pc22], rfl, fun _ => rfl⟩
  obtain ⟨e1, de1, ue1⟩ := u22.aluImm hc22 pw_at_146 (off' := 0x148) (by decide)
  have rA : upd (reg n22) a0 (aluEval .add (reg n22 sp) 0x300) a0 = G + BitVec.ofNat 32 0x440 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, R22.1, eA]
  have hpsA : ∀ p ∈ pwPs, p.1 ≠ a0 := by decide
  obtain ⟨e2, ce2, ue2⟩ := St.block (restoreBlockR a0 pwPs) ue1 hc22 pwRestore_end
    (restoreBlockR_ok n22.mem _ a0 (by decide) pwPs _ rA hpsA fun q hq => by
      simp only [pwPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> exact aligned_add (aligned_add hGa (k := 0x440) (by decide)) (by decide))
  simp only [restoreBlockR_run n22.mem _ a0 (by decide) pwPs _ rA hpsA] at ue2
  obtain ⟨e3, de3, ue3⟩ := ue2.aluImm hc22 pw_at_150 (off' := 0x154) (by decide)
  obtain ⟨e4, de4, pc4, mem4, regs4⟩ := ue3.jalr hc22 pw_at_154
  have slotW : ∀ r o, (r, o) ∈ pwPs → memLoad32 n22.mem (G + BitVec.ofNat 32 0x440 + o) = reg m r := fun r o h => by
    have ho : 4 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x10 := by
      simp only [pwPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, add_ofNat_assoc, slot22 _ (by omega) (by omega)]
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs n22.mem (G + BitVec.ofNat 32 0x440) f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ pwPs →
      restoreRegs n22.mem (G + BitVec.ofNat 32 0x440) (upd (reg n22) a0 (aluEval .add (reg n22 sp) 0x300)) pwPs r =
        reg m r := fun r o hm => by
    simp only [pwPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  have rsp : restoreRegs n22.mem (G + BitVec.ofNat 32 0x440) (upd (reg n22) a0 (aluEval .add (reg n22 sp) 0x300))
      pwPs sp = F := by
    rw [rr _ _ sp (by decide) (by decide), upd_ne (by decide) (by decide)]; exact R22.1
  have S : Steps m n22 := by
    have S0 : Steps m m3 := .cons d1 (.cons d2 (cp3.trans cp4))
    exact S0.trans (cb1.trans (c1.trans (cb2.trans (c2.trans (cb3.trans (c3.trans (cb4.trans (c4.trans (cb5.trans
      (c5.trans (cb6.trans (c6.trans (cb7.trans (c7.trans (cb8.trans (c8.trans (cb9.trans (c9.trans (cb10.trans
      (c10.trans (cb11.trans (c11.trans (cb12.trans (c12.trans (cb13.trans (c13.trans (cb14.trans (c14.trans
      (cb15.trans (c15.trans (cb16.trans (c16.trans (cb17.trans (c17.trans (cb18.trans (c18.trans (cb19.trans
      (c19.trans (cb20.trans (c20.trans (cb21.trans (c21.trans (cb22.trans (c22a.trans
      (c22)))))))))))))))))))))))))))))))))))))))))))))
  refine ⟨e4, S.trans (.cons de1 (ce2.trans (.cons de3 (.single de4)))), ?_, ?_, fun q hq => ?_,
    fun i hi => ?_, fun x hx ho => ?_⟩
  · rw [pc4]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0xC (by decide), hra, add_lit_zero, hret]
  · rw [regs4]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp, eS]
  · rw [regs4]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨
        (q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧
          q ≠ a0 ∧ (∀ p ∈ pwPs, p.1 ≠ q)) := by decide
    rcases key q hq with rfl | rfl | rfl | ⟨h1, h0, hs, ha, hps⟩
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0xC (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x8 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x4 (by decide)
    · rw [upd_ne h0 hs, rr _ _ q h0 hps, upd_ne h0 ha]; exact R22.2.2.2 q h1
  · rw [mem4]; exact ⟨OUT i hi, OUT3 i hi⟩
  · rw [mem4]; exact inv22 x hx ho

end C3.RV32
