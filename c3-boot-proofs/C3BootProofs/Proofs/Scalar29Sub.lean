import C3BootProofs.Proofs.Leaves
import C3BootProofs.Proofs.Fe25519
import C3BootProofs.Proofs.MemcpyAny
import C3BootProofs.Proofs.Block
import C3BootProofs.Proofs.Sha256LoopBlocks
import C3BootProofs.Proofs.FeMul
import C3BootProofs.Proofs.FeAdd

/-!
# `curve25519_dalek`'s `Scalar29::sub(a, &L)`, as compiled

The image has one copy of `Scalar29::sub`, with its second operand fixed to
`constants::L`, the order of Ed25519's base point, which it reads from the
image's data. It zeroes a frame copy of the result with `memset`, subtracts
`L` limb by limb with the borrow in each word's top bit, passes the last
borrow through `black_box` to select `L` or zero, adds that back limb by limb
(`conditional_add_l`), and copies the result out with `memcpy`. Each limb
access is a call to `<Scalar29 as Index<usize>>::index` or `index_mut`, which
return the address of limb `i` of the nine and panic past the last.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem six_at_0 : fetchRel scalar29IndexCode 0x0 = some (.alu .add a2 x0 a1, 2) := by decide
theorem six_at_2 : fetchRel scalar29IndexCode 0x2 = some (.aluImm .add a1 x0 0x8, 2) := by decide
theorem six_at_4 : fetchRel scalar29IndexCode 0x4 = some (.branch .bltu a1 a2 0xA, 4) := by decide
theorem six_at_8 : fetchRel scalar29IndexCode 0x8 = some (.aluImm .sll a2 a2 0x2, 2) := by decide
theorem six_at_a : fetchRel scalar29IndexCode 0xA = some (.alu .add a0 a0 a2, 2) := by decide
theorem six_at_c : fetchRel scalar29IndexCode 0xC = some (.jalr x0 ra 0x0, 2) := by decide
theorem six_at_e : fetchRel scalar29IndexCode 0xE = some (.aluImm .add a1 x0 0x9, 2) := by decide
theorem six_at_10 : fetchRel scalar29IndexCode 0x10 = some (.alu .add a0 x0 a2, 2) := by decide
theorem six_at_12 : fetchRel scalar29IndexCode 0x12 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem six_at_16 : fetchRel scalar29IndexCode 0x16 = some (.jalr ra ra 0x3D4, 4) := by decide
theorem sixm_at_0 : fetchRel scalar29IndexMutCode 0x0 = some (.alu .add a2 x0 a1, 2) := by decide
theorem sixm_at_2 : fetchRel scalar29IndexMutCode 0x2 = some (.aluImm .add a1 x0 0x8, 2) := by decide
theorem sixm_at_4 : fetchRel scalar29IndexMutCode 0x4 = some (.branch .bltu a1 a2 0xA, 4) := by decide
theorem sixm_at_8 : fetchRel scalar29IndexMutCode 0x8 = some (.aluImm .sll a2 a2 0x2, 2) := by decide
theorem sixm_at_a : fetchRel scalar29IndexMutCode 0xA = some (.alu .add a0 a0 a2, 2) := by decide
theorem sixm_at_c : fetchRel scalar29IndexMutCode 0xC = some (.jalr x0 ra 0x0, 2) := by decide
theorem sixm_at_e : fetchRel scalar29IndexMutCode 0xE = some (.aluImm .add a1 x0 0x9, 2) := by decide
theorem sixm_at_10 : fetchRel scalar29IndexMutCode 0x10 = some (.alu .add a0 x0 a2, 2) := by decide
theorem sixm_at_12 : fetchRel scalar29IndexMutCode 0x12 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem sixm_at_16 : fetchRel scalar29IndexMutCode 0x16 = some (.jalr ra ra 0x3BA, 4) := by decide
theorem ssub_at_0 : fetchRel scalar29SubCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFB0, 2) := by decide
theorem ssub_at_2 : fetchRel scalar29SubCode 0x2 = some (.store .sw sp ra 0x4C, 2) := by decide
theorem ssub_at_4 : fetchRel scalar29SubCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x48, 2) := by decide
theorem ssub_at_6 : fetchRel scalar29SubCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x44, 2) := by decide
theorem ssub_at_8 : fetchRel scalar29SubCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x40, 2) := by decide
theorem ssub_at_a : fetchRel scalar29SubCode 0xA = some (.store .sw sp (19 : Fin 32) 0x3C, 2) := by decide
theorem ssub_at_c : fetchRel scalar29SubCode 0xC = some (.store .sw sp (20 : Fin 32) 0x38, 2) := by decide
theorem ssub_at_e : fetchRel scalar29SubCode 0xE = some (.store .sw sp (21 : Fin 32) 0x34, 2) := by decide
theorem ssub_at_10 : fetchRel scalar29SubCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x30, 2) := by decide
theorem ssub_at_12 : fetchRel scalar29SubCode 0x12 = some (.store .sw sp (23 : Fin 32) 0x2C, 2) := by decide
theorem ssub_at_14 : fetchRel scalar29SubCode 0x14 = some (.store .sw sp (24 : Fin 32) 0x28, 2) := by decide
theorem ssub_at_16 : fetchRel scalar29SubCode 0x16 = some (.alu .add (21 : Fin 32) x0 a1, 2) := by decide
theorem ssub_at_18 : fetchRel scalar29SubCode 0x18 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem ssub_at_1a : fetchRel scalar29SubCode 0x1A = some (.lui (20 : Fin 32) 0x20000000, 4) := by decide
theorem ssub_at_1e : fetchRel scalar29SubCode 0x1E = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem ssub_at_20 : fetchRel scalar29SubCode 0x20 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem ssub_at_22 : fetchRel scalar29SubCode 0x22 = some (.aluImm .add a2 x0 0x24, 4) := by decide
theorem ssub_at_26 : fetchRel scalar29SubCode 0x26 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem ssub_at_28 : fetchRel scalar29SubCode 0x28 = some (.auipc ra 0x6000, 4) := by decide
theorem ssub_at_2c : fetchRel scalar29SubCode 0x2C = some (.jalr ra ra 0xFFFFFB74, 4) := by decide
theorem ssub_at_30 : fetchRel scalar29SubCode 0x30 = some (.aluImm .add (8 : Fin 32) x0 0x0, 2) := by decide
theorem ssub_at_32 : fetchRel scalar29SubCode 0x32 = some (.aluImm .add (24 : Fin 32) x0 0x0, 2) := by decide
theorem ssub_at_34 : fetchRel scalar29SubCode 0x34 = some (.aluImm .add (22 : Fin 32) x0 0x9, 2) := by decide
theorem ssub_at_36 : fetchRel scalar29SubCode 0x36 = some (.lui (19 : Fin 32) 0x3FCC5000, 4) := by decide
theorem ssub_at_3a : fetchRel scalar29SubCode 0x3A = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0xFFFFFA08, 4) := by decide
theorem ssub_at_3e : fetchRel scalar29SubCode 0x3E = some (.branch .beq (22 : Fin 32) x0 0x46, 4) := by decide
theorem ssub_at_42 : fetchRel scalar29SubCode 0x42 = some (.aluImm .add (23 : Fin 32) (8 : Fin 32) 0x1, 4) := by decide
theorem ssub_at_46 : fetchRel scalar29SubCode 0x46 = some (.alu .add a0 x0 (21 : Fin 32), 2) := by decide
theorem ssub_at_48 : fetchRel scalar29SubCode 0x48 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem ssub_at_4a : fetchRel scalar29SubCode 0x4A = some (.auipc ra 0x0, 4) := by decide
theorem ssub_at_4e : fetchRel scalar29SubCode 0x4E = some (.jalr ra ra 0x22E, 4) := by decide
theorem ssub_at_52 : fetchRel scalar29SubCode 0x52 = some (.load .lw (9 : Fin 32) a0 0x0, 2) := by decide
theorem ssub_at_54 : fetchRel scalar29SubCode 0x54 = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem ssub_at_56 : fetchRel scalar29SubCode 0x56 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem ssub_at_58 : fetchRel scalar29SubCode 0x58 = some (.auipc ra 0x0, 4) := by decide
theorem ssub_at_5c : fetchRel scalar29SubCode 0x5C = some (.jalr ra ra 0x220, 4) := by decide
theorem ssub_at_60 : fetchRel scalar29SubCode 0x60 = some (.load .lw a0 a0 0x0, 2) := by decide
theorem ssub_at_62 : fetchRel scalar29SubCode 0x62 = some (.aluImm .sra a1 (24 : Fin 32) 0x1F, 4) := by decide
theorem ssub_at_66 : fetchRel scalar29SubCode 0x66 = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem ssub_at_68 : fetchRel scalar29SubCode 0x68 = some (.alu .sub (24 : Fin 32) a1 a0, 4) := by decide
theorem ssub_at_6c : fetchRel scalar29SubCode 0x6C = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem ssub_at_6e : fetchRel scalar29SubCode 0x6E = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem ssub_at_70 : fetchRel scalar29SubCode 0x70 = some (.auipc ra 0x0, 4) := by decide
theorem ssub_at_74 : fetchRel scalar29SubCode 0x74 = some (.jalr ra ra 0x222, 4) := by decide
theorem ssub_at_78 : fetchRel scalar29SubCode 0x78 = some (.alu .and a1 (24 : Fin 32) (20 : Fin 32), 4) := by decide
theorem ssub_at_7c : fetchRel scalar29SubCode 0x7C = some (.store .sw a0 a1 0x0, 2) := by decide
theorem ssub_at_7e : fetchRel scalar29SubCode 0x7E = some (.alu .add (8 : Fin 32) x0 (23 : Fin 32), 2) := by decide
theorem ssub_at_80 : fetchRel scalar29SubCode 0x80 = some (.branch .bne (23 : Fin 32) (22 : Fin 32) 0xFFFFFFC2, 4) := by decide
theorem ssub_at_84 : fetchRel scalar29SubCode 0x84 = some (.aluImm .srl a0 (24 : Fin 32) 0x1F, 4) := by decide
theorem ssub_at_88 : fetchRel scalar29SubCode 0x88 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem ssub_at_8c : fetchRel scalar29SubCode 0x8C = some (.jalr ra ra 0xFFFFFA72, 4) := by decide
theorem ssub_at_90 : fetchRel scalar29SubCode 0x90 = some (.aluImm .add (9 : Fin 32) x0 0x0, 2) := by decide
theorem ssub_at_92 : fetchRel scalar29SubCode 0x92 = some (.aluImm .add (8 : Fin 32) x0 0x0, 2) := by decide
theorem ssub_at_94 : fetchRel scalar29SubCode 0x94 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem ssub_at_98 : fetchRel scalar29SubCode 0x98 = some (.alu .sub (22 : Fin 32) x0 a0, 4) := by decide
theorem ssub_at_9c : fetchRel scalar29SubCode 0x9C = some (.aluImm .add (21 : Fin 32) x0 0x9, 2) := by decide
theorem ssub_at_9e : fetchRel scalar29SubCode 0x9E = some (.lui (19 : Fin 32) 0x3FCC5000, 4) := by decide
theorem ssub_at_a2 : fetchRel scalar29SubCode 0xA2 = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0xFFFFFA08, 4) := by decide
theorem ssub_at_a6 : fetchRel scalar29SubCode 0xA6 = some (.branch .beq (21 : Fin 32) x0 0x48, 4) := by decide
theorem ssub_at_aa : fetchRel scalar29SubCode 0xAA = some (.aluImm .add (23 : Fin 32) (9 : Fin 32) 0x1, 4) := by decide
theorem ssub_at_ae : fetchRel scalar29SubCode 0xAE = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem ssub_at_b0 : fetchRel scalar29SubCode 0xB0 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem ssub_at_b2 : fetchRel scalar29SubCode 0xB2 = some (.auipc ra 0x0, 4) := by decide
theorem ssub_at_b6 : fetchRel scalar29SubCode 0xB6 = some (.jalr ra ra 0x1C6, 4) := by decide
theorem ssub_at_ba : fetchRel scalar29SubCode 0xBA = some (.aluImm .srl (24 : Fin 32) (8 : Fin 32) 0x1D, 4) := by decide
theorem ssub_at_be : fetchRel scalar29SubCode 0xBE = some (.load .lw a0 a0 0x0, 2) := by decide
theorem ssub_at_c0 : fetchRel scalar29SubCode 0xC0 = some (.alu .and (8 : Fin 32) a0 (22 : Fin 32), 4) := by decide
theorem ssub_at_c4 : fetchRel scalar29SubCode 0xC4 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem ssub_at_c6 : fetchRel scalar29SubCode 0xC6 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem ssub_at_c8 : fetchRel scalar29SubCode 0xC8 = some (.auipc ra 0x0, 4) := by decide
theorem ssub_at_cc : fetchRel scalar29SubCode 0xCC = some (.jalr ra ra 0x1B0, 4) := by decide
theorem ssub_at_d0 : fetchRel scalar29SubCode 0xD0 = some (.load .lw a0 a0 0x0, 2) := by decide
theorem ssub_at_d2 : fetchRel scalar29SubCode 0xD2 = some (.alu .add a0 a0 (24 : Fin 32), 2) := by decide
theorem ssub_at_d4 : fetchRel scalar29SubCode 0xD4 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a0, 2) := by decide
theorem ssub_at_d6 : fetchRel scalar29SubCode 0xD6 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem ssub_at_d8 : fetchRel scalar29SubCode 0xD8 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem ssub_at_da : fetchRel scalar29SubCode 0xDA = some (.auipc ra 0x0, 4) := by decide
theorem ssub_at_de : fetchRel scalar29SubCode 0xDE = some (.jalr ra ra 0x1B8, 4) := by decide
theorem ssub_at_e2 : fetchRel scalar29SubCode 0xE2 = some (.alu .and a1 (8 : Fin 32) (20 : Fin 32), 4) := by decide
theorem ssub_at_e6 : fetchRel scalar29SubCode 0xE6 = some (.store .sw a0 a1 0x0, 2) := by decide
theorem ssub_at_e8 : fetchRel scalar29SubCode 0xE8 = some (.alu .add (9 : Fin 32) x0 (23 : Fin 32), 2) := by decide
theorem ssub_at_ea : fetchRel scalar29SubCode 0xEA = some (.branch .bne (23 : Fin 32) (21 : Fin 32) 0xFFFFFFC0, 4) := by decide
theorem ssub_at_ee : fetchRel scalar29SubCode 0xEE = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem ssub_at_f0 : fetchRel scalar29SubCode 0xF0 = some (.aluImm .add a2 x0 0x24, 4) := by decide
theorem ssub_at_f4 : fetchRel scalar29SubCode 0xF4 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem ssub_at_f6 : fetchRel scalar29SubCode 0xF6 = some (.auipc ra 0x6000, 4) := by decide
theorem ssub_at_fa : fetchRel scalar29SubCode 0xFA = some (.jalr ra ra 0xFFFFFB0E, 4) := by decide
theorem ssub_at_fe : fetchRel scalar29SubCode 0xFE = some (.load .lw ra sp 0x4C, 2) := by decide
theorem ssub_at_100 : fetchRel scalar29SubCode 0x100 = some (.load .lw (8 : Fin 32) sp 0x48, 2) := by decide
theorem ssub_at_102 : fetchRel scalar29SubCode 0x102 = some (.load .lw (9 : Fin 32) sp 0x44, 2) := by decide
theorem ssub_at_104 : fetchRel scalar29SubCode 0x104 = some (.load .lw (18 : Fin 32) sp 0x40, 2) := by decide
theorem ssub_at_106 : fetchRel scalar29SubCode 0x106 = some (.load .lw (19 : Fin 32) sp 0x3C, 2) := by decide
theorem ssub_at_108 : fetchRel scalar29SubCode 0x108 = some (.load .lw (20 : Fin 32) sp 0x38, 2) := by decide
theorem ssub_at_10a : fetchRel scalar29SubCode 0x10A = some (.load .lw (21 : Fin 32) sp 0x34, 2) := by decide
theorem ssub_at_10c : fetchRel scalar29SubCode 0x10C = some (.load .lw (22 : Fin 32) sp 0x30, 2) := by decide
theorem ssub_at_10e : fetchRel scalar29SubCode 0x10E = some (.load .lw (23 : Fin 32) sp 0x2C, 2) := by decide
theorem ssub_at_110 : fetchRel scalar29SubCode 0x110 = some (.load .lw (24 : Fin 32) sp 0x28, 2) := by decide
theorem ssub_at_112 : fetchRel scalar29SubCode 0x112 = some (.aluImm .add sp sp 0x50, 2) := by decide
theorem ssub_at_114 : fetchRel scalar29SubCode 0x114 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- `constants::L`, the order of Ed25519's base point, as nine 29-bit limbs. -/
def scalarL : List Nat := [0x1cf5d3ed, 0x009318d2, 0x1de73596, 0x1df3bd45, 0x0000014d, 0, 0, 0, 0x00100000]

/-- `Scalar29::sub(a, &L)`'s first loop on naturals: the `borrow` word after
`i` limbs, each `wrapping_sub` modulo 2^32. -/
def s29Borrow (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => (a i + 2 ^ 32 - (scalarL.getD i 0 + s29Borrow a i / 2 ^ 31) % 2 ^ 32) % 2 ^ 32

/-- `conditional_add_l`'s `carry` after `i` limbs: the difference's limbs,
plus `L`'s when `c = 1`, carried 29 bits at a time. -/
def s29Carry (a : Nat → Nat) (c : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 =>
    (s29Carry a c i / 2 ^ 29 + s29Borrow a (i + 1) % 2 ^ 29 + (if c = 1 then scalarL.getD i 0 else 0)) % 2 ^ 32

/-- `Scalar29::sub(a, &L)`'s limb `j`: `a - L` limb by limb, and `L` added
back when the subtraction borrowed. -/
def s29Out (a : Nat → Nat) (j : Nat) : Nat := s29Carry a (s29Borrow a 9 / 2 ^ 31) (j + 1) % 2 ^ 29

/-- Where `Scalar29::sub(a, &L)` runs: its code and its callees' at their
offsets, `L` in the image's data, the 0x60 bytes of stack at `G` below the
caller's `sp` that it and its callees use, the result `out`, and `a` at
`ap`, each apart from what it must not touch. `a` may overlap `out`: the
function reads `a` before it writes `out`. -/
structure SSEnv (M : Word → BitVec 8) (P G out ap : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P scalar29SubCode
  idx : CodeIn M (P + 0x278) scalar29IndexCode
  idxm : CodeIn M (P + 0x292) scalar29IndexMutCode
  mset : CodeIn M (P + 0x5B9C) memsetCode
  stub : CodeIn M (P + 0x5C04) memcpyStubCode
  body : CodeIn M (P + 0x5C0C) memcpyBodyCode
  bb : CodeIn M (P + 0xFFFFEAFA) blackBoxU8Code
  ldata : CodeIn M (BitVec.ofNat 32 scalarLAddress) scalarLData
  hG : G.toNat % 4 = 0
  hGt : G.toNat + 0x60 ≤ 2 ^ 32
  hout : out.toNat % 4 = 0
  hot : out.toNat + 36 < 2 ^ 32
  hap : ap.toNat % 4 = 0
  sGC : Sep G 0x60 P scalar29SubCode.length
  sGI : Sep G 0x60 (P + 0x278) scalar29IndexCode.length
  sGIM : Sep G 0x60 (P + 0x292) scalar29IndexMutCode.length
  sGM : Sep G 0x60 (P + 0x5B9C) memsetCode.length
  sGS : Sep G 0x60 (P + 0x5C04) memcpyStubCode.length
  sGB : Sep G 0x60 (P + 0x5C0C) memcpyBodyCode.length
  sGBB : Sep G 0x60 (P + 0xFFFFEAFA) blackBoxU8Code.length
  sGL : Sep G 0x60 (BitVec.ofNat 32 scalarLAddress) 36
  sAG : Sep ap 36 G 0x60
  sOG : Sep out 36 G 0x60
  sOC : Sep out 36 P scalar29SubCode.length
  sOB : Sep out 36 (P + 0x5C0C) memcpyBodyCode.length

/-- The index code, shared by `index` and `index_mut`: for `i < 9`, `a0`
becomes `p + 4 i`. -/
theorem s29_index {code : List Nat} (h0 : fetchRel code 0x0 = some (.alu .add a2 x0 a1, 2))
    (h2 : fetchRel code 0x2 = some (.aluImm .add a1 x0 0x8, 2))
    (h4 : fetchRel code 0x4 = some (.branch .bltu a1 a2 0xA, 4))
    (h8 : fetchRel code 0x8 = some (.aluImm .sll a2 a2 0x2, 2))
    (ha : fetchRel code 0xA = some (.alu .add a0 a0 a2, 2)) (hcr : fetchRel code 0xC = some (.jalr x0 ra 0x0, 2))
    (m : Machine) {base retAddr p : Word} {i : Nat} (hc : CodeIn m.mem base code) (hpc : m.pc = base)
    (ha0 : reg m a0 = p) (ha1 : reg m a1 = BitVec.ofNat 32 i) (hi : i < 9) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' a0 = p + BitVec.ofNat 32 (4 * i) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.alu hc h0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.aluImm hc h2 (off' := 4) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.notTaken hc 0x8 h4 (by decide) (by
    simp +decide only [upd_app, ↓reduceIte]; rw [hz, ha1]
    show (BitVec.ult (aluEval .add 0 0x8) (aluEval .add 0 (BitVec.ofNat 32 i))) = false
    exact decide_eq_false (by
      show ¬ (8 : Nat) < (0 + BitVec.ofNat 32 i).toNat
      rw [zw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega))
  obtain ⟨n4, d4, u4⟩ := u3.aluImm hc h8 (off' := 0xA) (by decide)
  obtain ⟨n5, d5, u5⟩ := u4.alu hc ha (off' := 0xC) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hc hcr
  refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), ?_, ?_, fun r h0' h1 h2' => ?_, mem6⟩
  · rw [pc6]; simp +decide only [upd_app, ↓reduceIte]; rw [hra, add_lit_zero, hret]
  · rw [regs6]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0, hz, ha1]
    apply BitVec.eq_of_toNat_eq
    show (p + ((0 + BitVec.ofNat 32 i) <<< (2 % 32))).toNat = (p + BitVec.ofNat 32 (4 * i)).toNat
    rw [zw, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq, show (2 ^ (2 % 32) : Nat) = 4 from rfl]
    congr 1; omega
  · rw [regs6]
    by_cases hr0 : r.val = 0
    · have : r = 0 := Fin.ext hr0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, hr0, h0', h1, h2', ite_false]

theorem scalar29Index_correct (m : Machine) {base retAddr p : Word} {i : Nat}
    (hc : CodeIn m.mem base scalar29IndexCode) (hpc : m.pc = base) (ha0 : reg m a0 = p)
    (ha1 : reg m a1 = BitVec.ofNat 32 i) (hi : i < 9) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' a0 = p + BitVec.ofNat 32 (4 * i) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m' r = reg m r) ∧ m'.mem = m.mem :=
  s29_index six_at_0 six_at_2 six_at_4 six_at_8 six_at_a six_at_c m hc hpc ha0 ha1 hi hra hret

theorem scalar29IndexMut_correct (m : Machine) {base retAddr p : Word} {i : Nat}
    (hc : CodeIn m.mem base scalar29IndexMutCode) (hpc : m.pc = base) (ha0 : reg m a0 = p)
    (ha1 : reg m a1 = BitVec.ofNat 32 i) (hi : i < 9) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' a0 = p + BitVec.ofNat 32 (4 * i) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m' r = reg m r) ∧ m'.mem = m.mem :=
  s29_index sixm_at_0 sixm_at_2 sixm_at_4 sixm_at_8 sixm_at_a sixm_at_c m hc hpc ha0 ha1 hi hra hret

theorem sra31_eq (w : Word) : aluEval .sra w 31 = if w.toNat < 2 ^ 31 then 0 else 0xFFFFFFFF := by
  show BitVec.ofInt 32 (w.toInt >>> (31 % 32)) = _
  unfold BitVec.toInt
  have hw := w.isLt
  by_cases h : w.toNat < 2 ^ 31
  · rw [ite_eq_left (show 2 * w.toNat < 2 ^ 32 by omega), ite_eq_left h]
    have e : ((w.toNat : Int) >>> (31 % 32)) = ((w.toNat >>> 31 : Nat) : Int) := rfl
    rw [e, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]; rfl
  · rw [ite_eq_right (show ¬ 2 * w.toNat < 2 ^ 32 by omega), ite_eq_right h]
    have e : ((w.toNat : Int) - ((2 ^ 32 : Nat) : Int)) = Int.negSucc (2 ^ 32 - 1 - w.toNat) := by
      rw [Int.negSucc_eq]; omega
    rw [e]
    show BitVec.ofInt 32 (Int.negSucc ((2 ^ 32 - 1 - w.toNat) >>> 31)) = _
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)]; rfl

/-- The first loop's step on words: `a[i] - (L[i] + (borrow >> 31))`, with the
borrow's top bit taken by an arithmetic shift. -/
theorem s29_borrow_tn (b x y : Word) :
    (aluEval .sub (aluEval .add (aluEval .sra b 31) x) y).toNat =
      (x.toNat + 2 ^ 32 - (y.toNat + b.toNat / 2 ^ 31) % 2 ^ 32) % 2 ^ 32 := by
  rw [sra31_eq]
  have hx := x.isLt; have hy := y.isLt; have hb := b.isLt
  show (_ - y).toNat = _
  rw [BitVec.toNat_sub]
  by_cases h : b.toNat < 2 ^ 31
  · rw [ite_eq_left h]; show (2 ^ 32 - y.toNat + (0 + x).toNat) % 2 ^ 32 = _
    rw [BitVec.toNat_add, show (0 : Word).toNat = 0 from rfl, Nat.div_eq_of_lt h]; omega
  · rw [ite_eq_right h]; show (2 ^ 32 - y.toNat + (0xFFFFFFFF + x).toNat) % 2 ^ 32 = _
    rw [BitVec.toNat_add, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl,
      show b.toNat / 2 ^ 31 = 1 by omega]; omega

theorem and29_tn (w : Word) : (aluEval .and w 0x1FFFFFFF).toNat = w.toNat % 2 ^ 29 :=
  and_low (by decide) (by decide)

/-- `L`'s limb `i`, read from the image's data. -/
theorem scalarL_word {M : Word → BitVec 8} {Lb : Word} (h : CodeIn M Lb scalarLData) {i : Nat} (hi : i < 9) :
    memLoad32 M (Lb + BitVec.ofNat 32 (4 * i)) = BitVec.ofNat 32 (scalarL.getD i 0) := by
  have e : ∀ c, c < 4 → M (Lb + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 c) = byteAt scalarLData (4 * i + c) :=
    fun c hc => by rw [add_ofNat_assoc]; exact h (4 * i + c) (by show _ < 36; omega)
  unfold memLoad32
  rw [show (3 : Word) = BitVec.ofNat 32 3 from rfl, show (2 : Word) = BitVec.ofNat 32 2 from rfl,
    show (1 : Word) = BitVec.ofNat 32 1 from rfl, e 3 (by decide), e 2 (by decide), e 1 (by decide),
    show Lb + BitVec.ofNat 32 (4 * i) = Lb + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0 from
      (add_ofNat_zero _).symm, e 0 (by decide)]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A call of `index` or `index_mut` from `off`: `a0` becomes `p + 4 i`, and
only `ra`, `a0`, `a1`, and `a2` change. -/
theorem ss_idx {code idx : List Nat} {M : Word → BitVec 8} {P c : Word} {n : Machine} {off : Nat}
    {f : Fin 32 → Word} (s : St M P n off f) (hc : CodeIn M P code) {imm o : Word}
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + c) (hP : P.toNat % 2 = 0) (hoff : off % 2 = 0)
    (hce : (P + c).toNat % 2 = 0) (hidx : CodeIn M (P + c) idx)
    (i0 : fetchRel idx 0x0 = some (.alu .add a2 x0 a1, 2)) (i2 : fetchRel idx 0x2 = some (.aluImm .add a1 x0 0x8, 2))
    (i4 : fetchRel idx 0x4 = some (.branch .bltu a1 a2 0xA, 4)) (i8 : fetchRel idx 0x8 = some (.aluImm .sll a2 a2 0x2, 2))
    (ia : fetchRel idx 0xA = some (.alu .add a0 a0 a2, 2)) (icr : fetchRel idx 0xC = some (.jalr x0 ra 0x0, 2))
    {p : Word} {i : Nat} (ha0 : f a0 = p) (ha1 : f a1 = BitVec.ofNat 32 i) (hi : i < 9) :
    ∃ n', Steps n n' ∧ St M P n' (off + 8) (reg n') ∧ reg n' a0 = p + BitVec.ofNat 32 (4 * i) ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ ra → reg n' r = f r := by
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb hce
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨m2, c2, pc2, a02, k2, mem2⟩ := s29_index i0 i2 i4 i8 ia icr m1 (by rw [mem1]; exact hidx) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) hi (by rw [regs1]; simp [upd])
    (even_clear _ (even_at P hP (off + 8) (by omega)))
  exact ⟨m2, c1.trans c2, ⟨pc2, by rw [mem2, mem1], fun _ => rfl⟩, a02,
    fun r h0 h1' h2' h3 => by rw [k2 r h0 h1' h2', r1 r h3]⟩

/-- The first loop, from 0x42 to 0x4A: the next index, and `index(a, i)`'s arguments. -/
def ssA : List BInstr := [.aluImm .add (23 : Fin 32) (8 : Fin 32) 0x1, .alu .add a0 x0 (21 : Fin 32), .alu .add a1 x0 (8 : Fin 32)]
/-- From 0x52 to 0x58: `a[i]`, and `index(L, i)`'s arguments. -/
def ssB : List BInstr := [.lw (9 : Fin 32) a0 0x0, .alu .add a0 x0 (19 : Fin 32), .alu .add a1 x0 (8 : Fin 32)]
/-- From 0x60 to 0x70: the borrow word, and `index_mut(difference, i)`'s arguments. -/
def ssC : List BInstr :=
  [.lw a0 a0 0x0, .aluImm .sra a1 (24 : Fin 32) 0x1F, .alu .add a1 a1 (9 : Fin 32), .alu .sub (24 : Fin 32) a1 a0,
   .aluImm .add a0 sp 0x4, .alu .add a1 x0 (8 : Fin 32)]
/-- From 0x78 to 0x80: the limb's low 29 bits to `difference[i]`. -/
def ssD : List BInstr := [.alu .and a1 (24 : Fin 32) (20 : Fin 32), .sw a0 a1 0x0, .alu .add (8 : Fin 32) x0 (23 : Fin 32)]

section
set_option maxRecDepth 20000
theorem ssA_end : blockEnd scalar29SubCode 0x42 ssA = some 0x4A := by decide
theorem ssB_end : blockEnd scalar29SubCode 0x52 ssB = some 0x58 := by decide
theorem ssC_end : blockEnd scalar29SubCode 0x60 ssC = some 0x70 := by decide
theorem ssD_end : blockEnd scalar29SubCode 0x78 ssD = some 0x80 := by decide
end

/-- `a`'s limb `i - L`'s limb `i - (borrow >> 31)`, as the compiled code computes it. -/
abbrev ssB1 (b x y : Word) : Word := aluEval .sub (aluEval .add (aluEval .sra b 31) x) y

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- One pass of the first loop, from 0x42 to the branch at 0x80. -/
theorem ss_body1 {M : Word → BitVec 8} {P F ap Lb : Word} {n : Machine} (hP : P.toNat % 2 = 0)
    (hc : CodeIn M P scalar29SubCode) (hi1 : CodeIn M (P + 0x278) scalar29IndexCode)
    (hi2 : CodeIn M (P + 0x292) scalar29IndexMutCode) (s : St M P n 0x42 (reg n)) {i : Nat} (hi : i < 9)
    (h8 : reg n 8 = BitVec.ofNat 32 i) (h21 : reg n 21 = ap) (h19 : reg n 19 = Lb) (hsp : reg n sp = F)
    (hF : F.toNat % 4 = 0) (hap : ap.toNat % 4 = 0) (hLb : Lb.toNat % 4 = 0)
    (sWC : Sep (F + 4 + BitVec.ofNat 32 (4 * i)) 4 P scalar29SubCode.length) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (F + 4 + BitVec.ofNat 32 (4 * i)) (aluEval .and (ssB1 (reg n 24)
        (memLoad32 M (ap + BitVec.ofNat 32 (4 * i))) (memLoad32 M (Lb + BitVec.ofNat 32 (4 * i)))) (reg n 20)))
        P n' 0x80 (reg n') ∧
      reg n' 24 = ssB1 (reg n 24) (memLoad32 M (ap + BitVec.ofNat 32 (4 * i))) (memLoad32 M (Lb + BitVec.ofNat 32 (4 * i))) ∧
      reg n' 23 = BitVec.ofNat 32 (i + 1) ∧ reg n' 8 = BitVec.ofNat 32 (i + 1) ∧
      ∀ q : Fin 32, q.val ∉ [1, 8, 9, 10, 11, 12, 23, 24] → reg n' q = reg n q := by
  have hz := s.zero
  have nq : ∀ q : Fin 32, q.val ∉ [1, 8, 9, 10, 11, 12, 23, 24] → ∀ r : Fin 32, r.val ∈ [1, 8, 9, 10, 11, 12, 23, 24] →
      q ≠ r := fun q hq r hr e => hq (e ▸ hr)
  obtain ⟨n1, c1, u1⟩ := St.block ssA s hc ssA_end (by simp [BlockOk, BInstr.ok, ssA])
  simp only [runBlock, BInstr.run, ssA] at u1
  obtain ⟨n2, c2, u2, a02, k2⟩ := ss_idx u1 hc ssub_at_4a ssub_at_4e (c := 0x278) (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    hP (by decide) (even_at P hP 0x278 (by decide)) hi1 six_at_0 six_at_2 six_at_4 six_at_8 six_at_a six_at_c
    (p := ap) (i := i) (by simp +decide only [upd_app, ↓reduceIte]; rw [h21]; exact zw _)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [h8]; exact zw _) hi
  have b2 : ∀ q : Fin 32, q.val ∉ [1, 10, 11, 12, 23] → reg n2 q = reg n q := fun q hq => by
    have nq' : ∀ r : Fin 32, r.val ∈ [1, 10, 11, 12, 23] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [k2 q (nq' a0 (by decide)) (nq' a1 (by decide)) (nq' a2 (by decide)) (nq' ra (by decide))]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero, hz]
    simp only [upd_app, h0, nq' a1 (by decide), nq' a0 (by decide), nq' 23 (by decide), ite_false]
  have s7_2 : reg n2 23 = BitVec.ofNat 32 (i + 1) := by
    rw [k2 _ (by decide) (by decide) (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]
    rw [h8]; exact ofNat_add_lit i 1
  have hz2 := u2.zero
  obtain ⟨n3, c3, u3⟩ := St.block ssB u2 hc ssB_end (by
    simp only [BlockOk, BInstr.ok, ssB, and_true]; rw [a02, add_lit_zero]; exact aligned_add hap (by omega))
  simp only [runBlock, BInstr.run, ssB] at u3
  obtain ⟨n4, c4, u4, a04, k4⟩ := ss_idx u3 hc ssub_at_58 ssub_at_5c (c := 0x278) (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    hP (by decide) (even_at P hP 0x278 (by decide)) hi1 six_at_0 six_at_2 six_at_4 six_at_8 six_at_a six_at_c
    (p := Lb) (i := i) (by simp +decide only [upd_app, ↓reduceIte]; rw [b2 _ (by decide), h19]; exact zw _)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [b2 _ (by decide), h8]; exact zw _) hi
  have s1_4 : reg n4 9 = memLoad32 M (ap + BitVec.ofNat 32 (4 * i)) := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]
    rw [a02, add_lit_zero]
  have b4 : ∀ q : Fin 32, q.val ∉ [1, 9, 10, 11, 12, 23] → reg n4 q = reg n q := fun q hq => by
    have nq' : ∀ r : Fin 32, r.val ∈ [1, 9, 10, 11, 12, 23] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [k4 q (nq' a0 (by decide)) (nq' a1 (by decide)) (nq' a2 (by decide)) (nq' ra (by decide))]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero, hz]
    simp only [upd_app, h0, nq' a1 (by decide), nq' a0 (by decide), nq' 9 (by decide), ite_false]
    exact b2 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega))
  have s7_4 : reg n4 23 = BitVec.ofNat 32 (i + 1) := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]; exact s7_2
  have hz4 := u4.zero
  obtain ⟨n5, c5, u5⟩ := St.block ssC u4 hc ssC_end (by
    simp only [BlockOk, BInstr.ok, ssC, and_true]; rw [a04, add_lit_zero]; exact aligned_add hLb (by omega))
  simp only [runBlock, BInstr.run, ssC] at u5
  obtain ⟨n6, c6, u6, a06, k6⟩ := ss_idx u5 hc ssub_at_70 ssub_at_74 (c := 0x292) (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    hP (by decide) (even_at P hP 0x292 (by decide)) hi2 sixm_at_0 sixm_at_2 sixm_at_4 sixm_at_8 sixm_at_a sixm_at_c
    (p := F + 4) (i := i) (by simp +decide only [upd_app, ↓reduceIte]; rw [b4 _ (by decide), hsp]; rfl)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [b4 _ (by decide), h8]; exact zw _) hi
  have s8_6 : reg n6 24 = ssB1 (reg n 24) (memLoad32 M (ap + BitVec.ofNat 32 (4 * i)))
      (memLoad32 M (Lb + BitVec.ofNat 32 (4 * i))) := by
    rw [k6 _ (by decide) (by decide) (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]
    rw [a04, add_lit_zero, s1_4, b4 _ (by decide)]
  have b6 : ∀ q : Fin 32, q.val ∉ [1, 9, 10, 11, 12, 23, 24] → reg n6 q = reg n q := fun q hq => by
    have nq' : ∀ r : Fin 32, r.val ∈ [1, 9, 10, 11, 12, 23, 24] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [k6 q (nq' a0 (by decide)) (nq' a1 (by decide)) (nq' a2 (by decide)) (nq' ra (by decide))]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero, hz]
    simp only [upd_app, h0, nq' a1 (by decide), nq' a0 (by decide), nq' 24 (by decide), ite_false]
    exact b4 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega))
  have s7_6 : reg n6 23 = BitVec.ofNat 32 (i + 1) := by
    rw [k6 _ (by decide) (by decide) (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]; exact s7_4
  obtain ⟨n7, c7, u7⟩ := St.block ssD u6 hc ssD_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, ssD, and_true, true_and]
    try simp +decide only [upd_app, ↓reduceIte]
    rw [a06, add_lit_zero, show F + 4 + BitVec.ofNat 32 (4 * i) = F + BitVec.ofNat 32 (4 + 4 * i) by
      rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]]
    refine ⟨aligned_add hF (by omega), ?_⟩
    rw [← show F + 4 + BitVec.ofNat 32 (4 * i) = F + BitVec.ofNat 32 (4 + 4 * i) by
      rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]]
    exact sWC)
  simp only [runBlock, BInstr.run, ssD] at u7
  have hz6 := u6.zero
  refine ⟨n7, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans c7))))), ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · have e : reg n6 a0 + 0 = F + 4 + BitVec.ofNat 32 (4 * i) := by rw [a06, add_lit_zero]
    have e2 : upd (reg n6) a1 (aluEval .and (reg n6 24) (reg n6 20)) a1 = aluEval .and (ssB1 (reg n 24)
        (memLoad32 M (ap + BitVec.ofNat 32 (4 * i))) (memLoad32 M (Lb + BitVec.ofNat 32 (4 * i)))) (reg n 20) := by
      simp +decide only [upd_app, ↓reduceIte]; rw [s8_6, b6 _ (by decide)]
    have e3 : upd (reg n6) a1 (aluEval .and (reg n6 24) (reg n6 20)) a0 = reg n6 a0 := by
      simp +decide only [upd_app, ↓reduceIte]
    rw [e3, e, e2] at u7
    exact ⟨u7.pc, u7.mem, fun r => by rw [u7.regs]⟩
  · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; exact s8_6
  · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; exact s7_6
  · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s7_6]; exact zw _
  · rw [u7.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero, hz]
    simp only [upd_app, h0, nq q hq 8 (by decide), nq q hq a1 (by decide), ite_false]
    exact b6 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega))

theorem s29Borrow_lt (a : Nat → Nat) : ∀ i, s29Borrow a i < 2 ^ 32
  | 0 => by show 0 < 2 ^ 32; decide
  | _ + 1 => Nat.mod_lt _ (by decide)

theorem ssO (F : Word) (j : Nat) : F + 4 + BitVec.ofNat 32 (4 * j) = F + BitVec.ofNat 32 (4 + 4 * j) := by
  rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]

/-- A store to `difference[i]` leaves the other limbs. -/
theorem ss_slot {M : Word → BitVec 8} {F v : Word} {i j : Nat} (hi : i < 9) (hj : j < 9) :
    memLoad32 (memStore32 M (F + 4 + BitVec.ofNat 32 (4 * i)) v) (F + 4 + BitVec.ofNat 32 (4 * j)) =
      if j = i then v else memLoad32 M (F + 4 + BitVec.ofNat 32 (4 * j)) := by
  by_cases h : j = i
  · subst h; rw [ite_eq_left rfl, memLoad32_store32_same]
  · rw [ite_eq_right h, ssO, ssO, memLoad32_store32_sep (sep_offsets F (by omega) (by omega) (by omega))]

theorem bne_9 {i : Nat} (hi : i < 9) :
    branchTaken .bne (BitVec.ofNat 32 (i + 1)) (BitVec.ofNat 32 9) = decide (i + 1 ≠ 9) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `a`'s limbs, as numbers. -/
abbrev ssAw (M : Word → BitVec 8) (ap : Word) (j : Nat) : Nat := (memLoad32 M (ap + BitVec.ofNat 32 (4 * j))).toNat

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The first loop, from 0x42 with `i` limbs done to its exit at 0x84: the
borrow word after all nine, and `difference` holding each limb's low 29 bits. -/
theorem ss_loop1 {Mb : Word → BitVec 8} {P F ap Lb : Word} (hP : P.toNat % 2 = 0)
    (hcb : CodeIn Mb P scalar29SubCode) (hi1b : CodeIn Mb (P + 0x278) scalar29IndexCode)
    (hi2b : CodeIn Mb (P + 0x292) scalar29IndexMutCode) (hL : CodeIn Mb Lb scalarLData)
    (hF : F.toNat % 4 = 0) (hap : ap.toNat % 4 = 0) (hLb : Lb.toNat % 4 = 0)
    (sDC : Sep (F + 4) 36 P scalar29SubCode.length) (sD1 : Sep (F + 4) 36 (P + 0x278) scalar29IndexCode.length)
    (sD2 : Sep (F + 4) 36 (P + 0x292) scalar29IndexMutCode.length) (sDL : Sep (F + 4) 36 Lb 36)
    (sDA : Sep (F + 4) 36 ap 36) :
    ∀ r i (n : Machine) (Mi : Word → BitVec 8), i + r = 9 → 0 < r → St Mi P n 0x42 (reg n) →
      (∀ x, Sep (F + 4) 36 x 1 → Mi x = Mb x) →
      (∀ j, j < 9 → memLoad32 Mi (F + 4 + BitVec.ofNat 32 (4 * j)) =
        if j < i then BitVec.ofNat 32 (s29Borrow (ssAw Mb ap) (j + 1) % 2 ^ 29) else 0) →
      reg n 8 = BitVec.ofNat 32 i → reg n 21 = ap → reg n 19 = Lb → reg n sp = F → reg n 20 = 0x1FFFFFFF →
      reg n 22 = BitVec.ofNat 32 9 → reg n 24 = BitVec.ofNat 32 (s29Borrow (ssAw Mb ap) i) →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x84 (reg n') ∧ (∀ x, Sep (F + 4) 36 x 1 → M' x = Mb x) ∧
        (∀ j, j < 9 → memLoad32 M' (F + 4 + BitVec.ofNat 32 (4 * j)) =
          BitVec.ofNat 32 (s29Borrow (ssAw Mb ap) (j + 1) % 2 ^ 29)) ∧
        reg n' 24 = BitVec.ofNat 32 (s29Borrow (ssAw Mb ap) 9) ∧
        ∀ q : Fin 32, q.val ∉ [1, 8, 9, 10, 11, 12, 23, 24] → reg n' q = reg n q := by
  intro r
  induction r with
  | zero => intro _ _ _ _ hr; exact absurd hr (Nat.lt_irrefl 0)
  | succ r ih =>
  intro i n Mi hir _ s fr hd h8 h21 h19 hsp h20 h22 h24
  have hi : i < 9 := by omega
  have cIn : ∀ {b : Word} {code : List Nat}, CodeIn Mb b code → Sep (F + 4) 36 b code.length → CodeIn Mi b code :=
    fun hc hs k hk => by rw [fr _ (hs.subR (c := k) (l := 1) (by omega))]; exact hc k hk
  have hci := cIn hcb sDC
  have hA : memLoad32 Mi (ap + BitVec.ofNat 32 (4 * i)) = memLoad32 Mb (ap + BitVec.ofNat 32 (4 * i)) :=
    load_frame fr (sDA.subR (c := 4 * i) (l := 4) (by omega))
  have hLw : memLoad32 Mi (Lb + BitVec.ofNat 32 (4 * i)) = BitVec.ofNat 32 (scalarL.getD i 0) := by
    rw [load_frame fr (sDL.subR (c := 4 * i) (l := 4) (by omega))]; exact scalarL_word hL hi
  have sW : Sep (F + 4 + BitVec.ofNat 32 (4 * i)) 4 P scalar29SubCode.length := sDC.sub (by omega)
  obtain ⟨n1, c1, u1, s8_1, s7_1, s0_1, k1⟩ := ss_body1 hP hci (cIn hi1b sD1) (cIn hi2b sD2) s hi h8 h21 h19
    hsp hF hap hLb sW
  have hB : ssB1 (reg n 24) (memLoad32 Mi (ap + BitVec.ofNat 32 (4 * i))) (memLoad32 Mi (Lb + BitVec.ofNat 32 (4 * i)))
      = BitVec.ofNat 32 (s29Borrow (ssAw Mb ap) (i + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [s29_borrow_tn, h24, hA, hLw, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (s29Borrow_lt _ i), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s29Borrow_lt _ (i + 1))]
    have hL32 : scalarL.getD i 0 < 2 ^ 32 := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [Nat.mod_eq_of_lt hL32]
    rfl
  have hS : aluEval .and (ssB1 (reg n 24) (memLoad32 Mi (ap + BitVec.ofNat 32 (4 * i)))
      (memLoad32 Mi (Lb + BitVec.ofNat 32 (4 * i)))) (reg n 20) =
      BitVec.ofNat 32 (s29Borrow (ssAw Mb ap) (i + 1) % 2 ^ 29) := by
    rw [hB, h20]; apply BitVec.eq_of_toNat_eq
    rw [and29_tn, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s29Borrow_lt _ (i + 1)),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
  rw [hS] at u1
  rw [hB] at s8_1
  obtain ⟨M1, hM1⟩ : ∃ M', memStore32 Mi (F + 4 + BitVec.ofNat 32 (4 * i))
      (BitVec.ofNat 32 (s29Borrow (ssAw Mb ap) (i + 1) % 2 ^ 29)) = M' := ⟨_, rfl⟩
  rw [hM1] at u1
  have fr1 : ∀ x, Sep (F + 4) 36 x 1 → M1 x = Mb x := fun x hx => by
    rw [← hM1, memStore32_get_sep (hx.sub (c := 4 * i) (l := 4) (by omega)), fr x hx]
  have hd1 : ∀ j, j < 9 → memLoad32 M1 (F + 4 + BitVec.ofNat 32 (4 * j)) =
      if j < i + 1 then BitVec.ofNat 32 (s29Borrow (ssAw Mb ap) (j + 1) % 2 ^ 29) else 0 := fun j hj => by
    rw [← hM1, ss_slot hi hj]
    by_cases e : j = i
    · subst e; rw [ite_eq_left rfl, ite_eq_left (by omega)]
    · rw [ite_eq_right e, hd j hj]
      by_cases hl : j < i
      · rw [ite_eq_left hl, ite_eq_left (by omega)]
      · rw [ite_eq_right hl, ite_eq_right (by omega)]
  have hc1 : CodeIn M1 P scalar29SubCode := fun k hk => by
    rw [fr1 _ (sDC.subR (c := k) (l := 1) (by omega))]; exact hcb k hk
  have k1' : ∀ q : Fin 32, q.val ∉ [1, 8, 9, 10, 11, 12, 23, 24] → reg n1 q = reg n q := k1
  have s6_1 : reg n1 22 = BitVec.ofNat 32 9 := by rw [k1' _ (by decide), h22]
  by_cases hlast : i + 1 = 9
  · obtain ⟨n2, d2, u2⟩ := u1.notTaken hc1 0x84 ssub_at_80 (by decide) (by rw [s7_1, s6_1, bne_9 hi]; exact decide_eq_false (by omega))
    refine ⟨n2, M1, c1.trans (.single d2), u2.self, fr1, fun j hj => by rw [hd1 j hj, ite_eq_left (by omega)], ?_, ?_⟩
    · rw [u2.regs, s8_1, hlast]
    · intro q hq; rw [u2.regs, k1' q hq]
  · obtain ⟨n2, d2, u2⟩ := u1.taken hc1 0x42 ssub_at_80 (by decide) (by rw [s7_1, s6_1, bne_9 hi]; exact decide_eq_true hlast)
    have g : ∀ q, reg n2 q = reg n1 q := u2.regs
    obtain ⟨n3, M3, c3, u3, fr3, hd3, s8_3, k3⟩ := ih (i + 1) n2 M1 (by omega) (by omega) u2.self fr1 hd1
      (by rw [g, s0_1]) (by rw [g, k1' _ (by decide), h21]) (by rw [g, k1' _ (by decide), h19])
      (by rw [g, k1' _ (by decide), hsp]) (by rw [g, k1' _ (by decide), h20]) (by rw [g, s6_1]) (by rw [g, s8_1])
    exact ⟨n3, M3, c1.trans (.cons d2 c3), u3, fr3, hd3, s8_3, fun q hq => by rw [k3 q hq, g, k1' q hq]⟩

/-- `conditional_add_l`, from 0xAA to 0xB2: the next index, and `index(L, i)`'s arguments. -/
def ssE : List BInstr := [.aluImm .add (23 : Fin 32) (9 : Fin 32) 0x1, .alu .add a0 x0 (19 : Fin 32), .alu .add a1 x0 (9 : Fin 32)]
/-- From 0xBA to 0xC8: the carry's top bits, `L[i]` under the mask, and `index(difference, i)`'s arguments. -/
def ssF : List BInstr :=
  [.aluImm .srl (24 : Fin 32) (8 : Fin 32) 0x1D, .lw a0 a0 0x0, .alu .and (8 : Fin 32) a0 (22 : Fin 32),
   .aluImm .add a0 sp 0x4, .alu .add a1 x0 (9 : Fin 32)]
/-- From 0xD0 to 0xDA: the new carry, and `index_mut(difference, i)`'s arguments. -/
def ssG : List BInstr :=
  [.lw a0 a0 0x0, .alu .add a0 a0 (24 : Fin 32), .alu .add (8 : Fin 32) (8 : Fin 32) a0, .aluImm .add a0 sp 0x4,
   .alu .add a1 x0 (9 : Fin 32)]
/-- From 0xE2 to 0xEA: the carry's low 29 bits to `difference[i]`. -/
def ssH : List BInstr := [.alu .and a1 (8 : Fin 32) (20 : Fin 32), .sw a0 a1 0x0, .alu .add (9 : Fin 32) x0 (23 : Fin 32)]

section
set_option maxRecDepth 20000
theorem ssE_end : blockEnd scalar29SubCode 0xAA ssE = some 0xB2 := by decide
theorem ssF_end : blockEnd scalar29SubCode 0xBA ssF = some 0xC8 := by decide
theorem ssG_end : blockEnd scalar29SubCode 0xD0 ssG = some 0xDA := by decide
theorem ssH_end : blockEnd scalar29SubCode 0xE2 ssH = some 0xEA := by decide
end

/-- `conditional_add_l`'s carry step, as the compiled code computes it. -/
abbrev ssC1 (c l mask d : Word) : Word := aluEval .add (aluEval .and l mask) (aluEval .add d (aluEval .srl c 0x1D))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- One pass of `conditional_add_l`'s loop, from 0xAA to the branch at 0xEA. -/
theorem ss_body2 {M : Word → BitVec 8} {P F Lb : Word} {n : Machine} (hP : P.toNat % 2 = 0)
    (hc : CodeIn M P scalar29SubCode) (hi1 : CodeIn M (P + 0x278) scalar29IndexCode)
    (hi2 : CodeIn M (P + 0x292) scalar29IndexMutCode) (s : St M P n 0xAA (reg n)) {i : Nat} (hi : i < 9)
    (h9 : reg n 9 = BitVec.ofNat 32 i) (h19 : reg n 19 = Lb) (hsp : reg n sp = F)
    (hF : F.toNat % 4 = 0) (hLb : Lb.toNat % 4 = 0)
    (sWC : Sep (F + 4 + BitVec.ofNat 32 (4 * i)) 4 P scalar29SubCode.length) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (F + 4 + BitVec.ofNat 32 (4 * i)) (aluEval .and (ssC1 (reg n 8)
        (memLoad32 M (Lb + BitVec.ofNat 32 (4 * i))) (reg n 22) (memLoad32 M (F + 4 + BitVec.ofNat 32 (4 * i))))
        (reg n 20))) P n' 0xEA (reg n') ∧
      reg n' 8 = ssC1 (reg n 8) (memLoad32 M (Lb + BitVec.ofNat 32 (4 * i))) (reg n 22)
        (memLoad32 M (F + 4 + BitVec.ofNat 32 (4 * i))) ∧
      reg n' 23 = BitVec.ofNat 32 (i + 1) ∧ reg n' 9 = BitVec.ofNat 32 (i + 1) ∧
      ∀ q : Fin 32, q.val ∉ [1, 8, 9, 10, 11, 12, 23, 24] → reg n' q = reg n q := by
  have hz := s.zero
  have nq : ∀ q : Fin 32, q.val ∉ [1, 8, 9, 10, 11, 12, 23, 24] → ∀ r : Fin 32, r.val ∈ [1, 8, 9, 10, 11, 12, 23, 24] →
      q ≠ r := fun q hq r hr e => hq (e ▸ hr)
  obtain ⟨n1, c1, u1⟩ := St.block ssE s hc ssE_end (by simp [BlockOk, BInstr.ok, ssE])
  simp only [runBlock, BInstr.run, ssE] at u1
  obtain ⟨n2, c2, u2, a02, k2⟩ := ss_idx u1 hc ssub_at_b2 ssub_at_b6 (c := 0x278) (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    hP (by decide) (even_at P hP 0x278 (by decide)) hi1 six_at_0 six_at_2 six_at_4 six_at_8 six_at_a six_at_c
    (p := Lb) (i := i) (by simp +decide only [upd_app, ↓reduceIte]; rw [h19]; exact zw _)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [h9]; exact zw _) hi
  have b2 : ∀ q : Fin 32, q.val ∉ [1, 10, 11, 12, 23] → reg n2 q = reg n q := fun q hq => by
    have nq' : ∀ r : Fin 32, r.val ∈ [1, 10, 11, 12, 23] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [k2 q (nq' a0 (by decide)) (nq' a1 (by decide)) (nq' a2 (by decide)) (nq' ra (by decide))]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero, hz]
    simp only [upd_app, h0, nq' a1 (by decide), nq' a0 (by decide), nq' 23 (by decide), ite_false]
  have s7_2 : reg n2 23 = BitVec.ofNat 32 (i + 1) := by
    rw [k2 _ (by decide) (by decide) (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]
    rw [h9]; exact ofNat_add_lit i 1
  obtain ⟨n3, c3, u3⟩ := St.block ssF u2 hc ssF_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, ssF, and_true, true_and]
    try simp +decide only [upd_app, ↓reduceIte]
    rw [a02, add_lit_zero]; exact aligned_add hLb (by omega))
  simp only [runBlock, BInstr.run, ssF] at u3
  obtain ⟨n4, c4, u4, a04, k4⟩ := ss_idx u3 hc ssub_at_c8 ssub_at_cc (c := 0x278) (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    hP (by decide) (even_at P hP 0x278 (by decide)) hi1 six_at_0 six_at_2 six_at_4 six_at_8 six_at_a six_at_c
    (p := F + 4) (i := i) (by simp +decide only [upd_app, ↓reduceIte]; rw [b2 _ (by decide), hsp]; rfl)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [b2 _ (by decide), h9]; exact zw _) hi
  have s0_4 : reg n4 8 = aluEval .and (memLoad32 M (Lb + BitVec.ofNat 32 (4 * i))) (reg n 22) := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]
    rw [a02, add_lit_zero, b2 _ (by decide)]
  have s8_4 : reg n4 24 = aluEval .srl (reg n 8) 0x1D := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]
    rw [b2 _ (by decide)]
  have b4 : ∀ q : Fin 32, q.val ∉ [1, 8, 10, 11, 12, 23, 24] → reg n4 q = reg n q := fun q hq => by
    have nq' : ∀ r : Fin 32, r.val ∈ [1, 8, 10, 11, 12, 23, 24] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [k4 q (nq' a0 (by decide)) (nq' a1 (by decide)) (nq' a2 (by decide)) (nq' ra (by decide))]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero, hz]
    simp only [upd_app, h0, nq' a1 (by decide), nq' a0 (by decide), nq' 8 (by decide), nq' 24 (by decide), ite_false]
    exact b2 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega))
  have s7_4 : reg n4 23 = BitVec.ofNat 32 (i + 1) := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]; exact s7_2
  obtain ⟨n5, c5, u5⟩ := St.block ssG u4 hc ssG_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, ssG, and_true, true_and]
    rw [a04, add_lit_zero, ssO]; exact aligned_add hF (by omega))
  simp only [runBlock, BInstr.run, ssG] at u5
  obtain ⟨n6, c6, u6, a06, k6⟩ := ss_idx u5 hc ssub_at_da ssub_at_de (c := 0x292) (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    hP (by decide) (even_at P hP 0x292 (by decide)) hi2 sixm_at_0 sixm_at_2 sixm_at_4 sixm_at_8 sixm_at_a sixm_at_c
    (p := F + 4) (i := i) (by simp +decide only [upd_app, ↓reduceIte]; rw [b4 _ (by decide), hsp]; rfl)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [b4 _ (by decide), h9]; exact zw _) hi
  have s0_6 : reg n6 8 = ssC1 (reg n 8) (memLoad32 M (Lb + BitVec.ofNat 32 (4 * i))) (reg n 22)
      (memLoad32 M (F + 4 + BitVec.ofNat 32 (4 * i))) := by
    rw [k6 _ (by decide) (by decide) (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]
    rw [a04, add_lit_zero, s0_4, s8_4]
  have b6 : ∀ q : Fin 32, q.val ∉ [1, 8, 10, 11, 12, 23, 24] → reg n6 q = reg n q := fun q hq => by
    have nq' : ∀ r : Fin 32, r.val ∈ [1, 8, 10, 11, 12, 23, 24] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [k6 q (nq' a0 (by decide)) (nq' a1 (by decide)) (nq' a2 (by decide)) (nq' ra (by decide))]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero, hz]
    simp only [upd_app, h0, nq' a1 (by decide), nq' a0 (by decide), nq' 8 (by decide), ite_false]
    exact b4 q hq
  have s7_6 : reg n6 23 = BitVec.ofNat 32 (i + 1) := by
    rw [k6 _ (by decide) (by decide) (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]; exact s7_4
  obtain ⟨n7, c7, u7⟩ := St.block ssH u6 hc ssH_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, ssH, and_true, true_and]
    try simp +decide only [upd_app, ↓reduceIte]
    rw [a06, add_lit_zero]
    exact ⟨by rw [ssO]; exact aligned_add hF (by omega), sWC⟩)
  simp only [runBlock, BInstr.run, ssH] at u7
  refine ⟨n7, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans c7))))), ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · have e : reg n6 a0 + 0 = F + 4 + BitVec.ofNat 32 (4 * i) := by rw [a06, add_lit_zero]
    have e2 : upd (reg n6) a1 (aluEval .and (reg n6 8) (reg n6 20)) a1 = aluEval .and (ssC1 (reg n 8)
        (memLoad32 M (Lb + BitVec.ofNat 32 (4 * i))) (reg n 22) (memLoad32 M (F + 4 + BitVec.ofNat 32 (4 * i))))
        (reg n 20) := by
      simp +decide only [upd_app, ↓reduceIte]; rw [s0_6, b6 _ (by decide)]
    have e3 : upd (reg n6) a1 (aluEval .and (reg n6 8) (reg n6 20)) a0 = reg n6 a0 := by
      simp +decide only [upd_app, ↓reduceIte]
    rw [e3, e, e2] at u7
    exact ⟨u7.pc, u7.mem, fun r => by rw [u7.regs]⟩
  · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; exact s0_6
  · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; exact s7_6
  · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s7_6]; exact zw _
  · rw [u7.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero, hz]
    simp only [upd_app, h0, nq q hq 9 (by decide), nq q hq a1 (by decide), ite_false]
    exact b6 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega))

theorem s29Carry_lt (a : Nat → Nat) (c : Nat) : ∀ i, s29Carry a c i < 2 ^ 32
  | 0 => by show 0 < 2 ^ 32; decide
  | _ + 1 => Nat.mod_lt _ (by decide)

/-- The select mask: all ones when `L` is added back. -/
abbrev ssMask (c : Nat) : Word := if c = 1 then 0xFFFFFFFF else 0

theorem ss_carry_tn (c : Nat) (cw l d : Word) :
    (ssC1 cw l (ssMask c) d).toNat = (cw.toNat / 2 ^ 29 + d.toNat + (if c = 1 then l.toNat else 0)) % 2 ^ 32 := by
  have hl := l.isLt
  have hm : (aluEval .and l (ssMask c)).toNat = if c = 1 then l.toNat else 0 := by
    by_cases h : c = 1
    · rw [ite_eq_left h]; simp only [ssMask, ite_eq_left h]
      show (l &&& (0xFFFFFFFF : Word)).toNat = _
      rw [and_low (m := (0xFFFFFFFF : Word)) (k := 32) (by decide) (by decide), Nat.mod_eq_of_lt hl]
    · rw [ite_eq_right h]; simp only [ssMask, ite_eq_right h]
      show (l &&& 0#32).toNat = 0
      rw [BitVec.and_zero]; rfl
  show (aluEval .and l (ssMask c) + (d + aluEval .srl cw 0x1D)).toNat = _
  rw [BitVec.toNat_add, hm, BitVec.toNat_add, tn_srl rfl, show ((0x1D : Word).toNat % 32) = 29 from rfl]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `conditional_add_l`'s loop, from 0xAA with `i` limbs done to its exit at
0xEE: `difference` holds the carried sum's limbs. -/
theorem ss_loop2 {Mb : Word → BitVec 8} {P F Lb : Word} {a : Nat → Nat} {c : Nat} (hP : P.toNat % 2 = 0)
    (hcb : CodeIn Mb P scalar29SubCode) (hi1b : CodeIn Mb (P + 0x278) scalar29IndexCode)
    (hi2b : CodeIn Mb (P + 0x292) scalar29IndexMutCode) (hL : CodeIn Mb Lb scalarLData)
    (hF : F.toNat % 4 = 0) (hLb : Lb.toNat % 4 = 0)
    (sDC : Sep (F + 4) 36 P scalar29SubCode.length) (sD1 : Sep (F + 4) 36 (P + 0x278) scalar29IndexCode.length)
    (sD2 : Sep (F + 4) 36 (P + 0x292) scalar29IndexMutCode.length) (sDL : Sep (F + 4) 36 Lb 36) :
    ∀ r i (n : Machine) (Mi : Word → BitVec 8), i + r = 9 → 0 < r → St Mi P n 0xAA (reg n) →
      (∀ x, Sep (F + 4) 36 x 1 → Mi x = Mb x) →
      (∀ j, j < 9 → memLoad32 Mi (F + 4 + BitVec.ofNat 32 (4 * j)) =
        if j < i then BitVec.ofNat 32 (s29Carry a c (j + 1) % 2 ^ 29)
        else BitVec.ofNat 32 (s29Borrow a (j + 1) % 2 ^ 29)) →
      reg n 9 = BitVec.ofNat 32 i → reg n 19 = Lb → reg n sp = F → reg n 20 = 0x1FFFFFFF →
      reg n 21 = BitVec.ofNat 32 9 → reg n 22 = ssMask c → reg n 8 = BitVec.ofNat 32 (s29Carry a c i) →
      ∃ n' M', Steps n n' ∧ St M' P n' 0xEE (reg n') ∧ (∀ x, Sep (F + 4) 36 x 1 → M' x = Mb x) ∧
        (∀ j, j < 9 → memLoad32 M' (F + 4 + BitVec.ofNat 32 (4 * j)) = BitVec.ofNat 32 (s29Carry a c (j + 1) % 2 ^ 29)) ∧
        ∀ q : Fin 32, q.val ∉ [1, 8, 9, 10, 11, 12, 23, 24] → reg n' q = reg n q := by
  intro r
  induction r with
  | zero => intro _ _ _ _ hr; exact absurd hr (Nat.lt_irrefl 0)
  | succ r ih =>
  intro i n Mi hir _ s fr hd h9 h19 hsp h20 h21 h22 h8
  have hi : i < 9 := by omega
  have cIn : ∀ {b : Word} {code : List Nat}, CodeIn Mb b code → Sep (F + 4) 36 b code.length → CodeIn Mi b code :=
    fun hc hs k hk => by rw [fr _ (hs.subR (c := k) (l := 1) (by omega))]; exact hc k hk
  have hci := cIn hcb sDC
  have hLw : memLoad32 Mi (Lb + BitVec.ofNat 32 (4 * i)) = BitVec.ofNat 32 (scalarL.getD i 0) := by
    rw [load_frame fr (sDL.subR (c := 4 * i) (l := 4) (by omega))]; exact scalarL_word hL hi
  have hDw : memLoad32 Mi (F + 4 + BitVec.ofNat 32 (4 * i)) = BitVec.ofNat 32 (s29Borrow a (i + 1) % 2 ^ 29) := by
    rw [hd i hi, ite_eq_right (by omega)]
  have sW : Sep (F + 4 + BitVec.ofNat 32 (4 * i)) 4 P scalar29SubCode.length := sDC.sub (by omega)
  obtain ⟨n1, c1, u1, s0_1, s7_1, s1_1, k1⟩ := ss_body2 hP hci (cIn hi1b sD1) (cIn hi2b sD2) s hi h9 h19
    hsp hF hLb sW
  have hL32 : scalarL.getD i 0 < 2 ^ 32 := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hC : ssC1 (reg n 8) (memLoad32 Mi (Lb + BitVec.ofNat 32 (4 * i))) (reg n 22)
      (memLoad32 Mi (F + 4 + BitVec.ofNat 32 (4 * i))) = BitVec.ofNat 32 (s29Carry a c (i + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [h22, ss_carry_tn, h8, hLw, hDw, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s29Carry_lt _ _ i), Nat.mod_eq_of_lt (s29Carry_lt _ _ (i + 1)),
      Nat.mod_eq_of_lt hL32, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
    rfl
  have hS : aluEval .and (ssC1 (reg n 8) (memLoad32 Mi (Lb + BitVec.ofNat 32 (4 * i))) (reg n 22)
      (memLoad32 Mi (F + 4 + BitVec.ofNat 32 (4 * i)))) (reg n 20) = BitVec.ofNat 32 (s29Carry a c (i + 1) % 2 ^ 29) := by
    rw [hC, h20]; apply BitVec.eq_of_toNat_eq
    rw [and29_tn, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s29Carry_lt _ _ (i + 1)),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
  rw [hS] at u1
  rw [hC] at s0_1
  obtain ⟨M1, hM1⟩ : ∃ M', memStore32 Mi (F + 4 + BitVec.ofNat 32 (4 * i))
      (BitVec.ofNat 32 (s29Carry a c (i + 1) % 2 ^ 29)) = M' := ⟨_, rfl⟩
  rw [hM1] at u1
  have fr1 : ∀ x, Sep (F + 4) 36 x 1 → M1 x = Mb x := fun x hx => by
    rw [← hM1, memStore32_get_sep (hx.sub (c := 4 * i) (l := 4) (by omega)), fr x hx]
  have hd1 : ∀ j, j < 9 → memLoad32 M1 (F + 4 + BitVec.ofNat 32 (4 * j)) =
      if j < i + 1 then BitVec.ofNat 32 (s29Carry a c (j + 1) % 2 ^ 29)
      else BitVec.ofNat 32 (s29Borrow a (j + 1) % 2 ^ 29) := fun j hj => by
    rw [← hM1, ss_slot hi hj]
    by_cases e : j = i
    · subst e; rw [ite_eq_left rfl, ite_eq_left (by omega)]
    · rw [ite_eq_right e, hd j hj]
      by_cases hl : j < i
      · rw [ite_eq_left hl, ite_eq_left (by omega)]
      · rw [ite_eq_right hl, ite_eq_right (by omega)]
  have hc1 : CodeIn M1 P scalar29SubCode := fun k hk => by
    rw [fr1 _ (sDC.subR (c := k) (l := 1) (by omega))]; exact hcb k hk
  have k1' : ∀ q : Fin 32, q.val ∉ [1, 8, 9, 10, 11, 12, 23, 24] → reg n1 q = reg n q := k1
  have s5_1 : reg n1 21 = BitVec.ofNat 32 9 := by rw [k1' _ (by decide), h21]
  by_cases hlast : i + 1 = 9
  · obtain ⟨n2, d2, u2⟩ := u1.notTaken hc1 0xEE ssub_at_ea (by decide) (by rw [s7_1, s5_1, bne_9 hi]; exact decide_eq_false (by omega))
    refine ⟨n2, M1, c1.trans (.single d2), u2.self, fr1, fun j hj => by rw [hd1 j hj, ite_eq_left (by omega)], ?_⟩
    intro q hq; rw [u2.regs, k1' q hq]
  · obtain ⟨n2, d2, u2⟩ := u1.taken hc1 0xAA ssub_at_ea (by decide) (by rw [s7_1, s5_1, bne_9 hi]; exact decide_eq_true hlast)
    have g : ∀ q, reg n2 q = reg n1 q := u2.regs
    obtain ⟨n3, M3, c3, u3, fr3, hd3, k3⟩ := ih (i + 1) n2 M1 (by omega) (by omega) u2.self fr1 hd1
      (by rw [g, s1_1]) (by rw [g, k1' _ (by decide), h19]) (by rw [g, k1' _ (by decide), hsp])
      (by rw [g, k1' _ (by decide), h20]) (by rw [g, s5_1]) (by rw [g, k1' _ (by decide), h22]) (by rw [g, s0_1])
    exact ⟨n3, M3, c1.trans (.cons d2 c3), u3, fr3, hd3, fun q hq => by rw [k3 q hq, g, k1' q hq]⟩

/-- The registers the function saves, at offsets from its `sp`. -/
abbrev ssPs : List (Fin 32 × Word) :=
  [(ra, 0x4C), ((8 : Fin 32), 0x48), ((9 : Fin 32), 0x44), ((18 : Fin 32), 0x40), ((19 : Fin 32), 0x3C),
   ((20 : Fin 32), 0x38), ((21 : Fin 32), 0x34), ((22 : Fin 32), 0x30), ((23 : Fin 32), 0x2C), ((24 : Fin 32), 0x28)]

set_option maxRecDepth 20000 in
theorem ssPs_range : ∀ p ∈ ssPs, p.2.toNat % 4 = 0 ∧ 0x28 ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x50 := by decide

theorem ssPs_sp : ∀ p ∈ ssPs, p.1 ≠ sp := by decide

/-- From 0x16 to 0x28: keep the arguments, the 29-bit mask, and `memset`'s arguments. -/
def ssPro : List BInstr :=
  [.alu .add (21 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .lui (20 : Fin 32) 0x20000000,
   .aluImm .add (20 : Fin 32) (20 : Fin 32) 0xFFFFFFFF, .aluImm .add a0 sp 0x4, .aluImm .add a2 x0 0x24,
   .aluImm .add a1 x0 0x0]
/-- From 0x30 to 0x3E: the first loop's index, borrow, count, and `&L`. -/
def ssM1 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x0, .aluImm .add (24 : Fin 32) x0 0x0, .aluImm .add (22 : Fin 32) x0 0x9,
   .lui (19 : Fin 32) 0x3FCC5000, .aluImm .add (19 : Fin 32) (19 : Fin 32) 0xFFFFFA08]

section
set_option maxRecDepth 20000
theorem ssSave_end : blockEnd scalar29SubCode 2 (saveBlock ssPs) = some 0x16 := by decide
theorem ssPro_end : blockEnd scalar29SubCode 0x16 ssPro = some 0x28 := by decide
theorem ssM1_end : blockEnd scalar29SubCode 0x30 ssM1 = some 0x3E := by decide
theorem ssRestore_end : blockEnd scalar29SubCode 0xFE (restoreBlock ssPs) = some 0x112 := by decide
end

theorem ssG_ofs (G : Word) (c : Nat) : G + 0x10 + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x10 + c) := by
  rw [show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl, add_ofNat_assoc]

theorem ssF_in {G b : Word} {c l k : Nat} (h : c + l ≤ 0x50) (hx : Sep G 0x60 b k) :
    Sep (G + 0x10 + BitVec.ofNat 32 c) l b k := by
  rw [ssG_ofs]; exact hx.sub (by omega)

theorem ssD_in {G b : Word} {k : Nat} (hx : Sep G 0x60 b k) : Sep (G + 0x10 + 4) 36 b k := by
  have := ssF_in (c := 4) (l := 36) (by decide) hx; exact this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The prologue, from entry to the first loop at 0x42: save the registers,
keep the arguments, and zero `difference` with `memset`. -/
theorem ss_pro (m : Machine) {P G out ap : Word} (env : SSEnv m.mem P G out ap)
    (hpc : m.pc = P) (hsp : reg m sp = G + 0x60) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ap) :
    ∃ n Msv, Steps m n ∧ St (fillBytes Msv (G + 0x10 + 4) ((0 : Word).extractLsb' 0 8) 36) P n 0x42 (reg n) ∧
      (∀ x, Sep (G + 0x10) 0x50 x 1 → Msv x = m.mem x) ∧
      (∀ r o, (r, o) ∈ ssPs → memLoad32 Msv (G + 0x10 + o) = reg m r) ∧
      reg n sp = G + 0x10 ∧ reg n 8 = BitVec.ofNat 32 0 ∧ reg n 21 = ap ∧ reg n 18 = out ∧
      reg n 19 = BitVec.ofNat 32 scalarLAddress ∧ reg n 20 = 0x1FFFFFFF ∧ reg n 22 = BitVec.ofNat 32 9 ∧
      reg n 24 = BitVec.ofNat 32 0 ∧ ∀ q : Fin 32, q.val ∈ [3, 4, 25, 26, 27] → reg n q = reg m q := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hFa : (G + 0x10).toNat % 4 = 0 := aligned_add env.hG (k := 0x10) (by decide)
  have sFC : Sep (G + 0x10) 0x50 P scalar29SubCode.length := by
    have := ssF_in (c := 0) (l := 0x50) (by decide) env.sGC; rwa [add_ofNat_zero] at this
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code ssub_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0) sp = G + 0x10 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [hsp]; show G + 0x60 + 0xFFFFFFB0 = _
    rw [BitVec.add_assoc]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock ssPs) u1 env.code ssSave_end (saveBlock_ok _ ssPs _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (ssPs_range p hp).1, frm_sep' sFC (by have := ssPs_range p hp; omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (G + 0x10)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0)) ssPs = Msv := ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep (G + 0x10) 0x50 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; exact saveMem_outside ssPs fun p hp => frm_sep' hx (by have := ssPs_range p hp; omega)
  have cOf : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x60 b code.length →
      CodeIn Msv b code := fun hc hs i hi => by
    rw [frSv _ (by have := ssF_in (c := 0) (l := 0x50) (by decide) hs; rw [add_ofNat_zero] at this
                   exact this.subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  have hcv : CodeIn Msv P scalar29SubCode := cOf env.code env.sGC
  obtain ⟨m3, c3, u3⟩ := St.block ssPro u2.self hcv ssPro_end (by simp [BlockOk, BInstr.ok, ssPro])
  simp only [runBlock, BInstr.run, ssPro] at u3
  have r2 : ∀ q, reg m2 q = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0) q := u2.regs
  have sp3 : reg m3 sp = G + 0x10 := by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2, sp1]
  have hz3 := u3.self.zero
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hcv ssub_at_28 ssub_at_2c (cb := P + 0x5B9C)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x5B9C (by decide))
  have r4 := PEnv.reg1 regs4 hz3
  obtain ⟨m5, c5, pc5, mem5, a05, K5⟩ := memset_correct m4 (P + 0x5B9C) (P + BitVec.ofNat 32 (0x28 + 8))
    (G + 0x10 + 4) 0 36 (fun i hi => by show m4.mem _ = _; rw [mem4]; exact cOf env.mset env.sGM i hi)
    (even_at P env.hP 0x5B9C (by decide)) pc4
    (by rw [r4 _ (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2, sp1]; rfl)
    (by rw [r4 _ (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [r4 _ (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x28 + 8) (by decide)))
    (by rw [show G + 0x10 + 4 = G + BitVec.ofNat 32 0x14 by rw [BitVec.add_assoc]; rfl, BitVec.toNat_add,
          BitVec.toNat_ofNat]; have := env.hGt; omega)
    (ssD_in env.sGM)
  rw [mem4] at mem5
  have hcz : CodeIn (fillBytes Msv (G + 0x10 + 4) ((0 : Word).extractLsb' 0 8) 36) P scalar29SubCode :=
    fun i hi => by rw [fillBytes_sep ((ssD_in env.sGC).subR (c := i) (l := 1) (by omega)) (Nat.le_refl _)]; exact hcv i hi
  have w5 : St (fillBytes Msv (G + 0x10 + 4) ((0 : Word).extractLsb' 0 8) 36) P m5 0x30 (reg m5) :=
    ⟨by rw [pc5], by rw [mem5], fun _ => rfl⟩
  obtain ⟨m6, c6, u6⟩ := St.block ssM1 w5 hcz ssM1_end (by simp [BlockOk, BInstr.ok, ssM1])
  simp only [runBlock, BInstr.run, ssM1] at u6
  have K5' : ∀ q : Fin 32, q.val ∉ [12, 13, 14, 15, 16] → reg m5 q = reg m4 q := fun q hq =>
    K5 q (fun e => hq (e ▸ by decide)) (fun e => hq (e ▸ by decide)) (fun e => hq (e ▸ by decide))
      (fun e => hq (e ▸ by decide)) (fun e => hq (e ▸ by decide))
  have b5 : ∀ q : Fin 32, q.val ∉ [1, 2, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21] → reg m5 q = reg m q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [1, 2, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [K5' q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega)),
      r4 q (nq ra (by decide)), u3.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero, hz]
    simp only [upd_app, h0, nq a1 (by decide), nq a2 (by decide), nq a0 (by decide), nq 20 (by decide),
      nq 18 (by decide), nq 21 (by decide), ite_false]
    rw [r2]; simp only [upd_app, h0, nq sp (by decide), ite_false]
  have k5 : ∀ q : Fin 32, q.val ∈ [2, 18, 20, 21] → reg m5 q = reg m3 q := fun q hq => by
    rw [K5' q (fun h => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h hq; omega),
      r4 q (fun e => by rw [e] at hq; simp at hq)]
  have hz5 := w5.zero
  obtain ⟨m7, d7, u7⟩ := u6.notTaken hcz 0x42 ssub_at_3e (by decide) (by
    simp +decide only [branchTaken, upd_app, ↓reduceIte])
  refine ⟨m7, Msv, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (.single d7)))))), u7.self, frSv,
    fun r o h => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [← hMsv]
    simp only [ssPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [k5 _ (by decide), sp3]
  · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte, hz5]
  · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [k5 _ (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte, r2]; rw [ha1]; exact zw _
  · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [k5 _ (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte, r2]; rw [ha0]; exact zw _
  · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]
  · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [k5 _ (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte]
  · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte, hz5]
  · rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte, hz5]
  · have nq : ∀ r : Fin 32, r.val ∉ [3, 4, 25, 26, 27] → q ≠ r := fun r hr e => hr (e ▸ hq)
    rw [u7.regs]
    have h0 : q.val ≠ 0 := fun e => by rw [e] at hq; simp at hq
    simp only [upd_app, h0, nq 19 (by decide), nq 22 (by decide), nq 24 (by decide), nq 8 (by decide), ite_false]
    exact b5 q (fun h => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h hq; omega)

/-- 0x84: the borrow's top bit, `black_box`'s argument. -/
def ssS : List BInstr := [.aluImm .srl a0 (24 : Fin 32) 0x1F]
/-- From 0x90 to 0xA6: `conditional_add_l`'s index, carry, mask, count, and `&L`. -/
def ssM2 : List BInstr :=
  [.aluImm .add (9 : Fin 32) x0 0x0, .aluImm .add (8 : Fin 32) x0 0x0, .aluImm .and a0 a0 0xFF,
   .alu .sub (22 : Fin 32) x0 a0, .aluImm .add (21 : Fin 32) x0 0x9, .lui (19 : Fin 32) 0x3FCC5000,
   .aluImm .add (19 : Fin 32) (19 : Fin 32) 0xFFFFFA08]
/-- From 0xEE to 0xF6: `memcpy(out, difference, 36)`'s arguments. -/
def ssT : List BInstr := [.aluImm .add a1 sp 0x4, .aluImm .add a2 x0 0x24, .alu .add a0 x0 (18 : Fin 32)]

section
set_option maxRecDepth 20000
theorem ssS_end : blockEnd scalar29SubCode 0x84 ssS = some 0x88 := by decide
theorem ssM2_end : blockEnd scalar29SubCode 0x90 ssM2 = some 0xA6 := by decide
theorem ssT_end : blockEnd scalar29SubCode 0xEE ssT = some 0xF6 := by decide
end

/-- The mask `Choice::from((borrow >> 31) as u8)` becomes, through `black_box`. -/
theorem ss_mask {b : Nat} (hb : b < 2 ^ 32) :
    aluEval .sub 0 (aluEval .and (((aluEval .srl (BitVec.ofNat 32 b) 0x1F).extractLsb' 0 8).zeroExtend 32) 0xFF) =
      ssMask (b / 2 ^ 31) := by
  have e : aluEval .srl (BitVec.ofNat 32 b) 0x1F = BitVec.ofNat 32 (b / 2 ^ 31) := by
    apply BitVec.eq_of_toNat_eq
    rw [tn_srl rfl, show ((0x1F : Word).toNat % 32) = 31 from rfl, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega)]
  rw [e]
  rcases (by omega : b / 2 ^ 31 = 0 ∨ b / 2 ^ 31 = 1) with h | h <;> rw [h] <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From the first loop's exit at 0x84 to `conditional_add_l`'s loop at 0xAA:
the mask from the borrow's top bit, through `black_box`, which writes one byte
below the frame. -/
theorem ss_mid {M : Word → BitVec 8} {P G : Word} {n : Machine} (hP : P.toNat % 2 = 0)
    (hc : CodeIn M P scalar29SubCode) (hbb : CodeIn M (P + 0xFFFFEAFA) blackBoxU8Code)
    (sGC : Sep G 0x60 P scalar29SubCode.length) (sGBB : Sep G 0x60 (P + 0xFFFFEAFA) blackBoxU8Code.length)
    (s : St M P n 0x84 (reg n)) (hsp : reg n sp = G + 0x10) {b : Nat} (hb : b < 2 ^ 32)
    (h24 : reg n 24 = BitVec.ofNat 32 b) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0xAA (reg n') ∧ (∀ x, Sep (G + 0xF) 1 x 1 → M' x = M x) ∧
      reg n' 9 = BitVec.ofNat 32 0 ∧ reg n' 8 = BitVec.ofNat 32 0 ∧ reg n' 22 = ssMask (b / 2 ^ 31) ∧
      reg n' 21 = BitVec.ofNat 32 9 ∧ reg n' 19 = BitVec.ofNat 32 scalarLAddress ∧
      ∀ q : Fin 32, q.val ∉ [1, 8, 9, 10, 19, 21, 22] → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := St.block ssS s hc ssS_end (by simp [BlockOk, BInstr.ok, ssS])
  simp only [runBlock, BInstr.run, ssS] at u1
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1.callRa hc ssub_at_88 ssub_at_8c (cb := P + 0xFFFFEAFA)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP 0xFFFFEAFA (by decide))
  have r2 := PEnv.reg1 regs2 u1.zero
  have sp2 : reg n2 sp = G + 0x10 := by
    rw [r2 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte]; exact hsp
  have e15 : G + 0x10 + 0xFFFFFFFF = G + 0xF := by rw [BitVec.add_assoc]; rfl
  have sBB : Sep (G + 0xF) 1 (P + 0xFFFFEAFA) blackBoxU8Code.length := by
    have := sGBB.sub (c := 0xF) (l := 1) (by decide); exact this
  obtain ⟨n3, c3, pc3, a03, k3, fr3⟩ := blackBoxU8_correct n2 (by rw [mem2]; exact hbb) pc2
    (by rw [regs2]; simp [upd]) (even_clear _ (even_at P hP (0x88 + 8) (by decide)))
    (by rw [sp2, e15]; exact sBB)
  rw [sp2, e15] at fr3
  obtain ⟨M3, hM3⟩ : ∃ M', n3.mem = M' := ⟨_, rfl⟩
  have fr3' : ∀ x, Sep (G + 0xF) 1 x 1 → M3 x = M x := fun x hx => by rw [← hM3, fr3 x hx, mem2]
  have hc3 : CodeIn M3 P scalar29SubCode := fun i hi => by
    have hs : Sep (G + 0xF) 1 (P + BitVec.ofNat 32 i) 1 :=
      (sGC.sub (c := 0xF) (l := 1) (by decide)).subR (c := i) (l := 1) (by omega)
    rw [← hM3, fr3 _ hs.symm.symm, mem2]; exact hc i hi
  have w3 : St M3 P n3 0x90 (reg n3) := ⟨by rw [pc3], hM3, fun _ => rfl⟩
  obtain ⟨n4, c4, u4⟩ := St.block ssM2 w3 hc3 ssM2_end (by simp [BlockOk, BInstr.ok, ssM2])
  simp only [runBlock, BInstr.run, ssM2] at u4
  have hz3 := w3.zero
  obtain ⟨n5, d5, u5⟩ := u4.notTaken hc3 0xAA ssub_at_a6 (by decide) (by
    simp +decide only [branchTaken, upd_app, ↓reduceIte, hz3])
  have a0_3 : reg n3 a0 = ((aluEval .srl (BitVec.ofNat 32 b) 0x1F).extractLsb' 0 8).zeroExtend 32 := by
    rw [a03, r2 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte]; rw [h24]
  have b3 : ∀ q : Fin 32, q.val ∉ [1, 10] → reg n3 q = reg n q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [1, 10] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [k3 q (nq a0 (by decide)), r2 q (nq ra (by decide))]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero, hz]
    simp only [upd_app, h0, nq a0 (by decide), ite_false]
  refine ⟨n5, M3, c1.trans (c2.trans (c3.trans (c4.trans (.single d5)))), u5.self, fr3', ?_, ?_, ?_, ?_, ?_,
    fun q hq => ?_⟩
  · rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte, hz3]
  · rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte, hz3]
  · rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte, hz3]; rw [a0_3]; exact ss_mask hb
  · rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte, hz3]
  · rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte]
  · have nq : ∀ r : Fin 32, r.val ∈ [1, 8, 9, 10, 19, 21, 22] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [u5.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero, hz]
    simp only [upd_app, h0, nq 19 (by decide), nq 21 (by decide), nq 22 (by decide), nq a0 (by decide),
      nq 8 (by decide), nq 9 (by decide), ite_false]
    exact b3 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- From 0xEE to 0xFE: `memcpy` copies `difference` to `out`, with its own 16
bytes of stack at `G`. -/
theorem ss_cpy {M : Word → BitVec 8} {P G out : Word} {n : Machine} (hP : P.toNat % 2 = 0)
    (hc : CodeIn M P scalar29SubCode) (hst : CodeIn M (P + 0x5C04) memcpyStubCode)
    (E : McEnv M (P + 0x5C0C) out (G + 0x10 + 4) G 36)
    (s : St M P n 0xEE (reg n)) (hsp : reg n sp = G + 0x10) (h18 : reg n 18 = out) :
    ∃ n', Steps n n' ∧ St n'.mem P n' 0xFE (reg n') ∧
      (∀ x, Sep G 16 x 1 → n'.mem x = copyBytes M out (G + 0x10 + 4) 36 x) ∧ reg n' sp = G + 0x10 ∧
      ∀ q : Fin 32, q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30] → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := St.block ssT s hc ssT_end (by simp [BlockOk, BInstr.ok, ssT])
  simp only [runBlock, BInstr.run, ssT] at u1
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1.callRa hc ssub_at_f6 ssub_at_fa (cb := P + 0x5C04)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP 0x5C04 (by decide))
  have r2 := PEnv.reg1 regs2 u1.zero
  have sp2 : reg n2 sp = G + 0x10 := by
    rw [r2 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte]; exact hsp
  obtain ⟨n3, c3, pc3, sp3, a03, mem3, K3⟩ := memcpy_correct n2 (P + 0x5C04) (P + BitVec.ofNat 32 (0xF6 + 8))
    out (G + 0x10 + 4) 36 (fun i hi => by show n2.mem _ = _; rw [mem2]; exact hst i hi)
    (even_at P hP 0x5C04 (by decide)) pc2
    (by rw [r2 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte, hz]; rw [h18]; exact zw _)
    (by rw [r2 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte]; rw [hsp]; rfl)
    (by rw [r2 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte, hz])
    (by rw [regs2]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P hP (0xF6 + 8) (by decide)))
    (by
      rw [mem2, sp2, show P + 0x5C04 + 8 = P + 0x5C0C by rw [BitVec.add_assoc]; rfl,
        show G + 0x10 + 0xFFFFFFF0 = G by rw [BitVec.add_assoc]; exact BitVec.add_zero G]
      exact E)
  rw [mem2, sp2, show G + 0x10 + 0xFFFFFFF0 = G by rw [BitVec.add_assoc]; exact BitVec.add_zero G] at mem3
  refine ⟨n3, c1.trans (c2.trans c3), ⟨by rw [pc3], rfl, fun _ => rfl⟩, mem3, by rw [sp3, sp2], fun q hq => ?_⟩
  have nq : ∀ r : Fin 32, r.val ∈ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30] → q ≠ r :=
    fun r hr e => hq (e ▸ hr)
  by_cases hs : q = sp
  · subst hs; rw [sp3, sp2, hsp]
  rw [K3 q (nq a1 (by decide)) (nq a2 (by decide)) (nq a3 (by decide)) (nq a4 (by decide)) (nq a5 (by decide))
    (nq a6 (by decide)) (nq a7 (by decide)) (nq t0 (by decide)) (nq t1 (by decide)) (nq 7 (by decide))
    (nq 28 (by decide)) (nq 29 (by decide)) (nq 30 (by decide)) hs, r2 q (nq ra (by decide))]
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; rw [upd_zero, hz]
  simp only [upd_app, h0, nq a0 (by decide), nq a1 (by decide), nq a2 (by decide), ite_false]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The epilogue, from 0xFE: restore the saved registers and `sp`, and return. -/
theorem ss_epi {M : Word → BitVec 8} {P F : Word} {v : Fin 32 → Word} {n : Machine}
    (st : St M P n 0xFE (reg n)) (hc : CodeIn M P scalar29SubCode) (hFa : F.toNat % 4 = 0) (rsp : reg n sp = F)
    (hsl : ∀ r o, (r, o) ∈ ssPs → memLoad32 M (F + o) = v r) :
    ∃ n', Steps n n' ∧ n'.pc = v ra &&& ~~~1 ∧ reg n' sp = F + 0x50 ∧ n'.mem = M ∧
      (∀ r o, (r, o) ∈ ssPs → reg n' r = v r) ∧
      ∀ q, q.val ∉ [1, 8, 9, 18, 19, 20, 21, 22, 23, 24] → q ≠ sp → reg n' q = reg n q := by
  obtain ⟨n4, c4, u4⟩ := St.block (restoreBlock ssPs) st hc ssRestore_end
    (restoreBlock_ok M _ ssPs (reg n) rsp ssPs_sp fun p hp => fr_al' hFa (ssPs_range p hp).1)
  simp only [restoreBlock_run M _ ssPs (reg n) rsp ssPs_sp] at u4
  have rsp4 : restoreRegs M F (reg n) ssPs sp = F := by rw [restoreRegs_sp _ _ _ _ ssPs_sp]; exact rsp
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc ssub_at_112 (off' := 0x114) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hc ssub_at_114
  refine ⟨n6, c4.trans (.cons d5 (.single d6)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc6]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [add_lit_zero, hsl ra 0x4C (by decide)]
  · rw [regs6]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rsp4]; try rfl
  · exact mem6
  · intro r o h
    rw [regs6]
    simp only [ssPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact hsl _ _ (by decide)
  · intro q hq hs
    have ne : ∀ w : Fin 32, w.val ∈ [1, 8, 9, 18, 19, 20, 21, 22, 23, 24] → q ≠ w := fun w hw e => hq (e ▸ hw)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact (show reg n6 0 = 0 from rfl).trans (show reg n 0 = 0 from rfl).symm
    rw [regs6]
    simp only [upd_app, h0, hs, ite_false]
    simp only [restoreRegs]
    simp only [upd_app, h0, ne ra (by decide), ne 8 (by decide), ne 9 (by decide), ne 18 (by decide),
      ne 19 (by decide), ne 20 (by decide), ne 21 (by decide), ne 22 (by decide), ne 23 (by decide),
      ne 24 (by decide), ite_false]

theorem s29Borrow_congr {a b : Nat → Nat} : ∀ i, (∀ j, j < i → a j = b j) → s29Borrow a i = s29Borrow b i
  | 0, _ => rfl
  | i + 1, h => by
    simp only [s29Borrow]
    rw [h i (by omega), s29Borrow_congr i fun j hj => h j (by omega)]

theorem s29Carry_congr {a b : Nat → Nat} (c : Nat) :
    ∀ i, (∀ j, j < i → a j = b j) → s29Carry a c i = s29Carry b c i
  | 0, _ => rfl
  | i + 1, h => by
    simp only [s29Carry]
    rw [s29Carry_congr c i fun j hj => h j (by omega), s29Borrow_congr (i + 1) h]

theorem s29Out_congr {a b : Nat → Nat} (h : ∀ j, j < 9 → a j = b j) {j : Nat} (hj : j < 9) :
    s29Out a j = s29Out b j := by
  unfold s29Out
  rw [s29Borrow_congr 9 h, s29Carry_congr _ (j + 1) fun k hk => h k (by omega)]

theorem s29_fill0 {M : Word → BitVec 8} {dst : Word} {j : Nat} (hj : j < 9) (hn : dst.toNat + 36 < 2 ^ 32) :
    memLoad32 (fillBytes M dst ((0 : Word).extractLsb' 0 8) 36) (dst + BitVec.ofNat 32 (4 * j)) = 0 := by
  have e : ∀ c, c < 4 → fillBytes M dst ((0 : Word).extractLsb' 0 8) 36 (dst + BitVec.ofNat 32 (4 * j) +
      BitVec.ofNat 32 c) = (0 : Word).extractLsb' 0 8 := fun c hc => by
    rw [add_ofNat_assoc]; unfold fillBytes
    rw [add_sub_toNat dst (by omega), ite_eq_left (by omega)]
  unfold memLoad32
  rw [show (3 : Word) = BitVec.ofNat 32 3 from rfl, show (2 : Word) = BitVec.ofNat 32 2 from rfl,
    show (1 : Word) = BitVec.ofNat 32 1 from rfl, e 3 (by decide), e 2 (by decide), e 1 (by decide),
    show dst + BitVec.ofNat 32 (4 * j) = dst + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 0 from
      (add_ofNat_zero _).symm, e 0 (by decide)]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The compiled `Scalar29::sub(a, &constants::L)`**, called with the
result at `out` and `a` at `ap`: limb `j` of `out` is `s29Out a j`, the
difference `a - L` with `L` added back when it borrowed, limb by limb as the
Rust source computes it. It returns with `sp` and every register but `t0`
through `t6` and `a0` through `a7` as they were, and changes no memory outside
its 0x60 bytes of stack and the result. -/
theorem scalar29Sub_correct (m : Machine) {P G out ap retAddr : Word} (env : SSEnv m.mem P G out ap)
    (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ap) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = G + 0x60) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + 0x60 ∧ (∀ q, feMKeep q = true → reg m' q = reg m q) ∧
      (∀ j, j < 9 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * j)) =
        BitVec.ofNat 32 (s29Out (ssAw m.mem ap) j)) ∧
      ∀ x, Sep G 0x60 x 1 → Sep out 36 x 1 → m'.mem x = m.mem x := by
  have hGt := env.hGt
  have hFa : (G + 0x10).toNat % 4 = 0 := aligned_add env.hG (k := 0x10) (by decide)
  have hLb : (BitVec.ofNat 32 scalarLAddress).toNat % 4 = 0 := by decide
  have hD : (G + 0x10 + 4).toNat = G.toNat + 0x14 := by
    rw [show G + 0x10 + 4 = G + BitVec.ofNat 32 0x14 by rw [BitVec.add_assoc]; rfl, BitVec.toNat_add,
      BitVec.toNat_ofNat]; omega
  obtain ⟨n0, Msv, c0, u0, frSv, hsl, sp0, s8_0, s21_0, s18_0, s19_0, s20_0, s22_0, s24_0, pass0⟩ :=
    ss_pro m env hpc hsp ha0 ha1
  obtain ⟨Mz, hMz⟩ : ∃ M, fillBytes Msv (G + 0x10 + 4) ((0 : Word).extractLsb' 0 8) 36 = M := ⟨_, rfl⟩
  rw [hMz] at u0
  have MzG : ∀ x, Sep G 0x60 x 1 → Mz x = m.mem x := fun x hx => by
    rw [← hMz, fillBytes_sep (ssD_in hx) (Nat.le_refl _)]
    exact frSv x (by have := ssF_in (c := 0) (l := 0x50) (by decide) hx; rwa [add_ofNat_zero] at this)
  have cZ : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x60 b code.length → CodeIn Mz b code :=
    fun hc hs i hi => by rw [MzG _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hAw : ∀ j, j < 9 → ssAw Mz ap j = ssAw m.mem ap j := fun j hj => by
    show (memLoad32 Mz _).toNat = (memLoad32 m.mem _).toNat
    rw [load_frame MzG (env.sAG.symm.subR (c := 4 * j) (l := 4) (by omega))]
  have sDC := ssD_in env.sGC
  have sD1 := ssD_in env.sGI
  have sD2 := ssD_in env.sGIM
  have sDL := ssD_in env.sGL
  have sDA : Sep (G + 0x10 + 4) 36 ap 36 := ssD_in env.sAG.symm
  -- the first loop
  obtain ⟨n1, M1, c1, u1, fr1, hd1, s24_1, k1⟩ := ss_loop1 (Mb := Mz) env.hP (cZ env.code env.sGC)
    (cZ env.idx env.sGI) (cZ env.idxm env.sGIM) (cZ env.ldata env.sGL) hFa env.hap hLb sDC sD1 sD2 sDL sDA
    9 0 n0 Mz rfl (by decide) u0 (fun _ _ => rfl)
    (fun j hj => by rw [ite_eq_right (by omega), ← hMz]; exact s29_fill0 hj (by rw [hD]; omega))
    s8_0 s21_0 s19_0 sp0 s20_0 s22_0 s24_0
  obtain ⟨b9, hb9⟩ : ∃ b, s29Borrow (ssAw Mz ap) 9 = b := ⟨_, rfl⟩
  rw [hb9] at s24_1
  have M1G : ∀ x, Sep G 0x60 x 1 → M1 x = m.mem x := fun x hx => by rw [fr1 x (ssD_in hx), MzG x hx]
  have c1G : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x60 b code.length → CodeIn M1 b code :=
    fun hc hs i hi => by rw [M1G _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have k1' : ∀ q : Fin 32, q.val ∉ [1, 8, 9, 10, 11, 12, 23, 24] → reg n1 q = reg n0 q := k1
  -- `black_box` and the mask
  obtain ⟨n2, M2, c2, u2, fr2, s9_2, s8_2, s22_2, s21_2, s19_2, k2⟩ := ss_mid env.hP (c1G env.code env.sGC)
    (c1G env.bb env.sGBB) env.sGC env.sGBB u1 (by rw [k1' _ (by decide), sp0]) (by rw [← hb9]; exact s29Borrow_lt _ 9)
    s24_1
  have k2' : ∀ q : Fin 32, q.val ∉ [1, 8, 9, 10, 19, 21, 22] → reg n2 q = reg n1 q := k2
  have sGF : ∀ x, Sep G 0x60 x 1 → Sep (G + 0xF) 1 x 1 := fun x hx => hx.sub (c := 0xF) (l := 1) (by decide)
  have M2G : ∀ x, Sep G 0x60 x 1 → M2 x = m.mem x := fun x hx => by rw [fr2 x (sGF x hx), M1G x hx]
  have c2G : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x60 b code.length → CodeIn M2 b code :=
    fun hc hs i hi => by rw [M2G _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have sDF : Sep (G + 0x10 + 4) 36 (G + 0xF) 1 := by
    rw [show G + 0x10 + 4 = G + BitVec.ofNat 32 0x14 by rw [BitVec.add_assoc]; rfl]
    exact sep_offsets G (by decide) (by decide) (by decide)
  have hd2 : ∀ j, j < 9 → memLoad32 M2 (G + 0x10 + 4 + BitVec.ofNat 32 (4 * j)) =
      if j < 0 then BitVec.ofNat 32 (s29Carry (ssAw Mz ap) (b9 / 2 ^ 31) (j + 1) % 2 ^ 29)
      else BitVec.ofNat 32 (s29Borrow (ssAw Mz ap) (j + 1) % 2 ^ 29) := fun j hj => by
    rw [ite_eq_right (by omega), ← hd1 j hj]
    exact load_frame fr2 (sDF.symm.subR (c := 4 * j) (l := 4) (by omega))
  -- `conditional_add_l`
  obtain ⟨n3, M3, c3, u3, fr3, hd3, k3⟩ := ss_loop2 (Mb := M2) (a := ssAw Mz ap) (c := b9 / 2 ^ 31) env.hP
    (c2G env.code env.sGC) (c2G env.idx env.sGI) (c2G env.idxm env.sGIM) (c2G env.ldata env.sGL) hFa hLb
    sDC sD1 sD2 sDL 9 0 n2 M2 rfl (by decide) u2 (fun _ _ => rfl) hd2 s9_2 s19_2
    (by rw [k2' _ (by decide), k1' _ (by decide), sp0]) (by rw [k2' _ (by decide), k1' _ (by decide), s20_0])
    s21_2 s22_2 s8_2
  have k3' : ∀ q : Fin 32, q.val ∉ [1, 8, 9, 10, 11, 12, 23, 24] → reg n3 q = reg n2 q := k3
  have M3G : ∀ x, Sep G 0x60 x 1 → M3 x = m.mem x := fun x hx => by rw [fr3 x (ssD_in hx), M2G x hx]
  have c3G : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x60 b code.length → CodeIn M3 b code :=
    fun hc hs i hi => by rw [M3G _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  -- `memcpy`
  have sOD : Sep out 36 (G + 0x10 + 4) 36 := by
    have := env.sOG.subR (c := 0x14) (l := 36) (by decide)
    rwa [show G + BitVec.ofNat 32 0x14 = G + 0x10 + 4 by rw [BitVec.add_assoc]; rfl] at this
  have E : McEnv M3 (P + 0x5C0C) out (G + 0x10 + 4) G 36 := {
    code := c3G env.body env.sGB
    hDC := env.sOB
    hFC := by have := env.sGB.sub (c := 0) (l := 16) (by decide); rwa [add_ofNat_zero] at this
    hdF := by have := env.sOG.subR (c := 0) (l := 16) (by decide); rwa [add_ofNat_zero] at this
    hsF := by
      rw [show G + 0x10 + 4 = G + BitVec.ofNat 32 0x14 by rw [BitVec.add_assoc]; rfl]
      have := sep_offsets G (c := 0x14) (n := 36) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    hsep := sOD
    hF := env.hG
    hFw := by omega
    hdw := env.hot
    hsw := by rw [hD]; omega }
  obtain ⟨n4, c4, u4, mem4, sp4, k4⟩ := ss_cpy env.hP (c3G env.code env.sGC) (c3G env.stub env.sGS) E u3
    (by rw [k3' _ (by decide), k2' _ (by decide), k1' _ (by decide), sp0])
    (by rw [k3' _ (by decide), k2' _ (by decide), k1' _ (by decide), s18_0])
  have k4' : ∀ q : Fin 32, q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30] → reg n4 q = reg n3 q := k4
  have M4G : ∀ x, Sep G 0x60 x 1 → Sep out 36 x 1 → n4.mem x = m.mem x := fun x hx ho => by
    rw [mem4 x (sep_pre hx (by decide)), copyBytes_sep ho (Nat.le_refl _), M3G x hx]
  have hc4 : CodeIn n4.mem P scalar29SubCode := fun i hi => by
    rw [M4G _ (env.sGC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  -- the saved registers survive
  have sv : ∀ r o, (r, o) ∈ ssPs → memLoad32 n4.mem (G + 0x10 + o) = reg m r := fun r o h => by
    rw [← hsl r o h]
    have ho : o.toNat % 4 = 0 ∧ 0x28 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x50 := ssPs_range (r, o) h
    apply memLoad32_congr
    intro j hj
    have hx : G + 0x10 + o + BitVec.ofNat 32 j = G + BitVec.ofNat 32 (0x10 + o.toNat + j) := by
      rw [← ofNat_toNat_self o, ssG_ofs, add_ofNat_assoc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt o.isLt]
    rw [hx]
    have h16 : Sep G 16 (G + BitVec.ofNat 32 (0x10 + o.toNat + j)) 1 := by
      have := sep_offsets G (c := 0) (n := 16) (d := 0x10 + o.toNat + j) (k := 1) (.inl (by omega)) (by decide)
        (by omega)
      rwa [add_ofNat_zero] at this
    have hO : Sep out 36 (G + BitVec.ofNat 32 (0x10 + o.toNat + j)) 1 :=
      env.sOG.subR (c := 0x10 + o.toNat + j) (l := 1) (by omega)
    have hDx : Sep (G + 0x10 + 4) 36 (G + BitVec.ofNat 32 (0x10 + o.toNat + j)) 1 := by
      rw [show G + 0x10 + 4 = G + BitVec.ofNat 32 0x14 by rw [BitVec.add_assoc]; rfl]
      exact sep_offsets G (.inl (by omega)) (by decide) (by omega)
    have hFx : Sep (G + 0xF) 1 (G + BitVec.ofNat 32 (0x10 + o.toNat + j)) 1 :=
      sep_offsets G (c := 0xF) (.inl (by omega)) (by decide) (by omega)
    rw [mem4 _ h16, copyBytes_sep hO (Nat.le_refl _), fr3 _ hDx, fr2 _ hFx, fr1 _ hDx, ← hMz,
      fillBytes_sep hDx (Nat.le_refl _)]
  -- the epilogue
  obtain ⟨n5, c5, pc5, sp5, mem5, rs5, k5⟩ := ss_epi (v := reg m) u4 hc4 hFa sp4 sv
  have bk : ∀ q : Fin 32, q.val ∈ [3, 4, 25, 26, 27] → reg n5 q = reg m q := fun q hq => by
    have nn : ∀ L : List Nat, (∀ v, v ∈ L → v ∉ [3, 4, 25, 26, 27]) → q.val ∉ L := fun L hL h => hL _ h hq
    rw [k5 q (nn _ (by decide)) (fun e => by rw [e] at hq; simp at hq), k4' q (nn _ (by decide)),
      k3' q (nn _ (by decide)), k2' q (nn _ (by decide)), k1' q (nn _ (by decide)), pass0 q hq]
  refine ⟨n5, c0.trans (c1.trans (c2.trans (c3.trans (c4.trans c5)))), ?_, ?_, fun q hq => ?_, fun j hj => ?_,
    fun x hx ho => ?_⟩
  · rw [pc5, hra, hret]
  · rw [sp5, BitVec.add_assoc]; rfl
  · have hmem : q = 0 ∨ q = sp ∨ q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
        q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q = (23 : Fin 32) ∨
        q = (24 : Fin 32) ∨ q.val ∈ [3, 4, 25, 26, 27] := by
      revert hq; revert q; decide
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    · rfl
    · rw [sp5, BitVec.add_assoc, hsp]; rfl
    · exact rs5 _ 0x4C (by decide)
    · exact rs5 _ 0x48 (by decide)
    · exact rs5 _ 0x44 (by decide)
    · exact rs5 _ 0x40 (by decide)
    · exact rs5 _ 0x3C (by decide)
    · exact rs5 _ 0x38 (by decide)
    · exact rs5 _ 0x34 (by decide)
    · exact rs5 _ 0x30 (by decide)
    · exact rs5 _ 0x2C (by decide)
    · exact rs5 _ 0x28 (by decide)
    · exact bk q h
  · have hs : Sep G 16 (out + BitVec.ofNat 32 (4 * j)) 4 :=
      sep_pre (env.sOG.sub (c := 4 * j) (l := 4) (by omega)).symm (by decide)
    rw [mem5, load_frame (fun a ha => mem4 a ha) hs, cb_load (by omega) (by omega), hd3 j hj,
      ← s29Out_congr hAw hj, ← hb9]
    rfl
  · rw [mem5]; exact M4G x hx ho

end C3.RV32
