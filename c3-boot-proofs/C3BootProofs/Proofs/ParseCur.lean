import C3BootProofs.Proofs.Parse
import C3BootProofs.Proofs.MagicCur
import C3BootProofs.Proofs.PartCur
import C3BootProofs.Proofs.KeySet

/-!
# `c3_verify::manifest::parse`, as compiled

The current image compiles `parse` as V0 did, with the register saves and
restores inline instead of in outlined helpers. The checks and the stores
are the same, so the spec is V0's: `parseErr` is the error the compiled
checks return, and `parseMem` is the memory they leave.
`manifestParse_correct` proves the function computes them, with each call
through the callee's theorem. The code sits at its absolute address, above
`0x40000000`, and the stack, manifest, and result sit below it.
-/

namespace C3.RV32.Cur

open C3.Image

/-- Where the image puts `parse`. -/
abbrev MP : Word := BitVec.ofNat 32 manifestParseAddress

/-- The functions `parse` runs, where the image puts them. -/
structure MPCode (M : Word → BitVec 8) : Prop where
  parse : CodeIn M MP manifestParseCode
  magic : CodeIn M (BitVec.ofNat 32 readerMagicAddress) readerMagicCode
  array4 : CodeIn M (BitVec.ofNat 32 readerArray4Address) readerArray4Code
  bytes : CodeIn M (BitVec.ofNat 32 readerBytesAddress) readerBytesCode
  version : CodeIn M (BitVec.ofNat 32 readerVersion1Address) readerVersion1Code
  u16 : CodeIn M (BitVec.ofNat 32 readerU16Address) readerU16Code
  reserved : CodeIn M (BitVec.ofNat 32 readerReservedAddress) readerReservedCode
  part : CodeIn M (BitVec.ofNat 32 manifestPartAddress) manifestPartCode
  u32 : CodeIn M (BitVec.ofNat 32 readerU32Address) readerU32Code

set_option maxRecDepth 8000 in
theorem MPCode.hi {M M' : Word → BitVec 8} (c : MPCode M)
    (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) : MPCode M' :=
  ⟨c.parse.hi h (by decide) (by decide), c.magic.hi h (by decide) (by decide),
    c.array4.hi h (by decide) (by decide), c.bytes.hi h (by decide) (by decide),
    c.version.hi h (by decide) (by decide), c.u16.hi h (by decide) (by decide),
    c.reserved.hi h (by decide) (by decide), c.part.hi h (by decide) (by decide),
    c.u32.hi h (by decide) (by decide)⟩

/-- `parse`'s stack: 144 bytes at `R`, its 64-byte frame at `G = R + 80` and
up to 80 bytes for its callees, below `0x40000000`, with the 40-byte
manifest at `bp` apart from it. -/
structure MLay (R G bp : Word) : Prop where
  hRG : G = R + BitVec.ofNat 32 80
  hR : R.toNat + 144 ≤ 0x40000000
  hG : G.toNat % 4 = 0
  hbp : bp ≠ 0 ∧ bp.toNat + 40 ≤ 2 ^ 32
  hBS : Sep bp 40 R 144

theorem stackStack (R : Word) (c n d l : Nat) (hn : c + n ≤ 144) (hl : d + l ≤ 144) (h : c + n ≤ d ∨ d + l ≤ c) :
    Sep (R + BitVec.ofNat 32 c) n (R + BitVec.ofNat 32 d) l :=
  sep_offsets R h (by omega) (by omega)

namespace MLay

variable {R G bp : Word}

theorem g_ofs (L : MLay R G bp) (c : Nat) : G + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (80 + c) := by
  rw [L.hRG, add_ofNat_assoc]

theorem r_eqs (L : MLay R G bp) :
    G + 0xFFFFFFD0 = R + BitVec.ofNat 32 32 ∧ G + 0xFFFFFFE0 = R + BitVec.ofNat 32 48 ∧
    G + 0xFFFFFFF0 = R + BitVec.ofNat 32 64 ∧ G + 0xFFFFFFB0 = R ∧ G + 8 = R + BitVec.ofNat 32 88 ∧
    G + 8 + 8 = R + BitVec.ofNat 32 96 ∧ G + 0x14 = R + BitVec.ofNat 32 100 := by
  rw [L.hRG]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [BitVec.add_assoc] <;> try rfl
  exact BitVec.add_zero R

theorem low (L : MLay R G bp) (c n : Nat) (h : c + n ≤ 144) : (R + BitVec.ofNat 32 c).toNat + n ≤ 0x40000000 := by
  have := L.hR
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem hiS (L : MLay R G bp) (x : Word) (hx : 0x40000000 ≤ x.toNat) : Sep R 144 x 1 :=
  sep_of_le (by have := L.hR; omega) (by have := x.isLt; omega)

theorem code {M0 Mx : Word → BitVec 8} (L : MLay R G bp) (c0 : MPCode M0)
    (hO : ∀ x, Sep R 144 x 1 → Mx x = M0 x) : MPCode Mx :=
  c0.hi fun x hx => hO x (L.hiS x hx)

/-- A stack range apart from code above `0x40000000`. -/
theorem lo (L : MLay R G bp) {c n : Nat} (h : c + n ≤ 144) {b : Word} {l : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + l ≤ 2 ^ 32) : Sep (R + BitVec.ofNat 32 c) n b l :=
  lowSep (L.low c n h) hb hbl

end MLay

section
set_option maxRecDepth 20000
theorem mpc_at_0 : fetchRel manifestParseCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem mpc_at_2 : fetchRel manifestParseCode 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem mpc_at_4 : fetchRel manifestParseCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem mpc_at_6 : fetchRel manifestParseCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem mpc_at_8 : fetchRel manifestParseCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem mpc_at_a : fetchRel manifestParseCode 0xA = some (.store .sw sp (19 : Fin 32) 0x2C, 2) := by decide
theorem mpc_at_c : fetchRel manifestParseCode 0xC = some (.store .sw sp (20 : Fin 32) 0x28, 2) := by decide
theorem mpc_at_e : fetchRel manifestParseCode 0xE = some (.store .sw sp (21 : Fin 32) 0x24, 2) := by decide
theorem mpc_at_10 : fetchRel manifestParseCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x20, 2) := by decide
theorem mpc_at_12 : fetchRel manifestParseCode 0x12 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem mpc_at_14 : fetchRel manifestParseCode 0x14 = some (.aluImm .add a0 x0 0x28, 4) := by decide
theorem mpc_at_18 : fetchRel manifestParseCode 0x18 = some (.store .sw sp a1 0x8, 2) := by decide
theorem mpc_at_1a : fetchRel manifestParseCode 0x1A = some (.store .sw sp a0 0xC, 2) := by decide
theorem mpc_at_1c : fetchRel manifestParseCode 0x1C = some (.store .sw sp x0 0x10, 2) := by decide
theorem mpc_at_1e : fetchRel manifestParseCode 0x1E = some (.lui a1 0x4C533000, 4) := by decide
theorem mpc_at_22 : fetchRel manifestParseCode 0x22 = some (.aluImm .add a1 a1 0x343, 4) := by decide
theorem mpc_at_26 : fetchRel manifestParseCode 0x26 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem mpc_at_28 : fetchRel manifestParseCode 0x28 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem mpc_at_2c : fetchRel manifestParseCode 0x2C = some (.jalr ra ra 0xEE, 4) := by decide
theorem mpc_at_30 : fetchRel manifestParseCode 0x30 = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem mpc_at_34 : fetchRel manifestParseCode 0x34 = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem mpc_at_38 : fetchRel manifestParseCode 0x38 = some (.branch .bne a1 x0 0x9E, 2) := by decide
theorem mpc_at_3a : fetchRel manifestParseCode 0x3A = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem mpc_at_3c : fetchRel manifestParseCode 0x3C = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem mpc_at_40 : fetchRel manifestParseCode 0x40 = some (.jalr ra ra 0x12C, 4) := by decide
theorem mpc_at_44 : fetchRel manifestParseCode 0x44 = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem mpc_at_48 : fetchRel manifestParseCode 0x48 = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem mpc_at_4c : fetchRel manifestParseCode 0x4C = some (.branch .bne a1 x0 0x8A, 2) := by decide
theorem mpc_at_4e : fetchRel manifestParseCode 0x4E = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem mpc_at_50 : fetchRel manifestParseCode 0x50 = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem mpc_at_52 : fetchRel manifestParseCode 0x52 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem mpc_at_56 : fetchRel manifestParseCode 0x56 = some (.jalr ra ra 0x17A, 4) := by decide
theorem mpc_at_5a : fetchRel manifestParseCode 0x5A = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem mpc_at_5e : fetchRel manifestParseCode 0x5E = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem mpc_at_62 : fetchRel manifestParseCode 0x62 = some (.branch .bne a1 x0 0x74, 2) := by decide
theorem mpc_at_64 : fetchRel manifestParseCode 0x64 = some (.aluImm .add a0 sp 0x14, 2) := by decide
theorem mpc_at_66 : fetchRel manifestParseCode 0x66 = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem mpc_at_68 : fetchRel manifestParseCode 0x68 = some (.aluImm .add a2 x0 0x25, 4) := by decide
theorem mpc_at_6c : fetchRel manifestParseCode 0x6C = some (.lui a3 0x1D0000, 4) := by decide
theorem mpc_at_70 : fetchRel manifestParseCode 0x70 = some (.auipc ra 0x0, 4) := by decide
theorem mpc_at_74 : fetchRel manifestParseCode 0x74 = some (.jalr ra ra 0xFA, 4) := by decide
theorem mpc_at_78 : fetchRel manifestParseCode 0x78 = some (.load .lbu a0 sp 0x14, 4) := by decide
theorem mpc_at_7c : fetchRel manifestParseCode 0x7C = some (.branch .bne a0 x0 0x56, 2) := by decide
theorem mpc_at_7e : fetchRel manifestParseCode 0x7E = some (.load .lw (9 : Fin 32) sp 0x18, 2) := by decide
theorem mpc_at_80 : fetchRel manifestParseCode 0x80 = some (.load .lw (22 : Fin 32) sp 0x1C, 2) := by decide
theorem mpc_at_82 : fetchRel manifestParseCode 0x82 = some (.aluImm .add a0 sp 0x14, 2) := by decide
theorem mpc_at_84 : fetchRel manifestParseCode 0x84 = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem mpc_at_86 : fetchRel manifestParseCode 0x86 = some (.aluImm .add a2 x0 0x31, 4) := by decide
theorem mpc_at_8a : fetchRel manifestParseCode 0x8A = some (.lui a3 0x4000, 2) := by decide
theorem mpc_at_8c : fetchRel manifestParseCode 0x8C = some (.auipc ra 0x0, 4) := by decide
theorem mpc_at_90 : fetchRel manifestParseCode 0x90 = some (.jalr ra ra 0xDE, 4) := by decide
theorem mpc_at_94 : fetchRel manifestParseCode 0x94 = some (.load .lbu a0 sp 0x14, 4) := by decide
theorem mpc_at_98 : fetchRel manifestParseCode 0x98 = some (.branch .bne a0 x0 0x3A, 2) := by decide
theorem mpc_at_9a : fetchRel manifestParseCode 0x9A = some (.load .lw (18 : Fin 32) sp 0x18, 2) := by decide
theorem mpc_at_9c : fetchRel manifestParseCode 0x9C = some (.load .lw (19 : Fin 32) sp 0x1C, 2) := by decide
theorem mpc_at_9e : fetchRel manifestParseCode 0x9E = some (.aluImm .add a3 x0 0x1, 2) := by decide
theorem mpc_at_a0 : fetchRel manifestParseCode 0xA0 = some (.aluImm .sll a3 a3 0xB, 2) := by decide
theorem mpc_at_a2 : fetchRel manifestParseCode 0xA2 = some (.aluImm .add a0 sp 0x14, 2) := by decide
theorem mpc_at_a4 : fetchRel manifestParseCode 0xA4 = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem mpc_at_a6 : fetchRel manifestParseCode 0xA6 = some (.aluImm .add a2 x0 0x8, 2) := by decide
theorem mpc_at_a8 : fetchRel manifestParseCode 0xA8 = some (.auipc ra 0x0, 4) := by decide
theorem mpc_at_ac : fetchRel manifestParseCode 0xAC = some (.jalr ra ra 0xC2, 4) := by decide
theorem mpc_at_b0 : fetchRel manifestParseCode 0xB0 = some (.load .lbu a0 sp 0x14, 4) := by decide
theorem mpc_at_b4 : fetchRel manifestParseCode 0xB4 = some (.branch .bne a0 x0 0x1E, 2) := by decide
theorem mpc_at_b6 : fetchRel manifestParseCode 0xB6 = some (.load .lw (20 : Fin 32) sp 0x18, 2) := by decide
theorem mpc_at_b8 : fetchRel manifestParseCode 0xB8 = some (.load .lw (21 : Fin 32) sp 0x1C, 2) := by decide
theorem mpc_at_ba : fetchRel manifestParseCode 0xBA = some (.aluImm .add a0 sp 0x14, 2) := by decide
theorem mpc_at_bc : fetchRel manifestParseCode 0xBC = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem mpc_at_be : fetchRel manifestParseCode 0xBE = some (.aluImm .add a2 x0 0x1BB, 4) := by decide
theorem mpc_at_c2 : fetchRel manifestParseCode 0xC2 = some (.lui a3 0x1000, 2) := by decide
theorem mpc_at_c4 : fetchRel manifestParseCode 0xC4 = some (.auipc ra 0x0, 4) := by decide
theorem mpc_at_c8 : fetchRel manifestParseCode 0xC8 = some (.jalr ra ra 0xA6, 4) := by decide
theorem mpc_at_cc : fetchRel manifestParseCode 0xCC = some (.load .lbu a0 sp 0x14, 4) := by decide
theorem mpc_at_d0 : fetchRel manifestParseCode 0xD0 = some (.branch .beq a0 x0 0x24, 2) := by decide
theorem mpc_at_d2 : fetchRel manifestParseCode 0xD2 = some (.load .lbu a0 sp 0x15, 4) := by decide
theorem mpc_at_d6 : fetchRel manifestParseCode 0xD6 = some (.store .sb (8 : Fin 32) a0 0x1, 4) := by decide
theorem mpc_at_da : fetchRel manifestParseCode 0xDA = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem mpc_at_dc : fetchRel manifestParseCode 0xDC = some (.store .sb (8 : Fin 32) a0 0x0, 4) := by decide
theorem mpc_at_e0 : fetchRel manifestParseCode 0xE0 = some (.load .lw ra sp 0x3C, 2) := by decide
theorem mpc_at_e2 : fetchRel manifestParseCode 0xE2 = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem mpc_at_e4 : fetchRel manifestParseCode 0xE4 = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem mpc_at_e6 : fetchRel manifestParseCode 0xE6 = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem mpc_at_e8 : fetchRel manifestParseCode 0xE8 = some (.load .lw (19 : Fin 32) sp 0x2C, 2) := by decide
theorem mpc_at_ea : fetchRel manifestParseCode 0xEA = some (.load .lw (20 : Fin 32) sp 0x28, 2) := by decide
theorem mpc_at_ec : fetchRel manifestParseCode 0xEC = some (.load .lw (21 : Fin 32) sp 0x24, 2) := by decide
theorem mpc_at_ee : fetchRel manifestParseCode 0xEE = some (.load .lw (22 : Fin 32) sp 0x20, 2) := by decide
theorem mpc_at_f0 : fetchRel manifestParseCode 0xF0 = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem mpc_at_f2 : fetchRel manifestParseCode 0xF2 = some (.jalr x0 ra 0x0, 2) := by decide
theorem mpc_at_f4 : fetchRel manifestParseCode 0xF4 = some (.load .lw a0 sp 0xC, 2) := by decide
theorem mpc_at_f6 : fetchRel manifestParseCode 0xF6 = some (.load .lw a1 sp 0x10, 2) := by decide
theorem mpc_at_f8 : fetchRel manifestParseCode 0xF8 = some (.branch .bne a1 a0 0x6A, 4) := by decide
theorem mpc_at_fc : fetchRel manifestParseCode 0xFC = some (.lui a3 0x10000, 2) := by decide
theorem mpc_at_fe : fetchRel manifestParseCode 0xFE = some (.branch .bne (9 : Fin 32) a3 0x68, 4) := by decide
theorem mpc_at_102 : fetchRel manifestParseCode 0x102 = some (.lui a0 0xFFFF0000, 2) := by decide
theorem mpc_at_104 : fetchRel manifestParseCode 0x104 = some (.aluImm .add a1 a0 0xFFFFFFFF, 4) := by decide
theorem mpc_at_108 : fetchRel manifestParseCode 0x108 = some (.aluImm .add a0 x0 0x6, 2) := by decide
theorem mpc_at_10a : fetchRel manifestParseCode 0x10A = some (.branch .bltu a1 (22 : Fin 32) 0xFFFFFFCC, 4) := by decide
theorem mpc_at_10e : fetchRel manifestParseCode 0x10E = some (.alu .add a4 (19 : Fin 32) (18 : Fin 32), 4) := by decide
theorem mpc_at_112 : fetchRel manifestParseCode 0x112 = some (.branch .bltu a4 (19 : Fin 32) 0xFFFFFFC4, 4) := by decide
theorem mpc_at_116 : fetchRel manifestParseCode 0x116 = some (.alu .add a5 (21 : Fin 32) (20 : Fin 32), 4) := by decide
theorem mpc_at_11a : fetchRel manifestParseCode 0x11A = some (.branch .bltu a5 (21 : Fin 32) 0xFFFFFFBC, 4) := by decide
theorem mpc_at_11e : fetchRel manifestParseCode 0x11E = some (.load .lw (9 : Fin 32) sp 0x18, 2) := by decide
theorem mpc_at_120 : fetchRel manifestParseCode 0x120 = some (.load .lw a2 sp 0x1C, 2) := by decide
theorem mpc_at_122 : fetchRel manifestParseCode 0x122 = some (.alu .add a1 a2 (9 : Fin 32), 4) := by decide
theorem mpc_at_126 : fetchRel manifestParseCode 0x126 = some (.branch .bltu a1 a2 0xFFFFFFB0, 4) := by decide
theorem mpc_at_12a : fetchRel manifestParseCode 0x12A = some (.alu .add a3 a3 (22 : Fin 32), 2) := by decide
theorem mpc_at_12c : fetchRel manifestParseCode 0x12C = some (.branch .bltu (18 : Fin 32) a3 0x3A, 4) := by decide
theorem mpc_at_130 : fetchRel manifestParseCode 0x130 = some (.branch .bltu (20 : Fin 32) a4 0x36, 4) := by decide
theorem mpc_at_134 : fetchRel manifestParseCode 0x134 = some (.branch .bltu (9 : Fin 32) a5 0x32, 4) := by decide
theorem mpc_at_138 : fetchRel manifestParseCode 0x138 = some (.lui a3 0x1E0000, 4) := by decide
theorem mpc_at_13c : fetchRel manifestParseCode 0x13C = some (.aluImm .add a0 x0 0x7, 2) := by decide
theorem mpc_at_13e : fetchRel manifestParseCode 0x13E = some (.branch .bltu a3 a1 0xFFFFFF98, 4) := by decide
theorem mpc_at_142 : fetchRel manifestParseCode 0x142 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem mpc_at_144 : fetchRel manifestParseCode 0x144 = some (.lui a1 0x10000, 2) := by decide
theorem mpc_at_146 : fetchRel manifestParseCode 0x146 = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem mpc_at_148 : fetchRel manifestParseCode 0x148 = some (.store .sw (8 : Fin 32) (22 : Fin 32) 0x8, 4) := by decide
theorem mpc_at_14c : fetchRel manifestParseCode 0x14C = some (.store .sw (8 : Fin 32) (18 : Fin 32) 0xC, 4) := by decide
theorem mpc_at_150 : fetchRel manifestParseCode 0x150 = some (.store .sw (8 : Fin 32) (19 : Fin 32) 0x10, 4) := by decide
theorem mpc_at_154 : fetchRel manifestParseCode 0x154 = some (.store .sw (8 : Fin 32) (20 : Fin 32) 0x14, 4) := by decide
theorem mpc_at_158 : fetchRel manifestParseCode 0x158 = some (.store .sw (8 : Fin 32) (21 : Fin 32) 0x18, 4) := by decide
theorem mpc_at_15c : fetchRel manifestParseCode 0x15C = some (.store .sw (8 : Fin 32) (9 : Fin 32) 0x1C, 2) := by decide
theorem mpc_at_15e : fetchRel manifestParseCode 0x15E = some (.store .sw (8 : Fin 32) a2 0x20, 2) := by decide
theorem mpc_at_160 : fetchRel manifestParseCode 0x160 = some (.jal x0 0xFFFFFF7C, 2) := by decide
theorem mpc_at_162 : fetchRel manifestParseCode 0x162 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem mpc_at_164 : fetchRel manifestParseCode 0x164 = some (.jal x0 0xFFFFFF72, 2) := by decide
theorem mpc_at_166 : fetchRel manifestParseCode 0x166 = some (.aluImm .add a0 x0 0x7, 2) := by decide
theorem mpc_at_168 : fetchRel manifestParseCode 0x168 = some (.jal x0 0xFFFFFF6E, 2) := by decide
end

theorem MLay.advance {R G bp : Word} (Ly : MLay R G bp) {M0 M2 Mx My : Word → BitVec 8}
    {e : Word} {c N : Nat} (hcN : c + N ≤ 80)
    (hrp : memLoad32 Mx (G + 8) = bp) (hrl : memLoad32 Mx (G + 8 + 4) = 40)
    (hO : ∀ x, Sep R 144 x 1 → Mx x = M0 x)
    (hS : ∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k))
    (hm : ∀ x, Sep (R + BitVec.ofNat 32 c) N x 1 → My x = memStore32 Mx (G + 8 + 8) e x) :
    memLoad32 My (G + 8) = bp ∧ memLoad32 My (G + 8 + 4) = 40 ∧ memLoad32 My (G + 8 + 8) = e ∧
    (∀ x, Sep R 144 x 1 → My x = M0 x) ∧
    (∀ k, 0x20 ≤ k → k < 0x40 → My (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) := by
  obtain ⟨-, -, -, -, e88, e96, -⟩ := Ly.r_eqs
  have fr : ∀ k, 8 ≤ k → k < 64 → Sep (R + BitVec.ofNat 32 c) N (G + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    rw [Ly.g_ofs]; exact stackStack R c N (80 + k) 1 (by omega) (by omega) (by omega)
  have ld : ∀ k, 8 ≤ k → k + 4 ≤ 64 →
      memLoad32 My (G + BitVec.ofNat 32 k) = memLoad32 (memStore32 Mx (G + 8 + 8) e) (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hm _ (fr (k + j) (by omega) (by omega))
  have p16 : G + 8 + 8 = G + BitVec.ofNat 32 16 := by rw [BitVec.add_assoc]; rfl
  refine ⟨?_, ?_, ?_, fun x hx => ?_, fun k h1 h2 => ?_⟩
  · rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, ld 8 (by omega) (by omega), p16,
      memLoad32_store32_sep (sep_offsets G (c := 16) (n := 4) (d := 8) (k := 4) (by omega) (by omega) (by omega))]
    exact hrp
  · rw [show G + 8 + 4 = G + BitVec.ofNat 32 12 from by rw [BitVec.add_assoc]; rfl, ld 12 (by omega) (by omega), p16,
      memLoad32_store32_sep (sep_offsets G (c := 16) (n := 4) (d := 12) (k := 4) (by omega) (by omega) (by omega)),
      show G + BitVec.ofNat 32 12 = G + 8 + 4 from by rw [BitVec.add_assoc]; rfl]
    exact hrl
  · rw [p16, ld 16 (by omega) (by omega), ← p16]; exact memLoad32_store32_same _ _ _
  · have hx' : Sep (R + BitVec.ofNat 32 c) N x 1 := (hx.sub (c := c) (l := N) (by omega))
    rw [hm x hx', memStore32_get_sep (by rw [e96]; exact hx.sub (c := 96) (l := 4) (by omega)), hO x hx]
  · rw [hm _ (fr k (by omega) (by omega)), p16,
      memStore32_get_sep (sep_offsets G (c := 16) (n := 4) (d := k) (k := 1) (by omega) (by omega) (by omega))]
    exact hS k h1 h2

/-- After an in-range `part`, as `PEnv.advance`, with the part in the frame
at `G + 0x14`. -/
theorem MLay.advance_part_ok {R G bp : Word} (Ly : MLay R G bp)
    {M0 M2 Mx My : Word → BitVec 8} {e v1 v2 : Word}
    (hrp : memLoad32 Mx (G + 8) = bp) (hrl : memLoad32 Mx (G + 8 + 4) = 40)
    (hO : ∀ x, Sep R 144 x 1 → Mx x = M0 x)
    (hS : ∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k))
    (hm : ∀ x, Sep R 80 x 1 → My x = memStore8 (memStore32 (memStore32 (memStore32 Mx (G + 8 + 8) e)
      (G + 0x14 + 4) v1) (G + 0x14 + 8) v2) (G + 0x14) 0 x) :
    memLoad32 My (G + 8) = bp ∧ memLoad32 My (G + 8 + 4) = 40 ∧ memLoad32 My (G + 8 + 8) = e ∧
    (∀ x, Sep R 144 x 1 → My x = M0 x) ∧
    (∀ k, 0x20 ≤ k → k < 0x40 → My (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) ∧
    My (G + 0x14) = 0 ∧ memLoad32 My (G + 0x18) = v1 ∧ memLoad32 My (G + 0x1C) = v2 := by
  obtain ⟨-, -, -, -, -, e96, e100⟩ := Ly.r_eqs
  have fr : ∀ k, 8 ≤ k → k < 64 → Sep (R + BitVec.ofNat 32 0) 80 (G + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    rw [Ly.g_ofs]; exact stackStack R 0 80 (80 + k) 1 (by omega) (by omega) (by omega)
  have fr' : ∀ k, 8 ≤ k → k < 64 → Sep R 80 (G + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    have := fr k h1 h2; rwa [add_ofNat_zero] at this
  have eqs : G + 8 + 8 = G + BitVec.ofNat 32 16 ∧ G + 0x14 + 4 = G + BitVec.ofNat 32 0x18 ∧
      G + 0x14 + 8 = G + BitVec.ofNat 32 0x1C ∧ G + 0x14 = G + BitVec.ofNat 32 0x14 := by
    refine ⟨?_, ?_, ?_, rfl⟩ <;> (rw [BitVec.add_assoc]; rfl)
  obtain ⟨q16, q18, q1c, q14⟩ := eqs
  rw [q16, q18, q1c, q14] at hm
  -- The value of the store chain at a frame byte.
  have T : ∀ k, 8 ≤ k → k < 64 → My (G + BitVec.ofNat 32 k) =
      memStore8 (memStore32 (memStore32 (memStore32 Mx (G + BitVec.ofNat 32 16) e)
        (G + BitVec.ofNat 32 0x18) v1) (G + BitVec.ofNat 32 0x1C) v2) (G + BitVec.ofNat 32 0x14) 0
        (G + BitVec.ofNat 32 k) := fun k h1 h2 => hm _ (fr' k h1 h2)
  have so : ∀ a l b k, a + l ≤ b ∨ b + k ≤ a → a + l ≤ 64 → b + k ≤ 64 →
      Sep (G + BitVec.ofNat 32 a) l (G + BitVec.ofNat 32 b) k :=
    fun a l b k h h1 h2 => sep_offsets G h (by omega) (by omega)
  have ne : ∀ a b, a < 64 → b < 64 → a ≠ b → G + BitVec.ofNat 32 b ≠ G + BitVec.ofNat 32 a :=
    fun a b ha hb h => add_ofNat_ne G (by omega) (by omega) (Ne.symm h)
  have L : ∀ k, 8 ≤ k → k + 4 ≤ 64 → memLoad32 My (G + BitVec.ofNat 32 k) =
      memLoad32 (memStore8 (memStore32 (memStore32 (memStore32 Mx (G + BitVec.ofNat 32 16) e)
        (G + BitVec.ofNat 32 0x18) v1) (G + BitVec.ofNat 32 0x1C) v2) (G + BitVec.ofNat 32 0x14) 0)
        (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact T (k + j) (by omega) (by omega)
  refine ⟨?_, ?_, ?_, fun x hx => ?_, fun k h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, L 8 (by omega) (by omega),
      memLoad32_store8_sep (so 0x14 1 8 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x1C 4 8 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x18 4 8 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 16 4 8 4 (by omega) (by omega) (by omega))]
    exact hrp
  · rw [show G + 8 + 4 = G + BitVec.ofNat 32 12 from by rw [BitVec.add_assoc]; rfl, L 12 (by omega) (by omega),
      memLoad32_store8_sep (so 0x14 1 12 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x1C 4 12 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x18 4 12 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 16 4 12 4 (by omega) (by omega) (by omega)),
      show G + BitVec.ofNat 32 12 = G + 8 + 4 from by rw [BitVec.add_assoc]; rfl]
    exact hrl
  · rw [q16, L 16 (by omega) (by omega),
      memLoad32_store8_sep (so 0x14 1 16 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x1C 4 16 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x18 4 16 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_same]
  · have hx' : Sep R 80 x 1 := by have := hx.sub (c := 0) (l := 80) (by omega); rwa [add_ofNat_zero] at this
    have g : ∀ a l, 8 ≤ a → a + l ≤ 64 → Sep (G + BitVec.ofNat 32 a) l x 1 := fun a l h1 h2 => by
      rw [Ly.g_ofs]; exact hx.sub (c := 80 + a) (l := l) (by omega)
    have g1 : x ≠ G + BitVec.ofNat 32 0x14 := fun h => g 0x14 1 (by omega) (by omega) 0 (by omega) 0 (by omega)
      (by rw [add_ofNat_zero, add_ofNat_zero, h])
    rw [hm x hx', memStore8_ne g1, memStore32_get_sep (g 0x1C 4 (by omega) (by omega)),
      memStore32_get_sep (g 0x18 4 (by omega) (by omega)), memStore32_get_sep (g 16 4 (by omega) (by omega)),
      hO x hx]
  · rw [T k (by omega) h2, memStore8_ne (ne 0x14 k (by omega) h2 (by omega)),
      memStore32_get_sep (so 0x1C 4 k 1 (by omega) (by omega) (by omega)),
      memStore32_get_sep (so 0x18 4 k 1 (by omega) (by omega) (by omega)),
      memStore32_get_sep (so 16 4 k 1 (by omega) (by omega) (by omega))]
    exact hS k h1 h2
  · rw [q14, T 0x14 (by omega) (by omega), memStore8_same]
  · rw [show G + 0x18 = G + BitVec.ofNat 32 0x18 from rfl, L 0x18 (by omega) (by omega),
      memLoad32_store8_sep (so 0x14 1 0x18 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x1C 4 0x18 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_same]
  · rw [show G + 0x1C = G + BitVec.ofNat 32 0x1C from rfl, L 0x1C (by omega) (by omega),
      memLoad32_store8_sep (so 0x14 1 0x1C 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_same]

/-- After an out-of-range `part`: the tag and error byte in the frame, the
rest of memory, and the saved slots. -/
theorem MLay.advance_part_err {R G bp : Word} (Ly : MLay R G bp)
    {M0 M2 Mx My : Word → BitVec 8} {e : Word}
    (hO : ∀ x, Sep R 144 x 1 → Mx x = M0 x)
    (hS : ∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k))
    (hm : ∀ x, Sep R 80 x 1 → My x = memStore8 (memStore8 (memStore32 Mx (G + 8 + 8) e)
      (G + 0x14 + 1) 5) (G + 0x14) 1 x) :
    (∀ x, Sep R 144 x 1 → My x = M0 x) ∧
    (∀ k, 0x20 ≤ k → k < 0x40 → My (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) ∧
    My (G + 0x14) = 1 ∧ My (G + 0x15) = 5 := by
  have fr' : ∀ k, 8 ≤ k → k < 64 → Sep R 80 (G + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    rw [Ly.g_ofs]; have := stackStack R 0 80 (80 + k) 1 (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have q16 : G + 8 + 8 = G + BitVec.ofNat 32 16 := by rw [BitVec.add_assoc]; rfl
  have q15 : G + 0x14 + 1 = G + BitVec.ofNat 32 0x15 := by rw [BitVec.add_assoc]; rfl
  rw [q16, q15, show G + 0x14 = G + BitVec.ofNat 32 0x14 from rfl] at hm
  have ne : ∀ a b, a < 64 → b < 64 → a ≠ b → G + BitVec.ofNat 32 b ≠ G + BitVec.ofNat 32 a :=
    fun a b ha hb h => add_ofNat_ne G (by omega) (by omega) (Ne.symm h)
  refine ⟨fun x hx => ?_, fun k h1 h2 => ?_, ?_, ?_⟩
  · have hx' : Sep R 80 x 1 := by have := hx.sub (c := 0) (l := 80) (by omega); rwa [add_ofNat_zero] at this
    have g : ∀ a l, 8 ≤ a → a + l ≤ 64 → Sep (G + BitVec.ofNat 32 a) l x 1 := fun a l h1 h2 => by
      rw [Ly.g_ofs]; exact hx.sub (c := 80 + a) (l := l) (by omega)
    have gne : ∀ a, 8 ≤ a → a < 64 → x ≠ G + BitVec.ofNat 32 a := fun a h1 h2 h =>
      g a 1 h1 (by omega) 0 (by omega) 0 (by omega) (by rw [add_ofNat_zero, add_ofNat_zero, h])
    rw [hm x hx', memStore8_ne (gne 0x14 (by omega) (by omega)), memStore8_ne (gne 0x15 (by omega) (by omega)),
      memStore32_get_sep (g 16 4 (by omega) (by omega)), hO x hx]
  · rw [hm _ (fr' k (by omega) h2), memStore8_ne (ne 0x14 k (by omega) h2 (by omega)),
      memStore8_ne (ne 0x15 k (by omega) h2 (by omega)),
      memStore32_get_sep (sep_offsets G (c := 16) (n := 4) (d := k) (k := 1) (by omega) (by omega) (by omega))]
    exact hS k h1 h2
  · rw [show G + 0x14 = G + BitVec.ofNat 32 0x14 from rfl, hm _ (fr' 0x14 (by omega) (by omega)), memStore8_same]
  · rw [show G + 0x15 = G + BitVec.ofNat 32 0x15 from rfl, hm _ (fr' 0x15 (by omega) (by omega)),
      memStore8_ne (ne 0x14 0x15 (by omega) (by omega) (by omega)), memStore8_same]

theorem mp_reg1 {f : Fin 32 → Word} {m1 : Machine} {L : Word}
    (regs : ∀ r, reg m1 r = upd f ra L r) (hz : f 0 = 0) : ∀ r, r ≠ ra → reg m1 r = f r := fun r h => by
  rw [regs]; exact updz hz h

/-- A call from `parse` to `Reader::magic` on the reader at `G + 8`. -/
theorem mp_magic {R G bp : Word} (Ly : MLay R G bp) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {k imm o : Word} (s : St Mx MP m off f)
    (code : MPCode Mx)
    (h1 : fetchRel manifestParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel manifestParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : MP + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 readerMagicAddress)
    (hl : (MP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 8) (ha1 : f a1 = k)
    (hrp : memLoad32 Mx (G + 8) = bp) (hrl : memLoad32 Mx (G + 8 + 4) = 40) :
    ∃ m', Steps m m' ∧ St m'.mem MP m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = magicResult Mx (G + 8) k ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep (G + 0xFFFFFFD0) 48 x 1 → m'.mem x = magicMem Mx (G + 8) x := by
  obtain ⟨e32, -, -, -, e88, e96, -⟩ := Ly.r_eqs
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb (by decide)
  have r1 := mp_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := Cur.readerMagic_correct m1 (BitVec.ofNat 32 readerMagicAddress)
    (MP + BitVec.ofNat 32 (off + 8)) (G + 8) k
    (fun i hi => by rw [mem1]; exact code.magic i hi)
    (fun i hi => by
      rw [mem1, show (BitVec.ofNat 32 readerMagicAddress + 0x1BC : Word) = BitVec.ofNat 32 readerArray4Address
        from by decide]
      exact code.array4 i hi)
    (fun i hi => by
      rw [mem1, show (BitVec.ofNat 32 readerMagicAddress + 0x1BC + 0xFFFFFF96 : Word) =
        BitVec.ofNat 32 readerBytesAddress from by decide]
      exact code.bytes i hi)
    (by decide) pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by rw [sp1]; exact Ly.hG)
    (aligned_add Ly.hG (k := 8) (by decide))
    (by rw [mem1, hrp, hrl]; exact ⟨Ly.hbp.1, Ly.hbp.2⟩)
    (by rw [sp1, e32]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e32]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e32]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e96]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e96]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e96]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e32, e88]; exact stackStack R 88 12 32 48 (by omega) (by omega) (by omega))
    (by rw [mem1, hrp, hrl, sp1, e32]; exact Ly.hBS.subR (c := 32) (l := 48) (by omega))
    (by rw [mem1, hrp, hrl, e96]; exact Ly.hBS.subR (c := 96) (l := 4) (by omega))
  rw [mem1] at a02 mem2
  rw [sp1] at sp2 mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, fun r h0 h1' h2' h3 h4 h5 h6 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5 h6, r1 r h7]

/-- A call from `parse` to `Reader::version_1` on the reader at `G + 8`. -/
theorem mp_version {R G bp : Word} (Ly : MLay R G bp) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o : Word} (s : St Mx MP m off f)
    (code : MPCode Mx)
    (h1 : fetchRel manifestParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel manifestParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : MP + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 readerVersion1Address)
    (hl : (MP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 8)
    (hrp : memLoad32 Mx (G + 8) = bp) (hrl : memLoad32 Mx (G + 8 + 4) = 40) :
    ∃ m', Steps m m' ∧ St m'.mem MP m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = version1Result Mx (G + 8) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep (G + 0xFFFFFFE0) 32 x 1 → m'.mem x = u16Mem Mx (G + 8) x := by
  obtain ⟨-, e48, -, -, e88, e96, -⟩ := Ly.r_eqs
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb (by decide)
  have r1 := mp_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := readerVersion1_correct m1 (BitVec.ofNat 32 readerVersion1Address)
    (MP + BitVec.ofNat 32 (off + 8)) (G + 8)
    (fun i hi => by rw [mem1]; exact code.version i hi)
    (fun i hi => by
      rw [mem1, show (BitVec.ofNat 32 readerVersion1Address + 0x126 : Word) = BitVec.ofNat 32 readerU16Address
        from by decide]
      exact code.u16 i hi)
    (fun i hi => by
      rw [mem1, show (BitVec.ofNat 32 readerVersion1Address + 0x126 + 0xFFFFFFDA : Word) =
        BitVec.ofNat 32 readerBytesAddress from by decide]
      exact code.bytes i hi)
    (by decide) pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hl)
    (by rw [sp1]; exact Ly.hG) (aligned_add Ly.hG (k := 8) (by decide))
    (by rw [mem1, hrp, hrl]; exact ⟨Ly.hbp.1, Ly.hbp.2⟩)
    (by rw [sp1, e48]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e48]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e48]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e96]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e96]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e96]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e48, e88]; exact stackStack R 88 12 48 32 (by omega) (by omega) (by omega))
    (by rw [mem1, hrp, hrl, sp1, e48]; exact Ly.hBS.subR (c := 48) (l := 32) (by omega))
    (by rw [mem1, hrp, hrl, e96]; exact Ly.hBS.subR (c := 96) (l := 4) (by omega))
  rw [mem1] at a02 mem2
  rw [sp1] at sp2 mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, fun r h0 h1' h2' h3 h4 h5 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5, r1 r h7]

/-- A call from `parse` to `Reader::reserved(2)` on the reader at `G + 8`. -/
theorem mp_reserved {R G bp : Word} (Ly : MLay R G bp) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o : Word} (s : St Mx MP m off f)
    (code : MPCode Mx)
    (h1 : fetchRel manifestParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel manifestParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : MP + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 readerReservedAddress)
    (hl : (MP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 8) (ha1 : f a1 = 2)
    (hrp : memLoad32 Mx (G + 8) = bp) (hrl : memLoad32 Mx (G + 8 + 4) = 40) :
    ∃ m', Steps m m' ∧ St m'.mem MP m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = reservedResult Mx (G + 8) 2 ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep (G + 0xFFFFFFF0) 16 x 1 → m'.mem x = reservedMem Mx (G + 8) 2 x := by
  obtain ⟨-, -, e64, -, e88, e96, -⟩ := Ly.r_eqs
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb (by decide)
  have r1 := mp_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := readerReserved_correct m1 (BitVec.ofNat 32 readerReservedAddress)
    (MP + BitVec.ofNat 32 (off + 8)) (G + 8) 2
    (fun i hi => by rw [mem1]; exact code.reserved i hi)
    (fun i hi => by
      rw [mem1, show (BitVec.ofNat 32 readerReservedAddress + 0x9C : Word) = BitVec.ofNat 32 readerBytesAddress
        from by decide]
      exact code.bytes i hi)
    (by decide) pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by decide)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl)
    (by rw [sp1]; exact Ly.hG) (aligned_add Ly.hG (k := 8) (by decide))
    (by rw [mem1, hrp, hrl]; exact ⟨Ly.hbp.1, Ly.hbp.2⟩)
    (by rw [sp1, e64]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e64]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e96]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e96]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e64, e88]; exact stackStack R 88 12 64 16 (by omega) (by omega) (by omega))
    (by rw [mem1, hrp, hrl, sp1, e64]; exact Ly.hBS.subR (c := 64) (l := 16) (by omega))
    (by rw [mem1, hrp, hrl, e96]; exact Ly.hBS.subR (c := 96) (l := 4) (by omega))
  rw [mem1] at a02 mem2
  rw [sp1] at sp2 mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, fun r h0 h1' h2' h3 h4 h5 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5, r1 r h7]

/-- A call from `parse` to `manifest::part` on the reader at `G + 8`, with
the result at `G + 0x14`. -/
theorem mp_part {R G bp : Word} (Ly : MLay R G bp) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o lo hi : Word} (s : St Mx MP m off f)
    (code : MPCode Mx)
    (h1 : fetchRel manifestParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel manifestParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : MP + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 manifestPartAddress)
    (hl : (MP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 0x14) (ha1 : f a1 = G + 8) (ha2 : f a2 = lo) (ha3 : f a3 = hi)
    (hrp : memLoad32 Mx (G + 8) = bp) (hrl : memLoad32 Mx (G + 8 + 4) = 40) :
    ∃ m', Steps m m' ∧ St m'.mem MP m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep R 80 x 1 → m'.mem x = partMem Mx (G + 0x14) (G + 8) lo hi x := by
  obtain ⟨-, -, -, eR, e88, e96, e100⟩ := Ly.r_eqs
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb (by decide)
  have r1 := mp_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  have R0 : R = R + BitVec.ofNat 32 0 := (add_ofNat_zero R).symm
  obtain ⟨m2, c2, pc2, sp2, fr2, mem2⟩ := Cur.manifestPart_correct m1 (BitVec.ofNat 32 manifestPartAddress)
    (MP + BitVec.ofNat 32 (off + 8)) (G + 0x14) (G + 8) lo hi
    (fun i hi' => by rw [mem1]; exact code.part i hi')
    (fun i hi' => by
      rw [mem1, show (BitVec.ofNat 32 manifestPartAddress + 0xFFFFC6B2 : Word) = BitVec.ofNat 32 readerU32Address
        from by decide]
      exact code.u32 i hi')
    (fun i hi' => by
      rw [mem1, show (BitVec.ofNat 32 manifestPartAddress + 0xFFFFC6B2 + 0xFFFFFAB6 : Word) =
        BitVec.ofNat 32 readerArray4Address from by decide]
      exact code.array4 i hi')
    (fun i hi' => by
      rw [mem1, show (BitVec.ofNat 32 manifestPartAddress + 0xFFFFC6B2 + 0xFFFFFAB6 + 0xFFFFFF96 : Word) =
        BitVec.ofNat 32 readerBytesAddress from by decide]
      exact code.bytes i hi')
    (by decide) pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [r1 a2 (by decide), ha2]) (by rw [r1 a3 (by decide), ha3])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by rw [sp1]; exact Ly.hG)
    (aligned_add Ly.hG (k := 0x14) (by decide)) (aligned_add Ly.hG (k := 8) (by decide))
    (by rw [mem1, hrp, hrl]; exact ⟨Ly.hbp.1, Ly.hbp.2⟩)
    (by rw [sp1, eR, R0]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e100]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e96]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, eR, e88]
        have := stackStack R 88 12 0 80 (by omega) (by omega) (by omega); rwa [add_ofNat_zero] at this)
    (by rw [sp1, eR, e100]
        have := stackStack R 100 12 0 80 (by omega) (by omega) (by omega); rwa [add_ofNat_zero] at this)
    (by rw [mem1, hrp, hrl, sp1, eR]
        have := Ly.hBS.subR (c := 0) (l := 80) (by omega); rwa [add_ofNat_zero] at this)
    (by rw [mem1, hrp, hrl, e96]; exact Ly.hBS.subR (c := 96) (l := 4) (by omega))
  rw [mem1] at mem2
  rw [sp1, eR] at mem2
  rw [sp1] at sp2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun r h0 h1' h2' h3 h4 h5 h6 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5 h6, r1 r h7]

/-- One of `parse`'s calls to `part` at offset `off`, then `lbu a0, 0x14(sp)`:
the result's tag in `a0` and, for a length in range, the two words and the
reader advanced by 8. -/
theorem mp_part_step {R G bp : Word} (Ly : MLay R G bp) {M0 M2 Mx : Word → BitVec 8} (c0 : MPCode M0)
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o lo hi : Word} (p : Nat) (hp : p + 8 ≤ 40)
    (s : St Mx MP m off f)
    (h1 : fetchRel manifestParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel manifestParseCode (off + 4) = some (.jalr ra ra o, 4))
    (h3 : fetchRel manifestParseCode (off + 8) = some (.load .lbu a0 sp 0x14, 4))
    (hb : MP + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 manifestPartAddress)
    (hl : (MP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 0x14) (ha1 : f a1 = G + 8) (ha2 : f a2 = lo) (ha3 : f a3 = hi)
    (hrp : memLoad32 Mx (G + 8) = bp) (hrl : memLoad32 Mx (G + 8 + 4) = 40)
    (hrq : memLoad32 Mx (G + 8 + 8) = BitVec.ofNat 32 p)
    (hO : ∀ x, Sep R 144 x 1 → Mx x = M0 x)
    (hS : ∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k))
    :
    ∃ m' My, Steps m m' ∧ St My MP m' (off + 12) (reg m') ∧ reg m' sp = G ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra → reg m' r = f r) ∧
      (∀ x, Sep R 144 x 1 → My x = M0 x) ∧
      (∀ k, 0x20 ≤ k → k < 0x40 → My (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) ∧
      (if partOut lo hi (mw M0 bp (p + 4)) then reg m' a0 = 1 ∧ My (G + 0x15) = 5
       else reg m' a0 = 0 ∧ memLoad32 My (G + 8) = bp ∧ memLoad32 My (G + 8 + 4) = 40 ∧
         memLoad32 My (G + 8 + 8) = BitVec.ofNat 32 (p + 8) ∧
         memLoad32 My (G + 0x18) = mw M0 bp p ∧ memLoad32 My (G + 0x1C) = mw M0 bp (p + 4)) := by
  have code := Ly.code c0 hO
  obtain ⟨m1, c1, t1, sp1, fr1, mem1⟩ := mp_part Ly s code h1 h2 hb hl hsp ha0 ha1 ha2 ha3 hrp hrl
  have b1 := bytesResult_at bp p 4 (by omega)
  have b2 : bytesResult bp 40 (BitVec.ofNat 32 p + 4) 4 =
      some (bp + (BitVec.ofNat 32 p + 4), BitVec.ofNat 32 p + 4 + 4) := by
    rw [show BitVec.ofNat 32 p + 4 = BitVec.ofNat 32 (p + 4) from ofNat_add_ofNat p 4]
    exact bytesResult_at bp (p + 4) 4 (by omega)
  have buf : ∀ i, i + 4 ≤ 40 → memLoad32 Mx (bp + BitVec.ofNat 32 i) = mw M0 bp i := fun i hi =>
    memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact hO _ (Ly.hBS.sub (c := i + j) (l := 1) (by omega)).symm
  have hv1 : memLoad32 Mx (bp + BitVec.ofNat 32 p) = mw M0 bp p := buf p (by omega)
  have hv2 : memLoad32 Mx (bp + (BitVec.ofNat 32 p + 4)) = mw M0 bp (p + 4) := by
    rw [show BitVec.ofNat 32 p + 4 = BitVec.ofNat 32 (p + 4) from ofNat_add_ofNat p 4]; exact buf (p + 4) (by omega)
  have he : BitVec.ofNat 32 p + 4 + 4 = BitVec.ofNat 32 (p + 8) := by
    rw [show BitVec.ofNat 32 p + 4 = BitVec.ofNat 32 (p + 4) from ofNat_add_ofNat p 4]
    exact ofNat_add_ofNat (p + 4) 4
  have mem1' : ∀ x, Sep R 80 x 1 → m1.mem x =
      if partOut lo hi (mw M0 bp (p + 4)) then
        memStore8 (memStore8 (memStore32 Mx (G + 8 + 8) (BitVec.ofNat 32 (p + 8))) (G + 0x14 + 1) 5) (G + 0x14) 1 x
      else
        memStore8 (memStore32 (memStore32 (memStore32 Mx (G + 8 + 8) (BitVec.ofNat 32 (p + 8))) (G + 0x14 + 4)
          (mw M0 bp p)) (G + 0x14 + 8) (mw M0 bp (p + 4))) (G + 0x14) 0 x := fun x hx => by
    rw [mem1 x hx, part_val (BitVec.ofNat 32 p) hrp hrl hrq b1 b2 x, hv1, hv2, he]
  have t1' : St m1.mem MP m1 (off + 8) (reg m1) := t1
  cases hc : partOut lo hi (mw M0 bp (p + 4))
  · simp only [hc, Bool.false_eq_true, ite_false] at mem1'
    obtain ⟨q1, q2, q3, O1, S1, tag, w1, w2⟩ := Ly.advance_part_ok (M0 := M0) (M2 := M2) (My := m1.mem)
      hrp hrl hO hS mem1'
    obtain ⟨m2, e2, t2⟩ := t1'.lbu (Ly.code c0 O1).parse h3 (off' := off + 12) (ofNat_add_ofNat (off + 8) 4)
    rw [sp1, show G + 0x14 = G + 0x14 from rfl, tag] at t2
    refine ⟨m2, m1.mem, c1.trans (.single e2), t2.self, ?_, fun r h0 h1' h2' h3' h4 h5 h6 h7 => ?_, O1, S1,
      ⟨?_, q1, q2, q3, w1, w2⟩⟩
    · rw [t2.regs]; simp +decide [upd, sp1]
    · rw [t2.regs]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd]; exact s.zero.symm
      · simp [upd, hr, h0]; exact fr1 r h0 h1' h2' h3' h4 h5 h6 h7
    · rw [t2.regs]; simp +decide [upd]
  · simp only [hc, ite_true] at mem1'
    obtain ⟨O1, S1, tag, err⟩ := Ly.advance_part_err (M0 := M0) (M2 := M2) (My := m1.mem) hO hS mem1'
    obtain ⟨m2, e2, t2⟩ := t1'.lbu (Ly.code c0 O1).parse h3 (off' := off + 12) (ofNat_add_ofNat (off + 8) 4)
    rw [sp1, tag] at t2
    refine ⟨m2, m1.mem, c1.trans (.single e2), t2.self, ?_, fun r h0 h1' h2' h3' h4 h5 h6 h7 => ?_, O1, S1,
      ⟨?_, err⟩⟩
    · rw [t2.regs]; simp +decide [upd, sp1]
    · rw [t2.regs]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd]; exact s.zero.symm
      · simp [upd, hr, h0]; exact fr1 r h0 h1' h2' h3' h4 h5 h6 h7
    · rw [t2.regs]; simp +decide [upd]

/-- `check_branch` for the current code: `andi a1, a0, 0xFF; addi a1, a1,
-0xFF; bne a1, x0` continues when the low byte of `a0` is 0xFF and goes to
the error path at 0xD6 otherwise. -/
theorem mp_check {Mx : Word → BitVec 8} {base : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word}
    {o : Word} (s : St Mx base m off f) (hc : CodeIn Mx base manifestParseCode)
    (h1 : fetchRel manifestParseCode off = some (.aluImm .and a1 a0 0xFF, 4))
    (h2 : fetchRel manifestParseCode (off + 4) = some (.aluImm .add a1 a1 0xFFFFFF01, 4))
    (h3 : fetchRel manifestParseCode (off + 8) = some (.branch .bne a1 x0 o, 2))
    (ho : BitVec.ofNat 32 (off + 8) + o = BitVec.ofNat 32 0xD6) :
    ∃ m' g, Steps m m' ∧ (∀ r, r ≠ a1 → g r = f r) ∧
      ((f a0 &&& 0xFF = 0xFF ∧ St Mx base m' (off + 10) g) ∨
       (f a0 &&& 0xFF ≠ 0xFF ∧ St Mx base m' 0xD6 g)) := by
  have hz := s.zero
  obtain ⟨m1, e1, t1⟩ := s.aluImm hc h1 (off' := off + 4) (ofNat_add_ofNat off 4)
  obtain ⟨m2, e2, t2⟩ := t1.aluImm hc h2 (off' := off + 8) (ofNat_add_ofNat (off + 4) 4)
  have g2 : ∀ r, r ≠ a1 → upd (upd f a1 (aluEval .and (f a0) 0xFF)) a1
      (aluEval .add (upd f a1 (aluEval .and (f a0) 0xFF) a1) 0xFFFFFF01) r = f r := fun r h => by
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, hz]
    · simp [upd, hr, h]
  have v2 : upd (upd f a1 (aluEval .and (f a0) 0xFF)) a1
      (aluEval .add (upd f a1 (aluEval .and (f a0) 0xFF) a1) 0xFFFFFF01) a1 =
        (f a0 &&& 0xFF) + 0xFFFFFF01 := by simp +decide [upd, aluEval]
  have z2 : upd (upd f a1 (aluEval .and (f a0) 0xFF)) a1
      (aluEval .add (upd f a1 (aluEval .and (f a0) 0xFF) a1) 0xFFFFFF01) x0 = 0 := by simp [upd]
  by_cases h : f a0 &&& 0xFF = 0xFF
  · obtain ⟨m3, e3, t3⟩ := t2.notTaken hc (off + 10) h3 (ofNat_add_ofNat (off + 8) 2)
      (by rw [v2, z2, h]; decide)
    exact ⟨m3, _, .cons e1 (.cons e2 (.single e3)), g2, .inl ⟨h, t3⟩⟩
  · have hne : (f a0 &&& 0xFF) + 0xFFFFFF01 ≠ 0 := fun e => h (by
      have := congrArg (· + 0xFF) e
      simp only [BitVec.add_assoc] at this
      rw [show (0xFFFFFF01 : Word) + 0xFF = 0 from rfl] at this
      exact (BitVec.add_zero _).symm.trans (this.trans (BitVec.zero_add _)))
    obtain ⟨m3, e3, t3⟩ := t2.taken hc 0xD6 h3 ho (by rw [v2, z2]; exact bne_iff_ne.mpr hne)
    exact ⟨m3, _, .cons e1 (.cons e2 (.single e3)), g2, .inr ⟨h, t3⟩⟩

theorem clob_ne {r q : Fin 32} (hr : r ∉ parseClob) (hq : q ∈ parseClob) : r ≠ q := fun h => hr (h ▸ hq)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **`manifest::parse`, as compiled**: with its callees where the image puts
them, 144 bytes of stack below `sp` (below `0x40000000`), the 40-byte
manifest at `bp` apart from that stack, and the 36-byte result at `out`
apart from it and below `0x40000000`, it returns to `ra` with `sp` and every
register but `a0` through `a5` and `t0` restored, and memory outside its
stack as `parseMem` says. -/
theorem manifestParse_correct (m : Machine) {retAddr out bp : Word}
    (code : MPCode m.mem) (hpc : m.pc = MP)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = bp) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 4 = 0) (hsl : 144 ≤ (reg m sp).toNat) (hsw : (reg m sp).toNat ≤ 0x40000000)
    (hbp : bp ≠ 0 ∧ bp.toNat + 40 ≤ 2 ^ 32) (hBS : Sep bp 40 (reg m sp + 0xFFFFFF70) 144)
    (hout : out.toNat % 4 = 0) (how : out.toNat + 36 ≤ 0x40000000)
    (hOS : Sep out 36 (reg m sp + 0xFFFFFF70) 144) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFF70) 144 x 1 → m'.mem x = parseMem m.mem out bp x := by
  obtain ⟨R, hRd⟩ : ∃ R, reg m sp + 0xFFFFFF70 = R := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G, reg m sp + 0xFFFFFFC0 = G := ⟨_, rfl⟩
  rw [hRd] at hBS hOS ⊢
  have hRn : R.toNat = (reg m sp).toNat - 144 := by
    rw [← hRd, BitVec.toNat_add, show (0xFFFFFF70 : Word).toNat = 2 ^ 32 - 144 from rfl]; omega
  have hGn : G.toNat = (reg m sp).toNat - 64 := by
    rw [← hGd, BitVec.toNat_add, show (0xFFFFFFC0 : Word).toNat = 2 ^ 32 - 64 from rfl]; omega
  have hRG : G = R + BitVec.ofNat 32 80 := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hGn, hRn]; omega)
  have hspG : G + 0x40 = reg m sp := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, show (0x40 : Word).toNat = 0x40 from rfl, hGn]; omega)
  have hGa : G.toNat % 4 = 0 := by omega
  have Ly : MLay R G bp := ⟨hRG, by omega, hGa, hbp, hBS⟩
  have hc := code.parse
  have fr : ∀ c l, c + l ≤ 0x40 → ∀ (x : Word) (n : Nat), Sep R 144 x n → Sep (G + BitVec.ofNat 32 c) l x n :=
    fun c l h x n hx => by rw [hRG, add_ofNat_assoc]; exact hx.sub (c := 80 + c) (l := l) (by omega)
  have gLow : ∀ c, c + 4 ≤ 0x40 → (G + BitVec.ofNat 32 c).toNat + 4 ≤ 0x40000000 := fun c h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have s0' : St m.mem MP m 0 (reg m) := ⟨by rw [hpc]; rfl, rfl, fun _ => rfl⟩
  have hz := s0'.zero
  obtain ⟨m1, e1, t1⟩ := s0'.aluImm hc mpc_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFC0 = G from hGd] at t1
  have u1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp G r = reg m r := fun r h => updz hz h
  obtain ⟨m2, e2, t2⟩ := t1.sw hc mpc_at_2 (off' := 0x4) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x3C) (by decide))
  rw [u1sp, f1 ra (by decide)] at t2
  have hc2 := hc.store32 (v := reg m ra) (lowSep (gLow 0x3C (by omega)) (by decide) (by decide))
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 mpc_at_4 (off' := 0x6) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x38) (by decide))
  rw [u1sp, f1 8 (by decide)] at t3
  have hc3 := hc2.store32 (v := reg m 8) (lowSep (gLow 0x38 (by omega)) (by decide) (by decide))
  obtain ⟨m4, e4, t4⟩ := t3.sw hc3 mpc_at_6 (off' := 0x8) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x34) (by decide))
  rw [u1sp, f1 9 (by decide)] at t4
  have hc4 := hc3.store32 (v := reg m 9) (lowSep (gLow 0x34 (by omega)) (by decide) (by decide))
  obtain ⟨m5, e5, t5⟩ := t4.sw hc4 mpc_at_8 (off' := 0xA) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x30) (by decide))
  rw [u1sp, f1 18 (by decide)] at t5
  have hc5 := hc4.store32 (v := reg m 18) (lowSep (gLow 0x30 (by omega)) (by decide) (by decide))
  obtain ⟨m6, e6, t6⟩ := t5.sw hc5 mpc_at_a (off' := 0xC) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x2C) (by decide))
  rw [u1sp, f1 19 (by decide)] at t6
  have hc6 := hc5.store32 (v := reg m 19) (lowSep (gLow 0x2C (by omega)) (by decide) (by decide))
  obtain ⟨m7, e7, t7⟩ := t6.sw hc6 mpc_at_c (off' := 0xE) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x28) (by decide))
  rw [u1sp, f1 20 (by decide)] at t7
  have hc7 := hc6.store32 (v := reg m 20) (lowSep (gLow 0x28 (by omega)) (by decide) (by decide))
  obtain ⟨m8, e8, t8⟩ := t7.sw hc7 mpc_at_e (off' := 0x10) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x24) (by decide))
  rw [u1sp, f1 21 (by decide)] at t8
  have hc8 := hc7.store32 (v := reg m 21) (lowSep (gLow 0x24 (by omega)) (by decide) (by decide))
  obtain ⟨m9, e9, t9⟩ := t8.sw hc8 mpc_at_10 (off' := 0x12) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x20) (by decide))
  rw [u1sp, f1 22 (by decide)] at t9
  obtain ⟨M8, hM8⟩ : ∃ M8, memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (m.mem) (G + 0x3C) (reg m ra)) (G + 0x38) (reg m 8)) (G + 0x34) (reg m 9)) (G + 0x30) (reg m 18)) (G + 0x2C) (reg m 19)) (G + 0x28) (reg m 20)) (G + 0x24) (reg m 21)) (G + 0x20) (reg m 22) = M8 := ⟨_, rfl⟩
  rw [hM8] at t9
  have hc8 : CodeIn M8 MP manifestParseCode := by
    rw [← hM8]; exact hc8.store32 (lowSep (gLow 0x20 (by omega)) (by decide) (by decide))

  have M8out : ∀ x, Sep R 144 x 1 → M8 x = m.mem x := fun x hx => by
    rw [← hM8]
    exact (memStore32_get_sep (fr 0x20 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x24 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x28 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x2C 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x30 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x34 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x38 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x3C 4 (by omega) x 1 hx)))))))))
  have fl3c : memLoad32 M8 (G + 0x3C) = reg m ra := by
    rw [← hM8]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x3C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x24) (n := 4) (d := 0x3C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x28) (n := 4) (d := 0x3C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x2C) (n := 4) (d := 0x3C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x30) (n := 4) (d := 0x3C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x34) (n := 4) (d := 0x3C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x38) (n := 4) (d := 0x3C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl38 : memLoad32 M8 (G + 0x38) = reg m 8 := by
    rw [← hM8]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x38) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x24) (n := 4) (d := 0x38) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x28) (n := 4) (d := 0x38) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x2C) (n := 4) (d := 0x38) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x30) (n := 4) (d := 0x38) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x34) (n := 4) (d := 0x38) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl34 : memLoad32 M8 (G + 0x34) = reg m 9 := by
    rw [← hM8]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x34) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x24) (n := 4) (d := 0x34) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x28) (n := 4) (d := 0x34) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x2C) (n := 4) (d := 0x34) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x30) (n := 4) (d := 0x34) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl30 : memLoad32 M8 (G + 0x30) = reg m 18 := by
    rw [← hM8]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x30) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x24) (n := 4) (d := 0x30) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x28) (n := 4) (d := 0x30) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x2C) (n := 4) (d := 0x30) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl2c : memLoad32 M8 (G + 0x2C) = reg m 19 := by
    rw [← hM8]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x24) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x28) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl28 : memLoad32 M8 (G + 0x28) = reg m 20 := by
    rw [← hM8]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x24) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl24 : memLoad32 M8 (G + 0x24) = reg m 21 := by
    rw [← hM8]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl20 : memLoad32 M8 (G + 0x20) = reg m 22 := by
    rw [← hM8]
    exact memLoad32_store32_same _ _ _
  have exitDC : ∀ (n : Machine) (Mx : Word → BitVec 8) (g : Fin 32 → Word) (v : BitVec 8),
      Steps m n → St Mx MP n 0xDC g → CodeIn Mx MP manifestParseCode → g sp = G → g s0 = out →
      (g a0).extractLsb' 0 8 = v →
      (∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M8 (G + BitVec.ofNat 32 k)) →
      (∀ r, r ∉ parseClob → g r = reg m r) →
      (∀ x, Sep R 144 x 1 → memStore8 Mx out v x = parseMem m.mem out bp x) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg m' r = reg m r) ∧
        ∀ x, Sep R 144 x 1 → m'.mem x = parseMem m.mem out bp x := by
    intro n Mx g v hn s hcx hs hs0 hv hS hk hm
    obtain ⟨n0, d0, u0⟩ := s.sbG hcx mpc_at_dc (off' := 0xE0) (by decide) (a := out) (v := g a0)
      (by rw [hs0]; exact BitVec.add_zero out) rfl
    rw [hv] at u0
    have hcf : CodeIn (memStore8 Mx out v) MP manifestParseCode :=
      hcx.store8 (lowSep (by omega) (by decide) (by decide))
    have hF : ∀ k, 0x20 ≤ k → k < 0x40 → memStore8 Mx out v (G + BitVec.ofNat 32 k) = M8 (G + BitVec.ofNat 32 k) :=
      fun k h1 h2 => by
        rw [memStore8_ne (fun e => hOS 0 (by omega) (80 + k) (by omega) (by rw [add_ofNat_zero, ← Ly.g_ofs k, e]))]
        exact hS k h1 h2
    have ldF : ∀ c, 0x20 ≤ c → c + 4 ≤ 0x40 →
        memLoad32 (memStore8 Mx out v) (G + BitVec.ofNat 32 c) = memLoad32 M8 (G + BitVec.ofNat 32 c) :=
      fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hF _ (by omega) (by omega)
    obtain ⟨n1, d1, u1⟩ := u0.lw hcf mpc_at_e0 (off' := 0xE2) (by decide)
      (by rw [hs]; exact aligned_add hGa (k := 0x3C) (by decide))
    rw [hs, show memLoad32 (memStore8 Mx out v) (G + 0x3C) = reg m ra from
      (ldF 0x3C (by omega) (by omega)).trans fl3c] at u1
    have q1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [u1.regs]; exact updz u0.zero h
    have w1 : reg n1 ra = reg m ra := by rw [u1.regs]; simp +decide only [upd, ite_true, ite_false]
    have p1 : reg n1 sp = G := by rw [q1 sp (by decide)]; exact hs
    obtain ⟨n2, d2, u2⟩ := u1.self.lw hcf mpc_at_e2 (off' := 0xE4) (by decide)
      (by rw [p1]; exact aligned_add hGa (k := 0x38) (by decide))
    rw [p1, show memLoad32 (memStore8 Mx out v) (G + 0x38) = reg m 8 from
      (ldF 0x38 (by omega) (by omega)).trans fl38] at u2
    have q2 : ∀ r, r ≠ 8 → reg n2 r = reg n1 r := fun r h => by rw [u2.regs]; exact updz u1.self.zero h
    have w2 : reg n2 8 = reg m 8 := by rw [u2.regs]; simp +decide only [upd, ite_true, ite_false]
    have p2 : reg n2 sp = G := by rw [q2 sp (by decide)]; exact p1
    obtain ⟨n3, d3, u3⟩ := u2.self.lw hcf mpc_at_e4 (off' := 0xE6) (by decide)
      (by rw [p2]; exact aligned_add hGa (k := 0x34) (by decide))
    rw [p2, show memLoad32 (memStore8 Mx out v) (G + 0x34) = reg m 9 from
      (ldF 0x34 (by omega) (by omega)).trans fl34] at u3
    have q3 : ∀ r, r ≠ 9 → reg n3 r = reg n2 r := fun r h => by rw [u3.regs]; exact updz u2.self.zero h
    have w3 : reg n3 9 = reg m 9 := by rw [u3.regs]; simp +decide only [upd, ite_true, ite_false]
    have p3 : reg n3 sp = G := by rw [q3 sp (by decide)]; exact p2
    obtain ⟨n4, d4, u4⟩ := u3.self.lw hcf mpc_at_e6 (off' := 0xE8) (by decide)
      (by rw [p3]; exact aligned_add hGa (k := 0x30) (by decide))
    rw [p3, show memLoad32 (memStore8 Mx out v) (G + 0x30) = reg m 18 from
      (ldF 0x30 (by omega) (by omega)).trans fl30] at u4
    have q4 : ∀ r, r ≠ 18 → reg n4 r = reg n3 r := fun r h => by rw [u4.regs]; exact updz u3.self.zero h
    have w4 : reg n4 18 = reg m 18 := by rw [u4.regs]; simp +decide only [upd, ite_true, ite_false]
    have p4 : reg n4 sp = G := by rw [q4 sp (by decide)]; exact p3
    obtain ⟨n5, d5, u5⟩ := u4.self.lw hcf mpc_at_e8 (off' := 0xEA) (by decide)
      (by rw [p4]; exact aligned_add hGa (k := 0x2C) (by decide))
    rw [p4, show memLoad32 (memStore8 Mx out v) (G + 0x2C) = reg m 19 from
      (ldF 0x2C (by omega) (by omega)).trans fl2c] at u5
    have q5 : ∀ r, r ≠ 19 → reg n5 r = reg n4 r := fun r h => by rw [u5.regs]; exact updz u4.self.zero h
    have w5 : reg n5 19 = reg m 19 := by rw [u5.regs]; simp +decide only [upd, ite_true, ite_false]
    have p5 : reg n5 sp = G := by rw [q5 sp (by decide)]; exact p4
    obtain ⟨n6, d6, u6⟩ := u5.self.lw hcf mpc_at_ea (off' := 0xEC) (by decide)
      (by rw [p5]; exact aligned_add hGa (k := 0x28) (by decide))
    rw [p5, show memLoad32 (memStore8 Mx out v) (G + 0x28) = reg m 20 from
      (ldF 0x28 (by omega) (by omega)).trans fl28] at u6
    have q6 : ∀ r, r ≠ 20 → reg n6 r = reg n5 r := fun r h => by rw [u6.regs]; exact updz u5.self.zero h
    have w6 : reg n6 20 = reg m 20 := by rw [u6.regs]; simp +decide only [upd, ite_true, ite_false]
    have p6 : reg n6 sp = G := by rw [q6 sp (by decide)]; exact p5
    obtain ⟨n7, d7, u7⟩ := u6.self.lw hcf mpc_at_ec (off' := 0xEE) (by decide)
      (by rw [p6]; exact aligned_add hGa (k := 0x24) (by decide))
    rw [p6, show memLoad32 (memStore8 Mx out v) (G + 0x24) = reg m 21 from
      (ldF 0x24 (by omega) (by omega)).trans fl24] at u7
    have q7 : ∀ r, r ≠ 21 → reg n7 r = reg n6 r := fun r h => by rw [u7.regs]; exact updz u6.self.zero h
    have w7 : reg n7 21 = reg m 21 := by rw [u7.regs]; simp +decide only [upd, ite_true, ite_false]
    have p7 : reg n7 sp = G := by rw [q7 sp (by decide)]; exact p6
    obtain ⟨n8, d8, u8⟩ := u7.self.lw hcf mpc_at_ee (off' := 0xF0) (by decide)
      (by rw [p7]; exact aligned_add hGa (k := 0x20) (by decide))
    rw [p7, show memLoad32 (memStore8 Mx out v) (G + 0x20) = reg m 22 from
      (ldF 0x20 (by omega) (by omega)).trans fl20] at u8
    have q8 : ∀ r, r ≠ 22 → reg n8 r = reg n7 r := fun r h => by rw [u8.regs]; exact updz u7.self.zero h
    have w8 : reg n8 22 = reg m 22 := by rw [u8.regs]; simp +decide only [upd, ite_true, ite_false]
    have p8 : reg n8 sp = G := by rw [q8 sp (by decide)]; exact p7
    obtain ⟨n9, d9, u9⟩ := u8.self.aluImm hcf mpc_at_f0 (off' := 0xF2) (by decide)
    obtain ⟨n10, d10, pc10, mem10, regs10⟩ := u9.jalr hcf mpc_at_f2
    have z8 : ∀ r, r ≠ ra → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 22 → reg n8 r = g r :=
      fun r h1 h2 h3 h4 h5 h6 h7 h8 => by
        rw [q8 r h8, q7 r h7, q6 r h6, q5 r h5, q4 r h4, q3 r h3, q2 r h2, q1 r h1]
    have vra : reg n8 ra = reg m ra := by rw [q8 ra (by decide), q7 ra (by decide), q6 ra (by decide), q5 ra (by decide), q4 ra (by decide), q3 ra (by decide), q2 ra (by decide)]; exact w1
    have v8 : reg n8 8 = reg m 8 := by rw [q8 8 (by decide), q7 8 (by decide), q6 8 (by decide), q5 8 (by decide), q4 8 (by decide), q3 8 (by decide)]; exact w2
    have v9 : reg n8 9 = reg m 9 := by rw [q8 9 (by decide), q7 9 (by decide), q6 9 (by decide), q5 9 (by decide), q4 9 (by decide)]; exact w3
    have v18 : reg n8 18 = reg m 18 := by rw [q8 18 (by decide), q7 18 (by decide), q6 18 (by decide), q5 18 (by decide)]; exact w4
    have v19 : reg n8 19 = reg m 19 := by rw [q8 19 (by decide), q7 19 (by decide), q6 19 (by decide)]; exact w5
    have v20 : reg n8 20 = reg m 20 := by rw [q8 20 (by decide), q7 20 (by decide)]; exact w6
    have v21 : reg n8 21 = reg m 21 := by rw [q8 21 (by decide)]; exact w7
    have v22 : reg n8 22 = reg m 22 := by exact w8
    have r10 : ∀ r, r ≠ sp → reg n10 r = reg n8 r := fun r h => by rw [regs10]; exact updz u8.self.zero h
    refine ⟨n10, hn.trans (.cons d0 (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8
      (.cons d9 (.single d10))))))))))), ?_, ?_, fun r h0 h1 h2 h3 h4 h5 h6 => ?_, fun x hx => by rw [mem10]; exact hm x hx⟩
    · rw [pc10, add_lit_zero, updz u8.self.zero (show ra ≠ sp by decide), vra, hra, hret]
    · rw [regs10]; simp +decide only [upd, ite_true, ite_false]; rw [p8, ← hspG]; rfl
    by_cases e : r = sp
    · subst e; rw [regs10]; simp +decide only [upd, ite_true, ite_false]; rw [p8, ← hspG]; rfl
    by_cases e1 : r = ra
    · subst e1; rw [r10 ra (by decide)]; exact vra
    by_cases e2 : r = s0
    · subst e2; rw [r10 s0 (by decide)]; exact v8
    by_cases e3 : r = s1
    · subst e3; rw [r10 s1 (by decide)]; exact v9
    by_cases e4 : r = s2
    · subst e4; rw [r10 s2 (by decide)]; exact v18
    by_cases e5 : r = s3
    · subst e5; rw [r10 s3 (by decide)]; exact v19
    by_cases e6 : r = s4
    · subst e6; rw [r10 s4 (by decide)]; exact v20
    by_cases e7 : r = s5
    · subst e7; rw [r10 s5 (by decide)]; exact v21
    by_cases e8 : r = s6
    · subst e8; rw [r10 s6 (by decide)]; exact v22
    have hr : r ∉ parseClob := by
      simp only [parseClob, List.mem_cons, List.not_mem_nil, or_false]
      intro hh
      rcases hh with hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh <;>
        contradiction
    rw [r10 r e, z8 r e1 e2 e3 e4 e5 e6 e7 e8]; exact hk r hr
  have errD6 : ∀ (n : Machine) (Mx : Word → BitVec 8) (g : Fin 32 → Word) (e : BitVec 8),
      Steps m n → St Mx MP n 0xD6 g → CodeIn Mx MP manifestParseCode → g sp = G → g s0 = out →
      (g a0).extractLsb' 0 8 = e → parseErr m.mem bp = some e →
      (∀ x, Sep R 144 x 1 → Mx x = m.mem x) →
      (∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M8 (G + BitVec.ofNat 32 k)) →
      (∀ r, r ∉ parseClob → g r = reg m r) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg m' r = reg m r) ∧
        ∀ x, Sep R 144 x 1 → m'.mem x = parseMem m.mem out bp x := by
    intro n Mx g e hn s hcx hs hs0 he hpe hO hS hk
    obtain ⟨n1, d1, u1⟩ := s.sbG hcx mpc_at_d6 (off' := 0xDA) (by decide) (a := out + 1) (v := g a0)
      (by rw [hs0]) rfl
    rw [he] at u1
    have hc1 : CodeIn (memStore8 Mx (out + 1) e) MP manifestParseCode :=
      hcx.store8 (lowSep (by rw [BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl]; omega) (by decide) (by decide))
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc1 mpc_at_da (off' := 0xDC) (by decide)
    refine exitDC n2 _ _ 1 (hn.trans (.cons d1 (.single d2))) u2 hc1
      (by rw [updz s.zero (by decide)]; exact hs) (by rw [updz s.zero (by decide)]; exact hs0)
      (by simp +decide only [upd, ite_true, ite_false]; rw [s.zero]; rfl)
      (fun k h1 h2 => by
        rw [memStore8_ne (fun e' => hOS 1 (by omega) (80 + k) (by omega) (by rw [← Ly.g_ofs k, e']; rfl))]
        exact hS k h1 h2)
      (fun r hr => by rw [updz s.zero (clob_ne hr (by decide))]; exact hk r hr)
      (fun x hx => by
        have : parseMem m.mem out bp x = memStore8 (memStore8 m.mem (out + 1) e) out 1 x := by
          unfold parseMem; rw [hpe]
        rw [this]; exact memStore8_congr (memStore8_congr (hO x hx)))
  have errD2 : ∀ (n : Machine) (Mx : Word → BitVec 8) (g : Fin 32 → Word),
      Steps m n → St Mx MP n 0xD2 g → CodeIn Mx MP manifestParseCode → g sp = G → g s0 = out →
      Mx (G + 0x15) = 5 → parseErr m.mem bp = some 5 →
      (∀ x, Sep R 144 x 1 → Mx x = m.mem x) →
      (∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M8 (G + BitVec.ofNat 32 k)) →
      (∀ r, r ∉ parseClob → g r = reg m r) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg m' r = reg m r) ∧
        ∀ x, Sep R 144 x 1 → m'.mem x = parseMem m.mem out bp x := by
    intro n Mx g hn s hcx hs hs0 h15 hpe hO hS hk
    obtain ⟨n1, d1, u1⟩ := s.lbu hcx mpc_at_d2 (off' := 0xD6) (by decide)
    exact errD6 n1 Mx _ 5 (hn.trans (.single d1)) u1 hcx (by rw [updz s.zero (by decide)]; exact hs)
      (by rw [updz s.zero (by decide)]; exact hs0)
      (by simp +decide only [upd, ite_true, ite_false]; rw [hs, h15]; rfl) hpe hO hS
      (fun r hr => by rw [updz s.zero (clob_ne hr (by decide))]; exact hk r hr)
  -- 0x12 to 0x26: the reader over the 40 bytes at `bp`, at `G + 8`.
  have k9 : ∀ r, r ∉ parseClob → upd (reg m) sp G r = reg m r := fun r hr => f1 r (clob_ne hr (by decide))
  obtain ⟨m10, e10, t10⟩ := t9.alu hc8 mpc_at_12 (off' := 0x14) (by decide)
  have u10 := t10.self
  obtain ⟨m11, e11, t11⟩ := u10.aluImm hc8 mpc_at_14 (off' := 0x18) (by decide)
  have u11 := t11.self
  have sp11 : reg m11 sp = G := by
    rw [t11.regs, updz u10.zero (by decide), t10.regs, updz t9.zero (by decide)]; exact u1sp
  have a111 : reg m11 a1 = bp := by
    rw [t11.regs, updz u10.zero (by decide), t10.regs, updz t9.zero (by decide), f1 a1 (by decide)]; exact ha1
  have a011 : reg m11 a0 = 0x28 := by
    rw [t11.regs]; simp +decide only [upd, ite_true, ite_false]; rw [u10.zero]; rfl
  have s011 : reg m11 s0 = out := by
    rw [t11.regs, updz u10.zero (by decide), t10.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [ha0]; exact BitVec.zero_add out
  have k11 : ∀ r, r ∉ parseClob → reg m11 r = reg m r := fun r hr => by
    rw [t11.regs, updz u10.zero (clob_ne hr (by decide)), t10.regs, updz t9.zero (clob_ne hr (by decide))]
    exact k9 r hr
  obtain ⟨m12, e12, t12⟩ := u11.sw hc8 mpc_at_18 (off' := 0x1A) (by decide)
    (by rw [sp11]; exact aligned_add hGa (k := 8) (by decide))
  rw [sp11, a111] at t12
  have hc12 := hc8.store32 (v := bp) (lowSep (gLow 8 (by omega)) (by decide) (by decide))
  obtain ⟨m13, e13, t13⟩ := t12.sw hc12 mpc_at_1a (off' := 0x1C) (by decide)
    (by rw [sp11]; exact aligned_add hGa (k := 0xC) (by decide))
  rw [sp11, a011] at t13
  have hc13 := hc12.store32 (v := 0x28) (lowSep (gLow 0xC (by omega)) (by decide) (by decide))
  obtain ⟨m14, e14, t14⟩ := t13.sw hc13 mpc_at_1c (off' := 0x1E) (by decide)
    (by rw [sp11]; exact aligned_add hGa (k := 0x10) (by decide))
  rw [sp11, show reg m11 x0 = 0 from u11.zero] at t14
  obtain ⟨M11, hM11⟩ : ∃ M11, memStore32 (memStore32 (memStore32 M8 (G + 8) bp) (G + 0xC) 0x28) (G + 0x10) 0 = M11 :=
    ⟨_, rfl⟩
  rw [hM11] at t14
  have hM11' : memStore32 (memStore32 (memStore32 M8 (G + BitVec.ofNat 32 8) bp) (G + BitVec.ofNat 32 0xC) 0x28)
      (G + BitVec.ofNat 32 0x10) 0 = M11 := hM11
  have hc14 : CodeIn M11 MP manifestParseCode := by
    rw [← hM11]; exact hc13.store32 (lowSep (gLow 0x10 (by omega)) (by decide) (by decide))
  obtain ⟨m15, e15, t15⟩ := t14.lui hc14 mpc_at_1e (off' := 0x22) (by decide)
  have u15 := t15.self
  obtain ⟨m16, e16, t16⟩ := u15.aluImm hc14 mpc_at_22 (off' := 0x26) (by decide)
  have u16 := t16.self
  obtain ⟨m17, e17, t17⟩ := u16.aluImm hc14 mpc_at_26 (off' := 0x28) (by decide)
  have u17 := t17.self
  have g17 : ∀ r, r ≠ a0 → r ≠ a1 → reg m17 r = reg m11 r := fun r h0 h1 => by
    rw [t17.regs, updz u16.zero h0, t16.regs, updz u15.zero h1, t15.regs, updz u11.zero h1]
  have sp17 : reg m17 sp = G := by rw [g17 sp (by decide) (by decide)]; exact sp11
  have s017 : reg m17 s0 = out := by rw [g17 s0 (by decide) (by decide)]; exact s011
  have a017 : reg m17 a0 = G + 8 := by
    rw [t17.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [show reg m16 sp = G from by
      rw [t16.regs, updz u15.zero (by decide), t15.regs, updz u11.zero (by decide)]; exact sp11]; rfl
  have a117 : reg m17 a1 = 0x4C533343 := by
    rw [t17.regs, updz u16.zero (by decide), t16.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [t15.regs]; simp +decide only [upd, ite_true, ite_false]; try rfl
  have k17 : ∀ r, r ∉ parseClob → reg m17 r = reg m r := fun r hr => by
    rw [g17 r (clob_ne hr (by decide)) (clob_ne hr (by decide))]; exact k11 r hr
  have pre17 : Steps m m17 := .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
    (.cons e9 (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.cons e14 (.cons e15 (.cons e16 (.single e17))))))))))))))))
  -- The reader and the frame in `M11`.
  have so : ∀ a l b k, a + l ≤ b ∨ b + k ≤ a → a + l ≤ 64 → b + k ≤ 64 →
      Sep (G + BitVec.ofNat 32 a) l (G + BitVec.ofNat 32 b) k :=
    fun a l b k h h1 h2 => sep_offsets G h (by omega) (by omega)
  have O11 : ∀ x, Sep R 144 x 1 → M11 x = m.mem x := fun x hx => by
    rw [← hM11', memStore32_get_sep (fr 0x10 4 (by omega) x 1 hx), memStore32_get_sep (fr 0xC 4 (by omega) x 1 hx),
      memStore32_get_sep (fr 8 4 (by omega) x 1 hx)]
    exact M8out x hx
  have S11 : ∀ k, 0x20 ≤ k → k < 0x40 → M11 (G + BitVec.ofNat 32 k) = M8 (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => by
      rw [← hM11', memStore32_get_sep (so 0x10 4 k 1 (by omega) (by omega) (by omega)),
        memStore32_get_sep (so 0xC 4 k 1 (by omega) (by omega) (by omega)),
        memStore32_get_sep (so 8 4 k 1 (by omega) (by omega) (by omega))]
  have rp11 : memLoad32 M11 (G + 8) = bp := by
    rw [← hM11', show G + 8 = G + BitVec.ofNat 32 8 from rfl,
      memLoad32_store32_sep (so 0x10 4 8 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0xC 4 8 4 (by omega) (by omega) (by omega))]
    exact memLoad32_store32_same _ _ _
  have rl11 : memLoad32 M11 (G + 8 + 4) = 40 := by
    rw [← hM11', show G + 8 + 4 = G + BitVec.ofNat 32 0xC from by rw [BitVec.add_assoc]; rfl,
      memLoad32_store32_sep (so 0x10 4 0xC 4 (by omega) (by omega) (by omega))]
    exact memLoad32_store32_same _ _ _
  have rq11 : memLoad32 M11 (G + 8 + 8) = 0 := by
    rw [← hM11', show G + 8 + 8 = G + BitVec.ofNat 32 0x10 from by rw [BitVec.add_assoc]; rfl]
    exact memLoad32_store32_same _ _ _
  have mw_eq : ∀ (Mx : Word → BitVec 8), (∀ x, Sep R 144 x 1 → Mx x = m.mem x) → ∀ i, i + 4 ≤ 40 →
      memLoad32 Mx (bp + BitVec.ofNat 32 i) = mw m.mem bp i := fun Mx hO i hi =>
    memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact hO _ (hBS.sub (c := i + j) (l := 1) (by omega)).symm
  -- 0x28: `Reader::magic(b"C3MF")`.
  obtain ⟨m18, c18, t18, sp18, a018, fr18, mem18⟩ := mp_magic Ly u17 (Ly.code code O11) mpc_at_28 mpc_at_2c
    (by decide) (by decide) sp17 a017 a117 rp11 rl11
  have hmg : magicResult M11 (G + 8) 0x4C533343 =
      if mw m.mem bp 0 == 0x4C533343 then 0xFFFFFFFF else 2 := by
    unfold magicResult
    rw [rp11, rl11, rq11, show bytesResult bp 40 0 4 = some (bp + 0, 0 + 4) from rfl]
    simp only
    rw [show bp + 0 = bp + BitVec.ofNat 32 0 from rfl, mw_eq M11 O11 0 (by omega)]
  have k18 : ∀ r, r ∉ parseClob → reg m18 r = reg m r := fun r hr =>
    (fr18 r (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide))
      (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide))).trans
      (k17 r hr)
  have s018 : reg m18 s0 = out := by
    rw [fr18 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact s017
  have mm18 : ∀ x, Sep (R + BitVec.ofNat 32 32) 48 x 1 → m18.mem x = memStore32 M11 (G + 8 + 8) 4 x := by
    obtain ⟨e32, -⟩ := Ly.r_eqs
    intro x hx
    rw [mem18 x (by rw [e32]; exact hx)]
    unfold magicMem
    rw [rp11, rl11, rq11, show bytesResult bp 40 0 4 = some (bp + 0, 0 + 4) from rfl]
    rfl
  obtain ⟨rp18, rl18, rq18, O18, S18⟩ := Ly.advance (c := 32) (N := 48) (by omega) rp11 rl11 O11 S11 mm18
  obtain ⟨m19, g19, c19, hg19, br19⟩ := mp_check t18 (Ly.code code O18).parse mpc_at_30 mpc_at_34 mpc_at_38
    (by decide)
  rw [hmg] at a018
  by_cases hm : (mw m.mem bp 0 == 0x4C533343) = false
  · rw [hm] at a018
    rcases br19 with ⟨hff, -⟩ | ⟨-, t19⟩
    · rw [a018] at hff; exact absurd hff (by decide)
    · exact errD6 m19 m18.mem g19 2 (pre17.trans (c18.trans c19)) t19 (Ly.code code O18).parse
        (by rw [hg19 sp (by decide)]; exact sp18) (by rw [hg19 s0 (by decide)]; exact s018)
        (by rw [hg19 a0 (by decide), a018]; rfl) (by unfold parseErr; rw [hm]; rfl) O18 S18
        (fun r hr => by rw [hg19 r (clob_ne hr (by decide))]; exact k18 r hr)
  replace hm : (mw m.mem bp 0 == 0x4C533343) = true := by
    cases h : (mw m.mem bp 0 == 0x4C533343)
    · exact absurd h hm
    · rfl
  rw [hm] at a018
  have t19 := (br19.resolve_right fun h => by rw [a018] at h; exact h.1 (by decide)).2
  -- 0x3A: `Reader::version_1`.
  have hc18 := (Ly.code code O18).parse
  obtain ⟨m20, e20, t20⟩ := t19.aluImm hc18 mpc_at_3a (off' := 0x3C) (by decide)
  obtain ⟨m21, c21, t21, sp21, a021, fr21, mem21⟩ := mp_version Ly t20 (Ly.code code O18) mpc_at_3c mpc_at_40
    (by decide) (by decide) (by rw [updz t19.zero (by decide), hg19 sp (by decide)]; exact sp18)
    (by simp +decide only [upd, ite_true, ite_false]; rw [hg19 sp (by decide), sp18]; rfl) rp18 rl18
  have k21 : ∀ r, r ∉ parseClob → reg m21 r = reg m r := fun r hr => by
    rw [fr21 r (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide))
      (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)),
      updz t19.zero (clob_ne hr (by decide)), hg19 r (clob_ne hr (by decide))]
    exact k18 r hr
  have s021 : reg m21 s0 = out := by
    rw [fr21 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      updz t19.zero (by decide), hg19 s0 (by decide)]; exact s018
  rw [version_val rp18 rl18 rq18 (O18 _ (hBS.sub (c := 4) (l := 1) (by omega)).symm)
    (O18 _ (hBS.sub (c := 5) (l := 1) (by omega)).symm)] at a021
  have mm21 : ∀ x, Sep (R + BitVec.ofNat 32 48) 32 x 1 → m21.mem x = memStore32 m18.mem (G + 8 + 8) 6 x := by
    obtain ⟨-, e48, -⟩ := Ly.r_eqs
    intro x hx
    rw [mem21 x (by rw [e48]; exact hx), u16Mem_val rp18 rl18 rq18 x]
  obtain ⟨rp21, rl21, rq21, O21, S21⟩ := Ly.advance (c := 48) (N := 32) (by omega) rp18 rl18 O18 S18 mm21
  have pre21 : Steps m m21 := pre17.trans (c18.trans (c19.trans (.cons e20 c21)))
  obtain ⟨m22, g22, c22, hg22, br22⟩ := mp_check t21 (Ly.code code O21).parse mpc_at_44 mpc_at_48 mpc_at_4c
    (by decide)
  by_cases hv : (((m.mem (bp + 5)).zeroExtend 32 <<< 24 ||| (m.mem (bp + 4)).zeroExtend 32 <<< 16 : Word) >>> 16
      == 1) = false
  · rw [hv] at a021
    rcases br22 with ⟨hff, -⟩ | ⟨-, t22⟩
    · rw [a021] at hff; exact absurd hff (by decide)
    · exact errD6 m22 m21.mem g22 3 (pre21.trans c22) t22 (Ly.code code O21).parse
        (by rw [hg22 sp (by decide)]; exact sp21) (by rw [hg22 s0 (by decide)]; exact s021)
        (by rw [hg22 a0 (by decide), a021]; rfl) (by unfold parseErr; rw [hm, hv]; rfl) O21 S21
        (fun r hr => by rw [hg22 r (clob_ne hr (by decide))]; exact k21 r hr)
  replace hv : (((m.mem (bp + 5)).zeroExtend 32 <<< 24 ||| (m.mem (bp + 4)).zeroExtend 32 <<< 16 : Word) >>> 16
      == 1) = true := by
    cases h : (((m.mem (bp + 5)).zeroExtend 32 <<< 24 ||| (m.mem (bp + 4)).zeroExtend 32 <<< 16 : Word) >>> 16
      == 1)
    · exact absurd h hv
    · rfl
  rw [hv] at a021
  have t22 := (br22.resolve_right fun h => by rw [a021] at h; exact h.1 (by decide)).2
  -- 0x4E: `Reader::reserved(2)`.
  have hc21 := (Ly.code code O21).parse
  obtain ⟨m23, e23, t23⟩ := t22.aluImm hc21 mpc_at_4e (off' := 0x50) (by decide)
  have u23 := t23.self
  obtain ⟨m24, e24, t24⟩ := u23.aluImm hc21 mpc_at_50 (off' := 0x52) (by decide)
  have g23 : ∀ r, r ≠ a0 → r ≠ a1 → reg m23 r = reg m21 r := fun r h0 h1 => by
    rw [t23.regs, updz t22.zero h0, hg22 r h1]
  obtain ⟨m25, c25, t25, sp25, a025, fr25, mem25⟩ := mp_reserved Ly t24 (Ly.code code O21) mpc_at_52 mpc_at_56
    (by decide) (by decide) (by rw [updz u23.zero (by decide), g23 sp (by decide) (by decide)]; exact sp21)
    (by
      rw [updz u23.zero (by decide), t23.regs]; simp +decide only [upd, ite_true, ite_false]
      rw [hg22 sp (by decide), sp21]; rfl)
    (by simp +decide only [upd, ite_true, ite_false]; rw [u23.zero]; rfl) rp21 rl21
  have k25 : ∀ r, r ∉ parseClob → reg m25 r = reg m r := fun r hr => by
    rw [fr25 r (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide))
      (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)),
      updz u23.zero (clob_ne hr (by decide)), g23 r (clob_ne hr (by decide)) (clob_ne hr (by decide))]
    exact k21 r hr
  have s025 : reg m25 s0 = out := by
    rw [fr25 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      updz u23.zero (by decide), g23 s0 (by decide) (by decide)]; exact s021
  have z6 : m21.mem (bp + 6) = m.mem (bp + 6) := O21 _ (hBS.sub (c := 6) (l := 1) (by omega)).symm
  have z7 : m21.mem (bp + 6 + 1) = m.mem (bp + 6 + 1) := by
    rw [show bp + 6 + 1 = bp + BitVec.ofNat 32 7 from by rw [BitVec.add_assoc]; rfl]
    exact O21 _ (hBS.sub (c := 7) (l := 1) (by omega)).symm
  rw [reserved_val rp21 rl21 rq21 (by
    show (m21.mem (bp + 6) == 0 && (m21.mem (bp + 6 + 1) == 0 && true)) =
      (m.mem (bp + 6) == 0 && (m.mem (bp + 6 + 1) == 0 && true))
    rw [z6, z7])] at a025
  have mm25 : ∀ x, Sep (R + BitVec.ofNat 32 64) 16 x 1 → m25.mem x = memStore32 m21.mem (G + 8 + 8) 8 x := by
    obtain ⟨-, -, e64, -⟩ := Ly.r_eqs
    intro x hx
    rw [mem25 x (by rw [e64]; exact hx), reservedMem_val rp21 rl21 rq21 x]
  obtain ⟨rp25, rl25, rq25, O25, S25⟩ := Ly.advance (c := 64) (N := 16) (by omega) rp21 rl21 O21 S21 mm25
  have pre25 : Steps m m25 := pre21.trans (c22.trans (.cons e23 (.cons e24 c25)))
  obtain ⟨m26, g26, c26, hg26, br26⟩ := mp_check t25 (Ly.code code O25).parse mpc_at_5a mpc_at_5e mpc_at_62
    (by decide)
  by_cases hz : allZero m.mem (bp + 6) 2 = false
  · rw [hz] at a025
    rcases br26 with ⟨hff, -⟩ | ⟨-, t26⟩
    · rw [a025] at hff; exact absurd hff (by decide)
    · exact errD6 m26 m25.mem g26 4 (pre25.trans c26) t26 (Ly.code code O25).parse
        (by rw [hg26 sp (by decide)]; exact sp25) (by rw [hg26 s0 (by decide)]; exact s025)
        (by rw [hg26 a0 (by decide), a025]; rfl) (by unfold parseErr; rw [hm, hv, hz]; rfl) O25 S25
        (fun r hr => by rw [hg26 r (clob_ne hr (by decide))]; exact k25 r hr)
  replace hz : allZero m.mem (bp + 6) 2 = true := by
    cases h : allZero m.mem (bp + 6) 2
    · exact absurd h hz
    · rfl
  rw [hz] at a025
  have t26 := (br26.resolve_right fun h => by rw [a025] at h; exact h.1 (by decide)).2
  have u26 := t26.self
  have sp26 : reg m26 sp = G := by rw [t26.regs, hg26 sp (by decide)]; exact sp25
  have s026 : reg m26 s0 = out := by rw [t26.regs, hg26 s0 (by decide)]; exact s025
  have k26 : ∀ r, r ∉ parseClob → reg m26 r = reg m r := fun r hr => by
    rw [t26.regs, hg26 r (clob_ne hr (by decide))]; exact k25 r hr
  have pre26 : Steps m m26 := pre25.trans c26
  have hc26 := (Ly.code code O25).parse
  obtain ⟨m27, e27, t27⟩ := u26.aluImm hc26 mpc_at_64 (off' := 0x66) (by decide)
  have u27 := t27.self
  have q27 : ∀ r, r ≠ a0 → reg m27 r = reg m26 r := fun r h => by rw [t27.regs]; exact updz u26.zero h
  obtain ⟨m28, e28, t28⟩ := u27.aluImm hc26 mpc_at_66 (off' := 0x68) (by decide)
  have u28 := t28.self
  have q28 : ∀ r, r ≠ a1 → reg m28 r = reg m27 r := fun r h => by rw [t28.regs]; exact updz u27.zero h
  obtain ⟨m29, e29, t29⟩ := u28.aluImm hc26 mpc_at_68 (off' := 0x6C) (by decide)
  have u29 := t29.self
  have q29 : ∀ r, r ≠ a2 → reg m29 r = reg m28 r := fun r h => by rw [t29.regs]; exact updz u28.zero h
  obtain ⟨m30, e30, t30⟩ := u29.lui hc26 mpc_at_6c (off' := 0x70) (by decide)
  have u30 := t30.self
  have q30 : ∀ r, r ≠ a3 → reg m30 r = reg m29 r := fun r h => by rw [t30.regs]; exact updz u29.zero h
  have b30 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m30 r = reg m26 r := fun r h0 h1 h2 h3 => by
    rw [q30 r h3, q29 r h2, q28 r h1, q27 r h0]
  have v30a0 : reg m30 a0 = G + 0x14 := by rw [q30 a0 (by decide), q29 a0 (by decide), q28 a0 (by decide)]; rw [t27.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp26]; rfl
  have v30a1 : reg m30 a1 = G + 8 := by rw [q30 a1 (by decide), q29 a1 (by decide)]; rw [t28.regs]; simp +decide only [upd, ite_true, ite_false]; rw [q27 sp (by decide), sp26]; rfl
  have v30a2 : reg m30 a2 = 0x25 := by rw [q30 a2 (by decide)]; rw [t29.regs]; simp +decide only [upd, ite_true, ite_false]; rw [show reg m28 x0 = 0 from u28.zero]; rfl
  have v30a3 : reg m30 a3 = 0x1D0000 := by rw [t30.regs]; simp +decide only [upd, ite_true, ite_false]
  obtain ⟨m31, My31, c31, t31, sp31, fr31, O31, S31, res31⟩ := mp_part_step Ly code (M0 := m.mem) (M2 := M8)
    (lo := 37) (hi := 0x1D0000) 8 (by omega) u30 mpc_at_70 mpc_at_74 mpc_at_78
    (by decide) (by decide) (by rw [b30 sp (by decide) (by decide) (by decide) (by decide)]; exact sp26) v30a0 v30a1 v30a2 v30a3
    rp25 rl25 rq25 O25 S25
  simp only [Nat.reduceAdd] at res31
  have k31 : ∀ r, r ∉ parseClob → reg m31 r = reg m r := fun r hr => by
    rw [fr31 r (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide))
      (clob_ne hr (by decide)) (clob_ne hr (by decide)), b30 r (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide))]
    exact k26 r hr
  have s031 : reg m31 s0 = out := by
    rw [fr31 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b30 s0 (by decide) (by decide) (by decide) (by decide)]; exact s026
  have pre31 : Steps m m31 := pre26.trans ((.cons e27 (.cons e28 (.cons e29 (.cons e30 c31)))))
  by_cases hpo1 : partOut 37 0x1D0000 (mw m.mem bp 12) = true
  · rw [ite_eq_left hpo1] at res31
    obtain ⟨err31a0, err3115⟩ := res31
    obtain ⟨m32, e32, t32⟩ := t31.taken (Ly.code code O31).parse 0xD2 mpc_at_7c (by decide)
      (by rw [err31a0, show reg m31 x0 = 0 from t31.zero]; decide)
    exact errD2 m32 My31 (reg m31) (pre31.trans (.single e32)) t32 (Ly.code code O31).parse sp31 s031
      err3115 (by unfold parseErr; rw [hm, hv, hz, hpo1]; rfl) O31 S31 k31
  replace hpo1 : partOut 37 0x1D0000 (mw m.mem bp 12) = false := by
    cases hh : partOut 37 0x1D0000 (mw m.mem bp 12)
    · rfl
    · exact absurd hh hpo1
  rw [ite_eq_right (by rw [hpo1]; decide)] at res31
  obtain ⟨ok31a0, rp31, rl31, rq31, w3118, w311c⟩ := res31
  obtain ⟨m32, e32, t32⟩ := t31.notTaken (Ly.code code O31).parse 0x7E mpc_at_7c (by decide)
    (by rw [ok31a0, show reg m31 x0 = 0 from t31.zero]; decide)
  obtain ⟨m33, e33, t33⟩ := t32.lw (Ly.code code O31).parse mpc_at_7e (off' := 0x80) (by decide)
    (by rw [sp31]; exact aligned_add hGa (k := 0x18) (by decide))
  have u33 := t33.self
  have q33 : ∀ r, r ≠ 9 → reg m33 r = reg m31 r := fun r h => by
    rw [t33.regs]; exact updz t32.zero h
  have sp33 : reg m33 sp = G := by rw [q33 sp (by decide)]; exact sp31
  have l33_9 : reg m33 9 = mw m.mem bp 8 := by
    rw [t33.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp31]; exact w3118
  obtain ⟨m34, e34, t34⟩ := u33.lw (Ly.code code O31).parse mpc_at_80 (off' := 0x82) (by decide)
    (by rw [sp33]; exact aligned_add hGa (k := 0x1C) (by decide))
  have u34 := t34.self
  have q34 : ∀ r, r ≠ 22 → reg m34 r = reg m33 r := fun r h => by
    rw [t34.regs]; exact updz u33.zero h
  have sp34 : reg m34 sp = G := by rw [q34 sp (by decide)]; exact sp33
  have l34_22 : reg m34 22 = mw m.mem bp 12 := by
    rw [t34.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp33]; exact w311c
  have k34 : ∀ r, r ∉ parseClob → reg m34 r = reg m r := fun r hr => by
    rw [q34 r (clob_ne hr (by decide)), q33 r (clob_ne hr (by decide))]; exact k31 r hr
  have s034 : reg m34 s0 = out := by rw [q34 s0 (by decide), q33 s0 (by decide)]; exact s031
  have L34_9 : reg m34 9 = mw m.mem bp 8 := by rw [q34 9 (by decide)]; exact l33_9
  have pre34 : Steps m m34 := pre31.trans (.cons e32 (.cons e33 (.single e34)))
  have sp34' := sp34
  have hc34 := (Ly.code code O31).parse
  obtain ⟨m35, e35, t35⟩ := u34.aluImm hc34 mpc_at_82 (off' := 0x84) (by decide)
  have u35 := t35.self
  have q35 : ∀ r, r ≠ a0 → reg m35 r = reg m34 r := fun r h => by rw [t35.regs]; exact updz u34.zero h
  obtain ⟨m36, e36, t36⟩ := u35.aluImm hc34 mpc_at_84 (off' := 0x86) (by decide)
  have u36 := t36.self
  have q36 : ∀ r, r ≠ a1 → reg m36 r = reg m35 r := fun r h => by rw [t36.regs]; exact updz u35.zero h
  obtain ⟨m37, e37, t37⟩ := u36.aluImm hc34 mpc_at_86 (off' := 0x8A) (by decide)
  have u37 := t37.self
  have q37 : ∀ r, r ≠ a2 → reg m37 r = reg m36 r := fun r h => by rw [t37.regs]; exact updz u36.zero h
  obtain ⟨m38, e38, t38⟩ := u37.lui hc34 mpc_at_8a (off' := 0x8C) (by decide)
  have u38 := t38.self
  have q38 : ∀ r, r ≠ a3 → reg m38 r = reg m37 r := fun r h => by rw [t38.regs]; exact updz u37.zero h
  have b38 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m38 r = reg m34 r := fun r h0 h1 h2 h3 => by
    rw [q38 r h3, q37 r h2, q36 r h1, q35 r h0]
  have v38a0 : reg m38 a0 = G + 0x14 := by rw [q38 a0 (by decide), q37 a0 (by decide), q36 a0 (by decide)]; rw [t35.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp34]; rfl
  have v38a1 : reg m38 a1 = G + 8 := by rw [q38 a1 (by decide), q37 a1 (by decide)]; rw [t36.regs]; simp +decide only [upd, ite_true, ite_false]; rw [q35 sp (by decide), sp34]; rfl
  have v38a2 : reg m38 a2 = 0x31 := by rw [q38 a2 (by decide)]; rw [t37.regs]; simp +decide only [upd, ite_true, ite_false]; rw [show reg m36 x0 = 0 from u36.zero]; rfl
  have v38a3 : reg m38 a3 = 0x4000 := by rw [t38.regs]; simp +decide only [upd, ite_true, ite_false]
  obtain ⟨m39, My39, c39, t39, sp39, fr39, O39, S39, res39⟩ := mp_part_step Ly code (M0 := m.mem) (M2 := M8)
    (lo := 49) (hi := 0x4000) 16 (by omega) u38 mpc_at_8c mpc_at_90 mpc_at_94
    (by decide) (by decide) (by rw [b38 sp (by decide) (by decide) (by decide) (by decide)]; exact sp34) v38a0 v38a1 v38a2 v38a3
    rp31 rl31 rq31 O31 S31
  simp only [Nat.reduceAdd] at res39
  have k39 : ∀ r, r ∉ parseClob → reg m39 r = reg m r := fun r hr => by
    rw [fr39 r (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide))
      (clob_ne hr (by decide)) (clob_ne hr (by decide)), b38 r (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide))]
    exact k34 r hr
  have s039 : reg m39 s0 = out := by
    rw [fr39 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b38 s0 (by decide) (by decide) (by decide) (by decide)]; exact s034
  have l39_9 : reg m39 9 = mw m.mem bp 8 := by
    rw [fr39 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b38 9 (by decide) (by decide) (by decide) (by decide)]; exact L34_9
  have l39_22 : reg m39 22 = mw m.mem bp 12 := by
    rw [fr39 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b38 22 (by decide) (by decide) (by decide) (by decide)]; exact l34_22
  have pre39 : Steps m m39 := pre34.trans ((.cons e35 (.cons e36 (.cons e37 (.cons e38 c39)))))
  by_cases hpo2 : partOut 49 0x4000 (mw m.mem bp 20) = true
  · rw [ite_eq_left hpo2] at res39
    obtain ⟨err39a0, err3915⟩ := res39
    obtain ⟨m40, e40, t40⟩ := t39.taken (Ly.code code O39).parse 0xD2 mpc_at_98 (by decide)
      (by rw [err39a0, show reg m39 x0 = 0 from t39.zero]; decide)
    exact errD2 m40 My39 (reg m39) (pre39.trans (.single e40)) t40 (Ly.code code O39).parse sp39 s039
      err3915 (by unfold parseErr; rw [hm, hv, hz, hpo1, hpo2]; rfl) O39 S39 k39
  replace hpo2 : partOut 49 0x4000 (mw m.mem bp 20) = false := by
    cases hh : partOut 49 0x4000 (mw m.mem bp 20)
    · rfl
    · exact absurd hh hpo2
  rw [ite_eq_right (by rw [hpo2]; decide)] at res39
  obtain ⟨ok39a0, rp39, rl39, rq39, w3918, w391c⟩ := res39
  obtain ⟨m40, e40, t40⟩ := t39.notTaken (Ly.code code O39).parse 0x9A mpc_at_98 (by decide)
    (by rw [ok39a0, show reg m39 x0 = 0 from t39.zero]; decide)
  obtain ⟨m41, e41, t41⟩ := t40.lw (Ly.code code O39).parse mpc_at_9a (off' := 0x9C) (by decide)
    (by rw [sp39]; exact aligned_add hGa (k := 0x18) (by decide))
  have u41 := t41.self
  have q41 : ∀ r, r ≠ 18 → reg m41 r = reg m39 r := fun r h => by
    rw [t41.regs]; exact updz t40.zero h
  have sp41 : reg m41 sp = G := by rw [q41 sp (by decide)]; exact sp39
  have l41_18 : reg m41 18 = mw m.mem bp 16 := by
    rw [t41.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp39]; exact w3918
  obtain ⟨m42, e42, t42⟩ := u41.lw (Ly.code code O39).parse mpc_at_9c (off' := 0x9E) (by decide)
    (by rw [sp41]; exact aligned_add hGa (k := 0x1C) (by decide))
  have u42 := t42.self
  have q42 : ∀ r, r ≠ 19 → reg m42 r = reg m41 r := fun r h => by
    rw [t42.regs]; exact updz u41.zero h
  have sp42 : reg m42 sp = G := by rw [q42 sp (by decide)]; exact sp41
  have l42_19 : reg m42 19 = mw m.mem bp 20 := by
    rw [t42.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp41]; exact w391c
  have k42 : ∀ r, r ∉ parseClob → reg m42 r = reg m r := fun r hr => by
    rw [q42 r (clob_ne hr (by decide)), q41 r (clob_ne hr (by decide))]; exact k39 r hr
  have s042 : reg m42 s0 = out := by rw [q42 s0 (by decide), q41 s0 (by decide)]; exact s039
  have L42_18 : reg m42 18 = mw m.mem bp 16 := by rw [q42 18 (by decide)]; exact l41_18
  have pre42 : Steps m m42 := pre39.trans (.cons e40 (.cons e41 (.single e42)))
  have L42_9 : reg m42 9 = mw m.mem bp 8 := by rw [q42 9 (by decide), q41 9 (by decide)]; exact l39_9
  have L42_22 : reg m42 22 = mw m.mem bp 12 := by rw [q42 22 (by decide), q41 22 (by decide)]; exact l39_22
  have sp42' := sp42
  have hc42 := (Ly.code code O39).parse
  obtain ⟨m43, e43, t43⟩ := u42.aluImm hc42 mpc_at_9e (off' := 0xA0) (by decide)
  have u43 := t43.self
  have q43 : ∀ r, r ≠ a3 → reg m43 r = reg m42 r := fun r h => by rw [t43.regs]; exact updz u42.zero h
  obtain ⟨m44, e44, t44⟩ := u43.aluImm hc42 mpc_at_a0 (off' := 0xA2) (by decide)
  have u44 := t44.self
  have q44 : ∀ r, r ≠ a3 → reg m44 r = reg m43 r := fun r h => by rw [t44.regs]; exact updz u43.zero h
  obtain ⟨m45, e45, t45⟩ := u44.aluImm hc42 mpc_at_a2 (off' := 0xA4) (by decide)
  have u45 := t45.self
  have q45 : ∀ r, r ≠ a0 → reg m45 r = reg m44 r := fun r h => by rw [t45.regs]; exact updz u44.zero h
  obtain ⟨m46, e46, t46⟩ := u45.aluImm hc42 mpc_at_a4 (off' := 0xA6) (by decide)
  have u46 := t46.self
  have q46 : ∀ r, r ≠ a1 → reg m46 r = reg m45 r := fun r h => by rw [t46.regs]; exact updz u45.zero h
  obtain ⟨m47, e47, t47⟩ := u46.aluImm hc42 mpc_at_a6 (off' := 0xA8) (by decide)
  have u47 := t47.self
  have q47 : ∀ r, r ≠ a2 → reg m47 r = reg m46 r := fun r h => by rw [t47.regs]; exact updz u46.zero h
  have b47 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m47 r = reg m42 r := fun r h0 h1 h2 h3 => by
    rw [q47 r h2, q46 r h1, q45 r h0, q44 r h3, q43 r h3]
  have v43a3 : reg m43 a3 = 1 := by rw [t43.regs]; simp +decide only [upd, ite_true, ite_false]; rw [show reg m42 x0 = 0 from u42.zero]; rfl
  have v47a0 : reg m47 a0 = G + 0x14 := by rw [q47 a0 (by decide), q46 a0 (by decide)]; rw [t45.regs]; simp +decide only [upd, ite_true, ite_false]; rw [q44 sp (by decide), q43 sp (by decide), sp42]; rfl
  have v47a1 : reg m47 a1 = G + 8 := by rw [q47 a1 (by decide)]; rw [t46.regs]; simp +decide only [upd, ite_true, ite_false]; rw [q45 sp (by decide), q44 sp (by decide), q43 sp (by decide), sp42]; rfl
  have v47a2 : reg m47 a2 = 0x8 := by rw [t47.regs]; simp +decide only [upd, ite_true, ite_false]; rw [show reg m46 x0 = 0 from u46.zero]; rfl
  have v47a3 : reg m47 a3 = 0x800 := by rw [q47 a3 (by decide), q46 a3 (by decide), q45 a3 (by decide)]; rw [t44.regs]; simp +decide only [upd, ite_true, ite_false]; rw [v43a3]; rfl
  obtain ⟨m48, My48, c48, t48, sp48, fr48, O48, S48, res48⟩ := mp_part_step Ly code (M0 := m.mem) (M2 := M8)
    (lo := 8) (hi := 0x800) 24 (by omega) u47 mpc_at_a8 mpc_at_ac mpc_at_b0
    (by decide) (by decide) (by rw [b47 sp (by decide) (by decide) (by decide) (by decide)]; exact sp42) v47a0 v47a1 v47a2 v47a3
    rp39 rl39 rq39 O39 S39
  simp only [Nat.reduceAdd] at res48
  have k48 : ∀ r, r ∉ parseClob → reg m48 r = reg m r := fun r hr => by
    rw [fr48 r (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide))
      (clob_ne hr (by decide)) (clob_ne hr (by decide)), b47 r (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide))]
    exact k42 r hr
  have s048 : reg m48 s0 = out := by
    rw [fr48 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b47 s0 (by decide) (by decide) (by decide) (by decide)]; exact s042
  have l48_9 : reg m48 9 = mw m.mem bp 8 := by
    rw [fr48 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b47 9 (by decide) (by decide) (by decide) (by decide)]; exact L42_9
  have l48_22 : reg m48 22 = mw m.mem bp 12 := by
    rw [fr48 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b47 22 (by decide) (by decide) (by decide) (by decide)]; exact L42_22
  have l48_18 : reg m48 18 = mw m.mem bp 16 := by
    rw [fr48 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b47 18 (by decide) (by decide) (by decide) (by decide)]; exact L42_18
  have l48_19 : reg m48 19 = mw m.mem bp 20 := by
    rw [fr48 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b47 19 (by decide) (by decide) (by decide) (by decide)]; exact l42_19
  have pre48 : Steps m m48 := pre42.trans ((.cons e43 (.cons e44 (.cons e45 (.cons e46 (.cons e47 c48))))))
  by_cases hpo3 : partOut 8 0x800 (mw m.mem bp 28) = true
  · rw [ite_eq_left hpo3] at res48
    obtain ⟨err48a0, err4815⟩ := res48
    obtain ⟨m49, e49, t49⟩ := t48.taken (Ly.code code O48).parse 0xD2 mpc_at_b4 (by decide)
      (by rw [err48a0, show reg m48 x0 = 0 from t48.zero]; decide)
    exact errD2 m49 My48 (reg m48) (pre48.trans (.single e49)) t49 (Ly.code code O48).parse sp48 s048
      err4815 (by unfold parseErr; rw [hm, hv, hz, hpo1, hpo2, hpo3]; rfl) O48 S48 k48
  replace hpo3 : partOut 8 0x800 (mw m.mem bp 28) = false := by
    cases hh : partOut 8 0x800 (mw m.mem bp 28)
    · rfl
    · exact absurd hh hpo3
  rw [ite_eq_right (by rw [hpo3]; decide)] at res48
  obtain ⟨ok48a0, rp48, rl48, rq48, w4818, w481c⟩ := res48
  obtain ⟨m49, e49, t49⟩ := t48.notTaken (Ly.code code O48).parse 0xB6 mpc_at_b4 (by decide)
    (by rw [ok48a0, show reg m48 x0 = 0 from t48.zero]; decide)
  obtain ⟨m50, e50, t50⟩ := t49.lw (Ly.code code O48).parse mpc_at_b6 (off' := 0xB8) (by decide)
    (by rw [sp48]; exact aligned_add hGa (k := 0x18) (by decide))
  have u50 := t50.self
  have q50 : ∀ r, r ≠ 20 → reg m50 r = reg m48 r := fun r h => by
    rw [t50.regs]; exact updz t49.zero h
  have sp50 : reg m50 sp = G := by rw [q50 sp (by decide)]; exact sp48
  have l50_20 : reg m50 20 = mw m.mem bp 24 := by
    rw [t50.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp48]; exact w4818
  obtain ⟨m51, e51, t51⟩ := u50.lw (Ly.code code O48).parse mpc_at_b8 (off' := 0xBA) (by decide)
    (by rw [sp50]; exact aligned_add hGa (k := 0x1C) (by decide))
  have u51 := t51.self
  have q51 : ∀ r, r ≠ 21 → reg m51 r = reg m50 r := fun r h => by
    rw [t51.regs]; exact updz u50.zero h
  have sp51 : reg m51 sp = G := by rw [q51 sp (by decide)]; exact sp50
  have l51_21 : reg m51 21 = mw m.mem bp 28 := by
    rw [t51.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp50]; exact w481c
  have k51 : ∀ r, r ∉ parseClob → reg m51 r = reg m r := fun r hr => by
    rw [q51 r (clob_ne hr (by decide)), q50 r (clob_ne hr (by decide))]; exact k48 r hr
  have s051 : reg m51 s0 = out := by rw [q51 s0 (by decide), q50 s0 (by decide)]; exact s048
  have L51_20 : reg m51 20 = mw m.mem bp 24 := by rw [q51 20 (by decide)]; exact l50_20
  have pre51 : Steps m m51 := pre48.trans (.cons e49 (.cons e50 (.single e51)))
  have L51_9 : reg m51 9 = mw m.mem bp 8 := by rw [q51 9 (by decide), q50 9 (by decide)]; exact l48_9
  have L51_22 : reg m51 22 = mw m.mem bp 12 := by rw [q51 22 (by decide), q50 22 (by decide)]; exact l48_22
  have L51_18 : reg m51 18 = mw m.mem bp 16 := by rw [q51 18 (by decide), q50 18 (by decide)]; exact l48_18
  have L51_19 : reg m51 19 = mw m.mem bp 20 := by rw [q51 19 (by decide), q50 19 (by decide)]; exact l48_19
  have sp51' := sp51
  have hc51 := (Ly.code code O48).parse
  obtain ⟨m52, e52, t52⟩ := u51.aluImm hc51 mpc_at_ba (off' := 0xBC) (by decide)
  have u52 := t52.self
  have q52 : ∀ r, r ≠ a0 → reg m52 r = reg m51 r := fun r h => by rw [t52.regs]; exact updz u51.zero h
  obtain ⟨m53, e53, t53⟩ := u52.aluImm hc51 mpc_at_bc (off' := 0xBE) (by decide)
  have u53 := t53.self
  have q53 : ∀ r, r ≠ a1 → reg m53 r = reg m52 r := fun r h => by rw [t53.regs]; exact updz u52.zero h
  obtain ⟨m54, e54, t54⟩ := u53.aluImm hc51 mpc_at_be (off' := 0xC2) (by decide)
  have u54 := t54.self
  have q54 : ∀ r, r ≠ a2 → reg m54 r = reg m53 r := fun r h => by rw [t54.regs]; exact updz u53.zero h
  obtain ⟨m55, e55, t55⟩ := u54.lui hc51 mpc_at_c2 (off' := 0xC4) (by decide)
  have u55 := t55.self
  have q55 : ∀ r, r ≠ a3 → reg m55 r = reg m54 r := fun r h => by rw [t55.regs]; exact updz u54.zero h
  have b55 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m55 r = reg m51 r := fun r h0 h1 h2 h3 => by
    rw [q55 r h3, q54 r h2, q53 r h1, q52 r h0]
  have v55a0 : reg m55 a0 = G + 0x14 := by rw [q55 a0 (by decide), q54 a0 (by decide), q53 a0 (by decide)]; rw [t52.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp51]; rfl
  have v55a1 : reg m55 a1 = G + 8 := by rw [q55 a1 (by decide), q54 a1 (by decide)]; rw [t53.regs]; simp +decide only [upd, ite_true, ite_false]; rw [q52 sp (by decide), sp51]; rfl
  have v55a2 : reg m55 a2 = 0x1BB := by rw [q55 a2 (by decide)]; rw [t54.regs]; simp +decide only [upd, ite_true, ite_false]; rw [show reg m53 x0 = 0 from u53.zero]; rfl
  have v55a3 : reg m55 a3 = 0x1000 := by rw [t55.regs]; simp +decide only [upd, ite_true, ite_false]
  obtain ⟨m56, My56, c56, t56, sp56, fr56, O56, S56, res56⟩ := mp_part_step Ly code (M0 := m.mem) (M2 := M8)
    (lo := 443) (hi := 0x1000) 32 (by omega) u55 mpc_at_c4 mpc_at_c8 mpc_at_cc
    (by decide) (by decide) (by rw [b55 sp (by decide) (by decide) (by decide) (by decide)]; exact sp51) v55a0 v55a1 v55a2 v55a3
    rp48 rl48 rq48 O48 S48
  simp only [Nat.reduceAdd] at res56
  have k56 : ∀ r, r ∉ parseClob → reg m56 r = reg m r := fun r hr => by
    rw [fr56 r (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide))
      (clob_ne hr (by decide)) (clob_ne hr (by decide)), b55 r (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide)) (clob_ne hr (by decide))]
    exact k51 r hr
  have s056 : reg m56 s0 = out := by
    rw [fr56 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b55 s0 (by decide) (by decide) (by decide) (by decide)]; exact s051
  have l56_9 : reg m56 9 = mw m.mem bp 8 := by
    rw [fr56 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b55 9 (by decide) (by decide) (by decide) (by decide)]; exact L51_9
  have l56_22 : reg m56 22 = mw m.mem bp 12 := by
    rw [fr56 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b55 22 (by decide) (by decide) (by decide) (by decide)]; exact L51_22
  have l56_18 : reg m56 18 = mw m.mem bp 16 := by
    rw [fr56 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b55 18 (by decide) (by decide) (by decide) (by decide)]; exact L51_18
  have l56_19 : reg m56 19 = mw m.mem bp 20 := by
    rw [fr56 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b55 19 (by decide) (by decide) (by decide) (by decide)]; exact L51_19
  have l56_20 : reg m56 20 = mw m.mem bp 24 := by
    rw [fr56 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b55 20 (by decide) (by decide) (by decide) (by decide)]; exact L51_20
  have l56_21 : reg m56 21 = mw m.mem bp 28 := by
    rw [fr56 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b55 21 (by decide) (by decide) (by decide) (by decide)]; exact l51_21
  have pre56 : Steps m m56 := pre51.trans ((.cons e52 (.cons e53 (.cons e54 (.cons e55 c56)))))
  -- LAST
  have hcY := (Ly.code code O56).parse
  by_cases hpo4 : partOut 443 0x1000 (mw m.mem bp 36) = true
  · rw [ite_eq_left hpo4] at res56
    obtain ⟨err56a0, err5615⟩ := res56
    obtain ⟨m57, e57, t57⟩ := t56.notTaken hcY 0xD2 mpc_at_d0 (by decide)
      (by rw [err56a0, show reg m56 x0 = 0 from t56.zero]; decide)
    exact errD2 m57 My56 (reg m56) (pre56.trans (.single e57)) t57 hcY sp56 s056 err5615
      (by unfold parseErr; rw [hm, hv, hz, hpo1, hpo2, hpo3, hpo4]; rfl) O56 S56 k56
  replace hpo4 : partOut 443 0x1000 (mw m.mem bp 36) = false := by
    cases hh : partOut 443 0x1000 (mw m.mem bp 36)
    · rfl
    · exact absurd hh hpo4
  rw [ite_eq_right (by rw [hpo4]; decide)] at res56
  obtain ⟨ok56a0, rp56, rl56, rq56, w5618, w561c⟩ := res56
  obtain ⟨m57, e57, t57⟩ := t56.taken hcY 0xF4 mpc_at_d0 (by decide)
    (by rw [ok56a0, show reg m56 x0 = 0 from t56.zero]; decide)
  have u57 := t57.self
  have q57 : ∀ r, reg m57 r = reg m56 r := t57.regs
  have sp57 : reg m57 sp = G := by rw [q57]; exact sp56
  have s057 : reg m57 s0 = out := by rw [q57]; exact s056
  have k57 : ∀ r, r ∉ parseClob → reg m57 r = reg m r := fun r hr => by rw [q57]; exact k56 r hr
  have pre57 : Steps m m57 := pre56.trans (.single e57)
  have err166 : ∀ (n : Machine) (g : Fin 32 → Word), Steps m n → St My56 MP n 0x166 g → g sp = G → g s0 = out →
      (∀ r, r ∉ parseClob → g r = reg m r) → parseErr m.mem bp = some 7 →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg m' r = reg m r) ∧
        ∀ x, Sep R 144 x 1 → m'.mem x = parseMem m.mem out bp x := by
    intro n g hn s hs hs0 hk hpe
    obtain ⟨n1, d1, u1⟩ := s.aluImm hcY mpc_at_166 (off' := 0x168) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.jump hcY mpc_at_168 (off' := 0xD6) (by decide) (by rw [u1.pc]; decide)
    exact errD6 n2 My56 _ 7 (hn.trans (.cons d1 (.single d2))) u2 hcY (by rw [updz s.zero (by decide)]; exact hs)
      (by rw [updz s.zero (by decide)]; exact hs0) (by simp +decide only [upd, ite_true, ite_false]; rw [s.zero]; rfl)
      hpe O56 S56 (fun r hr => by rw [updz s.zero (clob_ne hr (by decide))]; exact hk r hr)
  obtain ⟨m58, e58, t58⟩ := u57.lw hcY mpc_at_f4 (off' := 0xF6) (by decide)
    (by rw [sp57]; exact aligned_add hGa (k := 0xC) (by decide))
  have u58 := t58.self
  have q58 : ∀ r, r ≠ a0 → reg m58 r = reg m57 r := fun r h => by rw [t58.regs]; exact updz u57.zero h
  have sp58 : reg m58 sp = G := by rw [q58 sp (by decide)]; exact sp57
  have s058 : reg m58 s0 = out := by rw [q58 s0 (by decide)]; exact s057
  have k58 : ∀ r, r ∉ parseClob → reg m58 r = reg m r := fun r hr => by
    rw [q58 r (clob_ne hr (by decide))]; exact k57 r hr
  have pre58 : Steps m m58 := pre57.trans (.single e58)
  have v58a0 : reg m58 a0 = 40 := by
    rw [t58.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp57, show G + 0xC = G + 8 + 4 from by rw [BitVec.add_assoc]; rfl]; exact rl56
  obtain ⟨m59, e59, t59⟩ := u58.lw hcY mpc_at_f6 (off' := 0xF8) (by decide)
    (by rw [sp58]; exact aligned_add hGa (k := 0x10) (by decide))
  have u59 := t59.self
  have q59 : ∀ r, r ≠ a1 → reg m59 r = reg m58 r := fun r h => by rw [t59.regs]; exact updz u58.zero h
  have sp59 : reg m59 sp = G := by rw [q59 sp (by decide)]; exact sp58
  have s059 : reg m59 s0 = out := by rw [q59 s0 (by decide)]; exact s058
  have k59 : ∀ r, r ∉ parseClob → reg m59 r = reg m r := fun r hr => by
    rw [q59 r (clob_ne hr (by decide))]; exact k58 r hr
  have pre59 : Steps m m59 := pre58.trans (.single e59)
  have v59a1 : reg m59 a1 = 40 := by
    rw [t59.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp58, show G + 0x10 = G + 8 + 8 from by rw [BitVec.add_assoc]; rfl]; exact rq56
  obtain ⟨m60, e60, t60⟩ := u59.notTaken hcY 0xFC mpc_at_f8 (by decide)
    (by rw [v59a1, q59 a0 (by decide), v58a0]; decide)
  have u60 := t60.self
  have q60 : ∀ r, reg m60 r = reg m59 r := t60.regs
  have sp60 : reg m60 sp = G := by rw [q60]; exact sp59
  have s060 : reg m60 s0 = out := by rw [q60]; exact s059
  have k60 : ∀ r, r ∉ parseClob → reg m60 r = reg m r := fun r hr => by rw [q60]; exact k59 r hr
  have pre60 : Steps m m60 := pre59.trans (.single e60)
  have base : ∀ r, r ≠ a0 → r ≠ a1 → reg m60 r = reg m56 r := fun r h0 h1 => by
    rw [q60, q59 r h1, q58 r h0, q57]
  obtain ⟨m61, e61, t61⟩ := u60.lui hcY mpc_at_fc (off' := 0xFE) (by decide)
  have u61 := t61.self
  have q61 : ∀ r, r ≠ a3 → reg m61 r = reg m60 r := fun r h => by rw [t61.regs]; exact updz u60.zero h
  have sp61 : reg m61 sp = G := by rw [q61 sp (by decide)]; exact sp60
  have s061 : reg m61 s0 = out := by rw [q61 s0 (by decide)]; exact s060
  have k61 : ∀ r, r ∉ parseClob → reg m61 r = reg m r := fun r hr => by
    rw [q61 r (clob_ne hr (by decide))]; exact k60 r hr
  have pre61 : Steps m m61 := pre60.trans (.single e61)
  have v61a3 : reg m61 a3 = 0x10000 := by rw [t61.regs]; simp +decide only [upd, ite_true, ite_false]
  have v619 : reg m61 9 = mw m.mem bp 8 := by rw [q61 9 (by decide), base 9 (by decide) (by decide)]; exact l56_9
  by_cases hc7 : (mw m.mem bp 8 == 0x10000) = false
  · obtain ⟨m62, e62, t62⟩ := u61.taken hcY 0x166 mpc_at_fe (by decide)
      (by rw [v619, v61a3]; show (!(mw m.mem bp 8 == 0x10000)) = true; rw [hc7]; rfl)
    exact err166 m62 (reg m61) (pre61.trans (.single e62)) t62 sp61 s061 k61
      (by unfold parseErr; rw [hm, hv, hz, hpo1, hpo2, hpo3, hpo4, hc7]; rfl)
  replace hc7 : (mw m.mem bp 8 == 0x10000) = true := by
    cases hh : (mw m.mem bp 8 == 0x10000)
    · exact absurd hh hc7
    · rfl
  obtain ⟨m62, e62, t62⟩ := u61.notTaken hcY 0x102 mpc_at_fe (by decide)
    (by rw [v619, v61a3]; show (!(mw m.mem bp 8 == 0x10000)) = false; rw [hc7]; rfl)
  have u62 := t62.self
  have q62 : ∀ r, reg m62 r = reg m61 r := t62.regs
  have sp62 : reg m62 sp = G := by rw [q62]; exact sp61
  have s062 : reg m62 s0 = out := by rw [q62]; exact s061
  have k62 : ∀ r, r ∉ parseClob → reg m62 r = reg m r := fun r hr => by rw [q62]; exact k61 r hr
  have pre62 : Steps m m62 := pre61.trans (.single e62)
  obtain ⟨m63, e63, t63⟩ := u62.lui hcY mpc_at_102 (off' := 0x104) (by decide)
  have u63 := t63.self
  have q63 : ∀ r, r ≠ a0 → reg m63 r = reg m62 r := fun r h => by rw [t63.regs]; exact updz u62.zero h
  have sp63 : reg m63 sp = G := by rw [q63 sp (by decide)]; exact sp62
  have s063 : reg m63 s0 = out := by rw [q63 s0 (by decide)]; exact s062
  have k63 : ∀ r, r ∉ parseClob → reg m63 r = reg m r := fun r hr => by
    rw [q63 r (clob_ne hr (by decide))]; exact k62 r hr
  have pre63 : Steps m m63 := pre62.trans (.single e63)
  obtain ⟨m64, e64, t64⟩ := u63.aluImm hcY mpc_at_104 (off' := 0x108) (by decide)
  have u64 := t64.self
  have q64 : ∀ r, r ≠ a1 → reg m64 r = reg m63 r := fun r h => by rw [t64.regs]; exact updz u63.zero h
  have sp64 : reg m64 sp = G := by rw [q64 sp (by decide)]; exact sp63
  have s064 : reg m64 s0 = out := by rw [q64 s0 (by decide)]; exact s063
  have k64 : ∀ r, r ∉ parseClob → reg m64 r = reg m r := fun r hr => by
    rw [q64 r (clob_ne hr (by decide))]; exact k63 r hr
  have pre64 : Steps m m64 := pre63.trans (.single e64)
  have v64a1 : reg m64 a1 = 0xFFFEFFFF := by
    rw [t64.regs]; simp +decide only [upd, ite_true, ite_false]; rw [t63.regs]; simp +decide only [upd, ite_true, ite_false]
  obtain ⟨m65, e65, t65⟩ := u64.aluImm hcY mpc_at_108 (off' := 0x10A) (by decide)
  have u65 := t65.self
  have q65 : ∀ r, r ≠ a0 → reg m65 r = reg m64 r := fun r h => by rw [t65.regs]; exact updz u64.zero h
  have sp65 : reg m65 sp = G := by rw [q65 sp (by decide)]; exact sp64
  have s065 : reg m65 s0 = out := by rw [q65 s0 (by decide)]; exact s064
  have k65 : ∀ r, r ∉ parseClob → reg m65 r = reg m r := fun r hr => by
    rw [q65 r (clob_ne hr (by decide))]; exact k64 r hr
  have pre65 : Steps m m65 := pre64.trans (.single e65)
  have v65a0 : reg m65 a0 = 6 := by
    rw [t65.regs]; simp +decide only [upd, ite_true, ite_false]; rw [show reg m64 x0 = 0 from u64.zero]; rfl
  have base65 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a3 → reg m65 r = reg m56 r := fun r h0 h1 h3 => by
    rw [q65 r h0, q64 r h1, q63 r h0, q62, q61 r h3, base r h0 h1]
  have v6522 : reg m65 22 = mw m.mem bp 12 := by rw [base65 22 (by decide) (by decide) (by decide)]; exact l56_22
  have v65a1 : reg m65 a1 = 0xFFFEFFFF := by rw [q65 a1 (by decide)]; exact v64a1
  have err6 : ∀ (n : Machine) (g : Fin 32 → Word), Steps m n → St My56 MP n 0xD6 g → g sp = G → g s0 = out →
      g a0 = 6 → (∀ r, r ∉ parseClob → g r = reg m r) → parseErr m.mem bp = some 6 →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg m' r = reg m r) ∧
        ∀ x, Sep R 144 x 1 → m'.mem x = parseMem m.mem out bp x := fun n g hn s hs hs0 ha hk hpe =>
    errD6 n My56 g 6 hn s hcY hs hs0 (by rw [ha]; rfl) hpe O56 S56 hk
  by_cases hc6a : (0xFFFEFFFF : Word).ult (mw m.mem bp 12) = true
  · obtain ⟨m66, e66, t66⟩ := u65.taken hcY 0xD6 mpc_at_10a (by decide)
      (by rw [v65a1, v6522]; exact hc6a)
    exact err6 m66 (reg m65) (pre65.trans (.single e66)) t66 sp65 s065 v65a0 k65
      (by unfold parseErr; rw [hm, hv, hz, hpo1, hpo2, hpo3, hpo4, hc7, hc6a]; rfl)
  replace hc6a : (0xFFFEFFFF : Word).ult (mw m.mem bp 12) = false := by
    cases hh : (0xFFFEFFFF : Word).ult (mw m.mem bp 12)
    · rfl
    · exact absurd hh hc6a
  obtain ⟨m66, e66, t66⟩ := u65.notTaken hcY 0x10E mpc_at_10a (by decide)
    (by rw [v65a1, v6522]; exact hc6a)
  have u66 := t66.self
  have q66 : ∀ r, reg m66 r = reg m65 r := t66.regs
  have sp66 : reg m66 sp = G := by rw [q66]; exact sp65
  have s066 : reg m66 s0 = out := by rw [q66]; exact s065
  have k66 : ∀ r, r ∉ parseClob → reg m66 r = reg m r := fun r hr => by rw [q66]; exact k65 r hr
  have pre66 : Steps m m66 := pre65.trans (.single e66)
  obtain ⟨m67, e67, t67⟩ := u66.alu hcY mpc_at_10e (off' := 0x112) (by decide)
  have u67 := t67.self
  have q67 : ∀ r, r ≠ a4 → reg m67 r = reg m66 r := fun r h => by rw [t67.regs]; exact updz u66.zero h
  have sp67 : reg m67 sp = G := by rw [q67 sp (by decide)]; exact sp66
  have s067 : reg m67 s0 = out := by rw [q67 s0 (by decide)]; exact s066
  have k67 : ∀ r, r ∉ parseClob → reg m67 r = reg m r := fun r hr => by
    rw [q67 r (clob_ne hr (by decide))]; exact k66 r hr
  have pre67 : Steps m m67 := pre66.trans (.single e67)
  have base67 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a3 → r ≠ a4 → reg m67 r = reg m56 r := fun r h0 h1 h3 h4 => by
    rw [q67 r h4, q66, base65 r h0 h1 h3]
  have v67a4 : reg m67 a4 = mw m.mem bp 20 + mw m.mem bp 16 := by
    rw [t67.regs]; simp +decide only [upd, ite_true, ite_false]; rw [q66 19, q66 18, base65 19 (by decide) (by decide) (by decide), base65 18 (by decide) (by decide) (by decide), l56_19, l56_18]; rfl
  have v6719 : reg m67 19 = mw m.mem bp 20 := by rw [base67 19 (by decide) (by decide) (by decide) (by decide)]; exact l56_19
  have v67a0 : reg m67 a0 = 6 := by rw [q67 a0 (by decide), q66]; exact v65a0
  by_cases hc6b : (mw m.mem bp 20 + mw m.mem bp 16).ult (mw m.mem bp 20) = true
  · obtain ⟨m68, e68, t68⟩ := u67.taken hcY 0xD6 mpc_at_112 (by decide)
      (by rw [v67a4, v6719]; exact hc6b)
    exact err6 m68 (reg m67) (pre67.trans (.single e68)) t68 sp67 s067 v67a0 k67
      (by unfold parseErr; rw [hm, hv, hz, hpo1, hpo2, hpo3, hpo4, hc7, hc6a, hc6b]; rfl)
  replace hc6b : (mw m.mem bp 20 + mw m.mem bp 16).ult (mw m.mem bp 20) = false := by
    cases hh : (mw m.mem bp 20 + mw m.mem bp 16).ult (mw m.mem bp 20)
    · rfl
    · exact absurd hh hc6b
  obtain ⟨m68, e68, t68⟩ := u67.notTaken hcY 0x116 mpc_at_112 (by decide)
    (by rw [v67a4, v6719]; exact hc6b)
  have u68 := t68.self
  have q68 : ∀ r, reg m68 r = reg m67 r := t68.regs
  have sp68 : reg m68 sp = G := by rw [q68]; exact sp67
  have s068 : reg m68 s0 = out := by rw [q68]; exact s067
  have k68 : ∀ r, r ∉ parseClob → reg m68 r = reg m r := fun r hr => by rw [q68]; exact k67 r hr
  have pre68 : Steps m m68 := pre67.trans (.single e68)
  obtain ⟨m69, e69, t69⟩ := u68.alu hcY mpc_at_116 (off' := 0x11A) (by decide)
  have u69 := t69.self
  have q69 : ∀ r, r ≠ a5 → reg m69 r = reg m68 r := fun r h => by rw [t69.regs]; exact updz u68.zero h
  have sp69 : reg m69 sp = G := by rw [q69 sp (by decide)]; exact sp68
  have s069 : reg m69 s0 = out := by rw [q69 s0 (by decide)]; exact s068
  have k69 : ∀ r, r ∉ parseClob → reg m69 r = reg m r := fun r hr => by
    rw [q69 r (clob_ne hr (by decide))]; exact k68 r hr
  have pre69 : Steps m m69 := pre68.trans (.single e69)
  have base69 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m69 r = reg m56 r := fun r h0 h1 h3 h4 h5 => by
    rw [q69 r h5, q68, base67 r h0 h1 h3 h4]
  have v69a5 : reg m69 a5 = mw m.mem bp 28 + mw m.mem bp 24 := by
    rw [t69.regs]; simp +decide only [upd, ite_true, ite_false]; rw [q68 21, q68 20, base67 21 (by decide) (by decide) (by decide) (by decide), base67 20 (by decide) (by decide) (by decide) (by decide), l56_21, l56_20]; rfl
  have v6921 : reg m69 21 = mw m.mem bp 28 := by rw [base69 21 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l56_21
  have v69a0 : reg m69 a0 = 6 := by rw [q69 a0 (by decide), q68]; exact v67a0
  by_cases hc6c : (mw m.mem bp 28 + mw m.mem bp 24).ult (mw m.mem bp 28) = true
  · obtain ⟨m70, e70, t70⟩ := u69.taken hcY 0xD6 mpc_at_11a (by decide)
      (by rw [v69a5, v6921]; exact hc6c)
    exact err6 m70 (reg m69) (pre69.trans (.single e70)) t70 sp69 s069 v69a0 k69
      (by unfold parseErr; rw [hm, hv, hz, hpo1, hpo2, hpo3, hpo4, hc7, hc6a, hc6b, hc6c]; rfl)
  replace hc6c : (mw m.mem bp 28 + mw m.mem bp 24).ult (mw m.mem bp 28) = false := by
    cases hh : (mw m.mem bp 28 + mw m.mem bp 24).ult (mw m.mem bp 28)
    · rfl
    · exact absurd hh hc6c
  obtain ⟨m70, e70, t70⟩ := u69.notTaken hcY 0x11E mpc_at_11a (by decide)
    (by rw [v69a5, v6921]; exact hc6c)
  have u70 := t70.self
  have q70 : ∀ r, reg m70 r = reg m69 r := t70.regs
  have sp70 : reg m70 sp = G := by rw [q70]; exact sp69
  have s070 : reg m70 s0 = out := by rw [q70]; exact s069
  have k70 : ∀ r, r ∉ parseClob → reg m70 r = reg m r := fun r hr => by rw [q70]; exact k69 r hr
  have pre70 : Steps m m70 := pre69.trans (.single e70)
  obtain ⟨m71, e71, t71⟩ := u70.lw hcY mpc_at_11e (off' := 0x120) (by decide)
    (by rw [sp70]; exact aligned_add hGa (k := 0x18) (by decide))
  have u71 := t71.self
  have q71 : ∀ r, r ≠ 9 → reg m71 r = reg m70 r := fun r h => by rw [t71.regs]; exact updz u70.zero h
  have sp71 : reg m71 sp = G := by rw [q71 sp (by decide)]; exact sp70
  have s071 : reg m71 s0 = out := by rw [q71 s0 (by decide)]; exact s070
  have k71 : ∀ r, r ∉ parseClob → reg m71 r = reg m r := fun r hr => by
    rw [q71 r (clob_ne hr (by decide))]; exact k70 r hr
  have pre71 : Steps m m71 := pre70.trans (.single e71)
  have v719 : reg m71 9 = mw m.mem bp 32 := by
    rw [t71.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp70]; exact w5618
  obtain ⟨m72, e72, t72⟩ := u71.lw hcY mpc_at_120 (off' := 0x122) (by decide)
    (by rw [sp71]; exact aligned_add hGa (k := 0x1C) (by decide))
  have u72 := t72.self
  have q72 : ∀ r, r ≠ a2 → reg m72 r = reg m71 r := fun r h => by rw [t72.regs]; exact updz u71.zero h
  have sp72 : reg m72 sp = G := by rw [q72 sp (by decide)]; exact sp71
  have s072 : reg m72 s0 = out := by rw [q72 s0 (by decide)]; exact s071
  have k72 : ∀ r, r ∉ parseClob → reg m72 r = reg m r := fun r hr => by
    rw [q72 r (clob_ne hr (by decide))]; exact k71 r hr
  have pre72 : Steps m m72 := pre71.trans (.single e72)
  have v72a2 : reg m72 a2 = mw m.mem bp 36 := by
    rw [t72.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp71]; exact w561c
  obtain ⟨m73, e73, t73⟩ := u72.alu hcY mpc_at_122 (off' := 0x126) (by decide)
  have u73 := t73.self
  have q73 : ∀ r, r ≠ a1 → reg m73 r = reg m72 r := fun r h => by rw [t73.regs]; exact updz u72.zero h
  have sp73 : reg m73 sp = G := by rw [q73 sp (by decide)]; exact sp72
  have s073 : reg m73 s0 = out := by rw [q73 s0 (by decide)]; exact s072
  have k73 : ∀ r, r ∉ parseClob → reg m73 r = reg m r := fun r hr => by
    rw [q73 r (clob_ne hr (by decide))]; exact k72 r hr
  have pre73 : Steps m m73 := pre72.trans (.single e73)
  have v73a1 : reg m73 a1 = mw m.mem bp 36 + mw m.mem bp 32 := by
    rw [t73.regs]; simp +decide only [upd, ite_true, ite_false]; rw [v72a2, q72 9 (by decide), v719]; rfl
  have v73a2 : reg m73 a2 = mw m.mem bp 36 := by rw [q73 a2 (by decide)]; exact v72a2
  have v73a0 : reg m73 a0 = 6 := by rw [q73 a0 (by decide), q72 a0 (by decide), q71 a0 (by decide), q70]; exact v69a0
  by_cases hc6d : (mw m.mem bp 36 + mw m.mem bp 32).ult (mw m.mem bp 36) = true
  · obtain ⟨m74, e74, t74⟩ := u73.taken hcY 0xD6 mpc_at_126 (by decide)
      (by rw [v73a1, v73a2]; exact hc6d)
    exact err6 m74 (reg m73) (pre73.trans (.single e74)) t74 sp73 s073 v73a0 k73
      (by unfold parseErr; rw [hm, hv, hz, hpo1, hpo2, hpo3, hpo4, hc7, hc6a, hc6b, hc6c, hc6d]; rfl)
  replace hc6d : (mw m.mem bp 36 + mw m.mem bp 32).ult (mw m.mem bp 36) = false := by
    cases hh : (mw m.mem bp 36 + mw m.mem bp 32).ult (mw m.mem bp 36)
    · rfl
    · exact absurd hh hc6d
  obtain ⟨m74, e74, t74⟩ := u73.notTaken hcY 0x12A mpc_at_126 (by decide)
    (by rw [v73a1, v73a2]; exact hc6d)
  have u74 := t74.self
  have q74 : ∀ r, reg m74 r = reg m73 r := t74.regs
  have sp74 : reg m74 sp = G := by rw [q74]; exact sp73
  have s074 : reg m74 s0 = out := by rw [q74]; exact s073
  have k74 : ∀ r, r ∉ parseClob → reg m74 r = reg m r := fun r hr => by rw [q74]; exact k73 r hr
  have pre74 : Steps m m74 := pre73.trans (.single e74)
  have F74 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 9 → reg m74 r = reg m56 r :=
    fun r h0 h1 h2 h3 h4 h5 h9 => by
      rw [q74, q73 r h1, q72 r h2, q71 r h9, q70, base69 r h0 h1 h3 h4 h5]
  obtain ⟨m75, e75, t75⟩ := u74.alu hcY mpc_at_12a (off' := 0x12C) (by decide)
  have u75 := t75.self
  have q75 : ∀ r, r ≠ a3 → reg m75 r = reg m74 r := fun r h => by rw [t75.regs]; exact updz u74.zero h
  have sp75 : reg m75 sp = G := by rw [q75 sp (by decide)]; exact sp74
  have s075 : reg m75 s0 = out := by rw [q75 s0 (by decide)]; exact s074
  have k75 : ∀ r, r ∉ parseClob → reg m75 r = reg m r := fun r hr => by
    rw [q75 r (clob_ne hr (by decide))]; exact k74 r hr
  have pre75 : Steps m m75 := pre74.trans (.single e75)
  have v75a3 : reg m75 a3 = 0x10000 + mw m.mem bp 12 := by
    rw [t75.regs]; simp +decide only [upd, ite_true, ite_false]; rw [q74, q73 a3 (by decide), q72 a3 (by decide), q71 a3 (by decide), q70, q69 a3 (by decide), q68, q67 a3 (by decide), q66, q65 a3 (by decide), q64 a3 (by decide), q63 a3 (by decide), q62, v61a3, F74 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), l56_22]; rfl
  have F75 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 9 → reg m75 r = reg m56 r :=
    fun r h0 h1 h2 h3 h4 h5 h9 => by rw [q75 r h3]; exact F74 r h0 h1 h2 h3 h4 h5 h9
  have v7518 : reg m75 18 = mw m.mem bp 16 := by rw [F75 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l56_18
  by_cases hc7a : (mw m.mem bp 16).ult (0x10000 + mw m.mem bp 12) = true
  · obtain ⟨m76, e76, t76⟩ := u75.taken hcY 0x166 mpc_at_12c (by decide)
      (by rw [v7518, v75a3]; exact hc7a)
    exact err166 m76 (reg m75) (pre75.trans (.single e76)) t76 sp75 s075 k75
      (by unfold parseErr; rw [hm, hv, hz, hpo1, hpo2, hpo3, hpo4, hc7, hc6a, hc6b, hc6c, hc6d, hc7a]; rfl)
  replace hc7a : (mw m.mem bp 16).ult (0x10000 + mw m.mem bp 12) = false := by
    cases hh : (mw m.mem bp 16).ult (0x10000 + mw m.mem bp 12)
    · rfl
    · exact absurd hh hc7a
  obtain ⟨m76, e76, t76⟩ := u75.notTaken hcY 0x130 mpc_at_12c (by decide)
    (by rw [v7518, v75a3]; exact hc7a)
  have u76 := t76.self
  have q76 : ∀ r, reg m76 r = reg m75 r := t76.regs
  have sp76 : reg m76 sp = G := by rw [q76]; exact sp75
  have s076 : reg m76 s0 = out := by rw [q76]; exact s075
  have k76 : ∀ r, r ∉ parseClob → reg m76 r = reg m r := fun r hr => by rw [q76]; exact k75 r hr
  have pre76 : Steps m m76 := pre75.trans (.single e76)
  have v7620 : reg m76 20 = mw m.mem bp 24 := by
    rw [q76, F75 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l56_20
  have v76a4 : reg m76 a4 = mw m.mem bp 20 + mw m.mem bp 16 := by
    rw [q76, q75 a4 (by decide), q74, q73 a4 (by decide), q72 a4 (by decide), q71 a4 (by decide), q70, q69 a4 (by decide), q68]
    exact v67a4
  by_cases hc7b : (mw m.mem bp 24).ult (mw m.mem bp 20 + mw m.mem bp 16) = true
  · obtain ⟨m77, e77, t77⟩ := u76.taken hcY 0x166 mpc_at_130 (by decide)
      (by rw [v7620, v76a4]; exact hc7b)
    exact err166 m77 (reg m76) (pre76.trans (.single e77)) t77 sp76 s076 k76
      (by unfold parseErr; rw [hm, hv, hz, hpo1, hpo2, hpo3, hpo4, hc7, hc6a, hc6b, hc6c, hc6d, hc7a, hc7b]; rfl)
  replace hc7b : (mw m.mem bp 24).ult (mw m.mem bp 20 + mw m.mem bp 16) = false := by
    cases hh : (mw m.mem bp 24).ult (mw m.mem bp 20 + mw m.mem bp 16)
    · rfl
    · exact absurd hh hc7b
  obtain ⟨m77, e77, t77⟩ := u76.notTaken hcY 0x134 mpc_at_130 (by decide)
    (by rw [v7620, v76a4]; exact hc7b)
  have u77 := t77.self
  have q77 : ∀ r, reg m77 r = reg m76 r := t77.regs
  have sp77 : reg m77 sp = G := by rw [q77]; exact sp76
  have s077 : reg m77 s0 = out := by rw [q77]; exact s076
  have k77 : ∀ r, r ∉ parseClob → reg m77 r = reg m r := fun r hr => by rw [q77]; exact k76 r hr
  have pre77 : Steps m m77 := pre76.trans (.single e77)
  have v779 : reg m77 9 = mw m.mem bp 32 := by
    rw [q77, q76, q75 9 (by decide), q74, q73 9 (by decide), q72 9 (by decide)]; exact v719
  have v77a5 : reg m77 a5 = mw m.mem bp 28 + mw m.mem bp 24 := by
    rw [q77, q76, q75 a5 (by decide), q74, q73 a5 (by decide), q72 a5 (by decide), q71 a5 (by decide), q70]
    exact v69a5
  by_cases hc7c : (mw m.mem bp 32).ult (mw m.mem bp 28 + mw m.mem bp 24) = true
  · obtain ⟨m78, e78, t78⟩ := u77.taken hcY 0x166 mpc_at_134 (by decide)
      (by rw [v779, v77a5]; exact hc7c)
    exact err166 m78 (reg m77) (pre77.trans (.single e78)) t78 sp77 s077 k77
      (by unfold parseErr; rw [hm, hv, hz, hpo1, hpo2, hpo3, hpo4, hc7, hc6a, hc6b, hc6c, hc6d, hc7a, hc7b, hc7c]; rfl)
  replace hc7c : (mw m.mem bp 32).ult (mw m.mem bp 28 + mw m.mem bp 24) = false := by
    cases hh : (mw m.mem bp 32).ult (mw m.mem bp 28 + mw m.mem bp 24)
    · rfl
    · exact absurd hh hc7c
  obtain ⟨m78, e78, t78⟩ := u77.notTaken hcY 0x138 mpc_at_134 (by decide)
    (by rw [v779, v77a5]; exact hc7c)
  have u78 := t78.self
  have q78 : ∀ r, reg m78 r = reg m77 r := t78.regs
  have sp78 : reg m78 sp = G := by rw [q78]; exact sp77
  have s078 : reg m78 s0 = out := by rw [q78]; exact s077
  have k78 : ∀ r, r ∉ parseClob → reg m78 r = reg m r := fun r hr => by rw [q78]; exact k77 r hr
  have pre78 : Steps m m78 := pre77.trans (.single e78)
  obtain ⟨m79, e79, t79⟩ := u78.lui hcY mpc_at_138 (off' := 0x13C) (by decide)
  have u79 := t79.self
  have q79 : ∀ r, r ≠ a3 → reg m79 r = reg m78 r := fun r h => by rw [t79.regs]; exact updz u78.zero h
  have sp79 : reg m79 sp = G := by rw [q79 sp (by decide)]; exact sp78
  have s079 : reg m79 s0 = out := by rw [q79 s0 (by decide)]; exact s078
  have k79 : ∀ r, r ∉ parseClob → reg m79 r = reg m r := fun r hr => by
    rw [q79 r (clob_ne hr (by decide))]; exact k78 r hr
  have pre79 : Steps m m79 := pre78.trans (.single e79)
  obtain ⟨m80, e80, t80⟩ := u79.aluImm hcY mpc_at_13c (off' := 0x13E) (by decide)
  have u80 := t80.self
  have q80 : ∀ r, r ≠ a0 → reg m80 r = reg m79 r := fun r h => by rw [t80.regs]; exact updz u79.zero h
  have sp80 : reg m80 sp = G := by rw [q80 sp (by decide)]; exact sp79
  have s080 : reg m80 s0 = out := by rw [q80 s0 (by decide)]; exact s079
  have k80 : ∀ r, r ∉ parseClob → reg m80 r = reg m r := fun r hr => by
    rw [q80 r (clob_ne hr (by decide))]; exact k79 r hr
  have pre80 : Steps m m80 := pre79.trans (.single e80)
  have v80a3 : reg m80 a3 = 0x1E0000 := by
    rw [q80 a3 (by decide), t79.regs]; simp +decide only [upd, ite_true, ite_false]
  have v80a1 : reg m80 a1 = mw m.mem bp 36 + mw m.mem bp 32 := by
    rw [q80 a1 (by decide), q79 a1 (by decide), q78, q77, q76, q75 a1 (by decide), q74]; exact v73a1
  have v80a0 : reg m80 a0 = 7 := by
    rw [t80.regs]; simp +decide only [upd, ite_true, ite_false]; rw [show reg m79 x0 = 0 from u79.zero]; rfl
  by_cases hc7d : (0x1E0000 : Word).ult (mw m.mem bp 36 + mw m.mem bp 32) = true
  · obtain ⟨m81, e81, t81⟩ := u80.taken hcY 0xD6 mpc_at_13e (by decide)
      (by rw [v80a3, v80a1]; exact hc7d)
    exact errD6 m81 My56 (reg m80) 7 (pre80.trans (.single e81)) t81 hcY sp80 s080
      (by rw [v80a0]; rfl) (by unfold parseErr; rw [hm, hv, hz, hpo1, hpo2, hpo3, hpo4, hc7, hc6a, hc6b, hc6c, hc6d, hc7a, hc7b, hc7c, hc7d]; rfl) O56 S56 k80
  replace hc7d : (0x1E0000 : Word).ult (mw m.mem bp 36 + mw m.mem bp 32) = false := by
    cases hh : (0x1E0000 : Word).ult (mw m.mem bp 36 + mw m.mem bp 32)
    · rfl
    · exact absurd hh hc7d
  have hpe : parseErr m.mem bp = none := by unfold parseErr; rw [hm, hv, hz, hpo1, hpo2, hpo3, hpo4, hc7, hc6a, hc6b, hc6c, hc6d, hc7a, hc7b, hc7c, hc7d]; rfl
  obtain ⟨m81, e81, t81⟩ := u80.notTaken hcY 0x142 mpc_at_13e (by decide)
    (by rw [v80a3, v80a1]; exact hc7d)
  have u81 := t81.self
  have q81 : ∀ r, reg m81 r = reg m80 r := t81.regs
  obtain ⟨m82, e82, t82⟩ := u81.aluImm hcY mpc_at_142 (off' := 0x144) (by decide)
  have u82 := t82.self
  have q82 : ∀ r, r ≠ a0 → reg m82 r = reg m81 r := fun r h => by rw [t82.regs]; exact updz u81.zero h
  obtain ⟨m83, e83, t83⟩ := u82.lui hcY mpc_at_144 (off' := 0x146) (by decide)
  have u83 := t83.self
  have q83 : ∀ r, r ≠ a1 → reg m83 r = reg m82 r := fun r h => by rw [t83.regs]; exact updz u82.zero h
  have F80 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 9 → reg m80 r = reg m56 r :=
    fun r h0 h1 h2 h3 h4 h5 h9 => by
      rw [q80 r h0, q79 r h3, q78, q77, q76]; exact F75 r h0 h1 h2 h3 h4 h5 h9
  have G83 : ∀ r, r ≠ a0 → r ≠ a1 → reg m83 r = reg m80 r := fun r h0 h1 => by rw [q83 r h1, q82 r h0, q81]
  have v83a0 : reg m83 a0 = 0 := by
    rw [q83 a0 (by decide), t82.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [show reg m81 x0 = 0 from u81.zero]; rfl
  have v83a1 : reg m83 a1 = 0x10000 := by rw [t83.regs]; simp +decide only [upd, ite_true, ite_false]
  have sp83 : reg m83 sp = G := by rw [G83 sp (by decide) (by decide)]; exact sp80
  have s083 : reg m83 s0 = out := by rw [G83 s0 (by decide) (by decide)]; exact s080
  have k83 : ∀ r, r ∉ parseClob → reg m83 r = reg m r := fun r hr => by
    rw [G83 r (clob_ne hr (by decide)) (clob_ne hr (by decide))]; exact k80 r hr
  have v83_22 : reg m83 22 = mw m.mem bp 12 := by
    rw [G83 22 (by decide) (by decide), F80 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l56_22
  have v83_18 : reg m83 18 = mw m.mem bp 16 := by
    rw [G83 18 (by decide) (by decide), F80 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l56_18
  have v83_19 : reg m83 19 = mw m.mem bp 20 := by
    rw [G83 19 (by decide) (by decide), F80 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l56_19
  have v83_20 : reg m83 20 = mw m.mem bp 24 := by
    rw [G83 20 (by decide) (by decide), F80 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l56_20
  have v83_21 : reg m83 21 = mw m.mem bp 28 := by
    rw [G83 21 (by decide) (by decide), F80 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l56_21
  have v83_9 : reg m83 9 = mw m.mem bp 32 := by
    rw [G83 9 (by decide) (by decide), q80 9 (by decide), q79 9 (by decide), q78]; exact v779
  have v83a2 : reg m83 a2 = mw m.mem bp 36 := by
    rw [G83 a2 (by decide) (by decide), q80 a2 (by decide), q79 a2 (by decide), q78, q77, q76, q75 a2 (by decide), q74]
    exact v73a2
  have pre83 : Steps m m83 := pre80.trans (.cons e81 (.cons e82 (.single e83)))
  have outLow : ∀ c, c + 4 ≤ 36 → (out + BitVec.ofNat 32 c).toNat + 4 ≤ 0x40000000 := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨m84, e84, t84⟩ := u83.sw hcY mpc_at_146 (off' := 0x148) (by decide)
    (by rw [s083]; exact aligned_add hout (k := 0x4) (by decide))
  rw [s083, v83a1] at t84
  have hc84 := hcY.store32 (a := out + 0x4) (v := 0x10000) (lowSep (outLow 0x4 (by omega)) (by decide) (by decide))
  obtain ⟨m85, e85, t85⟩ := t84.sw hc84 mpc_at_148 (off' := 0x14C) (by decide)
    (by rw [s083]; exact aligned_add hout (k := 0x8) (by decide))
  rw [s083, v83_22] at t85
  have hc85 := hc84.store32 (a := out + 0x8) (v := mw m.mem bp 12) (lowSep (outLow 0x8 (by omega)) (by decide) (by decide))
  obtain ⟨m86, e86, t86⟩ := t85.sw hc85 mpc_at_14c (off' := 0x150) (by decide)
    (by rw [s083]; exact aligned_add hout (k := 0xC) (by decide))
  rw [s083, v83_18] at t86
  have hc86 := hc85.store32 (a := out + 0xC) (v := mw m.mem bp 16) (lowSep (outLow 0xC (by omega)) (by decide) (by decide))
  obtain ⟨m87, e87, t87⟩ := t86.sw hc86 mpc_at_150 (off' := 0x154) (by decide)
    (by rw [s083]; exact aligned_add hout (k := 0x10) (by decide))
  rw [s083, v83_19] at t87
  have hc87 := hc86.store32 (a := out + 0x10) (v := mw m.mem bp 20) (lowSep (outLow 0x10 (by omega)) (by decide) (by decide))
  obtain ⟨m88, e88, t88⟩ := t87.sw hc87 mpc_at_154 (off' := 0x158) (by decide)
    (by rw [s083]; exact aligned_add hout (k := 0x14) (by decide))
  rw [s083, v83_20] at t88
  have hc88 := hc87.store32 (a := out + 0x14) (v := mw m.mem bp 24) (lowSep (outLow 0x14 (by omega)) (by decide) (by decide))
  obtain ⟨m89, e89, t89⟩ := t88.sw hc88 mpc_at_158 (off' := 0x15C) (by decide)
    (by rw [s083]; exact aligned_add hout (k := 0x18) (by decide))
  rw [s083, v83_21] at t89
  have hc89 := hc88.store32 (a := out + 0x18) (v := mw m.mem bp 28) (lowSep (outLow 0x18 (by omega)) (by decide) (by decide))
  obtain ⟨m90, e90, t90⟩ := t89.sw hc89 mpc_at_15c (off' := 0x15E) (by decide)
    (by rw [s083]; exact aligned_add hout (k := 0x1C) (by decide))
  rw [s083, v83_9] at t90
  have hc90 := hc89.store32 (a := out + 0x1C) (v := mw m.mem bp 32) (lowSep (outLow 0x1C (by omega)) (by decide) (by decide))
  obtain ⟨m91, e91, t91⟩ := t90.sw hc90 mpc_at_15e (off' := 0x160) (by decide)
    (by rw [s083]; exact aligned_add hout (k := 0x20) (by decide))
  rw [s083, v83a2] at t91
  have hc91 := hc90.store32 (a := out + 0x20) (v := mw m.mem bp 36) (lowSep (outLow 0x20 (by omega)) (by decide) (by decide))
  obtain ⟨m92, e92, t92⟩ := t91.jump hc91 mpc_at_160 (off' := 0xDC) (by decide) (by rw [t91.pc]; decide)
  refine exitDC m92 _ (reg m83) 0 (pre83.trans (.cons e84 (.cons e85 (.cons e86 (.cons e87 (.cons e88 (.cons e89 (.cons e90 (.cons e91 (.single e92)))))))))) t92 hc91
    sp83 s083 (by rw [v83a0]; rfl) (fun k h1 h2 => ?_) k83 (fun x hx => ?_)
  · rw [Ly.g_ofs k, memStore32_get_sep (a := out + 0x20) ((hOS.sub (c := 32) (l := 4) (by omega)).subR (c := 80 + k) (l := 1) (by omega)), memStore32_get_sep (a := out + 0x1C) ((hOS.sub (c := 28) (l := 4) (by omega)).subR (c := 80 + k) (l := 1) (by omega)), memStore32_get_sep (a := out + 0x18) ((hOS.sub (c := 24) (l := 4) (by omega)).subR (c := 80 + k) (l := 1) (by omega)), memStore32_get_sep (a := out + 0x14) ((hOS.sub (c := 20) (l := 4) (by omega)).subR (c := 80 + k) (l := 1) (by omega)), memStore32_get_sep (a := out + 0x10) ((hOS.sub (c := 16) (l := 4) (by omega)).subR (c := 80 + k) (l := 1) (by omega)), memStore32_get_sep (a := out + 0xC) ((hOS.sub (c := 12) (l := 4) (by omega)).subR (c := 80 + k) (l := 1) (by omega)), memStore32_get_sep (a := out + 0x8) ((hOS.sub (c := 8) (l := 4) (by omega)).subR (c := 80 + k) (l := 1) (by omega)), memStore32_get_sep (a := out + 0x4) ((hOS.sub (c := 4) (l := 4) (by omega)).subR (c := 80 + k) (l := 1) (by omega)), ← Ly.g_ofs k]
    exact S56 k h1 h2
  · unfold parseMem; rw [hpe]
    exact memStore8_congr (memStore32_congr (memStore32_congr (memStore32_congr (memStore32_congr (memStore32_congr (memStore32_congr (memStore32_congr (memStore32_congr (O56 x hx)))))))))

end C3.RV32.Cur
