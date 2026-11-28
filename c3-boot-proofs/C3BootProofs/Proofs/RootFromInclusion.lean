import C3BootProofs.Proofs.MerkleNode
import C3BootProofs.Proofs.Pair64
import C3BootProofs.Proofs.MerkleSpecLemmas

/-!
# `c3_verify::merkle::root_from_inclusion`, as compiled

The RFC 9162 section 2.1.3.2 algorithm: it checks the index against the
size and the proof's length, then for each 32-byte hash of the proof
combines it with the running hash through `node_hash`, shifting the 64-bit
index and size it keeps in register pairs. `rootFromInclusion_correct` says
it returns what `rootFromInclusion` specifies.
-/

namespace C3.RV32

open C3.Image

section

set_option maxRecDepth 20000

theorem rf_at_0 : fetchRel rootFromInclusionCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFA0, 2) := by decide
theorem rf_at_2 : fetchRel rootFromInclusionCode 0x2 = some (.store .sw sp ra 0x5C, 2) := by decide
theorem rf_at_4 : fetchRel rootFromInclusionCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x58, 2) := by decide
theorem rf_at_6 : fetchRel rootFromInclusionCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x54, 2) := by decide
theorem rf_at_8 : fetchRel rootFromInclusionCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x50, 2) := by decide
theorem rf_at_a : fetchRel rootFromInclusionCode 0xA = some (.store .sw sp (19 : Fin 32) 0x4C, 2) := by decide
theorem rf_at_c : fetchRel rootFromInclusionCode 0xC = some (.store .sw sp (20 : Fin 32) 0x48, 2) := by decide
theorem rf_at_e : fetchRel rootFromInclusionCode 0xE = some (.store .sw sp (21 : Fin 32) 0x44, 2) := by decide
theorem rf_at_10 : fetchRel rootFromInclusionCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x40, 2) := by decide
theorem rf_at_12 : fetchRel rootFromInclusionCode 0x12 = some (.alu .add (20 : Fin 32) x0 (17 : Fin 32), 2) := by decide
theorem rf_at_14 : fetchRel rootFromInclusionCode 0x14 = some (.alu .add (19 : Fin 32) x0 a6, 2) := by decide
theorem rf_at_16 : fetchRel rootFromInclusionCode 0x16 = some (.alu .add (8 : Fin 32) x0 a2, 2) := by decide
theorem rf_at_18 : fetchRel rootFromInclusionCode 0x18 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem rf_at_1a : fetchRel rootFromInclusionCode 0x1A = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem rf_at_1c : fetchRel rootFromInclusionCode 0x1C = some (.branch .beq a2 a4 0xC, 4) := by decide
theorem rf_at_20 : fetchRel rootFromInclusionCode 0x20 = some (.alu .sltu a0 (8 : Fin 32) a4, 4) := by decide
theorem rf_at_24 : fetchRel rootFromInclusionCode 0x24 = some (.branch .bne a0 x0 0xA, 2) := by decide
theorem rf_at_26 : fetchRel rootFromInclusionCode 0x26 = some (.jal x0 0xDA, 2) := by decide
theorem rf_at_28 : fetchRel rootFromInclusionCode 0x28 = some (.alu .sltu a0 (9 : Fin 32) a3, 4) := by decide
theorem rf_at_2c : fetchRel rootFromInclusionCode 0x2C = some (.branch .beq a0 x0 0xD4, 2) := by decide
theorem rf_at_2e : fetchRel rootFromInclusionCode 0x2E = some (.aluImm .srl a0 (20 : Fin 32) 0x5, 4) := by decide
theorem rf_at_32 : fetchRel rootFromInclusionCode 0x32 = some (.aluImm .add a1 x0 0x40, 4) := by decide
theorem rf_at_36 : fetchRel rootFromInclusionCode 0x36 = some (.branch .bltu a1 a0 0xCA, 4) := by decide
theorem rf_at_3a : fetchRel rootFromInclusionCode 0x3A = some (.aluImm .and a0 (20 : Fin 32) 0x1F, 4) := by decide
theorem rf_at_3e : fetchRel rootFromInclusionCode 0x3E = some (.branch .bne a0 x0 0xC2, 2) := by decide
theorem rf_at_40 : fetchRel rootFromInclusionCode 0x40 = some (.aluImm .sltu a0 a3 0x1, 4) := by decide
theorem rf_at_44 : fetchRel rootFromInclusionCode 0x44 = some (.alu .sub (21 : Fin 32) a4 a0, 4) := by decide
theorem rf_at_48 : fetchRel rootFromInclusionCode 0x48 = some (.aluImm .add (22 : Fin 32) a3 0xFFFFFFFF, 4) := by decide
theorem rf_at_4c : fetchRel rootFromInclusionCode 0x4C = some (.alu .add a0 x0 sp, 2) := by decide
theorem rf_at_4e : fetchRel rootFromInclusionCode 0x4E = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem rf_at_52 : fetchRel rootFromInclusionCode 0x52 = some (.alu .add a1 x0 a5, 2) := by decide
theorem rf_at_54 : fetchRel rootFromInclusionCode 0x54 = some (.auipc ra 0x9000, 4) := by decide
theorem rf_at_58 : fetchRel rootFromInclusionCode 0x58 = some (.jalr ra ra 0x57C, 4) := by decide
theorem rf_at_5c : fetchRel rootFromInclusionCode 0x5C = some (.alu .add (20 : Fin 32) (20 : Fin 32) (19 : Fin 32), 2) := by decide
theorem rf_at_5e : fetchRel rootFromInclusionCode 0x5E = some (.alu .or a0 (22 : Fin 32) (21 : Fin 32), 4) := by decide
theorem rf_at_62 : fetchRel rootFromInclusionCode 0x62 = some (.branch .beq (19 : Fin 32) (20 : Fin 32) 0x9C, 4) := by decide
theorem rf_at_66 : fetchRel rootFromInclusionCode 0x66 = some (.branch .beq a0 x0 0x9A, 2) := by decide
theorem rf_at_68 : fetchRel rootFromInclusionCode 0x68 = some (.aluImm .and a0 (9 : Fin 32) 0x1, 4) := by decide
theorem rf_at_6c : fetchRel rootFromInclusionCode 0x6C = some (.branch .bne a0 x0 0x4C, 2) := by decide
theorem rf_at_6e : fetchRel rootFromInclusionCode 0x6E = some (.alu .xor a0 (9 : Fin 32) (22 : Fin 32), 4) := by decide
theorem rf_at_72 : fetchRel rootFromInclusionCode 0x72 = some (.alu .xor a1 (8 : Fin 32) (21 : Fin 32), 4) := by decide
theorem rf_at_76 : fetchRel rootFromInclusionCode 0x76 = some (.alu .or a0 a0 a1, 2) := by decide
theorem rf_at_78 : fetchRel rootFromInclusionCode 0x78 = some (.branch .beq a0 x0 0x40, 2) := by decide
theorem rf_at_7a : fetchRel rootFromInclusionCode 0x7A = some (.aluImm .add a0 sp 0x20, 2) := by decide
theorem rf_at_7c : fetchRel rootFromInclusionCode 0x7C = some (.alu .add a1 x0 sp, 2) := by decide
theorem rf_at_7e : fetchRel rootFromInclusionCode 0x7E = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem rf_at_80 : fetchRel rootFromInclusionCode 0x80 = some (.auipc ra 0x0, 4) := by decide
theorem rf_at_84 : fetchRel rootFromInclusionCode 0x84 = some (.jalr ra ra 0xB8, 4) := by decide
theorem rf_at_88 : fetchRel rootFromInclusionCode 0x88 = some (.alu .add a0 x0 sp, 2) := by decide
theorem rf_at_8a : fetchRel rootFromInclusionCode 0x8A = some (.aluImm .add a1 sp 0x20, 2) := by decide
theorem rf_at_8c : fetchRel rootFromInclusionCode 0x8C = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem rf_at_90 : fetchRel rootFromInclusionCode 0x90 = some (.auipc ra 0x9000, 4) := by decide
theorem rf_at_94 : fetchRel rootFromInclusionCode 0x94 = some (.jalr ra ra 0x540, 4) := by decide
theorem rf_at_98 : fetchRel rootFromInclusionCode 0x98 = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x20, 4) := by decide
theorem rf_at_9c : fetchRel rootFromInclusionCode 0x9C = some (.aluImm .srl (9 : Fin 32) (9 : Fin 32) 0x1, 2) := by decide
theorem rf_at_9e : fetchRel rootFromInclusionCode 0x9E = some (.aluImm .sll a0 (8 : Fin 32) 0x1F, 4) := by decide
theorem rf_at_a2 : fetchRel rootFromInclusionCode 0xA2 = some (.alu .or (9 : Fin 32) (9 : Fin 32) a0, 2) := by decide
theorem rf_at_a4 : fetchRel rootFromInclusionCode 0xA4 = some (.aluImm .srl (8 : Fin 32) (8 : Fin 32) 0x1, 2) := by decide
theorem rf_at_a6 : fetchRel rootFromInclusionCode 0xA6 = some (.aluImm .srl a0 (22 : Fin 32) 0x1, 4) := by decide
theorem rf_at_aa : fetchRel rootFromInclusionCode 0xAA = some (.aluImm .sll a1 (21 : Fin 32) 0x1F, 4) := by decide
theorem rf_at_ae : fetchRel rootFromInclusionCode 0xAE = some (.alu .or (22 : Fin 32) a0 a1, 4) := by decide
theorem rf_at_b2 : fetchRel rootFromInclusionCode 0xB2 = some (.aluImm .srl (21 : Fin 32) (21 : Fin 32) 0x1, 4) := by decide
theorem rf_at_b6 : fetchRel rootFromInclusionCode 0xB6 = some (.jal x0 0xFFFFFFA8, 2) := by decide
theorem rf_at_b8 : fetchRel rootFromInclusionCode 0xB8 = some (.aluImm .add a0 sp 0x20, 2) := by decide
theorem rf_at_ba : fetchRel rootFromInclusionCode 0xBA = some (.alu .add a2 x0 sp, 2) := by decide
theorem rf_at_bc : fetchRel rootFromInclusionCode 0xBC = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem rf_at_be : fetchRel rootFromInclusionCode 0xBE = some (.auipc ra 0x0, 4) := by decide
theorem rf_at_c2 : fetchRel rootFromInclusionCode 0xC2 = some (.jalr ra ra 0x7A, 4) := by decide
theorem rf_at_c6 : fetchRel rootFromInclusionCode 0xC6 = some (.alu .add a0 x0 sp, 2) := by decide
theorem rf_at_c8 : fetchRel rootFromInclusionCode 0xC8 = some (.aluImm .add a1 sp 0x20, 2) := by decide
theorem rf_at_ca : fetchRel rootFromInclusionCode 0xCA = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem rf_at_ce : fetchRel rootFromInclusionCode 0xCE = some (.auipc ra 0x9000, 4) := by decide
theorem rf_at_d2 : fetchRel rootFromInclusionCode 0xD2 = some (.jalr ra ra 0x502, 4) := by decide
theorem rf_at_d6 : fetchRel rootFromInclusionCode 0xD6 = some (.alu .or a0 (9 : Fin 32) (8 : Fin 32), 4) := by decide
theorem rf_at_da : fetchRel rootFromInclusionCode 0xDA = some (.branch .beq a0 x0 0xFFFFFFBE, 2) := by decide
theorem rf_at_dc : fetchRel rootFromInclusionCode 0xDC = some (.aluImm .and a0 (9 : Fin 32) 0x1, 4) := by decide
theorem rf_at_e0 : fetchRel rootFromInclusionCode 0xE0 = some (.branch .bne a0 x0 0xFFFFFFB8, 2) := by decide
theorem rf_at_e2 : fetchRel rootFromInclusionCode 0xE2 = some (.aluImm .srl (9 : Fin 32) (9 : Fin 32) 0x1, 2) := by decide
theorem rf_at_e4 : fetchRel rootFromInclusionCode 0xE4 = some (.aluImm .sll a0 (8 : Fin 32) 0x1F, 4) := by decide
theorem rf_at_e8 : fetchRel rootFromInclusionCode 0xE8 = some (.aluImm .srl (8 : Fin 32) (8 : Fin 32) 0x1, 2) := by decide
theorem rf_at_ea : fetchRel rootFromInclusionCode 0xEA = some (.alu .or (9 : Fin 32) (9 : Fin 32) a0, 2) := by decide
theorem rf_at_ec : fetchRel rootFromInclusionCode 0xEC = some (.aluImm .srl a0 (22 : Fin 32) 0x1, 4) := by decide
theorem rf_at_f0 : fetchRel rootFromInclusionCode 0xF0 = some (.aluImm .sll a1 (21 : Fin 32) 0x1F, 4) := by decide
theorem rf_at_f4 : fetchRel rootFromInclusionCode 0xF4 = some (.alu .or (22 : Fin 32) a0 a1, 4) := by decide
theorem rf_at_f8 : fetchRel rootFromInclusionCode 0xF8 = some (.aluImm .srl (21 : Fin 32) (21 : Fin 32) 0x1, 4) := by decide
theorem rf_at_fc : fetchRel rootFromInclusionCode 0xFC = some (.jal x0 0xFFFFFFDA, 2) := by decide
theorem rf_at_fe : fetchRel rootFromInclusionCode 0xFE = some (.branch .beq a0 x0 0x22, 2) := by decide
theorem rf_at_100 : fetchRel rootFromInclusionCode 0x100 = some (.aluImm .add a0 x0 0x1B, 2) := by decide
theorem rf_at_102 : fetchRel rootFromInclusionCode 0x102 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem rf_at_104 : fetchRel rootFromInclusionCode 0x104 = some (.store .sb (18 : Fin 32) a1 0x0, 4) := by decide
theorem rf_at_108 : fetchRel rootFromInclusionCode 0x108 = some (.store .sb (18 : Fin 32) a0 0x1, 4) := by decide
theorem rf_at_10c : fetchRel rootFromInclusionCode 0x10C = some (.load .lw ra sp 0x5C, 2) := by decide
theorem rf_at_10e : fetchRel rootFromInclusionCode 0x10E = some (.load .lw (8 : Fin 32) sp 0x58, 2) := by decide
theorem rf_at_110 : fetchRel rootFromInclusionCode 0x110 = some (.load .lw (9 : Fin 32) sp 0x54, 2) := by decide
theorem rf_at_112 : fetchRel rootFromInclusionCode 0x112 = some (.load .lw (18 : Fin 32) sp 0x50, 2) := by decide
theorem rf_at_114 : fetchRel rootFromInclusionCode 0x114 = some (.load .lw (19 : Fin 32) sp 0x4C, 2) := by decide
theorem rf_at_116 : fetchRel rootFromInclusionCode 0x116 = some (.load .lw (20 : Fin 32) sp 0x48, 2) := by decide
theorem rf_at_118 : fetchRel rootFromInclusionCode 0x118 = some (.load .lw (21 : Fin 32) sp 0x44, 2) := by decide
theorem rf_at_11a : fetchRel rootFromInclusionCode 0x11A = some (.load .lw (22 : Fin 32) sp 0x40, 2) := by decide
theorem rf_at_11c : fetchRel rootFromInclusionCode 0x11C = some (.aluImm .add sp sp 0x60, 2) := by decide
theorem rf_at_11e : fetchRel rootFromInclusionCode 0x11E = some (.jalr x0 ra 0x0, 2) := by decide
theorem rf_at_120 : fetchRel rootFromInclusionCode 0x120 = some (.aluImm .add a0 (18 : Fin 32) 0x1, 4) := by decide
theorem rf_at_124 : fetchRel rootFromInclusionCode 0x124 = some (.alu .add a1 x0 sp, 2) := by decide
theorem rf_at_126 : fetchRel rootFromInclusionCode 0x126 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem rf_at_12a : fetchRel rootFromInclusionCode 0x12A = some (.auipc ra 0x9000, 4) := by decide
theorem rf_at_12e : fetchRel rootFromInclusionCode 0x12E = some (.jalr ra ra 0x4A6, 4) := by decide
theorem rf_at_132 : fetchRel rootFromInclusionCode 0x132 = some (.store .sb (18 : Fin 32) x0 0x0, 4) := by decide
theorem rf_at_136 : fetchRel rootFromInclusionCode 0x136 = some (.jal x0 0xFFFFFFD6, 2) := by decide

def rfCopy : List BInstr := [.alu .add a0 x0 sp, .aluImm .add a1 sp 0x20, .aluImm .add a2 x0 0x20]

/-- The 64-bit shifts after a step, from 0x9C. -/
def rfShA : List BInstr :=
  [.aluImm .srl (9 : Fin 32) (9 : Fin 32) 0x1, .aluImm .sll a0 (8 : Fin 32) 0x1F, .alu .or (9 : Fin 32) (9 : Fin 32) a0,
    .aluImm .srl (8 : Fin 32) (8 : Fin 32) 0x1, .aluImm .srl a0 (22 : Fin 32) 0x1, .aluImm .sll a1 (21 : Fin 32) 0x1F,
    .alu .or (22 : Fin 32) a0 a1, .aluImm .srl (21 : Fin 32) (21 : Fin 32) 0x1]

/-- The 64-bit shifts in the loop that skips even `f`, from 0xE2. -/
def rfShB : List BInstr :=
  [.aluImm .srl (9 : Fin 32) (9 : Fin 32) 0x1, .aluImm .sll a0 (8 : Fin 32) 0x1F, .aluImm .srl (8 : Fin 32) (8 : Fin 32) 0x1,
    .alu .or (9 : Fin 32) (9 : Fin 32) a0, .aluImm .srl a0 (22 : Fin 32) 0x1, .aluImm .sll a1 (21 : Fin 32) 0x1F,
    .alu .or (22 : Fin 32) a0 a1, .aluImm .srl (21 : Fin 32) (21 : Fin 32) 0x1]

theorem rfCopyA_end : blockEnd rootFromInclusionCode 0x88 rfCopy = some 0x90 := by decide
theorem rfCopyB_end : blockEnd rootFromInclusionCode 0xC6 rfCopy = some 0xCE := by decide
theorem rfShA_end : blockEnd rootFromInclusionCode 0x9C rfShA = some 0xB6 := by decide
theorem rfShB_end : blockEnd rootFromInclusionCode 0xE2 rfShB = some 0xFC := by decide

end

/-- Where `root_from_inclusion` runs: its code and `node_hash`'s and
`memcpy`'s, the prefix byte; the leaf hash at `L`, the `n` proof bytes at
`Pp`, the 33-byte result at `out`, and 0x2F0 bytes of stack below `sp0`,
all below 0x40000000; the leaf, the proof, the result, the prefix byte, the
initial hash value, and the round constants each apart from the stack. -/
structure RootEnv (M : Word → BitVec 8) (out L Pp sp0 : Word) (n : Nat) : Prop where
  cRF : CodeIn M (BitVec.ofNat 32 rootFromInclusionAddress) rootFromInclusionCode
  cN : CodeIn M (BitVec.ofNat 32 merkleNodeHashAddress) merkleNodeHashCode
  cPre : CodeIn M (BitVec.ofNat 32 merklePrefixAddress) merklePrefixData
  cX : CodeIn M (BitVec.ofNat 32 sha256PartsAddress) sha256PartsCode
  cIV : CodeIn M (BitVec.ofNat 32 shaIVAddress) shaIVData
  cU : CodeIn M (BitVec.ofNat 32 shaUpdateAddress) shaUpdateCode
  cUBlk : CodeIn M (BitVec.ofNat 32 shaUpdateBlocksAddress) shaUpdateBlocksCode
  cF : CodeIn M (BitVec.ofNat 32 shaFinalizeAddress) shaFinalizeCode
  cZ : CodeIn M (BitVec.ofNat 32 shaZero32Address) shaZero32Code
  cFBlk : CodeIn M (BitVec.ofNat 32 shaFinBlockAddress) shaFinBlockCode
  cMs : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  cMS : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cMB : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  cC : CodeIn M (BitVec.ofNat 32 sha256CompressAddress) sha256CompressCode
  cI : CodeIn M (BitVec.ofNat 32 sha256CompressAddress + 0x25A) rangeFromIndexCode
  cK : CodeIn M (BitVec.ofNat 32 shaKAddress) shaKData
  hsp : sp0.toNat % 16 = 0
  hspl : 0x2F0 ≤ sp0.toNat
  hspw : sp0.toNat ≤ 0x40000000
  hOw : out.toNat + 33 ≤ 0x40000000
  hLw : L.toNat + 32 ≤ 0x40000000
  hPw : Pp.toNat + n ≤ 0x40000000
  sOF : Sep out 33 (sp0 + 0xFFFFFD10) 0x2F0
  sLF : Sep L 32 (sp0 + 0xFFFFFD10) 0x2F0
  sPF : Sep Pp n (sp0 + 0xFFFFFD10) 0x2F0
  sXF : Sep (BitVec.ofNat 32 merklePrefixAddress) 1 (sp0 + 0xFFFFFD10) 0x2F0
  sKF : Sep (BitVec.ofNat 32 shaKAddress) 256 (sp0 + 0xFFFFFD10) 0x2F0
  sIF : Sep (BitVec.ofNat 32 shaIVAddress) 32 (sp0 + 0xFFFFFD10) 0x2F0

/-- What every part of `root_from_inclusion`'s proof shares: the
environment, the 0x2F0-byte stack area at `R`, the frame at `G` at its top,
and `M1`, the memory after the prologue, which differs from `M0` only in
that area. -/
structure RFCtx (M0 M1 : Word → BitVec 8) (out L Pp sp0 R G : Word) (n : Nat) : Prop where
  E : RootEnv M0 out L Pp sp0 n
  hR : sp0 + 0xFFFFFD10 = R
  hGR : G = R + BitVec.ofNat 32 0x290
  M1R : ∀ x, Sep R 0x2F0 x 1 → M1 x = M0 x

namespace RFCtx

variable {M0 M1 : Word → BitVec 8} {out L Pp sp0 R G : Word} {n : Nat}

theorem hRn (C : RFCtx M0 M1 out L Pp sp0 R G n) : R.toNat = sp0.toNat - 0x2F0 := by
  have := C.E.hspl
  rw [← C.hR, BitVec.toNat_add, show (0xFFFFFD10 : Word).toNat = 2 ^ 32 - 0x2F0 from rfl]; omega

theorem hRc (C : RFCtx M0 M1 out L Pp sp0 R G n) {c : Nat} (hc : c ≤ 0x2F0) :
    (R + BitVec.ofNat 32 c).toNat = R.toNat + c := by
  have := C.hRn; have := C.E.hspw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem Gc (C : RFCtx M0 M1 out L Pp sp0 R G n) (c : Nat) : G + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x290 + c) := by
  rw [C.hGR, add_ofNat_assoc]

theorem hGn (C : RFCtx M0 M1 out L Pp sp0 R G n) : G.toNat = sp0.toNat - 0x60 := by
  have := C.E.hspl
  rw [C.hGR, C.hRc (by omega), C.hRn]; omega

theorem hGa (C : RFCtx M0 M1 out L Pp sp0 R G n) : G.toNat % 16 = 0 := by
  rw [C.hGn]; have := C.E.hsp; have := C.E.hspl; omega

theorem Rd (C : RFCtx M0 M1 out L Pp sp0 R G n) {c l : Nat} (h : c + l ≤ 0x2F0) {b : Word} {k : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbk : b.toNat + k ≤ 2 ^ 32) : Sep (R + BitVec.ofNat 32 c) l b k := by
  have := C.E.hspw; have := C.hRn
  exact data_code (by rw [C.hRc (by omega)]; omega) hb hbk

theorem agree (C : RFCtx M0 M1 out L Pp sp0 R G n) {My : Word → BitVec 8}
    (h : ∀ x, Sep R 0x2D0 x 1 → My x = M1 x) : ∀ x, Sep R 0x2F0 x 1 → My x = M0 x := fun x hx => by
  rw [h x (hx.sub (c := 0) (l := 0x2D0) (by omega) |> fun h' => by rwa [add_ofNat_zero] at h'), C.M1R x hx]

theorem codeX (C : RFCtx M0 M1 out L Pp sp0 R G n) {My : Word → BitVec 8}
    (h : ∀ x, Sep R 0x2D0 x 1 → My x = M1 x) {b : Word} {code : List Nat} (hc : CodeIn M0 b code)
    (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + code.length ≤ 2 ^ 32) : CodeIn My b code := fun i hi => by
  have := C.E.hspw; have := C.hRn
  rw [C.agree h _ ((data_code (a := R) (n := 0x2F0) (by omega) hb hbl).subR (c := i) (l := 1) (by omega))]
  exact hc i hi

/-- Data apart from the stack area keeps its value. -/
theorem dat (C : RFCtx M0 M1 out L Pp sp0 R G n) {My : Word → BitVec 8}
    (h : ∀ x, Sep R 0x2D0 x 1 → My x = M1 x) {b : Word} {k : Nat} (hs : Sep b k R 0x2F0) :
    memBytes My b k = memBytes M0 b k :=
  memBytes_congr fun i hi => C.agree h _ (hs.sub (c := i) (l := 1) (by omega)).symm

end RFCtx

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- One step's hash, at either call of `node_hash` (offset `off`): it hashes
the 32 bytes at `X` and then at `Y` into the frame at `G + 0x20` and copies
the result to the running hash at `G`. Everything outside the stack area's
low 0x2D0 bytes keeps the prologue's memory. -/
theorem rf_hash {M0 M1 Mx : Word → BitVec 8} {out L Pp sp0 R G X Y o o2 : Word} {n off : Nat}
    (C : RFCtx M0 M1 out L Pp sp0 R G n) (nn : Machine)
    (s : St Mx (BitVec.ofNat 32 rootFromInclusionAddress) nn off (reg nn))
    (inv : ∀ x, Sep R 0x2D0 x 1 → Mx x = M1 x)
    (h1 : fetchRel rootFromInclusionCode off = some (.auipc ra 0x0, 4))
    (h2 : fetchRel rootFromInclusionCode (off + 4) = some (.jalr ra ra o, 4))
    (hT : BitVec.ofNat 32 rootFromInclusionAddress + BitVec.ofNat 32 off + 0x0 + o =
      BitVec.ofNat 32 merkleNodeHashAddress)
    (hb : blockEnd rootFromInclusionCode (off + 8) rfCopy = some (off + 0x10))
    (h3 : fetchRel rootFromInclusionCode (off + 0x10) = some (.auipc ra 0x9000, 4))
    (h4 : fetchRel rootFromInclusionCode (off + 0x10 + 4) = some (.jalr ra ra o2, 4))
    (hT2 : BitVec.ofNat 32 rootFromInclusionAddress + BitVec.ofNat 32 (off + 0x10) + 0x9000 + o2 =
      BitVec.ofNat 32 memcpyStubAddress)
    (hoff : off % 2 = 0)
    (ha0 : reg nn a0 = G + 0x20) (ha1 : reg nn a1 = X) (ha2 : reg nn a2 = Y) (hsp : reg nn sp = G)
    (hXw : X.toNat + 32 ≤ 0x40000000) (hYw : Y.toNat + 32 ≤ 0x40000000)
    (hXs : Sep X 32 R 0x290) (hYs : Sep Y 32 R 0x290) :
    ∃ n' My, Steps nn n' ∧ St My (BitVec.ofNat 32 rootFromInclusionAddress) n' (off + 0x18) (reg n') ∧
      memBytes My G 32 = nodeHash (memBytes Mx X 32) (memBytes Mx Y 32) ∧
      (∀ x, Sep R 0x2D0 x 1 → My x = M1 x) ∧
      ∀ q, q ≠ ra → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 →
        q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) →
        q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → reg n' q = reg nn q := by
  let Q := BitVec.ofNat 32 rootFromInclusionAddress
  have E := C.E
  have hspw := E.hspw
  have hspl := E.hspl
  have hRn := C.hRn
  have hGn := C.hGn
  have hGa := C.hGa
  have hGa4 : G.toNat % 4 = 0 := by omega
  have sR : ∀ {b : Word} {k : Nat}, Sep b k (sp0 + 0xFFFFFD10) 0x2F0 → Sep b k R 0x290 := fun h => by
    rw [C.hR] at h; exact h.subR (c := 0) (l := 0x290) (by omega) |> fun h' => by rwa [add_ofNat_zero] at h'
  have aMx := C.agree inv
  have cx : ∀ {b : Word} {code : List Nat}, CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn Mx b code := fun hc hb hbl => C.codeX inv hc hb hbl
  have hQ : Q.toNat % 2 = 0 := by decide
  have eNR : G + 0xFFFFFD70 = R := by rw [C.hGR, BitVec.add_assoc]; exact BitVec.add_zero R
  -- `node_hash`.
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (cx E.cRF (by decide) (by decide)) h1 h2 hT (by decide)
  have r1 : ∀ q, q ≠ ra → reg n1 q = reg nn q := fun q h => by rw [regs1]; exact updz s.zero h
  have ra1 : reg n1 ra = Q + BitVec.ofNat 32 (off + 8) := by rw [regs1]; simp +decide only [upd_app, ↓reduceIte]; try rfl
  have retE : (Q + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = Q + BitVec.ofNat 32 (off + 8) :=
    even_clear _ (even_at Q hQ _ (by omega))
  obtain ⟨n2, c2, pc2, sp2, K2, out2, fr2⟩ := merkleNodeHash_correct n1 (out := G + 0x20) (L := X) (Rt := Y)
    (sp0 := G) (retAddr := Q + BitVec.ofNat 32 (off + 8))
    (by
      rw [mem1]
      exact { cN := cx E.cN (by decide) (by decide)
              cPre := fun i hi => by
                have hi' : i < 1 := hi
                rw [aMx _ (by rw [← C.hR]; exact (E.sXF.sub (c := i) (l := 1) (by omega)).symm)]; exact E.cPre i hi
              cX := cx E.cX (by decide) (by decide)
              cIV := fun i hi => by
                have hi' : i < 32 := by rw [show shaIVData.length = 32 from rfl] at hi; exact hi
                rw [aMx _ (by rw [← C.hR]; exact (E.sIF.sub (c := i) (l := 1) (by omega)).symm)]; exact E.cIV i hi
              cU := cx E.cU (by decide) (by decide)
              cUBlk := cx E.cUBlk (by decide) (by decide)
              cF := cx E.cF (by decide) (by decide)
              cZ := cx E.cZ (by decide) (by decide)
              cFBlk := cx E.cFBlk (by decide) (by decide)
              cMs := cx E.cMs (by decide) (by decide)
              cMS := cx E.cMS (by decide) (by decide)
              cMB := cx E.cMB (by decide) (by decide)
              cC := cx E.cC (by decide) (by decide)
              cI := cx E.cI (by decide) (by decide)
              cK := fun i hi => by
                have hi' : i < 256 := by rw [show shaKData.length = 256 from rfl] at hi; exact hi
                rw [aMx _ (by rw [← C.hR]; exact (E.sKF.sub (c := i) (l := 1) (by omega)).symm)]; exact E.cK i hi
              hsp := hGa
              hspl := by omega
              hspw := by omega
              hOw := by
                rw [show G + (0x20 : Word) = G + BitVec.ofNat 32 0x20 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]
                omega
              hLw := hXw
              hRw := hYw
              sOF := by
                rw [eNR, show G + (0x20 : Word) = G + BitVec.ofNat 32 0x20 from rfl, C.Gc]
                exact sep_offsets R (c := 0x290 + 0x20) (n := 32) (d := 0) (k := 0x290) (Or.inr (by omega)) (by omega)
                  (by omega) |> fun h => by rwa [add_ofNat_zero] at h
              sLF := by rw [eNR]; exact hXs
              sRF := by rw [eNR]; exact hYs
              sPF := by rw [eNR]; exact sR E.sXF
              sKF := by rw [eNR]; exact sR E.sKF
              sIF := by rw [eNR]; exact sR E.sIF })
    pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    ra1 retE (by rw [r1 sp (by decide), hsp])
  rw [mem1, eNR] at fr2
  rw [mem1] at out2
  obtain ⟨M2, hM2⟩ : ∃ M2, n2.mem = M2 := ⟨_, rfl⟩
  rw [hM2] at out2 fr2
  have i2 : ∀ x, Sep R 0x2D0 x 1 → M2 x = M1 x := fun x hx => by
    rw [fr2 x (hx.sub (c := 0) (l := 0x290) (by omega) |> fun h => by rwa [add_ofNat_zero] at h)
      (by
        rw [show G + (0x20 : Word) = G + BitVec.ofNat 32 0x20 from rfl, C.Gc]
        exact hx.sub (c := 0x290 + 0x20) (l := 32) (by omega)), inv x hx]
  have k2 : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 →
      r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) →
      r ≠ (31 : Fin 32) → reg n2 r = reg n1 r := K2
  have c2x : ∀ {b : Word} {code : List Nat}, CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn M2 b code := fun hc hb hbl => C.codeX i2 hc hb hbl
  -- Copy the hash over the running one.
  have u2 : St M2 Q n2 (off + 8) (reg n2) := ⟨by rw [pc2], hM2, fun _ => rfl⟩
  obtain ⟨n3, c3, u3⟩ := St.block rfCopy u2 (c2x E.cRF (by decide) (by decide)) hb (by simp [BlockOk, BInstr.ok, rfCopy])
  have R3 : ∀ q, reg n3 q = (runBlock rfCopy (M2, reg n2)).2 q := u3.regs
  have u3' : St M2 Q n3 (off + 0x10) (reg n3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  obtain ⟨n4, c4, pc4, mem4, regs4⟩ := u3'.callRa (c2x E.cRF (by decide) (by decide)) h3 h4 hT2 (by decide)
  have r4 : ∀ q, q ≠ ra → reg n4 q = reg n3 q := fun q h => by rw [regs4]; exact updz u3'.zero h
  have sp3 : reg n3 sp = G := by
    rw [R3]; simp +decide only [runBlock, BInstr.run, rfCopy, upd_app, ↓reduceIte]; exact sp2
  have eF16 : G + 0xFFFFFFF0 = R + BitVec.ofNat 32 0x280 := by rw [C.hGR, BitVec.add_assoc]; rfl
  have hF16 : (G + 0xFFFFFFF0).toNat = R.toNat + 0x280 := by rw [eF16, C.hRc (by omega)]
  have e20 : G + (0x20 : Word) = R + BitVec.ofNat 32 0x2B0 := by
    rw [show G + (0x20 : Word) = G + BitVec.ofNat 32 0x20 from rfl, C.Gc]
  obtain ⟨n5, c5, pc5, sp5, _, mem5, K5⟩ := memcpy_correct n4 (BitVec.ofNat 32 memcpyStubAddress)
    (Q + BitVec.ofNat 32 (off + 0x18)) G (G + 0x20) 32
    (fun i hi => by show n4.mem _ = _; rw [mem4]; exact c2x E.cMS (by decide) (by decide) i hi) (by decide) pc4
    (by rw [r4 a0 (by decide), R3]; simp +decide only [runBlock, BInstr.run, rfCopy, upd_app, ↓reduceIte]; rw [sp2]
        exact BitVec.zero_add _)
    (by rw [r4 a1 (by decide), R3]; simp +decide only [runBlock, BInstr.run, rfCopy, upd_app, ↓reduceIte]; rw [sp2]
        try rfl)
    (by rw [r4 a2 (by decide), R3]; simp +decide only [runBlock, BInstr.run, rfCopy, upd_app, ↓reduceIte]; try rfl)
    (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte]; try rfl)
    (even_clear _ (even_at Q hQ _ (by omega)))
    (by
      rw [mem4, r4 sp (by decide), sp3]
      exact { code := c2x E.cMB (by decide) (by decide)
              hDC := data_code (by omega) (by decide) (by decide)
              hFC := data_code (by rw [hF16]; omega) (by decide) (by decide)
              hdF := by
                rw [eF16, C.hGR]
                exact sep_offsets R (c := 0x290) (n := 32) (d := 0x280) (k := 16) (Or.inr (by omega)) (by omega)
                  (by omega)
              hsF := by
                rw [eF16, e20]
                exact sep_offsets R (c := 0x2B0) (n := 32) (d := 0x280) (k := 16) (Or.inr (by omega)) (by omega)
                  (by omega)
              hsep := by
                rw [e20, C.hGR]
                exact sep_offsets R (c := 0x290) (n := 32) (d := 0x2B0) (k := 32) (Or.inl (by omega)) (by omega)
                  (by omega)
              hF := by rw [hF16, hRn]; have := E.hsp; omega
              hFw := by rw [hF16]; omega
              hdw := by omega
              hsw := by rw [e20, C.hRc (by omega)]; omega })
  rw [mem4, r4 sp (by decide), sp3, eF16] at mem5
  obtain ⟨M5, hM5⟩ : ∃ M5, n5.mem = M5 := ⟨_, rfl⟩
  rw [hM5] at mem5
  have k5 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg n5 r = reg n4 r := K5
  refine ⟨n5, M5, c1.trans (c2.trans (c3.trans (c4.trans c5))), ⟨by rw [pc5], hM5, fun _ => rfl⟩, ?_, ?_,
    fun q q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => ?_⟩
  · rw [← out2]
    unfold memBytes; apply List.map_congr_left; intro i hi; have hi := List.mem_range.mp hi
    show (M5 (G + BitVec.ofNat 32 i)).toNat = (M2 (G + 0x20 + BitVec.ofNat 32 i)).toNat
    rw [mem5 _ (by
        rw [C.hGR, add_ofNat_assoc]
        exact sep_offsets R (c := 0x280) (n := 16) (d := 0x290 + i) (k := 1) (Or.inl (by omega)) (by omega)
          (by omega)),
      copyBytes_in hi (by omega)]
  · intro x hx
    rw [mem5 x (hx.sub (c := 0x280) (l := 16) (by omega)),
      copyBytes_sep (by rw [C.hGR]; exact hx.sub (c := 0x290) (l := 32) (by omega)) (Nat.le_refl _), i2 x hx]
  · have q2 : q ≠ sp ∨ q = sp := by by_cases h : q = sp <;> simp [h]
    rcases q2 with q2 | rfl
    · rw [k5 q q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2, r4 q q1, R3]
      simp only [runBlock, BInstr.run, rfCopy]
      rw [updz (by simp [upd]) q12, updz (by simp [upd]) q11, updz u2.zero q10,
        k2 q q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, r1 q q1]
    · rw [sp5, r4 sp (by decide), sp3, ← hsp]

set_option maxRecDepth 20000 in
/-- The shifts at 0x9C halve the index and the size. -/
theorem rf_shA {M : Word → BitVec 8} {nn : Machine} {f : Fin 32 → Word}
    (s : St M (BitVec.ofNat 32 rootFromInclusionAddress) nn 0x9C f)
    (hc : CodeIn M (BitVec.ofNat 32 rootFromInclusionAddress) rootFromInclusionCode) :
    ∃ n', Steps nn n' ∧ St M (BitVec.ofNat 32 rootFromInclusionAddress) n' 0xB6 (reg n') ∧
      pair64 (reg n' s1) (reg n' s0) = pair64 (f s1) (f s0) / 2 ∧
      pair64 (reg n' s6) (reg n' s5) = pair64 (f s6) (f s5) / 2 ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ s0 → q ≠ s1 → q ≠ s5 → q ≠ s6 → reg n' q = f q := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := St.block rfShA s hc rfShA_end (by simp [BlockOk, BInstr.ok, rfShA])
  have R : ∀ q, reg n1 q = (runBlock rfShA (M, f)).2 q := u1.regs
  refine ⟨n1, c1, ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩, ?_, ?_, fun q h10 h11 h8 h9 h21 h22 => ?_⟩
  · rw [R, R]; simp +decide only [runBlock, BInstr.run, rfShA, upd_app, ↓reduceIte]; exact pair64_shr1 _ _
  · rw [R, R]; simp +decide only [runBlock, BInstr.run, rfShA, upd_app, ↓reduceIte]; exact pair64_shr1 _ _
  · rw [R]; simp only [runBlock, BInstr.run, rfShA]
    rw [updz (by simp [upd]) h21, updz (by simp [upd]) h22, updz (by simp [upd]) h11, updz (by simp [upd]) h10,
      updz (by simp [upd]) h8, updz (by simp [upd]) h9, updz (by simp [upd]) h10, updz hz h9]

set_option maxRecDepth 20000 in
/-- The shifts at 0xE2 halve the index and the size. -/
theorem rf_shB {M : Word → BitVec 8} {nn : Machine} {f : Fin 32 → Word}
    (s : St M (BitVec.ofNat 32 rootFromInclusionAddress) nn 0xE2 f)
    (hc : CodeIn M (BitVec.ofNat 32 rootFromInclusionAddress) rootFromInclusionCode) :
    ∃ n', Steps nn n' ∧ St M (BitVec.ofNat 32 rootFromInclusionAddress) n' 0xFC (reg n') ∧
      pair64 (reg n' s1) (reg n' s0) = pair64 (f s1) (f s0) / 2 ∧
      pair64 (reg n' s6) (reg n' s5) = pair64 (f s6) (f s5) / 2 ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ s0 → q ≠ s1 → q ≠ s5 → q ≠ s6 → reg n' q = f q := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := St.block rfShB s hc rfShB_end (by simp [BlockOk, BInstr.ok, rfShB])
  have R : ∀ q, reg n1 q = (runBlock rfShB (M, f)).2 q := u1.regs
  refine ⟨n1, c1, ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩, ?_, ?_, fun q h10 h11 h8 h9 h21 h22 => ?_⟩
  · rw [R, R]; simp +decide only [runBlock, BInstr.run, rfShB, upd_app, ↓reduceIte]; exact pair64_shr1 _ _
  · rw [R, R]; simp +decide only [runBlock, BInstr.run, rfShB, upd_app, ↓reduceIte]; exact pair64_shr1 _ _
  · rw [R]; simp only [runBlock, BInstr.run, rfShB]
    rw [updz (by simp [upd]) h21, updz (by simp [upd]) h22, updz (by simp [upd]) h11, updz (by simp [upd]) h10,
      updz (by simp [upd]) h9, updz (by simp [upd]) h8, updz (by simp [upd]) h10, updz hz h9]

set_option maxRecDepth 20000 in
/-- The loop from 0xD6 that shifts the index and size while the index is
even and nonzero, then goes to 0x98: it computes `shiftEven`. -/
theorem rf_even {M : Word → BitVec 8}
    (hc : CodeIn M (BitVec.ofNat 32 rootFromInclusionAddress) rootFromInclusionCode) :
    ∀ t (nn : Machine), pair64 (reg nn s1) (reg nn s0) < 2 ^ t →
      St M (BitVec.ofNat 32 rootFromInclusionAddress) nn 0xD6 (reg nn) →
      ∃ n', Steps nn n' ∧ St M (BitVec.ofNat 32 rootFromInclusionAddress) n' 0x98 (reg n') ∧
        (pair64 (reg n' s1) (reg n' s0), pair64 (reg n' s6) (reg n' s5)) =
          shiftEven (pair64 (reg nn s1) (reg nn s0)) (pair64 (reg nn s6) (reg nn s5)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ s0 → q ≠ s1 → q ≠ s5 → q ≠ s6 → reg n' q = reg nn q := by
  intro t
  induction t with
  | zero =>
    intro nn hlt s
    have h0 : pair64 (reg nn s1) (reg nn s0) = 0 := by rw [Nat.pow_zero] at hlt; omega
    have hz := s.zero
    obtain ⟨n1, e1, u1⟩ := s.alu hc rf_at_d6 (off' := 0xDA) (by decide)
    have K1 := u1.upd_ne hz
    have A1 : reg n1 a0 = aluEval .or (reg nn s1) (reg nn s0) := u1.upd_eq (by decide)
    have u1' := u1.self
    obtain ⟨n2, e2, u2⟩ := u1'.taken hc 0x98 rf_at_da (by decide) (by
      simp only [branchTaken]; rw [A1, (pair64_zero _ _).mpr h0, u1'.zero]; decide)
    refine ⟨n2, .cons e1 (.single e2), u2.self, ?_, fun q h10 _ _ _ _ _ => by rw [u2.regs, K1 q h10]⟩
    rw [u2.regs, u2.regs, u2.regs, u2.regs, K1 s1 (by decide), K1 s0 (by decide), K1 s6 (by decide),
      K1 s5 (by decide), shiftEven_eq, ite_eq_right (fun h => h.2 h0)]
  | succ t ih =>
    intro nn hlt s
    have hz := s.zero
    obtain ⟨n1, e1, u1⟩ := s.alu hc rf_at_d6 (off' := 0xDA) (by decide)
    have K1 := u1.upd_ne hz
    have A1 : reg n1 a0 = aluEval .or (reg nn s1) (reg nn s0) := u1.upd_eq (by decide)
    have u1' := u1.self
    by_cases h0 : pair64 (reg nn s1) (reg nn s0) = 0
    · obtain ⟨n2, e2, u2⟩ := u1'.taken hc 0x98 rf_at_da (by decide) (by
        simp only [branchTaken]; rw [A1, (pair64_zero _ _).mpr h0, u1'.zero]; decide)
      refine ⟨n2, .cons e1 (.single e2), u2.self, ?_, fun q h10 _ _ _ _ _ => by rw [u2.regs, K1 q h10]⟩
      rw [u2.regs, u2.regs, u2.regs, u2.regs, K1 s1 (by decide), K1 s0 (by decide), K1 s6 (by decide),
        K1 s5 (by decide), shiftEven_eq, ite_eq_right (fun h => h.2 h0)]
    · obtain ⟨n2, e2, u2⟩ := u1'.notTaken hc 0xDC rf_at_da (by decide) (by
        simp only [branchTaken]; rw [A1, u1'.zero]
        exact beq_eq_false_iff_ne.mpr (fun h => h0 ((pair64_zero _ _).mp h)))
      have u2' := u2.self
      obtain ⟨n3, e3, u3⟩ := u2'.aluImm hc rf_at_dc (off' := 0xE0) (by decide)
      have K3 := u3.upd_ne u2'.zero
      have A3 : reg n3 a0 = aluEval .and (reg nn s1) 1 := by rw [u3.upd_eq (by decide), u2.regs, K1 s1 (by decide)]
      have u3' := u3.self
      by_cases hodd : pair64 (reg nn s1) (reg nn s0) % 2 = 0
      · obtain ⟨n4, e4, u4⟩ := u3'.notTaken hc 0xE2 rf_at_e0 (by decide) (by
          simp only [branchTaken]; rw [A3, (pair64_odd _ _).mpr hodd, u3'.zero]; decide)
        have rr : ∀ q, q ≠ a0 → reg n4 q = reg nn q := fun q h => by
          rw [u4.regs, K3 q h, u2.regs, K1 q h]
        obtain ⟨n5, c5, u5, hf5, hs5, K5⟩ := rf_shB u4.self hc
        obtain ⟨n6, e6, u6⟩ := u5.jump hc rf_at_fc (off' := 0xD6) (by decide)
          (by rw [u5.pc, BitVec.add_assoc]; exact even_bit0 (by decide))
        have lt6 : pair64 (reg n6 s1) (reg n6 s0) < 2 ^ t := by
          rw [u6.regs, u6.regs, hf5, rr s1 (by decide), rr s0 (by decide)]
          rw [Nat.pow_succ] at hlt; omega
        obtain ⟨n7, c7, u7, hp7, K7⟩ := ih n6 lt6 u6.self
        refine ⟨n7, .cons e1 (.cons e2 (.cons e3 (.cons e4 (c5.trans (.cons e6 c7))))), u7, ?_,
          fun q h10 h11 h8 h9 h21 h22 => by
            rw [K7 q h10 h11 h8 h9 h21 h22, u6.regs, K5 q h10 h11 h8 h9 h21 h22, rr q h10]⟩
        rw [hp7, u6.regs, u6.regs, u6.regs, u6.regs, hf5, hs5, rr s1 (by decide), rr s0 (by decide),
          rr s6 (by decide), rr s5 (by decide), shiftEven_eq (pair64 (reg nn s1) (reg nn s0)),
          ite_eq_left ⟨hodd, h0⟩]
      · obtain ⟨n4, e4, u4⟩ := u3'.taken hc 0x98 rf_at_e0 (by decide) (by
          simp only [branchTaken]; rw [A3, u3'.zero]
          exact bne_iff_ne.mpr (fun h => hodd ((pair64_odd _ _).mp h)))
        refine ⟨n4, .cons e1 (.cons e2 (.cons e3 (.single e4))), u4.self, ?_,
          fun q h10 _ _ _ _ _ => by rw [u4.regs, K3 q h10, u2.regs, K1 q h10]⟩
        rw [u4.regs, u4.regs, u4.regs, u4.regs, K3 s1 (by decide), K3 s0 (by decide), K3 s6 (by decide),
          K3 s5 (by decide), u2.regs, u2.regs, u2.regs, u2.regs, K1 s1 (by decide), K1 s0 (by decide),
          K1 s6 (by decide), K1 s5 (by decide), shiftEven_eq, ite_eq_right (fun h => hodd h.1)]

def rfA : List BInstr := [.aluImm .add a0 sp 0x20, .alu .add a1 x0 sp, .alu .add a2 x0 (19 : Fin 32)]
def rfB : List BInstr := [.aluImm .add a0 sp 0x20, .alu .add a2 x0 sp, .alu .add a1 x0 (19 : Fin 32)]
def rfX : List BInstr := [.alu .xor a0 (9 : Fin 32) (22 : Fin 32), .alu .xor a1 (8 : Fin 32) (21 : Fin 32), .alu .or a0 a0 a1]

set_option maxRecDepth 20000 in
theorem rfA_end : blockEnd rootFromInclusionCode 0x7A rfA = some 0x80 := by decide
set_option maxRecDepth 20000 in
theorem rfB_end : blockEnd rootFromInclusionCode 0xB8 rfB = some 0xBE := by decide
set_option maxRecDepth 20000 in
theorem rfX_end : blockEnd rootFromInclusionCode 0x6E rfX = some 0x78 := by decide

/-- Where `root_from_inclusion`'s loop ends for the result `o` of the
specification's loop: at 0x120 with the root in the frame at `G` when `o`
has `sn = 0`, and at the error path at 0x100 otherwise. -/
def RFDone (o : Option (Nat × Bytes)) (My : Word → BitVec 8) (G : Word) (n' : Machine) : Prop :=
  match o with
  | some (sf, rf) =>
    if sf = 0 then St My (BitVec.ofNat 32 rootFromInclusionAddress) n' 0x120 (reg n') ∧ memBytes My G 32 = rf
    else St My (BitVec.ofNat 32 rootFromInclusionAddress) n' 0x100 (reg n')
  | none => St My (BitVec.ofNat 32 rootFromInclusionAddress) n' 0x100 (reg n')

theorem pair64_ne_of_lt {lo hi lo' hi' : Word} (h : pair64 lo hi ≠ pair64 lo' hi') :
    aluEval .or (aluEval .xor lo lo') (aluEval .xor hi hi') ≠ 0 := fun e => h ((pair64_eq _ _ _ _).mp e)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- `root_from_inclusion`'s loop from 0x5E, with `j` proof hashes left
after the first `i`: it ends as `RFDone` says for the specification's loop
over those hashes, from the index and size in its register pairs and the
running hash `r` in the frame. -/
theorem rf_loop {M0 M1 : Word → BitVec 8} {out L Pp sp0 R G : Word} {n k : Nat}
    (C : RFCtx M0 M1 out L Pp sp0 R G n) (hk : n = 32 * k) :
    ∀ j i (nn : Machine) (Mx : Word → BitVec 8) (r : Bytes), i + j = k →
      St Mx (BitVec.ofNat 32 rootFromInclusionAddress) nn 0x5E (reg nn) →
      (∀ x, Sep R 0x2D0 x 1 → Mx x = M1 x) → memBytes Mx G 32 = r →
      reg nn s3 = Pp + BitVec.ofNat 32 (32 * i) → reg nn s4 = Pp + BitVec.ofNat 32 n → reg nn sp = G →
      ∃ n' My, Steps nn n' ∧ (∀ x, Sep R 0x2D0 x 1 → My x = M1 x) ∧
        (∀ q, q ≠ ra → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 →
          q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) →
          q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → q ≠ s0 → q ≠ s1 → q ≠ s3 → q ≠ s5 → q ≠ s6 →
          reg n' q = reg nn q) ∧
        RFDone (inclusionPath (pair64 (reg nn s1) (reg nn s0)) (pair64 (reg nn s6) (reg nn s5)) r
          (chunks32 j (memBytes M0 (Pp + BitVec.ofNat 32 (32 * i)) (32 * j)))) My G n' := by
  have E := C.E
  have hPw := E.hPw
  intro j
  induction j with
  | zero =>
    intro i nn Mx r hij s inv hr hs3 hs4 hsp
    have hc := C.codeX inv E.cRF (by decide) (by decide)
    have hz := s.zero
    obtain ⟨n1, e1, u1⟩ := s.alu hc rf_at_5e (off' := 0x62) (by decide)
    have K1 := u1.upd_ne hz
    have A1 : reg n1 a0 = aluEval .or (reg nn s6) (reg nn s5) := u1.upd_eq (by decide)
    have u1' := u1.self
    obtain ⟨n2, e2, u2⟩ := u1'.taken hc 0xFE rf_at_62 (by decide) (by
      simp only [branchTaken]; rw [K1 s3 (by decide), K1 s4 (by decide), hs3, hs4, hk, show i = k by omega]
      exact beq_iff_eq.mpr rfl)
    have keep2 : ∀ q, q ≠ a0 → reg n2 q = reg nn q := fun q h => by rw [u2.regs, K1 q h]
    show ∃ n' My, _ ∧ _ ∧ _ ∧ RFDone (some (pair64 (reg nn s6) (reg nn s5), r)) My G n'
    by_cases h0 : pair64 (reg nn s6) (reg nn s5) = 0
    · obtain ⟨n3, e3, u3⟩ := u2.self.taken hc 0x120 rf_at_fe (by decide) (by
        simp only [branchTaken]; rw [u2.regs, A1, (pair64_zero _ _).mpr h0, u2.self.zero]; decide)
      refine ⟨n3, Mx, .cons e1 (.cons e2 (.single e3)), inv,
        fun q q1 q5 q6 q7 q10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by rw [u3.regs, keep2 q q10], ?_⟩
      show if pair64 (reg nn s6) (reg nn s5) = 0 then _ else _
      rw [ite_eq_left h0]; exact ⟨u3.self, hr⟩
    · obtain ⟨n3, e3, u3⟩ := u2.self.notTaken hc 0x100 rf_at_fe (by decide) (by
        simp only [branchTaken]; rw [u2.regs, A1, u2.self.zero]
        exact beq_eq_false_iff_ne.mpr (fun h => h0 ((pair64_zero _ _).mp h)))
      refine ⟨n3, Mx, .cons e1 (.cons e2 (.single e3)), inv,
        fun q q1 q5 q6 q7 q10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by rw [u3.regs, keep2 q q10], ?_⟩
      show if pair64 (reg nn s6) (reg nn s5) = 0 then _ else _
      rw [ite_eq_right h0]; exact u3.self
  | succ j ih =>
    intro i nn Mx r hij s inv hr hs3 hs4 hsp
    have hc := C.codeX inv E.cRF (by decide) (by decide)
    have hz := s.zero
    obtain ⟨p, hp⟩ : ∃ p, Pp + BitVec.ofNat 32 (32 * i) = p := ⟨_, rfl⟩
    rw [hp] at hs3 ⊢
    have hpn : p.toNat = Pp.toNat + 32 * i := by
      rw [← hp, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 32 * i) (by omega)]; omega
    have hps : Sep p 32 R 0x290 := by
      have h := E.sPF; rw [C.hR] at h
      rw [← hp]; exact (h.sub (c := 32 * i) (l := 32) (by omega)).subR (c := 0) (l := 0x290) (by omega)
        |> fun h' => by rwa [add_ofNat_zero] at h'
    have hpd : memBytes Mx p 32 = memBytes M0 p 32 := C.dat inv (by
      have h := E.sPF; rw [C.hR] at h; rw [← hp]; exact h.sub (c := 32 * i) (l := 32) (by omega))
    have hch : chunks32 (j + 1) (memBytes M0 p (32 * (j + 1))) =
        memBytes M0 p 32 :: chunks32 j (memBytes M0 (Pp + BitVec.ofNat 32 (32 * (i + 1))) (32 * j)) := by
      show (memBytes M0 p (32 * (j + 1))).take 32 :: chunks32 j ((memBytes M0 p (32 * (j + 1))).drop 32) = _
      rw [memBytes_take M0 p (by omega), memBytes_drop M0 p (by omega), ← hp, add_ofNat_assoc,
        show 32 * i + 32 = 32 * (i + 1) by omega, show 32 * (j + 1) - 32 = 32 * j by omega]
    rw [hch, inclusionPath_cons]
    obtain ⟨f, hf⟩ : ∃ f, pair64 (reg nn s1) (reg nn s0) = f := ⟨_, rfl⟩
    obtain ⟨z, hzz⟩ : ∃ z, pair64 (reg nn s6) (reg nn s5) = z := ⟨_, rfl⟩
    rw [hf, hzz]
    -- The rest of a step, from 0x98: the next hash's address, the shifts, and the loop.
    have tail : ∀ (n9 : Machine) (M9 : Word → BitVec 8) (r9 : Bytes),
        St M9 (BitVec.ofNat 32 rootFromInclusionAddress) n9 0x98 (reg n9) → (∀ x, Sep R 0x2D0 x 1 → M9 x = M1 x) →
        memBytes M9 G 32 = r9 → reg n9 s3 = p → reg n9 s4 = Pp + BitVec.ofNat 32 n → reg n9 sp = G →
        ∃ n' My, Steps n9 n' ∧ (∀ x, Sep R 0x2D0 x 1 → My x = M1 x) ∧
          (∀ q, q ≠ ra → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 →
            q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) →
            q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → q ≠ s0 → q ≠ s1 → q ≠ s3 → q ≠ s5 → q ≠ s6 →
            reg n' q = reg n9 q) ∧
          RFDone (inclusionPath (pair64 (reg n9 s1) (reg n9 s0) / 2) (pair64 (reg n9 s6) (reg n9 s5) / 2) r9
            (chunks32 j (memBytes M0 (Pp + BitVec.ofNat 32 (32 * (i + 1))) (32 * j)))) My G n' := by
      intro n9 M9 r9 u9 i9 hr9 h3 h4 h2
      have hc9 := C.codeX i9 E.cRF (by decide) (by decide)
      obtain ⟨n10, e10, u10⟩ := u9.aluImm hc9 rf_at_98 (off' := 0x9C) (by decide)
      obtain ⟨n11, c11, u11, hf11, hs11, K11⟩ := rf_shA u10 hc9
      obtain ⟨n12, e12, u12⟩ := u11.jump hc9 rf_at_b6 (off' := 0x5E) (by decide)
        (by rw [u11.pc, BitVec.add_assoc]; exact even_bit0 (by decide))
      have R12 : ∀ q, reg n12 q = reg n11 q := u12.regs
      have keep10 : ∀ q, q ≠ s3 → upd (reg n9) (19 : Fin 32) (aluEval .add (reg n9 s3) 0x20) q = reg n9 q :=
        fun q h => updz u9.zero h
      obtain ⟨n13, M13, c13, i13, K13, D13⟩ := ih (i + 1) n12 M9 r9 (by omega) u12.self i9 hr9
        (by rw [R12, K11 s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add]; rw [h3, ← hp]
            exact add_ofNat_assoc Pp (32 * i) 32)
        (by rw [R12, K11 s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), keep10 _ (by decide), h4])
        (by rw [R12, K11 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), keep10 _ (by decide), h2])
      refine ⟨n13, M13, .cons e10 (c11.trans (.cons e12 c13)), i13,
        fun q q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9 q19 q21 q22 => ?_, ?_⟩
      · rw [K13 q q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9 q19 q21 q22, R12,
          K11 q q10 q11 q8 q9 q21 q22, keep10 q q19]
      · rw [R12, R12, R12, R12, hf11, hs11, keep10 _ (by decide), keep10 _ (by decide), keep10 _ (by decide),
          keep10 _ (by decide)] at D13
        exact D13
    have hGw : G.toNat + 32 ≤ 0x40000000 := by have := C.hGn; have := E.hspw; have := E.hspl; omega
    have hpw : p.toNat + 32 ≤ 0x40000000 := by rw [hpn]; omega
    have hGs : Sep G 32 R 0x290 := by
      rw [C.hGR]; exact sep_offsets R (c := 0x290) (n := 32) (d := 0) (k := 0x290) (Or.inr (by omega)) (by omega)
        (by omega) |> fun h => by rwa [add_ofNat_zero] at h
    have hGr : memBytes Mx G 32 = r := hr
    -- Path B: `node_hash(p, r)`, then skip even `f`.
    have pathB : ∀ n5 : Machine, St Mx (BitVec.ofNat 32 rootFromInclusionAddress) n5 0xB8 (reg n5) →
        Steps nn n5 → (∀ q, q ≠ a0 → q ≠ a1 → reg n5 q = reg nn q) →
        ∃ n' My, Steps nn n' ∧ (∀ x, Sep R 0x2D0 x 1 → My x = M1 x) ∧
          (∀ q, q ≠ ra → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 →
            q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) →
            q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → q ≠ s0 → q ≠ s1 → q ≠ s3 → q ≠ s5 → q ≠ s6 →
            reg n' q = reg nn q) ∧
          RFDone (inclusionPath ((shiftEven f z).1 / 2) ((shiftEven f z).2 / 2) (nodeHash (memBytes M0 p 32) r)
            (chunks32 j (memBytes M0 (Pp + BitVec.ofNat 32 (32 * (i + 1))) (32 * j)))) My G n' := by
      intro n5 u5 c5 k5
      obtain ⟨n6, c6, u6⟩ := St.block rfB u5 hc rfB_end (by simp [BlockOk, BInstr.ok, rfB])
      have R6 : ∀ q, reg n6 q = (runBlock rfB (Mx, reg n5)).2 q := u6.regs
      have u6' : St Mx (BitVec.ofNat 32 rootFromInclusionAddress) n6 0xBE (reg n6) := ⟨u6.pc, by rw [u6.mem]; rfl, fun _ => rfl⟩
      have sp5 : reg n5 sp = G := by rw [k5 sp (by decide) (by decide), hsp]
      obtain ⟨n7, M7, c7, u7, h7, i7, K7⟩ := rf_hash C n6 u6' inv rf_at_be rf_at_c2 (by decide) rfCopyB_end rf_at_ce
        rf_at_d2 (by decide) (by decide)
        (by rw [R6]; simp +decide only [runBlock, BInstr.run, rfB, upd_app, ↓reduceIte]; simp only [ev_add]; rw [sp5])
        (by rw [R6]; simp +decide only [runBlock, BInstr.run, rfB, upd_app, ↓reduceIte]; simp only [ev_add]
            rw [k5 s3 (by decide) (by decide), hs3]; exact BitVec.zero_add _)
        (by rw [R6]; simp +decide only [runBlock, BInstr.run, rfB, upd_app, ↓reduceIte]; simp only [ev_add]
            rw [sp5]; exact BitVec.zero_add _)
        (by rw [R6]; simp +decide only [runBlock, BInstr.run, rfB, upd_app, ↓reduceIte]; exact sp5)
        hpw hGw hps hGs
      rw [hpd, hGr] at h7
      have hc7 := C.codeX i7 E.cRF (by decide) (by decide)
      have k7 : ∀ q, q ≠ ra → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 →
          q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) →
          q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → reg n7 q = reg nn q :=
        fun q q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => by
          rw [K7 q q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, R6]
          simp only [runBlock, BInstr.run, rfB]
          rw [updz (by simp [upd]) q11, updz (by simp [upd]) q12, updz u5.zero q10, k5 q q10 q11]
      have ks : ∀ q, q = s0 ∨ q = s1 ∨ q = s5 ∨ q = s6 ∨ q = s3 ∨ q = s4 ∨ q = sp → reg n7 q = reg nn q := by
        intro q hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact k7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide)
      obtain ⟨n8, c8, u8, he8, K8⟩ := rf_even hc7 64 n7 (by
        rw [ks s1 (by simp), ks s0 (by simp)]; exact pair64_bound _ _) u7
      rw [ks s1 (by simp), ks s0 (by simp), ks s6 (by simp), ks s5 (by simp), hf, hzz] at he8
      have kk : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ s0 → q ≠ s1 → q ≠ s5 → q ≠ s6 → reg n8 q = reg n7 q := K8
      obtain ⟨n9, My, c9, i9, K9, D9⟩ := tail n8 M7 _ u8 i7 h7
        (by rw [kk s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ks s3 (by simp), hs3])
        (by rw [kk s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ks s4 (by simp), hs4])
        (by rw [kk sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ks sp (by simp), hsp])
      have e1 : pair64 (reg n8 s1) (reg n8 s0) = (shiftEven f z).1 := by rw [← he8]
      have e2 : pair64 (reg n8 s6) (reg n8 s5) = (shiftEven f z).2 := by rw [← he8]
      rw [e1, e2] at D9
      refine ⟨n9, My, c5.trans (c6.trans (c7.trans (c8.trans c9))), i9,
        fun q q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9 q19 q21 q22 => ?_, D9⟩
      rw [K9 q q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9 q19 q21 q22,
        kk q q10 q11 q8 q9 q21 q22, k7 q q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31]
    -- Path A: `node_hash(r, p)`.
    have pathA : ∀ n5 : Machine, St Mx (BitVec.ofNat 32 rootFromInclusionAddress) n5 0x7A (reg n5) →
        Steps nn n5 → (∀ q, q ≠ a0 → q ≠ a1 → reg n5 q = reg nn q) →
        ∃ n' My, Steps nn n' ∧ (∀ x, Sep R 0x2D0 x 1 → My x = M1 x) ∧
          (∀ q, q ≠ ra → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 →
            q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) →
            q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → q ≠ s0 → q ≠ s1 → q ≠ s3 → q ≠ s5 → q ≠ s6 →
            reg n' q = reg nn q) ∧
          RFDone (inclusionPath (f / 2) (z / 2) (nodeHash r (memBytes M0 p 32))
            (chunks32 j (memBytes M0 (Pp + BitVec.ofNat 32 (32 * (i + 1))) (32 * j)))) My G n' := by
      intro n5 u5 c5 k5
      obtain ⟨n6, c6, u6⟩ := St.block rfA u5 hc rfA_end (by simp [BlockOk, BInstr.ok, rfA])
      have R6 : ∀ q, reg n6 q = (runBlock rfA (Mx, reg n5)).2 q := u6.regs
      have u6' : St Mx (BitVec.ofNat 32 rootFromInclusionAddress) n6 0x80 (reg n6) := ⟨u6.pc, by rw [u6.mem]; rfl, fun _ => rfl⟩
      have sp5 : reg n5 sp = G := by rw [k5 sp (by decide) (by decide), hsp]
      obtain ⟨n7, M7, c7, u7, h7, i7, K7⟩ := rf_hash C n6 u6' inv rf_at_80 rf_at_84 (by decide) rfCopyA_end rf_at_90
        rf_at_94 (by decide) (by decide)
        (by rw [R6]; simp +decide only [runBlock, BInstr.run, rfA, upd_app, ↓reduceIte]; simp only [ev_add]; rw [sp5])
        (by rw [R6]; simp +decide only [runBlock, BInstr.run, rfA, upd_app, ↓reduceIte]; simp only [ev_add]
            rw [sp5]; exact BitVec.zero_add _)
        (by rw [R6]; simp +decide only [runBlock, BInstr.run, rfA, upd_app, ↓reduceIte]; simp only [ev_add]
            rw [k5 s3 (by decide) (by decide), hs3]; exact BitVec.zero_add _)
        (by rw [R6]; simp +decide only [runBlock, BInstr.run, rfA, upd_app, ↓reduceIte]; exact sp5)
        hGw hpw hGs hps
      rw [hpd, hGr] at h7
      have k7 : ∀ q, q ≠ ra → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 →
          q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) →
          q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → reg n7 q = reg nn q :=
        fun q q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => by
          rw [K7 q q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, R6]
          simp only [runBlock, BInstr.run, rfA]
          rw [updz (by simp [upd]) q12, updz (by simp [upd]) q11, updz u5.zero q10, k5 q q10 q11]
      have ks : ∀ q, q = s0 ∨ q = s1 ∨ q = s5 ∨ q = s6 ∨ q = s3 ∨ q = s4 ∨ q = sp → reg n7 q = reg nn q := by
        intro q hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact k7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide)
      obtain ⟨n9, My, c9, i9, K9, D9⟩ := tail n7 M7 _ u7 i7 h7 (by rw [ks s3 (by simp), hs3])
        (by rw [ks s4 (by simp), hs4]) (by rw [ks sp (by simp), hsp])
      rw [ks s1 (by simp), ks s0 (by simp), ks s6 (by simp), ks s5 (by simp), hf, hzz] at D9
      refine ⟨n9, My, c5.trans (c6.trans (c7.trans c9)), i9,
        fun q q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9 q19 q21 q22 => ?_, D9⟩
      rw [K9 q q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9 q19 q21 q22,
        k7 q q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31]
    -- The tests at 0x5E through 0x78.
    obtain ⟨n1, e1, u1⟩ := s.alu hc rf_at_5e (off' := 0x62) (by decide)
    have K1 := u1.upd_ne hz
    have A1 : reg n1 a0 = aluEval .or (reg nn s6) (reg nn s5) := u1.upd_eq (by decide)
    have u1' := u1.self
    have hne : p ≠ Pp + BitVec.ofNat 32 n := by rw [← hp]; exact add_ofNat_ne Pp (by omega) (by omega) (by omega)
    obtain ⟨n2, e2, u2⟩ := u1'.notTaken hc 0x66 rf_at_62 (by decide) (by
      simp only [branchTaken]; rw [K1 s3 (by decide), K1 s4 (by decide), hs3, hs4]
      exact beq_eq_false_iff_ne.mpr hne)
    have R2 : ∀ q, reg n2 q = reg n1 q := u2.regs
    have u2' := u2.self
    by_cases hz0 : z = 0
    · obtain ⟨n3, e3, u3⟩ := u2'.taken hc 0x100 rf_at_66 (by decide) (by
        simp only [branchTaken]; rw [R2, A1, (pair64_zero _ _).mpr (hzz.trans hz0), u2'.zero]; decide)
      refine ⟨n3, Mx, .cons e1 (.cons e2 (.single e3)), inv,
        fun q q1 q5 q6 q7 q10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by rw [u3.regs, R2, K1 q q10], ?_⟩
      rw [ite_eq_left hz0]; exact u3.self
    · obtain ⟨n3, e3, u3⟩ := u2'.notTaken hc 0x68 rf_at_66 (by decide) (by
        simp only [branchTaken]; rw [R2, A1, u2'.zero]
        exact beq_eq_false_iff_ne.mpr (fun h => hz0 (hzz ▸ (pair64_zero _ _).mp h)))
      rw [ite_eq_right hz0]
      have u3' := u3.self
      obtain ⟨n4, e4, u4⟩ := u3'.aluImm hc rf_at_68 (off' := 0x6C) (by decide)
      have K4 := u4.upd_ne u3'.zero
      have A4 : reg n4 a0 = aluEval .and (reg nn s1) 1 := by
        rw [u4.upd_eq (by decide), u3.regs, R2, K1 s1 (by decide)]
      have k4 : ∀ q, q ≠ a0 → reg n4 q = reg nn q := fun q h => by rw [K4 q h, u3.regs, R2, K1 q h]
      have u4' := u4.self
      by_cases hodd : f % 2 = 1
      · obtain ⟨n5, e5, u5⟩ := u4'.taken hc 0xB8 rf_at_6c (by decide) (by
          simp only [branchTaken]; rw [A4, u4'.zero]
          exact bne_iff_ne.mpr (fun h => by have := (pair64_odd (reg nn s1) (reg nn s0)).mp h; rw [hf] at this; omega))
        rw [ite_eq_left (Or.inl hodd)]
        exact pathB n5 u5.self (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.single e5)))))
          fun q h0 _ => by rw [u5.regs, k4 q h0]
      · obtain ⟨n5, e5, u5⟩ := u4'.notTaken hc 0x6E rf_at_6c (by decide) (by
          simp only [branchTaken]; rw [A4, (pair64_odd (reg nn s1) (reg nn s0)).mpr (by rw [hf]; omega), u4'.zero]; decide)
        obtain ⟨n6, c6, u6⟩ := St.block rfX u5.self hc rfX_end (by simp [BlockOk, BInstr.ok, rfX])
        have R6 : ∀ q, reg n6 q = (runBlock rfX (Mx, reg n5)).2 q := u6.regs
        have u6' : St Mx (BitVec.ofNat 32 rootFromInclusionAddress) n6 0x78 (reg n6) := ⟨u6.pc, by rw [u6.mem]; rfl, fun _ => rfl⟩
        have k5 : ∀ q, q ≠ a0 → reg n5 q = reg nn q := fun q h => by rw [u5.regs, k4 q h]
        have A6 : reg n6 a0 = aluEval .or (aluEval .xor (reg nn s1) (reg nn s6)) (aluEval .xor (reg nn s0) (reg nn s5)) := by
          rw [R6]; simp +decide only [runBlock, BInstr.run, rfX, upd_app, ↓reduceIte]
          rw [k5 s1 (by decide), k5 s6 (by decide), k5 s0 (by decide), k5 s5 (by decide)]
        have k6 : ∀ q, q ≠ a0 → q ≠ a1 → reg n6 q = reg nn q := fun q h0 h1 => by
          rw [R6]; simp only [runBlock, BInstr.run, rfX]
          rw [updz (by simp [upd]) h0, updz (by simp [upd]) h1, updz u5.self.zero h0, k5 q h0]
        by_cases heq : f = z
        · obtain ⟨n7, e7, u7⟩ := u6'.taken hc 0xB8 rf_at_78 (by decide) (by
            simp only [branchTaken]; rw [A6, (pair64_eq _ _ _ _).mpr (hf.trans (heq.trans hzz.symm)), u6'.zero]; decide)
          rw [ite_eq_left (Or.inr heq)]
          exact pathB n7 u7.self (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (c6.trans (.single e7)))))))
            fun q h0 h1 => by rw [u7.regs, k6 q h0 h1]
        · obtain ⟨n7, e7, u7⟩ := u6'.notTaken hc 0x7A rf_at_78 (by decide) (by
            simp only [branchTaken]; rw [A6, u6'.zero]
            exact beq_eq_false_iff_ne.mpr (fun h => heq (hf.symm.trans (((pair64_eq _ _ _ _).mp h).trans hzz))))
          rw [ite_eq_right (fun h => h.elim (fun h' => hodd h') heq)]
          exact pathA n7 u7.self (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (c6.trans (.single e7)))))))
            fun q h0 h1 => by rw [u7.regs, k6 q h0 h1]

set_option maxRecDepth 20000 in
theorem rfEpi_end : blockEnd rootFromInclusionCode 0x10C finEpi = some 0x11E := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- `root_from_inclusion`'s epilogue from 0x10C: when the frame at `G`
still holds what the prologue saved from `f`, it restores `ra` and `s0`
through `s6`, frees the frame, and returns to `f ra`. -/
theorem rf_epi {M0 Mw : Word → BitVec 8} {G : Word} {f : Fin 32 → Word} {nw : Machine}
    (s : St Mw (BitVec.ofNat 32 rootFromInclusionAddress) nw 0x10C (reg nw))
    (hc : CodeIn Mw (BitVec.ofNat 32 rootFromInclusionAddress) rootFromInclusionCode)
    (hsp : reg nw sp = G) (hGa : G.toNat % 4 = 0)
    (slots : ∀ c, 0x40 ≤ c → c < 0x60 →
      Mw (G + BitVec.ofNat 32 c) = finSaved M0 G (upd f sp G) (f s6) (G + BitVec.ofNat 32 c))
    (hret : f ra &&& ~~~1 = f ra) (hf0 : f 0 = 0) :
    ∃ n', Steps nw n' ∧ n'.pc = f ra ∧ n'.mem = Mw ∧ reg n' sp = G + 0x60 ∧
      (∀ q, q = ra ∨ q = s0 ∨ q = s1 ∨ q = s2 ∨ q = s3 ∨ q = s4 ∨ q = s5 ∨ q = s6 → reg n' q = f q) ∧
      ∀ q, q ≠ ra → q ≠ s0 → q ≠ s1 → q ≠ s2 → q ≠ s3 → q ≠ s4 → q ≠ s5 → q ≠ s6 → q ≠ sp →
        reg n' q = reg nw q := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := St.block finEpi s hc rfEpi_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, finEpi, upd_app, ↓reduceIte, and_true]
    rw [hsp]
    exact ⟨aligned_add hGa (k := 0x5C) (by decide), aligned_add hGa (k := 0x58) (by decide),
      aligned_add hGa (k := 0x54) (by decide), aligned_add hGa (k := 0x50) (by decide),
      aligned_add hGa (k := 0x4C) (by decide), aligned_add hGa (k := 0x48) (by decide),
      aligned_add hGa (k := 0x44) (by decide), aligned_add hGa (k := 0x40) (by decide)⟩)
  have R : ∀ q, reg n1 q = (runBlock finEpi (Mw, reg nw)).2 q := u1.regs
  have ld : ∀ c, 0x40 ≤ c → c + 4 ≤ 0x60 →
      memLoad32 Mw (G + BitVec.ofNat 32 c) = memLoad32 (finSaved M0 G (upd f sp G) (f s6)) (G + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact slots _ (by omega) (by omega)
  obtain ⟨v40, vra, vs0, vs1, vs2, vs3, vs4, vs5⟩ := finSaved_slots M0 G (upd f sp G) (f s6)
  have fu : ∀ q, q ≠ sp → upd f sp G q = f q := fun q h => updz hf0 h
  have L : ∀ (q : Fin 32) (c : Nat), (q, BitVec.ofNat 32 c) ∈ finEpiPs → 0x40 ≤ c → c + 4 ≤ 0x60 →
      reg n1 q = memLoad32 (finSaved M0 G (upd f sp G) (f s6)) (G + BitVec.ofNat 32 c) := by
    intro q c hm h1 h2
    rw [R, ← ld c h1 h2]
    simp only [finEpiPs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, hc'⟩ | ⟨rfl, hc'⟩ | ⟨rfl, hc'⟩ | ⟨rfl, hc'⟩ | ⟨rfl, hc'⟩ | ⟨rfl, hc'⟩ | ⟨rfl, hc'⟩ |
      ⟨rfl, hc'⟩ <;> (simp +decide only [runBlock, BInstr.run, finEpi, upd_app, ↓reduceIte]; rw [hsp, hc'])
  have u1' : St Mw (BitVec.ofNat 32 rootFromInclusionAddress) n1 0x11E (reg n1) :=
    ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩
  obtain ⟨n2, e2, pc2, mem2, regs2⟩ := u1'.jalr hc rf_at_11e
  have ra1 : reg n1 ra = f ra := by
    rw [L ra 0x5C (by decide) (by omega) (by omega)]; exact vra.trans (fu ra (by decide))
  refine ⟨n2, c1.trans (.single e2), by rw [pc2, ra1, add_lit_zero, hret], mem2, ?_, fun q hq => ?_,
    fun q q1 q8 q9 q18 q19 q20 q21 q22 q2 => ?_⟩
  · rw [regs2, R]; simp +decide only [runBlock, BInstr.run, finEpi, upd_app, ↓reduceIte]; simp only [ev_add]
    rw [hsp]
  · rw [regs2]
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ra1
    · rw [L s0 0x58 (by decide) (by omega) (by omega)]; exact vs0.trans (fu _ (by decide))
    · rw [L s1 0x54 (by decide) (by omega) (by omega)]; exact vs1.trans (fu _ (by decide))
    · rw [L s2 0x50 (by decide) (by omega) (by omega)]; exact vs2.trans (fu _ (by decide))
    · rw [L s3 0x4C (by decide) (by omega) (by omega)]; exact vs3.trans (fu _ (by decide))
    · rw [L s4 0x48 (by decide) (by omega) (by omega)]; exact vs4.trans (fu _ (by decide))
    · rw [L s5 0x44 (by decide) (by omega) (by omega)]; exact vs5.trans (fu _ (by decide))
    · rw [L s6 0x40 (by decide) (by omega) (by omega)]; exact v40
  · rw [regs2, R]; simp only [runBlock, BInstr.run, finEpi]
    rw [updz (by simp [upd]) q2, updz (by simp [upd]) q22, updz (by simp [upd]) q21, updz (by simp [upd]) q20,
      updz (by simp [upd]) q19, updz (by simp [upd]) q18, updz (by simp [upd]) q9, updz (by simp [upd]) q8,
      updz hz q1]

def rfErr : List BInstr := [.aluImm .add a0 x0 0x1B, .aluImm .add a1 x0 0x1, .sb (18 : Fin 32) a1 0x0, .sb (18 : Fin 32) a0 0x1]
def rfOk : List BInstr := [.aluImm .add a0 (18 : Fin 32) 0x1, .alu .add a1 x0 sp, .aluImm .add a2 x0 0x20]

set_option maxRecDepth 20000 in
theorem rfErr_end : blockEnd rootFromInclusionCode 0x100 rfErr = some 0x10C := by decide
set_option maxRecDepth 20000 in
theorem rfOk_end : blockEnd rootFromInclusionCode 0x120 rfOk = some 0x12A := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- The error exit from 0x100: it stores `Err(BadProof)` (tag 1, then
0x1B) at `out` and returns through the epilogue. -/
theorem rf_err {M0 M1 Mz : Word → BitVec 8} {out L Pp sp0 R G : Word} {n : Nat}
    (C : RFCtx M0 M1 out L Pp sp0 R G n) {f : Fin 32 → Word}
    (hM1 : ∀ c, 0x40 ≤ c → c < 0x60 → M1 (G + BitVec.ofNat 32 c) = finSaved M0 G (upd f sp G) (f s6) (G + BitVec.ofNat 32 c))
    (hret : f ra &&& ~~~1 = f ra) (hf0 : f 0 = 0) (nz : Machine)
    (s : St Mz (BitVec.ofNat 32 rootFromInclusionAddress) nz 0x100 (reg nz))
    (inv : ∀ x, Sep R 0x2D0 x 1 → Mz x = M1 x) (hs2 : reg nz s2 = out) (hsp : reg nz sp = G) :
    ∃ m', Steps nz m' ∧ m'.pc = f ra ∧ reg m' sp = G + 0x60 ∧
      (∀ q, q = ra ∨ q = s0 ∨ q = s1 ∨ q = s2 ∨ q = s3 ∨ q = s4 ∨ q = s5 ∨ q = s6 → reg m' q = f q) ∧
      (∀ q, q ≠ ra → q ≠ s0 → q ≠ s1 → q ≠ s2 → q ≠ s3 → q ≠ s4 → q ≠ s5 → q ≠ s6 → q ≠ sp → q ≠ a0 → q ≠ a1 →
        reg m' q = reg nz q) ∧
      m'.mem out = 1 ∧ m'.mem (out + 1) = 0x1B ∧
      ∀ x, Sep R 0x2F0 x 1 → Sep out 33 x 1 → m'.mem x = M0 x := by
  have E := C.E
  have hc := C.codeX inv E.cRF (by decide) (by decide)
  have hz := s.zero
  have sOF := E.sOF; rw [C.hR] at sOF
  have hOw := E.hOw
  have sOc : ∀ c, c < 33 → Sep (out + BitVec.ofNat 32 c) 1 (BitVec.ofNat 32 rootFromInclusionAddress)
      rootFromInclusionCode.length := fun c hc' =>
    data_code (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := St.block rfErr s hc rfErr_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, rfErr, upd_app, ↓reduceIte, true_and]
    rw [hs2]; exact ⟨sOc 0 (by omega), sOc 1 (by omega), trivial⟩)
  obtain ⟨Mw, hMw⟩ : ∃ Mw, memStore8 (memStore8 Mz (out + BitVec.ofNat 32 0) ((1 : Word).extractLsb' 0 8))
      (out + BitVec.ofNat 32 1) ((0x1B : Word).extractLsb' 0 8) = Mw := ⟨_, rfl⟩
  have eMw : (runBlock rfErr (Mz, reg nz)).1 = Mw := by
    simp +decide only [runBlock, BInstr.run, rfErr, upd_app, ↓reduceIte]; rw [hs2, hz, ← hMw]; rfl
  have u1' : St Mw (BitVec.ofNat 32 rootFromInclusionAddress) n1 0x10C (reg n1) := ⟨u1.pc, by rw [u1.mem, eMw], fun _ => rfl⟩
  have R1 : ∀ q, reg n1 q = (runBlock rfErr (Mz, reg nz)).2 q := u1.regs
  have nO : ∀ x, Sep out 33 x 1 → Mw x = Mz x := fun x hx => by
    rw [← hMw, memStore8_ne (fun e => hx 1 (by omega) 0 (by decide) (by rw [add_ofNat_zero]; exact e.symm)),
      memStore8_ne (fun e => hx 0 (by omega) 0 (by decide) (by simp only [add_ofNat_zero] at e ⊢; exact e.symm))]
  have cW : CodeIn Mw (BitVec.ofNat 32 rootFromInclusionAddress) rootFromInclusionCode := fun i hi => by
    rw [nO _ (by
      exact (data_code (a := out) (n := 33) (b := BitVec.ofNat 32 rootFromInclusionAddress)
        (l := rootFromInclusionCode.length) (by omega) (by decide) (by decide)).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  have hGa4 : G.toNat % 4 = 0 := by have := C.hGa; omega
  obtain ⟨m', c', pc', mem', sp', rs', ks'⟩ := rf_epi (M0 := M0) (f := f) u1' cW
    (by rw [R1]; simp +decide only [runBlock, BInstr.run, rfErr, upd_app, ↓reduceIte]; exact hsp) hGa4
    (fun c h1 h2 => by
      rw [nO _ (by rw [C.Gc]; exact sOF.subR (c := 0x290 + c) (l := 1) (by omega)), inv _ (by
        rw [C.Gc]
        exact sep_offsets R (c := 0) (n := 0x2D0) (d := 0x290 + c) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
          |> fun h => by rwa [add_ofNat_zero] at h), hM1 c h1 h2])
    hret hf0
  refine ⟨m', c1.trans c', pc', sp', rs', fun q q1 q8 q9 q18 q19 q20 q21 q22 q2 q10 q11 => ?_, ?_, ?_, fun x hx hy => ?_⟩
  · rw [ks' q q1 q8 q9 q18 q19 q20 q21 q22 q2, R1]; simp only [runBlock, BInstr.run, rfErr]
    rw [updz (by simp [upd]) q11, updz hz q10]
  · rw [mem', ← hMw, memStore8_ne (show out ≠ out + BitVec.ofNat 32 1 from fun e => by
      have := add_ofNat_ne out (c := 0) (d := 1) (by decide) (by decide) (by decide)
      rw [add_ofNat_zero] at this; exact this e), add_ofNat_zero, memStore8_same]; rfl
  · rw [mem', ← hMw, show out + (1 : Word) = out + BitVec.ofNat 32 1 from rfl, memStore8_same]; rfl
  · rw [mem', nO x hy, C.agree inv x hx]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- The success exit from 0x120: it copies the running hash at `G` to
`out + 1`, stores tag 0 at `out`, and returns through the epilogue. -/
theorem rf_ok {M0 M1 Mz : Word → BitVec 8} {out L Pp sp0 R G : Word} {n : Nat} {r : List Nat}
    (C : RFCtx M0 M1 out L Pp sp0 R G n) {f : Fin 32 → Word}
    (hM1 : ∀ c, 0x40 ≤ c → c < 0x60 → M1 (G + BitVec.ofNat 32 c) = finSaved M0 G (upd f sp G) (f s6) (G + BitVec.ofNat 32 c))
    (hret : f ra &&& ~~~1 = f ra) (hf0 : f 0 = 0) (nz : Machine)
    (s : St Mz (BitVec.ofNat 32 rootFromInclusionAddress) nz 0x120 (reg nz))
    (inv : ∀ x, Sep R 0x2D0 x 1 → Mz x = M1 x) (hs2 : reg nz s2 = out) (hsp : reg nz sp = G)
    (hr : memBytes Mz G 32 = r) :
    ∃ m', Steps nz m' ∧ m'.pc = f ra ∧ reg m' sp = G + 0x60 ∧
      (∀ q, q = ra ∨ q = s0 ∨ q = s1 ∨ q = s2 ∨ q = s3 ∨ q = s4 ∨ q = s5 ∨ q = s6 → reg m' q = f q) ∧
      (∀ q, q ≠ ra → q ≠ s0 → q ≠ s1 → q ≠ s2 → q ≠ s3 → q ≠ s4 → q ≠ s5 → q ≠ s6 → q ≠ sp → q ≠ a0 → q ≠ a1 →
        q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) →
        q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → reg m' q = reg nz q) ∧
      m'.mem out = 0 ∧ memBytes m'.mem (out + 1) 32 = r ∧
      ∀ x, Sep R 0x2F0 x 1 → Sep out 33 x 1 → m'.mem x = M0 x := by
  let Q := BitVec.ofNat 32 rootFromInclusionAddress
  have E := C.E
  have hspw := E.hspw
  have hspl := E.hspl
  have hRn := C.hRn
  have hGn := C.hGn
  have hGa := C.hGa
  have hOw := E.hOw
  have hQ : Q.toNat % 2 = 0 := by decide
  have sOF := E.sOF; rw [C.hR] at sOF
  have hc := C.codeX inv E.cRF (by decide) (by decide)
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := St.block rfOk s hc rfOk_end (by simp [BlockOk, BInstr.ok, rfOk])
  have R1 : ∀ q, reg n1 q = (runBlock rfOk (Mz, reg nz)).2 q := u1.regs
  have u1' : St Mz Q n1 0x12A (reg n1) := ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1'.callRa hc rf_at_12a rf_at_12e
    (show Q + BitVec.ofNat 32 0x12A + 0x9000 + 0x4A6 = BitVec.ofNat 32 memcpyStubAddress by decide) (by decide)
  have r2 : ∀ q, q ≠ ra → reg n2 q = reg n1 q := fun q h => by rw [regs2]; exact updz u1'.zero h
  have sp1 : reg n1 sp = G := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, rfOk, upd_app, ↓reduceIte]; exact hsp
  have eF16 : G + 0xFFFFFFF0 = R + BitVec.ofNat 32 0x280 := by rw [C.hGR, BitVec.add_assoc]; rfl
  have hF16 : (G + 0xFFFFFFF0).toNat = R.toNat + 0x280 := by rw [eF16, C.hRc (by omega)]
  have hO1 : (out + BitVec.ofNat 32 1).toNat = out.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have sO1 : Sep (out + BitVec.ofNat 32 1) 32 R 0x2F0 := sOF.sub (c := 1) (l := 32) (by omega)
  obtain ⟨n3, c3, pc3, sp3, _, mem3, K3⟩ := memcpy_correct n2 (BitVec.ofNat 32 memcpyStubAddress)
    (Q + BitVec.ofNat 32 0x132) (out + BitVec.ofNat 32 1) G 32
    (fun i hi => by show n2.mem _ = _; rw [mem2]; exact C.codeX inv E.cMS (by decide) (by decide) i hi) (by decide) pc2
    (by rw [r2 a0 (by decide), R1]; simp +decide only [runBlock, BInstr.run, rfOk, upd_app, ↓reduceIte]; rw [hs2]; try rfl)
    (by rw [r2 a1 (by decide), R1]; simp +decide only [runBlock, BInstr.run, rfOk, upd_app, ↓reduceIte]; rw [hsp]
        exact BitVec.zero_add _)
    (by rw [r2 a2 (by decide), R1]; simp +decide only [runBlock, BInstr.run, rfOk, upd_app, ↓reduceIte]; try rfl)
    (by rw [regs2]; simp +decide only [upd_app, ↓reduceIte]; try rfl)
    (even_clear _ (even_at Q hQ _ (by omega)))
    (by
      rw [mem2, r2 sp (by decide), sp1]
      exact { code := C.codeX inv E.cMB (by decide) (by decide)
              hDC := data_code (by rw [hO1]; omega) (by decide) (by decide)
              hFC := data_code (by rw [hF16]; omega) (by decide) (by decide)
              hdF := by rw [eF16]; exact sO1.subR (c := 0x280) (l := 16) (by omega)
              hsF := by
                rw [eF16, C.hGR]
                exact sep_offsets R (c := 0x290) (n := 32) (d := 0x280) (k := 16) (Or.inr (by omega)) (by omega)
                  (by omega)
              hsep := by rw [C.hGR]; exact sO1.subR (c := 0x290) (l := 32) (by omega)
              hF := by rw [hF16, hRn]; have := E.hsp; omega
              hFw := by rw [hF16]; omega
              hdw := by rw [hO1]; omega
              hsw := by omega })
  rw [mem2, r2 sp (by decide), sp1, eF16] at mem3
  obtain ⟨M3, hM3⟩ : ∃ M3, n3.mem = M3 := ⟨_, rfl⟩
  rw [hM3] at mem3
  have k3 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ sp →
      reg n3 q = reg n2 q := K3
  have sp3' : reg n3 sp = G := by rw [sp3, r2 sp (by decide), sp1]
  have s23 : reg n3 s2 = out := by
    rw [k3 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r2 s2 (by decide), R1]
    simp +decide only [runBlock, BInstr.run, rfOk, upd_app, ↓reduceIte]; exact hs2
  have i3 : ∀ x, Sep R 0x2F0 x 1 → Sep out 33 x 1 → M3 x = Mz x := fun x hx hy => by
    rw [mem3 x (hx.sub (c := 0x280) (l := 16) (by omega)),
      copyBytes_sep (hy.sub (c := 1) (l := 32) (by omega)) (Nat.le_refl _)]
  have cz : ∀ i, i < rootFromInclusionCode.length → Sep (R + BitVec.ofNat 32 0x280) 16 (Q + BitVec.ofNat 32 i) 1 ∧
      Sep out 33 (Q + BitVec.ofNat 32 i) 1 := fun i hi =>
    ⟨(C.Rd (c := 0x280) (l := 16) (by omega) (b := Q) (k := rootFromInclusionCode.length) (by decide)
        (by decide)).subR (c := i) (l := 1) hi,
     (data_code (a := out) (n := 33) (b := Q) (l := rootFromInclusionCode.length) (by omega) (by decide)
        (by decide)).subR (c := i) (l := 1) hi⟩
  have hc3 : CodeIn M3 Q rootFromInclusionCode := fun i hi => by
    rw [mem3 _ (cz i hi).1, copyBytes_sep ((cz i hi).2.sub (c := 1) (l := 32) (by omega)) (Nat.le_refl _)]
    exact hc i hi
  have u3 : St M3 Q n3 0x132 (reg n3) := ⟨by rw [pc3], hM3, fun _ => rfl⟩
  obtain ⟨n4, e4, u4⟩ := u3.sb hc3 rf_at_132 (off' := 0x136) (by decide)
  rw [s23, show (reg n3 x0).extractLsb' 0 8 = 0 from by rw [u3.zero]; rfl] at u4
  obtain ⟨M4, hM4⟩ : ∃ M4, memStore8 M3 (out + 0x0) 0 = M4 := ⟨_, rfl⟩
  rw [hM4] at u4
  have nO : ∀ x, x ≠ out → M4 x = M3 x := fun x hx => by
    rw [← hM4, memStore8_ne (by rw [show out + (0x0 : Word) = out from BitVec.add_zero out]; exact hx)]
  have hc4 : CodeIn M4 Q rootFromInclusionCode := fun i hi => by
    rw [nO _ (fun e => (cz i hi).2 0 (by omega) 0 (by omega) (by simp only [add_ofNat_zero]; exact e.symm))]
    exact hc3 i hi
  obtain ⟨n5, e5, u5⟩ := u4.jump hc4 rf_at_136 (off' := 0x10C) (by decide)
    (by rw [u4.pc, BitVec.add_assoc]; exact even_bit0 (by decide))
  have u5' : St M4 Q n5 0x10C (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
  have hGa4 : G.toNat % 4 = 0 := by omega
  obtain ⟨m', c', pc', mem', sp', rs', ks'⟩ := rf_epi (M0 := M0) (f := f) u5' hc4
    (by rw [u5.regs, sp3']) hGa4
    (fun c h1 h2 => by
      have hx : Sep R 0x2D0 (G + BitVec.ofNat 32 c) 1 := by
        rw [C.Gc]
        exact sep_offsets R (c := 0) (n := 0x2D0) (d := 0x290 + c) (k := 1) (Or.inl (by omega)) (by omega)
          (by omega) |> fun h => by rwa [add_ofNat_zero] at h
      have hy : Sep out 33 (G + BitVec.ofNat 32 c) 1 := by
        rw [C.Gc]; exact sOF.subR (c := 0x290 + c) (l := 1) (by omega)
      rw [nO _ (fun e => hy 0 (by omega) 0 (by omega) (by simp only [add_ofNat_zero] at e ⊢; exact e.symm)),
        mem3 _ (by
          rw [C.Gc]
          exact sep_offsets R (c := 0x280) (n := 16) (d := 0x290 + c) (k := 1) (Or.inl (by omega)) (by omega)
            (by omega)),
        copyBytes_sep (hy.sub (c := 1) (l := 32) (by omega)) (Nat.le_refl _), inv _ hx, hM1 c h1 h2])
    hret hf0
  refine ⟨m', c1.trans (c2.trans (c3.trans (.cons e4 (.cons e5 c')))), pc', sp', rs',
    fun q q1 q8 q9 q18 q19 q20 q21 q22 q2 qa0 qa1 qa2 qa3 qa4 qa5 qa6 qa7 qt0 qt1 q7 q28 q29 q30 q31 => ?_, ?_, ?_,
    fun x hx hy => ?_⟩
  · rw [ks' q q1 q8 q9 q18 q19 q20 q21 q22 q2, u5.regs,
      k3 q qa1 qa2 qa3 qa4 qa5 qa6 qa7 qt0 qt1 q7 q28 q29 q30 q2, r2 q q1, R1]
    simp only [runBlock, BInstr.run, rfOk]
    rw [updz (by simp [upd, hz]) qa2, updz (by simp [upd, hz]) qa1, updz hz qa0]
  · rw [mem', ← hM4, show out + (0x0 : Word) = out from BitVec.add_zero out, memStore8_same]
  · rw [mem', ← hr]
    unfold memBytes; apply List.map_congr_left; intro i hi; have hi := List.mem_range.mp hi
    show (M4 (out + BitVec.ofNat 32 1 + BitVec.ofNat 32 i)).toNat = (Mz (G + BitVec.ofNat 32 i)).toNat
    rw [nO _ (fun e => add_ofNat_ne out (c := 1 + i) (d := 0) (by omega) (by omega) (by omega)
        (by rw [← add_ofNat_assoc, add_ofNat_zero]; exact e)),
      mem3 _ (by
        rw [add_ofNat_assoc]
        exact ((sOF.sub (c := 1 + i) (l := 1) (by omega)).subR (c := 0x280) (l := 16) (by omega)).symm),
      copyBytes_in hi (by omega)]
  · rw [mem', nO x (fun e => hy 0 (by omega) 0 (by omega) (by simp only [add_ofNat_zero]; exact e.symm)),
      i3 x hx hy, C.agree inv x hx]

def rfPro : List BInstr :=
  finPro ++ [.alu .add (20 : Fin 32) x0 (17 : Fin 32), .alu .add (19 : Fin 32) x0 a6,
    .alu .add (8 : Fin 32) x0 a2, .alu .add (9 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0]
def rfS : List BInstr :=
  [.aluImm .sltu a0 a3 0x1, .alu .sub (21 : Fin 32) a4 a0, .aluImm .add (22 : Fin 32) a3 0xFFFFFFFF,
    .alu .add a0 x0 sp, .aluImm .add a2 x0 0x20, .alu .add a1 x0 a5]

set_option maxRecDepth 20000 in
theorem rfPro_end : blockEnd rootFromInclusionCode 0 rfPro = some 0x1C := by decide
set_option maxRecDepth 20000 in
theorem rfS_end : blockEnd rootFromInclusionCode 0x40 rfS = some 0x54 := by decide

/-- The registers that nothing in `root_from_inclusion` writes. -/
def RFOther (q : Fin 32) : Prop := q.val ∈ [0, 3, 4, 23, 24, 25, 26, 27]

theorem RFOther.ne {q : Fin 32} (h : RFOther q) {r : Fin 32}
    (hr : r.val ∉ [0, 3, 4, 23, 24, 25, 26, 27] := by decide) : q ≠ r := fun e => hr (e ▸ h)

set_option synthInstance.maxSize 100000 in
theorem rf_cat : ∀ q : Fin 32, q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 →
    q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) →
    q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) →
    (q = ra ∨ q = s0 ∨ q = s1 ∨ q = s2 ∨ q = s3 ∨ q = s4 ∨ q = s5 ∨ q = s6) ∨ q = sp ∨ RFOther q := by
  unfold RFOther; decide

/-- What `rootFromInclusion_correct` concludes about the machine `m'` it
returns to, for the specification's result `res`. -/
def RFPost (m m' : Machine) (sp0 out retAddr : Word) (res : Option Bytes) : Prop :=
  Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
    (∀ q, q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 →
      q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) →
      q ≠ (31 : Fin 32) → reg m' q = reg m q) ∧
    (match res with
      | some root => m'.mem out = 0 ∧ memBytes m'.mem (out + 1) 32 = root
      | none => m'.mem out = 1 ∧ m'.mem (out + 1) = 0x1B) ∧
    ∀ x, Sep (sp0 + 0xFFFFFD10) 0x2F0 x 1 → Sep out 33 x 1 → m'.mem x = m.mem x

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- **The compiled `c3_verify::merkle::root_from_inclusion`.** Called with
the result buffer at `out`, the index and tree size as 64-bit numbers in
`a1`:`a2` and `a3`:`a4` (low word first), the leaf hash at `L`, and the `n`
proof bytes at `Pp`, it returns what RFC 6962's `rootFromInclusion` says:
for `some root`, tag 0 at `out` and `root` in the 32 bytes after it; for
`none`, tag 1 and `Error::BadProof` (0x1B). It returns to `retAddr` with
`sp` and the callee-saved registers kept, and changes no memory outside the
33 result bytes and 0x2F0 bytes of stack below `sp`. -/
theorem rootFromInclusion_correct (m : Machine) {out L Pp sp0 retAddr : Word} {n : Nat}
    (E : RootEnv m.mem out L Pp sp0 n) (hpc : m.pc = BitVec.ofNat 32 rootFromInclusionAddress)
    (ha0 : reg m a0 = out) (ha5 : reg m a5 = L) (ha6 : reg m a6 = Pp) (ha7 : reg m a7 = BitVec.ofNat 32 n)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 →
        q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) →
        q ≠ (31 : Fin 32) → reg m' q = reg m q) ∧
      (match rootFromInclusion (pair64 (reg m a1) (reg m a2)) (pair64 (reg m a3) (reg m a4))
          (memBytes m.mem L 32) (memBytes m.mem Pp n) with
        | some root => m'.mem out = 0 ∧ memBytes m'.mem (out + 1) 32 = root
        | none => m'.mem out = 1 ∧ m'.mem (out + 1) = 0x1B) ∧
      ∀ x, Sep (sp0 + 0xFFFFFD10) 0x2F0 x 1 → Sep out 33 x 1 → m'.mem x = m.mem x := by
  suffices H : ∀ spec, rootFromInclusion (pair64 (reg m a1) (reg m a2)) (pair64 (reg m a3) (reg m a4))
      (memBytes m.mem L 32) (memBytes m.mem Pp n) = spec → ∃ m', RFPost m m' sp0 out retAddr spec by
    obtain ⟨m', h⟩ := H _ rfl; exact ⟨m', h⟩
  intro spec hspec
  let Q := BitVec.ofNat 32 rootFromInclusionAddress
  let M0 := m.mem
  let R := sp0 + 0xFFFFFD10
  let G := sp0 + 0xFFFFFFA0
  have hGR : G = R + BitVec.ofNat 32 0x290 := by
    show sp0 + 0xFFFFFFA0 = sp0 + 0xFFFFFD10 + BitVec.ofNat 32 0x290; rw [BitVec.add_assoc]; rfl
  have eG60 : G + 0x60 = sp0 := by
    show sp0 + 0xFFFFFFA0 + 0x60 = sp0; rw [BitVec.add_assoc]; exact BitVec.add_zero sp0
  let g1 := upd (reg m) sp G
  let M1 := finSaved M0 G g1 (reg m s6)
  have hz0 : reg m 0 = 0 := rfl
  have M1R : ∀ x, Sep R 0x2F0 x 1 → M1 x = M0 x := fun x hx =>
    finSaved_out M0 G g1 _ x (by rw [hGR, add_ofNat_assoc]; exact hx.sub (c := 0x290 + 0x40) (l := 0x20) (by omega))
  have C : RFCtx M0 M1 out L Pp sp0 R G n := ⟨E, rfl, hGR, M1R⟩
  have hspw := E.hspw
  have hspl := E.hspl
  have hPw := E.hPw
  have hRn := C.hRn
  have hGn := C.hGn
  have hGa := C.hGa
  have hGa4 : G.toNat % 4 = 0 := by omega
  have hQ : Q.toNat % 2 = 0 := by decide
  have hret' : reg m ra &&& ~~~1 = reg m ra := by rw [hra]; exact hret
  -- The two exits.
  have errK : ∀ (nz : Machine) (Mz : Word → BitVec 8), spec = none →
      St Mz Q nz 0x100 (reg nz) → (∀ x, Sep R 0x2D0 x 1 → Mz x = M1 x) → Steps m nz →
      reg nz s2 = out → reg nz sp = G → (∀ q, RFOther q → reg nz q = reg m q) →
      ∃ m', RFPost m m' sp0 out retAddr spec := by
    intro nz Mz hn s inv cs hs2 hsp' ko
    obtain ⟨m', c', pc', sp', rs', ks', o1, o2, fr⟩ :=
      rf_err C (f := reg m) (fun _ _ _ => rfl) hret' hz0 nz s inv hs2 hsp'
    refine ⟨m', cs.trans c', by rw [pc', hra], by rw [sp', eG60],
      fun q q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => ?_, by rw [hn]; exact ⟨o1, o2⟩,
      fun x hx hy => by rw [fr x hx hy]⟩
    rcases rf_cat q q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 with hr | rfl | hO
    · exact rs' q hr
    · rw [sp', eG60, hsp]
    · rw [ks' q hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne, ko q hO]
  have okK : ∀ (nz : Machine) (Mz : Word → BitVec 8) (r : Bytes), spec = some r →
      St Mz Q nz 0x120 (reg nz) → (∀ x, Sep R 0x2D0 x 1 → Mz x = M1 x) → memBytes Mz G 32 = r → Steps m nz →
      reg nz s2 = out → reg nz sp = G → (∀ q, RFOther q → reg nz q = reg m q) →
      ∃ m', RFPost m m' sp0 out retAddr spec := by
    intro nz Mz r hn s inv hr cs hs2 hsp' ko
    obtain ⟨m', c', pc', sp', rs', ks', o1, o2, fr⟩ :=
      rf_ok C (f := reg m) (fun _ _ _ => rfl) hret' hz0 nz s inv hs2 hsp' hr
    refine ⟨m', cs.trans c', by rw [pc', hra], by rw [sp', eG60],
      fun q q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => ?_, by rw [hn]; exact ⟨o1, o2⟩,
      fun x hx hy => by rw [fr x hx hy]⟩
    rcases rf_cat q q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 with hr | rfl | hO
    · exact rs' q hr
    · rw [sp', eG60, hsp]
    · rw [ks' q hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne
        hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne, ko q hO]
  have hn32 : n < 2 ^ 32 := by omega
  have hlen : (memBytes M0 Pp n).length = n := memBytes_length _ _ _
  -- The prologue.
  have st0 : St M0 Q m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have slotP : ∀ (o : Nat), o + 4 ≤ 0x60 → o % 4 = 0 →
      (G + BitVec.ofNat 32 o).toNat % 4 = 0 ∧ Sep (G + BitVec.ofNat 32 o) 4 Q rootFromInclusionCode.length :=
    fun o h2 h3 => ⟨aligned_add hGa4 h3, by rw [C.Gc]; exact C.Rd (by omega) (by decide) (by decide)⟩
  obtain ⟨n1, c1, u1⟩ := St.block rfPro st0 E.cRF rfPro_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, rfPro, finPro, List.cons_append, List.nil_append, upd_app,
      ↓reduceIte, and_true]
    simp only [ev_add]; rw [hsp]
    exact ⟨True.intro, slotP 0x5C (by omega) (by omega), slotP 0x58 (by omega) (by omega),
      slotP 0x54 (by omega) (by omega), slotP 0x50 (by omega) (by omega), slotP 0x4C (by omega) (by omega),
      slotP 0x48 (by omega) (by omega), slotP 0x44 (by omega) (by omega), slotP 0x40 (by omega) (by omega)⟩)
  have eM1 : (runBlock rfPro (M0, reg m)).1 = M1 := by
    simp +decide only [runBlock, BInstr.run, rfPro, finPro, List.cons_append, List.nil_append, upd_app, ↓reduceIte]
    simp only [ev_add]; rw [hsp]
    simp +decide only [M1, finSaved, saveMem, g1, upd_app, ↓reduceIte]; rfl
  have R1 : ∀ q, reg n1 q = (runBlock rfPro (M0, reg m)).2 q := u1.regs
  have u1' : St M1 Q n1 0x1C (reg n1) := ⟨u1.pc, by rw [u1.mem, eM1], fun _ => rfl⟩
  have K1 : ∀ q, q ≠ sp → q ≠ s0 → q ≠ s1 → q ≠ s2 → q ≠ s3 → q ≠ s4 → reg n1 q = reg m q :=
    fun q h2 h8 h9 h18 h19 h20 => by
      rw [R1]; simp only [runBlock, BInstr.run, rfPro, finPro, List.cons_append, List.nil_append]
      rw [updz (by simp [upd]) h18, updz (by simp [upd]) h9, updz (by simp [upd]) h8, updz (by simp [upd]) h19,
        updz (by simp [upd]) h20, updz hz0 h2]
  have sp1 : reg n1 sp = G := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, rfPro, finPro, List.cons_append, List.nil_append, upd_app,
      ↓reduceIte]
    simp only [ev_add]; rw [hsp]
  have s4_1 : reg n1 s4 = BitVec.ofNat 32 n := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, rfPro, finPro, List.cons_append, List.nil_append, upd_app,
      ↓reduceIte]
    simp only [ev_add]; exact (BitVec.zero_add _).trans ha7
  have s3_1 : reg n1 s3 = Pp := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, rfPro, finPro, List.cons_append, List.nil_append, upd_app,
      ↓reduceIte]
    simp only [ev_add]; exact (BitVec.zero_add _).trans ha6
  have s0_1 : reg n1 s0 = reg m a2 := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, rfPro, finPro, List.cons_append, List.nil_append, upd_app,
      ↓reduceIte]
    simp only [ev_add]; exact BitVec.zero_add _
  have s1_1 : reg n1 s1 = reg m a1 := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, rfPro, finPro, List.cons_append, List.nil_append, upd_app,
      ↓reduceIte]
    simp only [ev_add]; exact BitVec.zero_add _
  have s2_1 : reg n1 s2 = out := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, rfPro, finPro, List.cons_append, List.nil_append, upd_app,
      ↓reduceIte]
    simp only [ev_add]; exact (BitVec.zero_add _).trans ha0
  have hc1 : CodeIn M1 Q rootFromInclusionCode := C.codeX (My := M1) (fun _ _ => rfl) E.cRF (by decide) (by decide)
  -- An error exit with the registers after the prologue.
  have err1 : ∀ nz, St M1 Q nz 0x100 (reg nz) → Steps m nz → (∀ q, q ≠ a0 → q ≠ a1 → reg nz q = reg n1 q) →
      spec = none → ∃ m', RFPost m m' sp0 out retAddr spec := fun nz s cs kz hn =>
    errK nz M1 hn s (fun _ _ => rfl) cs (by rw [kz s2 (by decide) (by decide), s2_1])
      (by rw [kz sp (by decide) (by decide), sp1])
      (fun q hO => by rw [kz q hO.ne hO.ne, K1 q hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne])
  -- After the checks: copy the leaf, run the loop, and exit.
  have bodyP : ∀ n6, St M1 Q n6 0x40 (reg n6) → Steps m n6 → (∀ q, q ≠ a0 → q ≠ a1 → reg n6 q = reg n1 q) →
      n % 32 = 0 → n / 32 ≤ maxProofHashes → pair64 (reg m a1) (reg m a2) < pair64 (reg m a3) (reg m a4) →
      ∃ m', RFPost m m' sp0 out retAddr spec := by
    intro n6 u6 cs6 k6 hm hb hlt
    obtain ⟨n7, c7, u7⟩ := St.block rfS u6 hc1 rfS_end (by simp [BlockOk, BInstr.ok, rfS])
    have R7 : ∀ q, reg n7 q = (runBlock rfS (M1, reg n6)).2 q := u7.regs
    have u7' : St M1 Q n7 0x54 (reg n7) := ⟨u7.pc, by rw [u7.mem]; rfl, fun _ => rfl⟩
    have hz6 : reg n6 0 = 0 := u6.zero
    have k7 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ s5 → q ≠ s6 → reg n7 q = reg n6 q := fun q h10 h11 h12 h21 h22 => by
      rw [R7]; simp only [runBlock, BInstr.run, rfS]
      rw [updz (by simp [upd]) h11, updz (by simp [upd]) h12, updz (by simp [upd]) h10, updz (by simp [upd]) h22,
        updz (by simp [upd]) h21, updz hz6 h10]
    obtain ⟨n8, c8, pc8, mem8, regs8⟩ := u7'.callRa hc1 rf_at_54 rf_at_58
      (show Q + BitVec.ofNat 32 0x54 + 0x9000 + 0x57C = BitVec.ofNat 32 memcpyStubAddress by decide) (by decide)
    have r8 : ∀ q, q ≠ ra → reg n8 q = reg n7 q := fun q h => by rw [regs8]; exact updz u7'.zero h
    have sp6 : reg n6 sp = G := by rw [k6 sp (by decide) (by decide), sp1]
    have eF16 : G + 0xFFFFFFF0 = R + BitVec.ofNat 32 0x280 := by rw [hGR, BitVec.add_assoc]; rfl
    have hF16 : (G + 0xFFFFFFF0).toNat = R.toNat + 0x280 := by rw [eF16, C.hRc (by omega)]
    have sLF := E.sLF
    have hLw := E.hLw
    have hcMS : CodeIn M1 (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode :=
      C.codeX (My := M1) (fun _ _ => rfl) E.cMS (by decide) (by decide)
    have hGs : Sep G 32 (R + BitVec.ofNat 32 0x280) 16 := by
      rw [hGR]
      exact sep_offsets R (c := 0x290) (n := 32) (d := 0x280) (k := 16) (Or.inr (by omega)) (by omega) (by omega)
    obtain ⟨n9, c9, pc9, sp9, _, mem9, K9⟩ := memcpy_correct n8 (BitVec.ofNat 32 memcpyStubAddress)
      (Q + BitVec.ofNat 32 (0x54 + 8)) G L 32
      (fun i hi => by show n8.mem _ = _; rw [mem8]; exact hcMS i hi) (by decide) pc8
      (by rw [r8 a0 (by decide), R7]; simp +decide only [runBlock, BInstr.run, rfS, upd_app, ↓reduceIte]
          simp only [ev_add]; rw [sp6]; exact BitVec.zero_add _)
      (by rw [r8 a1 (by decide), R7]; simp +decide only [runBlock, BInstr.run, rfS, upd_app, ↓reduceIte]
          simp only [ev_add]; rw [k6 a5 (by decide) (by decide), K1 a5 (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide), ha5]; exact BitVec.zero_add _)
      (by rw [r8 a2 (by decide), R7]; simp +decide only [runBlock, BInstr.run, rfS, upd_app, ↓reduceIte]; try rfl)
      (by rw [regs8]; simp +decide only [upd_app, ↓reduceIte])
      (even_clear _ (even_at Q hQ _ (by omega)))
      (by
        rw [mem8, r8 sp (by decide), k7 sp (by decide) (by decide) (by decide) (by decide) (by decide), sp6]
        exact { code := C.codeX (My := M1) (fun _ _ => rfl) E.cMB (by decide) (by decide)
                hDC := data_code (by omega) (by decide) (by decide)
                hFC := data_code (by rw [hF16]; omega) (by decide) (by decide)
                hdF := by rw [eF16]; exact hGs
                hsF := by rw [eF16]; exact sLF.subR (c := 0x280) (l := 16) (by omega)
                hsep := by rw [hGR]; exact (sLF.subR (c := 0x290) (l := 32) (by omega)).symm
                hF := by rw [hF16, hRn]; have := E.hsp; omega
                hFw := by rw [hF16]; omega
                hdw := by omega
                hsw := by omega })
    rw [mem8, r8 sp (by decide), k7 sp (by decide) (by decide) (by decide) (by decide) (by decide), sp6, eF16] at mem9
    obtain ⟨M9, hM9⟩ : ∃ M9, n9.mem = M9 := ⟨_, rfl⟩
    rw [hM9] at mem9
    have k9 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ sp →
        reg n9 q = reg n8 q := K9
    have i9 : ∀ x, Sep R 0x2D0 x 1 → M9 x = M1 x := fun x hx => by
      rw [mem9 x (hx.sub (c := 0x280) (l := 16) (by omega)),
        copyBytes_sep (by rw [hGR]; exact hx.sub (c := 0x290) (l := 32) (by omega)) (Nat.le_refl _)]
    have hr9 : memBytes M9 G 32 = memBytes M0 L 32 := by
      unfold memBytes; apply List.map_congr_left; intro i hi; have hi := List.mem_range.mp hi
      show (M9 (G + BitVec.ofNat 32 i)).toNat = (M0 (L + BitVec.ofNat 32 i)).toNat
      rw [mem9 _ ((hGs.sub (c := i) (l := 1) (by omega)).symm), copyBytes_in hi (by omega),
        M1R _ ((sLF.sub (c := i) (l := 1) (by omega)).symm)]
    have u9 : St M9 Q n9 0x5C (reg n9) := ⟨by rw [pc9], hM9, fun _ => rfl⟩
    have hc9 := C.codeX i9 E.cRF (by decide) (by decide)
    obtain ⟨n10, e10, u10⟩ := u9.alu hc9 rf_at_5c (off' := 0x5E) (by decide)
    have u10' := u10.self
    -- Registers through the copy.
    have kB : ∀ q, q ≠ ra → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
        q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ sp →
        q ≠ s4 → q ≠ s5 → q ≠ s6 → reg n10 q = reg n6 q :=
      fun q q1 q10 q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2 q20 q21 q22 => by
        rw [u10.upd_ne u9.zero q q20, k9 q q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2, r8 q q1,
          k7 q q10 q11 q12 q21 q22]
    have sp10 : reg n10 sp = G := by
      rw [u10.upd_ne u9.zero sp (by decide), sp9, r8 sp (by decide),
        k7 sp (by decide) (by decide) (by decide) (by decide) (by decide), sp6]
    have s3_10 : reg n10 s3 = Pp := by
      rw [kB s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), k6 s3 (by decide) (by decide), s3_1]
    have s4_10 : reg n10 s4 = Pp + BitVec.ofNat 32 n := by
      rw [u10.upd_eq (by decide), k9 s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8 s4 (by decide),
        k7 s4 (by decide) (by decide) (by decide) (by decide) (by decide),
        k9 s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8 s3 (by decide),
        k7 s3 (by decide) (by decide) (by decide) (by decide) (by decide),
        k6 s4 (by decide) (by decide), k6 s3 (by decide) (by decide), s4_1, s3_1]
      exact BitVec.add_comm _ _
    have s01 : ∀ q, (q = s0 ∨ q = s1 ∨ q = s2) → reg n10 q = reg n1 q := fun q hq => by
      have : q ≠ ra ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧
          q ≠ (7 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ sp ∧ q ≠ s4 ∧
          q ≠ s5 ∧ q ≠ s6 := by rcases hq with rfl | rfl | rfl <;> decide
      obtain ⟨q1, q10, q11, q12, q13, q14, q15, q16, q17, q5, q6, q7, q28, q29, q30, q2, q20, q21, q22⟩ := this
      rw [kB q q1 q10 q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2 q20 q21 q22, k6 q q10 q11]
    have oB : ∀ q, RFOther q → reg n10 q = reg m q := fun q hO => by
      rw [kB q hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne
        hO.ne hO.ne hO.ne, k6 q hO.ne hO.ne, K1 q hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne]
    have s6_10 : reg n10 s6 = aluEval .add (reg m a3) 0xFFFFFFFF := by
      rw [u10.upd_ne u9.zero s6 (by decide), k9 s6 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        r8 s6 (by decide), R7]
      simp +decide only [runBlock, BInstr.run, rfS, upd_app, ↓reduceIte]
      rw [k6 a3 (by decide) (by decide), K1 a3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    have s5_10 : reg n10 s5 = aluEval .sub (reg m a4) (aluEval .sltu (reg m a3) 1) := by
      rw [u10.upd_ne u9.zero s5 (by decide), k9 s5 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        r8 s5 (by decide), R7]
      simp +decide only [runBlock, BInstr.run, rfS, upd_app, ↓reduceIte]
      rw [k6 a3 (by decide) (by decide), K1 a3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        k6 a4 (by decide) (by decide), K1 a4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    have hpos : 0 < pair64 (reg m a3) (reg m a4) := by omega
    obtain ⟨n', My, c', i', K', D⟩ := rf_loop C (k := n / 32) (by omega) (n / 32) 0 n10 M9 (memBytes M0 L 32)
      (by omega) u10' i9 hr9 (by rw [s3_10, show 32 * 0 = 0 from rfl, add_ofNat_zero]) s4_10 sp10
    rw [s01 s1 (by decide), s01 s0 (by decide), s1_1, s0_1, s6_10, s5_10, pair64_dec _ _ hpos,
      show 32 * 0 = 0 from rfl, add_ofNat_zero, show 32 * (n / 32) = n by omega] at D
    have hS : spec = match inclusionPath (pair64 (reg m a1) (reg m a2)) (pair64 (reg m a3) (reg m a4) - 1)
        (memBytes M0 L 32) (chunks32 (n / 32) (memBytes M0 Pp n)) with
        | some (s, r) => if s = 0 then some r else none
        | none => none := by
      rw [← hspec, rootFromInclusion_eq, hlen, ite_eq_left ⟨hm, hb, hlt⟩]; rfl
    have cs : Steps m n10 := cs6.trans (c7.trans (c8.trans (c9.trans (.single e10))))
    have ks2 : reg n' s2 = out := by
      rw [K' s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), s01 s2 (by decide), s2_1]
    have ksp : reg n' sp = G := by
      rw [K' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), sp10]
    have ko : ∀ q, RFOther q → reg n' q = reg m q := fun q hO => by
      rw [K' q hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne hO.ne
        hO.ne hO.ne hO.ne hO.ne hO.ne, oB q hO]
    generalize inclusionPath (pair64 (reg m a1) (reg m a2)) (pair64 (reg m a3) (reg m a4) - 1)
      (memBytes M0 L 32) (chunks32 (n / 32) (memBytes M0 Pp n)) = o at D hS
    rcases o with _ | ⟨sf, rf⟩
    · exact errK n' My hS D i' (cs.trans c') ks2 ksp ko
    · by_cases h0 : sf = 0
      · have D' : St My Q n' 0x120 (reg n') ∧ memBytes My G 32 = rf := by
          have D'' : if sf = 0 then _ else _ := D
          rw [ite_eq_left h0] at D''; exact D''
        exact okK n' My rf (by rw [hS]; show (if sf = 0 then some rf else none) = _; rw [ite_eq_left h0])
          D'.1 i' D'.2 (cs.trans c') ks2 ksp ko
      · have D' : St My Q n' 0x100 (reg n') := by
          have D'' : if sf = 0 then _ else _ := D
          rw [ite_eq_right h0] at D''; exact D''
        exact errK n' My (by rw [hS]; show (if sf = 0 then some rf else none) = _; rw [ite_eq_right h0])
          D' i' (cs.trans c') ks2 ksp ko
  -- With this implication in context, `omega` uses `Classical.choice`, so it comes after the last `omega`.
  have specNo : ¬ (n % 32 = 0 ∧ n / 32 ≤ maxProofHashes ∧
      pair64 (reg m a1) (reg m a2) < pair64 (reg m a3) (reg m a4)) → spec = none := fun h => by
    rw [← hspec, rootFromInclusion_eq, hlen, ite_eq_right h]
  -- The length checks: no bytes left over, and at most 64 hashes.
  have lenP : ∀ n2, St M1 Q n2 0x2E (reg n2) → Steps m n2 → (∀ q, q ≠ a0 → reg n2 q = reg n1 q) →
      pair64 (reg m a1) (reg m a2) < pair64 (reg m a3) (reg m a4) → ∃ m', RFPost m m' sp0 out retAddr spec := by
    intro n2 u2 cs2 k2 hlt
    have s4_2 : reg n2 s4 = BitVec.ofNat 32 n := by rw [k2 s4 (by decide), s4_1]
    obtain ⟨n3, e3, u3⟩ := u2.aluImm hc1 rf_at_2e (off' := 0x32) (by decide)
    have A3 : (reg n3 a0).toNat = n / 32 := by
      rw [u3.upd_eq (by decide), s4_2]
      show (BitVec.ofNat 32 n >>> 5).toNat = _
      rw [toNat_srl5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32]
    have u3' := u3.self
    obtain ⟨n4, e4, u4⟩ := u3'.aluImm hc1 rf_at_32 (off' := 0x36) (by decide)
    have A4 : reg n4 a1 = 0x40 := by rw [u4.upd_eq (by decide), u3'.zero]; rfl
    have A4' : reg n4 a0 = reg n3 a0 := u4.upd_ne u3'.zero a0 (by decide)
    have k4 : ∀ q, q ≠ a0 → q ≠ a1 → reg n4 q = reg n1 q := fun q h1 h2 => by
      rw [u4.upd_ne u3'.zero q h2, u3.upd_ne u2.zero q h1, k2 q h1]
    have u4' := u4.self
    by_cases hb : 64 < n / 32
    · obtain ⟨n5, e5, u5⟩ := u4'.taken hc1 0x100 rf_at_36 (by decide) (by
        simp only [branchTaken, BitVec.ult]; rw [A4, A4', A3]; exact decide_eq_true hb)
      exact err1 n5 u5.self (cs2.trans (.cons e3 (.cons e4 (.single e5))))
        (fun q h1 h2 => by rw [u5.regs, k4 q h1 h2])
        (specNo fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hb h.2.1))
    · obtain ⟨n5, e5, u5⟩ := u4'.notTaken hc1 0x3A rf_at_36 (by decide) (by
        simp only [branchTaken, BitVec.ult]; rw [A4, A4', A3]; exact decide_eq_false hb)
      have u5' := u5.self
      obtain ⟨n6, e6, u6⟩ := u5'.aluImm hc1 rf_at_3a (off' := 0x3E) (by decide)
      have A6 : (reg n6 a0).toNat = n % 32 := by
        rw [u6.upd_eq (by decide), u5.regs, k4 s4 (by decide) (by decide), s4_1]
        show (BitVec.ofNat 32 n &&& 0x1F#32).toNat = _
        rw [toNat_and31, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32]
      have k6 : ∀ q, q ≠ a0 → q ≠ a1 → reg n6 q = reg n1 q := fun q h1 h2 => by
        rw [u6.upd_ne u5'.zero q h1, u5.regs, k4 q h1 h2]
      have u6' := u6.self
      by_cases hm : n % 32 = 0
      · obtain ⟨n7, e7, u7⟩ := u6'.notTaken hc1 0x40 rf_at_3e (by decide) (by
          simp only [branchTaken]
          rw [show reg n6 a0 = 0 from BitVec.eq_of_toNat_eq (by rw [A6, hm]; rfl), u6'.zero]; rfl)
        exact bodyP n7 u7.self (cs2.trans (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.single e7))))))
          (fun q h1 h2 => by rw [u7.regs, k6 q h1 h2]) hm (show n / 32 ≤ 64 from Nat.le_of_not_lt hb) hlt
      · obtain ⟨n7, e7, u7⟩ := u6'.taken hc1 0x100 rf_at_3e (by decide) (by
          simp only [branchTaken]; rw [u6'.zero]
          exact bne_iff_ne.mpr (fun e => hm (by rw [← A6, e]; rfl)))
        exact err1 n7 u7.self (cs2.trans (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.single e7))))))
          (fun q h1 h2 => by rw [u7.regs, k6 q h1 h2]) (specNo fun h => hm h.1)
  -- The index check, on the 64-bit pairs.
  have hlt := pair64_lt (reg m a1) (reg m a2) (reg m a3) (reg m a4)
  have e_a2 : reg n1 a2 = reg m a2 := K1 a2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e_a3 : reg n1 a3 = reg m a3 := K1 a3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e_a4 : reg n1 a4 = reg m a4 := K1 a4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  by_cases hh : reg m a2 = reg m a4
  · rw [ite_eq_left hh] at hlt
    obtain ⟨n2, e2, u2⟩ := u1'.taken hc1 0x28 rf_at_1c (by decide) (by
      simp only [branchTaken]; rw [e_a2, e_a4, hh]; exact beq_iff_eq.mpr rfl)
    obtain ⟨n3, e3, u3⟩ := u2.self.alu hc1 rf_at_28 (off' := 0x2C) (by decide)
    have A3 : reg n3 a0 = aluEval .sltu (reg m a1) (reg m a3) := by
      rw [u3.upd_eq (by decide), u2.regs, u2.regs, s1_1, e_a3]
    have k3 : ∀ q, q ≠ a0 → reg n3 q = reg n1 q := fun q h => by rw [u3.upd_ne u2.self.zero q h, u2.regs]
    have u3' := u3.self
    by_cases hl : (reg m a1).ult (reg m a3) = true
    · obtain ⟨n4, e4, u4⟩ := u3'.notTaken hc1 0x2E rf_at_2c (by decide) (by
        simp only [branchTaken]; rw [A3, u3'.zero]
        show ((if (reg m a1).ult (reg m a3) then 1 else 0 : Word) == 0) = false
        rw [ite_eq_left hl]; rfl)
      exact lenP n4 u4.self (c1.trans (.cons e2 (.cons e3 (.single e4)))) (fun q h => by rw [u4.regs, k3 q h])
        (hlt.mpr hl)
    · obtain ⟨n4, e4, u4⟩ := u3'.taken hc1 0x100 rf_at_2c (by decide) (by
        simp only [branchTaken]; rw [A3, u3'.zero]
        show ((if (reg m a1).ult (reg m a3) then 1 else 0 : Word) == 0) = true
        rw [ite_eq_right hl]; rfl)
      exact err1 n4 u4.self (c1.trans (.cons e2 (.cons e3 (.single e4)))) (fun q h _ => by rw [u4.regs, k3 q h])
        (specNo fun h => hl (hlt.mp h.2.2))
  · rw [ite_eq_right hh] at hlt
    obtain ⟨n2, e2, u2⟩ := u1'.notTaken hc1 0x20 rf_at_1c (by decide) (by
      simp only [branchTaken]; rw [e_a2, e_a4]; exact beq_eq_false_iff_ne.mpr hh)
    obtain ⟨n3, e3, u3⟩ := u2.self.alu hc1 rf_at_20 (off' := 0x24) (by decide)
    have A3 : reg n3 a0 = aluEval .sltu (reg m a2) (reg m a4) := by
      rw [u3.upd_eq (by decide), u2.regs, u2.regs, s0_1, e_a4]
    have k3 : ∀ q, q ≠ a0 → reg n3 q = reg n1 q := fun q h => by rw [u3.upd_ne u2.self.zero q h, u2.regs]
    have u3' := u3.self
    by_cases hl : (reg m a2).ult (reg m a4) = true
    · obtain ⟨n4, e4, u4⟩ := u3'.taken hc1 0x2E rf_at_24 (by decide) (by
        simp only [branchTaken]; rw [A3, u3'.zero]
        show ((if (reg m a2).ult (reg m a4) then 1 else 0 : Word) != 0) = true
        rw [ite_eq_left hl]; rfl)
      exact lenP n4 u4.self (c1.trans (.cons e2 (.cons e3 (.single e4)))) (fun q h => by rw [u4.regs, k3 q h])
        (hlt.mpr hl)
    · obtain ⟨n4, e4, u4⟩ := u3'.notTaken hc1 0x26 rf_at_24 (by decide) (by
        simp only [branchTaken]; rw [A3, u3'.zero]
        show ((if (reg m a2).ult (reg m a4) then 1 else 0 : Word) != 0) = false
        rw [ite_eq_right hl]; rfl)
      obtain ⟨n5, e5, u5⟩ := u4.self.jump hc1 rf_at_26 (off' := 0x100) (by decide)
        (by rw [u4.pc, BitVec.add_assoc]; exact even_bit0 (by decide))
      exact err1 n5 u5.self (c1.trans (.cons e2 (.cons e3 (.cons e4 (.single e5)))))
        (fun q h _ => by rw [u5.regs, u4.regs, k3 q h]) (specNo fun h => hl (hlt.mp h.2.2))

end C3.RV32
