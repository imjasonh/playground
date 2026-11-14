import C3BootProofs.Proofs.ShaSupport
import C3BootProofs.Image.BootloaderV0

/-!
# Environment, byte-block assembly, and helper calls for `compress256`
-/

namespace C3.RV32

open C3.ImageV0

set_option maxRecDepth 20000

/-! ## The round constants table `shaKData` -/

def shaKWordAt (t : Nat) : Word :=
  byteAt shaKData (4 * t + 3) ++ byteAt shaKData (4 * t + 2) ++
    byteAt shaKData (4 * t + 1) ++ byteAt shaKData (4 * t)

theorem shaKWordAt_eq : ∀ t : Fin 64, shaKWordAt t.val = Sha256.k[t.val]! := by decide +kernel

theorem shaK_words {M : Word → BitVec 8} (hk : CodeIn M (BitVec.ofNat 32 shaKAddress) shaKData) :
    ∀ t, t < 64 → memLoad32 M (BitVec.ofNat 32 shaKAddress + BitVec.ofNat 32 (4 * t)) = ktAt t := by
  intro t ht
  rw [ktAt_def, ← shaKWordAt_eq ⟨t, ht⟩]
  unfold memLoad32 shaKWordAt
  have hlen : shaKData.length = 256 := rfl
  have b0 := hk (4 * t) (by omega)
  have b1 : M (BitVec.ofNat 32 shaKAddress + BitVec.ofNat 32 (4 * t) + 1) = byteAt shaKData (4 * t + 1) := by
    rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]; exact hk _ (by omega)
  have b2 : M (BitVec.ofNat 32 shaKAddress + BitVec.ofNat 32 (4 * t) + 2) = byteAt shaKData (4 * t + 2) := by
    rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc]; exact hk _ (by omega)
  have b3 : M (BitVec.ofNat 32 shaKAddress + BitVec.ofNat 32 (4 * t) + 3) = byteAt shaKData (4 * t + 3) := by
    rw [show (3 : Word) = BitVec.ofNat 32 3 from rfl, add_ofNat_assoc]; exact hk _ (by omega)
  rw [b3, b2, b1, b0]

/-! ## Environment and decoded windows for `compress256` -/

/-- Where `sha2::sha256::compress256` runs: its code at `P`, the slice-index
helper and `OUTLINED_FUNCTION_97` where the image puts them, the round
constants at `shaKAddress`, the 32-byte state at `stp`, `n` 64-byte blocks at
`bp` without wrapping, and the 0xE0-byte stack frame below `sp0` and `stp`
apart from code, constants, and blocks. -/
structure SCEnv (M : Word → BitVec 8) (P sp0 stp bp : Word) (n : Nat) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P sha256CompressCode
  idx : CodeIn M (P + 0x2B94) shaIndexCode
  o97 : CodeIn M (P + 0xC09C) shaSigma1PartCode
  kdata : CodeIn M (BitVec.ofNat 32 shaKAddress) shaKData
  hsp : sp0.toNat % 4 = 0
  hS : 0xE0 ≤ sp0.toNat
  hstp : stp.toNat % 4 = 0
  hwbp : bp.toNat + 64 * n < 2 ^ 32
  sC : Sep (sp0 + 0xFFFFFF20) 0xE0 P sha256CompressCode.length
  sI : Sep (sp0 + 0xFFFFFF20) 0xE0 (P + 0x2B94) shaIndexCode.length
  s97 : Sep (sp0 + 0xFFFFFF20) 0xE0 (P + 0xC09C) shaSigma1PartCode.length
  sK : Sep (sp0 + 0xFFFFFF20) 0xE0 (BitVec.ofNat 32 shaKAddress) 256
  stC : Sep stp 32 P sha256CompressCode.length
  stI : Sep stp 32 (P + 0x2B94) shaIndexCode.length
  st97 : Sep stp 32 (P + 0xC09C) shaSigma1PartCode.length
  stK : Sep stp 32 (BitVec.ofNat 32 shaKAddress) 256
  stF : Sep stp 32 (sp0 + 0xFFFFFF20) 0xE0
  bF : Sep bp (64 * n) (sp0 + 0xFFFFFF20) 0xE0
  bSt : Sep bp (64 * n) stp 32

def shaHead : List Nat :=
  [0x15, 0x71, 0x86, 0xcf, 0xa2, 0xcd, 0xa6, 0xcb, 0xca, 0xc9, 0xce, 0xc7, 0xd2, 0xc5, 0xd6, 0xc3,
   0xda, 0xc1, 0x5e, 0xdf, 0x62, 0xdd, 0x66, 0xdb, 0x6a, 0xd9, 0x6e, 0xd7, 0xae, 0x84, 0x03, 0x2c,
   0x05, 0x00, 0x83, 0x2a, 0x45, 0x00, 0x83, 0x2c, 0x85, 0x00, 0x03, 0x2d, 0xc5, 0x00, 0x03, 0x29,
   0x05, 0x01, 0x83, 0x2d, 0x45, 0x01, 0x03, 0x2b, 0x85, 0x01, 0x2a, 0xc6, 0x83, 0x2b, 0xc5, 0x01,
   0x1a, 0x06, 0x2e, 0x96, 0x32, 0xc8, 0x8d, 0x49, 0x13, 0x0a, 0xc1, 0x06, 0x42, 0x45, 0x63, 0x94,
   0xa4, 0x00, 0x6f, 0x20, 0x70, 0x31, 0x01, 0x44, 0x13, 0x85, 0x04, 0x04, 0xaa, 0xc0, 0x13, 0x05,
   0x04, 0xfc, 0x21, 0xc1, 0x13, 0x06, 0x00, 0x04, 0x22, 0x85, 0xa6, 0x85, 0x97, 0x30, 0x00, 0x00,
   0xe7, 0x80, 0x80, 0xb2, 0x63, 0xe4, 0xb9, 0x00, 0x6f, 0x20, 0xf0, 0x30, 0x83, 0x45, 0x25, 0x00,
   0x03, 0x46, 0x05, 0x00, 0x83, 0x46, 0x15, 0x00, 0x03, 0x45, 0x35, 0x00, 0xa2, 0x05, 0xc2, 0x06,
   0x62, 0x06, 0x4d, 0x8d, 0x55, 0x8e, 0x51, 0x8d, 0xb3, 0x05, 0x8a, 0x00, 0x88, 0xc1, 0x11, 0x04,
   0x7d, 0xbf]

theorem sh_at_0 : fetchRel shaHead 0x0 = some (.aluImm .add sp sp 0xFFFFFF20, 2) := by decide
theorem sh_at_2 : fetchRel shaHead 0x2 = some (.store .sw sp ra 0xDC, 2) := by decide
theorem sh_at_4 : fetchRel shaHead 0x4 = some (.store .sw sp (8 : Fin 32) 0xD8, 2) := by decide
theorem sh_at_6 : fetchRel shaHead 0x6 = some (.store .sw sp (9 : Fin 32) 0xD4, 2) := by decide
theorem sh_at_8 : fetchRel shaHead 0x8 = some (.store .sw sp (18 : Fin 32) 0xD0, 2) := by decide
theorem sh_at_a : fetchRel shaHead 0xA = some (.store .sw sp (19 : Fin 32) 0xCC, 2) := by decide
theorem sh_at_c : fetchRel shaHead 0xC = some (.store .sw sp (20 : Fin 32) 0xC8, 2) := by decide
theorem sh_at_e : fetchRel shaHead 0xE = some (.store .sw sp (21 : Fin 32) 0xC4, 2) := by decide
theorem sh_at_10 : fetchRel shaHead 0x10 = some (.store .sw sp (22 : Fin 32) 0xC0, 2) := by decide
theorem sh_at_12 : fetchRel shaHead 0x12 = some (.store .sw sp (23 : Fin 32) 0xBC, 2) := by decide
theorem sh_at_14 : fetchRel shaHead 0x14 = some (.store .sw sp (24 : Fin 32) 0xB8, 2) := by decide
theorem sh_at_16 : fetchRel shaHead 0x16 = some (.store .sw sp (25 : Fin 32) 0xB4, 2) := by decide
theorem sh_at_18 : fetchRel shaHead 0x18 = some (.store .sw sp (26 : Fin 32) 0xB0, 2) := by decide
theorem sh_at_1a : fetchRel shaHead 0x1A = some (.store .sw sp (27 : Fin 32) 0xAC, 2) := by decide
theorem sh_at_1c : fetchRel shaHead 0x1C = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem sh_at_1e : fetchRel shaHead 0x1E = some (.load .lw (24 : Fin 32) a0 0x0, 4) := by decide
theorem sh_at_22 : fetchRel shaHead 0x22 = some (.load .lw (21 : Fin 32) a0 0x4, 4) := by decide
theorem sh_at_26 : fetchRel shaHead 0x26 = some (.load .lw (25 : Fin 32) a0 0x8, 4) := by decide
theorem sh_at_2a : fetchRel shaHead 0x2A = some (.load .lw (26 : Fin 32) a0 0xC, 4) := by decide
theorem sh_at_2e : fetchRel shaHead 0x2E = some (.load .lw (18 : Fin 32) a0 0x10, 4) := by decide
theorem sh_at_32 : fetchRel shaHead 0x32 = some (.load .lw (27 : Fin 32) a0 0x14, 4) := by decide
theorem sh_at_36 : fetchRel shaHead 0x36 = some (.load .lw (22 : Fin 32) a0 0x18, 4) := by decide
theorem sh_at_3a : fetchRel shaHead 0x3A = some (.store .sw sp a0 0xC, 2) := by decide
theorem sh_at_3c : fetchRel shaHead 0x3C = some (.load .lw (23 : Fin 32) a0 0x1C, 4) := by decide
theorem sh_at_40 : fetchRel shaHead 0x40 = some (.aluImm .sll a2 a2 0x6, 2) := by decide
theorem sh_at_42 : fetchRel shaHead 0x42 = some (.alu .add a2 a2 a1, 2) := by decide
theorem sh_at_44 : fetchRel shaHead 0x44 = some (.store .sw sp a2 0x10, 2) := by decide
theorem sh_at_46 : fetchRel shaHead 0x46 = some (.aluImm .add (19 : Fin 32) x0 0x3, 2) := by decide
theorem sh_at_48 : fetchRel shaHead 0x48 = some (.aluImm .add (20 : Fin 32) sp 0x6C, 4) := by decide
theorem sh_at_4c : fetchRel shaHead 0x4C = some (.load .lw a0 sp 0x10, 2) := by decide
theorem sh_at_4e : fetchRel shaHead 0x4E = some (.branch .bne (9 : Fin 32) a0 0x8, 4) := by decide
theorem sh_at_52 : fetchRel shaHead 0x52 = some (.jal x0 0x2B16, 4) := by decide
theorem sh_at_56 : fetchRel shaHead 0x56 = some (.aluImm .add (8 : Fin 32) x0 0x0, 2) := by decide
theorem sh_at_58 : fetchRel shaHead 0x58 = some (.aluImm .add a0 (9 : Fin 32) 0x40, 4) := by decide
theorem sh_at_5c : fetchRel shaHead 0x5C = some (.store .sw sp a0 0x40, 2) := by decide
theorem sh_at_5e : fetchRel shaHead 0x5E = some (.aluImm .add a0 (8 : Fin 32) 0xFFFFFFC0, 4) := by decide
theorem sh_at_62 : fetchRel shaHead 0x62 = some (.branch .beq a0 x0 0x40, 2) := by decide
theorem sh_at_64 : fetchRel shaHead 0x64 = some (.aluImm .add a2 x0 0x40, 4) := by decide
theorem sh_at_68 : fetchRel shaHead 0x68 = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem sh_at_6a : fetchRel shaHead 0x6A = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem sh_at_6c : fetchRel shaHead 0x6C = some (.auipc ra 0x3000, 4) := by decide
theorem sh_at_70 : fetchRel shaHead 0x70 = some (.jalr ra ra 0xFFFFFB28, 4) := by decide
theorem sh_at_74 : fetchRel shaHead 0x74 = some (.branch .bltu (19 : Fin 32) a1 0x8, 4) := by decide
theorem sh_at_78 : fetchRel shaHead 0x78 = some (.jal x0 0x2B0E, 4) := by decide
theorem sh_at_7c : fetchRel shaHead 0x7C = some (.load .lbu a1 a0 0x2, 4) := by decide
theorem sh_at_80 : fetchRel shaHead 0x80 = some (.load .lbu a2 a0 0x0, 4) := by decide
theorem sh_at_84 : fetchRel shaHead 0x84 = some (.load .lbu a3 a0 0x1, 4) := by decide
theorem sh_at_88 : fetchRel shaHead 0x88 = some (.load .lbu a0 a0 0x3, 4) := by decide
theorem sh_at_8c : fetchRel shaHead 0x8C = some (.aluImm .sll a1 a1 0x8, 2) := by decide
theorem sh_at_8e : fetchRel shaHead 0x8E = some (.aluImm .sll a3 a3 0x10, 2) := by decide
theorem sh_at_90 : fetchRel shaHead 0x90 = some (.aluImm .sll a2 a2 0x18, 2) := by decide
theorem sh_at_92 : fetchRel shaHead 0x92 = some (.alu .or a0 a0 a1, 2) := by decide
theorem sh_at_94 : fetchRel shaHead 0x94 = some (.alu .or a2 a2 a3, 2) := by decide
theorem sh_at_96 : fetchRel shaHead 0x96 = some (.alu .or a0 a0 a2, 2) := by decide
theorem sh_at_98 : fetchRel shaHead 0x98 = some (.alu .add a1 (20 : Fin 32) (8 : Fin 32), 4) := by decide
theorem sh_at_9c : fetchRel shaHead 0x9C = some (.store .sw a1 a0 0x0, 2) := by decide
theorem sh_at_9e : fetchRel shaHead 0x9E = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem sh_at_a0 : fetchRel shaHead 0xA0 = some (.jal x0 0xFFFFFFBE, 2) := by decide

def shaTail : List Nat :=
  [0x6f, 0xd0, 0x8f, 0xce, 0xfe, 0x40, 0x6e, 0x44, 0xde, 0x44, 0x4e, 0x49, 0xbe, 0x49, 0x2e, 0x4a,
   0x9e, 0x4a, 0x0e, 0x4b, 0xfa, 0x5b, 0x6a, 0x5c, 0xda, 0x5c, 0x4a, 0x5d, 0xba, 0x5d, 0x2d, 0x61,
   0x82, 0x80]

theorem st_at_0 : fetchRel shaTail 0x0 = some (.jal x0 0xFFFFD4E8, 4) := by decide
theorem st_at_4 : fetchRel shaTail 0x4 = some (.load .lw ra sp 0xDC, 2) := by decide
theorem st_at_6 : fetchRel shaTail 0x6 = some (.load .lw (8 : Fin 32) sp 0xD8, 2) := by decide
theorem st_at_8 : fetchRel shaTail 0x8 = some (.load .lw (9 : Fin 32) sp 0xD4, 2) := by decide
theorem st_at_a : fetchRel shaTail 0xA = some (.load .lw (18 : Fin 32) sp 0xD0, 2) := by decide
theorem st_at_c : fetchRel shaTail 0xC = some (.load .lw (19 : Fin 32) sp 0xCC, 2) := by decide
theorem st_at_e : fetchRel shaTail 0xE = some (.load .lw (20 : Fin 32) sp 0xC8, 2) := by decide
theorem st_at_10 : fetchRel shaTail 0x10 = some (.load .lw (21 : Fin 32) sp 0xC4, 2) := by decide
theorem st_at_12 : fetchRel shaTail 0x12 = some (.load .lw (22 : Fin 32) sp 0xC0, 2) := by decide
theorem st_at_14 : fetchRel shaTail 0x14 = some (.load .lw (23 : Fin 32) sp 0xBC, 2) := by decide
theorem st_at_16 : fetchRel shaTail 0x16 = some (.load .lw (24 : Fin 32) sp 0xB8, 2) := by decide
theorem st_at_18 : fetchRel shaTail 0x18 = some (.load .lw (25 : Fin 32) sp 0xB4, 2) := by decide
theorem st_at_1a : fetchRel shaTail 0x1A = some (.load .lw (26 : Fin 32) sp 0xB0, 2) := by decide
theorem st_at_1c : fetchRel shaTail 0x1C = some (.load .lw (27 : Fin 32) sp 0xAC, 2) := by decide
theorem st_at_1e : fetchRel shaTail 0x1E = some (.aluImm .add sp sp 0xE0, 2) := by decide
theorem st_at_20 : fetchRel shaTail 0x20 = some (.jalr x0 ra 0x0, 2) := by decide

theorem sx_at_0 : fetchRel shaIndexCode 0x0 = some (.branch .bltu a2 a0 0xC, 4) := by decide
theorem sx_at_4 : fetchRel shaIndexCode 0x4 = some (.alu .sub a2 a2 a0, 2) := by decide
theorem sx_at_6 : fetchRel shaIndexCode 0x6 = some (.alu .add a0 a0 a1, 2) := by decide
theorem sx_at_8 : fetchRel shaIndexCode 0x8 = some (.alu .add a1 x0 a2, 2) := by decide
theorem sx_at_a : fetchRel shaIndexCode 0xA = some (.jalr x0 ra 0x0, 2) := by decide

/-! ## Slice indexing helper `shaIndexCode` -/

theorem shaIndex_ok {B cur retAddr : Word} {off : Nat} {m : Machine}
    (hc : CodeIn m.mem B shaIndexCode) (hpc : m.pc = B) (hoff : off ≤ 0x40)
    (ha0 : reg m a0 = BitVec.ofNat 32 off) (ha1 : reg m a1 = cur) (ha2 : reg m a2 = 0x40)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = m.mem ∧
      reg m' a0 = cur + BitVec.ofNat 32 off ∧ reg m' a1 = BitVec.ofNat 32 (0x40 - off) ∧
      reg m' a2 = BitVec.ofNat 32 (0x40 - off) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m' q = reg m q := by
  have s0 : St m.mem B m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hnb : branchTaken .bltu (reg m a2) (reg m a0) = false := by
    unfold branchTaken; rw [ha2, ha0]
    simp only [BitVec.ult, BitVec.toNat_ofNat]
    have h64 : (0x40 : Word).toNat = 64 := rfl
    have ho : off % 2 ^ 32 = off := Nat.mod_eq_of_lt (by omega)
    rw [h64, ho]; exact decide_eq_false (by omega)
  obtain ⟨m1, d1, u1⟩ := s0.notTaken hc 4 sx_at_0 (by decide) hnb
  obtain ⟨m2, d2, u2⟩ := u1.alu hc sx_at_4 (off' := 6) (by decide)
  obtain ⟨m3, d3, u3⟩ := u2.alu hc sx_at_6 (off' := 8) (by decide)
  obtain ⟨m4, d4, u4⟩ := u3.alu hc sx_at_8 (off' := 0xA) (by decide)
  obtain ⟨m5, d5, pc5, mem5, regs5⟩ := u4.jalr hc sx_at_a
  have sub_eq : (0x40 : Word) - BitVec.ofNat 32 off = BitVec.ofNat 32 (0x40 - off) := by
    apply BitVec.eq_of_toNat_eq
    have h64 : (0x40 : Word).toNat = 64 := rfl
    rw [BitVec.toNat_sub, h64, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  refine ⟨m5, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5)))), ?_, mem5, ?_, ?_, ?_, ?_⟩
  · rw [pc5]; simp +decide only [upd, ↓reduceIte]; rw [add_lit_zero, hra, hret]
  · rw [regs5]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [ha0, ha1, BitVec.add_comm]
  · rw [regs5]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [ha2, ha0, sub_eq]; exact BitVec.zero_add _
  · rw [regs5]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [ha2, ha0, sub_eq]
  · intro q q0 q1 q2
    rw [regs5]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, s0.zero]
    · simp only [upd, h0, q0, q1, q2, ite_false]

end C3.RV32
