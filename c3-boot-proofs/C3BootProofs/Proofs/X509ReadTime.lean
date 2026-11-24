import C3BootProofs.Proofs.GeneralizedTime
import C3BootProofs.Proofs.ListsOid
import C3BootProofs.Proofs.DerOid
import C3BootProofs.Spec.X509

/-!
# `x509::read_time`, as compiled

`c3_verify::x509::read_time` peeks at the tag of the next element. For a
`GeneralizedTime` it reads the element with `Der::tlv` and tail-calls
`generalized_time` on its content. For a `UTCTime` it reads the element and
runs `utc_time` inlined: `digits::<2>` for the year, the 1950 to 2049
window, `date_time`, and a lone `Z`. `x509ReadTime_correct` matches it to
`Spec.X509`'s `readTime`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem xrt_at_0 : fetchRel x509ReadTimeCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem xrt_at_2 : fetchRel x509ReadTimeCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem xrt_at_4 : fetchRel x509ReadTimeCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem xrt_at_6 : fetchRel x509ReadTimeCode 0x6 = some (.load .lw a2 a1 0xC, 2) := by decide
theorem xrt_at_8 : fetchRel x509ReadTimeCode 0x8 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem xrt_at_a : fetchRel x509ReadTimeCode 0xA = some (.branch .beq a2 x0 0x34, 2) := by decide
theorem xrt_at_c : fetchRel x509ReadTimeCode 0xC = some (.load .lw a0 a1 0x8, 2) := by decide
theorem xrt_at_e : fetchRel x509ReadTimeCode 0xE = some (.load .lbu a0 a0 0x0, 4) := by decide
theorem xrt_at_12 : fetchRel x509ReadTimeCode 0x12 = some (.aluImm .add a2 x0 0x17, 2) := by decide
theorem xrt_at_14 : fetchRel x509ReadTimeCode 0x14 = some (.branch .beq a0 a2 0x2E, 4) := by decide
theorem xrt_at_18 : fetchRel x509ReadTimeCode 0x18 = some (.aluImm .add a2 x0 0x18, 2) := by decide
theorem xrt_at_1a : fetchRel x509ReadTimeCode 0x1A = some (.branch .bne a0 a2 0x54, 4) := by decide
theorem xrt_at_1e : fetchRel x509ReadTimeCode 0x1E = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem xrt_at_20 : fetchRel x509ReadTimeCode 0x20 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem xrt_at_24 : fetchRel x509ReadTimeCode 0x24 = some (.jalr ra ra 0x1BE, 4) := by decide
theorem xrt_at_28 : fetchRel x509ReadTimeCode 0x28 = some (.load .lw a1 sp 0x8, 2) := by decide
theorem xrt_at_2a : fetchRel x509ReadTimeCode 0x2A = some (.branch .beq a1 x0 0x50, 2) := by decide
theorem xrt_at_2c : fetchRel x509ReadTimeCode 0x2C = some (.load .lw a2 sp 0xC, 2) := by decide
theorem xrt_at_2e : fetchRel x509ReadTimeCode 0x2E = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem xrt_at_30 : fetchRel x509ReadTimeCode 0x30 = some (.load .lw ra sp 0x2C, 2) := by decide
theorem xrt_at_32 : fetchRel x509ReadTimeCode 0x32 = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem xrt_at_34 : fetchRel x509ReadTimeCode 0x34 = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem xrt_at_36 : fetchRel x509ReadTimeCode 0x36 = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem xrt_at_3a : fetchRel x509ReadTimeCode 0x3A = some (.jalr x0 (6 : Fin 32) 0xFFFFFB92, 4) := by decide
theorem xrt_at_3e : fetchRel x509ReadTimeCode 0x3E = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem xrt_at_40 : fetchRel x509ReadTimeCode 0x40 = some (.jal x0 0x34, 2) := by decide
theorem xrt_at_42 : fetchRel x509ReadTimeCode 0x42 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem xrt_at_44 : fetchRel x509ReadTimeCode 0x44 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem xrt_at_48 : fetchRel x509ReadTimeCode 0x48 = some (.jalr ra ra 0x19A, 4) := by decide
theorem xrt_at_4c : fetchRel x509ReadTimeCode 0x4C = some (.load .lw a0 sp 0x8, 2) := by decide
theorem xrt_at_4e : fetchRel x509ReadTimeCode 0x4E = some (.branch .beq a0 x0 0x2C, 2) := by decide
theorem xrt_at_50 : fetchRel x509ReadTimeCode 0x50 = some (.load .lw a1 sp 0xC, 2) := by decide
theorem xrt_at_52 : fetchRel x509ReadTimeCode 0x52 = some (.store .sw sp a0 0x20, 2) := by decide
theorem xrt_at_54 : fetchRel x509ReadTimeCode 0x54 = some (.store .sw sp a1 0x24, 2) := by decide
theorem xrt_at_56 : fetchRel x509ReadTimeCode 0x56 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem xrt_at_58 : fetchRel x509ReadTimeCode 0x58 = some (.aluImm .add a1 sp 0x20, 2) := by decide
theorem xrt_at_5a : fetchRel x509ReadTimeCode 0x5A = some (.auipc ra 0x0, 4) := by decide
theorem xrt_at_5e : fetchRel x509ReadTimeCode 0x5E = some (.jalr ra ra 0xFFFFFEE0, 4) := by decide
theorem xrt_at_62 : fetchRel x509ReadTimeCode 0x62 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem xrt_at_66 : fetchRel x509ReadTimeCode 0x66 = some (.branch .beq a0 x0 0x24, 2) := by decide
theorem xrt_at_68 : fetchRel x509ReadTimeCode 0x68 = some (.load .lbu a0 sp 0x9, 4) := by decide
theorem xrt_at_6c : fetchRel x509ReadTimeCode 0x6C = some (.jal x0 0x3A, 2) := by decide
theorem xrt_at_6e : fetchRel x509ReadTimeCode 0x6E = some (.lui a0 0x1000, 2) := by decide
theorem xrt_at_70 : fetchRel x509ReadTimeCode 0x70 = some (.aluImm .add a0 a0 0x401, 4) := by decide
theorem xrt_at_74 : fetchRel x509ReadTimeCode 0x74 = some (.store .sh (8 : Fin 32) a0 0x0, 4) := by decide
theorem xrt_at_78 : fetchRel x509ReadTimeCode 0x78 = some (.jal x0 0x38, 2) := by decide
theorem xrt_at_7a : fetchRel x509ReadTimeCode 0x7A = some (.load .lbu a0 sp 0xC, 4) := by decide
theorem xrt_at_7e : fetchRel x509ReadTimeCode 0x7E = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem xrt_at_80 : fetchRel x509ReadTimeCode 0x80 = some (.store .sb (8 : Fin 32) a1 0x0, 4) := by decide
theorem xrt_at_84 : fetchRel x509ReadTimeCode 0x84 = some (.store .sb (8 : Fin 32) a0 0x1, 4) := by decide
theorem xrt_at_88 : fetchRel x509ReadTimeCode 0x88 = some (.jal x0 0x28, 2) := by decide
theorem xrt_at_8a : fetchRel x509ReadTimeCode 0x8A = some (.load .lw a1 sp 0xC, 2) := by decide
theorem xrt_at_8c : fetchRel x509ReadTimeCode 0x8C = some (.aluImm .add a0 x0 0x31, 4) := by decide
theorem xrt_at_90 : fetchRel x509ReadTimeCode 0x90 = some (.branch .bltu a0 a1 0xA, 4) := by decide
theorem xrt_at_94 : fetchRel x509ReadTimeCode 0x94 = some (.aluImm .add a0 x0 0x7D0, 4) := by decide
theorem xrt_at_98 : fetchRel x509ReadTimeCode 0x98 = some (.jal x0 0x6, 2) := by decide
theorem xrt_at_9a : fetchRel x509ReadTimeCode 0x9A = some (.aluImm .add a0 x0 0x76C, 4) := by decide
theorem xrt_at_9e : fetchRel x509ReadTimeCode 0x9E = some (.alu .add a1 a1 a0, 2) := by decide
theorem xrt_at_a0 : fetchRel x509ReadTimeCode 0xA0 = some (.branch .bgeu a1 a0 0x18, 4) := by decide
theorem xrt_at_a4 : fetchRel x509ReadTimeCode 0xA4 = some (.aluImm .add a0 x0 0x6, 2) := by decide
theorem xrt_at_a6 : fetchRel x509ReadTimeCode 0xA6 = some (.store .sb (8 : Fin 32) a0 0x1, 4) := by decide
theorem xrt_at_aa : fetchRel x509ReadTimeCode 0xAA = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem xrt_at_ac : fetchRel x509ReadTimeCode 0xAC = some (.store .sb (8 : Fin 32) a0 0x0, 4) := by decide
theorem xrt_at_b0 : fetchRel x509ReadTimeCode 0xB0 = some (.load .lw ra sp 0x2C, 2) := by decide
theorem xrt_at_b2 : fetchRel x509ReadTimeCode 0xB2 = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem xrt_at_b4 : fetchRel x509ReadTimeCode 0xB4 = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem xrt_at_b6 : fetchRel x509ReadTimeCode 0xB6 = some (.jalr x0 ra 0x0, 2) := by decide
theorem xrt_at_b8 : fetchRel x509ReadTimeCode 0xB8 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem xrt_at_ba : fetchRel x509ReadTimeCode 0xBA = some (.aluImm .add a2 sp 0x20, 2) := by decide
theorem xrt_at_bc : fetchRel x509ReadTimeCode 0xBC = some (.auipc ra 0x0, 4) := by decide
theorem xrt_at_c0 : fetchRel x509ReadTimeCode 0xC0 = some (.jalr ra ra 0xFFFFFC62, 4) := by decide
theorem xrt_at_c4 : fetchRel x509ReadTimeCode 0xC4 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem xrt_at_c8 : fetchRel x509ReadTimeCode 0xC8 = some (.branch .bne a0 x0 0xFFFFFFA0, 2) := by decide
theorem xrt_at_ca : fetchRel x509ReadTimeCode 0xCA = some (.load .lw a1 sp 0x24, 2) := by decide
theorem xrt_at_cc : fetchRel x509ReadTimeCode 0xCC = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem xrt_at_ce : fetchRel x509ReadTimeCode 0xCE = some (.aluImm .add a0 x0 0x19, 2) := by decide
theorem xrt_at_d0 : fetchRel x509ReadTimeCode 0xD0 = some (.branch .bne a1 a2 0xFFFFFFD6, 4) := by decide
theorem xrt_at_d4 : fetchRel x509ReadTimeCode 0xD4 = some (.load .lw a1 sp 0x20, 2) := by decide
theorem xrt_at_d6 : fetchRel x509ReadTimeCode 0xD6 = some (.load .lbu a1 a1 0x0, 4) := by decide
theorem xrt_at_da : fetchRel x509ReadTimeCode 0xDA = some (.aluImm .add a1 a1 0xFFFFFFA6, 4) := by decide
theorem xrt_at_de : fetchRel x509ReadTimeCode 0xDE = some (.branch .bne a1 x0 0xFFFFFFC8, 2) := by decide
theorem xrt_at_e0 : fetchRel x509ReadTimeCode 0xE0 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem xrt_at_e2 : fetchRel x509ReadTimeCode 0xE2 = some (.load .lw a1 sp 0x10, 2) := by decide
theorem xrt_at_e4 : fetchRel x509ReadTimeCode 0xE4 = some (.load .lw a2 sp 0x14, 2) := by decide
theorem xrt_at_e6 : fetchRel x509ReadTimeCode 0xE6 = some (.store .sw (8 : Fin 32) a1 0x8, 2) := by decide
theorem xrt_at_e8 : fetchRel x509ReadTimeCode 0xE8 = some (.store .sw (8 : Fin 32) a2 0xC, 2) := by decide
theorem xrt_at_ea : fetchRel x509ReadTimeCode 0xEA = some (.jal x0 0xFFFFFFC2, 2) := by decide
end

abbrev XRT : Word := BitVec.ofNat 32 x509ReadTimeAddress
abbrev TLV : Word := BitVec.ofNat 32 derTlvAddress

abbrev xrtPs : List (Fin 32 × Word) := [(ra, 0x2C), ((8 : Fin 32), 0x28)]

def xrtA : List BInstr :=
  [.lw a2 a1 0xC, .alu .add (8 : Fin 32) x0 a0]
def xrtB : List BInstr :=
  [.lw a0 a1 0x8, .lbu a0 a0 0x0, .aluImm .add a2 x0 0x17]
def xrtU1 : List BInstr :=
  [.lw a1 sp 0xC, .sw sp a0 0x20, .sw sp a1 0x24, .aluImm .add a0 sp 0x8, .aluImm .add a1 sp 0x20]
def xrtU2 : List BInstr :=
  [.aluImm .add a0 sp 0x8, .aluImm .add a2 sp 0x20]
def xrtU3 : List BInstr :=
  [.lw a1 sp 0x24, .aluImm .add a2 x0 0x1, .aluImm .add a0 x0 0x19]
def xrtU4 : List BInstr :=
  [.lw a1 sp 0x20, .lbu a1 a1 0x0, .aluImm .add a1 a1 0xFFFFFFA6]
def xrtU5 : List BInstr :=
  [.aluImm .add a0 x0 0x0, .lw a1 sp 0x10, .lw a2 sp 0x14, .sw (8 : Fin 32) a1 0x8, .sw (8 : Fin 32) a2 0xC]
def xrtE7A : List BInstr :=
  [.lbu a0 sp 0xC, .aluImm .add a1 x0 0x1, .sb (8 : Fin 32) a1 0x0, .sb (8 : Fin 32) a0 0x1]
def xrtEA6 : List BInstr :=
  [.sb (8 : Fin 32) a0 0x1, .aluImm .add a0 x0 0x1]
def xrtT : List BInstr :=
  [.lw a2 sp 0xC, .alu .add a0 x0 (8 : Fin 32), .lw ra sp 0x2C, .lw (8 : Fin 32) sp 0x28, .aluImm .add sp sp 0x30]

section
set_option maxRecDepth 20000
theorem xrtA_end : blockEnd x509ReadTimeCode 0x6 xrtA = some 0xA := by decide
theorem xrtB_end : blockEnd x509ReadTimeCode 0xC xrtB = some 0x14 := by decide
theorem xrtU1_end : blockEnd x509ReadTimeCode 0x50 xrtU1 = some 0x5A := by decide
theorem xrtU2_end : blockEnd x509ReadTimeCode 0xB8 xrtU2 = some 0xBC := by decide
theorem xrtU3_end : blockEnd x509ReadTimeCode 0xCA xrtU3 = some 0xD0 := by decide
theorem xrtU4_end : blockEnd x509ReadTimeCode 0xD4 xrtU4 = some 0xDE := by decide
theorem xrtU5_end : blockEnd x509ReadTimeCode 0xE0 xrtU5 = some 0xEA := by decide
theorem xrtE7A_end : blockEnd x509ReadTimeCode 0x7A xrtE7A = some 0x88 := by decide
theorem xrtEA6_end : blockEnd x509ReadTimeCode 0xA6 xrtEA6 = some 0xAC := by decide
theorem xrtT_end : blockEnd x509ReadTimeCode 0x2C xrtT = some 0x36 := by decide
theorem xrtSave_end : blockEnd x509ReadTimeCode 2 (saveBlock xrtPs) = some 0x6 := by decide
theorem xrtRestore_end : blockEnd x509ReadTimeCode 0xB0 (restoreBlock xrtPs) = some 0xB4 := by decide
end

theorem derTlv_tag {b : Nat} {L : Bytes} {t : DerTlv} (h : derTlv (b :: L) = .ok t) : t.tag = b := by
  match L with
  | [] =>
    simp only [derTlv] at h
    by_cases h1 : b % 32 = 31
    · simp only [h1, ↓reduceIte] at h; cases h
    · simp only [h1, ↓reduceIte] at h; cases h
  | first :: afterLen =>
    simp only [derTlv] at h
    by_cases h1 : b % 32 = 31
    · simp only [h1, ↓reduceIte] at h; cases h
    simp only [h1, ↓reduceIte] at h
    by_cases h2 : first < 0x80
    · simp only [h2, ↓reduceIte] at h
      by_cases h3 : afterLen.length < first
      · simp only [h3, ↓reduceIte] at h; cases h
      · simp only [h3, ↓reduceIte] at h; cases h; rfl
    simp only [h2, ↓reduceIte] at h
    by_cases h3 : first % 128 = 0 ∨ 4 < first % 128
    · simp only [h3, ↓reduceIte] at h; cases h
    simp only [h3, ↓reduceIte] at h
    clear h3
    by_cases h4 : afterLen.length < first % 128
    · simp only [h4, ↓reduceIte] at h; cases h
    simp only [h4, ↓reduceIte] at h
    by_cases h5 : afterLen.head? = some 0
    · simp only [h5, ↓reduceIte] at h; cases h
    simp only [h5, ↓reduceIte] at h
    cases hl : derLongLen 0 (afterLen.take (first % 128)) with
    | error e => simp only [hl] at h; cases h
    | ok len =>
      simp only [hl] at h
      by_cases h6 : len < 0x80
      · simp only [h6, ↓reduceIte] at h; cases h
      simp only [h6, ↓reduceIte] at h
      by_cases h7 : afterLen.length - first % 128 < len
      · simp only [h7, ↓reduceIte] at h; cases h
      · simp only [h7, ↓reduceIte] at h; cases h; rfl

theorem xrt_memBytes_drop (M : Word → BitVec 8) (p : Word) {k n : Nat} (h : k ≤ n) :
    (memBytes M p n).drop k = memBytes M (p + BitVec.ofNat 32 k) (n - k) := by
  have := memBytes_split M p k (n - k)
  rw [show k + (n - k) = n by omega] at this
  rw [this, List.drop_left' (memBytes_length M p k)]

/-- What `Der::tlv` leaves when it reads an element: the content pointer and
length in its result at `o`, the reader at `d` past the element, and every
other byte as it was. -/
theorem derTlvMem_ok (M : Word → BitVec 8) (o d rp rl : Word) (t : DerTlv) (sOd : Sep o 17 (d + 8) 8) :
    memLoad32 (derTlvMem M o d rp rl (.ok t)) o = rp + BitVec.ofNat 32 t.header ∧
    memLoad32 (derTlvMem M o d rp rl (.ok t)) (o + 4) = BitVec.ofNat 32 t.len ∧
    memLoad32 (derTlvMem M o d rp rl (.ok t)) (d + 8) = rp + BitVec.ofNat 32 (t.header + t.len) ∧
    memLoad32 (derTlvMem M o d rp rl (.ok t)) (d + 0xC) = rl - BitVec.ofNat 32 (t.header + t.len) ∧
    ∀ x, Sep o 17 x 1 → Sep (d + 8) 8 x 1 → derTlvMem M o d rp rl (.ok t) x = M x := by
  have oo : ∀ {c n e k : Nat}, c + n ≤ e ∨ e + k ≤ c → c + n ≤ 17 → e + k ≤ 17 →
      Sep (o + BitVec.ofNat 32 c) n (o + BitVec.ofNat 32 e) k := fun h h1 h2 => sep_offsets o h (by omega) (by omega)
  have od : ∀ {c n e k : Nat}, c + n ≤ 17 → e + k ≤ 8 → Sep (o + BitVec.ofNat 32 c) n (d + 8 + BitVec.ofNat 32 e) k :=
    fun h1 h2 => (sOd.sub h1).subR h2
  have so_10_0 : Sep (o + 0x10) 1 (o) 4 := by
    have := oo (c := 0x10) (n := 1) (e := 0x0) (k := 4) (by omega) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); exact this
  have so_c_0 : Sep (o + 0xC) 4 (o) 4 := by
    have := oo (c := 0xC) (n := 4) (e := 0x0) (k := 4) (by omega) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); exact this
  have so_8_0 : Sep (o + 0x8) 4 (o) 4 := by
    have := oo (c := 0x8) (n := 4) (e := 0x0) (k := 4) (by omega) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); exact this
  have so_4_0 : Sep (o + 0x4) 4 (o) 4 := by
    have := oo (c := 0x4) (n := 4) (e := 0x0) (k := 4) (by omega) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); exact this
  have so_10_4 : Sep (o + 0x10) 1 (o + 0x4) 4 := by
    have := oo (c := 0x10) (n := 1) (e := 0x4) (k := 4) (by omega) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); exact this
  have so_c_4 : Sep (o + 0xC) 4 (o + 0x4) 4 := by
    have := oo (c := 0xC) (n := 4) (e := 0x4) (k := 4) (by omega) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); exact this
  have so_8_4 : Sep (o + 0x8) 4 (o + 0x4) 4 := by
    have := oo (c := 0x8) (n := 4) (e := 0x4) (k := 4) (by omega) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); exact this
  have sd_10_0 : Sep (o + 0x10) 1 (d + 8) 4 := by
    have := od (c := 0x10) (n := 1) (e := 0) (k := 4) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); exact this
  have sd_c_0 : Sep (o + 0xC) 4 (d + 8) 4 := by
    have := od (c := 0xC) (n := 4) (e := 0) (k := 4) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); exact this
  have sd_8_0 : Sep (o + 0x8) 4 (d + 8) 4 := by
    have := od (c := 0x8) (n := 4) (e := 0) (k := 4) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); exact this
  have sd_4_0 : Sep (o + 0x4) 4 (d + 8) 4 := by
    have := od (c := 0x4) (n := 4) (e := 0) (k := 4) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); exact this
  have sd_0_0 : Sep (o) 4 (d + 8) 4 := by
    have := od (c := 0x0) (n := 4) (e := 0) (k := 4) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); exact this
  have sd_10_4 : Sep (o + 0x10) 1 (d + 0xC) 4 := by
    have := od (c := 0x10) (n := 1) (e := 4) (k := 4) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); rw [show d + 8 + BitVec.ofNat 32 4 = d + 0xC by rw [BitVec.add_assoc]; rfl] at this; exact this
  have sd_c_4 : Sep (o + 0xC) 4 (d + 0xC) 4 := by
    have := od (c := 0xC) (n := 4) (e := 4) (k := 4) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); rw [show d + 8 + BitVec.ofNat 32 4 = d + 0xC by rw [BitVec.add_assoc]; rfl] at this; exact this
  have sd_8_4 : Sep (o + 0x8) 4 (d + 0xC) 4 := by
    have := od (c := 0x8) (n := 4) (e := 4) (k := 4) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); rw [show d + 8 + BitVec.ofNat 32 4 = d + 0xC by rw [BitVec.add_assoc]; rfl] at this; exact this
  have sd_4_4 : Sep (o + 0x4) 4 (d + 0xC) 4 := by
    have := od (c := 0x4) (n := 4) (e := 4) (k := 4) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); rw [show d + 8 + BitVec.ofNat 32 4 = d + 0xC by rw [BitVec.add_assoc]; rfl] at this; exact this
  have sd_0_4 : Sep (o) 4 (d + 0xC) 4 := by
    have := od (c := 0x0) (n := 4) (e := 4) (k := 4) (by omega) (by omega)
    (try simp only [add_ofNat_zero] at this); rw [show d + 8 + BitVec.ofNat 32 4 = d + 0xC by rw [BitVec.add_assoc]; rfl] at this; exact this
  have dd : Sep (d + 0xC) 4 (d + 8) 4 := by
    have := sep_offsets (d + 8) (c := 4) (n := 4) (d := 0) (k := 4) (by omega) (by omega) (by omega)
    rw [add_ofNat_zero, show d + 8 + BitVec.ofNat 32 4 = d + 0xC by rw [BitVec.add_assoc]; rfl] at this; exact this
  unfold derTlvMem
  refine ⟨?_, ?_, ?_, ?_, fun x hx hx' => ?_⟩
  · rw [memLoad32_store8_sep so_10_0, memLoad32_store32_sep so_c_0, memLoad32_store32_sep so_8_0,
      memLoad32_store32_sep so_4_0, memLoad32_store32_same]
  · rw [memLoad32_store8_sep so_10_4, memLoad32_store32_sep so_c_4, memLoad32_store32_sep so_8_4,
      memLoad32_store32_same]
  · rw [memLoad32_store8_sep sd_10_0, memLoad32_store32_sep sd_c_0, memLoad32_store32_sep sd_8_0,
      memLoad32_store32_sep sd_4_0, memLoad32_store32_sep sd_0_0, memLoad32_store32_sep dd, memLoad32_store32_same]
  · rw [memLoad32_store8_sep sd_10_4, memLoad32_store32_sep sd_c_4, memLoad32_store32_sep sd_8_4,
      memLoad32_store32_sep sd_4_4, memLoad32_store32_sep sd_0_4, memLoad32_store32_same]
  · have hxo : ∀ {c n : Nat}, c + n ≤ 17 → Sep (o + BitVec.ofNat 32 c) n x 1 := fun h => hx.sub h
    have x10 : Sep (o + 0x10) 1 x 1 := hxo (c := 0x10) (n := 1) (by omega)
    have xC : Sep (o + 0xC) 4 x 1 := hxo (c := 0xC) (n := 4) (by omega)
    have x8 : Sep (o + 8) 4 x 1 := hxo (c := 8) (n := 4) (by omega)
    have x4 : Sep (o + 4) 4 x 1 := hxo (c := 4) (n := 4) (by omega)
    have x0 : Sep o 4 x 1 := by have := hxo (c := 0) (n := 4) (by omega); rwa [add_ofNat_zero] at this
    have xd8 : Sep (d + 8) 4 x 1 := by have := hx'.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
    have xdC : Sep (d + 0xC) 4 x 1 := by
      have := hx'.sub (c := 4) (l := 4) (by omega)
      rwa [show d + 8 + BitVec.ofNat 32 4 = d + 0xC by rw [BitVec.add_assoc]; rfl] at this
    dsimp only
    rw [memStore8_ne (dn_sep1 x10), memStore32_get_sep xC, memStore32_get_sep x8, memStore32_get_sep x4,
      memStore32_get_sep x0, memStore32_get_sep xdC, memStore32_get_sep xd8]

theorem xrt_tag17 : ∀ b : BitVec 8, branchTaken .beq (b.zeroExtend 32) (aluEval .add 0 0x17) = decide (b.toNat = 0x17) := by
  decide
theorem xrt_tag18 : ∀ b : BitVec 8, branchTaken .bne (b.zeroExtend 32) (aluEval .add 0 0x18) = !decide (b.toNat = 0x18) := by
  decide

/-- `readTime` when `Der::tlv` fails. -/
theorem readTime_err {L : Bytes} {e : DerError} (h : derTlv L = .error e) : readTime L = none := by
  unfold readTime readTlv; rw [h]; rfl

/-- `readTime` when `Der::tlv` reads an element of the `n` bytes at `p`. -/
theorem readTime_ok (M : Word → BitVec 8) (p : Word) (n : Nat) {t : DerTlv}
    (h : derTlv (memBytes M p n) = .ok t) :
    readTime (memBytes M p n) =
      (if t.tag = 0x17 then utcTime (memBytes M (p + BitVec.ofNat 32 t.header) t.len)
       else if t.tag = 0x18 then generalizedTime (memBytes M (p + BitVec.ofNat 32 t.header) t.len) else none).map
        fun x => (x, memBytes M (p + BitVec.ofNat 32 (t.header + t.len)) (n - (t.header + t.len))) := by
  have hb := derTlv_bound h
  rw [memBytes_length] at hb
  unfold readTime readTlv
  rw [h]
  dsimp only [DerTlv.content, bind, Option.bind, pure]
  rw [memBytes_drop_take hb, xrt_memBytes_drop M p hb]
  obtain ⟨tg, htg⟩ : ∃ tg, t.tag = tg := ⟨_, rfl⟩
  rw [htg]
  by_cases h17 : tg = 0x17
  · subst h17
    rcases utcTime _ with _ | x <;> rfl
  · by_cases h18 : tg = 0x18
    · subst h18
      rcases generalizedTime _ with _ | x <;> rfl
    · have e17 : (tg == 0x17) = false := beq_eq_false_iff_ne.mpr h17
      have e18 : (tg == 0x18) = false := beq_eq_false_iff_ne.mpr h18
      rw [if_neg h17, if_neg h18]
      simp only [e17, e18, Bool.false_eq_true, ↓reduceIte]; rfl

/-- `utcTime` in steps: the year, the rest of the date and time, and `Z`. -/
theorem utcTime_eq (content : Bytes) :
    utcTime content = (readDigits 2 content).bind fun yr =>
      (readDateTime (yr.1 + if yr.1 ≥ 50 then 1900 else 2000) yr.2).bind fun tr =>
        if tr.2 = [asciiZ] then some tr.1 else none := by
  unfold utcTime
  simp only [bind, Option.bind, require, pure]
  rcases readDigits 2 content with _ | ⟨y, r⟩
  · rfl
  · dsimp only
    rcases readDateTime _ r with _ | ⟨t, r2⟩
    · rfl
    · dsimp only
      by_cases h : r2 = [asciiZ]
      · rw [if_pos h]; subst h; rfl
      · rw [if_neg h]
        have : (r2 == [asciiZ]) = false := beq_eq_false_iff_ne.mpr h
        simp only [this, Bool.false_eq_true, ↓reduceIte]



set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `x509::read_time`**: with a DER reader at `d` over the
`rl` bytes at `rp`, it writes `readTime`'s answer to the `Result<u64, Error>`
at `out`. When `readTime` reads a time `t` with `r` left over, the tag is 0,
`t` is at `out + 8` as two words, and the reader is past the element, over
`r`; when it fails, the tag is 1. It returns with `sp` and the callee-saved
registers restored and writes only `out`, the reader, and the 0x60 bytes of
stack below `sp`. -/
theorem x509ReadTime_correct (m : Machine) {sp0 out d rp retAddr : Word} {rl : Nat}
    (hcR : CodeIn m.mem XRT x509ReadTimeCode) (hcL : CodeIn m.mem TLV derTlvCode)
    (hcG : CodeIn m.mem GNT generalizedTimeCode) (hcD : CodeIn m.mem DT dateTimeCode)
    (hcT : CodeIn m.mem TD timeDigits2Code) (hpc : m.pc = XRT) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hsa : sp0.toNat % 4 = 0) (hsl : 0x60 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (how : out.toNat + 16 ≤ 0x40000000) (hoa : out.toNat % 4 = 0) (hdw : d.toNat + 16 ≤ 0x40000000)
    (hda : d.toNat % 4 = 0) (lp : memLoad32 m.mem (d + 8) = rp) (ln : memLoad32 m.mem (d + 0xC) = BitVec.ofNat 32 rl)
    (hrw : rp.toNat + rl + 14 ≤ 0x40000000) (hr0 : 0 < rp.toNat)
    (sOG : Sep out 16 (sp0 + 0xFFFFFFA0) 0x60) (sDG : Sep (d + 8) 8 (sp0 + 0xFFFFFFA0) 0x60)
    (sOD : Sep out 16 (d + 8) 8) (sPG : Sep rp (rl + 14) (sp0 + 0xFFFFFFA0) 0x60) (sPD : Sep rp rl (d + 8) 8) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ t r, readTime (memBytes m.mem rp rl) = some (t, r) → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
        memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
        memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32) ∧
        ∃ k, k ≤ rl ∧ memLoad32 m'.mem (d + 8) = rp + BitVec.ofNat 32 k ∧
          memLoad32 m'.mem (d + 0xC) = BitVec.ofNat 32 (rl - k) ∧ r = memBytes m.mem (rp + BitVec.ofNat 32 k) (rl - k)) ∧
      (readTime (memBytes m.mem rp rl) = none → m'.mem out = 1) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → Sep out 16 x 1 → Sep (d + 8) 8 x 1 → m'.mem x = m.mem x := by
  obtain ⟨R, hR⟩ : ∃ R, sp0 + 0xFFFFFFA0 = R := ⟨_, rfl⟩
  rw [hR] at sOG sDG sPG ⊢
  have hRn : R.toNat = sp0.toNat - 0x60 := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFFFA0 : Word).toNat = 2 ^ 32 - 0x60 from rfl]; have := sp0.isLt; omega
  have hRc : ∀ c, c ≤ 0x60 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨F, hF⟩ : ∃ F, R + BitVec.ofNat 32 0x30 = F := ⟨_, rfl⟩
  have hFn : F.toNat = R.toNat + 0x30 := by rw [← hF]; exact hRc _ (by decide)
  have hFa : F.toNat % 4 = 0 := by omega
  have eFk : ∀ k, F + BitVec.ofNat 32 k = R + BitVec.ofNat 32 (0x30 + k) := fun k => by rw [← hF, add_ofNat_assoc]
  have eFS : F + 0x30 = sp0 := by
    rw [show (0x30 : Word) = BitVec.ofNat 32 0x30 from rfl, eFk, ← hR, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eF0 : F + 0xFFFFFFD0 = R := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero R
  have offs : ∀ {c n e k : Nat}, c + n ≤ e ∨ e + k ≤ c → c + n ≤ 0x60 → e + k ≤ 0x60 →
      Sep (R + BitVec.ofNat 32 c) n (R + BitVec.ofNat 32 e) k := fun h h1 h2 => sep_offsets R h (by omega) (by omega)
  have inR : ∀ {c l : Nat} {x : Word}, Sep R 0x60 x 1 → c + l ≤ 0x60 → Sep (R + BitVec.ofNat 32 c) l x 1 :=
    fun hx h => (hx.symm.subR h).symm
  have hiR : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep R 0x60 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have hiD : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (d + 8) 8 x 1 := fun x hx =>
    sep_of_le (by rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      (by have := x.isLt; omega)
  have cd : ∀ {M' : Word → BitVec 8} {c : Word} {code : List Nat}, CodeIn m.mem c code → 0x40000000 ≤ c.toNat →
      c.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → M' x = m.mem x) →
      CodeIn M' c code :=
    fun hc h1 h2 hM i hi' => by
      rw [hM _ (hiR _ (dn_code_hi h1 h2 hi')) (hiD _ (dn_code_hi h1 h2 hi'))]; exact hc i hi'
  have hXn : XRT.toNat = (img% x509ReadTimeAddress) := by decide
  have cdX : ∀ {M' : Word → BitVec 8}, (∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → M' x = m.mem x) →
      CodeIn M' XRT x509ReadTimeCode := fun hM => cd hcR (by rw [hXn]; decide) (by rw [hXn]; decide) hM
  have hiC : ∀ {c l : Nat} {a : Word} {len : Nat}, c + l ≤ 0x60 → 0x40000000 ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 →
      Sep (R + BitVec.ofNat 32 c) l a len := fun h h1 h2 => sep_of_le (by rw [hRc _ (by omega)]; omega) h2
  have st0 : St m.mem XRT m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hcR xrt_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0) sp = F := by
    simp +decide only [upd, ↓reduceIte]; rw [hsp, ← hF, ← hR, BitVec.add_assoc]; rfl
  have slotO : ∀ o : Word, F + o = R + BitVec.ofNat 32 (0x30 + o.toNat) := fun o => by rw [← eFk, ofNat_toNat_self]
  have slotC : ∀ o : Word, o.toNat ≤ 0x2C → Sep (F + o) 4 XRT x509ReadTimeCode.length := fun o ho => by
    rw [slotO]; exact hiC (by omega) (by rw [hXn]; decide) (by rw [hXn]; decide)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock xrtPs) u1 hcR xrtSave_end (saveBlock_ok _ xrtPs _ fun q hq => by
      rw [sp1]
      simp only [xrtPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl <;> exact ⟨aligned_add hFa (by decide), slotC _ (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) xrtPs = Ms :=
    ⟨_, rfl⟩
  rw [hMs] at u2
  have IMs : ∀ x, Sep R 0x60 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside xrtPs fun q hq => by
      simp only [xrtPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl <;> (rw [slotO]; exact inR hx (by decide))
  have slots : ∀ r o, (r, o) ∈ xrtPs → memLoad32 Ms (F + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [xrtPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot xrtPs _ hm (by
      simp only [xrtPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide), upd_ne (by
        simp only [xrtPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hr]
  have IMs' : ∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → Ms x = m.mem x := fun x hx _ => IMs x hx
  have hc2 := cdX IMs'
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  -- the exit, from 0xB0
  have hpsp : ∀ p ∈ xrtPs, p.1 ≠ sp := by decide
  have exB0 : ∀ {Mt : Word → BitVec 8} {nn : Machine}, St Mt XRT nn 0xB0 (reg nn) → CodeIn Mt XRT x509ReadTimeCode →
      reg nn sp = F → (∀ c', 0x58 ≤ c' → c' < 0x60 → Mt (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c')) →
      (∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      ∃ nn', Steps nn nn' ∧ nn'.pc = retAddr ∧ reg nn' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn' q = reg m q) ∧
        nn'.mem = Mt := by
    intro Mt nn st hct rsp hsl' hK
    have slotT : ∀ o : Word, 0x28 ≤ o.toNat → o.toNat + 4 ≤ 0x30 → memLoad32 Mt (F + o) = memLoad32 Ms (F + o) :=
      fun o h1 h2 => by
        rw [slotO]; apply memLoad32_congr; intro j hj
        rw [add_ofNat_assoc, hsl' _ (by omega) (by omega)]
    obtain ⟨n2, c2', u2'⟩ := St.block (restoreBlock xrtPs) st hct xrtRestore_end
      (restoreBlock_ok Mt F xrtPs (reg nn) rsp hpsp fun q hq => by
        simp only [xrtPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl <;> exact aligned_add hFa (by decide))
    simp only [restoreBlock_run Mt F xrtPs (reg nn) rsp hpsp] at u2'
    have rsp' : restoreRegs Mt F (reg nn) xrtPs sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact rsp
    obtain ⟨n3, d3, u3⟩ := u2'.aluImm hct xrt_at_b4 (off' := 0xB6) (by decide)
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hct xrt_at_b6
    have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
        restoreRegs Mt F f ps q = f q := by
      intro f ps q hq0
      induction ps generalizing f with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro h
        simp only [restoreRegs]
        rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
    have hslot : ∀ r o, (r, o) ∈ xrtPs → reg n4 r = reg m r := fun r o hm => by
      rw [regs4]
      simp only [xrtPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
        rw [slotT _ (by decide) (by decide)]; exact slots _ _ (by decide)
    refine ⟨n4, c2'.trans (.cons d3 (.single d4)), ?_, ?_, fun q hq => ?_, mem4⟩
    · rw [pc4, ← regs4, hslot ra 0x2C (by decide), hra, add_lit_zero, hret]
    · rw [regs4]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [rsp', eFS]
    · rcases (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          q = ra ∨ q = (8 : Fin 32) ∨ q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) q hq with
        rfl | rfl | hL
      · exact hslot _ 0x2C (by decide)
      · exact hslot _ 0x28 (by decide)
      · obtain ⟨hv, hs, hps⟩ : q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ xrtPs, p.1 ≠ q) := by revert hL; revert q; decide
        rw [regs4, upd_ne hv hs, rr _ _ q hv hps, hK q hL]
  -- `Error` exits
  have o01 : out + 1 ≠ out := by
    have := sep_offsets out (c := 0) (n := 1) (d := 1) (k := 1) (by omega) (by omega) (by omega)
    rw [add_ofNat_zero] at this; exact dn_sep1 this
  have xo0 : ∀ {x : Word}, Sep out 16 x 1 → x ≠ out := fun hx => by
    have := hx.sub (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this; exact dn_sep1 this
  have xo1 : ∀ {x : Word}, Sep out 16 x 1 → x ≠ out + 1 := fun hx => dn_sep1 (hx.sub (c := 1) (l := 1) (by decide))
  have sOC : ∀ {c l : Nat}, c + l ≤ 16 → Sep (out + BitVec.ofNat 32 c) l XRT x509ReadTimeCode.length :=
    fun {c l} h => by
      have e : (out + BitVec.ofNat 32 c).toNat = out.toNat + c := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact sep_of_le (by rw [e, hXn]; omega) (by rw [hXn]; decide)
  have so0 : Sep out 1 XRT x509ReadTimeCode.length := by
    have := sOC (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
  have so1 : Sep (out + 1) 1 XRT x509ReadTimeCode.length := sOC (c := 1) (l := 1) (by decide)
  have sRo : ∀ {c' : Nat}, c' < 0x60 → Sep out 16 (R + BitVec.ofNat 32 c') 1 := fun {c'} h => sOG.subR (c := c') (l := 1) h
  have sl0 : ∀ {Mt : Word → BitVec 8} {b : BitVec 8},
      (∀ c', 0x58 ≤ c' → c' < 0x60 → Mt (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c')) →
      ∀ c', 0x58 ≤ c' → c' < 0x60 → memStore8 Mt out b (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c') :=
    fun hS c' h1 h2 => by rw [memStore8_ne (xo0 (sRo h2)), hS c' h1 h2]
  have sl1 : ∀ {Mt : Word → BitVec 8} {b : BitVec 8},
      (∀ c', 0x58 ≤ c' → c' < 0x60 → Mt (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c')) →
      ∀ c', 0x58 ≤ c' → c' < 0x60 → memStore8 Mt (out + 1) b (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c') :=
    fun hS c' h1 h2 => by rw [memStore8_ne (xo1 (sRo h2)), hS c' h1 h2]
  have finMem : ∀ {nn : Machine}, Steps m nn → nn.pc = retAddr → reg nn sp = sp0 →
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) → nn.mem out = 1 →
      (∀ x, Sep R 0x60 x 1 → Sep out 16 x 1 → Sep (d + 8) 8 x 1 → nn.mem x = m.mem x) →
      readTime (memBytes m.mem rp rl) = none → ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t r, readTime (memBytes m.mem rp rl) = some (t, r) → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
          memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32) ∧
          ∃ k, k ≤ rl ∧ memLoad32 m'.mem (d + 8) = rp + BitVec.ofNat 32 k ∧
            memLoad32 m'.mem (d + 0xC) = BitVec.ofNat 32 (rl - k) ∧ r = memBytes m.mem (rp + BitVec.ofNat 32 k) (rl - k)) ∧
        (readTime (memBytes m.mem rp rl) = none → m'.mem out = 1) ∧
        ∀ x, Sep R 0x60 x 1 → Sep out 16 x 1 → Sep (d + 8) 8 x 1 → m'.mem x = m.mem x := fun pre pc sp' K hout hfr hspec =>
    ⟨_, pre, pc, sp', K, fun t r h => absurd (hspec ▸ h) (by simp), fun _ => hout, hfr⟩
  have fin74 : ∀ {Mt : Word → BitVec 8} {nn : Machine} {v : Word}, Steps m nn → St Mt XRT nn 0x74 (reg nn) →
      (∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → Mt x = m.mem x) →
      (∀ c', 0x58 ≤ c' → c' < 0x60 → Mt (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c')) →
      reg nn sp = F → reg nn 8 = out → (∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      readTime (memBytes m.mem rp rl) = none → reg nn a0 = v → v.extractLsb' 0 8 = 1 → ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t r, readTime (memBytes m.mem rp rl) = some (t, r) → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
          memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32) ∧
          ∃ k, k ≤ rl ∧ memLoad32 m'.mem (d + 8) = rp + BitVec.ofNat 32 k ∧
            memLoad32 m'.mem (d + 0xC) = BitVec.ofNat 32 (rl - k) ∧ r = memBytes m.mem (rp + BitVec.ofNat 32 k) (rl - k)) ∧
        (readTime (memBytes m.mem rp rl) = none → m'.mem out = 1) ∧
        ∀ x, Sep R 0x60 x 1 → Sep out 16 x 1 → Sep (d + 8) 8 x 1 → m'.mem x = m.mem x := by
    intro Mt nn v pre st hI hS rsp r8 hK hspec ra0 hv
    have hct := cdX hI
    obtain ⟨n1, d1, u1⟩ := st.sh hct xrt_at_74 (off' := 0x78) (by decide) (by rw [r8, add_lit_zero]; omega)
    rw [r8, add_lit_zero, ra0] at u1
    have hct1 := (hct.store8 (v := v.extractLsb' 0 8) so0).store8 (v := v.extractLsb' 8 8) so1
    obtain ⟨n2, d2, u2⟩ := u1.jump hct1 xrt_at_78 (off' := 0xB0) (by decide) (by rw [u1.pc]; decide)
    obtain ⟨n3, c3, pc3, sp3, K3, mem3⟩ := exB0 u2.self hct1 (by rw [u2.regs, rsp]) (sl1 (sl0 hS))
      (fun q hq => by rw [u2.regs, hK q hq])
    refine finMem (pre.trans (.cons d1 (.cons d2 c3))) pc3 sp3 K3 ?_ (fun x hx hx1 hx2 => ?_) hspec
    · rw [mem3, memStore8_ne (fun e => o01 e.symm), memStore8_same, hv]
    · rw [mem3, memStore8_ne (xo1 hx1), memStore8_ne (xo0 hx1), hI x hx hx2]
  have finA6 : ∀ {Mt : Word → BitVec 8} {nn : Machine} {v : Word}, Steps m nn → St Mt XRT nn 0xA6 (reg nn) →
      (∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → Mt x = m.mem x) →
      (∀ c', 0x58 ≤ c' → c' < 0x60 → Mt (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c')) →
      reg nn sp = F → reg nn 8 = out → (∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      readTime (memBytes m.mem rp rl) = none → reg nn a0 = v → ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t r, readTime (memBytes m.mem rp rl) = some (t, r) → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
          memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32) ∧
          ∃ k, k ≤ rl ∧ memLoad32 m'.mem (d + 8) = rp + BitVec.ofNat 32 k ∧
            memLoad32 m'.mem (d + 0xC) = BitVec.ofNat 32 (rl - k) ∧ r = memBytes m.mem (rp + BitVec.ofNat 32 k) (rl - k)) ∧
        (readTime (memBytes m.mem rp rl) = none → m'.mem out = 1) ∧
        ∀ x, Sep R 0x60 x 1 → Sep out 16 x 1 → Sep (d + 8) 8 x 1 → m'.mem x = m.mem x := by
    intro Mt nn v pre st hI hS rsp r8 hK hspec ra0
    have hct := cdX hI
    obtain ⟨n1, c1, u1⟩ := St.block xrtEA6 st hct xrtEA6_end (by
      simp +decide only [BlockOk, BInstr.ok, xrtEA6, and_true, true_and]; rw [r8]; exact so1)
    have R1 : ∀ q, reg n1 q = (runBlock xrtEA6 (Mt, reg nn)).2 q := u1.regs
    have eM : (runBlock xrtEA6 (Mt, reg nn)).1 = memStore8 Mt (out + 1) (v.extractLsb' 0 8) := by
      simp +decide only [runBlock, BInstr.run, xrtEA6]; rw [r8, ra0]
    rw [eM] at u1
    have hct1 := hct.store8 (v := v.extractLsb' 0 8) so1
    have u1' : St (memStore8 Mt (out + 1) (v.extractLsb' 0 8)) XRT n1 0xAC (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
    obtain ⟨n2, d2, u2⟩ := u1'.sb hct1 xrt_at_ac (off' := 0xB0) (by decide)
    have r81 : reg n1 8 = out := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, xrtEA6, upd_app, ↓reduceIte]; exact r8
    have a01 : reg n1 a0 = 1 := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, xrtEA6, upd_app, ↓reduceIte]; rw [st.zero]; rfl
    rw [r81, add_lit_zero, a01] at u2
    have hct2 := hct1.store8 (v := (1 : Word).extractLsb' 0 8) so0
    have K1 : ∀ q, q ≠ a0 → reg n1 q = reg nn q := fun q hq => by
      have hd : q ∉ xrtEA6.filterMap BInstr.dst := by
        simp only [xrtEA6, List.filterMap_cons, List.filterMap_nil, BInstr.dst, List.mem_cons, List.mem_nil_iff,
          or_false]; exact hq
      rw [R1, runBlock_reg _ _ _ q st.zero hd]
    obtain ⟨n3, c3, pc3, sp3, K3, mem3⟩ := exB0 u2.self hct2 (by rw [u2.regs, K1 sp (by decide), rsp])
      (sl0 (sl1 hS)) (fun q hq => by rw [u2.regs, K1 q (by revert hq; revert q; decide), hK q hq])
    refine finMem (pre.trans (c1.trans (.cons d2 c3))) pc3 sp3 K3 ?_ (fun x hx hx1 hx2 => ?_) hspec
    · rw [mem3, memStore8_same]; rfl
    · rw [mem3, memStore8_ne (xo0 hx1), memStore8_ne (xo1 hx1), hI x hx hx2]
  have fin7A : ∀ {Mt : Word → BitVec 8} {nn : Machine}, Steps m nn → St Mt XRT nn 0x7A (reg nn) →
      (∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → Mt x = m.mem x) →
      (∀ c', 0x58 ≤ c' → c' < 0x60 → Mt (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c')) →
      reg nn sp = F → reg nn 8 = out → (∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      readTime (memBytes m.mem rp rl) = none → ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t r, readTime (memBytes m.mem rp rl) = some (t, r) → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
          memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32) ∧
          ∃ k, k ≤ rl ∧ memLoad32 m'.mem (d + 8) = rp + BitVec.ofNat 32 k ∧
            memLoad32 m'.mem (d + 0xC) = BitVec.ofNat 32 (rl - k) ∧ r = memBytes m.mem (rp + BitVec.ofNat 32 k) (rl - k)) ∧
        (readTime (memBytes m.mem rp rl) = none → m'.mem out = 1) ∧
        ∀ x, Sep R 0x60 x 1 → Sep out 16 x 1 → Sep (d + 8) 8 x 1 → m'.mem x = m.mem x := by
    intro Mt nn pre st hI hS rsp r8 hK hspec
    have hct := cdX hI
    obtain ⟨n1, c1, u1⟩ := St.block xrtE7A st hct xrtE7A_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, xrtE7A, upd_app, ↓reduceIte, and_true, true_and]
      rw [r8, add_lit_zero]; exact ⟨so0, so1⟩)
    have R1 : ∀ q, reg n1 q = (runBlock xrtE7A (Mt, reg nn)).2 q := u1.regs
    obtain ⟨b, hb⟩ : ∃ b, Mt (F + 0xC) = b := ⟨_, rfl⟩
    have eM : (runBlock xrtE7A (Mt, reg nn)).1 = memStore8 (memStore8 Mt out 1) (out + 1) b := by
      simp +decide only [runBlock, BInstr.run, xrtE7A, upd_app, ↓reduceIte]
      rw [r8, rsp, add_lit_zero, hb, dt_zext8]; rfl
    rw [eM] at u1
    have hct1 := (hct.store8 (v := 1) so0).store8 (v := b) so1
    obtain ⟨n2, d2, u2⟩ := u1.jump hct1 xrt_at_88 (off' := 0xB0) (by decide) (by rw [u1.pc]; decide)
    have K2 : ∀ q, q ≠ a0 → q ≠ a1 → reg n2 q = reg nn q := fun q h0 h1 => by
      have hd : q ∉ xrtE7A.filterMap BInstr.dst := by
        simp only [xrtE7A, List.filterMap_cons, List.filterMap_nil, BInstr.dst, List.mem_cons, List.mem_nil_iff,
          or_false]; intro h; rcases h with h | h
        · exact h0 h
        · exact h1 h
      rw [u2.regs, runBlock_reg _ _ _ q st.zero hd]
    obtain ⟨n3, c3, pc3, sp3, K3, mem3⟩ := exB0 u2.self hct1 (by rw [K2 sp (by decide) (by decide), rsp])
      (sl1 (sl0 hS)) (fun q hq => by
        rw [K2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), hK q hq])
    refine finMem (pre.trans (c1.trans (.cons d2 c3))) pc3 sp3 K3 ?_ (fun x hx hx1 hx2 => ?_) hspec
    · rw [mem3, memStore8_ne (fun e => o01 e.symm), memStore8_same]
    · rw [mem3, memStore8_ne (xo1 hx1), memStore8_ne (xo0 hx1), hI x hx hx2]
  -- 0x6: the reader's length and the result pointer
  have hd8 : (d + 8).toNat = d.toNat + 8 := by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hdC : (d + 0xC).toNat % 4 = 0 := by
    rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hd8a : (d + 8).toNat % 4 = 0 := by omega
  have ld8 : ∀ {Mx : Word → BitVec 8}, (∀ x, Sep R 0x60 x 1 → Mx x = m.mem x) → memLoad32 Mx (d + 8) = rp :=
    fun hM => by
      rw [← lp]; exact memLoad32_congr fun j hj => hM _ ((sDG.sub (c := j) (l := 1) (by omega)).symm)
  have ldC : ∀ {Mx : Word → BitVec 8}, (∀ x, Sep R 0x60 x 1 → Mx x = m.mem x) →
      memLoad32 Mx (d + 0xC) = BitVec.ofNat 32 rl := fun hM => by
    rw [← ln]; exact memLoad32_congr fun j hj => by
      rw [show d + 0xC + BitVec.ofNat 32 j = d + 8 + BitVec.ofNat 32 (4 + j) by
        rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, show (8 : Word) = BitVec.ofNat 32 8 from rfl,
          add_ofNat_assoc, add_ofNat_assoc, show 8 + (4 + j) = 0xC + j by omega]]
      exact hM _ ((sDG.sub (c := 4 + j) (l := 1) (by omega)).symm)
  have hrl : rl < 2 ^ 32 := by omega
  obtain ⟨m3, c3, u3⟩ := St.block xrtA u2.self hc2 xrtA_end (by
    simp +decide only [BlockOk, BInstr.ok, xrtA, and_true]; rw [r2 a1 (by decide), ha1]; exact hdC)
  have R3 : ∀ q, reg m3 q = (runBlock xrtA (Ms, reg m2)).2 q := u3.regs
  have u3' : St Ms XRT m3 0xA (reg m3) := ⟨u3.pc, by rw [u3.mem]; rfl, fun _ => rfl⟩
  have v3 : reg m3 a2 = BitVec.ofNat 32 rl ∧ reg m3 8 = out := by
    simp +decide only [R3, runBlock, BInstr.run, xrtA, upd_app, ↓reduceIte]
    rw [r2 a1 (by decide), ha1, ldC IMs, r2 a0 (by decide), ha0]; exact ⟨rfl, zw _⟩
  have K3 : ∀ q, q.val ∉ [8, 12] → reg m3 q = reg m2 q := fun q hq => by
    have hd' : q ∉ xrtA.filterMap BInstr.dst := by
      simp only [xrtA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [R3, runBlock_reg _ _ _ q u2.self.zero hd']
  have kk3 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m3 q = reg m q := fun q hq => by
    rw [K3 q (by revert hq; revert q; decide), r2 q (by revert hq; revert q; decide)]
  have sp3 : reg m3 sp = F := by rw [K3 sp (by decide), sp2]
  have SMs : ∀ c', 0x58 ≤ c' → c' < 0x60 → Ms (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c') :=
    fun _ _ _ => rfl
  have pre3 : Steps m m3 := .cons d1 (c2.trans c3)
  by_cases hl0 : rl = 0
  · obtain ⟨m4, d4, u4⟩ := u3'.taken hc2 0x3E xrt_at_a (by decide) (by
      rw [v3.1, u3'.zero, dn_beq0 _ hrl]; exact decide_eq_true hl0)
    obtain ⟨m5, d5, u5⟩ := u4.self.aluImm hc2 xrt_at_3e (off' := 0x40) (by decide)
    obtain ⟨m6, d6, u6⟩ := u5.self.jump hc2 xrt_at_40 (off' := 0x74) (by decide) (by rw [u5.pc]; decide)
    have K6 : ∀ q, q ≠ a0 → reg m6 q = reg m3 q := fun q hq => by
      rw [u6.regs, u5.regs, upd_ne' hq u4.self.zero, u4.regs]
    exact fin74 (v := 1) (pre3.trans (.cons d4 (.cons d5 (.single d6)))) u6.self IMs' SMs
      (by rw [K6 sp (by decide), sp3]) (by rw [K6 8 (by decide), v3.2])
      (fun q hq => by rw [K6 q (by revert hq; revert q; decide), kk3 q hq])
      (by subst hl0; rw [memBytes_zero]; rfl)
      (by rw [u6.regs, u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u4.self.zero]; rfl) (by decide)
  obtain ⟨m4, d4, u4⟩ := u3'.notTaken hc2 0xC xrt_at_a (by decide) (by
    rw [v3.1, u3'.zero, dn_beq0 _ hrl]; exact decide_eq_false hl0)
  -- 0xC: the tag
  obtain ⟨m5, c5, u5⟩ := St.block xrtB u4.self hc2 xrtB_end (by
    simp +decide only [BlockOk, BInstr.ok, xrtB, and_true]; rw [u4.regs, K3 a1 (by decide), r2 a1 (by decide), ha1]
    exact hd8a)
  have R5 : ∀ q, reg m5 q = (runBlock xrtB (Ms, reg m4)).2 q := u5.regs
  have u5' : St Ms XRT m5 0x14 (reg m5) := ⟨u5.pc, by rw [u5.mem]; rfl, fun _ => rfl⟩
  have srp : ∀ i, i < rl + 14 → Sep R 0x60 (rp + BitVec.ofNat 32 i) 1 := fun i hi =>
    sPG.symm.subR (c := i) (l := 1) hi
  have brp : ∀ {Mx : Word → BitVec 8}, (∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → Mx x = m.mem x) →
      ∀ i, i < rl → Mx (rp + BitVec.ofNat 32 i) = m.mem (rp + BitVec.ofNat 32 i) := fun hM i hi =>
    hM _ (srp i (by omega)) (sPD.symm.subR (c := i) (l := 1) hi)
  have hmbx : ∀ {Mx : Word → BitVec 8}, (∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → Mx x = m.mem x) →
      ∀ (c l : Nat), c + l ≤ rl → memBytes Mx (rp + BitVec.ofNat 32 c) l = memBytes m.mem (rp + BitVec.ofNat 32 c) l :=
    fun hM c l h => dn_memBytes_eq (brp hM) h
  have hmb0 : memBytes Ms rp rl = memBytes m.mem rp rl := by
    have := hmbx IMs' 0 rl (by omega); rwa [add_ofNat_zero] at this
  have b0 : Ms rp = m.mem rp := by have := brp IMs' 0 (by omega); rwa [add_ofNat_zero] at this
  have v5 : reg m5 a0 = (m.mem rp).zeroExtend 32 ∧ reg m5 a2 = aluEval .add 0 0x17 := by
    simp +decide only [R5, runBlock, BInstr.run, xrtB, upd_app, ↓reduceIte]
    rw [u4.regs, K3 a1 (by decide), r2 a1 (by decide), ha1, ld8 IMs, add_lit_zero, b0]
    exact ⟨rfl, trivial⟩
  have K5 : ∀ q, q.val ∉ [10, 12] → reg m5 q = reg m3 q := fun q hq => by
    have hd' : q ∉ xrtB.filterMap BInstr.dst := by
      simp only [xrtB, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [R5, runBlock_reg _ _ _ q u4.self.zero hd', u4.regs]
  have pre5 : Steps m m5 := pre3.trans (.cons d4 c5)
  obtain ⟨rl', rfl⟩ : ∃ rl', rl = rl' + 1 := ⟨rl - 1, by omega⟩
  have hcons : memBytes m.mem rp (rl' + 1) = (m.mem rp).toNat :: memBytes m.mem (rp + 1) rl' := memBytes_succ _ _ _
  by_cases h17 : (m.mem rp).toNat = 0x17
  rotate_left
  · obtain ⟨m6, d6, u6⟩ := u5'.notTaken hc2 0x18 xrt_at_14 (by decide) (by
      rw [v5.1, v5.2, xrt_tag17]; exact decide_eq_false h17)
    obtain ⟨m7, d7, u7⟩ := u6.self.aluImm hc2 xrt_at_18 (off' := 0x1A) (by decide)
    have a07 : reg m7 a0 = (m.mem rp).zeroExtend 32 := by
      rw [u7.regs, upd_ne' (by decide) u6.self.zero, u6.regs, v5.1]
    have a27 : reg m7 a2 = aluEval .add 0 0x18 := by
      rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u6.self.zero]
    by_cases h18 : (m.mem rp).toNat = 0x18
    rotate_left
    · -- neither tag: `BadDer`
      obtain ⟨m8, d8, u8⟩ := u7.self.taken hc2 0x6E xrt_at_1a (by decide) (by
        rw [a07, a27, xrt_tag18, decide_eq_false h18]; rfl)
      obtain ⟨m9, d9, u9⟩ := u8.self.lui hc2 xrt_at_6e (off' := 0x70) (by decide)
      obtain ⟨m10, d10, u10⟩ := u9.self.aluImm hc2 xrt_at_70 (off' := 0x74) (by decide)
      have K10 : ∀ q, q ≠ a0 → q ≠ a2 → reg m10 q = reg m3 q := fun q h0 h2 => by
        have hq5 : q.val ∉ [10, 12] := by
          intro h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
          rcases h with h | h
          · exact h0 (Fin.ext h)
          · exact h2 (Fin.ext h)
        rw [u10.regs, upd_ne' h0 u9.self.zero, u9.regs, upd_ne' h0 u8.self.zero, u8.regs, u7.regs,
          upd_ne' h2 u6.self.zero, u6.regs, K5 q hq5]
      have hspec : readTime (memBytes m.mem rp (rl' + 1)) = none := by
        cases hdt : derTlv (memBytes m.mem rp (rl' + 1)) with
        | error e => exact readTime_err hdt
        | ok t =>
          have ht := derTlv_tag (hcons ▸ hdt)
          rw [readTime_ok m.mem rp (rl' + 1) hdt, ht, if_neg h17, if_neg h18]; rfl
      exact fin74 (v := 0x1401) (pre5.trans (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.single d10)))))) u10.self IMs'
        SMs (by rw [K10 sp (by decide) (by decide), sp3]) (by rw [K10 8 (by decide) (by decide), v3.2])
        (fun q hq => by rw [K10 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), kk3 q hq]) hspec
        (by rw [u10.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte])
        (by decide)
    -- `GeneralizedTime`
    obtain ⟨m8, d8, u8⟩ := u7.self.notTaken hc2 0x1E xrt_at_1a (by decide) (by
      rw [a07, a27, xrt_tag18, decide_eq_true h18]; rfl)
    -- `GeneralizedTime`: read the element and go on into `generalized_time`
    obtain ⟨m9, d9, u9⟩ := u8.self.aluImm hc2 xrt_at_1e (off' := 0x20) (by decide)
    have K9 : ∀ q, q ≠ a0 → q ≠ a2 → reg m9 q = reg m3 q := fun q h0 h2 => by
      have hq5 : q.val ∉ [10, 12] := by
        intro h; simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
        rcases h with h | h
        · exact h0 (Fin.ext h)
        · exact h2 (Fin.ext h)
      rw [u9.regs, upd_ne' h0 u8.self.zero, u8.regs, u7.regs, upd_ne' h2 u6.self.zero, u6.regs, K5 q hq5]
    have a09 : reg m9 a0 = F + 8 := by
      rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u8.regs, u7.regs, upd_ne' (by decide) u6.self.zero,
        u6.regs, K5 sp (by decide), sp3]; rfl
    have hF8a : (F + 8).toNat % 4 = 0 := by
      rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eFk, hRc _ (by decide)]; omega
    obtain ⟨m10, c10, pc10, mem10, regs10⟩ := u9.self.callRa hc2 xrt_at_20 xrt_at_24 (cb := TLV) (by decide) (by decide)
    have r10 := PEnv.reg1 regs10 u9.self.zero
    have hTn : TLV.toNat = (img% derTlvAddress) := by decide
    have sF8T : Sep (F + 8) 17 TLV derTlvCode.length := by
      rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eFk]; exact hiC (by decide) (by rw [hTn]; decide) (by rw [hTn]; decide)
    have sDT : Sep (d + 8) 8 TLV derTlvCode.length := sep_of_le (by rw [hd8, hTn]; omega) (by rw [hTn]; decide)
    obtain ⟨m11, c11, pc11, mem11, k11⟩ := derTlv_correct m10 (base := TLV) (out := F + 8) (d := d)
      (retAddr := XRT + BitVec.ofNat 32 (0x20 + 8)) (by decide)
      (by rw [mem10]; exact cd hcL (by rw [hTn]; decide) (by rw [hTn]; decide) IMs') pc10
      (by rw [r10 a0 (by decide), a09]) (by rw [r10 a1 (by decide), K9 a1 (by decide) (by decide), K3 a1 (by decide),
        r2 a1 (by decide), ha1]) (by rw [regs10]; simp +decide only [upd_app, ↓reduceIte])
      (even_clear _ (even_at XRT (by decide) _ (by decide))) hF8a hda sF8T sDT
    rw [mem10, ld8 IMs, ldC IMs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrl, hmb0] at mem11
    have u11 : St m11.mem XRT m11 0x28 (reg m11) := ⟨by rw [pc11], rfl, fun _ => rfl⟩
    have kk11 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m11 q = reg m q := fun q hq => by
      rw [k11 q (by revert hq; revert q; decide), r10 q (by revert hq; revert q; decide),
        K9 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), kk3 q hq]
    have sp11 : reg m11 sp = F := by
      rw [k11 sp (by decide), r10 sp (by decide), K9 sp (by decide) (by decide), sp3]
    have r811 : reg m11 8 = out := by
      rw [k11 8 (by decide), r10 8 (by decide), K9 8 (by decide) (by decide), v3.2]
    have pre11 : Steps m m11 := pre5.trans (.cons d6 (.cons d7 (.cons d8 (.cons d9 (c10.trans c11)))))
    have sF8x : ∀ {x : Word}, Sep R 0x60 x 1 → Sep (F + 8) 17 x 1 := fun hx => by
      rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eFk]; exact inR hx (by decide)
    have sF8s : ∀ {c' : Nat}, 0x58 ≤ c' → c' < 0x60 → Sep (F + 8) 17 (R + BitVec.ofNat 32 c') 1 := fun h1 h2 => by
      rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eFk]; exact offs (by omega) (by omega) (by omega)
    have sF8d : Sep (F + 8) 17 (d + 8) 8 := by
      rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eFk]; exact sDG.symm.sub (c := 0x38) (l := 17) (by omega)
    cases hdt : derTlv (memBytes m.mem rp (rl' + 1)) with
    | error e =>
      rw [hdt] at mem11
      have I11 : ∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → m11.mem x = m.mem x := fun x hx _ => by
        have e1 : Sep (F + 8 + 4) 1 x 1 := (sF8x hx).sub (c := 4) (l := 1) (by omega)
        have e2 : Sep (F + 8) 4 x 1 := by have := (sF8x hx).sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
        rw [mem11]; simp only [derTlvMem]
        rw [memStore8_ne (dn_sep1 e1), memStore32_get_sep e2, IMs x hx]
      have S11 : ∀ c', 0x58 ≤ c' → c' < 0x60 → m11.mem (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c') :=
        fun c' h1 h2 => by
          have e1 : Sep (F + 8 + 4) 1 (R + BitVec.ofNat 32 c') 1 := (sF8s h1 h2).sub (c := 4) (l := 1) (by omega)
          have e2 : Sep (F + 8) 4 (R + BitVec.ofNat 32 c') 1 := by
            have := (sF8s h1 h2).sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
          rw [mem11]; simp only [derTlvMem]
          rw [memStore8_ne (dn_sep1 e1), memStore32_get_sep e2]
      have hc11 := cdX I11
      obtain ⟨m12, d12, u12⟩ := u11.lw hc11 xrt_at_28 (off' := 0x2A) (by decide) (by rw [sp11]; exact hF8a)
      have a112 : reg m12 a1 = 0 := by
        rw [u12.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp11, mem11]; simp only [derTlvMem]
        have e1 : Sep (F + 8 + 4) 1 (F + 8) 4 := by
          have := sep_offsets (F + 8) (c := 4) (n := 1) (d := 0) (k := 4) (by omega) (by omega) (by omega)
          rwa [add_ofNat_zero] at this
        rw [memLoad32_store8_sep e1, memLoad32_store32_same]
      obtain ⟨m13, d13, u13⟩ := u12.self.taken hc11 0x7A xrt_at_2a (by decide) (by rw [a112, u12.self.zero]; rfl)
      have K13 : ∀ q, q ≠ a1 → reg m13 q = reg m11 q := fun q hq => by rw [u13.regs, u12.regs, upd_ne' hq u11.zero]
      exact fin7A (pre11.trans (.cons d12 (.single d13))) u13.self I11 S11 (by rw [K13 sp (by decide), sp11])
        (by rw [K13 8 (by decide), r811]) (fun q hq => by rw [K13 q (by revert hq; revert q; decide), kk11 q hq])
        (readTime_err hdt)
    | ok t =>
      rw [hdt] at mem11
      obtain ⟨lo0, lo4, ld8', ldC', fr11⟩ := derTlvMem_ok Ms (F + 8) d rp (BitVec.ofNat 32 (rl' + 1)) t sF8d
      rw [← mem11] at lo0 lo4 ld8' ldC' fr11
      have hth := derTlv_header hdt
      have htb := derTlv_bound hdt
      rw [memBytes_length] at htb
      have I11 : ∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → m11.mem x = m.mem x := fun x hx hx' => by
        rw [fr11 x (sF8x hx) hx', IMs x hx]
      have S11 : ∀ c', 0x58 ≤ c' → c' < 0x60 → m11.mem (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c') :=
        fun c' h1 h2 => fr11 _ (sF8s h1 h2) (sDG.subR (c := c') (l := 1) (by omega))
      have hc11 := cdX I11
      obtain ⟨m12, d12, u12⟩ := u11.lw hc11 xrt_at_28 (off' := 0x2A) (by decide) (by rw [sp11]; exact hF8a)
      have a112 : reg m12 a1 = rp + BitVec.ofNat 32 t.header := by
        rw [u12.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp11, lo0]
      have hch : (rp + BitVec.ofNat 32 t.header).toNat = rp.toNat + t.header := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      obtain ⟨m13, d13, u13⟩ := u12.self.notTaken hc11 0x2C xrt_at_2a (by decide) (by
        rw [a112, u12.self.zero]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]
        intro e; have := congrArg BitVec.toNat e; rw [hch, show (0 : Word).toNat = 0 from rfl] at this; omega)
      -- 0x2C: restore the frame and jump to `generalized_time` with the content
      have hFk : ∀ k, k ≤ 0x30 → k % 4 = 0 → (F + BitVec.ofNat 32 k).toNat % 4 = 0 := fun k hk h4 => by
        rw [eFk, hRc _ (by omega)]; omega
      obtain ⟨m14, c14, u14⟩ := St.block xrtT u13.self hc11 xrtT_end (by
        simp +decide only [BlockOk, BInstr.ok, BInstr.run, xrtT, upd_app, ↓reduceIte, and_true, true_and]
        simp only [u13.regs, u12.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp11]
        exact ⟨hFk 0xC (by decide) (by decide), hFk 0x2C (by decide) (by decide), hFk 0x28 (by decide) (by decide)⟩)
      have R14 : ∀ q, reg m14 q = (runBlock xrtT (m11.mem, reg m13)).2 q := u14.regs
      have u14' : St m11.mem XRT m14 0x36 (reg m14) := ⟨u14.pc, by rw [u14.mem]; rfl, fun _ => rfl⟩
      have eC : F + 0xC = F + 8 + 4 := by rw [BitVec.add_assoc]; rfl
      have slotL : ∀ o : Word, 0x28 ≤ o.toNat → o.toNat + 4 ≤ 0x30 → memLoad32 m11.mem (F + o) = memLoad32 Ms (F + o) :=
        fun o h1 h2 => by
          rw [slotO]; apply memLoad32_congr; intro j hj
          rw [add_ofNat_assoc, S11 _ (by omega) (by omega)]
      have r13 : ∀ q, q ≠ a1 → reg m13 q = reg m11 q := fun q hq => by rw [u13.regs, u12.regs, upd_ne' hq u11.zero]
      have v14 : reg m14 a2 = BitVec.ofNat 32 t.len ∧ reg m14 a0 = out ∧ reg m14 ra = retAddr ∧ reg m14 8 = reg m 8 ∧
          reg m14 sp = sp0 ∧ reg m14 a1 = rp + BitVec.ofNat 32 t.header := by
        simp +decide only [R14, runBlock, BInstr.run, xrtT, upd_app, ↓reduceIte]
        simp only [u13.regs, u12.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [sp11, eC, lo4, r811, slotL _ (by decide) (by decide), slotL _ (by decide) (by decide),
          slots ra 0x2C (by decide), slots 8 0x28 (by decide), hra]
        refine ⟨rfl, zw _, rfl, rfl, ?_, lo0⟩
        rw [ev_add]; exact eFS
      obtain ⟨v14a2, v14a0, v14ra, v148, v14sp, v14a1⟩ := v14
      have K14 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m14 q = reg m q := fun q hq => by
        have hd' : q ∉ xrtT.filterMap BInstr.dst := by
          simp only [xrtT, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
        rw [R14, runBlock_reg _ _ _ q u13.self.zero hd', r13 q (by revert hq; revert q; decide), kk11 q hq]
      obtain ⟨m15, d15, u15⟩ := u14'.auipc hc11 xrt_at_36 (off' := 0x3A) (by decide)
      obtain ⟨m16, d16, pc16, mem16, regs16⟩ := u15.jalr hc11 xrt_at_3a
      have r16 : ∀ q, q.val ≠ 6 → reg m16 q = reg m14 q := fun q hq => by
        rw [regs16, upd_ne' (fun e => hq (by rw [e]; rfl)) u14'.zero]
      have pc16' : m16.pc = GNT := by
        rw [pc16]; simp +decide only [upd_app, ↓reduceIte]
      have hcode : ∀ {c : Word} {code : List Nat}, CodeIn m.mem c code → 0x40000000 ≤ c.toNat →
          c.toNat + code.length ≤ 2 ^ 32 → CodeIn m16.mem c code := fun hc h1 h2 => by rw [mem16]; exact cd hc h1 h2 I11
      have hGn : GNT.toNat = (img% generalizedTimeAddress) := by decide
      have hDn : DT.toNat = (img% dateTimeAddress) := by decide
      have hTDn : TD.toNat = (img% timeDigits2Address) := by decide
      have hpw' : (rp + BitVec.ofNat 32 t.header).toNat + t.len + 14 ≤ 0x40000000 := by rw [hch]; omega
      obtain ⟨mf, cf, pcf, spf, Kf, hSf, hNf, frf⟩ := generalizedTime_correct m16 (sp0 := sp0) (out := out)
        (p := rp + BitVec.ofNat 32 t.header) (n := t.len) (retAddr := retAddr)
        (hcode hcG (by rw [hGn]; decide) (by rw [hGn]; decide)) (hcode hcD (by rw [hDn]; decide) (by rw [hDn]; decide))
        (hcode hcT (by rw [hTDn]; decide) (by rw [hTDn]; decide)) pc16'
        (by rw [r16 a0 (by decide), v14a0]) (by rw [r16 a1 (by decide), v14a1]) (by rw [r16 a2 (by decide), v14a2])
        (by rw [r16 ra (by decide), v14ra]) hret (by rw [r16 sp (by decide), v14sp]) hsa hsl hsw how hoa (by omega)
        hpw' (by rw [hch]; omega) (by rw [hR]; exact sOG)
        (by rw [hR]; exact sPG.sub (c := t.header) (l := t.len + 14) (by omega))
      rw [mem16] at hSf hNf frf
      rw [hR] at frf
      have hcon : memBytes m11.mem (rp + BitVec.ofNat 32 t.header) t.len =
          memBytes m.mem (rp + BitVec.ofNat 32 t.header) t.len := hmbx I11 _ _ (by omega)
      rw [hcon] at hSf hNf
      have ht18 : t.tag = 0x18 := by rw [derTlv_tag (hcons ▸ hdt), h18]
      have hspec : readTime (memBytes m.mem rp (rl' + 1)) =
          (generalizedTime (memBytes m.mem (rp + BitVec.ofNat 32 t.header) t.len)).map fun x =>
            (x, memBytes m.mem (rp + BitVec.ofNat 32 (t.header + t.len)) (rl' + 1 - (t.header + t.len))) := by
        rw [readTime_ok m.mem rp (rl' + 1) hdt, ht18]; rfl
      refine ⟨mf, pre11.trans (.cons d12 (.cons d13 (c14.trans (.cons d15 (.cons d16 cf))))), pcf, spf,
        fun q hq => ?_, fun tt r h => ?_, fun h => ?_, fun x hx hx1 hx2 => ?_⟩
      · rw [Kf q hq]
        rcases (by decide : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
            q = ra ∨ q = (8 : Fin 32) ∨ q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) q hq with
          rfl | rfl | hL
        · rw [r16 ra (by decide), v14ra, hra]
        · rw [r16 8 (by decide), v148]
        · rw [r16 q (by revert hL; revert q; decide), K14 q hL]
      · rw [hspec] at h
        cases hg : generalizedTime (memBytes m.mem (rp + BitVec.ofNat 32 t.header) t.len) with
        | none => rw [hg] at h; cases h
        | some tg =>
          rw [hg] at h; simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2, h3, h4⟩ := hSf tg hg
          have ldf : ∀ j, j < 8 → mf.mem (d + 8 + BitVec.ofNat 32 j) = m11.mem (d + 8 + BitVec.ofNat 32 j) :=
            fun j hj => frf _ ((sDG.sub (c := j) (l := 1) (by omega)).symm) (sOD.subR (c := j) (l := 1) (by omega))
          have hsub : BitVec.ofNat 32 (rl' + 1) - BitVec.ofNat 32 (t.header + t.len) =
              BitVec.ofNat 32 (rl' + 1 - (t.header + t.len)) := BitVec.eq_of_toNat_eq (by
            rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
          refine ⟨h1, h2, h3, h4, t.header + t.len, htb, ?_, ?_, rfl⟩
          · rw [← ld8']; exact memLoad32_congr fun j hj => ldf j (by omega)
          · rw [← hsub, ← ldC']
            exact memLoad32_congr fun j hj => by
              rw [show d + 0xC + BitVec.ofNat 32 j = d + 8 + BitVec.ofNat 32 (4 + j) by
                rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, show (8 : Word) = BitVec.ofNat 32 8 from rfl,
                  add_ofNat_assoc, add_ofNat_assoc, show 8 + (4 + j) = 0xC + j by omega]]
              exact ldf _ (by omega)
      · rw [hspec] at h
        cases hg : generalizedTime (memBytes m.mem (rp + BitVec.ofNat 32 t.header) t.len) with
        | none => exact (hNf hg).1
        | some tg => rw [hg] at h; cases h
      · rw [frf x hx hx1, I11 x hx hx2]
  -- `UTCTime`: read the element and run `utc_time` on its content
  obtain ⟨m6, d6, u6⟩ := u5'.taken hc2 0x42 xrt_at_14 (by decide) (by rw [v5.1, v5.2, xrt_tag17]; exact decide_eq_true h17)
  obtain ⟨m9, d9, u9⟩ := u6.self.aluImm hc2 xrt_at_42 (off' := 0x44) (by decide)
  have K9 : ∀ q, q.val ∉ [10, 12] → reg m9 q = reg m3 q := fun q hq => by
    rw [u9.regs, upd_ne' (by intro h; apply hq; rw [h]; decide) u6.self.zero, u6.regs, K5 q hq]
  have a09 : reg m9 a0 = F + 8 := by
    rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u6.regs, K5 sp (by decide), sp3]; rfl
  have hF8a : (F + 8).toNat % 4 = 0 := by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eFk, hRc _ (by decide)]; omega
  obtain ⟨m10, c10, pc10, mem10, regs10⟩ := u9.self.callRa hc2 xrt_at_44 xrt_at_48 (cb := TLV) (by decide) (by decide)
  have r10 := PEnv.reg1 regs10 u9.self.zero
  have hTn : TLV.toNat = (img% derTlvAddress) := by decide
  have sF8T : Sep (F + 8) 17 TLV derTlvCode.length := by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eFk]; exact hiC (by decide) (by rw [hTn]; decide) (by rw [hTn]; decide)
  have sDT : Sep (d + 8) 8 TLV derTlvCode.length := sep_of_le (by rw [hd8, hTn]; omega) (by rw [hTn]; decide)
  obtain ⟨m11, c11, pc11, mem11, k11⟩ := derTlv_correct m10 (base := TLV) (out := F + 8) (d := d)
    (retAddr := XRT + BitVec.ofNat 32 (0x44 + 8)) (by decide)
    (by rw [mem10]; exact cd hcL (by rw [hTn]; decide) (by rw [hTn]; decide) IMs') pc10
    (by rw [r10 a0 (by decide), a09]) (by rw [r10 a1 (by decide), K9 a1 (by decide), K3 a1 (by decide),
      r2 a1 (by decide), ha1]) (by rw [regs10]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at XRT (by decide) _ (by decide))) hF8a hda sF8T sDT
  rw [mem10, ld8 IMs, ldC IMs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrl, hmb0] at mem11
  have u11 : St m11.mem XRT m11 0x4C (reg m11) := ⟨by rw [pc11], rfl, fun _ => rfl⟩
  have kk11 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m11 q = reg m q := fun q hq => by
    rw [k11 q (by revert hq; revert q; decide), r10 q (by revert hq; revert q; decide),
      K9 q (by revert hq; revert q; decide), kk3 q hq]
  have sp11 : reg m11 sp = F := by rw [k11 sp (by decide), r10 sp (by decide), K9 sp (by decide), sp3]
  have r811 : reg m11 8 = out := by rw [k11 8 (by decide), r10 8 (by decide), K9 8 (by decide), v3.2]
  have pre11 : Steps m m11 := pre5.trans (.cons d6 (.cons d9 (c10.trans c11)))
  have sF8x : ∀ {x : Word}, Sep R 0x60 x 1 → Sep (F + 8) 17 x 1 := fun hx => by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eFk]; exact inR hx (by decide)
  have sF8s : ∀ {c' : Nat}, 0x58 ≤ c' → c' < 0x60 → Sep (F + 8) 17 (R + BitVec.ofNat 32 c') 1 := fun h1 h2 => by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eFk]; exact offs (by omega) (by omega) (by omega)
  have sF8d : Sep (F + 8) 17 (d + 8) 8 := by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eFk]; exact sDG.symm.sub (c := 0x38) (l := 17) (by omega)
  cases hdt : derTlv (memBytes m.mem rp (rl' + 1)) with
  | error e =>
    rw [hdt] at mem11
    have I11 : ∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → m11.mem x = m.mem x := fun x hx _ => by
      have e1 : Sep (F + 8 + 4) 1 x 1 := (sF8x hx).sub (c := 4) (l := 1) (by omega)
      have e2 : Sep (F + 8) 4 x 1 := by have := (sF8x hx).sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
      rw [mem11]; simp only [derTlvMem]
      rw [memStore8_ne (dn_sep1 e1), memStore32_get_sep e2, IMs x hx]
    have S11 : ∀ c', 0x58 ≤ c' → c' < 0x60 → m11.mem (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c') :=
      fun c' h1 h2 => by
        have e1 : Sep (F + 8 + 4) 1 (R + BitVec.ofNat 32 c') 1 := (sF8s h1 h2).sub (c := 4) (l := 1) (by omega)
        have e2 : Sep (F + 8) 4 (R + BitVec.ofNat 32 c') 1 := by
          have := (sF8s h1 h2).sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
        rw [mem11]; simp only [derTlvMem]
        rw [memStore8_ne (dn_sep1 e1), memStore32_get_sep e2]
    have hc11 := cdX I11
    obtain ⟨m12, d12, u12⟩ := u11.lw hc11 xrt_at_4c (off' := 0x4E) (by decide) (by rw [sp11]; exact hF8a)
    have a012 : reg m12 a0 = 0 := by
      rw [u12.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp11, mem11]; simp only [derTlvMem]
      have e1 : Sep (F + 8 + 4) 1 (F + 8) 4 := by
        have := sep_offsets (F + 8) (c := 4) (n := 1) (d := 0) (k := 4) (by omega) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      rw [memLoad32_store8_sep e1, memLoad32_store32_same]
    obtain ⟨m13, d13, u13⟩ := u12.self.taken hc11 0x7A xrt_at_4e (by decide) (by rw [a012, u12.self.zero]; rfl)
    have K13 : ∀ q, q ≠ a0 → reg m13 q = reg m11 q := fun q hq => by rw [u13.regs, u12.regs, upd_ne' hq u11.zero]
    exact fin7A (pre11.trans (.cons d12 (.single d13))) u13.self I11 S11 (by rw [K13 sp (by decide), sp11])
      (by rw [K13 8 (by decide), r811]) (fun q hq => by rw [K13 q (by revert hq; revert q; decide), kk11 q hq])
      (readTime_err hdt)
  | ok t =>
  rw [hdt] at mem11
  obtain ⟨lo0, lo4, ld8', ldC', fr11⟩ := derTlvMem_ok Ms (F + 8) d rp (BitVec.ofNat 32 (rl' + 1)) t sF8d
  rw [← mem11] at lo0 lo4 ld8' ldC' fr11
  have hth := derTlv_header hdt
  have htb := derTlv_bound hdt
  rw [memBytes_length] at htb
  have I11 : ∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → m11.mem x = m.mem x := fun x hx hx' => by
    rw [fr11 x (sF8x hx) hx', IMs x hx]
  have S11 : ∀ c', 0x58 ≤ c' → c' < 0x60 → m11.mem (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c') :=
    fun c' h1 h2 => fr11 _ (sF8s h1 h2) (sDG.subR (c := c') (l := 1) (by omega))
  have hc11 := cdX I11
  obtain ⟨m12, d12, u12⟩ := u11.lw hc11 xrt_at_4c (off' := 0x4E) (by decide) (by rw [sp11]; exact hF8a)
  have a012 : reg m12 a0 = rp + BitVec.ofNat 32 t.header := by
    rw [u12.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp11, lo0]
  have hch : (rp + BitVec.ofNat 32 t.header).toNat = rp.toNat + t.header := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨m13, d13, u13⟩ := u12.self.notTaken hc11 0x50 xrt_at_4e (by decide) (by
    rw [a012, u12.self.zero]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg BitVec.toNat e; rw [hch, show (0 : Word).toNat = 0 from rfl] at this; omega)
  have ht17 : t.tag = 0x17 := by rw [derTlv_tag (hcons ▸ hdt), h17]
  have hspec : readTime (memBytes m.mem rp (rl' + 1)) =
      (utcTime (memBytes m.mem (rp + BitVec.ofNat 32 t.header) t.len)).map fun x =>
        (x, memBytes m.mem (rp + BitVec.ofNat 32 (t.header + t.len)) (rl' + 1 - (t.header + t.len))) := by
    rw [readTime_ok m.mem rp (rl' + 1) hdt, ht17]; rfl
  have r13 : ∀ q, q ≠ a0 → reg m13 q = reg m11 q := fun q hq => by rw [u13.regs, u12.regs, upd_ne' hq u11.zero]
  have pre13 : Steps m m13 := pre11.trans (.cons d12 (.single d13))
  -- 0x50: a reader over the content at `F + 0x20`
  obtain ⟨c, hc⟩ : ∃ c, rp + BitVec.ofNat 32 t.header = c := ⟨_, rfl⟩
  rw [hc] at hspec a012 hch lo0
  have hFk : ∀ k, k ≤ 0x30 → k % 4 = 0 → (F + BitVec.ofNat 32 k).toNat % 4 = 0 := fun k hk h4 => by
    rw [eFk, hRc _ (by omega)]; omega
  have sFT : ∀ {k l : Nat}, k + l ≤ 0x30 → Sep (F + BitVec.ofNat 32 k) l XRT x509ReadTimeCode.length := fun h => by
    rw [eFk]; exact hiC (by omega) (by rw [hXn]; decide) (by rw [hXn]; decide)
  obtain ⟨m14, c14, u14⟩ := St.block xrtU1 u13.self hc11 xrtU1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, xrtU1, upd_app, ↓reduceIte, and_true, true_and]
    rw [r13 sp (by decide), sp11]
    exact ⟨hFk 0xC (by decide) (by decide), ⟨hFk 0x20 (by decide) (by decide), sFT (by decide)⟩,
      hFk 0x24 (by decide) (by decide), sFT (by decide)⟩)
  have R14 : ∀ q, reg m14 q = (runBlock xrtU1 (m11.mem, reg m13)).2 q := u14.regs
  have eC : F + 0xC = F + 8 + 4 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 (memStore32 m11.mem (F + 0x20) c) (F + 0x24) (BitVec.ofNat 32 t.len) = M2 :=
    ⟨_, rfl⟩
  have eM14 : (runBlock xrtU1 (m11.mem, reg m13)).1 = M2 := by
    simp +decide only [runBlock, BInstr.run, xrtU1, upd_app, ↓reduceIte]
    rw [r13 sp (by decide), sp11, u13.regs, u12.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [sp11, eC, lo4, lo0, ← hM2]
  have u14' : St M2 XRT m14 0x5A (reg m14) := ⟨u14.pc, by rw [u14.mem, eM14], fun _ => rfl⟩
  have sF20x : ∀ {x : Word} {k : Nat}, Sep R 0x60 x 1 → 0x20 ≤ k → k + 4 ≤ 0x30 → Sep (F + BitVec.ofNat 32 k) 4 x 1 :=
    fun hx h1 h2 => by rw [eFk]; exact inR hx (by omega)
  have I2 : ∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → M2 x = m.mem x := fun x hx hx' => by
    have e1 : Sep (F + 0x24) 4 x 1 := sF20x (k := 0x24) hx (by decide) (by decide)
    have e2 : Sep (F + 0x20) 4 x 1 := sF20x (k := 0x20) hx (by decide) (by decide)
    rw [← hM2, memStore32_get_sep e1, memStore32_get_sep e2, I11 x hx hx']
  have S2 : ∀ c', 0x58 ≤ c' → c' < 0x60 → M2 (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c') :=
    fun c' h1 h2 => by
      have e1 : Sep (F + 0x24) 4 (R + BitVec.ofNat 32 c') 1 := by
        rw [show (0x24 : Word) = BitVec.ofNat 32 0x24 from rfl, eFk]; exact offs (by omega) (by omega) (by omega)
      have e2 : Sep (F + 0x20) 4 (R + BitVec.ofNat 32 c') 1 := by
        rw [show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, eFk]; exact offs (by omega) (by omega) (by omega)
      rw [← hM2, memStore32_get_sep e1, memStore32_get_sep e2, S11 c' h1 h2]
  have hc14 := cdX I2
  have v14 : reg m14 a0 = F + 8 ∧ reg m14 a1 = F + 0x20 := by
    simp +decide only [R14, runBlock, BInstr.run, xrtU1, upd_app, ↓reduceIte]
    rw [r13 sp (by decide), sp11]; exact ⟨rfl, rfl⟩
  have K14 : ∀ q, q.val ∉ [10, 11] → reg m14 q = reg m13 q := fun q hq => by
    have hd' : q ∉ xrtU1.filterMap BInstr.dst := by
      simp only [xrtU1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [R14, runBlock_reg _ _ _ q u13.self.zero hd']
  have kk14 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m14 q = reg m q := fun q hq => by
    rw [K14 q (by revert hq; revert q; decide), r13 q (by revert hq; revert q; decide), kk11 q hq]
  have sp14 : reg m14 sp = F := by rw [K14 sp (by decide), r13 sp (by decide), sp11]
  have r814 : reg m14 8 = out := by rw [K14 8 (by decide), r13 8 (by decide), r811]
  have pre14 : Steps m m14 := pre13.trans c14
  -- 0x5A: the two-digit year
  obtain ⟨m15, c15, pc15, mem15, regs15⟩ := u14'.callRa hc14 xrt_at_5a xrt_at_5e (cb := TD) (by decide) (by decide)
  have r15 := PEnv.reg1 regs15 u14'.zero
  have hTDn : TD.toNat = (img% timeDigits2Address) := by decide
  have sF8TD : Sep (F + 8) 8 TD timeDigits2Code.length := by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eFk]; exact hiC (by decide) (by rw [hTDn]; decide) (by rw [hTDn]; decide)
  have sF20TD : Sep (F + 0x20) 8 TD timeDigits2Code.length := by
    rw [show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, eFk]
    exact hiC (by decide) (by rw [hTDn]; decide) (by rw [hTDn]; decide)
  have hcn : c.toNat = rp.toNat + t.header := hch
  have sF20c : ∀ {k : Nat}, k ≤ 12 → Sep (F + 0x20) 8 (c + BitVec.ofNat 32 k) (14 - k) := fun {k} hk => by
    rw [show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, eFk, ← hc, add_ofNat_assoc]
    exact (sPG.sub (c := t.header + k) (l := 14 - k) (by omega)).subR (c := 0x50) (l := 8) (by omega) |>.symm
  have s2420 : Sep (F + 0x24) 4 (F + 0x20) 4 := by
    rw [show (0x24 : Word) = BitVec.ofNat 32 0x24 from rfl, show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, eFk, eFk]
    exact offs (by omega) (by omega) (by omega)
  have l20 : memLoad32 M2 (F + 0x20) = c := by
    rw [← hM2, memLoad32_store32_sep s2420, memLoad32_store32_same]
  have sDPc : Sep (F + 0x20) 8 c 2 := by
    have := sF20c (k := 0) (by omega); rw [add_ofNat_zero] at this
    have h2 := this.subR (c := 0) (l := 2) (by omega); rwa [add_ofNat_zero] at h2
  have l24 : memLoad32 M2 (F + 0x20 + 4) = BitVec.ofNat 32 t.len := by
    rw [show F + 0x20 + 4 = F + 0x24 by rw [BitVec.add_assoc]; rfl, ← hM2, memLoad32_store32_same]
  have hTD15 : CodeIn m15.mem TD timeDigits2Code := by
    rw [mem15]; exact cd hcT (by rw [hTDn]; decide) (by rw [hTDn]; decide) I2
  obtain ⟨m16, c16, pc16, mem16, k16⟩ := timeDigits2_correct m15 (base := TD) (retAddr := XRT + BitVec.ofNat 32 (0x5A + 8))
    (out := F + 8) (d := F + 0x20) (p := c) (n := t.len) (by decide) hTD15 pc15 (by rw [r15 a0 (by decide), v14.1]) (by rw [r15 a1 (by decide), v14.2])
    (hFk 0x20 (by decide) (by decide)) hF8a (by omega) (by rw [mem15, l20]) (by rw [mem15, l24]) sF8TD sF20TD sDPc
    (by rw [regs15]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at XRT (by decide) _ (by decide)))
  rw [mem15] at mem16
  have sF8_20 : Sep (F + 8) 8 (F + 0x20) 8 := by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, eFk, eFk]
    exact offs (by omega) (by omega) (by omega)
  obtain ⟨frm, cs⟩ := digits2Mem_cases M2 (F + 8) (F + 0x20) c t.len (by omega) sF8_20
  rw [← mem16] at frm cs
  have I3 : ∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → m16.mem x = m.mem x := fun x hx hx' => by
    rw [frm x (by have := (sF8x hx).sub (c := 0) (l := 8) (by omega); rwa [add_ofNat_zero] at this)
      (by rw [show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, eFk]; exact inR hx (by omega)), I2 x hx hx']
  have S3 : ∀ c', 0x58 ≤ c' → c' < 0x60 → m16.mem (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c') :=
    fun c' h1 h2 => by
      have e1 : Sep (F + 8) 8 (R + BitVec.ofNat 32 c') 1 := by
        have := (sF8s h1 h2).sub (c := 0) (l := 8) (by omega); rwa [add_ofNat_zero] at this
      have e2 : Sep (F + 0x20) 8 (R + BitVec.ofNat 32 c') 1 := by
        rw [show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, eFk]; exact offs (by omega) (by omega) (by omega)
      rw [frm _ e1 e2, S2 c' h1 h2]
  have hc16 := cdX I3
  have u16 : St m16.mem XRT m16 0x62 (reg m16) := ⟨by rw [pc16], rfl, fun _ => rfl⟩
  have kk16 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m16 q = reg m q := fun q hq => by
    rw [k16 q (by revert hq; revert q; decide), r15 q (by revert hq; revert q; decide), kk14 q hq]
  have sp16 : reg m16 sp = F := by rw [k16 sp (by decide), r15 sp (by decide), sp14]
  have r816 : reg m16 8 = out := by rw [k16 8 (by decide), r15 8 (by decide), r814]
  have pre16 : Steps m m16 := pre14.trans (c15.trans c16)
  obtain ⟨m17, d17, u17⟩ := u16.lbu hc16 xrt_at_62 (off' := 0x66) (by decide)
  have a017 : reg m17 a0 = (m16.mem (F + 8)).zeroExtend 32 := by
    rw [u17.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp16]
  have K17 : ∀ q, q ≠ a0 → reg m17 q = reg m16 q := fun q hq => by rw [u17.regs, upd_ne' hq u16.zero]
  have hcont : memBytes M2 c t.len = memBytes m.mem c t.len := by
    rw [← hc]; exact hmbx I2 _ _ (by omega)
  -- `digits::<2>` failed: its code goes out through 0xA6
  have errA6 : ∀ {Mx : Word → BitVec 8} {nn : Machine}, Steps m nn → St Mx XRT nn 0x68 (reg nn) →
      (∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → Mx x = m.mem x) →
      (∀ c', 0x58 ≤ c' → c' < 0x60 → Mx (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c')) →
      reg nn sp = F → reg nn 8 = out → (∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nn q = reg m q) →
      utcTime (memBytes m.mem c t.len) = none → ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t r, readTime (memBytes m.mem rp (rl' + 1)) = some (t, r) → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
          memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32) ∧
          ∃ k, k ≤ rl' + 1 ∧ memLoad32 m'.mem (d + 8) = rp + BitVec.ofNat 32 k ∧
            memLoad32 m'.mem (d + 0xC) = BitVec.ofNat 32 (rl' + 1 - k) ∧
            r = memBytes m.mem (rp + BitVec.ofNat 32 k) (rl' + 1 - k)) ∧
        (readTime (memBytes m.mem rp (rl' + 1)) = none → m'.mem out = 1) ∧
        ∀ x, Sep R 0x60 x 1 → Sep out 16 x 1 → Sep (d + 8) 8 x 1 → m'.mem x = m.mem x := by
    intro Mx nn pre st hI hS rsp r8 hK hu
    have hcx := cdX hI
    obtain ⟨n1, d1, u1⟩ := st.lbu hcx xrt_at_68 (off' := 0x6C) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.self.jump hcx xrt_at_6c (off' := 0xA6) (by decide) (by rw [u1.pc]; decide)
    have K2 : ∀ q, q ≠ a0 → reg n2 q = reg nn q := fun q hq => by rw [u2.regs, u1.regs, upd_ne' hq st.zero]
    exact finA6 (v := (Mx (reg nn sp + 9)).zeroExtend 32) (pre.trans (.cons d1 (.single d2))) u2.self hI hS
      (by rw [K2 sp (by decide), rsp]) (by rw [K2 8 (by decide), r8])
      (fun q hq => by rw [K2 q (by revert hq; revert q; decide), hK q hq])
      (by rw [hspec, hu]; rfl) (by rw [u2.regs, u1.regs]; simp +decide only [upd_app, ↓reduceIte])
  rcases cs with ⟨hr, h8, _⟩ | ⟨v, hr, hv, h8, h12, hd0, hd4, h2⟩
  · rw [hcont] at hr
    obtain ⟨m18, d18, u18⟩ := u17.self.notTaken hc16 0x68 xrt_at_66 (by decide) (by rw [a017, h8, u17.self.zero]; rfl)
    exact errA6 (pre16.trans (.cons d17 (.single d18))) u18.self I3 S3 (by rw [u18.regs, K17 sp (by decide), sp16])
      (by rw [u18.regs, K17 8 (by decide), r816]) (fun q hq => by rw [u18.regs, K17 q (by revert hq; revert q; decide), kk16 q hq])
      (by rw [utcTime_eq, hr]; rfl)
  rw [hcont] at hr
  have hmb2 : memBytes M2 (c + 2) (t.len - 2) = memBytes m.mem (c + 2) (t.len - 2) := by
    rw [← hc, show rp + BitVec.ofNat 32 t.header + 2 = rp + BitVec.ofNat 32 (t.header + 2) by
      rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc]]
    exact hmbx I2 _ _ (by omega)
  rw [hmb2] at hr
  obtain ⟨m18, d18, u18⟩ := u17.self.taken hc16 0x8A xrt_at_66 (by decide) (by rw [a017, h8, u17.self.zero]; rfl)
  have r18 : ∀ q, reg m18 q = reg m17 q := u18.regs
  -- 0x8A: the century
  obtain ⟨m19, d19, u19⟩ := u18.self.lw hc16 xrt_at_8a (off' := 0x8C) (by decide)
    (by rw [r18, K17 sp (by decide), sp16]; exact hFk 0xC (by decide) (by decide))
  have a119 : reg m19 a1 = BitVec.ofNat 32 v := by
    rw [u19.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r18, K17 sp (by decide), sp16, eC, h12]
  obtain ⟨m20, d20, u20⟩ := u19.self.aluImm hc16 xrt_at_8c (off' := 0x90) (by decide)
  have a020 : reg m20 a0 = BitVec.ofNat 32 49 := by
    rw [u20.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u19.self.zero]; rfl
  have a120 : reg m20 a1 = BitVec.ofNat 32 v := by rw [u20.regs, upd_ne' (by decide) u19.self.zero, a119]
  have K20 : ∀ q, q ≠ a0 → q ≠ a1 → reg m20 q = reg m16 q := fun q h0 h1 => by
    rw [u20.regs, upd_ne' h0 u19.self.zero, u19.regs, upd_ne' h1 u18.self.zero, r18, K17 q h0]
  obtain ⟨Yv, hYv, m21, c21, u21, a021, a121, K21⟩ : ∃ Yv : Nat, Yv = v + (if v ≥ 50 then 1900 else 2000) ∧
      ∃ m21, Steps m20 m21 ∧ St m16.mem XRT m21 0x9E (reg m21) ∧
        reg m21 a0 = BitVec.ofNat 32 (if v ≥ 50 then 1900 else 2000) ∧ reg m21 a1 = BitVec.ofNat 32 v ∧
        ∀ q, q ≠ a0 → reg m21 q = reg m20 q := by
    refine ⟨_, rfl, ?_⟩
    by_cases h50 : v ≥ 50
    · obtain ⟨n1, e1, w1⟩ := u20.self.taken hc16 0x9A xrt_at_90 (by decide) (by
        rw [a020, a120, dn_bltu _ _ (by decide) (by omega)]; exact decide_eq_true (by omega))
      obtain ⟨n2, e2, w2⟩ := w1.self.aluImm hc16 xrt_at_9a (off' := 0x9E) (by decide)
      refine ⟨n2, .cons e1 (.single e2), w2.self, ?_, ?_, fun q hq => ?_⟩
      · rw [w2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [w1.self.zero, if_pos h50]; rfl
      · rw [w2.regs, upd_ne' (by decide) w1.self.zero, w1.regs, a120]
      · rw [w2.regs, upd_ne' hq w1.self.zero, w1.regs]
    · obtain ⟨n1, e1, w1⟩ := u20.self.notTaken hc16 0x94 xrt_at_90 (by decide) (by
        rw [a020, a120, dn_bltu _ _ (by decide) (by omega)]; exact decide_eq_false (by omega))
      obtain ⟨n2, e2, w2⟩ := w1.self.aluImm hc16 xrt_at_94 (off' := 0x98) (by decide)
      obtain ⟨n3, e3, w3⟩ := w2.self.jump hc16 xrt_at_98 (off' := 0x9E) (by decide) (by rw [w2.pc]; decide)
      refine ⟨n3, .cons e1 (.cons e2 (.single e3)), w3.self, ?_, ?_, fun q hq => ?_⟩
      · rw [w3.regs, w2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [w1.self.zero, if_neg h50]; rfl
      · rw [w3.regs, w2.regs, upd_ne' (by decide) w1.self.zero, w1.regs, a120]
      · rw [w3.regs, w2.regs, upd_ne' hq w1.self.zero, w1.regs]
  have hYb : Yv < 2100 := by rw [hYv]; split <;> omega
  obtain ⟨m22, d22, u22⟩ := u21.alu hc16 xrt_at_9e (off' := 0xA0) (by decide)
  have a122 : reg m22 a1 = BitVec.ofNat 32 Yv := by
    rw [u22.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [a121, a021, dn_addN, hYv]
    exact dn_ofNat_congr (Nat.mod_eq_of_lt (by split <;> omega))
  have a022 : reg m22 a0 = BitVec.ofNat 32 (if v ≥ 50 then 1900 else 2000) := by
    rw [u22.regs, upd_ne' (by decide) u21.zero, a021]
  obtain ⟨m23, d23, u23⟩ := u22.self.taken hc16 0xB8 xrt_at_a0 (by decide) (by
    rw [a122, a022]; simp only [branchTaken]
    rw [show (BitVec.ofNat 32 Yv).ult (BitVec.ofNat 32 (if v ≥ 50 then 1900 else 2000)) = false from by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; rw [hYv]; split <;> omega]; rfl)
  have K23 : ∀ q, q ≠ a0 → q ≠ a1 → reg m23 q = reg m16 q := fun q h0 h1 => by
    rw [u23.regs, u22.regs, upd_ne' h1 u21.zero, K21 q h0, K20 q h0 h1]
  -- 0xB8: `date_time` with the year and the reader at `F + 0x20`
  obtain ⟨m24, c24, u24⟩ := St.block xrtU2 u23.self hc16 xrtU2_end (by simp only [BlockOk, BInstr.ok, xrtU2, and_self])
  have R24 : ∀ q, reg m24 q = (runBlock xrtU2 (m16.mem, reg m23)).2 q := u24.regs
  have u24' : St m16.mem XRT m24 0xBC (reg m24) := ⟨u24.pc, by rw [u24.mem]; rfl, fun _ => rfl⟩
  have sp23 : reg m23 sp = F := by rw [K23 sp (by decide) (by decide), sp16]
  have v24 : reg m24 a0 = F + 8 ∧ reg m24 a2 = F + 0x20 ∧ reg m24 a1 = BitVec.ofNat 32 Yv := by
    simp +decide only [R24, runBlock, BInstr.run, xrtU2, upd_app, ↓reduceIte]
    rw [sp23, u23.regs, a122]; exact ⟨rfl, rfl, rfl⟩
  have K24 : ∀ q, q.val ∉ [10, 11, 12] → reg m24 q = reg m16 q := fun q hq => by
    have hd' : q ∉ xrtU2.filterMap BInstr.dst := by
      simp only [xrtU2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [R24, runBlock_reg _ _ _ q u23.self.zero hd', K23 q (by intro h; apply hq; rw [h]; decide)
      (by intro h; apply hq; rw [h]; decide)]
  obtain ⟨m25, c25, pc25, mem25, regs25⟩ := u24'.callRa hc16 xrt_at_bc xrt_at_c0 (cb := DT) (by decide) (by decide)
  have r25 := PEnv.reg1 regs25 u24'.zero
  have hDn : DT.toNat = (img% dateTimeAddress) := by decide
  have hc2' : (c + 2).toNat = rp.toNat + t.header + 2 := by
    rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat, hcn]; omega
  have sPc2 : Sep (c + 2) (t.len - 2) R 0x60 := by
    rw [← hc, show rp + BitVec.ofNat 32 t.header + 2 = rp + BitVec.ofNat 32 (t.header + 2) by
      rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc]]
    exact sPG.sub (by omega)
  have sPc2' : Sep (c + 2) 10 R 0x60 := by
    rw [← hc, show rp + BitVec.ofNat 32 t.header + 2 = rp + BitVec.ofNat 32 (t.header + 2) by
      rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc]]
    exact sPG.sub (by omega)
  have hDT25 : CodeIn m25.mem DT dateTimeCode := by
    rw [mem25]; exact cd hcD (by rw [hDn]; decide) (by rw [hDn]; decide) I3
  have hTD25 : CodeIn m25.mem TD timeDigits2Code := by
    rw [mem25]; exact cd hcT (by rw [hTDn]; decide) (by rw [hTDn]; decide) I3
  have eF20 : F + 0x20 = R + BitVec.ofNat 32 0x50 := by rw [show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, eFk]
  have eF8 : F + 8 = R + BitVec.ofNat 32 0x38 := by rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, eFk]
  obtain ⟨m26, c26, pc26, sp26, K26, hS26, hN26, fr26⟩ := dateTime_correct m25 (sp0 := F) (out := F + 8)
    (d := F + 0x20) (p := c + 2) (Y := BitVec.ofNat 32 Yv) (retAddr := XRT + BitVec.ofNat 32 (0xBC + 8))
    (n := t.len - 2) hDT25 hTD25 pc25 (by rw [r25 a0 (by decide), v24.1]) (by rw [r25 a1 (by decide), v24.2.2])
    (by rw [r25 a2 (by decide), v24.2.1]) (by rw [regs25]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at XRT (by decide) _ (by decide))) (by rw [r25 sp (by decide), K24 sp (by decide), sp16])
    hFa (by omega) (by omega) (by rw [eF8, hRc _ (by decide)]; omega) hF8a (by rw [eF20, hRc _ (by decide)]; omega)
    (hFk 0x20 (by decide) (by decide)) (by omega) (by rw [mem25, hd0]) (by rw [mem25, hd4])
    (by rw [eF0, eF8]; have := offs (c := 0x38) (n := 16) (e := 0) (k := 0x30) (by omega) (by omega) (by omega)
        rwa [add_ofNat_zero] at this)
    (by rw [eF0, eF20]; have := offs (c := 0x50) (n := 8) (e := 0) (k := 0x30) (by omega) (by omega) (by omega)
        rwa [add_ofNat_zero] at this)
    (by rw [eF8, eF20]; exact offs (by omega) (by omega) (by omega))
    (by rw [eF0]; have := sPc2.subR (c := 0) (l := 0x30) (by omega); rwa [add_ofNat_zero] at this)
    (by rw [eF20]; exact sPc2.subR (by omega))
    (by rw [eF20]; exact (sPc2'.subR (c := 0x50) (l := 8) (by omega)).symm)
  rw [mem25] at hS26 hN26 fr26
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : Yv < 2 ^ 32)] at hS26 hN26
  have hmb3 : memBytes m16.mem (c + 2) (t.len - 2) = memBytes m.mem (c + 2) (t.len - 2) := by
    rw [← hc, show rp + BitVec.ofNat 32 t.header + 2 = rp + BitVec.ofNat 32 (t.header + 2) by
      rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc]]
    exact hmbx I3 _ _ (by omega)
  rw [hmb3] at hS26 hN26
  have hfr26 : ∀ x, Sep R 0x60 x 1 → Sep (F + 0xFFFFFFD0) 0x30 x 1 ∧ Sep (F + 8) 16 x 1 ∧ Sep (F + 0x20) 8 x 1 :=
    fun x hx => ⟨by rw [eF0]; have := inR (c := 0) (l := 0x30) hx (by decide); rwa [add_ofNat_zero] at this,
      by rw [eF8]; exact inR hx (by decide), by rw [eF20]; exact inR hx (by decide)⟩
  have I4 : ∀ x, Sep R 0x60 x 1 → Sep (d + 8) 8 x 1 → m26.mem x = m.mem x := fun x hx hx' => by
    obtain ⟨h1, h2, h3⟩ := hfr26 x hx; rw [fr26 x h1 h2 h3, I3 x hx hx']
  have S4 : ∀ c', 0x58 ≤ c' → c' < 0x60 → m26.mem (R + BitVec.ofNat 32 c') = Ms (R + BitVec.ofNat 32 c') :=
    fun c' h1 h2 => by
      have e1 : Sep (F + 0xFFFFFFD0) 0x30 (R + BitVec.ofNat 32 c') 1 := by
        rw [eF0]; have := offs (c := 0) (n := 0x30) (e := c') (k := 1) (by omega) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      have e2 : Sep (F + 8) 16 (R + BitVec.ofNat 32 c') 1 := by rw [eF8]; exact offs (by omega) (by omega) (by omega)
      have e3 : Sep (F + 0x20) 8 (R + BitVec.ofNat 32 c') 1 := by rw [eF20]; exact offs (by omega) (by omega) (by omega)
      rw [fr26 _ e1 e2 e3, S3 c' h1 h2]
  have dkeep : ∀ j, j < 8 → m26.mem (d + 8 + BitVec.ofNat 32 j) = m11.mem (d + 8 + BitVec.ofNat 32 j) := fun j hj => by
    have hx : Sep R 0x60 (d + 8 + BitVec.ofNat 32 j) 1 := (sDG.sub (c := j) (l := 1) (by omega)).symm
    obtain ⟨h1, h2, h3⟩ := hfr26 _ hx
    have e8 : Sep (F + 8) 8 (d + 8 + BitVec.ofNat 32 j) 1 := by
      have := h2.sub (c := 0) (l := 8) (by omega); rwa [add_ofNat_zero] at this
    have e24 : Sep (F + 0x24) 4 (d + 8 + BitVec.ofNat 32 j) 1 := by
      rw [show (0x24 : Word) = BitVec.ofNat 32 0x24 from rfl, eFk]; exact inR hx (by omega)
    have e20 : Sep (F + 0x20) 4 (d + 8 + BitVec.ofNat 32 j) 1 := by
      have := h3.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
    rw [fr26 _ h1 h2 h3, frm _ e8 h3, ← hM2, memStore32_get_sep e24, memStore32_get_sep e20]
  have hc26 := cdX I4
  have u26 : St m26.mem XRT m26 0xC4 (reg m26) := ⟨by rw [pc26], rfl, fun _ => rfl⟩
  have kk26 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m26 q = reg m q := fun q hq => by
    rw [K26 q (by revert hq; revert q; decide), r25 q (by revert hq; revert q; decide),
      K24 q (by revert hq; revert q; decide), kk16 q hq]
  have sp26' : reg m26 sp = F := sp26
  have r826 : reg m26 8 = out := by
    rw [K26 8 (by decide), r25 8 (by decide), K24 8 (by decide), r816]
  have pre26 : Steps m m26 :=
    pre16.trans (.cons d17 (.cons d18 (.cons d19 (.cons d20 (c21.trans (.cons d22 (.cons d23 (c24.trans
      (c25.trans c26)))))))))
  obtain ⟨m27, d27, u27⟩ := u26.lbu hc26 xrt_at_c4 (off' := 0xC8) (by decide)
  have a027 : reg m27 a0 = (m26.mem (F + 8)).zeroExtend 32 := by
    rw [u27.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp26']
  have K27 : ∀ q, q ≠ a0 → reg m27 q = reg m26 q := fun q hq => by rw [u27.regs, upd_ne' hq u26.zero]
  have hutc : utcTime (memBytes m.mem c t.len) = (readDateTime Yv (memBytes m.mem (c + 2) (t.len - 2))).bind
      fun tr => if tr.2 = [asciiZ] then some tr.1 else none := by
    rw [utcTime_eq, hr]; simp only [Option.bind]; rw [hYv]
  cases hdtm : readDateTime Yv (memBytes m.mem (c + 2) (t.len - 2)) with
  | none =>
    obtain ⟨t1, _⟩ := hN26 hdtm
    obtain ⟨m28, d28, u28⟩ := u27.self.taken hc26 0x68 xrt_at_c8 (by decide) (by rw [a027, t1, u27.self.zero]; rfl)
    exact errA6 (pre26.trans (.cons d27 (.single d28))) u28.self I4 S4 (by rw [u28.regs, K27 sp (by decide), sp26'])
      (by rw [u28.regs, K27 8 (by decide), r826]) (fun q hq => by rw [u28.regs, K27 q (by revert hq; revert q; decide), kk26 q hq])
      (by rw [hutc, hdtm]; rfl)
  | some tr =>
  obtain ⟨tt, rest2⟩ := tr
  obtain ⟨htt, t0, tlo, thi, hr2, hq2, hL2⟩ := hS26 tt rest2 hdtm
  obtain ⟨m28, d28, u28⟩ := u27.self.notTaken hc26 0xCA xrt_at_c8 (by decide) (by rw [a027, t0, u27.self.zero]; rfl)
  have r28 : ∀ q, reg m28 q = reg m27 q := u28.regs
  -- 0xCA: one byte left, and it is `Z`
  obtain ⟨m29, c29, u29⟩ := St.block xrtU3 u28.self hc26 xrtU3_end (by
    simp +decide only [BlockOk, BInstr.ok, xrtU3, and_true]; rw [r28, K27 sp (by decide), sp26']
    exact hFk 0x24 (by decide) (by decide))
  have R29 : ∀ q, reg m29 q = (runBlock xrtU3 (m26.mem, reg m28)).2 q := u29.regs
  have u29' : St m26.mem XRT m29 0xD0 (reg m29) := ⟨u29.pc, by rw [u29.mem]; rfl, fun _ => rfl⟩
  have v29 : reg m29 a1 = BitVec.ofNat 32 (t.len - 2 - 10) ∧ reg m29 a2 = 1 ∧ reg m29 a0 = 0x19 := by
    simp +decide only [R29, runBlock, BInstr.run, xrtU3, upd_app, ↓reduceIte]
    rw [r28, K27 sp (by decide), sp26', show F + 0x24 = F + 0x20 + 4 by rw [BitVec.add_assoc]; rfl, hL2]
    exact ⟨rfl, trivial⟩
  have K29 : ∀ q, q.val ∉ [10, 11, 12] → reg m29 q = reg m26 q := fun q hq => by
    have hd' : q ∉ xrtU3.filterMap BInstr.dst := by
      simp only [xrtU3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [R29, runBlock_reg _ _ _ q u28.self.zero hd', r28, K27 q (by intro h; apply hq; rw [h]; decide)]
  have pre29 : Steps m m29 := pre26.trans (.cons d27 (.cons d28 c29))
  have bad29 : ∀ {nn : Machine}, Steps m nn → St m26.mem XRT nn 0xA6 (reg nn) →
      (∀ q, q.val ∉ [10, 11, 12] → reg nn q = reg m26 q) → reg nn a0 = 0x19 → rest2 ≠ [asciiZ] → ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        (∀ t r, readTime (memBytes m.mem rp (rl' + 1)) = some (t, r) → t < 2 ^ 64 ∧ m'.mem out = 0 ∧
          memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
          memLoad32 m'.mem (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32) ∧
          ∃ k, k ≤ rl' + 1 ∧ memLoad32 m'.mem (d + 8) = rp + BitVec.ofNat 32 k ∧
            memLoad32 m'.mem (d + 0xC) = BitVec.ofNat 32 (rl' + 1 - k) ∧
            r = memBytes m.mem (rp + BitVec.ofNat 32 k) (rl' + 1 - k)) ∧
        (readTime (memBytes m.mem rp (rl' + 1)) = none → m'.mem out = 1) ∧
        ∀ x, Sep R 0x60 x 1 → Sep out 16 x 1 → Sep (d + 8) 8 x 1 → m'.mem x = m.mem x :=
    fun pre st hK ra0 hne => finA6 pre st I4 S4 (by rw [hK sp (by decide), sp26']) (by rw [hK 8 (by decide), r826])
      (fun q hq => by rw [hK q (by revert hq; revert q; decide), kk26 q hq])
      (by rw [hspec, hutc, hdtm]; simp only [Option.bind]; rw [if_neg hne]; rfl) ra0
  have ec12 : c + 2 + 10 = rp + BitVec.ofNat 32 (t.header + 12) := by
    rw [← hc, BitVec.add_assoc, BitVec.add_assoc, show (2 : Word) + 10 = BitVec.ofNat 32 12 from rfl, ofNat_add_ofNat]
  have hrest2 : rest2 = memBytes m.mem (c + 2 + 10) (t.len - 2 - 10) := by
    rw [hr2]
    by_cases h12 : 12 ≤ t.len
    · rw [ec12, hmbx I3 _ _ (by omega)]
    · rw [show t.len - 2 - 10 = 0 by omega, memBytes_zero, memBytes_zero]
  by_cases hl1 : t.len - 2 - 10 = 1
  rotate_left
  · obtain ⟨m30, d30, u30⟩ := u29'.taken hc26 0xA6 xrt_at_d0 (by decide) (by
      rw [v29.1, v29.2.1]; simp only [branchTaken, bne_iff_ne, ne_eq]
      intro e; have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl] at this
      exact hl1 (by omega))
    exact bad29 (pre29.trans (.single d30)) u30.self (fun q hq => by rw [u30.regs, K29 q hq])
      (by rw [u30.regs, v29.2.2]) (fun h => by
        have := congrArg List.length h; rw [hrest2, memBytes_length] at this; exact hl1 this)
  obtain ⟨m30, d30, u30⟩ := u29'.notTaken hc26 0xD4 xrt_at_d0 (by decide) (by
    rw [v29.1, v29.2.1, hl1]; rfl)
  obtain ⟨m31, c31, u31⟩ := St.block xrtU4 u30.self hc26 xrtU4_end (by
    simp +decide only [BlockOk, BInstr.ok, xrtU4, and_true]; rw [u30.regs, K29 sp (by decide), sp26']
    exact hFk 0x20 (by decide) (by decide))
  have R31 : ∀ q, reg m31 q = (runBlock xrtU4 (m26.mem, reg m30)).2 q := u31.regs
  have u31' : St m26.mem XRT m31 0xDE (reg m31) := ⟨u31.pc, by rw [u31.mem]; rfl, fun _ => rfl⟩
  have hz12 : m26.mem (c + 2 + 10) = m.mem (c + 2 + 10) := by
    rw [ec12]; exact brp I4 _ (by omega)
  have v31 : reg m31 a1 = aluEval .add ((m.mem (c + 2 + 10)).zeroExtend 32) 0xFFFFFFA6 := by
    simp +decide only [R31, runBlock, BInstr.run, xrtU4, upd_app, ↓reduceIte]
    rw [u30.regs, K29 sp (by decide), sp26', hq2, add_lit_zero, hz12]
  have K31 : ∀ q, q.val ∉ [10, 11, 12] → reg m31 q = reg m26 q := fun q hq => by
    have hd' : q ∉ xrtU4.filterMap BInstr.dst := by
      simp only [xrtU4, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [R31, runBlock_reg _ _ _ q u30.self.zero hd', u30.regs, K29 q hq]
  have a031 : reg m31 a0 = 0x19 := by
    rw [R31, runBlock_reg _ _ _ _ u30.self.zero (by decide), u30.regs, v29.2.2]
  have pre31 : Steps m m31 := pre29.trans (.cons d30 c31)
  have hr1 : rest2 = [(m.mem (c + 2 + 10)).toNat] := by
    rw [hrest2, hl1, memBytes_succ, memBytes_zero]
  by_cases hZ : (m.mem (c + 2 + 10)).toNat = 0x5A
  rotate_left
  · obtain ⟨m32, d32, u32⟩ := u31'.taken hc26 0xA6 xrt_at_de (by decide) (by
      rw [v31, u31'.zero, gnt_isZ, decide_eq_false hZ]; rfl)
    exact bad29 (pre31.trans (.single d32)) u32.self (fun q hq => by rw [u32.regs, K31 q hq])
      (by rw [u32.regs, a031]) (fun h => by rw [hr1] at h; simp only [List.cons.injEq, and_true] at h; exact hZ h)
  obtain ⟨m32, d32, u32⟩ := u31'.notTaken hc26 0xE0 xrt_at_de (by decide) (by
    rw [v31, u31'.zero, gnt_isZ, decide_eq_true hZ]; rfl)
  -- 0xE0: the time, and the tag 0
  have so8 : (out + 8).toNat % 4 = 0 := by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have so12 : (out + 0xC).toNat % 4 = 0 := by
    rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨m33, c33, u33⟩ := St.block xrtU5 u32.self hc26 xrtU5_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, xrtU5, upd_app, ↓reduceIte, and_true, true_and]
    simp only [u32.regs]; rw [K31 sp (by decide), sp26', K31 8 (by decide), r826]
    exact ⟨hFk 0x10 (by decide) (by decide), hFk 0x14 (by decide) (by decide), ⟨so8, sOC (c := 8) (l := 4) (by decide)⟩,
      so12, sOC (c := 0xC) (l := 4) (by decide)⟩)
  have R33 : ∀ q, reg m33 q = (runBlock xrtU5 (m26.mem, reg m32)).2 q := u33.regs
  have eM33 : (runBlock xrtU5 (m26.mem, reg m32)).1 = memStore32 (memStore32 m26.mem (out + 8)
      (BitVec.ofNat 32 (tt % 2 ^ 32))) (out + 0xC) (BitVec.ofNat 32 (tt / 2 ^ 32)) := by
    simp +decide only [runBlock, BInstr.run, xrtU5, upd_app, ↓reduceIte]
    simp only [u32.regs]; rw [K31 sp (by decide), sp26', K31 8 (by decide), r826,
      show F + 0x10 = F + 8 + 8 by rw [BitVec.add_assoc]; rfl, tlo,
      show F + 0x14 = F + 8 + 0xC by rw [BitVec.add_assoc]; rfl, thi]
  rw [eM33] at u33
  have so8T : Sep (out + 8) 4 XRT x509ReadTimeCode.length := sOC (c := 8) (l := 4) (by decide)
  have so12T : Sep (out + 0xC) 4 XRT x509ReadTimeCode.length := sOC (c := 0xC) (l := 4) (by decide)
  have hct33 := ((hc26.store32 (v := BitVec.ofNat 32 (tt % 2 ^ 32)) so8T).store32
    (v := BitVec.ofNat 32 (tt / 2 ^ 32)) so12T)
  obtain ⟨m34, d34, u34⟩ := u33.jump hct33 xrt_at_ea (off' := 0xAC) (by decide) (by rw [u33.pc]; decide)
  have R34 : ∀ q, reg m34 q = (runBlock xrtU5 (m26.mem, reg m32)).2 q := u34.regs
  have r834 : reg m34 8 = out := by
    rw [R34, runBlock_reg _ _ _ _ u32.self.zero (by decide), u32.regs, K31 8 (by decide), r826]
  have a034 : reg m34 a0 = 0 := by
    rw [R34]; simp +decide only [runBlock, BInstr.run, xrtU5, upd_app, ↓reduceIte]; rw [u32.self.zero]; rfl
  obtain ⟨m35, d35, u35⟩ := u34.self.sb hct33 xrt_at_ac (off' := 0xB0) (by decide)
  rw [r834, add_lit_zero, a034] at u35
  have sx8 : ∀ {x : Word}, Sep out 16 x 1 → Sep (out + 8) 4 x 1 := fun hx => hx.sub (c := 8) (l := 4) (by decide)
  have sx12 : ∀ {x : Word}, Sep out 16 x 1 → Sep (out + 0xC) 4 x 1 := fun hx => hx.sub (c := 0xC) (l := 4) (by decide)
  have K34 : ∀ q, q.val ∉ [10, 11, 12] → reg m34 q = reg m26 q := fun q hq => by
    have hd' : q ∉ xrtU5.filterMap BInstr.dst := by
      simp only [xrtU5, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [R34, runBlock_reg _ _ _ q u32.self.zero hd', u32.regs, K31 q hq]
  obtain ⟨mf, cf, pcf, spf, Kf, memf⟩ := exB0 u35.self (hct33.store8 so0) (by rw [u35.regs, K34 sp (by decide), sp26'])
    (fun c' h1 h2 => by
      rw [memStore8_ne (v := BitVec.extractLsb' 0 8 (0 : Word)) (xo0 (sRo h2)), memStore32_get_sep (sx12 (sRo h2)),
        memStore32_get_sep (sx8 (sRo h2)), S4 c' h1 h2])
    (fun q hq => by rw [u35.regs, K34 q (by revert hq; revert q; decide), kk26 q hq])
  have hutcOk : utcTime (memBytes m.mem c t.len) = some tt := by
    rw [hutc, hdtm]; simp only [Option.bind]; rw [if_pos (by rw [hr1, hZ]; rfl)]
  have s0_8 : Sep out 1 (out + 8) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 8) (k := 4) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have s0_12 : Sep out 1 (out + 0xC) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 0xC) (k := 4) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have s12_8 : Sep (out + 0xC) 4 (out + 8) 4 := sep_offsets out (c := 0xC) (n := 4) (d := 8) (k := 4) (by omega)
    (by omega) (by omega)
  have dfin : ∀ j, j < 8 → mf.mem (d + 8 + BitVec.ofNat 32 j) = m11.mem (d + 8 + BitVec.ofNat 32 j) := fun j hj => by
    have ho := sOD.subR (c := j) (l := 1) (by omega)
    rw [memf, memStore8_ne (xo0 ho), memStore32_get_sep (sx12 ho), memStore32_get_sep (sx8 ho), dkeep j hj]
  have hsub : BitVec.ofNat 32 (rl' + 1) - BitVec.ofNat 32 (t.header + t.len) =
      BitVec.ofNat 32 (rl' + 1 - (t.header + t.len)) := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
  refine ⟨mf, pre31.trans (.cons d32 (c33.trans (.cons d34 (.cons d35 cf)))), pcf, spf, Kf, fun t' r h => ?_,
    fun h => ?_, fun x hx hx1 hx2 => ?_⟩
  · rw [hspec, hutcOk] at h; simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨htt, by rw [memf, memStore8_same]; rfl, ?_, ?_, t.header + t.len, htb, ?_, ?_, rfl⟩
    · rw [memf, memLoad32_store8_sep s0_8, memLoad32_store32_sep s12_8, memLoad32_store32_same]
    · rw [memf, memLoad32_store8_sep s0_12, memLoad32_store32_same]
    · rw [← ld8']; exact memLoad32_congr fun j hj => dfin j (by omega)
    · rw [← hsub, ← ldC']
      exact memLoad32_congr fun j hj => by
        rw [show d + 0xC + BitVec.ofNat 32 j = d + 8 + BitVec.ofNat 32 (4 + j) by
          rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, show (8 : Word) = BitVec.ofNat 32 8 from rfl,
            add_ofNat_assoc, add_ofNat_assoc, show 8 + (4 + j) = 0xC + j by omega]]
        exact dfin _ (by omega)
  · rw [hspec, hutcOk] at h; cases h
  · rw [memf, memStore8_ne (xo0 hx1), memStore32_get_sep (sx12 hx1), memStore32_get_sep (sx8 hx1), I4 x hx hx2]


end C3.RV32
