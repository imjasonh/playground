import C3BootProofs.Proofs.ParseCur
import C3BootProofs.Proofs.ImageHelpers
import C3BootProofs.Proofs.Crc32

/-!
# `c3_verify::bootstate::decode`, as compiled

`decode` checks the record's CRC-32 over its first 28 bytes against the
last four, then reads it with a `Reader`: the magic `C3BS`, version 1, two
reserved bytes, the generation, the preferred slot, the trial slot, the
trial boots left, the confirmed bits, and twelve reserved bytes. It returns
`Result<State, Error>` through `a0`: the error byte at offset 0 and 2 at
offset 7 for `Err`, or the state for `Ok`, with the trial slot 2 for no
trial.

`bsErr` is what the compiled checks decide, in the code's own word
arithmetic, and `bsMem` is the memory they leave. `bootstateDecode_correct`
proves the function computes them, with each call through the callee's
theorem.
-/

namespace C3.RV32.Cur

open C3.Image

/-- The 28 bytes the record's checksum covers. -/
def bsBody (M : Word → BitVec 8) (b : Word) : List (BitVec 8) :=
  (List.range 28).map fun i => M (b + BitVec.ofNat 32 i)

/-- The record's stored checksum, assembled as the code does. -/
def bsSum (M : Word → BitVec 8) (b : Word) : Word :=
  ((M (b + 0x1D)).zeroExtend 32 <<< 8 ||| (M (b + 0x1C)).zeroExtend 32) |||
    ((M (b + 0x1E)).zeroExtend 32 <<< 16 ||| (M (b + 0x1F)).zeroExtend 32 <<< 24)

/-- The record's trial-slot byte, as the code compares it. -/
abbrev bsTrial (M : Word → BitVec 8) (b : Word) : Word := (M (b + 13)).zeroExtend 32 &&& 0xFF

/-- The error the compiled `decode` returns for the record at `b`, or `none`
when it accepts it. -/
def bsErr (M : Word → BitVec 8) (b : Word) : Option (BitVec 8) :=
  if !(crcBits (bsBody M b) == bsSum M b) then some 0x11
  else if !(mw M b 0 == 0x53423343) then some 2
  else if !(((M (b + 5)).zeroExtend 32 <<< 24 ||| (M (b + 4)).zeroExtend 32 <<< 16 : Word) >>> 16 == 1)
    then some 3
  else if !(allZero M (b + 6) 2) then some 4
  else if (1 : Word).ult ((M (b + 12)).zeroExtend 32 &&& 0xFF) then some 5
  else if !(allZero M (b + 16) 12) then some 4
  else if (3 : Word).ult (((M (b + 15)).zeroExtend 32 ||| (M (b + 14)).zeroExtend 32) &&& 0xFF) then some 5
  else if (bsTrial M b).ult 2 then none
  else if !(bsTrial M b + 0xFFFFFF01 == 0) then some 5
  else if !((M (b + 14)).zeroExtend 32 &&& 0xFF == 0) then some 5
  else none

/-- Memory after `decode` returns, outside the stack it uses. -/
def bsMem (M : Word → BitVec 8) (out b : Word) : Word → BitVec 8 :=
  match bsErr M b with
  | some e => memStore8 (memStore8 M out e) (out + 7) 2
  | none =>
    memStore8 (memStore8 (memStore8 (memStore8 (memStore32 M out (mw M b 8)) (out + 4)
      (if (bsTrial M b).ult 2 then M (b + 13) else 2)) (out + 5) (M (b + 14))) (out + 6) (M (b + 15)))
      (out + 7) (M (b + 12))

theorem zextByte_lo (x : BitVec 8) : (x.zeroExtend 32).extractLsb' 0 8 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (a := x.toNat) (b := 2 ^ 32) (by omega), Nat.mod_eq_of_lt this]

/-- Where the image puts `decode`. -/
abbrev BSD : Word := BitVec.ofNat 32 bootstateDecodeAddress

/-- The functions `decode` runs, where the image puts them. -/
structure BSCode (M : Word → BitVec 8) : Prop where
  decode : CodeIn M BSD bootstateDecodeCode
  crc : CodeIn M (BitVec.ofNat 32 crc32Address) crc32Code
  magic : CodeIn M (BitVec.ofNat 32 readerMagicAddress) readerMagicCode
  array4 : CodeIn M (BitVec.ofNat 32 readerArray4Address) readerArray4Code
  bytes : CodeIn M (BitVec.ofNat 32 readerBytesAddress) readerBytesCode
  version : CodeIn M (BitVec.ofNat 32 readerVersion1Address) readerVersion1Code
  u16 : CodeIn M (BitVec.ofNat 32 readerU16Address) readerU16Code
  reserved : CodeIn M (BitVec.ofNat 32 readerReservedAddress) readerReservedCode
  u32 : CodeIn M (BitVec.ofNat 32 readerU32Address) readerU32Code
  u8 : CodeIn M (BitVec.ofNat 32 readerU8Address) readerU8Code

set_option maxRecDepth 8000 in
theorem BSCode.hi {M M' : Word → BitVec 8} (c : BSCode M)
    (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) : BSCode M' :=
  ⟨c.decode.hi h (by decide) (by decide), c.crc.hi h (by decide) (by decide),
    c.magic.hi h (by decide) (by decide), c.array4.hi h (by decide) (by decide),
    c.bytes.hi h (by decide) (by decide), c.version.hi h (by decide) (by decide),
    c.u16.hi h (by decide) (by decide), c.reserved.hi h (by decide) (by decide),
    c.u32.hi h (by decide) (by decide), c.u8.hi h (by decide) (by decide)⟩

/-- `decode`'s stack: 112 bytes at `R`, its 64-byte frame at `G = R + 48`
and up to 48 bytes for its callees, below `0x40000000`, with the 32-byte
record at `b` apart from it. -/
structure BLay (R G b : Word) : Prop where
  hRG : G = R + BitVec.ofNat 32 48
  hR : R.toNat + 112 ≤ 0x40000000
  hG : G.toNat % 4 = 0
  hb : b ≠ 0 ∧ b.toNat + 28 ≤ 2 ^ 32
  hBS : Sep b 32 R 112

namespace BLay

variable {R G b : Word}

theorem g_ofs (L : BLay R G b) (c : Nat) : G + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (48 + c) := by
  rw [L.hRG, add_ofNat_assoc]

theorem r_eqs (L : BLay R G b) :
    G + 0xFFFFFFD0 = R ∧ G + 0xFFFFFFE0 = R + BitVec.ofNat 32 16 ∧ G + 0xFFFFFFF0 = R + BitVec.ofNat 32 32 ∧
    G + 0xC = R + BitVec.ofNat 32 60 ∧ G + 0xC + 8 = R + BitVec.ofNat 32 68 ∧
    G + 0x18 = R + BitVec.ofNat 32 72 := by
  rw [L.hRG]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [BitVec.add_assoc] <;> try rfl
  exact BitVec.add_zero R

theorem low (L : BLay R G b) (c n : Nat) (h : c + n ≤ 112) : (R + BitVec.ofNat 32 c).toNat + n ≤ 0x40000000 := by
  have := L.hR
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem hiS (L : BLay R G b) (x : Word) (hx : 0x40000000 ≤ x.toNat) : Sep R 112 x 1 :=
  sep_of_le (by have := L.hR; omega) (by have := x.isLt; omega)

theorem code {M0 Mx : Word → BitVec 8} (L : BLay R G b) (c0 : BSCode M0)
    (hO : ∀ x, Sep R 112 x 1 → Mx x = M0 x) : BSCode Mx :=
  c0.hi fun x hx => hO x (L.hiS x hx)

theorem lo (L : BLay R G b) {c n : Nat} (h : c + n ≤ 112) {a : Word} {l : Nat}
    (ha : 0x40000000 ≤ a.toNat) (hal : a.toNat + l ≤ 2 ^ 32) : Sep (R + BitVec.ofNat 32 c) n a l :=
  lowSep (L.low c n h) ha hal

theorem lo0 (L : BLay R G b) {n : Nat} (h : n ≤ 112) {a : Word} {l : Nat}
    (ha : 0x40000000 ≤ a.toNat) (hal : a.toNat + l ≤ 2 ^ 32) : Sep R n a l := by
  have := L.lo (c := 0) (n := n) (by omega) ha hal; rwa [add_ofNat_zero] at this

theorem buf (L : BLay R G b) {c n : Nat} (h : c + n ≤ 112) : Sep b 28 (R + BitVec.ofNat 32 c) n := by
  have := (L.hBS.sub (c := 0) (l := 28) (by omega)).subR (c := c) (l := n) h
  rwa [add_ofNat_zero] at this

theorem buf0 (L : BLay R G b) {n : Nat} (h : n ≤ 112) : Sep b 28 R n := by
  have := L.buf (c := 0) (n := n) (by omega); rwa [add_ofNat_zero] at this

/-- The frame bytes from `G + 0xC` on are apart from the callees' 48 bytes. -/
theorem frame (_L : BLay R G b) {c N : Nat} (hcN : c + N ≤ 48) {k l : Nat} (hk : 0xC ≤ k) (hkl : k + l ≤ 64) :
    Sep (R + BitVec.ofNat 32 c) N (R + BitVec.ofNat 32 (48 + k)) l :=
  sep_offsets R (Or.inl (by omega)) (by omega) (by omega)

end BLay
section
set_option maxRecDepth 20000
theorem bsd_at_0 : fetchRel bootstateDecodeCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem bsd_at_2 : fetchRel bootstateDecodeCode 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem bsd_at_4 : fetchRel bootstateDecodeCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem bsd_at_6 : fetchRel bootstateDecodeCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem bsd_at_8 : fetchRel bootstateDecodeCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem bsd_at_a : fetchRel bootstateDecodeCode 0xA = some (.store .sw sp (19 : Fin 32) 0x2C, 2) := by decide
theorem bsd_at_c : fetchRel bootstateDecodeCode 0xC = some (.store .sw sp (20 : Fin 32) 0x28, 2) := by decide
theorem bsd_at_e : fetchRel bootstateDecodeCode 0xE = some (.store .sw sp (21 : Fin 32) 0x24, 2) := by decide
theorem bsd_at_10 : fetchRel bootstateDecodeCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x20, 2) := by decide
theorem bsd_at_12 : fetchRel bootstateDecodeCode 0x12 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem bsd_at_14 : fetchRel bootstateDecodeCode 0x14 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem bsd_at_16 : fetchRel bootstateDecodeCode 0x16 = some (.alu .add a0 x0 a1, 2) := by decide
theorem bsd_at_18 : fetchRel bootstateDecodeCode 0x18 = some (.auipc ra 0x0, 4) := by decide
theorem bsd_at_1c : fetchRel bootstateDecodeCode 0x1C = some (.jalr ra ra 0x182, 4) := by decide
theorem bsd_at_20 : fetchRel bootstateDecodeCode 0x20 = some (.load .lbu a1 (9 : Fin 32) 0x1D, 4) := by decide
theorem bsd_at_24 : fetchRel bootstateDecodeCode 0x24 = some (.load .lbu a2 (9 : Fin 32) 0x1E, 4) := by decide
theorem bsd_at_28 : fetchRel bootstateDecodeCode 0x28 = some (.load .lbu a3 (9 : Fin 32) 0x1F, 4) := by decide
theorem bsd_at_2c : fetchRel bootstateDecodeCode 0x2C = some (.load .lbu a4 (9 : Fin 32) 0x1C, 4) := by decide
theorem bsd_at_30 : fetchRel bootstateDecodeCode 0x30 = some (.aluImm .sll a1 a1 0x8, 2) := by decide
theorem bsd_at_32 : fetchRel bootstateDecodeCode 0x32 = some (.aluImm .sll a2 a2 0x10, 2) := by decide
theorem bsd_at_34 : fetchRel bootstateDecodeCode 0x34 = some (.aluImm .sll a3 a3 0x18, 2) := by decide
theorem bsd_at_36 : fetchRel bootstateDecodeCode 0x36 = some (.alu .or a1 a1 a4, 2) := by decide
theorem bsd_at_38 : fetchRel bootstateDecodeCode 0x38 = some (.alu .or a2 a2 a3, 2) := by decide
theorem bsd_at_3a : fetchRel bootstateDecodeCode 0x3A = some (.alu .or a1 a1 a2, 2) := by decide
theorem bsd_at_3c : fetchRel bootstateDecodeCode 0x3C = some (.branch .bne a0 a1 0x72, 4) := by decide
theorem bsd_at_40 : fetchRel bootstateDecodeCode 0x40 = some (.aluImm .add a0 x0 0x1C, 2) := by decide
theorem bsd_at_42 : fetchRel bootstateDecodeCode 0x42 = some (.store .sw sp (9 : Fin 32) 0xC, 2) := by decide
theorem bsd_at_44 : fetchRel bootstateDecodeCode 0x44 = some (.store .sw sp a0 0x10, 2) := by decide
theorem bsd_at_46 : fetchRel bootstateDecodeCode 0x46 = some (.store .sw sp x0 0x14, 2) := by decide
theorem bsd_at_48 : fetchRel bootstateDecodeCode 0x48 = some (.lui a1 0x53423000, 4) := by decide
theorem bsd_at_4c : fetchRel bootstateDecodeCode 0x4C = some (.aluImm .add a1 a1 0x343, 4) := by decide
theorem bsd_at_50 : fetchRel bootstateDecodeCode 0x50 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem bsd_at_52 : fetchRel bootstateDecodeCode 0x52 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem bsd_at_56 : fetchRel bootstateDecodeCode 0x56 = some (.jalr ra ra 0xFFFFFEEA, 4) := by decide
theorem bsd_at_5a : fetchRel bootstateDecodeCode 0x5A = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem bsd_at_5c : fetchRel bootstateDecodeCode 0x5C = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem bsd_at_60 : fetchRel bootstateDecodeCode 0x60 = some (.aluImm .add a0 a0 0xFFFFFF01, 4) := by decide
theorem bsd_at_64 : fetchRel bootstateDecodeCode 0x64 = some (.branch .bne a0 x0 0x108, 4) := by decide
theorem bsd_at_68 : fetchRel bootstateDecodeCode 0x68 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem bsd_at_6a : fetchRel bootstateDecodeCode 0x6A = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem bsd_at_6e : fetchRel bootstateDecodeCode 0x6E = some (.jalr ra ra 0xFFFFFF24, 4) := by decide
theorem bsd_at_72 : fetchRel bootstateDecodeCode 0x72 = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem bsd_at_74 : fetchRel bootstateDecodeCode 0x74 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem bsd_at_78 : fetchRel bootstateDecodeCode 0x78 = some (.aluImm .add a0 a0 0xFFFFFF01, 4) := by decide
theorem bsd_at_7c : fetchRel bootstateDecodeCode 0x7C = some (.branch .bne a0 x0 0xF0, 2) := by decide
theorem bsd_at_7e : fetchRel bootstateDecodeCode 0x7E = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem bsd_at_80 : fetchRel bootstateDecodeCode 0x80 = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem bsd_at_82 : fetchRel bootstateDecodeCode 0x82 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem bsd_at_86 : fetchRel bootstateDecodeCode 0x86 = some (.jalr ra ra 0xFFFFFF70, 4) := by decide
theorem bsd_at_8a : fetchRel bootstateDecodeCode 0x8A = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem bsd_at_8c : fetchRel bootstateDecodeCode 0x8C = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem bsd_at_90 : fetchRel bootstateDecodeCode 0x90 = some (.aluImm .add a0 a0 0xFFFFFF01, 4) := by decide
theorem bsd_at_94 : fetchRel bootstateDecodeCode 0x94 = some (.branch .bne a0 x0 0xD8, 2) := by decide
theorem bsd_at_96 : fetchRel bootstateDecodeCode 0x96 = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem bsd_at_98 : fetchRel bootstateDecodeCode 0x98 = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem bsd_at_9a : fetchRel bootstateDecodeCode 0x9A = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem bsd_at_9e : fetchRel bootstateDecodeCode 0x9E = some (.jalr ra ra 0x5A8, 4) := by decide
theorem bsd_at_a2 : fetchRel bootstateDecodeCode 0xA2 = some (.load .lbu a0 sp 0x18, 4) := by decide
theorem bsd_at_a6 : fetchRel bootstateDecodeCode 0xA6 = some (.branch .beq a0 x0 0x16, 2) := by decide
theorem bsd_at_a8 : fetchRel bootstateDecodeCode 0xA8 = some (.load .lbu (9 : Fin 32) sp 0x19, 4) := by decide
theorem bsd_at_ac : fetchRel bootstateDecodeCode 0xAC = some (.jal x0 0xC0, 2) := by decide
theorem bsd_at_ae : fetchRel bootstateDecodeCode 0xAE = some (.aluImm .add a0 x0 0x11, 2) := by decide
theorem bsd_at_b0 : fetchRel bootstateDecodeCode 0xB0 = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem bsd_at_b2 : fetchRel bootstateDecodeCode 0xB2 = some (.store .sb (8 : Fin 32) a0 0x0, 4) := by decide
theorem bsd_at_b6 : fetchRel bootstateDecodeCode 0xB6 = some (.store .sb (8 : Fin 32) a1 0x7, 4) := by decide
theorem bsd_at_ba : fetchRel bootstateDecodeCode 0xBA = some (.jal x0 0xBC, 2) := by decide
theorem bsd_at_bc : fetchRel bootstateDecodeCode 0xBC = some (.load .lw (22 : Fin 32) sp 0x1C, 2) := by decide
theorem bsd_at_be : fetchRel bootstateDecodeCode 0xBE = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem bsd_at_c0 : fetchRel bootstateDecodeCode 0xC0 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem bsd_at_c4 : fetchRel bootstateDecodeCode 0xC4 = some (.jalr ra ra 0xFFFFFEF8, 4) := by decide
theorem bsd_at_c8 : fetchRel bootstateDecodeCode 0xC8 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem bsd_at_ca : fetchRel bootstateDecodeCode 0xCA = some (.alu .add (18 : Fin 32) x0 a1, 2) := by decide
theorem bsd_at_cc : fetchRel bootstateDecodeCode 0xCC = some (.branch .beq a0 x0 0x6, 2) := by decide
theorem bsd_at_ce : fetchRel bootstateDecodeCode 0xCE = some (.alu .add (9 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem bsd_at_d0 : fetchRel bootstateDecodeCode 0xD0 = some (.jal x0 0x9C, 2) := by decide
theorem bsd_at_d2 : fetchRel bootstateDecodeCode 0xD2 = some (.aluImm .and a0 (18 : Fin 32) 0xFF, 4) := by decide
theorem bsd_at_d6 : fetchRel bootstateDecodeCode 0xD6 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem bsd_at_d8 : fetchRel bootstateDecodeCode 0xD8 = some (.aluImm .add (9 : Fin 32) x0 0x5, 2) := by decide
theorem bsd_at_da : fetchRel bootstateDecodeCode 0xDA = some (.branch .bltu a1 a0 0x92, 4) := by decide
theorem bsd_at_de : fetchRel bootstateDecodeCode 0xDE = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem bsd_at_e0 : fetchRel bootstateDecodeCode 0xE0 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem bsd_at_e4 : fetchRel bootstateDecodeCode 0xE4 = some (.jalr ra ra 0xFFFFFED8, 4) := by decide
theorem bsd_at_e8 : fetchRel bootstateDecodeCode 0xE8 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem bsd_at_ea : fetchRel bootstateDecodeCode 0xEA = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem bsd_at_ec : fetchRel bootstateDecodeCode 0xEC = some (.branch .beq a0 x0 0x6, 2) := by decide
theorem bsd_at_ee : fetchRel bootstateDecodeCode 0xEE = some (.alu .add (9 : Fin 32) x0 (19 : Fin 32), 2) := by decide
theorem bsd_at_f0 : fetchRel bootstateDecodeCode 0xF0 = some (.jal x0 0x7C, 2) := by decide
theorem bsd_at_f2 : fetchRel bootstateDecodeCode 0xF2 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem bsd_at_f4 : fetchRel bootstateDecodeCode 0xF4 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem bsd_at_f8 : fetchRel bootstateDecodeCode 0xF8 = some (.jalr ra ra 0xFFFFFEC4, 4) := by decide
theorem bsd_at_fc : fetchRel bootstateDecodeCode 0xFC = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem bsd_at_fe : fetchRel bootstateDecodeCode 0xFE = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem bsd_at_100 : fetchRel bootstateDecodeCode 0x100 = some (.branch .beq a0 x0 0x6, 2) := by decide
theorem bsd_at_102 : fetchRel bootstateDecodeCode 0x102 = some (.alu .add (9 : Fin 32) x0 (20 : Fin 32), 2) := by decide
theorem bsd_at_104 : fetchRel bootstateDecodeCode 0x104 = some (.jal x0 0x68, 2) := by decide
theorem bsd_at_106 : fetchRel bootstateDecodeCode 0x106 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem bsd_at_108 : fetchRel bootstateDecodeCode 0x108 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem bsd_at_10c : fetchRel bootstateDecodeCode 0x10C = some (.jalr ra ra 0xFFFFFEB0, 4) := by decide
theorem bsd_at_110 : fetchRel bootstateDecodeCode 0x110 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem bsd_at_112 : fetchRel bootstateDecodeCode 0x112 = some (.alu .add (21 : Fin 32) x0 a1, 2) := by decide
theorem bsd_at_114 : fetchRel bootstateDecodeCode 0x114 = some (.branch .beq a0 x0 0x6, 2) := by decide
theorem bsd_at_116 : fetchRel bootstateDecodeCode 0x116 = some (.alu .add (9 : Fin 32) x0 (21 : Fin 32), 2) := by decide
theorem bsd_at_118 : fetchRel bootstateDecodeCode 0x118 = some (.jal x0 0x54, 2) := by decide
theorem bsd_at_11a : fetchRel bootstateDecodeCode 0x11A = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem bsd_at_11c : fetchRel bootstateDecodeCode 0x11C = some (.aluImm .add a1 x0 0xC, 2) := by decide
theorem bsd_at_11e : fetchRel bootstateDecodeCode 0x11E = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem bsd_at_122 : fetchRel bootstateDecodeCode 0x122 = some (.jalr ra ra 0xFFFFFED4, 4) := by decide
theorem bsd_at_126 : fetchRel bootstateDecodeCode 0x126 = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem bsd_at_12a : fetchRel bootstateDecodeCode 0x12A = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem bsd_at_12e : fetchRel bootstateDecodeCode 0x12E = some (.branch .beq a1 x0 0x6, 2) := by decide
theorem bsd_at_130 : fetchRel bootstateDecodeCode 0x130 = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem bsd_at_132 : fetchRel bootstateDecodeCode 0x132 = some (.jal x0 0x3A, 2) := by decide
theorem bsd_at_134 : fetchRel bootstateDecodeCode 0x134 = some (.load .lw a0 sp 0x10, 2) := by decide
theorem bsd_at_136 : fetchRel bootstateDecodeCode 0x136 = some (.load .lw a1 sp 0x14, 2) := by decide
theorem bsd_at_138 : fetchRel bootstateDecodeCode 0x138 = some (.branch .bne a1 a0 0x32, 4) := by decide
theorem bsd_at_13c : fetchRel bootstateDecodeCode 0x13C = some (.alu .or a0 (21 : Fin 32) (20 : Fin 32), 4) := by decide
theorem bsd_at_140 : fetchRel bootstateDecodeCode 0x140 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem bsd_at_144 : fetchRel bootstateDecodeCode 0x144 = some (.aluImm .add a1 x0 0x3, 2) := by decide
theorem bsd_at_146 : fetchRel bootstateDecodeCode 0x146 = some (.branch .bltu a1 a0 0x26, 4) := by decide
theorem bsd_at_14a : fetchRel bootstateDecodeCode 0x14A = some (.aluImm .and a0 (19 : Fin 32) 0xFF, 4) := by decide
theorem bsd_at_14e : fetchRel bootstateDecodeCode 0x14E = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem bsd_at_150 : fetchRel bootstateDecodeCode 0x150 = some (.branch .bgeu a0 a1 0x3A, 4) := by decide
theorem bsd_at_154 : fetchRel bootstateDecodeCode 0x154 = some (.store .sw (8 : Fin 32) (22 : Fin 32) 0x0, 4) := by decide
theorem bsd_at_158 : fetchRel bootstateDecodeCode 0x158 = some (.store .sb (8 : Fin 32) (19 : Fin 32) 0x4, 4) := by decide
theorem bsd_at_15c : fetchRel bootstateDecodeCode 0x15C = some (.store .sb (8 : Fin 32) (20 : Fin 32) 0x5, 4) := by decide
theorem bsd_at_160 : fetchRel bootstateDecodeCode 0x160 = some (.store .sb (8 : Fin 32) (21 : Fin 32) 0x6, 4) := by decide
theorem bsd_at_164 : fetchRel bootstateDecodeCode 0x164 = some (.store .sb (8 : Fin 32) (18 : Fin 32) 0x7, 4) := by decide
theorem bsd_at_168 : fetchRel bootstateDecodeCode 0x168 = some (.jal x0 0xE, 2) := by decide
theorem bsd_at_16a : fetchRel bootstateDecodeCode 0x16A = some (.aluImm .add (9 : Fin 32) x0 0x1, 2) := by decide
theorem bsd_at_16c : fetchRel bootstateDecodeCode 0x16C = some (.aluImm .add a0 x0 0x2, 2) := by decide
theorem bsd_at_16e : fetchRel bootstateDecodeCode 0x16E = some (.store .sb (8 : Fin 32) (9 : Fin 32) 0x0, 4) := by decide
theorem bsd_at_172 : fetchRel bootstateDecodeCode 0x172 = some (.store .sb (8 : Fin 32) a0 0x7, 4) := by decide
theorem bsd_at_176 : fetchRel bootstateDecodeCode 0x176 = some (.load .lw ra sp 0x3C, 2) := by decide
theorem bsd_at_178 : fetchRel bootstateDecodeCode 0x178 = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem bsd_at_17a : fetchRel bootstateDecodeCode 0x17A = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem bsd_at_17c : fetchRel bootstateDecodeCode 0x17C = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem bsd_at_17e : fetchRel bootstateDecodeCode 0x17E = some (.load .lw (19 : Fin 32) sp 0x2C, 2) := by decide
theorem bsd_at_180 : fetchRel bootstateDecodeCode 0x180 = some (.load .lw (20 : Fin 32) sp 0x28, 2) := by decide
theorem bsd_at_182 : fetchRel bootstateDecodeCode 0x182 = some (.load .lw (21 : Fin 32) sp 0x24, 2) := by decide
theorem bsd_at_184 : fetchRel bootstateDecodeCode 0x184 = some (.load .lw (22 : Fin 32) sp 0x20, 2) := by decide
theorem bsd_at_186 : fetchRel bootstateDecodeCode 0x186 = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem bsd_at_188 : fetchRel bootstateDecodeCode 0x188 = some (.jalr x0 ra 0x0, 2) := by decide
theorem bsd_at_18a : fetchRel bootstateDecodeCode 0x18A = some (.aluImm .add a0 a0 0xFFFFFF01, 4) := by decide
theorem bsd_at_18e : fetchRel bootstateDecodeCode 0x18E = some (.branch .bne a0 x0 0xFFFFFFDE, 2) := by decide
theorem bsd_at_190 : fetchRel bootstateDecodeCode 0x190 = some (.aluImm .and a0 (20 : Fin 32) 0xFF, 4) := by decide
theorem bsd_at_194 : fetchRel bootstateDecodeCode 0x194 = some (.branch .bne a0 x0 0xFFFFFFD8, 2) := by decide
theorem bsd_at_196 : fetchRel bootstateDecodeCode 0x196 = some (.aluImm .add (19 : Fin 32) x0 0x2, 2) := by decide
theorem bsd_at_198 : fetchRel bootstateDecodeCode 0x198 = some (.jal x0 0xFFFFFFBC, 2) := by decide
end

/-- After a callee that advanced the reader at `G + 0xC` to `e` and used
stack bytes `c` through `c + N` of `R`: the reader, the memory outside the
stack, and the saved slots. -/
theorem BLay.advance {R G b : Word} (Ly : BLay R G b) {M0 M2 Mx My : Word → BitVec 8} {e : Word} {c N : Nat}
    (hcN : c + N ≤ 48) (hrp : memLoad32 Mx (G + 0xC) = b) (hrl : memLoad32 Mx (G + 0xC + 4) = 28)
    (hO : ∀ x, Sep R 112 x 1 → Mx x = M0 x)
    (hS : ∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k))
    (hm : ∀ x, Sep (R + BitVec.ofNat 32 c) N x 1 → My x = memStore32 Mx (G + 0xC + 8) e x) :
    memLoad32 My (G + 0xC) = b ∧ memLoad32 My (G + 0xC + 4) = 28 ∧ memLoad32 My (G + 0xC + 8) = e ∧
    (∀ x, Sep R 112 x 1 → My x = M0 x) ∧
    (∀ k, 0x20 ≤ k → k < 0x40 → My (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) := by
  have fr : ∀ k, 0xC ≤ k → k < 64 → Sep (R + BitVec.ofNat 32 c) N (G + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    rw [Ly.g_ofs]; exact Ly.frame hcN h1 (by omega)
  have p20 : G + 0xC + 8 = G + BitVec.ofNat 32 20 := by rw [BitVec.add_assoc]; rfl
  have ld : ∀ k, 0xC ≤ k → k + 4 ≤ 64 → memLoad32 My (G + BitVec.ofNat 32 k) =
      memLoad32 (memStore32 Mx (G + BitVec.ofNat 32 20) e) (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, ← p20]; exact hm _ (fr (k + j) (by omega) (by omega))
  refine ⟨?_, ?_, ?_, fun x hx => ?_, fun k h1 h2 => ?_⟩
  · rw [show G + 0xC = G + BitVec.ofNat 32 12 from rfl, ld 12 (by omega) (by omega),
      memLoad32_store32_sep (sep_offsets G (c := 20) (n := 4) (d := 12) (k := 4) (by omega) (by omega) (by omega))]
    exact hrp
  · rw [show G + 0xC + 4 = G + BitVec.ofNat 32 16 from by rw [BitVec.add_assoc]; rfl, ld 16 (by omega) (by omega),
      memLoad32_store32_sep (sep_offsets G (c := 20) (n := 4) (d := 16) (k := 4) (by omega) (by omega) (by omega)),
      show G + BitVec.ofNat 32 16 = G + 0xC + 4 from by rw [BitVec.add_assoc]; rfl]
    exact hrl
  · rw [p20, ld 20 (by omega) (by omega)]; exact memLoad32_store32_same _ _ _
  · have hx' : Sep (R + BitVec.ofNat 32 c) N x 1 := hx.sub (c := c) (l := N) (by omega)
    rw [hm x hx', p20, memStore32_get_sep (by rw [Ly.g_ofs]; exact hx.sub (c := 48 + 20) (l := 4) (by omega)),
      hO x hx]
  · rw [hm _ (fr k (by omega) h2), p20,
      memStore32_get_sep (sep_offsets G (c := 20) (n := 4) (d := k) (k := 1) (by omega) (by omega) (by omega))]
    exact hS k h1 h2

/-- After `Reader::u32` with the result at `G + 0x18`: as `BLay.advance`,
with the result's tag and word in the frame. -/
theorem BLay.advance_u32 {R G b : Word} (Ly : BLay R G b) {M0 M2 Mx My : Word → BitVec 8} {e v : Word}
    (hrp : memLoad32 Mx (G + 0xC) = b) (hrl : memLoad32 Mx (G + 0xC + 4) = 28)
    (hO : ∀ x, Sep R 112 x 1 → Mx x = M0 x)
    (hS : ∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k))
    (hm : ∀ x, Sep R 48 x 1 → My x =
      memStore8 (memStore32 (memStore32 Mx (G + 0xC + 8) e) (G + 0x18 + 4) v) (G + 0x18) 0 x) :
    memLoad32 My (G + 0xC) = b ∧ memLoad32 My (G + 0xC + 4) = 28 ∧ memLoad32 My (G + 0xC + 8) = e ∧
    (∀ x, Sep R 112 x 1 → My x = M0 x) ∧
    (∀ k, 0x20 ≤ k → k < 0x40 → My (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) ∧
    My (G + 0x18) = 0 ∧ memLoad32 My (G + 0x1C) = v := by
  have fr : ∀ k, 0xC ≤ k → k < 64 → Sep R 48 (G + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    rw [Ly.g_ofs]; have := Ly.frame (c := 0) (N := 48) (by omega) h1 (l := 1) (by omega)
    rwa [add_ofNat_zero] at this
  have q20 : G + 0xC + 8 = G + BitVec.ofNat 32 20 := by rw [BitVec.add_assoc]; rfl
  have q1c : G + 0x18 + 4 = G + BitVec.ofNat 32 0x1C := by rw [BitVec.add_assoc]; rfl
  have q18 : G + 0x18 = G + BitVec.ofNat 32 0x18 := rfl
  rw [q20, q1c, q18] at hm
  have T : ∀ k, 0xC ≤ k → k < 64 → My (G + BitVec.ofNat 32 k) =
      memStore8 (memStore32 (memStore32 Mx (G + BitVec.ofNat 32 20) e) (G + BitVec.ofNat 32 0x1C) v)
        (G + BitVec.ofNat 32 0x18) 0 (G + BitVec.ofNat 32 k) := fun k h1 h2 => hm _ (fr k h1 h2)
  have so : ∀ a l c k, a + l ≤ c ∨ c + k ≤ a → a + l ≤ 64 → c + k ≤ 64 →
      Sep (G + BitVec.ofNat 32 a) l (G + BitVec.ofNat 32 c) k :=
    fun a l c k h h1 h2 => sep_offsets G h (by omega) (by omega)
  have ne : ∀ a c, a < 64 → c < 64 → a ≠ c → G + BitVec.ofNat 32 c ≠ G + BitVec.ofNat 32 a :=
    fun a c ha hc h => add_ofNat_ne G (by omega) (by omega) (Ne.symm h)
  have L : ∀ k, 0xC ≤ k → k + 4 ≤ 64 → memLoad32 My (G + BitVec.ofNat 32 k) =
      memLoad32 (memStore8 (memStore32 (memStore32 Mx (G + BitVec.ofNat 32 20) e) (G + BitVec.ofNat 32 0x1C) v)
        (G + BitVec.ofNat 32 0x18) 0) (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact T (k + j) (by omega) (by omega)
  refine ⟨?_, ?_, ?_, fun x hx => ?_, fun k h1 h2 => ?_, ?_, ?_⟩
  · rw [show G + 0xC = G + BitVec.ofNat 32 12 from rfl, L 12 (by omega) (by omega),
      memLoad32_store8_sep (so 0x18 1 12 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x1C 4 12 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 20 4 12 4 (by omega) (by omega) (by omega))]
    exact hrp
  · rw [show G + 0xC + 4 = G + BitVec.ofNat 32 16 from by rw [BitVec.add_assoc]; rfl, L 16 (by omega) (by omega),
      memLoad32_store8_sep (so 0x18 1 16 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x1C 4 16 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 20 4 16 4 (by omega) (by omega) (by omega)),
      show G + BitVec.ofNat 32 16 = G + 0xC + 4 from by rw [BitVec.add_assoc]; rfl]
    exact hrl
  · rw [q20, L 20 (by omega) (by omega),
      memLoad32_store8_sep (so 0x18 1 20 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x1C 4 20 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_same]
  · have hx' : Sep R 48 x 1 := by have := hx.sub (c := 0) (l := 48) (by omega); rwa [add_ofNat_zero] at this
    have g : ∀ a l, 0xC ≤ a → a + l ≤ 64 → Sep (G + BitVec.ofNat 32 a) l x 1 := fun a l h1 h2 => by
      rw [Ly.g_ofs]; exact hx.sub (c := 48 + a) (l := l) (by omega)
    have g1 : x ≠ G + BitVec.ofNat 32 0x18 := fun h => g 0x18 1 (by omega) (by omega) 0 (by omega) 0 (by omega)
      (by rw [add_ofNat_zero, add_ofNat_zero, h])
    rw [hm x hx', memStore8_ne g1, memStore32_get_sep (g 0x1C 4 (by omega) (by omega)),
      memStore32_get_sep (g 20 4 (by omega) (by omega)), hO x hx]
  · rw [T k (by omega) h2, memStore8_ne (ne 0x18 k (by omega) h2 (by omega)),
      memStore32_get_sep (so 0x1C 4 k 1 (by omega) (by omega) (by omega)),
      memStore32_get_sep (so 20 4 k 1 (by omega) (by omega) (by omega))]
    exact hS k h1 h2
  · rw [q18, T 0x18 (by omega) (by omega), memStore8_same]
  · rw [show G + 0x1C = G + BitVec.ofNat 32 0x1C from rfl, L 0x1C (by omega) (by omega),
      memLoad32_store8_sep (so 0x18 1 0x1C 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_same]

theorem bs_reg1 {f : Fin 32 → Word} {m1 : Machine} {L : Word}
    (regs : ∀ r, reg m1 r = upd f ra L r) (hz : f 0 = 0) : ∀ r, r ≠ ra → reg m1 r = f r := fun r h => by
  rw [regs]; exact updz hz h


/-- A call from `decode` to `Reader::magic` on the reader at `G + 0xC`. -/
theorem bs_magic {R G b : Word} (Ly : BLay R G b) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {k imm o : Word} (s : St Mx BSD m off f)
    (code : BSCode Mx)
    (h1 : fetchRel bootstateDecodeCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootstateDecodeCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : BSD + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 readerMagicAddress)
    (hl : (BSD + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 0xC) (ha1 : f a1 = k)
    (hrp : memLoad32 Mx (G + 0xC) = b) (hrl : memLoad32 Mx (G + 0xC + 4) = 28) :
    ∃ m', Steps m m' ∧ St m'.mem BSD m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = magicResult Mx (G + 0xC) k ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep R 48 x 1 → m'.mem x = magicMem Mx (G + 0xC) x := by
  obtain ⟨eR, -, -, e60, e68, -⟩ := Ly.r_eqs
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.decode h1 h2 hb (by decide)
  have r1 := bs_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := Cur.readerMagic_correct m1 (BitVec.ofNat 32 readerMagicAddress)
    (BSD + BitVec.ofNat 32 (off + 8)) (G + 0xC) k
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
    (aligned_add Ly.hG (k := 0xC) (by decide))
    (by rw [mem1, hrp, hrl]; exact ⟨Ly.hb.1, Ly.hb.2⟩)
    (by rw [sp1, eR]; exact Ly.lo0 (by omega) (by decide) (by decide))
    (by rw [sp1, eR]; exact Ly.lo0 (by omega) (by decide) (by decide))
    (by rw [sp1, eR]; exact Ly.lo0 (by omega) (by decide) (by decide))
    (by rw [e68]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e68]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e68]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, eR, e60]; have := Ly.frame (c := 0) (N := 48) (by omega) (k := 0xC) (l := 12) (by omega) (by omega)
        rw [add_ofNat_zero] at this; exact this.symm)
    (by rw [mem1, hrp, hrl, sp1, eR]; exact Ly.buf0 (by omega))
    (by rw [mem1, hrp, hrl, e68]; exact Ly.buf (by omega))
  rw [mem1] at a02 mem2
  rw [sp1, eR] at mem2
  rw [sp1] at sp2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, fun r h0 h1' h2' h3 h4 h5 h6 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5 h6, r1 r h7]

/-- A call from `decode` to `Reader::version_1` on the reader at `G + 0xC`. -/
theorem bs_version {R G b : Word} (Ly : BLay R G b) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o : Word} (s : St Mx BSD m off f)
    (code : BSCode Mx)
    (h1 : fetchRel bootstateDecodeCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootstateDecodeCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : BSD + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 readerVersion1Address)
    (hl : (BSD + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 0xC)
    (hrp : memLoad32 Mx (G + 0xC) = b) (hrl : memLoad32 Mx (G + 0xC + 4) = 28) :
    ∃ m', Steps m m' ∧ St m'.mem BSD m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = version1Result Mx (G + 0xC) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep (R + BitVec.ofNat 32 16) 32 x 1 → m'.mem x = u16Mem Mx (G + 0xC) x := by
  obtain ⟨-, e16, -, e60, e68, -⟩ := Ly.r_eqs
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.decode h1 h2 hb (by decide)
  have r1 := bs_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := readerVersion1_correct m1 (BitVec.ofNat 32 readerVersion1Address)
    (BSD + BitVec.ofNat 32 (off + 8)) (G + 0xC)
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
    (by rw [sp1]; exact Ly.hG) (aligned_add Ly.hG (k := 0xC) (by decide))
    (by rw [mem1, hrp, hrl]; exact ⟨Ly.hb.1, Ly.hb.2⟩)
    (by rw [sp1, e16]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e16]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e16]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e68]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e68]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e68]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e16, e60]; exact (Ly.frame (c := 16) (N := 32) (by omega) (k := 0xC) (l := 12) (by omega) (by omega)).symm)
    (by rw [mem1, hrp, hrl, sp1, e16]; exact Ly.buf (by omega))
    (by rw [mem1, hrp, hrl, e68]; exact Ly.buf (by omega))
  rw [mem1] at a02 mem2
  rw [sp1, e16] at mem2
  rw [sp1] at sp2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, fun r h0 h1' h2' h3 h4 h5 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5, r1 r h7]

/-- A call from `decode` to `Reader::reserved(n)` on the reader at `G + 0xC`. -/
theorem bs_reserved {R G b : Word} (Ly : BLay R G b) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {n imm o : Word} (s : St Mx BSD m off f)
    (code : BSCode Mx)
    (h1 : fetchRel bootstateDecodeCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootstateDecodeCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : BSD + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 readerReservedAddress)
    (hl : (BSD + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 0xC) (ha1 : f a1 = n) (hn : n ≠ 0)
    (hrp : memLoad32 Mx (G + 0xC) = b) (hrl : memLoad32 Mx (G + 0xC + 4) = 28) :
    ∃ m', Steps m m' ∧ St m'.mem BSD m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = reservedResult Mx (G + 0xC) n ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep (R + BitVec.ofNat 32 32) 16 x 1 → m'.mem x = reservedMem Mx (G + 0xC) n x := by
  obtain ⟨-, -, e32, e60, e68, -⟩ := Ly.r_eqs
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.decode h1 h2 hb (by decide)
  have r1 := bs_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := readerReserved_correct m1 (BitVec.ofNat 32 readerReservedAddress)
    (BSD + BitVec.ofNat 32 (off + 8)) (G + 0xC) n
    (fun i hi => by rw [mem1]; exact code.reserved i hi)
    (fun i hi => by
      rw [mem1, show (BitVec.ofNat 32 readerReservedAddress + 0x9C : Word) = BitVec.ofNat 32 readerBytesAddress
        from by decide]
      exact code.bytes i hi)
    (by decide) pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) hn
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl)
    (by rw [sp1]; exact Ly.hG) (aligned_add Ly.hG (k := 0xC) (by decide))
    (by rw [mem1, hrp, hrl]; exact ⟨Ly.hb.1, Ly.hb.2⟩)
    (by rw [sp1, e32]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e32]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e68]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e68]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e32, e60]; exact (Ly.frame (c := 32) (N := 16) (by omega) (k := 0xC) (l := 12) (by omega) (by omega)).symm)
    (by rw [mem1, hrp, hrl, sp1, e32]; exact Ly.buf (by omega))
    (by rw [mem1, hrp, hrl, e68]; exact Ly.buf (by omega))
  rw [mem1] at a02 mem2
  rw [sp1, e32] at mem2
  rw [sp1] at sp2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, fun r h0 h1' h2' h3 h4 h5 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5, r1 r h7]

/-- A call from `decode` to `Reader::u32` on the reader at `G + 0xC`, with
the result at `G + 0x18`. -/
theorem bs_u32 {R G b : Word} (Ly : BLay R G b) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o : Word} (s : St Mx BSD m off f)
    (code : BSCode Mx)
    (h1 : fetchRel bootstateDecodeCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootstateDecodeCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : BSD + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 readerU32Address)
    (hl : (BSD + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 0x18) (ha1 : f a1 = G + 0xC)
    (hrp : memLoad32 Mx (G + 0xC) = b) (hrl : memLoad32 Mx (G + 0xC + 4) = 28) :
    ∃ m', Steps m m' ∧ St m'.mem BSD m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep R 48 x 1 → m'.mem x = u32Mem Mx (G + 0x18) (G + 0xC) x := by
  obtain ⟨eR, -, -, e60, e68, e72⟩ := Ly.r_eqs
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.decode h1 h2 hb (by decide)
  have r1 := bs_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  obtain ⟨m2, c2, pc2, sp2, fr2, mem2⟩ := Cur.readerU32_correct m1 (BitVec.ofNat 32 readerU32Address)
    (BSD + BitVec.ofNat 32 (off + 8)) (G + 0x18) (G + 0xC)
    (fun i hi => by rw [mem1]; exact code.u32 i hi)
    (fun i hi => by
      rw [mem1, show (BitVec.ofNat 32 readerU32Address + 0xFFFFFAB6 : Word) = BitVec.ofNat 32 readerArray4Address
        from by decide]
      exact code.array4 i hi)
    (fun i hi => by
      rw [mem1, show (BitVec.ofNat 32 readerU32Address + 0xFFFFFAB6 + 0xFFFFFF96 : Word) =
        BitVec.ofNat 32 readerBytesAddress from by decide]
      exact code.bytes i hi)
    (by decide) pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by rw [sp1]; exact Ly.hG)
    (aligned_add Ly.hG (k := 0x18) (by decide)) (aligned_add Ly.hG (k := 0xC) (by decide))
    (by rw [mem1, hrp, hrl]; exact ⟨Ly.hb.1, Ly.hb.2⟩)
    (by rw [sp1, eR]; exact Ly.lo0 (by omega) (by decide) (by decide))
    (by rw [sp1, eR]; exact Ly.lo0 (by omega) (by decide) (by decide))
    (by rw [sp1, eR]; exact Ly.lo0 (by omega) (by decide) (by decide))
    (by rw [e72]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e68]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e68]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e68]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, eR, e60]; have := Ly.frame (c := 0) (N := 48) (by omega) (k := 0xC) (l := 12) (by omega) (by omega)
        rw [add_ofNat_zero] at this; exact this.symm)
    (by rw [sp1, eR, e72]; have := Ly.frame (c := 0) (N := 48) (by omega) (k := 0x18) (l := 8) (by omega) (by omega)
        rw [add_ofNat_zero] at this; exact this.symm)
    (by rw [mem1, hrp, hrl, sp1, eR]; exact Ly.buf0 (by omega))
    (by rw [mem1, hrp, hrl, e68]; exact Ly.buf (by omega))
  rw [mem1] at mem2
  rw [sp1, eR] at mem2
  rw [sp1] at sp2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun r h0 h1' h2' h3 h4 h5 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5, r1 r h7]

/-- A call from `decode` to `Reader::u8` on the reader at `G + 0xC`. -/
theorem bs_u8 {R G b : Word} (Ly : BLay R G b) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o : Word} (s : St Mx BSD m off f)
    (code : BSCode Mx)
    (h1 : fetchRel bootstateDecodeCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootstateDecodeCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : BSD + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 readerU8Address)
    (hl : (BSD + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 0xC)
    (hrp : memLoad32 Mx (G + 0xC) = b) (hrl : memLoad32 Mx (G + 0xC + 4) = 28) :
    ∃ m', Steps m m' ∧ St m'.mem BSD m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = (u8Result Mx (G + 0xC)).1 ∧ reg m' a1 = (u8Result Mx (G + 0xC)).2 ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep (R + BitVec.ofNat 32 32) 16 x 1 → m'.mem x = reservedMem Mx (G + 0xC) 1 x := by
  obtain ⟨-, -, e32, e60, e68, -⟩ := Ly.r_eqs
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.decode h1 h2 hb (by decide)
  have r1 := bs_reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  obtain ⟨m2, c2, pc2, sp2, a02, a12, fr2, mem2⟩ := readerU8_correct m1 (BitVec.ofNat 32 readerU8Address)
    (BSD + BitVec.ofNat 32 (off + 8)) (G + 0xC)
    (fun i hi => by rw [mem1]; exact code.u8 i hi)
    (fun i hi => by
      rw [mem1, show (BitVec.ofNat 32 readerU8Address + 0xD6 : Word) = BitVec.ofNat 32 readerBytesAddress
        from by decide]
      exact code.bytes i hi)
    (by decide) pc1 (by rw [r1 a0 (by decide), ha0])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl)
    (by rw [sp1]; exact Ly.hG) (aligned_add Ly.hG (k := 0xC) (by decide))
    (by rw [mem1, hrp, hrl]; exact ⟨Ly.hb.1, Ly.hb.2⟩)
    (by rw [sp1, e32]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e32]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e68]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [e68]; exact Ly.lo (by omega) (by decide) (by decide))
    (by rw [sp1, e32, e60]; exact (Ly.frame (c := 32) (N := 16) (by omega) (k := 0xC) (l := 12) (by omega) (by omega)).symm)
    (by rw [mem1, hrp, hrl, sp1, e32]; exact Ly.buf (by omega))
    (by rw [mem1, hrp, hrl, e68]; exact Ly.buf (by omega))
  rw [mem1] at a02 a12 mem2
  rw [sp1, e32] at mem2
  rw [sp1] at sp2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, a12,
    fun r h0 h1' h2' h3 h4 h5 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5, r1 r h7]


theorem bytesResult_at' (bp : Word) (p n : Nat) (h : p + n ≤ 28) :
    bytesResult bp 28 (BitVec.ofNat 32 p) (BitVec.ofNat 32 n) =
      some (bp + BitVec.ofNat 32 p, BitVec.ofNat 32 p + BitVec.ofNat 32 n) := by
  rw [bytesResult_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), show (28 : Word).toNat = 28 from rfl]
  simp only [h, ↓reduceIte]

theorem bs_version_val {Mx M : Word → BitVec 8} {self bp : Word} (hp : memLoad32 Mx self = bp)
    (hl : memLoad32 Mx (self + 4) = 28) (hq : memLoad32 Mx (self + 8) = 4)
    (h4 : Mx (bp + 4) = M (bp + 4)) (h5 : Mx (bp + 5) = M (bp + 5)) :
    version1Result Mx self =
      if ((M (bp + 5)).zeroExtend 32 <<< 24 ||| (M (bp + 4)).zeroExtend 32 <<< 16 : Word) >>> 16 == 1
      then 0xFFFFFFFF else 3 := by
  have hb : bytesResult bp 28 4 2 = some (bp + 4, 4 + 2) := rfl
  unfold version1Result u16Result
  rw [hp, hl, hq]
  have h5' : Mx (bp + 4 + 1) = M (bp + 5) := by
    rw [show bp + 4 + 1 = bp + 5 from by rw [BitVec.add_assoc]; rfl]; exact h5
  simp only [hb, h5', h4]

theorem bs_u16Mem_val {Mx : Word → BitVec 8} {self bp : Word} (hp : memLoad32 Mx self = bp)
    (hl : memLoad32 Mx (self + 4) = 28) (hq : memLoad32 Mx (self + 8) = 4) (x : Word) :
    u16Mem Mx self x = memStore32 Mx (self + 8) 6 x := by
  have hb : bytesResult bp 28 4 2 = some (bp + 4, 6) := rfl
  unfold u16Mem; rw [hp, hl, hq]; simp only [hb]

/-- `Reader::reserved(n)` on the reader over the 28 bytes at `bp`, at
position `p`, when `n` bytes are left. -/
theorem bs_reserved_val {Mx M : Word → BitVec 8} {self bp : Word} (p n : Nat) (hpn : p + n ≤ 28)
    (hp : memLoad32 Mx self = bp) (hl : memLoad32 Mx (self + 4) = 28)
    (hq : memLoad32 Mx (self + 8) = BitVec.ofNat 32 p)
    (hz : ∀ i, i < n → Mx (bp + BitVec.ofNat 32 (p + i)) = M (bp + BitVec.ofNat 32 (p + i))) :
    reservedResult Mx self (BitVec.ofNat 32 n) =
      if allZero M (bp + BitVec.ofNat 32 p) n then 0xFF else 4 := by
  have hb : bytesResult bp 28 (BitVec.ofNat 32 p) (BitVec.ofNat 32 n) =
      some (bp + BitVec.ofNat 32 p, BitVec.ofNat 32 p + BitVec.ofNat 32 n) := bytesResult_at' bp p n hpn
  unfold reservedResult; rw [hp, hl, hq]; simp only [hb]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    allZero_congr (M' := Mx) (M := M) n _ fun i hi => by rw [add_ofNat_assoc]; exact hz i hi]

theorem bs_reservedMem_val {Mx : Word → BitVec 8} {self bp : Word} (p n : Nat) (hpn : p + n ≤ 28)
    (hp : memLoad32 Mx self = bp) (hl : memLoad32 Mx (self + 4) = 28)
    (hq : memLoad32 Mx (self + 8) = BitVec.ofNat 32 p) (x : Word) :
    reservedMem Mx self (BitVec.ofNat 32 n) x = memStore32 Mx (self + 8) (BitVec.ofNat 32 (p + n)) x := by
  have hb := bytesResult_at' bp p n hpn
  unfold reservedMem; rw [hp, hl, hq]; simp only [hb]; rw [ofNat_add_ofNat]

theorem bs_u8_val {Mx : Word → BitVec 8} {self bp : Word} (p : Nat) (hpn : p + 1 ≤ 28)
    (hp : memLoad32 Mx self = bp) (hl : memLoad32 Mx (self + 4) = 28)
    (hq : memLoad32 Mx (self + 8) = BitVec.ofNat 32 p) :
    u8Result Mx self = (0, (Mx (bp + BitVec.ofNat 32 p)).zeroExtend 32) := by
  have hb : bytesResult bp 28 (BitVec.ofNat 32 p) 1 = some (bp + BitVec.ofNat 32 p, BitVec.ofNat 32 p + 1) :=
    bytesResult_at' bp p 1 hpn
  unfold u8Result; rw [hp, hl, hq]; simp only [hb]

/-- `decode`'s test after `magic`, `version_1`, and `reserved`: `mv s1, a0;
andi a0, a0, 0xFF; addi a0, a0, -0xFF; bne a0, x0` continues when the low
byte of `a0` is 0xFF and goes to the error path at 0x16C otherwise, with the
result in `s1`. -/
theorem bs_check {Mx : Word → BitVec 8} {base : Word} {m : Machine} {off off' : Nat} {f : Fin 32 → Word}
    {o len : Word} (s : St Mx base m off f) (hc : CodeIn Mx base bootstateDecodeCode)
    (h0 : fetchRel bootstateDecodeCode off = some (.alu .add (9 : Fin 32) x0 a0, 2))
    (h1 : fetchRel bootstateDecodeCode (off + 2) = some (.aluImm .and a0 a0 0xFF, 4))
    (h2 : fetchRel bootstateDecodeCode (off + 6) = some (.aluImm .add a0 a0 0xFFFFFF01, 4))
    (h3 : fetchRel bootstateDecodeCode (off + 10) = some (.branch .bne a0 x0 o, len))
    (hn : BitVec.ofNat 32 (off + 10) + len = BitVec.ofNat 32 off')
    (ho : BitVec.ofNat 32 (off + 10) + o = BitVec.ofNat 32 0x16C) :
    ∃ m' g, Steps m m' ∧ (∀ r, r ≠ a0 → r ≠ 9 → g r = f r) ∧ g 9 = f a0 ∧
      ((f a0 &&& 0xFF = 0xFF ∧ St Mx base m' off' g) ∨ (f a0 &&& 0xFF ≠ 0xFF ∧ St Mx base m' 0x16C g)) := by
  have hz := s.zero
  obtain ⟨m0, e0, t0'⟩ := s.alu hc h0 (off' := off + 2) (ofNat_add_ofNat off 2)
  have u0 := t0'.self
  obtain ⟨m1, e1, t1⟩ := u0.aluImm hc h1 (off' := off + 6) (by rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_ofNat])
  have u1 := t1.self
  obtain ⟨m2, e2, t2⟩ := u1.aluImm hc h2 (off' := off + 10) (by rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_ofNat])
  have v0 : reg m0 a0 = f a0 := by rw [t0'.regs, updz hz (by decide)]
  have w0 : reg m0 9 = f a0 := by
    rw [t0'.regs]; simp +decide only [upd, ite_true, ite_false]; rw [hz]; exact BitVec.zero_add _
  have g2 : ∀ r, r ≠ a0 → r ≠ 9 → reg m2 r = f r := fun r h h9 => by
    rw [t2.regs, updz u1.zero h, t1.regs, updz u0.zero h, t0'.regs, updz hz h9]
  have v2 : reg m2 a0 = (f a0 &&& 0xFF) + 0xFFFFFF01 := by
    rw [t2.regs]; simp +decide only [upd, ite_true, ite_false]; rw [t1.regs]
    simp +decide only [upd, ite_true, ite_false]; rw [v0]; rfl
  have w2 : reg m2 9 = f a0 := by rw [t2.regs, updz u1.zero (by decide), t1.regs, updz u0.zero (by decide), w0]
  have u2 := t2.self
  by_cases h : f a0 &&& 0xFF = 0xFF
  · obtain ⟨m3, e3, t3⟩ := u2.notTaken hc off' h3 hn (by rw [v2, u2.zero, h]; decide)
    exact ⟨m3, _, .cons e0 (.cons e1 (.cons e2 (.single e3))), g2, w2, .inl ⟨h, t3⟩⟩
  · have hne : (f a0 &&& 0xFF) + 0xFFFFFF01 ≠ 0 := fun e => h (by
      have := congrArg (· + 0xFF) e
      simp only [BitVec.add_assoc] at this
      rw [show (0xFFFFFF01 : Word) + 0xFF = 0 from rfl] at this
      exact (BitVec.add_zero _).symm.trans (this.trans (BitVec.zero_add _)))
    obtain ⟨m3, e3, t3⟩ := u2.taken hc 0x16C h3 ho (by rw [v2, u2.zero]; exact bne_iff_ne.mpr hne)
    exact ⟨m3, _, .cons e0 (.cons e1 (.cons e2 (.single e3))), g2, w2, .inr ⟨h, t3⟩⟩

/-- The registers `decode` writes before it restores the saved ones. -/
abbrev bsClob : List (Fin 32) := [a0, a1, a2, a3, a4, a5, a6, t0, ra, sp, s0, s1, s2, s3, s4, s5, s6]

theorem bs_clob_ne {r q : Fin 32} (hr : r ∉ bsClob) (hq : q ∈ bsClob) : r ≠ q := fun h => hr (h ▸ hq)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **`bootstate::decode`, as compiled**: with its callees where the image
puts them, 112 bytes of stack below `sp` (below `0x40000000`), the 32-byte
record at `b` apart from that stack, and the 8-byte result at `out` apart
from it and below `0x40000000`, it returns to `ra` with `sp` and every
register but `a0` through `a6` and `t0` restored, and memory outside its
stack as `bsMem` says. -/
theorem bootstateDecode_correct (m : Machine) {retAddr out b : Word}
    (code : BSCode m.mem) (hpc : m.pc = BSD)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = b) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 4 = 0) (hsl : 112 ≤ (reg m sp).toNat) (hsw : (reg m sp).toNat ≤ 0x40000000)
    (hb : b ≠ 0 ∧ b.toNat + 28 ≤ 2 ^ 32) (hBS : Sep b 32 (reg m sp + 0xFFFFFF90) 112)
    (hout : out.toNat % 4 = 0) (how : out.toNat + 8 ≤ 0x40000000)
    (hOS : Sep out 8 (reg m sp + 0xFFFFFF90) 112) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ t0 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFF90) 112 x 1 → m'.mem x = bsMem m.mem out b x := by
  obtain ⟨R, hRd⟩ : ∃ R, reg m sp + 0xFFFFFF90 = R := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G, reg m sp + 0xFFFFFFC0 = G := ⟨_, rfl⟩
  rw [hRd] at hBS hOS ⊢
  have hRn : R.toNat = (reg m sp).toNat - 112 := by
    rw [← hRd, BitVec.toNat_add, show (0xFFFFFF90 : Word).toNat = 2 ^ 32 - 112 from rfl]; omega
  have hGn : G.toNat = (reg m sp).toNat - 64 := by
    rw [← hGd, BitVec.toNat_add, show (0xFFFFFFC0 : Word).toNat = 2 ^ 32 - 64 from rfl]; omega
  have hRG : G = R + BitVec.ofNat 32 48 := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hGn, hRn]; omega)
  have hspG : G + 0x40 = reg m sp := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, show (0x40 : Word).toNat = 0x40 from rfl, hGn]; omega)
  have hGa : G.toNat % 4 = 0 := by omega
  have Ly : BLay R G b := ⟨hRG, by omega, hGa, hb, hBS⟩
  have hc := code.decode
  have fr : ∀ c l, c + l ≤ 0x40 → ∀ (x : Word) (n : Nat), Sep R 112 x n → Sep (G + BitVec.ofNat 32 c) l x n :=
    fun c l h x n hx => by rw [hRG, add_ofNat_assoc]; exact hx.sub (c := 48 + c) (l := l) (by omega)
  have gLow : ∀ c, c + 4 ≤ 0x40 → (G + BitVec.ofNat 32 c).toNat + 4 ≤ 0x40000000 := fun c h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have s0' : St m.mem BSD m 0 (reg m) := ⟨by rw [hpc]; rfl, rfl, fun _ => rfl⟩
  have hz := s0'.zero
  obtain ⟨m1, e1, t1⟩ := s0'.aluImm hc bsd_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFC0 = G from hGd] at t1
  have u1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp G r = reg m r := fun r h => updz hz h
  obtain ⟨m2, e2, t2⟩ := t1.sw hc bsd_at_2 (off' := 0x4) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x3C) (by decide))
  rw [u1sp, f1 ra (by decide)] at t2
  have hc2 := hc.store32 (v := reg m ra) (lowSep (gLow 0x3C (by omega)) (by decide) (by decide))
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 bsd_at_4 (off' := 0x6) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x38) (by decide))
  rw [u1sp, f1 8 (by decide)] at t3
  have hc3 := hc2.store32 (v := reg m 8) (lowSep (gLow 0x38 (by omega)) (by decide) (by decide))
  obtain ⟨m4, e4, t4⟩ := t3.sw hc3 bsd_at_6 (off' := 0x8) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x34) (by decide))
  rw [u1sp, f1 9 (by decide)] at t4
  have hc4 := hc3.store32 (v := reg m 9) (lowSep (gLow 0x34 (by omega)) (by decide) (by decide))
  obtain ⟨m5, e5, t5⟩ := t4.sw hc4 bsd_at_8 (off' := 0xA) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x30) (by decide))
  rw [u1sp, f1 18 (by decide)] at t5
  have hc5 := hc4.store32 (v := reg m 18) (lowSep (gLow 0x30 (by omega)) (by decide) (by decide))
  obtain ⟨m6, e6, t6⟩ := t5.sw hc5 bsd_at_a (off' := 0xC) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x2C) (by decide))
  rw [u1sp, f1 19 (by decide)] at t6
  have hc6 := hc5.store32 (v := reg m 19) (lowSep (gLow 0x2C (by omega)) (by decide) (by decide))
  obtain ⟨m7, e7, t7⟩ := t6.sw hc6 bsd_at_c (off' := 0xE) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x28) (by decide))
  rw [u1sp, f1 20 (by decide)] at t7
  have hc7 := hc6.store32 (v := reg m 20) (lowSep (gLow 0x28 (by omega)) (by decide) (by decide))
  obtain ⟨m8, e8, t8⟩ := t7.sw hc7 bsd_at_e (off' := 0x10) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x24) (by decide))
  rw [u1sp, f1 21 (by decide)] at t8
  have hc8 := hc7.store32 (v := reg m 21) (lowSep (gLow 0x24 (by omega)) (by decide) (by decide))
  obtain ⟨m9, e9, t9⟩ := t8.sw hc8 bsd_at_10 (off' := 0x12) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x20) (by decide))
  rw [u1sp, f1 22 (by decide)] at t9
  obtain ⟨M8, hM8⟩ : ∃ M8, memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (m.mem) (G + 0x3C) (reg m ra)) (G + 0x38) (reg m 8)) (G + 0x34) (reg m 9)) (G + 0x30) (reg m 18)) (G + 0x2C) (reg m 19)) (G + 0x28) (reg m 20)) (G + 0x24) (reg m 21)) (G + 0x20) (reg m 22) = M8 := ⟨_, rfl⟩
  rw [hM8] at t9
  have hc8 : CodeIn M8 BSD bootstateDecodeCode := by
    rw [← hM8]; exact hc8.store32 (lowSep (gLow 0x20 (by omega)) (by decide) (by decide))
  have M8out : ∀ x, Sep R 112 x 1 → M8 x = m.mem x := fun x hx => by
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
  have exit176 : ∀ (n : Machine) (Mx : Word → BitVec 8) (g : Fin 32 → Word),
      Steps m n → St Mx BSD n 0x176 g → CodeIn Mx BSD bootstateDecodeCode → g sp = G →
      (∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M8 (G + BitVec.ofNat 32 k)) →
      (∀ r, r ∉ bsClob → g r = reg m r) →
      (∀ x, Sep R 112 x 1 → Mx x = bsMem m.mem out b x) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ t0 → reg m' r = reg m r) ∧
        ∀ x, Sep R 112 x 1 → m'.mem x = bsMem m.mem out b x := by
    intro n Mx g hn u0 hcf hs hF hk hm
    have ldF : ∀ c, 0x20 ≤ c → c + 4 ≤ 0x40 →
        memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M8 (G + BitVec.ofNat 32 c) :=
      fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hF _ (by omega) (by omega)
    obtain ⟨n1, d1, u1⟩ := u0.lw hcf bsd_at_176 (off' := 0x178) (by decide)
      (by rw [hs]; exact aligned_add hGa (k := 0x3C) (by decide))
    rw [hs, show memLoad32 Mx (G + 0x3C) = reg m ra from
      (ldF 0x3C (by omega) (by omega)).trans fl3c] at u1
    have q1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [u1.regs]; exact updz u0.zero h
    have w1 : reg n1 ra = reg m ra := by rw [u1.regs]; simp +decide only [upd, ite_true, ite_false]
    have p1 : reg n1 sp = G := by rw [q1 sp (by decide)]; exact hs
    obtain ⟨n2, d2, u2⟩ := u1.self.lw hcf bsd_at_178 (off' := 0x17A) (by decide)
      (by rw [p1]; exact aligned_add hGa (k := 0x38) (by decide))
    rw [p1, show memLoad32 Mx (G + 0x38) = reg m 8 from
      (ldF 0x38 (by omega) (by omega)).trans fl38] at u2
    have q2 : ∀ r, r ≠ 8 → reg n2 r = reg n1 r := fun r h => by rw [u2.regs]; exact updz u1.self.zero h
    have w2 : reg n2 8 = reg m 8 := by rw [u2.regs]; simp +decide only [upd, ite_true, ite_false]
    have p2 : reg n2 sp = G := by rw [q2 sp (by decide)]; exact p1
    obtain ⟨n3, d3, u3⟩ := u2.self.lw hcf bsd_at_17a (off' := 0x17C) (by decide)
      (by rw [p2]; exact aligned_add hGa (k := 0x34) (by decide))
    rw [p2, show memLoad32 Mx (G + 0x34) = reg m 9 from
      (ldF 0x34 (by omega) (by omega)).trans fl34] at u3
    have q3 : ∀ r, r ≠ 9 → reg n3 r = reg n2 r := fun r h => by rw [u3.regs]; exact updz u2.self.zero h
    have w3 : reg n3 9 = reg m 9 := by rw [u3.regs]; simp +decide only [upd, ite_true, ite_false]
    have p3 : reg n3 sp = G := by rw [q3 sp (by decide)]; exact p2
    obtain ⟨n4, d4, u4⟩ := u3.self.lw hcf bsd_at_17c (off' := 0x17E) (by decide)
      (by rw [p3]; exact aligned_add hGa (k := 0x30) (by decide))
    rw [p3, show memLoad32 Mx (G + 0x30) = reg m 18 from
      (ldF 0x30 (by omega) (by omega)).trans fl30] at u4
    have q4 : ∀ r, r ≠ 18 → reg n4 r = reg n3 r := fun r h => by rw [u4.regs]; exact updz u3.self.zero h
    have w4 : reg n4 18 = reg m 18 := by rw [u4.regs]; simp +decide only [upd, ite_true, ite_false]
    have p4 : reg n4 sp = G := by rw [q4 sp (by decide)]; exact p3
    obtain ⟨n5, d5, u5⟩ := u4.self.lw hcf bsd_at_17e (off' := 0x180) (by decide)
      (by rw [p4]; exact aligned_add hGa (k := 0x2C) (by decide))
    rw [p4, show memLoad32 Mx (G + 0x2C) = reg m 19 from
      (ldF 0x2C (by omega) (by omega)).trans fl2c] at u5
    have q5 : ∀ r, r ≠ 19 → reg n5 r = reg n4 r := fun r h => by rw [u5.regs]; exact updz u4.self.zero h
    have w5 : reg n5 19 = reg m 19 := by rw [u5.regs]; simp +decide only [upd, ite_true, ite_false]
    have p5 : reg n5 sp = G := by rw [q5 sp (by decide)]; exact p4
    obtain ⟨n6, d6, u6⟩ := u5.self.lw hcf bsd_at_180 (off' := 0x182) (by decide)
      (by rw [p5]; exact aligned_add hGa (k := 0x28) (by decide))
    rw [p5, show memLoad32 Mx (G + 0x28) = reg m 20 from
      (ldF 0x28 (by omega) (by omega)).trans fl28] at u6
    have q6 : ∀ r, r ≠ 20 → reg n6 r = reg n5 r := fun r h => by rw [u6.regs]; exact updz u5.self.zero h
    have w6 : reg n6 20 = reg m 20 := by rw [u6.regs]; simp +decide only [upd, ite_true, ite_false]
    have p6 : reg n6 sp = G := by rw [q6 sp (by decide)]; exact p5
    obtain ⟨n7, d7, u7⟩ := u6.self.lw hcf bsd_at_182 (off' := 0x184) (by decide)
      (by rw [p6]; exact aligned_add hGa (k := 0x24) (by decide))
    rw [p6, show memLoad32 Mx (G + 0x24) = reg m 21 from
      (ldF 0x24 (by omega) (by omega)).trans fl24] at u7
    have q7 : ∀ r, r ≠ 21 → reg n7 r = reg n6 r := fun r h => by rw [u7.regs]; exact updz u6.self.zero h
    have w7 : reg n7 21 = reg m 21 := by rw [u7.regs]; simp +decide only [upd, ite_true, ite_false]
    have p7 : reg n7 sp = G := by rw [q7 sp (by decide)]; exact p6
    obtain ⟨n8, d8, u8⟩ := u7.self.lw hcf bsd_at_184 (off' := 0x186) (by decide)
      (by rw [p7]; exact aligned_add hGa (k := 0x20) (by decide))
    rw [p7, show memLoad32 Mx (G + 0x20) = reg m 22 from
      (ldF 0x20 (by omega) (by omega)).trans fl20] at u8
    have q8 : ∀ r, r ≠ 22 → reg n8 r = reg n7 r := fun r h => by rw [u8.regs]; exact updz u7.self.zero h
    have w8 : reg n8 22 = reg m 22 := by rw [u8.regs]; simp +decide only [upd, ite_true, ite_false]
    have p8 : reg n8 sp = G := by rw [q8 sp (by decide)]; exact p7
    obtain ⟨n9, d9, u9⟩ := u8.self.aluImm hcf bsd_at_186 (off' := 0x188) (by decide)
    obtain ⟨n10, d10, pc10, mem10, regs10⟩ := u9.jalr hcf bsd_at_188
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
    refine ⟨n10, hn.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8
      (.cons d9 (.single d10)))))))))), ?_, ?_, fun r h0 h1 h2 h3 h4 h5 h6 h7 => ?_, fun x hx => by rw [mem10]; exact hm x hx⟩
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
    have hr : r ∉ bsClob := by
      simp only [bsClob, List.mem_cons, List.not_mem_nil, or_false]
      intro hh
      rcases hh with hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh <;>
        contradiction
    rw [r10 r e, z8 r e1 e2 e3 e4 e5 e6 e7 e8]; exact hk r hr
  have err16C : ∀ (n : Machine) (Mx : Word → BitVec 8) (g : Fin 32 → Word) (e : BitVec 8),
      Steps m n → St Mx BSD n 0x16C g → CodeIn Mx BSD bootstateDecodeCode → g sp = G → g s0 = out →
      (g 9).extractLsb' 0 8 = e → bsErr m.mem b = some e →
      (∀ x, Sep R 112 x 1 → Mx x = m.mem x) →
      (∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M8 (G + BitVec.ofNat 32 k)) →
      (∀ r, r ∉ bsClob → g r = reg m r) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ t0 → reg m' r = reg m r) ∧
        ∀ x, Sep R 112 x 1 → m'.mem x = bsMem m.mem out b x := by
    intro n Mx g e hn s hcx hs hs0 he hpe hO hS hk
    obtain ⟨n1, d1, u1⟩ := s.aluImm hcx bsd_at_16c (off' := 0x16E) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.sbG hcx bsd_at_16e (off' := 0x172) (by decide) (a := out) (v := g 9)
      (by rw [updz s.zero (by decide), hs0]; exact BitVec.add_zero out) (updz s.zero (by decide))
    rw [he] at u2
    have hc2 : CodeIn (memStore8 Mx out e) BSD bootstateDecodeCode :=
      hcx.store8 (lowSep (by omega) (by decide) (by decide))
    obtain ⟨n3, d3, u3⟩ := u2.sbG hc2 bsd_at_172 (off' := 0x176) (by decide) (a := out + 7) (v := 2)
      (by rw [updz s.zero (by decide), hs0])
      (by simp +decide only [upd, ite_true, ite_false]; rw [s.zero]; rfl)
    rw [show (2 : Word).extractLsb' 0 8 = (2 : BitVec 8) from rfl] at u3
    have hc3 : CodeIn (memStore8 (memStore8 Mx out e) (out + 7) 2) BSD bootstateDecodeCode :=
      hc2.store8 (lowSep (by rw [BitVec.toNat_add, show (7 : Word).toNat = 7 from rfl]; omega) (by decide) (by decide))
    refine exit176 n3 _ _ (hn.trans (.cons d1 (.cons d2 (.single d3)))) u3 hc3
      (by rw [updz s.zero (by decide)]; exact hs)
      (fun k h1 h2 => by
        rw [memStore8_ne (fun e' => hOS 7 (by omega) (48 + k) (by omega) (by rw [← Ly.g_ofs k, e']; rfl)),
          memStore8_ne (fun e' => hOS 0 (by omega) (48 + k) (by omega) (by rw [add_ofNat_zero, ← Ly.g_ofs k, e']))]
        exact hS k h1 h2)
      (fun r hr => by rw [updz s.zero (bs_clob_ne hr (by decide))]; exact hk r hr)
      (fun x hx => by
        have : bsMem m.mem out b x = memStore8 (memStore8 m.mem out e) (out + 7) 2 x := by
          unfold bsMem; rw [hpe]
        rw [this]; exact memStore8_congr (memStore8_congr (hO x hx)))
  -- 0x12 to 0x16.
  obtain ⟨m10, e10, t10⟩ := t9.alu hc8 bsd_at_12 (off' := 0x14) (by decide)
  have u10 := t10.self
  obtain ⟨m11, e11, t11⟩ := u10.alu hc8 bsd_at_14 (off' := 0x16) (by decide)
  have u11 := t11.self
  obtain ⟨m12, e12, t12⟩ := u11.alu hc8 bsd_at_16 (off' := 0x18) (by decide)
  have u12 := t12.self
  have g12 : ∀ r, r ≠ a0 → r ≠ 8 → r ≠ 9 → r ≠ sp → reg m12 r = reg m r := fun r h0 h8 h9 hs => by
    rw [t12.regs, updz u11.zero h0, t11.regs, updz u10.zero h8, t10.regs, updz t9.zero h9, f1 r hs]
  have sp12 : reg m12 sp = G := by
    rw [t12.regs, updz u11.zero (by decide), t11.regs, updz u10.zero (by decide), t10.regs, updz t9.zero (by decide)]
    exact u1sp
  have s112 : reg m12 9 = b := by
    rw [t12.regs, updz u11.zero (by decide), t11.regs, updz u10.zero (by decide), t10.regs]
    simp +decide only [upd, ite_true, ite_false]; rw [ha1]; exact BitVec.zero_add b
  have s012 : reg m12 8 = out := by
    rw [t12.regs, updz u11.zero (by decide), t11.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [show reg m10 x0 = 0 from u10.zero, t10.regs, updz t9.zero (by decide), f1 a0 (by decide), ha0]
    exact BitVec.zero_add out
  have a012 : reg m12 a0 = b := by
    rw [t12.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [show reg m11 x0 = 0 from u11.zero, t11.regs, updz u10.zero (by decide), t10.regs, updz t9.zero (by decide),
      f1 a1 (by decide), ha1]
    exact BitVec.zero_add b
  have k12 : ∀ r, r ∉ bsClob → reg m12 r = reg m r := fun r hr =>
    g12 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))
      (bs_clob_ne hr (by decide))
  -- 0x18: `crc32` over the first 28 bytes.
  obtain ⟨m13, c13, pc13, mem13, regs13⟩ := u12.callRa (cb := BitVec.ofNat 32 crc32Address) hc8 bsd_at_18 bsd_at_1c
    (by decide) (by decide)
  have r13 := bs_reg1 regs13 u12.zero
  obtain ⟨m14, c14, pc14, mem14, a014, k14'⟩ := crc32_correct m13 (BitVec.ofNat 32 crc32Address)
    (BSD + BitVec.ofNat 32 (0x18 + 8)) (fun i hi => by rw [mem13]; exact (Ly.code code M8out).crc i hi) pc13
    (by rw [regs13]; simp +decide [upd]) (even_clear _ (by decide))
  have hcrc : reg m14 a0 = crcBits (bsBody m.mem b) := by
    rw [a014, r13 a0 (by decide), a012]
    unfold bytesAt bsBody; rw [mem13]
    apply congrArg
    apply List.map_congr_left
    intro i hi
    have hi' : i < 28 := List.mem_range.mp hi
    exact M8out _ (hBS.sub (c := i) (l := 1) (by omega)).symm
  have t14 : St M8 BSD m14 0x20 (reg m14) := ⟨by rw [pc14], by rw [mem14, mem13], fun _ => rfl⟩
  have g14 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ ra →
      reg m14 r = reg m12 r := fun r h0 h1 h2 h3 h4 h5 h6 hra' => by
    rw [k14' r h0 h1 h2 h3 h4 h5 h6, r13 r hra']
  have s114 : reg m14 9 = b := by
    rw [g14 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact s112
  have k14 : ∀ r, r ∉ bsClob → reg m14 r = reg m r := fun r hr => by
    rw [g14 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))
      (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))
      (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]
    exact k12 r hr
  have pre14 : Steps m m14 := .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
    (.cons e9 (.cons e10 (.cons e11 (.cons e12 (c13.trans c14))))))))))))
  -- 0x20 to 0x3A: the stored checksum.
  obtain ⟨m15, e15, t15⟩ := t14.lbu hc8 bsd_at_20 (off' := 0x24) (by decide)
  have u15 := t15.self
  obtain ⟨m16, e16, t16⟩ := u15.lbu hc8 bsd_at_24 (off' := 0x28) (by decide)
  have u16 := t16.self
  obtain ⟨m17, e17, t17⟩ := u16.lbu hc8 bsd_at_28 (off' := 0x2C) (by decide)
  have u17 := t17.self
  obtain ⟨m18, e18, t18⟩ := u17.lbu hc8 bsd_at_2c (off' := 0x30) (by decide)
  have u18 := t18.self
  obtain ⟨m19, e19, t19⟩ := u18.aluImm hc8 bsd_at_30 (off' := 0x32) (by decide)
  have u19 := t19.self
  obtain ⟨m20, e20, t20⟩ := u19.aluImm hc8 bsd_at_32 (off' := 0x34) (by decide)
  have u20 := t20.self
  obtain ⟨m21, e21, t21⟩ := u20.aluImm hc8 bsd_at_34 (off' := 0x36) (by decide)
  have u21 := t21.self
  obtain ⟨m22, e22, t22⟩ := u21.alu hc8 bsd_at_36 (off' := 0x38) (by decide)
  have u22 := t22.self
  obtain ⟨m23, e23, t23⟩ := u22.alu hc8 bsd_at_38 (off' := 0x3A) (by decide)
  have u23 := t23.self
  obtain ⟨m24, e24, t24⟩ := u23.alu hc8 bsd_at_3a (off' := 0x3C) (by decide)
  have u24 := t24.self
  have g24 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m24 r = reg m14 r := fun r h1 h2 h3 h4 => by
    rw [t24.regs, updz u23.zero h1, t23.regs, updz u22.zero h2, t22.regs, updz u21.zero h1, t21.regs,
      updz u20.zero h3, t20.regs, updz u19.zero h2, t19.regs, updz u18.zero h1, t18.regs, updz u17.zero h4,
      t17.regs, updz u16.zero h3, t16.regs, updz u15.zero h2, t15.regs, updz t14.zero h1]
  have hbyte : ∀ i, i < 32 → M8 (b + BitVec.ofNat 32 i) = m.mem (b + BitVec.ofNat 32 i) := fun i hi =>
    M8out _ (hBS.sub (c := i) (l := 1) (by omega)).symm
  have a124 : reg m24 a1 = bsSum m.mem b := by
    simp +decide only [t24.regs, t23.regs, t22.regs, t21.regs, t20.regs, t19.regs, t18.regs, t17.regs, t16.regs,
      t15.regs, upd, ite_true, ite_false]
    rw [s114, show M8 (b + 0x1D) = m.mem (b + 0x1D) from hbyte 0x1D (by omega),
      show M8 (b + 0x1E) = m.mem (b + 0x1E) from hbyte 0x1E (by omega),
      show M8 (b + 0x1F) = m.mem (b + 0x1F) from hbyte 0x1F (by omega),
      show M8 (b + 0x1C) = m.mem (b + 0x1C) from hbyte 0x1C (by omega)]
    rfl
  have a024 : reg m24 a0 = crcBits (bsBody m.mem b) := by
    rw [g24 a0 (by decide) (by decide) (by decide) (by decide)]; exact hcrc
  have sp24 : reg m24 sp = G := by
    rw [g24 sp (by decide) (by decide) (by decide) (by decide), g14 sp (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp12
  have s024 : reg m24 8 = out := by
    rw [g24 8 (by decide) (by decide) (by decide) (by decide), g14 8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s012
  have s124 : reg m24 9 = b := by rw [g24 9 (by decide) (by decide) (by decide) (by decide)]; exact s114
  have k24 : ∀ r, r ∉ bsClob → reg m24 r = reg m r := fun r hr => by
    rw [g24 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))
      (bs_clob_ne hr (by decide))]; exact k14 r hr
  have pre24 : Steps m m24 := pre14.trans (.cons e15 (.cons e16 (.cons e17 (.cons e18 (.cons e19 (.cons e20
    (.cons e21 (.cons e22 (.cons e23 (.single e24))))))))))
  -- 0x3C: the checksum.
  by_cases hck : (crcBits (bsBody m.mem b) == bsSum m.mem b) = false
  · obtain ⟨m25, e25, t25⟩ := u24.taken hc8 0xAE bsd_at_3c (by decide)
      (by rw [a024, a124]; show (!(crcBits (bsBody m.mem b) == bsSum m.mem b)) = true; rw [hck]; rfl)
    obtain ⟨m26, e26, t26⟩ := t25.aluImm hc8 bsd_at_ae (off' := 0xB0) (by decide)
    have u26 := t26.self
    obtain ⟨m27, e27, t27⟩ := u26.aluImm hc8 bsd_at_b0 (off' := 0xB2) (by decide)
    have u27 := t27.self
    have g27 : ∀ r, r ≠ a0 → r ≠ a1 → reg m27 r = reg m24 r := fun r h0 h1 => by
      rw [t27.regs, updz u26.zero h1, t26.regs, updz u24.zero h0]
    have a027 : reg m27 a0 = 0x11 := by
      rw [t27.regs, updz u26.zero (by decide), t26.regs]; simp +decide only [upd, ite_true, ite_false]
      rw [show reg m24 x0 = 0 from u24.zero]; rfl
    have a127 : reg m27 a1 = 2 := by
      rw [t27.regs]; simp +decide only [upd, ite_true, ite_false]; rw [show reg m26 x0 = 0 from u26.zero]; rfl
    obtain ⟨m28, e28, t28⟩ := u27.sbG hc8 bsd_at_b2 (off' := 0xB6) (by decide) (a := out) (v := 0x11)
      (by rw [g27 s0 (by decide) (by decide), s024]; exact BitVec.add_zero out) a027
    rw [show (0x11 : Word).extractLsb' 0 8 = (0x11 : BitVec 8) from rfl] at t28
    have hc28 : CodeIn (memStore8 M8 out 0x11) BSD bootstateDecodeCode :=
      hc8.store8 (lowSep (by omega) (by decide) (by decide))
    obtain ⟨m29, e29, t29⟩ := t28.sbG hc28 bsd_at_b6 (off' := 0xBA) (by decide) (a := out + 7) (v := 2)
      (by rw [g27 s0 (by decide) (by decide), s024]) a127
    rw [show (2 : Word).extractLsb' 0 8 = (2 : BitVec 8) from rfl] at t29
    have hc29 : CodeIn (memStore8 (memStore8 M8 out 0x11) (out + 7) 2) BSD bootstateDecodeCode :=
      hc28.store8 (lowSep (by rw [BitVec.toNat_add, show (7 : Word).toNat = 7 from rfl]; omega) (by decide) (by decide))
    obtain ⟨m30, e30, t30⟩ := t29.jump hc29 bsd_at_ba (off' := 0x176) (by decide) (by rw [t29.pc]; decide)
    refine exit176 m30 _ (reg m27) (pre24.trans (.cons e25 (.cons e26 (.cons e27 (.cons e28 (.cons e29
      (.single e30))))))) t30 hc29 (by rw [g27 sp (by decide) (by decide)]; exact sp24)
      (fun k h1 h2 => by
        rw [memStore8_ne (fun e' => hOS 7 (by omega) (48 + k) (by omega) (by rw [← Ly.g_ofs k, e']; rfl)),
          memStore8_ne (fun e' => hOS 0 (by omega) (48 + k) (by omega) (by rw [add_ofNat_zero, ← Ly.g_ofs k, e']))])
      (fun r hr => by rw [g27 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]; exact k24 r hr)
      (fun x hx => by
        have : bsMem m.mem out b x = memStore8 (memStore8 m.mem out 0x11) (out + 7) 2 x := by
          unfold bsMem; rw [show bsErr m.mem b = some 0x11 from by unfold bsErr; rw [hck]; rfl]
        rw [this]; exact memStore8_congr (memStore8_congr (M8out x hx)))
  replace hck : (crcBits (bsBody m.mem b) == bsSum m.mem b) = true := by
    cases h : (crcBits (bsBody m.mem b) == bsSum m.mem b)
    · exact absurd h hck
    · rfl
  obtain ⟨m25, e25, t25⟩ := u24.notTaken hc8 0x40 bsd_at_3c (by decide)
    (by rw [a024, a124]; show (!(crcBits (bsBody m.mem b) == bsSum m.mem b)) = false; rw [hck]; rfl)
  -- 0x40 to 0x50: the reader over the first 28 bytes, at `G + 0xC`.
  obtain ⟨m26, e26, t26⟩ := t25.aluImm hc8 bsd_at_40 (off' := 0x42) (by decide)
  have u26 := t26.self
  have a026 : reg m26 a0 = 0x1C := by
    rw [t26.regs]; simp +decide only [upd, ite_true, ite_false]; rw [show reg m24 x0 = 0 from u24.zero]; rfl
  have g26 : ∀ r, r ≠ a0 → reg m26 r = reg m24 r := fun r h => by rw [t26.regs, updz u24.zero h]
  have sp26 : reg m26 sp = G := by rw [g26 sp (by decide)]; exact sp24
  obtain ⟨m27, e27, t27⟩ := u26.sw hc8 bsd_at_42 (off' := 0x44) (by decide)
    (by rw [sp26]; exact aligned_add hGa (k := 0xC) (by decide))
  rw [sp26, g26 9 (by decide), s124] at t27
  have hc27 := hc8.store32 (v := b) (lowSep (gLow 0xC (by omega)) (by decide) (by decide))
  obtain ⟨m28, e28, t28⟩ := t27.sw hc27 bsd_at_44 (off' := 0x46) (by decide)
    (by rw [sp26]; exact aligned_add hGa (k := 0x10) (by decide))
  rw [sp26, a026] at t28
  have hc28 := hc27.store32 (v := 0x1C) (lowSep (gLow 0x10 (by omega)) (by decide) (by decide))
  obtain ⟨m29, e29, t29⟩ := t28.sw hc28 bsd_at_46 (off' := 0x48) (by decide)
    (by rw [sp26]; exact aligned_add hGa (k := 0x14) (by decide))
  rw [sp26, show reg m26 x0 = 0 from u26.zero] at t29
  obtain ⟨Mr, hMr⟩ : ∃ Mr, memStore32 (memStore32 (memStore32 M8 (G + 0xC) b) (G + 0x10) 0x1C) (G + 0x14) 0 = Mr :=
    ⟨_, rfl⟩
  rw [hMr] at t29
  have hMr' : memStore32 (memStore32 (memStore32 M8 (G + BitVec.ofNat 32 0xC) b) (G + BitVec.ofNat 32 0x10) 0x1C)
      (G + BitVec.ofNat 32 0x14) 0 = Mr := hMr
  have hc29 : CodeIn Mr BSD bootstateDecodeCode := by
    rw [← hMr]; exact hc28.store32 (lowSep (gLow 0x14 (by omega)) (by decide) (by decide))
  obtain ⟨m30, e30, t30⟩ := t29.lui hc29 bsd_at_48 (off' := 0x4C) (by decide)
  have u30 := t30.self
  obtain ⟨m31, e31, t31⟩ := u30.aluImm hc29 bsd_at_4c (off' := 0x50) (by decide)
  have u31 := t31.self
  obtain ⟨m32, e32, t32⟩ := u31.aluImm hc29 bsd_at_50 (off' := 0x52) (by decide)
  have u32' := t32.self
  have g32 : ∀ r, r ≠ a0 → r ≠ a1 → reg m32 r = reg m26 r := fun r h0 h1 => by
    rw [t32.regs, updz u31.zero h0, t31.regs, updz u30.zero h1, t30.regs, updz u26.zero h1]
  have sp32 : reg m32 sp = G := by rw [g32 sp (by decide) (by decide)]; exact sp26
  have a032 : reg m32 a0 = G + 0xC := by
    rw [t32.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [show reg m31 sp = G from by
      rw [t31.regs, updz u30.zero (by decide), t30.regs, updz u26.zero (by decide)]; exact sp26]; rfl
  have a132 : reg m32 a1 = 0x53423343 := by
    rw [t32.regs, updz u31.zero (by decide), t31.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [t30.regs]; simp +decide only [upd, ite_true, ite_false]; try rfl
  have k32 : ∀ r, r ∉ bsClob → reg m32 r = reg m r := fun r hr => by
    rw [g32 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)), g26 r (bs_clob_ne hr (by decide))]
    exact k24 r hr
  have s032 : reg m32 8 = out := by
    rw [g32 8 (by decide) (by decide), g26 8 (by decide)]; exact s024
  have pre32 : Steps m m32 := pre24.trans (.cons e25 (.cons e26 (.cons e27 (.cons e28 (.cons e29 (.cons e30
    (.cons e31 (.single e32))))))))
  have so : ∀ a l c k, a + l ≤ c ∨ c + k ≤ a → a + l ≤ 64 → c + k ≤ 64 →
      Sep (G + BitVec.ofNat 32 a) l (G + BitVec.ofNat 32 c) k :=
    fun a l c k h h1 h2 => sep_offsets G h (by omega) (by omega)
  have Or' : ∀ x, Sep R 112 x 1 → Mr x = m.mem x := fun x hx => by
    rw [← hMr', memStore32_get_sep (fr 0x14 4 (by omega) x 1 hx), memStore32_get_sep (fr 0x10 4 (by omega) x 1 hx),
      memStore32_get_sep (fr 0xC 4 (by omega) x 1 hx)]
    exact M8out x hx
  have Sr : ∀ k, 0x20 ≤ k → k < 0x40 → Mr (G + BitVec.ofNat 32 k) = M8 (G + BitVec.ofNat 32 k) := fun k h1 h2 => by
    rw [← hMr', memStore32_get_sep (so 0x14 4 k 1 (by omega) (by omega) (by omega)),
      memStore32_get_sep (so 0x10 4 k 1 (by omega) (by omega) (by omega)),
      memStore32_get_sep (so 0xC 4 k 1 (by omega) (by omega) (by omega))]
  have rpr : memLoad32 Mr (G + 0xC) = b := by
    rw [← hMr', show G + 0xC = G + BitVec.ofNat 32 0xC from rfl,
      memLoad32_store32_sep (so 0x14 4 0xC 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x10 4 0xC 4 (by omega) (by omega) (by omega))]
    exact memLoad32_store32_same _ _ _
  have rlr : memLoad32 Mr (G + 0xC + 4) = 28 := by
    rw [← hMr', show G + 0xC + 4 = G + BitVec.ofNat 32 0x10 from by rw [BitVec.add_assoc]; rfl,
      memLoad32_store32_sep (so 0x14 4 0x10 4 (by omega) (by omega) (by omega))]
    exact memLoad32_store32_same _ _ _
  have rqr : memLoad32 Mr (G + 0xC + 8) = 0 := by
    rw [← hMr', show G + 0xC + 8 = G + BitVec.ofNat 32 0x14 from by rw [BitVec.add_assoc]; rfl]
    exact memLoad32_store32_same _ _ _
  have mw_eq : ∀ (Mx : Word → BitVec 8), (∀ x, Sep R 112 x 1 → Mx x = m.mem x) → ∀ i, i + 4 ≤ 32 →
      memLoad32 Mx (b + BitVec.ofNat 32 i) = mw m.mem b i := fun Mx hO i hi =>
    memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact hO _ (hBS.sub (c := i + j) (l := 1) (by omega)).symm
  have bO : ∀ (Mx : Word → BitVec 8), (∀ x, Sep R 112 x 1 → Mx x = m.mem x) → ∀ i, i < 32 →
      Mx (b + BitVec.ofNat 32 i) = m.mem (b + BitVec.ofNat 32 i) := fun Mx hO i hi =>
    hO _ (hBS.sub (c := i) (l := 1) (by omega)).symm
  -- 0x52: `Reader::magic(b"C3BS")`.
  obtain ⟨m33, c33, t33, sp33, a033, fr33, mem33⟩ := bs_magic Ly u32' (Ly.code code Or') bsd_at_52 bsd_at_56
    (by decide) (by decide) sp32 a032 a132 rpr rlr
  have hmg : magicResult Mr (G + 0xC) 0x53423343 = if mw m.mem b 0 == 0x53423343 then 0xFFFFFFFF else 2 := by
    unfold magicResult
    rw [rpr, rlr, rqr, show bytesResult b 28 0 4 = some (b + 0, 0 + 4) from rfl]
    simp only
    rw [show b + 0 = b + BitVec.ofNat 32 0 from rfl, mw_eq Mr Or' 0 (by omega)]
  have k33 : ∀ r, r ∉ bsClob → reg m33 r = reg m r := fun r hr =>
    (fr33 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))
      (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))
      (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))).trans (k32 r hr)
  have s033 : reg m33 8 = out := by
    rw [fr33 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact s032
  have mm33 : ∀ x, Sep (R + BitVec.ofNat 32 0) 48 x 1 → m33.mem x = memStore32 Mr (G + 0xC + 8) 4 x := by
    intro x hx
    rw [add_ofNat_zero] at hx
    rw [mem33 x hx]
    unfold magicMem
    rw [rpr, rlr, rqr, show bytesResult b 28 0 4 = some (b + 0, 0 + 4) from rfl]
    rfl
  obtain ⟨rp33, rl33, rq33, O33, S33⟩ := Ly.advance (c := 0) (N := 48) (by omega) rpr rlr Or' Sr mm33
  rw [hmg] at a033
  obtain ⟨m34, g34, c34, hg34, hs34, br34⟩ := bs_check t33 (Ly.code code O33).decode bsd_at_5a bsd_at_5c bsd_at_60
    bsd_at_64 (off' := 0x68) (by decide) (by decide)
  by_cases hm : (mw m.mem b 0 == 0x53423343) = false
  · rw [hm] at a033
    rcases br34 with ⟨hff, -⟩ | ⟨-, t34⟩
    · rw [a033] at hff; exact absurd hff (by decide)
    · exact err16C m34 m33.mem g34 2 (pre32.trans (c33.trans c34)) t34 (Ly.code code O33).decode
        (by rw [hg34 sp (by decide) (by decide)]; exact sp33) (by rw [hg34 s0 (by decide) (by decide)]; exact s033)
        (by rw [hs34, a033]; rfl) (by unfold bsErr; rw [hck, hm]; rfl) O33 S33
        (fun r hr => by rw [hg34 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]; exact k33 r hr)
  replace hm : (mw m.mem b 0 == 0x53423343) = true := by
    cases h : (mw m.mem b 0 == 0x53423343)
    · exact absurd h hm
    · rfl
  rw [hm] at a033
  have t34 := (br34.resolve_right fun h => by rw [a033] at h; exact h.1 (by decide)).2
  -- 0x68: `Reader::version_1`.
  have hc33 := (Ly.code code O33).decode
  obtain ⟨m35, e35, t35⟩ := t34.aluImm hc33 bsd_at_68 (off' := 0x6A) (by decide)
  obtain ⟨m36, c36, t36, sp36, a036, fr36, mem36⟩ := bs_version Ly t35 (Ly.code code O33) bsd_at_6a bsd_at_6e
    (by decide) (by decide) (by rw [updz t34.zero (by decide), hg34 sp (by decide) (by decide)]; exact sp33)
    (by simp +decide only [upd, ite_true, ite_false]; rw [hg34 sp (by decide) (by decide), sp33]; rfl) rp33 rl33
  have k36 : ∀ r, r ∉ bsClob → reg m36 r = reg m r := fun r hr => by
    rw [fr36 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))
      (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))
      (bs_clob_ne hr (by decide)), updz t34.zero (bs_clob_ne hr (by decide)),
      hg34 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]
    exact k33 r hr
  have s036 : reg m36 8 = out := by
    rw [fr36 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      updz t34.zero (by decide), hg34 8 (by decide) (by decide)]; exact s033
  rw [bs_version_val rp33 rl33 rq33 (bO _ O33 4 (by omega)) (bO _ O33 5 (by omega))] at a036
  have mm36 : ∀ x, Sep (R + BitVec.ofNat 32 16) 32 x 1 → m36.mem x = memStore32 m33.mem (G + 0xC + 8) 6 x :=
    fun x hx => by rw [mem36 x hx, bs_u16Mem_val rp33 rl33 rq33 x]
  obtain ⟨rp36, rl36, rq36, O36, S36⟩ := Ly.advance (c := 16) (N := 32) (by omega) rp33 rl33 O33 S33 mm36
  have pre36 : Steps m m36 := pre32.trans (c33.trans (c34.trans (.cons e35 c36)))
  obtain ⟨m37, g37, c37, hg37, hs37, br37⟩ := bs_check t36 (Ly.code code O36).decode bsd_at_72 bsd_at_74 bsd_at_78
    bsd_at_7c (off' := 0x7E) (by decide) (by decide)
  by_cases hv : (((m.mem (b + 5)).zeroExtend 32 <<< 24 ||| (m.mem (b + 4)).zeroExtend 32 <<< 16 : Word) >>> 16
      == 1) = false
  · rw [hv] at a036
    rcases br37 with ⟨hff, -⟩ | ⟨-, t37⟩
    · rw [a036] at hff; exact absurd hff (by decide)
    · exact err16C m37 m36.mem g37 3 (pre36.trans c37) t37 (Ly.code code O36).decode
        (by rw [hg37 sp (by decide) (by decide)]; exact sp36) (by rw [hg37 s0 (by decide) (by decide)]; exact s036)
        (by rw [hs37, a036]; rfl) (by unfold bsErr; rw [hck, hm, hv]; rfl) O36 S36
        (fun r hr => by rw [hg37 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]; exact k36 r hr)
  replace hv : (((m.mem (b + 5)).zeroExtend 32 <<< 24 ||| (m.mem (b + 4)).zeroExtend 32 <<< 16 : Word) >>> 16
      == 1) = true := by
    cases h : (((m.mem (b + 5)).zeroExtend 32 <<< 24 ||| (m.mem (b + 4)).zeroExtend 32 <<< 16 : Word) >>> 16 == 1)
    · exact absurd h hv
    · rfl
  rw [hv] at a036
  have t37 := (br37.resolve_right fun h => by rw [a036] at h; exact h.1 (by decide)).2
  -- 0x7E: `Reader::reserved(2)`.
  have hc36 := (Ly.code code O36).decode
  obtain ⟨m38, e38, t38⟩ := t37.aluImm hc36 bsd_at_7e (off' := 0x80) (by decide)
  have u38 := t38.self
  obtain ⟨m39, e39, t39⟩ := u38.aluImm hc36 bsd_at_80 (off' := 0x82) (by decide)
  have g38 : ∀ r, r ≠ a0 → r ≠ 9 → reg m38 r = reg m36 r := fun r h0 h9 => by
    rw [t38.regs, updz t37.zero h0, hg37 r h0 h9]
  obtain ⟨m40, c40, t40, sp40, a040, fr40, mem40⟩ := bs_reserved (n := BitVec.ofNat 32 2) Ly t39 (Ly.code code O36)
    bsd_at_82 bsd_at_86 (by decide) (by decide) (by rw [updz u38.zero (by decide), g38 sp (by decide) (by decide)]; exact sp36)
    (by
      rw [updz u38.zero (by decide), t38.regs]; simp +decide only [upd, ite_true, ite_false]
      rw [hg37 sp (by decide) (by decide), sp36]; rfl)
    (by simp +decide only [upd, ite_true, ite_false]; rw [u38.zero]; rfl) (by decide) rp36 rl36
  have k40 : ∀ r, r ∉ bsClob → reg m40 r = reg m r := fun r hr => by
    rw [fr40 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))
      (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))
      (bs_clob_ne hr (by decide)), updz u38.zero (bs_clob_ne hr (by decide)),
      g38 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]
    exact k36 r hr
  have s040 : reg m40 8 = out := by
    rw [fr40 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      updz u38.zero (by decide), g38 8 (by decide) (by decide)]; exact s036
  rw [bs_reserved_val 6 2 (by omega) rp36 rl36 rq36 (fun i hi => bO _ O36 (6 + i) (by omega))] at a040
  have a040' : reg m40 a0 = if allZero m.mem (b + 6) 2 then 0xFF else 4 := a040
  have mm40 : ∀ x, Sep (R + BitVec.ofNat 32 32) 16 x 1 →
      m40.mem x = memStore32 m36.mem (G + 0xC + 8) (BitVec.ofNat 32 8) x :=
    fun x hx => by rw [mem40 x hx, bs_reservedMem_val 6 2 (by omega) rp36 rl36 rq36 x]
  obtain ⟨rp40, rl40, rq40, O40, S40⟩ := Ly.advance (c := 32) (N := 16) (by omega) rp36 rl36 O36 S36 mm40
  have pre40 : Steps m m40 := pre36.trans (c37.trans (.cons e38 (.cons e39 c40)))
  obtain ⟨m41, g41, c41, hg41, hs41, br41⟩ := bs_check t40 (Ly.code code O40).decode bsd_at_8a bsd_at_8c bsd_at_90
    bsd_at_94 (off' := 0x96) (by decide) (by decide)
  by_cases hz : allZero m.mem (b + 6) 2 = false
  · rw [hz] at a040'
    rcases br41 with ⟨hff, -⟩ | ⟨-, t41⟩
    · rw [a040'] at hff; exact absurd hff (by decide)
    · exact err16C m41 m40.mem g41 4 (pre40.trans c41) t41 (Ly.code code O40).decode
        (by rw [hg41 sp (by decide) (by decide)]; exact sp40) (by rw [hg41 s0 (by decide) (by decide)]; exact s040)
        (by rw [hs41, a040']; rfl) (by unfold bsErr; rw [hck, hm, hv, hz]; rfl) O40 S40
        (fun r hr => by rw [hg41 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]; exact k40 r hr)
  replace hz : allZero m.mem (b + 6) 2 = true := by
    cases h : allZero m.mem (b + 6) 2
    · exact absurd h hz
    · rfl
  rw [hz] at a040'
  have t41 := (br41.resolve_right fun h => by rw [a040'] at h; exact h.1 (by decide)).2
  -- 0x96: `Reader::u32`, the generation.
  have hc40 := (Ly.code code O40).decode
  obtain ⟨m42, e42, t42⟩ := t41.aluImm hc40 bsd_at_96 (off' := 0x98) (by decide)
  have u42 := t42.self
  obtain ⟨m43, e43, t43⟩ := u42.aluImm hc40 bsd_at_98 (off' := 0x9A) (by decide)
  have g42 : ∀ r, r ≠ a0 → r ≠ 9 → reg m42 r = reg m40 r := fun r h0 h9 => by
    rw [t42.regs, updz t41.zero h0, hg41 r h0 h9]
  have sp42 : reg m42 sp = G := by rw [g42 sp (by decide) (by decide)]; exact sp40
  obtain ⟨m44, c44, t44, sp44, fr44, mem44⟩ := bs_u32 Ly t43 (Ly.code code O40) bsd_at_9a bsd_at_9e (by decide)
    (by decide) (by rw [updz u42.zero (by decide)]; exact sp42)
    (by
      rw [updz u42.zero (by decide), t42.regs]; simp +decide only [upd, ite_true, ite_false]
      rw [hg41 sp (by decide) (by decide), sp40]; rfl)
    (by simp +decide only [upd, ite_true, ite_false]; rw [sp42]; rfl) rp40 rl40
  have mm44 : ∀ x, Sep R 48 x 1 → m44.mem x = memStore8 (memStore32 (memStore32 m40.mem (G + 0xC + 8)
      (BitVec.ofNat 32 8 + 4)) (G + 0x18 + 4) (memLoad32 m40.mem (b + BitVec.ofNat 32 8))) (G + 0x18) 0 x := by
    intro x hx
    rw [mem44 x hx]
    unfold u32Mem
    rw [rp40, rl40, rq40, show bytesResult b 28 (BitVec.ofNat 32 8) 4 =
      some (b + BitVec.ofNat 32 8, BitVec.ofNat 32 8 + 4) from rfl]
  obtain ⟨rp44, rl44, rq44, O44, S44, tag44, w44⟩ := Ly.advance_u32 rp40 rl40 O40 S40 mm44
  have rq44' : memLoad32 m44.mem (G + 0xC + 8) = BitVec.ofNat 32 12 := rq44
  rw [mw_eq m40.mem O40 8 (by omega)] at w44
  have k44 : ∀ r, r ∉ bsClob → reg m44 r = reg m r := fun r hr => by
    rw [fr44 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))
      (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))
      (bs_clob_ne hr (by decide)), updz u42.zero (bs_clob_ne hr (by decide)),
      g42 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]
    exact k40 r hr
  have s044 : reg m44 8 = out := by
    rw [fr44 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      updz u42.zero (by decide), g42 8 (by decide) (by decide)]; exact s040
  have hc44 := (Ly.code code O44).decode
  obtain ⟨m45, e45, t45⟩ := t44.lbu hc44 bsd_at_a2 (off' := 0xA6) (by decide)
  have a045 : upd (reg m44) a0 ((m44.mem (reg m44 sp + 0x18)).zeroExtend 32) a0 = 0 := by
    simp +decide only [upd, ite_true, ite_false]; rw [sp44, tag44]; rfl
  obtain ⟨m46, e46, t46⟩ := t45.taken hc44 0xBC bsd_at_a6 (by decide) (by rw [a045, updz t44.zero (by decide)]; rfl)
  obtain ⟨m47, e47, t47⟩ := t46.lw hc44 bsd_at_bc (off' := 0xBE) (by decide)
    (by rw [updz t44.zero (by decide), sp44]; exact aligned_add hGa (k := 0x1C) (by decide))
  have u47 := t47.self
  have g47 : ∀ r, r ≠ a0 → r ≠ 22 → reg m47 r = reg m44 r := fun r h0 h22 => by
    rw [t47.regs, updz t45.zero h22, updz t44.zero h0]
  have sp47 : reg m47 sp = G := by rw [g47 sp (by decide) (by decide)]; exact sp44
  have s047 : reg m47 8 = out := by rw [g47 8 (by decide) (by decide)]; exact s044
  have s647 : reg m47 22 = mw m.mem b 8 := by
    rw [t47.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp44]; exact w44
  have k47 : ∀ r, r ∉ bsClob → reg m47 r = reg m r := fun r hr => by
    rw [g47 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]; exact k44 r hr
  have pre47 : Steps m m47 := pre40.trans (c41.trans (.cons e42 (.cons e43 (c44.trans (.cons e45 (.cons e46
    (.single e47)))))))
  -- 0xBE: `Reader::u8`, byte 12.
  have hc47' := (Ly.code code O44).decode
  obtain ⟨m48, e48, t48⟩ := u47.aluImm hc47' bsd_at_be (off' := 0xC0) (by decide)
  obtain ⟨m49, c49, t49, sp49, a049, a149, fr49, mem49⟩ := bs_u8 Ly t48 (Ly.code code O44) bsd_at_c0
    bsd_at_c4 (by decide) (by decide) (by rw [updz u47.zero (by decide)]; exact sp47)
    (by simp +decide only [upd, ite_true, ite_false]; rw [sp47]; rfl) rp44 rl44
  rw [bs_u8_val 12 (by omega) rp44 rl44 rq44'] at a049 a149
  have a049' : reg m49 a0 = 0 := a049
  have a149' : reg m49 a1 = (m.mem (b + 12)).zeroExtend 32 := by
    rw [a149]; show (m44.mem (b + BitVec.ofNat 32 12)).zeroExtend 32 = _; rw [bO _ O44 12 (by omega)]; rfl
  have mm49 : ∀ x, Sep (R + BitVec.ofNat 32 32) 16 x 1 →
      m49.mem x = memStore32 m44.mem (G + 0xC + 8) (BitVec.ofNat 32 (12 + 1)) x := fun x hx => by
    have e : reservedMem m44.mem (G + 0xC) 1 x = memStore32 m44.mem (G + 0xC + 8) (BitVec.ofNat 32 (12 + 1)) x :=
      bs_reservedMem_val 12 1 (by omega) rp44 rl44 rq44' x
    rw [mem49 x hx, e]
  obtain ⟨rp49, rl49, rq49, O49, S49⟩ := Ly.advance (c := 32) (N := 16) (by omega) rp44 rl44 O44 S44 mm49
  have g49 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m49 r = reg m47 r :=
    fun r h0 h1 h2 h3 h4 h5 hra' => by rw [fr49 r h0 h1 h2 h3 h4 h5 hra', updz u47.zero h0]
  have hc49 := (Ly.code code O49).decode
  obtain ⟨m50, e50, t50⟩ := t49.aluImm hc49 bsd_at_c8 (off' := 0xCA) (by decide)
  have u50 := t50.self
  obtain ⟨m51, e51, t51⟩ := u50.alu hc49 bsd_at_ca (off' := 0xCC) (by decide)
  have u51 := t51.self
  have a051 : reg m51 a0 = 0 := by
    rw [t51.regs, updz u50.zero (by decide), t50.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [a049']; rfl
  obtain ⟨m52, e52, t52⟩ := u51.taken hc49 0xD2 bsd_at_cc (by decide)
    (by rw [a051, show reg m51 x0 = 0 from u51.zero]; rfl)
  have u52 := t52.self
  have g52 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ 18 →
      reg m52 r = reg m47 r := fun r h0 h1 h2 h3 h4 h5 hra' hg => by
    rw [t52.regs, t51.regs, updz u50.zero hg, t50.regs, updz t49.zero h0, g49 r h0 h1 h2 h3 h4 h5 hra']
  have v52_18 : reg m52 18 = (m.mem (b + 12)).zeroExtend 32 := by
    rw [t52.regs, t51.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [show reg m50 x0 = 0 from u50.zero, t50.regs, updz t49.zero (by decide), a149']
    exact BitVec.zero_add _
  have sp52 : reg m52 sp = G := by rw [g52 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp47
  have s052 : reg m52 8 = out := by rw [g52 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s047
  have k52 : ∀ r, r ∉ bsClob → reg m52 r = reg m r := fun r hr => by
    rw [g52 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]; exact k47 r hr
  have pre52 : Steps m m52 := pre47.trans (.cons e48 (c49.trans (.cons e50 (.cons e51 (.single e52)))))
  have v52_22 : reg m52 22 = mw m.mem b 8 := by rw [g52 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s647
  obtain ⟨m53, e53, t53⟩ := u52.aluImm hc49 bsd_at_d2 (off' := 0xD6) (by decide)
  have u53 := t53.self
  obtain ⟨m54, e54, t54⟩ := u53.aluImm hc49 bsd_at_d6 (off' := 0xD8) (by decide)
  have u54 := t54.self
  obtain ⟨m55, e55, t55⟩ := u54.aluImm hc49 bsd_at_d8 (off' := 0xDA) (by decide)
  have u55 := t55.self
  have g55 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ 9 → reg m55 r = reg m52 r := fun r h0 h1 h9 => by
    rw [t55.regs, updz u54.zero h9, t54.regs, updz u53.zero h1, t53.regs, updz u52.zero h0]
  have a055 : reg m55 a0 = (m.mem (b + 12)).zeroExtend 32 &&& 0xFF := by
    rw [t55.regs, updz u54.zero (by decide), t54.regs, updz u53.zero (by decide), t53.regs]
    simp +decide only [upd, ite_true, ite_false]; rw [v52_18]; rfl
  have a155 : reg m55 a1 = 1 := by
    rw [t55.regs, updz u54.zero (by decide), t54.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [show reg m53 x0 = 0 from u53.zero]; rfl
  have s155 : reg m55 9 = 5 := by
    rw [t55.regs]; simp +decide only [upd, ite_true, ite_false]; rw [show reg m54 x0 = 0 from u54.zero]; rfl
  have sp55 : reg m55 sp = G := by rw [g55 sp (by decide) (by decide) (by decide)]; exact sp52
  have s055 : reg m55 8 = out := by rw [g55 8 (by decide) (by decide) (by decide)]; exact s052
  have k55 : ∀ r, r ∉ bsClob → reg m55 r = reg m r := fun r hr => by
    rw [g55 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]
    exact k52 r hr
  have pre55 : Steps m m55 := pre52.trans (.cons e53 (.cons e54 (.single e55)))
  by_cases hp5 : (1 : Word).ult ((m.mem (b + 12)).zeroExtend 32 &&& 0xFF) = true
  · obtain ⟨m56, e56, t56⟩ := u55.taken hc49 0x16C bsd_at_da (by decide) (by rw [a155, a055]; exact hp5)
    exact err16C m56 m49.mem (reg m55) 5 (pre55.trans (.single e56)) t56 hc49 sp55 s055
      (by rw [s155]; rfl) (by unfold bsErr; rw [hck, hm, hv, hz, hp5]; rfl) O49 S49 k55
  replace hp5 : (1 : Word).ult ((m.mem (b + 12)).zeroExtend 32 &&& 0xFF) = false := by
    cases hh : (1 : Word).ult ((m.mem (b + 12)).zeroExtend 32 &&& 0xFF)
    · rfl
    · exact absurd hh hp5
  obtain ⟨m56, e56, t56⟩ := u55.notTaken hc49 0xDE bsd_at_da (by decide) (by rw [a155, a055]; exact hp5)
  have u56 := t56.self
  have q56 : ∀ r, reg m56 r = reg m55 r := t56.regs
  have sp56 : reg m56 sp = G := by rw [q56]; exact sp55
  have s056 : reg m56 8 = out := by rw [q56]; exact s055
  have k56 : ∀ r, r ∉ bsClob → reg m56 r = reg m r := fun r hr => by rw [q56]; exact k55 r hr
  have pre56 : Steps m m56 := pre55.trans (.single e56)
  have v56_9 : reg m56 9 = 5 := by rw [q56]; exact s155
  have v56_22 : reg m56 22 = mw m.mem b 8 := by rw [q56, g55 22 (by decide) (by decide) (by decide)]; exact v52_22
  have v56_18 : reg m56 18 = (m.mem (b + 12)).zeroExtend 32 := by rw [q56, g55 18 (by decide) (by decide) (by decide)]; exact v52_18
  -- 0xDE: `Reader::u8`, byte 13.
  have hc56' := (Ly.code code O49).decode
  obtain ⟨m57, e57, t57⟩ := u56.aluImm hc56' bsd_at_de (off' := 0xE0) (by decide)
  obtain ⟨m58, c58, t58, sp58, a058, a158, fr58, mem58⟩ := bs_u8 Ly t57 (Ly.code code O49) bsd_at_e0
    bsd_at_e4 (by decide) (by decide) (by rw [updz u56.zero (by decide)]; exact sp56)
    (by simp +decide only [upd, ite_true, ite_false]; rw [sp56]; rfl) rp49 rl49
  rw [bs_u8_val 13 (by omega) rp49 rl49 rq49] at a058 a158
  have a058' : reg m58 a0 = 0 := a058
  have a158' : reg m58 a1 = (m.mem (b + 13)).zeroExtend 32 := by
    rw [a158]; show (m49.mem (b + BitVec.ofNat 32 13)).zeroExtend 32 = _; rw [bO _ O49 13 (by omega)]; rfl
  have mm58 : ∀ x, Sep (R + BitVec.ofNat 32 32) 16 x 1 →
      m58.mem x = memStore32 m49.mem (G + 0xC + 8) (BitVec.ofNat 32 (13 + 1)) x := fun x hx => by
    have e : reservedMem m49.mem (G + 0xC) 1 x = memStore32 m49.mem (G + 0xC + 8) (BitVec.ofNat 32 (13 + 1)) x :=
      bs_reservedMem_val 13 1 (by omega) rp49 rl49 rq49 x
    rw [mem58 x hx, e]
  obtain ⟨rp58, rl58, rq58, O58, S58⟩ := Ly.advance (c := 32) (N := 16) (by omega) rp49 rl49 O49 S49 mm58
  have g58 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m58 r = reg m56 r :=
    fun r h0 h1 h2 h3 h4 h5 hra' => by rw [fr58 r h0 h1 h2 h3 h4 h5 hra', updz u56.zero h0]
  have hc58 := (Ly.code code O58).decode
  obtain ⟨m59, e59, t59⟩ := t58.aluImm hc58 bsd_at_e8 (off' := 0xEA) (by decide)
  have u59 := t59.self
  obtain ⟨m60, e60, t60⟩ := u59.alu hc58 bsd_at_ea (off' := 0xEC) (by decide)
  have u60 := t60.self
  have a060 : reg m60 a0 = 0 := by
    rw [t60.regs, updz u59.zero (by decide), t59.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [a058']; rfl
  obtain ⟨m61, e61, t61⟩ := u60.taken hc58 0xF2 bsd_at_ec (by decide)
    (by rw [a060, show reg m60 x0 = 0 from u60.zero]; rfl)
  have u61 := t61.self
  have g61 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ 19 →
      reg m61 r = reg m56 r := fun r h0 h1 h2 h3 h4 h5 hra' hg => by
    rw [t61.regs, t60.regs, updz u59.zero hg, t59.regs, updz t58.zero h0, g58 r h0 h1 h2 h3 h4 h5 hra']
  have v61_19 : reg m61 19 = (m.mem (b + 13)).zeroExtend 32 := by
    rw [t61.regs, t60.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [show reg m59 x0 = 0 from u59.zero, t59.regs, updz t58.zero (by decide), a158']
    exact BitVec.zero_add _
  have sp61 : reg m61 sp = G := by rw [g61 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp56
  have s061 : reg m61 8 = out := by rw [g61 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s056
  have k61 : ∀ r, r ∉ bsClob → reg m61 r = reg m r := fun r hr => by
    rw [g61 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]; exact k56 r hr
  have pre61 : Steps m m61 := pre56.trans (.cons e57 (c58.trans (.cons e59 (.cons e60 (.single e61)))))
  have v61_22 : reg m61 22 = mw m.mem b 8 := by rw [g61 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v56_22
  have v61_18 : reg m61 18 = (m.mem (b + 12)).zeroExtend 32 := by rw [g61 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v56_18
  have v61_9 : reg m61 9 = 5 := by rw [g61 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v56_9
  -- 0xF2: `Reader::u8`, byte 14.
  have hc61' := (Ly.code code O58).decode
  obtain ⟨m62, e62, t62⟩ := u61.aluImm hc61' bsd_at_f2 (off' := 0xF4) (by decide)
  obtain ⟨m63, c63, t63, sp63, a063, a163, fr63, mem63⟩ := bs_u8 Ly t62 (Ly.code code O58) bsd_at_f4
    bsd_at_f8 (by decide) (by decide) (by rw [updz u61.zero (by decide)]; exact sp61)
    (by simp +decide only [upd, ite_true, ite_false]; rw [sp61]; rfl) rp58 rl58
  rw [bs_u8_val 14 (by omega) rp58 rl58 rq58] at a063 a163
  have a063' : reg m63 a0 = 0 := a063
  have a163' : reg m63 a1 = (m.mem (b + 14)).zeroExtend 32 := by
    rw [a163]; show (m58.mem (b + BitVec.ofNat 32 14)).zeroExtend 32 = _; rw [bO _ O58 14 (by omega)]; rfl
  have mm63 : ∀ x, Sep (R + BitVec.ofNat 32 32) 16 x 1 →
      m63.mem x = memStore32 m58.mem (G + 0xC + 8) (BitVec.ofNat 32 (14 + 1)) x := fun x hx => by
    have e : reservedMem m58.mem (G + 0xC) 1 x = memStore32 m58.mem (G + 0xC + 8) (BitVec.ofNat 32 (14 + 1)) x :=
      bs_reservedMem_val 14 1 (by omega) rp58 rl58 rq58 x
    rw [mem63 x hx, e]
  obtain ⟨rp63, rl63, rq63, O63, S63⟩ := Ly.advance (c := 32) (N := 16) (by omega) rp58 rl58 O58 S58 mm63
  have g63 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m63 r = reg m61 r :=
    fun r h0 h1 h2 h3 h4 h5 hra' => by rw [fr63 r h0 h1 h2 h3 h4 h5 hra', updz u61.zero h0]
  have hc63 := (Ly.code code O63).decode
  obtain ⟨m64, e64, t64⟩ := t63.aluImm hc63 bsd_at_fc (off' := 0xFE) (by decide)
  have u64 := t64.self
  obtain ⟨m65, e65, t65⟩ := u64.alu hc63 bsd_at_fe (off' := 0x100) (by decide)
  have u65 := t65.self
  have a065 : reg m65 a0 = 0 := by
    rw [t65.regs, updz u64.zero (by decide), t64.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [a063']; rfl
  obtain ⟨m66, e66, t66⟩ := u65.taken hc63 0x106 bsd_at_100 (by decide)
    (by rw [a065, show reg m65 x0 = 0 from u65.zero]; rfl)
  have u66 := t66.self
  have g66 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ 20 →
      reg m66 r = reg m61 r := fun r h0 h1 h2 h3 h4 h5 hra' hg => by
    rw [t66.regs, t65.regs, updz u64.zero hg, t64.regs, updz t63.zero h0, g63 r h0 h1 h2 h3 h4 h5 hra']
  have v66_20 : reg m66 20 = (m.mem (b + 14)).zeroExtend 32 := by
    rw [t66.regs, t65.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [show reg m64 x0 = 0 from u64.zero, t64.regs, updz t63.zero (by decide), a163']
    exact BitVec.zero_add _
  have sp66 : reg m66 sp = G := by rw [g66 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp61
  have s066 : reg m66 8 = out := by rw [g66 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s061
  have k66 : ∀ r, r ∉ bsClob → reg m66 r = reg m r := fun r hr => by
    rw [g66 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]; exact k61 r hr
  have pre66 : Steps m m66 := pre61.trans (.cons e62 (c63.trans (.cons e64 (.cons e65 (.single e66)))))
  have v66_22 : reg m66 22 = mw m.mem b 8 := by rw [g66 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v61_22
  have v66_18 : reg m66 18 = (m.mem (b + 12)).zeroExtend 32 := by rw [g66 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v61_18
  have v66_9 : reg m66 9 = 5 := by rw [g66 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v61_9
  have v66_19 : reg m66 19 = (m.mem (b + 13)).zeroExtend 32 := by rw [g66 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v61_19
  -- 0x106: `Reader::u8`, byte 15.
  have hc66' := (Ly.code code O63).decode
  obtain ⟨m67, e67, t67⟩ := u66.aluImm hc66' bsd_at_106 (off' := 0x108) (by decide)
  obtain ⟨m68, c68, t68, sp68, a068, a168, fr68, mem68⟩ := bs_u8 Ly t67 (Ly.code code O63) bsd_at_108
    bsd_at_10c (by decide) (by decide) (by rw [updz u66.zero (by decide)]; exact sp66)
    (by simp +decide only [upd, ite_true, ite_false]; rw [sp66]; rfl) rp63 rl63
  rw [bs_u8_val 15 (by omega) rp63 rl63 rq63] at a068 a168
  have a068' : reg m68 a0 = 0 := a068
  have a168' : reg m68 a1 = (m.mem (b + 15)).zeroExtend 32 := by
    rw [a168]; show (m63.mem (b + BitVec.ofNat 32 15)).zeroExtend 32 = _; rw [bO _ O63 15 (by omega)]; rfl
  have mm68 : ∀ x, Sep (R + BitVec.ofNat 32 32) 16 x 1 →
      m68.mem x = memStore32 m63.mem (G + 0xC + 8) (BitVec.ofNat 32 (15 + 1)) x := fun x hx => by
    have e : reservedMem m63.mem (G + 0xC) 1 x = memStore32 m63.mem (G + 0xC + 8) (BitVec.ofNat 32 (15 + 1)) x :=
      bs_reservedMem_val 15 1 (by omega) rp63 rl63 rq63 x
    rw [mem68 x hx, e]
  obtain ⟨rp68, rl68, rq68, O68, S68⟩ := Ly.advance (c := 32) (N := 16) (by omega) rp63 rl63 O63 S63 mm68
  have g68 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m68 r = reg m66 r :=
    fun r h0 h1 h2 h3 h4 h5 hra' => by rw [fr68 r h0 h1 h2 h3 h4 h5 hra', updz u66.zero h0]
  have hc68 := (Ly.code code O68).decode
  obtain ⟨m69, e69, t69⟩ := t68.aluImm hc68 bsd_at_110 (off' := 0x112) (by decide)
  have u69 := t69.self
  obtain ⟨m70, e70, t70⟩ := u69.alu hc68 bsd_at_112 (off' := 0x114) (by decide)
  have u70 := t70.self
  have a070 : reg m70 a0 = 0 := by
    rw [t70.regs, updz u69.zero (by decide), t69.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [a068']; rfl
  obtain ⟨m71, e71, t71⟩ := u70.taken hc68 0x11A bsd_at_114 (by decide)
    (by rw [a070, show reg m70 x0 = 0 from u70.zero]; rfl)
  have u71 := t71.self
  have g71 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ 21 →
      reg m71 r = reg m66 r := fun r h0 h1 h2 h3 h4 h5 hra' hg => by
    rw [t71.regs, t70.regs, updz u69.zero hg, t69.regs, updz t68.zero h0, g68 r h0 h1 h2 h3 h4 h5 hra']
  have v71_21 : reg m71 21 = (m.mem (b + 15)).zeroExtend 32 := by
    rw [t71.regs, t70.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [show reg m69 x0 = 0 from u69.zero, t69.regs, updz t68.zero (by decide), a168']
    exact BitVec.zero_add _
  have sp71 : reg m71 sp = G := by rw [g71 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp66
  have s071 : reg m71 8 = out := by rw [g71 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s066
  have k71 : ∀ r, r ∉ bsClob → reg m71 r = reg m r := fun r hr => by
    rw [g71 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]; exact k66 r hr
  have pre71 : Steps m m71 := pre66.trans (.cons e67 (c68.trans (.cons e69 (.cons e70 (.single e71)))))
  have v71_22 : reg m71 22 = mw m.mem b 8 := by rw [g71 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v66_22
  have v71_18 : reg m71 18 = (m.mem (b + 12)).zeroExtend 32 := by rw [g71 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v66_18
  have v71_9 : reg m71 9 = 5 := by rw [g71 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v66_9
  have v71_19 : reg m71 19 = (m.mem (b + 13)).zeroExtend 32 := by rw [g71 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v66_19
  have v71_20 : reg m71 20 = (m.mem (b + 14)).zeroExtend 32 := by rw [g71 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v66_20
  -- 0x11A: `Reader::reserved(12)`.
  obtain ⟨m72, e72, t72⟩ := u71.aluImm hc68 bsd_at_11a (off' := 0x11C) (by decide)
  have u72 := t72.self
  obtain ⟨m73, e73, t73⟩ := u72.aluImm hc68 bsd_at_11c (off' := 0x11E) (by decide)
  have g72 : ∀ r, r ≠ a0 → reg m72 r = reg m71 r := fun r h => by rw [t72.regs, updz u71.zero h]
  obtain ⟨m74, c74, t74, sp74, a074, fr74, mem74⟩ := bs_reserved (n := BitVec.ofNat 32 12) Ly t73 (Ly.code code O68)
    bsd_at_11e bsd_at_122 (by decide) (by decide) (by rw [updz u72.zero (by decide), g72 sp (by decide)]; exact sp71)
    (by rw [updz u72.zero (by decide), t72.regs]; simp +decide only [upd, ite_true, ite_false]; rw [sp71]; rfl)
    (by simp +decide only [upd, ite_true, ite_false]; rw [u72.zero]; rfl) (by decide) rp68 rl68
  rw [bs_reserved_val 16 12 (by omega) rp68 rl68 rq68 (fun i hi => bO _ O68 (16 + i) (by omega))] at a074
  have a074' : reg m74 a0 = if allZero m.mem (b + 16) 12 then 0xFF else 4 := a074
  have mm74 : ∀ x, Sep (R + BitVec.ofNat 32 32) 16 x 1 →
      m74.mem x = memStore32 m68.mem (G + 0xC + 8) (BitVec.ofNat 32 28) x :=
    fun x hx => by rw [mem74 x hx, bs_reservedMem_val 16 12 (by omega) rp68 rl68 rq68 x]
  obtain ⟨rp74, rl74, rq74, O74, S74⟩ := Ly.advance (c := 32) (N := 16) (by omega) rp68 rl68 O68 S68 mm74
  have g74 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m74 r = reg m71 r :=
    fun r h0 h1 h2 h3 h4 h5 hra' => by
      rw [fr74 r h0 h1 h2 h3 h4 h5 hra', updz u72.zero h1, g72 r h0]
  have hc74 := (Ly.code code O74).decode
  have pre74 : Steps m m74 := pre71.trans (.cons e72 (.cons e73 c74))
  have k74 : ∀ r, r ∉ bsClob → reg m74 r = reg m r := fun r hr => by
    rw [g74 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))
      (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))
      (bs_clob_ne hr (by decide))]; exact k71 r hr
  obtain ⟨m75, e75, t75⟩ := t74.aluImm hc74 bsd_at_126 (off' := 0x12A) (by decide)
  have u75 := t75.self
  obtain ⟨m76, e76, t76⟩ := u75.aluImm hc74 bsd_at_12a (off' := 0x12E) (by decide)
  have u76 := t76.self
  have g76 : ∀ r, r ≠ a1 → reg m76 r = reg m74 r := fun r h => by
    rw [t76.regs, updz u75.zero h, t75.regs, updz t74.zero h]
  have a176 : reg m76 a1 = (reg m74 a0 &&& 0xFF) + 0xFFFFFF01 := by
    rw [t76.regs]; simp +decide only [upd, ite_true, ite_false]; rw [t75.regs]
    simp +decide only [upd, ite_true, ite_false]; rfl
  have sp76 : reg m76 sp = G := by rw [g76 sp (by decide)]; exact sp74
  have s076 : reg m76 8 = out := by
    rw [g76 8 (by decide), g74 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact s071
  have k76 : ∀ r, r ∉ bsClob → reg m76 r = reg m r := fun r hr => by
    rw [g76 r (bs_clob_ne hr (by decide))]; exact k74 r hr
  have pre76 : Steps m m76 := pre74.trans (.cons e75 (.single e76))
  by_cases hz12 : allZero m.mem (b + 16) 12 = false
  · rw [hz12] at a074'
    obtain ⟨m77, e77, t77⟩ := u76.notTaken hc74 0x130 bsd_at_12e (by decide)
      (by rw [a176, a074', show reg m76 x0 = 0 from u76.zero]; decide)
    obtain ⟨m78, e78, t78⟩ := t77.alu hc74 bsd_at_130 (off' := 0x132) (by decide)
    obtain ⟨m79, e79, t79⟩ := t78.jump hc74 bsd_at_132 (off' := 0x16C) (by decide) (by rw [t78.pc]; decide)
    exact err16C m79 m74.mem _ 4 (pre76.trans (.cons e77 (.cons e78 (.single e79)))) t79 hc74
      (by rw [updz u76.zero (by decide)]; exact sp76) (by rw [updz u76.zero (by decide)]; exact s076)
      (by
        simp +decide only [upd, ite_true, ite_false]
        rw [show reg m76 x0 = 0 from u76.zero, g76 a0 (by decide), a074']; rfl)
      (by unfold bsErr; rw [hck, hm, hv, hz, hp5, hz12]; rfl) O74 S74
      (fun r hr => by rw [updz u76.zero (bs_clob_ne hr (by decide))]; exact k76 r hr)
  replace hz12 : allZero m.mem (b + 16) 12 = true := by
    cases hh : allZero m.mem (b + 16) 12
    · exact absurd hh hz12
    · rfl
  rw [hz12] at a074'
  obtain ⟨m77, e77, t77⟩ := u76.taken hc74 0x134 bsd_at_12e (by decide)
    (by rw [a176, a074', show reg m76 x0 = 0 from u76.zero]; decide)
  -- 0x134: `Reader::finish`, which passes: 28 bytes read of 28.
  obtain ⟨m78, e78, t78⟩ := t77.lw hc74 bsd_at_134 (off' := 0x136) (by decide)
    (by rw [sp76]; exact aligned_add hGa (k := 0x10) (by decide))
  have u78 := t78.self
  obtain ⟨m79, e79, t79⟩ := u78.lw hc74 bsd_at_136 (off' := 0x138) (by decide)
    (by rw [show reg m78 sp = G from by rw [t78.regs, updz u76.zero (by decide)]; exact sp76];
        exact aligned_add hGa (k := 0x14) (by decide))
  have u79 := t79.self
  have a079 : reg m79 a0 = 28 := by
    rw [t79.regs, updz u78.zero (by decide), t78.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [sp76, show G + 0x10 = G + 0xC + 4 from by rw [BitVec.add_assoc]; rfl]; exact rl74
  have a179 : reg m79 a1 = 28 := by
    rw [t79.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [show reg m78 sp = G from by rw [t78.regs, updz u76.zero (by decide)]; exact sp76,
      show G + 0x14 = G + 0xC + 8 from by rw [BitVec.add_assoc]; rfl]; exact rq74
  obtain ⟨m80, e80, t80⟩ := u79.notTaken hc74 0x13C bsd_at_138 (by decide) (by rw [a179, a079]; decide)
  have u80 := t80.self
  have g80 : ∀ r, r ≠ a0 → r ≠ a1 → reg m80 r = reg m74 r := fun r h0 h1 => by
    rw [t80.regs, t79.regs, updz u78.zero h1, t78.regs, updz u76.zero h0, g76 r h1]
  have g80' : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m80 r = reg m71 r :=
    fun r h0 h1 h2 h3 h4 h5 hra' => by rw [g80 r h0 h1, g74 r h0 h1 h2 h3 h4 h5 hra']
  have sp80 : reg m80 sp = G := by rw [g80 sp (by decide) (by decide)]; exact sp74
  have s080 : reg m80 8 = out := by
    rw [g80' 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s071
  have k80 : ∀ r, r ∉ bsClob → reg m80 r = reg m r := fun r hr => by
    rw [g80 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]; exact k74 r hr
  have pre80 : Steps m m80 := pre76.trans (.cons e77 (.cons e78 (.cons e79 (.single e80))))
  have v80 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m80 r = reg m71 r := g80'
  have v80_9 : reg m80 9 = 5 := by rw [v80 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v71_9
  have v80_18 : reg m80 18 = (m.mem (b + 12)).zeroExtend 32 := by
    rw [v80 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v71_18
  have v80_19 : reg m80 19 = (m.mem (b + 13)).zeroExtend 32 := by
    rw [v80 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v71_19
  have v80_20 : reg m80 20 = (m.mem (b + 14)).zeroExtend 32 := by
    rw [v80 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v71_20
  have v80_21 : reg m80 21 = (m.mem (b + 15)).zeroExtend 32 := by
    rw [v80 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v71_21
  have v80_22 : reg m80 22 = mw m.mem b 8 := by
    rw [v80 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v71_22
  have outLow : ∀ c, c + 1 ≤ 8 → (out + BitVec.ofNat 32 c).toNat + 1 ≤ 0x40000000 := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have outG : ∀ c, c < 8 → ∀ k, 0x20 ≤ k → k < 0x40 → G + BitVec.ofNat 32 k ≠ out + BitVec.ofNat 32 c :=
    fun c hc k h1 h2 e' => hOS c (by omega) (48 + k) (by omega) (by rw [← Ly.g_ofs k, e'])
  -- The stores of a decoded state, at 0x154.
  have succ154 : ∀ (n : Machine) (g : Fin 32 → Word) (v3 : BitVec 8), Steps m n → St m74.mem BSD n 0x154 g →
      g sp = G → g 8 = out → g 22 = mw m.mem b 8 → (g 19).extractLsb' 0 8 = v3 →
      g 20 = (m.mem (b + 14)).zeroExtend 32 → g 21 = (m.mem (b + 15)).zeroExtend 32 →
      g 18 = (m.mem (b + 12)).zeroExtend 32 → (∀ r, r ∉ bsClob → g r = reg m r) → bsErr m.mem b = none →
      v3 = (if (bsTrial m.mem b).ult 2 then m.mem (b + 13) else 2) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ t0 → reg m' r = reg m r) ∧
        ∀ x, Sep R 112 x 1 → m'.mem x = bsMem m.mem out b x := by
    intro n g v3 hn s hs hs0 h22 h19 h20 h21 h18 hk hpe hv3
    obtain ⟨n1, d1, u1⟩ := s.sw hc74 bsd_at_154 (off' := 0x158) (by decide) (by rw [hs0, add_lit_zero]; exact hout)
    rw [hs0, h22, add_lit_zero] at u1
    have hc1 : CodeIn (memStore32 m74.mem out (mw m.mem b 8)) BSD bootstateDecodeCode :=
      hc74.store32 (lowSep (by omega) (by decide) (by decide))
    obtain ⟨n2, d2, u2⟩ := u1.sbG hc1 bsd_at_158 (off' := 0x15C) (by decide) (a := out + 4) (v := g 19) (by rw [hs0]) rfl
    rw [h19] at u2
    have hc2 := hc1.store8 (a := out + 4) (v := v3) (lowSep (outLow 4 (by omega)) (by decide) (by decide))
    obtain ⟨n3, d3, u3⟩ := u2.sbG hc2 bsd_at_15c (off' := 0x160) (by decide) (a := out + 5) (v := g 20) (by rw [hs0]) rfl
    rw [h20, zextByte_lo] at u3
    have hc3 := hc2.store8 (a := out + 5) (v := m.mem (b + 14)) (lowSep (outLow 5 (by omega)) (by decide) (by decide))
    obtain ⟨n4, d4, u4⟩ := u3.sbG hc3 bsd_at_160 (off' := 0x164) (by decide) (a := out + 6) (v := g 21) (by rw [hs0]) rfl
    rw [h21, zextByte_lo] at u4
    have hc4 := hc3.store8 (a := out + 6) (v := m.mem (b + 15)) (lowSep (outLow 6 (by omega)) (by decide) (by decide))
    obtain ⟨n5, d5, u5⟩ := u4.sbG hc4 bsd_at_164 (off' := 0x168) (by decide) (a := out + 7) (v := g 18) (by rw [hs0]) rfl
    rw [h18, zextByte_lo] at u5
    have hc5 := hc4.store8 (a := out + 7) (v := m.mem (b + 12)) (lowSep (outLow 7 (by omega)) (by decide) (by decide))
    obtain ⟨n6, d6, u6⟩ := u5.jump hc5 bsd_at_168 (off' := 0x176) (by decide) (by rw [u5.pc]; decide)
    refine exit176 n6 _ g (hn.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))))) u6 hc5 hs
      (fun k h1 h2 => ?_) hk (fun x hx => ?_)
    · rw [memStore8_ne (a := out + 7) (outG 7 (by omega) k h1 h2), memStore8_ne (a := out + 6) (outG 6 (by omega) k h1 h2),
        memStore8_ne (a := out + 5) (outG 5 (by omega) k h1 h2), memStore8_ne (a := out + 4) (outG 4 (by omega) k h1 h2),
        memStore32_get_sep (a := out) (by
          have := (hOS.sub (c := 0) (l := 4) (by omega)).subR (c := 48 + k) (l := 1) (by omega)
          rwa [add_ofNat_zero, ← Ly.g_ofs k] at this)]
      exact S74 k h1 h2
    · unfold bsMem; rw [hpe, ← hv3]
      exact memStore8_congr (memStore8_congr (memStore8_congr (memStore8_congr (memStore32_congr (O74 x hx)))))
  -- 0x13C: boots left and the confirmed bits.
  obtain ⟨m81, e81, t81⟩ := u80.alu hc74 bsd_at_13c (off' := 0x140) (by decide)
  have u81 := t81.self
  obtain ⟨m82, e82, t82⟩ := u81.aluImm hc74 bsd_at_140 (off' := 0x144) (by decide)
  have u82 := t82.self
  obtain ⟨m83, e83, t83⟩ := u82.aluImm hc74 bsd_at_144 (off' := 0x146) (by decide)
  have u83 := t83.self
  have g83 : ∀ r, r ≠ a0 → r ≠ a1 → reg m83 r = reg m80 r := fun r h0 h1 => by
    rw [t83.regs, updz u82.zero h1, t82.regs, updz u81.zero h0, t81.regs, updz u80.zero h0]
  have a083 : reg m83 a0 = ((m.mem (b + 15)).zeroExtend 32 ||| (m.mem (b + 14)).zeroExtend 32) &&& 0xFF := by
    rw [t83.regs, updz u82.zero (by decide), t82.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [t81.regs]; simp +decide only [upd, ite_true, ite_false]; rw [v80_21, v80_20]; rfl
  have a183 : reg m83 a1 = 3 := by
    rw [t83.regs]; simp +decide only [upd, ite_true, ite_false]; rw [show reg m82 x0 = 0 from u82.zero]; rfl
  have sp83 : reg m83 sp = G := by rw [g83 sp (by decide) (by decide)]; exact sp80
  have s083 : reg m83 8 = out := by rw [g83 8 (by decide) (by decide)]; exact s080
  have k83 : ∀ r, r ∉ bsClob → reg m83 r = reg m r := fun r hr => by
    rw [g83 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]; exact k80 r hr
  have pre83 : Steps m m83 := pre80.trans (.cons e81 (.cons e82 (.single e83)))
  by_cases hr3 : (3 : Word).ult (((m.mem (b + 15)).zeroExtend 32 ||| (m.mem (b + 14)).zeroExtend 32) &&& 0xFF) = true
  · obtain ⟨m84, e84, t84⟩ := u83.taken hc74 0x16C bsd_at_146 (by decide) (by rw [a183, a083]; exact hr3)
    exact err16C m84 m74.mem (reg m83) 5 (pre83.trans (.single e84)) t84 hc74 sp83 s083
      (by rw [g83 9 (by decide) (by decide), v80_9]; rfl)
      (by unfold bsErr; rw [hck, hm, hv, hz, hp5, hz12, hr3]; rfl) O74 S74 k83
  replace hr3 : (3 : Word).ult (((m.mem (b + 15)).zeroExtend 32 ||| (m.mem (b + 14)).zeroExtend 32) &&& 0xFF) =
      false := by
    cases hh : (3 : Word).ult (((m.mem (b + 15)).zeroExtend 32 ||| (m.mem (b + 14)).zeroExtend 32) &&& 0xFF)
    · rfl
    · exact absurd hh hr3
  obtain ⟨m84, e84, t84⟩ := u83.notTaken hc74 0x14A bsd_at_146 (by decide) (by rw [a183, a083]; exact hr3)
  have u84 := t84.self
  -- 0x14A: the trial slot.
  obtain ⟨m85, e85, t85⟩ := u84.aluImm hc74 bsd_at_14a (off' := 0x14E) (by decide)
  have u85 := t85.self
  obtain ⟨m86, e86, t86⟩ := u85.aluImm hc74 bsd_at_14e (off' := 0x150) (by decide)
  have u86 := t86.self
  have g86 : ∀ r, r ≠ a0 → r ≠ a1 → reg m86 r = reg m80 r := fun r h0 h1 => by
    rw [t86.regs, updz u85.zero h1, t85.regs, updz u84.zero h0, t84.regs, g83 r h0 h1]
  have a086 : reg m86 a0 = bsTrial m.mem b := by
    rw [t86.regs, updz u85.zero (by decide), t85.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [t84.regs, g83 19 (by decide) (by decide), v80_19]; rfl
  have a186 : reg m86 a1 = 2 := by
    rw [t86.regs]; simp +decide only [upd, ite_true, ite_false]; rw [show reg m85 x0 = 0 from u85.zero]; rfl
  have sp86 : reg m86 sp = G := by rw [g86 sp (by decide) (by decide)]; exact sp80
  have s086 : reg m86 8 = out := by rw [g86 8 (by decide) (by decide)]; exact s080
  have k86 : ∀ r, r ∉ bsClob → reg m86 r = reg m r := fun r hr => by
    rw [g86 r (bs_clob_ne hr (by decide)) (bs_clob_ne hr (by decide))]; exact k80 r hr
  have pre86 : Steps m m86 := pre83.trans (.cons e84 (.cons e85 (.single e86)))
  by_cases ht : (bsTrial m.mem b).ult 2 = true
  · obtain ⟨m87, e87, t87⟩ := u86.notTaken hc74 0x154 bsd_at_150 (by decide)
      (by rw [a086, a186]; show (!(bsTrial m.mem b).ult 2) = false; rw [ht]; rfl)
    refine succ154 m87 (reg m86) (m.mem (b + 13)) (pre86.trans (.single e87)) t87 sp86 s086
      (by rw [g86 22 (by decide) (by decide)]; exact v80_22)
      (by rw [g86 19 (by decide) (by decide), v80_19]; exact zextByte_lo _)
      (by rw [g86 20 (by decide) (by decide)]; exact v80_20) (by rw [g86 21 (by decide) (by decide)]; exact v80_21)
      (by rw [g86 18 (by decide) (by decide)]; exact v80_18) k86
      (by unfold bsErr; rw [hck, hm, hv, hz, hp5, hz12, hr3, ht]; rfl) (by rw [ite_eq_left ht])
  replace ht : (bsTrial m.mem b).ult 2 = false := by
    cases hh : (bsTrial m.mem b).ult 2
    · rfl
    · exact absurd hh ht
  obtain ⟨m87, e87, t87⟩ := u86.taken hc74 0x18A bsd_at_150 (by decide)
    (by rw [a086, a186]; show (!(bsTrial m.mem b).ult 2) = true; rw [ht]; rfl)
  obtain ⟨m88, e88, t88⟩ := t87.aluImm hc74 bsd_at_18a (off' := 0x18E) (by decide)
  have a088 : upd (reg m86) a0 (aluEval .add (reg m86 a0) 0xFFFFFF01) a0 = bsTrial m.mem b + 0xFFFFFF01 := by
    simp +decide only [upd, ite_true, ite_false]; rw [a086]; rfl
  have z88 : upd (reg m86) a0 (aluEval .add (reg m86 a0) 0xFFFFFF01) x0 = 0 := by
    rw [updz u86.zero (by decide)]; exact u86.zero
  by_cases hff : (bsTrial m.mem b + 0xFFFFFF01 == 0) = false
  · obtain ⟨m89, e89, t89⟩ := t88.taken hc74 0x16C bsd_at_18e (by decide)
      (by rw [a088, z88]; show (!(bsTrial m.mem b + 0xFFFFFF01 == 0)) = true; rw [hff]; rfl)
    exact err16C m89 m74.mem _ 5 (pre86.trans (.cons e87 (.cons e88 (.single e89)))) t89 hc74
      (by rw [updz u86.zero (by decide)]; exact sp86) (by rw [updz u86.zero (by decide)]; exact s086)
      (by rw [updz u86.zero (by decide), g86 9 (by decide) (by decide), v80_9]; rfl)
      (by unfold bsErr; rw [hck, hm, hv, hz, hp5, hz12, hr3, ht, hff]; rfl) O74 S74
      (fun r hr => by rw [updz u86.zero (bs_clob_ne hr (by decide))]; exact k86 r hr)
  replace hff : (bsTrial m.mem b + 0xFFFFFF01 == 0) = true := by
    cases hh : (bsTrial m.mem b + 0xFFFFFF01 == 0)
    · exact absurd hh hff
    · rfl
  obtain ⟨m89, e89, t89⟩ := t88.notTaken hc74 0x190 bsd_at_18e (by decide)
    (by rw [a088, z88]; show (!(bsTrial m.mem b + 0xFFFFFF01 == 0)) = false; rw [hff]; rfl)
  have u89 := t89.self
  have g89 : ∀ r, r ≠ a0 → reg m89 r = reg m86 r := fun r h => by rw [t89.regs, updz u86.zero h]
  obtain ⟨m90, e90, t90⟩ := u89.aluImm hc74 bsd_at_190 (off' := 0x194) (by decide)
  have a090 : upd (reg m89) a0 (aluEval .and (reg m89 20) 0xFF) a0 = (m.mem (b + 14)).zeroExtend 32 &&& 0xFF := by
    simp +decide only [upd, ite_true, ite_false]; rw [g89 20 (by decide), g86 20 (by decide) (by decide), v80_20]; rfl
  have z90 : upd (reg m89) a0 (aluEval .and (reg m89 20) 0xFF) x0 = 0 := by
    rw [updz u89.zero (by decide)]; exact u89.zero
  by_cases hbl : ((m.mem (b + 14)).zeroExtend 32 &&& 0xFF == 0) = false
  · obtain ⟨m91, e91, t91⟩ := t90.taken hc74 0x16C bsd_at_194 (by decide)
      (by rw [a090, z90]; show (!((m.mem (b + 14)).zeroExtend 32 &&& 0xFF == 0)) = true; rw [hbl]; rfl)
    exact err16C m91 m74.mem _ 5 (pre86.trans (.cons e87 (.cons e88 (.cons e89 (.cons e90 (.single e91)))))) t91 hc74
      (by rw [updz u89.zero (by decide), g89 sp (by decide)]; exact sp86)
      (by rw [updz u89.zero (by decide), g89 8 (by decide)]; exact s086)
      (by rw [updz u89.zero (by decide), g89 9 (by decide), g86 9 (by decide) (by decide), v80_9]; rfl)
      (by unfold bsErr; rw [hck, hm, hv, hz, hp5, hz12, hr3, ht, hff, hbl]; rfl) O74 S74
      (fun r hr => by
        rw [updz u89.zero (bs_clob_ne hr (by decide)), g89 r (bs_clob_ne hr (by decide))]; exact k86 r hr)
  replace hbl : ((m.mem (b + 14)).zeroExtend 32 &&& 0xFF == 0) = true := by
    cases hh : ((m.mem (b + 14)).zeroExtend 32 &&& 0xFF == 0)
    · exact absurd hh hbl
    · rfl
  obtain ⟨m91, e91, t91⟩ := t90.notTaken hc74 0x196 bsd_at_194 (by decide)
    (by rw [a090, z90]; show (!((m.mem (b + 14)).zeroExtend 32 &&& 0xFF == 0)) = false; rw [hbl]; rfl)
  have u91 := t91.self
  obtain ⟨m92, e92, t92⟩ := u91.aluImm hc74 bsd_at_196 (off' := 0x198) (by decide)
  obtain ⟨m93, e93, t93⟩ := t92.jump hc74 bsd_at_198 (off' := 0x154) (by decide) (by rw [t92.pc]; decide)
  have g91 : ∀ r, r ≠ a0 → reg m91 r = reg m86 r := fun r h => by
    rw [t91.regs, updz u89.zero h, g89 r h]
  have q93 : ∀ r, r ≠ 19 → upd (reg m91) 19 (aluEval .add (reg m91 x0) 2) r = reg m91 r := fun r h =>
    updz u91.zero h
  refine succ154 m93 _ 2 (pre86.trans (.cons e87 (.cons e88 (.cons e89 (.cons e90 (.cons e91 (.cons e92
    (.single e93)))))))) t93 (by rw [q93 sp (by decide), g91 sp (by decide)]; exact sp86)
    (by rw [q93 8 (by decide), g91 8 (by decide)]; exact s086)
    (by rw [q93 22 (by decide), g91 22 (by decide), g86 22 (by decide) (by decide)]; exact v80_22)
    (by simp +decide only [upd, ite_true, ite_false]; rw [show reg m91 x0 = 0 from u91.zero]; rfl)
    (by rw [q93 20 (by decide), g91 20 (by decide), g86 20 (by decide) (by decide)]; exact v80_20)
    (by rw [q93 21 (by decide), g91 21 (by decide), g86 21 (by decide) (by decide)]; exact v80_21)
    (by rw [q93 18 (by decide), g91 18 (by decide), g86 18 (by decide) (by decide)]; exact v80_18)
    (fun r hr => by
      rw [q93 r (bs_clob_ne hr (by decide)), g91 r (bs_clob_ne hr (by decide))]; exact k86 r hr)
    (by unfold bsErr; rw [hck, hm, hv, hz, hp5, hz12, hr3, ht, hff, hbl]; rfl) (by rw [ite_eq_right (by rw [ht]; decide)])

end C3.RV32.Cur
