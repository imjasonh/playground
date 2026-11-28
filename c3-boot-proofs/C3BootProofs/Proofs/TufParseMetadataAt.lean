import C3BootProofs.Proof.FetchChunk
import C3BootProofs.Image.Bootloader
import C3BootProofs.Proofs.ReaderArray

/-! Fetch lemmas for `tuf::parse_metadata` (`tufParseMetadataCode`). -/

namespace C3.RV32

open C3.Image

/-- Where `tuf::parse_metadata` is in the image. -/
abbrev TPM : Word := BitVec.ofNat 32 tufParseMetadataAddress

set_option maxRecDepth 20000

/-- Bytes 0x0 to 0x104 of `tufParseMetadataCode`. -/
def pm_c0 : List Nat :=
  [0x19, 0x71, 0x86, 0xde, 0xa2, 0xdc, 0xa6, 0xda, 0xca, 0xd8, 0xce, 0xd6,
    0xd2, 0xd4, 0xd6, 0xd2, 0xda, 0xd0, 0xde, 0xce, 0xe2, 0xcc, 0xe6, 0xca,
    0xea, 0xc8, 0x3a, 0x8b, 0xb6, 0x8b, 0x2a, 0x8d, 0x68, 0x08, 0x85, 0x46,
    0x97, 0xf0, 0xff, 0xff, 0xe7, 0x80, 0xc0, 0xb2, 0xf2, 0x45, 0x63, 0x8b,
    0x05, 0x22, 0x02, 0x56, 0x68, 0x08, 0x97, 0xe0, 0xff, 0xff, 0xe7, 0x80,
    0x20, 0xf3, 0x72, 0x44, 0x83, 0x44, 0x01, 0x02, 0x63, 0x07, 0x04, 0x22,
    0x93, 0x05, 0x11, 0x02, 0x13, 0x05, 0x51, 0x01, 0x1d, 0x46, 0x97, 0xa0,
    0x00, 0x00, 0xe7, 0x80, 0xa0, 0xe4, 0x22, 0xc8, 0x23, 0x0a, 0x91, 0x00,
    0x68, 0x08, 0x0c, 0x08, 0x97, 0xd0, 0xff, 0xff, 0xe7, 0x80, 0x60, 0x29,
    0x03, 0x45, 0xc1, 0x01, 0x19, 0xed, 0x82, 0x54, 0xcd, 0xc0, 0x92, 0x59,
    0xa2, 0x5a, 0x32, 0x59, 0x68, 0x08, 0x0c, 0x08, 0x97, 0xd0, 0xff, 0xff,
    0xe7, 0x80, 0xa0, 0x27, 0x03, 0x45, 0xc1, 0x01, 0x01, 0xc5, 0x03, 0x45,
    0xd1, 0x01, 0xd9, 0xaa, 0x02, 0x5c, 0x63, 0x00, 0x0c, 0x08, 0x29, 0x45,
    0x63, 0x9d, 0xa9, 0x06, 0x92, 0x5c, 0xa2, 0x59, 0x32, 0x5a, 0xb7, 0x55,
    0xcc, 0x3f, 0x93, 0x85, 0x85, 0x8a, 0x29, 0x46, 0x26, 0x85, 0x97, 0xa0,
    0x00, 0x00, 0xe7, 0x80, 0x20, 0xd6, 0x31, 0xed, 0x19, 0x45, 0x63, 0x9c,
    0xac, 0x04, 0x03, 0x45, 0x1c, 0x00, 0x83, 0x45, 0x0c, 0x00, 0x03, 0x46,
    0x2c, 0x00, 0x83, 0x46, 0x3c, 0x00, 0x03, 0x47, 0x5c, 0x00, 0x83, 0x47,
    0x4c, 0x00, 0x22, 0x05, 0x4d, 0x8d, 0x42, 0x06, 0xe2, 0x06, 0x55, 0x8e,
    0x22, 0x07, 0x5d, 0x8f, 0x51, 0x8d, 0xb7, 0x75, 0x67, 0x6e, 0x19, 0x66,
    0x93, 0x85, 0x35, 0x97, 0x13, 0x06, 0x56, 0x46, 0x2d, 0x8d, 0x39, 0x8e,
    0x51, 0x8d, 0x01, 0xed, 0x68, 0x08, 0x0c, 0x08]
theorem pm_c0_ok : pm_c0 <+: List.drop 0 tufParseMetadataCode := by decide

/-- Bytes 0x100 to 0x204 of `tufParseMetadataCode`. -/
def pm_c1 : List Nat :=
  [0x68, 0x08, 0x0c, 0x08, 0x97, 0xd0, 0xff, 0xff, 0xe7, 0x80, 0x60, 0x1f,
    0x03, 0x45, 0xc1, 0x01, 0x3d, 0xfd, 0x02, 0x55, 0x01, 0xc5, 0x13, 0x05,
    0x10, 0x02, 0xb9, 0xa2, 0xb7, 0x56, 0xcc, 0x3f, 0x93, 0x86, 0x26, 0x8b,
    0x68, 0x08, 0x15, 0x47, 0xce, 0x85, 0x52, 0x86, 0x97, 0xe0, 0xff, 0xff,
    0xe7, 0x80, 0xa0, 0xc2, 0xf2, 0x45, 0x63, 0x87, 0x05, 0x12, 0x02, 0x56,
    0x68, 0x18, 0x97, 0xe0, 0xff, 0xff, 0xe7, 0x80, 0x40, 0xc5, 0x72, 0x55,
    0x63, 0x07, 0x05, 0x14, 0x86, 0x45, 0x5e, 0x86, 0xda, 0x86, 0x97, 0xf0,
    0xff, 0xff, 0xe7, 0x80, 0x80, 0x9e, 0x55, 0xfd, 0x68, 0x08, 0xd6, 0x85,
    0x4a, 0x86, 0x97, 0xe0, 0xff, 0xff, 0xe7, 0x80, 0xc0, 0xb4, 0x72, 0x44,
    0x83, 0x44, 0x01, 0x02, 0x63, 0x01, 0x04, 0x10, 0x93, 0x05, 0x11, 0x02,
    0x13, 0x05, 0x51, 0x03, 0x1d, 0x46, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80,
    0xe0, 0xd1, 0x22, 0xd8, 0x23, 0x0a, 0x91, 0x02, 0xb7, 0x4b, 0xcc, 0x3f,
    0x93, 0x8b, 0xcb, 0x77, 0x37, 0x4b, 0xcc, 0x3f, 0x13, 0x0b, 0x1b, 0x78,
    0x68, 0x08, 0x0c, 0x18, 0x97, 0xe0, 0xff, 0xff, 0xe7, 0x80, 0x80, 0xb5,
    0x03, 0x45, 0xc1, 0x01, 0xe3, 0x11, 0x05, 0xee, 0x82, 0x54, 0xe5, 0xc8,
    0x12, 0x5c, 0x68, 0x08, 0x15, 0x47, 0xa6, 0x85, 0x62, 0x86, 0xde, 0x86,
    0x97, 0xe0, 0xff, 0xff, 0xe7, 0x80, 0x60, 0xb9, 0xf2, 0x45, 0xc9, 0xcd,
    0x62, 0xc6, 0x02, 0x56, 0x68, 0x18, 0x97, 0xe0, 0xff, 0xff, 0xe7, 0x80,
    0x00, 0xbc, 0x72, 0x55, 0x2a, 0xc4, 0x45, 0xcd, 0x06, 0x4c, 0x68, 0x08,
    0x0d, 0x47, 0xa6, 0x85, 0x32, 0x46, 0xda, 0x86, 0x97, 0xe0, 0xff, 0xff,
    0xe7, 0x80, 0xa0, 0xb6, 0xf2, 0x45, 0xbd, 0xc5, 0x02, 0x56, 0x68, 0x18,
    0x97, 0xe0, 0xff, 0xff, 0xe7, 0x80, 0x60, 0xb9]
theorem pm_c1_ok : pm_c1 <+: List.drop 256 tufParseMetadataCode := by decide

/-- Bytes 0x200 to 0x2B4 of `tufParseMetadataCode`. -/
def pm_c2 : List Nat :=
  [0xe7, 0x80, 0x60, 0xb9, 0x72, 0x55, 0x41, 0xc9, 0x42, 0x55, 0xd2, 0x55,
    0x62, 0x56, 0x2a, 0xde, 0xae, 0xc0, 0xb2, 0xc2, 0xa2, 0x44, 0x68, 0x08,
    0x6c, 0x18, 0x97, 0xe0, 0xff, 0xff, 0xe7, 0x80, 0xe0, 0xad, 0x03, 0x45,
    0xc1, 0x01, 0xe3, 0x14, 0x05, 0xe6, 0x82, 0x55, 0xa5, 0xd9, 0x12, 0x56,
    0x68, 0x08, 0x15, 0x47, 0xde, 0x86, 0x97, 0xe0, 0xff, 0xff, 0xe7, 0x80,
    0x00, 0xb2, 0xf2, 0x45, 0x95, 0xc1, 0x02, 0x56, 0xa8, 0x00, 0x97, 0xe0,
    0xff, 0xff, 0xe7, 0x80, 0xc0, 0xb4, 0x26, 0x45, 0x31, 0xc5, 0xb6, 0x45,
    0x26, 0x86, 0xe2, 0x86, 0x97, 0xe0, 0xff, 0xff, 0xe7, 0x80, 0x40, 0xc5,
    0x5d, 0xd9, 0x55, 0xbd, 0x03, 0x45, 0x01, 0x02, 0x23, 0x20, 0x0d, 0x00,
    0x23, 0x02, 0xad, 0x00, 0x29, 0xa0, 0x23, 0x20, 0x0d, 0x00, 0x23, 0x02,
    0x9d, 0x00, 0xf6, 0x50, 0x66, 0x54, 0xd6, 0x54, 0x46, 0x59, 0xb6, 0x59,
    0x26, 0x5a, 0x96, 0x5a, 0x06, 0x5b, 0xf6, 0x4b, 0x66, 0x4c, 0xd6, 0x4c,
    0x46, 0x4d, 0x09, 0x61, 0x82, 0x80, 0x03, 0x45, 0x01, 0x04, 0xf9, 0xb7,
    0x03, 0x45, 0xc1, 0x04, 0xe1, 0xb7, 0x23, 0x20, 0x3d, 0x01, 0x23, 0x22,
    0x4d, 0x01, 0x23, 0x24, 0x5d, 0x01, 0x23, 0x26, 0x2d, 0x01, 0xe1, 0xb7]
theorem pm_c2_ok : pm_c2 <+: List.drop 512 tufParseMetadataCode := by decide

theorem pm_at_0 : fetchRel tufParseMetadataCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF80, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_2 : fetchRel tufParseMetadataCode 0x2 = some (.store .sw sp ra 0x7C, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_4 : fetchRel tufParseMetadataCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x78, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_6 : fetchRel tufParseMetadataCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x74, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_8 : fetchRel tufParseMetadataCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x70, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_a : fetchRel tufParseMetadataCode 0xA = some (.store .sw sp (19 : Fin 32) 0x6C, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_c : fetchRel tufParseMetadataCode 0xC = some (.store .sw sp (20 : Fin 32) 0x68, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_e : fetchRel tufParseMetadataCode 0xE = some (.store .sw sp (21 : Fin 32) 0x64, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_10 : fetchRel tufParseMetadataCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x60, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_12 : fetchRel tufParseMetadataCode 0x12 = some (.store .sw sp (23 : Fin 32) 0x5C, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_14 : fetchRel tufParseMetadataCode 0x14 = some (.store .sw sp (24 : Fin 32) 0x58, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_16 : fetchRel tufParseMetadataCode 0x16 = some (.store .sw sp (25 : Fin 32) 0x54, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_18 : fetchRel tufParseMetadataCode 0x18 = some (.store .sw sp (26 : Fin 32) 0x50, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1a : fetchRel tufParseMetadataCode 0x1A = some (.alu .add (22 : Fin 32) x0 a4, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1c : fetchRel tufParseMetadataCode 0x1C = some (.alu .add (23 : Fin 32) x0 a3, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1e : fetchRel tufParseMetadataCode 0x1E = some (.alu .add (26 : Fin 32) x0 a0, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_20 : fetchRel tufParseMetadataCode 0x20 = some (.aluImm .add a0 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_22 : fetchRel tufParseMetadataCode 0x22 = some (.aluImm .add a3 x0 0x1, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_24 : fetchRel tufParseMetadataCode 0x24 = some (.auipc ra 0xFFFFF000, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_28 : fetchRel tufParseMetadataCode 0x28 = some (.jalr ra ra 0xFFFFFB2C, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_2c : fetchRel tufParseMetadataCode 0x2C = some (.load .lw a1 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_2e : fetchRel tufParseMetadataCode 0x2E = some (.branch .beq a1 x0 0x236, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_32 : fetchRel tufParseMetadataCode 0x32 = some (.load .lw a2 sp 0x20, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_34 : fetchRel tufParseMetadataCode 0x34 = some (.aluImm .add a0 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_36 : fetchRel tufParseMetadataCode 0x36 = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_3a : fetchRel tufParseMetadataCode 0x3A = some (.jalr ra ra 0xFFFFFF32, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_3e : fetchRel tufParseMetadataCode 0x3E = some (.load .lw (8 : Fin 32) sp 0x1C, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_40 : fetchRel tufParseMetadataCode 0x40 = some (.load .lbu (9 : Fin 32) sp 0x20, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_44 : fetchRel tufParseMetadataCode 0x44 = some (.branch .beq (8 : Fin 32) x0 0x22E, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_48 : fetchRel tufParseMetadataCode 0x48 = some (.aluImm .add a1 sp 0x21, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_4c : fetchRel tufParseMetadataCode 0x4C = some (.aluImm .add a0 sp 0x15, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_50 : fetchRel tufParseMetadataCode 0x50 = some (.aluImm .add a2 x0 0x7, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_52 : fetchRel tufParseMetadataCode 0x52 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_56 : fetchRel tufParseMetadataCode 0x56 = some (.jalr ra ra 0xFFFFFE4A, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_5a : fetchRel tufParseMetadataCode 0x5A = some (.store .sw sp (8 : Fin 32) 0x10, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_5c : fetchRel tufParseMetadataCode 0x5C = some (.store .sb sp (9 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_60 : fetchRel tufParseMetadataCode 0x60 = some (.aluImm .add a0 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_62 : fetchRel tufParseMetadataCode 0x62 = some (.aluImm .add a1 sp 0x10, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_64 : fetchRel tufParseMetadataCode 0x64 = some (.auipc ra 0xFFFFD000, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_68 : fetchRel tufParseMetadataCode 0x68 = some (.jalr ra ra 0x296, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_6c : fetchRel tufParseMetadataCode 0x6C = some (.load .lbu a0 sp 0x1C, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_70 : fetchRel tufParseMetadataCode 0x70 = some (.branch .bne a0 x0 0x1E, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_72 : fetchRel tufParseMetadataCode 0x72 = some (.load .lw (9 : Fin 32) sp 0x20, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_74 : fetchRel tufParseMetadataCode 0x74 = some (.branch .beq (9 : Fin 32) x0 0xA2, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_76 : fetchRel tufParseMetadataCode 0x76 = some (.load .lw (19 : Fin 32) sp 0x24, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_78 : fetchRel tufParseMetadataCode 0x78 = some (.load .lw (21 : Fin 32) sp 0x28, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_7a : fetchRel tufParseMetadataCode 0x7A = some (.load .lw (18 : Fin 32) sp 0x2C, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_7c : fetchRel tufParseMetadataCode 0x7C = some (.aluImm .add a0 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_7e : fetchRel tufParseMetadataCode 0x7E = some (.aluImm .add a1 sp 0x10, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_80 : fetchRel tufParseMetadataCode 0x80 = some (.auipc ra 0xFFFFD000, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_84 : fetchRel tufParseMetadataCode 0x84 = some (.jalr ra ra 0x27A, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_88 : fetchRel tufParseMetadataCode 0x88 = some (.load .lbu a0 sp 0x1C, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_8c : fetchRel tufParseMetadataCode 0x8C = some (.branch .beq a0 x0 0x8, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_8e : fetchRel tufParseMetadataCode 0x8E = some (.load .lbu a0 sp 0x1D, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_92 : fetchRel tufParseMetadataCode 0x92 = some (.jal x0 0x1D6, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_94 : fetchRel tufParseMetadataCode 0x94 = some (.load .lw (24 : Fin 32) sp 0x20, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_96 : fetchRel tufParseMetadataCode 0x96 = some (.branch .beq (24 : Fin 32) x0 0x80, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_9a : fetchRel tufParseMetadataCode 0x9A = some (.aluImm .add a0 x0 0xA, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_9c : fetchRel tufParseMetadataCode 0x9C = some (.branch .bne (19 : Fin 32) a0 0x7A, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_a0 : fetchRel tufParseMetadataCode 0xA0 = some (.load .lw (25 : Fin 32) sp 0x24, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_a2 : fetchRel tufParseMetadataCode 0xA2 = some (.load .lw (19 : Fin 32) sp 0x28, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_a4 : fetchRel tufParseMetadataCode 0xA4 = some (.load .lw (20 : Fin 32) sp 0x2C, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_a6 : fetchRel tufParseMetadataCode 0xA6 = some (.lui a1 0x3FCC5000, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_aa : fetchRel tufParseMetadataCode 0xAA = some (.aluImm .add a1 a1 0xFFFFF8A8, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_ae : fetchRel tufParseMetadataCode 0xAE = some (.aluImm .add a2 x0 0xA, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_b0 : fetchRel tufParseMetadataCode 0xB0 = some (.alu .add a0 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_b2 : fetchRel tufParseMetadataCode 0xB2 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_b6 : fetchRel tufParseMetadataCode 0xB6 = some (.jalr ra ra 0xFFFFFD62, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_ba : fetchRel tufParseMetadataCode 0xBA = some (.branch .bne a0 x0 0x5C, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_bc : fetchRel tufParseMetadataCode 0xBC = some (.aluImm .add a0 x0 0x6, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_be : fetchRel tufParseMetadataCode 0xBE = some (.branch .bne (25 : Fin 32) a0 0x58, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_c2 : fetchRel tufParseMetadataCode 0xC2 = some (.load .lbu a0 (24 : Fin 32) 0x1, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_c6 : fetchRel tufParseMetadataCode 0xC6 = some (.load .lbu a1 (24 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_ca : fetchRel tufParseMetadataCode 0xCA = some (.load .lbu a2 (24 : Fin 32) 0x2, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_ce : fetchRel tufParseMetadataCode 0xCE = some (.load .lbu a3 (24 : Fin 32) 0x3, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_d2 : fetchRel tufParseMetadataCode 0xD2 = some (.load .lbu a4 (24 : Fin 32) 0x5, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_d6 : fetchRel tufParseMetadataCode 0xD6 = some (.load .lbu a5 (24 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_da : fetchRel tufParseMetadataCode 0xDA = some (.aluImm .sll a0 a0 0x8, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_dc : fetchRel tufParseMetadataCode 0xDC = some (.alu .or a0 a0 a1, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_de : fetchRel tufParseMetadataCode 0xDE = some (.aluImm .sll a2 a2 0x10, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_e0 : fetchRel tufParseMetadataCode 0xE0 = some (.aluImm .sll a3 a3 0x18, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_e2 : fetchRel tufParseMetadataCode 0xE2 = some (.alu .or a2 a2 a3, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_e4 : fetchRel tufParseMetadataCode 0xE4 = some (.aluImm .sll a4 a4 0x8, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_e6 : fetchRel tufParseMetadataCode 0xE6 = some (.alu .or a4 a4 a5, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_e8 : fetchRel tufParseMetadataCode 0xE8 = some (.alu .or a0 a0 a2, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_ea : fetchRel tufParseMetadataCode 0xEA = some (.lui a1 0x6E677000, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_ee : fetchRel tufParseMetadataCode 0xEE = some (.lui a2 0x6000, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_f0 : fetchRel tufParseMetadataCode 0xF0 = some (.aluImm .add a1 a1 0xFFFFF973, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_f4 : fetchRel tufParseMetadataCode 0xF4 = some (.aluImm .add a2 a2 0x465, 4) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_f8 : fetchRel tufParseMetadataCode 0xF8 = some (.alu .xor a0 a0 a1, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_fa : fetchRel tufParseMetadataCode 0xFA = some (.alu .xor a2 a2 a4, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_fc : fetchRel tufParseMetadataCode 0xFC = some (.alu .or a0 a0 a2, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_fe : fetchRel tufParseMetadataCode 0xFE = some (.branch .bne a0 x0 0x18, 2) :=
  (fetchRel_chunk pm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_100 : fetchRel tufParseMetadataCode 0x100 = some (.aluImm .add a0 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_102 : fetchRel tufParseMetadataCode 0x102 = some (.aluImm .add a1 sp 0x10, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_104 : fetchRel tufParseMetadataCode 0x104 = some (.auipc ra 0xFFFFD000, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_108 : fetchRel tufParseMetadataCode 0x108 = some (.jalr ra ra 0x1F6, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_10c : fetchRel tufParseMetadataCode 0x10C = some (.load .lbu a0 sp 0x1C, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_110 : fetchRel tufParseMetadataCode 0x110 = some (.branch .bne a0 x0 0xFFFFFF7E, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_112 : fetchRel tufParseMetadataCode 0x112 = some (.load .lw a0 sp 0x20, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_114 : fetchRel tufParseMetadataCode 0x114 = some (.branch .beq a0 x0 0x8, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_116 : fetchRel tufParseMetadataCode 0x116 = some (.aluImm .add a0 x0 0x21, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_11a : fetchRel tufParseMetadataCode 0x11A = some (.jal x0 0x14E, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_11c : fetchRel tufParseMetadataCode 0x11C = some (.lui a3 0x3FCC5000, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_120 : fetchRel tufParseMetadataCode 0x120 = some (.aluImm .add a3 a3 0xFFFFF8B2, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_124 : fetchRel tufParseMetadataCode 0x124 = some (.aluImm .add a0 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_126 : fetchRel tufParseMetadataCode 0x126 = some (.aluImm .add a4 x0 0x5, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_128 : fetchRel tufParseMetadataCode 0x128 = some (.alu .add a1 x0 (19 : Fin 32), 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_12a : fetchRel tufParseMetadataCode 0x12A = some (.alu .add a2 x0 (20 : Fin 32), 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_12c : fetchRel tufParseMetadataCode 0x12C = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_130 : fetchRel tufParseMetadataCode 0x130 = some (.jalr ra ra 0xFFFFFC2A, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_134 : fetchRel tufParseMetadataCode 0x134 = some (.load .lw a1 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_136 : fetchRel tufParseMetadataCode 0x136 = some (.branch .beq a1 x0 0x12E, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_13a : fetchRel tufParseMetadataCode 0x13A = some (.load .lw a2 sp 0x20, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_13c : fetchRel tufParseMetadataCode 0x13C = some (.aluImm .add a0 sp 0x3C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_13e : fetchRel tufParseMetadataCode 0x13E = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_142 : fetchRel tufParseMetadataCode 0x142 = some (.jalr ra ra 0xFFFFFC54, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_146 : fetchRel tufParseMetadataCode 0x146 = some (.load .lw a0 sp 0x3C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_148 : fetchRel tufParseMetadataCode 0x148 = some (.branch .beq a0 x0 0x14E, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_14c : fetchRel tufParseMetadataCode 0x14C = some (.load .lw a1 sp 0x40, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_14e : fetchRel tufParseMetadataCode 0x14E = some (.alu .add a2 x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_150 : fetchRel tufParseMetadataCode 0x150 = some (.alu .add a3 x0 (22 : Fin 32), 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_152 : fetchRel tufParseMetadataCode 0x152 = some (.auipc ra 0xFFFFF000, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_156 : fetchRel tufParseMetadataCode 0x156 = some (.jalr ra ra 0xFFFFF9E8, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_15a : fetchRel tufParseMetadataCode 0x15A = some (.branch .bne a0 x0 0xFFFFFFBC, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_15c : fetchRel tufParseMetadataCode 0x15C = some (.aluImm .add a0 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_15e : fetchRel tufParseMetadataCode 0x15E = some (.alu .add a1 x0 (21 : Fin 32), 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_160 : fetchRel tufParseMetadataCode 0x160 = some (.alu .add a2 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_162 : fetchRel tufParseMetadataCode 0x162 = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_166 : fetchRel tufParseMetadataCode 0x166 = some (.jalr ra ra 0xFFFFFB4C, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_16a : fetchRel tufParseMetadataCode 0x16A = some (.load .lw (8 : Fin 32) sp 0x1C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_16c : fetchRel tufParseMetadataCode 0x16C = some (.load .lbu (9 : Fin 32) sp 0x20, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_170 : fetchRel tufParseMetadataCode 0x170 = some (.branch .beq (8 : Fin 32) x0 0x102, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_174 : fetchRel tufParseMetadataCode 0x174 = some (.aluImm .add a1 sp 0x21, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_178 : fetchRel tufParseMetadataCode 0x178 = some (.aluImm .add a0 sp 0x35, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_17c : fetchRel tufParseMetadataCode 0x17C = some (.aluImm .add a2 x0 0x7, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_17e : fetchRel tufParseMetadataCode 0x17E = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_182 : fetchRel tufParseMetadataCode 0x182 = some (.jalr ra ra 0xFFFFFD1E, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_186 : fetchRel tufParseMetadataCode 0x186 = some (.store .sw sp (8 : Fin 32) 0x30, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_188 : fetchRel tufParseMetadataCode 0x188 = some (.store .sb sp (9 : Fin 32) 0x34, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_18c : fetchRel tufParseMetadataCode 0x18C = some (.lui (23 : Fin 32) 0x3FCC4000, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_190 : fetchRel tufParseMetadataCode 0x190 = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0x77C, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_194 : fetchRel tufParseMetadataCode 0x194 = some (.lui (22 : Fin 32) 0x3FCC4000, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_198 : fetchRel tufParseMetadataCode 0x198 = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0x781, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_19c : fetchRel tufParseMetadataCode 0x19C = some (.aluImm .add a0 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_19e : fetchRel tufParseMetadataCode 0x19E = some (.aluImm .add a1 sp 0x30, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1a0 : fetchRel tufParseMetadataCode 0x1A0 = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1a4 : fetchRel tufParseMetadataCode 0x1A4 = some (.jalr ra ra 0xFFFFFB58, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1a8 : fetchRel tufParseMetadataCode 0x1A8 = some (.load .lbu a0 sp 0x1C, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1ac : fetchRel tufParseMetadataCode 0x1AC = some (.branch .bne a0 x0 0xFFFFFEE2, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1b0 : fetchRel tufParseMetadataCode 0x1B0 = some (.load .lw (9 : Fin 32) sp 0x20, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1b2 : fetchRel tufParseMetadataCode 0x1B2 = some (.branch .beq (9 : Fin 32) x0 0xF0, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1b4 : fetchRel tufParseMetadataCode 0x1B4 = some (.load .lw (24 : Fin 32) sp 0x24, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1b6 : fetchRel tufParseMetadataCode 0x1B6 = some (.aluImm .add a0 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1b8 : fetchRel tufParseMetadataCode 0x1B8 = some (.aluImm .add a4 x0 0x5, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1ba : fetchRel tufParseMetadataCode 0x1BA = some (.alu .add a1 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1bc : fetchRel tufParseMetadataCode 0x1BC = some (.alu .add a2 x0 (24 : Fin 32), 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1be : fetchRel tufParseMetadataCode 0x1BE = some (.alu .add a3 x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1c0 : fetchRel tufParseMetadataCode 0x1C0 = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1c4 : fetchRel tufParseMetadataCode 0x1C4 = some (.jalr ra ra 0xFFFFFB96, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1c8 : fetchRel tufParseMetadataCode 0x1C8 = some (.load .lw a1 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1ca : fetchRel tufParseMetadataCode 0x1CA = some (.branch .beq a1 x0 0x9A, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1cc : fetchRel tufParseMetadataCode 0x1CC = some (.store .sw sp (24 : Fin 32) 0xC, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1ce : fetchRel tufParseMetadataCode 0x1CE = some (.load .lw a2 sp 0x20, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1d0 : fetchRel tufParseMetadataCode 0x1D0 = some (.aluImm .add a0 sp 0x3C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1d2 : fetchRel tufParseMetadataCode 0x1D2 = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1d6 : fetchRel tufParseMetadataCode 0x1D6 = some (.jalr ra ra 0xFFFFFBC0, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1da : fetchRel tufParseMetadataCode 0x1DA = some (.load .lw a0 sp 0x3C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1dc : fetchRel tufParseMetadataCode 0x1DC = some (.store .sw sp a0 0x8, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1de : fetchRel tufParseMetadataCode 0x1DE = some (.branch .beq a0 x0 0xB8, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1e0 : fetchRel tufParseMetadataCode 0x1E0 = some (.load .lw (24 : Fin 32) sp 0x40, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1e2 : fetchRel tufParseMetadataCode 0x1E2 = some (.aluImm .add a0 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1e4 : fetchRel tufParseMetadataCode 0x1E4 = some (.aluImm .add a4 x0 0x3, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1e6 : fetchRel tufParseMetadataCode 0x1E6 = some (.alu .add a1 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1e8 : fetchRel tufParseMetadataCode 0x1E8 = some (.load .lw a2 sp 0xC, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1ea : fetchRel tufParseMetadataCode 0x1EA = some (.alu .add a3 x0 (22 : Fin 32), 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1ec : fetchRel tufParseMetadataCode 0x1EC = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1f0 : fetchRel tufParseMetadataCode 0x1F0 = some (.jalr ra ra 0xFFFFFB6A, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1f4 : fetchRel tufParseMetadataCode 0x1F4 = some (.load .lw a1 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1f6 : fetchRel tufParseMetadataCode 0x1F6 = some (.branch .beq a1 x0 0x6E, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1f8 : fetchRel tufParseMetadataCode 0x1F8 = some (.load .lw a2 sp 0x20, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1fa : fetchRel tufParseMetadataCode 0x1FA = some (.aluImm .add a0 sp 0x3C, 2) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_1fc : fetchRel tufParseMetadataCode 0x1FC = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk pm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_200 : fetchRel tufParseMetadataCode 0x200 = some (.jalr ra ra 0xFFFFFB96, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_204 : fetchRel tufParseMetadataCode 0x204 = some (.load .lw a0 sp 0x3C, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_206 : fetchRel tufParseMetadataCode 0x206 = some (.branch .beq a0 x0 0x90, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_208 : fetchRel tufParseMetadataCode 0x208 = some (.load .lw a0 sp 0x30, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_20a : fetchRel tufParseMetadataCode 0x20A = some (.load .lw a1 sp 0x34, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_20c : fetchRel tufParseMetadataCode 0x20C = some (.load .lw a2 sp 0x38, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_20e : fetchRel tufParseMetadataCode 0x20E = some (.store .sw sp a0 0x3C, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_210 : fetchRel tufParseMetadataCode 0x210 = some (.store .sw sp a1 0x40, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_212 : fetchRel tufParseMetadataCode 0x212 = some (.store .sw sp a2 0x44, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_214 : fetchRel tufParseMetadataCode 0x214 = some (.load .lw (9 : Fin 32) sp 0x8, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_216 : fetchRel tufParseMetadataCode 0x216 = some (.aluImm .add a0 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_218 : fetchRel tufParseMetadataCode 0x218 = some (.aluImm .add a1 sp 0x3C, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_21a : fetchRel tufParseMetadataCode 0x21A = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_21e : fetchRel tufParseMetadataCode 0x21E = some (.jalr ra ra 0xFFFFFADE, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_222 : fetchRel tufParseMetadataCode 0x222 = some (.load .lbu a0 sp 0x1C, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_226 : fetchRel tufParseMetadataCode 0x226 = some (.branch .bne a0 x0 0xFFFFFE68, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_22a : fetchRel tufParseMetadataCode 0x22A = some (.load .lw a1 sp 0x20, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_22c : fetchRel tufParseMetadataCode 0x22C = some (.branch .beq a1 x0 0xFFFFFF70, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_22e : fetchRel tufParseMetadataCode 0x22E = some (.load .lw a2 sp 0x24, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_230 : fetchRel tufParseMetadataCode 0x230 = some (.aluImm .add a0 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_232 : fetchRel tufParseMetadataCode 0x232 = some (.aluImm .add a4 x0 0x5, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_234 : fetchRel tufParseMetadataCode 0x234 = some (.alu .add a3 x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_236 : fetchRel tufParseMetadataCode 0x236 = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_23a : fetchRel tufParseMetadataCode 0x23A = some (.jalr ra ra 0xFFFFFB20, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_23e : fetchRel tufParseMetadataCode 0x23E = some (.load .lw a1 sp 0x1C, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_240 : fetchRel tufParseMetadataCode 0x240 = some (.branch .beq a1 x0 0x24, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_242 : fetchRel tufParseMetadataCode 0x242 = some (.load .lw a2 sp 0x20, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_244 : fetchRel tufParseMetadataCode 0x244 = some (.aluImm .add a0 sp 0x48, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_246 : fetchRel tufParseMetadataCode 0x246 = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_24a : fetchRel tufParseMetadataCode 0x24A = some (.jalr ra ra 0xFFFFFB4C, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_24e : fetchRel tufParseMetadataCode 0x24E = some (.load .lw a0 sp 0x48, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_250 : fetchRel tufParseMetadataCode 0x250 = some (.branch .beq a0 x0 0x4C, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_252 : fetchRel tufParseMetadataCode 0x252 = some (.load .lw a1 sp 0x4C, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_254 : fetchRel tufParseMetadataCode 0x254 = some (.alu .add a2 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_256 : fetchRel tufParseMetadataCode 0x256 = some (.alu .add a3 x0 (24 : Fin 32), 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_258 : fetchRel tufParseMetadataCode 0x258 = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_25c : fetchRel tufParseMetadataCode 0x25C = some (.jalr ra ra 0xFFFFFC54, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_260 : fetchRel tufParseMetadataCode 0x260 = some (.branch .beq a0 x0 0xFFFFFFB6, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_262 : fetchRel tufParseMetadataCode 0x262 = some (.jal x0 0xFFFFFEB4, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_264 : fetchRel tufParseMetadataCode 0x264 = some (.load .lbu a0 sp 0x20, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_268 : fetchRel tufParseMetadataCode 0x268 = some (.store .sw (26 : Fin 32) x0 0x0, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_26c : fetchRel tufParseMetadataCode 0x26C = some (.store .sb (26 : Fin 32) a0 0x4, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_270 : fetchRel tufParseMetadataCode 0x270 = some (.jal x0 0xA, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_272 : fetchRel tufParseMetadataCode 0x272 = some (.store .sw (26 : Fin 32) x0 0x0, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_276 : fetchRel tufParseMetadataCode 0x276 = some (.store .sb (26 : Fin 32) (9 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_27a : fetchRel tufParseMetadataCode 0x27A = some (.load .lw ra sp 0x7C, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_27c : fetchRel tufParseMetadataCode 0x27C = some (.load .lw (8 : Fin 32) sp 0x78, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_27e : fetchRel tufParseMetadataCode 0x27E = some (.load .lw (9 : Fin 32) sp 0x74, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_280 : fetchRel tufParseMetadataCode 0x280 = some (.load .lw (18 : Fin 32) sp 0x70, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_282 : fetchRel tufParseMetadataCode 0x282 = some (.load .lw (19 : Fin 32) sp 0x6C, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_284 : fetchRel tufParseMetadataCode 0x284 = some (.load .lw (20 : Fin 32) sp 0x68, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_286 : fetchRel tufParseMetadataCode 0x286 = some (.load .lw (21 : Fin 32) sp 0x64, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_288 : fetchRel tufParseMetadataCode 0x288 = some (.load .lw (22 : Fin 32) sp 0x60, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_28a : fetchRel tufParseMetadataCode 0x28A = some (.load .lw (23 : Fin 32) sp 0x5C, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_28c : fetchRel tufParseMetadataCode 0x28C = some (.load .lw (24 : Fin 32) sp 0x58, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_28e : fetchRel tufParseMetadataCode 0x28E = some (.load .lw (25 : Fin 32) sp 0x54, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_290 : fetchRel tufParseMetadataCode 0x290 = some (.load .lw (26 : Fin 32) sp 0x50, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_292 : fetchRel tufParseMetadataCode 0x292 = some (.aluImm .add sp sp 0x80, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_294 : fetchRel tufParseMetadataCode 0x294 = some (.jalr x0 ra 0x0, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_296 : fetchRel tufParseMetadataCode 0x296 = some (.load .lbu a0 sp 0x40, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_29a : fetchRel tufParseMetadataCode 0x29A = some (.jal x0 0xFFFFFFCE, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_29c : fetchRel tufParseMetadataCode 0x29C = some (.load .lbu a0 sp 0x4C, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_2a0 : fetchRel tufParseMetadataCode 0x2A0 = some (.jal x0 0xFFFFFFC8, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_2a2 : fetchRel tufParseMetadataCode 0x2A2 = some (.store .sw (26 : Fin 32) (19 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_2a6 : fetchRel tufParseMetadataCode 0x2A6 = some (.store .sw (26 : Fin 32) (20 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_2aa : fetchRel tufParseMetadataCode 0x2AA = some (.store .sw (26 : Fin 32) (21 : Fin 32) 0x8, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_2ae : fetchRel tufParseMetadataCode 0x2AE = some (.store .sw (26 : Fin 32) (18 : Fin 32) 0xC, 4) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem pm_at_2b2 : fetchRel tufParseMetadataCode 0x2B2 = some (.jal x0 0xFFFFFFC8, 2) :=
  (fetchRel_chunk pm_c2_ok (by decide) (.inr (by decide))).trans (by decide)

end C3.RV32
