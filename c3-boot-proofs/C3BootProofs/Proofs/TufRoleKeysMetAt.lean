import C3BootProofs.Proof.FetchChunk
import C3BootProofs.Image.Bootloader
import C3BootProofs.Proofs.ReaderArray

/-! Fetch lemmas for `tuf::RoleKeys::met` (`tufRoleKeysMetCode`). -/

namespace C3.RV32

open C3.Image

/-- Where `tuf::RoleKeys::met` is in the image. -/
abbrev TRM : Word := BitVec.ofNat 32 tufRoleKeysMetAddress

set_option maxRecDepth 20000

/-- Bytes 0x0 to 0x104 of `tufRoleKeysMetCode`. -/
def rkm_c0 : List Nat :=
  [0x41, 0x71, 0x10, 0x03, 0x23, 0x26, 0x16, 0x06, 0x20, 0xd6, 0x64, 0xd2,
    0x23, 0x20, 0x26, 0x07, 0x23, 0x2e, 0x36, 0x05, 0x23, 0x2c, 0x46, 0x05,
    0x23, 0x2a, 0x56, 0x05, 0x23, 0x28, 0x66, 0x05, 0x23, 0x26, 0x76, 0x05,
    0x23, 0x24, 0x86, 0x05, 0x23, 0x22, 0x96, 0x05, 0x23, 0x20, 0xa6, 0x05,
    0x23, 0x2e, 0xb6, 0x03, 0x2e, 0x84, 0x8c, 0x41, 0x2e, 0xca, 0x4c, 0x40,
    0x2e, 0xc8, 0xaa, 0x89, 0x28, 0x10, 0x13, 0x06, 0x00, 0x02, 0x81, 0x45,
    0x24, 0x10, 0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0xa0, 0x4e, 0x02, 0xce,
    0x81, 0x4b, 0x01, 0x45, 0x03, 0xaa, 0x89, 0x53, 0x13, 0x87, 0x89, 0x51,
    0x14, 0x44, 0x50, 0x44, 0x93, 0x07, 0x20, 0x06, 0x13, 0x04, 0x00, 0x04,
    0x36, 0xd2, 0x32, 0xd0, 0x2a, 0xcc, 0x0a, 0x05, 0x26, 0x95, 0x2a, 0xc6,
    0x5e, 0x8b, 0x63, 0xfd, 0x4b, 0x2d, 0xb3, 0x0d, 0xfb, 0x02, 0x93, 0x0b,
    0x1b, 0x00, 0xce, 0x9d, 0x1d, 0x45, 0xe3, 0x67, 0x65, 0xff, 0x03, 0xcc,
    0x0d, 0x00, 0x13, 0x05, 0x1c, 0xf0, 0x6d, 0xd1, 0x13, 0x15, 0x2b, 0x00,
    0x3a, 0x95, 0x83, 0x2c, 0x05, 0x00, 0x13, 0x0d, 0x10, 0x02, 0x63, 0x64,
    0x94, 0x2d, 0x13, 0x09, 0x20, 0x06, 0xa8, 0x00, 0xb6, 0x85, 0x97, 0x00,
    0x00, 0x00, 0xe7, 0x80, 0xc0, 0x2f, 0xa6, 0x44, 0x03, 0x44, 0xc1, 0x04,
    0x63, 0x85, 0x04, 0x2e, 0x93, 0x1a, 0x6b, 0x00, 0x13, 0x85, 0x89, 0x31,
    0xaa, 0x9a, 0x1d, 0x46, 0x13, 0x05, 0xd1, 0x0c, 0x93, 0x05, 0xd1, 0x04,
    0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0x40, 0x4c, 0xa6, 0xc5, 0x23, 0x06,
    0x81, 0x0c, 0xa8, 0x00, 0xac, 0x01, 0x97, 0x00, 0x00, 0x00, 0xe7, 0x80,
    0xe0, 0x30, 0x03, 0x45, 0x81, 0x04, 0x63, 0x16, 0x05, 0x24, 0x36, 0x44,
    0x63, 0x02, 0x04, 0x1c, 0xc6, 0x44, 0xa8, 0x00]
theorem rkm_c0_ok : rkm_c0 <+: List.drop 0 tufRoleKeysMetCode := by decide

/-- Bytes 0x100 to 0x204 of `tufRoleKeysMetCode`. -/
def rkm_c1 : List Nat :=
  [0xc6, 0x44, 0xa8, 0x00, 0x15, 0x47, 0xa2, 0x85, 0x26, 0x86, 0xb7, 0x46,
    0xcc, 0x3f, 0x93, 0x86, 0xc6, 0x77, 0x97, 0x00, 0x00, 0x00, 0xe7, 0x80,
    0x40, 0x34, 0xa6, 0x45, 0x63, 0x86, 0x05, 0x22, 0x36, 0x46, 0x68, 0x03,
    0x97, 0x00, 0x00, 0x00, 0xe7, 0x80, 0xe0, 0x36, 0x03, 0x25, 0xc1, 0x18,
    0x63, 0x0f, 0x05, 0x20, 0x83, 0x25, 0x01, 0x19, 0x56, 0x86, 0xe6, 0x86,
    0x97, 0x00, 0x00, 0x00, 0xe7, 0x80, 0x00, 0x47, 0x4d, 0xd1, 0xa8, 0x00,
    0x0d, 0x47, 0xa2, 0x85, 0x26, 0x86, 0xb7, 0x46, 0xcc, 0x3f, 0x93, 0x86,
    0x16, 0x78, 0x97, 0x00, 0x00, 0x00, 0xe7, 0x80, 0x00, 0x30, 0xa6, 0x45,
    0x63, 0x84, 0x05, 0x1e, 0x36, 0x46, 0x68, 0x03, 0x97, 0x00, 0x00, 0x00,
    0xe7, 0x80, 0xa0, 0x32, 0x83, 0x2c, 0xc1, 0x18, 0x63, 0x8d, 0x0c, 0x1c,
    0x03, 0x25, 0x01, 0x19, 0x2a, 0xc4, 0x20, 0x10, 0xf2, 0x44, 0xc1, 0xc4,
    0x83, 0x2a, 0x04, 0x00, 0xa8, 0x00, 0x13, 0x06, 0x20, 0x06, 0xee, 0x85,
    0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0xc0, 0x40, 0x1d, 0x45, 0x63, 0x62,
    0x55, 0x05, 0x33, 0x85, 0x2a, 0x03, 0x4e, 0x95, 0x83, 0x45, 0x05, 0x00,
    0x03, 0x46, 0x81, 0x04, 0x93, 0x86, 0x15, 0xf0, 0x9d, 0xc2, 0x93, 0x06,
    0x16, 0xf0, 0x85, 0xc2, 0x63, 0x93, 0xc5, 0x02, 0x05, 0x05, 0x85, 0xc5,
    0x05, 0x46, 0x63, 0x9c, 0xc5, 0x02, 0x93, 0x05, 0x91, 0x04, 0x97, 0x00,
    0x00, 0x00, 0xe7, 0x80, 0xe0, 0x2f, 0x7d, 0xe5, 0x29, 0xa0, 0xf1, 0x8d,
    0x13, 0x85, 0x15, 0xf0, 0x75, 0xc1, 0x11, 0x04, 0xf1, 0x14, 0x85, 0xc4,
    0x45, 0xb7, 0x13, 0x06, 0x10, 0x04, 0x93, 0x05, 0x91, 0x04, 0x97, 0xc0,
    0x00, 0x00, 0xe7, 0x80, 0x60, 0x32, 0x69, 0xc5, 0xdd, 0xb7, 0x93, 0x05,
    0x91, 0x04, 0x97, 0x00, 0x00, 0x00, 0xe7, 0x80]
theorem rkm_c1_ok : rkm_c1 <+: List.drop 256 tufRoleKeysMetCode := by decide

/-- Bytes 0x200 to 0x304 of `tufRoleKeysMetCode`. -/
def rkm_c2 : List Nat :=
  [0x00, 0x00, 0xe7, 0x80, 0x40, 0x2e, 0x4d, 0xed, 0xd9, 0xbf, 0xa8, 0x00,
    0x13, 0x06, 0x00, 0x08, 0x81, 0x45, 0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80,
    0x20, 0x32, 0xb0, 0x00, 0x66, 0x85, 0xa2, 0x45, 0x97, 0x00, 0x00, 0x00,
    0xe7, 0x80, 0xc0, 0x2d, 0x41, 0xcd, 0xaa, 0x86, 0x2e, 0x86, 0x13, 0x84,
    0x1d, 0x00, 0x09, 0x45, 0x63, 0x02, 0xac, 0x06, 0x05, 0x45, 0x63, 0x1a,
    0xac, 0x06, 0xa8, 0x01, 0xb6, 0x85, 0x97, 0xf0, 0xff, 0xff, 0xe7, 0x80,
    0xe0, 0x30, 0x03, 0x45, 0x81, 0x0c, 0x2d, 0xe9, 0x68, 0x12, 0x13, 0x06,
    0x00, 0x03, 0x93, 0x05, 0x91, 0x0c, 0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80,
    0x20, 0x34, 0xe8, 0x0a, 0x13, 0x06, 0x00, 0x03, 0x93, 0x05, 0x91, 0x0f,
    0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0x00, 0x33, 0x68, 0x03, 0xd2, 0x45,
    0x42, 0x46, 0x97, 0xd0, 0xff, 0xff, 0xe7, 0x80, 0x20, 0x92, 0x6c, 0x03,
    0x13, 0x06, 0x00, 0x03, 0x74, 0x12, 0xf8, 0x0a, 0x22, 0x85, 0x97, 0xe0,
    0xff, 0xff, 0xe7, 0x80, 0xe0, 0xcd, 0xbd, 0xa8, 0x13, 0x05, 0x06, 0xfc,
    0x15, 0xe1, 0x22, 0x85, 0xd2, 0x45, 0x42, 0x46, 0x97, 0x90, 0xff, 0xff,
    0xe7, 0x80, 0x20, 0xed, 0xa5, 0xa0, 0xa8, 0x01, 0xb6, 0x85, 0x97, 0xf0,
    0xff, 0xff, 0xe7, 0x80, 0x00, 0xef, 0x03, 0x45, 0x81, 0x0c, 0x11, 0xc9,
    0x13, 0x87, 0x89, 0x51, 0x92, 0x56, 0x02, 0x56, 0x93, 0x07, 0x20, 0x06,
    0x13, 0x04, 0x00, 0x04, 0x65, 0xb3, 0x68, 0x12, 0x13, 0x06, 0x00, 0x02,
    0x93, 0x05, 0x91, 0x0c, 0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0x00, 0x2c,
    0xe8, 0x0a, 0x13, 0x06, 0x00, 0x02, 0x93, 0x05, 0x91, 0x0e, 0x97, 0xc0,
    0x00, 0x00, 0xe7, 0x80, 0xe0, 0x2a, 0x68, 0x03, 0xd2, 0x45, 0x42, 0x46,
    0x97, 0xd0, 0xff, 0xff, 0xe7, 0x80, 0xc0, 0x83]
theorem rkm_c2_ok : rkm_c2 <+: List.drop 512 tufRoleKeysMetCode := by decide

/-- Bytes 0x300 to 0x3AE of `tufRoleKeysMetCode`. -/
def rkm_c3 : List Nat :=
  [0xe7, 0x80, 0xc0, 0x83, 0x6c, 0x03, 0x70, 0x12, 0xf4, 0x0a, 0x22, 0x85,
    0x97, 0xd0, 0xff, 0xff, 0xe7, 0x80, 0xa0, 0xb4, 0x13, 0x87, 0x89, 0x51,
    0x92, 0x56, 0x02, 0x56, 0x93, 0x07, 0x20, 0x06, 0x13, 0x04, 0x00, 0x04,
    0xe3, 0x0a, 0x05, 0xd4, 0x62, 0x45, 0xa1, 0x45, 0x63, 0x01, 0xb5, 0x04,
    0xb2, 0x45, 0x23, 0xa0, 0x65, 0x01, 0x05, 0x05, 0xf2, 0x45, 0x91, 0x05,
    0x2e, 0xce, 0x24, 0x10, 0x05, 0xbb, 0x03, 0x4d, 0x91, 0x04, 0x25, 0xa0,
    0x03, 0x4d, 0xc1, 0x04, 0x0d, 0xa0, 0x03, 0x4d, 0x01, 0x19, 0x31, 0xa8,
    0x03, 0xa5, 0x09, 0x31, 0x83, 0xa5, 0x49, 0x31, 0x62, 0x46, 0x33, 0x35,
    0xa6, 0x00, 0x13, 0x45, 0xf5, 0xff, 0x93, 0xb5, 0x15, 0x00, 0x33, 0x7d,
    0xb5, 0x00, 0x33, 0x35, 0x4b, 0x01, 0xea, 0x85, 0x10, 0x03, 0x83, 0x20,
    0xc6, 0x06, 0x20, 0x56, 0x64, 0x52, 0x03, 0x29, 0x06, 0x06, 0x83, 0x29,
    0xc6, 0x05, 0x03, 0x2a, 0x86, 0x05, 0x83, 0x2a, 0x46, 0x05, 0x03, 0x2b,
    0x06, 0x05, 0x83, 0x2b, 0xc6, 0x04, 0x03, 0x2c, 0x86, 0x04, 0x83, 0x2c,
    0x46, 0x04, 0x03, 0x2d, 0x06, 0x04, 0x83, 0x2d, 0xc6, 0x03, 0x7d, 0x61,
    0x82, 0x80, 0x22, 0x8d, 0xc9, 0xb7]
theorem rkm_c3_ok : rkm_c3 <+: List.drop 768 tufRoleKeysMetCode := by decide

theorem rkm_at_0 : fetchRel tufRoleKeysMetCode 0x0 = some (.aluImm .add sp sp 0xFFFFFE10, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2 : fetchRel tufRoleKeysMetCode 0x2 = some (.aluImm .add a2 sp 0x180, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_4 : fetchRel tufRoleKeysMetCode 0x4 = some (.store .sw a2 ra 0x6C, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_8 : fetchRel tufRoleKeysMetCode 0x8 = some (.store .sw a2 (8 : Fin 32) 0x68, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_a : fetchRel tufRoleKeysMetCode 0xA = some (.store .sw a2 (9 : Fin 32) 0x64, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_c : fetchRel tufRoleKeysMetCode 0xC = some (.store .sw a2 (18 : Fin 32) 0x60, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_10 : fetchRel tufRoleKeysMetCode 0x10 = some (.store .sw a2 (19 : Fin 32) 0x5C, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_14 : fetchRel tufRoleKeysMetCode 0x14 = some (.store .sw a2 (20 : Fin 32) 0x58, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_18 : fetchRel tufRoleKeysMetCode 0x18 = some (.store .sw a2 (21 : Fin 32) 0x54, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1c : fetchRel tufRoleKeysMetCode 0x1C = some (.store .sw a2 (22 : Fin 32) 0x50, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_20 : fetchRel tufRoleKeysMetCode 0x20 = some (.store .sw a2 (23 : Fin 32) 0x4C, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_24 : fetchRel tufRoleKeysMetCode 0x24 = some (.store .sw a2 (24 : Fin 32) 0x48, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_28 : fetchRel tufRoleKeysMetCode 0x28 = some (.store .sw a2 (25 : Fin 32) 0x44, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2c : fetchRel tufRoleKeysMetCode 0x2C = some (.store .sw a2 (26 : Fin 32) 0x40, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_30 : fetchRel tufRoleKeysMetCode 0x30 = some (.store .sw a2 (27 : Fin 32) 0x3C, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_34 : fetchRel tufRoleKeysMetCode 0x34 = some (.alu .add (8 : Fin 32) x0 a1, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_36 : fetchRel tufRoleKeysMetCode 0x36 = some (.load .lw a1 a1 0x0, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_38 : fetchRel tufRoleKeysMetCode 0x38 = some (.store .sw sp a1 0x14, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_3a : fetchRel tufRoleKeysMetCode 0x3A = some (.load .lw a1 (8 : Fin 32) 0x4, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_3c : fetchRel tufRoleKeysMetCode 0x3C = some (.store .sw sp a1 0x10, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_3e : fetchRel tufRoleKeysMetCode 0x3E = some (.alu .add (19 : Fin 32) x0 a0, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_40 : fetchRel tufRoleKeysMetCode 0x40 = some (.aluImm .add a0 sp 0x28, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_42 : fetchRel tufRoleKeysMetCode 0x42 = some (.aluImm .add a2 x0 0x20, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_46 : fetchRel tufRoleKeysMetCode 0x46 = some (.aluImm .add a1 x0 0x0, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_48 : fetchRel tufRoleKeysMetCode 0x48 = some (.aluImm .add (9 : Fin 32) sp 0x28, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_4a : fetchRel tufRoleKeysMetCode 0x4A = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_4e : fetchRel tufRoleKeysMetCode 0x4E = some (.jalr ra ra 0x4EA, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_52 : fetchRel tufRoleKeysMetCode 0x52 = some (.store .sw sp x0 0x1C, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_54 : fetchRel tufRoleKeysMetCode 0x54 = some (.aluImm .add (23 : Fin 32) x0 0x0, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_56 : fetchRel tufRoleKeysMetCode 0x56 = some (.aluImm .add a0 x0 0x0, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_58 : fetchRel tufRoleKeysMetCode 0x58 = some (.load .lw (20 : Fin 32) (19 : Fin 32) 0x538, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_5c : fetchRel tufRoleKeysMetCode 0x5C = some (.aluImm .add a4 (19 : Fin 32) 0x518, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_60 : fetchRel tufRoleKeysMetCode 0x60 = some (.load .lw a3 (8 : Fin 32) 0x8, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_62 : fetchRel tufRoleKeysMetCode 0x62 = some (.load .lw a2 (8 : Fin 32) 0xC, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_64 : fetchRel tufRoleKeysMetCode 0x64 = some (.aluImm .add a5 x0 0x62, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_68 : fetchRel tufRoleKeysMetCode 0x68 = some (.aluImm .add (8 : Fin 32) x0 0x40, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_6c : fetchRel tufRoleKeysMetCode 0x6C = some (.store .sw sp a3 0x24, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_6e : fetchRel tufRoleKeysMetCode 0x6E = some (.store .sw sp a2 0x20, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_70 : fetchRel tufRoleKeysMetCode 0x70 = some (.store .sw sp a0 0x18, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_72 : fetchRel tufRoleKeysMetCode 0x72 = some (.aluImm .sll a0 a0 0x2, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_74 : fetchRel tufRoleKeysMetCode 0x74 = some (.alu .add a0 a0 (9 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_76 : fetchRel tufRoleKeysMetCode 0x76 = some (.store .sw sp a0 0xC, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_78 : fetchRel tufRoleKeysMetCode 0x78 = some (.alu .add (22 : Fin 32) x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_7a : fetchRel tufRoleKeysMetCode 0x7A = some (.branch .bgeu (23 : Fin 32) (20 : Fin 32) 0x2DA, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_7e : fetchRel tufRoleKeysMetCode 0x7E = some (.alu .mul (27 : Fin 32) (22 : Fin 32) a5, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_82 : fetchRel tufRoleKeysMetCode 0x82 = some (.aluImm .add (23 : Fin 32) (22 : Fin 32) 0x1, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_86 : fetchRel tufRoleKeysMetCode 0x86 = some (.alu .add (27 : Fin 32) (27 : Fin 32) (19 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_88 : fetchRel tufRoleKeysMetCode 0x88 = some (.aluImm .add a0 x0 0x7, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_8a : fetchRel tufRoleKeysMetCode 0x8A = some (.branch .bltu a0 (22 : Fin 32) 0xFFFFFFEE, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_8e : fetchRel tufRoleKeysMetCode 0x8E = some (.load .lbu (24 : Fin 32) (27 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_92 : fetchRel tufRoleKeysMetCode 0x92 = some (.aluImm .add a0 (24 : Fin 32) 0xFFFFFF01, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_96 : fetchRel tufRoleKeysMetCode 0x96 = some (.branch .beq a0 x0 0xFFFFFFE2, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_98 : fetchRel tufRoleKeysMetCode 0x98 = some (.aluImm .sll a0 (22 : Fin 32) 0x2, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_9c : fetchRel tufRoleKeysMetCode 0x9C = some (.alu .add a0 a0 a4, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_9e : fetchRel tufRoleKeysMetCode 0x9E = some (.load .lw (25 : Fin 32) a0 0x0, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_a2 : fetchRel tufRoleKeysMetCode 0xA2 = some (.aluImm .add (26 : Fin 32) x0 0x21, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_a6 : fetchRel tufRoleKeysMetCode 0xA6 = some (.branch .bltu (8 : Fin 32) (25 : Fin 32) 0x2C8, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_aa : fetchRel tufRoleKeysMetCode 0xAA = some (.aluImm .add (18 : Fin 32) x0 0x62, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_ae : fetchRel tufRoleKeysMetCode 0xAE = some (.aluImm .add a0 sp 0x48, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_b0 : fetchRel tufRoleKeysMetCode 0xB0 = some (.alu .add a1 x0 a3, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_b2 : fetchRel tufRoleKeysMetCode 0xB2 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_b6 : fetchRel tufRoleKeysMetCode 0xB6 = some (.jalr ra ra 0x2FC, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_ba : fetchRel tufRoleKeysMetCode 0xBA = some (.load .lw (9 : Fin 32) sp 0x48, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_bc : fetchRel tufRoleKeysMetCode 0xBC = some (.load .lbu (8 : Fin 32) sp 0x4C, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_c0 : fetchRel tufRoleKeysMetCode 0xC0 = some (.branch .beq (9 : Fin 32) x0 0x2EA, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_c4 : fetchRel tufRoleKeysMetCode 0xC4 = some (.aluImm .sll (21 : Fin 32) (22 : Fin 32) 0x6, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_c8 : fetchRel tufRoleKeysMetCode 0xC8 = some (.aluImm .add a0 (19 : Fin 32) 0x318, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_cc : fetchRel tufRoleKeysMetCode 0xCC = some (.alu .add (21 : Fin 32) (21 : Fin 32) a0, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_ce : fetchRel tufRoleKeysMetCode 0xCE = some (.aluImm .add a2 x0 0x7, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_d0 : fetchRel tufRoleKeysMetCode 0xD0 = some (.aluImm .add a0 sp 0xCD, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_d4 : fetchRel tufRoleKeysMetCode 0xD4 = some (.aluImm .add a1 sp 0x4D, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_d8 : fetchRel tufRoleKeysMetCode 0xD8 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_dc : fetchRel tufRoleKeysMetCode 0xDC = some (.jalr ra ra 0x4C4, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_e0 : fetchRel tufRoleKeysMetCode 0xE0 = some (.store .sw sp (9 : Fin 32) 0xC8, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_e2 : fetchRel tufRoleKeysMetCode 0xE2 = some (.store .sb sp (8 : Fin 32) 0xCC, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_e6 : fetchRel tufRoleKeysMetCode 0xE6 = some (.aluImm .add a0 sp 0x48, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_e8 : fetchRel tufRoleKeysMetCode 0xE8 = some (.aluImm .add a1 sp 0xC8, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_ea : fetchRel tufRoleKeysMetCode 0xEA = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_ee : fetchRel tufRoleKeysMetCode 0xEE = some (.jalr ra ra 0x30E, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_f2 : fetchRel tufRoleKeysMetCode 0xF2 = some (.load .lbu a0 sp 0x48, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_f6 : fetchRel tufRoleKeysMetCode 0xF6 = some (.branch .bne a0 x0 0x24C, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_fa : fetchRel tufRoleKeysMetCode 0xFA = some (.load .lw (8 : Fin 32) sp 0x4C, 2) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_fc : fetchRel tufRoleKeysMetCode 0xFC = some (.branch .beq (8 : Fin 32) x0 0x1C4, 4) :=
  (fetchRel_chunk rkm_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_100 : fetchRel tufRoleKeysMetCode 0x100 = some (.load .lw (9 : Fin 32) sp 0x50, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_102 : fetchRel tufRoleKeysMetCode 0x102 = some (.aluImm .add a0 sp 0x48, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_104 : fetchRel tufRoleKeysMetCode 0x104 = some (.aluImm .add a4 x0 0x5, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_106 : fetchRel tufRoleKeysMetCode 0x106 = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_108 : fetchRel tufRoleKeysMetCode 0x108 = some (.alu .add a2 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_10a : fetchRel tufRoleKeysMetCode 0x10A = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_10e : fetchRel tufRoleKeysMetCode 0x10E = some (.aluImm .add a3 a3 0x77C, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_112 : fetchRel tufRoleKeysMetCode 0x112 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_116 : fetchRel tufRoleKeysMetCode 0x116 = some (.jalr ra ra 0x344, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_11a : fetchRel tufRoleKeysMetCode 0x11A = some (.load .lw a1 sp 0x48, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_11c : fetchRel tufRoleKeysMetCode 0x11C = some (.branch .beq a1 x0 0x22C, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_120 : fetchRel tufRoleKeysMetCode 0x120 = some (.load .lw a2 sp 0x4C, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_122 : fetchRel tufRoleKeysMetCode 0x122 = some (.aluImm .add a0 sp 0x18C, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_124 : fetchRel tufRoleKeysMetCode 0x124 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_128 : fetchRel tufRoleKeysMetCode 0x128 = some (.jalr ra ra 0x36E, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_12c : fetchRel tufRoleKeysMetCode 0x12C = some (.load .lw a0 sp 0x18C, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_130 : fetchRel tufRoleKeysMetCode 0x130 = some (.branch .beq a0 x0 0x21E, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_134 : fetchRel tufRoleKeysMetCode 0x134 = some (.load .lw a1 sp 0x190, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_138 : fetchRel tufRoleKeysMetCode 0x138 = some (.alu .add a2 x0 (21 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_13a : fetchRel tufRoleKeysMetCode 0x13A = some (.alu .add a3 x0 (25 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_13c : fetchRel tufRoleKeysMetCode 0x13C = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_140 : fetchRel tufRoleKeysMetCode 0x140 = some (.jalr ra ra 0x470, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_144 : fetchRel tufRoleKeysMetCode 0x144 = some (.branch .beq a0 x0 0xFFFFFFA2, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_146 : fetchRel tufRoleKeysMetCode 0x146 = some (.aluImm .add a0 sp 0x48, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_148 : fetchRel tufRoleKeysMetCode 0x148 = some (.aluImm .add a4 x0 0x3, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_14a : fetchRel tufRoleKeysMetCode 0x14A = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_14c : fetchRel tufRoleKeysMetCode 0x14C = some (.alu .add a2 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_14e : fetchRel tufRoleKeysMetCode 0x14E = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_152 : fetchRel tufRoleKeysMetCode 0x152 = some (.aluImm .add a3 a3 0x781, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_156 : fetchRel tufRoleKeysMetCode 0x156 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_15a : fetchRel tufRoleKeysMetCode 0x15A = some (.jalr ra ra 0x300, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_15e : fetchRel tufRoleKeysMetCode 0x15E = some (.load .lw a1 sp 0x48, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_160 : fetchRel tufRoleKeysMetCode 0x160 = some (.branch .beq a1 x0 0x1E8, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_164 : fetchRel tufRoleKeysMetCode 0x164 = some (.load .lw a2 sp 0x4C, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_166 : fetchRel tufRoleKeysMetCode 0x166 = some (.aluImm .add a0 sp 0x18C, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_168 : fetchRel tufRoleKeysMetCode 0x168 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_16c : fetchRel tufRoleKeysMetCode 0x16C = some (.jalr ra ra 0x32A, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_170 : fetchRel tufRoleKeysMetCode 0x170 = some (.load .lw (25 : Fin 32) sp 0x18C, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_174 : fetchRel tufRoleKeysMetCode 0x174 = some (.branch .beq (25 : Fin 32) x0 0x1DA, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_178 : fetchRel tufRoleKeysMetCode 0x178 = some (.load .lw a0 sp 0x190, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_17c : fetchRel tufRoleKeysMetCode 0x17C = some (.store .sw sp a0 0x8, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_17e : fetchRel tufRoleKeysMetCode 0x17E = some (.aluImm .add (8 : Fin 32) sp 0x28, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_180 : fetchRel tufRoleKeysMetCode 0x180 = some (.load .lw (9 : Fin 32) sp 0x1C, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_182 : fetchRel tufRoleKeysMetCode 0x182 = some (.branch .beq (9 : Fin 32) x0 0x88, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_184 : fetchRel tufRoleKeysMetCode 0x184 = some (.load .lw (21 : Fin 32) (8 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_188 : fetchRel tufRoleKeysMetCode 0x188 = some (.aluImm .add a0 sp 0x48, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_18a : fetchRel tufRoleKeysMetCode 0x18A = some (.aluImm .add a2 x0 0x62, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_18e : fetchRel tufRoleKeysMetCode 0x18E = some (.alu .add a1 x0 (27 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_190 : fetchRel tufRoleKeysMetCode 0x190 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_194 : fetchRel tufRoleKeysMetCode 0x194 = some (.jalr ra ra 0x40C, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_198 : fetchRel tufRoleKeysMetCode 0x198 = some (.aluImm .add a0 x0 0x7, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_19a : fetchRel tufRoleKeysMetCode 0x19A = some (.branch .bltu a0 (21 : Fin 32) 0x44, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_19e : fetchRel tufRoleKeysMetCode 0x19E = some (.alu .mul a0 (21 : Fin 32) (18 : Fin 32), 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1a2 : fetchRel tufRoleKeysMetCode 0x1A2 = some (.alu .add a0 a0 (19 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1a4 : fetchRel tufRoleKeysMetCode 0x1A4 = some (.load .lbu a1 a0 0x0, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1a8 : fetchRel tufRoleKeysMetCode 0x1A8 = some (.load .lbu a2 sp 0x48, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1ac : fetchRel tufRoleKeysMetCode 0x1AC = some (.aluImm .add a3 a1 0xFFFFFF01, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1b0 : fetchRel tufRoleKeysMetCode 0x1B0 = some (.branch .beq a3 x0 0x26, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1b2 : fetchRel tufRoleKeysMetCode 0x1B2 = some (.aluImm .add a3 a2 0xFFFFFF01, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1b6 : fetchRel tufRoleKeysMetCode 0x1B6 = some (.branch .beq a3 x0 0x20, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1b8 : fetchRel tufRoleKeysMetCode 0x1B8 = some (.branch .bne a1 a2 0x26, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1bc : fetchRel tufRoleKeysMetCode 0x1BC = some (.aluImm .add a0 a0 0x1, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1be : fetchRel tufRoleKeysMetCode 0x1BE = some (.branch .beq a1 x0 0x28, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1c0 : fetchRel tufRoleKeysMetCode 0x1C0 = some (.aluImm .add a2 x0 0x1, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1c2 : fetchRel tufRoleKeysMetCode 0x1C2 = some (.branch .bne a1 a2 0x38, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1c6 : fetchRel tufRoleKeysMetCode 0x1C6 = some (.aluImm .add a1 sp 0x49, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1ca : fetchRel tufRoleKeysMetCode 0x1CA = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1ce : fetchRel tufRoleKeysMetCode 0x1CE = some (.jalr ra ra 0x2FE, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1d2 : fetchRel tufRoleKeysMetCode 0x1D2 = some (.branch .bne a0 x0 0xEE, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1d4 : fetchRel tufRoleKeysMetCode 0x1D4 = some (.jal x0 0xA, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1d6 : fetchRel tufRoleKeysMetCode 0x1D6 = some (.alu .and a1 a1 a2, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1d8 : fetchRel tufRoleKeysMetCode 0x1D8 = some (.aluImm .add a0 a1 0xFFFFFF01, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1dc : fetchRel tufRoleKeysMetCode 0x1DC = some (.branch .beq a0 x0 0xE4, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1de : fetchRel tufRoleKeysMetCode 0x1DE = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1e0 : fetchRel tufRoleKeysMetCode 0x1E0 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFC, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1e2 : fetchRel tufRoleKeysMetCode 0x1E2 = some (.branch .beq (9 : Fin 32) x0 0x28, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1e4 : fetchRel tufRoleKeysMetCode 0x1E4 = some (.jal x0 0xFFFFFFA0, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1e6 : fetchRel tufRoleKeysMetCode 0x1E6 = some (.aluImm .add a2 x0 0x41, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1ea : fetchRel tufRoleKeysMetCode 0x1EA = some (.aluImm .add a1 sp 0x49, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1ee : fetchRel tufRoleKeysMetCode 0x1EE = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1f2 : fetchRel tufRoleKeysMetCode 0x1F2 = some (.jalr ra ra 0x326, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1f6 : fetchRel tufRoleKeysMetCode 0x1F6 = some (.branch .beq a0 x0 0xCA, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1f8 : fetchRel tufRoleKeysMetCode 0x1F8 = some (.jal x0 0xFFFFFFE6, 2) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1fa : fetchRel tufRoleKeysMetCode 0x1FA = some (.aluImm .add a1 sp 0x49, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_1fe : fetchRel tufRoleKeysMetCode 0x1FE = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkm_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_202 : fetchRel tufRoleKeysMetCode 0x202 = some (.jalr ra ra 0x2E4, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_206 : fetchRel tufRoleKeysMetCode 0x206 = some (.branch .bne a0 x0 0xBA, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_208 : fetchRel tufRoleKeysMetCode 0x208 = some (.jal x0 0xFFFFFFD6, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_20a : fetchRel tufRoleKeysMetCode 0x20A = some (.aluImm .add a0 sp 0x48, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_20c : fetchRel tufRoleKeysMetCode 0x20C = some (.aluImm .add a2 x0 0x80, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_210 : fetchRel tufRoleKeysMetCode 0x210 = some (.aluImm .add a1 x0 0x0, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_212 : fetchRel tufRoleKeysMetCode 0x212 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_216 : fetchRel tufRoleKeysMetCode 0x216 = some (.jalr ra ra 0x322, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_21a : fetchRel tufRoleKeysMetCode 0x21A = some (.aluImm .add a2 sp 0x48, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_21c : fetchRel tufRoleKeysMetCode 0x21C = some (.alu .add a0 x0 (25 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_21e : fetchRel tufRoleKeysMetCode 0x21E = some (.load .lw a1 sp 0x8, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_220 : fetchRel tufRoleKeysMetCode 0x220 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_224 : fetchRel tufRoleKeysMetCode 0x224 = some (.jalr ra ra 0x2DC, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_228 : fetchRel tufRoleKeysMetCode 0x228 = some (.branch .beq a0 x0 0x98, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_22a : fetchRel tufRoleKeysMetCode 0x22A = some (.alu .add a3 x0 a0, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_22c : fetchRel tufRoleKeysMetCode 0x22C = some (.alu .add a2 x0 a1, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_22e : fetchRel tufRoleKeysMetCode 0x22E = some (.aluImm .add (8 : Fin 32) (27 : Fin 32) 0x1, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_232 : fetchRel tufRoleKeysMetCode 0x232 = some (.aluImm .add a0 x0 0x2, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_234 : fetchRel tufRoleKeysMetCode 0x234 = some (.branch .beq (24 : Fin 32) a0 0x64, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_238 : fetchRel tufRoleKeysMetCode 0x238 = some (.aluImm .add a0 x0 0x1, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_23a : fetchRel tufRoleKeysMetCode 0x23A = some (.branch .bne (24 : Fin 32) a0 0x74, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_23e : fetchRel tufRoleKeysMetCode 0x23E = some (.aluImm .add a0 sp 0xC8, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_240 : fetchRel tufRoleKeysMetCode 0x240 = some (.alu .add a1 x0 a3, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_242 : fetchRel tufRoleKeysMetCode 0x242 = some (.auipc ra 0xFFFFF000, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_246 : fetchRel tufRoleKeysMetCode 0x246 = some (.jalr ra ra 0x30E, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_24a : fetchRel tufRoleKeysMetCode 0x24A = some (.load .lbu a0 sp 0xC8, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_24e : fetchRel tufRoleKeysMetCode 0x24E = some (.branch .bne a0 x0 0x72, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_250 : fetchRel tufRoleKeysMetCode 0x250 = some (.aluImm .add a0 sp 0x12C, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_252 : fetchRel tufRoleKeysMetCode 0x252 = some (.aluImm .add a2 x0 0x30, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_256 : fetchRel tufRoleKeysMetCode 0x256 = some (.aluImm .add a1 sp 0xC9, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_25a : fetchRel tufRoleKeysMetCode 0x25A = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_25e : fetchRel tufRoleKeysMetCode 0x25E = some (.jalr ra ra 0x342, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_262 : fetchRel tufRoleKeysMetCode 0x262 = some (.aluImm .add a0 sp 0x15C, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_264 : fetchRel tufRoleKeysMetCode 0x264 = some (.aluImm .add a2 x0 0x30, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_268 : fetchRel tufRoleKeysMetCode 0x268 = some (.aluImm .add a1 sp 0xF9, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_26c : fetchRel tufRoleKeysMetCode 0x26C = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_270 : fetchRel tufRoleKeysMetCode 0x270 = some (.jalr ra ra 0x330, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_274 : fetchRel tufRoleKeysMetCode 0x274 = some (.aluImm .add a0 sp 0x18C, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_276 : fetchRel tufRoleKeysMetCode 0x276 = some (.load .lw a1 sp 0x14, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_278 : fetchRel tufRoleKeysMetCode 0x278 = some (.load .lw a2 sp 0x10, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_27a : fetchRel tufRoleKeysMetCode 0x27A = some (.auipc ra 0xFFFFD000, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_27e : fetchRel tufRoleKeysMetCode 0x27E = some (.jalr ra ra 0xFFFFF922, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_282 : fetchRel tufRoleKeysMetCode 0x282 = some (.aluImm .add a1 sp 0x18C, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_284 : fetchRel tufRoleKeysMetCode 0x284 = some (.aluImm .add a2 x0 0x30, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_288 : fetchRel tufRoleKeysMetCode 0x288 = some (.aluImm .add a3 sp 0x12C, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_28a : fetchRel tufRoleKeysMetCode 0x28A = some (.aluImm .add a4 sp 0x15C, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_28c : fetchRel tufRoleKeysMetCode 0x28C = some (.alu .add a0 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_28e : fetchRel tufRoleKeysMetCode 0x28E = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_292 : fetchRel tufRoleKeysMetCode 0x292 = some (.jalr ra ra 0xFFFFFCDE, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_296 : fetchRel tufRoleKeysMetCode 0x296 = some (.jal x0 0x7E, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_298 : fetchRel tufRoleKeysMetCode 0x298 = some (.aluImm .add a0 a2 0xFFFFFFC0, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_29c : fetchRel tufRoleKeysMetCode 0x29C = some (.branch .bne a0 x0 0x24, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_29e : fetchRel tufRoleKeysMetCode 0x29E = some (.alu .add a0 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2a0 : fetchRel tufRoleKeysMetCode 0x2A0 = some (.load .lw a1 sp 0x14, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2a2 : fetchRel tufRoleKeysMetCode 0x2A2 = some (.load .lw a2 sp 0x10, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2a4 : fetchRel tufRoleKeysMetCode 0x2A4 = some (.auipc ra 0xFFFF9000, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2a8 : fetchRel tufRoleKeysMetCode 0x2A8 = some (.jalr ra ra 0xFFFFFED2, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2ac : fetchRel tufRoleKeysMetCode 0x2AC = some (.jal x0 0x68, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2ae : fetchRel tufRoleKeysMetCode 0x2AE = some (.aluImm .add a0 sp 0xC8, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2b0 : fetchRel tufRoleKeysMetCode 0x2B0 = some (.alu .add a1 x0 a3, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2b2 : fetchRel tufRoleKeysMetCode 0x2B2 = some (.auipc ra 0xFFFFF000, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2b6 : fetchRel tufRoleKeysMetCode 0x2B6 = some (.jalr ra ra 0xFFFFFEF0, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2ba : fetchRel tufRoleKeysMetCode 0x2BA = some (.load .lbu a0 sp 0xC8, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2be : fetchRel tufRoleKeysMetCode 0x2BE = some (.branch .beq a0 x0 0x14, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2c0 : fetchRel tufRoleKeysMetCode 0x2C0 = some (.aluImm .add a4 (19 : Fin 32) 0x518, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2c4 : fetchRel tufRoleKeysMetCode 0x2C4 = some (.load .lw a3 sp 0x24, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2c6 : fetchRel tufRoleKeysMetCode 0x2C6 = some (.load .lw a2 sp 0x20, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2c8 : fetchRel tufRoleKeysMetCode 0x2C8 = some (.aluImm .add a5 x0 0x62, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2cc : fetchRel tufRoleKeysMetCode 0x2CC = some (.aluImm .add (8 : Fin 32) x0 0x40, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2d0 : fetchRel tufRoleKeysMetCode 0x2D0 = some (.jal x0 0xFFFFFDA8, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2d2 : fetchRel tufRoleKeysMetCode 0x2D2 = some (.aluImm .add a0 sp 0x12C, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2d4 : fetchRel tufRoleKeysMetCode 0x2D4 = some (.aluImm .add a2 x0 0x20, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2d8 : fetchRel tufRoleKeysMetCode 0x2D8 = some (.aluImm .add a1 sp 0xC9, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2dc : fetchRel tufRoleKeysMetCode 0x2DC = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2e0 : fetchRel tufRoleKeysMetCode 0x2E0 = some (.jalr ra ra 0x2C0, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2e4 : fetchRel tufRoleKeysMetCode 0x2E4 = some (.aluImm .add a0 sp 0x15C, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2e6 : fetchRel tufRoleKeysMetCode 0x2E6 = some (.aluImm .add a2 x0 0x20, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2ea : fetchRel tufRoleKeysMetCode 0x2EA = some (.aluImm .add a1 sp 0xE9, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2ee : fetchRel tufRoleKeysMetCode 0x2EE = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2f2 : fetchRel tufRoleKeysMetCode 0x2F2 = some (.jalr ra ra 0x2AE, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2f6 : fetchRel tufRoleKeysMetCode 0x2F6 = some (.aluImm .add a0 sp 0x18C, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2f8 : fetchRel tufRoleKeysMetCode 0x2F8 = some (.load .lw a1 sp 0x14, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2fa : fetchRel tufRoleKeysMetCode 0x2FA = some (.load .lw a2 sp 0x10, 2) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_2fc : fetchRel tufRoleKeysMetCode 0x2FC = some (.auipc ra 0xFFFFD000, 4) :=
  (fetchRel_chunk rkm_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_300 : fetchRel tufRoleKeysMetCode 0x300 = some (.jalr ra ra 0xFFFFF83C, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_304 : fetchRel tufRoleKeysMetCode 0x304 = some (.aluImm .add a1 sp 0x18C, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_306 : fetchRel tufRoleKeysMetCode 0x306 = some (.aluImm .add a2 sp 0x12C, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_308 : fetchRel tufRoleKeysMetCode 0x308 = some (.aluImm .add a3 sp 0x15C, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_30a : fetchRel tufRoleKeysMetCode 0x30A = some (.alu .add a0 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_30c : fetchRel tufRoleKeysMetCode 0x30C = some (.auipc ra 0xFFFFD000, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_310 : fetchRel tufRoleKeysMetCode 0x310 = some (.jalr ra ra 0xFFFFFB4A, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_314 : fetchRel tufRoleKeysMetCode 0x314 = some (.aluImm .add a4 (19 : Fin 32) 0x518, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_318 : fetchRel tufRoleKeysMetCode 0x318 = some (.load .lw a3 sp 0x24, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_31a : fetchRel tufRoleKeysMetCode 0x31A = some (.load .lw a2 sp 0x20, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_31c : fetchRel tufRoleKeysMetCode 0x31C = some (.aluImm .add a5 x0 0x62, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_320 : fetchRel tufRoleKeysMetCode 0x320 = some (.aluImm .add (8 : Fin 32) x0 0x40, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_324 : fetchRel tufRoleKeysMetCode 0x324 = some (.branch .beq a0 x0 0xFFFFFD54, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_328 : fetchRel tufRoleKeysMetCode 0x328 = some (.load .lw a0 sp 0x18, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_32a : fetchRel tufRoleKeysMetCode 0x32A = some (.aluImm .add a1 x0 0x8, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_32c : fetchRel tufRoleKeysMetCode 0x32C = some (.branch .beq a0 a1 0x42, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_330 : fetchRel tufRoleKeysMetCode 0x330 = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_332 : fetchRel tufRoleKeysMetCode 0x332 = some (.store .sw a1 (22 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_336 : fetchRel tufRoleKeysMetCode 0x336 = some (.aluImm .add a0 a0 0x1, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_338 : fetchRel tufRoleKeysMetCode 0x338 = some (.load .lw a1 sp 0x1C, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_33a : fetchRel tufRoleKeysMetCode 0x33A = some (.aluImm .add a1 a1 0x4, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_33c : fetchRel tufRoleKeysMetCode 0x33C = some (.store .sw sp a1 0x1C, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_33e : fetchRel tufRoleKeysMetCode 0x33E = some (.aluImm .add (9 : Fin 32) sp 0x28, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_340 : fetchRel tufRoleKeysMetCode 0x340 = some (.jal x0 0xFFFFFD30, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_342 : fetchRel tufRoleKeysMetCode 0x342 = some (.load .lbu (26 : Fin 32) sp 0x49, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_346 : fetchRel tufRoleKeysMetCode 0x346 = some (.jal x0 0x28, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_348 : fetchRel tufRoleKeysMetCode 0x348 = some (.load .lbu (26 : Fin 32) sp 0x4C, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_34c : fetchRel tufRoleKeysMetCode 0x34C = some (.jal x0 0x22, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_34e : fetchRel tufRoleKeysMetCode 0x34E = some (.load .lbu (26 : Fin 32) sp 0x190, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_352 : fetchRel tufRoleKeysMetCode 0x352 = some (.jal x0 0x1C, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_354 : fetchRel tufRoleKeysMetCode 0x354 = some (.load .lw a0 (19 : Fin 32) 0x310, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_358 : fetchRel tufRoleKeysMetCode 0x358 = some (.load .lw a1 (19 : Fin 32) 0x314, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_35c : fetchRel tufRoleKeysMetCode 0x35C = some (.load .lw a2 sp 0x18, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_35e : fetchRel tufRoleKeysMetCode 0x35E = some (.alu .sltu a0 a2 a0, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_362 : fetchRel tufRoleKeysMetCode 0x362 = some (.aluImm .xor a0 a0 0xFFFFFFFF, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_366 : fetchRel tufRoleKeysMetCode 0x366 = some (.aluImm .sltu a1 a1 0x1, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_36a : fetchRel tufRoleKeysMetCode 0x36A = some (.alu .and (26 : Fin 32) a0 a1, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_36e : fetchRel tufRoleKeysMetCode 0x36E = some (.alu .sltu a0 (22 : Fin 32) (20 : Fin 32), 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_372 : fetchRel tufRoleKeysMetCode 0x372 = some (.alu .add a1 x0 (26 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_374 : fetchRel tufRoleKeysMetCode 0x374 = some (.aluImm .add a2 sp 0x180, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_376 : fetchRel tufRoleKeysMetCode 0x376 = some (.load .lw ra a2 0x6C, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_37a : fetchRel tufRoleKeysMetCode 0x37A = some (.load .lw (8 : Fin 32) a2 0x68, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_37c : fetchRel tufRoleKeysMetCode 0x37C = some (.load .lw (9 : Fin 32) a2 0x64, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_37e : fetchRel tufRoleKeysMetCode 0x37E = some (.load .lw (18 : Fin 32) a2 0x60, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_382 : fetchRel tufRoleKeysMetCode 0x382 = some (.load .lw (19 : Fin 32) a2 0x5C, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_386 : fetchRel tufRoleKeysMetCode 0x386 = some (.load .lw (20 : Fin 32) a2 0x58, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_38a : fetchRel tufRoleKeysMetCode 0x38A = some (.load .lw (21 : Fin 32) a2 0x54, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_38e : fetchRel tufRoleKeysMetCode 0x38E = some (.load .lw (22 : Fin 32) a2 0x50, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_392 : fetchRel tufRoleKeysMetCode 0x392 = some (.load .lw (23 : Fin 32) a2 0x4C, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_396 : fetchRel tufRoleKeysMetCode 0x396 = some (.load .lw (24 : Fin 32) a2 0x48, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_39a : fetchRel tufRoleKeysMetCode 0x39A = some (.load .lw (25 : Fin 32) a2 0x44, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_39e : fetchRel tufRoleKeysMetCode 0x39E = some (.load .lw (26 : Fin 32) a2 0x40, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_3a2 : fetchRel tufRoleKeysMetCode 0x3A2 = some (.load .lw (27 : Fin 32) a2 0x3C, 4) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_3a6 : fetchRel tufRoleKeysMetCode 0x3A6 = some (.aluImm .add sp sp 0x1F0, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_3a8 : fetchRel tufRoleKeysMetCode 0x3A8 = some (.jalr x0 ra 0x0, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_3aa : fetchRel tufRoleKeysMetCode 0x3AA = some (.alu .add (26 : Fin 32) x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkm_at_3ac : fetchRel tufRoleKeysMetCode 0x3AC = some (.jal x0 0xFFFFFFC2, 2) :=
  (fetchRel_chunk rkm_c3_ok (by decide) (.inr (by decide))).trans (by decide)

end C3.RV32
