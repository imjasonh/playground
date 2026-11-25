import C3BootProofs.Proof.FetchChunk
import C3BootProofs.Image.Bootloader
import C3BootProofs.Proofs.ReaderArray

/-! Fetch lemmas for `tuf::RoleKeys::read` (`tufRoleKeysReadCode`). -/

namespace C3.RV32

open C3.Image

/-- Where `tuf::RoleKeys::read` is in the image. -/
abbrev TRK : Word := BitVec.ofNat 32 tufRoleKeysReadAddress

set_option maxRecDepth 20000

/-- Bytes 0x0 to 0x104 of `tufRoleKeysReadCode`. -/
def rkr_c0 : List Nat :=
  [0x13, 0x01, 0x01, 0x81, 0x93, 0x07, 0x01, 0x78, 0x23, 0xa6, 0x17, 0x06,
    0xa0, 0xd7, 0xe4, 0xd3, 0x23, 0xa0, 0x27, 0x07, 0x23, 0xae, 0x37, 0x05,
    0x23, 0xac, 0x47, 0x05, 0x23, 0xaa, 0x57, 0x05, 0x23, 0xa8, 0x67, 0x05,
    0x23, 0xa6, 0x77, 0x05, 0x23, 0xa4, 0x87, 0x05, 0x23, 0xa2, 0x97, 0x05,
    0x23, 0xa0, 0xa7, 0x05, 0x23, 0xae, 0xb7, 0x03, 0x13, 0x01, 0x01, 0xd3,
    0x3a, 0x84, 0xb6, 0x84, 0x32, 0x89, 0xae, 0x89, 0xaa, 0x8d, 0xb7, 0x46,
    0xcc, 0x3f, 0x93, 0x86, 0x06, 0x75, 0x28, 0x08, 0x15, 0x47, 0x97, 0x00,
    0x00, 0x00, 0xe7, 0x80, 0x20, 0xd5, 0xe2, 0x45, 0xe3, 0x81, 0x05, 0x08,
    0x72, 0x46, 0x13, 0x05, 0xc1, 0x75, 0xa6, 0x86, 0x22, 0x87, 0x97, 0x00,
    0x00, 0x00, 0xe7, 0x80, 0xa0, 0xd3, 0x83, 0x2b, 0xc1, 0x75, 0xe3, 0x87,
    0x0b, 0x06, 0x03, 0x2b, 0x01, 0x76, 0xb7, 0x46, 0xcc, 0x3f, 0x93, 0x86,
    0x56, 0x75, 0x13, 0x05, 0xc1, 0x75, 0x25, 0x47, 0xde, 0x85, 0x5a, 0x86,
    0x97, 0x00, 0x00, 0x00, 0xe7, 0x80, 0x40, 0xd1, 0x83, 0x25, 0xc1, 0x75,
    0xe3, 0x84, 0x05, 0x04, 0x03, 0x26, 0x01, 0x76, 0x28, 0x08, 0x97, 0x10,
    0x00, 0x00, 0xe7, 0x80, 0x00, 0x8c, 0x03, 0x45, 0x81, 0x01, 0x09, 0xc5,
    0x03, 0x45, 0x91, 0x01, 0x6f, 0x00, 0x10, 0x03, 0x02, 0x5c, 0x12, 0x5a,
    0x33, 0x65, 0x4c, 0x01, 0xe3, 0x06, 0x05, 0x06, 0xb7, 0x46, 0xcc, 0x3f,
    0x93, 0x86, 0x26, 0x76, 0x28, 0x08, 0x11, 0x47, 0xce, 0x85, 0x4a, 0x86,
    0x97, 0x00, 0x00, 0x00, 0xe7, 0x80, 0xc0, 0xcc, 0xe2, 0x4a, 0x63, 0x8e,
    0x0a, 0x7e, 0x72, 0x49, 0x28, 0x08, 0xd6, 0x85, 0x4a, 0x86, 0x97, 0x00,
    0x00, 0x00, 0xe7, 0x80, 0x80, 0xec, 0x62, 0x45, 0x63, 0x03, 0x05, 0x7e,
    0x13, 0x04, 0xc1, 0x55, 0xa1, 0x44, 0x89, 0xcc]
theorem rkr_c0_ok : rkr_c0 <+: List.drop 0 tufRoleKeysReadCode := by decide

/-- Bytes 0x100 to 0x204 of `tufRoleKeysReadCode`. -/
def rkr_c1 : List Nat :=
  [0xa1, 0x44, 0x89, 0xcc, 0x13, 0x06, 0x00, 0x04, 0x22, 0x85, 0x81, 0x45,
    0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0x60, 0xd7, 0x13, 0x04, 0x04, 0x04,
    0xfd, 0x14, 0xed, 0xf4, 0x13, 0x05, 0xc1, 0x75, 0xa1, 0x45, 0x7d, 0x56,
    0x99, 0xc5, 0x23, 0x00, 0xc5, 0x00, 0x13, 0x05, 0x25, 0x06, 0xfd, 0x15,
    0xfd, 0xf9, 0x23, 0x24, 0x81, 0x33, 0x23, 0x26, 0x41, 0x33, 0x23, 0x28,
    0x01, 0x54, 0x93, 0x09, 0x01, 0x33, 0x93, 0x05, 0xc1, 0x55, 0x13, 0x06,
    0x00, 0x20, 0x4e, 0x85, 0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0xe0, 0xd9,
    0x13, 0x0a, 0x01, 0x53, 0x13, 0x06, 0x00, 0x02, 0x52, 0x85, 0x81, 0x45,
    0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0x20, 0xd2, 0x28, 0x08, 0x93, 0x05,
    0xc1, 0x75, 0x13, 0x06, 0x00, 0x31, 0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80,
    0x80, 0xd7, 0xb7, 0x46, 0xcc, 0x3f, 0x93, 0x86, 0x66, 0x77, 0x13, 0x05,
    0xc1, 0x55, 0x19, 0x47, 0xde, 0x85, 0x5a, 0x86, 0x97, 0x00, 0x00, 0x00,
    0xe7, 0x80, 0x80, 0xc1, 0x83, 0x25, 0xc1, 0x55, 0x63, 0x82, 0x05, 0x7a,
    0x03, 0x26, 0x01, 0x56, 0x13, 0x05, 0xc1, 0x75, 0x97, 0x00, 0x00, 0x00,
    0xe7, 0x80, 0x80, 0xb5, 0x83, 0x24, 0xc1, 0x75, 0x03, 0x44, 0x01, 0x76,
    0x63, 0x87, 0x04, 0x78, 0x93, 0x05, 0x11, 0x76, 0x13, 0x05, 0xf1, 0x7f,
    0x13, 0x05, 0x25, 0x27, 0x1d, 0x46, 0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80,
    0x40, 0xd2, 0x13, 0x0c, 0xf1, 0x7f, 0x13, 0x0c, 0xdc, 0x26, 0x23, 0x20,
    0x9c, 0x00, 0x23, 0x02, 0x8c, 0x00, 0x05, 0x4d, 0x93, 0x0c, 0x91, 0x01,
    0xa5, 0x4b, 0x13, 0x05, 0xc1, 0x75, 0x93, 0x05, 0xf1, 0x7f, 0x93, 0x85,
    0xd5, 0x26, 0x97, 0x00, 0x00, 0x00, 0xe7, 0x80, 0x40, 0xb5, 0x03, 0x45,
    0xc1, 0x75, 0x63, 0x18, 0x05, 0x74, 0x83, 0x25]
theorem rkr_c1_ok : rkr_c1 <+: List.drop 256 tufRoleKeysReadCode := by decide

/-- Bytes 0x200 to 0x304 of `tufRoleKeysReadCode`. -/
def rkr_c2 : List Nat :=
  [0x05, 0x74, 0x83, 0x25, 0x01, 0x76, 0x63, 0x87, 0x05, 0x74, 0x03, 0x26,
    0x41, 0x76, 0x13, 0x05, 0xc1, 0x75, 0x97, 0x00, 0x00, 0x00, 0xe7, 0x80,
    0xe0, 0xbc, 0x03, 0x24, 0xc1, 0x75, 0x63, 0x03, 0x04, 0x6c, 0x63, 0x07,
    0x7d, 0x71, 0x83, 0x24, 0x01, 0x76, 0x13, 0x05, 0x10, 0x04, 0x63, 0xf1,
    0xa4, 0x70, 0x4e, 0x85, 0xa6, 0x85, 0x22, 0x86, 0xa6, 0x86, 0x97, 0x40,
    0x00, 0x00, 0xe7, 0x80, 0x20, 0x69, 0x23, 0x20, 0x9a, 0x00, 0x13, 0x05,
    0xc1, 0x75, 0xd6, 0x85, 0x4a, 0x86, 0xa2, 0x86, 0x26, 0x87, 0x97, 0x00,
    0x00, 0x00, 0xe7, 0x80, 0xe0, 0xcb, 0x03, 0x45, 0xc1, 0x75, 0x63, 0x18,
    0x05, 0x6e, 0x03, 0x24, 0x01, 0x76, 0x13, 0x0b, 0xf0, 0x0f, 0x63, 0x05,
    0x04, 0x48, 0x83, 0x24, 0x41, 0x76, 0x13, 0x05, 0xc1, 0x75, 0x1d, 0x47,
    0xa2, 0x85, 0x26, 0x86, 0xb7, 0x56, 0xcc, 0x3f, 0x93, 0x86, 0x16, 0x87,
    0x97, 0x00, 0x00, 0x00, 0xe7, 0x80, 0x00, 0xb2, 0x83, 0x25, 0xc1, 0x75,
    0x63, 0x82, 0x05, 0x46, 0x03, 0x26, 0x01, 0x76, 0x13, 0x05, 0xf1, 0x7f,
    0x13, 0x05, 0x15, 0x28, 0x97, 0x00, 0x00, 0x00, 0xe7, 0x80, 0x00, 0xb4,
    0x83, 0x2b, 0x4c, 0x01, 0x63, 0x83, 0x0b, 0x44, 0x03, 0x25, 0x8c, 0x01,
    0x2a, 0xca, 0x13, 0x05, 0xc1, 0x75, 0x19, 0x47, 0xa2, 0x85, 0x26, 0x86,
    0xb7, 0x56, 0xcc, 0x3f, 0x93, 0x86, 0x86, 0x87, 0x97, 0x00, 0x00, 0x00,
    0xe7, 0x80, 0xc0, 0xad, 0x83, 0x25, 0xc1, 0x75, 0x63, 0x8f, 0x05, 0x40,
    0x03, 0x26, 0x01, 0x76, 0x13, 0x05, 0xf1, 0x7f, 0x13, 0x05, 0x15, 0x28,
    0x97, 0x00, 0x00, 0x00, 0xe7, 0x80, 0xc0, 0xaf, 0x03, 0x25, 0x4c, 0x01,
    0x63, 0x01, 0x05, 0x40, 0x2a, 0xc6, 0x13, 0x0c, 0xf1, 0x7f, 0x13, 0x0c,
    0xdc, 0x26, 0x03, 0x25, 0x8c, 0x01, 0x2a, 0xc8]
theorem rkr_c2_ok : rkr_c2 <+: List.drop 512 tufRoleKeysReadCode := by decide

/-- Bytes 0x300 to 0x404 of `tufRoleKeysReadCode`. -/
def rkr_c3 : List Nat :=
  [0x8c, 0x01, 0x2a, 0xc8, 0x13, 0x05, 0xc1, 0x75, 0x19, 0x47, 0xa2, 0x85,
    0x26, 0x86, 0xb7, 0x56, 0xcc, 0x3f, 0x93, 0x86, 0xe6, 0x87, 0x97, 0x00,
    0x00, 0x00, 0xe7, 0x80, 0xe0, 0xa8, 0x83, 0x25, 0xc1, 0x75, 0x63, 0x84,
    0x05, 0x3c, 0x03, 0x26, 0x01, 0x76, 0x13, 0x05, 0xf1, 0x7f, 0x13, 0x05,
    0x15, 0x28, 0x19, 0x47, 0xb7, 0x56, 0xcc, 0x3f, 0x93, 0x86, 0x46, 0x88,
    0x97, 0x00, 0x00, 0x00, 0xe7, 0x80, 0x80, 0xa6, 0x83, 0x25, 0x4c, 0x01,
    0x63, 0x81, 0x05, 0x3a, 0xe2, 0x84, 0x90, 0x4c, 0x13, 0x05, 0xf1, 0x7f,
    0x13, 0x05, 0x95, 0x27, 0x97, 0x00, 0x00, 0x00, 0xe7, 0x80, 0x80, 0xa8,
    0xc0, 0x44, 0x63, 0x04, 0x04, 0x38, 0x83, 0x24, 0x0c, 0x01, 0x13, 0x05,
    0xc1, 0x75, 0x13, 0x06, 0x00, 0x08, 0x81, 0x45, 0x97, 0xc0, 0x00, 0x00,
    0xe7, 0x80, 0xe0, 0xb0, 0x4d, 0x45, 0xc2, 0x46, 0x63, 0x94, 0xa6, 0x1c,
    0x32, 0x46, 0x03, 0x45, 0x06, 0x00, 0x93, 0x05, 0xb5, 0xf9, 0x13, 0x05,
    0xf0, 0x0f, 0x63, 0x9b, 0x05, 0x28, 0x83, 0x45, 0x16, 0x00, 0x93, 0x85,
    0xd5, 0xf9, 0x13, 0x0c, 0xf1, 0x7f, 0x13, 0x0c, 0xdc, 0x26, 0x63, 0x95,
    0x05, 0x28, 0x83, 0x45, 0x26, 0x00, 0x93, 0x85, 0xc5, 0xf9, 0x63, 0x9f,
    0x05, 0x26, 0x83, 0x45, 0x36, 0x00, 0x93, 0x85, 0xd5, 0xf8, 0x63, 0x95,
    0x05, 0x26, 0xb2, 0x45, 0x83, 0xc5, 0x45, 0x00, 0x93, 0x85, 0xf5, 0xf9,
    0x63, 0x9e, 0x05, 0x24, 0xb2, 0x45, 0x83, 0xc5, 0x55, 0x00, 0x93, 0x85,
    0x35, 0xfd, 0x63, 0x97, 0x05, 0x24, 0xb2, 0x45, 0x83, 0xc5, 0x65, 0x00,
    0x93, 0x85, 0xd5, 0xf8, 0x63, 0x90, 0x05, 0x24, 0xb2, 0x45, 0x83, 0xc5,
    0x75, 0x00, 0x93, 0x85, 0x85, 0xf9, 0x63, 0x99, 0x05, 0x22, 0xb2, 0x45,
    0x83, 0xc5, 0x85, 0x00, 0x93, 0x85, 0xf5, 0xf9]
theorem rkr_c3_ok : rkr_c3 <+: List.drop 768 tufRoleKeysReadCode := by decide

/-- Bytes 0x400 to 0x504 of `tufRoleKeysReadCode`. -/
def rkr_c4 : List Nat :=
  [0x93, 0x85, 0xf5, 0xf9, 0x63, 0x92, 0x05, 0x22, 0xb2, 0x45, 0x83, 0xc5,
    0x95, 0x00, 0x93, 0x85, 0xe5, 0xfc, 0x63, 0x9b, 0x05, 0x20, 0xb2, 0x45,
    0x83, 0xc5, 0xa5, 0x00, 0x93, 0x85, 0x35, 0xfd, 0x63, 0x94, 0x05, 0x20,
    0xb2, 0x45, 0x83, 0xc5, 0xb5, 0x00, 0x93, 0x85, 0x25, 0xf9, 0x63, 0x9d,
    0x05, 0x1e, 0xb2, 0x45, 0x83, 0xc5, 0xc5, 0x00, 0x93, 0x85, 0x75, 0xf9,
    0x63, 0x96, 0x05, 0x1e, 0xb2, 0x45, 0x83, 0xc5, 0xd5, 0x00, 0x93, 0x85,
    0xd5, 0xf8, 0x63, 0x9f, 0x05, 0x1c, 0xb2, 0x45, 0x83, 0xc5, 0xe5, 0x00,
    0x93, 0x85, 0xc5, 0xf8, 0x63, 0x98, 0x05, 0x1c, 0xb2, 0x45, 0x83, 0xc5,
    0xf5, 0x00, 0x93, 0x85, 0x05, 0xf9, 0x63, 0x91, 0x05, 0x1c, 0xb2, 0x45,
    0x83, 0xc5, 0x05, 0x01, 0x13, 0x86, 0xd5, 0xfc, 0x63, 0x01, 0x06, 0x1c,
    0x93, 0x85, 0xe5, 0xfc, 0x63, 0x96, 0x05, 0x1a, 0xb2, 0x45, 0x83, 0xc5,
    0x15, 0x01, 0x93, 0x85, 0xb5, 0xfc, 0x63, 0x9f, 0x05, 0x18, 0xb2, 0x45,
    0x83, 0xc5, 0x25, 0x01, 0x93, 0x85, 0xa5, 0xfc, 0x63, 0x98, 0x05, 0x18,
    0xcd, 0x45, 0x52, 0x46, 0x63, 0x0e, 0xb6, 0x26, 0x95, 0x45, 0x52, 0x46,
    0x63, 0x10, 0xb6, 0x18, 0x83, 0xc5, 0x0b, 0x00, 0x93, 0x85, 0xb5, 0xf9,
    0x63, 0x9a, 0x05, 0x16, 0x83, 0xc5, 0x1b, 0x00, 0x93, 0x85, 0xd5, 0xf9,
    0x63, 0x94, 0x05, 0x16, 0x83, 0xc5, 0x2b, 0x00, 0x93, 0x85, 0xc5, 0xf9,
    0x63, 0x9e, 0x05, 0x14, 0x83, 0xc5, 0x3b, 0x00, 0x93, 0x85, 0xd5, 0xf8,
    0x63, 0x98, 0x05, 0x14, 0x83, 0xc5, 0x4b, 0x00, 0x93, 0x85, 0xf5, 0xf9,
    0x13, 0x0c, 0xf1, 0x7f, 0x13, 0x0c, 0xdc, 0x26, 0xa5, 0x4b, 0x63, 0x92,
    0x05, 0x14, 0x13, 0x06, 0xc1, 0x75, 0x22, 0x85, 0xa6, 0x85, 0x97, 0x00,
    0x00, 0x00, 0xe7, 0x80, 0xe0, 0x4f, 0x63, 0x04]
theorem rkr_c4_ok : rkr_c4 <+: List.drop 1024 tufRoleKeysReadCode := by decide

/-- Bytes 0x500 to 0x604 of `tufRoleKeysReadCode`. -/
def rkr_c5 : List Nat :=
  [0xe0, 0x4f, 0x63, 0x04, 0x05, 0x1e, 0x2a, 0x84, 0xae, 0x84, 0x69, 0x45,
    0x63, 0xef, 0xa5, 0x1c, 0x69, 0x46, 0x22, 0x85, 0xb7, 0x45, 0xcc, 0x3f,
    0x93, 0x85, 0xc5, 0x69, 0x97, 0xe0, 0xff, 0xff, 0xe7, 0x80, 0x80, 0x58,
    0x63, 0x03, 0x05, 0x1c, 0x13, 0x85, 0x54, 0xfa, 0x63, 0x1f, 0x05, 0x1a,
    0x93, 0x05, 0xa4, 0x01, 0x13, 0x05, 0xc1, 0x55, 0x13, 0x06, 0x10, 0x04,
    0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0xe0, 0x9a, 0x01, 0x45, 0xcd, 0xa0,
    0x13, 0x05, 0xf0, 0x0f, 0x9d, 0x45, 0x52, 0x46, 0x63, 0x1c, 0xb6, 0x0c,
    0x63, 0x9a, 0xb6, 0x0c, 0x83, 0xc5, 0x0b, 0x00, 0x93, 0x85, 0xb5, 0xf9,
    0xe1, 0xe5, 0x83, 0xc5, 0x1b, 0x00, 0x93, 0x85, 0xc5, 0xf9, 0xdd, 0xed,
    0x83, 0xc5, 0x2b, 0x00, 0x93, 0x85, 0xe5, 0xfc, 0xd5, 0xe9, 0x83, 0xc5,
    0x3b, 0x00, 0x93, 0x85, 0xb5, 0xfc, 0xcd, 0xe5, 0x83, 0xc5, 0x4b, 0x00,
    0x93, 0x85, 0xb5, 0xfc, 0xc5, 0xe1, 0x83, 0xc5, 0x5b, 0x00, 0x93, 0x85,
    0xf5, 0xfc, 0xd9, 0xe9, 0x83, 0xc5, 0x6b, 0x00, 0x93, 0x85, 0x75, 0xfc,
    0xd1, 0xe5, 0xb2, 0x45, 0x83, 0xc5, 0x05, 0x00, 0x93, 0x85, 0xb5, 0xf9,
    0xc1, 0xe1, 0xb2, 0x45, 0x83, 0xc5, 0x15, 0x00, 0x93, 0x85, 0xc5, 0xf9,
    0xb5, 0xe9, 0xb2, 0x45, 0x83, 0xc5, 0x25, 0x00, 0x93, 0x85, 0xe5, 0xfc,
    0xa5, 0xe5, 0xb2, 0x45, 0x83, 0xc5, 0x35, 0x00, 0x93, 0x85, 0xb5, 0xfc,
    0xb1, 0xed, 0xb2, 0x45, 0x83, 0xc5, 0x45, 0x00, 0x93, 0x85, 0xb5, 0xfc,
    0xa1, 0xe9, 0xb2, 0x45, 0x83, 0xc5, 0x55, 0x00, 0x93, 0x85, 0xf5, 0xfc,
    0xb1, 0xe1, 0xb2, 0x45, 0x83, 0xc5, 0x65, 0x00, 0x93, 0x85, 0x75, 0xfc,
    0x13, 0x0c, 0xf1, 0x7f, 0x13, 0x0c, 0xdc, 0x26, 0xa5, 0x4b, 0x85, 0xed,
    0x13, 0x06, 0xc1, 0x75, 0x22, 0x85, 0xa6, 0x85]
theorem rkr_c5_ok : rkr_c5 <+: List.drop 1280 tufRoleKeysReadCode := by decide

/-- Bytes 0x600 to 0x704 of `tufRoleKeysReadCode`. -/
def rkr_c6 : List Nat :=
  [0x22, 0x85, 0xa6, 0x85, 0x97, 0x00, 0x00, 0x00, 0xe7, 0x80, 0x60, 0x84,
    0x79, 0xcd, 0x81, 0x15, 0xe9, 0xed, 0xaa, 0x86, 0x13, 0x05, 0xc1, 0x55,
    0x13, 0x06, 0x00, 0x02, 0xb6, 0x85, 0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80,
    0xc0, 0x8c, 0x09, 0x45, 0x13, 0x0c, 0xf1, 0x7f, 0x13, 0x0c, 0xdc, 0x26,
    0xa5, 0x4b, 0x2a, 0x8b, 0xc1, 0xa0, 0xb2, 0x45, 0x83, 0xc5, 0x15, 0x01,
    0x93, 0x85, 0x85, 0xfc, 0xe5, 0xf5, 0xb2, 0x45, 0x83, 0xc5, 0x25, 0x01,
    0x93, 0x85, 0xc5, 0xfc, 0xf1, 0xfd, 0xcd, 0x45, 0x52, 0x46, 0x63, 0x05,
    0xb6, 0x1a, 0x95, 0x45, 0x52, 0x46, 0xe3, 0x17, 0xb6, 0xfc, 0x83, 0xc5,
    0x0b, 0x00, 0x93, 0x85, 0xb5, 0xf9, 0xe9, 0xf1, 0x83, 0xc5, 0x1b, 0x00,
    0x93, 0x85, 0xd5, 0xf9, 0xc5, 0xfd, 0x83, 0xc5, 0x2b, 0x00, 0x93, 0x85,
    0xc5, 0xf9, 0xdd, 0xf5, 0x83, 0xc5, 0x3b, 0x00, 0x93, 0x85, 0xd5, 0xf8,
    0xd5, 0xf1, 0x83, 0xc5, 0x4b, 0x00, 0x93, 0x85, 0xf5, 0xf9, 0x13, 0x0c,
    0xf1, 0x7f, 0x13, 0x0c, 0xdc, 0x26, 0xa5, 0x4b, 0xc9, 0xfd, 0x13, 0x06,
    0xc1, 0x75, 0x22, 0x85, 0xa6, 0x85, 0x97, 0x00, 0x00, 0x00, 0xe7, 0x80,
    0x60, 0x35, 0x21, 0xc1, 0x2a, 0x84, 0xae, 0x84, 0x5d, 0x45, 0x63, 0xec,
    0xa5, 0x02, 0x5d, 0x46, 0x22, 0x85, 0xb7, 0x55, 0xcc, 0x3f, 0x93, 0x85,
    0xa5, 0x88, 0x97, 0xe0, 0xff, 0xff, 0xe7, 0x80, 0x20, 0x3e, 0x05, 0xc1,
    0x13, 0x85, 0x84, 0xf8, 0x09, 0xed, 0x93, 0x05, 0x74, 0x01, 0x13, 0x05,
    0xc1, 0x55, 0x13, 0x06, 0x10, 0x06, 0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80,
    0xc0, 0x80, 0x05, 0x45, 0x81, 0xb7, 0x13, 0x0c, 0xf1, 0x7f, 0x13, 0x0c,
    0xdc, 0x26, 0xa5, 0x4b, 0xa3, 0x8f, 0x6c, 0xff, 0x93, 0x05, 0xc1, 0x55,
    0x13, 0x06, 0x10, 0x06, 0x66, 0x85, 0x97, 0xb0]
theorem rkr_c6_ok : rkr_c6 <+: List.drop 1536 tufRoleKeysReadCode := by decide

/-- Bytes 0x700 to 0x804 of `tufRoleKeysReadCode`. -/
def rkr_c7 : List Nat :=
  [0x66, 0x85, 0x97, 0xb0, 0x00, 0x00, 0xe7, 0x80, 0x80, 0x7e, 0x23, 0x28,
    0xa1, 0x55, 0x11, 0x0a, 0x93, 0x8c, 0x2c, 0x06, 0x05, 0x0d, 0x93, 0x89,
    0x09, 0x04, 0xf1, 0xb4, 0x83, 0xc5, 0x0b, 0x00, 0x93, 0x85, 0xb5, 0xf9,
    0x91, 0xf1, 0x83, 0xc5, 0x1b, 0x00, 0x93, 0x85, 0xd5, 0xf9, 0xe3, 0x9d,
    0x05, 0xee, 0x83, 0xc5, 0x2b, 0x00, 0x93, 0x85, 0xc5, 0xf9, 0xe3, 0x97,
    0x05, 0xee, 0x83, 0xc5, 0x3b, 0x00, 0x93, 0x85, 0xd5, 0xf8, 0xe3, 0x91,
    0x05, 0xee, 0x83, 0xc5, 0x4b, 0x00, 0x93, 0x85, 0xf5, 0xf9, 0xe3, 0x9b,
    0x05, 0xec, 0x83, 0xc5, 0x5b, 0x00, 0x93, 0x85, 0x35, 0xfd, 0xe3, 0x95,
    0x05, 0xec, 0x83, 0xc5, 0x6b, 0x00, 0x93, 0x85, 0xd5, 0xf8, 0xe3, 0x9f,
    0x05, 0xea, 0x83, 0xc5, 0x7b, 0x00, 0x93, 0x85, 0x85, 0xf9, 0xe3, 0x99,
    0x05, 0xea, 0x83, 0xc5, 0x8b, 0x00, 0x93, 0x85, 0xf5, 0xf9, 0xe3, 0x93,
    0x05, 0xea, 0x83, 0xc5, 0x9b, 0x00, 0x93, 0x85, 0xe5, 0xfc, 0xe3, 0x9d,
    0x05, 0xe8, 0x83, 0xc5, 0xab, 0x00, 0x93, 0x85, 0x35, 0xfd, 0xe3, 0x97,
    0x05, 0xe8, 0x83, 0xc5, 0xbb, 0x00, 0x93, 0x85, 0x25, 0xf9, 0xe3, 0x91,
    0x05, 0xe8, 0x83, 0xc5, 0xcb, 0x00, 0x93, 0x85, 0x75, 0xf9, 0xe3, 0x9b,
    0x05, 0xe6, 0x83, 0xc5, 0xdb, 0x00, 0x93, 0x85, 0xd5, 0xf8, 0xe3, 0x95,
    0x05, 0xe6, 0x83, 0xc5, 0xeb, 0x00, 0x93, 0x85, 0xc5, 0xf8, 0xe3, 0x9f,
    0x05, 0xe4, 0x83, 0xc5, 0xfb, 0x00, 0x93, 0x85, 0x05, 0xf9, 0xe3, 0x99,
    0x05, 0xe4, 0x83, 0xc5, 0x0b, 0x01, 0x93, 0x85, 0xe5, 0xfc, 0xe3, 0x93,
    0x05, 0xe4, 0x83, 0xc5, 0x1b, 0x01, 0x93, 0x85, 0xb5, 0xfc, 0xe3, 0x9d,
    0x05, 0xe2, 0x83, 0xc5, 0x2b, 0x01, 0x93, 0x85, 0xa5, 0xfc, 0xed, 0xb1,
    0x83, 0xc5, 0x0b, 0x00, 0x93, 0x85, 0xb5, 0xf9]
theorem rkr_c7_ok : rkr_c7 <+: List.drop 1792 tufRoleKeysReadCode := by decide

/-- Bytes 0x800 to 0x904 of `tufRoleKeysReadCode`. -/
def rkr_c8 : List Nat :=
  [0x93, 0x85, 0xb5, 0xf9, 0xe3, 0x92, 0x05, 0xe2, 0x83, 0xc5, 0x1b, 0x00,
    0x93, 0x85, 0xd5, 0xf9, 0xe3, 0x9c, 0x05, 0xe0, 0x83, 0xc5, 0x2b, 0x00,
    0x93, 0x85, 0xc5, 0xf9, 0xe3, 0x96, 0x05, 0xe0, 0x83, 0xc5, 0x3b, 0x00,
    0x93, 0x85, 0xd5, 0xf8, 0xe3, 0x90, 0x05, 0xe0, 0x83, 0xc5, 0x4b, 0x00,
    0x93, 0x85, 0xf5, 0xf9, 0xe3, 0x9a, 0x05, 0xde, 0x83, 0xc5, 0x5b, 0x00,
    0x93, 0x85, 0x35, 0xfd, 0xe3, 0x94, 0x05, 0xde, 0x83, 0xc5, 0x6b, 0x00,
    0x93, 0x85, 0xd5, 0xf8, 0xe3, 0x9e, 0x05, 0xdc, 0x83, 0xc5, 0x7b, 0x00,
    0x93, 0x85, 0x85, 0xf9, 0xe3, 0x98, 0x05, 0xdc, 0x83, 0xc5, 0x8b, 0x00,
    0x93, 0x85, 0xf5, 0xf9, 0xe3, 0x92, 0x05, 0xdc, 0x83, 0xc5, 0x9b, 0x00,
    0x93, 0x85, 0xe5, 0xfc, 0xe3, 0x9c, 0x05, 0xda, 0x83, 0xc5, 0xab, 0x00,
    0x93, 0x85, 0x35, 0xfd, 0xe3, 0x96, 0x05, 0xda, 0x83, 0xc5, 0xbb, 0x00,
    0x93, 0x85, 0x25, 0xf9, 0xe3, 0x90, 0x05, 0xda, 0x83, 0xc5, 0xcb, 0x00,
    0x93, 0x85, 0x75, 0xf9, 0xe3, 0x9a, 0x05, 0xd8, 0x83, 0xc5, 0xdb, 0x00,
    0x93, 0x85, 0xd5, 0xf8, 0xe3, 0x94, 0x05, 0xd8, 0x83, 0xc5, 0xeb, 0x00,
    0x93, 0x85, 0xc5, 0xf8, 0xe3, 0x9e, 0x05, 0xd6, 0x83, 0xc5, 0xfb, 0x00,
    0x93, 0x85, 0x05, 0xf9, 0xe3, 0x98, 0x05, 0xd6, 0x83, 0xc5, 0x0b, 0x01,
    0x93, 0x85, 0xd5, 0xfc, 0xe3, 0x92, 0x05, 0xd6, 0x83, 0xc5, 0x1b, 0x01,
    0x93, 0x85, 0x85, 0xfc, 0xe3, 0x9c, 0x05, 0xd4, 0x83, 0xc5, 0x2b, 0x01,
    0x93, 0x85, 0xc5, 0xfc, 0x4d, 0xbb, 0x03, 0x45, 0xc1, 0x01, 0x19, 0xa0,
    0x03, 0x45, 0x01, 0x76, 0xf9, 0x55, 0x23, 0x80, 0xbd, 0x00, 0xa3, 0x80,
    0xad, 0x00, 0x13, 0x01, 0x01, 0x2d, 0x13, 0x05, 0x01, 0x78, 0x83, 0x20,
    0xc5, 0x06, 0x20, 0x55, 0x64, 0x51, 0x03, 0x29]
theorem rkr_c8_ok : rkr_c8 <+: List.drop 2048 tufRoleKeysReadCode := by decide

/-- Bytes 0x900 to 0x966 of `tufRoleKeysReadCode`. -/
def rkr_c9 : List Nat :=
  [0x64, 0x51, 0x03, 0x29, 0x05, 0x06, 0x83, 0x29, 0xc5, 0x05, 0x03, 0x2a,
    0x85, 0x05, 0x83, 0x2a, 0x45, 0x05, 0x03, 0x2b, 0x05, 0x05, 0x83, 0x2b,
    0xc5, 0x04, 0x03, 0x2c, 0x85, 0x04, 0x83, 0x2c, 0x45, 0x04, 0x03, 0x2d,
    0x05, 0x04, 0x83, 0x2d, 0xc5, 0x03, 0x13, 0x01, 0x01, 0x7f, 0x82, 0x80,
    0x09, 0x65, 0x13, 0x05, 0xe5, 0x1f, 0x23, 0x90, 0xad, 0x00, 0x65, 0xbf,
    0x03, 0x45, 0x01, 0x56, 0x65, 0xb7, 0x79, 0x55, 0x23, 0x80, 0xad, 0x00,
    0xa3, 0x80, 0x8d, 0x00, 0x5d, 0xb7, 0x03, 0x45, 0xd1, 0x75, 0x59, 0xbf,
    0x2c, 0x08, 0x13, 0x06, 0x00, 0x54, 0x6e, 0x85, 0x97, 0xb0, 0x00, 0x00,
    0xe7, 0x80, 0xe0, 0x58, 0x79, 0xb7]
theorem rkr_c9_ok : rkr_c9 <+: List.drop 2304 tufRoleKeysReadCode := by decide

theorem rkr_at_0 : fetchRel tufRoleKeysReadCode 0x0 = some (.aluImm .add sp sp 0xFFFFF810, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4 : fetchRel tufRoleKeysReadCode 0x4 = some (.aluImm .add a5 sp 0x780, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8 : fetchRel tufRoleKeysReadCode 0x8 = some (.store .sw a5 ra 0x6C, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_c : fetchRel tufRoleKeysReadCode 0xC = some (.store .sw a5 (8 : Fin 32) 0x68, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_e : fetchRel tufRoleKeysReadCode 0xE = some (.store .sw a5 (9 : Fin 32) 0x64, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_10 : fetchRel tufRoleKeysReadCode 0x10 = some (.store .sw a5 (18 : Fin 32) 0x60, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_14 : fetchRel tufRoleKeysReadCode 0x14 = some (.store .sw a5 (19 : Fin 32) 0x5C, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_18 : fetchRel tufRoleKeysReadCode 0x18 = some (.store .sw a5 (20 : Fin 32) 0x58, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1c : fetchRel tufRoleKeysReadCode 0x1C = some (.store .sw a5 (21 : Fin 32) 0x54, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_20 : fetchRel tufRoleKeysReadCode 0x20 = some (.store .sw a5 (22 : Fin 32) 0x50, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_24 : fetchRel tufRoleKeysReadCode 0x24 = some (.store .sw a5 (23 : Fin 32) 0x4C, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_28 : fetchRel tufRoleKeysReadCode 0x28 = some (.store .sw a5 (24 : Fin 32) 0x48, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2c : fetchRel tufRoleKeysReadCode 0x2C = some (.store .sw a5 (25 : Fin 32) 0x44, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_30 : fetchRel tufRoleKeysReadCode 0x30 = some (.store .sw a5 (26 : Fin 32) 0x40, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_34 : fetchRel tufRoleKeysReadCode 0x34 = some (.store .sw a5 (27 : Fin 32) 0x3C, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_38 : fetchRel tufRoleKeysReadCode 0x38 = some (.aluImm .add sp sp 0xFFFFFD30, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3c : fetchRel tufRoleKeysReadCode 0x3C = some (.alu .add (8 : Fin 32) x0 a4, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3e : fetchRel tufRoleKeysReadCode 0x3E = some (.alu .add (9 : Fin 32) x0 a3, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_40 : fetchRel tufRoleKeysReadCode 0x40 = some (.alu .add (18 : Fin 32) x0 a2, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_42 : fetchRel tufRoleKeysReadCode 0x42 = some (.alu .add (19 : Fin 32) x0 a1, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_44 : fetchRel tufRoleKeysReadCode 0x44 = some (.alu .add (27 : Fin 32) x0 a0, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_46 : fetchRel tufRoleKeysReadCode 0x46 = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4a : fetchRel tufRoleKeysReadCode 0x4A = some (.aluImm .add a3 a3 0x750, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4e : fetchRel tufRoleKeysReadCode 0x4E = some (.aluImm .add a0 sp 0x18, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_50 : fetchRel tufRoleKeysReadCode 0x50 = some (.aluImm .add a4 x0 0x5, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_52 : fetchRel tufRoleKeysReadCode 0x52 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_56 : fetchRel tufRoleKeysReadCode 0x56 = some (.jalr ra ra 0xFFFFFD52, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5a : fetchRel tufRoleKeysReadCode 0x5A = some (.load .lw a1 sp 0x18, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5c : fetchRel tufRoleKeysReadCode 0x5C = some (.branch .beq a1 x0 0x882, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_60 : fetchRel tufRoleKeysReadCode 0x60 = some (.load .lw a2 sp 0x1C, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_62 : fetchRel tufRoleKeysReadCode 0x62 = some (.aluImm .add a0 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_66 : fetchRel tufRoleKeysReadCode 0x66 = some (.alu .add a3 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_68 : fetchRel tufRoleKeysReadCode 0x68 = some (.alu .add a4 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6a : fetchRel tufRoleKeysReadCode 0x6A = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6e : fetchRel tufRoleKeysReadCode 0x6E = some (.jalr ra ra 0xFFFFFD3A, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_72 : fetchRel tufRoleKeysReadCode 0x72 = some (.load .lw (23 : Fin 32) sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_76 : fetchRel tufRoleKeysReadCode 0x76 = some (.branch .beq (23 : Fin 32) x0 0x86E, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7a : fetchRel tufRoleKeysReadCode 0x7A = some (.load .lw (22 : Fin 32) sp 0x760, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7e : fetchRel tufRoleKeysReadCode 0x7E = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_82 : fetchRel tufRoleKeysReadCode 0x82 = some (.aluImm .add a3 a3 0x755, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_86 : fetchRel tufRoleKeysReadCode 0x86 = some (.aluImm .add a0 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8a : fetchRel tufRoleKeysReadCode 0x8A = some (.aluImm .add a4 x0 0x9, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8c : fetchRel tufRoleKeysReadCode 0x8C = some (.alu .add a1 x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8e : fetchRel tufRoleKeysReadCode 0x8E = some (.alu .add a2 x0 (22 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_90 : fetchRel tufRoleKeysReadCode 0x90 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_94 : fetchRel tufRoleKeysReadCode 0x94 = some (.jalr ra ra 0xFFFFFD14, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_98 : fetchRel tufRoleKeysReadCode 0x98 = some (.load .lw a1 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_9c : fetchRel tufRoleKeysReadCode 0x9C = some (.branch .beq a1 x0 0x848, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_a0 : fetchRel tufRoleKeysReadCode 0xA0 = some (.load .lw a2 sp 0x760, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_a4 : fetchRel tufRoleKeysReadCode 0xA4 = some (.aluImm .add a0 sp 0x18, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_a6 : fetchRel tufRoleKeysReadCode 0xA6 = some (.auipc ra 0x1000, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_aa : fetchRel tufRoleKeysReadCode 0xAA = some (.jalr ra ra 0xFFFFF8C0, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_ae : fetchRel tufRoleKeysReadCode 0xAE = some (.load .lbu a0 sp 0x18, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_b2 : fetchRel tufRoleKeysReadCode 0xB2 = some (.branch .beq a0 x0 0xA, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_b4 : fetchRel tufRoleKeysReadCode 0xB4 = some (.load .lbu a0 sp 0x19, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_b8 : fetchRel tufRoleKeysReadCode 0xB8 = some (.jal x0 0x830, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_bc : fetchRel tufRoleKeysReadCode 0xBC = some (.load .lw (24 : Fin 32) sp 0x20, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_be : fetchRel tufRoleKeysReadCode 0xBE = some (.load .lw (20 : Fin 32) sp 0x24, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_c0 : fetchRel tufRoleKeysReadCode 0xC0 = some (.alu .or a0 (24 : Fin 32) (20 : Fin 32), 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_c4 : fetchRel tufRoleKeysReadCode 0xC4 = some (.branch .beq a0 x0 0x86C, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_c8 : fetchRel tufRoleKeysReadCode 0xC8 = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_cc : fetchRel tufRoleKeysReadCode 0xCC = some (.aluImm .add a3 a3 0x762, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_d0 : fetchRel tufRoleKeysReadCode 0xD0 = some (.aluImm .add a0 sp 0x18, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_d2 : fetchRel tufRoleKeysReadCode 0xD2 = some (.aluImm .add a4 x0 0x4, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_d4 : fetchRel tufRoleKeysReadCode 0xD4 = some (.alu .add a1 x0 (19 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_d6 : fetchRel tufRoleKeysReadCode 0xD6 = some (.alu .add a2 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_d8 : fetchRel tufRoleKeysReadCode 0xD8 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_dc : fetchRel tufRoleKeysReadCode 0xDC = some (.jalr ra ra 0xFFFFFCCC, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_e0 : fetchRel tufRoleKeysReadCode 0xE0 = some (.load .lw (21 : Fin 32) sp 0x18, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_e2 : fetchRel tufRoleKeysReadCode 0xE2 = some (.branch .beq (21 : Fin 32) x0 0x7FC, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_e6 : fetchRel tufRoleKeysReadCode 0xE6 = some (.load .lw (18 : Fin 32) sp 0x1C, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_e8 : fetchRel tufRoleKeysReadCode 0xE8 = some (.aluImm .add a0 sp 0x18, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_ea : fetchRel tufRoleKeysReadCode 0xEA = some (.alu .add a1 x0 (21 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_ec : fetchRel tufRoleKeysReadCode 0xEC = some (.alu .add a2 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_ee : fetchRel tufRoleKeysReadCode 0xEE = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_f2 : fetchRel tufRoleKeysReadCode 0xF2 = some (.jalr ra ra 0xFFFFFEC8, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_f6 : fetchRel tufRoleKeysReadCode 0xF6 = some (.load .lw a0 sp 0x18, 2) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_f8 : fetchRel tufRoleKeysReadCode 0xF8 = some (.branch .beq a0 x0 0x7E6, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_fc : fetchRel tufRoleKeysReadCode 0xFC = some (.aluImm .add (8 : Fin 32) sp 0x55C, 4) :=
  (fetchRel_chunk rkr_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_100 : fetchRel tufRoleKeysReadCode 0x100 = some (.aluImm .add (9 : Fin 32) x0 0x8, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_102 : fetchRel tufRoleKeysReadCode 0x102 = some (.branch .beq (9 : Fin 32) x0 0x1A, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_104 : fetchRel tufRoleKeysReadCode 0x104 = some (.aluImm .add a2 x0 0x40, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_108 : fetchRel tufRoleKeysReadCode 0x108 = some (.alu .add a0 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_10a : fetchRel tufRoleKeysReadCode 0x10A = some (.aluImm .add a1 x0 0x0, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_10c : fetchRel tufRoleKeysReadCode 0x10C = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_110 : fetchRel tufRoleKeysReadCode 0x110 = some (.jalr ra ra 0xFFFFFD76, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_114 : fetchRel tufRoleKeysReadCode 0x114 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x40, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_118 : fetchRel tufRoleKeysReadCode 0x118 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_11a : fetchRel tufRoleKeysReadCode 0x11A = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFEA, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_11c : fetchRel tufRoleKeysReadCode 0x11C = some (.aluImm .add a0 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_120 : fetchRel tufRoleKeysReadCode 0x120 = some (.aluImm .add a1 x0 0x8, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_122 : fetchRel tufRoleKeysReadCode 0x122 = some (.aluImm .add a2 x0 0xFFFFFFFF, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_124 : fetchRel tufRoleKeysReadCode 0x124 = some (.branch .beq a1 x0 0xE, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_126 : fetchRel tufRoleKeysReadCode 0x126 = some (.store .sb a0 a2 0x0, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_12a : fetchRel tufRoleKeysReadCode 0x12A = some (.aluImm .add a0 a0 0x62, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_12e : fetchRel tufRoleKeysReadCode 0x12E = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_130 : fetchRel tufRoleKeysReadCode 0x130 = some (.branch .bne a1 x0 0xFFFFFFF6, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_132 : fetchRel tufRoleKeysReadCode 0x132 = some (.store .sw sp (24 : Fin 32) 0x328, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_136 : fetchRel tufRoleKeysReadCode 0x136 = some (.store .sw sp (20 : Fin 32) 0x32C, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_13a : fetchRel tufRoleKeysReadCode 0x13A = some (.store .sw sp x0 0x550, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_13e : fetchRel tufRoleKeysReadCode 0x13E = some (.aluImm .add (19 : Fin 32) sp 0x330, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_142 : fetchRel tufRoleKeysReadCode 0x142 = some (.aluImm .add a1 sp 0x55C, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_146 : fetchRel tufRoleKeysReadCode 0x146 = some (.aluImm .add a2 x0 0x200, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_14a : fetchRel tufRoleKeysReadCode 0x14A = some (.alu .add a0 x0 (19 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_14c : fetchRel tufRoleKeysReadCode 0x14C = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_150 : fetchRel tufRoleKeysReadCode 0x150 = some (.jalr ra ra 0xFFFFFD9E, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_154 : fetchRel tufRoleKeysReadCode 0x154 = some (.aluImm .add (20 : Fin 32) sp 0x530, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_158 : fetchRel tufRoleKeysReadCode 0x158 = some (.aluImm .add a2 x0 0x20, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_15c : fetchRel tufRoleKeysReadCode 0x15C = some (.alu .add a0 x0 (20 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_15e : fetchRel tufRoleKeysReadCode 0x15E = some (.aluImm .add a1 x0 0x0, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_160 : fetchRel tufRoleKeysReadCode 0x160 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_164 : fetchRel tufRoleKeysReadCode 0x164 = some (.jalr ra ra 0xFFFFFD22, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_168 : fetchRel tufRoleKeysReadCode 0x168 = some (.aluImm .add a0 sp 0x18, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_16a : fetchRel tufRoleKeysReadCode 0x16A = some (.aluImm .add a1 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_16e : fetchRel tufRoleKeysReadCode 0x16E = some (.aluImm .add a2 x0 0x310, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_172 : fetchRel tufRoleKeysReadCode 0x172 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_176 : fetchRel tufRoleKeysReadCode 0x176 = some (.jalr ra ra 0xFFFFFD78, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_17a : fetchRel tufRoleKeysReadCode 0x17A = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_17e : fetchRel tufRoleKeysReadCode 0x17E = some (.aluImm .add a3 a3 0x776, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_182 : fetchRel tufRoleKeysReadCode 0x182 = some (.aluImm .add a0 sp 0x55C, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_186 : fetchRel tufRoleKeysReadCode 0x186 = some (.aluImm .add a4 x0 0x6, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_188 : fetchRel tufRoleKeysReadCode 0x188 = some (.alu .add a1 x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_18a : fetchRel tufRoleKeysReadCode 0x18A = some (.alu .add a2 x0 (22 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_18c : fetchRel tufRoleKeysReadCode 0x18C = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_190 : fetchRel tufRoleKeysReadCode 0x190 = some (.jalr ra ra 0xFFFFFC18, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_194 : fetchRel tufRoleKeysReadCode 0x194 = some (.load .lw a1 sp 0x55C, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_198 : fetchRel tufRoleKeysReadCode 0x198 = some (.branch .beq a1 x0 0x7A4, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_19c : fetchRel tufRoleKeysReadCode 0x19C = some (.load .lw a2 sp 0x560, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1a0 : fetchRel tufRoleKeysReadCode 0x1A0 = some (.aluImm .add a0 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1a4 : fetchRel tufRoleKeysReadCode 0x1A4 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1a8 : fetchRel tufRoleKeysReadCode 0x1A8 = some (.jalr ra ra 0xFFFFFB58, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1ac : fetchRel tufRoleKeysReadCode 0x1AC = some (.load .lw (9 : Fin 32) sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1b0 : fetchRel tufRoleKeysReadCode 0x1B0 = some (.load .lbu (8 : Fin 32) sp 0x760, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1b4 : fetchRel tufRoleKeysReadCode 0x1B4 = some (.branch .beq (9 : Fin 32) x0 0x78E, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1b8 : fetchRel tufRoleKeysReadCode 0x1B8 = some (.aluImm .add a1 sp 0x761, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1bc : fetchRel tufRoleKeysReadCode 0x1BC = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1c0 : fetchRel tufRoleKeysReadCode 0x1C0 = some (.aluImm .add a0 a0 0x272, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1c4 : fetchRel tufRoleKeysReadCode 0x1C4 = some (.aluImm .add a2 x0 0x7, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1c6 : fetchRel tufRoleKeysReadCode 0x1C6 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1ca : fetchRel tufRoleKeysReadCode 0x1CA = some (.jalr ra ra 0xFFFFFD24, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1ce : fetchRel tufRoleKeysReadCode 0x1CE = some (.aluImm .add (24 : Fin 32) sp 0x7FF, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1d2 : fetchRel tufRoleKeysReadCode 0x1D2 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x26D, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1d6 : fetchRel tufRoleKeysReadCode 0x1D6 = some (.store .sw (24 : Fin 32) (9 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1da : fetchRel tufRoleKeysReadCode 0x1DA = some (.store .sb (24 : Fin 32) (8 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1de : fetchRel tufRoleKeysReadCode 0x1DE = some (.aluImm .add (26 : Fin 32) x0 0x1, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1e0 : fetchRel tufRoleKeysReadCode 0x1E0 = some (.aluImm .add (25 : Fin 32) sp 0x19, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1e4 : fetchRel tufRoleKeysReadCode 0x1E4 = some (.aluImm .add (23 : Fin 32) x0 0x9, 2) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1e6 : fetchRel tufRoleKeysReadCode 0x1E6 = some (.aluImm .add a0 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1ea : fetchRel tufRoleKeysReadCode 0x1EA = some (.aluImm .add a1 sp 0x7FF, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1ee : fetchRel tufRoleKeysReadCode 0x1EE = some (.aluImm .add a1 a1 0x26D, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1f2 : fetchRel tufRoleKeysReadCode 0x1F2 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1f6 : fetchRel tufRoleKeysReadCode 0x1F6 = some (.jalr ra ra 0xFFFFFB54, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1fa : fetchRel tufRoleKeysReadCode 0x1FA = some (.load .lbu a0 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_1fe : fetchRel tufRoleKeysReadCode 0x1FE = some (.branch .bne a0 x0 0x750, 4) :=
  (fetchRel_chunk rkr_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_202 : fetchRel tufRoleKeysReadCode 0x202 = some (.load .lw a1 sp 0x760, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_206 : fetchRel tufRoleKeysReadCode 0x206 = some (.branch .beq a1 x0 0x74E, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_20a : fetchRel tufRoleKeysReadCode 0x20A = some (.load .lw a2 sp 0x764, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_20e : fetchRel tufRoleKeysReadCode 0x20E = some (.aluImm .add a0 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_212 : fetchRel tufRoleKeysReadCode 0x212 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_216 : fetchRel tufRoleKeysReadCode 0x216 = some (.jalr ra ra 0xFFFFFBCE, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_21a : fetchRel tufRoleKeysReadCode 0x21A = some (.load .lw (8 : Fin 32) sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_21e : fetchRel tufRoleKeysReadCode 0x21E = some (.branch .beq (8 : Fin 32) x0 0x6C6, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_222 : fetchRel tufRoleKeysReadCode 0x222 = some (.branch .beq (26 : Fin 32) (23 : Fin 32) 0x70E, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_226 : fetchRel tufRoleKeysReadCode 0x226 = some (.load .lw (9 : Fin 32) sp 0x760, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_22a : fetchRel tufRoleKeysReadCode 0x22A = some (.aluImm .add a0 x0 0x41, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_22e : fetchRel tufRoleKeysReadCode 0x22E = some (.branch .bgeu (9 : Fin 32) a0 0x702, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_232 : fetchRel tufRoleKeysReadCode 0x232 = some (.alu .add a0 x0 (19 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_234 : fetchRel tufRoleKeysReadCode 0x234 = some (.alu .add a1 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_236 : fetchRel tufRoleKeysReadCode 0x236 = some (.alu .add a2 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_238 : fetchRel tufRoleKeysReadCode 0x238 = some (.alu .add a3 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_23a : fetchRel tufRoleKeysReadCode 0x23A = some (.auipc ra 0x4000, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_23e : fetchRel tufRoleKeysReadCode 0x23E = some (.jalr ra ra 0x692, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_242 : fetchRel tufRoleKeysReadCode 0x242 = some (.store .sw (20 : Fin 32) (9 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_246 : fetchRel tufRoleKeysReadCode 0x246 = some (.aluImm .add a0 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_24a : fetchRel tufRoleKeysReadCode 0x24A = some (.alu .add a1 x0 (21 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_24c : fetchRel tufRoleKeysReadCode 0x24C = some (.alu .add a2 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_24e : fetchRel tufRoleKeysReadCode 0x24E = some (.alu .add a3 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_250 : fetchRel tufRoleKeysReadCode 0x250 = some (.alu .add a4 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_252 : fetchRel tufRoleKeysReadCode 0x252 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_256 : fetchRel tufRoleKeysReadCode 0x256 = some (.jalr ra ra 0xFFFFFCBE, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_25a : fetchRel tufRoleKeysReadCode 0x25A = some (.load .lbu a0 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_25e : fetchRel tufRoleKeysReadCode 0x25E = some (.branch .bne a0 x0 0x6F0, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_262 : fetchRel tufRoleKeysReadCode 0x262 = some (.load .lw (8 : Fin 32) sp 0x760, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_266 : fetchRel tufRoleKeysReadCode 0x266 = some (.aluImm .add (22 : Fin 32) x0 0xFF, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_26a : fetchRel tufRoleKeysReadCode 0x26A = some (.branch .beq (8 : Fin 32) x0 0x48A, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_26e : fetchRel tufRoleKeysReadCode 0x26E = some (.load .lw (9 : Fin 32) sp 0x764, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_272 : fetchRel tufRoleKeysReadCode 0x272 = some (.aluImm .add a0 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_276 : fetchRel tufRoleKeysReadCode 0x276 = some (.aluImm .add a4 x0 0x7, 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_278 : fetchRel tufRoleKeysReadCode 0x278 = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_27a : fetchRel tufRoleKeysReadCode 0x27A = some (.alu .add a2 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_27c : fetchRel tufRoleKeysReadCode 0x27C = some (.lui a3 0x3FCC5000, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_280 : fetchRel tufRoleKeysReadCode 0x280 = some (.aluImm .add a3 a3 0xFFFFF871, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_284 : fetchRel tufRoleKeysReadCode 0x284 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_288 : fetchRel tufRoleKeysReadCode 0x288 = some (.jalr ra ra 0xFFFFFB20, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_28c : fetchRel tufRoleKeysReadCode 0x28C = some (.load .lw a1 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_290 : fetchRel tufRoleKeysReadCode 0x290 = some (.branch .beq a1 x0 0x464, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_294 : fetchRel tufRoleKeysReadCode 0x294 = some (.load .lw a2 sp 0x760, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_298 : fetchRel tufRoleKeysReadCode 0x298 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_29c : fetchRel tufRoleKeysReadCode 0x29C = some (.aluImm .add a0 a0 0x281, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2a0 : fetchRel tufRoleKeysReadCode 0x2A0 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2a4 : fetchRel tufRoleKeysReadCode 0x2A4 = some (.jalr ra ra 0xFFFFFB40, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2a8 : fetchRel tufRoleKeysReadCode 0x2A8 = some (.load .lw (23 : Fin 32) (24 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2ac : fetchRel tufRoleKeysReadCode 0x2AC = some (.branch .beq (23 : Fin 32) x0 0x446, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2b0 : fetchRel tufRoleKeysReadCode 0x2B0 = some (.load .lw a0 (24 : Fin 32) 0x18, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2b4 : fetchRel tufRoleKeysReadCode 0x2B4 = some (.store .sw sp a0 0x14, 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2b6 : fetchRel tufRoleKeysReadCode 0x2B6 = some (.aluImm .add a0 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2ba : fetchRel tufRoleKeysReadCode 0x2BA = some (.aluImm .add a4 x0 0x6, 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2bc : fetchRel tufRoleKeysReadCode 0x2BC = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2be : fetchRel tufRoleKeysReadCode 0x2BE = some (.alu .add a2 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2c0 : fetchRel tufRoleKeysReadCode 0x2C0 = some (.lui a3 0x3FCC5000, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2c4 : fetchRel tufRoleKeysReadCode 0x2C4 = some (.aluImm .add a3 a3 0xFFFFF878, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2c8 : fetchRel tufRoleKeysReadCode 0x2C8 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2cc : fetchRel tufRoleKeysReadCode 0x2CC = some (.jalr ra ra 0xFFFFFADC, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2d0 : fetchRel tufRoleKeysReadCode 0x2D0 = some (.load .lw a1 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2d4 : fetchRel tufRoleKeysReadCode 0x2D4 = some (.branch .beq a1 x0 0x41E, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2d8 : fetchRel tufRoleKeysReadCode 0x2D8 = some (.load .lw a2 sp 0x760, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2dc : fetchRel tufRoleKeysReadCode 0x2DC = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2e0 : fetchRel tufRoleKeysReadCode 0x2E0 = some (.aluImm .add a0 a0 0x281, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2e4 : fetchRel tufRoleKeysReadCode 0x2E4 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2e8 : fetchRel tufRoleKeysReadCode 0x2E8 = some (.jalr ra ra 0xFFFFFAFC, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2ec : fetchRel tufRoleKeysReadCode 0x2EC = some (.load .lw a0 (24 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2f0 : fetchRel tufRoleKeysReadCode 0x2F0 = some (.branch .beq a0 x0 0x402, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2f4 : fetchRel tufRoleKeysReadCode 0x2F4 = some (.store .sw sp a0 0xC, 2) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2f6 : fetchRel tufRoleKeysReadCode 0x2F6 = some (.aluImm .add (24 : Fin 32) sp 0x7FF, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2fa : fetchRel tufRoleKeysReadCode 0x2FA = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x26D, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_2fe : fetchRel tufRoleKeysReadCode 0x2FE = some (.load .lw a0 (24 : Fin 32) 0x18, 4) :=
  (fetchRel_chunk rkr_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_302 : fetchRel tufRoleKeysReadCode 0x302 = some (.store .sw sp a0 0x10, 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_304 : fetchRel tufRoleKeysReadCode 0x304 = some (.aluImm .add a0 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_308 : fetchRel tufRoleKeysReadCode 0x308 = some (.aluImm .add a4 x0 0x6, 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_30a : fetchRel tufRoleKeysReadCode 0x30A = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_30c : fetchRel tufRoleKeysReadCode 0x30C = some (.alu .add a2 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_30e : fetchRel tufRoleKeysReadCode 0x30E = some (.lui a3 0x3FCC5000, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_312 : fetchRel tufRoleKeysReadCode 0x312 = some (.aluImm .add a3 a3 0xFFFFF87E, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_316 : fetchRel tufRoleKeysReadCode 0x316 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_31a : fetchRel tufRoleKeysReadCode 0x31A = some (.jalr ra ra 0xFFFFFA8E, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_31e : fetchRel tufRoleKeysReadCode 0x31E = some (.load .lw a1 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_322 : fetchRel tufRoleKeysReadCode 0x322 = some (.branch .beq a1 x0 0x3C8, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_326 : fetchRel tufRoleKeysReadCode 0x326 = some (.load .lw a2 sp 0x760, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_32a : fetchRel tufRoleKeysReadCode 0x32A = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_32e : fetchRel tufRoleKeysReadCode 0x32E = some (.aluImm .add a0 a0 0x281, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_332 : fetchRel tufRoleKeysReadCode 0x332 = some (.aluImm .add a4 x0 0x6, 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_334 : fetchRel tufRoleKeysReadCode 0x334 = some (.lui a3 0x3FCC5000, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_338 : fetchRel tufRoleKeysReadCode 0x338 = some (.aluImm .add a3 a3 0xFFFFF884, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_33c : fetchRel tufRoleKeysReadCode 0x33C = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_340 : fetchRel tufRoleKeysReadCode 0x340 = some (.jalr ra ra 0xFFFFFA68, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_344 : fetchRel tufRoleKeysReadCode 0x344 = some (.load .lw a1 (24 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_348 : fetchRel tufRoleKeysReadCode 0x348 = some (.branch .beq a1 x0 0x3A2, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_34c : fetchRel tufRoleKeysReadCode 0x34C = some (.alu .add (9 : Fin 32) x0 (24 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_34e : fetchRel tufRoleKeysReadCode 0x34E = some (.load .lw a2 (9 : Fin 32) 0x18, 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_350 : fetchRel tufRoleKeysReadCode 0x350 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_354 : fetchRel tufRoleKeysReadCode 0x354 = some (.aluImm .add a0 a0 0x279, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_358 : fetchRel tufRoleKeysReadCode 0x358 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_35c : fetchRel tufRoleKeysReadCode 0x35C = some (.jalr ra ra 0xFFFFFA88, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_360 : fetchRel tufRoleKeysReadCode 0x360 = some (.load .lw (8 : Fin 32) (9 : Fin 32) 0xC, 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_362 : fetchRel tufRoleKeysReadCode 0x362 = some (.branch .beq (8 : Fin 32) x0 0x388, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_366 : fetchRel tufRoleKeysReadCode 0x366 = some (.load .lw (9 : Fin 32) (24 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_36a : fetchRel tufRoleKeysReadCode 0x36A = some (.aluImm .add a0 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_36e : fetchRel tufRoleKeysReadCode 0x36E = some (.aluImm .add a2 x0 0x80, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_372 : fetchRel tufRoleKeysReadCode 0x372 = some (.aluImm .add a1 x0 0x0, 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_374 : fetchRel tufRoleKeysReadCode 0x374 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_378 : fetchRel tufRoleKeysReadCode 0x378 = some (.jalr ra ra 0xFFFFFB0E, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_37c : fetchRel tufRoleKeysReadCode 0x37C = some (.aluImm .add a0 x0 0x13, 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_37e : fetchRel tufRoleKeysReadCode 0x37E = some (.load .lw a3 sp 0x10, 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_380 : fetchRel tufRoleKeysReadCode 0x380 = some (.branch .bne a3 a0 0x1C8, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_384 : fetchRel tufRoleKeysReadCode 0x384 = some (.load .lw a2 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_386 : fetchRel tufRoleKeysReadCode 0x386 = some (.load .lbu a0 a2 0x0, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_38a : fetchRel tufRoleKeysReadCode 0x38A = some (.aluImm .add a1 a0 0xFFFFFF9B, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_38e : fetchRel tufRoleKeysReadCode 0x38E = some (.aluImm .add a0 x0 0xFF, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_392 : fetchRel tufRoleKeysReadCode 0x392 = some (.branch .bne a1 x0 0x296, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_396 : fetchRel tufRoleKeysReadCode 0x396 = some (.load .lbu a1 a2 0x1, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_39a : fetchRel tufRoleKeysReadCode 0x39A = some (.aluImm .add a1 a1 0xFFFFFF9D, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_39e : fetchRel tufRoleKeysReadCode 0x39E = some (.aluImm .add (24 : Fin 32) sp 0x7FF, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3a2 : fetchRel tufRoleKeysReadCode 0x3A2 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x26D, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3a6 : fetchRel tufRoleKeysReadCode 0x3A6 = some (.branch .bne a1 x0 0x28A, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3aa : fetchRel tufRoleKeysReadCode 0x3AA = some (.load .lbu a1 a2 0x2, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3ae : fetchRel tufRoleKeysReadCode 0x3AE = some (.aluImm .add a1 a1 0xFFFFFF9C, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3b2 : fetchRel tufRoleKeysReadCode 0x3B2 = some (.branch .bne a1 x0 0x27E, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3b6 : fetchRel tufRoleKeysReadCode 0x3B6 = some (.load .lbu a1 a2 0x3, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3ba : fetchRel tufRoleKeysReadCode 0x3BA = some (.aluImm .add a1 a1 0xFFFFFF8D, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3be : fetchRel tufRoleKeysReadCode 0x3BE = some (.branch .bne a1 x0 0x26A, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3c2 : fetchRel tufRoleKeysReadCode 0x3C2 = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3c4 : fetchRel tufRoleKeysReadCode 0x3C4 = some (.load .lbu a1 a1 0x4, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3c8 : fetchRel tufRoleKeysReadCode 0x3C8 = some (.aluImm .add a1 a1 0xFFFFFF9F, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3cc : fetchRel tufRoleKeysReadCode 0x3CC = some (.branch .bne a1 x0 0x25C, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3d0 : fetchRel tufRoleKeysReadCode 0x3D0 = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3d2 : fetchRel tufRoleKeysReadCode 0x3D2 = some (.load .lbu a1 a1 0x5, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3d6 : fetchRel tufRoleKeysReadCode 0x3D6 = some (.aluImm .add a1 a1 0xFFFFFFD3, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3da : fetchRel tufRoleKeysReadCode 0x3DA = some (.branch .bne a1 x0 0x24E, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3de : fetchRel tufRoleKeysReadCode 0x3DE = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3e0 : fetchRel tufRoleKeysReadCode 0x3E0 = some (.load .lbu a1 a1 0x6, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3e4 : fetchRel tufRoleKeysReadCode 0x3E4 = some (.aluImm .add a1 a1 0xFFFFFF8D, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3e8 : fetchRel tufRoleKeysReadCode 0x3E8 = some (.branch .bne a1 x0 0x240, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3ec : fetchRel tufRoleKeysReadCode 0x3EC = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3ee : fetchRel tufRoleKeysReadCode 0x3EE = some (.load .lbu a1 a1 0x7, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3f2 : fetchRel tufRoleKeysReadCode 0x3F2 = some (.aluImm .add a1 a1 0xFFFFFF98, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3f6 : fetchRel tufRoleKeysReadCode 0x3F6 = some (.branch .bne a1 x0 0x232, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3fa : fetchRel tufRoleKeysReadCode 0x3FA = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_3fc : fetchRel tufRoleKeysReadCode 0x3FC = some (.load .lbu a1 a1 0x8, 4) :=
  (fetchRel_chunk rkr_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_400 : fetchRel tufRoleKeysReadCode 0x400 = some (.aluImm .add a1 a1 0xFFFFFF9F, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_404 : fetchRel tufRoleKeysReadCode 0x404 = some (.branch .bne a1 x0 0x224, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_408 : fetchRel tufRoleKeysReadCode 0x408 = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_40a : fetchRel tufRoleKeysReadCode 0x40A = some (.load .lbu a1 a1 0x9, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_40e : fetchRel tufRoleKeysReadCode 0x40E = some (.aluImm .add a1 a1 0xFFFFFFCE, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_412 : fetchRel tufRoleKeysReadCode 0x412 = some (.branch .bne a1 x0 0x216, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_416 : fetchRel tufRoleKeysReadCode 0x416 = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_418 : fetchRel tufRoleKeysReadCode 0x418 = some (.load .lbu a1 a1 0xA, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_41c : fetchRel tufRoleKeysReadCode 0x41C = some (.aluImm .add a1 a1 0xFFFFFFD3, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_420 : fetchRel tufRoleKeysReadCode 0x420 = some (.branch .bne a1 x0 0x208, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_424 : fetchRel tufRoleKeysReadCode 0x424 = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_426 : fetchRel tufRoleKeysReadCode 0x426 = some (.load .lbu a1 a1 0xB, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_42a : fetchRel tufRoleKeysReadCode 0x42A = some (.aluImm .add a1 a1 0xFFFFFF92, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_42e : fetchRel tufRoleKeysReadCode 0x42E = some (.branch .bne a1 x0 0x1FA, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_432 : fetchRel tufRoleKeysReadCode 0x432 = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_434 : fetchRel tufRoleKeysReadCode 0x434 = some (.load .lbu a1 a1 0xC, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_438 : fetchRel tufRoleKeysReadCode 0x438 = some (.aluImm .add a1 a1 0xFFFFFF97, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_43c : fetchRel tufRoleKeysReadCode 0x43C = some (.branch .bne a1 x0 0x1EC, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_440 : fetchRel tufRoleKeysReadCode 0x440 = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_442 : fetchRel tufRoleKeysReadCode 0x442 = some (.load .lbu a1 a1 0xD, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_446 : fetchRel tufRoleKeysReadCode 0x446 = some (.aluImm .add a1 a1 0xFFFFFF8D, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_44a : fetchRel tufRoleKeysReadCode 0x44A = some (.branch .bne a1 x0 0x1DE, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_44e : fetchRel tufRoleKeysReadCode 0x44E = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_450 : fetchRel tufRoleKeysReadCode 0x450 = some (.load .lbu a1 a1 0xE, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_454 : fetchRel tufRoleKeysReadCode 0x454 = some (.aluImm .add a1 a1 0xFFFFFF8C, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_458 : fetchRel tufRoleKeysReadCode 0x458 = some (.branch .bne a1 x0 0x1D0, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_45c : fetchRel tufRoleKeysReadCode 0x45C = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_45e : fetchRel tufRoleKeysReadCode 0x45E = some (.load .lbu a1 a1 0xF, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_462 : fetchRel tufRoleKeysReadCode 0x462 = some (.aluImm .add a1 a1 0xFFFFFF90, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_466 : fetchRel tufRoleKeysReadCode 0x466 = some (.branch .bne a1 x0 0x1C2, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_46a : fetchRel tufRoleKeysReadCode 0x46A = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_46c : fetchRel tufRoleKeysReadCode 0x46C = some (.load .lbu a1 a1 0x10, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_470 : fetchRel tufRoleKeysReadCode 0x470 = some (.aluImm .add a2 a1 0xFFFFFFCD, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_474 : fetchRel tufRoleKeysReadCode 0x474 = some (.branch .beq a2 x0 0x1C2, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_478 : fetchRel tufRoleKeysReadCode 0x478 = some (.aluImm .add a1 a1 0xFFFFFFCE, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_47c : fetchRel tufRoleKeysReadCode 0x47C = some (.branch .bne a1 x0 0x1AC, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_480 : fetchRel tufRoleKeysReadCode 0x480 = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_482 : fetchRel tufRoleKeysReadCode 0x482 = some (.load .lbu a1 a1 0x11, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_486 : fetchRel tufRoleKeysReadCode 0x486 = some (.aluImm .add a1 a1 0xFFFFFFCB, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_48a : fetchRel tufRoleKeysReadCode 0x48A = some (.branch .bne a1 x0 0x19E, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_48e : fetchRel tufRoleKeysReadCode 0x48E = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_490 : fetchRel tufRoleKeysReadCode 0x490 = some (.load .lbu a1 a1 0x12, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_494 : fetchRel tufRoleKeysReadCode 0x494 = some (.aluImm .add a1 a1 0xFFFFFFCA, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_498 : fetchRel tufRoleKeysReadCode 0x498 = some (.branch .bne a1 x0 0x190, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_49c : fetchRel tufRoleKeysReadCode 0x49C = some (.aluImm .add a1 x0 0x13, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_49e : fetchRel tufRoleKeysReadCode 0x49E = some (.load .lw a2 sp 0x14, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4a0 : fetchRel tufRoleKeysReadCode 0x4A0 = some (.branch .beq a2 a1 0x27C, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4a4 : fetchRel tufRoleKeysReadCode 0x4A4 = some (.aluImm .add a1 x0 0x5, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4a6 : fetchRel tufRoleKeysReadCode 0x4A6 = some (.load .lw a2 sp 0x14, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4a8 : fetchRel tufRoleKeysReadCode 0x4A8 = some (.branch .bne a2 a1 0x180, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4ac : fetchRel tufRoleKeysReadCode 0x4AC = some (.load .lbu a1 (23 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4b0 : fetchRel tufRoleKeysReadCode 0x4B0 = some (.aluImm .add a1 a1 0xFFFFFF9B, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4b4 : fetchRel tufRoleKeysReadCode 0x4B4 = some (.branch .bne a1 x0 0x174, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4b8 : fetchRel tufRoleKeysReadCode 0x4B8 = some (.load .lbu a1 (23 : Fin 32) 0x1, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4bc : fetchRel tufRoleKeysReadCode 0x4BC = some (.aluImm .add a1 a1 0xFFFFFF9D, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4c0 : fetchRel tufRoleKeysReadCode 0x4C0 = some (.branch .bne a1 x0 0x168, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4c4 : fetchRel tufRoleKeysReadCode 0x4C4 = some (.load .lbu a1 (23 : Fin 32) 0x2, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4c8 : fetchRel tufRoleKeysReadCode 0x4C8 = some (.aluImm .add a1 a1 0xFFFFFF9C, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4cc : fetchRel tufRoleKeysReadCode 0x4CC = some (.branch .bne a1 x0 0x15C, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4d0 : fetchRel tufRoleKeysReadCode 0x4D0 = some (.load .lbu a1 (23 : Fin 32) 0x3, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4d4 : fetchRel tufRoleKeysReadCode 0x4D4 = some (.aluImm .add a1 a1 0xFFFFFF8D, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4d8 : fetchRel tufRoleKeysReadCode 0x4D8 = some (.branch .bne a1 x0 0x150, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4dc : fetchRel tufRoleKeysReadCode 0x4DC = some (.load .lbu a1 (23 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4e0 : fetchRel tufRoleKeysReadCode 0x4E0 = some (.aluImm .add a1 a1 0xFFFFFF9F, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4e4 : fetchRel tufRoleKeysReadCode 0x4E4 = some (.aluImm .add (24 : Fin 32) sp 0x7FF, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4e8 : fetchRel tufRoleKeysReadCode 0x4E8 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x26D, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4ec : fetchRel tufRoleKeysReadCode 0x4EC = some (.aluImm .add (23 : Fin 32) x0 0x9, 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4ee : fetchRel tufRoleKeysReadCode 0x4EE = some (.branch .bne a1 x0 0x144, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4f2 : fetchRel tufRoleKeysReadCode 0x4F2 = some (.aluImm .add a2 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4f6 : fetchRel tufRoleKeysReadCode 0x4F6 = some (.alu .add a0 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4f8 : fetchRel tufRoleKeysReadCode 0x4F8 = some (.alu .add a1 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4fa : fetchRel tufRoleKeysReadCode 0x4FA = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_4fe : fetchRel tufRoleKeysReadCode 0x4FE = some (.jalr ra ra 0x4FE, 4) :=
  (fetchRel_chunk rkr_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_502 : fetchRel tufRoleKeysReadCode 0x502 = some (.branch .beq a0 x0 0x1E8, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_506 : fetchRel tufRoleKeysReadCode 0x506 = some (.alu .add (8 : Fin 32) x0 a0, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_508 : fetchRel tufRoleKeysReadCode 0x508 = some (.alu .add (9 : Fin 32) x0 a1, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_50a : fetchRel tufRoleKeysReadCode 0x50A = some (.aluImm .add a0 x0 0x1A, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_50c : fetchRel tufRoleKeysReadCode 0x50C = some (.branch .bltu a1 a0 0x1DE, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_510 : fetchRel tufRoleKeysReadCode 0x510 = some (.aluImm .add a2 x0 0x1A, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_512 : fetchRel tufRoleKeysReadCode 0x512 = some (.alu .add a0 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_514 : fetchRel tufRoleKeysReadCode 0x514 = some (.lui a1 0x3FCC4000, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_518 : fetchRel tufRoleKeysReadCode 0x518 = some (.aluImm .add a1 a1 0x69C, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_51c : fetchRel tufRoleKeysReadCode 0x51C = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_520 : fetchRel tufRoleKeysReadCode 0x520 = some (.jalr ra ra 0x588, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_524 : fetchRel tufRoleKeysReadCode 0x524 = some (.branch .beq a0 x0 0x1C6, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_528 : fetchRel tufRoleKeysReadCode 0x528 = some (.aluImm .add a0 (9 : Fin 32) 0xFFFFFFA5, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_52c : fetchRel tufRoleKeysReadCode 0x52C = some (.branch .bne a0 x0 0x1BE, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_530 : fetchRel tufRoleKeysReadCode 0x530 = some (.aluImm .add a1 (8 : Fin 32) 0x1A, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_534 : fetchRel tufRoleKeysReadCode 0x534 = some (.aluImm .add a0 sp 0x55C, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_538 : fetchRel tufRoleKeysReadCode 0x538 = some (.aluImm .add a2 x0 0x41, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_53c : fetchRel tufRoleKeysReadCode 0x53C = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_540 : fetchRel tufRoleKeysReadCode 0x540 = some (.jalr ra ra 0xFFFFF9AE, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_544 : fetchRel tufRoleKeysReadCode 0x544 = some (.aluImm .add a0 x0 0x0, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_546 : fetchRel tufRoleKeysReadCode 0x546 = some (.jal x0 0xE2, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_548 : fetchRel tufRoleKeysReadCode 0x548 = some (.aluImm .add a0 x0 0xFF, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_54c : fetchRel tufRoleKeysReadCode 0x54C = some (.aluImm .add a1 x0 0x7, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_54e : fetchRel tufRoleKeysReadCode 0x54E = some (.load .lw a2 sp 0x14, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_550 : fetchRel tufRoleKeysReadCode 0x550 = some (.branch .bne a2 a1 0xD8, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_554 : fetchRel tufRoleKeysReadCode 0x554 = some (.branch .bne a3 a1 0xD4, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_558 : fetchRel tufRoleKeysReadCode 0x558 = some (.load .lbu a1 (23 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_55c : fetchRel tufRoleKeysReadCode 0x55C = some (.aluImm .add a1 a1 0xFFFFFF9B, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_560 : fetchRel tufRoleKeysReadCode 0x560 = some (.branch .bne a1 x0 0xC8, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_562 : fetchRel tufRoleKeysReadCode 0x562 = some (.load .lbu a1 (23 : Fin 32) 0x1, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_566 : fetchRel tufRoleKeysReadCode 0x566 = some (.aluImm .add a1 a1 0xFFFFFF9C, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_56a : fetchRel tufRoleKeysReadCode 0x56A = some (.branch .bne a1 x0 0xBE, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_56c : fetchRel tufRoleKeysReadCode 0x56C = some (.load .lbu a1 (23 : Fin 32) 0x2, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_570 : fetchRel tufRoleKeysReadCode 0x570 = some (.aluImm .add a1 a1 0xFFFFFFCE, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_574 : fetchRel tufRoleKeysReadCode 0x574 = some (.branch .bne a1 x0 0xB4, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_576 : fetchRel tufRoleKeysReadCode 0x576 = some (.load .lbu a1 (23 : Fin 32) 0x3, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_57a : fetchRel tufRoleKeysReadCode 0x57A = some (.aluImm .add a1 a1 0xFFFFFFCB, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_57e : fetchRel tufRoleKeysReadCode 0x57E = some (.branch .bne a1 x0 0xAA, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_580 : fetchRel tufRoleKeysReadCode 0x580 = some (.load .lbu a1 (23 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_584 : fetchRel tufRoleKeysReadCode 0x584 = some (.aluImm .add a1 a1 0xFFFFFFCB, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_588 : fetchRel tufRoleKeysReadCode 0x588 = some (.branch .bne a1 x0 0xA0, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_58a : fetchRel tufRoleKeysReadCode 0x58A = some (.load .lbu a1 (23 : Fin 32) 0x5, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_58e : fetchRel tufRoleKeysReadCode 0x58E = some (.aluImm .add a1 a1 0xFFFFFFCF, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_592 : fetchRel tufRoleKeysReadCode 0x592 = some (.branch .bne a1 x0 0x96, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_594 : fetchRel tufRoleKeysReadCode 0x594 = some (.load .lbu a1 (23 : Fin 32) 0x6, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_598 : fetchRel tufRoleKeysReadCode 0x598 = some (.aluImm .add a1 a1 0xFFFFFFC7, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_59c : fetchRel tufRoleKeysReadCode 0x59C = some (.branch .bne a1 x0 0x8C, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_59e : fetchRel tufRoleKeysReadCode 0x59E = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5a0 : fetchRel tufRoleKeysReadCode 0x5A0 = some (.load .lbu a1 a1 0x0, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5a4 : fetchRel tufRoleKeysReadCode 0x5A4 = some (.aluImm .add a1 a1 0xFFFFFF9B, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5a8 : fetchRel tufRoleKeysReadCode 0x5A8 = some (.branch .bne a1 x0 0x80, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5aa : fetchRel tufRoleKeysReadCode 0x5AA = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5ac : fetchRel tufRoleKeysReadCode 0x5AC = some (.load .lbu a1 a1 0x1, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5b0 : fetchRel tufRoleKeysReadCode 0x5B0 = some (.aluImm .add a1 a1 0xFFFFFF9C, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5b4 : fetchRel tufRoleKeysReadCode 0x5B4 = some (.branch .bne a1 x0 0x74, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5b6 : fetchRel tufRoleKeysReadCode 0x5B6 = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5b8 : fetchRel tufRoleKeysReadCode 0x5B8 = some (.load .lbu a1 a1 0x2, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5bc : fetchRel tufRoleKeysReadCode 0x5BC = some (.aluImm .add a1 a1 0xFFFFFFCE, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5c0 : fetchRel tufRoleKeysReadCode 0x5C0 = some (.branch .bne a1 x0 0x68, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5c2 : fetchRel tufRoleKeysReadCode 0x5C2 = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5c4 : fetchRel tufRoleKeysReadCode 0x5C4 = some (.load .lbu a1 a1 0x3, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5c8 : fetchRel tufRoleKeysReadCode 0x5C8 = some (.aluImm .add a1 a1 0xFFFFFFCB, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5cc : fetchRel tufRoleKeysReadCode 0x5CC = some (.branch .bne a1 x0 0x5C, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5ce : fetchRel tufRoleKeysReadCode 0x5CE = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5d0 : fetchRel tufRoleKeysReadCode 0x5D0 = some (.load .lbu a1 a1 0x4, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5d4 : fetchRel tufRoleKeysReadCode 0x5D4 = some (.aluImm .add a1 a1 0xFFFFFFCB, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5d8 : fetchRel tufRoleKeysReadCode 0x5D8 = some (.branch .bne a1 x0 0x50, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5da : fetchRel tufRoleKeysReadCode 0x5DA = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5dc : fetchRel tufRoleKeysReadCode 0x5DC = some (.load .lbu a1 a1 0x5, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5e0 : fetchRel tufRoleKeysReadCode 0x5E0 = some (.aluImm .add a1 a1 0xFFFFFFCF, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5e4 : fetchRel tufRoleKeysReadCode 0x5E4 = some (.branch .bne a1 x0 0x44, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5e6 : fetchRel tufRoleKeysReadCode 0x5E6 = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5e8 : fetchRel tufRoleKeysReadCode 0x5E8 = some (.load .lbu a1 a1 0x6, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5ec : fetchRel tufRoleKeysReadCode 0x5EC = some (.aluImm .add a1 a1 0xFFFFFFC7, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5f0 : fetchRel tufRoleKeysReadCode 0x5F0 = some (.aluImm .add (24 : Fin 32) sp 0x7FF, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5f4 : fetchRel tufRoleKeysReadCode 0x5F4 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x26D, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5f8 : fetchRel tufRoleKeysReadCode 0x5F8 = some (.aluImm .add (23 : Fin 32) x0 0x9, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5fa : fetchRel tufRoleKeysReadCode 0x5FA = some (.branch .bne a1 x0 0x38, 2) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_5fc : fetchRel tufRoleKeysReadCode 0x5FC = some (.aluImm .add a2 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_600 : fetchRel tufRoleKeysReadCode 0x600 = some (.alu .add a0 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_602 : fetchRel tufRoleKeysReadCode 0x602 = some (.alu .add a1 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_604 : fetchRel tufRoleKeysReadCode 0x604 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_608 : fetchRel tufRoleKeysReadCode 0x608 = some (.jalr ra ra 0xFFFFF846, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_60c : fetchRel tufRoleKeysReadCode 0x60C = some (.branch .beq a0 x0 0xDE, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_60e : fetchRel tufRoleKeysReadCode 0x60E = some (.aluImm .add a1 a1 0xFFFFFFE0, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_610 : fetchRel tufRoleKeysReadCode 0x610 = some (.branch .bne a1 x0 0xDA, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_612 : fetchRel tufRoleKeysReadCode 0x612 = some (.alu .add a3 x0 a0, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_614 : fetchRel tufRoleKeysReadCode 0x614 = some (.aluImm .add a0 sp 0x55C, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_618 : fetchRel tufRoleKeysReadCode 0x618 = some (.aluImm .add a2 x0 0x20, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_61c : fetchRel tufRoleKeysReadCode 0x61C = some (.alu .add a1 x0 a3, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_61e : fetchRel tufRoleKeysReadCode 0x61E = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_622 : fetchRel tufRoleKeysReadCode 0x622 = some (.jalr ra ra 0xFFFFF8CC, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_626 : fetchRel tufRoleKeysReadCode 0x626 = some (.aluImm .add a0 x0 0x2, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_628 : fetchRel tufRoleKeysReadCode 0x628 = some (.aluImm .add (24 : Fin 32) sp 0x7FF, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_62c : fetchRel tufRoleKeysReadCode 0x62C = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x26D, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_630 : fetchRel tufRoleKeysReadCode 0x630 = some (.aluImm .add (23 : Fin 32) x0 0x9, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_632 : fetchRel tufRoleKeysReadCode 0x632 = some (.alu .add (22 : Fin 32) x0 a0, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_634 : fetchRel tufRoleKeysReadCode 0x634 = some (.jal x0 0xC0, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_636 : fetchRel tufRoleKeysReadCode 0x636 = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_638 : fetchRel tufRoleKeysReadCode 0x638 = some (.load .lbu a1 a1 0x11, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_63c : fetchRel tufRoleKeysReadCode 0x63C = some (.aluImm .add a1 a1 0xFFFFFFC8, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_640 : fetchRel tufRoleKeysReadCode 0x640 = some (.branch .bne a1 x0 0xFFFFFFE8, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_642 : fetchRel tufRoleKeysReadCode 0x642 = some (.load .lw a1 sp 0xC, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_644 : fetchRel tufRoleKeysReadCode 0x644 = some (.load .lbu a1 a1 0x12, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_648 : fetchRel tufRoleKeysReadCode 0x648 = some (.aluImm .add a1 a1 0xFFFFFFCC, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_64c : fetchRel tufRoleKeysReadCode 0x64C = some (.branch .bne a1 x0 0xFFFFFFDC, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_64e : fetchRel tufRoleKeysReadCode 0x64E = some (.aluImm .add a1 x0 0x13, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_650 : fetchRel tufRoleKeysReadCode 0x650 = some (.load .lw a2 sp 0x14, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_652 : fetchRel tufRoleKeysReadCode 0x652 = some (.branch .beq a2 a1 0x1AA, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_656 : fetchRel tufRoleKeysReadCode 0x656 = some (.aluImm .add a1 x0 0x5, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_658 : fetchRel tufRoleKeysReadCode 0x658 = some (.load .lw a2 sp 0x14, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_65a : fetchRel tufRoleKeysReadCode 0x65A = some (.branch .bne a2 a1 0xFFFFFFCE, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_65e : fetchRel tufRoleKeysReadCode 0x65E = some (.load .lbu a1 (23 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_662 : fetchRel tufRoleKeysReadCode 0x662 = some (.aluImm .add a1 a1 0xFFFFFF9B, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_666 : fetchRel tufRoleKeysReadCode 0x666 = some (.branch .bne a1 x0 0xFFFFFFC2, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_668 : fetchRel tufRoleKeysReadCode 0x668 = some (.load .lbu a1 (23 : Fin 32) 0x1, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_66c : fetchRel tufRoleKeysReadCode 0x66C = some (.aluImm .add a1 a1 0xFFFFFF9D, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_670 : fetchRel tufRoleKeysReadCode 0x670 = some (.branch .bne a1 x0 0xFFFFFFB8, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_672 : fetchRel tufRoleKeysReadCode 0x672 = some (.load .lbu a1 (23 : Fin 32) 0x2, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_676 : fetchRel tufRoleKeysReadCode 0x676 = some (.aluImm .add a1 a1 0xFFFFFF9C, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_67a : fetchRel tufRoleKeysReadCode 0x67A = some (.branch .bne a1 x0 0xFFFFFFAE, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_67c : fetchRel tufRoleKeysReadCode 0x67C = some (.load .lbu a1 (23 : Fin 32) 0x3, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_680 : fetchRel tufRoleKeysReadCode 0x680 = some (.aluImm .add a1 a1 0xFFFFFF8D, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_684 : fetchRel tufRoleKeysReadCode 0x684 = some (.branch .bne a1 x0 0xFFFFFFA4, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_686 : fetchRel tufRoleKeysReadCode 0x686 = some (.load .lbu a1 (23 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_68a : fetchRel tufRoleKeysReadCode 0x68A = some (.aluImm .add a1 a1 0xFFFFFF9F, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_68e : fetchRel tufRoleKeysReadCode 0x68E = some (.aluImm .add (24 : Fin 32) sp 0x7FF, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_692 : fetchRel tufRoleKeysReadCode 0x692 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x26D, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_696 : fetchRel tufRoleKeysReadCode 0x696 = some (.aluImm .add (23 : Fin 32) x0 0x9, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_698 : fetchRel tufRoleKeysReadCode 0x698 = some (.branch .bne a1 x0 0xFFFFFF9A, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_69a : fetchRel tufRoleKeysReadCode 0x69A = some (.aluImm .add a2 sp 0x75C, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_69e : fetchRel tufRoleKeysReadCode 0x69E = some (.alu .add a0 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6a0 : fetchRel tufRoleKeysReadCode 0x6A0 = some (.alu .add a1 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6a2 : fetchRel tufRoleKeysReadCode 0x6A2 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6a6 : fetchRel tufRoleKeysReadCode 0x6A6 = some (.jalr ra ra 0x356, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6aa : fetchRel tufRoleKeysReadCode 0x6AA = some (.branch .beq a0 x0 0x40, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6ac : fetchRel tufRoleKeysReadCode 0x6AC = some (.alu .add (8 : Fin 32) x0 a0, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6ae : fetchRel tufRoleKeysReadCode 0x6AE = some (.alu .add (9 : Fin 32) x0 a1, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6b0 : fetchRel tufRoleKeysReadCode 0x6B0 = some (.aluImm .add a0 x0 0x17, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6b2 : fetchRel tufRoleKeysReadCode 0x6B2 = some (.branch .bltu a1 a0 0x38, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6b6 : fetchRel tufRoleKeysReadCode 0x6B6 = some (.aluImm .add a2 x0 0x17, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6b8 : fetchRel tufRoleKeysReadCode 0x6B8 = some (.alu .add a0 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6ba : fetchRel tufRoleKeysReadCode 0x6BA = some (.lui a1 0x3FCC5000, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6be : fetchRel tufRoleKeysReadCode 0x6BE = some (.aluImm .add a1 a1 0xFFFFF88A, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6c2 : fetchRel tufRoleKeysReadCode 0x6C2 = some (.auipc ra 0xFFFFE000, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6c6 : fetchRel tufRoleKeysReadCode 0x6C6 = some (.jalr ra ra 0x3E2, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6ca : fetchRel tufRoleKeysReadCode 0x6CA = some (.branch .beq a0 x0 0x20, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6cc : fetchRel tufRoleKeysReadCode 0x6CC = some (.aluImm .add a0 (9 : Fin 32) 0xFFFFFF88, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6d0 : fetchRel tufRoleKeysReadCode 0x6D0 = some (.branch .bne a0 x0 0x1A, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6d2 : fetchRel tufRoleKeysReadCode 0x6D2 = some (.aluImm .add a1 (8 : Fin 32) 0x17, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6d6 : fetchRel tufRoleKeysReadCode 0x6D6 = some (.aluImm .add a0 sp 0x55C, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6da : fetchRel tufRoleKeysReadCode 0x6DA = some (.aluImm .add a2 x0 0x61, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6de : fetchRel tufRoleKeysReadCode 0x6DE = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6e2 : fetchRel tufRoleKeysReadCode 0x6E2 = some (.jalr ra ra 0xFFFFF80C, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6e6 : fetchRel tufRoleKeysReadCode 0x6E6 = some (.aluImm .add a0 x0 0x1, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6e8 : fetchRel tufRoleKeysReadCode 0x6E8 = some (.jal x0 0xFFFFFF40, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6ea : fetchRel tufRoleKeysReadCode 0x6EA = some (.aluImm .add (24 : Fin 32) sp 0x7FF, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6ee : fetchRel tufRoleKeysReadCode 0x6EE = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x26D, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6f2 : fetchRel tufRoleKeysReadCode 0x6F2 = some (.aluImm .add (23 : Fin 32) x0 0x9, 2) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6f4 : fetchRel tufRoleKeysReadCode 0x6F4 = some (.store .sb (25 : Fin 32) (22 : Fin 32) 0xFFFFFFFF, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6f8 : fetchRel tufRoleKeysReadCode 0x6F8 = some (.aluImm .add a1 sp 0x55C, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_6fc : fetchRel tufRoleKeysReadCode 0x6FC = some (.aluImm .add a2 x0 0x61, 4) :=
  (fetchRel_chunk rkr_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_700 : fetchRel tufRoleKeysReadCode 0x700 = some (.alu .add a0 x0 (25 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_702 : fetchRel tufRoleKeysReadCode 0x702 = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_706 : fetchRel tufRoleKeysReadCode 0x706 = some (.jalr ra ra 0x7E8, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_70a : fetchRel tufRoleKeysReadCode 0x70A = some (.store .sw sp (26 : Fin 32) 0x550, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_70e : fetchRel tufRoleKeysReadCode 0x70E = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4, 2) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_710 : fetchRel tufRoleKeysReadCode 0x710 = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0x62, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_714 : fetchRel tufRoleKeysReadCode 0x714 = some (.aluImm .add (26 : Fin 32) (26 : Fin 32) 0x1, 2) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_716 : fetchRel tufRoleKeysReadCode 0x716 = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x40, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_71a : fetchRel tufRoleKeysReadCode 0x71A = some (.jal x0 0xFFFFFACC, 2) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_71c : fetchRel tufRoleKeysReadCode 0x71C = some (.load .lbu a1 (23 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_720 : fetchRel tufRoleKeysReadCode 0x720 = some (.aluImm .add a1 a1 0xFFFFFF9B, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_724 : fetchRel tufRoleKeysReadCode 0x724 = some (.branch .bne a1 x0 0xFFFFFF04, 2) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_726 : fetchRel tufRoleKeysReadCode 0x726 = some (.load .lbu a1 (23 : Fin 32) 0x1, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_72a : fetchRel tufRoleKeysReadCode 0x72A = some (.aluImm .add a1 a1 0xFFFFFF9D, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_72e : fetchRel tufRoleKeysReadCode 0x72E = some (.branch .bne a1 x0 0xFFFFFEFA, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_732 : fetchRel tufRoleKeysReadCode 0x732 = some (.load .lbu a1 (23 : Fin 32) 0x2, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_736 : fetchRel tufRoleKeysReadCode 0x736 = some (.aluImm .add a1 a1 0xFFFFFF9C, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_73a : fetchRel tufRoleKeysReadCode 0x73A = some (.branch .bne a1 x0 0xFFFFFEEE, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_73e : fetchRel tufRoleKeysReadCode 0x73E = some (.load .lbu a1 (23 : Fin 32) 0x3, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_742 : fetchRel tufRoleKeysReadCode 0x742 = some (.aluImm .add a1 a1 0xFFFFFF8D, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_746 : fetchRel tufRoleKeysReadCode 0x746 = some (.branch .bne a1 x0 0xFFFFFEE2, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_74a : fetchRel tufRoleKeysReadCode 0x74A = some (.load .lbu a1 (23 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_74e : fetchRel tufRoleKeysReadCode 0x74E = some (.aluImm .add a1 a1 0xFFFFFF9F, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_752 : fetchRel tufRoleKeysReadCode 0x752 = some (.branch .bne a1 x0 0xFFFFFED6, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_756 : fetchRel tufRoleKeysReadCode 0x756 = some (.load .lbu a1 (23 : Fin 32) 0x5, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_75a : fetchRel tufRoleKeysReadCode 0x75A = some (.aluImm .add a1 a1 0xFFFFFFD3, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_75e : fetchRel tufRoleKeysReadCode 0x75E = some (.branch .bne a1 x0 0xFFFFFECA, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_762 : fetchRel tufRoleKeysReadCode 0x762 = some (.load .lbu a1 (23 : Fin 32) 0x6, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_766 : fetchRel tufRoleKeysReadCode 0x766 = some (.aluImm .add a1 a1 0xFFFFFF8D, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_76a : fetchRel tufRoleKeysReadCode 0x76A = some (.branch .bne a1 x0 0xFFFFFEBE, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_76e : fetchRel tufRoleKeysReadCode 0x76E = some (.load .lbu a1 (23 : Fin 32) 0x7, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_772 : fetchRel tufRoleKeysReadCode 0x772 = some (.aluImm .add a1 a1 0xFFFFFF98, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_776 : fetchRel tufRoleKeysReadCode 0x776 = some (.branch .bne a1 x0 0xFFFFFEB2, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_77a : fetchRel tufRoleKeysReadCode 0x77A = some (.load .lbu a1 (23 : Fin 32) 0x8, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_77e : fetchRel tufRoleKeysReadCode 0x77E = some (.aluImm .add a1 a1 0xFFFFFF9F, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_782 : fetchRel tufRoleKeysReadCode 0x782 = some (.branch .bne a1 x0 0xFFFFFEA6, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_786 : fetchRel tufRoleKeysReadCode 0x786 = some (.load .lbu a1 (23 : Fin 32) 0x9, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_78a : fetchRel tufRoleKeysReadCode 0x78A = some (.aluImm .add a1 a1 0xFFFFFFCE, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_78e : fetchRel tufRoleKeysReadCode 0x78E = some (.branch .bne a1 x0 0xFFFFFE9A, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_792 : fetchRel tufRoleKeysReadCode 0x792 = some (.load .lbu a1 (23 : Fin 32) 0xA, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_796 : fetchRel tufRoleKeysReadCode 0x796 = some (.aluImm .add a1 a1 0xFFFFFFD3, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_79a : fetchRel tufRoleKeysReadCode 0x79A = some (.branch .bne a1 x0 0xFFFFFE8E, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_79e : fetchRel tufRoleKeysReadCode 0x79E = some (.load .lbu a1 (23 : Fin 32) 0xB, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7a2 : fetchRel tufRoleKeysReadCode 0x7A2 = some (.aluImm .add a1 a1 0xFFFFFF92, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7a6 : fetchRel tufRoleKeysReadCode 0x7A6 = some (.branch .bne a1 x0 0xFFFFFE82, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7aa : fetchRel tufRoleKeysReadCode 0x7AA = some (.load .lbu a1 (23 : Fin 32) 0xC, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7ae : fetchRel tufRoleKeysReadCode 0x7AE = some (.aluImm .add a1 a1 0xFFFFFF97, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7b2 : fetchRel tufRoleKeysReadCode 0x7B2 = some (.branch .bne a1 x0 0xFFFFFE76, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7b6 : fetchRel tufRoleKeysReadCode 0x7B6 = some (.load .lbu a1 (23 : Fin 32) 0xD, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7ba : fetchRel tufRoleKeysReadCode 0x7BA = some (.aluImm .add a1 a1 0xFFFFFF8D, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7be : fetchRel tufRoleKeysReadCode 0x7BE = some (.branch .bne a1 x0 0xFFFFFE6A, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7c2 : fetchRel tufRoleKeysReadCode 0x7C2 = some (.load .lbu a1 (23 : Fin 32) 0xE, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7c6 : fetchRel tufRoleKeysReadCode 0x7C6 = some (.aluImm .add a1 a1 0xFFFFFF8C, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7ca : fetchRel tufRoleKeysReadCode 0x7CA = some (.branch .bne a1 x0 0xFFFFFE5E, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7ce : fetchRel tufRoleKeysReadCode 0x7CE = some (.load .lbu a1 (23 : Fin 32) 0xF, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7d2 : fetchRel tufRoleKeysReadCode 0x7D2 = some (.aluImm .add a1 a1 0xFFFFFF90, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7d6 : fetchRel tufRoleKeysReadCode 0x7D6 = some (.branch .bne a1 x0 0xFFFFFE52, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7da : fetchRel tufRoleKeysReadCode 0x7DA = some (.load .lbu a1 (23 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7de : fetchRel tufRoleKeysReadCode 0x7DE = some (.aluImm .add a1 a1 0xFFFFFFCE, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7e2 : fetchRel tufRoleKeysReadCode 0x7E2 = some (.branch .bne a1 x0 0xFFFFFE46, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7e6 : fetchRel tufRoleKeysReadCode 0x7E6 = some (.load .lbu a1 (23 : Fin 32) 0x11, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7ea : fetchRel tufRoleKeysReadCode 0x7EA = some (.aluImm .add a1 a1 0xFFFFFFCB, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7ee : fetchRel tufRoleKeysReadCode 0x7EE = some (.branch .bne a1 x0 0xFFFFFE3A, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7f2 : fetchRel tufRoleKeysReadCode 0x7F2 = some (.load .lbu a1 (23 : Fin 32) 0x12, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7f6 : fetchRel tufRoleKeysReadCode 0x7F6 = some (.aluImm .add a1 a1 0xFFFFFFCA, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7fa : fetchRel tufRoleKeysReadCode 0x7FA = some (.jal x0 0xFFFFFCEA, 2) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_7fc : fetchRel tufRoleKeysReadCode 0x7FC = some (.load .lbu a1 (23 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk rkr_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_800 : fetchRel tufRoleKeysReadCode 0x800 = some (.aluImm .add a1 a1 0xFFFFFF9B, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_804 : fetchRel tufRoleKeysReadCode 0x804 = some (.branch .bne a1 x0 0xFFFFFE24, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_808 : fetchRel tufRoleKeysReadCode 0x808 = some (.load .lbu a1 (23 : Fin 32) 0x1, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_80c : fetchRel tufRoleKeysReadCode 0x80C = some (.aluImm .add a1 a1 0xFFFFFF9D, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_810 : fetchRel tufRoleKeysReadCode 0x810 = some (.branch .bne a1 x0 0xFFFFFE18, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_814 : fetchRel tufRoleKeysReadCode 0x814 = some (.load .lbu a1 (23 : Fin 32) 0x2, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_818 : fetchRel tufRoleKeysReadCode 0x818 = some (.aluImm .add a1 a1 0xFFFFFF9C, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_81c : fetchRel tufRoleKeysReadCode 0x81C = some (.branch .bne a1 x0 0xFFFFFE0C, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_820 : fetchRel tufRoleKeysReadCode 0x820 = some (.load .lbu a1 (23 : Fin 32) 0x3, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_824 : fetchRel tufRoleKeysReadCode 0x824 = some (.aluImm .add a1 a1 0xFFFFFF8D, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_828 : fetchRel tufRoleKeysReadCode 0x828 = some (.branch .bne a1 x0 0xFFFFFE00, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_82c : fetchRel tufRoleKeysReadCode 0x82C = some (.load .lbu a1 (23 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_830 : fetchRel tufRoleKeysReadCode 0x830 = some (.aluImm .add a1 a1 0xFFFFFF9F, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_834 : fetchRel tufRoleKeysReadCode 0x834 = some (.branch .bne a1 x0 0xFFFFFDF4, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_838 : fetchRel tufRoleKeysReadCode 0x838 = some (.load .lbu a1 (23 : Fin 32) 0x5, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_83c : fetchRel tufRoleKeysReadCode 0x83C = some (.aluImm .add a1 a1 0xFFFFFFD3, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_840 : fetchRel tufRoleKeysReadCode 0x840 = some (.branch .bne a1 x0 0xFFFFFDE8, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_844 : fetchRel tufRoleKeysReadCode 0x844 = some (.load .lbu a1 (23 : Fin 32) 0x6, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_848 : fetchRel tufRoleKeysReadCode 0x848 = some (.aluImm .add a1 a1 0xFFFFFF8D, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_84c : fetchRel tufRoleKeysReadCode 0x84C = some (.branch .bne a1 x0 0xFFFFFDDC, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_850 : fetchRel tufRoleKeysReadCode 0x850 = some (.load .lbu a1 (23 : Fin 32) 0x7, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_854 : fetchRel tufRoleKeysReadCode 0x854 = some (.aluImm .add a1 a1 0xFFFFFF98, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_858 : fetchRel tufRoleKeysReadCode 0x858 = some (.branch .bne a1 x0 0xFFFFFDD0, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_85c : fetchRel tufRoleKeysReadCode 0x85C = some (.load .lbu a1 (23 : Fin 32) 0x8, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_860 : fetchRel tufRoleKeysReadCode 0x860 = some (.aluImm .add a1 a1 0xFFFFFF9F, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_864 : fetchRel tufRoleKeysReadCode 0x864 = some (.branch .bne a1 x0 0xFFFFFDC4, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_868 : fetchRel tufRoleKeysReadCode 0x868 = some (.load .lbu a1 (23 : Fin 32) 0x9, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_86c : fetchRel tufRoleKeysReadCode 0x86C = some (.aluImm .add a1 a1 0xFFFFFFCE, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_870 : fetchRel tufRoleKeysReadCode 0x870 = some (.branch .bne a1 x0 0xFFFFFDB8, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_874 : fetchRel tufRoleKeysReadCode 0x874 = some (.load .lbu a1 (23 : Fin 32) 0xA, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_878 : fetchRel tufRoleKeysReadCode 0x878 = some (.aluImm .add a1 a1 0xFFFFFFD3, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_87c : fetchRel tufRoleKeysReadCode 0x87C = some (.branch .bne a1 x0 0xFFFFFDAC, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_880 : fetchRel tufRoleKeysReadCode 0x880 = some (.load .lbu a1 (23 : Fin 32) 0xB, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_884 : fetchRel tufRoleKeysReadCode 0x884 = some (.aluImm .add a1 a1 0xFFFFFF92, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_888 : fetchRel tufRoleKeysReadCode 0x888 = some (.branch .bne a1 x0 0xFFFFFDA0, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_88c : fetchRel tufRoleKeysReadCode 0x88C = some (.load .lbu a1 (23 : Fin 32) 0xC, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_890 : fetchRel tufRoleKeysReadCode 0x890 = some (.aluImm .add a1 a1 0xFFFFFF97, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_894 : fetchRel tufRoleKeysReadCode 0x894 = some (.branch .bne a1 x0 0xFFFFFD94, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_898 : fetchRel tufRoleKeysReadCode 0x898 = some (.load .lbu a1 (23 : Fin 32) 0xD, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_89c : fetchRel tufRoleKeysReadCode 0x89C = some (.aluImm .add a1 a1 0xFFFFFF8D, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8a0 : fetchRel tufRoleKeysReadCode 0x8A0 = some (.branch .bne a1 x0 0xFFFFFD88, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8a4 : fetchRel tufRoleKeysReadCode 0x8A4 = some (.load .lbu a1 (23 : Fin 32) 0xE, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8a8 : fetchRel tufRoleKeysReadCode 0x8A8 = some (.aluImm .add a1 a1 0xFFFFFF8C, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8ac : fetchRel tufRoleKeysReadCode 0x8AC = some (.branch .bne a1 x0 0xFFFFFD7C, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8b0 : fetchRel tufRoleKeysReadCode 0x8B0 = some (.load .lbu a1 (23 : Fin 32) 0xF, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8b4 : fetchRel tufRoleKeysReadCode 0x8B4 = some (.aluImm .add a1 a1 0xFFFFFF90, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8b8 : fetchRel tufRoleKeysReadCode 0x8B8 = some (.branch .bne a1 x0 0xFFFFFD70, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8bc : fetchRel tufRoleKeysReadCode 0x8BC = some (.load .lbu a1 (23 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8c0 : fetchRel tufRoleKeysReadCode 0x8C0 = some (.aluImm .add a1 a1 0xFFFFFFCD, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8c4 : fetchRel tufRoleKeysReadCode 0x8C4 = some (.branch .bne a1 x0 0xFFFFFD64, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8c8 : fetchRel tufRoleKeysReadCode 0x8C8 = some (.load .lbu a1 (23 : Fin 32) 0x11, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8cc : fetchRel tufRoleKeysReadCode 0x8CC = some (.aluImm .add a1 a1 0xFFFFFFC8, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8d0 : fetchRel tufRoleKeysReadCode 0x8D0 = some (.branch .bne a1 x0 0xFFFFFD58, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8d4 : fetchRel tufRoleKeysReadCode 0x8D4 = some (.load .lbu a1 (23 : Fin 32) 0x12, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8d8 : fetchRel tufRoleKeysReadCode 0x8D8 = some (.aluImm .add a1 a1 0xFFFFFFCC, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8dc : fetchRel tufRoleKeysReadCode 0x8DC = some (.jal x0 0xFFFFFDB2, 2) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8de : fetchRel tufRoleKeysReadCode 0x8DE = some (.load .lbu a0 sp 0x1C, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8e2 : fetchRel tufRoleKeysReadCode 0x8E2 = some (.jal x0 0x6, 2) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8e4 : fetchRel tufRoleKeysReadCode 0x8E4 = some (.load .lbu a0 sp 0x760, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8e8 : fetchRel tufRoleKeysReadCode 0x8E8 = some (.aluImm .add a1 x0 0xFFFFFFFE, 2) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8ea : fetchRel tufRoleKeysReadCode 0x8EA = some (.store .sb (27 : Fin 32) a1 0x0, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8ee : fetchRel tufRoleKeysReadCode 0x8EE = some (.store .sb (27 : Fin 32) a0 0x1, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8f2 : fetchRel tufRoleKeysReadCode 0x8F2 = some (.aluImm .add sp sp 0x2D0, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8f6 : fetchRel tufRoleKeysReadCode 0x8F6 = some (.aluImm .add a0 sp 0x780, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8fa : fetchRel tufRoleKeysReadCode 0x8FA = some (.load .lw ra a0 0x6C, 4) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_8fe : fetchRel tufRoleKeysReadCode 0x8FE = some (.load .lw (8 : Fin 32) a0 0x68, 2) :=
  (fetchRel_chunk rkr_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_900 : fetchRel tufRoleKeysReadCode 0x900 = some (.load .lw (9 : Fin 32) a0 0x64, 2) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_902 : fetchRel tufRoleKeysReadCode 0x902 = some (.load .lw (18 : Fin 32) a0 0x60, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_906 : fetchRel tufRoleKeysReadCode 0x906 = some (.load .lw (19 : Fin 32) a0 0x5C, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_90a : fetchRel tufRoleKeysReadCode 0x90A = some (.load .lw (20 : Fin 32) a0 0x58, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_90e : fetchRel tufRoleKeysReadCode 0x90E = some (.load .lw (21 : Fin 32) a0 0x54, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_912 : fetchRel tufRoleKeysReadCode 0x912 = some (.load .lw (22 : Fin 32) a0 0x50, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_916 : fetchRel tufRoleKeysReadCode 0x916 = some (.load .lw (23 : Fin 32) a0 0x4C, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_91a : fetchRel tufRoleKeysReadCode 0x91A = some (.load .lw (24 : Fin 32) a0 0x48, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_91e : fetchRel tufRoleKeysReadCode 0x91E = some (.load .lw (25 : Fin 32) a0 0x44, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_922 : fetchRel tufRoleKeysReadCode 0x922 = some (.load .lw (26 : Fin 32) a0 0x40, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_926 : fetchRel tufRoleKeysReadCode 0x926 = some (.load .lw (27 : Fin 32) a0 0x3C, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_92a : fetchRel tufRoleKeysReadCode 0x92A = some (.aluImm .add sp sp 0x7F0, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_92e : fetchRel tufRoleKeysReadCode 0x92E = some (.jalr x0 ra 0x0, 2) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_930 : fetchRel tufRoleKeysReadCode 0x930 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_932 : fetchRel tufRoleKeysReadCode 0x932 = some (.aluImm .add a0 a0 0x1FE, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_936 : fetchRel tufRoleKeysReadCode 0x936 = some (.store .sh (27 : Fin 32) a0 0x0, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_93a : fetchRel tufRoleKeysReadCode 0x93A = some (.jal x0 0xFFFFFFB8, 2) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_93c : fetchRel tufRoleKeysReadCode 0x93C = some (.load .lbu a0 sp 0x560, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_940 : fetchRel tufRoleKeysReadCode 0x940 = some (.jal x0 0xFFFFFFA8, 2) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_942 : fetchRel tufRoleKeysReadCode 0x942 = some (.aluImm .add a0 x0 0xFFFFFFFE, 2) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_944 : fetchRel tufRoleKeysReadCode 0x944 = some (.store .sb (27 : Fin 32) a0 0x0, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_948 : fetchRel tufRoleKeysReadCode 0x948 = some (.store .sb (27 : Fin 32) (8 : Fin 32) 0x1, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_94c : fetchRel tufRoleKeysReadCode 0x94C = some (.jal x0 0xFFFFFFA6, 2) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_94e : fetchRel tufRoleKeysReadCode 0x94E = some (.load .lbu a0 sp 0x75D, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_952 : fetchRel tufRoleKeysReadCode 0x952 = some (.jal x0 0xFFFFFF96, 2) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_954 : fetchRel tufRoleKeysReadCode 0x954 = some (.aluImm .add a1 sp 0x18, 2) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_956 : fetchRel tufRoleKeysReadCode 0x956 = some (.aluImm .add a2 x0 0x540, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_95a : fetchRel tufRoleKeysReadCode 0x95A = some (.alu .add a0 x0 (27 : Fin 32), 2) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_95c : fetchRel tufRoleKeysReadCode 0x95C = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_960 : fetchRel tufRoleKeysReadCode 0x960 = some (.jalr ra ra 0x58E, 4) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem rkr_at_964 : fetchRel tufRoleKeysReadCode 0x964 = some (.jal x0 0xFFFFFF8E, 2) :=
  (fetchRel_chunk rkr_c9_ok (by decide) (.inr (by decide))).trans (by decide)

end C3.RV32
