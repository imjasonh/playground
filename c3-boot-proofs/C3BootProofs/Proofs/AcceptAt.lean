import C3BootProofs.Proof.FetchChunk
import C3BootProofs.Image.Bootloader
import C3BootProofs.Proofs.ReaderArray

/-! Fetch lemmas for `c3_bootloader::boot_main::{closure#0}` (`bootMainClosure0Code`). -/

namespace C3.RV32.Ac

open C3.Image

/-- Where `c3_bootloader::boot_main::{closure#0}` is in the image. -/
abbrev AC : Word := BitVec.ofNat 32 bootMainClosure0Address

set_option maxRecDepth 20000

/-- Bytes 0x0 to 0x104 of `bootMainClosure0Code`. -/
def ac_c0 : List Nat :=
  [0x11, 0x71, 0x86, 0xdf, 0xa2, 0xdd, 0xa6, 0xdb, 0xca, 0xd9, 0xce, 0xd7,
    0xd2, 0xd5, 0xd6, 0xd3, 0xda, 0xd1, 0xde, 0xcf, 0xe2, 0xcd, 0xe6, 0xcb,
    0xea, 0xc9, 0xee, 0xc7, 0x09, 0x67, 0x13, 0x07, 0x07, 0xf2, 0x33, 0x01,
    0xe1, 0x40, 0x36, 0x84, 0xb2, 0x8a, 0x2e, 0x8d, 0xaa, 0x89, 0x37, 0x0c,
    0x21, 0x00, 0x99, 0xe2, 0x37, 0x0c, 0x03, 0x00, 0xa8, 0x00, 0x13, 0x06,
    0x00, 0x02, 0x81, 0x45, 0x97, 0x60, 0x01, 0x00, 0xe7, 0x80, 0xe0, 0x66,
    0xac, 0x00, 0x13, 0x06, 0x00, 0x02, 0x62, 0x85, 0x97, 0x70, 0x01, 0x00,
    0xe7, 0x80, 0x40, 0xb8, 0x63, 0x09, 0x05, 0x10, 0x05, 0x65, 0x13, 0x05,
    0x05, 0x31, 0xb3, 0x04, 0xa1, 0x00, 0x09, 0x65, 0x13, 0x05, 0x05, 0x87,
    0x0a, 0x95, 0xac, 0x00, 0x97, 0xd0, 0x00, 0x00, 0xe7, 0x80, 0xe0, 0x23,
    0x03, 0xc5, 0x04, 0x56, 0x7d, 0xe5, 0x03, 0xa5, 0x44, 0x56, 0xb3, 0x05,
    0x85, 0x01, 0xae, 0xc2, 0x63, 0xe1, 0xa5, 0x0e, 0x83, 0xad, 0x84, 0x56,
    0x13, 0x05, 0x40, 0x11, 0x6e, 0x8b, 0x63, 0xe4, 0xad, 0x00, 0x13, 0x0b,
    0x40, 0x11, 0x03, 0xa9, 0xc4, 0x56, 0x03, 0xaa, 0x04, 0x57, 0x83, 0xab,
    0x44, 0x57, 0x83, 0xa4, 0x84, 0x57, 0x31, 0x65, 0x13, 0x05, 0x05, 0x84,
    0xb3, 0x8c, 0xaa, 0x00, 0x16, 0x45, 0xe6, 0x85, 0x5a, 0x86, 0x97, 0x70,
    0x01, 0x00, 0xe7, 0x80, 0x60, 0xb1, 0x55, 0xc1, 0x5e, 0xd8, 0x52, 0xdc,
    0x22, 0xde, 0xce, 0xc0, 0xa3, 0x03, 0x01, 0x0a, 0x28, 0x11, 0xb7, 0x45,
    0xcc, 0x3f, 0x93, 0x85, 0x85, 0x11, 0x13, 0x06, 0x00, 0x02, 0x97, 0x60,
    0x01, 0x00, 0xe7, 0x80, 0x40, 0x63, 0x81, 0x49, 0x82, 0xc5, 0x82, 0xc7,
    0x11, 0x6a, 0x95, 0x4b, 0x56, 0xda, 0x56, 0x9a, 0xae, 0x0b, 0x16, 0x44,
    0x63, 0x8c, 0x0d, 0x02, 0xb3, 0x8a, 0x3d, 0x41]
theorem ac_c0_ok : ac_c0 <+: List.drop 0 bootMainClosure0Code := by decide

/-- Bytes 0x100 to 0x204 of `bootMainClosure0Code`. -/
def ac_c1 : List Nat :=
  [0xb3, 0x8a, 0x3d, 0x41, 0x63, 0xe3, 0x7a, 0x01, 0xde, 0x8a, 0x33, 0x85,
    0x89, 0x00, 0x63, 0x6c, 0x35, 0x05, 0xd2, 0x85, 0x56, 0x86, 0x97, 0x70,
    0x01, 0x00, 0xe7, 0x80, 0xe0, 0xab, 0x21, 0xc5, 0xa8, 0x10, 0xd2, 0x85,
    0x56, 0x86, 0x97, 0x70, 0x00, 0x00, 0xe7, 0x80, 0x20, 0xa5, 0xd6, 0x99,
    0xe3, 0xe8, 0xb9, 0xfd, 0xc8, 0x09, 0xac, 0x10, 0x97, 0x70, 0x00, 0x00,
    0xe7, 0x80, 0x00, 0x8b, 0x11, 0x65, 0x62, 0x54, 0x63, 0x61, 0x85, 0x02,
    0x33, 0x05, 0x89, 0x01, 0x63, 0x6d, 0x25, 0x01, 0xd2, 0x55, 0x22, 0x86,
    0x97, 0x70, 0x01, 0x00, 0xe7, 0x80, 0x00, 0xa8, 0x09, 0xc5, 0x42, 0x55,
    0x2a, 0x9c, 0x63, 0x74, 0xac, 0x04, 0x86, 0x49, 0x72, 0x54, 0x93, 0x05,
    0xa4, 0x00, 0x37, 0x65, 0xcc, 0x3f, 0x13, 0x05, 0x05, 0x6c, 0x97, 0x00,
    0xc6, 0xff, 0xe7, 0x80, 0x40, 0xe2, 0x7d, 0x55, 0x23, 0x86, 0xa9, 0x00,
    0x09, 0x65, 0x13, 0x05, 0x05, 0xf2, 0x2a, 0x91, 0xfe, 0x50, 0x6e, 0x54,
    0xde, 0x54, 0x4e, 0x59, 0xbe, 0x59, 0x2e, 0x5a, 0x9e, 0x5a, 0x0e, 0x5b,
    0xfe, 0x4b, 0x6e, 0x4c, 0xde, 0x4c, 0x4e, 0x4d, 0xbe, 0x4d, 0x11, 0x61,
    0x82, 0x80, 0xe6, 0xdb, 0xda, 0xdd, 0x23, 0x22, 0xb1, 0x11, 0x28, 0x02,
    0xcc, 0x09, 0x13, 0x06, 0x00, 0x02, 0x97, 0x60, 0x01, 0x00, 0xe7, 0x80,
    0xc0, 0x55, 0x52, 0x55, 0xaa, 0xdf, 0x08, 0x02, 0x00, 0xc1, 0x23, 0x24,
    0x85, 0x03, 0x44, 0xd5, 0xa6, 0x8b, 0x04, 0xd9, 0x09, 0x65, 0x13, 0x05,
    0x05, 0x87, 0x0a, 0x95, 0xe6, 0x85, 0x5a, 0x86, 0xee, 0x86, 0x97, 0xd0,
    0x00, 0x00, 0xe7, 0x80, 0xe0, 0x9b, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31,
    0xb3, 0x04, 0xa1, 0x00, 0x83, 0xcc, 0xc4, 0x56, 0x83, 0xca, 0x04, 0x56,
    0x13, 0x85, 0x1c, 0xf0, 0x63, 0x0b, 0x05, 0x5c]
theorem ac_c1_ok : ac_c1 <+: List.drop 256 bootMainClosure0Code := by decide

/-- Bytes 0x200 to 0x304 of `bootMainClosure0Code`. -/
def ac_c2 : List Nat :=
  [0x63, 0x0b, 0x05, 0x5c, 0x83, 0xc8, 0x94, 0x56, 0x83, 0xc5, 0xa4, 0x56,
    0x03, 0xc8, 0xb4, 0x56, 0x83, 0xc2, 0x54, 0x56, 0x03, 0xc3, 0x64, 0x56,
    0x83, 0xc7, 0x14, 0x56, 0x03, 0xc4, 0x24, 0x56, 0x03, 0xc6, 0x34, 0x56,
    0x03, 0xc5, 0x44, 0x56, 0xa2, 0x05, 0xb3, 0xe8, 0x15, 0x01, 0x83, 0xc6,
    0x74, 0x56, 0x03, 0xc7, 0x84, 0x56, 0x22, 0x03, 0xb3, 0x65, 0x53, 0x00,
    0x22, 0x04, 0x42, 0x06, 0x62, 0x05, 0xc1, 0x8f, 0x51, 0x8d, 0xc2, 0x06,
    0x62, 0x07, 0xd9, 0x8e, 0x5d, 0x8d, 0xd5, 0x8d, 0x23, 0x2c, 0xa1, 0x22,
    0x23, 0x2e, 0xb1, 0x22, 0x23, 0x10, 0x11, 0x25, 0x23, 0x01, 0x01, 0x25,
    0x09, 0x65, 0x13, 0x05, 0xd5, 0x87, 0xb3, 0x05, 0xa1, 0x00, 0x13, 0x05,
    0x91, 0x13, 0x13, 0x06, 0xf0, 0x0f, 0x97, 0x60, 0x01, 0x00, 0xe7, 0x80,
    0x40, 0x4a, 0x03, 0xc5, 0xe4, 0x66, 0x83, 0xc5, 0xd4, 0x66, 0x83, 0xcd,
    0xc4, 0x66, 0x03, 0xc6, 0xf4, 0x66, 0x22, 0x05, 0x4d, 0x8d, 0x93, 0x75,
    0xfd, 0x0f, 0x23, 0x1b, 0xa1, 0x12, 0x23, 0x0c, 0xc1, 0x12, 0x63, 0xf6,
    0xbd, 0x00, 0xc9, 0x4a, 0x86, 0x49, 0x72, 0x54, 0xb9, 0xab, 0x37, 0x05,
    0x06, 0x00, 0x63, 0x74, 0x75, 0x01, 0x15, 0x45, 0x51, 0xa2, 0xde, 0x85,
    0x09, 0x65, 0x13, 0x05, 0x05, 0xdb, 0x33, 0x04, 0xa1, 0x00, 0x01, 0x45,
    0x08, 0xc0, 0x48, 0xc0, 0x01, 0x46, 0x09, 0x65, 0x13, 0x05, 0x05, 0xdb,
    0xb3, 0x06, 0xa1, 0x00, 0x21, 0x47, 0x62, 0x85, 0x89, 0x67, 0x93, 0x87,
    0x07, 0xdb, 0xb3, 0x09, 0xf1, 0x00, 0xa1, 0x44, 0x97, 0x70, 0x01, 0x00,
    0xe7, 0x80, 0xc0, 0xa4, 0x63, 0x04, 0x05, 0x14, 0x05, 0x65, 0x13, 0x05,
    0x05, 0x31, 0x33, 0x0d, 0xa1, 0x00, 0x23, 0x26, 0x34, 0x01, 0x04, 0xc8,
    0x23, 0x2a, 0x04, 0x00, 0xb7, 0x35, 0x54, 0x55]
theorem ac_c2_ok : ac_c2 <+: List.drop 512 bootMainClosure0Code := by decide

/-- Bytes 0x300 to 0x404 of `bootMainClosure0Code`. -/
def ac_c3 : List Nat :=
  [0xb7, 0x35, 0x54, 0x55, 0x93, 0x85, 0x35, 0x34, 0x09, 0x65, 0x13, 0x05,
    0xc5, 0xdb, 0x0a, 0x95, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80, 0x80, 0xe1,
    0x93, 0x75, 0xf5, 0x0f, 0x93, 0x85, 0x15, 0xf0, 0x63, 0x9a, 0x05, 0x10,
    0x09, 0x65, 0x13, 0x05, 0xc5, 0xdb, 0x0a, 0x95, 0x97, 0xa0, 0x00, 0x00,
    0xe7, 0x80, 0xc0, 0xcf, 0x93, 0x75, 0x15, 0x00, 0x99, 0xc1, 0x21, 0x81,
    0xe5, 0xa8, 0x41, 0x81, 0x89, 0x45, 0x63, 0x1d, 0xb5, 0x0e, 0x09, 0x65,
    0x13, 0x05, 0xc5, 0xdb, 0x0a, 0x95, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80,
    0xa0, 0xcd, 0x93, 0x75, 0x15, 0x00, 0xe5, 0xf1, 0x13, 0x59, 0x05, 0x01,
    0x13, 0x05, 0x00, 0x04, 0xe3, 0x65, 0x25, 0xf5, 0x09, 0x65, 0x13, 0x05,
    0x85, 0xdc, 0x0a, 0x95, 0x13, 0x06, 0x80, 0x10, 0x81, 0x45, 0x97, 0x60,
    0x01, 0x00, 0xe7, 0x80, 0x80, 0x33, 0xa1, 0x45, 0x01, 0x45, 0x63, 0xe9,
    0xbb, 0x0a, 0x13, 0x14, 0x29, 0x00, 0x21, 0x04, 0x21, 0x46, 0x09, 0x65,
    0x13, 0x05, 0x85, 0xdc, 0xb3, 0x06, 0xa1, 0x00, 0x62, 0x85, 0xde, 0x85,
    0x22, 0x87, 0x89, 0x67, 0x93, 0x87, 0x87, 0xdc, 0xb3, 0x09, 0xf1, 0x00,
    0x97, 0x70, 0x01, 0x00, 0xe7, 0x80, 0x40, 0x98, 0x41, 0xc1, 0x35, 0x45,
    0x2e, 0x05, 0xd2, 0x55, 0x2e, 0x95, 0x2a, 0xd8, 0x09, 0x65, 0x13, 0x05,
    0x05, 0xed, 0x0a, 0x95, 0x13, 0x06, 0x80, 0x10, 0x81, 0x45, 0x89, 0x66,
    0x93, 0x86, 0x06, 0xed, 0xb3, 0x04, 0xd1, 0x00, 0x97, 0x60, 0x01, 0x00,
    0xe7, 0x80, 0xa0, 0x2d, 0x09, 0x65, 0x13, 0x05, 0x05, 0xdb, 0x0a, 0x95,
    0x23, 0x24, 0x25, 0x23, 0x23, 0x26, 0x35, 0x23, 0x23, 0x28, 0x85, 0x22,
    0x23, 0x2a, 0x05, 0x22, 0x75, 0x75, 0x6d, 0x5b, 0x93, 0x09, 0xf5, 0x7f,
    0x2e, 0x0b, 0x29, 0xc0, 0x09, 0x65, 0x13, 0x05]
theorem ac_c3_ok : ac_c3 <+: List.drop 768 bootMainClosure0Code := by decide

/-- Bytes 0x400 to 0x504 of `bootMainClosure0Code`. -/
def ac_c4 : List Nat :=
  [0x09, 0x65, 0x13, 0x05, 0x05, 0x86, 0x0a, 0x95, 0x89, 0x65, 0x93, 0x85,
    0xc5, 0xfd, 0x8a, 0x95, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80, 0x20, 0xc8,
    0x03, 0x45, 0x0d, 0x55, 0x39, 0xe1, 0x03, 0x25, 0x4d, 0x55, 0x88, 0xc0,
    0x91, 0x04, 0x4e, 0x95, 0x71, 0x14, 0xe3, 0x62, 0x65, 0xe9, 0xc1, 0xbf,
    0x13, 0x05, 0x60, 0x02, 0x86, 0x49, 0x72, 0x54, 0xaa, 0x8a, 0x45, 0xa6,
    0x0d, 0x45, 0xdd, 0xbf, 0x13, 0x06, 0x19, 0x00, 0x09, 0x65, 0x13, 0x05,
    0x05, 0x86, 0x0a, 0x95, 0x89, 0x65, 0x93, 0x85, 0x05, 0xed, 0x8a, 0x95,
    0x97, 0xb0, 0x00, 0x00, 0xe7, 0x80, 0xc0, 0xeb, 0x03, 0x45, 0x0d, 0x55,
    0x01, 0xc5, 0x03, 0x45, 0x1d, 0x55, 0xf9, 0xb7, 0x05, 0x65, 0x13, 0x05,
    0x05, 0x31, 0xb3, 0x05, 0xa1, 0x00, 0x03, 0xa5, 0x45, 0x55, 0x05, 0x66,
    0x13, 0x06, 0x06, 0x31, 0xb3, 0x04, 0xc1, 0x00, 0x83, 0xa5, 0x85, 0x55,
    0x2e, 0x95, 0x63, 0x74, 0xb5, 0x00, 0x19, 0x45, 0x65, 0xb7, 0x63, 0xf4,
    0xab, 0x00, 0x01, 0x45, 0x45, 0xb7, 0x63, 0x74, 0x75, 0x01, 0x05, 0x45,
    0x61, 0xbf, 0x09, 0x65, 0x13, 0x05, 0x25, 0x87, 0x33, 0x09, 0xa1, 0x00,
    0x09, 0x65, 0x13, 0x05, 0x05, 0xed, 0xb3, 0x05, 0xa1, 0x00, 0x13, 0x06,
    0xc0, 0x10, 0x4a, 0x85, 0x97, 0x60, 0x01, 0x00, 0xe7, 0x80, 0xe0, 0x25,
    0x13, 0x04, 0x21, 0x35, 0x13, 0x06, 0xc0, 0x10, 0x22, 0x85, 0xca, 0x85,
    0x97, 0x60, 0x01, 0x00, 0xe7, 0x80, 0xa0, 0x24, 0xc8, 0x04, 0x13, 0x06,
    0xc0, 0x10, 0xa2, 0x85, 0x97, 0x60, 0x01, 0x00, 0xe7, 0x80, 0xa0, 0x23,
    0x03, 0x25, 0xc1, 0x34, 0x2a, 0xce, 0xb7, 0x55, 0xcc, 0x3f, 0x93, 0x85,
    0x95, 0x30, 0x05, 0x66, 0x13, 0x06, 0x86, 0x31, 0x09, 0x65, 0x13, 0x05,
    0x05, 0x87, 0x0a, 0x95, 0x97, 0xc0, 0x00, 0x00]
theorem ac_c4_ok : ac_c4 <+: List.drop 1024 bootMainClosure0Code := by decide

/-- Bytes 0x500 to 0x604 of `bootMainClosure0Code`. -/
def ac_c5 : List Nat :=
  [0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0x80, 0x29, 0x03, 0xa4, 0x04, 0x56,
    0x63, 0x0b, 0x04, 0x26, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0xb3, 0x09,
    0xa1, 0x00, 0x93, 0x85, 0x09, 0x50, 0xe4, 0x51, 0xa8, 0x59, 0x2a, 0xd2,
    0xe8, 0x59, 0x2a, 0xd0, 0xb7, 0x46, 0xcc, 0x3f, 0x93, 0x86, 0xe6, 0x76,
    0x05, 0x65, 0x13, 0x05, 0x05, 0x32, 0x0a, 0x95, 0x11, 0x47, 0xa2, 0x85,
    0x26, 0x86, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80, 0xe0, 0x2e, 0xb7, 0x46,
    0xcc, 0x3f, 0x93, 0x86, 0x06, 0x02, 0x13, 0x05, 0xf1, 0x7f, 0x13, 0x05,
    0x15, 0x5d, 0x1d, 0x47, 0xa2, 0x85, 0x26, 0x86, 0x97, 0xa0, 0x00, 0x00,
    0xe7, 0x80, 0x00, 0x2d, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95,
    0xa2, 0x85, 0x26, 0x86, 0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0xe0, 0x5b,
    0x02, 0xd6, 0x03, 0xc5, 0x09, 0x01, 0x2a, 0xd4, 0x03, 0xcb, 0x19, 0x01,
    0x32, 0x55, 0xf2, 0x45, 0x63, 0x80, 0xa5, 0x20, 0x88, 0x0e, 0xd4, 0x04,
    0xe2, 0x85, 0x5e, 0x86, 0x32, 0x57, 0xd2, 0x87, 0x97, 0x00, 0x00, 0x00,
    0xe7, 0x80, 0x00, 0x9f, 0x83, 0x25, 0x01, 0x35, 0x63, 0x86, 0x05, 0x20,
    0x03, 0x26, 0x41, 0x35, 0x09, 0x65, 0x13, 0x05, 0x05, 0x87, 0x0a, 0x95,
    0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0x40, 0x1e, 0x05, 0x65, 0x13, 0x05,
    0x05, 0x31, 0x0a, 0x95, 0x03, 0x24, 0x05, 0x56, 0x63, 0x07, 0x04, 0x1e,
    0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x33, 0x06, 0xa1, 0x00, 0x93, 0x06,
    0x06, 0x50, 0xe4, 0x52, 0xa8, 0x56, 0xec, 0x56, 0xb8, 0x5a, 0xfc, 0x5a,
    0x12, 0x56, 0x82, 0x56, 0x75, 0x8e, 0x89, 0x66, 0x93, 0x86, 0x06, 0xdb,
    0x8a, 0x96, 0x23, 0xa0, 0x86, 0x12, 0x23, 0xa2, 0x96, 0x12, 0x23, 0xa4,
    0xa6, 0x12, 0x13, 0x85, 0x06, 0x10, 0x4c, 0xd5]
theorem ac_c5_ok : ac_c5 <+: List.drop 1280 bootMainClosure0Code := by decide

/-- Bytes 0x600 to 0x704 of `bootMainClosure0Code`. -/
def ac_c6 : List Nat :=
  [0x06, 0x10, 0x4c, 0xd5, 0x18, 0xd9, 0x5c, 0xd9, 0x13, 0x05, 0x20, 0x02,
    0xfd, 0x55, 0x63, 0x03, 0xb6, 0x1c, 0x3a, 0x8d, 0xbe, 0x89, 0x92, 0x55,
    0x85, 0x05, 0x13, 0xb6, 0x15, 0x00, 0x82, 0x56, 0x36, 0x96, 0xb9, 0x8d,
    0x3d, 0x8e, 0xd1, 0x8d, 0x63, 0x96, 0x05, 0x1a, 0x22, 0x55, 0x13, 0x05,
    0x25, 0xf0, 0x63, 0x00, 0x05, 0x1a, 0x26, 0x89, 0x13, 0x06, 0xe0, 0x53,
    0x09, 0x65, 0x13, 0x05, 0x25, 0x87, 0x0a, 0x95, 0x85, 0x65, 0x93, 0x85,
    0x25, 0x32, 0x8a, 0x95, 0x97, 0x60, 0x01, 0x00, 0xe7, 0x80, 0xa0, 0x0c,
    0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0xa2, 0x55, 0x23, 0x00,
    0xb5, 0x56, 0xa3, 0x00, 0x65, 0x57, 0x09, 0x65, 0x13, 0x05, 0x05, 0x87,
    0x0a, 0x95, 0x89, 0x65, 0x93, 0x85, 0x05, 0xed, 0x8a, 0x95, 0x97, 0xa0,
    0x00, 0x00, 0xe7, 0x80, 0x40, 0xb0, 0x05, 0x89, 0x2e, 0x8b, 0x63, 0x18,
    0x05, 0x14, 0x93, 0x74, 0x1b, 0x00, 0x63, 0x8d, 0x04, 0x12, 0x09, 0x65,
    0x13, 0x05, 0x05, 0x87, 0x0a, 0x95, 0x11, 0x47, 0xa2, 0x85, 0x4a, 0x86,
    0xb7, 0x46, 0xcc, 0x3f, 0x93, 0x86, 0xe6, 0x76, 0x97, 0xa0, 0x00, 0x00,
    0xe7, 0x80, 0x80, 0x18, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95,
    0x83, 0x45, 0x05, 0x56, 0x03, 0x4b, 0x15, 0x56, 0x2e, 0xd4, 0x13, 0x85,
    0x25, 0xf0, 0x63, 0x08, 0x05, 0x10, 0x13, 0x05, 0xf1, 0x7f, 0x13, 0x05,
    0x15, 0x09, 0x13, 0x06, 0xe0, 0x53, 0x89, 0x65, 0x93, 0x85, 0x25, 0x87,
    0x8a, 0x95, 0x97, 0x60, 0x01, 0x00, 0xe7, 0x80, 0xc0, 0x03, 0x22, 0x55,
    0x23, 0x08, 0xa1, 0x34, 0xa3, 0x08, 0x61, 0x35, 0x93, 0x05, 0xf1, 0x7f,
    0x93, 0x85, 0x15, 0x09, 0x13, 0x06, 0xe0, 0x53, 0x13, 0x05, 0x21, 0x35,
    0x97, 0x60, 0x01, 0x00, 0xe7, 0x80, 0xa0, 0x01]
theorem ac_c6_ok : ac_c6 <+: List.drop 1536 bootMainClosure0Code := by decide

/-- Bytes 0x700 to 0x804 of `bootMainClosure0Code`. -/
def ac_c7 : List Nat :=
  [0xe7, 0x80, 0xa0, 0x01, 0x88, 0x0e, 0x89, 0x65, 0x93, 0x85, 0x05, 0xed,
    0x8a, 0x95, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80, 0xc0, 0xa6, 0x05, 0x89,
    0x4d, 0xe9, 0x85, 0x89, 0xcd, 0xc9, 0x32, 0x55, 0xf2, 0x45, 0xfd, 0x15,
    0x63, 0x9b, 0xa5, 0x02, 0x13, 0x05, 0xf1, 0x7f, 0x13, 0x05, 0x15, 0x5d,
    0x1d, 0x47, 0xa2, 0x85, 0x4a, 0x86, 0xb7, 0x46, 0xcc, 0x3f, 0x93, 0x86,
    0x06, 0x02, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80, 0xe0, 0x0e, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0xa2, 0x85, 0x4a, 0x86, 0x97, 0xc0,
    0x00, 0x00, 0xe7, 0x80, 0xc0, 0x3d, 0x93, 0x05, 0xf1, 0x7f, 0x93, 0x85,
    0x15, 0x09, 0x13, 0x06, 0xe0, 0x53, 0x05, 0x65, 0x13, 0x05, 0x25, 0x32,
    0x0a, 0x95, 0x97, 0x60, 0x01, 0x00, 0xe7, 0x80, 0x80, 0xfa, 0x32, 0x55,
    0x05, 0x05, 0x2a, 0xd6, 0x6a, 0xd2, 0x4e, 0xd0, 0x11, 0xb5, 0x83, 0xca,
    0x44, 0x56, 0x81, 0xa8, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x33, 0x06,
    0xa1, 0x00, 0x03, 0x45, 0x06, 0x00, 0xa2, 0x55, 0x23, 0x08, 0xb6, 0x00,
    0x85, 0x65, 0x93, 0x85, 0x05, 0x31, 0x8a, 0x95, 0xa3, 0x08, 0x66, 0x01,
    0x59, 0xc5, 0x83, 0xca, 0x15, 0x00, 0x25, 0xa0, 0x03, 0x45, 0x41, 0x35,
    0x05, 0xa0, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0x03, 0x45,
    0x45, 0x56, 0x09, 0xa8, 0x13, 0x05, 0x30, 0x02, 0x31, 0xa0, 0x2e, 0x8b,
    0x19, 0xa0, 0x13, 0x0b, 0x30, 0x02, 0x5a, 0x85, 0xaa, 0x8a, 0x86, 0x49,
    0x72, 0x54, 0x13, 0xf5, 0xfa, 0x0f, 0x93, 0x05, 0x00, 0x02, 0x63, 0x60,
    0xb5, 0x02, 0x01, 0x15, 0x0a, 0x05, 0xb7, 0x45, 0xcc, 0x3f, 0x93, 0x85,
    0x05, 0x00, 0x2e, 0x95, 0x08, 0x41, 0x93, 0x05, 0x00, 0x10, 0x02, 0x85,
    0x93, 0x05, 0x10, 0x10, 0x19, 0xa0, 0x93, 0xf5]
theorem ac_c7_ok : ac_c7 <+: List.drop 1792 bootMainClosure0Code := by decide

/-- Bytes 0x800 to 0x904 of `bootMainClosure0Code`. -/
def ac_c8 : List Nat :=
  [0x19, 0xa0, 0x93, 0xf5, 0xfa, 0x0f, 0x37, 0x65, 0xcc, 0x3f, 0x13, 0x05,
    0x65, 0x65, 0x97, 0xf0, 0xc5, 0xff, 0xe7, 0x80, 0xc0, 0x78, 0x91, 0xba,
    0x93, 0x05, 0x40, 0x10, 0xed, 0xb7, 0x93, 0x05, 0x20, 0x10, 0xd5, 0xb7,
    0x93, 0x05, 0x30, 0x10, 0xf9, 0xbf, 0x93, 0x05, 0x50, 0x10, 0xe1, 0xbf,
    0x93, 0x05, 0x60, 0x10, 0xc9, 0xbf, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31,
    0x0a, 0x95, 0x0c, 0x45, 0x2e, 0xd4, 0x48, 0x45, 0x2a, 0xd6, 0x88, 0x0e,
    0xd4, 0x04, 0xe2, 0x85, 0x5e, 0x86, 0x72, 0x47, 0xd2, 0x87, 0x97, 0xf0,
    0xff, 0xff, 0xe7, 0x80, 0x60, 0x73, 0x83, 0x25, 0x01, 0x35, 0x99, 0xe1,
    0x6f, 0x10, 0x60, 0x20, 0x03, 0x26, 0x41, 0x35, 0xb7, 0x46, 0xcc, 0x3f,
    0x93, 0x86, 0x06, 0x02, 0x09, 0x65, 0x13, 0x05, 0x05, 0x87, 0x0a, 0x95,
    0x1d, 0x47, 0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0x00, 0x00, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0x03, 0x29, 0x05, 0x56, 0x03, 0x44,
    0x45, 0x56, 0x63, 0x14, 0x09, 0x00, 0x6f, 0x10, 0x40, 0x1d, 0x09, 0x65,
    0x13, 0x05, 0x55, 0x87, 0xb3, 0x05, 0xa1, 0x00, 0x09, 0x65, 0x13, 0x05,
    0x55, 0x86, 0x0a, 0x95, 0x2d, 0x46, 0x97, 0x60, 0x01, 0x00, 0xe7, 0x80,
    0x80, 0xe6, 0x13, 0x05, 0xf1, 0x7f, 0x13, 0x05, 0x15, 0x09, 0x83, 0x44,
    0x05, 0x54, 0x85, 0x65, 0x93, 0x85, 0x05, 0x31, 0x8a, 0x95, 0x23, 0x8a,
    0x85, 0x54, 0x93, 0x09, 0xf1, 0x7f, 0x93, 0x89, 0x19, 0x09, 0x03, 0x44,
    0x15, 0x54, 0x13, 0x85, 0x24, 0xf0, 0x23, 0xa8, 0x25, 0x55, 0x19, 0xe1,
    0x6f, 0x10, 0x60, 0x18, 0x93, 0x05, 0xf1, 0x7f, 0x93, 0x85, 0x35, 0x5d,
    0x09, 0x65, 0x13, 0x05, 0x25, 0x87, 0x0a, 0x95, 0x13, 0x06, 0xe0, 0x53,
    0x97, 0x60, 0x01, 0x00, 0xe7, 0x80, 0xa0, 0xe1]
theorem ac_c8_ok : ac_c8 <+: List.drop 2048 bootMainClosure0Code := by decide

/-- Bytes 0x900 to 0xA04 of `bootMainClosure0Code`. -/
def ac_c9 : List Nat :=
  [0xe7, 0x80, 0xa0, 0xe1, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95,
    0x23, 0x00, 0x95, 0x56, 0xa3, 0x00, 0x85, 0x56, 0x09, 0x65, 0x13, 0x05,
    0x05, 0x87, 0x0a, 0x95, 0x89, 0x65, 0x93, 0x85, 0x05, 0x86, 0x8a, 0x95,
    0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80, 0x60, 0x85, 0x05, 0x89, 0x2e, 0x84,
    0x19, 0xc1, 0x6f, 0x10, 0x80, 0x13, 0x05, 0x88, 0x15, 0xcc, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x31, 0xb3, 0x04, 0xa1, 0x00, 0x03, 0xa4, 0x44, 0x55,
    0x09, 0x65, 0x13, 0x05, 0x05, 0x87, 0x0a, 0x95, 0xca, 0x85, 0x22, 0x86,
    0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0xa0, 0x1d, 0x05, 0x65, 0x13, 0x05,
    0x05, 0x31, 0xb3, 0x05, 0xa1, 0x00, 0x03, 0xc5, 0x04, 0x56, 0x09, 0xc9,
    0x03, 0xc4, 0x15, 0x56, 0x6f, 0x10, 0xa0, 0x0f, 0x13, 0x04, 0x30, 0x02,
    0x6f, 0x10, 0x20, 0x0f, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95,
    0x83, 0x25, 0x85, 0x56, 0x2e, 0xd0, 0x85, 0x65, 0x93, 0x85, 0x05, 0x31,
    0xb3, 0x04, 0xb1, 0x00, 0x03, 0x25, 0xc5, 0x56, 0x2a, 0xd2, 0xb7, 0x46,
    0xcc, 0x3f, 0x93, 0x86, 0x06, 0x02, 0x88, 0x0e, 0x1d, 0x47, 0xca, 0x85,
    0x22, 0x86, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80, 0x60, 0xc2, 0x83, 0x25,
    0x01, 0x35, 0x99, 0xe1, 0x6f, 0x10, 0xe0, 0x0a, 0x03, 0x26, 0x41, 0x35,
    0xb7, 0x46, 0xcc, 0x3f, 0x93, 0x86, 0x76, 0x02, 0x09, 0x65, 0x13, 0x05,
    0x05, 0x87, 0x0a, 0x95, 0x45, 0x47, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80,
    0xa0, 0xd6, 0x03, 0xc5, 0x04, 0x56, 0x09, 0xc5, 0x03, 0xc4, 0x14, 0x56,
    0x6f, 0x10, 0x60, 0x08, 0x03, 0xa4, 0x44, 0x56, 0x63, 0x0b, 0x04, 0x20,
    0x03, 0xa9, 0x84, 0x56, 0xb7, 0x46, 0xcc, 0x3f, 0x93, 0x86, 0x86, 0x03,
    0x88, 0x0e, 0x19, 0x47, 0xa2, 0x85, 0x4a, 0x86]
theorem ac_c9_ok : ac_c9 <+: List.drop 2304 bootMainClosure0Code := by decide

/-- Bytes 0xA00 to 0xB04 of `bootMainClosure0Code`. -/
def ac_c10 : List Nat :=
  [0xa2, 0x85, 0x4a, 0x86, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80, 0xc0, 0xbc,
    0x83, 0x25, 0x01, 0x35, 0x99, 0xe1, 0x6f, 0x10, 0x40, 0x05, 0x03, 0x26,
    0x41, 0x35, 0x09, 0x65, 0x13, 0x05, 0x05, 0x87, 0x0a, 0x95, 0x97, 0xa0,
    0x00, 0x00, 0xe7, 0x80, 0x00, 0x77, 0x03, 0xc5, 0x04, 0x56, 0x4d, 0xf9,
    0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0xb3, 0x04, 0xa1, 0x00, 0x03, 0xa5,
    0x84, 0x56, 0x2a, 0xca, 0x03, 0xa5, 0xc4, 0x56, 0x2a, 0xcc, 0xb7, 0x46,
    0xcc, 0x3f, 0x93, 0x86, 0xe6, 0x03, 0x09, 0x65, 0x13, 0x05, 0x05, 0x87,
    0x0a, 0x95, 0x19, 0x47, 0xa2, 0x85, 0x4a, 0x86, 0x97, 0xa0, 0x00, 0x00,
    0xe7, 0x80, 0x40, 0xb7, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x33, 0x0b,
    0xa1, 0x00, 0x83, 0xa5, 0x04, 0x56, 0x63, 0x8c, 0x05, 0x18, 0x03, 0x26,
    0x4b, 0x56, 0xb7, 0x46, 0xcc, 0x3f, 0x93, 0x86, 0x46, 0x04, 0x09, 0x65,
    0x13, 0x05, 0x05, 0xed, 0x0a, 0x95, 0x19, 0x47, 0x97, 0xa0, 0x00, 0x00,
    0xe7, 0x80, 0x40, 0xb4, 0x09, 0x65, 0x13, 0x05, 0x05, 0xdb, 0x0a, 0x95,
    0x83, 0x25, 0x05, 0x12, 0xa5, 0xc1, 0x09, 0x65, 0x13, 0x05, 0x05, 0xdb,
    0x0a, 0x95, 0x03, 0x25, 0x45, 0x12, 0x09, 0x46, 0x13, 0x04, 0x10, 0x02,
    0x63, 0x74, 0xc5, 0x00, 0x6f, 0x00, 0x30, 0x7b, 0x03, 0xc6, 0x05, 0x00,
    0x13, 0x06, 0xe6, 0xfd, 0x19, 0xc2, 0x6f, 0x00, 0x50, 0x7a, 0x33, 0x86,
    0xa5, 0x00, 0x03, 0x46, 0xf6, 0xff, 0x13, 0x06, 0xe6, 0xfd, 0x19, 0xc2,
    0x6f, 0x00, 0x30, 0x79, 0x93, 0x04, 0xe5, 0xfb, 0x91, 0xe8, 0x85, 0x05,
    0x13, 0x05, 0x11, 0x35, 0x13, 0x06, 0x00, 0x04, 0x97, 0x60, 0x01, 0x00,
    0xe7, 0x80, 0xa0, 0xc2, 0x72, 0x47, 0x05, 0x07, 0x01, 0xef, 0x19, 0x44,
    0x6f, 0x00, 0xf0, 0x76, 0x09, 0x65, 0x13, 0x05]
theorem ac_c10_ok : ac_c10 <+: List.drop 2560 bootMainClosure0Code := by decide

/-- Bytes 0xB00 to 0xC04 of `bootMainClosure0Code`. -/
def ac_c11 : List Nat :=
  [0x09, 0x65, 0x13, 0x05, 0x05, 0xdb, 0x0a, 0x95, 0x03, 0x44, 0x45, 0x12,
    0x6f, 0x00, 0xf0, 0x75, 0x09, 0x65, 0x13, 0x05, 0x05, 0x87, 0x0a, 0x95,
    0xd4, 0x04, 0xe2, 0x85, 0x5e, 0x86, 0xd2, 0x87, 0x97, 0xf0, 0xff, 0xff,
    0xe7, 0x80, 0x80, 0x46, 0x03, 0x29, 0x0b, 0x56, 0x63, 0x0f, 0x09, 0x0c,
    0x03, 0x2c, 0x4b, 0x56, 0x09, 0x65, 0x13, 0x05, 0x85, 0xdc, 0x0a, 0x95,
    0xca, 0x85, 0x62, 0x86, 0x89, 0x66, 0x93, 0x86, 0x86, 0xdc, 0x33, 0x04,
    0xd1, 0x00, 0x97, 0x60, 0x00, 0x00, 0xe7, 0x80, 0x80, 0x16, 0x09, 0x65,
    0x13, 0x05, 0x05, 0x87, 0x0a, 0x95, 0x13, 0x06, 0x00, 0x04, 0x81, 0x45,
    0x97, 0x60, 0x01, 0x00, 0xe7, 0x80, 0xe0, 0xb4, 0x13, 0x05, 0x00, 0x02,
    0x89, 0x65, 0x93, 0x85, 0x15, 0x87, 0x8a, 0x95, 0x37, 0x56, 0xcc, 0x3f,
    0x13, 0x06, 0x06, 0x9a, 0x05, 0xc5, 0x83, 0x46, 0x04, 0x00, 0x05, 0x04,
    0x13, 0xd7, 0x46, 0x00, 0xbd, 0x8a, 0x32, 0x97, 0xb2, 0x96, 0x03, 0x47,
    0x07, 0x00, 0x83, 0xc6, 0x06, 0x00, 0xa3, 0x8f, 0xe5, 0xfe, 0x23, 0x80,
    0xd5, 0x00, 0x89, 0x05, 0x7d, 0x15, 0x71, 0xfd, 0x09, 0x65, 0x13, 0x05,
    0x05, 0xed, 0x0a, 0x95, 0x89, 0x65, 0x93, 0x85, 0x05, 0x87, 0x8a, 0x95,
    0x13, 0x06, 0x00, 0x04, 0x97, 0x60, 0x01, 0x00, 0xe7, 0x80, 0xe0, 0xb5,
    0x62, 0x45, 0x21, 0xe1, 0x52, 0x45, 0x63, 0x1e, 0xac, 0x02, 0x09, 0x65,
    0x13, 0x05, 0x15, 0x87, 0x33, 0x0a, 0xa1, 0x00, 0x09, 0x65, 0x13, 0x05,
    0x05, 0xed, 0xb3, 0x05, 0xa1, 0x00, 0x13, 0x06, 0x00, 0x04, 0x52, 0x85,
    0x97, 0x60, 0x01, 0x00, 0xe7, 0x80, 0x20, 0xb3, 0x99, 0xe8, 0x13, 0x05,
    0x11, 0x35, 0x13, 0x06, 0x00, 0x04, 0xd2, 0x85, 0x97, 0x60, 0x01, 0x00,
    0xe7, 0x80, 0x60, 0xa9, 0x09, 0xc9, 0x13, 0x04]
theorem ac_c11_ok : ac_c11 <+: List.drop 2816 bootMainClosure0Code := by decide

/-- Bytes 0xC00 to 0xD04 of `bootMainClosure0Code`. -/
def ac_c12 : List Nat :=
  [0x09, 0xc9, 0x13, 0x04, 0x40, 0x02, 0x6f, 0x00, 0x50, 0x66, 0x03, 0x44,
    0x4b, 0x56, 0x6f, 0x00, 0xd0, 0x65, 0x12, 0x55, 0xb2, 0x55, 0x63, 0x05,
    0xb5, 0x00, 0x12, 0x55, 0xb2, 0x55, 0x19, 0xa0, 0x02, 0x55, 0xa2, 0x55,
    0x33, 0x35, 0xb5, 0x00, 0x09, 0xe5, 0x32, 0x55, 0x2a, 0xd2, 0x22, 0x55,
    0x2a, 0xd0, 0x15, 0x45, 0x2e, 0x05, 0x63, 0x75, 0x85, 0x01, 0x4d, 0x44,
    0x6f, 0x00, 0xf0, 0x62, 0x15, 0x65, 0x13, 0x05, 0x05, 0x04, 0x89, 0x65,
    0x93, 0x85, 0x05, 0xdb, 0x8a, 0x95, 0x42, 0x56, 0x23, 0xa6, 0xc5, 0x22,
    0x23, 0xa8, 0xa5, 0x22, 0x05, 0x65, 0x13, 0x05, 0x05, 0x32, 0x0a, 0x95,
    0xca, 0x85, 0x62, 0x86, 0x81, 0x46, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80,
    0x40, 0x76, 0x03, 0x2d, 0x0b, 0x01, 0x63, 0x09, 0x0d, 0x06, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x31, 0x33, 0x04, 0xa1, 0x00, 0x50, 0x48, 0xb7, 0x46,
    0xcc, 0x3f, 0x93, 0x86, 0xa6, 0x79, 0x05, 0x65, 0x13, 0x05, 0x05, 0x32,
    0x0a, 0x95, 0x25, 0x47, 0xea, 0x85, 0x32, 0xd8, 0x97, 0xa0, 0x00, 0x00,
    0xe7, 0x80, 0x80, 0x93, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95,
    0x0c, 0x48, 0x63, 0x80, 0x05, 0x76, 0x50, 0x49, 0x88, 0x0e, 0x97, 0xa0,
    0x00, 0x00, 0xe7, 0x80, 0xa0, 0x95, 0x03, 0x25, 0x01, 0x35, 0xe3, 0x04,
    0x05, 0x5a, 0x83, 0x25, 0x41, 0x35, 0x37, 0x46, 0xcc, 0x3f, 0x13, 0x06,
    0x36, 0x7a, 0x93, 0x06, 0x90, 0x03, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80,
    0x20, 0x6e, 0x09, 0xc9, 0x13, 0x04, 0x10, 0x02, 0x6f, 0x00, 0xb0, 0x58,
    0x03, 0x44, 0x4b, 0x01, 0x6f, 0x00, 0x30, 0x58, 0x09, 0x65, 0x13, 0x05,
    0x05, 0xed, 0x0a, 0x95, 0xa1, 0x45, 0x99, 0xc5, 0x23, 0x20, 0x05, 0x00,
    0x13, 0x05, 0x05, 0x02, 0xfd, 0x15, 0xfd, 0xf9]
theorem ac_c12_ok : ac_c12 <+: List.drop 3072 bootMainClosure0Code := by decide

/-- Bytes 0xD00 to 0xE04 of `bootMainClosure0Code`. -/
def ac_c13 : List Nat :=
  [0xfd, 0x15, 0xfd, 0xf9, 0xb7, 0x46, 0xcc, 0x3f, 0x93, 0x86, 0xc6, 0x7d,
    0x88, 0x0e, 0x59, 0x47, 0xea, 0x85, 0x42, 0x56, 0x97, 0xa0, 0x00, 0x00,
    0xe7, 0x80, 0xc0, 0x8b, 0x83, 0x25, 0x01, 0x35, 0xe3, 0x83, 0x05, 0x54,
    0x03, 0x26, 0x41, 0x35, 0x05, 0x65, 0x13, 0x05, 0x05, 0x32, 0x0a, 0x95,
    0x97, 0x90, 0x00, 0x00, 0xe7, 0x80, 0x80, 0x7f, 0x05, 0x65, 0x13, 0x05,
    0x05, 0x31, 0x0a, 0x95, 0x04, 0x49, 0x03, 0x44, 0x45, 0x01, 0xe3, 0x82,
    0x04, 0x52, 0x05, 0x65, 0x13, 0x05, 0x55, 0x32, 0xb3, 0x05, 0xa1, 0x00,
    0x05, 0x65, 0x13, 0x05, 0x55, 0x31, 0x0a, 0x95, 0x1d, 0x46, 0x1d, 0x49,
    0x97, 0x60, 0x01, 0x00, 0xe7, 0x80, 0x60, 0x9b, 0x01, 0x4b, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0x04, 0xc1, 0x85, 0x65, 0x93, 0x85,
    0x05, 0x31, 0xb3, 0x04, 0xb1, 0x00, 0x23, 0x02, 0x85, 0x00, 0x09, 0x65,
    0x13, 0x05, 0x05, 0xed, 0x33, 0x0a, 0xa1, 0x00, 0x05, 0x65, 0x13, 0x05,
    0x05, 0x32, 0x0a, 0x95, 0x85, 0x65, 0x93, 0x85, 0x05, 0x31, 0x8a, 0x95,
    0x97, 0x90, 0x00, 0x00, 0xe7, 0x80, 0x60, 0x7d, 0x03, 0xc5, 0x04, 0x01,
    0x3d, 0xed, 0xcc, 0x48, 0xc9, 0xc1, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31,
    0x33, 0x04, 0xa1, 0x00, 0x10, 0x4c, 0x05, 0x65, 0x13, 0x05, 0x05, 0x32,
    0x0a, 0x95, 0x89, 0x66, 0x93, 0x86, 0xc6, 0xfd, 0x8a, 0x96, 0x97, 0xb0,
    0x00, 0x00, 0xe7, 0x80, 0x40, 0x93, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31,
    0xb3, 0x04, 0xa1, 0x00, 0x08, 0x48, 0x63, 0x00, 0x05, 0x3c, 0x88, 0x5c,
    0x45, 0xd5, 0x63, 0x6f, 0x69, 0x63, 0x85, 0x65, 0x93, 0x85, 0x05, 0x31,
    0x33, 0x04, 0xb1, 0x00, 0x0c, 0x50, 0x50, 0x50, 0x34, 0x40, 0x78, 0x40,
    0x3c, 0x44, 0x05, 0x68, 0x13, 0x08, 0x08, 0x31]
theorem ac_c13_ok : ac_c13 <+: List.drop 3328 bootMainClosure0Code := by decide

/-- Bytes 0xE00 to 0xF04 of `bootMainClosure0Code`. -/
def ac_c14 : List Nat :=
  [0x13, 0x08, 0x08, 0x31, 0xb3, 0x04, 0x01, 0x01, 0x03, 0x28, 0xc4, 0x04,
    0x13, 0x14, 0x5b, 0x00, 0x52, 0x94, 0x0c, 0xc0, 0x50, 0xc0, 0x14, 0xc4,
    0x58, 0xc4, 0x1c, 0xc8, 0x23, 0x2a, 0x04, 0x01, 0x08, 0xcc, 0x05, 0x0b,
    0xa5, 0xb7, 0x03, 0xc4, 0x14, 0x01, 0x6f, 0x00, 0x10, 0x44, 0x88, 0x0e,
    0xc1, 0x45, 0x99, 0xc5, 0x23, 0x20, 0x05, 0x00, 0x13, 0x05, 0x05, 0x02,
    0xfd, 0x15, 0xfd, 0xf9, 0xb7, 0x46, 0xcc, 0x3f, 0x93, 0x86, 0x26, 0x7f,
    0x13, 0x05, 0xf1, 0x7f, 0x13, 0x05, 0x15, 0x09, 0x15, 0x47, 0xea, 0x85,
    0x42, 0x56, 0x97, 0x90, 0x00, 0x00, 0xe7, 0x80, 0xa0, 0x77, 0x83, 0xa5,
    0x09, 0x00, 0x63, 0x87, 0x05, 0x5a, 0x03, 0xa6, 0x49, 0x00, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x32, 0x0a, 0x95, 0x97, 0x90, 0x00, 0x00, 0xe7, 0x80,
    0x60, 0x6b, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0x04, 0x49,
    0x03, 0x44, 0x45, 0x01, 0xe3, 0x81, 0x04, 0x3e, 0x05, 0x65, 0x13, 0x05,
    0x55, 0x32, 0xb3, 0x05, 0xa1, 0x00, 0x09, 0x65, 0x13, 0x05, 0x55, 0x86,
    0x0a, 0x95, 0x1d, 0x46, 0x97, 0x60, 0x01, 0x00, 0xe7, 0x80, 0x60, 0x87,
    0x02, 0xd6, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0x23, 0x28,
    0x95, 0x54, 0x23, 0x0a, 0x85, 0x54, 0x05, 0x65, 0x13, 0x05, 0x05, 0x32,
    0x0a, 0x95, 0x89, 0x65, 0x93, 0x85, 0x05, 0x86, 0x8a, 0x95, 0x97, 0x90,
    0x00, 0x00, 0xe7, 0x80, 0x80, 0x6a, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31,
    0x0a, 0x95, 0x03, 0x45, 0x05, 0x01, 0x63, 0x1c, 0x05, 0x52, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0x03, 0x2b, 0x45, 0x01, 0x63, 0x0c,
    0x0b, 0x2a, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x33, 0x04, 0xa1, 0x00,
    0x83, 0x2b, 0x84, 0x01, 0x05, 0x65, 0x13, 0x05]
theorem ac_c14_ok : ac_c14 <+: List.drop 3584 bootMainClosure0Code := by decide

/-- Bytes 0xF00 to 0x1004 of `bootMainClosure0Code`. -/
def ac_c15 : List Nat :=
  [0x05, 0x65, 0x13, 0x05, 0x05, 0x32, 0x0a, 0x95, 0x25, 0x47, 0xda, 0x85,
    0x5e, 0x86, 0xb7, 0x56, 0xcc, 0x3f, 0x93, 0x86, 0xb6, 0x80, 0x97, 0x90,
    0x00, 0x00, 0xe7, 0x80, 0xa0, 0x6b, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31,
    0x0a, 0x95, 0x0c, 0x48, 0x2e, 0xd4, 0x63, 0x80, 0x05, 0x4e, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x31, 0x33, 0x04, 0xa1, 0x00, 0x50, 0x48, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x32, 0x0a, 0x95, 0x29, 0x47, 0xa2, 0x55, 0x32, 0xce,
    0xb7, 0x56, 0xcc, 0x3f, 0x93, 0x86, 0x46, 0x81, 0x97, 0x90, 0x00, 0x00,
    0xe7, 0x80, 0x00, 0x68, 0x0c, 0x48, 0x63, 0x84, 0x05, 0x4a, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0x50, 0x49, 0x13, 0x05, 0xf1, 0x7f,
    0x13, 0x05, 0x15, 0x09, 0x97, 0x90, 0x00, 0x00, 0xe7, 0x80, 0xc0, 0x69,
    0x03, 0xa5, 0x09, 0x00, 0x63, 0x0a, 0x05, 0x48, 0x83, 0xa5, 0x49, 0x00,
    0x31, 0x46, 0xe3, 0x9a, 0xc5, 0xf2, 0x31, 0x46, 0xb7, 0x55, 0xcc, 0x3f,
    0x93, 0x85, 0xe5, 0x81, 0x97, 0x50, 0x01, 0x00, 0xe7, 0x80, 0xa0, 0x6f,
    0x19, 0xfd, 0x05, 0x65, 0x13, 0x05, 0x05, 0x32, 0x0a, 0x95, 0x21, 0x47,
    0xa2, 0x55, 0x72, 0x46, 0xb7, 0x46, 0xcc, 0x3f, 0x93, 0x86, 0x06, 0x73,
    0x97, 0x90, 0x00, 0x00, 0xe7, 0x80, 0xc0, 0x61, 0x05, 0x65, 0x13, 0x05,
    0x05, 0x31, 0x0a, 0x95, 0x0c, 0x49, 0x63, 0x8e, 0x05, 0x42, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0x50, 0x49, 0x13, 0x05, 0xf1, 0x7f,
    0x13, 0x05, 0x15, 0x09, 0x97, 0x90, 0x00, 0x00, 0xe7, 0x80, 0x00, 0x63,
    0x83, 0xa5, 0x09, 0x00, 0x63, 0x84, 0x05, 0x42, 0x03, 0xa6, 0x49, 0x00,
    0xc8, 0x04, 0x89, 0x66, 0x93, 0x86, 0xc6, 0xfd, 0x8a, 0x96, 0x97, 0xb0,
    0x00, 0x00, 0xe7, 0x80, 0x80, 0xc4, 0x03, 0x2c]
theorem ac_c15_ok : ac_c15 <+: List.drop 3840 bootMainClosure0Code := by decide

/-- Bytes 0x1000 to 0x1104 of `bootMainClosure0Code`. -/
def ac_c16 : List Nat :=
  [0x80, 0xc4, 0x03, 0x2c, 0x41, 0x24, 0x63, 0x01, 0x0c, 0x42, 0x83, 0x24,
    0x81, 0x24, 0x39, 0x44, 0x31, 0x45, 0xe3, 0xec, 0xa4, 0x24, 0x31, 0x46,
    0x62, 0x85, 0xb7, 0x45, 0xcc, 0x3f, 0x93, 0x85, 0x05, 0x69, 0x97, 0x80,
    0x00, 0x00, 0xe7, 0x80, 0xe0, 0x2a, 0x13, 0x89, 0x44, 0xfd, 0xe3, 0x1e,
    0x09, 0x22, 0x2a, 0x8a, 0xe3, 0x0b, 0x05, 0x22, 0x31, 0x0c, 0x62, 0x85,
    0x97, 0x40, 0x00, 0x00, 0xe7, 0x80, 0xc0, 0xca, 0xe3, 0x03, 0x05, 0x22,
    0x05, 0x65, 0x13, 0x05, 0x05, 0x32, 0x0a, 0x95, 0x1d, 0x47, 0xda, 0x85,
    0x5e, 0x86, 0xb7, 0x56, 0xcc, 0x3f, 0x93, 0x86, 0xa6, 0x82, 0x97, 0x90,
    0x00, 0x00, 0xe7, 0x80, 0x20, 0x57, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31,
    0x0a, 0x95, 0x0c, 0x49, 0x63, 0x89, 0x05, 0x38, 0x05, 0x65, 0x13, 0x05,
    0x05, 0x31, 0x0a, 0x95, 0x50, 0x49, 0x13, 0x05, 0xf1, 0x7f, 0x13, 0x05,
    0x15, 0x09, 0x97, 0x90, 0x00, 0x00, 0xe7, 0x80, 0x60, 0x58, 0x83, 0xa4,
    0x09, 0x00, 0x63, 0x8f, 0x04, 0x36, 0x83, 0xab, 0x49, 0x00, 0x13, 0x04,
    0x10, 0x02, 0x21, 0x45, 0xe3, 0xe5, 0xab, 0x1c, 0x21, 0x46, 0x26, 0x85,
    0xb7, 0x45, 0xcc, 0x3f, 0x93, 0x85, 0x05, 0x74, 0x97, 0x80, 0x00, 0x00,
    0xe7, 0x80, 0x00, 0x22, 0xe3, 0x09, 0x05, 0x1a, 0x13, 0x35, 0x19, 0x00,
    0x33, 0x75, 0x45, 0x01, 0x13, 0x8a, 0x84, 0x00, 0x33, 0x05, 0xa0, 0x40,
    0x13, 0x89, 0x8b, 0xff, 0x33, 0x7c, 0x85, 0x01, 0x13, 0x8b, 0x9b, 0xff,
    0xa6, 0x9b, 0xe3, 0x08, 0x09, 0x18, 0xca, 0x84, 0x7d, 0x19, 0x7d, 0x1b,
    0xfd, 0x1b, 0x05, 0x46, 0x5e, 0x85, 0xb7, 0x55, 0xcc, 0x3f, 0x93, 0x85,
    0x15, 0x83, 0x97, 0x80, 0x00, 0x00, 0xe7, 0x80, 0xe0, 0x1d, 0x65, 0xf1,
    0x52, 0x85, 0x81, 0xcc, 0x83, 0x45, 0x05, 0x00]
theorem ac_c16_ok : ac_c16 <+: List.drop 4096 bootMainClosure0Code := by decide

/-- Bytes 0x1100 to 0x1204 of `bootMainClosure0Code`. -/
def ac_c17 : List Nat :=
  [0x83, 0x45, 0x05, 0x00, 0x05, 0x05, 0x81, 0x15, 0xfd, 0x14, 0x13, 0x06,
    0xf0, 0x05, 0xe3, 0xe8, 0xc5, 0xfe, 0x6f, 0x00, 0x90, 0x15, 0x13, 0x05,
    0xf1, 0x7f, 0x13, 0x05, 0x15, 0x09, 0x21, 0x47, 0xa2, 0x55, 0x72, 0x46,
    0xb7, 0x46, 0xcc, 0x3f, 0x93, 0x86, 0x06, 0x70, 0x97, 0x90, 0x00, 0x00,
    0xe7, 0x80, 0x40, 0x4a, 0x83, 0xa5, 0x09, 0x00, 0x63, 0x8c, 0x05, 0x2c,
    0x03, 0xa6, 0x49, 0x00, 0x05, 0x65, 0x13, 0x05, 0x05, 0x32, 0x0a, 0x95,
    0x97, 0xb0, 0x00, 0x00, 0xe7, 0x80, 0x40, 0xb6, 0x05, 0x65, 0x13, 0x05,
    0x05, 0x31, 0x0a, 0x95, 0x03, 0x45, 0x05, 0x01, 0x63, 0x1d, 0x05, 0x2a,
    0x32, 0x55, 0xbd, 0x45, 0x63, 0xe0, 0xa5, 0x2c, 0x05, 0x65, 0x13, 0x05,
    0x05, 0x31, 0xb3, 0x06, 0xa1, 0x00, 0x88, 0x4e, 0xcc, 0x4e, 0x90, 0x52,
    0xd4, 0x52, 0xb2, 0x57, 0x13, 0x97, 0x57, 0x00, 0x84, 0x0e, 0x26, 0x97,
    0x23, 0x20, 0x47, 0x01, 0x23, 0x22, 0x67, 0x01, 0x08, 0xc7, 0x4c, 0xc7,
    0x10, 0xcb, 0x54, 0xcb, 0x23, 0x2c, 0x87, 0x01, 0x85, 0x07, 0x3e, 0xd6,
    0x39, 0xbb, 0x03, 0xc4, 0x44, 0x01, 0x6f, 0x00, 0x90, 0x0c, 0x13, 0x05,
    0xf1, 0x7f, 0x13, 0x05, 0x15, 0x09, 0xa1, 0x45, 0x99, 0xc5, 0x23, 0x20,
    0x05, 0x00, 0x13, 0x05, 0x05, 0x02, 0xfd, 0x15, 0xfd, 0xf9, 0xb7, 0x46,
    0xcc, 0x3f, 0x93, 0x86, 0x76, 0x7f, 0xc8, 0x04, 0x51, 0x47, 0xea, 0x85,
    0x42, 0x56, 0x97, 0x90, 0x00, 0x00, 0xe7, 0x80, 0x20, 0x40, 0x83, 0x25,
    0x41, 0x24, 0x63, 0x87, 0x05, 0x24, 0x03, 0x26, 0x81, 0x24, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x32, 0x0a, 0x95, 0x97, 0x90, 0x00, 0x00, 0xe7, 0x80,
    0xe0, 0x33, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0x04, 0x49,
    0x85, 0x65, 0x93, 0x85, 0x05, 0x31, 0xb3, 0x09]
theorem ac_c17_ok : ac_c17 <+: List.drop 4352 bootMainClosure0Code := by decide

/-- Bytes 0x1200 to 0x1304 of `bootMainClosure0Code`. -/
def ac_c18 : List Nat :=
  [0x05, 0x31, 0xb3, 0x09, 0xb1, 0x00, 0x03, 0x44, 0x45, 0x01, 0xe3, 0x80,
    0x04, 0x06, 0x05, 0x65, 0x13, 0x05, 0x55, 0x32, 0xb3, 0x05, 0xa1, 0x00,
    0x09, 0x65, 0x13, 0x05, 0xd5, 0xdc, 0x0a, 0x95, 0x1d, 0x46, 0x97, 0x50,
    0x01, 0x00, 0xe7, 0x80, 0x40, 0x4f, 0x01, 0x4d, 0x09, 0x65, 0x13, 0x05,
    0x05, 0xdb, 0x0a, 0x95, 0x04, 0xcd, 0x23, 0x0e, 0x85, 0x00, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x32, 0x0a, 0x95, 0x89, 0x65, 0x93, 0x85, 0x85, 0xdc,
    0x8a, 0x95, 0x97, 0x90, 0x00, 0x00, 0xe7, 0x80, 0x80, 0x32, 0x03, 0xc5,
    0x09, 0x01, 0x63, 0x1c, 0x05, 0x1c, 0x83, 0xa5, 0x49, 0x01, 0x63, 0x8b,
    0x05, 0x1c, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x33, 0x04, 0xa1, 0x00,
    0x10, 0x4c, 0x05, 0x65, 0x13, 0x05, 0x05, 0x32, 0x0a, 0x95, 0x89, 0x66,
    0x93, 0x86, 0xc6, 0xfd, 0x8a, 0x96, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80,
    0x00, 0x48, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0xb3, 0x09, 0xa1, 0x00,
    0x08, 0x48, 0x63, 0x0c, 0x05, 0x22, 0xaa, 0x8b, 0x03, 0xa5, 0x89, 0x03,
    0x2a, 0xd8, 0x51, 0xdd, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95,
    0x4c, 0x49, 0x03, 0x2a, 0xc5, 0x01, 0x33, 0x05, 0xba, 0x00, 0xe3, 0x64,
    0x45, 0x85, 0x2e, 0x8b, 0x93, 0x55, 0x05, 0x01, 0x81, 0xc5, 0x93, 0x05,
    0x10, 0x50, 0x29, 0xa0, 0x93, 0x15, 0x05, 0x01, 0x93, 0x85, 0x05, 0x50,
    0x13, 0xf6, 0x15, 0x00, 0x15, 0x44, 0x63, 0x1c, 0x06, 0x78, 0x05, 0x66,
    0x13, 0x06, 0x06, 0x31, 0xb3, 0x07, 0xc1, 0x00, 0xf0, 0x47, 0x32, 0xd6,
    0x90, 0x4f, 0x32, 0xca, 0xb0, 0x43, 0x32, 0xce, 0xf0, 0x43, 0x32, 0xcc,
    0xb0, 0x47, 0x32, 0xd4, 0x93, 0xd6, 0x05, 0x01, 0x13, 0xf6, 0xf6, 0x0f,
    0x13, 0xd7, 0x75, 0x01, 0x93, 0x04, 0x00, 0x03]
theorem ac_c18_ok : ac_c18 <+: List.drop 4608 bootMainClosure0Code := by decide

/-- Bytes 0x1300 to 0x1404 of `bootMainClosure0Code`. -/
def ac_c19 : List Nat :=
  [0x93, 0x04, 0x00, 0x03, 0x23, 0x88, 0x97, 0x00, 0x23, 0x89, 0xd7, 0x00,
    0x05, 0x68, 0x13, 0x08, 0x08, 0x31, 0xb3, 0x09, 0x01, 0x01, 0xa3, 0x89,
    0x07, 0x00, 0x09, 0xe7, 0xa3, 0x88, 0xc9, 0x00, 0x89, 0x45, 0x2d, 0xa8,
    0xe1, 0x81, 0x99, 0xe5, 0x93, 0x05, 0x10, 0x08, 0xa3, 0x88, 0xb9, 0x00,
    0x8d, 0x45, 0x2d, 0xa0, 0xa2, 0x06, 0xd5, 0x8d, 0x85, 0x66, 0x93, 0x86,
    0x06, 0x31, 0x8a, 0x96, 0x13, 0x07, 0x20, 0x08, 0xa3, 0x88, 0xe6, 0x00,
    0x23, 0x89, 0xb6, 0x00, 0x85, 0x65, 0x93, 0x85, 0x05, 0x31, 0xb3, 0x09,
    0xb1, 0x00, 0xa3, 0x89, 0xc6, 0x00, 0x91, 0x45, 0x33, 0x89, 0xa5, 0x00,
    0x63, 0x6d, 0xb9, 0xf8, 0x09, 0x65, 0x13, 0x05, 0x05, 0xdb, 0x0a, 0x95,
    0x03, 0x25, 0x05, 0x23, 0xe3, 0x65, 0x25, 0x8d, 0x09, 0x66, 0x13, 0x06,
    0x06, 0xdb, 0xb3, 0x06, 0xc1, 0x00, 0x13, 0x87, 0x06, 0x20, 0x44, 0x57,
    0x33, 0x05, 0x25, 0x41, 0x33, 0x86, 0x24, 0x01, 0x33, 0x8c, 0xb4, 0x00,
    0x50, 0xd7, 0x08, 0xdb, 0x33, 0x05, 0x4c, 0x01, 0x2a, 0xc8, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x32, 0x33, 0x06, 0xa1, 0x00, 0x26, 0x85, 0xae, 0x86,
    0x97, 0xe0, 0x00, 0x00, 0xe7, 0x80, 0x00, 0xd5, 0x62, 0x85, 0xd2, 0x85,
    0x52, 0x46, 0xd2, 0x86, 0x97, 0xe0, 0x00, 0x00, 0xe7, 0x80, 0x00, 0xd4,
    0x42, 0x45, 0xda, 0x85, 0x5e, 0x86, 0xda, 0x86, 0x97, 0xe0, 0x00, 0x00,
    0xe7, 0x80, 0x00, 0xd3, 0x1d, 0x45, 0x63, 0x6c, 0xa5, 0x69, 0x13, 0x15,
    0x5d, 0x00, 0x05, 0x0d, 0x93, 0x05, 0xf1, 0x7f, 0x93, 0x85, 0x15, 0x09,
    0x2e, 0x95, 0x04, 0xc1, 0x23, 0x22, 0x25, 0x01, 0xf2, 0x45, 0x0c, 0xc5,
    0xe2, 0x45, 0x4c, 0xc5, 0xa2, 0x55, 0x0c, 0xc9, 0xb2, 0x55, 0x4c, 0xc9,
    0xc2, 0x55, 0x0c, 0xcd, 0x2d, 0xbd, 0x05, 0x65]
theorem ac_c19_ok : ac_c19 <+: List.drop 4864 bootMainClosure0Code := by decide

/-- Bytes 0x1400 to 0x1504 of `bootMainClosure0Code`. -/
def ac_c20 : List Nat :=
  [0x2d, 0xbd, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0x03, 0x44,
    0x45, 0x01, 0xb1, 0xad, 0x03, 0xc4, 0x49, 0x00, 0x99, 0xad, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0x03, 0x44, 0x15, 0x01, 0xa1, 0xa5,
    0x15, 0x44, 0x91, 0xa5, 0x03, 0x44, 0x81, 0x24, 0x3d, 0xad, 0x03, 0xc4,
    0x19, 0x01, 0x25, 0xad, 0x09, 0x65, 0x13, 0x05, 0x05, 0xed, 0x33, 0x09,
    0xa1, 0x00, 0x09, 0x65, 0x13, 0x05, 0x05, 0xfd, 0x33, 0x0a, 0xa1, 0x00,
    0x08, 0x04, 0x23, 0x22, 0x25, 0x05, 0x23, 0x24, 0x45, 0x05, 0x23, 0x26,
    0x05, 0x04, 0xc8, 0x04, 0x97, 0xb0, 0x00, 0x00, 0xe7, 0x80, 0x20, 0x93,
    0xa5, 0xc9, 0x05, 0x05, 0x33, 0x36, 0xa0, 0x00, 0x83, 0xa9, 0x05, 0x00,
    0x03, 0xab, 0x45, 0x00, 0x7d, 0x16, 0x51, 0x8d, 0x85, 0x65, 0x93, 0x85,
    0x05, 0x31, 0x8a, 0x95, 0x23, 0xa8, 0x25, 0x01, 0x23, 0xaa, 0x45, 0x01,
    0x23, 0xac, 0x05, 0x00, 0x93, 0x05, 0xf5, 0xff, 0x05, 0x65, 0x13, 0x05,
    0x05, 0x32, 0x0a, 0x95, 0x97, 0xb0, 0x00, 0x00, 0xe7, 0x80, 0xc0, 0x91,
    0x4d, 0xdd, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0x10, 0x49,
    0x40, 0x49, 0xe3, 0x06, 0x86, 0xfa, 0x08, 0x42, 0x5d, 0xd1, 0x4c, 0x42,
    0x93, 0x04, 0x06, 0x02, 0x4e, 0x86, 0xda, 0x86, 0x97, 0x90, 0x00, 0x00,
    0xe7, 0x80, 0xa0, 0x26, 0x26, 0x86, 0x75, 0xd1, 0x75, 0xa4, 0x03, 0xc4,
    0x49, 0x01, 0x71, 0xab, 0x09, 0x65, 0x13, 0x05, 0x05, 0xed, 0x33, 0x09,
    0xa1, 0x00, 0x08, 0x04, 0x23, 0x22, 0x25, 0x05, 0x23, 0x24, 0x45, 0x05,
    0x23, 0x26, 0x05, 0x04, 0xc8, 0x04, 0x97, 0xb0, 0x00, 0x00, 0xe7, 0x80,
    0x00, 0x8a, 0xb5, 0xc1, 0x05, 0x05, 0x33, 0x36, 0xa0, 0x00, 0x83, 0xa9,
    0x85, 0x01, 0x7d, 0x16, 0x51, 0x8d, 0x85, 0x65]
theorem ac_c20_ok : ac_c20 <+: List.drop 5120 bootMainClosure0Code := by decide

/-- Bytes 0x1500 to 0x1604 of `bootMainClosure0Code`. -/
def ac_c21 : List Nat :=
  [0x51, 0x8d, 0x85, 0x65, 0x93, 0x85, 0x05, 0x31, 0x8a, 0x95, 0x23, 0xa8,
    0x25, 0x01, 0x23, 0xaa, 0x45, 0x01, 0x23, 0xac, 0x05, 0x00, 0x93, 0x05,
    0xf5, 0xff, 0x05, 0x65, 0x13, 0x05, 0x05, 0x32, 0x0a, 0x95, 0x97, 0xb0,
    0x00, 0x00, 0xe7, 0x80, 0xe0, 0x88, 0x5d, 0xdd, 0x05, 0x65, 0x13, 0x05,
    0x05, 0x31, 0x0a, 0x95, 0x0c, 0x49, 0x44, 0x49, 0xe3, 0x88, 0x95, 0xfa,
    0x88, 0x41, 0x4d, 0xd5, 0x88, 0x4d, 0x13, 0x84, 0x05, 0x02, 0xce, 0x85,
    0x97, 0x90, 0x00, 0x00, 0xe7, 0x80, 0xa0, 0x0f, 0xa2, 0x85, 0x7d, 0xd1,
    0x05, 0xa4, 0x13, 0x09, 0x01, 0x35, 0x13, 0x0a, 0x01, 0x55, 0x08, 0x04,
    0x23, 0x22, 0x25, 0x05, 0x23, 0x24, 0x45, 0x05, 0x23, 0x26, 0x05, 0x04,
    0xc8, 0x04, 0x97, 0xb0, 0x00, 0x00, 0xe7, 0x80, 0xc0, 0x81, 0xad, 0xc5,
    0x05, 0x05, 0x33, 0x36, 0xa0, 0x00, 0x83, 0xa9, 0x05, 0x00, 0x03, 0xab,
    0x45, 0x00, 0x7d, 0x16, 0x51, 0x8d, 0x85, 0x65, 0x93, 0x85, 0x05, 0x31,
    0x8a, 0x95, 0x23, 0xa8, 0x25, 0x01, 0x23, 0xaa, 0x45, 0x01, 0x23, 0xac,
    0x05, 0x00, 0x93, 0x05, 0xf5, 0xff, 0x05, 0x65, 0x13, 0x05, 0x05, 0x32,
    0x0a, 0x95, 0x97, 0xb0, 0x00, 0x00, 0xe7, 0x80, 0x60, 0x80, 0x4d, 0xdd,
    0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95, 0x10, 0x49, 0x40, 0x49,
    0xe3, 0x06, 0x86, 0xfa, 0x08, 0x42, 0x5d, 0xd1, 0x4c, 0x42, 0x93, 0x04,
    0x06, 0x02, 0x4e, 0x86, 0xda, 0x86, 0x97, 0x90, 0x00, 0x00, 0xe7, 0x80,
    0x40, 0x15, 0x26, 0x86, 0x75, 0xd1, 0x59, 0xaa, 0x13, 0x09, 0x01, 0x35,
    0x08, 0x04, 0x23, 0x22, 0x25, 0x05, 0x23, 0x24, 0x45, 0x05, 0x23, 0x26,
    0x05, 0x04, 0xc8, 0x04, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80, 0x60, 0x79,
    0xb5, 0xc1, 0x05, 0x05, 0x33, 0x36, 0xa0, 0x00]
theorem ac_c21_ok : ac_c21 <+: List.drop 5376 bootMainClosure0Code := by decide

/-- Bytes 0x1600 to 0x1704 of `bootMainClosure0Code`. -/
def ac_c22 : List Nat :=
  [0x33, 0x36, 0xa0, 0x00, 0x83, 0xa9, 0x85, 0x01, 0x7d, 0x16, 0x51, 0x8d,
    0x85, 0x65, 0x93, 0x85, 0x05, 0x31, 0x8a, 0x95, 0x23, 0xa8, 0x25, 0x01,
    0x23, 0xaa, 0x45, 0x01, 0x23, 0xac, 0x05, 0x00, 0x93, 0x05, 0xf5, 0xff,
    0x05, 0x65, 0x13, 0x05, 0x05, 0x32, 0x0a, 0x95, 0x97, 0xa0, 0x00, 0x00,
    0xe7, 0x80, 0x40, 0x78, 0x5d, 0xdd, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31,
    0x0a, 0x95, 0x0c, 0x49, 0x44, 0x49, 0xe3, 0x88, 0x95, 0xfa, 0x88, 0x41,
    0x4d, 0xd5, 0x88, 0x4d, 0x13, 0x84, 0x05, 0x02, 0xce, 0x85, 0x97, 0x90,
    0x00, 0x00, 0xe7, 0x80, 0xa0, 0x00, 0xa2, 0x85, 0x7d, 0xd1, 0x19, 0xaa,
    0x13, 0x09, 0xf1, 0x7f, 0x13, 0x09, 0x19, 0x09, 0x13, 0x0a, 0xf1, 0x7f,
    0x13, 0x0a, 0x1a, 0x19, 0x08, 0x04, 0x23, 0x22, 0x25, 0x05, 0x23, 0x24,
    0x45, 0x05, 0x23, 0x26, 0x05, 0x04, 0xc8, 0x04, 0x97, 0xa0, 0x00, 0x00,
    0xe7, 0x80, 0xa0, 0x70, 0xad, 0xc5, 0x05, 0x05, 0x33, 0x36, 0xa0, 0x00,
    0x83, 0xa9, 0x05, 0x00, 0x03, 0xab, 0x45, 0x00, 0x7d, 0x16, 0x51, 0x8d,
    0x85, 0x65, 0x93, 0x85, 0x05, 0x31, 0x8a, 0x95, 0x23, 0xa8, 0x25, 0x01,
    0x23, 0xaa, 0x45, 0x01, 0x23, 0xac, 0x05, 0x00, 0x93, 0x05, 0xf5, 0xff,
    0x05, 0x65, 0x13, 0x05, 0x05, 0x32, 0x0a, 0x95, 0x97, 0xa0, 0x00, 0x00,
    0xe7, 0x80, 0x40, 0x6f, 0x4d, 0xdd, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31,
    0x0a, 0x95, 0x10, 0x49, 0x40, 0x49, 0xe3, 0x06, 0x86, 0xfa, 0x08, 0x42,
    0x5d, 0xd1, 0x4c, 0x42, 0x93, 0x04, 0x06, 0x02, 0x4e, 0x86, 0xda, 0x86,
    0x97, 0x90, 0x00, 0x00, 0xe7, 0x80, 0x20, 0x04, 0x26, 0x86, 0x75, 0xd1,
    0x51, 0xa0, 0x13, 0x09, 0xf1, 0x7f, 0x13, 0x09, 0x19, 0x09, 0x08, 0x04,
    0x23, 0x22, 0x25, 0x05, 0x23, 0x24, 0x45, 0x05]
theorem ac_c22_ok : ac_c22 <+: List.drop 5632 bootMainClosure0Code := by decide

/-- Bytes 0x1700 to 0x1804 of `bootMainClosure0Code`. -/
def ac_c23 : List Nat :=
  [0x23, 0x24, 0x45, 0x05, 0x23, 0x26, 0x05, 0x04, 0xc8, 0x04, 0x97, 0xa0,
    0x00, 0x00, 0xe7, 0x80, 0x00, 0x68, 0xbd, 0xc1, 0x05, 0x05, 0x33, 0x36,
    0xa0, 0x00, 0x83, 0xa9, 0x85, 0x01, 0x7d, 0x16, 0x51, 0x8d, 0x85, 0x65,
    0x93, 0x85, 0x05, 0x31, 0x8a, 0x95, 0x23, 0xa8, 0x25, 0x01, 0x23, 0xaa,
    0x45, 0x01, 0x23, 0xac, 0x05, 0x00, 0x93, 0x05, 0xf5, 0xff, 0x05, 0x65,
    0x13, 0x05, 0x05, 0x32, 0x0a, 0x95, 0x97, 0xa0, 0x00, 0x00, 0xe7, 0x80,
    0xe0, 0x66, 0x5d, 0xdd, 0x05, 0x65, 0x13, 0x05, 0x05, 0x31, 0x0a, 0x95,
    0x0c, 0x49, 0x44, 0x49, 0xe3, 0x88, 0x95, 0xfa, 0x88, 0x41, 0x4d, 0xd5,
    0x88, 0x4d, 0x13, 0x84, 0x05, 0x02, 0xce, 0x85, 0x97, 0x90, 0x00, 0x00,
    0xe7, 0x80, 0xa0, 0xed, 0xa2, 0x85, 0x7d, 0xd1, 0x35, 0x44, 0xd5, 0xac,
    0x05, 0x65, 0x13, 0x05, 0x35, 0x34, 0x0a, 0x95, 0x89, 0x65, 0x93, 0x85,
    0x05, 0xed, 0x8a, 0x95, 0x13, 0x06, 0x00, 0x10, 0x97, 0x50, 0x01, 0x00,
    0xe7, 0x80, 0xa0, 0xf8, 0x05, 0x65, 0x13, 0x05, 0x35, 0x44, 0x0a, 0x95,
    0x8c, 0x0e, 0x13, 0x06, 0x00, 0x20, 0x97, 0x50, 0x01, 0x00, 0xe7, 0x80,
    0x40, 0xf7, 0x05, 0x65, 0x13, 0x05, 0x35, 0x64, 0x0a, 0x95, 0x93, 0x05,
    0xf1, 0x7f, 0x93, 0x85, 0x15, 0x09, 0x13, 0x06, 0x00, 0x10, 0x97, 0x50,
    0x01, 0x00, 0xe7, 0x80, 0x80, 0xf5, 0xb7, 0x45, 0xcc, 0x3f, 0x93, 0x85,
    0x15, 0x05, 0x05, 0x65, 0x13, 0x05, 0x05, 0x32, 0x0a, 0x95, 0x13, 0x06,
    0x30, 0x02, 0x97, 0x50, 0x01, 0x00, 0xe7, 0x80, 0xc0, 0xf3, 0x13, 0x05,
    0xf1, 0x7f, 0x13, 0x05, 0x15, 0x5d, 0x85, 0x65, 0x93, 0x85, 0x05, 0x32,
    0x8a, 0x95, 0x13, 0x06, 0x30, 0x42, 0x97, 0x50, 0x01, 0x00, 0xe7, 0x80,
    0x00, 0xf2, 0x09, 0x65, 0x13, 0x05, 0x55, 0x87]
theorem ac_c23_ok : ac_c23 <+: List.drop 5888 bootMainClosure0Code := by decide

/-- Bytes 0x1800 to 0x1904 of `bootMainClosure0Code`. -/
def ac_c24 : List Nat :=
  [0x13, 0x05, 0x55, 0x87, 0x0a, 0x95, 0x93, 0x05, 0xf1, 0x7f, 0x93, 0x85,
    0x15, 0x5d, 0x13, 0x06, 0x30, 0x42, 0x97, 0x50, 0x01, 0x00, 0xe7, 0x80,
    0x40, 0xf0, 0x37, 0x65, 0xcc, 0x3f, 0x13, 0x05, 0x15, 0x62, 0x93, 0x05,
    0xb0, 0x02, 0x05, 0x66, 0x13, 0x06, 0x06, 0x31, 0x0a, 0x96, 0x23, 0x20,
    0xa6, 0x56, 0x23, 0x02, 0xb6, 0x56, 0x13, 0x05, 0xf1, 0x7f, 0x13, 0x05,
    0x15, 0x09, 0xd2, 0x55, 0x23, 0x20, 0xb5, 0x54, 0xe2, 0x55, 0x23, 0x22,
    0xb5, 0x54, 0x23, 0x24, 0x05, 0x54, 0xb7, 0x35, 0x42, 0x4e, 0x93, 0x85,
    0x35, 0x34, 0x13, 0x05, 0xf1, 0x7f, 0x13, 0x05, 0x15, 0x5d, 0x97, 0x90,
    0x00, 0x00, 0xe7, 0x80, 0xa0, 0x8c, 0x2a, 0x84, 0x13, 0x75, 0xf5, 0x0f,
    0x13, 0x05, 0x15, 0xf0, 0x63, 0x1d, 0x05, 0x1e, 0x13, 0x05, 0xf1, 0x7f,
    0x13, 0x05, 0x15, 0x5d, 0x97, 0xb0, 0x00, 0x00, 0xe7, 0x80, 0x80, 0x75,
    0x2a, 0x84, 0x13, 0x75, 0xf5, 0x0f, 0x13, 0x05, 0x15, 0xf0, 0x63, 0x1e,
    0x05, 0x1c, 0x88, 0x0e, 0x93, 0x05, 0xf1, 0x7f, 0x93, 0x85, 0x15, 0x5d,
    0x05, 0x46, 0x85, 0x66, 0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0x20, 0x84,
    0x03, 0x2d, 0x01, 0x35, 0x63, 0x0d, 0x0d, 0x1a, 0x83, 0x2b, 0x41, 0x35,
    0x88, 0x0e, 0x93, 0x05, 0xf1, 0x7f, 0x93, 0x85, 0x15, 0x5d, 0x21, 0x46,
    0x93, 0x06, 0x80, 0x04, 0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80, 0xe0, 0x81,
    0x03, 0x25, 0x01, 0x35, 0x2a, 0xdc, 0x63, 0x0a, 0x05, 0x18, 0x03, 0x25,
    0x41, 0x35, 0x2a, 0xda, 0x88, 0x0e, 0x93, 0x05, 0xf1, 0x7f, 0x93, 0x85,
    0x15, 0x5d, 0x21, 0x46, 0xa1, 0x46, 0x21, 0x49, 0x97, 0xb0, 0x00, 0x00,
    0xe7, 0x80, 0x60, 0x7f, 0x03, 0x25, 0x01, 0x35, 0x63, 0x07, 0x05, 0x16,
    0x83, 0x25, 0x41, 0x35, 0x15, 0x44, 0x63, 0x94]
theorem ac_c24_ok : ac_c24 <+: List.drop 6144 bootMainClosure0Code := by decide

/-- Bytes 0x1900 to 0x1A04 of `bootMainClosure0Code`. -/
def ac_c25 : List Nat :=
  [0x15, 0x44, 0x63, 0x94, 0x25, 0x17, 0x83, 0x45, 0x45, 0x00, 0x2e, 0xd8,
    0x83, 0x49, 0x55, 0x00, 0x83, 0x45, 0x65, 0x00, 0x2e, 0xcc, 0x83, 0x45,
    0x75, 0x00, 0x2e, 0xca, 0x83, 0x44, 0x05, 0x00, 0x83, 0x45, 0x15, 0x00,
    0x2e, 0xce, 0x83, 0x45, 0x25, 0x00, 0x2e, 0xd6, 0x03, 0x45, 0x35, 0x00,
    0x2a, 0xd4, 0x85, 0x46, 0xae, 0x06, 0x88, 0x0e, 0x93, 0x05, 0xf1, 0x7f,
    0x93, 0x85, 0x15, 0x5d, 0x01, 0x46, 0x97, 0xb0, 0x00, 0x00, 0xe7, 0x80,
    0x00, 0x7a, 0x03, 0x29, 0x01, 0x35, 0x63, 0x0c, 0x09, 0x10, 0x03, 0x2b,
    0x41, 0x35, 0x13, 0x75, 0xfb, 0x01, 0x63, 0x18, 0x05, 0x10, 0x88, 0x0e,
    0x93, 0x05, 0xf1, 0x7f, 0x93, 0x85, 0x15, 0x5d, 0x05, 0x46, 0x93, 0x06,
    0x00, 0x40, 0x97, 0xb0, 0x00, 0x00, 0xe7, 0x80, 0x40, 0x77, 0x03, 0x2a,
    0x01, 0x35, 0x63, 0x06, 0x0a, 0x0e, 0x03, 0x2c, 0x41, 0x35, 0x88, 0x0e,
    0x93, 0x05, 0xf1, 0x7f, 0x93, 0x85, 0x15, 0x5d, 0x05, 0x46, 0x89, 0x66,
    0x05, 0x44, 0x97, 0xb0, 0x00, 0x00, 0xe7, 0x80, 0x00, 0x75, 0x03, 0x25,
    0x01, 0x35, 0x61, 0xc5, 0x13, 0x06, 0xf1, 0x7f, 0x13, 0x06, 0x16, 0x09,
    0x83, 0x25, 0x46, 0x54, 0x03, 0x26, 0x86, 0x54, 0x63, 0x1d, 0xb6, 0x0a,
    0xa2, 0x09, 0xe2, 0x45, 0xc2, 0x05, 0x52, 0x46, 0x62, 0x06, 0xc2, 0x56,
    0xb3, 0xe6, 0xd9, 0x00, 0xd1, 0x8d, 0xd5, 0x8d, 0x72, 0x46, 0x22, 0x06,
    0xb2, 0x56, 0xc2, 0x06, 0x22, 0x57, 0x62, 0x07, 0x45, 0x8e, 0xd9, 0x8e,
    0x55, 0x8e, 0x83, 0x26, 0x41, 0x35, 0x13, 0xd7, 0x8b, 0x00, 0x93, 0xd7,
    0x0b, 0x01, 0x93, 0xd4, 0x8b, 0x01, 0x05, 0x68, 0x13, 0x08, 0x08, 0x31,
    0x33, 0x04, 0x01, 0x01, 0x23, 0x28, 0xa4, 0x01, 0x23, 0x0a, 0x74, 0x01,
    0xa3, 0x0a, 0xe4, 0x00, 0x23, 0x0b, 0xf4, 0x00]
theorem ac_c25_ok : ac_c25 <+: List.drop 6400 bootMainClosure0Code := by decide

/-- Bytes 0x1A00 to 0x1B00 of `bootMainClosure0Code`. -/
def ac_c26 : List Nat :=
  [0x23, 0x0b, 0xf4, 0x00, 0xa3, 0x0b, 0x94, 0x00, 0x62, 0x57, 0x18, 0xcc,
    0x52, 0x57, 0x58, 0xcc, 0x23, 0x20, 0x24, 0x03, 0x23, 0x22, 0x64, 0x03,
    0x23, 0x24, 0x44, 0x03, 0x23, 0x26, 0x84, 0x03, 0x08, 0xd8, 0x54, 0xd8,
    0x10, 0xdc, 0x4c, 0xdc, 0x13, 0x05, 0xf1, 0x7f, 0x13, 0x05, 0x15, 0x5d,
    0x85, 0x65, 0x93, 0x85, 0x05, 0x32, 0x8a, 0x95, 0x09, 0x66, 0x13, 0x06,
    0x06, 0x87, 0x0a, 0x96, 0x34, 0x02, 0x97, 0xc0, 0x00, 0x00, 0xe7, 0x80,
    0xa0, 0xa1, 0x13, 0x05, 0xf1, 0x7f, 0x13, 0x05, 0x15, 0x09, 0x03, 0x45,
    0x05, 0x54, 0x09, 0xcd, 0x13, 0x05, 0xf1, 0x7f, 0x13, 0x05, 0x15, 0x09,
    0x03, 0x44, 0x15, 0x54, 0x19, 0xa0, 0x03, 0x44, 0x41, 0x35, 0xa2, 0x8a,
    0x6f, 0xe0, 0xbf, 0xd6, 0x13, 0x05, 0xf1, 0x7f, 0x13, 0x05, 0x15, 0x09,
    0x03, 0x24, 0xc5, 0x54, 0x03, 0x29, 0x85, 0x54, 0x12, 0x55, 0x63, 0x06,
    0xa4, 0x00, 0x12, 0x55, 0x33, 0x35, 0x85, 0x00, 0x21, 0xa0, 0x02, 0x55,
    0x33, 0x35, 0x25, 0x01, 0x01, 0xc5, 0x13, 0x04, 0x50, 0x02, 0xc1, 0xbf,
    0x86, 0x44, 0x13, 0x85, 0x14, 0x00, 0x2c, 0x1c, 0x2d, 0x46, 0x97, 0x50,
    0x01, 0x00, 0xe7, 0x80, 0x00, 0xc7, 0x13, 0x85, 0xd4, 0x00, 0x93, 0x05,
    0x91, 0x13, 0x13, 0x06, 0xf0, 0x0f, 0x97, 0x50, 0x01, 0x00, 0xe7, 0x80,
    0xc0, 0xc5, 0x03, 0x45, 0x61, 0x13, 0x83, 0x45, 0x71, 0x13, 0x03, 0x46,
    0x81, 0x13, 0x23, 0x86, 0xb4, 0x11, 0xa3, 0x86, 0xa4, 0x10, 0x23, 0x87,
    0xb4, 0x10, 0xa3, 0x87, 0xc4, 0x10, 0x23, 0xa8, 0x24, 0x11, 0x23, 0xaa,
    0x84, 0x10, 0x23, 0x8c, 0xb4, 0x11, 0x16, 0x45, 0x23, 0xa0, 0xa4, 0x12,
    0x23, 0x80, 0x54, 0x01, 0x23, 0x86, 0x94, 0x01, 0x23, 0x84, 0xb4, 0x13,
    0x6f, 0xe0, 0x8f, 0xe8]
theorem ac_c26_ok : ac_c26 <+: List.drop 6656 bootMainClosure0Code := by decide

theorem ac_at_0 : fetchRel bootMainClosure0Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF00, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2 : fetchRel bootMainClosure0Code 0x2 = some (.store .sw sp ra 0xFC, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4 : fetchRel bootMainClosure0Code 0x4 = some (.store .sw sp (8 : Fin 32) 0xF8, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6 : fetchRel bootMainClosure0Code 0x6 = some (.store .sw sp (9 : Fin 32) 0xF4, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8 : fetchRel bootMainClosure0Code 0x8 = some (.store .sw sp (18 : Fin 32) 0xF0, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a : fetchRel bootMainClosure0Code 0xA = some (.store .sw sp (19 : Fin 32) 0xEC, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c : fetchRel bootMainClosure0Code 0xC = some (.store .sw sp (20 : Fin 32) 0xE8, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e : fetchRel bootMainClosure0Code 0xE = some (.store .sw sp (21 : Fin 32) 0xE4, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10 : fetchRel bootMainClosure0Code 0x10 = some (.store .sw sp (22 : Fin 32) 0xE0, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12 : fetchRel bootMainClosure0Code 0x12 = some (.store .sw sp (23 : Fin 32) 0xDC, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14 : fetchRel bootMainClosure0Code 0x14 = some (.store .sw sp (24 : Fin 32) 0xD8, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16 : fetchRel bootMainClosure0Code 0x16 = some (.store .sw sp (25 : Fin 32) 0xD4, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18 : fetchRel bootMainClosure0Code 0x18 = some (.store .sw sp (26 : Fin 32) 0xD0, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a : fetchRel bootMainClosure0Code 0x1A = some (.store .sw sp (27 : Fin 32) 0xCC, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1c : fetchRel bootMainClosure0Code 0x1C = some (.lui a4 0x2000, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1e : fetchRel bootMainClosure0Code 0x1E = some (.aluImm .add a4 a4 0xFFFFFF20, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_22 : fetchRel bootMainClosure0Code 0x22 = some (.alu .sub sp sp a4, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_26 : fetchRel bootMainClosure0Code 0x26 = some (.alu .add (8 : Fin 32) x0 a3, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_28 : fetchRel bootMainClosure0Code 0x28 = some (.alu .add (21 : Fin 32) x0 a2, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2a : fetchRel bootMainClosure0Code 0x2A = some (.alu .add (26 : Fin 32) x0 a1, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2c : fetchRel bootMainClosure0Code 0x2C = some (.alu .add (19 : Fin 32) x0 a0, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2e : fetchRel bootMainClosure0Code 0x2E = some (.lui (24 : Fin 32) 0x210000, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_32 : fetchRel bootMainClosure0Code 0x32 = some (.branch .bne a3 x0 0x6, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_34 : fetchRel bootMainClosure0Code 0x34 = some (.lui (24 : Fin 32) 0x30000, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_38 : fetchRel bootMainClosure0Code 0x38 = some (.aluImm .add a0 sp 0x48, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3a : fetchRel bootMainClosure0Code 0x3A = some (.aluImm .add a2 x0 0x20, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3e : fetchRel bootMainClosure0Code 0x3E = some (.aluImm .add a1 x0 0x0, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_40 : fetchRel bootMainClosure0Code 0x40 = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_44 : fetchRel bootMainClosure0Code 0x44 = some (.jalr ra ra 0x66E, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_48 : fetchRel bootMainClosure0Code 0x48 = some (.aluImm .add a1 sp 0x48, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4a : fetchRel bootMainClosure0Code 0x4A = some (.aluImm .add a2 x0 0x20, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4e : fetchRel bootMainClosure0Code 0x4E = some (.alu .add a0 x0 (24 : Fin 32), 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_50 : fetchRel bootMainClosure0Code 0x50 = some (.auipc ra 0x17000, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_54 : fetchRel bootMainClosure0Code 0x54 = some (.jalr ra ra 0xFFFFFB84, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_58 : fetchRel bootMainClosure0Code 0x58 = some (.branch .beq a0 x0 0x112, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5c : fetchRel bootMainClosure0Code 0x5C = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5e : fetchRel bootMainClosure0Code 0x5E = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_62 : fetchRel bootMainClosure0Code 0x62 = some (.alu .add (9 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_66 : fetchRel bootMainClosure0Code 0x66 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_68 : fetchRel bootMainClosure0Code 0x68 = some (.aluImm .add a0 a0 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6c : fetchRel bootMainClosure0Code 0x6C = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6e : fetchRel bootMainClosure0Code 0x6E = some (.aluImm .add a1 sp 0x48, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_70 : fetchRel bootMainClosure0Code 0x70 = some (.auipc ra 0xD000, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_74 : fetchRel bootMainClosure0Code 0x74 = some (.jalr ra ra 0x23E, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_78 : fetchRel bootMainClosure0Code 0x78 = some (.load .lbu a0 (9 : Fin 32) 0x560, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7c : fetchRel bootMainClosure0Code 0x7C = some (.branch .bne a0 x0 0xEE, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7e : fetchRel bootMainClosure0Code 0x7E = some (.load .lw a0 (9 : Fin 32) 0x564, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_82 : fetchRel bootMainClosure0Code 0x82 = some (.alu .add a1 a0 (24 : Fin 32), 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_86 : fetchRel bootMainClosure0Code 0x86 = some (.store .sw sp a1 0x44, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_88 : fetchRel bootMainClosure0Code 0x88 = some (.branch .bltu a1 a0 0xE2, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8c : fetchRel bootMainClosure0Code 0x8C = some (.load .lw (27 : Fin 32) (9 : Fin 32) 0x568, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_90 : fetchRel bootMainClosure0Code 0x90 = some (.aluImm .add a0 x0 0x114, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_94 : fetchRel bootMainClosure0Code 0x94 = some (.alu .add (22 : Fin 32) x0 (27 : Fin 32), 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_96 : fetchRel bootMainClosure0Code 0x96 = some (.branch .bltu (27 : Fin 32) a0 0x8, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9a : fetchRel bootMainClosure0Code 0x9A = some (.aluImm .add (22 : Fin 32) x0 0x114, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9e : fetchRel bootMainClosure0Code 0x9E = some (.load .lw (18 : Fin 32) (9 : Fin 32) 0x56C, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a2 : fetchRel bootMainClosure0Code 0xA2 = some (.load .lw (20 : Fin 32) (9 : Fin 32) 0x570, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a6 : fetchRel bootMainClosure0Code 0xA6 = some (.load .lw (23 : Fin 32) (9 : Fin 32) 0x574, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_aa : fetchRel bootMainClosure0Code 0xAA = some (.load .lw (9 : Fin 32) (9 : Fin 32) 0x578, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ae : fetchRel bootMainClosure0Code 0xAE = some (.lui a0 0xC000, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b0 : fetchRel bootMainClosure0Code 0xB0 = some (.aluImm .add a0 a0 0xFFFFF840, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b4 : fetchRel bootMainClosure0Code 0xB4 = some (.alu .add (25 : Fin 32) (21 : Fin 32) a0, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b8 : fetchRel bootMainClosure0Code 0xB8 = some (.load .lw a0 sp 0x44, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ba : fetchRel bootMainClosure0Code 0xBA = some (.alu .add a1 x0 (25 : Fin 32), 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bc : fetchRel bootMainClosure0Code 0xBC = some (.alu .add a2 x0 (22 : Fin 32), 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_be : fetchRel bootMainClosure0Code 0xBE = some (.auipc ra 0x17000, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c2 : fetchRel bootMainClosure0Code 0xC2 = some (.jalr ra ra 0xFFFFFB16, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c6 : fetchRel bootMainClosure0Code 0xC6 = some (.branch .beq a0 x0 0xA4, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c8 : fetchRel bootMainClosure0Code 0xC8 = some (.store .sw sp (23 : Fin 32) 0x30, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ca : fetchRel bootMainClosure0Code 0xCA = some (.store .sw sp (20 : Fin 32) 0x38, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cc : fetchRel bootMainClosure0Code 0xCC = some (.store .sw sp (8 : Fin 32) 0x3C, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ce : fetchRel bootMainClosure0Code 0xCE = some (.store .sw sp (19 : Fin 32) 0x40, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d0 : fetchRel bootMainClosure0Code 0xD0 = some (.store .sb sp x0 0xA7, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d4 : fetchRel bootMainClosure0Code 0xD4 = some (.aluImm .add a0 sp 0xA8, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d6 : fetchRel bootMainClosure0Code 0xD6 = some (.lui a1 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_da : fetchRel bootMainClosure0Code 0xDA = some (.aluImm .add a1 a1 0x118, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_de : fetchRel bootMainClosure0Code 0xDE = some (.aluImm .add a2 x0 0x20, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e2 : fetchRel bootMainClosure0Code 0xE2 = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e6 : fetchRel bootMainClosure0Code 0xE6 = some (.jalr ra ra 0x634, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ea : fetchRel bootMainClosure0Code 0xEA = some (.aluImm .add (19 : Fin 32) x0 0x0, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ec : fetchRel bootMainClosure0Code 0xEC = some (.store .sw sp x0 0xC8, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ee : fetchRel bootMainClosure0Code 0xEE = some (.store .sw sp x0 0xCC, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f0 : fetchRel bootMainClosure0Code 0xF0 = some (.lui (20 : Fin 32) 0x4000, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f2 : fetchRel bootMainClosure0Code 0xF2 = some (.aluImm .add (23 : Fin 32) x0 0x5, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f4 : fetchRel bootMainClosure0Code 0xF4 = some (.store .sw sp (21 : Fin 32) 0x34, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f6 : fetchRel bootMainClosure0Code 0xF6 = some (.alu .add (20 : Fin 32) (20 : Fin 32) (21 : Fin 32), 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f8 : fetchRel bootMainClosure0Code 0xF8 = some (.aluImm .sll (23 : Fin 32) (23 : Fin 32) 0xB, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fa : fetchRel bootMainClosure0Code 0xFA = some (.load .lw (8 : Fin 32) sp 0x44, 2) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fc : fetchRel bootMainClosure0Code 0xFC = some (.branch .beq (27 : Fin 32) x0 0x38, 4) :=
  (fetchRel_chunk ac_c0_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_100 : fetchRel bootMainClosure0Code 0x100 = some (.alu .sub (21 : Fin 32) (27 : Fin 32) (19 : Fin 32), 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_104 : fetchRel bootMainClosure0Code 0x104 = some (.branch .bltu (21 : Fin 32) (23 : Fin 32) 0x6, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_108 : fetchRel bootMainClosure0Code 0x108 = some (.alu .add (21 : Fin 32) x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10a : fetchRel bootMainClosure0Code 0x10A = some (.alu .add a0 (19 : Fin 32) (8 : Fin 32), 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10e : fetchRel bootMainClosure0Code 0x10E = some (.branch .bltu a0 (19 : Fin 32) 0x58, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_112 : fetchRel bootMainClosure0Code 0x112 = some (.alu .add a1 x0 (20 : Fin 32), 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_114 : fetchRel bootMainClosure0Code 0x114 = some (.alu .add a2 x0 (21 : Fin 32), 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_116 : fetchRel bootMainClosure0Code 0x116 = some (.auipc ra 0x17000, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11a : fetchRel bootMainClosure0Code 0x11A = some (.jalr ra ra 0xFFFFFABE, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11e : fetchRel bootMainClosure0Code 0x11E = some (.branch .beq a0 x0 0x48, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_120 : fetchRel bootMainClosure0Code 0x120 = some (.aluImm .add a0 sp 0x68, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_122 : fetchRel bootMainClosure0Code 0x122 = some (.alu .add a1 x0 (20 : Fin 32), 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_124 : fetchRel bootMainClosure0Code 0x124 = some (.alu .add a2 x0 (21 : Fin 32), 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_126 : fetchRel bootMainClosure0Code 0x126 = some (.auipc ra 0x7000, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12a : fetchRel bootMainClosure0Code 0x12A = some (.jalr ra ra 0xFFFFFA52, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12e : fetchRel bootMainClosure0Code 0x12E = some (.alu .add (19 : Fin 32) (19 : Fin 32) (21 : Fin 32), 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_130 : fetchRel bootMainClosure0Code 0x130 = some (.branch .bltu (19 : Fin 32) (27 : Fin 32) 0xFFFFFFD0, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_134 : fetchRel bootMainClosure0Code 0x134 = some (.aluImm .add a0 sp 0xD4, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_136 : fetchRel bootMainClosure0Code 0x136 = some (.aluImm .add a1 sp 0x68, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_138 : fetchRel bootMainClosure0Code 0x138 = some (.auipc ra 0x7000, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13c : fetchRel bootMainClosure0Code 0x13C = some (.jalr ra ra 0xFFFFF8B0, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_140 : fetchRel bootMainClosure0Code 0x140 = some (.lui a0 0x4000, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_142 : fetchRel bootMainClosure0Code 0x142 = some (.load .lw (8 : Fin 32) sp 0x38, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_144 : fetchRel bootMainClosure0Code 0x144 = some (.branch .bltu a0 (8 : Fin 32) 0x22, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_148 : fetchRel bootMainClosure0Code 0x148 = some (.alu .add a0 (18 : Fin 32) (24 : Fin 32), 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14c : fetchRel bootMainClosure0Code 0x14C = some (.branch .bltu a0 (18 : Fin 32) 0x1A, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_150 : fetchRel bootMainClosure0Code 0x150 = some (.load .lw a1 sp 0x34, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_152 : fetchRel bootMainClosure0Code 0x152 = some (.alu .add a2 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_154 : fetchRel bootMainClosure0Code 0x154 = some (.auipc ra 0x17000, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_158 : fetchRel bootMainClosure0Code 0x158 = some (.jalr ra ra 0xFFFFFA80, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15c : fetchRel bootMainClosure0Code 0x15C = some (.branch .beq a0 x0 0xA, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15e : fetchRel bootMainClosure0Code 0x15E = some (.load .lw a0 sp 0x30, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_160 : fetchRel bootMainClosure0Code 0x160 = some (.alu .add (24 : Fin 32) (24 : Fin 32) a0, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_162 : fetchRel bootMainClosure0Code 0x162 = some (.branch .bgeu (24 : Fin 32) a0 0x48, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_166 : fetchRel bootMainClosure0Code 0x166 = some (.load .lw (19 : Fin 32) sp 0x40, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_168 : fetchRel bootMainClosure0Code 0x168 = some (.load .lw (8 : Fin 32) sp 0x3C, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16a : fetchRel bootMainClosure0Code 0x16A = some (.aluImm .add a1 (8 : Fin 32) 0xA, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16e : fetchRel bootMainClosure0Code 0x16E = some (.lui a0 0x3FCC6000, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_172 : fetchRel bootMainClosure0Code 0x172 = some (.aluImm .add a0 a0 0x6C0, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_176 : fetchRel bootMainClosure0Code 0x176 = some (.auipc ra 0xFFC60000, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17a : fetchRel bootMainClosure0Code 0x17A = some (.jalr ra ra 0xFFFFFE24, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17e : fetchRel bootMainClosure0Code 0x17E = some (.aluImm .add a0 x0 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_180 : fetchRel bootMainClosure0Code 0x180 = some (.store .sb (19 : Fin 32) a0 0xC, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_184 : fetchRel bootMainClosure0Code 0x184 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_186 : fetchRel bootMainClosure0Code 0x186 = some (.aluImm .add a0 a0 0xFFFFFF20, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18a : fetchRel bootMainClosure0Code 0x18A = some (.alu .add sp sp a0, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18c : fetchRel bootMainClosure0Code 0x18C = some (.load .lw ra sp 0xFC, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18e : fetchRel bootMainClosure0Code 0x18E = some (.load .lw (8 : Fin 32) sp 0xF8, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_190 : fetchRel bootMainClosure0Code 0x190 = some (.load .lw (9 : Fin 32) sp 0xF4, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_192 : fetchRel bootMainClosure0Code 0x192 = some (.load .lw (18 : Fin 32) sp 0xF0, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_194 : fetchRel bootMainClosure0Code 0x194 = some (.load .lw (19 : Fin 32) sp 0xEC, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_196 : fetchRel bootMainClosure0Code 0x196 = some (.load .lw (20 : Fin 32) sp 0xE8, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_198 : fetchRel bootMainClosure0Code 0x198 = some (.load .lw (21 : Fin 32) sp 0xE4, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19a : fetchRel bootMainClosure0Code 0x19A = some (.load .lw (22 : Fin 32) sp 0xE0, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19c : fetchRel bootMainClosure0Code 0x19C = some (.load .lw (23 : Fin 32) sp 0xDC, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19e : fetchRel bootMainClosure0Code 0x19E = some (.load .lw (24 : Fin 32) sp 0xD8, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a0 : fetchRel bootMainClosure0Code 0x1A0 = some (.load .lw (25 : Fin 32) sp 0xD4, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a2 : fetchRel bootMainClosure0Code 0x1A2 = some (.load .lw (26 : Fin 32) sp 0xD0, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a4 : fetchRel bootMainClosure0Code 0x1A4 = some (.load .lw (27 : Fin 32) sp 0xCC, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a6 : fetchRel bootMainClosure0Code 0x1A6 = some (.aluImm .add sp sp 0x100, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a8 : fetchRel bootMainClosure0Code 0x1A8 = some (.jalr x0 ra 0x0, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1aa : fetchRel bootMainClosure0Code 0x1AA = some (.store .sw sp (25 : Fin 32) 0xF4, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ac : fetchRel bootMainClosure0Code 0x1AC = some (.store .sw sp (22 : Fin 32) 0xF8, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ae : fetchRel bootMainClosure0Code 0x1AE = some (.store .sw sp (27 : Fin 32) 0x104, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1b2 : fetchRel bootMainClosure0Code 0x1B2 = some (.aluImm .add a0 sp 0x108, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1b4 : fetchRel bootMainClosure0Code 0x1B4 = some (.aluImm .add a1 sp 0xD4, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1b6 : fetchRel bootMainClosure0Code 0x1B6 = some (.aluImm .add a2 x0 0x20, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ba : fetchRel bootMainClosure0Code 0x1BA = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1be : fetchRel bootMainClosure0Code 0x1BE = some (.jalr ra ra 0x55C, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1c2 : fetchRel bootMainClosure0Code 0x1C2 = some (.load .lw a0 sp 0x34, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1c4 : fetchRel bootMainClosure0Code 0x1C4 = some (.store .sw sp a0 0xFC, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1c6 : fetchRel bootMainClosure0Code 0x1C6 = some (.aluImm .add a0 sp 0x100, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1c8 : fetchRel bootMainClosure0Code 0x1C8 = some (.store .sw a0 (8 : Fin 32) 0x0, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ca : fetchRel bootMainClosure0Code 0x1CA = some (.store .sw a0 (24 : Fin 32) 0x28, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ce : fetchRel bootMainClosure0Code 0x1CE = some (.store .sw a0 (9 : Fin 32) 0x2C, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1d0 : fetchRel bootMainClosure0Code 0x1D0 = some (.alu .add (23 : Fin 32) x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1d2 : fetchRel bootMainClosure0Code 0x1D2 = some (.store .sw a0 (9 : Fin 32) 0x30, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1d4 : fetchRel bootMainClosure0Code 0x1D4 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1d6 : fetchRel bootMainClosure0Code 0x1D6 = some (.aluImm .add a0 a0 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1da : fetchRel bootMainClosure0Code 0x1DA = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1dc : fetchRel bootMainClosure0Code 0x1DC = some (.alu .add a1 x0 (25 : Fin 32), 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1de : fetchRel bootMainClosure0Code 0x1DE = some (.alu .add a2 x0 (22 : Fin 32), 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1e0 : fetchRel bootMainClosure0Code 0x1E0 = some (.alu .add a3 x0 (27 : Fin 32), 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1e2 : fetchRel bootMainClosure0Code 0x1E2 = some (.auipc ra 0xD000, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1e6 : fetchRel bootMainClosure0Code 0x1E6 = some (.jalr ra ra 0xFFFFF9BE, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ea : fetchRel bootMainClosure0Code 0x1EA = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ec : fetchRel bootMainClosure0Code 0x1EC = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1f0 : fetchRel bootMainClosure0Code 0x1F0 = some (.alu .add (9 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1f4 : fetchRel bootMainClosure0Code 0x1F4 = some (.load .lbu (25 : Fin 32) (9 : Fin 32) 0x56C, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1f8 : fetchRel bootMainClosure0Code 0x1F8 = some (.load .lbu (21 : Fin 32) (9 : Fin 32) 0x560, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1fc : fetchRel bootMainClosure0Code 0x1FC = some (.aluImm .add a0 (25 : Fin 32) 0xFFFFFF01, 4) :=
  (fetchRel_chunk ac_c1_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_200 : fetchRel bootMainClosure0Code 0x200 = some (.branch .beq a0 x0 0x5D6, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_204 : fetchRel bootMainClosure0Code 0x204 = some (.load .lbu (17 : Fin 32) (9 : Fin 32) 0x569, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_208 : fetchRel bootMainClosure0Code 0x208 = some (.load .lbu a1 (9 : Fin 32) 0x56A, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_20c : fetchRel bootMainClosure0Code 0x20C = some (.load .lbu a6 (9 : Fin 32) 0x56B, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_210 : fetchRel bootMainClosure0Code 0x210 = some (.load .lbu (5 : Fin 32) (9 : Fin 32) 0x565, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_214 : fetchRel bootMainClosure0Code 0x214 = some (.load .lbu (6 : Fin 32) (9 : Fin 32) 0x566, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_218 : fetchRel bootMainClosure0Code 0x218 = some (.load .lbu a5 (9 : Fin 32) 0x561, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_21c : fetchRel bootMainClosure0Code 0x21C = some (.load .lbu (8 : Fin 32) (9 : Fin 32) 0x562, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_220 : fetchRel bootMainClosure0Code 0x220 = some (.load .lbu a2 (9 : Fin 32) 0x563, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_224 : fetchRel bootMainClosure0Code 0x224 = some (.load .lbu a0 (9 : Fin 32) 0x564, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_228 : fetchRel bootMainClosure0Code 0x228 = some (.aluImm .sll a1 a1 0x8, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_22a : fetchRel bootMainClosure0Code 0x22A = some (.alu .or (17 : Fin 32) a1 (17 : Fin 32), 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_22e : fetchRel bootMainClosure0Code 0x22E = some (.load .lbu a3 (9 : Fin 32) 0x567, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_232 : fetchRel bootMainClosure0Code 0x232 = some (.load .lbu a4 (9 : Fin 32) 0x568, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_236 : fetchRel bootMainClosure0Code 0x236 = some (.aluImm .sll (6 : Fin 32) (6 : Fin 32) 0x8, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_238 : fetchRel bootMainClosure0Code 0x238 = some (.alu .or a1 (6 : Fin 32) (5 : Fin 32), 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_23c : fetchRel bootMainClosure0Code 0x23C = some (.aluImm .sll (8 : Fin 32) (8 : Fin 32) 0x8, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_23e : fetchRel bootMainClosure0Code 0x23E = some (.aluImm .sll a2 a2 0x10, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_240 : fetchRel bootMainClosure0Code 0x240 = some (.aluImm .sll a0 a0 0x18, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_242 : fetchRel bootMainClosure0Code 0x242 = some (.alu .or a5 a5 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_244 : fetchRel bootMainClosure0Code 0x244 = some (.alu .or a0 a0 a2, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_246 : fetchRel bootMainClosure0Code 0x246 = some (.aluImm .sll a3 a3 0x10, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_248 : fetchRel bootMainClosure0Code 0x248 = some (.aluImm .sll a4 a4 0x18, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_24a : fetchRel bootMainClosure0Code 0x24A = some (.alu .or a3 a3 a4, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_24c : fetchRel bootMainClosure0Code 0x24C = some (.alu .or a0 a0 a5, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_24e : fetchRel bootMainClosure0Code 0x24E = some (.alu .or a1 a1 a3, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_250 : fetchRel bootMainClosure0Code 0x250 = some (.store .sw sp a0 0x238, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_254 : fetchRel bootMainClosure0Code 0x254 = some (.store .sw sp a1 0x23C, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_258 : fetchRel bootMainClosure0Code 0x258 = some (.store .sh sp (17 : Fin 32) 0x240, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_25c : fetchRel bootMainClosure0Code 0x25C = some (.store .sb sp a6 0x242, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_260 : fetchRel bootMainClosure0Code 0x260 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_262 : fetchRel bootMainClosure0Code 0x262 = some (.aluImm .add a0 a0 0xFFFFF87D, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_266 : fetchRel bootMainClosure0Code 0x266 = some (.alu .add a1 sp a0, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_26a : fetchRel bootMainClosure0Code 0x26A = some (.aluImm .add a0 sp 0x139, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_26e : fetchRel bootMainClosure0Code 0x26E = some (.aluImm .add a2 x0 0xFF, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_272 : fetchRel bootMainClosure0Code 0x272 = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_276 : fetchRel bootMainClosure0Code 0x276 = some (.jalr ra ra 0x4A4, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_27a : fetchRel bootMainClosure0Code 0x27A = some (.load .lbu a0 (9 : Fin 32) 0x66E, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_27e : fetchRel bootMainClosure0Code 0x27E = some (.load .lbu a1 (9 : Fin 32) 0x66D, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_282 : fetchRel bootMainClosure0Code 0x282 = some (.load .lbu (27 : Fin 32) (9 : Fin 32) 0x66C, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_286 : fetchRel bootMainClosure0Code 0x286 = some (.load .lbu a2 (9 : Fin 32) 0x66F, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_28a : fetchRel bootMainClosure0Code 0x28A = some (.aluImm .sll a0 a0 0x8, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_28c : fetchRel bootMainClosure0Code 0x28C = some (.alu .or a0 a0 a1, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_28e : fetchRel bootMainClosure0Code 0x28E = some (.aluImm .and a1 (26 : Fin 32) 0xFF, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_292 : fetchRel bootMainClosure0Code 0x292 = some (.store .sh sp a0 0x136, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_296 : fetchRel bootMainClosure0Code 0x296 = some (.store .sb sp a2 0x138, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_29a : fetchRel bootMainClosure0Code 0x29A = some (.branch .bgeu (27 : Fin 32) a1 0xC, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_29e : fetchRel bootMainClosure0Code 0x29E = some (.aluImm .add (21 : Fin 32) x0 0x12, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2a0 : fetchRel bootMainClosure0Code 0x2A0 = some (.load .lw (19 : Fin 32) sp 0x40, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2a2 : fetchRel bootMainClosure0Code 0x2A2 = some (.load .lw (8 : Fin 32) sp 0x3C, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2a4 : fetchRel bootMainClosure0Code 0x2A4 = some (.jal x0 0x55E, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2a6 : fetchRel bootMainClosure0Code 0x2A6 = some (.lui a0 0x60000, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2aa : fetchRel bootMainClosure0Code 0x2AA = some (.branch .bgeu a0 (23 : Fin 32) 0x8, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2ae : fetchRel bootMainClosure0Code 0x2AE = some (.aluImm .add a0 x0 0x5, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2b0 : fetchRel bootMainClosure0Code 0x2B0 = some (.jal x0 0x184, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2b2 : fetchRel bootMainClosure0Code 0x2B2 = some (.alu .add a1 x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2b4 : fetchRel bootMainClosure0Code 0x2B4 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2b6 : fetchRel bootMainClosure0Code 0x2B6 = some (.aluImm .add a0 a0 0xFFFFFDB0, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2ba : fetchRel bootMainClosure0Code 0x2BA = some (.alu .add (8 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2be : fetchRel bootMainClosure0Code 0x2BE = some (.aluImm .add a0 x0 0x0, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2c0 : fetchRel bootMainClosure0Code 0x2C0 = some (.store .sw (8 : Fin 32) a0 0x0, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2c2 : fetchRel bootMainClosure0Code 0x2C2 = some (.store .sw (8 : Fin 32) a0 0x4, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2c4 : fetchRel bootMainClosure0Code 0x2C4 = some (.aluImm .add a2 x0 0x0, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2c6 : fetchRel bootMainClosure0Code 0x2C6 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2c8 : fetchRel bootMainClosure0Code 0x2C8 = some (.aluImm .add a0 a0 0xFFFFFDB0, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2cc : fetchRel bootMainClosure0Code 0x2CC = some (.alu .add a3 sp a0, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2d0 : fetchRel bootMainClosure0Code 0x2D0 = some (.aluImm .add a4 x0 0x8, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2d2 : fetchRel bootMainClosure0Code 0x2D2 = some (.alu .add a0 x0 (24 : Fin 32), 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2d4 : fetchRel bootMainClosure0Code 0x2D4 = some (.lui a5 0x2000, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2d6 : fetchRel bootMainClosure0Code 0x2D6 = some (.aluImm .add a5 a5 0xFFFFFDB0, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2da : fetchRel bootMainClosure0Code 0x2DA = some (.alu .add (19 : Fin 32) sp a5, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2de : fetchRel bootMainClosure0Code 0x2DE = some (.aluImm .add (9 : Fin 32) x0 0x8, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2e0 : fetchRel bootMainClosure0Code 0x2E0 = some (.auipc ra 0x17000, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2e4 : fetchRel bootMainClosure0Code 0x2E4 = some (.jalr ra ra 0xFFFFFA4C, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2e8 : fetchRel bootMainClosure0Code 0x2E8 = some (.branch .beq a0 x0 0x148, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2ec : fetchRel bootMainClosure0Code 0x2EC = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2ee : fetchRel bootMainClosure0Code 0x2EE = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2f2 : fetchRel bootMainClosure0Code 0x2F2 = some (.alu .add (26 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2f6 : fetchRel bootMainClosure0Code 0x2F6 = some (.store .sw (8 : Fin 32) (19 : Fin 32) 0xC, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2fa : fetchRel bootMainClosure0Code 0x2FA = some (.store .sw (8 : Fin 32) (9 : Fin 32) 0x10, 2) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_2fc : fetchRel bootMainClosure0Code 0x2FC = some (.store .sw (8 : Fin 32) x0 0x14, 4) :=
  (fetchRel_chunk ac_c2_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_300 : fetchRel bootMainClosure0Code 0x300 = some (.lui a1 0x55543000, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_304 : fetchRel bootMainClosure0Code 0x304 = some (.aluImm .add a1 a1 0x343, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_308 : fetchRel bootMainClosure0Code 0x308 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_30a : fetchRel bootMainClosure0Code 0x30A = some (.aluImm .add a0 a0 0xFFFFFDBC, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_30e : fetchRel bootMainClosure0Code 0x30E = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_310 : fetchRel bootMainClosure0Code 0x310 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_314 : fetchRel bootMainClosure0Code 0x314 = some (.jalr ra ra 0xFFFFFE18, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_318 : fetchRel bootMainClosure0Code 0x318 = some (.aluImm .and a1 a0 0xFF, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_31c : fetchRel bootMainClosure0Code 0x31C = some (.aluImm .add a1 a1 0xFFFFFF01, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_320 : fetchRel bootMainClosure0Code 0x320 = some (.branch .bne a1 x0 0x114, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_324 : fetchRel bootMainClosure0Code 0x324 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_326 : fetchRel bootMainClosure0Code 0x326 = some (.aluImm .add a0 a0 0xFFFFFDBC, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_32a : fetchRel bootMainClosure0Code 0x32A = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_32c : fetchRel bootMainClosure0Code 0x32C = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_330 : fetchRel bootMainClosure0Code 0x330 = some (.jalr ra ra 0xFFFFFCFC, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_334 : fetchRel bootMainClosure0Code 0x334 = some (.aluImm .and a1 a0 0x1, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_338 : fetchRel bootMainClosure0Code 0x338 = some (.branch .beq a1 x0 0x6, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_33a : fetchRel bootMainClosure0Code 0x33A = some (.aluImm .srl a0 a0 0x8, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_33c : fetchRel bootMainClosure0Code 0x33C = some (.jal x0 0xF8, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_33e : fetchRel bootMainClosure0Code 0x33E = some (.aluImm .srl a0 a0 0x10, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_340 : fetchRel bootMainClosure0Code 0x340 = some (.aluImm .add a1 x0 0x2, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_342 : fetchRel bootMainClosure0Code 0x342 = some (.branch .bne a0 a1 0xFA, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_346 : fetchRel bootMainClosure0Code 0x346 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_348 : fetchRel bootMainClosure0Code 0x348 = some (.aluImm .add a0 a0 0xFFFFFDBC, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_34c : fetchRel bootMainClosure0Code 0x34C = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_34e : fetchRel bootMainClosure0Code 0x34E = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_352 : fetchRel bootMainClosure0Code 0x352 = some (.jalr ra ra 0xFFFFFCDA, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_356 : fetchRel bootMainClosure0Code 0x356 = some (.aluImm .and a1 a0 0x1, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_35a : fetchRel bootMainClosure0Code 0x35A = some (.branch .bne a1 x0 0xFFFFFFE0, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_35c : fetchRel bootMainClosure0Code 0x35C = some (.aluImm .srl (18 : Fin 32) a0 0x10, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_360 : fetchRel bootMainClosure0Code 0x360 = some (.aluImm .add a0 x0 0x40, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_364 : fetchRel bootMainClosure0Code 0x364 = some (.branch .bltu a0 (18 : Fin 32) 0xFFFFFF4A, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_368 : fetchRel bootMainClosure0Code 0x368 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_36a : fetchRel bootMainClosure0Code 0x36A = some (.aluImm .add a0 a0 0xFFFFFDC8, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_36e : fetchRel bootMainClosure0Code 0x36E = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_370 : fetchRel bootMainClosure0Code 0x370 = some (.aluImm .add a2 x0 0x108, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_374 : fetchRel bootMainClosure0Code 0x374 = some (.aluImm .add a1 x0 0x0, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_376 : fetchRel bootMainClosure0Code 0x376 = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_37a : fetchRel bootMainClosure0Code 0x37A = some (.jalr ra ra 0x338, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_37e : fetchRel bootMainClosure0Code 0x37E = some (.aluImm .add a1 x0 0x8, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_380 : fetchRel bootMainClosure0Code 0x380 = some (.aluImm .add a0 x0 0x0, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_382 : fetchRel bootMainClosure0Code 0x382 = some (.branch .bltu (23 : Fin 32) a1 0xB2, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_386 : fetchRel bootMainClosure0Code 0x386 = some (.aluImm .sll (8 : Fin 32) (18 : Fin 32) 0x2, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_38a : fetchRel bootMainClosure0Code 0x38A = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x8, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_38c : fetchRel bootMainClosure0Code 0x38C = some (.aluImm .add a2 x0 0x8, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_38e : fetchRel bootMainClosure0Code 0x38E = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_390 : fetchRel bootMainClosure0Code 0x390 = some (.aluImm .add a0 a0 0xFFFFFDC8, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_394 : fetchRel bootMainClosure0Code 0x394 = some (.alu .add a3 sp a0, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_398 : fetchRel bootMainClosure0Code 0x398 = some (.alu .add a0 x0 (24 : Fin 32), 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_39a : fetchRel bootMainClosure0Code 0x39A = some (.alu .add a1 x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_39c : fetchRel bootMainClosure0Code 0x39C = some (.alu .add a4 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_39e : fetchRel bootMainClosure0Code 0x39E = some (.lui a5 0x2000, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3a0 : fetchRel bootMainClosure0Code 0x3A0 = some (.aluImm .add a5 a5 0xFFFFFDC8, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3a4 : fetchRel bootMainClosure0Code 0x3A4 = some (.alu .add (19 : Fin 32) sp a5, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3a8 : fetchRel bootMainClosure0Code 0x3A8 = some (.auipc ra 0x17000, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3ac : fetchRel bootMainClosure0Code 0x3AC = some (.jalr ra ra 0xFFFFF984, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3b0 : fetchRel bootMainClosure0Code 0x3B0 = some (.branch .beq a0 x0 0x80, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3b2 : fetchRel bootMainClosure0Code 0x3B2 = some (.aluImm .add a0 x0 0xD, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3b4 : fetchRel bootMainClosure0Code 0x3B4 = some (.aluImm .sll a0 a0 0xB, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3b6 : fetchRel bootMainClosure0Code 0x3B6 = some (.load .lw a1 sp 0x34, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3b8 : fetchRel bootMainClosure0Code 0x3B8 = some (.alu .add a0 a0 a1, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3ba : fetchRel bootMainClosure0Code 0x3BA = some (.store .sw sp a0 0x30, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3bc : fetchRel bootMainClosure0Code 0x3BC = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3be : fetchRel bootMainClosure0Code 0x3BE = some (.aluImm .add a0 a0 0xFFFFFED0, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3c2 : fetchRel bootMainClosure0Code 0x3C2 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3c4 : fetchRel bootMainClosure0Code 0x3C4 = some (.aluImm .add a2 x0 0x108, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3c8 : fetchRel bootMainClosure0Code 0x3C8 = some (.aluImm .add a1 x0 0x0, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3ca : fetchRel bootMainClosure0Code 0x3CA = some (.lui a3 0x2000, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3cc : fetchRel bootMainClosure0Code 0x3CC = some (.aluImm .add a3 a3 0xFFFFFED0, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3d0 : fetchRel bootMainClosure0Code 0x3D0 = some (.alu .add (9 : Fin 32) sp a3, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3d4 : fetchRel bootMainClosure0Code 0x3D4 = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3d8 : fetchRel bootMainClosure0Code 0x3D8 = some (.jalr ra ra 0x2DA, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3dc : fetchRel bootMainClosure0Code 0x3DC = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3de : fetchRel bootMainClosure0Code 0x3DE = some (.aluImm .add a0 a0 0xFFFFFDB0, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3e2 : fetchRel bootMainClosure0Code 0x3E2 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3e4 : fetchRel bootMainClosure0Code 0x3E4 = some (.store .sw a0 (18 : Fin 32) 0x228, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3e8 : fetchRel bootMainClosure0Code 0x3E8 = some (.store .sw a0 (19 : Fin 32) 0x22C, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3ec : fetchRel bootMainClosure0Code 0x3EC = some (.store .sw a0 (8 : Fin 32) 0x230, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3f0 : fetchRel bootMainClosure0Code 0x3F0 = some (.store .sw a0 x0 0x234, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3f4 : fetchRel bootMainClosure0Code 0x3F4 = some (.lui a0 0xFFFFD000, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3f6 : fetchRel bootMainClosure0Code 0x3F6 = some (.aluImm .add (22 : Fin 32) x0 0xFFFFFFFB, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3f8 : fetchRel bootMainClosure0Code 0x3F8 = some (.aluImm .add (19 : Fin 32) a0 0x7FF, 4) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3fc : fetchRel bootMainClosure0Code 0x3FC = some (.aluImm .sll (22 : Fin 32) (22 : Fin 32) 0xB, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_3fe : fetchRel bootMainClosure0Code 0x3FE = some (.branch .beq (8 : Fin 32) x0 0x42, 2) :=
  (fetchRel_chunk ac_c3_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_400 : fetchRel bootMainClosure0Code 0x400 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_402 : fetchRel bootMainClosure0Code 0x402 = some (.aluImm .add a0 a0 0xFFFFF860, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_406 : fetchRel bootMainClosure0Code 0x406 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_408 : fetchRel bootMainClosure0Code 0x408 = some (.lui a1 0x2000, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_40a : fetchRel bootMainClosure0Code 0x40A = some (.aluImm .add a1 a1 0xFFFFFFDC, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_40e : fetchRel bootMainClosure0Code 0x40E = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_410 : fetchRel bootMainClosure0Code 0x410 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_414 : fetchRel bootMainClosure0Code 0x414 = some (.jalr ra ra 0xFFFFFC82, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_418 : fetchRel bootMainClosure0Code 0x418 = some (.load .lbu a0 (26 : Fin 32) 0x550, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_41c : fetchRel bootMainClosure0Code 0x41C = some (.branch .bne a0 x0 0x46, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_41e : fetchRel bootMainClosure0Code 0x41E = some (.load .lw a0 (26 : Fin 32) 0x554, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_422 : fetchRel bootMainClosure0Code 0x422 = some (.store .sw (9 : Fin 32) a0 0x0, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_424 : fetchRel bootMainClosure0Code 0x424 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_426 : fetchRel bootMainClosure0Code 0x426 = some (.alu .add a0 a0 (19 : Fin 32), 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_428 : fetchRel bootMainClosure0Code 0x428 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFC, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_42a : fetchRel bootMainClosure0Code 0x42A = some (.branch .bltu a0 (22 : Fin 32) 0xFFFFFE84, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_42e : fetchRel bootMainClosure0Code 0x42E = some (.jal x0 0xFFFFFFD0, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_430 : fetchRel bootMainClosure0Code 0x430 = some (.aluImm .add a0 x0 0x26, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_434 : fetchRel bootMainClosure0Code 0x434 = some (.load .lw (19 : Fin 32) sp 0x40, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_436 : fetchRel bootMainClosure0Code 0x436 = some (.load .lw (8 : Fin 32) sp 0x3C, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_438 : fetchRel bootMainClosure0Code 0x438 = some (.alu .add (21 : Fin 32) x0 a0, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_43a : fetchRel bootMainClosure0Code 0x43A = some (.jal x0 0x3A0, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_43c : fetchRel bootMainClosure0Code 0x43C = some (.aluImm .add a0 x0 0x3, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_43e : fetchRel bootMainClosure0Code 0x43E = some (.jal x0 0xFFFFFFF6, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_440 : fetchRel bootMainClosure0Code 0x440 = some (.aluImm .add a2 (18 : Fin 32) 0x1, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_444 : fetchRel bootMainClosure0Code 0x444 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_446 : fetchRel bootMainClosure0Code 0x446 = some (.aluImm .add a0 a0 0xFFFFF860, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_44a : fetchRel bootMainClosure0Code 0x44A = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_44c : fetchRel bootMainClosure0Code 0x44C = some (.lui a1 0x2000, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_44e : fetchRel bootMainClosure0Code 0x44E = some (.aluImm .add a1 a1 0xFFFFFED0, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_452 : fetchRel bootMainClosure0Code 0x452 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_454 : fetchRel bootMainClosure0Code 0x454 = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_458 : fetchRel bootMainClosure0Code 0x458 = some (.jalr ra ra 0xFFFFFEBC, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_45c : fetchRel bootMainClosure0Code 0x45C = some (.load .lbu a0 (26 : Fin 32) 0x550, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_460 : fetchRel bootMainClosure0Code 0x460 = some (.branch .beq a0 x0 0x8, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_462 : fetchRel bootMainClosure0Code 0x462 = some (.load .lbu a0 (26 : Fin 32) 0x551, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_466 : fetchRel bootMainClosure0Code 0x466 = some (.jal x0 0xFFFFFFCE, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_468 : fetchRel bootMainClosure0Code 0x468 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_46a : fetchRel bootMainClosure0Code 0x46A = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_46e : fetchRel bootMainClosure0Code 0x46E = some (.alu .add a1 sp a0, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_472 : fetchRel bootMainClosure0Code 0x472 = some (.load .lw a0 a1 0x554, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_476 : fetchRel bootMainClosure0Code 0x476 = some (.lui a2 0x1000, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_478 : fetchRel bootMainClosure0Code 0x478 = some (.aluImm .add a2 a2 0x310, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_47c : fetchRel bootMainClosure0Code 0x47C = some (.alu .add (9 : Fin 32) sp a2, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_480 : fetchRel bootMainClosure0Code 0x480 = some (.load .lw a1 a1 0x558, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_484 : fetchRel bootMainClosure0Code 0x484 = some (.alu .add a0 a0 a1, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_486 : fetchRel bootMainClosure0Code 0x486 = some (.branch .bgeu a0 a1 0x8, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_48a : fetchRel bootMainClosure0Code 0x48A = some (.aluImm .add a0 x0 0x6, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_48c : fetchRel bootMainClosure0Code 0x48C = some (.jal x0 0xFFFFFFA8, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_48e : fetchRel bootMainClosure0Code 0x48E = some (.branch .bgeu (23 : Fin 32) a0 0x8, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_492 : fetchRel bootMainClosure0Code 0x492 = some (.aluImm .add a0 x0 0x0, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_494 : fetchRel bootMainClosure0Code 0x494 = some (.jal x0 0xFFFFFFA0, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_496 : fetchRel bootMainClosure0Code 0x496 = some (.branch .bgeu a0 (23 : Fin 32) 0x8, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_49a : fetchRel bootMainClosure0Code 0x49A = some (.aluImm .add a0 x0 0x1, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_49c : fetchRel bootMainClosure0Code 0x49C = some (.jal x0 0xFFFFFF98, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_49e : fetchRel bootMainClosure0Code 0x49E = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4a0 : fetchRel bootMainClosure0Code 0x4A0 = some (.aluImm .add a0 a0 0xFFFFF872, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4a4 : fetchRel bootMainClosure0Code 0x4A4 = some (.alu .add (18 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4a8 : fetchRel bootMainClosure0Code 0x4A8 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4aa : fetchRel bootMainClosure0Code 0x4AA = some (.aluImm .add a0 a0 0xFFFFFED0, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4ae : fetchRel bootMainClosure0Code 0x4AE = some (.alu .add a1 sp a0, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4b2 : fetchRel bootMainClosure0Code 0x4B2 = some (.aluImm .add a2 x0 0x10C, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4b6 : fetchRel bootMainClosure0Code 0x4B6 = some (.alu .add a0 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4b8 : fetchRel bootMainClosure0Code 0x4B8 = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4bc : fetchRel bootMainClosure0Code 0x4BC = some (.jalr ra ra 0x25E, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4c0 : fetchRel bootMainClosure0Code 0x4C0 = some (.aluImm .add (8 : Fin 32) sp 0x352, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4c4 : fetchRel bootMainClosure0Code 0x4C4 = some (.aluImm .add a2 x0 0x10C, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4c8 : fetchRel bootMainClosure0Code 0x4C8 = some (.alu .add a0 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4ca : fetchRel bootMainClosure0Code 0x4CA = some (.alu .add a1 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4cc : fetchRel bootMainClosure0Code 0x4CC = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4d0 : fetchRel bootMainClosure0Code 0x4D0 = some (.jalr ra ra 0x24A, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4d4 : fetchRel bootMainClosure0Code 0x4D4 = some (.aluImm .add a0 sp 0x244, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4d6 : fetchRel bootMainClosure0Code 0x4D6 = some (.aluImm .add a2 x0 0x10C, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4da : fetchRel bootMainClosure0Code 0x4DA = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4dc : fetchRel bootMainClosure0Code 0x4DC = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4e0 : fetchRel bootMainClosure0Code 0x4E0 = some (.jalr ra ra 0x23A, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4e4 : fetchRel bootMainClosure0Code 0x4E4 = some (.load .lw a0 sp 0x34C, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4e8 : fetchRel bootMainClosure0Code 0x4E8 = some (.store .sw sp a0 0x1C, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4ea : fetchRel bootMainClosure0Code 0x4EA = some (.lui a1 0x3FCC5000, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4ee : fetchRel bootMainClosure0Code 0x4EE = some (.aluImm .add a1 a1 0x309, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4f2 : fetchRel bootMainClosure0Code 0x4F2 = some (.lui a2 0x1000, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4f4 : fetchRel bootMainClosure0Code 0x4F4 = some (.aluImm .add a2 a2 0x318, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4f8 : fetchRel bootMainClosure0Code 0x4F8 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4fa : fetchRel bootMainClosure0Code 0x4FA = some (.aluImm .add a0 a0 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_4fe : fetchRel bootMainClosure0Code 0x4FE = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c4_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_500 : fetchRel bootMainClosure0Code 0x500 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_504 : fetchRel bootMainClosure0Code 0x504 = some (.jalr ra ra 0x298, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_508 : fetchRel bootMainClosure0Code 0x508 = some (.load .lw (8 : Fin 32) (9 : Fin 32) 0x560, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_50c : fetchRel bootMainClosure0Code 0x50C = some (.branch .beq (8 : Fin 32) x0 0x276, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_510 : fetchRel bootMainClosure0Code 0x510 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_512 : fetchRel bootMainClosure0Code 0x512 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_516 : fetchRel bootMainClosure0Code 0x516 = some (.alu .add (19 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_51a : fetchRel bootMainClosure0Code 0x51A = some (.aluImm .add a1 (19 : Fin 32) 0x500, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_51e : fetchRel bootMainClosure0Code 0x51E = some (.load .lw (9 : Fin 32) a1 0x64, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_520 : fetchRel bootMainClosure0Code 0x520 = some (.load .lw a0 a1 0x70, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_522 : fetchRel bootMainClosure0Code 0x522 = some (.store .sw sp a0 0x24, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_524 : fetchRel bootMainClosure0Code 0x524 = some (.load .lw a0 a1 0x74, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_526 : fetchRel bootMainClosure0Code 0x526 = some (.store .sw sp a0 0x20, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_528 : fetchRel bootMainClosure0Code 0x528 = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_52c : fetchRel bootMainClosure0Code 0x52C = some (.aluImm .add a3 a3 0x76E, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_530 : fetchRel bootMainClosure0Code 0x530 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_532 : fetchRel bootMainClosure0Code 0x532 = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_536 : fetchRel bootMainClosure0Code 0x536 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_538 : fetchRel bootMainClosure0Code 0x538 = some (.aluImm .add a4 x0 0x4, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_53a : fetchRel bootMainClosure0Code 0x53A = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_53c : fetchRel bootMainClosure0Code 0x53C = some (.alu .add a2 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_53e : fetchRel bootMainClosure0Code 0x53E = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_542 : fetchRel bootMainClosure0Code 0x542 = some (.jalr ra ra 0x2EE, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_546 : fetchRel bootMainClosure0Code 0x546 = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_54a : fetchRel bootMainClosure0Code 0x54A = some (.aluImm .add a3 a3 0x20, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_54e : fetchRel bootMainClosure0Code 0x54E = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_552 : fetchRel bootMainClosure0Code 0x552 = some (.aluImm .add a0 a0 0x5D1, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_556 : fetchRel bootMainClosure0Code 0x556 = some (.aluImm .add a4 x0 0x7, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_558 : fetchRel bootMainClosure0Code 0x558 = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_55a : fetchRel bootMainClosure0Code 0x55A = some (.alu .add a2 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_55c : fetchRel bootMainClosure0Code 0x55C = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_560 : fetchRel bootMainClosure0Code 0x560 = some (.jalr ra ra 0x2D0, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_564 : fetchRel bootMainClosure0Code 0x564 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_566 : fetchRel bootMainClosure0Code 0x566 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_56a : fetchRel bootMainClosure0Code 0x56A = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_56c : fetchRel bootMainClosure0Code 0x56C = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_56e : fetchRel bootMainClosure0Code 0x56E = some (.alu .add a2 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_570 : fetchRel bootMainClosure0Code 0x570 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_574 : fetchRel bootMainClosure0Code 0x574 = some (.jalr ra ra 0x5BE, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_578 : fetchRel bootMainClosure0Code 0x578 = some (.store .sw sp x0 0x2C, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_57a : fetchRel bootMainClosure0Code 0x57A = some (.load .lbu a0 (19 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_57e : fetchRel bootMainClosure0Code 0x57E = some (.store .sw sp a0 0x28, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_580 : fetchRel bootMainClosure0Code 0x580 = some (.load .lbu (22 : Fin 32) (19 : Fin 32) 0x11, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_584 : fetchRel bootMainClosure0Code 0x584 = some (.load .lw a0 sp 0x2C, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_586 : fetchRel bootMainClosure0Code 0x586 = some (.load .lw a1 sp 0x1C, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_588 : fetchRel bootMainClosure0Code 0x588 = some (.branch .beq a1 a0 0x200, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_58c : fetchRel bootMainClosure0Code 0x58C = some (.aluImm .add a0 sp 0x350, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_58e : fetchRel bootMainClosure0Code 0x58E = some (.aluImm .add a3 sp 0x244, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_590 : fetchRel bootMainClosure0Code 0x590 = some (.alu .add a1 x0 (24 : Fin 32), 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_592 : fetchRel bootMainClosure0Code 0x592 = some (.alu .add a2 x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_594 : fetchRel bootMainClosure0Code 0x594 = some (.load .lw a4 sp 0x2C, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_596 : fetchRel bootMainClosure0Code 0x596 = some (.alu .add a5 x0 (20 : Fin 32), 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_598 : fetchRel bootMainClosure0Code 0x598 = some (.auipc ra 0x0, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_59c : fetchRel bootMainClosure0Code 0x59C = some (.jalr ra ra 0xFFFFF9F0, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5a0 : fetchRel bootMainClosure0Code 0x5A0 = some (.load .lw a1 sp 0x350, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5a4 : fetchRel bootMainClosure0Code 0x5A4 = some (.branch .beq a1 x0 0x20C, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5a8 : fetchRel bootMainClosure0Code 0x5A8 = some (.load .lw a2 sp 0x354, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5ac : fetchRel bootMainClosure0Code 0x5AC = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5ae : fetchRel bootMainClosure0Code 0x5AE = some (.aluImm .add a0 a0 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5b2 : fetchRel bootMainClosure0Code 0x5B2 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5b4 : fetchRel bootMainClosure0Code 0x5B4 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5b8 : fetchRel bootMainClosure0Code 0x5B8 = some (.jalr ra ra 0x1E4, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5bc : fetchRel bootMainClosure0Code 0x5BC = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5be : fetchRel bootMainClosure0Code 0x5BE = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5c2 : fetchRel bootMainClosure0Code 0x5C2 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5c4 : fetchRel bootMainClosure0Code 0x5C4 = some (.load .lw (8 : Fin 32) a0 0x560, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5c8 : fetchRel bootMainClosure0Code 0x5C8 = some (.branch .beq (8 : Fin 32) x0 0x1EE, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5cc : fetchRel bootMainClosure0Code 0x5CC = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5ce : fetchRel bootMainClosure0Code 0x5CE = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5d2 : fetchRel bootMainClosure0Code 0x5D2 = some (.alu .add a2 sp a0, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5d6 : fetchRel bootMainClosure0Code 0x5D6 = some (.aluImm .add a3 a2 0x500, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5da : fetchRel bootMainClosure0Code 0x5DA = some (.load .lw (9 : Fin 32) a3 0x64, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5dc : fetchRel bootMainClosure0Code 0x5DC = some (.load .lw a0 a3 0x68, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5de : fetchRel bootMainClosure0Code 0x5DE = some (.load .lw a1 a3 0x6C, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5e0 : fetchRel bootMainClosure0Code 0x5E0 = some (.load .lw a4 a3 0x70, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5e2 : fetchRel bootMainClosure0Code 0x5E2 = some (.load .lw a5 a3 0x74, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5e4 : fetchRel bootMainClosure0Code 0x5E4 = some (.load .lw a2 sp 0x24, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5e6 : fetchRel bootMainClosure0Code 0x5E6 = some (.load .lw a3 sp 0x20, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5e8 : fetchRel bootMainClosure0Code 0x5E8 = some (.alu .and a2 a2 a3, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5ea : fetchRel bootMainClosure0Code 0x5EA = some (.lui a3 0x2000, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5ec : fetchRel bootMainClosure0Code 0x5EC = some (.aluImm .add a3 a3 0xFFFFFDB0, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5f0 : fetchRel bootMainClosure0Code 0x5F0 = some (.alu .add a3 a3 sp, 2) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5f2 : fetchRel bootMainClosure0Code 0x5F2 = some (.store .sw a3 (8 : Fin 32) 0x120, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5f6 : fetchRel bootMainClosure0Code 0x5F6 = some (.store .sw a3 (9 : Fin 32) 0x124, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5fa : fetchRel bootMainClosure0Code 0x5FA = some (.store .sw a3 a0 0x128, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_5fe : fetchRel bootMainClosure0Code 0x5FE = some (.aluImm .add a0 a3 0x100, 4) :=
  (fetchRel_chunk ac_c5_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_602 : fetchRel bootMainClosure0Code 0x602 = some (.store .sw a0 a1 0x2C, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_604 : fetchRel bootMainClosure0Code 0x604 = some (.store .sw a0 a4 0x30, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_606 : fetchRel bootMainClosure0Code 0x606 = some (.store .sw a0 a5 0x34, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_608 : fetchRel bootMainClosure0Code 0x608 = some (.aluImm .add a0 x0 0x22, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_60c : fetchRel bootMainClosure0Code 0x60C = some (.aluImm .add a1 x0 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_60e : fetchRel bootMainClosure0Code 0x60E = some (.branch .beq a2 a1 0x1C6, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_612 : fetchRel bootMainClosure0Code 0x612 = some (.alu .add (26 : Fin 32) x0 a4, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_614 : fetchRel bootMainClosure0Code 0x614 = some (.alu .add (19 : Fin 32) x0 a5, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_616 : fetchRel bootMainClosure0Code 0x616 = some (.load .lw a1 sp 0x24, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_618 : fetchRel bootMainClosure0Code 0x618 = some (.aluImm .add a1 a1 0x1, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_61a : fetchRel bootMainClosure0Code 0x61A = some (.aluImm .sltu a2 a1 0x1, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_61e : fetchRel bootMainClosure0Code 0x61E = some (.load .lw a3 sp 0x20, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_620 : fetchRel bootMainClosure0Code 0x620 = some (.alu .add a2 a2 a3, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_622 : fetchRel bootMainClosure0Code 0x622 = some (.alu .xor a1 a1 a4, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_624 : fetchRel bootMainClosure0Code 0x624 = some (.alu .xor a2 a2 a5, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_626 : fetchRel bootMainClosure0Code 0x626 = some (.alu .or a1 a1 a2, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_628 : fetchRel bootMainClosure0Code 0x628 = some (.branch .bne a1 x0 0x1AC, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_62c : fetchRel bootMainClosure0Code 0x62C = some (.load .lw a0 sp 0x28, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_62e : fetchRel bootMainClosure0Code 0x62E = some (.aluImm .add a0 a0 0xFFFFFF02, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_632 : fetchRel bootMainClosure0Code 0x632 = some (.branch .beq a0 x0 0x1A0, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_636 : fetchRel bootMainClosure0Code 0x636 = some (.alu .add (18 : Fin 32) x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_638 : fetchRel bootMainClosure0Code 0x638 = some (.aluImm .add a2 x0 0x53E, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_63c : fetchRel bootMainClosure0Code 0x63C = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_63e : fetchRel bootMainClosure0Code 0x63E = some (.aluImm .add a0 a0 0xFFFFF872, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_642 : fetchRel bootMainClosure0Code 0x642 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_644 : fetchRel bootMainClosure0Code 0x644 = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_646 : fetchRel bootMainClosure0Code 0x646 = some (.aluImm .add a1 a1 0x322, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_64a : fetchRel bootMainClosure0Code 0x64A = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_64c : fetchRel bootMainClosure0Code 0x64C = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_650 : fetchRel bootMainClosure0Code 0x650 = some (.jalr ra ra 0xCA, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_654 : fetchRel bootMainClosure0Code 0x654 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_656 : fetchRel bootMainClosure0Code 0x656 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_65a : fetchRel bootMainClosure0Code 0x65A = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_65c : fetchRel bootMainClosure0Code 0x65C = some (.load .lw a1 sp 0x28, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_65e : fetchRel bootMainClosure0Code 0x65E = some (.store .sb a0 a1 0x560, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_662 : fetchRel bootMainClosure0Code 0x662 = some (.store .sb a0 (22 : Fin 32) 0x561, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_666 : fetchRel bootMainClosure0Code 0x666 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_668 : fetchRel bootMainClosure0Code 0x668 = some (.aluImm .add a0 a0 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_66c : fetchRel bootMainClosure0Code 0x66C = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_66e : fetchRel bootMainClosure0Code 0x66E = some (.lui a1 0x2000, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_670 : fetchRel bootMainClosure0Code 0x670 = some (.aluImm .add a1 a1 0xFFFFFED0, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_674 : fetchRel bootMainClosure0Code 0x674 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_676 : fetchRel bootMainClosure0Code 0x676 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_67a : fetchRel bootMainClosure0Code 0x67A = some (.jalr ra ra 0xFFFFFB04, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_67e : fetchRel bootMainClosure0Code 0x67E = some (.aluImm .and a0 a0 0x1, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_680 : fetchRel bootMainClosure0Code 0x680 = some (.alu .add (22 : Fin 32) x0 a1, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_682 : fetchRel bootMainClosure0Code 0x682 = some (.branch .bne a0 x0 0x150, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_686 : fetchRel bootMainClosure0Code 0x686 = some (.aluImm .and (9 : Fin 32) (22 : Fin 32) 0x1, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_68a : fetchRel bootMainClosure0Code 0x68A = some (.branch .beq (9 : Fin 32) x0 0x13A, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_68e : fetchRel bootMainClosure0Code 0x68E = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_690 : fetchRel bootMainClosure0Code 0x690 = some (.aluImm .add a0 a0 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_694 : fetchRel bootMainClosure0Code 0x694 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_696 : fetchRel bootMainClosure0Code 0x696 = some (.aluImm .add a4 x0 0x4, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_698 : fetchRel bootMainClosure0Code 0x698 = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_69a : fetchRel bootMainClosure0Code 0x69A = some (.alu .add a2 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_69c : fetchRel bootMainClosure0Code 0x69C = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6a0 : fetchRel bootMainClosure0Code 0x6A0 = some (.aluImm .add a3 a3 0x76E, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6a4 : fetchRel bootMainClosure0Code 0x6A4 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6a8 : fetchRel bootMainClosure0Code 0x6A8 = some (.jalr ra ra 0x188, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6ac : fetchRel bootMainClosure0Code 0x6AC = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6ae : fetchRel bootMainClosure0Code 0x6AE = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6b2 : fetchRel bootMainClosure0Code 0x6B2 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6b4 : fetchRel bootMainClosure0Code 0x6B4 = some (.load .lbu a1 a0 0x560, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6b8 : fetchRel bootMainClosure0Code 0x6B8 = some (.load .lbu (22 : Fin 32) a0 0x561, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6bc : fetchRel bootMainClosure0Code 0x6BC = some (.store .sw sp a1 0x28, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6be : fetchRel bootMainClosure0Code 0x6BE = some (.aluImm .add a0 a1 0xFFFFFF02, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6c2 : fetchRel bootMainClosure0Code 0x6C2 = some (.branch .beq a0 x0 0x110, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6c6 : fetchRel bootMainClosure0Code 0x6C6 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6ca : fetchRel bootMainClosure0Code 0x6CA = some (.aluImm .add a0 a0 0x91, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6ce : fetchRel bootMainClosure0Code 0x6CE = some (.aluImm .add a2 x0 0x53E, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6d2 : fetchRel bootMainClosure0Code 0x6D2 = some (.lui a1 0x2000, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6d4 : fetchRel bootMainClosure0Code 0x6D4 = some (.aluImm .add a1 a1 0xFFFFF872, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6d8 : fetchRel bootMainClosure0Code 0x6D8 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6da : fetchRel bootMainClosure0Code 0x6DA = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6de : fetchRel bootMainClosure0Code 0x6DE = some (.jalr ra ra 0x3C, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6e2 : fetchRel bootMainClosure0Code 0x6E2 = some (.load .lw a0 sp 0x28, 2) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6e4 : fetchRel bootMainClosure0Code 0x6E4 = some (.store .sb sp a0 0x350, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6e8 : fetchRel bootMainClosure0Code 0x6E8 = some (.store .sb sp (22 : Fin 32) 0x351, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6ec : fetchRel bootMainClosure0Code 0x6EC = some (.aluImm .add a1 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6f0 : fetchRel bootMainClosure0Code 0x6F0 = some (.aluImm .add a1 a1 0x91, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6f4 : fetchRel bootMainClosure0Code 0x6F4 = some (.aluImm .add a2 x0 0x53E, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6f8 : fetchRel bootMainClosure0Code 0x6F8 = some (.aluImm .add a0 sp 0x352, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_6fc : fetchRel bootMainClosure0Code 0x6FC = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c6_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_700 : fetchRel bootMainClosure0Code 0x700 = some (.jalr ra ra 0x1A, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_704 : fetchRel bootMainClosure0Code 0x704 = some (.aluImm .add a0 sp 0x350, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_706 : fetchRel bootMainClosure0Code 0x706 = some (.lui a1 0x2000, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_708 : fetchRel bootMainClosure0Code 0x708 = some (.aluImm .add a1 a1 0xFFFFFED0, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_70c : fetchRel bootMainClosure0Code 0x70C = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_70e : fetchRel bootMainClosure0Code 0x70E = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_712 : fetchRel bootMainClosure0Code 0x712 = some (.jalr ra ra 0xFFFFFA6C, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_716 : fetchRel bootMainClosure0Code 0x716 = some (.aluImm .and a0 a0 0x1, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_718 : fetchRel bootMainClosure0Code 0x718 = some (.branch .bne a0 x0 0xB2, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_71a : fetchRel bootMainClosure0Code 0x71A = some (.aluImm .and a1 a1 0x1, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_71c : fetchRel bootMainClosure0Code 0x71C = some (.branch .beq a1 x0 0xB2, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_71e : fetchRel bootMainClosure0Code 0x71E = some (.load .lw a0 sp 0x2C, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_720 : fetchRel bootMainClosure0Code 0x720 = some (.load .lw a1 sp 0x1C, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_722 : fetchRel bootMainClosure0Code 0x722 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_724 : fetchRel bootMainClosure0Code 0x724 = some (.branch .bne a1 a0 0x36, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_728 : fetchRel bootMainClosure0Code 0x728 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_72c : fetchRel bootMainClosure0Code 0x72C = some (.aluImm .add a0 a0 0x5D1, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_730 : fetchRel bootMainClosure0Code 0x730 = some (.aluImm .add a4 x0 0x7, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_732 : fetchRel bootMainClosure0Code 0x732 = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_734 : fetchRel bootMainClosure0Code 0x734 = some (.alu .add a2 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_736 : fetchRel bootMainClosure0Code 0x736 = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_73a : fetchRel bootMainClosure0Code 0x73A = some (.aluImm .add a3 a3 0x20, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_73e : fetchRel bootMainClosure0Code 0x73E = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_742 : fetchRel bootMainClosure0Code 0x742 = some (.jalr ra ra 0xEE, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_746 : fetchRel bootMainClosure0Code 0x746 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_748 : fetchRel bootMainClosure0Code 0x748 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_74c : fetchRel bootMainClosure0Code 0x74C = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_74e : fetchRel bootMainClosure0Code 0x74E = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_750 : fetchRel bootMainClosure0Code 0x750 = some (.alu .add a2 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_752 : fetchRel bootMainClosure0Code 0x752 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_756 : fetchRel bootMainClosure0Code 0x756 = some (.jalr ra ra 0x3DC, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_75a : fetchRel bootMainClosure0Code 0x75A = some (.aluImm .add a1 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_75e : fetchRel bootMainClosure0Code 0x75E = some (.aluImm .add a1 a1 0x91, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_762 : fetchRel bootMainClosure0Code 0x762 = some (.aluImm .add a2 x0 0x53E, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_766 : fetchRel bootMainClosure0Code 0x766 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_768 : fetchRel bootMainClosure0Code 0x768 = some (.aluImm .add a0 a0 0x322, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_76c : fetchRel bootMainClosure0Code 0x76C = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_76e : fetchRel bootMainClosure0Code 0x76E = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_772 : fetchRel bootMainClosure0Code 0x772 = some (.jalr ra ra 0xFFFFFFA8, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_776 : fetchRel bootMainClosure0Code 0x776 = some (.load .lw a0 sp 0x2C, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_778 : fetchRel bootMainClosure0Code 0x778 = some (.aluImm .add a0 a0 0x1, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_77a : fetchRel bootMainClosure0Code 0x77A = some (.store .sw sp a0 0x2C, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_77c : fetchRel bootMainClosure0Code 0x77C = some (.store .sw sp (26 : Fin 32) 0x24, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_77e : fetchRel bootMainClosure0Code 0x77E = some (.store .sw sp (19 : Fin 32) 0x20, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_780 : fetchRel bootMainClosure0Code 0x780 = some (.jal x0 0xFFFFFE04, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_782 : fetchRel bootMainClosure0Code 0x782 = some (.load .lbu (21 : Fin 32) (9 : Fin 32) 0x564, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_786 : fetchRel bootMainClosure0Code 0x786 = some (.jal x0 0x50, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_788 : fetchRel bootMainClosure0Code 0x788 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_78a : fetchRel bootMainClosure0Code 0x78A = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_78e : fetchRel bootMainClosure0Code 0x78E = some (.alu .add a2 sp a0, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_792 : fetchRel bootMainClosure0Code 0x792 = some (.load .lbu a0 a2 0x0, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_796 : fetchRel bootMainClosure0Code 0x796 = some (.load .lw a1 sp 0x28, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_798 : fetchRel bootMainClosure0Code 0x798 = some (.store .sb a2 a1 0x10, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_79c : fetchRel bootMainClosure0Code 0x79C = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_79e : fetchRel bootMainClosure0Code 0x79E = some (.aluImm .add a1 a1 0x310, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7a2 : fetchRel bootMainClosure0Code 0x7A2 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7a4 : fetchRel bootMainClosure0Code 0x7A4 = some (.store .sb a2 (22 : Fin 32) 0x11, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7a8 : fetchRel bootMainClosure0Code 0x7A8 = some (.branch .beq a0 x0 0x8E, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7aa : fetchRel bootMainClosure0Code 0x7AA = some (.load .lbu (21 : Fin 32) a1 0x1, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7ae : fetchRel bootMainClosure0Code 0x7AE = some (.jal x0 0x28, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7b0 : fetchRel bootMainClosure0Code 0x7B0 = some (.load .lbu a0 sp 0x354, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7b4 : fetchRel bootMainClosure0Code 0x7B4 = some (.jal x0 0x20, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7b6 : fetchRel bootMainClosure0Code 0x7B6 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7b8 : fetchRel bootMainClosure0Code 0x7B8 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7bc : fetchRel bootMainClosure0Code 0x7BC = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7be : fetchRel bootMainClosure0Code 0x7BE = some (.load .lbu a0 a0 0x564, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7c2 : fetchRel bootMainClosure0Code 0x7C2 = some (.jal x0 0x12, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7c4 : fetchRel bootMainClosure0Code 0x7C4 = some (.aluImm .add a0 x0 0x23, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7c8 : fetchRel bootMainClosure0Code 0x7C8 = some (.jal x0 0xC, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7ca : fetchRel bootMainClosure0Code 0x7CA = some (.alu .add (22 : Fin 32) x0 a1, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7cc : fetchRel bootMainClosure0Code 0x7CC = some (.jal x0 0x6, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7ce : fetchRel bootMainClosure0Code 0x7CE = some (.aluImm .add (22 : Fin 32) x0 0x23, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7d2 : fetchRel bootMainClosure0Code 0x7D2 = some (.alu .add a0 x0 (22 : Fin 32), 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7d4 : fetchRel bootMainClosure0Code 0x7D4 = some (.alu .add (21 : Fin 32) x0 a0, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7d6 : fetchRel bootMainClosure0Code 0x7D6 = some (.load .lw (19 : Fin 32) sp 0x40, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7d8 : fetchRel bootMainClosure0Code 0x7D8 = some (.load .lw (8 : Fin 32) sp 0x3C, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7da : fetchRel bootMainClosure0Code 0x7DA = some (.aluImm .and a0 (21 : Fin 32) 0xFF, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7de : fetchRel bootMainClosure0Code 0x7DE = some (.aluImm .add a1 x0 0x20, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7e2 : fetchRel bootMainClosure0Code 0x7E2 = some (.branch .bltu a0 a1 0x20, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7e6 : fetchRel bootMainClosure0Code 0x7E6 = some (.aluImm .add a0 a0 0xFFFFFFE0, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7e8 : fetchRel bootMainClosure0Code 0x7E8 = some (.aluImm .sll a0 a0 0x2, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7ea : fetchRel bootMainClosure0Code 0x7EA = some (.lui a1 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7ee : fetchRel bootMainClosure0Code 0x7EE = some (.aluImm .add a1 a1 0x0, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7f2 : fetchRel bootMainClosure0Code 0x7F2 = some (.alu .add a0 a0 a1, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7f4 : fetchRel bootMainClosure0Code 0x7F4 = some (.load .lw a0 a0 0x0, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7f6 : fetchRel bootMainClosure0Code 0x7F6 = some (.aluImm .add a1 x0 0x100, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7fa : fetchRel bootMainClosure0Code 0x7FA = some (.jalr x0 a0 0x0, 2) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_7fc : fetchRel bootMainClosure0Code 0x7FC = some (.aluImm .add a1 x0 0x101, 4) :=
  (fetchRel_chunk ac_c7_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_800 : fetchRel bootMainClosure0Code 0x800 = some (.jal x0 0x6, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_802 : fetchRel bootMainClosure0Code 0x802 = some (.aluImm .and a1 (21 : Fin 32) 0xFF, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_806 : fetchRel bootMainClosure0Code 0x806 = some (.lui a0 0x3FCC6000, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_80a : fetchRel bootMainClosure0Code 0x80A = some (.aluImm .add a0 a0 0x656, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_80e : fetchRel bootMainClosure0Code 0x80E = some (.auipc ra 0xFFC5F000, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_812 : fetchRel bootMainClosure0Code 0x812 = some (.jalr ra ra 0x78C, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_816 : fetchRel bootMainClosure0Code 0x816 = some (.jal x0 0xFFFFF954, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_818 : fetchRel bootMainClosure0Code 0x818 = some (.aluImm .add a1 x0 0x104, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_81c : fetchRel bootMainClosure0Code 0x81C = some (.jal x0 0xFFFFFFEA, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_81e : fetchRel bootMainClosure0Code 0x81E = some (.aluImm .add a1 x0 0x102, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_822 : fetchRel bootMainClosure0Code 0x822 = some (.jal x0 0xFFFFFFE4, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_824 : fetchRel bootMainClosure0Code 0x824 = some (.aluImm .add a1 x0 0x103, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_828 : fetchRel bootMainClosure0Code 0x828 = some (.jal x0 0xFFFFFFDE, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_82a : fetchRel bootMainClosure0Code 0x82A = some (.aluImm .add a1 x0 0x105, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_82e : fetchRel bootMainClosure0Code 0x82E = some (.jal x0 0xFFFFFFD8, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_830 : fetchRel bootMainClosure0Code 0x830 = some (.aluImm .add a1 x0 0x106, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_834 : fetchRel bootMainClosure0Code 0x834 = some (.jal x0 0xFFFFFFD2, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_836 : fetchRel bootMainClosure0Code 0x836 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_838 : fetchRel bootMainClosure0Code 0x838 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_83c : fetchRel bootMainClosure0Code 0x83C = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_83e : fetchRel bootMainClosure0Code 0x83E = some (.load .lw a1 a0 0x8, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_840 : fetchRel bootMainClosure0Code 0x840 = some (.store .sw sp a1 0x28, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_842 : fetchRel bootMainClosure0Code 0x842 = some (.load .lw a0 a0 0xC, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_844 : fetchRel bootMainClosure0Code 0x844 = some (.store .sw sp a0 0x2C, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_846 : fetchRel bootMainClosure0Code 0x846 = some (.aluImm .add a0 sp 0x350, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_848 : fetchRel bootMainClosure0Code 0x848 = some (.aluImm .add a3 sp 0x244, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_84a : fetchRel bootMainClosure0Code 0x84A = some (.alu .add a1 x0 (24 : Fin 32), 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_84c : fetchRel bootMainClosure0Code 0x84C = some (.alu .add a2 x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_84e : fetchRel bootMainClosure0Code 0x84E = some (.load .lw a4 sp 0x1C, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_850 : fetchRel bootMainClosure0Code 0x850 = some (.alu .add a5 x0 (20 : Fin 32), 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_852 : fetchRel bootMainClosure0Code 0x852 = some (.auipc ra 0xFFFFF000, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_856 : fetchRel bootMainClosure0Code 0x856 = some (.jalr ra ra 0x736, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_85a : fetchRel bootMainClosure0Code 0x85A = some (.load .lw a1 sp 0x350, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_85e : fetchRel bootMainClosure0Code 0x85E = some (.branch .bne a1 x0 0x6, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_860 : fetchRel bootMainClosure0Code 0x860 = some (.jal x0 0x1206, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_864 : fetchRel bootMainClosure0Code 0x864 = some (.load .lw a2 sp 0x354, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_868 : fetchRel bootMainClosure0Code 0x868 = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_86c : fetchRel bootMainClosure0Code 0x86C = some (.aluImm .add a3 a3 0x20, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_870 : fetchRel bootMainClosure0Code 0x870 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_872 : fetchRel bootMainClosure0Code 0x872 = some (.aluImm .add a0 a0 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_876 : fetchRel bootMainClosure0Code 0x876 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_878 : fetchRel bootMainClosure0Code 0x878 = some (.aluImm .add a4 x0 0x7, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_87a : fetchRel bootMainClosure0Code 0x87A = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_87e : fetchRel bootMainClosure0Code 0x87E = some (.jalr ra ra 0x0, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_882 : fetchRel bootMainClosure0Code 0x882 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_884 : fetchRel bootMainClosure0Code 0x884 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_888 : fetchRel bootMainClosure0Code 0x888 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_88a : fetchRel bootMainClosure0Code 0x88A = some (.load .lw (18 : Fin 32) a0 0x560, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_88e : fetchRel bootMainClosure0Code 0x88E = some (.load .lbu (8 : Fin 32) a0 0x564, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_892 : fetchRel bootMainClosure0Code 0x892 = some (.branch .bne (18 : Fin 32) x0 0x8, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_896 : fetchRel bootMainClosure0Code 0x896 = some (.jal x0 0x11D4, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_89a : fetchRel bootMainClosure0Code 0x89A = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_89c : fetchRel bootMainClosure0Code 0x89C = some (.aluImm .add a0 a0 0xFFFFF875, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8a0 : fetchRel bootMainClosure0Code 0x8A0 = some (.alu .add a1 sp a0, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8a4 : fetchRel bootMainClosure0Code 0x8A4 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8a6 : fetchRel bootMainClosure0Code 0x8A6 = some (.aluImm .add a0 a0 0xFFFFF865, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8aa : fetchRel bootMainClosure0Code 0x8AA = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8ac : fetchRel bootMainClosure0Code 0x8AC = some (.aluImm .add a2 x0 0xB, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8ae : fetchRel bootMainClosure0Code 0x8AE = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8b2 : fetchRel bootMainClosure0Code 0x8B2 = some (.jalr ra ra 0xFFFFFE68, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8b6 : fetchRel bootMainClosure0Code 0x8B6 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8ba : fetchRel bootMainClosure0Code 0x8BA = some (.aluImm .add a0 a0 0x91, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8be : fetchRel bootMainClosure0Code 0x8BE = some (.load .lbu (9 : Fin 32) a0 0x540, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8c2 : fetchRel bootMainClosure0Code 0x8C2 = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8c4 : fetchRel bootMainClosure0Code 0x8C4 = some (.aluImm .add a1 a1 0x310, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8c8 : fetchRel bootMainClosure0Code 0x8C8 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8ca : fetchRel bootMainClosure0Code 0x8CA = some (.store .sb a1 (8 : Fin 32) 0x554, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8ce : fetchRel bootMainClosure0Code 0x8CE = some (.aluImm .add (19 : Fin 32) sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8d2 : fetchRel bootMainClosure0Code 0x8D2 = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x91, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8d6 : fetchRel bootMainClosure0Code 0x8D6 = some (.load .lbu (8 : Fin 32) a0 0x541, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8da : fetchRel bootMainClosure0Code 0x8DA = some (.aluImm .add a0 (9 : Fin 32) 0xFFFFFF02, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8de : fetchRel bootMainClosure0Code 0x8DE = some (.store .sw a1 (18 : Fin 32) 0x550, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8e2 : fetchRel bootMainClosure0Code 0x8E2 = some (.branch .bne a0 x0 0x6, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8e4 : fetchRel bootMainClosure0Code 0x8E4 = some (.jal x0 0x1186, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8e8 : fetchRel bootMainClosure0Code 0x8E8 = some (.aluImm .add a1 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8ec : fetchRel bootMainClosure0Code 0x8EC = some (.aluImm .add a1 a1 0x5D3, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8f0 : fetchRel bootMainClosure0Code 0x8F0 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8f2 : fetchRel bootMainClosure0Code 0x8F2 = some (.aluImm .add a0 a0 0xFFFFF872, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8f6 : fetchRel bootMainClosure0Code 0x8F6 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8f8 : fetchRel bootMainClosure0Code 0x8F8 = some (.aluImm .add a2 x0 0x53E, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_8fc : fetchRel bootMainClosure0Code 0x8FC = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c8_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_900 : fetchRel bootMainClosure0Code 0x900 = some (.jalr ra ra 0xFFFFFE1A, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_904 : fetchRel bootMainClosure0Code 0x904 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_906 : fetchRel bootMainClosure0Code 0x906 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_90a : fetchRel bootMainClosure0Code 0x90A = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_90c : fetchRel bootMainClosure0Code 0x90C = some (.store .sb a0 (9 : Fin 32) 0x560, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_910 : fetchRel bootMainClosure0Code 0x910 = some (.store .sb a0 (8 : Fin 32) 0x561, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_914 : fetchRel bootMainClosure0Code 0x914 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_916 : fetchRel bootMainClosure0Code 0x916 = some (.aluImm .add a0 a0 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_91a : fetchRel bootMainClosure0Code 0x91A = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_91c : fetchRel bootMainClosure0Code 0x91C = some (.lui a1 0x2000, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_91e : fetchRel bootMainClosure0Code 0x91E = some (.aluImm .add a1 a1 0xFFFFF860, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_922 : fetchRel bootMainClosure0Code 0x922 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_924 : fetchRel bootMainClosure0Code 0x924 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_928 : fetchRel bootMainClosure0Code 0x928 = some (.jalr ra ra 0xFFFFF856, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_92c : fetchRel bootMainClosure0Code 0x92C = some (.aluImm .and a0 a0 0x1, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_92e : fetchRel bootMainClosure0Code 0x92E = some (.alu .add (8 : Fin 32) x0 a1, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_930 : fetchRel bootMainClosure0Code 0x930 = some (.branch .beq a0 x0 0x6, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_932 : fetchRel bootMainClosure0Code 0x932 = some (.jal x0 0x1138, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_936 : fetchRel bootMainClosure0Code 0x936 = some (.aluImm .and (8 : Fin 32) (8 : Fin 32) 0x1, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_938 : fetchRel bootMainClosure0Code 0x938 = some (.branch .beq (8 : Fin 32) x0 0x3C, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_93a : fetchRel bootMainClosure0Code 0x93A = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_93c : fetchRel bootMainClosure0Code 0x93C = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_940 : fetchRel bootMainClosure0Code 0x940 = some (.alu .add (9 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_944 : fetchRel bootMainClosure0Code 0x944 = some (.load .lw (8 : Fin 32) (9 : Fin 32) 0x554, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_948 : fetchRel bootMainClosure0Code 0x948 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_94a : fetchRel bootMainClosure0Code 0x94A = some (.aluImm .add a0 a0 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_94e : fetchRel bootMainClosure0Code 0x94E = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_950 : fetchRel bootMainClosure0Code 0x950 = some (.alu .add a1 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_952 : fetchRel bootMainClosure0Code 0x952 = some (.alu .add a2 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_954 : fetchRel bootMainClosure0Code 0x954 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_958 : fetchRel bootMainClosure0Code 0x958 = some (.jalr ra ra 0x1DA, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_95c : fetchRel bootMainClosure0Code 0x95C = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_95e : fetchRel bootMainClosure0Code 0x95E = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_962 : fetchRel bootMainClosure0Code 0x962 = some (.alu .add a1 sp a0, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_966 : fetchRel bootMainClosure0Code 0x966 = some (.load .lbu a0 (9 : Fin 32) 0x560, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_96a : fetchRel bootMainClosure0Code 0x96A = some (.branch .beq a0 x0 0x12, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_96c : fetchRel bootMainClosure0Code 0x96C = some (.load .lbu (8 : Fin 32) a1 0x561, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_970 : fetchRel bootMainClosure0Code 0x970 = some (.jal x0 0x10FA, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_974 : fetchRel bootMainClosure0Code 0x974 = some (.aluImm .add (8 : Fin 32) x0 0x23, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_978 : fetchRel bootMainClosure0Code 0x978 = some (.jal x0 0x10F2, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_97c : fetchRel bootMainClosure0Code 0x97C = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_97e : fetchRel bootMainClosure0Code 0x97E = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_982 : fetchRel bootMainClosure0Code 0x982 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_984 : fetchRel bootMainClosure0Code 0x984 = some (.load .lw a1 a0 0x568, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_988 : fetchRel bootMainClosure0Code 0x988 = some (.store .sw sp a1 0x20, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_98a : fetchRel bootMainClosure0Code 0x98A = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_98c : fetchRel bootMainClosure0Code 0x98C = some (.aluImm .add a1 a1 0x310, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_990 : fetchRel bootMainClosure0Code 0x990 = some (.alu .add (9 : Fin 32) sp a1, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_994 : fetchRel bootMainClosure0Code 0x994 = some (.load .lw a0 a0 0x56C, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_998 : fetchRel bootMainClosure0Code 0x998 = some (.store .sw sp a0 0x24, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_99a : fetchRel bootMainClosure0Code 0x99A = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_99e : fetchRel bootMainClosure0Code 0x99E = some (.aluImm .add a3 a3 0x20, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9a2 : fetchRel bootMainClosure0Code 0x9A2 = some (.aluImm .add a0 sp 0x350, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9a4 : fetchRel bootMainClosure0Code 0x9A4 = some (.aluImm .add a4 x0 0x7, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9a6 : fetchRel bootMainClosure0Code 0x9A6 = some (.alu .add a1 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9a8 : fetchRel bootMainClosure0Code 0x9A8 = some (.alu .add a2 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9aa : fetchRel bootMainClosure0Code 0x9AA = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9ae : fetchRel bootMainClosure0Code 0x9AE = some (.jalr ra ra 0xFFFFFC26, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9b2 : fetchRel bootMainClosure0Code 0x9B2 = some (.load .lw a1 sp 0x350, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9b6 : fetchRel bootMainClosure0Code 0x9B6 = some (.branch .bne a1 x0 0x6, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9b8 : fetchRel bootMainClosure0Code 0x9B8 = some (.jal x0 0x10AE, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9bc : fetchRel bootMainClosure0Code 0x9BC = some (.load .lw a2 sp 0x354, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9c0 : fetchRel bootMainClosure0Code 0x9C0 = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9c4 : fetchRel bootMainClosure0Code 0x9C4 = some (.aluImm .add a3 a3 0x27, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9c8 : fetchRel bootMainClosure0Code 0x9C8 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9ca : fetchRel bootMainClosure0Code 0x9CA = some (.aluImm .add a0 a0 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9ce : fetchRel bootMainClosure0Code 0x9CE = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9d0 : fetchRel bootMainClosure0Code 0x9D0 = some (.aluImm .add a4 x0 0x11, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9d2 : fetchRel bootMainClosure0Code 0x9D2 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9d6 : fetchRel bootMainClosure0Code 0x9D6 = some (.jalr ra ra 0xFFFFFD6A, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9da : fetchRel bootMainClosure0Code 0x9DA = some (.load .lbu a0 (9 : Fin 32) 0x560, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9de : fetchRel bootMainClosure0Code 0x9DE = some (.branch .beq a0 x0 0xA, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9e0 : fetchRel bootMainClosure0Code 0x9E0 = some (.load .lbu (8 : Fin 32) (9 : Fin 32) 0x561, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9e4 : fetchRel bootMainClosure0Code 0x9E4 = some (.jal x0 0x1086, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9e8 : fetchRel bootMainClosure0Code 0x9E8 = some (.load .lw (8 : Fin 32) (9 : Fin 32) 0x564, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9ec : fetchRel bootMainClosure0Code 0x9EC = some (.branch .beq (8 : Fin 32) x0 0x216, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9f0 : fetchRel bootMainClosure0Code 0x9F0 = some (.load .lw (18 : Fin 32) (9 : Fin 32) 0x568, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9f4 : fetchRel bootMainClosure0Code 0x9F4 = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9f8 : fetchRel bootMainClosure0Code 0x9F8 = some (.aluImm .add a3 a3 0x38, 4) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9fc : fetchRel bootMainClosure0Code 0x9FC = some (.aluImm .add a0 sp 0x350, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_9fe : fetchRel bootMainClosure0Code 0x9FE = some (.aluImm .add a4 x0 0x6, 2) :=
  (fetchRel_chunk ac_c9_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a00 : fetchRel bootMainClosure0Code 0xA00 = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a02 : fetchRel bootMainClosure0Code 0xA02 = some (.alu .add a2 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a04 : fetchRel bootMainClosure0Code 0xA04 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a08 : fetchRel bootMainClosure0Code 0xA08 = some (.jalr ra ra 0xFFFFFBCC, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a0c : fetchRel bootMainClosure0Code 0xA0C = some (.load .lw a1 sp 0x350, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a10 : fetchRel bootMainClosure0Code 0xA10 = some (.branch .bne a1 x0 0x6, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a12 : fetchRel bootMainClosure0Code 0xA12 = some (.jal x0 0x1054, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a16 : fetchRel bootMainClosure0Code 0xA16 = some (.load .lw a2 sp 0x354, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a1a : fetchRel bootMainClosure0Code 0xA1A = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a1c : fetchRel bootMainClosure0Code 0xA1C = some (.aluImm .add a0 a0 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a20 : fetchRel bootMainClosure0Code 0xA20 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a22 : fetchRel bootMainClosure0Code 0xA22 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a26 : fetchRel bootMainClosure0Code 0xA26 = some (.jalr ra ra 0x770, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a2a : fetchRel bootMainClosure0Code 0xA2A = some (.load .lbu a0 (9 : Fin 32) 0x560, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a2e : fetchRel bootMainClosure0Code 0xA2E = some (.branch .bne a0 x0 0xFFFFFFB2, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a30 : fetchRel bootMainClosure0Code 0xA30 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a32 : fetchRel bootMainClosure0Code 0xA32 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a36 : fetchRel bootMainClosure0Code 0xA36 = some (.alu .add (9 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a3a : fetchRel bootMainClosure0Code 0xA3A = some (.load .lw a0 (9 : Fin 32) 0x568, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a3e : fetchRel bootMainClosure0Code 0xA3E = some (.store .sw sp a0 0x14, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a40 : fetchRel bootMainClosure0Code 0xA40 = some (.load .lw a0 (9 : Fin 32) 0x56C, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a44 : fetchRel bootMainClosure0Code 0xA44 = some (.store .sw sp a0 0x18, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a46 : fetchRel bootMainClosure0Code 0xA46 = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a4a : fetchRel bootMainClosure0Code 0xA4A = some (.aluImm .add a3 a3 0x3E, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a4e : fetchRel bootMainClosure0Code 0xA4E = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a50 : fetchRel bootMainClosure0Code 0xA50 = some (.aluImm .add a0 a0 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a54 : fetchRel bootMainClosure0Code 0xA54 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a56 : fetchRel bootMainClosure0Code 0xA56 = some (.aluImm .add a4 x0 0x6, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a58 : fetchRel bootMainClosure0Code 0xA58 = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a5a : fetchRel bootMainClosure0Code 0xA5A = some (.alu .add a2 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a5c : fetchRel bootMainClosure0Code 0xA5C = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a60 : fetchRel bootMainClosure0Code 0xA60 = some (.jalr ra ra 0xFFFFFB74, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a64 : fetchRel bootMainClosure0Code 0xA64 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a66 : fetchRel bootMainClosure0Code 0xA66 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a6a : fetchRel bootMainClosure0Code 0xA6A = some (.alu .add (22 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a6e : fetchRel bootMainClosure0Code 0xA6E = some (.load .lw a1 (9 : Fin 32) 0x560, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a72 : fetchRel bootMainClosure0Code 0xA72 = some (.branch .beq a1 x0 0x198, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a76 : fetchRel bootMainClosure0Code 0xA76 = some (.load .lw a2 (22 : Fin 32) 0x564, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a7a : fetchRel bootMainClosure0Code 0xA7A = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a7e : fetchRel bootMainClosure0Code 0xA7E = some (.aluImm .add a3 a3 0x44, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a82 : fetchRel bootMainClosure0Code 0xA82 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a84 : fetchRel bootMainClosure0Code 0xA84 = some (.aluImm .add a0 a0 0xFFFFFED0, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a88 : fetchRel bootMainClosure0Code 0xA88 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a8a : fetchRel bootMainClosure0Code 0xA8A = some (.aluImm .add a4 x0 0x6, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a8c : fetchRel bootMainClosure0Code 0xA8C = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a90 : fetchRel bootMainClosure0Code 0xA90 = some (.jalr ra ra 0xFFFFFB44, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a94 : fetchRel bootMainClosure0Code 0xA94 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a96 : fetchRel bootMainClosure0Code 0xA96 = some (.aluImm .add a0 a0 0xFFFFFDB0, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a9a : fetchRel bootMainClosure0Code 0xA9A = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_a9c : fetchRel bootMainClosure0Code 0xA9C = some (.load .lw a1 a0 0x120, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_aa0 : fetchRel bootMainClosure0Code 0xAA0 = some (.branch .beq a1 x0 0x60, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_aa2 : fetchRel bootMainClosure0Code 0xAA2 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_aa4 : fetchRel bootMainClosure0Code 0xAA4 = some (.aluImm .add a0 a0 0xFFFFFDB0, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_aa8 : fetchRel bootMainClosure0Code 0xAA8 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_aaa : fetchRel bootMainClosure0Code 0xAAA = some (.load .lw a0 a0 0x124, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_aae : fetchRel bootMainClosure0Code 0xAAE = some (.aluImm .add a2 x0 0x2, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ab0 : fetchRel bootMainClosure0Code 0xAB0 = some (.aluImm .add (8 : Fin 32) x0 0x21, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ab4 : fetchRel bootMainClosure0Code 0xAB4 = some (.branch .bgeu a0 a2 0x8, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ab8 : fetchRel bootMainClosure0Code 0xAB8 = some (.jal x0 0xFB2, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_abc : fetchRel bootMainClosure0Code 0xABC = some (.load .lbu a2 a1 0x0, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ac0 : fetchRel bootMainClosure0Code 0xAC0 = some (.aluImm .add a2 a2 0xFFFFFFDE, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ac4 : fetchRel bootMainClosure0Code 0xAC4 = some (.branch .beq a2 x0 0x6, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ac6 : fetchRel bootMainClosure0Code 0xAC6 = some (.jal x0 0xFA4, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_aca : fetchRel bootMainClosure0Code 0xACA = some (.alu .add a2 a1 a0, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ace : fetchRel bootMainClosure0Code 0xACE = some (.load .lbu a2 a2 0xFFFFFFFF, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ad2 : fetchRel bootMainClosure0Code 0xAD2 = some (.aluImm .add a2 a2 0xFFFFFFDE, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ad6 : fetchRel bootMainClosure0Code 0xAD6 = some (.branch .beq a2 x0 0x6, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ad8 : fetchRel bootMainClosure0Code 0xAD8 = some (.jal x0 0xF92, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_adc : fetchRel bootMainClosure0Code 0xADC = some (.aluImm .add (9 : Fin 32) a0 0xFFFFFFBE, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ae0 : fetchRel bootMainClosure0Code 0xAE0 = some (.branch .bne (9 : Fin 32) x0 0x14, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ae2 : fetchRel bootMainClosure0Code 0xAE2 = some (.aluImm .add a1 a1 0x1, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ae4 : fetchRel bootMainClosure0Code 0xAE4 = some (.aluImm .add a0 sp 0x351, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ae8 : fetchRel bootMainClosure0Code 0xAE8 = some (.aluImm .add a2 x0 0x40, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_aec : fetchRel bootMainClosure0Code 0xAEC = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_af0 : fetchRel bootMainClosure0Code 0xAF0 = some (.jalr ra ra 0xFFFFFC2A, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_af4 : fetchRel bootMainClosure0Code 0xAF4 = some (.load .lw a4 sp 0x1C, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_af6 : fetchRel bootMainClosure0Code 0xAF6 = some (.aluImm .add a4 a4 0x1, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_af8 : fetchRel bootMainClosure0Code 0xAF8 = some (.branch .bne a4 x0 0x18, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_afa : fetchRel bootMainClosure0Code 0xAFA = some (.aluImm .add (8 : Fin 32) x0 0x6, 2) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_afc : fetchRel bootMainClosure0Code 0xAFC = some (.jal x0 0xF6E, 4) :=
  (fetchRel_chunk ac_c10_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b00 : fetchRel bootMainClosure0Code 0xB00 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b02 : fetchRel bootMainClosure0Code 0xB02 = some (.aluImm .add a0 a0 0xFFFFFDB0, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b06 : fetchRel bootMainClosure0Code 0xB06 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b08 : fetchRel bootMainClosure0Code 0xB08 = some (.load .lbu (8 : Fin 32) a0 0x124, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b0c : fetchRel bootMainClosure0Code 0xB0C = some (.jal x0 0xF5E, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b10 : fetchRel bootMainClosure0Code 0xB10 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b12 : fetchRel bootMainClosure0Code 0xB12 = some (.aluImm .add a0 a0 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b16 : fetchRel bootMainClosure0Code 0xB16 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b18 : fetchRel bootMainClosure0Code 0xB18 = some (.aluImm .add a3 sp 0x244, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b1a : fetchRel bootMainClosure0Code 0xB1A = some (.alu .add a1 x0 (24 : Fin 32), 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b1c : fetchRel bootMainClosure0Code 0xB1C = some (.alu .add a2 x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b1e : fetchRel bootMainClosure0Code 0xB1E = some (.alu .add a5 x0 (20 : Fin 32), 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b20 : fetchRel bootMainClosure0Code 0xB20 = some (.auipc ra 0xFFFFF000, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b24 : fetchRel bootMainClosure0Code 0xB24 = some (.jalr ra ra 0x468, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b28 : fetchRel bootMainClosure0Code 0xB28 = some (.load .lw (18 : Fin 32) (22 : Fin 32) 0x560, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b2c : fetchRel bootMainClosure0Code 0xB2C = some (.branch .beq (18 : Fin 32) x0 0xDE, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b30 : fetchRel bootMainClosure0Code 0xB30 = some (.load .lw (24 : Fin 32) (22 : Fin 32) 0x564, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b34 : fetchRel bootMainClosure0Code 0xB34 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b36 : fetchRel bootMainClosure0Code 0xB36 = some (.aluImm .add a0 a0 0xFFFFFDC8, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b3a : fetchRel bootMainClosure0Code 0xB3A = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b3c : fetchRel bootMainClosure0Code 0xB3C = some (.alu .add a1 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b3e : fetchRel bootMainClosure0Code 0xB3E = some (.alu .add a2 x0 (24 : Fin 32), 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b40 : fetchRel bootMainClosure0Code 0xB40 = some (.lui a3 0x2000, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b42 : fetchRel bootMainClosure0Code 0xB42 = some (.aluImm .add a3 a3 0xFFFFFDC8, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b46 : fetchRel bootMainClosure0Code 0xB46 = some (.alu .add (8 : Fin 32) sp a3, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b4a : fetchRel bootMainClosure0Code 0xB4A = some (.auipc ra 0x6000, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b4e : fetchRel bootMainClosure0Code 0xB4E = some (.jalr ra ra 0x168, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b52 : fetchRel bootMainClosure0Code 0xB52 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b54 : fetchRel bootMainClosure0Code 0xB54 = some (.aluImm .add a0 a0 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b58 : fetchRel bootMainClosure0Code 0xB58 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b5a : fetchRel bootMainClosure0Code 0xB5A = some (.aluImm .add a2 x0 0x40, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b5e : fetchRel bootMainClosure0Code 0xB5E = some (.aluImm .add a1 x0 0x0, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b60 : fetchRel bootMainClosure0Code 0xB60 = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b64 : fetchRel bootMainClosure0Code 0xB64 = some (.jalr ra ra 0xFFFFFB4E, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b68 : fetchRel bootMainClosure0Code 0xB68 = some (.aluImm .add a0 x0 0x20, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b6c : fetchRel bootMainClosure0Code 0xB6C = some (.lui a1 0x2000, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b6e : fetchRel bootMainClosure0Code 0xB6E = some (.aluImm .add a1 a1 0xFFFFF871, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b72 : fetchRel bootMainClosure0Code 0xB72 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b74 : fetchRel bootMainClosure0Code 0xB74 = some (.lui a2 0x3FCC5000, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b78 : fetchRel bootMainClosure0Code 0xB78 = some (.aluImm .add a2 a2 0xFFFFF9A0, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b7c : fetchRel bootMainClosure0Code 0xB7C = some (.branch .beq a0 x0 0x28, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b7e : fetchRel bootMainClosure0Code 0xB7E = some (.load .lbu a3 (8 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b82 : fetchRel bootMainClosure0Code 0xB82 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x1, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b84 : fetchRel bootMainClosure0Code 0xB84 = some (.aluImm .srl a4 a3 0x4, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b88 : fetchRel bootMainClosure0Code 0xB88 = some (.aluImm .and a3 a3 0xF, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b8a : fetchRel bootMainClosure0Code 0xB8A = some (.alu .add a4 a4 a2, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b8c : fetchRel bootMainClosure0Code 0xB8C = some (.alu .add a3 a3 a2, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b8e : fetchRel bootMainClosure0Code 0xB8E = some (.load .lbu a4 a4 0x0, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b92 : fetchRel bootMainClosure0Code 0xB92 = some (.load .lbu a3 a3 0x0, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b96 : fetchRel bootMainClosure0Code 0xB96 = some (.store .sb a1 a4 0xFFFFFFFF, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b9a : fetchRel bootMainClosure0Code 0xB9A = some (.store .sb a1 a3 0x0, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_b9e : fetchRel bootMainClosure0Code 0xB9E = some (.aluImm .add a1 a1 0x2, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ba0 : fetchRel bootMainClosure0Code 0xBA0 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ba2 : fetchRel bootMainClosure0Code 0xBA2 = some (.branch .bne a0 x0 0xFFFFFFDC, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ba4 : fetchRel bootMainClosure0Code 0xBA4 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ba6 : fetchRel bootMainClosure0Code 0xBA6 = some (.aluImm .add a0 a0 0xFFFFFED0, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_baa : fetchRel bootMainClosure0Code 0xBAA = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bac : fetchRel bootMainClosure0Code 0xBAC = some (.lui a1 0x2000, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bae : fetchRel bootMainClosure0Code 0xBAE = some (.aluImm .add a1 a1 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bb2 : fetchRel bootMainClosure0Code 0xBB2 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bb4 : fetchRel bootMainClosure0Code 0xBB4 = some (.aluImm .add a2 x0 0x40, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bb8 : fetchRel bootMainClosure0Code 0xBB8 = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bbc : fetchRel bootMainClosure0Code 0xBBC = some (.jalr ra ra 0xFFFFFB5E, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bc0 : fetchRel bootMainClosure0Code 0xBC0 = some (.load .lw a0 sp 0x18, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bc2 : fetchRel bootMainClosure0Code 0xBC2 = some (.branch .bne a0 x0 0x40, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bc4 : fetchRel bootMainClosure0Code 0xBC4 = some (.load .lw a0 sp 0x14, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bc6 : fetchRel bootMainClosure0Code 0xBC6 = some (.branch .bne (24 : Fin 32) a0 0x3C, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bca : fetchRel bootMainClosure0Code 0xBCA = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bcc : fetchRel bootMainClosure0Code 0xBCC = some (.aluImm .add a0 a0 0xFFFFF871, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bd0 : fetchRel bootMainClosure0Code 0xBD0 = some (.alu .add (20 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bd4 : fetchRel bootMainClosure0Code 0xBD4 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bd6 : fetchRel bootMainClosure0Code 0xBD6 = some (.aluImm .add a0 a0 0xFFFFFED0, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bda : fetchRel bootMainClosure0Code 0xBDA = some (.alu .add a1 sp a0, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bde : fetchRel bootMainClosure0Code 0xBDE = some (.aluImm .add a2 x0 0x40, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_be2 : fetchRel bootMainClosure0Code 0xBE2 = some (.alu .add a0 x0 (20 : Fin 32), 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_be4 : fetchRel bootMainClosure0Code 0xBE4 = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_be8 : fetchRel bootMainClosure0Code 0xBE8 = some (.jalr ra ra 0xFFFFFB32, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bec : fetchRel bootMainClosure0Code 0xBEC = some (.branch .bne (9 : Fin 32) x0 0x16, 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bee : fetchRel bootMainClosure0Code 0xBEE = some (.aluImm .add a0 sp 0x351, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bf2 : fetchRel bootMainClosure0Code 0xBF2 = some (.aluImm .add a2 x0 0x40, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bf6 : fetchRel bootMainClosure0Code 0xBF6 = some (.alu .add a1 x0 (20 : Fin 32), 2) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bf8 : fetchRel bootMainClosure0Code 0xBF8 = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_bfc : fetchRel bootMainClosure0Code 0xBFC = some (.jalr ra ra 0xFFFFFA96, 4) :=
  (fetchRel_chunk ac_c11_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c00 : fetchRel bootMainClosure0Code 0xC00 = some (.branch .beq a0 x0 0x12, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c02 : fetchRel bootMainClosure0Code 0xC02 = some (.aluImm .add (8 : Fin 32) x0 0x24, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c06 : fetchRel bootMainClosure0Code 0xC06 = some (.jal x0 0xE64, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c0a : fetchRel bootMainClosure0Code 0xC0A = some (.load .lbu (8 : Fin 32) (22 : Fin 32) 0x564, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c0e : fetchRel bootMainClosure0Code 0xC0E = some (.jal x0 0xE5C, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c12 : fetchRel bootMainClosure0Code 0xC12 = some (.load .lw a0 sp 0x24, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c14 : fetchRel bootMainClosure0Code 0xC14 = some (.load .lw a1 sp 0x2C, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c16 : fetchRel bootMainClosure0Code 0xC16 = some (.branch .beq a0 a1 0xA, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c1a : fetchRel bootMainClosure0Code 0xC1A = some (.load .lw a0 sp 0x24, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c1c : fetchRel bootMainClosure0Code 0xC1C = some (.load .lw a1 sp 0x2C, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c1e : fetchRel bootMainClosure0Code 0xC1E = some (.jal x0 0x6, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c20 : fetchRel bootMainClosure0Code 0xC20 = some (.load .lw a0 sp 0x20, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c22 : fetchRel bootMainClosure0Code 0xC22 = some (.load .lw a1 sp 0x28, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c24 : fetchRel bootMainClosure0Code 0xC24 = some (.alu .sltu a0 a0 a1, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c28 : fetchRel bootMainClosure0Code 0xC28 = some (.branch .bne a0 x0 0xA, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c2a : fetchRel bootMainClosure0Code 0xC2A = some (.load .lw a0 sp 0x2C, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c2c : fetchRel bootMainClosure0Code 0xC2C = some (.store .sw sp a0 0x24, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c2e : fetchRel bootMainClosure0Code 0xC2E = some (.load .lw a0 sp 0x28, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c30 : fetchRel bootMainClosure0Code 0xC30 = some (.store .sw sp a0 0x20, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c32 : fetchRel bootMainClosure0Code 0xC32 = some (.aluImm .add a0 x0 0x5, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c34 : fetchRel bootMainClosure0Code 0xC34 = some (.aluImm .sll a0 a0 0xB, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c36 : fetchRel bootMainClosure0Code 0xC36 = some (.branch .bgeu a0 (24 : Fin 32) 0xA, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c3a : fetchRel bootMainClosure0Code 0xC3A = some (.aluImm .add (8 : Fin 32) x0 0x13, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c3c : fetchRel bootMainClosure0Code 0xC3C = some (.jal x0 0xE2E, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c40 : fetchRel bootMainClosure0Code 0xC40 = some (.lui a0 0x5000, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c42 : fetchRel bootMainClosure0Code 0xC42 = some (.aluImm .add a0 a0 0x40, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c46 : fetchRel bootMainClosure0Code 0xC46 = some (.lui a1 0x2000, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c48 : fetchRel bootMainClosure0Code 0xC48 = some (.aluImm .add a1 a1 0xFFFFFDB0, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c4c : fetchRel bootMainClosure0Code 0xC4C = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c4e : fetchRel bootMainClosure0Code 0xC4E = some (.load .lw a2 sp 0x30, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c50 : fetchRel bootMainClosure0Code 0xC50 = some (.store .sw a1 a2 0x22C, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c54 : fetchRel bootMainClosure0Code 0xC54 = some (.store .sw a1 a0 0x230, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c58 : fetchRel bootMainClosure0Code 0xC58 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c5a : fetchRel bootMainClosure0Code 0xC5A = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c5e : fetchRel bootMainClosure0Code 0xC5E = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c60 : fetchRel bootMainClosure0Code 0xC60 = some (.alu .add a1 x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c62 : fetchRel bootMainClosure0Code 0xC62 = some (.alu .add a2 x0 (24 : Fin 32), 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c64 : fetchRel bootMainClosure0Code 0xC64 = some (.aluImm .add a3 x0 0x0, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c66 : fetchRel bootMainClosure0Code 0xC66 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c6a : fetchRel bootMainClosure0Code 0xC6A = some (.jalr ra ra 0x764, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c6e : fetchRel bootMainClosure0Code 0xC6E = some (.load .lw (26 : Fin 32) (22 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c72 : fetchRel bootMainClosure0Code 0xC72 = some (.branch .beq (26 : Fin 32) x0 0x72, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c76 : fetchRel bootMainClosure0Code 0xC76 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c78 : fetchRel bootMainClosure0Code 0xC78 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c7c : fetchRel bootMainClosure0Code 0xC7C = some (.alu .add (8 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c80 : fetchRel bootMainClosure0Code 0xC80 = some (.load .lw a2 (8 : Fin 32) 0x14, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c82 : fetchRel bootMainClosure0Code 0xC82 = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c86 : fetchRel bootMainClosure0Code 0xC86 = some (.aluImm .add a3 a3 0x79A, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c8a : fetchRel bootMainClosure0Code 0xC8A = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c8c : fetchRel bootMainClosure0Code 0xC8C = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c90 : fetchRel bootMainClosure0Code 0xC90 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c92 : fetchRel bootMainClosure0Code 0xC92 = some (.aluImm .add a4 x0 0x9, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c94 : fetchRel bootMainClosure0Code 0xC94 = some (.alu .add a1 x0 (26 : Fin 32), 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c96 : fetchRel bootMainClosure0Code 0xC96 = some (.store .sw sp a2 0x30, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c98 : fetchRel bootMainClosure0Code 0xC98 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_c9c : fetchRel bootMainClosure0Code 0xC9C = some (.jalr ra ra 0xFFFFF938, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ca0 : fetchRel bootMainClosure0Code 0xCA0 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ca2 : fetchRel bootMainClosure0Code 0xCA2 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ca6 : fetchRel bootMainClosure0Code 0xCA6 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ca8 : fetchRel bootMainClosure0Code 0xCA8 = some (.load .lw a1 (8 : Fin 32) 0x10, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_caa : fetchRel bootMainClosure0Code 0xCAA = some (.branch .beq a1 x0 0x760, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cae : fetchRel bootMainClosure0Code 0xCAE = some (.load .lw a2 a0 0x14, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cb0 : fetchRel bootMainClosure0Code 0xCB0 = some (.aluImm .add a0 sp 0x350, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cb2 : fetchRel bootMainClosure0Code 0xCB2 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cb6 : fetchRel bootMainClosure0Code 0xCB6 = some (.jalr ra ra 0xFFFFF95A, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cba : fetchRel bootMainClosure0Code 0xCBA = some (.load .lw a0 sp 0x350, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cbe : fetchRel bootMainClosure0Code 0xCBE = some (.branch .beq a0 x0 0xDA8, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cc2 : fetchRel bootMainClosure0Code 0xCC2 = some (.load .lw a1 sp 0x354, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cc6 : fetchRel bootMainClosure0Code 0xCC6 = some (.lui a2 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cca : fetchRel bootMainClosure0Code 0xCCA = some (.aluImm .add a2 a2 0x7A3, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cce : fetchRel bootMainClosure0Code 0xCCE = some (.aluImm .add a3 x0 0x39, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cd2 : fetchRel bootMainClosure0Code 0xCD2 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cd6 : fetchRel bootMainClosure0Code 0xCD6 = some (.jalr ra ra 0x6E2, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cda : fetchRel bootMainClosure0Code 0xCDA = some (.branch .beq a0 x0 0x12, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cdc : fetchRel bootMainClosure0Code 0xCDC = some (.aluImm .add (8 : Fin 32) x0 0x21, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ce0 : fetchRel bootMainClosure0Code 0xCE0 = some (.jal x0 0xD8A, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ce4 : fetchRel bootMainClosure0Code 0xCE4 = some (.load .lbu (8 : Fin 32) (22 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ce8 : fetchRel bootMainClosure0Code 0xCE8 = some (.jal x0 0xD82, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cec : fetchRel bootMainClosure0Code 0xCEC = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cee : fetchRel bootMainClosure0Code 0xCEE = some (.aluImm .add a0 a0 0xFFFFFED0, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cf2 : fetchRel bootMainClosure0Code 0xCF2 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cf4 : fetchRel bootMainClosure0Code 0xCF4 = some (.aluImm .add a1 x0 0x8, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cf6 : fetchRel bootMainClosure0Code 0xCF6 = some (.branch .beq a1 x0 0xE, 2) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cf8 : fetchRel bootMainClosure0Code 0xCF8 = some (.store .sw a0 x0 0x0, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_cfc : fetchRel bootMainClosure0Code 0xCFC = some (.aluImm .add a0 a0 0x20, 4) :=
  (fetchRel_chunk ac_c12_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d00 : fetchRel bootMainClosure0Code 0xD00 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d02 : fetchRel bootMainClosure0Code 0xD02 = some (.branch .bne a1 x0 0xFFFFFFF6, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d04 : fetchRel bootMainClosure0Code 0xD04 = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d08 : fetchRel bootMainClosure0Code 0xD08 = some (.aluImm .add a3 a3 0x7DC, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d0c : fetchRel bootMainClosure0Code 0xD0C = some (.aluImm .add a0 sp 0x350, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d0e : fetchRel bootMainClosure0Code 0xD0E = some (.aluImm .add a4 x0 0x16, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d10 : fetchRel bootMainClosure0Code 0xD10 = some (.alu .add a1 x0 (26 : Fin 32), 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d12 : fetchRel bootMainClosure0Code 0xD12 = some (.load .lw a2 sp 0x30, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d14 : fetchRel bootMainClosure0Code 0xD14 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d18 : fetchRel bootMainClosure0Code 0xD18 = some (.jalr ra ra 0xFFFFF8BC, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d1c : fetchRel bootMainClosure0Code 0xD1C = some (.load .lw a1 sp 0x350, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d20 : fetchRel bootMainClosure0Code 0xD20 = some (.branch .beq a1 x0 0xD46, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d24 : fetchRel bootMainClosure0Code 0xD24 = some (.load .lw a2 sp 0x354, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d28 : fetchRel bootMainClosure0Code 0xD28 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d2a : fetchRel bootMainClosure0Code 0xD2A = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d2e : fetchRel bootMainClosure0Code 0xD2E = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d30 : fetchRel bootMainClosure0Code 0xD30 = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d34 : fetchRel bootMainClosure0Code 0xD34 = some (.jalr ra ra 0x7F8, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d38 : fetchRel bootMainClosure0Code 0xD38 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d3a : fetchRel bootMainClosure0Code 0xD3A = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d3e : fetchRel bootMainClosure0Code 0xD3E = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d40 : fetchRel bootMainClosure0Code 0xD40 = some (.load .lw (9 : Fin 32) a0 0x10, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d42 : fetchRel bootMainClosure0Code 0xD42 = some (.load .lbu (8 : Fin 32) a0 0x14, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d46 : fetchRel bootMainClosure0Code 0xD46 = some (.branch .beq (9 : Fin 32) x0 0xD24, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d4a : fetchRel bootMainClosure0Code 0xD4A = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d4c : fetchRel bootMainClosure0Code 0xD4C = some (.aluImm .add a0 a0 0x325, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d50 : fetchRel bootMainClosure0Code 0xD50 = some (.alu .add a1 sp a0, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d54 : fetchRel bootMainClosure0Code 0xD54 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d56 : fetchRel bootMainClosure0Code 0xD56 = some (.aluImm .add a0 a0 0x315, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d5a : fetchRel bootMainClosure0Code 0xD5A = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d5c : fetchRel bootMainClosure0Code 0xD5C = some (.aluImm .add a2 x0 0x7, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d5e : fetchRel bootMainClosure0Code 0xD5E = some (.aluImm .add (18 : Fin 32) x0 0x7, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d60 : fetchRel bootMainClosure0Code 0xD60 = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d64 : fetchRel bootMainClosure0Code 0xD64 = some (.jalr ra ra 0xFFFFF9B6, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d68 : fetchRel bootMainClosure0Code 0xD68 = some (.aluImm .add (22 : Fin 32) x0 0x0, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d6a : fetchRel bootMainClosure0Code 0xD6A = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d6c : fetchRel bootMainClosure0Code 0xD6C = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d70 : fetchRel bootMainClosure0Code 0xD70 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d72 : fetchRel bootMainClosure0Code 0xD72 = some (.store .sw a0 (9 : Fin 32) 0x0, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d74 : fetchRel bootMainClosure0Code 0xD74 = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d76 : fetchRel bootMainClosure0Code 0xD76 = some (.aluImm .add a1 a1 0x310, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d7a : fetchRel bootMainClosure0Code 0xD7A = some (.alu .add (9 : Fin 32) sp a1, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d7e : fetchRel bootMainClosure0Code 0xD7E = some (.store .sb a0 (8 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d82 : fetchRel bootMainClosure0Code 0xD82 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d84 : fetchRel bootMainClosure0Code 0xD84 = some (.aluImm .add a0 a0 0xFFFFFED0, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d88 : fetchRel bootMainClosure0Code 0xD88 = some (.alu .add (20 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d8c : fetchRel bootMainClosure0Code 0xD8C = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d8e : fetchRel bootMainClosure0Code 0xD8E = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d92 : fetchRel bootMainClosure0Code 0xD92 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d94 : fetchRel bootMainClosure0Code 0xD94 = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d96 : fetchRel bootMainClosure0Code 0xD96 = some (.aluImm .add a1 a1 0x310, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d9a : fetchRel bootMainClosure0Code 0xD9A = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_d9c : fetchRel bootMainClosure0Code 0xD9C = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_da0 : fetchRel bootMainClosure0Code 0xDA0 = some (.jalr ra ra 0x7D6, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_da4 : fetchRel bootMainClosure0Code 0xDA4 = some (.load .lbu a0 (9 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_da8 : fetchRel bootMainClosure0Code 0xDA8 = some (.branch .bne a0 x0 0x7E, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_daa : fetchRel bootMainClosure0Code 0xDAA = some (.load .lw a1 (9 : Fin 32) 0x14, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dac : fetchRel bootMainClosure0Code 0xDAC = some (.branch .beq a1 x0 0x82, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dae : fetchRel bootMainClosure0Code 0xDAE = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_db0 : fetchRel bootMainClosure0Code 0xDB0 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_db4 : fetchRel bootMainClosure0Code 0xDB4 = some (.alu .add (8 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_db8 : fetchRel bootMainClosure0Code 0xDB8 = some (.load .lw a2 (8 : Fin 32) 0x18, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dba : fetchRel bootMainClosure0Code 0xDBA = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dbc : fetchRel bootMainClosure0Code 0xDBC = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dc0 : fetchRel bootMainClosure0Code 0xDC0 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dc2 : fetchRel bootMainClosure0Code 0xDC2 = some (.lui a3 0x2000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dc4 : fetchRel bootMainClosure0Code 0xDC4 = some (.aluImm .add a3 a3 0xFFFFFFDC, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dc8 : fetchRel bootMainClosure0Code 0xDC8 = some (.alu .add a3 a3 sp, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dca : fetchRel bootMainClosure0Code 0xDCA = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dce : fetchRel bootMainClosure0Code 0xDCE = some (.jalr ra ra 0xFFFFF934, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dd2 : fetchRel bootMainClosure0Code 0xDD2 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dd4 : fetchRel bootMainClosure0Code 0xDD4 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dd8 : fetchRel bootMainClosure0Code 0xDD8 = some (.alu .add (9 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ddc : fetchRel bootMainClosure0Code 0xDDC = some (.load .lw a0 (8 : Fin 32) 0x10, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dde : fetchRel bootMainClosure0Code 0xDDE = some (.branch .beq a0 x0 0x3C0, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_de2 : fetchRel bootMainClosure0Code 0xDE2 = some (.load .lw a0 (9 : Fin 32) 0x38, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_de4 : fetchRel bootMainClosure0Code 0xDE4 = some (.branch .beq a0 x0 0xFFFFFFA8, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_de6 : fetchRel bootMainClosure0Code 0xDE6 = some (.branch .bltu (18 : Fin 32) (22 : Fin 32) 0x63E, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dea : fetchRel bootMainClosure0Code 0xDEA = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dec : fetchRel bootMainClosure0Code 0xDEC = some (.aluImm .add a1 a1 0x310, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_df0 : fetchRel bootMainClosure0Code 0xDF0 = some (.alu .add (8 : Fin 32) sp a1, 4) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_df4 : fetchRel bootMainClosure0Code 0xDF4 = some (.load .lw a1 (8 : Fin 32) 0x20, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_df6 : fetchRel bootMainClosure0Code 0xDF6 = some (.load .lw a2 (8 : Fin 32) 0x24, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_df8 : fetchRel bootMainClosure0Code 0xDF8 = some (.load .lw a3 (8 : Fin 32) 0x40, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dfa : fetchRel bootMainClosure0Code 0xDFA = some (.load .lw a4 (8 : Fin 32) 0x44, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dfc : fetchRel bootMainClosure0Code 0xDFC = some (.load .lw a5 (8 : Fin 32) 0x48, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_dfe : fetchRel bootMainClosure0Code 0xDFE = some (.lui a6 0x1000, 2) :=
  (fetchRel_chunk ac_c13_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e00 : fetchRel bootMainClosure0Code 0xE00 = some (.aluImm .add a6 a6 0x310, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e04 : fetchRel bootMainClosure0Code 0xE04 = some (.alu .add (9 : Fin 32) sp a6, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e08 : fetchRel bootMainClosure0Code 0xE08 = some (.load .lw a6 (8 : Fin 32) 0x4C, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e0c : fetchRel bootMainClosure0Code 0xE0C = some (.aluImm .sll (8 : Fin 32) (22 : Fin 32) 0x5, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e10 : fetchRel bootMainClosure0Code 0xE10 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (20 : Fin 32), 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e12 : fetchRel bootMainClosure0Code 0xE12 = some (.store .sw (8 : Fin 32) a1 0x0, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e14 : fetchRel bootMainClosure0Code 0xE14 = some (.store .sw (8 : Fin 32) a2 0x4, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e16 : fetchRel bootMainClosure0Code 0xE16 = some (.store .sw (8 : Fin 32) a3 0x8, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e18 : fetchRel bootMainClosure0Code 0xE18 = some (.store .sw (8 : Fin 32) a4 0xC, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e1a : fetchRel bootMainClosure0Code 0xE1A = some (.store .sw (8 : Fin 32) a5 0x10, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e1c : fetchRel bootMainClosure0Code 0xE1C = some (.store .sw (8 : Fin 32) a6 0x14, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e20 : fetchRel bootMainClosure0Code 0xE20 = some (.store .sw (8 : Fin 32) a0 0x18, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e22 : fetchRel bootMainClosure0Code 0xE22 = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0x1, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e24 : fetchRel bootMainClosure0Code 0xE24 = some (.jal x0 0xFFFFFF68, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e26 : fetchRel bootMainClosure0Code 0xE26 = some (.load .lbu (8 : Fin 32) (9 : Fin 32) 0x11, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e2a : fetchRel bootMainClosure0Code 0xE2A = some (.jal x0 0xC40, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e2e : fetchRel bootMainClosure0Code 0xE2E = some (.aluImm .add a0 sp 0x350, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e30 : fetchRel bootMainClosure0Code 0xE30 = some (.aluImm .add a1 x0 0x10, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e32 : fetchRel bootMainClosure0Code 0xE32 = some (.branch .beq a1 x0 0xE, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e34 : fetchRel bootMainClosure0Code 0xE34 = some (.store .sw a0 x0 0x0, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e38 : fetchRel bootMainClosure0Code 0xE38 = some (.aluImm .add a0 a0 0x20, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e3c : fetchRel bootMainClosure0Code 0xE3C = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e3e : fetchRel bootMainClosure0Code 0xE3E = some (.branch .bne a1 x0 0xFFFFFFF6, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e40 : fetchRel bootMainClosure0Code 0xE40 = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e44 : fetchRel bootMainClosure0Code 0xE44 = some (.aluImm .add a3 a3 0x7F2, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e48 : fetchRel bootMainClosure0Code 0xE48 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e4c : fetchRel bootMainClosure0Code 0xE4C = some (.aluImm .add a0 a0 0x91, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e50 : fetchRel bootMainClosure0Code 0xE50 = some (.aluImm .add a4 x0 0x5, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e52 : fetchRel bootMainClosure0Code 0xE52 = some (.alu .add a1 x0 (26 : Fin 32), 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e54 : fetchRel bootMainClosure0Code 0xE54 = some (.load .lw a2 sp 0x30, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e56 : fetchRel bootMainClosure0Code 0xE56 = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e5a : fetchRel bootMainClosure0Code 0xE5A = some (.jalr ra ra 0x77A, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e5e : fetchRel bootMainClosure0Code 0xE5E = some (.load .lw a1 (19 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e62 : fetchRel bootMainClosure0Code 0xE62 = some (.branch .beq a1 x0 0x5AE, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e66 : fetchRel bootMainClosure0Code 0xE66 = some (.load .lw a2 (19 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e6a : fetchRel bootMainClosure0Code 0xE6A = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e6c : fetchRel bootMainClosure0Code 0xE6C = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e70 : fetchRel bootMainClosure0Code 0xE70 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e72 : fetchRel bootMainClosure0Code 0xE72 = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e76 : fetchRel bootMainClosure0Code 0xE76 = some (.jalr ra ra 0x6B6, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e7a : fetchRel bootMainClosure0Code 0xE7A = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e7c : fetchRel bootMainClosure0Code 0xE7C = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e80 : fetchRel bootMainClosure0Code 0xE80 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e82 : fetchRel bootMainClosure0Code 0xE82 = some (.load .lw (9 : Fin 32) a0 0x10, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e84 : fetchRel bootMainClosure0Code 0xE84 = some (.load .lbu (8 : Fin 32) a0 0x14, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e88 : fetchRel bootMainClosure0Code 0xE88 = some (.branch .beq (9 : Fin 32) x0 0xBE2, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e8c : fetchRel bootMainClosure0Code 0xE8C = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e8e : fetchRel bootMainClosure0Code 0xE8E = some (.aluImm .add a0 a0 0x325, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e92 : fetchRel bootMainClosure0Code 0xE92 = some (.alu .add a1 sp a0, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e96 : fetchRel bootMainClosure0Code 0xE96 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e98 : fetchRel bootMainClosure0Code 0xE98 = some (.aluImm .add a0 a0 0xFFFFF865, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e9c : fetchRel bootMainClosure0Code 0xE9C = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_e9e : fetchRel bootMainClosure0Code 0xE9E = some (.aluImm .add a2 x0 0x7, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ea0 : fetchRel bootMainClosure0Code 0xEA0 = some (.auipc ra 0x16000, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ea4 : fetchRel bootMainClosure0Code 0xEA4 = some (.jalr ra ra 0xFFFFF876, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ea8 : fetchRel bootMainClosure0Code 0xEA8 = some (.store .sw sp x0 0x2C, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_eaa : fetchRel bootMainClosure0Code 0xEAA = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_eac : fetchRel bootMainClosure0Code 0xEAC = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_eb0 : fetchRel bootMainClosure0Code 0xEB0 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_eb2 : fetchRel bootMainClosure0Code 0xEB2 = some (.store .sw a0 (9 : Fin 32) 0x550, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_eb6 : fetchRel bootMainClosure0Code 0xEB6 = some (.store .sb a0 (8 : Fin 32) 0x554, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_eba : fetchRel bootMainClosure0Code 0xEBA = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ebc : fetchRel bootMainClosure0Code 0xEBC = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ec0 : fetchRel bootMainClosure0Code 0xEC0 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ec2 : fetchRel bootMainClosure0Code 0xEC2 = some (.lui a1 0x2000, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ec4 : fetchRel bootMainClosure0Code 0xEC4 = some (.aluImm .add a1 a1 0xFFFFF860, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ec8 : fetchRel bootMainClosure0Code 0xEC8 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_eca : fetchRel bootMainClosure0Code 0xECA = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ece : fetchRel bootMainClosure0Code 0xECE = some (.jalr ra ra 0x6A8, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ed2 : fetchRel bootMainClosure0Code 0xED2 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ed4 : fetchRel bootMainClosure0Code 0xED4 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ed8 : fetchRel bootMainClosure0Code 0xED8 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_eda : fetchRel bootMainClosure0Code 0xEDA = some (.load .lbu a0 a0 0x10, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ede : fetchRel bootMainClosure0Code 0xEDE = some (.branch .bne a0 x0 0x538, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ee2 : fetchRel bootMainClosure0Code 0xEE2 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ee4 : fetchRel bootMainClosure0Code 0xEE4 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ee8 : fetchRel bootMainClosure0Code 0xEE8 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_eea : fetchRel bootMainClosure0Code 0xEEA = some (.load .lw (22 : Fin 32) a0 0x14, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_eee : fetchRel bootMainClosure0Code 0xEEE = some (.branch .beq (22 : Fin 32) x0 0x2B8, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ef2 : fetchRel bootMainClosure0Code 0xEF2 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ef4 : fetchRel bootMainClosure0Code 0xEF4 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ef8 : fetchRel bootMainClosure0Code 0xEF8 = some (.alu .add (8 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_efc : fetchRel bootMainClosure0Code 0xEFC = some (.load .lw (23 : Fin 32) (8 : Fin 32) 0x18, 4) :=
  (fetchRel_chunk ac_c14_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f00 : fetchRel bootMainClosure0Code 0xF00 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f02 : fetchRel bootMainClosure0Code 0xF02 = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f06 : fetchRel bootMainClosure0Code 0xF06 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f08 : fetchRel bootMainClosure0Code 0xF08 = some (.aluImm .add a4 x0 0x9, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f0a : fetchRel bootMainClosure0Code 0xF0A = some (.alu .add a1 x0 (22 : Fin 32), 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f0c : fetchRel bootMainClosure0Code 0xF0C = some (.alu .add a2 x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f0e : fetchRel bootMainClosure0Code 0xF0E = some (.lui a3 0x3FCC5000, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f12 : fetchRel bootMainClosure0Code 0xF12 = some (.aluImm .add a3 a3 0xFFFFF80B, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f16 : fetchRel bootMainClosure0Code 0xF16 = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f1a : fetchRel bootMainClosure0Code 0xF1A = some (.jalr ra ra 0x6BA, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f1e : fetchRel bootMainClosure0Code 0xF1E = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f20 : fetchRel bootMainClosure0Code 0xF20 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f24 : fetchRel bootMainClosure0Code 0xF24 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f26 : fetchRel bootMainClosure0Code 0xF26 = some (.load .lw a1 (8 : Fin 32) 0x10, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f28 : fetchRel bootMainClosure0Code 0xF28 = some (.store .sw sp a1 0x28, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f2a : fetchRel bootMainClosure0Code 0xF2A = some (.branch .beq a1 x0 0x4E0, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f2e : fetchRel bootMainClosure0Code 0xF2E = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f30 : fetchRel bootMainClosure0Code 0xF30 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f34 : fetchRel bootMainClosure0Code 0xF34 = some (.alu .add (8 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f38 : fetchRel bootMainClosure0Code 0xF38 = some (.load .lw a2 (8 : Fin 32) 0x14, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f3a : fetchRel bootMainClosure0Code 0xF3A = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f3c : fetchRel bootMainClosure0Code 0xF3C = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f40 : fetchRel bootMainClosure0Code 0xF40 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f42 : fetchRel bootMainClosure0Code 0xF42 = some (.aluImm .add a4 x0 0xA, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f44 : fetchRel bootMainClosure0Code 0xF44 = some (.load .lw a1 sp 0x28, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f46 : fetchRel bootMainClosure0Code 0xF46 = some (.store .sw sp a2 0x1C, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f48 : fetchRel bootMainClosure0Code 0xF48 = some (.lui a3 0x3FCC5000, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f4c : fetchRel bootMainClosure0Code 0xF4C = some (.aluImm .add a3 a3 0xFFFFF814, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f50 : fetchRel bootMainClosure0Code 0xF50 = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f54 : fetchRel bootMainClosure0Code 0xF54 = some (.jalr ra ra 0x680, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f58 : fetchRel bootMainClosure0Code 0xF58 = some (.load .lw a1 (8 : Fin 32) 0x10, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f5a : fetchRel bootMainClosure0Code 0xF5A = some (.branch .beq a1 x0 0x4A8, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f5e : fetchRel bootMainClosure0Code 0xF5E = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f60 : fetchRel bootMainClosure0Code 0xF60 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f64 : fetchRel bootMainClosure0Code 0xF64 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f66 : fetchRel bootMainClosure0Code 0xF66 = some (.load .lw a2 a0 0x14, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f68 : fetchRel bootMainClosure0Code 0xF68 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f6c : fetchRel bootMainClosure0Code 0xF6C = some (.aluImm .add a0 a0 0x91, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f70 : fetchRel bootMainClosure0Code 0xF70 = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f74 : fetchRel bootMainClosure0Code 0xF74 = some (.jalr ra ra 0x69C, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f78 : fetchRel bootMainClosure0Code 0xF78 = some (.load .lw a0 (19 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f7c : fetchRel bootMainClosure0Code 0xF7C = some (.branch .beq a0 x0 0x494, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f80 : fetchRel bootMainClosure0Code 0xF80 = some (.load .lw a1 (19 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f84 : fetchRel bootMainClosure0Code 0xF84 = some (.aluImm .add a2 x0 0xC, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f86 : fetchRel bootMainClosure0Code 0xF86 = some (.branch .bne a1 a2 0xFFFFFF34, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f8a : fetchRel bootMainClosure0Code 0xF8A = some (.aluImm .add a2 x0 0xC, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f8c : fetchRel bootMainClosure0Code 0xF8C = some (.lui a1 0x3FCC5000, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f90 : fetchRel bootMainClosure0Code 0xF90 = some (.aluImm .add a1 a1 0xFFFFF81E, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f94 : fetchRel bootMainClosure0Code 0xF94 = some (.auipc ra 0x15000, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f98 : fetchRel bootMainClosure0Code 0xF98 = some (.jalr ra ra 0x6FA, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f9c : fetchRel bootMainClosure0Code 0xF9C = some (.branch .bne a0 x0 0xFFFFFF1E, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_f9e : fetchRel bootMainClosure0Code 0xF9E = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fa0 : fetchRel bootMainClosure0Code 0xFA0 = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fa4 : fetchRel bootMainClosure0Code 0xFA4 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fa6 : fetchRel bootMainClosure0Code 0xFA6 = some (.aluImm .add a4 x0 0x8, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fa8 : fetchRel bootMainClosure0Code 0xFA8 = some (.load .lw a1 sp 0x28, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_faa : fetchRel bootMainClosure0Code 0xFAA = some (.load .lw a2 sp 0x1C, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fac : fetchRel bootMainClosure0Code 0xFAC = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fb0 : fetchRel bootMainClosure0Code 0xFB0 = some (.aluImm .add a3 a3 0x730, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fb4 : fetchRel bootMainClosure0Code 0xFB4 = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fb8 : fetchRel bootMainClosure0Code 0xFB8 = some (.jalr ra ra 0x61C, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fbc : fetchRel bootMainClosure0Code 0xFBC = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fbe : fetchRel bootMainClosure0Code 0xFBE = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fc2 : fetchRel bootMainClosure0Code 0xFC2 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fc4 : fetchRel bootMainClosure0Code 0xFC4 = some (.load .lw a1 a0 0x10, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fc6 : fetchRel bootMainClosure0Code 0xFC6 = some (.branch .beq a1 x0 0x43C, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fca : fetchRel bootMainClosure0Code 0xFCA = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fcc : fetchRel bootMainClosure0Code 0xFCC = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fd0 : fetchRel bootMainClosure0Code 0xFD0 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fd2 : fetchRel bootMainClosure0Code 0xFD2 = some (.load .lw a2 a0 0x14, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fd4 : fetchRel bootMainClosure0Code 0xFD4 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fd8 : fetchRel bootMainClosure0Code 0xFD8 = some (.aluImm .add a0 a0 0x91, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fdc : fetchRel bootMainClosure0Code 0xFDC = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fe0 : fetchRel bootMainClosure0Code 0xFE0 = some (.jalr ra ra 0x630, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fe4 : fetchRel bootMainClosure0Code 0xFE4 = some (.load .lw a1 (19 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fe8 : fetchRel bootMainClosure0Code 0xFE8 = some (.branch .beq a1 x0 0x428, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_fec : fetchRel bootMainClosure0Code 0xFEC = some (.load .lw a2 (19 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ff0 : fetchRel bootMainClosure0Code 0xFF0 = some (.aluImm .add a0 sp 0x244, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ff2 : fetchRel bootMainClosure0Code 0xFF2 = some (.lui a3 0x2000, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ff4 : fetchRel bootMainClosure0Code 0xFF4 = some (.aluImm .add a3 a3 0xFFFFFFDC, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ff8 : fetchRel bootMainClosure0Code 0xFF8 = some (.alu .add a3 a3 sp, 2) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ffa : fetchRel bootMainClosure0Code 0xFFA = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_ffe : fetchRel bootMainClosure0Code 0xFFE = some (.jalr ra ra 0xFFFFFC48, 4) :=
  (fetchRel_chunk ac_c15_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1002 : fetchRel bootMainClosure0Code 0x1002 = some (.load .lw (24 : Fin 32) sp 0x244, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1006 : fetchRel bootMainClosure0Code 0x1006 = some (.branch .beq (24 : Fin 32) x0 0x422, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_100a : fetchRel bootMainClosure0Code 0x100A = some (.load .lw (9 : Fin 32) sp 0x248, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_100e : fetchRel bootMainClosure0Code 0x100E = some (.aluImm .add (8 : Fin 32) x0 0xE, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1010 : fetchRel bootMainClosure0Code 0x1010 = some (.aluImm .add a0 x0 0xC, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1012 : fetchRel bootMainClosure0Code 0x1012 = some (.branch .bltu (9 : Fin 32) a0 0xA58, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1016 : fetchRel bootMainClosure0Code 0x1016 = some (.aluImm .add a2 x0 0xC, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1018 : fetchRel bootMainClosure0Code 0x1018 = some (.alu .add a0 x0 (24 : Fin 32), 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_101a : fetchRel bootMainClosure0Code 0x101A = some (.lui a1 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_101e : fetchRel bootMainClosure0Code 0x101E = some (.aluImm .add a1 a1 0x690, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1022 : fetchRel bootMainClosure0Code 0x1022 = some (.auipc ra 0x8000, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1026 : fetchRel bootMainClosure0Code 0x1026 = some (.jalr ra ra 0x2AE, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_102a : fetchRel bootMainClosure0Code 0x102A = some (.aluImm .add (18 : Fin 32) (9 : Fin 32) 0xFFFFFFD4, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_102e : fetchRel bootMainClosure0Code 0x102E = some (.branch .bne (18 : Fin 32) x0 0xA3C, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1032 : fetchRel bootMainClosure0Code 0x1032 = some (.alu .add (20 : Fin 32) x0 a0, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1034 : fetchRel bootMainClosure0Code 0x1034 = some (.branch .beq a0 x0 0xA36, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1038 : fetchRel bootMainClosure0Code 0x1038 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0xC, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_103a : fetchRel bootMainClosure0Code 0x103A = some (.alu .add a0 x0 (24 : Fin 32), 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_103c : fetchRel bootMainClosure0Code 0x103C = some (.auipc ra 0x4000, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1040 : fetchRel bootMainClosure0Code 0x1040 = some (.jalr ra ra 0xFFFFFCAC, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1044 : fetchRel bootMainClosure0Code 0x1044 = some (.branch .beq a0 x0 0xA26, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1048 : fetchRel bootMainClosure0Code 0x1048 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_104a : fetchRel bootMainClosure0Code 0x104A = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_104e : fetchRel bootMainClosure0Code 0x104E = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1050 : fetchRel bootMainClosure0Code 0x1050 = some (.aluImm .add a4 x0 0x7, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1052 : fetchRel bootMainClosure0Code 0x1052 = some (.alu .add a1 x0 (22 : Fin 32), 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1054 : fetchRel bootMainClosure0Code 0x1054 = some (.alu .add a2 x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1056 : fetchRel bootMainClosure0Code 0x1056 = some (.lui a3 0x3FCC5000, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_105a : fetchRel bootMainClosure0Code 0x105A = some (.aluImm .add a3 a3 0xFFFFF82A, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_105e : fetchRel bootMainClosure0Code 0x105E = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1062 : fetchRel bootMainClosure0Code 0x1062 = some (.jalr ra ra 0x572, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1066 : fetchRel bootMainClosure0Code 0x1066 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1068 : fetchRel bootMainClosure0Code 0x1068 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_106c : fetchRel bootMainClosure0Code 0x106C = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_106e : fetchRel bootMainClosure0Code 0x106E = some (.load .lw a1 a0 0x10, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1070 : fetchRel bootMainClosure0Code 0x1070 = some (.branch .beq a1 x0 0x392, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1074 : fetchRel bootMainClosure0Code 0x1074 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1076 : fetchRel bootMainClosure0Code 0x1076 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_107a : fetchRel bootMainClosure0Code 0x107A = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_107c : fetchRel bootMainClosure0Code 0x107C = some (.load .lw a2 a0 0x14, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_107e : fetchRel bootMainClosure0Code 0x107E = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1082 : fetchRel bootMainClosure0Code 0x1082 = some (.aluImm .add a0 a0 0x91, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1086 : fetchRel bootMainClosure0Code 0x1086 = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_108a : fetchRel bootMainClosure0Code 0x108A = some (.jalr ra ra 0x586, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_108e : fetchRel bootMainClosure0Code 0x108E = some (.load .lw (9 : Fin 32) (19 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1092 : fetchRel bootMainClosure0Code 0x1092 = some (.branch .beq (9 : Fin 32) x0 0x37E, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1096 : fetchRel bootMainClosure0Code 0x1096 = some (.load .lw (23 : Fin 32) (19 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_109a : fetchRel bootMainClosure0Code 0x109A = some (.aluImm .add (8 : Fin 32) x0 0x21, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_109e : fetchRel bootMainClosure0Code 0x109E = some (.aluImm .add a0 x0 0x8, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10a0 : fetchRel bootMainClosure0Code 0x10A0 = some (.branch .bltu (23 : Fin 32) a0 0x9CA, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10a4 : fetchRel bootMainClosure0Code 0x10A4 = some (.aluImm .add a2 x0 0x8, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10a6 : fetchRel bootMainClosure0Code 0x10A6 = some (.alu .add a0 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10a8 : fetchRel bootMainClosure0Code 0x10A8 = some (.lui a1 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10ac : fetchRel bootMainClosure0Code 0x10AC = some (.aluImm .add a1 a1 0x740, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10b0 : fetchRel bootMainClosure0Code 0x10B0 = some (.auipc ra 0x8000, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10b4 : fetchRel bootMainClosure0Code 0x10B4 = some (.jalr ra ra 0x220, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10b8 : fetchRel bootMainClosure0Code 0x10B8 = some (.branch .beq a0 x0 0x9B2, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10bc : fetchRel bootMainClosure0Code 0x10BC = some (.aluImm .sltu a0 (18 : Fin 32) 0x1, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10c0 : fetchRel bootMainClosure0Code 0x10C0 = some (.alu .and a0 a0 (20 : Fin 32), 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10c4 : fetchRel bootMainClosure0Code 0x10C4 = some (.aluImm .add (20 : Fin 32) (9 : Fin 32) 0x8, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10c8 : fetchRel bootMainClosure0Code 0x10C8 = some (.alu .sub a0 x0 a0, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10cc : fetchRel bootMainClosure0Code 0x10CC = some (.aluImm .add (18 : Fin 32) (23 : Fin 32) 0xFFFFFFF8, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10d0 : fetchRel bootMainClosure0Code 0x10D0 = some (.alu .and (24 : Fin 32) a0 (24 : Fin 32), 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10d4 : fetchRel bootMainClosure0Code 0x10D4 = some (.aluImm .add (22 : Fin 32) (23 : Fin 32) 0xFFFFFFF9, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10d8 : fetchRel bootMainClosure0Code 0x10D8 = some (.alu .add (23 : Fin 32) (23 : Fin 32) (9 : Fin 32), 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10da : fetchRel bootMainClosure0Code 0x10DA = some (.branch .beq (18 : Fin 32) x0 0x990, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10de : fetchRel bootMainClosure0Code 0x10DE = some (.alu .add (9 : Fin 32) x0 (18 : Fin 32), 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10e0 : fetchRel bootMainClosure0Code 0x10E0 = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10e2 : fetchRel bootMainClosure0Code 0x10E2 = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10e4 : fetchRel bootMainClosure0Code 0x10E4 = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10e6 : fetchRel bootMainClosure0Code 0x10E6 = some (.aluImm .add a2 x0 0x1, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10e8 : fetchRel bootMainClosure0Code 0x10E8 = some (.alu .add a0 x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10ea : fetchRel bootMainClosure0Code 0x10EA = some (.lui a1 0x3FCC5000, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10ee : fetchRel bootMainClosure0Code 0x10EE = some (.aluImm .add a1 a1 0xFFFFF831, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10f2 : fetchRel bootMainClosure0Code 0x10F2 = some (.auipc ra 0x8000, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10f6 : fetchRel bootMainClosure0Code 0x10F6 = some (.jalr ra ra 0x1DE, 4) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10fa : fetchRel bootMainClosure0Code 0x10FA = some (.branch .bne a0 x0 0xFFFFFFE0, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10fc : fetchRel bootMainClosure0Code 0x10FC = some (.alu .add a0 x0 (20 : Fin 32), 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_10fe : fetchRel bootMainClosure0Code 0x10FE = some (.branch .beq (9 : Fin 32) x0 0x18, 2) :=
  (fetchRel_chunk ac_c16_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1100 : fetchRel bootMainClosure0Code 0x1100 = some (.load .lbu a1 a0 0x0, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1104 : fetchRel bootMainClosure0Code 0x1104 = some (.aluImm .add a0 a0 0x1, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1106 : fetchRel bootMainClosure0Code 0x1106 = some (.aluImm .add a1 a1 0xFFFFFFE0, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1108 : fetchRel bootMainClosure0Code 0x1108 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_110a : fetchRel bootMainClosure0Code 0x110A = some (.aluImm .add a2 x0 0x5F, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_110e : fetchRel bootMainClosure0Code 0x110E = some (.branch .bltu a1 a2 0xFFFFFFF0, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1112 : fetchRel bootMainClosure0Code 0x1112 = some (.jal x0 0x958, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1116 : fetchRel bootMainClosure0Code 0x1116 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_111a : fetchRel bootMainClosure0Code 0x111A = some (.aluImm .add a0 a0 0x91, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_111e : fetchRel bootMainClosure0Code 0x111E = some (.aluImm .add a4 x0 0x8, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1120 : fetchRel bootMainClosure0Code 0x1120 = some (.load .lw a1 sp 0x28, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1122 : fetchRel bootMainClosure0Code 0x1122 = some (.load .lw a2 sp 0x1C, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1124 : fetchRel bootMainClosure0Code 0x1124 = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1128 : fetchRel bootMainClosure0Code 0x1128 = some (.aluImm .add a3 a3 0x700, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_112c : fetchRel bootMainClosure0Code 0x112C = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1130 : fetchRel bootMainClosure0Code 0x1130 = some (.jalr ra ra 0x4A4, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1134 : fetchRel bootMainClosure0Code 0x1134 = some (.load .lw a1 (19 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1138 : fetchRel bootMainClosure0Code 0x1138 = some (.branch .beq a1 x0 0x2D8, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_113c : fetchRel bootMainClosure0Code 0x113C = some (.load .lw a2 (19 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1140 : fetchRel bootMainClosure0Code 0x1140 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1142 : fetchRel bootMainClosure0Code 0x1142 = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1146 : fetchRel bootMainClosure0Code 0x1146 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1148 : fetchRel bootMainClosure0Code 0x1148 = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_114c : fetchRel bootMainClosure0Code 0x114C = some (.jalr ra ra 0xFFFFFB64, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1150 : fetchRel bootMainClosure0Code 0x1150 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1152 : fetchRel bootMainClosure0Code 0x1152 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1156 : fetchRel bootMainClosure0Code 0x1156 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1158 : fetchRel bootMainClosure0Code 0x1158 = some (.load .lbu a0 a0 0x10, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_115c : fetchRel bootMainClosure0Code 0x115C = some (.branch .bne a0 x0 0x2BA, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1160 : fetchRel bootMainClosure0Code 0x1160 = some (.load .lw a0 sp 0x2C, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1162 : fetchRel bootMainClosure0Code 0x1162 = some (.aluImm .add a1 x0 0xF, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1164 : fetchRel bootMainClosure0Code 0x1164 = some (.branch .bltu a1 a0 0x2C0, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1168 : fetchRel bootMainClosure0Code 0x1168 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_116a : fetchRel bootMainClosure0Code 0x116A = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_116e : fetchRel bootMainClosure0Code 0x116E = some (.alu .add a3 sp a0, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1172 : fetchRel bootMainClosure0Code 0x1172 = some (.load .lw a0 a3 0x18, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1174 : fetchRel bootMainClosure0Code 0x1174 = some (.load .lw a1 a3 0x1C, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1176 : fetchRel bootMainClosure0Code 0x1176 = some (.load .lw a2 a3 0x20, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1178 : fetchRel bootMainClosure0Code 0x1178 = some (.load .lw a3 a3 0x24, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_117a : fetchRel bootMainClosure0Code 0x117A = some (.load .lw a5 sp 0x2C, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_117c : fetchRel bootMainClosure0Code 0x117C = some (.aluImm .sll a4 a5 0x5, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1180 : fetchRel bootMainClosure0Code 0x1180 = some (.aluImm .add (9 : Fin 32) sp 0x350, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1182 : fetchRel bootMainClosure0Code 0x1182 = some (.alu .add a4 a4 (9 : Fin 32), 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1184 : fetchRel bootMainClosure0Code 0x1184 = some (.store .sw a4 (20 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1188 : fetchRel bootMainClosure0Code 0x1188 = some (.store .sw a4 (22 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_118c : fetchRel bootMainClosure0Code 0x118C = some (.store .sw a4 a0 0x8, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_118e : fetchRel bootMainClosure0Code 0x118E = some (.store .sw a4 a1 0xC, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1190 : fetchRel bootMainClosure0Code 0x1190 = some (.store .sw a4 a2 0x10, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1192 : fetchRel bootMainClosure0Code 0x1192 = some (.store .sw a4 a3 0x14, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1194 : fetchRel bootMainClosure0Code 0x1194 = some (.store .sw a4 (24 : Fin 32) 0x18, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1198 : fetchRel bootMainClosure0Code 0x1198 = some (.aluImm .add a5 a5 0x1, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_119a : fetchRel bootMainClosure0Code 0x119A = some (.store .sw sp a5 0x2C, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_119c : fetchRel bootMainClosure0Code 0x119C = some (.jal x0 0xFFFFFD1E, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_119e : fetchRel bootMainClosure0Code 0x119E = some (.load .lbu (8 : Fin 32) (9 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11a2 : fetchRel bootMainClosure0Code 0x11A2 = some (.jal x0 0x8C8, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11a6 : fetchRel bootMainClosure0Code 0x11A6 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11aa : fetchRel bootMainClosure0Code 0x11AA = some (.aluImm .add a0 a0 0x91, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11ae : fetchRel bootMainClosure0Code 0x11AE = some (.aluImm .add a1 x0 0x8, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11b0 : fetchRel bootMainClosure0Code 0x11B0 = some (.branch .beq a1 x0 0xE, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11b2 : fetchRel bootMainClosure0Code 0x11B2 = some (.store .sw a0 x0 0x0, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11b6 : fetchRel bootMainClosure0Code 0x11B6 = some (.aluImm .add a0 a0 0x20, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11ba : fetchRel bootMainClosure0Code 0x11BA = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11bc : fetchRel bootMainClosure0Code 0x11BC = some (.branch .bne a1 x0 0xFFFFFFF6, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11be : fetchRel bootMainClosure0Code 0x11BE = some (.lui a3 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11c2 : fetchRel bootMainClosure0Code 0x11C2 = some (.aluImm .add a3 a3 0x7F7, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11c6 : fetchRel bootMainClosure0Code 0x11C6 = some (.aluImm .add a0 sp 0x244, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11c8 : fetchRel bootMainClosure0Code 0x11C8 = some (.aluImm .add a4 x0 0x14, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11ca : fetchRel bootMainClosure0Code 0x11CA = some (.alu .add a1 x0 (26 : Fin 32), 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11cc : fetchRel bootMainClosure0Code 0x11CC = some (.load .lw a2 sp 0x30, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11ce : fetchRel bootMainClosure0Code 0x11CE = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11d2 : fetchRel bootMainClosure0Code 0x11D2 = some (.jalr ra ra 0x402, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11d6 : fetchRel bootMainClosure0Code 0x11D6 = some (.load .lw a1 sp 0x244, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11da : fetchRel bootMainClosure0Code 0x11DA = some (.branch .beq a1 x0 0x24E, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11de : fetchRel bootMainClosure0Code 0x11DE = some (.load .lw a2 sp 0x248, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11e2 : fetchRel bootMainClosure0Code 0x11E2 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11e4 : fetchRel bootMainClosure0Code 0x11E4 = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11e8 : fetchRel bootMainClosure0Code 0x11E8 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11ea : fetchRel bootMainClosure0Code 0x11EA = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11ee : fetchRel bootMainClosure0Code 0x11EE = some (.jalr ra ra 0x33E, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11f2 : fetchRel bootMainClosure0Code 0x11F2 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11f4 : fetchRel bootMainClosure0Code 0x11F4 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11f8 : fetchRel bootMainClosure0Code 0x11F8 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11fa : fetchRel bootMainClosure0Code 0x11FA = some (.load .lw (9 : Fin 32) a0 0x10, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11fc : fetchRel bootMainClosure0Code 0x11FC = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_11fe : fetchRel bootMainClosure0Code 0x11FE = some (.aluImm .add a1 a1 0x310, 4) :=
  (fetchRel_chunk ac_c17_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1202 : fetchRel bootMainClosure0Code 0x1202 = some (.alu .add (19 : Fin 32) sp a1, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1206 : fetchRel bootMainClosure0Code 0x1206 = some (.load .lbu (8 : Fin 32) a0 0x14, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_120a : fetchRel bootMainClosure0Code 0x120A = some (.branch .beq (9 : Fin 32) x0 0x860, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_120e : fetchRel bootMainClosure0Code 0x120E = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1210 : fetchRel bootMainClosure0Code 0x1210 = some (.aluImm .add a0 a0 0x325, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1214 : fetchRel bootMainClosure0Code 0x1214 = some (.alu .add a1 sp a0, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1218 : fetchRel bootMainClosure0Code 0x1218 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_121a : fetchRel bootMainClosure0Code 0x121A = some (.aluImm .add a0 a0 0xFFFFFDCD, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_121e : fetchRel bootMainClosure0Code 0x121E = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1220 : fetchRel bootMainClosure0Code 0x1220 = some (.aluImm .add a2 x0 0x7, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1222 : fetchRel bootMainClosure0Code 0x1222 = some (.auipc ra 0x15000, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1226 : fetchRel bootMainClosure0Code 0x1226 = some (.jalr ra ra 0x4F4, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_122a : fetchRel bootMainClosure0Code 0x122A = some (.aluImm .add (26 : Fin 32) x0 0x0, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_122c : fetchRel bootMainClosure0Code 0x122C = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_122e : fetchRel bootMainClosure0Code 0x122E = some (.aluImm .add a0 a0 0xFFFFFDB0, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1232 : fetchRel bootMainClosure0Code 0x1232 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1234 : fetchRel bootMainClosure0Code 0x1234 = some (.store .sw a0 (9 : Fin 32) 0x18, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1236 : fetchRel bootMainClosure0Code 0x1236 = some (.store .sb a0 (8 : Fin 32) 0x1C, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_123a : fetchRel bootMainClosure0Code 0x123A = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_123c : fetchRel bootMainClosure0Code 0x123C = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1240 : fetchRel bootMainClosure0Code 0x1240 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1242 : fetchRel bootMainClosure0Code 0x1242 = some (.lui a1 0x2000, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1244 : fetchRel bootMainClosure0Code 0x1244 = some (.aluImm .add a1 a1 0xFFFFFDC8, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1248 : fetchRel bootMainClosure0Code 0x1248 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_124a : fetchRel bootMainClosure0Code 0x124A = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_124e : fetchRel bootMainClosure0Code 0x124E = some (.jalr ra ra 0x328, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1252 : fetchRel bootMainClosure0Code 0x1252 = some (.load .lbu a0 (19 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1256 : fetchRel bootMainClosure0Code 0x1256 = some (.branch .bne a0 x0 0x1D8, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_125a : fetchRel bootMainClosure0Code 0x125A = some (.load .lw a1 (19 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_125e : fetchRel bootMainClosure0Code 0x125E = some (.branch .beq a1 x0 0x1D6, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1262 : fetchRel bootMainClosure0Code 0x1262 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1264 : fetchRel bootMainClosure0Code 0x1264 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1268 : fetchRel bootMainClosure0Code 0x1268 = some (.alu .add (8 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_126c : fetchRel bootMainClosure0Code 0x126C = some (.load .lw a2 (8 : Fin 32) 0x18, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_126e : fetchRel bootMainClosure0Code 0x126E = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1270 : fetchRel bootMainClosure0Code 0x1270 = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1274 : fetchRel bootMainClosure0Code 0x1274 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1276 : fetchRel bootMainClosure0Code 0x1276 = some (.lui a3 0x2000, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1278 : fetchRel bootMainClosure0Code 0x1278 = some (.aluImm .add a3 a3 0xFFFFFFDC, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_127c : fetchRel bootMainClosure0Code 0x127C = some (.alu .add a3 a3 sp, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_127e : fetchRel bootMainClosure0Code 0x127E = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1282 : fetchRel bootMainClosure0Code 0x1282 = some (.jalr ra ra 0x480, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1286 : fetchRel bootMainClosure0Code 0x1286 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1288 : fetchRel bootMainClosure0Code 0x1288 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_128c : fetchRel bootMainClosure0Code 0x128C = some (.alu .add (19 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1290 : fetchRel bootMainClosure0Code 0x1290 = some (.load .lw a0 (8 : Fin 32) 0x10, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1292 : fetchRel bootMainClosure0Code 0x1292 = some (.branch .beq a0 x0 0x238, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1296 : fetchRel bootMainClosure0Code 0x1296 = some (.alu .add (23 : Fin 32) x0 a0, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1298 : fetchRel bootMainClosure0Code 0x1298 = some (.load .lw a0 (19 : Fin 32) 0x38, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_129c : fetchRel bootMainClosure0Code 0x129C = some (.store .sw sp a0 0x30, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_129e : fetchRel bootMainClosure0Code 0x129E = some (.branch .beq a0 x0 0xFFFFFF9C, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12a0 : fetchRel bootMainClosure0Code 0x12A0 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12a2 : fetchRel bootMainClosure0Code 0x12A2 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12a6 : fetchRel bootMainClosure0Code 0x12A6 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12a8 : fetchRel bootMainClosure0Code 0x12A8 = some (.load .lw a1 a0 0x14, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12aa : fetchRel bootMainClosure0Code 0x12AA = some (.load .lw (20 : Fin 32) a0 0x1C, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12ae : fetchRel bootMainClosure0Code 0x12AE = some (.alu .add a0 (20 : Fin 32) a1, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12b2 : fetchRel bootMainClosure0Code 0x12B2 = some (.branch .bltu a0 (20 : Fin 32) 0xFFFFF848, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12b6 : fetchRel bootMainClosure0Code 0x12B6 = some (.alu .add (22 : Fin 32) x0 a1, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12b8 : fetchRel bootMainClosure0Code 0x12B8 = some (.aluImm .srl a1 a0 0x10, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12bc : fetchRel bootMainClosure0Code 0x12BC = some (.branch .beq a1 x0 0x8, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12be : fetchRel bootMainClosure0Code 0x12BE = some (.aluImm .add a1 x0 0x501, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12c2 : fetchRel bootMainClosure0Code 0x12C2 = some (.jal x0 0xA, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12c4 : fetchRel bootMainClosure0Code 0x12C4 = some (.aluImm .sll a1 a0 0x10, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12c8 : fetchRel bootMainClosure0Code 0x12C8 = some (.aluImm .add a1 a1 0x500, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12cc : fetchRel bootMainClosure0Code 0x12CC = some (.aluImm .and a2 a1 0x1, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12d0 : fetchRel bootMainClosure0Code 0x12D0 = some (.aluImm .add (8 : Fin 32) x0 0x5, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12d2 : fetchRel bootMainClosure0Code 0x12D2 = some (.branch .bne a2 x0 0x798, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12d6 : fetchRel bootMainClosure0Code 0x12D6 = some (.lui a2 0x1000, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12d8 : fetchRel bootMainClosure0Code 0x12D8 = some (.aluImm .add a2 a2 0x310, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12dc : fetchRel bootMainClosure0Code 0x12DC = some (.alu .add a5 sp a2, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12e0 : fetchRel bootMainClosure0Code 0x12E0 = some (.load .lw a2 a5 0x4C, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12e2 : fetchRel bootMainClosure0Code 0x12E2 = some (.store .sw sp a2 0x2C, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12e4 : fetchRel bootMainClosure0Code 0x12E4 = some (.load .lw a2 a5 0x18, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12e6 : fetchRel bootMainClosure0Code 0x12E6 = some (.store .sw sp a2 0x14, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12e8 : fetchRel bootMainClosure0Code 0x12E8 = some (.load .lw a2 a5 0x40, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12ea : fetchRel bootMainClosure0Code 0x12EA = some (.store .sw sp a2 0x1C, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12ec : fetchRel bootMainClosure0Code 0x12EC = some (.load .lw a2 a5 0x44, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12ee : fetchRel bootMainClosure0Code 0x12EE = some (.store .sw sp a2 0x18, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12f0 : fetchRel bootMainClosure0Code 0x12F0 = some (.load .lw a2 a5 0x48, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12f2 : fetchRel bootMainClosure0Code 0x12F2 = some (.store .sw sp a2 0x28, 2) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12f4 : fetchRel bootMainClosure0Code 0x12F4 = some (.aluImm .srl a3 a1 0x10, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12f8 : fetchRel bootMainClosure0Code 0x12F8 = some (.aluImm .and a2 a3 0xFF, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_12fc : fetchRel bootMainClosure0Code 0x12FC = some (.aluImm .srl a4 a1 0x17, 4) :=
  (fetchRel_chunk ac_c18_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1300 : fetchRel bootMainClosure0Code 0x1300 = some (.aluImm .add (9 : Fin 32) x0 0x30, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1304 : fetchRel bootMainClosure0Code 0x1304 = some (.store .sb a5 (9 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1308 : fetchRel bootMainClosure0Code 0x1308 = some (.store .sb a5 a3 0x12, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_130c : fetchRel bootMainClosure0Code 0x130C = some (.lui a6 0x1000, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_130e : fetchRel bootMainClosure0Code 0x130E = some (.aluImm .add a6 a6 0x310, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1312 : fetchRel bootMainClosure0Code 0x1312 = some (.alu .add (19 : Fin 32) sp a6, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1316 : fetchRel bootMainClosure0Code 0x1316 = some (.store .sb a5 x0 0x13, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_131a : fetchRel bootMainClosure0Code 0x131A = some (.branch .bne a4 x0 0xA, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_131c : fetchRel bootMainClosure0Code 0x131C = some (.store .sb (19 : Fin 32) a2 0x11, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1320 : fetchRel bootMainClosure0Code 0x1320 = some (.aluImm .add a1 x0 0x2, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1322 : fetchRel bootMainClosure0Code 0x1322 = some (.jal x0 0x3A, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1324 : fetchRel bootMainClosure0Code 0x1324 = some (.aluImm .srl a1 a1 0x18, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1326 : fetchRel bootMainClosure0Code 0x1326 = some (.branch .bne a1 x0 0xE, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1328 : fetchRel bootMainClosure0Code 0x1328 = some (.aluImm .add a1 x0 0x81, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_132c : fetchRel bootMainClosure0Code 0x132C = some (.store .sb (19 : Fin 32) a1 0x11, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1330 : fetchRel bootMainClosure0Code 0x1330 = some (.aluImm .add a1 x0 0x3, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1332 : fetchRel bootMainClosure0Code 0x1332 = some (.jal x0 0x2A, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1334 : fetchRel bootMainClosure0Code 0x1334 = some (.aluImm .sll a3 a3 0x8, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1336 : fetchRel bootMainClosure0Code 0x1336 = some (.alu .or a1 a1 a3, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1338 : fetchRel bootMainClosure0Code 0x1338 = some (.lui a3 0x1000, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_133a : fetchRel bootMainClosure0Code 0x133A = some (.aluImm .add a3 a3 0x310, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_133e : fetchRel bootMainClosure0Code 0x133E = some (.alu .add a3 a3 sp, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1340 : fetchRel bootMainClosure0Code 0x1340 = some (.aluImm .add a4 x0 0x82, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1344 : fetchRel bootMainClosure0Code 0x1344 = some (.store .sb a3 a4 0x11, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1348 : fetchRel bootMainClosure0Code 0x1348 = some (.store .sb a3 a1 0x12, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_134c : fetchRel bootMainClosure0Code 0x134C = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_134e : fetchRel bootMainClosure0Code 0x134E = some (.aluImm .add a1 a1 0x310, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1352 : fetchRel bootMainClosure0Code 0x1352 = some (.alu .add (19 : Fin 32) sp a1, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1356 : fetchRel bootMainClosure0Code 0x1356 = some (.store .sb a3 a2 0x13, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_135a : fetchRel bootMainClosure0Code 0x135A = some (.aluImm .add a1 x0 0x4, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_135c : fetchRel bootMainClosure0Code 0x135C = some (.alu .add (18 : Fin 32) a1 a0, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1360 : fetchRel bootMainClosure0Code 0x1360 = some (.branch .bltu (18 : Fin 32) a1 0xFFFFF79A, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1364 : fetchRel bootMainClosure0Code 0x1364 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1366 : fetchRel bootMainClosure0Code 0x1366 = some (.aluImm .add a0 a0 0xFFFFFDB0, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_136a : fetchRel bootMainClosure0Code 0x136A = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_136c : fetchRel bootMainClosure0Code 0x136C = some (.load .lw a0 a0 0x230, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1370 : fetchRel bootMainClosure0Code 0x1370 = some (.branch .bltu a0 (18 : Fin 32) 0xFFFFF8CA, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1374 : fetchRel bootMainClosure0Code 0x1374 = some (.lui a2 0x2000, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1376 : fetchRel bootMainClosure0Code 0x1376 = some (.aluImm .add a2 a2 0xFFFFFDB0, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_137a : fetchRel bootMainClosure0Code 0x137A = some (.alu .add a3 sp a2, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_137e : fetchRel bootMainClosure0Code 0x137E = some (.aluImm .add a4 a3 0x200, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1382 : fetchRel bootMainClosure0Code 0x1382 = some (.load .lw (9 : Fin 32) a4 0x2C, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1384 : fetchRel bootMainClosure0Code 0x1384 = some (.alu .sub a0 a0 (18 : Fin 32), 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1388 : fetchRel bootMainClosure0Code 0x1388 = some (.alu .add a2 (9 : Fin 32) (18 : Fin 32), 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_138c : fetchRel bootMainClosure0Code 0x138C = some (.alu .add (24 : Fin 32) (9 : Fin 32) a1, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1390 : fetchRel bootMainClosure0Code 0x1390 = some (.store .sw a4 a2 0x2C, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1392 : fetchRel bootMainClosure0Code 0x1392 = some (.store .sw a4 a0 0x30, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1394 : fetchRel bootMainClosure0Code 0x1394 = some (.alu .add a0 (24 : Fin 32) (20 : Fin 32), 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1398 : fetchRel bootMainClosure0Code 0x1398 = some (.store .sw sp a0 0x10, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_139a : fetchRel bootMainClosure0Code 0x139A = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_139c : fetchRel bootMainClosure0Code 0x139C = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13a0 : fetchRel bootMainClosure0Code 0x13A0 = some (.alu .add a2 sp a0, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13a4 : fetchRel bootMainClosure0Code 0x13A4 = some (.alu .add a0 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13a6 : fetchRel bootMainClosure0Code 0x13A6 = some (.alu .add a3 x0 a1, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13a8 : fetchRel bootMainClosure0Code 0x13A8 = some (.auipc ra 0xE000, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13ac : fetchRel bootMainClosure0Code 0x13AC = some (.jalr ra ra 0xFFFFFD50, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13b0 : fetchRel bootMainClosure0Code 0x13B0 = some (.alu .add a0 x0 (24 : Fin 32), 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13b2 : fetchRel bootMainClosure0Code 0x13B2 = some (.alu .add a1 x0 (20 : Fin 32), 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13b4 : fetchRel bootMainClosure0Code 0x13B4 = some (.load .lw a2 sp 0x14, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13b6 : fetchRel bootMainClosure0Code 0x13B6 = some (.alu .add a3 x0 (20 : Fin 32), 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13b8 : fetchRel bootMainClosure0Code 0x13B8 = some (.auipc ra 0xE000, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13bc : fetchRel bootMainClosure0Code 0x13BC = some (.jalr ra ra 0xFFFFFD40, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13c0 : fetchRel bootMainClosure0Code 0x13C0 = some (.load .lw a0 sp 0x10, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13c2 : fetchRel bootMainClosure0Code 0x13C2 = some (.alu .add a1 x0 (22 : Fin 32), 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13c4 : fetchRel bootMainClosure0Code 0x13C4 = some (.alu .add a2 x0 (23 : Fin 32), 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13c6 : fetchRel bootMainClosure0Code 0x13C6 = some (.alu .add a3 x0 (22 : Fin 32), 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13c8 : fetchRel bootMainClosure0Code 0x13C8 = some (.auipc ra 0xE000, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13cc : fetchRel bootMainClosure0Code 0x13CC = some (.jalr ra ra 0xFFFFFD30, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13d0 : fetchRel bootMainClosure0Code 0x13D0 = some (.aluImm .add a0 x0 0x7, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13d2 : fetchRel bootMainClosure0Code 0x13D2 = some (.branch .bltu a0 (26 : Fin 32) 0x698, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13d6 : fetchRel bootMainClosure0Code 0x13D6 = some (.aluImm .sll a0 (26 : Fin 32) 0x5, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13da : fetchRel bootMainClosure0Code 0x13DA = some (.aluImm .add (26 : Fin 32) (26 : Fin 32) 0x1, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13dc : fetchRel bootMainClosure0Code 0x13DC = some (.aluImm .add a1 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13e0 : fetchRel bootMainClosure0Code 0x13E0 = some (.aluImm .add a1 a1 0x91, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13e4 : fetchRel bootMainClosure0Code 0x13E4 = some (.alu .add a0 a0 a1, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13e6 : fetchRel bootMainClosure0Code 0x13E6 = some (.store .sw a0 (9 : Fin 32) 0x0, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13e8 : fetchRel bootMainClosure0Code 0x13E8 = some (.store .sw a0 (18 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13ec : fetchRel bootMainClosure0Code 0x13EC = some (.load .lw a1 sp 0x1C, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13ee : fetchRel bootMainClosure0Code 0x13EE = some (.store .sw a0 a1 0x8, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13f0 : fetchRel bootMainClosure0Code 0x13F0 = some (.load .lw a1 sp 0x18, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13f2 : fetchRel bootMainClosure0Code 0x13F2 = some (.store .sw a0 a1 0xC, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13f4 : fetchRel bootMainClosure0Code 0x13F4 = some (.load .lw a1 sp 0x28, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13f6 : fetchRel bootMainClosure0Code 0x13F6 = some (.store .sw a0 a1 0x10, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13f8 : fetchRel bootMainClosure0Code 0x13F8 = some (.load .lw a1 sp 0x2C, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13fa : fetchRel bootMainClosure0Code 0x13FA = some (.store .sw a0 a1 0x14, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13fc : fetchRel bootMainClosure0Code 0x13FC = some (.load .lw a1 sp 0x30, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_13fe : fetchRel bootMainClosure0Code 0x13FE = some (.store .sw a0 a1 0x18, 2) :=
  (fetchRel_chunk ac_c19_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1400 : fetchRel bootMainClosure0Code 0x1400 = some (.jal x0 0xFFFFFE3A, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1402 : fetchRel bootMainClosure0Code 0x1402 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1404 : fetchRel bootMainClosure0Code 0x1404 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1408 : fetchRel bootMainClosure0Code 0x1408 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_140a : fetchRel bootMainClosure0Code 0x140A = some (.load .lbu (8 : Fin 32) a0 0x14, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_140e : fetchRel bootMainClosure0Code 0x140E = some (.jal x0 0x65C, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1410 : fetchRel bootMainClosure0Code 0x1410 = some (.load .lbu (8 : Fin 32) (19 : Fin 32) 0x4, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1414 : fetchRel bootMainClosure0Code 0x1414 = some (.jal x0 0x656, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1416 : fetchRel bootMainClosure0Code 0x1416 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1418 : fetchRel bootMainClosure0Code 0x1418 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_141c : fetchRel bootMainClosure0Code 0x141C = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_141e : fetchRel bootMainClosure0Code 0x141E = some (.load .lbu (8 : Fin 32) a0 0x11, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1422 : fetchRel bootMainClosure0Code 0x1422 = some (.jal x0 0x648, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1424 : fetchRel bootMainClosure0Code 0x1424 = some (.aluImm .add (8 : Fin 32) x0 0x5, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1426 : fetchRel bootMainClosure0Code 0x1426 = some (.jal x0 0x644, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1428 : fetchRel bootMainClosure0Code 0x1428 = some (.load .lbu (8 : Fin 32) sp 0x248, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_142c : fetchRel bootMainClosure0Code 0x142C = some (.jal x0 0x63E, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_142e : fetchRel bootMainClosure0Code 0x142E = some (.load .lbu (8 : Fin 32) (19 : Fin 32) 0x11, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1432 : fetchRel bootMainClosure0Code 0x1432 = some (.jal x0 0x638, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1434 : fetchRel bootMainClosure0Code 0x1434 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1436 : fetchRel bootMainClosure0Code 0x1436 = some (.aluImm .add a0 a0 0xFFFFFED0, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_143a : fetchRel bootMainClosure0Code 0x143A = some (.alu .add (18 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_143e : fetchRel bootMainClosure0Code 0x143E = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1440 : fetchRel bootMainClosure0Code 0x1440 = some (.aluImm .add a0 a0 0xFFFFFFD0, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1444 : fetchRel bootMainClosure0Code 0x1444 = some (.alu .add (20 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1448 : fetchRel bootMainClosure0Code 0x1448 = some (.aluImm .add a0 sp 0x200, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_144a : fetchRel bootMainClosure0Code 0x144A = some (.store .sw a0 (18 : Fin 32) 0x44, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_144e : fetchRel bootMainClosure0Code 0x144E = some (.store .sw a0 (20 : Fin 32) 0x48, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1452 : fetchRel bootMainClosure0Code 0x1452 = some (.store .sw a0 x0 0x4C, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1456 : fetchRel bootMainClosure0Code 0x1456 = some (.aluImm .add a0 sp 0x244, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1458 : fetchRel bootMainClosure0Code 0x1458 = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_145c : fetchRel bootMainClosure0Code 0x145C = some (.jalr ra ra 0xFFFFF932, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1460 : fetchRel bootMainClosure0Code 0x1460 = some (.branch .beq a1 x0 0x70, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1462 : fetchRel bootMainClosure0Code 0x1462 = some (.aluImm .add a0 a0 0x1, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1464 : fetchRel bootMainClosure0Code 0x1464 = some (.alu .sltu a2 x0 a0, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1468 : fetchRel bootMainClosure0Code 0x1468 = some (.load .lw (19 : Fin 32) a1 0x0, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_146c : fetchRel bootMainClosure0Code 0x146C = some (.load .lw (22 : Fin 32) a1 0x4, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1470 : fetchRel bootMainClosure0Code 0x1470 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1472 : fetchRel bootMainClosure0Code 0x1472 = some (.alu .or a0 a0 a2, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1474 : fetchRel bootMainClosure0Code 0x1474 = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1476 : fetchRel bootMainClosure0Code 0x1476 = some (.aluImm .add a1 a1 0x310, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_147a : fetchRel bootMainClosure0Code 0x147A = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_147c : fetchRel bootMainClosure0Code 0x147C = some (.store .sw a1 (18 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1480 : fetchRel bootMainClosure0Code 0x1480 = some (.store .sw a1 (20 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1484 : fetchRel bootMainClosure0Code 0x1484 = some (.store .sw a1 x0 0x18, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1488 : fetchRel bootMainClosure0Code 0x1488 = some (.aluImm .add a1 a0 0xFFFFFFFF, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_148c : fetchRel bootMainClosure0Code 0x148C = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_148e : fetchRel bootMainClosure0Code 0x148E = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1492 : fetchRel bootMainClosure0Code 0x1492 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1494 : fetchRel bootMainClosure0Code 0x1494 = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1498 : fetchRel bootMainClosure0Code 0x1498 = some (.jalr ra ra 0xFFFFF91C, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_149c : fetchRel bootMainClosure0Code 0x149C = some (.branch .beq a0 x0 0xFFFFFFBA, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_149e : fetchRel bootMainClosure0Code 0x149E = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14a0 : fetchRel bootMainClosure0Code 0x14A0 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14a4 : fetchRel bootMainClosure0Code 0x14A4 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14a6 : fetchRel bootMainClosure0Code 0x14A6 = some (.load .lw a2 a0 0x10, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14a8 : fetchRel bootMainClosure0Code 0x14A8 = some (.load .lw (8 : Fin 32) a0 0x14, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14aa : fetchRel bootMainClosure0Code 0x14AA = some (.branch .beq a2 (8 : Fin 32) 0xFFFFFFAC, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14ae : fetchRel bootMainClosure0Code 0x14AE = some (.load .lw a0 a2 0x0, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14b0 : fetchRel bootMainClosure0Code 0x14B0 = some (.branch .beq a0 x0 0xFFFFFFA6, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14b2 : fetchRel bootMainClosure0Code 0x14B2 = some (.load .lw a1 a2 0x4, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14b4 : fetchRel bootMainClosure0Code 0x14B4 = some (.aluImm .add (9 : Fin 32) a2 0x20, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14b8 : fetchRel bootMainClosure0Code 0x14B8 = some (.alu .add a2 x0 (19 : Fin 32), 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14ba : fetchRel bootMainClosure0Code 0x14BA = some (.alu .add a3 x0 (22 : Fin 32), 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14bc : fetchRel bootMainClosure0Code 0x14BC = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14c0 : fetchRel bootMainClosure0Code 0x14C0 = some (.jalr ra ra 0x26A, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14c4 : fetchRel bootMainClosure0Code 0x14C4 = some (.alu .add a2 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14c6 : fetchRel bootMainClosure0Code 0x14C6 = some (.branch .beq a0 x0 0xFFFFFFE4, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14c8 : fetchRel bootMainClosure0Code 0x14C8 = some (.jal x0 0x2AC, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14ca : fetchRel bootMainClosure0Code 0x14CA = some (.load .lbu (8 : Fin 32) (19 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14ce : fetchRel bootMainClosure0Code 0x14CE = some (.jal x0 0x59C, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14d0 : fetchRel bootMainClosure0Code 0x14D0 = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14d2 : fetchRel bootMainClosure0Code 0x14D2 = some (.aluImm .add a0 a0 0xFFFFFED0, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14d6 : fetchRel bootMainClosure0Code 0x14D6 = some (.alu .add (18 : Fin 32) sp a0, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14da : fetchRel bootMainClosure0Code 0x14DA = some (.aluImm .add a0 sp 0x200, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14dc : fetchRel bootMainClosure0Code 0x14DC = some (.store .sw a0 (18 : Fin 32) 0x44, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14e0 : fetchRel bootMainClosure0Code 0x14E0 = some (.store .sw a0 (20 : Fin 32) 0x48, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14e4 : fetchRel bootMainClosure0Code 0x14E4 = some (.store .sw a0 x0 0x4C, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14e8 : fetchRel bootMainClosure0Code 0x14E8 = some (.aluImm .add a0 sp 0x244, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14ea : fetchRel bootMainClosure0Code 0x14EA = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14ee : fetchRel bootMainClosure0Code 0x14EE = some (.jalr ra ra 0xFFFFF8A0, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14f2 : fetchRel bootMainClosure0Code 0x14F2 = some (.branch .beq a1 x0 0x64, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14f4 : fetchRel bootMainClosure0Code 0x14F4 = some (.aluImm .add a0 a0 0x1, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14f6 : fetchRel bootMainClosure0Code 0x14F6 = some (.alu .sltu a2 x0 a0, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14fa : fetchRel bootMainClosure0Code 0x14FA = some (.load .lw (19 : Fin 32) a1 0x18, 4) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_14fe : fetchRel bootMainClosure0Code 0x14FE = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c20_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1500 : fetchRel bootMainClosure0Code 0x1500 = some (.alu .or a0 a0 a2, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1502 : fetchRel bootMainClosure0Code 0x1502 = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1504 : fetchRel bootMainClosure0Code 0x1504 = some (.aluImm .add a1 a1 0x310, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1508 : fetchRel bootMainClosure0Code 0x1508 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_150a : fetchRel bootMainClosure0Code 0x150A = some (.store .sw a1 (18 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_150e : fetchRel bootMainClosure0Code 0x150E = some (.store .sw a1 (20 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1512 : fetchRel bootMainClosure0Code 0x1512 = some (.store .sw a1 x0 0x18, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1516 : fetchRel bootMainClosure0Code 0x1516 = some (.aluImm .add a1 a0 0xFFFFFFFF, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_151a : fetchRel bootMainClosure0Code 0x151A = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_151c : fetchRel bootMainClosure0Code 0x151C = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1520 : fetchRel bootMainClosure0Code 0x1520 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1522 : fetchRel bootMainClosure0Code 0x1522 = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1526 : fetchRel bootMainClosure0Code 0x1526 = some (.jalr ra ra 0xFFFFF88E, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_152a : fetchRel bootMainClosure0Code 0x152A = some (.branch .beq a0 x0 0xFFFFFFBE, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_152c : fetchRel bootMainClosure0Code 0x152C = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_152e : fetchRel bootMainClosure0Code 0x152E = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1532 : fetchRel bootMainClosure0Code 0x1532 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1534 : fetchRel bootMainClosure0Code 0x1534 = some (.load .lw a1 a0 0x10, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1536 : fetchRel bootMainClosure0Code 0x1536 = some (.load .lw (9 : Fin 32) a0 0x14, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1538 : fetchRel bootMainClosure0Code 0x1538 = some (.branch .beq a1 (9 : Fin 32) 0xFFFFFFB0, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_153c : fetchRel bootMainClosure0Code 0x153C = some (.load .lw a0 a1 0x0, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_153e : fetchRel bootMainClosure0Code 0x153E = some (.branch .beq a0 x0 0xFFFFFFAA, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1540 : fetchRel bootMainClosure0Code 0x1540 = some (.load .lw a0 a1 0x18, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1542 : fetchRel bootMainClosure0Code 0x1542 = some (.aluImm .add (8 : Fin 32) a1 0x20, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1546 : fetchRel bootMainClosure0Code 0x1546 = some (.alu .add a1 x0 (19 : Fin 32), 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1548 : fetchRel bootMainClosure0Code 0x1548 = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_154c : fetchRel bootMainClosure0Code 0x154C = some (.jalr ra ra 0xFA, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1550 : fetchRel bootMainClosure0Code 0x1550 = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1552 : fetchRel bootMainClosure0Code 0x1552 = some (.branch .beq a0 x0 0xFFFFFFE6, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1554 : fetchRel bootMainClosure0Code 0x1554 = some (.jal x0 0x220, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1556 : fetchRel bootMainClosure0Code 0x1556 = some (.aluImm .add (18 : Fin 32) sp 0x350, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_155a : fetchRel bootMainClosure0Code 0x155A = some (.aluImm .add (20 : Fin 32) sp 0x550, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_155e : fetchRel bootMainClosure0Code 0x155E = some (.aluImm .add a0 sp 0x200, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1560 : fetchRel bootMainClosure0Code 0x1560 = some (.store .sw a0 (18 : Fin 32) 0x44, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1564 : fetchRel bootMainClosure0Code 0x1564 = some (.store .sw a0 (20 : Fin 32) 0x48, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1568 : fetchRel bootMainClosure0Code 0x1568 = some (.store .sw a0 x0 0x4C, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_156c : fetchRel bootMainClosure0Code 0x156C = some (.aluImm .add a0 sp 0x244, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_156e : fetchRel bootMainClosure0Code 0x156E = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1572 : fetchRel bootMainClosure0Code 0x1572 = some (.jalr ra ra 0xFFFFF81C, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1576 : fetchRel bootMainClosure0Code 0x1576 = some (.branch .beq a1 x0 0x6A, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1578 : fetchRel bootMainClosure0Code 0x1578 = some (.aluImm .add a0 a0 0x1, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_157a : fetchRel bootMainClosure0Code 0x157A = some (.alu .sltu a2 x0 a0, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_157e : fetchRel bootMainClosure0Code 0x157E = some (.load .lw (19 : Fin 32) a1 0x0, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1582 : fetchRel bootMainClosure0Code 0x1582 = some (.load .lw (22 : Fin 32) a1 0x4, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1586 : fetchRel bootMainClosure0Code 0x1586 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1588 : fetchRel bootMainClosure0Code 0x1588 = some (.alu .or a0 a0 a2, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_158a : fetchRel bootMainClosure0Code 0x158A = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_158c : fetchRel bootMainClosure0Code 0x158C = some (.aluImm .add a1 a1 0x310, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1590 : fetchRel bootMainClosure0Code 0x1590 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1592 : fetchRel bootMainClosure0Code 0x1592 = some (.store .sw a1 (18 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1596 : fetchRel bootMainClosure0Code 0x1596 = some (.store .sw a1 (20 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_159a : fetchRel bootMainClosure0Code 0x159A = some (.store .sw a1 x0 0x18, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_159e : fetchRel bootMainClosure0Code 0x159E = some (.aluImm .add a1 a0 0xFFFFFFFF, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15a2 : fetchRel bootMainClosure0Code 0x15A2 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15a4 : fetchRel bootMainClosure0Code 0x15A4 = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15a8 : fetchRel bootMainClosure0Code 0x15A8 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15aa : fetchRel bootMainClosure0Code 0x15AA = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15ae : fetchRel bootMainClosure0Code 0x15AE = some (.jalr ra ra 0xFFFFF806, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15b2 : fetchRel bootMainClosure0Code 0x15B2 = some (.branch .beq a0 x0 0xFFFFFFBA, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15b4 : fetchRel bootMainClosure0Code 0x15B4 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15b6 : fetchRel bootMainClosure0Code 0x15B6 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15ba : fetchRel bootMainClosure0Code 0x15BA = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15bc : fetchRel bootMainClosure0Code 0x15BC = some (.load .lw a2 a0 0x10, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15be : fetchRel bootMainClosure0Code 0x15BE = some (.load .lw (8 : Fin 32) a0 0x14, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15c0 : fetchRel bootMainClosure0Code 0x15C0 = some (.branch .beq a2 (8 : Fin 32) 0xFFFFFFAC, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15c4 : fetchRel bootMainClosure0Code 0x15C4 = some (.load .lw a0 a2 0x0, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15c6 : fetchRel bootMainClosure0Code 0x15C6 = some (.branch .beq a0 x0 0xFFFFFFA6, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15c8 : fetchRel bootMainClosure0Code 0x15C8 = some (.load .lw a1 a2 0x4, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15ca : fetchRel bootMainClosure0Code 0x15CA = some (.aluImm .add (9 : Fin 32) a2 0x20, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15ce : fetchRel bootMainClosure0Code 0x15CE = some (.alu .add a2 x0 (19 : Fin 32), 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15d0 : fetchRel bootMainClosure0Code 0x15D0 = some (.alu .add a3 x0 (22 : Fin 32), 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15d2 : fetchRel bootMainClosure0Code 0x15D2 = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15d6 : fetchRel bootMainClosure0Code 0x15D6 = some (.jalr ra ra 0x154, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15da : fetchRel bootMainClosure0Code 0x15DA = some (.alu .add a2 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15dc : fetchRel bootMainClosure0Code 0x15DC = some (.branch .beq a0 x0 0xFFFFFFE4, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15de : fetchRel bootMainClosure0Code 0x15DE = some (.jal x0 0x196, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15e0 : fetchRel bootMainClosure0Code 0x15E0 = some (.aluImm .add (18 : Fin 32) sp 0x350, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15e4 : fetchRel bootMainClosure0Code 0x15E4 = some (.aluImm .add a0 sp 0x200, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15e6 : fetchRel bootMainClosure0Code 0x15E6 = some (.store .sw a0 (18 : Fin 32) 0x44, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15ea : fetchRel bootMainClosure0Code 0x15EA = some (.store .sw a0 (20 : Fin 32) 0x48, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15ee : fetchRel bootMainClosure0Code 0x15EE = some (.store .sw a0 x0 0x4C, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15f2 : fetchRel bootMainClosure0Code 0x15F2 = some (.aluImm .add a0 sp 0x244, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15f4 : fetchRel bootMainClosure0Code 0x15F4 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15f8 : fetchRel bootMainClosure0Code 0x15F8 = some (.jalr ra ra 0x796, 4) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15fc : fetchRel bootMainClosure0Code 0x15FC = some (.branch .beq a1 x0 0x64, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_15fe : fetchRel bootMainClosure0Code 0x15FE = some (.aluImm .add a0 a0 0x1, 2) :=
  (fetchRel_chunk ac_c21_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1600 : fetchRel bootMainClosure0Code 0x1600 = some (.alu .sltu a2 x0 a0, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1604 : fetchRel bootMainClosure0Code 0x1604 = some (.load .lw (19 : Fin 32) a1 0x18, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1608 : fetchRel bootMainClosure0Code 0x1608 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_160a : fetchRel bootMainClosure0Code 0x160A = some (.alu .or a0 a0 a2, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_160c : fetchRel bootMainClosure0Code 0x160C = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_160e : fetchRel bootMainClosure0Code 0x160E = some (.aluImm .add a1 a1 0x310, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1612 : fetchRel bootMainClosure0Code 0x1612 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1614 : fetchRel bootMainClosure0Code 0x1614 = some (.store .sw a1 (18 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1618 : fetchRel bootMainClosure0Code 0x1618 = some (.store .sw a1 (20 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_161c : fetchRel bootMainClosure0Code 0x161C = some (.store .sw a1 x0 0x18, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1620 : fetchRel bootMainClosure0Code 0x1620 = some (.aluImm .add a1 a0 0xFFFFFFFF, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1624 : fetchRel bootMainClosure0Code 0x1624 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1626 : fetchRel bootMainClosure0Code 0x1626 = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_162a : fetchRel bootMainClosure0Code 0x162A = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_162c : fetchRel bootMainClosure0Code 0x162C = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1630 : fetchRel bootMainClosure0Code 0x1630 = some (.jalr ra ra 0x784, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1634 : fetchRel bootMainClosure0Code 0x1634 = some (.branch .beq a0 x0 0xFFFFFFBE, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1636 : fetchRel bootMainClosure0Code 0x1636 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1638 : fetchRel bootMainClosure0Code 0x1638 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_163c : fetchRel bootMainClosure0Code 0x163C = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_163e : fetchRel bootMainClosure0Code 0x163E = some (.load .lw a1 a0 0x10, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1640 : fetchRel bootMainClosure0Code 0x1640 = some (.load .lw (9 : Fin 32) a0 0x14, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1642 : fetchRel bootMainClosure0Code 0x1642 = some (.branch .beq a1 (9 : Fin 32) 0xFFFFFFB0, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1646 : fetchRel bootMainClosure0Code 0x1646 = some (.load .lw a0 a1 0x0, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1648 : fetchRel bootMainClosure0Code 0x1648 = some (.branch .beq a0 x0 0xFFFFFFAA, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_164a : fetchRel bootMainClosure0Code 0x164A = some (.load .lw a0 a1 0x18, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_164c : fetchRel bootMainClosure0Code 0x164C = some (.aluImm .add (8 : Fin 32) a1 0x20, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1650 : fetchRel bootMainClosure0Code 0x1650 = some (.alu .add a1 x0 (19 : Fin 32), 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1652 : fetchRel bootMainClosure0Code 0x1652 = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1656 : fetchRel bootMainClosure0Code 0x1656 = some (.jalr ra ra 0xA, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_165a : fetchRel bootMainClosure0Code 0x165A = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_165c : fetchRel bootMainClosure0Code 0x165C = some (.branch .beq a0 x0 0xFFFFFFE6, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_165e : fetchRel bootMainClosure0Code 0x165E = some (.jal x0 0x116, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1660 : fetchRel bootMainClosure0Code 0x1660 = some (.aluImm .add (18 : Fin 32) sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1664 : fetchRel bootMainClosure0Code 0x1664 = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0x91, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1668 : fetchRel bootMainClosure0Code 0x1668 = some (.aluImm .add (20 : Fin 32) sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_166c : fetchRel bootMainClosure0Code 0x166C = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x191, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1670 : fetchRel bootMainClosure0Code 0x1670 = some (.aluImm .add a0 sp 0x200, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1672 : fetchRel bootMainClosure0Code 0x1672 = some (.store .sw a0 (18 : Fin 32) 0x44, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1676 : fetchRel bootMainClosure0Code 0x1676 = some (.store .sw a0 (20 : Fin 32) 0x48, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_167a : fetchRel bootMainClosure0Code 0x167A = some (.store .sw a0 x0 0x4C, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_167e : fetchRel bootMainClosure0Code 0x167E = some (.aluImm .add a0 sp 0x244, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1680 : fetchRel bootMainClosure0Code 0x1680 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1684 : fetchRel bootMainClosure0Code 0x1684 = some (.jalr ra ra 0x70A, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1688 : fetchRel bootMainClosure0Code 0x1688 = some (.branch .beq a1 x0 0x6A, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_168a : fetchRel bootMainClosure0Code 0x168A = some (.aluImm .add a0 a0 0x1, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_168c : fetchRel bootMainClosure0Code 0x168C = some (.alu .sltu a2 x0 a0, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1690 : fetchRel bootMainClosure0Code 0x1690 = some (.load .lw (19 : Fin 32) a1 0x0, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1694 : fetchRel bootMainClosure0Code 0x1694 = some (.load .lw (22 : Fin 32) a1 0x4, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1698 : fetchRel bootMainClosure0Code 0x1698 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_169a : fetchRel bootMainClosure0Code 0x169A = some (.alu .or a0 a0 a2, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_169c : fetchRel bootMainClosure0Code 0x169C = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_169e : fetchRel bootMainClosure0Code 0x169E = some (.aluImm .add a1 a1 0x310, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16a2 : fetchRel bootMainClosure0Code 0x16A2 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16a4 : fetchRel bootMainClosure0Code 0x16A4 = some (.store .sw a1 (18 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16a8 : fetchRel bootMainClosure0Code 0x16A8 = some (.store .sw a1 (20 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16ac : fetchRel bootMainClosure0Code 0x16AC = some (.store .sw a1 x0 0x18, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16b0 : fetchRel bootMainClosure0Code 0x16B0 = some (.aluImm .add a1 a0 0xFFFFFFFF, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16b4 : fetchRel bootMainClosure0Code 0x16B4 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16b6 : fetchRel bootMainClosure0Code 0x16B6 = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16ba : fetchRel bootMainClosure0Code 0x16BA = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16bc : fetchRel bootMainClosure0Code 0x16BC = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16c0 : fetchRel bootMainClosure0Code 0x16C0 = some (.jalr ra ra 0x6F4, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16c4 : fetchRel bootMainClosure0Code 0x16C4 = some (.branch .beq a0 x0 0xFFFFFFBA, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16c6 : fetchRel bootMainClosure0Code 0x16C6 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16c8 : fetchRel bootMainClosure0Code 0x16C8 = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16cc : fetchRel bootMainClosure0Code 0x16CC = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16ce : fetchRel bootMainClosure0Code 0x16CE = some (.load .lw a2 a0 0x10, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16d0 : fetchRel bootMainClosure0Code 0x16D0 = some (.load .lw (8 : Fin 32) a0 0x14, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16d2 : fetchRel bootMainClosure0Code 0x16D2 = some (.branch .beq a2 (8 : Fin 32) 0xFFFFFFAC, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16d6 : fetchRel bootMainClosure0Code 0x16D6 = some (.load .lw a0 a2 0x0, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16d8 : fetchRel bootMainClosure0Code 0x16D8 = some (.branch .beq a0 x0 0xFFFFFFA6, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16da : fetchRel bootMainClosure0Code 0x16DA = some (.load .lw a1 a2 0x4, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16dc : fetchRel bootMainClosure0Code 0x16DC = some (.aluImm .add (9 : Fin 32) a2 0x20, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16e0 : fetchRel bootMainClosure0Code 0x16E0 = some (.alu .add a2 x0 (19 : Fin 32), 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16e2 : fetchRel bootMainClosure0Code 0x16E2 = some (.alu .add a3 x0 (22 : Fin 32), 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16e4 : fetchRel bootMainClosure0Code 0x16E4 = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16e8 : fetchRel bootMainClosure0Code 0x16E8 = some (.jalr ra ra 0x42, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16ec : fetchRel bootMainClosure0Code 0x16EC = some (.alu .add a2 x0 (9 : Fin 32), 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16ee : fetchRel bootMainClosure0Code 0x16EE = some (.branch .beq a0 x0 0xFFFFFFE4, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16f0 : fetchRel bootMainClosure0Code 0x16F0 = some (.jal x0 0x84, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16f2 : fetchRel bootMainClosure0Code 0x16F2 = some (.aluImm .add (18 : Fin 32) sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16f6 : fetchRel bootMainClosure0Code 0x16F6 = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0x91, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16fa : fetchRel bootMainClosure0Code 0x16FA = some (.aluImm .add a0 sp 0x200, 2) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_16fc : fetchRel bootMainClosure0Code 0x16FC = some (.store .sw a0 (18 : Fin 32) 0x44, 4) :=
  (fetchRel_chunk ac_c22_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1700 : fetchRel bootMainClosure0Code 0x1700 = some (.store .sw a0 (20 : Fin 32) 0x48, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1704 : fetchRel bootMainClosure0Code 0x1704 = some (.store .sw a0 x0 0x4C, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1708 : fetchRel bootMainClosure0Code 0x1708 = some (.aluImm .add a0 sp 0x244, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_170a : fetchRel bootMainClosure0Code 0x170A = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_170e : fetchRel bootMainClosure0Code 0x170E = some (.jalr ra ra 0x680, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1712 : fetchRel bootMainClosure0Code 0x1712 = some (.branch .beq a1 x0 0x66, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1714 : fetchRel bootMainClosure0Code 0x1714 = some (.aluImm .add a0 a0 0x1, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1716 : fetchRel bootMainClosure0Code 0x1716 = some (.alu .sltu a2 x0 a0, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_171a : fetchRel bootMainClosure0Code 0x171A = some (.load .lw (19 : Fin 32) a1 0x18, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_171e : fetchRel bootMainClosure0Code 0x171E = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1720 : fetchRel bootMainClosure0Code 0x1720 = some (.alu .or a0 a0 a2, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1722 : fetchRel bootMainClosure0Code 0x1722 = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1724 : fetchRel bootMainClosure0Code 0x1724 = some (.aluImm .add a1 a1 0x310, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1728 : fetchRel bootMainClosure0Code 0x1728 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_172a : fetchRel bootMainClosure0Code 0x172A = some (.store .sw a1 (18 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_172e : fetchRel bootMainClosure0Code 0x172E = some (.store .sw a1 (20 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1732 : fetchRel bootMainClosure0Code 0x1732 = some (.store .sw a1 x0 0x18, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1736 : fetchRel bootMainClosure0Code 0x1736 = some (.aluImm .add a1 a0 0xFFFFFFFF, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_173a : fetchRel bootMainClosure0Code 0x173A = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_173c : fetchRel bootMainClosure0Code 0x173C = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1740 : fetchRel bootMainClosure0Code 0x1740 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1742 : fetchRel bootMainClosure0Code 0x1742 = some (.auipc ra 0xA000, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1746 : fetchRel bootMainClosure0Code 0x1746 = some (.jalr ra ra 0x66E, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_174a : fetchRel bootMainClosure0Code 0x174A = some (.branch .beq a0 x0 0xFFFFFFBE, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_174c : fetchRel bootMainClosure0Code 0x174C = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_174e : fetchRel bootMainClosure0Code 0x174E = some (.aluImm .add a0 a0 0x310, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1752 : fetchRel bootMainClosure0Code 0x1752 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1754 : fetchRel bootMainClosure0Code 0x1754 = some (.load .lw a1 a0 0x10, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1756 : fetchRel bootMainClosure0Code 0x1756 = some (.load .lw (9 : Fin 32) a0 0x14, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1758 : fetchRel bootMainClosure0Code 0x1758 = some (.branch .beq a1 (9 : Fin 32) 0xFFFFFFB0, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_175c : fetchRel bootMainClosure0Code 0x175C = some (.load .lw a0 a1 0x0, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_175e : fetchRel bootMainClosure0Code 0x175E = some (.branch .beq a0 x0 0xFFFFFFAA, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1760 : fetchRel bootMainClosure0Code 0x1760 = some (.load .lw a0 a1 0x18, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1762 : fetchRel bootMainClosure0Code 0x1762 = some (.aluImm .add (8 : Fin 32) a1 0x20, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1766 : fetchRel bootMainClosure0Code 0x1766 = some (.alu .add a1 x0 (19 : Fin 32), 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1768 : fetchRel bootMainClosure0Code 0x1768 = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_176c : fetchRel bootMainClosure0Code 0x176C = some (.jalr ra ra 0xFFFFFEDA, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1770 : fetchRel bootMainClosure0Code 0x1770 = some (.alu .add a1 x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1772 : fetchRel bootMainClosure0Code 0x1772 = some (.branch .beq a0 x0 0xFFFFFFE6, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1774 : fetchRel bootMainClosure0Code 0x1774 = some (.aluImm .add (8 : Fin 32) x0 0xD, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1776 : fetchRel bootMainClosure0Code 0x1776 = some (.jal x0 0x2F4, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1778 : fetchRel bootMainClosure0Code 0x1778 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_177a : fetchRel bootMainClosure0Code 0x177A = some (.aluImm .add a0 a0 0x343, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_177e : fetchRel bootMainClosure0Code 0x177E = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1780 : fetchRel bootMainClosure0Code 0x1780 = some (.lui a1 0x2000, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1782 : fetchRel bootMainClosure0Code 0x1782 = some (.aluImm .add a1 a1 0xFFFFFED0, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1786 : fetchRel bootMainClosure0Code 0x1786 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1788 : fetchRel bootMainClosure0Code 0x1788 = some (.aluImm .add a2 x0 0x100, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_178c : fetchRel bootMainClosure0Code 0x178C = some (.auipc ra 0x15000, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1790 : fetchRel bootMainClosure0Code 0x1790 = some (.jalr ra ra 0xFFFFFF8A, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1794 : fetchRel bootMainClosure0Code 0x1794 = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1796 : fetchRel bootMainClosure0Code 0x1796 = some (.aluImm .add a0 a0 0x443, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_179a : fetchRel bootMainClosure0Code 0x179A = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_179c : fetchRel bootMainClosure0Code 0x179C = some (.aluImm .add a1 sp 0x350, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_179e : fetchRel bootMainClosure0Code 0x179E = some (.aluImm .add a2 x0 0x200, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17a2 : fetchRel bootMainClosure0Code 0x17A2 = some (.auipc ra 0x15000, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17a6 : fetchRel bootMainClosure0Code 0x17A6 = some (.jalr ra ra 0xFFFFFF74, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17aa : fetchRel bootMainClosure0Code 0x17AA = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17ac : fetchRel bootMainClosure0Code 0x17AC = some (.aluImm .add a0 a0 0x643, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17b0 : fetchRel bootMainClosure0Code 0x17B0 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17b2 : fetchRel bootMainClosure0Code 0x17B2 = some (.aluImm .add a1 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17b6 : fetchRel bootMainClosure0Code 0x17B6 = some (.aluImm .add a1 a1 0x91, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17ba : fetchRel bootMainClosure0Code 0x17BA = some (.aluImm .add a2 x0 0x100, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17be : fetchRel bootMainClosure0Code 0x17BE = some (.auipc ra 0x15000, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17c2 : fetchRel bootMainClosure0Code 0x17C2 = some (.jalr ra ra 0xFFFFFF58, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17c6 : fetchRel bootMainClosure0Code 0x17C6 = some (.lui a1 0x3FCC4000, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17ca : fetchRel bootMainClosure0Code 0x17CA = some (.aluImm .add a1 a1 0x51, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17ce : fetchRel bootMainClosure0Code 0x17CE = some (.lui a0 0x1000, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17d0 : fetchRel bootMainClosure0Code 0x17D0 = some (.aluImm .add a0 a0 0x320, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17d4 : fetchRel bootMainClosure0Code 0x17D4 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17d6 : fetchRel bootMainClosure0Code 0x17D6 = some (.aluImm .add a2 x0 0x23, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17da : fetchRel bootMainClosure0Code 0x17DA = some (.auipc ra 0x15000, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17de : fetchRel bootMainClosure0Code 0x17DE = some (.jalr ra ra 0xFFFFFF3C, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17e2 : fetchRel bootMainClosure0Code 0x17E2 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17e6 : fetchRel bootMainClosure0Code 0x17E6 = some (.aluImm .add a0 a0 0x5D1, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17ea : fetchRel bootMainClosure0Code 0x17EA = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17ec : fetchRel bootMainClosure0Code 0x17EC = some (.aluImm .add a1 a1 0x320, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17f0 : fetchRel bootMainClosure0Code 0x17F0 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17f2 : fetchRel bootMainClosure0Code 0x17F2 = some (.aluImm .add a2 x0 0x423, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17f6 : fetchRel bootMainClosure0Code 0x17F6 = some (.auipc ra 0x15000, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17fa : fetchRel bootMainClosure0Code 0x17FA = some (.jalr ra ra 0xFFFFFF20, 4) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_17fe : fetchRel bootMainClosure0Code 0x17FE = some (.lui a0 0x2000, 2) :=
  (fetchRel_chunk ac_c23_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1800 : fetchRel bootMainClosure0Code 0x1800 = some (.aluImm .add a0 a0 0xFFFFF875, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1804 : fetchRel bootMainClosure0Code 0x1804 = some (.alu .add a0 a0 sp, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1806 : fetchRel bootMainClosure0Code 0x1806 = some (.aluImm .add a1 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_180a : fetchRel bootMainClosure0Code 0x180A = some (.aluImm .add a1 a1 0x5D1, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_180e : fetchRel bootMainClosure0Code 0x180E = some (.aluImm .add a2 x0 0x423, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1812 : fetchRel bootMainClosure0Code 0x1812 = some (.auipc ra 0x15000, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1816 : fetchRel bootMainClosure0Code 0x1816 = some (.jalr ra ra 0xFFFFFF04, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_181a : fetchRel bootMainClosure0Code 0x181A = some (.lui a0 0x3FCC6000, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_181e : fetchRel bootMainClosure0Code 0x181E = some (.aluImm .add a0 a0 0x621, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1822 : fetchRel bootMainClosure0Code 0x1822 = some (.aluImm .add a1 x0 0x2B, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1826 : fetchRel bootMainClosure0Code 0x1826 = some (.lui a2 0x1000, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1828 : fetchRel bootMainClosure0Code 0x1828 = some (.aluImm .add a2 a2 0x310, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_182c : fetchRel bootMainClosure0Code 0x182C = some (.alu .add a2 a2 sp, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_182e : fetchRel bootMainClosure0Code 0x182E = some (.store .sw a2 a0 0x560, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1832 : fetchRel bootMainClosure0Code 0x1832 = some (.store .sb a2 a1 0x564, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1836 : fetchRel bootMainClosure0Code 0x1836 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_183a : fetchRel bootMainClosure0Code 0x183A = some (.aluImm .add a0 a0 0x91, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_183e : fetchRel bootMainClosure0Code 0x183E = some (.load .lw a1 sp 0x34, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1840 : fetchRel bootMainClosure0Code 0x1840 = some (.store .sw a0 a1 0x540, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1844 : fetchRel bootMainClosure0Code 0x1844 = some (.load .lw a1 sp 0x38, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1846 : fetchRel bootMainClosure0Code 0x1846 = some (.store .sw a0 a1 0x544, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_184a : fetchRel bootMainClosure0Code 0x184A = some (.store .sw a0 x0 0x548, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_184e : fetchRel bootMainClosure0Code 0x184E = some (.lui a1 0x4E423000, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1852 : fetchRel bootMainClosure0Code 0x1852 = some (.aluImm .add a1 a1 0x343, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1856 : fetchRel bootMainClosure0Code 0x1856 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_185a : fetchRel bootMainClosure0Code 0x185A = some (.aluImm .add a0 a0 0x5D1, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_185e : fetchRel bootMainClosure0Code 0x185E = some (.auipc ra 0x9000, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1862 : fetchRel bootMainClosure0Code 0x1862 = some (.jalr ra ra 0xFFFFF8CA, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1866 : fetchRel bootMainClosure0Code 0x1866 = some (.alu .add (8 : Fin 32) x0 a0, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1868 : fetchRel bootMainClosure0Code 0x1868 = some (.aluImm .and a0 a0 0xFF, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_186c : fetchRel bootMainClosure0Code 0x186C = some (.aluImm .add a0 a0 0xFFFFFF01, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1870 : fetchRel bootMainClosure0Code 0x1870 = some (.branch .bne a0 x0 0x1FA, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1874 : fetchRel bootMainClosure0Code 0x1874 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1878 : fetchRel bootMainClosure0Code 0x1878 = some (.aluImm .add a0 a0 0x5D1, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_187c : fetchRel bootMainClosure0Code 0x187C = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1880 : fetchRel bootMainClosure0Code 0x1880 = some (.jalr ra ra 0x758, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1884 : fetchRel bootMainClosure0Code 0x1884 = some (.alu .add (8 : Fin 32) x0 a0, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1886 : fetchRel bootMainClosure0Code 0x1886 = some (.aluImm .and a0 a0 0xFF, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_188a : fetchRel bootMainClosure0Code 0x188A = some (.aluImm .add a0 a0 0xFFFFFF01, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_188e : fetchRel bootMainClosure0Code 0x188E = some (.branch .bne a0 x0 0x1DC, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1892 : fetchRel bootMainClosure0Code 0x1892 = some (.aluImm .add a0 sp 0x350, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1894 : fetchRel bootMainClosure0Code 0x1894 = some (.aluImm .add a1 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1898 : fetchRel bootMainClosure0Code 0x1898 = some (.aluImm .add a1 a1 0x5D1, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_189c : fetchRel bootMainClosure0Code 0x189C = some (.aluImm .add a2 x0 0x1, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_189e : fetchRel bootMainClosure0Code 0x189E = some (.lui a3 0x1000, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18a0 : fetchRel bootMainClosure0Code 0x18A0 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18a4 : fetchRel bootMainClosure0Code 0x18A4 = some (.jalr ra ra 0xFFFFF842, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18a8 : fetchRel bootMainClosure0Code 0x18A8 = some (.load .lw (26 : Fin 32) sp 0x350, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18ac : fetchRel bootMainClosure0Code 0x18AC = some (.branch .beq (26 : Fin 32) x0 0x1BA, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18b0 : fetchRel bootMainClosure0Code 0x18B0 = some (.load .lw (23 : Fin 32) sp 0x354, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18b4 : fetchRel bootMainClosure0Code 0x18B4 = some (.aluImm .add a0 sp 0x350, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18b6 : fetchRel bootMainClosure0Code 0x18B6 = some (.aluImm .add a1 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18ba : fetchRel bootMainClosure0Code 0x18BA = some (.aluImm .add a1 a1 0x5D1, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18be : fetchRel bootMainClosure0Code 0x18BE = some (.aluImm .add a2 x0 0x8, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18c0 : fetchRel bootMainClosure0Code 0x18C0 = some (.aluImm .add a3 x0 0x48, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18c4 : fetchRel bootMainClosure0Code 0x18C4 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18c8 : fetchRel bootMainClosure0Code 0x18C8 = some (.jalr ra ra 0xFFFFF81E, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18cc : fetchRel bootMainClosure0Code 0x18CC = some (.load .lw a0 sp 0x350, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18d0 : fetchRel bootMainClosure0Code 0x18D0 = some (.store .sw sp a0 0x38, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18d2 : fetchRel bootMainClosure0Code 0x18D2 = some (.branch .beq a0 x0 0x194, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18d6 : fetchRel bootMainClosure0Code 0x18D6 = some (.load .lw a0 sp 0x354, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18da : fetchRel bootMainClosure0Code 0x18DA = some (.store .sw sp a0 0x34, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18dc : fetchRel bootMainClosure0Code 0x18DC = some (.aluImm .add a0 sp 0x350, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18de : fetchRel bootMainClosure0Code 0x18DE = some (.aluImm .add a1 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18e2 : fetchRel bootMainClosure0Code 0x18E2 = some (.aluImm .add a1 a1 0x5D1, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18e6 : fetchRel bootMainClosure0Code 0x18E6 = some (.aluImm .add a2 x0 0x8, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18e8 : fetchRel bootMainClosure0Code 0x18E8 = some (.aluImm .add a3 x0 0x8, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18ea : fetchRel bootMainClosure0Code 0x18EA = some (.aluImm .add (18 : Fin 32) x0 0x8, 2) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18ec : fetchRel bootMainClosure0Code 0x18EC = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18f0 : fetchRel bootMainClosure0Code 0x18F0 = some (.jalr ra ra 0x7F6, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18f4 : fetchRel bootMainClosure0Code 0x18F4 = some (.load .lw a0 sp 0x350, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18f8 : fetchRel bootMainClosure0Code 0x18F8 = some (.branch .beq a0 x0 0x16E, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_18fc : fetchRel bootMainClosure0Code 0x18FC = some (.load .lw a1 sp 0x354, 4) :=
  (fetchRel_chunk ac_c24_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1900 : fetchRel bootMainClosure0Code 0x1900 = some (.aluImm .add (8 : Fin 32) x0 0x5, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1902 : fetchRel bootMainClosure0Code 0x1902 = some (.branch .bne a1 (18 : Fin 32) 0x168, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1906 : fetchRel bootMainClosure0Code 0x1906 = some (.load .lbu a1 a0 0x4, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_190a : fetchRel bootMainClosure0Code 0x190A = some (.store .sw sp a1 0x30, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_190c : fetchRel bootMainClosure0Code 0x190C = some (.load .lbu (19 : Fin 32) a0 0x5, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1910 : fetchRel bootMainClosure0Code 0x1910 = some (.load .lbu a1 a0 0x6, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1914 : fetchRel bootMainClosure0Code 0x1914 = some (.store .sw sp a1 0x18, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1916 : fetchRel bootMainClosure0Code 0x1916 = some (.load .lbu a1 a0 0x7, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_191a : fetchRel bootMainClosure0Code 0x191A = some (.store .sw sp a1 0x14, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_191c : fetchRel bootMainClosure0Code 0x191C = some (.load .lbu (9 : Fin 32) a0 0x0, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1920 : fetchRel bootMainClosure0Code 0x1920 = some (.load .lbu a1 a0 0x1, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1924 : fetchRel bootMainClosure0Code 0x1924 = some (.store .sw sp a1 0x1C, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1926 : fetchRel bootMainClosure0Code 0x1926 = some (.load .lbu a1 a0 0x2, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_192a : fetchRel bootMainClosure0Code 0x192A = some (.store .sw sp a1 0x2C, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_192c : fetchRel bootMainClosure0Code 0x192C = some (.load .lbu a0 a0 0x3, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1930 : fetchRel bootMainClosure0Code 0x1930 = some (.store .sw sp a0 0x28, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1932 : fetchRel bootMainClosure0Code 0x1932 = some (.aluImm .add a3 x0 0x1, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1934 : fetchRel bootMainClosure0Code 0x1934 = some (.aluImm .sll a3 a3 0xB, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1936 : fetchRel bootMainClosure0Code 0x1936 = some (.aluImm .add a0 sp 0x350, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1938 : fetchRel bootMainClosure0Code 0x1938 = some (.aluImm .add a1 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_193c : fetchRel bootMainClosure0Code 0x193C = some (.aluImm .add a1 a1 0x5D1, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1940 : fetchRel bootMainClosure0Code 0x1940 = some (.aluImm .add a2 x0 0x0, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1942 : fetchRel bootMainClosure0Code 0x1942 = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1946 : fetchRel bootMainClosure0Code 0x1946 = some (.jalr ra ra 0x7A0, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_194a : fetchRel bootMainClosure0Code 0x194A = some (.load .lw (18 : Fin 32) sp 0x350, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_194e : fetchRel bootMainClosure0Code 0x194E = some (.branch .beq (18 : Fin 32) x0 0x118, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1952 : fetchRel bootMainClosure0Code 0x1952 = some (.load .lw (22 : Fin 32) sp 0x354, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1956 : fetchRel bootMainClosure0Code 0x1956 = some (.aluImm .and a0 (22 : Fin 32) 0x1F, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_195a : fetchRel bootMainClosure0Code 0x195A = some (.branch .bne a0 x0 0x110, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_195e : fetchRel bootMainClosure0Code 0x195E = some (.aluImm .add a0 sp 0x350, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1960 : fetchRel bootMainClosure0Code 0x1960 = some (.aluImm .add a1 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1964 : fetchRel bootMainClosure0Code 0x1964 = some (.aluImm .add a1 a1 0x5D1, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1968 : fetchRel bootMainClosure0Code 0x1968 = some (.aluImm .add a2 x0 0x1, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_196a : fetchRel bootMainClosure0Code 0x196A = some (.aluImm .add a3 x0 0x400, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_196e : fetchRel bootMainClosure0Code 0x196E = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1972 : fetchRel bootMainClosure0Code 0x1972 = some (.jalr ra ra 0x774, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1976 : fetchRel bootMainClosure0Code 0x1976 = some (.load .lw (20 : Fin 32) sp 0x350, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_197a : fetchRel bootMainClosure0Code 0x197A = some (.branch .beq (20 : Fin 32) x0 0xEC, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_197e : fetchRel bootMainClosure0Code 0x197E = some (.load .lw (24 : Fin 32) sp 0x354, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1982 : fetchRel bootMainClosure0Code 0x1982 = some (.aluImm .add a0 sp 0x350, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1984 : fetchRel bootMainClosure0Code 0x1984 = some (.aluImm .add a1 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1988 : fetchRel bootMainClosure0Code 0x1988 = some (.aluImm .add a1 a1 0x5D1, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_198c : fetchRel bootMainClosure0Code 0x198C = some (.aluImm .add a2 x0 0x1, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_198e : fetchRel bootMainClosure0Code 0x198E = some (.lui a3 0x2000, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1990 : fetchRel bootMainClosure0Code 0x1990 = some (.aluImm .add (8 : Fin 32) x0 0x1, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1992 : fetchRel bootMainClosure0Code 0x1992 = some (.auipc ra 0xB000, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1996 : fetchRel bootMainClosure0Code 0x1996 = some (.jalr ra ra 0x750, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_199a : fetchRel bootMainClosure0Code 0x199A = some (.load .lw a0 sp 0x350, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_199e : fetchRel bootMainClosure0Code 0x199E = some (.branch .beq a0 x0 0xC8, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19a0 : fetchRel bootMainClosure0Code 0x19A0 = some (.aluImm .add a2 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19a4 : fetchRel bootMainClosure0Code 0x19A4 = some (.aluImm .add a2 a2 0x91, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19a8 : fetchRel bootMainClosure0Code 0x19A8 = some (.load .lw a1 a2 0x544, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19ac : fetchRel bootMainClosure0Code 0x19AC = some (.load .lw a2 a2 0x548, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19b0 : fetchRel bootMainClosure0Code 0x19B0 = some (.branch .bne a2 a1 0xBA, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19b4 : fetchRel bootMainClosure0Code 0x19B4 = some (.aluImm .sll (19 : Fin 32) (19 : Fin 32) 0x8, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19b6 : fetchRel bootMainClosure0Code 0x19B6 = some (.load .lw a1 sp 0x18, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19b8 : fetchRel bootMainClosure0Code 0x19B8 = some (.aluImm .sll a1 a1 0x10, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19ba : fetchRel bootMainClosure0Code 0x19BA = some (.load .lw a2 sp 0x14, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19bc : fetchRel bootMainClosure0Code 0x19BC = some (.aluImm .sll a2 a2 0x18, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19be : fetchRel bootMainClosure0Code 0x19BE = some (.load .lw a3 sp 0x30, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19c0 : fetchRel bootMainClosure0Code 0x19C0 = some (.alu .or a3 (19 : Fin 32) a3, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19c4 : fetchRel bootMainClosure0Code 0x19C4 = some (.alu .or a1 a1 a2, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19c6 : fetchRel bootMainClosure0Code 0x19C6 = some (.alu .or a1 a1 a3, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19c8 : fetchRel bootMainClosure0Code 0x19C8 = some (.load .lw a2 sp 0x1C, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19ca : fetchRel bootMainClosure0Code 0x19CA = some (.aluImm .sll a2 a2 0x8, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19cc : fetchRel bootMainClosure0Code 0x19CC = some (.load .lw a3 sp 0x2C, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19ce : fetchRel bootMainClosure0Code 0x19CE = some (.aluImm .sll a3 a3 0x10, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19d0 : fetchRel bootMainClosure0Code 0x19D0 = some (.load .lw a4 sp 0x28, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19d2 : fetchRel bootMainClosure0Code 0x19D2 = some (.aluImm .sll a4 a4 0x18, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19d4 : fetchRel bootMainClosure0Code 0x19D4 = some (.alu .or a2 a2 (9 : Fin 32), 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19d6 : fetchRel bootMainClosure0Code 0x19D6 = some (.alu .or a3 a3 a4, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19d8 : fetchRel bootMainClosure0Code 0x19D8 = some (.alu .or a2 a2 a3, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19da : fetchRel bootMainClosure0Code 0x19DA = some (.load .lw a3 sp 0x354, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19de : fetchRel bootMainClosure0Code 0x19DE = some (.aluImm .srl a4 (23 : Fin 32) 0x8, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19e2 : fetchRel bootMainClosure0Code 0x19E2 = some (.aluImm .srl a5 (23 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19e6 : fetchRel bootMainClosure0Code 0x19E6 = some (.aluImm .srl (9 : Fin 32) (23 : Fin 32) 0x18, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19ea : fetchRel bootMainClosure0Code 0x19EA = some (.lui a6 0x1000, 2) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19ec : fetchRel bootMainClosure0Code 0x19EC = some (.aluImm .add a6 a6 0x310, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19f0 : fetchRel bootMainClosure0Code 0x19F0 = some (.alu .add (8 : Fin 32) sp a6, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19f4 : fetchRel bootMainClosure0Code 0x19F4 = some (.store .sw (8 : Fin 32) (26 : Fin 32) 0x10, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19f8 : fetchRel bootMainClosure0Code 0x19F8 = some (.store .sb (8 : Fin 32) (23 : Fin 32) 0x14, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_19fc : fetchRel bootMainClosure0Code 0x19FC = some (.store .sb (8 : Fin 32) a4 0x15, 4) :=
  (fetchRel_chunk ac_c25_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a00 : fetchRel bootMainClosure0Code 0x1A00 = some (.store .sb (8 : Fin 32) a5 0x16, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a04 : fetchRel bootMainClosure0Code 0x1A04 = some (.store .sb (8 : Fin 32) (9 : Fin 32) 0x17, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a08 : fetchRel bootMainClosure0Code 0x1A08 = some (.load .lw a4 sp 0x38, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a0a : fetchRel bootMainClosure0Code 0x1A0A = some (.store .sw (8 : Fin 32) a4 0x18, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a0c : fetchRel bootMainClosure0Code 0x1A0C = some (.load .lw a4 sp 0x34, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a0e : fetchRel bootMainClosure0Code 0x1A0E = some (.store .sw (8 : Fin 32) a4 0x1C, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a10 : fetchRel bootMainClosure0Code 0x1A10 = some (.store .sw (8 : Fin 32) (18 : Fin 32) 0x20, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a14 : fetchRel bootMainClosure0Code 0x1A14 = some (.store .sw (8 : Fin 32) (22 : Fin 32) 0x24, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a18 : fetchRel bootMainClosure0Code 0x1A18 = some (.store .sw (8 : Fin 32) (20 : Fin 32) 0x28, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a1c : fetchRel bootMainClosure0Code 0x1A1C = some (.store .sw (8 : Fin 32) (24 : Fin 32) 0x2C, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a20 : fetchRel bootMainClosure0Code 0x1A20 = some (.store .sw (8 : Fin 32) a0 0x30, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a22 : fetchRel bootMainClosure0Code 0x1A22 = some (.store .sw (8 : Fin 32) a3 0x34, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a24 : fetchRel bootMainClosure0Code 0x1A24 = some (.store .sw (8 : Fin 32) a2 0x38, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a26 : fetchRel bootMainClosure0Code 0x1A26 = some (.store .sw (8 : Fin 32) a1 0x3C, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a28 : fetchRel bootMainClosure0Code 0x1A28 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a2c : fetchRel bootMainClosure0Code 0x1A2C = some (.aluImm .add a0 a0 0x5D1, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a30 : fetchRel bootMainClosure0Code 0x1A30 = some (.lui a1 0x1000, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a32 : fetchRel bootMainClosure0Code 0x1A32 = some (.aluImm .add a1 a1 0x320, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a36 : fetchRel bootMainClosure0Code 0x1A36 = some (.alu .add a1 a1 sp, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a38 : fetchRel bootMainClosure0Code 0x1A38 = some (.lui a2 0x2000, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a3a : fetchRel bootMainClosure0Code 0x1A3A = some (.aluImm .add a2 a2 0xFFFFF870, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a3e : fetchRel bootMainClosure0Code 0x1A3E = some (.alu .add a2 a2 sp, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a40 : fetchRel bootMainClosure0Code 0x1A40 = some (.aluImm .add a3 sp 0x108, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a42 : fetchRel bootMainClosure0Code 0x1A42 = some (.auipc ra 0xC000, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a46 : fetchRel bootMainClosure0Code 0x1A46 = some (.jalr ra ra 0xFFFFFA1A, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a4a : fetchRel bootMainClosure0Code 0x1A4A = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a4e : fetchRel bootMainClosure0Code 0x1A4E = some (.aluImm .add a0 a0 0x91, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a52 : fetchRel bootMainClosure0Code 0x1A52 = some (.load .lbu a0 a0 0x540, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a56 : fetchRel bootMainClosure0Code 0x1A56 = some (.branch .beq a0 x0 0x1A, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a58 : fetchRel bootMainClosure0Code 0x1A58 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a5c : fetchRel bootMainClosure0Code 0x1A5C = some (.aluImm .add a0 a0 0x91, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a60 : fetchRel bootMainClosure0Code 0x1A60 = some (.load .lbu (8 : Fin 32) a0 0x541, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a64 : fetchRel bootMainClosure0Code 0x1A64 = some (.jal x0 0x6, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a66 : fetchRel bootMainClosure0Code 0x1A66 = some (.load .lbu (8 : Fin 32) sp 0x354, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a6a : fetchRel bootMainClosure0Code 0x1A6A = some (.alu .add (21 : Fin 32) x0 (8 : Fin 32), 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a6c : fetchRel bootMainClosure0Code 0x1A6C = some (.jal x0 0xFFFFED6A, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a70 : fetchRel bootMainClosure0Code 0x1A70 = some (.aluImm .add a0 sp 0x7FF, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a74 : fetchRel bootMainClosure0Code 0x1A74 = some (.aluImm .add a0 a0 0x91, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a78 : fetchRel bootMainClosure0Code 0x1A78 = some (.load .lw (8 : Fin 32) a0 0x54C, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a7c : fetchRel bootMainClosure0Code 0x1A7C = some (.load .lw (18 : Fin 32) a0 0x548, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a80 : fetchRel bootMainClosure0Code 0x1A80 = some (.load .lw a0 sp 0x24, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a82 : fetchRel bootMainClosure0Code 0x1A82 = some (.branch .beq (8 : Fin 32) a0 0xC, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a86 : fetchRel bootMainClosure0Code 0x1A86 = some (.load .lw a0 sp 0x24, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a88 : fetchRel bootMainClosure0Code 0x1A88 = some (.alu .sltu a0 a0 (8 : Fin 32), 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a8c : fetchRel bootMainClosure0Code 0x1A8C = some (.jal x0 0x8, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a8e : fetchRel bootMainClosure0Code 0x1A8E = some (.load .lw a0 sp 0x20, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a90 : fetchRel bootMainClosure0Code 0x1A90 = some (.alu .sltu a0 a0 (18 : Fin 32), 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a94 : fetchRel bootMainClosure0Code 0x1A94 = some (.branch .beq a0 x0 0x8, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a96 : fetchRel bootMainClosure0Code 0x1A96 = some (.aluImm .add (8 : Fin 32) x0 0x25, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a9a : fetchRel bootMainClosure0Code 0x1A9A = some (.jal x0 0xFFFFFFD0, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a9c : fetchRel bootMainClosure0Code 0x1A9C = some (.load .lw (9 : Fin 32) sp 0x40, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1a9e : fetchRel bootMainClosure0Code 0x1A9E = some (.aluImm .add a0 (9 : Fin 32) 0x1, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1aa2 : fetchRel bootMainClosure0Code 0x1AA2 = some (.aluImm .add a1 sp 0x238, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1aa4 : fetchRel bootMainClosure0Code 0x1AA4 = some (.aluImm .add a2 x0 0xB, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1aa6 : fetchRel bootMainClosure0Code 0x1AA6 = some (.auipc ra 0x15000, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1aaa : fetchRel bootMainClosure0Code 0x1AAA = some (.jalr ra ra 0xFFFFFC70, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1aae : fetchRel bootMainClosure0Code 0x1AAE = some (.aluImm .add a0 (9 : Fin 32) 0xD, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ab2 : fetchRel bootMainClosure0Code 0x1AB2 = some (.aluImm .add a1 sp 0x139, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ab6 : fetchRel bootMainClosure0Code 0x1AB6 = some (.aluImm .add a2 x0 0xFF, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1aba : fetchRel bootMainClosure0Code 0x1ABA = some (.auipc ra 0x15000, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1abe : fetchRel bootMainClosure0Code 0x1ABE = some (.jalr ra ra 0xFFFFFC5C, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ac2 : fetchRel bootMainClosure0Code 0x1AC2 = some (.load .lbu a0 sp 0x136, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ac6 : fetchRel bootMainClosure0Code 0x1AC6 = some (.load .lbu a1 sp 0x137, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1aca : fetchRel bootMainClosure0Code 0x1ACA = some (.load .lbu a2 sp 0x138, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ace : fetchRel bootMainClosure0Code 0x1ACE = some (.store .sb (9 : Fin 32) (27 : Fin 32) 0x10C, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ad2 : fetchRel bootMainClosure0Code 0x1AD2 = some (.store .sb (9 : Fin 32) a0 0x10D, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ad6 : fetchRel bootMainClosure0Code 0x1AD6 = some (.store .sb (9 : Fin 32) a1 0x10E, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ada : fetchRel bootMainClosure0Code 0x1ADA = some (.store .sb (9 : Fin 32) a2 0x10F, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ade : fetchRel bootMainClosure0Code 0x1ADE = some (.store .sw (9 : Fin 32) (18 : Fin 32) 0x110, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ae2 : fetchRel bootMainClosure0Code 0x1AE2 = some (.store .sw (9 : Fin 32) (8 : Fin 32) 0x114, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1ae6 : fetchRel bootMainClosure0Code 0x1AE6 = some (.store .sb (9 : Fin 32) (27 : Fin 32) 0x118, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1aea : fetchRel bootMainClosure0Code 0x1AEA = some (.load .lw a0 sp 0x44, 2) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1aec : fetchRel bootMainClosure0Code 0x1AEC = some (.store .sw (9 : Fin 32) a0 0x120, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1af0 : fetchRel bootMainClosure0Code 0x1AF0 = some (.store .sb (9 : Fin 32) (21 : Fin 32) 0x0, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1af4 : fetchRel bootMainClosure0Code 0x1AF4 = some (.store .sb (9 : Fin 32) (25 : Fin 32) 0xC, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1af8 : fetchRel bootMainClosure0Code 0x1AF8 = some (.store .sb (9 : Fin 32) (27 : Fin 32) 0x128, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)
theorem ac_at_1afc : fetchRel bootMainClosure0Code 0x1AFC = some (.jal x0 0xFFFFE688, 4) :=
  (fetchRel_chunk ac_c26_ok (by decide) (.inl (by decide))).trans (by decide)

end C3.RV32.Ac
