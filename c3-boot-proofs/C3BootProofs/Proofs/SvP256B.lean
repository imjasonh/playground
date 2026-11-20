import C3BootProofs.Proofs.SvP256A
import C3BootProofs.Proofs.SvEcD
import C3BootProofs.Proofs.SvEcT0a
import C3BootProofs.Proofs.SvEcT0c
import C3BootProofs.Proofs.SvEcT0b
import C3BootProofs.Proofs.SvEcT1a
import C3BootProofs.Proofs.SvEcT1c
import C3BootProofs.Proofs.SvEcT1b
import C3BootProofs.Proofs.SvEcW2
import C3BootProofs.Proofs.SvEcW3
import C3BootProofs.Proofs.SvIvE

/-!
# `sigstore::verify`: the P-256 check from the inverse to the main loop

From 0x1556, where the inversion of `s` ends, to the main loop at 0x18F8: `sv_ive` normalizes the inverse,
`sv_ecd` computes `u₁` and `u₂`, the `sv_ect*` stages build the tables of odd multiples, and `sv_ecw` and
`sv_ecw3` write the wNAF digits, which leaves what `ml2_main` takes.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

theorem ptF_of {M : Word → BitVec 8} {B : Word} {c x y z : Nat}
    (hx : accV M (B + 0x21A0 + BitVec.ofNat 32 c) 8 = x) (hy : accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x20)) 8 = y)
    (hz : accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x40)) 8 = z) : ptF M B c = (x, y, z) := by
  unfold ptF; rw [hx, hy, hz]

set_option maxHeartbeats 64000000 in
/-- **The P-256 check from the inverse to the main loop**: from 0x1556 to 0x18F8, or a panic when the
inversion's `f` isn't 1. -/
theorem sv_p256_tab {B r3 r4 out bp x26 : Word} {qx qy qz rv sv zv N : Nat} {W v : Nat → Word} {n0 : Machine}
    {st : Iv} (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (s : St n0.mem SV n0 0x1556 (reg n0))
    (I : IvInv B n0 v r3 r4 out bp (BitVec.ofNat 32 0x1) x26 qx qy qz rv sv zv N W st)
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (IC0 : SvIvCode M0) (EC0 : SvEcCode M0) (UC0 : SvUpCode M0) (UE0 : CodeIn M0 (BitVec.ofNat 32 uint8EqAddress) uint8EqCode) (N80 : CodeIn M0 (BitVec.ofNat 32 norm8Address) norm8Code) (RS : SvRoSep B) (PM0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode) (WM0 : CodeIn M0 (BitVec.ofNat 32 wideMulAddress) wideMulCode) (PT0 : SvPtCode M0) (WN0 : SvWnCode M0) (ME : MlEnv M0)
    (hG : Pt2Lt (accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x40) 8))
    (hQ : Pt2Lt (qx, qy, qz)) :
    (¬ ((((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8) = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8)) ∧ True) ∧ Panics n0) ∨
    (((((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8) = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8)) ∧ True) ∧ ∃ m', Steps n0 m' ∧ (∀ x, SvR B x → m'.mem x = M0 x) ∧ St m'.mem SV m' 0x18F8 (reg m') ∧
      MlEnv m'.mem ∧ reg m' (3 : Fin 32) = r3 ∧ reg m' (4 : Fin 32) = r4 ∧
      reg m' sp = B + 0x21A0 ∧
      reg m' (9 : Fin 32) = BitVec.ofNat 32 (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length ∧
      reg m' a0 = BitVec.ofNat 32 (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length ∧
      reg m' (18 : Fin 32) = out ∧
      reg m' (19 : Fin 32) = bp ∧
      reg m' (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
      reg m' (21 : Fin 32) = (BitVec.ofNat 32 0x2) ∧
      reg m' (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 ∧
      reg m' (24 : Fin 32) = (BitVec.ofNat 32 0x2) ∧
      reg m' (25 : Fin 32) = BitVec.ofNat 32 0x2 ∧
      reg m' (26 : Fin 32) = x26 ∧
      reg m' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (W 0x24) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = (W 0x28) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (W 0x2C) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = (W 0x30) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = (W 0x34) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (W 0x38) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = (W 0x3C) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = (W 0x40) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (W 0x44) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = (W 0x48) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (W 0x4C) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = (W 0x50) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = (W 0x54) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = (W 0x58) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = (memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C)) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = (BitVec.ofNat 32 0x332E3755) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = (W 0x64) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = (W 0x68) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = (W 0x6C) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (BitVec.ofNat 32 0x11FF43B1) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (BitVec.ofNat 32 st.rem) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (W 0x7C) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (W 0x80) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (W 0x84) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (W 0x88) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (W 0x8C) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = (W 0x90) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = (W 0x94) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = (W 0x98) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = (W 0x9C) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = (W 0xA0) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = (W 0xA4) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = (W 0xA8) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = (W 0xAC) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = (W 0xB0) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = (W 0xB4) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = (W 0xB8) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = (W 0xBC) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = (W 0xC0) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = (W 0xC4) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = (W 0xC8) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = (W 0xCC) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = (W 0xD0) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = (W 0xD4) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = (W 0xD8) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (W 0xDC) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = (W 0xE0) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = (W 0xE4) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = (W 0xE8) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = (W 0xEC) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = (W 0xF0) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = (W 0xF4) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = (W 0xF8) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = (W 0xFC) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = (W 0x100) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = (W 0x104) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = (W 0x108) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = (W 0x10C) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = (W 0x110) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = (W 0x114) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = (W 0x118) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = (W 0x11C) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = (W 0x120) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = (W 0x124) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = (W 0x128) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = (W 0x12C) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = (W 0x130) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB28) = BitVec.ofNat 32 (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1128) = BitVec.ofNat 32 (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = (psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8))))) ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = (psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8))))) ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = (psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8))))) ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = (psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8))))) ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = (psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8))))) ∧
      leN (memBytes m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = (psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8))))) ∧
      GM2 B m'.mem (tbl2 (accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x40) 8)) (tbl2 (qx, qy, qz))
        (wnafBytes (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0) 0x101)
        (wnafBytes (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0) 0x101)) := by
  rcases @sv_ive _ _ _ 0 _ 0 _ _ _ _ [] [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F I.E I.V hret hO s M0 fM I.sp I.g18 I.g19 rfl I.g24 rfl I.g26 I.g27 (I.ww 0x24 (by decide)) (I.ww 0x28 (by decide)) (I.ww 0x2C (by decide)) (I.ww 0x30 (by decide)) (I.ww 0x34 (by decide)) (I.ww 0x38 (by decide)) (I.ww 0x3C (by decide)) (I.ww 0x40 (by decide)) (I.ww 0x44 (by decide)) (I.ww 0x48 (by decide)) (I.ww 0x4C (by decide)) (I.ww 0x50 (by decide)) (I.ww 0x54 (by decide)) (I.ww 0x58 (by decide)) rfl I.w60 (I.ww 0x64 (by decide)) (I.ww 0x68 (by decide)) (I.ww 0x6C (by decide)) I.w70 I.wr (I.ww 0x7C (by decide)) (I.ww 0x80 (by decide)) (I.ww 0x84 (by decide)) (I.ww 0x88 (by decide)) (I.ww 0x8C (by decide)) (I.ww 0x90 (by decide)) (I.ww 0x94 (by decide)) (I.ww 0x98 (by decide)) (I.ww 0x9C (by decide)) (I.ww 0xA0 (by decide)) (I.ww 0xA4 (by decide)) (I.ww 0xA8 (by decide)) (I.ww 0xAC (by decide)) (I.ww 0xB0 (by decide)) (I.ww 0xB4 (by decide)) (I.ww 0xB8 (by decide)) (I.ww 0xBC (by decide)) (I.ww 0xC0 (by decide)) (I.ww 0xC4 (by decide)) (I.ww 0xC8 (by decide)) (I.ww 0xCC (by decide)) (I.ww 0xD0 (by decide)) (I.ww 0xD4 (by decide)) (I.ww 0xD8 (by decide)) (I.ww 0xDC (by decide)) (I.ww 0xE0 (by decide)) (I.ww 0xE4 (by decide)) (I.ww 0xE8 (by decide)) (I.ww 0xEC (by decide)) (I.ww 0xF0 (by decide)) (I.ww 0xF4 (by decide)) (I.ww 0xF8 (by decide)) (I.ww 0xFC (by decide)) (I.ww 0x100 (by decide)) (I.ww 0x104 (by decide)) (I.ww 0x108 (by decide)) (I.ww 0x10C (by decide)) (I.ww 0x110 (by decide)) (I.ww 0x114 (by decide)) (I.ww 0x118 (by decide)) (I.ww 0x11C (by decide)) (I.ww 0x120 (by decide)) (I.ww 0x124 (by decide)) (I.ww 0x128 (by decide)) (I.ww 0x12C (by decide)) (I.ww 0x130 (by decide)) I.a240 I.a260 I.a280 I.a2a0 I.a2c0 I.a2e0 rfl rfl rfl rfl rfl rfl rfl rfl IC0 EC0 I.g21 UC0 UE0 N80 I.lf I.ld with ⟨hn, e⟩ | ⟨x1_0, n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_18, r1_19, r1_20, r1_21, r1_23, r1_24, r1_25, r1_26, r1_27, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_3c, w1_40, w1_44, w1_48, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, b1_440, b1_a20, b1_1040, b1_13a0, b1_14a0, a1_240, a1_260, a1_280, a1_2a0, a1_2c0, a1_2e0, a1_420, a1_1020, a1_1380, a1_1480⟩
  · exact .inl ⟨hn, e⟩
  rcases @sv_ecd _ _ _ 0 _ _ _ _ _ _ [] [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F E1 V1 hret hO s1 M0 fR1 r1_2 r1_18 r1_19 r1_21 r1_23 r1_24 r1_25 r1_26 r1_27 w1_24 w1_28 w1_2c w1_30 w1_34 w1_38 w1_3c w1_40 w1_44 w1_48 w1_4c w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_78 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_98 w1_9c w1_a0 w1_a4 w1_a8 w1_ac w1_b0 w1_b4 w1_b8 w1_bc w1_c0 w1_c4 w1_c8 w1_cc w1_d0 w1_d4 w1_d8 w1_dc w1_e0 w1_e4 w1_e8 w1_ec w1_f0 w1_f4 w1_f8 w1_fc w1_100 w1_104 w1_108 w1_10c w1_110 w1_114 w1_118 w1_11c w1_120 w1_124 w1_128 w1_12c w1_130 a1_240 a1_260 a1_280 a1_2a0 a1_2c0 a1_2e0 a1_1020 a1_1380 a1_1480 b1_440 b1_1040 b1_13a0 b1_14a0 IC0 EC0 r1_20 a1_420 RS PM0 WM0 with ⟨hn, -⟩ | ⟨n2, c2, s2, E2, V2, fR2, r2_2, r2_3, r2_4, r2_18, r2_19, r2_20, r2_21, r2_22, r2_23, r2_24, r2_25, r2_26, r2_27, w2_24, w2_28, w2_2c, w2_30, w2_34, w2_38, w2_3c, w2_40, w2_44, w2_48, w2_4c, w2_50, w2_54, w2_58, w2_5c, w2_60, w2_64, w2_68, w2_6c, w2_70, w2_78, w2_7c, w2_80, w2_84, w2_88, w2_8c, w2_90, w2_94, w2_98, w2_9c, w2_a0, w2_a4, w2_a8, w2_ac, w2_b0, w2_b4, w2_b8, w2_bc, w2_c0, w2_c4, w2_c8, w2_cc, w2_d0, w2_d4, w2_d8, w2_dc, w2_e0, w2_e4, w2_e8, w2_ec, w2_f0, w2_f4, w2_f8, w2_fc, w2_100, w2_104, w2_108, w2_10c, w2_110, w2_114, w2_118, w2_11c, w2_120, w2_124, w2_128, w2_12c, w2_130, b2_1040, b2_13a0, q2_320, q2_420, q2_1480, a2_240, a2_260, a2_280, a2_2a0, a2_2c0, a2_2e0, a2_300, a2_320, a2_340, a2_360, a2_380, a2_3a0, a2_3c0, a2_3e0, a2_400, a2_420, a2_440, a2_460, a2_480, a2_a20, a2_a40, a2_a60, a2_a80, a2_1020, a2_1380, a2_1480, a2_14a0, a2_14c0, a2_14e0, a2_1500, a2_1520, a2_1540, a2_1560⟩
  · exact absurd trivial hn
  rcases @sv_ect0a _ _ _ 0 _ 0 0 0 0 _ [] [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F E2 V2 hret hO s2 M0 fR2 r2_2 r2_18 r2_19 r2_26 r2_27 w2_24 w2_28 w2_2c w2_30 w2_34 w2_38 w2_3c w2_40 w2_44 w2_48 w2_4c w2_50 w2_54 w2_58 w2_5c w2_60 w2_64 w2_68 w2_6c w2_70 w2_78 w2_7c w2_80 w2_84 w2_88 w2_8c w2_90 w2_94 w2_98 w2_9c w2_a0 w2_a4 w2_a8 w2_ac w2_b0 w2_b4 w2_b8 w2_bc w2_c0 w2_c4 w2_c8 w2_cc w2_d0 w2_d4 w2_d8 w2_dc w2_e0 w2_e4 w2_e8 w2_ec w2_f0 w2_f4 w2_f8 w2_fc w2_100 w2_104 w2_108 w2_10c w2_110 w2_114 w2_118 w2_11c w2_120 w2_124 w2_128 w2_12c w2_130 a2_240 a2_260 a2_280 a2_2a0 a2_2c0 a2_2e0 a2_420 a2_1020 a2_1380 rfl b2_1040 b2_13a0 rfl IC0 EC0 r2_20 r2_21 r2_22 r2_23 r2_24 r2_25 (ptF_of a2_320 a2_340 a2_360) (ptF_of a2_3a0 a2_3c0 a2_3e0) a2_380 a2_400 (ptF_of a2_1480 a2_14a0 a2_14c0) (ptF_of a2_1500 a2_1520 a2_1540) a2_14e0 a2_1560 hG hQ RS PT0 with ⟨hn, -⟩ | ⟨n3, c3, s3, E3, V3, fR3, r3_2, r3_3, r3_4, r3_8, r3_9, r3_18, r3_19, r3_20, r3_21, r3_22, r3_23, r3_24, r3_25, r3_26, r3_27, w3_24, w3_28, w3_2c, w3_30, w3_34, w3_38, w3_3c, w3_40, w3_44, w3_48, w3_4c, w3_50, w3_54, w3_58, w3_5c, w3_60, w3_64, w3_68, w3_6c, w3_70, w3_78, w3_7c, w3_80, w3_84, w3_88, w3_8c, w3_90, w3_94, w3_98, w3_9c, w3_a0, w3_a4, w3_a8, w3_ac, w3_b0, w3_b4, w3_b8, w3_bc, w3_c0, w3_c4, w3_c8, w3_cc, w3_d0, w3_d4, w3_d8, w3_dc, w3_e0, w3_e4, w3_e8, w3_ec, w3_f0, w3_f4, w3_f8, w3_fc, w3_100, w3_104, w3_108, w3_10c, w3_110, w3_114, w3_118, w3_11c, w3_120, w3_124, w3_128, w3_12c, w3_130, b3_13a0, b3_14a0, q3_420, q3_480, q3_4e0, q3_540, q3_5a0, q3_600, q3_660, q3_6c0, q3_1020, q3_1080, q3_10e0, q3_1140, q3_11a0, q3_1200, q3_1260, q3_12c0, a3_240, a3_260, a3_280, a3_2a0, a3_2c0, a3_2e0, a3_380, a3_400, a3_13e0, a3_14e0, a3_1560, p3_320, p3_3a0, p3_1380, p3_1480, p3_1500⟩
  · exact absurd trivial hn
  rcases @sv_ect0c _ _ _ 0 _ 0 0 0 0 _ [] [] 0 _ 0 0 _ _ _ _ _ _ _ _ _ _ 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F E3 V3 hret hO s3 M0 fR3 r3_2 r3_8 r3_9 r3_18 r3_19 r3_20 r3_21 r3_22 r3_23 r3_24 r3_25 r3_26 r3_27 w3_24 w3_28 w3_2c w3_30 w3_34 w3_38 w3_3c w3_40 w3_44 w3_48 w3_4c w3_50 w3_54 w3_58 w3_5c w3_60 w3_64 w3_68 w3_6c w3_70 w3_78 w3_7c w3_80 w3_84 w3_88 w3_8c w3_90 w3_94 w3_98 w3_9c w3_a0 w3_a4 w3_a8 w3_ac w3_b0 w3_b4 w3_b8 w3_bc w3_c0 w3_c4 w3_c8 w3_cc w3_d0 w3_d4 w3_d8 w3_dc w3_e0 w3_e4 w3_e8 w3_ec w3_f0 w3_f4 w3_f8 w3_fc w3_100 w3_104 w3_108 w3_10c w3_110 w3_114 w3_118 w3_11c w3_120 w3_124 w3_128 w3_12c w3_130 b3_13a0 b3_14a0 q3_420 q3_480 q3_4e0 q3_540 q3_5a0 q3_600 q3_660 q3_6c0 q3_1020 q3_1080 q3_10e0 q3_1140 q3_11a0 q3_1200 q3_1260 q3_12c0 a3_240 a3_260 a3_280 a3_2a0 a3_2c0 a3_2e0 a3_380 a3_400 a3_13e0 a3_14e0 a3_1560 p3_320 p3_3a0 p3_1380 p3_1480 p3_1500 IC0 EC0 hG hQ RS PT0 with ⟨hn, -⟩ | ⟨n4, c4, s4, E4, V4, fR4, r4_2, r4_3, r4_4, r4_8, r4_9, r4_18, r4_19, r4_20, r4_21, r4_22, r4_23, r4_24, r4_25, r4_26, r4_27, w4_24, w4_28, w4_2c, w4_30, w4_34, w4_38, w4_3c, w4_40, w4_44, w4_48, w4_4c, w4_50, w4_54, w4_58, w4_5c, w4_60, w4_64, w4_68, w4_6c, w4_70, w4_78, w4_7c, w4_80, w4_84, w4_88, w4_8c, w4_90, w4_94, w4_98, w4_9c, w4_a0, w4_a4, w4_a8, w4_ac, w4_b0, w4_b4, w4_b8, w4_bc, w4_c0, w4_c4, w4_c8, w4_cc, w4_d0, w4_d4, w4_d8, w4_dc, w4_e0, w4_e4, w4_e8, w4_ec, w4_f0, w4_f4, w4_f8, w4_fc, w4_100, w4_104, w4_108, w4_10c, w4_110, w4_114, w4_118, w4_11c, w4_120, w4_124, w4_128, w4_12c, w4_130, b4_1040, b4_13a0, b4_14a0, q4_480, q4_4e0, q4_540, q4_5a0, q4_600, q4_660, q4_6c0, q4_11a0, q4_1200, q4_1260, q4_12c0, a4_240, a4_260, a4_280, a4_2a0, a4_2c0, a4_2e0, a4_380, a4_400, a4_13e0, a4_14e0, a4_1560, p4_320, p4_3a0, p4_420, p4_1020, p4_1080, p4_10e0, p4_1140, p4_1320, p4_1380, p4_1480, p4_1500⟩
  · exact absurd trivial hn
  rcases @sv_ect0b _ _ _ 0 _ 0 0 0 0 _ [] [] 0 _ 0 0 _ _ _ _ _ _ _ _ _ _ 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F E4 V4 hret hO s4 M0 fR4 r4_2 r4_8 r4_9 r4_18 r4_19 r4_20 r4_21 r4_22 r4_23 r4_24 r4_25 r4_26 r4_27 w4_24 w4_28 w4_2c w4_30 w4_34 w4_38 w4_3c w4_40 w4_44 w4_48 w4_4c w4_50 w4_54 w4_58 w4_5c w4_60 w4_64 w4_68 w4_6c w4_70 w4_78 w4_7c w4_80 w4_84 w4_88 w4_8c w4_90 w4_94 w4_98 w4_9c w4_a0 w4_a4 w4_a8 w4_ac w4_b0 w4_b4 w4_b8 w4_bc w4_c0 w4_c4 w4_c8 w4_cc w4_d0 w4_d4 w4_d8 w4_dc w4_e0 w4_e4 w4_e8 w4_ec w4_f0 w4_f4 w4_f8 w4_fc w4_100 w4_104 w4_108 w4_10c w4_110 w4_114 w4_118 w4_11c w4_120 w4_124 w4_128 w4_12c w4_130 b4_1040 b4_13a0 b4_14a0 q4_480 q4_4e0 q4_540 q4_5a0 q4_600 q4_660 q4_6c0 q4_11a0 q4_1200 q4_1260 q4_12c0 a4_240 a4_260 a4_280 a4_2a0 a4_2c0 a4_2e0 a4_380 a4_400 a4_13e0 a4_14e0 a4_1560 p4_320 p4_3a0 p4_420 p4_1020 p4_1080 p4_10e0 p4_1140 p4_1320 p4_1380 p4_1480 p4_1500 IC0 EC0 hG hQ RS PT0 with ⟨hn, -⟩ | ⟨n5, c5, s5, E5, V5, fR5, r5_2, r5_3, r5_4, r5_8, r5_9, r5_18, r5_19, r5_20, r5_21, r5_22, r5_23, r5_24, r5_25, r5_26, r5_27, w5_24, w5_28, w5_2c, w5_30, w5_34, w5_38, w5_3c, w5_40, w5_44, w5_48, w5_4c, w5_50, w5_54, w5_58, w5_5c, w5_60, w5_64, w5_68, w5_6c, w5_70, w5_78, w5_7c, w5_80, w5_84, w5_88, w5_8c, w5_90, w5_94, w5_98, w5_9c, w5_a0, w5_a4, w5_a8, w5_ac, w5_b0, w5_b4, w5_b8, w5_bc, w5_c0, w5_c4, w5_c8, w5_cc, w5_d0, w5_d4, w5_d8, w5_dc, w5_e0, w5_e4, w5_e8, w5_ec, w5_f0, w5_f4, w5_f8, w5_fc, w5_100, w5_104, w5_108, w5_10c, w5_110, w5_114, w5_118, w5_11c, w5_120, w5_124, w5_128, w5_12c, w5_130, b5_440, b5_a40, b5_1040, b5_13a0, b5_14a0, a5_240, a5_260, a5_280, a5_2a0, a5_2c0, a5_2e0, a5_380, a5_400, a5_13e0, a5_14e0, a5_1560, p5_320, p5_3a0, p5_420, p5_480, p5_4e0, p5_540, p5_5a0, p5_600, p5_660, p5_6c0, p5_a20, p5_a80, p5_ae0, p5_b40, p5_ba0, p5_c00, p5_c60, p5_cc0, p5_1020, p5_1080, p5_10e0, p5_1140, p5_11a0, p5_1200, p5_1260, p5_12c0, p5_1320, p5_1380, p5_1480, p5_1500⟩
  · exact absurd trivial hn
  rcases @sv_ect1a _ _ _ 0 _ 0 0 0 0 _ [] [] 0 _ 0 0 _ _ _ _ _ _ _ _ _ _ 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F E5 V5 hret hO s5 M0 fR5 r5_2 r5_8 r5_9 r5_18 r5_19 r5_20 r5_21 r5_22 r5_23 r5_24 r5_25 r5_26 r5_27 w5_24 w5_28 w5_2c w5_30 w5_34 w5_38 w5_3c w5_40 w5_44 w5_48 w5_4c w5_50 w5_54 w5_58 w5_5c w5_60 w5_64 w5_68 w5_6c w5_70 w5_78 w5_7c w5_80 w5_84 w5_88 w5_8c w5_90 w5_94 w5_98 w5_9c w5_a0 w5_a4 w5_a8 w5_ac w5_b0 w5_b4 w5_b8 w5_bc w5_c0 w5_c4 w5_c8 w5_cc w5_d0 w5_d4 w5_d8 w5_dc w5_e0 w5_e4 w5_e8 w5_ec w5_f0 w5_f4 w5_f8 w5_fc w5_100 w5_104 w5_108 w5_10c w5_110 w5_114 w5_118 w5_11c w5_120 w5_124 w5_128 w5_12c w5_130 b5_440 b5_a40 b5_1040 b5_13a0 b5_14a0 a5_240 a5_260 a5_280 a5_2a0 a5_2c0 a5_2e0 a5_380 a5_400 a5_13e0 a5_14e0 a5_1560 p5_320 p5_3a0 p5_420 p5_480 p5_4e0 p5_540 p5_5a0 p5_600 p5_660 p5_6c0 p5_a20 p5_a80 p5_ae0 p5_b40 p5_ba0 p5_c00 p5_c60 p5_cc0 p5_1020 p5_1080 p5_10e0 p5_1140 p5_11a0 p5_1200 p5_1260 p5_12c0 p5_1320 p5_1380 p5_1480 p5_1500 IC0 EC0 hG hQ RS PT0 with ⟨hn, -⟩ | ⟨n6, c6, s6, E6, V6, fR6, r6_2, r6_3, r6_4, r6_8, r6_9, r6_18, r6_19, r6_20, r6_21, r6_22, r6_23, r6_24, r6_25, r6_26, r6_27, w6_24, w6_28, w6_2c, w6_30, w6_34, w6_38, w6_3c, w6_40, w6_44, w6_48, w6_4c, w6_50, w6_54, w6_58, w6_5c, w6_60, w6_64, w6_68, w6_6c, w6_70, w6_78, w6_7c, w6_80, w6_84, w6_88, w6_8c, w6_90, w6_94, w6_98, w6_9c, w6_a0, w6_a4, w6_a8, w6_ac, w6_b0, w6_b4, w6_b8, w6_bc, w6_c0, w6_c4, w6_c8, w6_cc, w6_d0, w6_d4, w6_d8, w6_dc, w6_e0, w6_e4, w6_e8, w6_ec, w6_f0, w6_f4, w6_f8, w6_fc, w6_100, w6_104, w6_108, w6_10c, w6_110, w6_114, w6_118, w6_11c, w6_120, w6_124, w6_128, w6_12c, w6_130, b6_a40, b6_14a0, q6_420, q6_480, q6_4e0, q6_540, q6_5a0, q6_600, q6_660, q6_6c0, q6_1020, q6_1080, q6_10e0, q6_1140, q6_11a0, q6_1200, q6_1260, q6_12c0, a6_240, a6_260, a6_280, a6_2a0, a6_2c0, a6_2e0, a6_380, a6_400, a6_13e0, a6_14e0, a6_1560, p6_320, p6_3a0, p6_a20, p6_a80, p6_ae0, p6_b40, p6_ba0, p6_c00, p6_c60, p6_cc0, p6_1320, p6_1380, p6_1480, p6_1500⟩
  · exact absurd trivial hn
  rcases @sv_ect1c _ _ _ 0 _ 0 0 0 0 _ [] [] 0 _ 0 0 _ _ _ _ _ _ _ _ _ _ 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F E6 V6 hret hO s6 M0 fR6 r6_2 r6_8 r6_9 r6_18 r6_19 r6_20 r6_21 r6_22 r6_23 r6_24 r6_25 r6_26 r6_27 w6_24 w6_28 w6_2c w6_30 w6_34 w6_38 w6_3c w6_40 w6_44 w6_48 w6_4c w6_50 w6_54 w6_58 w6_5c w6_60 w6_64 w6_68 w6_6c w6_70 w6_78 w6_7c w6_80 w6_84 w6_88 w6_8c w6_90 w6_94 w6_98 w6_9c w6_a0 w6_a4 w6_a8 w6_ac w6_b0 w6_b4 w6_b8 w6_bc w6_c0 w6_c4 w6_c8 w6_cc w6_d0 w6_d4 w6_d8 w6_dc w6_e0 w6_e4 w6_e8 w6_ec w6_f0 w6_f4 w6_f8 w6_fc w6_100 w6_104 w6_108 w6_10c w6_110 w6_114 w6_118 w6_11c w6_120 w6_124 w6_128 w6_12c w6_130 b6_a40 b6_14a0 q6_420 q6_480 q6_4e0 q6_540 q6_5a0 q6_600 q6_660 q6_6c0 q6_1020 q6_1080 q6_10e0 q6_1140 q6_11a0 q6_1200 q6_1260 q6_12c0 a6_240 a6_260 a6_280 a6_2a0 a6_2c0 a6_2e0 a6_380 a6_400 a6_13e0 a6_14e0 a6_1560 p6_320 p6_3a0 p6_a20 p6_a80 p6_ae0 p6_b40 p6_ba0 p6_c00 p6_c60 p6_cc0 p6_1320 p6_1380 p6_1480 p6_1500 IC0 EC0 hG hQ RS PT0 with ⟨hn, -⟩ | ⟨n7, c7, s7, E7, V7, fR7, r7_2, r7_3, r7_4, r7_8, r7_9, r7_18, r7_19, r7_20, r7_21, r7_22, r7_23, r7_24, r7_25, r7_26, r7_27, w7_24, w7_28, w7_2c, w7_30, w7_34, w7_38, w7_3c, w7_40, w7_44, w7_48, w7_4c, w7_50, w7_54, w7_58, w7_5c, w7_60, w7_64, w7_68, w7_6c, w7_70, w7_78, w7_7c, w7_80, w7_84, w7_88, w7_8c, w7_90, w7_94, w7_98, w7_9c, w7_a0, w7_a4, w7_a8, w7_ac, w7_b0, w7_b4, w7_b8, w7_bc, w7_c0, w7_c4, w7_c8, w7_cc, w7_d0, w7_d4, w7_d8, w7_dc, w7_e0, w7_e4, w7_e8, w7_ec, w7_f0, w7_f4, w7_f8, w7_fc, w7_100, w7_104, w7_108, w7_10c, w7_110, w7_114, w7_118, w7_11c, w7_120, w7_124, w7_128, w7_12c, w7_130, b7_a40, b7_14a0, q7_480, q7_4e0, q7_540, q7_5a0, q7_600, q7_660, q7_6c0, q7_11a0, q7_1200, q7_1260, q7_12c0, a7_240, a7_260, a7_280, a7_2a0, a7_2c0, a7_2e0, a7_380, a7_400, a7_13e0, a7_14e0, a7_1560, p7_320, p7_3a0, p7_420, p7_a20, p7_a80, p7_ae0, p7_b40, p7_ba0, p7_c00, p7_c60, p7_cc0, p7_1020, p7_1080, p7_10e0, p7_1140, p7_1320, p7_1380, p7_1480, p7_1500⟩
  · exact absurd trivial hn
  rcases @sv_ect1b _ _ _ 0 _ 0 0 0 0 _ [] [] 0 _ 0 0 _ _ _ _ _ _ _ _ _ _ 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F E7 V7 hret hO s7 M0 fR7 r7_2 r7_8 r7_9 r7_18 r7_19 r7_20 r7_21 r7_22 r7_23 r7_24 r7_25 r7_26 r7_27 w7_24 w7_28 w7_2c w7_30 w7_34 w7_38 w7_3c w7_40 w7_44 w7_48 w7_4c w7_50 w7_54 w7_58 w7_5c w7_60 w7_64 w7_68 w7_6c w7_70 w7_78 w7_7c w7_80 w7_84 w7_88 w7_8c w7_90 w7_94 w7_98 w7_9c w7_a0 w7_a4 w7_a8 w7_ac w7_b0 w7_b4 w7_b8 w7_bc w7_c0 w7_c4 w7_c8 w7_cc w7_d0 w7_d4 w7_d8 w7_dc w7_e0 w7_e4 w7_e8 w7_ec w7_f0 w7_f4 w7_f8 w7_fc w7_100 w7_104 w7_108 w7_10c w7_110 w7_114 w7_118 w7_11c w7_120 w7_124 w7_128 w7_12c w7_130 b7_a40 b7_14a0 q7_480 q7_4e0 q7_540 q7_5a0 q7_600 q7_660 q7_6c0 q7_11a0 q7_1200 q7_1260 q7_12c0 a7_240 a7_260 a7_280 a7_2a0 a7_2c0 a7_2e0 a7_380 a7_400 a7_13e0 a7_14e0 a7_1560 p7_320 p7_3a0 p7_420 p7_a20 p7_a80 p7_ae0 p7_b40 p7_ba0 p7_c00 p7_c60 p7_cc0 p7_1020 p7_1080 p7_10e0 p7_1140 p7_1320 p7_1380 p7_1480 p7_1500 IC0 EC0 hG hQ RS PT0 with ⟨hn, -⟩ | ⟨n8, c8, s8, E8, V8, fR8, r8_2, r8_3, r8_4, r8_8, r8_9, r8_18, r8_19, r8_20, r8_21, r8_22, r8_23, r8_24, r8_25, r8_26, r8_27, w8_24, w8_28, w8_2c, w8_30, w8_34, w8_38, w8_3c, w8_40, w8_44, w8_48, w8_4c, w8_50, w8_54, w8_58, w8_5c, w8_60, w8_64, w8_68, w8_6c, w8_70, w8_78, w8_7c, w8_80, w8_84, w8_88, w8_8c, w8_90, w8_94, w8_98, w8_9c, w8_a0, w8_a4, w8_a8, w8_ac, w8_b0, w8_b4, w8_b8, w8_bc, w8_c0, w8_c4, w8_c8, w8_cc, w8_d0, w8_d4, w8_d8, w8_dc, w8_e0, w8_e4, w8_e8, w8_ec, w8_f0, w8_f4, w8_f8, w8_fc, w8_100, w8_104, w8_108, w8_10c, w8_110, w8_114, w8_118, w8_11c, w8_120, w8_124, w8_128, w8_12c, w8_130, b8_a40, b8_14a0, a8_240, a8_260, a8_280, a8_2a0, a8_2c0, a8_2e0, a8_380, a8_400, a8_13e0, a8_14e0, a8_1560, p8_320, p8_3a0, p8_420, p8_480, p8_4e0, p8_540, p8_5a0, p8_600, p8_660, p8_6c0, p8_a20, p8_a80, p8_ae0, p8_b40, p8_ba0, p8_c00, p8_c60, p8_cc0, p8_d20, p8_d80, p8_de0, p8_e40, p8_ea0, p8_f00, p8_f60, p8_fc0, p8_1020, p8_1080, p8_10e0, p8_1140, p8_11a0, p8_1200, p8_1260, p8_12c0, p8_1320, p8_1380, p8_1480, p8_1500⟩
  · exact absurd trivial hn
  rcases @sv_ecw _ _ _ 0 _ _ _ _ _ _ [] [] _ _ _ _ 0 0 0 _ _ _ 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F E8 V8 hret hO s8 M0 fR8 r8_2 r8_18 r8_19 r8_21 r8_23 r8_24 r8_25 r8_26 r8_27 w8_24 w8_28 w8_2c w8_30 w8_34 w8_38 w8_3c w8_40 w8_44 w8_48 w8_4c w8_50 w8_54 w8_58 w8_5c w8_60 w8_64 w8_68 w8_6c w8_70 w8_78 w8_7c w8_80 w8_84 w8_88 w8_8c w8_90 w8_94 w8_98 w8_9c w8_a0 w8_a4 w8_a8 w8_ac w8_b0 w8_b4 w8_b8 w8_bc w8_c0 w8_c4 w8_c8 w8_cc w8_d0 w8_d4 w8_d8 w8_dc w8_e0 w8_e4 w8_e8 w8_ec w8_f0 w8_f4 w8_f8 w8_fc w8_100 w8_104 w8_108 w8_10c w8_110 w8_114 w8_118 w8_11c w8_120 w8_124 w8_128 w8_12c w8_130 a8_2a0 a8_2c0 a8_2e0 IC0 EC0 r8_20 p8_320 p8_3a0 a8_380 a8_400 p8_a20 p8_a80 p8_ae0 p8_b40 p8_ba0 p8_c00 p8_c60 p8_cc0 p8_d20 p8_d80 p8_de0 p8_e40 p8_ea0 p8_f00 p8_f60 p8_fc0 WN0 with ⟨hn, -⟩ | ⟨n9, c9, s9, E9, V9, fR9, r9_2, r9_3, r9_4, r9_8, r9_9, r9_18, r9_19, r9_20, r9_21, r9_22, r9_23, r9_24, r9_25, r9_26, r9_27, w9_24, w9_28, w9_2c, w9_30, w9_34, w9_38, w9_3c, w9_40, w9_44, w9_48, w9_4c, w9_50, w9_54, w9_58, w9_5c, w9_60, w9_64, w9_68, w9_6c, w9_70, w9_78, w9_7c, w9_80, w9_84, w9_88, w9_8c, w9_90, w9_94, w9_98, w9_9c, w9_a0, w9_a4, w9_a8, w9_ac, w9_b0, w9_b4, w9_b8, w9_bc, w9_c0, w9_c4, w9_c8, w9_cc, w9_d0, w9_d4, w9_d8, w9_dc, w9_e0, w9_e4, w9_e8, w9_ec, w9_f0, w9_f4, w9_f8, w9_fc, w9_100, w9_104, w9_108, w9_10c, w9_110, w9_114, w9_118, w9_11c, w9_120, w9_124, w9_128, w9_12c, w9_130, w9_a20, w9_1020, w9_1480, a9_2a0, a9_2c0, a9_2e0, a9_380, a9_400, a9_13e0, a9_1460, a9_1588, p9_320, p9_3a0, p9_420, p9_480, p9_4e0, p9_540, p9_5a0, p9_600, p9_660, p9_6c0, p9_720, p9_780, p9_7e0, p9_840, p9_8a0, p9_900, p9_960, p9_9c0, p9_b40, p9_ba0, p9_c00, p9_c60, p9_cc0, p9_d20, p9_d80, p9_de0, p9_e40, p9_ea0, p9_f00, p9_f60, p9_fc0, p9_1380, p9_1400, mb9_a24, mb9_1024, l9_n1320, mb9_1484⟩
  · exact absurd trivial hn
  rcases @sv_ecw3 _ _ _ 0 _ _ _ 0 0 _ [] [] _ _ _ _ 0 0 0 _ _ _ 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F E9 V9 hret hO s9 M0 fR9 r9_2 r9_8 r9_9 r9_18 r9_19 r9_20 r9_21 r9_22 r9_23 r9_24 r9_25 r9_26 r9_27 w9_24 w9_28 w9_2c w9_30 w9_34 w9_38 w9_3c w9_40 w9_44 w9_48 w9_4c w9_50 w9_54 w9_58 w9_5c w9_60 w9_64 w9_68 w9_6c w9_70 w9_78 w9_7c w9_80 w9_84 w9_88 w9_8c w9_90 w9_94 w9_98 w9_9c w9_a0 w9_a4 w9_a8 w9_ac w9_b0 w9_b4 w9_b8 w9_bc w9_c0 w9_c4 w9_c8 w9_cc w9_d0 w9_d4 w9_d8 w9_dc w9_e0 w9_e4 w9_e8 w9_ec w9_f0 w9_f4 w9_f8 w9_fc w9_100 w9_104 w9_108 w9_10c w9_110 w9_114 w9_118 w9_11c w9_120 w9_124 w9_128 w9_12c w9_130 w9_a20 w9_1020 w9_1480 a9_2a0 a9_2c0 a9_2e0 a9_380 a9_400 a9_13e0 a9_1460 a9_1588 p9_320 p9_3a0 p9_420 p9_480 p9_4e0 p9_540 p9_5a0 p9_600 p9_660 p9_6c0 p9_720 p9_780 p9_7e0 p9_840 p9_8a0 p9_900 p9_960 p9_9c0 p9_b40 p9_ba0 p9_c00 p9_c60 p9_cc0 p9_d20 p9_d80 p9_de0 p9_e40 p9_ea0 p9_f00 p9_f60 p9_fc0 p9_1380 p9_1400 mb9_a24 mb9_1024 l9_n1320 mb9_1484 IC0 EC0 WN0 with ⟨hn, -⟩ | ⟨n10, c10, s10, E10, V10, fR10, r10_2, r10_3, r10_4, r10_9, r10_a0, r10_18, r10_19, r10_20, r10_21, r10_23, r10_24, r10_25, r10_26, r10_27, w10_24, w10_28, w10_2c, w10_30, w10_34, w10_38, w10_3c, w10_40, w10_44, w10_48, w10_4c, w10_50, w10_54, w10_58, w10_5c, w10_60, w10_64, w10_68, w10_6c, w10_70, w10_78, w10_7c, w10_80, w10_84, w10_88, w10_8c, w10_90, w10_94, w10_98, w10_9c, w10_a0, w10_a4, w10_a8, w10_ac, w10_b0, w10_b4, w10_b8, w10_bc, w10_c0, w10_c4, w10_c8, w10_cc, w10_d0, w10_d4, w10_d8, w10_dc, w10_e0, w10_e4, w10_e8, w10_ec, w10_f0, w10_f4, w10_f8, w10_fc, w10_100, w10_104, w10_108, w10_10c, w10_110, w10_114, w10_118, w10_11c, w10_120, w10_124, w10_128, w10_12c, w10_130, w10_a20, w10_b28, w10_1020, w10_1128, w10_1480, a10_2a0, a10_2c0, a10_2e0, a10_380, a10_400, a10_13e0, a10_1460, a10_1588, p10_320, p10_3a0, p10_420, p10_480, p10_4e0, p10_540, p10_5a0, p10_600, p10_660, p10_6c0, p10_720, p10_780, p10_7e0, p10_840, p10_8a0, p10_900, p10_960, p10_9c0, p10_c60, p10_cc0, p10_d20, p10_d80, p10_de0, p10_e40, p10_ea0, p10_f00, p10_f60, p10_fc0, p10_1380, p10_1400, mb10_a24, mb10_b2c, mb10_1024, mb10_112c, l10_n1320, mb10_1484⟩
  · exact absurd trivial hn
  refine .inr ⟨⟨x1_0, trivial⟩, n10, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10))))))))), fR10, s10, ME.fr F fR10,
    by rw [r10_3, r9_3, r8_3, r7_3, r6_3, r5_3, r4_3, r3_3, r2_3, r1_3]; exact I.g3, by rw [r10_4, r9_4, r8_4, r7_4, r6_4, r5_4, r4_4, r3_4, r2_4, r1_4]; exact I.g4,
    r10_2, r10_9, r10_a0, r10_18, r10_19, r10_20, r10_21, r10_23, r10_24, r10_25, r10_26, r10_27, w10_24, w10_28, w10_2c, w10_30, w10_34, w10_38, w10_3c, w10_40, w10_44, w10_48, w10_4c, w10_50, w10_54, w10_58, w10_5c, w10_60, w10_64, w10_68, w10_6c, w10_70, w10_78, w10_7c, w10_80, w10_84, w10_88, w10_8c, w10_90, w10_94, w10_98, w10_9c, w10_a0, w10_a4, w10_a8, w10_ac, w10_b0, w10_b4, w10_b8, w10_bc, w10_c0, w10_c4, w10_c8, w10_cc, w10_d0, w10_d4, w10_d8, w10_dc, w10_e0, w10_e4, w10_e8, w10_ec, w10_f0, w10_f4, w10_f8, w10_fc, w10_100, w10_104, w10_108, w10_10c, w10_110, w10_114, w10_118, w10_11c, w10_120, w10_124, w10_128, w10_12c, w10_130, w10_a20, w10_b28, w10_1020, w10_1128, w10_1480, a10_2a0, a10_2c0, a10_2e0, a10_380, a10_400, a10_13e0, a10_1460, a10_1588, l10_n1320,
    ⟨fun j hj => ?_, fun j hj => ?_, fun j _ => ⟨tbl2_lt hG j, tbl2_lt hQ j⟩, mb10_1024, mb10_112c⟩⟩
  · rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
    · exact p10_420
    · exact p10_480
    · exact p10_4e0
    · exact p10_540
    · exact p10_5a0
    · exact p10_600
    · exact p10_660
    · exact p10_6c0
    · omega
  · rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
    · exact p10_720
    · exact p10_780
    · exact p10_7e0
    · exact p10_840
    · exact p10_8a0
    · exact p10_900
    · exact p10_960
    · exact p10_9c0
    · omega

end C3.RV32.Sv
