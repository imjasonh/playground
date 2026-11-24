import C3BootProofs.Proofs.SvP256C
import C3BootProofs.Proofs.SvZE

/-!
# `sigstore::verify`: the end of the P-256 check

From the inversion of the sum's `Z` at 0x1B54, with no divsteps left, to 0x2034: `sv_ze` takes the affine
`x` of the sum and compares it with `r`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Gd

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The end of the P-256 check**: from 0x1B54 to 0x2034 when the affine `x` of the sum matches `r`,
and an error return otherwise. -/
theorem sv_p256_end {B r3 r4 out bp x26 nzw : Word} {rv sv zv X Y P R2 : Nat} {W v : Nat → Word} {n0 : Machine}
    {st : Iv} (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (s : St n0.mem SV n0 0x1B54 (reg n0))
    (I : ZvInv B n0 v r3 r4 out bp x26 nzw rv sv zv X Y P R2 W st) (h0 : st.rem = 0)
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (IC0 : SvIvCode M0) (EC0 : SvEcCode M0) (UC0 : SvUpCode M0) (UE0 : CodeIn M0 (BitVec.ofNat 32 uint8EqAddress) uint8EqCode) (N80 : CodeIn M0 (BitVec.ofNat 32 norm8Address) norm8Code) (P2C0 : P2Code M0) (GDC0 : C3.RV32.Gd.GdCode M0) (P2D0 : P2Data M0) (SC0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarCtEqAddress) p256ScalarCtEqCode) (BY0 : BYEnv M0) (WN0 : SvWnCode M0)
    (hnz : nzw = 0 ∨ nzw = 1)
    (hX : X < p256)
    (hY : Y < p256)
    (hid : accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8 < p256)
    (hzi : normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x340))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8)) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) < p256)
    :
    (¬ (((rv = (p2fm ((if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x340))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8)) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n)) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((((rv = (p2fm ((if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x340))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8)) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n)) ∧ True) ∧ ∃ m', Steps n0 m' ∧ (∀ x, SvR B x → m'.mem x = M0 x) ∧ St m'.mem SV m' 0x2034 (reg m') ∧
      SvCode m'.mem ∧ SvSaves B m'.mem v ∧ reg m' (3 : Fin 32) = r3 ∧ reg m' (4 : Fin 32) = r4 ∧
      reg m' sp = B + 0x21A0 ∧
      reg m' (18 : Fin 32) = out ∧
      reg m' (19 : Fin 32) = bp ∧
      reg m' (26 : Fin 32) = x26 ∧
      reg m' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = (memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34)) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38)) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (W 0x4C) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = (W 0x50) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = (W 0x54) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = (W 0x58) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = (W 0x64) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = (W 0x68) ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = (W 0x6C) ∧
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
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF ∧
      m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x340)) ∧
      m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA60) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 ∧
      m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = ((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 ∧
      m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8 ∧
      m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = (n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0)) ∧
      m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = (n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0)) ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x340))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8)) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8) ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (p2fm ((if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x340))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8)) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) 8 = p2fm (Y) ((if ((((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x340))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8)) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8) ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y ∧
      leN (memBytes m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 0x20).reverse = p2fm ((if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x340))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8)) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 ∧
      leN (memBytes m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20).reverse = p2fm ((if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm (X) ((if ((((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((nzw) &&& (((if (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x340))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8)) (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1 ∧
      SvKeepL B n0.mem m'.mem [(0xA20, 0x20), (0x1020, 0x20), (0x1040, 0x1), (0x420, 0x20), (0xA20, 0x20), (0xA40, 0x1), (0x420, 0x21), (0x1020, 0x20), (0x1480, 0x20), (0xA20, 0x20), (0xA40, 0x20), (0xA60, 0x1), (0xA64, 0x1), (0x420, 0x41), (0x1020, 0x20), (0xA20, 0x20), (0x1020, 0x20), (0x1480, 0x20), (0xA20, 0x20)]) := by
  have hrem' : BitVec.ofNat 32 st.rem = 0 := by rw [h0]; rfl
  rcases sv_ze F I.E I.V hret hO s M0 fM I.sp I.g18 I.g19 I.g26 I.g27 I.w20 rfl rfl (I.ww 0x4C (by decide)) (I.ww 0x50 (by decide)) (I.ww 0x54 (by decide)) (I.ww 0x58 (by decide)) (I.ww 0x64 (by decide)) (I.ww 0x68 (by decide)) (I.ww 0x6C (by decide)) I.wr (I.ww 0x7C (by decide)) (I.ww 0x80 (by decide)) (I.ww 0x84 (by decide)) (I.ww 0x88 (by decide)) (I.ww 0x8C (by decide)) (I.ww 0x90 (by decide)) (I.ww 0x94 (by decide)) (I.ww 0x98 (by decide)) (I.ww 0x9C (by decide)) (I.ww 0xA0 (by decide)) (I.ww 0xA4 (by decide)) (I.ww 0xA8 (by decide)) (I.ww 0xAC (by decide)) (I.ww 0xB0 (by decide)) (I.ww 0xB4 (by decide)) (I.ww 0xB8 (by decide)) (I.ww 0xBC (by decide)) (I.ww 0xC0 (by decide)) (I.ww 0xC4 (by decide)) (I.ww 0xC8 (by decide)) (I.ww 0xCC (by decide)) (I.ww 0xD0 (by decide)) (I.ww 0xD4 (by decide)) (I.ww 0xD8 (by decide)) (I.ww 0xDC (by decide)) (I.ww 0xE0 (by decide)) (I.ww 0xE4 (by decide)) (I.ww 0xE8 (by decide)) (I.ww 0xEC (by decide)) (I.ww 0xF0 (by decide)) (I.ww 0xF4 (by decide)) (I.ww 0xF8 (by decide)) (I.ww 0xFC (by decide)) (I.ww 0x100 (by decide)) (I.ww 0x104 (by decide)) (I.ww 0x108 (by decide)) (I.ww 0x10C (by decide)) (I.ww 0x110 (by decide)) (I.ww 0x114 (by decide)) (I.ww 0x118 (by decide)) (I.ww 0x11C (by decide)) (I.ww 0x120 (by decide)) (I.ww 0x124 (by decide)) (I.ww 0x128 (by decide)) (I.ww 0x12C (by decide)) (I.ww 0x130 (by decide)) I.w460 I.w464 I.a2a0 I.a2c0 I.a2e0 rfl (I.a420.trans (I.aP.symm.trans (accV_dataR F fM (by decide) (by decide)))) (I.a440.trans (I.aR.symm.trans (accV_dataR F fM (by decide) (by decide)))) rfl rfl rfl I.a15a8 I.a15c8 rfl rfl rfl rfl IC0 EC0 hrem' UC0 UE0 N80 P2C0 GDC0 P2D0 SC0 BY0 WN0 I.lf I.ld hnz hX hY hid hzi with ⟨hn, e⟩ | ⟨x1_0, n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_18, r1_19, r1_26, r1_27, w1_20, w1_34, w1_38, w1_4c, w1_50, w1_54, w1_58, w1_64, w1_68, w1_6c, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, w1_464, b1_340, b1_a60, b1_a64, b1_1040, b1_13a0, b1_14a0, a1_2a0, a1_2c0, a1_2e0, a1_320, a1_420, a1_a20, a1_a40, a1_1380, a1_15a8, a1_15c8, l1_n1020, l1_n1480, K1_L⟩
  · exact .inl ⟨hn, e⟩
  exact .inr ⟨⟨x1_0, trivial⟩, n1, c1, fR1, s1, E1, V1, by rw [r1_3]; exact I.g3,
    by rw [r1_4]; exact I.g4, r1_2, r1_18, r1_19, r1_26, r1_27, w1_20, w1_34, w1_38, w1_4c, w1_50, w1_54, w1_58, w1_64, w1_68, w1_6c, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, w1_464, b1_340, b1_a60, b1_a64, b1_1040, b1_13a0, b1_14a0, a1_2a0, a1_2c0, a1_2e0, a1_320, a1_420, a1_a20, a1_a40, a1_1380, a1_15a8, a1_15c8, l1_n1020, l1_n1480, K1_L⟩

end C3.RV32.Sv
