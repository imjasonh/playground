import C3BootProofs.Proofs.SvP256D
import C3BootProofs.Image.BootloaderData5

/-!
# `sigstore::verify`: the whole P-256 check

From 0xFBA to 0x2034: the range checks and key decode, the inversion of `s` (`ivLoop8`), the tables and
wNAF digits, the main loop (`mlMain2`), the inversion of the sum's `Z` (`zvLoop`), and the comparison with
`r`. The inverses that leave the two inversions are named by witnesses that `sgnVal` ties to the models'
states.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Gd

set_option maxRecDepth 100000

/-- The inversion of `s`'s state after its 10 batches. -/
def p256Sf (M0 : Word → BitVec 8) (es : Bytes) : Iv :=
  ivLoop8 (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8) 10 (p256Iv0 M0 es)

/-- The inversion of `Z`'s state after its 10 batches. -/
def p256Sz (M0 : Word → BitVec 8) (Z : Nat) : Iv :=
  zvLoop (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8) 10 (p256Zv0 M0 Z)

theorem p256_zx (b : BitVec 8) : (b.zeroExtend 32).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

theorem p256_nzw (Z : Nat) : (((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF) = 0 ∨
    (((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF) = 1 := by
  by_cases h : Z = 0
  · rw [ite_eq_left h]; exact .inl (by decide)
  · rw [ite_eq_right h]; exact .inr (by decide)

set_option maxHeartbeats 64000000 in
/-- **The P-256 check in `sigstore::verify`**: from 0xFBA to 0x2034 when the signature is valid by the
check's arithmetic, an error return when it isn't, or a panic when the inversion of `s` doesn't end with
`f = ±1` or the main loop meets an invalid wNAF digit. -/
theorem sv_p256 {B out bp x21 x26 : Word} {er es : Bytes} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xFBA (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (b0_138 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x138) = BitVec.ofNat 8 (er.getD 0 0))
    (q0_139 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x139 + j)) = BitVec.ofNat 8 (er.getD (1 + j) 0))
    (b0_158 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = BitVec.ofNat 8 (es.getD 0 0))
    (q0_159 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x159 + j)) = BitVec.ofNat 8 (es.getD (1 + j) 0))
    (EC0 : SvEcCode M0)
    (IC0 : SvIvCode M0) (UC0 : SvUpCode M0) (D0 : P2Data M0) (BG0 : BGEnv M0) (RS : SvRoSep B) (BY0 : BYEnv M0)
    (k1 : SvIn B x21 1) (k41 : SvIn B x21 0x41) (dg_in : SvIn B (memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84)) 32)
    (UE0 : CodeIn M0 (BitVec.ofNat 32 uint8EqAddress) uint8EqCode) (N80 : CodeIn M0 (BitVec.ofNat 32 norm8Address) norm8Code) (PM0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode) (WM0 : CodeIn M0 (BitVec.ofNat 32 wideMulAddress) wideMulCode) (PT0 : SvPtCode M0) (WN0 : SvWnCode M0) (ME : MlEnv M0) (P2C0 : P2Code M0) (GDC0 : C3.RV32.Gd.GdCode M0) (P2D0 : P2Data M0) (SC0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarCtEqAddress) p256ScalarCtEqCode)
    (hidC : CodeIn M0 (BitVec.ofNat 32 p256IdentityAddress) p256IdentityData)
    (GD : CodeIn M0 (BitVec.ofNat 32 p256GMontAddress) p256GMontData)
    (OD : CodeIn M0 (BitVec.ofNat 32 p256MontOneAddress) p256MontOneData)
    (AD : CodeIn M0 (BitVec.ofNat 32 p256AffineIdXAddress) p256AffineIdXData)
    (hzi : ∀ Z τd τf Dz Fz, τd ≤ 1 → τf ≤ 1 → sgnVal τf Fz = (p256Sz M0 Z).f → sgnVal τd Dz = (p256Sz M0 Z).d →
        normVal8 τd τf Dz (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8) < p256) :
    (¬ (((inScalarRange (b32 er) (memBytes M0 (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (inScalarRange (b32 es) (memBytes M0 (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (M0 x21 = 4) ∧ True) ∧ ((GsOk M0 x21) ∧ (beNat (b32 er) < C3.p256.n) ∧ (beNat (b32 es) < C3.p256.n) ∧ (beNat (b32 er) ≠ 0) ∧ (beNat (b32 es) ≠ 0) ∧ True)) ∧ SvErrRet B out v n0) ∨ Panics n0 ∨
    ((((inScalarRange (b32 er) (memBytes M0 (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (inScalarRange (b32 es) (memBytes M0 (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (M0 x21 = 4) ∧ True) ∧ ((GsOk M0 x21) ∧ (beNat (b32 er) < C3.p256.n) ∧ (beNat (b32 es) < C3.p256.n) ∧ (beNat (b32 er) ≠ 0) ∧ (beNat (b32 es) ≠ 0) ∧ True)) ∧
      ∃ σd σf Dv Fv, σd ≤ 1 ∧ σf ≤ 1 ∧ sgnVal σf Fv = (p256Sf M0 es).f ∧ sgnVal σd Dv = (p256Sf M0 es).d ∧
      (((Fv = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8)) ∧ True) ∧ ∃ stm, mlMain2 (tbl2 (accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x40) 8)) (tbl2 ((gsVal M0 x21 1 * 2 ^ 256 % p256), (gsVal M0 x21 0x21 * 2 ^ 256 % p256), (accV M0 (BitVec.ofNat 32 0x3FCC43A8) 8))) (wnafBytes (wnafGo ((psmVal (((beNat (memBytes M0 (memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84)) 32) % C3.p256.n)) * ((normVal8 σd σf Dv (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0) 0x101) (wnafBytes (wnafGo ((psmVal (((beNat (b32 er))) * ((normVal8 σd σf Dv (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0) 0x101) (max (wnafGo ((psmVal (((beNat (memBytes M0 (memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84)) 32) % C3.p256.n)) * ((normVal8 σd σf Dv (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length (wnafGo ((psmVal (((beNat (b32 er))) * ((normVal8 σd σf Dv (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length) = some stm ∧
      ∃ τd τf Dz Fz, τd ≤ 1 ∧ τf ≤ 1 ∧ sgnVal τf Fz = (p256Sz M0 stm.1.2.2).f ∧ sgnVal τd Dz = (p256Sz M0 stm.1.2.2).d ∧
      ((¬ ((((beNat (b32 er)) = (p2fm ((if (((((((((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm ((stm.1.1)) ((if ((((((((((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 τd τf Dz (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 0x3FCC442C) 8)) 1) % C3.p256.n)) ∧ True) ∧ SvErrRet B out v n0) ∨
       (((((beNat (b32 er)) = (p2fm ((if (((((((((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm ((stm.1.1)) ((if ((((((((((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 τd τf Dz (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 0x3FCC442C) 8)) 1) % C3.p256.n)) ∧ True) ∧ ∃ m', Steps n0 m' ∧ (∀ x, SvR B x → m'.mem x = M0 x) ∧ St m'.mem SV m' 0x2034 (reg m') ∧
        SvCode m'.mem ∧ SvSaves B m'.mem v ∧ reg m' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg m' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg m' sp = B + 0x21A0 ∧
        reg m' (18 : Fin 32) = out ∧
        reg m' (19 : Fin 32) = bp ∧
        reg m' (26 : Fin 32) = x26 ∧
        reg m' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF)) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x4C) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x50) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x54) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x58) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x64) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x68) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x6C) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (BitVec.ofNat 32 (p256Sz M0 stm.1.2.2).rem) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x7C) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x80) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x84) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x88) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x8C) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x90) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x94) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x98) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x9C) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xA0) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xA4) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xA8) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xAC) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xB0) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xB4) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xB8) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xBC) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xC0) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xC4) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xC8) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xCC) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xD0) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xD4) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xD8) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xDC) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xE0) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xE4) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xE8) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xEC) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xF0) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xF4) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xF8) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0xFC) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x100) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x104) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x108) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x10C) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x110) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x114) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x118) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x11C) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x120) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x124) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x128) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x12C) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = (((fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e))) 0x130) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF ∧
        m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA60) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 ∧
        accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = (beNat (b32 er)) ∧
        accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = (beNat (b32 es)) ∧
        accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = (beNat (memBytes M0 (memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84)) 32) % C3.p256.n) ∧
        accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = (stm.1.1) ∧
        accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = (stm.1.2.1)))) := by
  have hN : 0 < accV M0 (BitVec.ofNat 32 0x3FCC4268) 8 := by
    show 0 < accV M0 BYO 8; rw [BY0.ord]; decide
  have hP : 0 < accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by
    have h := code_accV D0.params 0 8 (by decide)
    rw [add_ofNat_zero] at h
    show 0 < accV M0 P2N 8; rw [h]; decide
  have hG : Pt2Lt (accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x40) 8) := by
    have g0 : accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x0) 8 = dataVal p256GMontData 0 8 :=
      code_accV GD 0 8 (by decide)
    have g1 : accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x20) 8 = dataVal p256GMontData 0x20 8 :=
      code_accV GD 0x20 8 (by decide)
    have g2 : accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x40) 8 = dataVal p256GMontData 0x40 8 :=
      code_accV GD 0x40 8 (by decide)
    rw [g0, g1, g2]; exact ⟨by decide, by decide, by decide⟩
  have hQ : Pt2Lt ((gsVal M0 x21 1 * 2 ^ 256 % p256), (gsVal M0 x21 0x21 * 2 ^ 256 % p256), (accV M0 (BitVec.ofNat 32 0x3FCC43A8) 8)) := by
    have z : accV M0 (BitVec.ofNat 32 0x3FCC43A8 + BitVec.ofNat 32 0) 8 = dataVal p256MontOneData 0 8 :=
      code_accV OD 0 8 (by decide)
    rw [add_ofNat_zero] at z
    exact ⟨Nat.mod_lt _ p256_pos, Nat.mod_lt _ p256_pos, by show accV M0 (BitVec.ofNat 32 0x3FCC43A8) 8 < p256; rw [z]; decide⟩
  have hidR : accV M0 (BitVec.ofNat 32 0x3FCC442C) 8 < p256 := by
    have z : accV M0 (BitVec.ofNat 32 0x3FCC442C + BitVec.ofNat 32 0) 8 = dataVal p256AffineIdXData 0 8 :=
      code_accV AD 0 8 (by decide)
    rw [add_ofNat_zero] at z
    rw [z]; decide
  rcases sv_p256_inv F E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_26 g0_27 b0_138 q0_139 b0_158 q0_159 EC0 IC0 UC0 D0 BG0 RS BY0 k1 k41 dg_in with ⟨hn, e⟩ | ⟨h1, h2, m1, c1, fr1, s1, I1⟩
  · exact .inl ⟨hn, e⟩
  obtain ⟨m2, c2, fr2, s2, I2⟩ := iv_loop F hret hO hN 10 s1 I1
  obtain ⟨m3, c3, fr3, s3, I3⟩ := iv_exit F hret hO hN s2 I2
    (ivLoop8_stop _ 10 _ (by show 0x24F ≤ 62 * 10; decide))
  have fM3 : ∀ x, SvR B x → m3.mem x = M0 x := fun x hx => by rw [fr3 x hx, fr2 x hx, fr1 x hx]
  rcases sv_p256_z F hret hO s3 I3 M0 fM3 IC0 EC0 UC0 UE0 N80 RS PM0 WM0 PT0 WN0 ME hG hQ hidC with e | ⟨x3, stm, hst, l3, m4, c4, fr4, s4, I4⟩
  · exact .inr (.inl (Panics.of_steps (c1.trans (c2.trans c3)) e))
  obtain ⟨m5, c5, fr5, s5, I5⟩ := zv_loop F hret hO hP 10 s4 I4
  have fM5 : ∀ x, SvR B x → m5.mem x = M0 x := fun x hx => by rw [fr5 x hx, fr4 x hx]
  have W3 : ((m3.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0)).zeroExtend 32).toNat ≤ 1 := by rw [p256_zx]; exact I3.lf
  have V3 : sgnVal ((m3.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0)).zeroExtend 32).toNat (accV m3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8) = (p256Sf M0 es).f := by rw [p256_zx]; exact I3.vf
  have W5 : ((m5.mem (B + 0x21A0 + BitVec.ofNat 32 0x340)).zeroExtend 32).toNat ≤ 1 := by rw [p256_zx]; exact I5.lf
  have V5 : sgnVal ((m5.mem (B + 0x21A0 + BitVec.ofNat 32 0x340)).zeroExtend 32).toNat (accV m5.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = (p256Sz M0 stm.1.2.2).f := by rw [p256_zx]; exact I5.vf
  rcases sv_p256_end F hret hO s5 I5 (zvLoop_rem _ 10 _ (by show 0x24F ≤ 62 * 10; decide)) M0 fM5 IC0 EC0 UC0 UE0 N80 P2C0 GDC0 P2D0 SC0 BY0 WN0 (p256_nzw _) l3.1 l3.2.1 hidR (hzi _ _ _ _ _ I5.ld W5 V5 I5.vd) with ⟨hn, e⟩ | ⟨h6, m6, c6, fr6, s6, E6, V6, g6_3, g6_4,
      d6_0, d6_1, d6_2, d6_3, d6_4, d6_5, d6_6, d6_7, d6_8, d6_9, d6_10, d6_11, d6_12, d6_13, d6_14, d6_15, d6_16, d6_17, d6_18, d6_19, d6_20, d6_21, d6_22, d6_23, d6_24, d6_25, d6_26, d6_27, d6_28, d6_29, d6_30, d6_31, d6_32, d6_33, d6_34, d6_35, d6_36, d6_37, d6_38, d6_39, d6_40, d6_41, d6_42, d6_43, d6_44, d6_45, d6_46, d6_47, d6_48, d6_49, d6_50, d6_51, d6_52, d6_53, d6_54, d6_55, d6_56, d6_57, d6_58, d6_59, d6_60, d6_61, d6_62, d6_63, d6_64, d6_65, d6_66, d6_67, d6_68, d6_69, d6_70, d6_71, d6_72, d6_73, d6_74, d6_75, d6_76, d6_77, d6_78, d6_79, d6_80⟩
  · exact .inr (.inr ⟨⟨h1, h2⟩, _, _, _, _, I3.ld, W3, V3, I3.vd, x3, stm, hst, _, _, _, _, I5.ld, W5, V5, I5.vd, .inl ⟨hn, SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans c5))))
      I5.g3 I5.g4 (fun x hx => (fM5 x hx).trans (fM x hx).symm) e⟩⟩)
  · exact .inr (.inr ⟨⟨h1, h2⟩, _, _, _, _, I3.ld, W3, V3, I3.vd, x3, stm, hst, _, _, _, _, I5.ld, W5, V5, I5.vd, .inr ⟨h6, m6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))),
      fr6, s6, E6, V6, g6_3, g6_4,
      d6_0, d6_1, d6_2, d6_3, d6_4, d6_5, d6_8, d6_9, d6_10, d6_11, d6_12, d6_13, d6_14, d6_15, d6_16, d6_17, d6_18, d6_19, d6_20, d6_21, d6_22, d6_23, d6_24, d6_25, d6_26, d6_27, d6_28, d6_29, d6_30, d6_31, d6_32, d6_33, d6_34, d6_35, d6_36, d6_37, d6_38, d6_39, d6_40, d6_41, d6_42, d6_43, d6_44, d6_45, d6_46, d6_47, d6_48, d6_49, d6_50, d6_51, d6_52, d6_53, d6_54, d6_55, d6_56, d6_57, d6_58, d6_59, d6_60, d6_61, d6_62, d6_64, d6_69, d6_70, d6_71, d6_77, d6_78⟩⟩)

end C3.RV32.Sv
