import C3BootProofs.Proofs.SvP256All

/-!
# `sigstore::verify`: the P-256 check, as a stage

Written by `scripts/gen-sv-p256st.py` from `sv_p256`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Gd

/-- A frame range that covers the whole frame keeps nothing. -/
theorem SvKeepL.whole {B : Word} {M M' : Word → BitVec 8} : SvKeepL B M M' [(0x0, 0x1690)] :=
  fun e he h => by have := h (0x0, 0x1690) (List.mem_singleton.mpr rfl); simp only at this; omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **The P-256 check, as a stage**: `sv_p256` from 0xFBA to 0x2034. -/
theorem sv_p256_st {B out bp x21 x26 : Word} {w84 w4c w50 w54 w58 w64 w68 w6c w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {er es : Bytes} {v : Nat → Word} {n0 : Machine}
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
    (k1 : SvIn B x21 1) (k41 : SvIn B x21 0x41) (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84) (dg_in : SvIn B w84 32)
    (UE0 : CodeIn M0 (BitVec.ofNat 32 uint8EqAddress) uint8EqCode) (N80 : CodeIn M0 (BitVec.ofNat 32 norm8Address) norm8Code) (PM0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode) (WM0 : CodeIn M0 (BitVec.ofNat 32 wideMulAddress) wideMulCode) (PT0 : SvPtCode M0) (WN0 : SvWnCode M0) (ME : MlEnv M0) (P2C0 : P2Code M0) (GDC0 : C3.RV32.Gd.GdCode M0) (P2D0 : P2Data M0) (SC0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarCtEqAddress) p256ScalarCtEqCode)
    (hidC : CodeIn M0 (BitVec.ofNat 32 p256IdentityAddress) p256IdentityData)
    (GD : CodeIn M0 (BitVec.ofNat 32 p256GMontAddress) p256GMontData)
    (OD : CodeIn M0 (BitVec.ofNat 32 p256MontOneAddress) p256MontOneData)
    (AD : CodeIn M0 (BitVec.ofNat 32 p256AffineIdXAddress) p256AffineIdXData)
    (hzi : ∀ Z τd τf Dz Fz, τd ≤ 1 → τf ≤ 1 → sgnVal τf Fz = (p256Sz M0 Z).f → sgnVal τd Dz = (p256Sz M0 Z).d →
        normVal8 τd τf Dz (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8) < p256)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c) (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50) (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54) (w0_58 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58) (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64) (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68) (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c) (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c) (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80) (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84) (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88) (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c) (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90) (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94) (w0_98 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98) (w0_9c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c) (w0_a0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0) (w0_a4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4) (w0_a8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8) (w0_ac : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac) (w0_b0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0) (w0_b4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4) (w0_b8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8) (w0_bc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc) (w0_c0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0) (w0_c4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4) (w0_c8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8) (w0_cc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc) (w0_d0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0) (w0_d4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4) (w0_d8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8) (w0_dc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc) (w0_e0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0) (w0_e4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4) (w0_e8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8) (w0_ec : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec) (w0_f0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0) (w0_f4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4) (w0_f8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8) (w0_fc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc) (w0_100 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100) (w0_104 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104) (w0_108 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108) (w0_10c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c) (w0_110 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110) (w0_114 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114) (w0_118 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118) (w0_11c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c) (w0_120 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120) (w0_124 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124) (w0_128 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128) (w0_12c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c) (w0_130 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130) :
    SvErrRet B out v n0 ∨ Panics n0 ∨
    ((((inScalarRange (b32 er) (memBytes M0 (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (inScalarRange (b32 es) (memBytes M0 (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (M0 x21 = 4) ∧ True) ∧ ((GsOk M0 x21) ∧ (beNat (b32 er) < C3.p256.n) ∧ (beNat (b32 es) < C3.p256.n) ∧ (beNat (b32 er) ≠ 0) ∧ (beNat (b32 es) ≠ 0) ∧ True)) ∧
      ∃ σd σf Dv Fv, σd ≤ 1 ∧ σf ≤ 1 ∧ sgnVal σf Fv = (p256Sf M0 es).f ∧ sgnVal σd Dv = (p256Sf M0 es).d ∧
      (((Fv = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8)) ∧ True) ∧ ∃ stm, mlMain2 (tbl2 (accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x40) 8)) (tbl2 ((gsVal M0 x21 1 * 2 ^ 256 % p256), (gsVal M0 x21 0x21 * 2 ^ 256 % p256), (accV M0 (BitVec.ofNat 32 0x3FCC43A8) 8))) (wnafBytes (wnafGo ((psmVal (((beNat (memBytes M0 (memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84)) 32) % C3.p256.n)) * ((normVal8 σd σf Dv (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0) 0x101) (wnafBytes (wnafGo ((psmVal (((beNat (b32 er))) * ((normVal8 σd σf Dv (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0) 0x101) (max (wnafGo ((psmVal (((beNat (memBytes M0 (memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84)) 32) % C3.p256.n)) * ((normVal8 σd σf Dv (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length (wnafGo ((psmVal (((beNat (b32 er))) * ((normVal8 σd σf Dv (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length) = some stm ∧
      ∃ τd τf Dz Fz, τd ≤ 1 ∧ τf ≤ 1 ∧ sgnVal τf Fz = (p256Sz M0 stm.1.2.2).f ∧ sgnVal τd Dz = (p256Sz M0 stm.1.2.2).d ∧
      ((((beNat (b32 er)) = (p2fm ((if (((((((((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm ((stm.1.1)) ((if ((((((((((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 τd τf Dz (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 0x3FCC442C) 8)) 1) % C3.p256.n)) ∧ True) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x2034 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (BitVec.ofNat 32 (p256Sz M0 stm.1.2.2).rem) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA60) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = (beNat (b32 er)) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = (beNat (b32 es)) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = (beNat (memBytes M0 (memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84)) 32) % C3.p256.n) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = (stm.1.1) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = (stm.1.2.1) ∧
        SvKeepL B n0.mem n'.mem [(0x0, 0x1690)]) := by
  rcases sv_p256 (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) F E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_26 g0_27 b0_138 q0_139 b0_158 q0_159 EC0 IC0 UC0 D0 BG0 RS BY0 k1 k41 (by rw [w0_84]; exact dg_in) UE0 N80 PM0 WM0 PT0 WN0 ME P2C0 GDC0 P2D0 SC0 hidC GD OD AD hzi with ⟨-, e⟩ | e | ⟨h1, σd, σf, Dv, Fv, a4, a5, a6, a7, a8, stm, a10, τd, τf, Dz, Fz, a15, a16, a17, a18, hfin⟩
  · exact .inl e
  · exact .inr (.inl e)
  rcases hfin with ⟨-, e⟩ | ⟨h2, n1, c1, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, f57, f58, f59, f60, f61, f62, f63, f64, f65, f66, f67, f68, f69, f70, f71, f72⟩
  · exact .inl e
  exact .inr (.inr ⟨h1, σd, σf, Dv, Fv, a4, a5, a6, a7, a8, stm, a10, τd, τf, Dz, Fz, a15, a16, a17, a18, h2, n1, c1, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12.trans w0_4c, f13.trans w0_50, f14.trans w0_54, f15.trans w0_58, f16.trans w0_64, f17.trans w0_68, f18.trans w0_6c, f19, f20.trans w0_7c, f21.trans w0_80, f22.trans w0_84, f23.trans w0_88, f24.trans w0_8c, f25.trans w0_90, f26.trans w0_94, f27.trans w0_98, f28.trans w0_9c, f29.trans w0_a0, f30.trans w0_a4, f31.trans w0_a8, f32.trans w0_ac, f33.trans w0_b0, f34.trans w0_b4, f35.trans w0_b8, f36.trans w0_bc, f37.trans w0_c0, f38.trans w0_c4, f39.trans w0_c8, f40.trans w0_cc, f41.trans w0_d0, f42.trans w0_d4, f43.trans w0_d8, f44.trans w0_dc, f45.trans w0_e0, f46.trans w0_e4, f47.trans w0_e8, f48.trans w0_ec, f49.trans w0_f0, f50.trans w0_f4, f51.trans w0_f8, f52.trans w0_fc, f53.trans w0_100, f54.trans w0_104, f55.trans w0_108, f56.trans w0_10c, f57.trans w0_110, f58.trans w0_114, f59.trans w0_118, f60.trans w0_11c, f61.trans w0_120, f62.trans w0_124, f63.trans w0_128, f64.trans w0_12c, f65.trans w0_130, f66, f67, f68, f69, f70, f71, f72, SvKeepL.whole⟩)

end C3.RV32.Sv
