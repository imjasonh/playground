import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvSegCkpt
import C3BootProofs.Proofs.SvCkdLoop
import C3BootProofs.Proofs.SvCSearch
import C3BootProofs.Proofs.SvCs1
import C3BootProofs.Proofs.SvCosigLoop
import C3BootProofs.Proofs.SvSegWin

/-!
# `sigstore::verify`: The transparency log entry

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The transparency log entry**: from the checkpoint at 0x2B34 to the successful exit at 0x3264: the checkpoint, the log that signed it, its signatures, the entry's index, and the validity windows. -/
theorem sv_seg_log {B out bp x21 x26 dg dp pv q ckp ckl : Word} {w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word} {n0 : Machine} {w8 : Word} {wc : Word} {w10 : Word} {w14 : Word} {w18 : Word} {w1c : Word} {sg : Bytes}
    (F : Fr B 0x3830)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x2B34 (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = pv)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = dp)
    (g0_23 : reg n0 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40)
    (g0_24 : reg n0 (24 : Fin 32) = dg)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24)
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28)
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54)
    (w0_58 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58)
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c)
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64)
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68)
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c)
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84)
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88)
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c)
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90)
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94)
    (w0_98 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98)
    (w0_9c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c)
    (w0_a0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0)
    (w0_a4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4)
    (w0_a8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8)
    (w0_ac : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac)
    (w0_b0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0)
    (w0_b4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4)
    (w0_b8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8)
    (w0_bc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc)
    (w0_c0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0)
    (w0_c4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4)
    (w0_c8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8)
    (w0_cc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc)
    (w0_d0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0)
    (w0_d4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4)
    (w0_d8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8)
    (w0_dc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc)
    (w0_e0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0)
    (w0_e4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4)
    (w0_e8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8)
    (w0_ec : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec)
    (w0_f0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0)
    (w0_f4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4)
    (w0_f8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8)
    (w0_fc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc)
    (w0_100 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100)
    (w0_104 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104)
    (w0_108 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108)
    (w0_10c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c)
    (w0_110 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110)
    (w0_114 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114)
    (w0_118 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118)
    (w0_11c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c)
    (w0_120 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120)
    (w0_124 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124)
    (w0_128 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128)
    (w0_12c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c)
    (w0_130 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130)
    (w0_a20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70)
    (w0_a24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21)
    (w0_a28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c)
    (w0_a2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48)
    (w0_a30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44)
    (w0_a34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60)
    (w0_a38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c)
    (w0_a3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78)
    (w0_aa0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp)
    (w0_aa4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg)
    (CK0 : SvCkCode M0)
    (hckp : memLoad32 M0 (bp + 0x18) = ckp)
    (hckl : memLoad32 M0 (bp + 0x1C) = ckl)
    (ckp_in4 : SvIn B (bp + 0x18) 4)
    (ckl_in4 : SvIn B (bp + 0x1C) 4)
    (a_ckp : (bp + 0x18).toNat % 4 = 0)
    (a_ckl : (bp + 0x1C).toNat % 4 = 0)
    (ck_in : SvIn B ckp ckl.toNat)
    (w0_8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8)
    (w0_c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc)
    (w0_10 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10)
    (w0_14 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18)
    (w0_1c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c)
    (H' : ∀ i, i < 8 → ∀ c'_3 q'_3 w80'_3, (c'_3, q'_3, w80'_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2.1)) + BitVec.ofNat 32 0x20, (memLoad32 M0 ((s.2.1) + 0x20)))) i ((BitVec.ofNat 32 0x100), ((w80) + BitVec.ofNat 32 0x98), w80) → (SvIn B (q'_3 + 0x20) 4) ∧ (SvIn B (q'_3 + 0x24) 4) ∧ ((q'_3 + 0x20).toNat % 4 = 0) ∧ ((q'_3 + 0x24).toNat % 4 = 0) ∧ (SvIn B (memLoad32 M0 (q'_3 + 0x20)) (memLoad32 M0 (q'_3 + 0x24)).toNat))
    (S2 : SvSha2Code M0)
    (KS : SvK2Sep B)
    (kp_in4 : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 M0 (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), ((w80) + BitVec.ofNat 32 0x98), w80) → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x18) 4)
    (kw_in4 : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 M0 (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), ((w80) + BitVec.ofNat 32 0x98), w80) → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x1C) 4)
    (a_kp : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 M0 (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), ((w80) + BitVec.ofNat 32 0x98), w80) → (((y1) + BitVec.ofNat 32 0x20) + 0x18).toNat % 4 = 0)
    (a_kw : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 M0 (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), ((w80) + BitVec.ofNat 32 0x98), w80) → (((y1) + BitVec.ofNat 32 0x20) + 0x1C).toNat % 4 = 0)
    (kp_in : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 M0 (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), ((w80) + BitVec.ofNat 32 0x98), w80) → SvIn B (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 32)
    (b0_10 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = BitVec.ofNat 8 (sg.getD 0 0))
    (q0_1480 : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1480 + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0))
    (EE0 : EvEnv M0)
    (RS : SvRoSep B)
    (hiv : (s5Hv M0 (BitVec.ofNat 32 0x3FCC4AF8)).toList = Sha512.h0)
    (pk_in : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 M0 (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), ((w80) + BitVec.ofNat 32 0x98), w80) → SvIn B (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 32)
    (lid_in : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 M0 (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), ((w80) + BitVec.ofNat 32 0x98), w80) → SvIn B (((y1) + BitVec.ofNat 32 0x20) + BitVec.ofNat 32 0x5) 19)
    (lih_in : SvIn B (bp + 0x2C) 4)
    (lil_in : SvIn B (bp + 0x28) 4)
    (a_lih : (bp + 0x2C).toNat % 4 = 0)
    (a_lil : (bp + 0x28).toNat % 4 = 0)
    (RK0 : SvRkCode M0)
    (dgi_in : SvIn B w84 32)
    (sig_in : SvIn B w68 w64.toNat)
    (crt_in : SvIn B w6c x26.toNat)
    (pp_in4 : SvIn B (bp + 0x10) 4)
    (pl_in4 : SvIn B (bp + 0x14) 4)
    (a_pp : (bp + 0x10).toNat % 4 = 0)
    (a_pl : (bp + 0x14).toNat % 4 = 0)
    (pp_in : SvIn B (memLoad32 M0 (bp + 0x10)) (memLoad32 M0 (bp + 0x14)).toNat)
    (ii2h : SvIn B (w7c + 0xFFFFFFE8) 4)
    (ai2h : (w7c + 0xFFFFFFE8).toNat % 4 = 0)
    (ii2l : SvIn B (w7c + 0xFFFFFFE4) 4)
    (ai2l : (w7c + 0xFFFFFFE4).toNat % 4 = 0)
    (ii3h : SvIn B (w7c + 0xFFFFFFF0) 4)
    (ai3h : (w7c + 0xFFFFFFF0).toNat % 4 = 0)
    (ii3l : SvIn B (w7c + 0xFFFFFFEC) 4)
    (ai3l : (w7c + 0xFFFFFFEC).toNat % 4 = 0)
    (it4h : SvIn B (q + 0xC) 4)
    (at4h : (q + 0xC).toNat % 4 = 0)
    (it4l : SvIn B (q + 0x8) 4)
    (at4l : (q + 0x8).toNat % 4 = 0)
    (it5h : SvIn B (q + 0x14) 4)
    (at5h : (q + 0x14).toNat % 4 = 0)
    (it5l : SvIn B (q + 0x10) 4)
    (at5l : (q + 0x10).toNat % 4 = 0) :
    SvErrRet B out v n0 ∨
    ((pv ≠ 0) ∧
      ∃ ix7_1_1, nlScan M0 (ckp) 0 ((ckl).toNat) = some ix7_1_1 ∧
      ∃ ix17_1_1, nlScan M0 ((ckp) + BitVec.ofNat 32 (ix7_1_1 + 1)) 0 (((ckl).toNat) - (ix7_1_1 + 1)) = some ix17_1_1 ∧
      ∃ ix25_1_1, nlScan M0 (((ckp) + BitVec.ofNat 32 (ix7_1_1 + 1)) + BitVec.ofNat 32 (ix17_1_1 + 1)) 0 ((((ckl).toNat) - (ix7_1_1 + 1)) - (ix17_1_1 + 1)) = some ix25_1_1 ∧
      ∃ ix33_1_1, nlScan M0 ((((ckp) + BitVec.ofNat 32 (ix7_1_1 + 1)) + BitVec.ofNat 32 (ix17_1_1 + 1)) + BitVec.ofNat 32 (ix25_1_1 + 1)) 0 (((((ckl).toNat) - (ix7_1_1 + 1)) - (ix17_1_1 + 1)) - (ix25_1_1 + 1)) = some ix33_1_1 ∧
      (BitVec.ofNat 32 ix33_1_1 = 0) ∧
      (BitVec.ofNat 32 (((((ckl).toNat) - (ix7_1_1 + 1)) - (ix17_1_1 + 1)) - (ix25_1_1 + 1)) - BitVec.ofNat 32 (ix33_1_1 + 1) ≠ 0) ∧
      ((((BitVec.ofNat 32 (((((ckl).toNat) - (ix7_1_1 + 1)) - (ix17_1_1 + 1)) - (ix25_1_1 + 1)) - BitVec.ofNat 32 (ix33_1_1 + 1)).toNat < ckl.toNat) ∧ (¬ (ckl).toNat < ((aluEval .xor ((BitVec.ofNat 32 (((((ckl).toNat) - (ix7_1_1 + 1)) - (ix17_1_1 + 1)) - (ix25_1_1 + 1)) - BitVec.ofNat 32 (ix33_1_1 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)).toNat) ∧ (¬ (((BitVec.ofNat 32 ix17_1_1)) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat) ∧ (M0 ((ckp) + BitVec.ofNat 32 (ix7_1_1 + 1)) ≠ 0x30)) ∨ (((BitVec.ofNat 32 (((((ckl).toNat) - (ix7_1_1 + 1)) - (ix17_1_1 + 1)) - (ix25_1_1 + 1)) - BitVec.ofNat 32 (ix33_1_1 + 1)).toNat < ckl.toNat) ∧ (¬ (ckl).toNat < ((aluEval .xor ((BitVec.ofNat 32 (((((ckl).toNat) - (ix7_1_1 + 1)) - (ix17_1_1 + 1)) - (ix25_1_1 + 1)) - BitVec.ofNat 32 (ix33_1_1 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)).toNat) ∧ (¬ (((BitVec.ofNat 32 ix17_1_1)) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat))) ∧
      ∃ c'_2 p'_2 x21'_2 w60'_2 w70'_2, (c'_2, p'_2, x21'_2, w60'_2, w70'_2) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, (s.2.2.2.2), ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))))) (BitVec.ofNat 32 ix17_1_1).toNat ((BitVec.ofNat 32 ix17_1_1), ((ckp) + BitVec.ofNat 32 (ix7_1_1 + 1)), x21, (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0)) ∧
      (w70'_2.toNat < 2 ^ 31) ∧ ∃ bs7_2, base64Decode (memBytes M0 ((((ckp) + BitVec.ofNat 32 (ix7_1_1 + 1)) + BitVec.ofNat 32 (ix17_1_1 + 1))) (((BitVec.ofNat 32 ix25_1_1)).toNat)) = some bs7_2 ∧ (bs7_2.length = 32) ∧
      ∃ k_3, k_3 < 8 ∧
      (∀ i, i < k_3 → ∀ c'_3 q'_3 w80'_3, (c'_3, q'_3, w80'_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2.1)) + BitVec.ofNat 32 0x20, (memLoad32 M0 ((s.2.1) + 0x20)))) i ((BitVec.ofNat 32 0x100), ((w80) + BitVec.ofNat 32 0x98), w80) → ¬ (memBytes M0 (memLoad32 M0 (q'_3 + 0x20)) (memLoad32 M0 (q'_3 + 0x24)).toNat = memBytes M0 ckp (BitVec.ofNat 32 ix7_1_1).toNat)) ∧
      ∃ c'_3 q'_3 w80'_3, (c'_3, q'_3, w80'_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2.1)) + BitVec.ofNat 32 0x20, (memLoad32 M0 ((s.2.1) + 0x20)))) k_3 ((BitVec.ofNat 32 0x100), ((w80) + BitVec.ofNat 32 0x98), w80) ∧
      ((memLoad32 M0 (q'_3 + 0x20)) ≠ 0) ∧
      ∃ k_5 c'_5 x21'_5 rl'_5 rp'_5 dg'_5 w8'_5 wc'_5 w28'_5 w2c'_5 w30'_5 w38'_5 w40'_5 w5c'_5 sg'_5, svChain (sv_cosigStep dp B out bp x26 ((q'_3) + BitVec.ofNat 32 0x20) bs7_2 (le4 (sha256 (memBytes M0 (ckp) (((BitVec.ofNat 32 ix7_1_1)).toNat) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4850) (1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D7) (1) ++ memBytes M0 ((memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x18))) (32))) 0) (memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x1C)) ((aluEval .xor ((BitVec.ofNat 32 (((((ckl).toNat) - (ix7_1_1 + 1)) - (ix17_1_1 + 1)) - (ix25_1_1 + 1)) - BitVec.ofNat 32 (ix33_1_1 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)) ckp (memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x18)) w3c (BitVec.ofNat 32 ix7_1_1) ckp w4c w50 w54 w58 w60'_2 w64 w68 w6c w70'_2 w78 w7c (memLoad32 M0 (q'_3 + 0x20)) w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 w70 x21 w5c w48 w44 w60 w3c w78 dg v 0 0 0 M0) k_5 (((c'_3) + BitVec.ofNat 32 0xFFFFFFE0), x21'_2, (BitVec.ofNat 32 ix25_1_1), (((ckp) + BitVec.ofNat 32 (ix7_1_1 + 1)) + BitVec.ofNat 32 (ix17_1_1 + 1)), dg, w8, wc, w28, w2c, (BitVec.ofNat 32 0x0), (((((ckp) + BitVec.ofNat 32 (ix7_1_1 + 1)) + BitVec.ofNat 32 (ix17_1_1 + 1)) + BitVec.ofNat 32 (ix25_1_1 + 1)) + BitVec.ofNat 32 (ix33_1_1 + 1)), w40, (BitVec.ofNat 32 (((((ckl).toNat) - (ix7_1_1 + 1)) - (ix17_1_1 + 1)) - (ix25_1_1 + 1)) - BitVec.ofNat 32 (ix33_1_1 + 1)), sg) (c'_5, x21'_5, rl'_5, rp'_5, dg'_5, w8'_5, wc'_5, w28'_5, w2c'_5, w30'_5, w38'_5, w40'_5, w5c'_5, sg'_5) ∧
      w5c'_5 = 0 ∧
      ((w30'_5) &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ (evSpec (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 0x420) sg'_5) (memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) ckp (((aluEval .xor ((BitVec.ofNat 32 (((((ckl).toNat) - (ix7_1_1 + 1)) - (ix17_1_1 + 1)) - (ix25_1_1 + 1)) - BitVec.ofNat 32 (ix33_1_1 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl))).toNat = true) ∧
      (((aluEval .sltu ((memLoad32 M0 (bp + 0x28))) (w60'_2) ≠ 0)) ∨ ((aluEval .sltu ((memLoad32 M0 (bp + 0x2C))) (w70'_2) ≠ 0))) ∧
      ∃ root6_3_6, rootFromInclusion (pair64 ((memLoad32 M0 (bp + 0x28))) ((memLoad32 M0 (bp + 0x2C)))) (pair64 (w60'_2) (w70'_2)) ((sha256 ([] ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4106) (0x1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC46F0) (0x71) ++ base64Encode (memBytes M0 (w84) (32)) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4761) (0x1B) ++ base64Encode (memBytes M0 (w68) ((w64).toNat)) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC477C) (0x54) ++ base64Encode (memBytes M0 (w6c) ((x26).toNat)) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D0) (0x7)))) (memBytes M0 ((memLoad32 M0 (bp + 0x10))) (((memLoad32 M0 (bp + 0x14))).toNat)) = some root6_3_6 ∧
      (b32 root6_3_6 = b32 bs7_2) ∧
      (((aluEval .sltu (w3c) (w58) = 0)) ∨ ((aluEval .sltu (w78) (w54) = 0))) ∧
      (((aluEval .sltu (w50) (w3c) = 0)) ∨ ((aluEval .sltu (w4c) (w78) = 0))) ∧
      (((aluEval .sltu (w3c) ((memLoad32 M0 (w7c + 0xFFFFFFE4))) = 0)) ∨ ((aluEval .sltu (w78) ((memLoad32 M0 (w7c + 0xFFFFFFE8))) = 0))) ∧
      (((aluEval .sltu ((memLoad32 M0 (w7c + 0xFFFFFFEC))) (w3c) = 0)) ∨ ((aluEval .sltu ((memLoad32 M0 (w7c + 0xFFFFFFF0))) (w78) = 0))) ∧
      (((aluEval .sltu (w3c) ((memLoad32 M0 (q + 0x8))) = 0)) ∨ ((aluEval .sltu (w78) ((memLoad32 M0 (q + 0xC))) = 0))) ∧
      (((aluEval .sltu ((memLoad32 M0 (q + 0x10))) (w3c) = 0)) ∨ ((aluEval .sltu ((memLoad32 M0 (q + 0x14))) (w78) = 0))) ∧
      (((aluEval .sltu (w3c) ((memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 3))) = 0)) ∨ ((aluEval .sltu (w78) ((memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7))) = 0))) ∧
      (((aluEval .sltu ((memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 11))) (w3c) = 0)) ∨ ((aluEval .sltu ((memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) (w78) = 0))) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x3264 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1048 ∧
        reg n' (9 : Fin 32) = ((BitVec.ofNat 8 (root6_3_6.getD 0 0)).zeroExtend 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = x21'_5 ∧
        reg n' (22 : Fin 32) = rl'_5 ∧
        reg n' (23 : Fin 32) = (memLoad32 M0 (bp + 0x2C)) ∧
        reg n' (24 : Fin 32) = dg'_5 ∧
        reg n' (25 : Fin 32) = (memLoad32 M0 (bp + 0x28)) ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8'_5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc'_5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = (le4 (sha256 (memBytes M0 (ckp) (((BitVec.ofNat 32 ix7_1_1)).toNat) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4850) (1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D7) (1) ++ memBytes M0 ((memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x18))) (32))) 0) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = (memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x1C)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (bs7_2.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((aluEval .xor ((BitVec.ofNat 32 (((((ckl).toNat) - (ix7_1_1 + 1)) - (ix17_1_1 + 1)) - (ix25_1_1 + 1)) - BitVec.ofNat 32 (ix33_1_1 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28'_5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = ((w30'_5) &&& BitVec.ofNat 32 0x1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30'_5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = (memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x18)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38'_5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40'_5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (BitVec.ofNat 32 ix7_1_1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c'_5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (memLoad32 M0 (q'_3 + 0x20)) ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = (memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 3)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = (memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = (memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 11)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1034) = (memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15)) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = BitVec.ofNat 8 (sg'_5.getD 0 0) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1048) = ((BitVec.ofNat 8 (bs7_2.getD 0 0)).zeroExtend 32).extractLsb' 0 8 ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (bs7_2.getD (1 + j) 0)) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1049 + j)) = BitVec.ofNat 8 (bs7_2.getD (1 + j) 0)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (memLoad32 M0 (q'_3 + 0x20)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1038) = (memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x18)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x103C) = (memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x1C)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = w60'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) = w70'_2 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6_3_6.getD 0 0) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 8 (root6_3_6.getD 0 0) ∧
        SvKeepL B n0.mem n'.mem [(0x24, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10), (0x5C, 0x4), (0x20, 0x4), (0x38, 0x4), (0x60, 0x4), (0x70, 0x4), (0x420, 0x60), (0x1380, 0x8), (0x1C, 0x4), (0x320, 0x1F), (0x80, 0x4), (0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x1380, 0x20), (0x30, 0x4), (0x14, 0x4), (0x2C, 0x4), (0x40, 0x4), (0x28, 0x4), (0xC, 0x4), (0x8, 0x4), (0x1380, 0x4), (0x420, 0x8), (0x200, 0x3), (0x10, 0x4), (0x1480, 0x3F), (0x421, 0x3F), (0x420, 0x1), (0x240, 0x13), (0x1320, 0x1F), (0x1025, 0x13), (0x1038, 0x4), (0x103C, 0x4), (0x1048, 0x1), (0x1049, 0x1F), (0x1020, 0x4), (0x1024, 0x1), (0x1040, 0x4), (0x1044, 0x4), (0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x21), (0x1481, 0x1F), (0x1480, 0x1)]) := by
  rcases sv_seg_ck F E0 V0 hret hO s0 M0 fM g0_2 g0_10 g0_18 g0_19 g0_21 g0_22 g0_23 g0_24 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 CK0 hckp hckl ckp_in4 ckl_in4 a_ckp a_ckl ck_in with e | ⟨x1_0, ix7_1_1, x1_1, ix17_1_1, x1_2, ix25_1_1, x1_3, ix33_1_1, x1_4, x1_5, x1_6, x1_7, n1, c1, fR1, s1, E1, V1, r1_3, r1_4, r1_2, r1_8, r1_9, r1_a0, r1_18, r1_19, r1_21, r1_22, r1_23, r1_24, r1_25, r1_26, r1_27, w1_20, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_3c, w1_40, w1_44, w1_48, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_74, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, w1_428, w1_aa0, w1_aa4, w1_a20, w1_a24, w1_a28, w1_a2c, w1_a30, w1_a34, w1_a38, w1_a3c, w1_42c, K1_L⟩
  · exact .inl e
  rcases sv_ckdloop_run F hret hO M0 E1 V1 s1 fR1 r1_2 r1_8 r1_9 r1_a0 r1_18 r1_19 r1_21 r1_22 r1_23 r1_24 r1_25 r1_26 r1_27 ((K1_L.w32 (by decide) (by decide)).trans w0_8) ((K1_L.w32 (by decide) (by decide)).trans w0_c) ((K1_L.w32 (by decide) (by decide)).trans w0_10) ((K1_L.w32 (by decide) (by decide)).trans w0_14) ((K1_L.w32 (by decide) (by decide)).trans w0_18) ((K1_L.w32 (by decide) (by decide)).trans w0_1c) w1_20 w1_24 w1_28 w1_2c w1_30 w1_34 w1_38 w1_3c w1_40 w1_44 w1_48 w1_4c w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_74 w1_78 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_98 w1_9c w1_a0 w1_a4 w1_a8 w1_ac w1_b0 w1_b4 w1_b8 w1_bc w1_c0 w1_c4 w1_c8 w1_cc w1_d0 w1_d4 w1_d8 w1_dc w1_e0 w1_e4 w1_e8 w1_ec w1_f0 w1_f4 w1_f8 w1_fc w1_100 w1_104 w1_108 w1_10c w1_110 w1_114 w1_118 w1_11c w1_120 w1_124 w1_128 w1_12c w1_130 w1_428 w1_aa0 w1_aa4 ((((ck_in).nlRest x1_1).nlLine x1_2).ofNatLen) (((((ck_in).nlRest x1_1).nlRest x1_2).nlLine x1_3).ofNatLen) CK0 with e | ⟨c'_2, p'_2, x21'_2, w60'_2, w70'_2, x2_0, x2_1, bs7_2, x2_2, x2_3, n2, c2, s2, E2, V2, fR2, r2_2, r2_3, r2_4, r2_9, r2_18, r2_19, r2_21, r2_22, r2_23, r2_24, r2_25, r2_26, r2_27, w2_8, w2_c, w2_10, w2_14, w2_18, w2_1c, w2_20, w2_24, w2_28, w2_2c, w2_30, w2_34, w2_38, w2_3c, w2_40, w2_44, w2_48, w2_4c, w2_50, w2_54, w2_58, w2_5c, w2_60, w2_64, w2_68, w2_6c, w2_70, w2_74, w2_78, w2_7c, w2_80, w2_84, w2_88, w2_8c, w2_90, w2_94, w2_98, w2_9c, w2_a0, w2_a4, w2_a8, w2_ac, w2_b0, w2_b4, w2_b8, w2_bc, w2_c0, w2_c4, w2_c8, w2_cc, w2_d0, w2_d4, w2_d8, w2_dc, w2_e0, w2_e4, w2_e8, w2_ec, w2_f0, w2_f4, w2_f8, w2_fc, w2_100, w2_104, w2_108, w2_10c, w2_110, w2_114, w2_118, w2_11c, w2_120, w2_124, w2_128, w2_12c, w2_130, w2_aa0, w2_aa4, w2_1384, b2_420, b2_1380, q2_320, q2_420, K2_L⟩
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  rcases sv_csearch_st F hret hO M0 (fun _ _ _ h => svCnt_zero Prod.fst (BitVec.ofNat 32 0x100) 0xFFFFFFE0 (by intro _; rfl) rfl (by decide) (congrArg Prod.fst h)) E2 V2 s2 fR2 r2_2 r2_9 r2_18 r2_19 r2_21 r2_22 r2_23 r2_24 r2_25 r2_26 r2_27 w2_8 w2_c w2_10 w2_14 w2_18 w2_1c w2_20 w2_24 w2_28 w2_2c w2_30 w2_34 w2_38 w2_3c w2_40 w2_44 w2_48 w2_4c w2_50 w2_54 w2_58 w2_5c w2_60 w2_64 w2_68 w2_6c w2_70 w2_78 w2_7c w2_80 w2_84 w2_88 w2_8c w2_90 w2_94 w2_98 w2_9c w2_a0 w2_a4 w2_a8 w2_ac w2_b0 w2_b4 w2_b8 w2_bc w2_c0 w2_c4 w2_c8 w2_cc w2_d0 w2_d4 w2_d8 w2_dc w2_e0 w2_e4 w2_e8 w2_ec w2_f0 w2_f4 w2_f8 w2_fc w2_100 w2_104 w2_108 w2_10c w2_110 w2_114 w2_118 w2_11c w2_120 w2_124 w2_128 w2_12c w2_130 rfl ((K2_L.w32 (by decide) (by decide)).trans w1_a20) ((K2_L.w32 (by decide) (by decide)).trans w1_a24) ((K2_L.w32 (by decide) (by decide)).trans w1_a28) ((K2_L.w32 (by decide) (by decide)).trans w1_a2c) ((K2_L.w32 (by decide) (by decide)).trans w1_a30) ((K2_L.w32 (by decide) (by decide)).trans w1_a34) ((K2_L.w32 (by decide) (by decide)).trans w1_a38) ((K2_L.w32 (by decide) (by decide)).trans w1_a3c) w2_aa0 w2_aa4 q2_320 (fun i hi c'_3 q'_3 w80'_3 h => ⟨(svCnt_ne Prod.fst (BitVec.ofNat 32 0x100) 0xFFFFFFE0 (by intro _; rfl) rfl (by decide) hi (congrArg Prod.fst h)), (H' i hi c'_3 q'_3 w80'_3 h).1, (H' i hi c'_3 q'_3 w80'_3 h).2.1, (H' i hi c'_3 q'_3 w80'_3 h).2.2.1, (H' i hi c'_3 q'_3 w80'_3 h).2.2.2.1, (H' i hi c'_3 q'_3 w80'_3 h).2.2.2.2, (((ck_in).nlLine x1_1).ofNatLen)⟩) with e | ⟨k_3, x3_0, x3_1, c'_3, q'_3, w80'_3, x3_2, x3_3, n3, c3, s3, E3, V3, fR3, r3_2, r3_3, r3_4, r3_9, r3_18, r3_19, r3_21, r3_22, r3_23, r3_24, r3_25, r3_26, r3_27, w3_8, w3_c, w3_10, w3_14, w3_18, w3_1c, w3_20, w3_24, w3_28, w3_2c, w3_30, w3_34, w3_38, w3_3c, w3_40, w3_44, w3_48, w3_4c, w3_50, w3_54, w3_58, w3_5c, w3_60, w3_64, w3_68, w3_6c, w3_70, w3_78, w3_7c, w3_80, w3_84, w3_88, w3_8c, w3_90, w3_94, w3_98, w3_9c, w3_a0, w3_a4, w3_a8, w3_ac, w3_b0, w3_b4, w3_b8, w3_bc, w3_c0, w3_c4, w3_c8, w3_cc, w3_d0, w3_d4, w3_d8, w3_dc, w3_e0, w3_e4, w3_e8, w3_ec, w3_f0, w3_f4, w3_f8, w3_fc, w3_100, w3_104, w3_108, w3_10c, w3_110, w3_114, w3_118, w3_11c, w3_120, w3_124, w3_128, w3_12c, w3_130, w3_428, w3_a20, w3_a24, w3_a28, w3_a2c, w3_a30, w3_a34, w3_a38, w3_a3c, w3_aa0, w3_aa4, q3_320, K3_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  rcases sv_cs1 (op := 0) (ol := 0) F E3 V3 hret hO s3 M0 fR3 r3_2 r3_9 r3_18 r3_19 r3_21 r3_22 r3_23 r3_24 r3_25 r3_26 r3_27 w3_8 w3_c w3_10 w3_14 w3_18 w3_1c w3_20 w3_24 w3_28 w3_2c w3_30 w3_34 w3_38 w3_3c w3_40 w3_44 w3_48 w3_4c w3_50 w3_54 w3_58 w3_5c w3_60 w3_64 w3_68 w3_6c w3_70 w3_78 w3_7c w3_80 w3_84 w3_88 w3_8c w3_90 w3_94 w3_98 w3_9c w3_a0 w3_a4 w3_a8 w3_ac w3_b0 w3_b4 w3_b8 w3_bc w3_c0 w3_c4 w3_c8 w3_cc w3_d0 w3_d4 w3_d8 w3_dc w3_e0 w3_e4 w3_e8 w3_ec w3_f0 w3_f4 w3_f8 w3_fc w3_100 w3_104 w3_108 w3_10c w3_110 w3_114 w3_118 w3_11c w3_120 w3_124 w3_128 w3_12c w3_130 w3_428 w3_a20 w3_a24 w3_a28 w3_a2c w3_a30 w3_a34 w3_a38 w3_a3c w3_aa0 w3_aa4 q3_320 S2 KS rfl rfl (kp_in4 k_3 x3_0 c'_3 q'_3 w80'_3 x3_2) (kw_in4 k_3 x3_0 c'_3 q'_3 w80'_3 x3_2) (a_kp k_3 x3_0 c'_3 q'_3 w80'_3 x3_2) (a_kw k_3 x3_0 c'_3 q'_3 w80'_3 x3_2) (kp_in k_3 x3_0 c'_3 q'_3 w80'_3 x3_2) (((ck_in).nlLine x1_1).ofNatLen) with ⟨-, e⟩ | ⟨n4, c4, s4, E4, V4, fR4, r4_2, r4_3, r4_4, r4_9, r4_18, r4_19, r4_21, r4_22, r4_23, r4_24, r4_25, r4_26, r4_27, w4_8, w4_c, w4_10, w4_14, w4_18, w4_1c, w4_20, w4_24, w4_28, w4_2c, w4_30, w4_34, w4_38, w4_3c, w4_40, w4_44, w4_48, w4_4c, w4_50, w4_54, w4_58, w4_5c, w4_60, w4_64, w4_68, w4_6c, w4_70, w4_78, w4_7c, w4_80, w4_84, w4_88, w4_8c, w4_90, w4_94, w4_98, w4_9c, w4_a0, w4_a4, w4_a8, w4_ac, w4_b0, w4_b4, w4_b8, w4_bc, w4_c0, w4_c4, w4_c8, w4_cc, w4_d0, w4_d4, w4_d8, w4_dc, w4_e0, w4_e4, w4_e8, w4_ec, w4_f0, w4_f4, w4_f8, w4_fc, w4_100, w4_104, w4_108, w4_10c, w4_110, w4_114, w4_118, w4_11c, w4_120, w4_124, w4_128, w4_12c, w4_130, w4_420, w4_424, w4_428, w4_42c, w4_430, w4_434, w4_438, w4_43c, w4_a20, w4_a24, w4_a28, w4_a2c, w4_a30, w4_a34, w4_a38, w4_a3c, w4_aa0, w4_aa4, w4_1380, q4_320, K4_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3))) (by rw [r3_3, r2_3, r1_3]) (by rw [r3_4, r2_4, r1_4])
      (fun x hx => (fR3 x hx).trans (fM x hx).symm) e)
  rcases sv_cosigloop_st (sgp := 0) (op := 0) (ol := 0) F hret hO M0 (Nat.le_refl _) E4 V4 s4 fR4 r4_2 r4_9 r4_18 r4_19 r4_21 r4_22 r4_23 r4_24 r4_25 r4_26 r4_27 w4_8 w4_c w4_14 w4_18 w4_1c w4_20 w4_24 w4_28 w4_2c w4_30 w4_34 w4_38 w4_3c w4_40 w4_44 w4_48 w4_4c w4_50 w4_54 w4_58 w4_5c w4_60 w4_64 w4_68 w4_6c w4_70 w4_78 w4_7c w4_80 w4_84 w4_88 w4_8c w4_90 w4_94 w4_98 w4_9c w4_a0 w4_a4 w4_a8 w4_ac w4_b0 w4_b4 w4_b8 w4_bc w4_c0 w4_c4 w4_c8 w4_cc w4_d0 w4_d4 w4_d8 w4_dc w4_e0 w4_e4 w4_e8 w4_ec w4_f0 w4_f4 w4_f8 w4_fc w4_100 w4_104 w4_108 w4_10c w4_110 w4_114 w4_118 w4_11c w4_120 w4_124 w4_128 w4_12c w4_130 w4_a20 w4_a24 w4_a28 w4_a2c w4_a30 w4_a34 w4_a38 w4_a3c w4_aa0 w4_aa4 q4_320 ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans ((K1_L.b8 (by decide) (by decide)).trans b0_10)))) (fun j hj => (K4_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K3_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K2_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K1_L.range (by decide) (by decide) j hj).trans (q0_1480 j hj)) j hj)) j hj)) j hj)) (by rw [svSubNat_toNat (by have := ((((ck_in).nlRest x1_1).nlRest x1_2).nlRest x1_3).lo; omega) (by have := (nlScan_lt _ _ _ x1_4).2; omega)]; exact ((((ck_in).nlRest x1_1).nlRest x1_2).nlRest x1_3).nlRest x1_4) CK0 (((ck_in).nlLine x1_1).ofNatLen) EE0 RS hiv (pk_in k_3 x3_0 c'_3 q'_3 w80'_3 x3_2) ((ck_in).shrink (svNotAdd_le (by have := (ck_in).lo; have := (nlScan_lt _ _ _ x1_1).2; have := (nlScan_lt _ _ _ x1_2).2; have := (nlScan_lt _ _ _ x1_3).2; have := (nlScan_lt _ _ _ x1_4).2; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow] at *; omega))) ((((ck_in).shrink (svNotAdd_le (by have := (ck_in).lo; have := (nlScan_lt _ _ _ x1_1).2; have := (nlScan_lt _ _ _ x1_2).2; have := (nlScan_lt _ _ _ x1_3).2; have := (nlScan_lt _ _ _ x1_4).2; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow] at *; omega)))).len_lt) with e | ⟨k_5, c'_5, x21'_5, rl'_5, rp'_5, dg'_5, w8'_5, wc'_5, w28'_5, w2c'_5, w30'_5, w38'_5, w40'_5, w5c'_5, sg'_5, x5_0, x5_1, x5_2, x5_3, n5, c5, s5, E5, V5, fR5, r5_2, r5_3, r5_4, r5_9, r5_18, r5_19, r5_21, r5_22, r5_23, r5_24, r5_25, r5_26, r5_27, w5_8, w5_c, w5_14, w5_18, w5_1c, w5_20, w5_24, w5_28, w5_2c, w5_30, w5_34, w5_38, w5_3c, w5_40, w5_44, w5_48, w5_4c, w5_50, w5_54, w5_58, w5_5c, w5_60, w5_64, w5_68, w5_6c, w5_70, w5_78, w5_7c, w5_80, w5_84, w5_88, w5_8c, w5_90, w5_94, w5_98, w5_9c, w5_a0, w5_a4, w5_a8, w5_ac, w5_b0, w5_b4, w5_b8, w5_bc, w5_c0, w5_c4, w5_c8, w5_cc, w5_d0, w5_d4, w5_d8, w5_dc, w5_e0, w5_e4, w5_e8, w5_ec, w5_f0, w5_f4, w5_f8, w5_fc, w5_100, w5_104, w5_108, w5_10c, w5_110, w5_114, w5_118, w5_11c, w5_120, w5_124, w5_128, w5_12c, w5_130, w5_a20, w5_a24, w5_a28, w5_a2c, w5_a30, w5_a34, w5_a38, w5_a3c, w5_aa0, w5_aa4, b5_10, q5_320, q5_421, q5_1480, K5_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4)))) (by rw [r4_3, r3_3, r2_3, r1_3]) (by rw [r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR4 x hx).trans (fM x hx).symm) e)
  rcases sv_seg_win F E5 V5 hret hO s5 M0 fR5 r5_2 r5_9 r5_18 r5_19 r5_21 r5_22 r5_23 r5_24 r5_25 r5_26 r5_27 w5_8 w5_c w5_14 w5_18 w5_1c w5_20 w5_24 w5_28 w5_2c w5_30 w5_34 w5_38 w5_3c w5_40 w5_44 w5_48 w5_4c w5_50 w5_54 w5_58 w5_5c w5_60 w5_64 w5_68 w5_6c w5_70 w5_78 w5_7c w5_80 w5_84 w5_88 w5_8c w5_90 w5_94 w5_98 w5_9c w5_a0 w5_a4 w5_a8 w5_ac w5_b0 w5_b4 w5_b8 w5_bc w5_c0 w5_c4 w5_c8 w5_cc w5_d0 w5_d4 w5_d8 w5_dc w5_e0 w5_e4 w5_e8 w5_ec w5_f0 w5_f4 w5_f8 w5_fc w5_100 w5_104 w5_108 w5_10c w5_110 w5_114 w5_118 w5_11c w5_120 w5_124 w5_128 w5_12c w5_130 w5_a20 w5_a24 w5_a28 w5_a2c w5_a30 w5_a34 w5_a38 w5_a3c w5_aa0 w5_aa4 q5_320 b5_10 q5_1480 (lid_in k_3 x3_0 c'_3 q'_3 w80'_3 x3_2) x3_3 rfl rfl lih_in lil_in a_lih a_lil ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans w2_74))) S2 KS RS RK0 dgi_in sig_in crt_in pp_in4 pl_in4 a_pp a_pl pp_in ii2h ai2h ii2l ai2l ii3h ai3h ii3l ai3l it4h at4h it4l at4l it5h at5h it5l at5l with e | ⟨x6_0, root6_3_6, x6_1, x6_2, x6_3, x6_4, x6_5, x6_6, x6_7, x6_8, x6_9, x6_10, n6, c6, fR6, s6, E6, V6, r6_3, r6_4, r6_2, r6_8, r6_9, r6_18, r6_19, r6_21, r6_22, r6_23, r6_24, r6_25, r6_26, r6_27, w6_8, w6_c, w6_14, w6_18, w6_1c, w6_20, w6_24, w6_28, w6_2c, w6_30, w6_34, w6_38, w6_3c, w6_40, w6_44, w6_48, w6_4c, w6_50, w6_54, w6_58, w6_5c, w6_60, w6_64, w6_68, w6_6c, w6_70, w6_74, w6_78, w6_7c, w6_80, w6_84, w6_88, w6_8c, w6_90, w6_94, w6_98, w6_9c, w6_a0, w6_a4, w6_a8, w6_ac, w6_b0, w6_b4, w6_b8, w6_bc, w6_c0, w6_c4, w6_c8, w6_cc, w6_d0, w6_d4, w6_d8, w6_dc, w6_e0, w6_e4, w6_e8, w6_ec, w6_f0, w6_f4, w6_f8, w6_fc, w6_100, w6_104, w6_108, w6_10c, w6_110, w6_114, w6_118, w6_11c, w6_120, w6_124, w6_128, w6_12c, w6_130, w6_a20, w6_a24, w6_a28, w6_a2c, w6_a30, w6_a34, w6_a38, w6_a3c, w6_aa0, w6_aa4, w6_1028, w6_102c, w6_1030, w6_1034, b6_10, b6_1048, q6_320, q6_1049, w6_1020, w6_1038, w6_103c, w6_1040, w6_1044, b6_420, b6_421, b6_1480, K6_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5))))) (by rw [r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR5 x hx).trans (fM x hx).symm) e)
  exact .inr ⟨x1_0, ix7_1_1, x1_1, ix17_1_1, x1_2, ix25_1_1, x1_3, ix33_1_1, x1_4, x1_5, x1_6, x1_7, c'_2, p'_2, x21'_2, w60'_2, w70'_2, x2_0, x2_1, bs7_2, x2_2, x2_3, k_3, x3_0, x3_1, c'_3, q'_3, w80'_3, x3_2, x3_3, k_5, c'_5, x21'_5, rl'_5, rp'_5, dg'_5, w8'_5, wc'_5, w28'_5, w2c'_5, w30'_5, w38'_5, w40'_5, w5c'_5, sg'_5, x5_0, x5_1, x5_2, x5_3, x6_0, root6_3_6, x6_1, x6_2, x6_3, x6_4, x6_5, x6_6, x6_7, x6_8, x6_9, x6_10, n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6))))), fR6, s6, E6, V6,
    by rw [r6_3, r5_3, r4_3, r3_3, r2_3, r1_3], by rw [r6_4, r5_4, r4_4, r3_4, r2_4, r1_4], r6_2, r6_8, r6_9, r6_18, r6_19, r6_21, r6_22, r6_23, r6_24, r6_25, r6_26, r6_27, w6_8, w6_c, w6_14, w6_18, w6_1c, w6_20, w6_24, w6_28, w6_2c, w6_30, w6_34, w6_38, w6_3c, w6_40, w6_44, w6_48, w6_4c, w6_50, w6_54, w6_58, w6_5c, w6_60, w6_64, w6_68, w6_6c, w6_70, w6_74, w6_78, w6_7c, w6_80, w6_84, w6_88, w6_8c, w6_90, w6_94, w6_98, w6_9c, w6_a0, w6_a4, w6_a8, w6_ac, w6_b0, w6_b4, w6_b8, w6_bc, w6_c0, w6_c4, w6_c8, w6_cc, w6_d0, w6_d4, w6_d8, w6_dc, w6_e0, w6_e4, w6_e8, w6_ec, w6_f0, w6_f4, w6_f8, w6_fc, w6_100, w6_104, w6_108, w6_10c, w6_110, w6_114, w6_118, w6_11c, w6_120, w6_124, w6_128, w6_12c, w6_130, w6_a20, w6_a24, w6_a28, w6_a2c, w6_a30, w6_a34, w6_a38, w6_a3c, w6_aa0, w6_aa4, w6_1028, w6_102c, w6_1030, w6_1034, b6_10, b6_1048, q6_320, q6_1049, w6_1020, w6_1038, w6_103c, w6_1040, w6_1044, b6_420, b6_421, b6_1480, ((((((K1_L).trans K2_L).trans K3_L).trans K4_L).trans K5_L).trans K6_L).mono (by decide)⟩

end C3.RV32.Sv
