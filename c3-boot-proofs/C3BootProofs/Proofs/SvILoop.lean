import C3BootProofs.Proofs.SvSeg
import C3BootProofs.Proofs.SvImiss

/-!
# `sigstore::verify`: The search of the root's Fulcio intermediates for the leaf's issuer, over `k` entries that don't match

Written by `scripts/gen-sv-loop.py` from `sv_imiss`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The search of the root's Fulcio intermediates for the leaf's issuer, over `k` entries that don't match. -/
theorem sv_iloop {B out bp x9 x21 x26 il ip : Word} {w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w60 w64 w68 w6c w70 w74 w78 w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word}
    (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8) :
    ∀ (k : Nat) {c q : Word} {n0 : Machine},
    (E0 : SvCode n0.mem) →
    (V0 : SvSaves B n0.mem v) →
    (s0 : St n0.mem SV n0 0xAE2 (reg n0)) →
    (fM : ∀ x, SvR B x → n0.mem x = M0 x) →
    (g0_2 : reg n0 sp = B + 0x21A0) →
    (g0_9 : reg n0 (9 : Fin 32) = x9) →
    (g0_18 : reg n0 (18 : Fin 32) = out) →
    (g0_19 : reg n0 (19 : Fin 32) = bp) →
    (g0_20 : reg n0 (20 : Fin 32) = c) →
    (g0_21 : reg n0 (21 : Fin 32) = x21) →
    (g0_25 : reg n0 (25 : Fin 32) = il) →
    (g0_26 : reg n0 (26 : Fin 32) = x26) →
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20) →
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24) →
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28) →
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c) →
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30) →
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34) →
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38) →
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c) →
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40) →
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44) →
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48) →
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c) →
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50) →
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54) →
    (w0_58 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58) →
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = ip) →
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60) →
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64) →
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68) →
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c) →
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70) →
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74) →
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78) →
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = q) →
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80) →
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84) →
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88) →
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c) →
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90) →
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94) →
    (w0_98 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98) →
    (w0_9c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c) →
    (w0_a0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0) →
    (w0_a4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4) →
    (w0_a8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8) →
    (w0_ac : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac) →
    (w0_b0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0) →
    (w0_b4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4) →
    (w0_b8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8) →
    (w0_bc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc) →
    (w0_c0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0) →
    (w0_c4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4) →
    (w0_c8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8) →
    (w0_cc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc) →
    (w0_d0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0) →
    (w0_d4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4) →
    (w0_d8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8) →
    (w0_dc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc) →
    (w0_e0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0) →
    (w0_e4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4) →
    (w0_e8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8) →
    (w0_ec : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec) →
    (w0_f0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0) →
    (w0_f4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4) →
    (w0_f8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8) →
    (w0_fc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc) →
    (w0_100 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100) →
    (w0_104 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104) →
    (w0_108 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108) →
    (w0_10c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c) →
    (w0_110 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110) →
    (w0_114 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114) →
    (w0_118 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118) →
    (w0_11c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c) →
    (w0_120 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120) →
    (w0_124 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124) →
    (w0_128 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128) →
    (w0_12c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c) →
    (w0_130 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130) →
    (∀ i, i < k → ∀ c' q', c' = (svIter (fun x => (x) + BitVec.ofNat 32 0xFFFFFFE0) i c) → q' = (svIter (fun x => (x) + BitVec.ofNat 32 0x20) i q) → ((c') ≠ 0) ∧ (SvIn B ((q') + 0xFFFFFFFC) 4) ∧ (SvIn B ((q') + 0x0) 4) ∧ (((q') + 0xFFFFFFFC).toNat % 4 = 0) ∧ (((q') + 0x0).toNat % 4 = 0) ∧ (SvIn B (memLoad32 M0 ((q') + 0xFFFFFFFC)) (memLoad32 M0 ((q') + 0x0)).toNat) ∧ (SvIn B ip il.toNat) ∧ (¬ memBytes M0 (memLoad32 M0 ((q') + 0xFFFFFFFC)) (memLoad32 M0 ((q') + 0x0)).toNat = memBytes M0 ip il.toNat)) →
    SvErrRet B out v n0 ∨ ∃ n' c' q', Steps n0 n' ∧ c' = (svIter (fun x => (x) + BitVec.ofNat 32 0xFFFFFFE0) k c) ∧ q' = (svIter (fun x => (x) + BitVec.ofNat 32 0x20) k q) ∧
      reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
      SvKeepL B n0.mem n'.mem [(0x7C, 0x4)] ∧
      SvCode n'.mem ∧
      SvSaves B n'.mem v ∧
      St n'.mem SV n' 0xAE2 (reg n') ∧
      (∀ x, SvR B x → n'.mem x = M0 x) ∧
      reg n' sp = B + 0x21A0 ∧
      reg n' (9 : Fin 32) = x9 ∧
      reg n' (18 : Fin 32) = out ∧
      reg n' (19 : Fin 32) = bp ∧
      reg n' (20 : Fin 32) = (c') ∧
      reg n' (21 : Fin 32) = x21 ∧
      reg n' (25 : Fin 32) = il ∧
      reg n' (26 : Fin 32) = x26 ∧
      reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = ip ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (q') ∧
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
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by
  intro k
  induction k with
  | zero =>
    intro c q n0 E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_25 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 _
    exact .inr ⟨n0, c, q, .refl _, (svIter_zero _ _).symm, (svIter_zero _ _).symm, rfl, rfl, SvKeepL.refl.mono (by decide), E0, V0, s0, fM, g0_2, g0_9, g0_18, g0_19, g0_20, g0_21, g0_25, g0_26, g0_27, w0_24, w0_28, w0_2c, w0_30, w0_34, w0_38, w0_3c, w0_40, w0_44, w0_48, w0_4c, w0_50, w0_54, w0_58, w0_5c, w0_60, w0_64, w0_68, w0_6c, w0_70, w0_74, w0_78, w0_7c, w0_80, w0_84, w0_88, w0_8c, w0_90, w0_94, w0_98, w0_9c, w0_a0, w0_a4, w0_a8, w0_ac, w0_b0, w0_b4, w0_b8, w0_bc, w0_c0, w0_c4, w0_c8, w0_cc, w0_d0, w0_d4, w0_d8, w0_dc, w0_e0, w0_e4, w0_e8, w0_ec, w0_f0, w0_f4, w0_f8, w0_fc, w0_100, w0_104, w0_108, w0_10c, w0_110, w0_114, w0_118, w0_11c, w0_120, w0_124, w0_128, w0_12c, w0_130⟩
  | succ k ih =>
    intro c q n0 E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_25 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 H
    obtain ⟨hc, es_in, el_in, a_subj, a_slen, s_in, i_in, hm⟩ := H 0 (Nat.succ_pos k) c q (svIter_zero _ _).symm (svIter_zero _ _).symm
    rcases sv_imiss (B := B) (out := out) (bp := bp) (x9 := x9) (x21 := x21) (x26 := x26) (il := il) (c := c) (q := q) (ip := ip) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (v := v) F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_25 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 hc rfl rfl es_in el_in a_subj a_slen s_in i_in hm with ⟨-, e⟩ | ⟨x1_0, n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_9, r1_18, r1_19, r1_20, r1_21, r1_25, r1_26, r1_27, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_3c, w1_40, w1_44, w1_48, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_74, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, K1_L⟩
    · exact .inl e
    rcases ih E1 V1 s1 fR1 r1_2 r1_9 r1_18 r1_19 r1_20 r1_21 r1_25 r1_26 r1_27 w1_24 w1_28 w1_2c w1_30 w1_34 w1_38 w1_3c w1_40 w1_44 w1_48 w1_4c w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_74 w1_78 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_98 w1_9c w1_a0 w1_a4 w1_a8 w1_ac w1_b0 w1_b4 w1_b8 w1_bc w1_c0 w1_c4 w1_c8 w1_cc w1_d0 w1_d4 w1_d8 w1_dc w1_e0 w1_e4 w1_e8 w1_ec w1_f0 w1_f4 w1_f8 w1_fc w1_100 w1_104 w1_108 w1_10c w1_110 w1_114 w1_118 w1_11c w1_120 w1_124 w1_128 w1_12c w1_130 (fun i hi c' q' e0 e1 => H (i + 1) (Nat.succ_lt_succ hi) c' q' (e0.trans (svIter_succ _ _ _).symm) (e1.trans (svIter_succ _ _ _).symm)) with e | ⟨n', c', q', cs, e0, e1, h3, h4, hk, rest⟩
    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
    · exact .inr ⟨n', c', q', c1.trans cs, (e0.trans (svIter_succ _ _ _).symm), (e1.trans (svIter_succ _ _ _).symm), h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), rest⟩

end C3.RV32.Sv
