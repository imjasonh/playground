import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvSegCosig
import C3BootProofs.Proofs.SvCsx

/-!
# `sigstore::verify`: the checkpoint's signature loop

Written by `scripts/gen-sv-relloop.py` from `sv_seg_cosig` and `sv_csx`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option linter.unusedVariables false in
/-- One more signature line, from state `s` to `s'`: there are bytes left, and the next line is well formed. -/
def sv_cosigStep (dp B out bp x26 q : Word) (rt : Bytes) (w14 w18 w20 w24 w34 w3c w44 w48 w4c w50 w54 w58 w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 wa20 wa24 wa28 wa2c wa30 wa34 wa38 wa3c waa4 : Word) (v : Nat → Word) (sgp op ol : Word) (M0 : Word → BitVec 8) : Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Bytes → Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Bytes → Prop :=
  fun s s' => s.2.2.2.2.2.2.2.2.2.2.2.2.1 ≠ 0 ∧ ∃ ix9_1, nlScan M0 ((s.2.2.2.2.2.2.2.2.2.2.1)) 0 (((s.2.2.2.2.2.2.2.2.2.2.2.2.1)).toNat) = some ix9_1 ∧ (4 ≤ ix9_1) ∧ (memBytes M0 (s.2.2.2.2.2.2.2.2.2.2.1) 4 = memBytes M0 (BitVec.ofNat 32 0x3FCC4855) 4) ∧ ∃ k_2, k_2 < ((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC).toNat ∧ (∀ i, i < k_2 → ∀ c'_2 pa'_2, (c'_2, pa'_2) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x1, ((s.2)) + BitVec.ofNat 32 0x1)) i ((BitVec.ofNat 32 0x0), (((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4)) → ¬ (M0 pa'_2 = 0x20)) ∧ ∃ c'_2 pa'_2, (c'_2, pa'_2) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x1, ((s.2)) + BitVec.ofNat 32 0x1)) k_2 ((BitVec.ofNat 32 0x0), (((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4)) ∧ (M0 pa'_2 = 0x20) ∧ c'_2 = (BitVec.ofNat 32 0x0) + BitVec.ofNat 32 (k_2 * 1) ∧ pa'_2 = (((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4) + BitVec.ofNat 32 (k_2 * 1) ∧ (c'_2 ≠ 0) ∧ (((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)) &&& BitVec.ofNat 32 0x3 = 0) ∧ ∃ dg'_3 pg'_3 gi'_3, (dg'_3, pg'_3, gi'_3) = svIter (fun s => (((s.2.1)) + BitVec.ofNat 32 0x4, ((s.2.1)) + BitVec.ofNat 32 0x4, ((s.2.2)) + BitVec.ofNat 32 0x1)) ((((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)) >>> 2).toNat) ((s.2.2.2.2.1), (((((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4)) + ((c'_2) + BitVec.ofNat 32 0x1)), (BitVec.ofNat 32 0x0)) ∧ (∀ i, i < ((((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)) >>> 2).toNat) → ∀ dg'_3 pg'_3 gi'_3, (dg'_3, pg'_3, gi'_3) = svIter (fun s => (((s.2.1)) + BitVec.ofNat 32 0x4, ((s.2.1)) + BitVec.ofNat 32 0x4, ((s.2.2)) + BitVec.ofNat 32 0x1)) i ((s.2.2.2.2.1), (((((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4)) + ((c'_2) + BitVec.ofNat 32 0x1)), (BitVec.ofNat 32 0x0)) → ((((M0 (pg'_3) = 0x3D) ∧ ((gi'_3) + BitVec.ofNat 32 0x1 = (((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)) >>> 2)) ∧ ∃ bq27, base64Decode (memBytes M0 pg'_3 4) = some bq27 ∧ (bq27.length ≤ 3)) ∨ ((¬ (M0 (pg'_3) = 0x3D)) ∧ (M0 ((pg'_3) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi'_3) + BitVec.ofNat 32 0x1 = (((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)) >>> 2)) ∧ ∃ bq33, base64Decode (memBytes M0 pg'_3 4) = some bq33 ∧ (bq33.length ≤ 3)) ∨ ((¬ (M0 (pg'_3) = 0x3D)) ∧ (¬ (M0 ((pg'_3) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (M0 (((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi'_3) + BitVec.ofNat 32 0x1 = (((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)) >>> 2)) ∧ ∃ bq39, base64Decode (memBytes M0 pg'_3 4) = some bq39 ∧ (bq39.length ≤ 3)) ∨ ((¬ (M0 (pg'_3) = 0x3D)) ∧ (¬ (M0 ((pg'_3) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 (((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (M0 ((((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi'_3) + BitVec.ofNat 32 0x1 = (((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)) >>> 2)) ∧ ∃ bq45, base64Decode (memBytes M0 pg'_3 4) = some bq45 ∧ (bq45.length ≤ 3)) ∨ ((¬ (M0 (pg'_3) = 0x3D)) ∧ (¬ (M0 ((pg'_3) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 (((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 ((((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ ∃ bq44, base64Decode (memBytes M0 pg'_3 4) = some bq44 ∧ (bq44.length ≤ 3))))) ∧ ∃ cm_sg_3 : Bytes, ∃ cm_w30_3 : Word, ((False) ∨ (False) ∨ (False) ∨ (∃ bs, base64Decode (memBytes M0 (((((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4)) + ((c'_2) + BitVec.ofNat 32 0x1)) ((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)).toNat) = some bs ∧ (¬ (((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC) = ((c'_2) + BitVec.ofNat 32 0x1))) ∧ (memBytes M0 (((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4) c'_2.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 (((((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4)) + ((c'_2) + BitVec.ofNat 32 0x1)) ((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)).toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (bs.length < 4) ∧ cm_sg_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.2) ∧ cm_w30_3 = (s.2.2.2.2.2.2.2.2.2.1)) ∨ (∃ bs, base64Decode (memBytes M0 (((((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4)) + ((c'_2) + BitVec.ofNat 32 0x1)) ((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)).toNat) = some bs ∧ (¬ (((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC) = ((c'_2) + BitVec.ofNat 32 0x1))) ∧ (memBytes M0 (((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4) c'_2.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 (((((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4)) + ((c'_2) + BitVec.ofNat 32 0x1)) ((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)).toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (¬ (bs.length < 4)) ∧ (le4 bs 0 = w14) ∧ (bs.length = 68) ∧ ((((s.2.2.2.2.2.2.2.2.2.1)) &&& BitVec.ofNat 32 0x1) = 0) ∧ cm_sg_3 = (bs.drop 4) ∧ cm_w30_3 = BitVec.ofNat 32 0x1) ∨ (False) ∨ (∃ bs, base64Decode (memBytes M0 (((((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4)) + ((c'_2) + BitVec.ofNat 32 0x1)) ((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)).toNat) = some bs ∧ (¬ (((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC) = ((c'_2) + BitVec.ofNat 32 0x1))) ∧ (memBytes M0 (((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4) c'_2.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 (((((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4)) + ((c'_2) + BitVec.ofNat 32 0x1)) ((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)).toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (¬ (bs.length < 4)) ∧ (¬ (le4 bs 0 = w14)) ∧ cm_sg_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.2) ∧ cm_w30_3 = (s.2.2.2.2.2.2.2.2.2.1)) ∨ ((¬ (((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC) = ((c'_2) + BitVec.ofNat 32 0x1))) ∧ (¬ (memBytes M0 (((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4) c'_2.toNat = memBytes M0 w48 w44.toNat)) ∧ cm_sg_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.2) ∧ cm_w30_3 = (s.2.2.2.2.2.2.2.2.2.1))) ∧ s' = (c'_2, (c'_2) + BitVec.ofNat 32 0x1, gi'_3, ((((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4)) + ((c'_2) + BitVec.ofNat 32 0x1), dg'_3, (aluEval .sll (((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)) >>> 2) (BitVec.ofNat 32 0x2)) + (((((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4)) + ((c'_2) + BitVec.ofNat 32 0x1)), ((((BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC)) - ((c'_2) + BitVec.ofNat 32 0x1)) >>> 2, ((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 0x4, ((s.2.2.2.2.2.2.2.2.2.1)) &&& BitVec.ofNat 32 0x1, cm_w30_3, ((s.2.2.2.2.2.2.2.2.2.2.1)) + BitVec.ofNat 32 (ix9_1 + 1), (BitVec.ofNat 32 ix9_1) + BitVec.ofNat 32 0xFFFFFFFC, BitVec.ofNat 32 (((s.2.2.2.2.2.2.2.2.2.2.2.2.1)).toNat) - BitVec.ofNat 32 (ix9_1 + 1), cm_sg_3)

set_option linter.unusedVariables false in
/-- How `sv_csx` ends once `w5c` is 0. -/
def sv_cosigloopOk (dp B out bp x26 q : Word) (rt : Bytes) (w14 w18 w20 w24 w34 w3c w44 w48 w4c w50 w54 w58 w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 wa20 wa24 wa28 wa2c wa30 wa34 wa38 wa3c waa4 : Word) (v : Nat → Word) (sgp op ol : Word) (M0 : Word → BitVec 8) (c' : Word) (x21' : Word) (rl' : Word) (rp' : Word) (dg' : Word) (w8' : Word) (wc' : Word) (w28' : Word) (w2c' : Word) (w30' : Word) (w38' : Word) (w40' : Word) (w5c' : Word) (sg' : Bytes) (nk : Machine) : Prop :=
  w5c' = 0 ∧ ((((w30') &&& BitVec.ofNat 32 0x1 ≠ 0) ∧
    (evSpec (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 0x420) sg') w34 (B + 0x21A0 + BitVec.ofNat 32 0x420) w24 (w20).toNat = true) ∧
    ∃ n', Steps nk n' ∧
        St n'.mem SV n' 0x2F5A (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg nk (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg nk (4 : Fin 32) ∧
        reg n' (9 : Fin 32) = c' ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = x21' ∧
        reg n' (22 : Fin 32) = rl' ∧
        reg n' (23 : Fin 32) = rp' ∧
        reg n' (24 : Fin 32) = dg' ∧
        reg n' (25 : Fin 32) = q ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (w30') &&& BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = wa20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = wa24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = wa28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = wa2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = wa30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = wa34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = wa38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = wa3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = waa4 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = BitVec.ofNat 8 (sg'.getD 0 0) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (sg'.getD (1 + j) 0)) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1480 + j)) = BitVec.ofNat 8 (sg'.getD (1 + j) 0)) ∧
        SvKeepL B nk.mem n'.mem [(0x2C, 0x4), (0x421, 0x3F), (0x420, 0x1)]))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The checkpoint's signature loop: `k` more lines, then the end. -/
theorem sv_cosigloop {dp B out bp x26 q : Word} {rt : Bytes} {w14 w18 w20 w24 w34 w3c w44 w48 w4c w50 w54 w58 w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 wa20 wa24 wa28 wa2c wa30 wa34 wa38 wa3c waa4 : Word} {v : Nat → Word} {sgp op ol : Word}
    (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8) :
    ∀ (N : Nat) {c : Word} {x21 : Word} {rl : Word} {rp : Word} {dg : Word} {w8 : Word} {wc : Word} {w28 : Word} {w2c : Word} {w30 : Word} {w38 : Word} {w40 : Word} {w5c : Word} {sg : Bytes} {n0 : Machine},
    (hN : w5c.toNat ≤ N) →
    (E0 : SvCode n0.mem) →
    (V0 : SvSaves B n0.mem v) →
    (s0 : St n0.mem SV n0 0x2D6E (reg n0)) →
    (fM : ∀ x, SvR B x → n0.mem x = M0 x) →
    (g0_2 : reg n0 sp = B + 0x21A0) →
    (g0_9 : reg n0 (9 : Fin 32) = c) →
    (g0_18 : reg n0 (18 : Fin 32) = out) →
    (g0_19 : reg n0 (19 : Fin 32) = bp) →
    (g0_21 : reg n0 (21 : Fin 32) = x21) →
    (g0_22 : reg n0 (22 : Fin 32) = rl) →
    (g0_23 : reg n0 (23 : Fin 32) = rp) →
    (g0_24 : reg n0 (24 : Fin 32) = dg) →
    (g0_25 : reg n0 (25 : Fin 32) = q) →
    (g0_26 : reg n0 (26 : Fin 32) = x26) →
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20) →
    (w0_8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8) →
    (w0_c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc) →
    (w0_14 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14) →
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18) →
    (w0_1c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32) →
    (w0_20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20) →
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
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c) →
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60) →
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64) →
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68) →
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c) →
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70) →
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78) →
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c) →
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
    (w0_a20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = wa20) →
    (w0_a24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = wa24) →
    (w0_a28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = wa28) →
    (w0_a2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = wa2c) →
    (w0_a30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = wa30) →
    (w0_a34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = wa34) →
    (w0_a38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = wa38) →
    (w0_a3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = wa3c) →
    (w0_aa0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp) →
    (w0_aa4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = waa4) →
    (q0_320 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) →
    (b0_10 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = BitVec.ofNat 8 (sg.getD 0 0)) →
    (q0_1480 : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1480 + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0)) →
    (sg_in : SvIn B w38 w5c.toNat) →
    (CK0 : SvCkCode M0) →
    (l_in : SvIn B w48 w44.toNat) →
    (EE0 : EvEnv M0) →
    (RS : SvRoSep B) →
    (hiv : (s5Hv M0 (BitVec.ofNat 32 0x3FCC4AF8)).toList = Sha512.h0) →
    (pk_in : SvIn B w34 32) →
    (msg_in : SvIn B w24 w20.toNat) →
    (hlen : w20.toNat < 2 ^ 31) →
    SvErrRet B out v n0 ∨ ∃ k c' x21' rl' rp' dg' w8' wc' w28' w2c' w30' w38' w40' w5c' sg', svChain (sv_cosigStep dp B out bp x26 q rt w14 w18 w20 w24 w34 w3c w44 w48 w4c w50 w54 w58 w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 wa20 wa24 wa28 wa2c wa30 wa34 wa38 wa3c waa4 v sgp op ol M0) k (c, x21, rl, rp, dg, w8, wc, w28, w2c, w30, w38, w40, w5c, sg) (c', x21', rl', rp', dg', w8', wc', w28', w2c', w30', w38', w40', w5c', sg') ∧
      ∃ nk, Steps n0 nk ∧ reg nk (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg nk (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
      SvKeepL B n0.mem nk.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x5C, 0x4), (0x40, 0x4), (0x28, 0x4), (0xC, 0x4), (0x8, 0x4), (0x1380, 0x4), (0x420, 0x8), (0x200, 0x3), (0x420, 0x60), (0x1380, 0x8), (0x10, 0x4), (0x1480, 0x3F), (0x30, 0x4)] ∧ sv_cosigloopOk dp B out bp x26 q rt w14 w18 w20 w24 w34 w3c w44 w48 w4c w50 w54 w58 w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 wa20 wa24 wa28 wa2c wa30 wa34 wa38 wa3c waa4 v sgp op ol M0 c' x21' rl' rp' dg' w8' wc' w28' w2c' w30' w38' w40' w5c' sg' nk := by
  intro N
  induction N with
  | zero =>
    intro c x21 rl rp dg w8 wc w28 w2c w30 w38 w40 w5c sg n0 hN E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 b0_10 q0_1480 sg_in CK0 l_in EE0 RS hiv pk_in msg_in hlen
    have h0 : w5c = 0 := svRem_zero hN
    rcases sv_csx (dp := dp) (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (c := c) (q := q) (rl := rl) (rp := rp) (sgp := sgp) (op := op) (ol := ol) (rt := rt) (sg := sg) (w8 := w8) (wc := wc) (w14 := w14) (w18 := w18) (w20 := w20) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (wa20 := wa20) (wa24 := wa24) (wa28 := wa28) (wa2c := wa2c) (wa30 := wa30) (wa34 := wa34) (wa38 := wa38) (wa3c := wa3c) (waa4 := waa4) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 b0_10 q0_1480 h0 EE0 RS hiv pk_in msg_in hlen with ⟨-, e⟩ | okx
    · exact .inl e
    · exact .inr ⟨0, c, x21, rl, rp, dg, w8, wc, w28, w2c, w30, w38, w40, w5c, sg, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), h0, okx⟩
  | succ N ih =>
    intro c x21 rl rp dg w8 wc w28 w2c w30 w38 w40 w5c sg n0 hN E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 b0_10 q0_1480 sg_in CK0 l_in EE0 RS hiv pk_in msg_in hlen
    by_cases h0 : w5c = 0
    · rcases sv_csx (dp := dp) (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (c := c) (q := q) (rl := rl) (rp := rp) (sgp := sgp) (op := op) (ol := ol) (rt := rt) (sg := sg) (w8 := w8) (wc := wc) (w14 := w14) (w18 := w18) (w20 := w20) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (wa20 := wa20) (wa24 := wa24) (wa28 := wa28) (wa2c := wa2c) (wa30 := wa30) (wa34 := wa34) (wa38 := wa38) (wa3c := wa3c) (waa4 := waa4) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 b0_10 q0_1480 h0 EE0 RS hiv pk_in msg_in hlen with ⟨-, e⟩ | okx
      · exact .inl e
      · exact .inr ⟨0, c, x21, rl, rp, dg, w8, wc, w28, w2c, w30, w38, w40, w5c, sg, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), h0, okx⟩
    rcases sv_seg_cosig (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (c := c) (q := q) (rl := rl) (rp := rp) (rt := rt) (sg := sg) (w8 := w8) (wc := wc) (w14 := w14) (w18 := w18) (w20 := w20) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (wa20 := wa20) (wa24 := wa24) (wa28 := wa28) (wa2c := wa2c) (wa30 := wa30) (wa34 := wa34) (wa38 := wa38) (wa3c := wa3c) (waa4 := waa4) (v := v) F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 b0_10 q0_1480 h0 sg_in CK0 l_in with e | ⟨x1_0ix9_1, x1_0, x1_1, x1_2, x1_3k_2, x1_3, x1_4, x1_5c'_2, x1_5pa'_2, x1_5, x1_6, x1_7, x1_8, x1_9, x1_10, x1_11dg'_3, x1_11pg'_3, x1_11gi'_3, x1_11, x1_12, x1_13cm_sg_3, x1_13cm_w30_3, x1_13, n1, c1, fR1, s1, E1, V1, r1_3, r1_4, r1_2, r1_9, r1_18, r1_19, r1_21, r1_22, r1_23, r1_24, r1_25, r1_26, r1_27, w1_8, w1_c, w1_14, w1_18, w1_1c, w1_20, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_3c, w1_40, w1_44, w1_48, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, w1_a20, w1_a24, w1_a28, w1_a2c, w1_a30, w1_a34, w1_a38, w1_a3c, w1_aa0, w1_aa4, b1_10, q1_320, q1_1480, K1_L⟩
    · exact .inl e
    have hdec := svRem_le1 (a := x1_0ix9_1 + 1) (N := N) (by omega) (by have := (nlScan_lt _ _ _ x1_0).2; omega) hN
    rcases ih hdec E1 V1 s1 fR1 r1_2 r1_9 r1_18 r1_19 r1_21 r1_22 r1_23 r1_24 r1_25 r1_26 r1_27 w1_8 w1_c w1_14 w1_18 w1_1c w1_20 w1_24 w1_28 w1_2c w1_30 w1_34 w1_38 w1_3c w1_40 w1_44 w1_48 w1_4c w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_78 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_98 w1_9c w1_a0 w1_a4 w1_a8 w1_ac w1_b0 w1_b4 w1_b8 w1_bc w1_c0 w1_c4 w1_c8 w1_cc w1_d0 w1_d4 w1_d8 w1_dc w1_e0 w1_e4 w1_e8 w1_ec w1_f0 w1_f4 w1_f8 w1_fc w1_100 w1_104 w1_108 w1_10c w1_110 w1_114 w1_118 w1_11c w1_120 w1_124 w1_128 w1_12c w1_130 w1_a20 w1_a24 w1_a28 w1_a2c w1_a30 w1_a34 w1_a38 w1_a3c w1_aa0 w1_aa4 q1_320 b1_10 q1_1480 (by rw [svSubOfNat_toNat (by have := (nlScan_lt _ _ _ x1_0).2; omega)]; exact (sg_in).nlRest x1_0) CK0 l_in EE0 RS hiv pk_in msg_in hlen with e | ⟨k, c', x21', rl', rp', dg', w8', wc', w28', w2c', w30', w38', w40', w5c', sg', chn, nk, cs, h3, h4, hk, okk⟩
    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
    · exact .inr ⟨k + 1, c', x21', rl', rp', dg', w8', wc', w28', w2c', w30', w38', w40', w5c', sg', svChain.cons ⟨h0, x1_0ix9_1, x1_0, x1_1, x1_2, x1_3k_2, x1_3, x1_4, x1_5c'_2, x1_5pa'_2, x1_5, x1_6, x1_7, x1_8, x1_9, x1_10, x1_11dg'_3, x1_11pg'_3, x1_11gi'_3, x1_11, x1_12, x1_13cm_sg_3, x1_13cm_w30_3, x1_13, rfl⟩ chn, nk, c1.trans cs, h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), okk⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `sv_cosigloop` as a stage. -/
theorem sv_cosigloop_st {dp B out bp x26 q : Word} {rt : Bytes} {w14 w18 w20 w24 w34 w3c w44 w48 w4c w50 w54 w58 w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 wa20 wa24 wa28 wa2c wa30 wa34 wa38 wa3c waa4 : Word} {v : Nat → Word} {sgp op ol : Word} {N : Nat} {c : Word} {x21 : Word} {rl : Word} {rp : Word} {dg : Word} {w8 : Word} {wc : Word} {w28 : Word} {w2c : Word} {w30 : Word} {w38 : Word} {w40 : Word} {w5c : Word} {sg : Bytes} {n0 : Machine}
    (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (hN : w5c.toNat ≤ N)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x2D6E (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = c)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = rl)
    (g0_23 : reg n0 (23 : Fin 32) = rp)
    (g0_24 : reg n0 (24 : Fin 32) = dg)
    (g0_25 : reg n0 (25 : Fin 32) = q)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8)
    (w0_c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc)
    (w0_14 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18)
    (w0_1c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32)
    (w0_20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20)
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
    (w0_a20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = wa20)
    (w0_a24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = wa24)
    (w0_a28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = wa28)
    (w0_a2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = wa2c)
    (w0_a30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = wa30)
    (w0_a34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = wa34)
    (w0_a38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = wa38)
    (w0_a3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = wa3c)
    (w0_aa0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp)
    (w0_aa4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = waa4)
    (q0_320 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0))
    (b0_10 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = BitVec.ofNat 8 (sg.getD 0 0))
    (q0_1480 : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1480 + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0))
    (sg_in : SvIn B w38 w5c.toNat)
    (CK0 : SvCkCode M0)
    (l_in : SvIn B w48 w44.toNat)
    (EE0 : EvEnv M0)
    (RS : SvRoSep B)
    (hiv : (s5Hv M0 (BitVec.ofNat 32 0x3FCC4AF8)).toList = Sha512.h0)
    (pk_in : SvIn B w34 32)
    (msg_in : SvIn B w24 w20.toNat)
    (hlen : w20.toNat < 2 ^ 31)
    :
    SvErrRet B out v n0 ∨
    (∃ k c' x21' rl' rp' dg' w8' wc' w28' w2c' w30' w38' w40' w5c' sg', svChain (sv_cosigStep dp B out bp x26 q rt w14 w18 w20 w24 w34 w3c w44 w48 w4c w50 w54 w58 w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 wa20 wa24 wa28 wa2c wa30 wa34 wa38 wa3c waa4 v sgp op ol M0) k (c, x21, rl, rp, dg, w8, wc, w28, w2c, w30, w38, w40, w5c, sg) (c', x21', rl', rp', dg', w8', wc', w28', w2c', w30', w38', w40', w5c', sg') ∧
      w5c' = 0 ∧
      ((w30') &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ (evSpec (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 0x420) sg') w34 (B + 0x21A0 + BitVec.ofNat 32 0x420) w24 (w20).toNat = true) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x2F5A (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (9 : Fin 32) = c' ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = x21' ∧
        reg n' (22 : Fin 32) = rl' ∧
        reg n' (23 : Fin 32) = rp' ∧
        reg n' (24 : Fin 32) = dg' ∧
        reg n' (25 : Fin 32) = q ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (w30') &&& BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = wa20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = wa24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = wa28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = wa2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = wa30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = wa34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = wa38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = wa3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = waa4 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = BitVec.ofNat 8 (sg'.getD 0 0) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (sg'.getD (1 + j) 0)) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1480 + j)) = BitVec.ofNat 8 (sg'.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x5C, 0x4), (0x40, 0x4), (0x28, 0x4), (0xC, 0x4), (0x8, 0x4), (0x1380, 0x4), (0x420, 0x8), (0x200, 0x3), (0x420, 0x60), (0x1380, 0x8), (0x10, 0x4), (0x1480, 0x3F), (0x30, 0x4), (0x421, 0x3F), (0x420, 0x1)]) := by
  rcases sv_cosigloop (dp := dp) (B := B) (out := out) (bp := bp) (x26 := x26) (q := q) (rt := rt) (w14 := w14) (w18 := w18) (w20 := w20) (w24 := w24) (w34 := w34) (w3c := w3c) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (wa20 := wa20) (wa24 := wa24) (wa28 := wa28) (wa2c := wa2c) (wa30 := wa30) (wa34 := wa34) (wa38 := wa38) (wa3c := wa3c) (waa4 := waa4) (v := v) (sgp := sgp) (op := op) (ol := ol) F hret hO M0 N hN E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 b0_10 q0_1480 sg_in CK0 l_in EE0 RS hiv pk_in msg_in hlen with e | ⟨k, c', x21', rl', rp', dg', w8', wc', w28', w2c', w30', w38', w40', w5c', sg', chn, nk, cs, hr3, hr4, hkl, okh⟩
  · exact .inl e
  obtain ⟨hz, h0, h1, n1, cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w14, f_w18, f_w1c, f_w20, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_wa8, f_wac, f_wb0, f_wb4, f_wb8, f_wbc, f_wc0, f_wc4, f_wc8, f_wcc, f_wd0, f_wd4, f_wd8, f_wdc, f_we0, f_we4, f_we8, f_wec, f_wf0, f_wf4, f_wf8, f_wfc, f_w100, f_w104, f_w108, f_w10c, f_w110, f_w114, f_w118, f_w11c, f_w120, f_w124, f_w128, f_w12c, f_w130, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_waa0, f_waa4, f_b10, f_q320, f_q421, f_q1480, f_KL⟩ := okh
  exact .inr ⟨k, c', x21', rl', rp', dg', w8', wc', w28', w2c', w30', w38', w40', w5c', sg', chn, hz, h0, h1, n1, cs.trans cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3.trans hr3, f_r4.trans hr4, f_r9, f_r18, f_r19, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w14, f_w18, f_w1c, f_w20, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_wa8, f_wac, f_wb0, f_wb4, f_wb8, f_wbc, f_wc0, f_wc4, f_wc8, f_wcc, f_wd0, f_wd4, f_wd8, f_wdc, f_we0, f_we4, f_we8, f_wec, f_wf0, f_wf4, f_wf8, f_wfc, f_w100, f_w104, f_w108, f_w10c, f_w110, f_w114, f_w118, f_w11c, f_w120, f_w124, f_w128, f_w12c, f_w130, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_waa0, f_waa4, f_b10, f_q320, f_q421, f_q1480, (hkl.trans f_KL).mono (by decide)⟩

/-- The signature that memory holds where the signature loop keeps a found one. -/
def svSigOf (M : Word → BitVec 8) (B : Word) : Bytes :=
  (M (B + 0x21A0 + BitVec.ofNat 32 0x10)).toNat :: memBytes M (B + 0x21A0 + BitVec.ofNat 32 0x1480) 63

theorem svSigOf_at (M : Word → BitVec 8) (B : Word) :
    M (B + 0x21A0 + BitVec.ofNat 32 0x10) = BitVec.ofNat 8 ((svSigOf M B).getD 0 0) ∧
    ∀ j, j < 63 → M (B + 0x21A0 + BitVec.ofNat 32 (0x1480 + j)) = BitVec.ofNat 8 ((svSigOf M B).getD (1 + j) 0) := by
  refine ⟨BitVec.eq_of_toNat_eq ?_, fun j hj => BitVec.eq_of_toNat_eq ?_⟩
  · show _ = (BitVec.ofNat 8 (M (B + 0x21A0 + BitVec.ofNat 32 0x10)).toNat).toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (M _).isLt]
  · rw [svSigOf, Nat.add_comm 1 j, List.getD_cons_succ, List.getD_eq_getElem?_getD, memBytes,
      List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some, add_ofNat_assoc,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (M _).isLt]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `sv_cosigloop_st` from the signature that memory holds where the loop keeps a found one: before any line, the loop has found none, so any value does. -/
theorem sv_cosigloop_st0 {dp B out bp x26 q : Word} {rt : Bytes} {w14 w18 w20 w24 w34 w3c w44 w48 w4c w50 w54 w58 w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 wa20 wa24 wa28 wa2c wa30 wa34 wa38 wa3c waa4 : Word} {v : Nat → Word} {sgp op ol : Word} {N : Nat} {c : Word} {x21 : Word} {rl : Word} {rp : Word} {dg : Word} {w8 : Word} {wc : Word} {w28 : Word} {w2c : Word} {w30 : Word} {w38 : Word} {w40 : Word} {w5c : Word} {n0 : Machine}
    (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (hN : w5c.toNat ≤ N)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x2D6E (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = c)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = rl)
    (g0_23 : reg n0 (23 : Fin 32) = rp)
    (g0_24 : reg n0 (24 : Fin 32) = dg)
    (g0_25 : reg n0 (25 : Fin 32) = q)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8)
    (w0_c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc)
    (w0_14 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18)
    (w0_1c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32)
    (w0_20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20)
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
    (w0_a20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = wa20)
    (w0_a24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = wa24)
    (w0_a28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = wa28)
    (w0_a2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = wa2c)
    (w0_a30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = wa30)
    (w0_a34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = wa34)
    (w0_a38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = wa38)
    (w0_a3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = wa3c)
    (w0_aa0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp)
    (w0_aa4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = waa4)
    (q0_320 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0))
    (sg_in : SvIn B w38 w5c.toNat)
    (CK0 : SvCkCode M0)
    (l_in : SvIn B w48 w44.toNat)
    (EE0 : EvEnv M0)
    (RS : SvRoSep B)
    (hiv : (s5Hv M0 (BitVec.ofNat 32 0x3FCC4AF8)).toList = Sha512.h0)
    (pk_in : SvIn B w34 32)
    (msg_in : SvIn B w24 w20.toNat)
    (hlen : w20.toNat < 2 ^ 31)
    :
    SvErrRet B out v n0 ∨
    (∃ sg, ∃ k c' x21' rl' rp' dg' w8' wc' w28' w2c' w30' w38' w40' w5c' sg', svChain (sv_cosigStep dp B out bp x26 q rt w14 w18 w20 w24 w34 w3c w44 w48 w4c w50 w54 w58 w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 wa20 wa24 wa28 wa2c wa30 wa34 wa38 wa3c waa4 v sgp op ol M0) k (c, x21, rl, rp, dg, w8, wc, w28, w2c, w30, w38, w40, w5c, sg) (c', x21', rl', rp', dg', w8', wc', w28', w2c', w30', w38', w40', w5c', sg') ∧
      w5c' = 0 ∧
      ((w30') &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ (evSpec (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 0x420) sg') w34 (B + 0x21A0 + BitVec.ofNat 32 0x420) w24 (w20).toNat = true) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x2F5A (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (9 : Fin 32) = c' ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = x21' ∧
        reg n' (22 : Fin 32) = rl' ∧
        reg n' (23 : Fin 32) = rp' ∧
        reg n' (24 : Fin 32) = dg' ∧
        reg n' (25 : Fin 32) = q ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (w30') &&& BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = wa20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = wa24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = wa28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = wa2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = wa30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = wa34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = wa38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = wa3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = waa4 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = BitVec.ofNat 8 (sg'.getD 0 0) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (sg'.getD (1 + j) 0)) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1480 + j)) = BitVec.ofNat 8 (sg'.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x5C, 0x4), (0x40, 0x4), (0x28, 0x4), (0xC, 0x4), (0x8, 0x4), (0x1380, 0x4), (0x420, 0x8), (0x200, 0x3), (0x420, 0x60), (0x1380, 0x8), (0x10, 0x4), (0x1480, 0x3F), (0x30, 0x4), (0x421, 0x3F), (0x420, 0x1)]) := by
  rcases sv_cosigloop_st (sg := svSigOf n0.mem B) (b0_10 := (svSigOf_at n0.mem B).1) (q0_1480 := (svSigOf_at n0.mem B).2) (dp := dp) (B := B) (out := out) (bp := bp) (x26 := x26) (q := q) (rt := rt) (w14 := w14) (w18 := w18) (w20 := w20) (w24 := w24) (w34 := w34) (w3c := w3c) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (wa20 := wa20) (wa24 := wa24) (wa28 := wa28) (wa2c := wa2c) (wa30 := wa30) (wa34 := wa34) (wa38 := wa38) (wa3c := wa3c) (waa4 := waa4) (v := v) (sgp := sgp) (op := op) (ol := ol) F hret hO M0 hN E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 sg_in CK0 l_in EE0 RS hiv pk_in msg_in hlen with e | h
  · exact .inl e
  · exact .inr ⟨_, h⟩

end C3.RV32.Sv
