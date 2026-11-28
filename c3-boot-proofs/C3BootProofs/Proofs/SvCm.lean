import C3BootProofs.Proofs.SvCme
import C3BootProofs.Proofs.SvCmdn
import C3BootProofs.Proofs.SvCmdl
import C3BootProofs.Proofs.SvCms
import C3BootProofs.Proofs.SvCmf
import C3BootProofs.Proofs.SvCmx
import C3BootProofs.Proofs.SvCmk
import C3BootProofs.Proofs.SvCmn

/-!
# `sigstore::verify`: The end of a signature line, empty or not.

Written by `scripts/gen-sv-segs.py` from `sv_cme`, `sv_cmdn`, `sv_cmdl`, `sv_cms`, `sv_cmf`, `sv_cmx`, `sv_cmk`, and `sv_cmn`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxHeartbeats 16000000 in
/-- The end of a signature line, empty or not. -/
theorem sv_cm {B out bp x20 : Word} {x21 : Word} {x22 x23 : Word} {x24 : Word} {x25 : Word} {x26 x27 : Word} {f w38 w50 kh w48 w44 kp ckp bl pg gi nl ns1 ni ns10 np w8 wc w10 w2c : Word} {sg : Bytes} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x16D4 (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = nl)
    (g0_9 : reg n0 (9 : Fin 32) = ns1)
    (g0_10 : reg n0 a0 = pg)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = gi)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = ni)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = ns10)
    (g0_27 : reg n0 (27 : Fin 32) = np)
    (w0_8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8)
    (w0_c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc)
    (w0_10 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh)
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl)
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp)
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (b0_14 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0))
    (q0_1fc : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0))
    (hend : pg = w8)
    (nm_in : SvIn B np ni.toNat)
    (l_in : SvIn B w48 w44.toNat)
    (CK0 : SvCkCode M0)
    (b_in : SvIn B w10 ns10.toNat) :
    SvErrRet B out v n0 ∨
    (∃ cm_sg : Bytes, ∃ cm_w30 : Word, ((False) ∨ (False) ∨ (False) ∨ (∃ bs, base64Decode (memBytes M0 w10 ns10.toNat) = some bs ∧ (¬ (nl = ns1)) ∧ (memBytes M0 np ni.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 w10 ns10.toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (bs.length < 4) ∧ cm_sg = sg ∧ cm_w30 = f) ∨ (∃ bs, base64Decode (memBytes M0 w10 ns10.toNat) = some bs ∧ (¬ (nl = ns1)) ∧ (memBytes M0 np ni.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 w10 ns10.toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (¬ (bs.length < 4)) ∧ (le4 bs 0 = kh) ∧ (bs.length = 68) ∧ (w2c = 0) ∧ cm_sg = (bs.drop 4) ∧ cm_w30 = BitVec.ofNat 32 0x1) ∨ (False) ∨ (∃ bs, base64Decode (memBytes M0 w10 ns10.toNat) = some bs ∧ (¬ (nl = ns1)) ∧ (memBytes M0 np ni.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 w10 ns10.toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (¬ (bs.length < 4)) ∧ (¬ (le4 bs 0 = kh)) ∧ cm_sg = sg ∧ cm_w30 = f) ∨ ((¬ (nl = ns1)) ∧ (¬ (memBytes M0 np ni.toNat = memBytes M0 w48 w44.toNat)) ∧ cm_sg = sg ∧ cm_w30 = f)) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1642 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = nl ∧
        reg n' (9 : Fin 32) = ns1 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = gi ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = ni ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = ns10 ∧
        reg n' (27 : Fin 32) = np ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = cm_w30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (cm_sg.getD 0 0) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (cm_sg.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60), (0x14, 0x4), (0x1FC, 0x3F), (0x30, 0x4)]) := by
  by_cases hb : nl = ns1
  · rcases sv_cme (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg) (gi := gi) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (w2c := w2c) (sg := sg) (bs := []) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hend hb with ⟨-, e⟩ | ⟨hf, -⟩
    · exact .inl e
    · exact hf.elim
  · by_cases hb2 : memBytes M0 np ni.toNat = memBytes M0 w48 w44.toNat
    · by_cases hb3 : base64Decode (memBytes M0 w10 ns10.toNat) = none
      · rcases sv_cmdn (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg) (gi := gi) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (w2c := w2c) (sg := sg) (bs := []) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hend hb nm_in l_in hb2 CK0 b_in hb3 with ⟨-, e⟩ | ⟨hf, -⟩
        · exact .inl e
        · exact hf.elim
      · obtain ⟨hb3v, hb3w⟩ := Option.ne_none_iff_exists'.mp hb3
        by_cases hb4 : 0x60 < hb3v.length
        · rcases sv_cmdl (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg) (gi := gi) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (w2c := w2c) (sg := sg) (bs := hb3v) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hend hb nm_in l_in hb2 CK0 b_in hb3w hb4 with ⟨-, e⟩ | ⟨hf, -⟩
          · exact .inl e
          · exact hf.elim
        · by_cases hb6 : hb3v.length < 4
          · rcases sv_cms (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg) (gi := gi) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (w2c := w2c) (sg := sg) (bs := hb3v) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hend hb nm_in l_in hb2 CK0 b_in hb3w (Nat.not_lt.mp hb4) hb6 with ⟨-, e⟩ | rest
            · exact .inl e
            · exact .inr ⟨sg, f, .inr (.inr (.inr (.inl ⟨hb3v, hb3w, hb, hb2, hb3, hb4, hb6, rfl, rfl⟩))), rest.imp (fun _ => fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun k => k.mono (by decide)))))))))))))))))))))))))))))))))))))⟩
          · by_cases hb8 : le4 hb3v 0 = kh
            · by_cases hb9 : hb3v.length = 68
              · rcases sv_cmf (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg) (gi := gi) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (w2c := w2c) (sg := sg) (bs := hb3v) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hend hb nm_in l_in hb2 CK0 b_in hb3w (Nat.not_lt.mp hb4) (Nat.not_lt.mp hb6) hb8 hb9 with ⟨-, e⟩ | ⟨h0, rest⟩
                · exact .inl e
                · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w10, f_w18, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w44, f_w48, f_w50, f_b14, f_q1fc, f_q420, f_KL⟩ := rest
                  exact .inr ⟨(hb3v.drop 4), BitVec.ofNat 32 0x1, .inr (.inr (.inr (.inr (.inl ⟨hb3v, hb3w, hb, hb2, hb3, hb4, hb6, hb8, hb9, h0, rfl, rfl⟩)))), ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w10, f_w18, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w44, f_w48, f_w50, f_b14, f_q1fc, f_KL.mono (by decide)⟩⟩
              · rcases sv_cmx (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg) (gi := gi) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (w2c := w2c) (sg := sg) (bs := hb3v) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hend hb nm_in l_in hb2 CK0 b_in hb3w (Nat.not_lt.mp hb4) (Nat.not_lt.mp hb6) hb8 hb9 with ⟨-, e⟩ | ⟨hf, -⟩
                · exact .inl e
                · exact hf.elim
            · rcases sv_cmk (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg) (gi := gi) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (w2c := w2c) (sg := sg) (bs := hb3v) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hend hb nm_in l_in hb2 CK0 b_in hb3w (Nat.not_lt.mp hb4) (Nat.not_lt.mp hb6) hb8 with ⟨-, e⟩ | rest
              · exact .inl e
              · exact .inr ⟨sg, f, .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨hb3v, hb3w, hb, hb2, hb3, hb4, hb6, hb8, rfl, rfl⟩)))))), rest.imp (fun _ => fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun k => k.mono (by decide)))))))))))))))))))))))))))))))))))))⟩
    · rcases sv_cmn (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg) (gi := gi) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (w2c := w2c) (sg := sg) (bs := []) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hend hb nm_in l_in hb2 with ⟨-, e⟩ | rest
      · exact .inl e
      · exact .inr ⟨sg, f, .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨hb, hb2, rfl, rfl⟩)))))), rest.imp (fun _ => fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun k => k.mono (by decide)))))))))))))))))))))))))))))))))))))⟩

end C3.RV32.Sv
