import C3BootProofs.Proofs.SvCg0
import C3BootProofs.Proofs.SvCg1
import C3BootProofs.Proofs.SvCg2
import C3BootProofs.Proofs.SvCg3
import C3BootProofs.Proofs.SvCg4

/-!
# `sigstore::verify`: One base64 group of a cosignature, padded at any of its places or not at all.

Written by `scripts/gen-sv-segs.py` from `sv_cg0`, `sv_cg1`, `sv_cg2`, `sv_cg3`, and `sv_cg4`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxHeartbeats 16000000 in
/-- One base64 group of a cosignature, padded at any of its places or not at all. -/
theorem sv_cg {w2c B out bp x20 : Word} {x21 : Word} {x22 x23 : Word} {x24 : Word} {x25 : Word} {x26 x27 : Word} {f w38 w50 kh w48 w44 kp ckp bl pg gi nl ns1 ni ns10 np w8 wc w10 : Word} {sg : Bytes} {v : Nat → Word} {n0 : Machine}
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
    (hne : pg ≠ w8)
    (CK0 : SvCkCode M0)
    (pg_in : SvIn B pg 4)
    (pb1 : SvIn B (pg + 0x1) 1)
    (pb2 : SvIn B (pg + 0x2) 1)
    (pb3 : SvIn B (pg + 0x3) 1)
    (pc0 : SvIn B (pg) 1)
    (pc1 : SvIn B ((pg) + BitVec.ofNat 32 0x1) 1)
    (pc2 : SvIn B (((pg) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) 1)
    (pc3 : SvIn B ((((pg) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) 1) :
    SvErrRet B out v n0 ∨
    ((((M0 (pg) = 0x3D) ∧ ((gi) + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq27, base64Decode (memBytes M0 pg 4) = some bq27 ∧ (bq27.length ≤ 3)) ∨ ((¬ (M0 (pg) = 0x3D)) ∧ (M0 ((pg) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi) + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq33, base64Decode (memBytes M0 pg 4) = some bq33 ∧ (bq33.length ≤ 3)) ∨ ((¬ (M0 (pg) = 0x3D)) ∧ (¬ (M0 ((pg) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (M0 (((pg) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi) + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq39, base64Decode (memBytes M0 pg 4) = some bq39 ∧ (bq39.length ≤ 3)) ∨ ((¬ (M0 (pg) = 0x3D)) ∧ (¬ (M0 ((pg) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 (((pg) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (M0 ((((pg) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi) + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq45, base64Decode (memBytes M0 pg 4) = some bq45 ∧ (bq45.length ≤ 3)) ∨ ((¬ (M0 (pg) = 0x3D)) ∧ (¬ (M0 ((pg) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 (((pg) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 ((((pg) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ ∃ bq44, base64Decode (memBytes M0 pg 4) = some bq44 ∧ (bq44.length ≤ 3))) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x16D4 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = nl ∧
        reg n' (9 : Fin 32) = ns1 ∧
        reg n' a0 = (pg) + BitVec.ofNat 32 0x4 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = ni ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = ns10 ∧
        reg n' (27 : Fin 32) = np ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)]) := by
  by_cases hb : M0 (pg) = 0x3D
  · rcases sv_cg0 (w2c := w2c) (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg) (gi := gi) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (sg := sg) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hne CK0 pg_in pb1 pb2 pb3 pc0 hb with ⟨-, e⟩ | ⟨h0, bq27, h1, h2, rest⟩
    · exact .inl e
    · exact .inr ⟨.inl ⟨hb, h0, bq27, h1, h2⟩, rest⟩
  · by_cases hb2 : M0 ((pg) + BitVec.ofNat 32 0x1) = 0x3D
    · rcases sv_cg1 (w2c := w2c) (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg) (gi := gi) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (sg := sg) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hne CK0 pg_in pb1 pb2 pb3 pc0 hb pc1 hb2 with ⟨-, e⟩ | ⟨h0, bq33, h1, h2, rest⟩
      · exact .inl e
      · exact .inr ⟨.inr (.inl ⟨hb, hb2, h0, bq33, h1, h2⟩), rest⟩
    · by_cases hb3 : M0 (((pg) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D
      · rcases sv_cg2 (w2c := w2c) (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg) (gi := gi) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (sg := sg) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hne CK0 pg_in pb1 pb2 pb3 pc0 hb pc1 hb2 pc2 hb3 with ⟨-, e⟩ | ⟨h0, bq39, h1, h2, rest⟩
        · exact .inl e
        · exact .inr ⟨.inr (.inr (.inl ⟨hb, hb2, hb3, h0, bq39, h1, h2⟩)), rest⟩
      · by_cases hb4 : M0 ((((pg) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D
        · rcases sv_cg3 (w2c := w2c) (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg) (gi := gi) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (sg := sg) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hne CK0 pg_in pb1 pb2 pb3 pc0 hb pc1 hb2 pc2 hb3 pc3 hb4 with ⟨-, e⟩ | ⟨h0, bq45, h1, h2, rest⟩
          · exact .inl e
          · exact .inr ⟨.inr (.inr (.inr (.inl ⟨hb, hb2, hb3, hb4, h0, bq45, h1, h2⟩))), rest⟩
        · rcases sv_cg4 (w2c := w2c) (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg) (gi := gi) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (sg := sg) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hne CK0 pg_in pb1 pb2 pb3 pc0 hb pc1 hb2 pc2 hb3 pc3 hb4 with ⟨-, e⟩ | ⟨bq44, h0, h1, rest⟩
          · exact .inl e
          · exact .inr ⟨.inr (.inr (.inr (.inr ⟨hb, hb2, hb3, hb4, bq44, h0, h1⟩))), rest⟩

end C3.RV32.Sv
