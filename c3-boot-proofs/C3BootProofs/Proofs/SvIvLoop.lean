import C3BootProofs.Proofs.SvZLoop2
import C3BootProofs.Proofs.SvIvHc
import C3BootProofs.Proofs.SvIvHx
import C3BootProofs.Proofs.SvIvA
import C3BootProofs.Proofs.SvIvB
import C3BootProofs.Proofs.SvEcDs

/-!
# `sigstore::verify`: the batches of the inversion of `s`

From the inversion's head at 0x1328 back to it: `sv_ivhc` starts a batch, `ec_scan` looks for a nonzero limb
of `g`, `sv_iva` loads the low words, `ec_loop` runs the divsteps, and `sv_ivb` applies their matrix, which
is one `ivStep8`. `iv_loop` runs batches as `ivLoop8` does, and `iv_exit` leaves for 0x1556 when no steps
are left or `g` is zero.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

/-- `-n⁻¹ mod 2⁶⁴` for the order `n` of P-256, which the inversion of `s` keeps at 0x70 and 0x60. -/
def ivMI : Nat := 0x332E375511FF43B1

/-- One batch of the inversion of `s` modulo `N`. -/
def ivStep8 (N : Nat) (s : Iv) : Iv :=
  let n := min s.rem 62
  let t := dsIter n ⟨s.δ, lowestI s.f, lowestI s.g, 1, 0, 0, 1⟩
  ⟨t.δ, fgUpd8 s.f s.g (i64Val t.u) (i64Val t.v) n, fgUpd8 s.f s.g (i64Val t.q) (i64Val t.r) n,
    deUpd8 s.d s.e (i64Val t.u) (i64Val t.v) ivMI n N, deUpd8 s.d s.e (i64Val t.q) (i64Val t.r) ivMI n N, s.rem - n⟩

/-- Batches until no steps are left or `g` is zero, with `k` batches at most. -/
def ivLoop8 (N : Nat) : Nat → Iv → Iv
  | 0, s => s
  | k + 1, s => if s.rem = 0 ∨ s.g = 0 then s else ivLoop8 N k (ivStep8 N s)

theorem ivLoop8_done (N : Nat) : ∀ k (s : Iv), s.rem = 0 ∨ s.g = 0 → ivLoop8 N k s = s
  | 0, _, _ => rfl
  | _ + 1, s, h => by rw [ivLoop8, ite_eq_left h]

theorem ivLoop8_stop (N : Nat) : ∀ k (s : Iv), s.rem ≤ 62 * k →
    (ivLoop8 N k s).rem = 0 ∨ (ivLoop8 N k s).g = 0
  | 0, s, h => by rw [ivLoop8]; omega
  | k + 1, s, h => by
    rw [ivLoop8]
    by_cases h0 : s.rem = 0 ∨ s.g = 0
    · rw [ite_eq_left h0]; exact h0
    · rw [ite_eq_right h0]
      exact ivLoop8_stop N k _ (by simp only [ivStep8]; omega)

/-- The frame words that the inversion of `s` leaves alone. -/
def ivWords : List Nat := [0x24, 0x28, 0x2C, 0x30, 0x34, 0x38, 0x3C, 0x40, 0x44, 0x48, 0x4C, 0x50, 0x54, 0x58, 0x64, 0x68, 0x6C, 0x7C, 0x80, 0x84, 0x88, 0x8C, 0x90, 0x94, 0x98, 0x9C, 0xA0, 0xA4, 0xA8, 0xAC, 0xB0, 0xB4, 0xB8, 0xBC, 0xC0, 0xC4, 0xC8, 0xCC, 0xD0, 0xD4, 0xD8, 0xDC, 0xE0, 0xE4, 0xE8, 0xEC, 0xF0, 0xF4, 0xF8, 0xFC, 0x100, 0x104, 0x108, 0x10C, 0x110, 0x114, 0x118, 0x11C, 0x120, 0x124, 0x128, 0x12C, 0x130]

/-- What holds at the inversion's head 0x1328 for the state `st`. -/
structure IvInv (B : Word) (m : Machine) (v : Nat → Word) (r3 r4 out bp s5v x26 : Word) (qx qy qz rv sv zv N : Nat)
    (W : Nat → Word) (st : Iv) : Prop where
  E : SvCode m.mem
  IC : SvIvCode m.mem
  EC : SvEcCode m.mem
  UC : SvUpCode m.mem
  V : SvSaves B m.mem v
  sp : reg m sp = B + 0x21A0
  g3 : reg m (3 : Fin 32) = r3
  g4 : reg m (4 : Fin 32) = r4
  g18 : reg m (18 : Fin 32) = out
  g19 : reg m (19 : Fin 32) = bp
  g21 : reg m (21 : Fin 32) = s5v
  g24 : reg m (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268
  g26 : reg m (26 : Fin 32) = x26
  g27 : reg m (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20
  wd : W64 (reg m (23 : Fin 32)) (reg m (25 : Fin 32)) = st.δ
  wr : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 st.rem
  rem : st.rem < 2 ^ 32
  w60 : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 0x332E3755
  w70 : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 0x11FF43B1
  aN : accV m.mem (BitVec.ofNat 32 0x3FCC4268) 8 = N
  a240 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx
  a260 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy
  a280 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz
  a2a0 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv
  a2c0 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv
  a2e0 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv
  vf : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8) = st.f
  lf : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0)).toNat ≤ 1
  vg : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8) = st.g
  lg : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0)).toNat ≤ 1
  vd : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8) = st.d
  ld : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040)).toNat ≤ 1
  ve : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x440)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8) = st.e
  le : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x440)).toNat ≤ 1
  ww : ∀ e, e ∈ ivWords → memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 e) = W e

theorem IvInv.of {B r3 r4 out bp s5v x26 : Word} {qx qy qz rv sv zv N : Nat} {W v : Nat → Word} {m m' : Machine} {st : Iv}
    (I : IvInv B m v r3 r4 out bp s5v x26 qx qy qz rv sv zv N W st) (hm : m'.mem = m.mem)
    (hr : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 21, 23, 24, 25, 26, 27] → reg m' q = reg m q) :
    IvInv B m' v r3 r4 out bp s5v x26 qx qy qz rv sv zv N W st := by
  exact ⟨by rw [hm]; exact I.E,
    by rw [hm]; exact I.IC,
    by rw [hm]; exact I.EC,
    by rw [hm]; exact I.UC,
    by rw [hm]; exact I.V,
    by rw [hr 2 (by decide)]; exact I.sp,
    by rw [hr 3 (by decide)]; exact I.g3,
    by rw [hr 4 (by decide)]; exact I.g4,
    by rw [hr 18 (by decide)]; exact I.g18,
    by rw [hr 19 (by decide)]; exact I.g19,
    by rw [hr 21 (by decide)]; exact I.g21,
    by rw [hr 24 (by decide)]; exact I.g24,
    by rw [hr 26 (by decide)]; exact I.g26,
    by rw [hr 27 (by decide)]; exact I.g27,
    by rw [hr 23 (by decide), hr 25 (by decide)]; exact I.wd,
    by rw [hm]; exact I.wr,
    I.rem,
    by rw [hm]; exact I.w60,
    by rw [hm]; exact I.w70,
    by rw [hm]; exact I.aN,
    by rw [hm]; exact I.a240,
    by rw [hm]; exact I.a260,
    by rw [hm]; exact I.a280,
    by rw [hm]; exact I.a2a0,
    by rw [hm]; exact I.a2c0,
    by rw [hm]; exact I.a2e0,
    by rw [hm]; exact I.vf,
    by rw [hm]; exact I.lf,
    by rw [hm]; exact I.vg,
    by rw [hm]; exact I.lg,
    by rw [hm]; exact I.vd,
    by rw [hm]; exact I.ld,
    by rw [hm]; exact I.ve,
    by rw [hm]; exact I.le,
    fun e he => by rw [hm]; exact I.ww e he⟩

theorem iv_keep74 {B : Word} {M M' : Word → BitVec 8} (F : Fr B 0x3830)
    (h : ∀ x, Sep (B + 0x21A0 + BitVec.ofNat 32 0x74) 4 x 1 → M' x = M x) : SvKeepL B M M' [(0x74, 4)] :=
  fun e he hL => h _ (by
    have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
    have h1 := hL _ (List.mem_singleton_self _)
    dsimp only at h1
    have hS : (B + 0x21A0).toNat + 0x1690 ≤ 2 ^ 32 := by have := FS.hi; omega
    exact zfr_sep (a := BitVec.ofNat 32 0x74) (b := BitVec.ofNat 32 e) hS (by decide) (by decide) (by decide)
      (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega))

theorem iv_s0 {B : Word} {M : Word → BitVec 8} {f : Fin 32 → Word} {δ : Nat} {F G : Int} {fs gs : BitVec 8}
    {fv gv : Nat} (hfs : fs.toNat ≤ 1) (hgs : gs.toNat ≤ 1) (vf : sgnVal fs.toNat fv = F)
    (vg : sgnVal gs.toNat gv = G) (wd : W64 (f 23) (f 25) = δ) (r2 : f 2 = B + 0x21A0)
    (r22 : f 22 = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32))
    (w74 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32))
    (r10 : f 10 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32))
    (r11 : f 11 = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32))
    (r14 : f 14 = BitVec.ofNat 32 0x1) (r5 : f 5 = BitVec.ofNat 32 0x0) (r31 : f 31 = BitVec.ofNat 32 0x0)
    (r17 : f 17 = BitVec.ofNat 32 0x0) (r8 : f 8 = BitVec.ofNat 32 0x0) (r29 : f 29 = BitVec.ofNat 32 0x0)
    (r12 : f 12 = BitVec.ofNat 32 0x1) (r6 : f 6 = BitVec.ofNat 32 0x0) :
    EcDsRegs M f ⟨δ, lowestI F, lowestI G, 1, 0, 0, 1⟩ := by
  refine ⟨wd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r22, r2]; show W64 _ (memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 0x74)) = _
    rw [w74, w64_ofNat_split (lowestVal_lt _ _), lowestI_of hfs vf]
  · rw [r10, r11, w64_ofNat_split (lowestVal_lt _ _), lowestI_of hgs vg]
  · rw [r14, r5]; rfl
  · rw [r31, r17]; rfl
  · rw [r8, r29]; rfl
  · rw [r12, r6]; rfl

set_option maxHeartbeats 64000000 in
/-- **One batch** of the inversion of `s`, from its head at 0x1328: to 0x1556 when `g` is zero, and
otherwise back to the head after one `ivStep8`. -/
theorem iv_iter {B r3 r4 out bp s5v x26 : Word} {qx qy qz rv sv zv N : Nat} {W v : Nat → Word} {m : Machine} {st : Iv}
    (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (hN : 0 < N)
    (s : St m.mem SV m 0x1328 (reg m)) (I : IvInv B m v r3 r4 out bp s5v x26 qx qy qz rv sv zv N W st) (h0 : st.rem ≠ 0) :
    ∃ m', Steps m m' ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧
      ((st.g = 0 ∧ St m'.mem SV m' 0x1556 (reg m') ∧ IvInv B m' v r3 r4 out bp s5v x26 qx qy qz rv sv zv N W st) ∨
       (st.g ≠ 0 ∧ St m'.mem SV m' 0x1328 (reg m') ∧ IvInv B m' v r3 r4 out bp s5v x26 qx qy qz rv sv zv N W (ivStep8 N st))) := by
  have hrem' : BitVec.ofNat 32 st.rem ≠ 0 := Pv.ofNat_ne0 (by omega) I.rem
  rcases sv_ivhc (x21 := 0) (er := []) (es := []) F I.E I.V hret hO s m.mem (fun _ _ => rfl) I.sp I.g18 I.g19 I.g21 rfl I.g24 rfl I.g26 I.g27 (I.ww 0x24 (by decide)) (I.ww 0x28 (by decide)) (I.ww 0x2C (by decide)) (I.ww 0x30 (by decide)) (I.ww 0x34 (by decide)) (I.ww 0x38 (by decide)) (I.ww 0x3C (by decide)) (I.ww 0x40 (by decide)) (I.ww 0x44 (by decide)) (I.ww 0x48 (by decide)) (I.ww 0x4C (by decide)) (I.ww 0x50 (by decide)) (I.ww 0x54 (by decide)) (I.ww 0x58 (by decide)) rfl I.w60 (I.ww 0x64 (by decide)) (I.ww 0x68 (by decide)) (I.ww 0x6C (by decide)) I.w70 I.wr (I.ww 0x7C (by decide)) (I.ww 0x80 (by decide)) (I.ww 0x84 (by decide)) (I.ww 0x88 (by decide)) (I.ww 0x8C (by decide)) (I.ww 0x90 (by decide)) (I.ww 0x94 (by decide)) (I.ww 0x98 (by decide)) (I.ww 0x9C (by decide)) (I.ww 0xA0 (by decide)) (I.ww 0xA4 (by decide)) (I.ww 0xA8 (by decide)) (I.ww 0xAC (by decide)) (I.ww 0xB0 (by decide)) (I.ww 0xB4 (by decide)) (I.ww 0xB8 (by decide)) (I.ww 0xBC (by decide)) (I.ww 0xC0 (by decide)) (I.ww 0xC4 (by decide)) (I.ww 0xC8 (by decide)) (I.ww 0xCC (by decide)) (I.ww 0xD0 (by decide)) (I.ww 0xD4 (by decide)) (I.ww 0xD8 (by decide)) (I.ww 0xDC (by decide)) (I.ww 0xE0 (by decide)) (I.ww 0xE4 (by decide)) (I.ww 0xE8 (by decide)) (I.ww 0xEC (by decide)) (I.ww 0xF0 (by decide)) (I.ww 0xF4 (by decide)) (I.ww 0xF8 (by decide)) (I.ww 0xFC (by decide)) (I.ww 0x100 (by decide)) (I.ww 0x104 (by decide)) (I.ww 0x108 (by decide)) (I.ww 0x10C (by decide)) (I.ww 0x110 (by decide)) (I.ww 0x114 (by decide)) (I.ww 0x118 (by decide)) (I.ww 0x11C (by decide)) (I.ww 0x120 (by decide)) (I.ww 0x124 (by decide)) (I.ww 0x128 (by decide)) (I.ww 0x12C (by decide)) (I.ww 0x130 (by decide)) I.a240 I.a260 I.a280 I.a2a0 I.a2c0 I.a2e0 rfl rfl rfl rfl rfl rfl rfl rfl I.IC I.EC hrem' with ⟨h, _⟩ | ⟨n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_a0, r1_a1, r1_18, r1_19, r1_21, r1_23, r1_24, r1_25, r1_26, r1_27, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_3c, w1_40, w1_44, w1_48, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, b1_440, b1_1040, b1_13a0, b1_14a0, a1_240, a1_260, a1_280, a1_2a0, a1_2c0, a1_2e0, a1_420, a1_1020, a1_1380, a1_1480⟩
  · exact absurd trivial h
  have I1 : IvInv B n1 v r3 r4 out bp s5v x26 qx qy qz rv sv zv N W st := by
    refine ⟨E1, I.IC.sv F fR1, I.EC.sv F fR1, I.UC.sv F fR1, V1, r1_2, by rw [r1_3]; exact I.g3, by rw [r1_4]; exact I.g4, r1_18, r1_19, r1_21, r1_24, r1_26, r1_27, by rw [r1_23, r1_25]; exact I.wd, w1_78, I.rem, w1_60, w1_70, by rw [accV_dataR F fR1 (by decide) (by decide)]; exact I.aN, a1_240, a1_260, a1_280, a1_2a0, a1_2c0, a1_2e0, by rw [b1_13a0, a1_1380]; exact I.vf, by rw [b1_13a0]; exact I.lf, by rw [b1_14a0, a1_1480]; exact I.vg, by rw [b1_14a0]; exact I.lg, by rw [b1_1040, a1_1020]; exact I.vd, by rw [b1_1040]; exact I.ld, by rw [b1_440, a1_420]; exact I.ve, by rw [b1_440]; exact I.le, fun e he => ?_⟩
    simp only [ivWords, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact w1_24
    · exact w1_28
    · exact w1_2c
    · exact w1_30
    · exact w1_34
    · exact w1_38
    · exact w1_3c
    · exact w1_40
    · exact w1_44
    · exact w1_48
    · exact w1_4c
    · exact w1_50
    · exact w1_54
    · exact w1_58
    · exact w1_64
    · exact w1_68
    · exact w1_6c
    · exact w1_7c
    · exact w1_80
    · exact w1_84
    · exact w1_88
    · exact w1_8c
    · exact w1_90
    · exact w1_94
    · exact w1_98
    · exact w1_9c
    · exact w1_a0
    · exact w1_a4
    · exact w1_a8
    · exact w1_ac
    · exact w1_b0
    · exact w1_b4
    · exact w1_b8
    · exact w1_bc
    · exact w1_c0
    · exact w1_c4
    · exact w1_c8
    · exact w1_cc
    · exact w1_d0
    · exact w1_d4
    · exact w1_d8
    · exact w1_dc
    · exact w1_e0
    · exact w1_e4
    · exact w1_e8
    · exact w1_ec
    · exact w1_f0
    · exact w1_f4
    · exact w1_f8
    · exact w1_fc
    · exact w1_100
    · exact w1_104
    · exact w1_108
    · exact w1_10c
    · exact w1_110
    · exact w1_114
    · exact w1_118
    · exact w1_11c
    · exact w1_120
    · exact w1_124
    · exact w1_128
    · exact w1_12c
    · exact w1_130
  obtain ⟨m2, c2, k2, h2⟩ := ec_scan F E1.self 8 0 rfl s1 (by rw [r1_a0]; rfl)
    (by rw [r1_a1]; exact (add_ofNat_zero _).symm) (fun k hk => absurd hk (Nat.not_lt_zero _))
  have kk : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 21, 23, 24, 25, 26, 27] → reg m2 q = reg n1 q := fun q hq =>
    k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  rcases h2 with ⟨hzr, s2⟩ | ⟨hnz, s2⟩
  · have m2m : m2.mem = n1.mem := s2.mem
    have hg : st.g = 0 := by
      rw [← I1.vg, sv_zero.2]
      exact (accV_zero_iff 8).2 hzr
    exact ⟨m2, c1.trans c2, fun x hx => by rw [m2m, fR1 x hx], .inl ⟨hg, ⟨s2.pc, rfl, fun _ => rfl⟩,
      I1.of m2m kk⟩⟩
  have m2m : m2.mem = n1.mem := s2.mem
  have hg : st.g ≠ 0 := by
    rw [← I1.vg]; intro h
    exact hnz ((accV_zero_iff 8).1 (sv_zero.1 h))
  have s2' : St m2.mem SV m2 0x134C (reg m2) := ⟨s2.pc, rfl, fun _ => rfl⟩
  have I2 := I1.of m2m kk
  have hns := umin_ofNat I.rem
  have hn : min st.rem 62 - 1 + 1 = min st.rem 62 := by omega
  rcases sv_iva (x21 := 0) (er := []) (es := []) F I2.E I2.V hret hO s2' m2.mem (fun _ _ => rfl) I2.sp I2.g18 I2.g19 I2.g21 rfl I2.g24 rfl I2.g26 I2.g27 (I2.ww 0x24 (by decide)) (I2.ww 0x28 (by decide)) (I2.ww 0x2C (by decide)) (I2.ww 0x30 (by decide)) (I2.ww 0x34 (by decide)) (I2.ww 0x38 (by decide)) (I2.ww 0x3C (by decide)) (I2.ww 0x40 (by decide)) (I2.ww 0x44 (by decide)) (I2.ww 0x48 (by decide)) (I2.ww 0x4C (by decide)) (I2.ww 0x50 (by decide)) (I2.ww 0x54 (by decide)) (I2.ww 0x58 (by decide)) rfl I2.w60 (I2.ww 0x64 (by decide)) (I2.ww 0x68 (by decide)) (I2.ww 0x6C (by decide)) I2.w70 I2.wr (I2.ww 0x7C (by decide)) (I2.ww 0x80 (by decide)) (I2.ww 0x84 (by decide)) (I2.ww 0x88 (by decide)) (I2.ww 0x8C (by decide)) (I2.ww 0x90 (by decide)) (I2.ww 0x94 (by decide)) (I2.ww 0x98 (by decide)) (I2.ww 0x9C (by decide)) (I2.ww 0xA0 (by decide)) (I2.ww 0xA4 (by decide)) (I2.ww 0xA8 (by decide)) (I2.ww 0xAC (by decide)) (I2.ww 0xB0 (by decide)) (I2.ww 0xB4 (by decide)) (I2.ww 0xB8 (by decide)) (I2.ww 0xBC (by decide)) (I2.ww 0xC0 (by decide)) (I2.ww 0xC4 (by decide)) (I2.ww 0xC8 (by decide)) (I2.ww 0xCC (by decide)) (I2.ww 0xD0 (by decide)) (I2.ww 0xD4 (by decide)) (I2.ww 0xD8 (by decide)) (I2.ww 0xDC (by decide)) (I2.ww 0xE0 (by decide)) (I2.ww 0xE4 (by decide)) (I2.ww 0xE8 (by decide)) (I2.ww 0xEC (by decide)) (I2.ww 0xF0 (by decide)) (I2.ww 0xF4 (by decide)) (I2.ww 0xF8 (by decide)) (I2.ww 0xFC (by decide)) (I2.ww 0x100 (by decide)) (I2.ww 0x104 (by decide)) (I2.ww 0x108 (by decide)) (I2.ww 0x10C (by decide)) (I2.ww 0x110 (by decide)) (I2.ww 0x114 (by decide)) (I2.ww 0x118 (by decide)) (I2.ww 0x11C (by decide)) (I2.ww 0x120 (by decide)) (I2.ww 0x124 (by decide)) (I2.ww 0x128 (by decide)) (I2.ww 0x12C (by decide)) (I2.ww 0x130 (by decide)) I2.a240 I2.a260 I2.a280 I2.a2a0 I2.a2c0 I2.a2e0 rfl rfl rfl rfl rfl rfl rfl rfl I2.IC I2.EC hrem' I2.lf I2.lg with ⟨h, _⟩ | ⟨n3, c3, s3, E3, V3, fR3, r3_2, r3_3, r3_4, r3_5, r3_6, r3_8, r3_9, r3_a0, r3_a1, r3_a2, r3_a4, r3_a6, r3_a7, r3_18, r3_19, r3_21, r3_22, r3_23, r3_24, r3_25, r3_26, r3_27, r3_29, r3_31, w3_24, w3_28, w3_2c, w3_30, w3_34, w3_38, w3_3c, w3_40, w3_44, w3_48, w3_4c, w3_50, w3_54, w3_58, w3_5c, w3_60, w3_64, w3_68, w3_6c, w3_70, w3_74, w3_78, w3_7c, w3_80, w3_84, w3_88, w3_8c, w3_90, w3_94, w3_98, w3_9c, w3_a0, w3_a4, w3_a8, w3_ac, w3_b0, w3_b4, w3_b8, w3_bc, w3_c0, w3_c4, w3_c8, w3_cc, w3_d0, w3_d4, w3_d8, w3_dc, w3_e0, w3_e4, w3_e8, w3_ec, w3_f0, w3_f4, w3_f8, w3_fc, w3_100, w3_104, w3_108, w3_10c, w3_110, w3_114, w3_118, w3_11c, w3_120, w3_124, w3_128, w3_12c, w3_130, b3_440, b3_1040, b3_13a0, b3_14a0, a3_240, a3_260, a3_280, a3_2a0, a3_2c0, a3_2e0, a3_420, a3_1020, a3_1380, a3_1480⟩
  · exact absurd trivial h
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  obtain ⟨n4, M4, c4, s4, h4, k4, f4, -⟩ := ec_loop (min st.rem 62 - 1) E3.self s3
    (iv_s0 (δ := st.δ) I2.lf I2.lg I2.vf I2.vg (by rw [r3_23, r3_25]; exact I2.wd) r3_2 r3_22 w3_74 r3_a0 r3_a1 r3_a4 r3_5
      r3_31 r3_a7 r3_8 r3_29 r3_a2 r3_6)
    (by rw [hn]; exact r3_a6.trans hns) (by omega)
    (by rw [r3_2]; exact zfr_al FS (c := 0x74) (by decide) (by decide))
    (by rw [r3_2]; exact zfr_code FS (c := 0x74) (by decide))
  have hm4 : n4.mem = M4 := s4.mem
  subst hm4
  rw [hn] at h4
  have f4' : ∀ x, Sep (B + 0x21A0 + BitVec.ofNat 32 0x74) 4 x 1 → n4.mem x = n3.mem x := fun x hx => f4 x (by rw [r3_2]; exact hx)
  have K4 := iv_keep74 F f4'
  have R4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x hx => f4' x (svR_hi (c := 0x74) (l := 4) hx (by decide))
  have CH3 : ∀ x, SvR B x → n3.mem x = m.mem x := fun x hx => by rw [fR3 x hx, m2m, fR1 x hx]
  have CH4 : ∀ x, SvR B x → n4.mem x = m.mem x := fun x hx => by rw [R4 x hx, CH3 x hx]
  rcases sv_ivb (x21 := 0) (er := []) (es := []) (w5c := 0) (s8v := 0) F (E3.fr F R4) (V3.keepL K4 (by decide)) hret hO s4 n4.mem (fun _ _ => rfl) ((k4 2 (by decide)).trans r3_2) ((k4 18 (by decide)).trans r3_18) ((k4 19 (by decide)).trans r3_19) ((k4 21 (by decide)).trans r3_21) rfl rfl ((k4 26 (by decide)).trans r3_26) ((k4 27 (by decide)).trans r3_27) ((K4.w32 (by decide) (by decide)).trans w3_24) ((K4.w32 (by decide) (by decide)).trans w3_28) ((K4.w32 (by decide) (by decide)).trans w3_2c) ((K4.w32 (by decide) (by decide)).trans w3_30) ((K4.w32 (by decide) (by decide)).trans w3_34) ((K4.w32 (by decide) (by decide)).trans w3_38) ((K4.w32 (by decide) (by decide)).trans w3_3c) ((K4.w32 (by decide) (by decide)).trans w3_40) ((K4.w32 (by decide) (by decide)).trans w3_44) ((K4.w32 (by decide) (by decide)).trans w3_48) ((K4.w32 (by decide) (by decide)).trans w3_4c) ((K4.w32 (by decide) (by decide)).trans w3_50) ((K4.w32 (by decide) (by decide)).trans w3_54) ((K4.w32 (by decide) (by decide)).trans w3_58) ((K4.w32 (by decide) (by decide)).trans w3_60) ((K4.w32 (by decide) (by decide)).trans w3_64) ((K4.w32 (by decide) (by decide)).trans w3_68) ((K4.w32 (by decide) (by decide)).trans w3_6c) ((K4.w32 (by decide) (by decide)).trans w3_70) ((K4.w32 (by decide) (by decide)).trans w3_78) ((K4.w32 (by decide) (by decide)).trans w3_7c) ((K4.w32 (by decide) (by decide)).trans w3_80) ((K4.w32 (by decide) (by decide)).trans w3_84) ((K4.w32 (by decide) (by decide)).trans w3_88) ((K4.w32 (by decide) (by decide)).trans w3_8c) ((K4.w32 (by decide) (by decide)).trans w3_90) ((K4.w32 (by decide) (by decide)).trans w3_94) ((K4.w32 (by decide) (by decide)).trans w3_98) ((K4.w32 (by decide) (by decide)).trans w3_9c) ((K4.w32 (by decide) (by decide)).trans w3_a0) ((K4.w32 (by decide) (by decide)).trans w3_a4) ((K4.w32 (by decide) (by decide)).trans w3_a8) ((K4.w32 (by decide) (by decide)).trans w3_ac) ((K4.w32 (by decide) (by decide)).trans w3_b0) ((K4.w32 (by decide) (by decide)).trans w3_b4) ((K4.w32 (by decide) (by decide)).trans w3_b8) ((K4.w32 (by decide) (by decide)).trans w3_bc) ((K4.w32 (by decide) (by decide)).trans w3_c0) ((K4.w32 (by decide) (by decide)).trans w3_c4) ((K4.w32 (by decide) (by decide)).trans w3_c8) ((K4.w32 (by decide) (by decide)).trans w3_cc) ((K4.w32 (by decide) (by decide)).trans w3_d0) ((K4.w32 (by decide) (by decide)).trans w3_d4) ((K4.w32 (by decide) (by decide)).trans w3_d8) ((K4.w32 (by decide) (by decide)).trans w3_dc) ((K4.w32 (by decide) (by decide)).trans w3_e0) ((K4.w32 (by decide) (by decide)).trans w3_e4) ((K4.w32 (by decide) (by decide)).trans w3_e8) ((K4.w32 (by decide) (by decide)).trans w3_ec) ((K4.w32 (by decide) (by decide)).trans w3_f0) ((K4.w32 (by decide) (by decide)).trans w3_f4) ((K4.w32 (by decide) (by decide)).trans w3_f8) ((K4.w32 (by decide) (by decide)).trans w3_fc) ((K4.w32 (by decide) (by decide)).trans w3_100) ((K4.w32 (by decide) (by decide)).trans w3_104) ((K4.w32 (by decide) (by decide)).trans w3_108) ((K4.w32 (by decide) (by decide)).trans w3_10c) ((K4.w32 (by decide) (by decide)).trans w3_110) ((K4.w32 (by decide) (by decide)).trans w3_114) ((K4.w32 (by decide) (by decide)).trans w3_118) ((K4.w32 (by decide) (by decide)).trans w3_11c) ((K4.w32 (by decide) (by decide)).trans w3_120) ((K4.w32 (by decide) (by decide)).trans w3_124) ((K4.w32 (by decide) (by decide)).trans w3_128) ((K4.w32 (by decide) (by decide)).trans w3_12c) ((K4.w32 (by decide) (by decide)).trans w3_130) ((K4.acc (by decide) (by decide)).trans a3_240) ((K4.acc (by decide) (by decide)).trans a3_260) ((K4.acc (by decide) (by decide)).trans a3_280) ((K4.acc (by decide) (by decide)).trans a3_2a0) ((K4.acc (by decide) (by decide)).trans a3_2c0) ((K4.acc (by decide) (by decide)).trans a3_2e0) ((K4.acc (by decide) (by decide)).trans a3_420) ((K4.acc (by decide) (by decide)).trans a3_1020) ((K4.acc (by decide) (by decide)).trans a3_1380) ((K4.acc (by decide) (by decide)).trans a3_1480) ((K4.b8 (by decide) (by decide)).trans b3_440) ((K4.b8 (by decide) (by decide)).trans b3_1040) ((K4.b8 (by decide) (by decide)).trans b3_13a0) ((K4.b8 (by decide) (by decide)).trans b3_14a0) (I.IC.sv F CH4) (I.EC.sv F CH4) ((k4 24 (by decide)).trans r3_24) rfl rfl rfl rfl rfl rfl rfl rfl ((K4.w32 (by decide) (by decide)).trans (w3_5c.trans hns)) (by omega) (Nat.min_le_right _ _) (I.UC.sv F CH4) I2.lf I2.lg I2.ld I2.le with ⟨h, _⟩ | ⟨σa, Aa, ea, la, σb, Ab, eb, lb, σc, Ac, ec, lc,
      σd, Ad, ed, ld, n5, c5, s5, E5, V5, fR5, r5_2, r5_3, r5_4, r5_18, r5_19, r5_21, r5_23, r5_24, r5_25, r5_26, r5_27, w5_24, w5_28, w5_2c, w5_30, w5_34, w5_38, w5_3c, w5_40, w5_44, w5_48, w5_4c, w5_50, w5_54, w5_58, w5_5c, w5_60, w5_64, w5_68, w5_6c, w5_70, w5_78, w5_7c, w5_80, w5_84, w5_88, w5_8c, w5_90, w5_94, w5_98, w5_9c, w5_a0, w5_a4, w5_a8, w5_ac, w5_b0, w5_b4, w5_b8, w5_bc, w5_c0, w5_c4, w5_c8, w5_cc, w5_d0, w5_d4, w5_d8, w5_dc, w5_e0, w5_e4, w5_e8, w5_ec, w5_f0, w5_f4, w5_f8, w5_fc, w5_100, w5_104, w5_108, w5_10c, w5_110, w5_114, w5_118, w5_11c, w5_120, w5_124, w5_128, w5_12c, w5_130, w5_320, w5_324, w5_328, w5_32c, w5_330, w5_334, w5_338, w5_33c, b5_440, b5_a40, b5_a64, b5_1040, b5_13a0, b5_14a0, a5_240, a5_260, a5_280, a5_2a0, a5_2c0, a5_2e0, a5_420, a5_a20, a5_a44, a5_1020, a5_1380, a5_1480⟩
  · exact absurd (sc4 _ _ _ _) h
  have CH5 : ∀ x, SvR B x → n5.mem x = m.mem x := fun x hx => by rw [fR5 x hx, CH4 x hx]
  have hNv : accV n4.mem (BitVec.ofNat 32 0x3FCC4268) 8 = N := by
    rw [accV_dataR F CH4 (by decide) (by decide), I.aN]
  have hMI : (BitVec.ofNat 32 0x11FF43B1 : Word).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755 : Word).toNat = ivMI :=
    rfl
  obtain ⟨Zd, -, -, Zu, Zv, Zq, Zr⟩ := h4
  have eu : i64Val ((reg n4 a4).toNat + 2 ^ 32 * (reg n4 (5 : Fin 32)).toNat) =
      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).u := by rw [← Zu]
  have ev : i64Val ((reg n4 (31 : Fin 32)).toNat + 2 ^ 32 * (reg n4 a7).toNat) =
      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).v := by rw [← Zv]
  have eq : i64Val ((reg n4 (8 : Fin 32)).toNat + 2 ^ 32 * (reg n4 (29 : Fin 32)).toNat) =
      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).q := by rw [← Zq]
  have er : i64Val ((reg n4 a2).toNat + 2 ^ 32 * (reg n4 (6 : Fin 32)).toNat) =
      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).r := by rw [← Zr]
  rw [I2.vf, I2.vg, eu, ev] at ea
  rw [I2.vf, I2.vg, eq, er] at eb
  rw [I2.vd, I2.ve, eu, ev] at ec
  rw [I2.vd, I2.ve, eq, er] at ed
  obtain ⟨vf', lf'⟩ := fgUpd8_of la ea (tn8 (by omega)) rfl
  obtain ⟨vg', lg'⟩ := fgUpd8_of lb eb (tn8 (by omega)) rfl
  rw [hNv, hMI] at b5_440 a5_420 b5_1040 a5_1020
  obtain ⟨vd', ld'⟩ := deUpd8_of lc hN ec (tn8 (Nat.lt_of_le_of_lt (lrsm8_le lc) (by decide))) rfl
  obtain ⟨ve', le'⟩ := deUpd8_of ld hN ed (tn8 (Nat.lt_of_le_of_lt (lrsm8_le ld) (by decide))) rfl
  refine ⟨n5, c1.trans (c2.trans (c3.trans (c4.trans c5))), CH5, .inr ⟨hg, s5, E5, I.IC.sv F CH5, I.EC.sv F CH5, I.UC.sv F CH5, V5, r5_2, by rw [r5_3, k4 3 (by decide), r3_3]; exact I2.g3, by rw [r5_4, k4 4 (by decide), r3_4]; exact I2.g4, r5_18, r5_19, r5_21, r5_24, r5_26, r5_27, by rw [r5_23, r5_25]; exact Zd, by rw [w5_78, ofNat_sub_ofNat (Nat.min_le_left _ _) I.rem]; rfl, by simp only [ivStep8]; have := I.rem; omega, w5_60, w5_70, by rw [accV_dataR F CH5 (by decide) (by decide)]; exact I.aN, a5_240, a5_260, a5_280, a5_2a0, a5_2c0, a5_2e0, by rw [b5_13a0, a5_1380]; exact vf', by rw [b5_13a0]; exact lf', by rw [b5_14a0, a5_1480]; exact vg', by rw [b5_14a0]; exact lg', by rw [b5_1040, a5_1020]; exact vd', by rw [b5_1040]; exact ld', by rw [b5_440, a5_420]; exact ve', by rw [b5_440]; exact le', fun e he => ?_⟩⟩
  simp only [ivWords, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact w5_24
  · exact w5_28
  · exact w5_2c
  · exact w5_30
  · exact w5_34
  · exact w5_38
  · exact w5_3c
  · exact w5_40
  · exact w5_44
  · exact w5_48
  · exact w5_4c
  · exact w5_50
  · exact w5_54
  · exact w5_58
  · exact w5_64
  · exact w5_68
  · exact w5_6c
  · exact w5_7c
  · exact w5_80
  · exact w5_84
  · exact w5_88
  · exact w5_8c
  · exact w5_90
  · exact w5_94
  · exact w5_98
  · exact w5_9c
  · exact w5_a0
  · exact w5_a4
  · exact w5_a8
  · exact w5_ac
  · exact w5_b0
  · exact w5_b4
  · exact w5_b8
  · exact w5_bc
  · exact w5_c0
  · exact w5_c4
  · exact w5_c8
  · exact w5_cc
  · exact w5_d0
  · exact w5_d4
  · exact w5_d8
  · exact w5_dc
  · exact w5_e0
  · exact w5_e4
  · exact w5_e8
  · exact w5_ec
  · exact w5_f0
  · exact w5_f4
  · exact w5_f8
  · exact w5_fc
  · exact w5_100
  · exact w5_104
  · exact w5_108
  · exact w5_10c
  · exact w5_110
  · exact w5_114
  · exact w5_118
  · exact w5_11c
  · exact w5_120
  · exact w5_124
  · exact w5_128
  · exact w5_12c
  · exact w5_130

/-- **The batches** of the inversion of `s`, from its head at 0x1328 back to it, as many as `ivLoop8` runs. -/
theorem iv_loop {B r3 r4 out bp s5v x26 : Word} {qx qy qz rv sv zv N : Nat} {W v : Nat → Word} (F : Fr B 0x3830)
    (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (hN : 0 < N) :
    ∀ k {m : Machine} {st : Iv}, St m.mem SV m 0x1328 (reg m) →
      IvInv B m v r3 r4 out bp s5v x26 qx qy qz rv sv zv N W st →
      ∃ m', Steps m m' ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ St m'.mem SV m' 0x1328 (reg m') ∧
        IvInv B m' v r3 r4 out bp s5v x26 qx qy qz rv sv zv N W (ivLoop8 N k st)
  | 0, m, st, s, I => ⟨m, .refl m, fun _ _ => rfl, s, I⟩
  | k + 1, m, st, s, I => by
    by_cases h0 : st.rem = 0 ∨ st.g = 0
    · rw [ivLoop8, ite_eq_left h0]; exact ⟨m, .refl m, fun _ _ => rfl, s, I⟩
    rw [ivLoop8, ite_eq_right h0]
    obtain ⟨n1, c1, fr1, h1⟩ := iv_iter F hret hO hN s I (fun h => h0 (.inl h))
    rcases h1 with ⟨hg, -, -⟩ | ⟨-, s1, I1⟩
    · exact absurd (.inr hg) h0
    obtain ⟨n2, c2, fr2, s2, I2⟩ := iv_loop F hret hO hN k s1 I1
    exact ⟨n2, c1.trans c2, fun x hx => by rw [fr2 x hx, fr1 x hx], s2, I2⟩

set_option maxHeartbeats 16000000 in
/-- **The exit** of the inversion of `s`: from its head at 0x1328 to 0x1556 once no steps are left or
`g` is zero. -/
theorem iv_exit {B r3 r4 out bp s5v x26 : Word} {qx qy qz rv sv zv N : Nat} {W v : Nat → Word} {m : Machine} {st : Iv}
    (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (hN : 0 < N)
    (s : St m.mem SV m 0x1328 (reg m)) (I : IvInv B m v r3 r4 out bp s5v x26 qx qy qz rv sv zv N W st) (h0 : st.rem = 0 ∨ st.g = 0) :
    ∃ m', Steps m m' ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ St m'.mem SV m' 0x1556 (reg m') ∧
      IvInv B m' v r3 r4 out bp s5v x26 qx qy qz rv sv zv N W st := by
  by_cases hr : st.rem = 0
  · have hrem' : BitVec.ofNat 32 st.rem = 0 := by rw [hr]; rfl
    rcases sv_ivhx (x21 := 0) (er := []) (es := []) F I.E I.V hret hO s m.mem (fun _ _ => rfl) I.sp I.g18 I.g19 I.g21 rfl I.g24 rfl I.g26 I.g27 (I.ww 0x24 (by decide)) (I.ww 0x28 (by decide)) (I.ww 0x2C (by decide)) (I.ww 0x30 (by decide)) (I.ww 0x34 (by decide)) (I.ww 0x38 (by decide)) (I.ww 0x3C (by decide)) (I.ww 0x40 (by decide)) (I.ww 0x44 (by decide)) (I.ww 0x48 (by decide)) (I.ww 0x4C (by decide)) (I.ww 0x50 (by decide)) (I.ww 0x54 (by decide)) (I.ww 0x58 (by decide)) rfl I.w60 (I.ww 0x64 (by decide)) (I.ww 0x68 (by decide)) (I.ww 0x6C (by decide)) I.w70 I.wr (I.ww 0x7C (by decide)) (I.ww 0x80 (by decide)) (I.ww 0x84 (by decide)) (I.ww 0x88 (by decide)) (I.ww 0x8C (by decide)) (I.ww 0x90 (by decide)) (I.ww 0x94 (by decide)) (I.ww 0x98 (by decide)) (I.ww 0x9C (by decide)) (I.ww 0xA0 (by decide)) (I.ww 0xA4 (by decide)) (I.ww 0xA8 (by decide)) (I.ww 0xAC (by decide)) (I.ww 0xB0 (by decide)) (I.ww 0xB4 (by decide)) (I.ww 0xB8 (by decide)) (I.ww 0xBC (by decide)) (I.ww 0xC0 (by decide)) (I.ww 0xC4 (by decide)) (I.ww 0xC8 (by decide)) (I.ww 0xCC (by decide)) (I.ww 0xD0 (by decide)) (I.ww 0xD4 (by decide)) (I.ww 0xD8 (by decide)) (I.ww 0xDC (by decide)) (I.ww 0xE0 (by decide)) (I.ww 0xE4 (by decide)) (I.ww 0xE8 (by decide)) (I.ww 0xEC (by decide)) (I.ww 0xF0 (by decide)) (I.ww 0xF4 (by decide)) (I.ww 0xF8 (by decide)) (I.ww 0xFC (by decide)) (I.ww 0x100 (by decide)) (I.ww 0x104 (by decide)) (I.ww 0x108 (by decide)) (I.ww 0x10C (by decide)) (I.ww 0x110 (by decide)) (I.ww 0x114 (by decide)) (I.ww 0x118 (by decide)) (I.ww 0x11C (by decide)) (I.ww 0x120 (by decide)) (I.ww 0x124 (by decide)) (I.ww 0x128 (by decide)) (I.ww 0x12C (by decide)) (I.ww 0x130 (by decide)) I.a240 I.a260 I.a280 I.a2a0 I.a2c0 I.a2e0 rfl rfl rfl rfl rfl rfl rfl rfl I.IC I.EC hrem' with ⟨h, _⟩ | ⟨n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_18, r1_19, r1_21, r1_23, r1_24, r1_25, r1_26, r1_27, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_3c, w1_40, w1_44, w1_48, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, b1_440, b1_1040, b1_13a0, b1_14a0, a1_240, a1_260, a1_280, a1_2a0, a1_2c0, a1_2e0, a1_420, a1_1020, a1_1380, a1_1480⟩
    · exact absurd trivial h
    refine ⟨n1, c1, fR1, s1, E1, I.IC.sv F fR1, I.EC.sv F fR1, I.UC.sv F fR1, V1, r1_2, by rw [r1_3]; exact I.g3, by rw [r1_4]; exact I.g4, r1_18, r1_19, r1_21, r1_24, r1_26, r1_27, by rw [r1_23, r1_25]; exact I.wd, w1_78, I.rem, w1_60, w1_70, by rw [accV_dataR F fR1 (by decide) (by decide)]; exact I.aN, a1_240, a1_260, a1_280, a1_2a0, a1_2c0, a1_2e0, by rw [b1_13a0, a1_1380]; exact I.vf, by rw [b1_13a0]; exact I.lf, by rw [b1_14a0, a1_1480]; exact I.vg, by rw [b1_14a0]; exact I.lg, by rw [b1_1040, a1_1020]; exact I.vd, by rw [b1_1040]; exact I.ld, by rw [b1_440, a1_420]; exact I.ve, by rw [b1_440]; exact I.le, fun e he => ?_⟩
    simp only [ivWords, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact w1_24
    · exact w1_28
    · exact w1_2c
    · exact w1_30
    · exact w1_34
    · exact w1_38
    · exact w1_3c
    · exact w1_40
    · exact w1_44
    · exact w1_48
    · exact w1_4c
    · exact w1_50
    · exact w1_54
    · exact w1_58
    · exact w1_64
    · exact w1_68
    · exact w1_6c
    · exact w1_7c
    · exact w1_80
    · exact w1_84
    · exact w1_88
    · exact w1_8c
    · exact w1_90
    · exact w1_94
    · exact w1_98
    · exact w1_9c
    · exact w1_a0
    · exact w1_a4
    · exact w1_a8
    · exact w1_ac
    · exact w1_b0
    · exact w1_b4
    · exact w1_b8
    · exact w1_bc
    · exact w1_c0
    · exact w1_c4
    · exact w1_c8
    · exact w1_cc
    · exact w1_d0
    · exact w1_d4
    · exact w1_d8
    · exact w1_dc
    · exact w1_e0
    · exact w1_e4
    · exact w1_e8
    · exact w1_ec
    · exact w1_f0
    · exact w1_f4
    · exact w1_f8
    · exact w1_fc
    · exact w1_100
    · exact w1_104
    · exact w1_108
    · exact w1_10c
    · exact w1_110
    · exact w1_114
    · exact w1_118
    · exact w1_11c
    · exact w1_120
    · exact w1_124
    · exact w1_128
    · exact w1_12c
    · exact w1_130
  obtain ⟨n1, c1, fr1, h1⟩ := iv_iter F hret hO hN s I hr
  rcases h1 with ⟨-, s1, I1⟩ | ⟨hg, -, -⟩
  · exact ⟨n1, c1, fr1, s1, I1⟩
  · exact absurd (h0.resolve_left hr) hg

end C3.RV32.Sv
