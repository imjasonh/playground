import C3BootProofs.Proofs.ScalarMontFacts

/-! # `montgomery_mul`'s body, segments 0 to 2

Each theorem steps 40 instructions. `scripts/gen-scalar-mont.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem smm_g0 {M0 Mi : Word → BitVec 8} {B F outp xp yp G3 G4 : Word} {n : Machine}
    (s : St Mi B n 0x34 (reg n)) (hc : CodeIn Mi B scalar29MontMulCode)
    (fr : ∀ x, Sep F 0x190 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q10 : reg n a0 = outp)
    (q11 : reg n a1 = xp)
    (q12 : reg n a2 = yp)
    (sl15C : memLoad32 Mi (F + 0x15C) = memLoad32 M0 (F + 0x15C))
    (sl160 : memLoad32 Mi (F + 0x160) = memLoad32 M0 (F + 0x160))
    (sl164 : memLoad32 Mi (F + 0x164) = memLoad32 M0 (F + 0x164))
    (sl168 : memLoad32 Mi (F + 0x168) = memLoad32 M0 (F + 0x168))
    (sl16C : memLoad32 Mi (F + 0x16C) = memLoad32 M0 (F + 0x16C))
    (sl170 : memLoad32 Mi (F + 0x170) = memLoad32 M0 (F + 0x170))
    (sl174 : memLoad32 Mi (F + 0x174) = memLoad32 M0 (F + 0x174))
    (sl178 : memLoad32 Mi (F + 0x178) = memLoad32 M0 (F + 0x178))
    (sl17C : memLoad32 Mi (F + 0x17C) = memLoad32 M0 (F + 0x17C))
    (sl180 : memLoad32 Mi (F + 0x180) = memLoad32 M0 (F + 0x180))
    (sl184 : memLoad32 Mi (F + 0x184) = memLoad32 M0 (F + 0x184))
    (sl188 : memLoad32 Mi (F + 0x188) = memLoad32 M0 (F + 0x188))
    (sl18C : memLoad32 Mi (F + 0x18C) = memLoad32 M0 (F + 0x18C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v23 v24 v25 v26 v27 v28 v30 v31 v32 v33 v34 v35 v36 v38 v39 : Word),
      Steps n n' ∧
      St M' B n' 0xC2 (reg n') ∧
      CodeIn M' B scalar29MontMulCode ∧
      (∀ x, Sep F 0x190 x 1 → M' x = M0 x) ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v9 ∧
      reg n' (6 : Fin 32) = v33 ∧
      reg n' (8 : Fin 32) = v35 ∧
      reg n' (9 : Fin 32) = v32 ∧
      reg n' a0 = v24 ∧
      reg n' a1 = v30 ∧
      reg n' a2 = yp ∧
      reg n' a3 = v31 ∧
      reg n' a4 = v39 ∧
      reg n' a5 = v34 ∧
      reg n' a6 = v27 ∧
      reg n' a7 = v38 ∧
      reg n' (19 : Fin 32) = yp ∧
      reg n' (20 : Fin 32) = v7 ∧
      reg n' (21 : Fin 32) = v10 ∧
      reg n' (22 : Fin 32) = v5 ∧
      reg n' (25 : Fin 32) = xp ∧
      reg n' (26 : Fin 32) = v6 ∧
      reg n' (28 : Fin 32) = v8 ∧
      reg n' (29 : Fin 32) = v4 ∧
      reg n' (30 : Fin 32) = v3 ∧
      reg n' (31 : Fin 32) = v23 ∧
      memLoad32 M' (F + 0xF8) = outp ∧
      memLoad32 M' (F + 0x10C) = v21 ∧
      memLoad32 M' (F + 0x110) = v28 ∧
      memLoad32 M' (F + 0x11C) = v36 ∧
      memLoad32 M' (F + 0x15C) = memLoad32 M0 (F + 0x15C) ∧
      memLoad32 M' (F + 0x160) = memLoad32 M0 (F + 0x160) ∧
      memLoad32 M' (F + 0x164) = memLoad32 M0 (F + 0x164) ∧
      memLoad32 M' (F + 0x168) = memLoad32 M0 (F + 0x168) ∧
      memLoad32 M' (F + 0x16C) = memLoad32 M0 (F + 0x16C) ∧
      memLoad32 M' (F + 0x170) = memLoad32 M0 (F + 0x170) ∧
      memLoad32 M' (F + 0x174) = memLoad32 M0 (F + 0x174) ∧
      memLoad32 M' (F + 0x178) = memLoad32 M0 (F + 0x178) ∧
      memLoad32 M' (F + 0x17C) = memLoad32 M0 (F + 0x17C) ∧
      memLoad32 M' (F + 0x180) = memLoad32 M0 (F + 0x180) ∧
      memLoad32 M' (F + 0x184) = memLoad32 M0 (F + 0x184) ∧
      memLoad32 M' (F + 0x188) = memLoad32 M0 (F + 0x188) ∧
      memLoad32 M' (F + 0x18C) = memLoad32 M0 (F + 0x18C) ∧
      memLoad32 M0 (yp + 0x4) = v3 ∧
      memLoad32 M0 (xp + 0x0) = v4 ∧
      memLoad32 M0 (xp + 0x4) = v5 ∧
      memLoad32 M0 (yp + 0x0) = v6 ∧
      memLoad32 M0 (yp + 0x8) = v7 ∧
      memLoad32 M0 (yp + 0xC) = v8 ∧
      memLoad32 M0 (xp + 0x8) = v9 ∧
      memLoad32 M0 (xp + 0xC) = v10 ∧
      aluEval .mul v3 v4 = v11 ∧
      aluEval .mulhu v3 v4 = v12 ∧
      aluEval .mul v5 v6 = v13 ∧
      aluEval .mulhu v5 v6 = v14 ∧
      aluEval .mulhu v7 v4 = v15 ∧
      aluEval .mulhu v5 v3 = v16 ∧
      aluEval .mul v7 v4 = v17 ∧
      aluEval .mul v5 v3 = v18 ∧
      aluEval .mul v9 v6 = v19 ∧
      aluEval .add v12 v14 = v20 ∧
      aluEval .add v11 v13 = v21 ∧
      aluEval .add v15 v16 = v23 ∧
      aluEval .add v18 v17 = v24 ∧
      aluEval .mulhu v9 v6 = v25 ∧
      aluEval .sltu v21 v13 = v26 ∧
      aluEval .mul v7 v5 = v27 ∧
      aluEval .add v20 v26 = v28 ∧
      aluEval .mul v9 v3 = v30 ∧
      aluEval .mulhu v7 v5 = v31 ∧
      aluEval .mulhu v9 v3 = v32 ∧
      aluEval .mulhu v8 v4 = v33 ∧
      aluEval .mul v8 v4 = v34 ∧
      aluEval .sltu v24 v17 = v35 ∧
      aluEval .add v19 v24 = v36 ∧
      aluEval .sltu v36 v24 = v38 ∧
      aluEval .add v25 v23 = v39 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n0, d0, u0⟩ := s.aluE hc smm_at_34 (off' := 0x36) (by decide) (v := yp)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n1, d1, u1⟩ := u0.aluE hc smm_at_36 (off' := 0x38) (by decide) (v := xp)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n2, d2, u2⟩ := u1.swG hc smm_at_38 (off' := 0x3A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]; exact aligned_add hF (k := 248) (by decide)) (a := F + 0xF8) (v := outp)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12])
  obtain ⟨M2, hM2⟩ : ∃ M', memStore32 Mi (F + 0xF8) outp = M' := ⟨_, rfl⟩
  rw [hM2] at u2
  have hc2 : CodeIn M2 B scalar29MontMulCode := by rw [← hM2]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr2 : ∀ x, Sep F 0x190 x 1 → M2 x = M0 x := fun x hx => by
    rw [← hM2, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n3, v3, d3, hv3, u3⟩ := u2.lwG hc2 smm_at_3a (off' := 0x3E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]; exact aligned_add hy (k := 4) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv3
  rw [load_frame fr2 (show Sep F 0x190 (yp + 0x4) 4 from sYF.symm.subR (c := 4) (l := 4) (by decide))] at hv3
  obtain ⟨n4, v4, d4, hv4, u4⟩ := u3.lwG hc2 smm_at_3e (off' := 0x42) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]; exact aligned_add hx (k := 0) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv4
  rw [load_frame fr2 (show Sep F 0x190 (xp + 0x0) 4 from sXF.symm.subR (c := 0) (l := 4) (by decide))] at hv4
  obtain ⟨n5, v5, d5, hv5, u5⟩ := u4.lwG hc2 smm_at_42 (off' := 0x46) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]; exact aligned_add hx (k := 4) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv5
  rw [load_frame fr2 (show Sep F 0x190 (xp + 0x4) 4 from sXF.symm.subR (c := 4) (l := 4) (by decide))] at hv5
  obtain ⟨n6, v6, d6, hv6, u6⟩ := u5.lwG hc2 smm_at_46 (off' := 0x4A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]; exact aligned_add hy (k := 0) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv6
  rw [load_frame fr2 (show Sep F 0x190 (yp + 0x0) 4 from sYF.symm.subR (c := 0) (l := 4) (by decide))] at hv6
  obtain ⟨n7, v7, d7, hv7, u7⟩ := u6.lwG hc2 smm_at_4a (off' := 0x4E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]; exact aligned_add hy (k := 8) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv7
  rw [load_frame fr2 (show Sep F 0x190 (yp + 0x8) 4 from sYF.symm.subR (c := 8) (l := 4) (by decide))] at hv7
  obtain ⟨n8, v8, d8, hv8, u8⟩ := u7.lwG hc2 smm_at_4e (off' := 0x52) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]; exact aligned_add hy (k := 12) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv8
  rw [load_frame fr2 (show Sep F 0x190 (yp + 0xC) 4 from sYF.symm.subR (c := 12) (l := 4) (by decide))] at hv8
  obtain ⟨n9, v9, d9, hv9, u9⟩ := u8.lwG hc2 smm_at_52 (off' := 0x56) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]; exact aligned_add hx (k := 8) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv9
  rw [load_frame fr2 (show Sep F 0x190 (xp + 0x8) 4 from sXF.symm.subR (c := 8) (l := 4) (by decide))] at hv9
  obtain ⟨n10, v10, d10, hv10, u10⟩ := u9.lwG hc2 smm_at_56 (off' := 0x5A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]; exact aligned_add hx (k := 12) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv10
  rw [load_frame fr2 (show Sep F 0x190 (xp + 0xC) 4 from sXF.symm.subR (c := 12) (l := 4) (by decide))] at hv10
  obtain ⟨n11, v11, d11, hv11, u11⟩ := u10.aluG hc2 smm_at_5a (off' := 0x5E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv11
  obtain ⟨n12, v12, d12, hv12, u12⟩ := u11.aluG hc2 smm_at_5e (off' := 0x62) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv12
  obtain ⟨n13, v13, d13, hv13, u13⟩ := u12.aluG hc2 smm_at_62 (off' := 0x66) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv13
  obtain ⟨n14, v14, d14, hv14, u14⟩ := u13.aluG hc2 smm_at_66 (off' := 0x6A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv14
  obtain ⟨n15, v15, d15, hv15, u15⟩ := u14.aluG hc2 smm_at_6a (off' := 0x6E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv15
  obtain ⟨n16, v16, d16, hv16, u16⟩ := u15.aluG hc2 smm_at_6e (off' := 0x72) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv16
  obtain ⟨n17, v17, d17, hv17, u17⟩ := u16.aluG hc2 smm_at_72 (off' := 0x76) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv17
  obtain ⟨n18, v18, d18, hv18, u18⟩ := u17.aluG hc2 smm_at_76 (off' := 0x7A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv18
  obtain ⟨n19, v19, d19, hv19, u19⟩ := u18.aluG hc2 smm_at_7a (off' := 0x7E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv19
  obtain ⟨n20, v20, d20, hv20, u20⟩ := u19.aluG hc2 smm_at_7e (off' := 0x80) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv20
  obtain ⟨n21, v21, d21, hv21, u21⟩ := u20.aluG hc2 smm_at_80 (off' := 0x82) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv21
  obtain ⟨n22, d22, u22⟩ := u21.swG hc2 smm_at_82 (off' := 0x86) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]; exact aligned_add hF (k := 268) (by decide)) (a := F + 0x10C) (v := v21)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12])
  obtain ⟨M22, hM22⟩ : ∃ M', memStore32 M2 (F + 0x10C) v21 = M' := ⟨_, rfl⟩
  rw [hM22] at u22
  have hc22 : CodeIn M22 B scalar29MontMulCode := by rw [← hM22]; exact hc2.store32 (frm_sep' sFC (by decide))
  have fr22 : ∀ x, Sep F 0x190 x 1 → M22 x = M0 x := fun x hx => by
    rw [← hM22, memStore32_get_sep (frm_sep' hx (by decide)), fr2 x hx]
  obtain ⟨n23, v23, d23, hv23, u23⟩ := u22.aluG hc22 smm_at_86 (off' := 0x8A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv23
  obtain ⟨n24, v24, d24, hv24, u24⟩ := u23.aluG hc22 smm_at_8a (off' := 0x8C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv24
  obtain ⟨n25, v25, d25, hv25, u25⟩ := u24.aluG hc22 smm_at_8c (off' := 0x90) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv25
  obtain ⟨n26, v26, d26, hv26, u26⟩ := u25.aluG hc22 smm_at_90 (off' := 0x94) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv26
  obtain ⟨n27, v27, d27, hv27, u27⟩ := u26.aluG hc22 smm_at_94 (off' := 0x98) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv27
  obtain ⟨n28, v28, d28, hv28, u28⟩ := u27.aluG hc22 smm_at_98 (off' := 0x9A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv28
  obtain ⟨n29, d29, u29⟩ := u28.swG hc22 smm_at_9a (off' := 0x9E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]; exact aligned_add hF (k := 272) (by decide)) (a := F + 0x110) (v := v28)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12])
  obtain ⟨M29, hM29⟩ : ∃ M', memStore32 M22 (F + 0x110) v28 = M' := ⟨_, rfl⟩
  rw [hM29] at u29
  have hc29 : CodeIn M29 B scalar29MontMulCode := by rw [← hM29]; exact hc22.store32 (frm_sep' sFC (by decide))
  have fr29 : ∀ x, Sep F 0x190 x 1 → M29 x = M0 x := fun x hx => by
    rw [← hM29, memStore32_get_sep (frm_sep' hx (by decide)), fr22 x hx]
  obtain ⟨n30, v30, d30, hv30, u30⟩ := u29.aluG hc29 smm_at_9e (off' := 0xA2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv30
  obtain ⟨n31, v31, d31, hv31, u31⟩ := u30.aluG hc29 smm_at_a2 (off' := 0xA6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv31
  obtain ⟨n32, v32, d32, hv32, u32⟩ := u31.aluG hc29 smm_at_a6 (off' := 0xAA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv32
  obtain ⟨n33, v33, d33, hv33, u33⟩ := u32.aluG hc29 smm_at_aa (off' := 0xAE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv33
  obtain ⟨n34, v34, d34, hv34, u34⟩ := u33.aluG hc29 smm_at_ae (off' := 0xB2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv34
  obtain ⟨n35, v35, d35, hv35, u35⟩ := u34.aluG hc29 smm_at_b2 (off' := 0xB6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv35
  obtain ⟨n36, v36, d36, hv36, u36⟩ := u35.aluG hc29 smm_at_b6 (off' := 0xB8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv36
  obtain ⟨n37, d37, u37⟩ := u36.swG hc29 smm_at_b8 (off' := 0xBC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]; exact aligned_add hF (k := 284) (by decide)) (a := F + 0x11C) (v := v36)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12])
  obtain ⟨M37, hM37⟩ : ∃ M', memStore32 M29 (F + 0x11C) v36 = M' := ⟨_, rfl⟩
  rw [hM37] at u37
  have hc37 : CodeIn M37 B scalar29MontMulCode := by rw [← hM37]; exact hc29.store32 (frm_sep' sFC (by decide))
  have fr37 : ∀ x, Sep F 0x190 x 1 → M37 x = M0 x := fun x hx => by
    rw [← hM37, memStore32_get_sep (frm_sep' hx (by decide)), fr29 x hx]
  obtain ⟨n38, v38, d38, hv38, u38⟩ := u37.aluG hc37 smm_at_bc (off' := 0xC0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv38
  obtain ⟨n39, v39, d39, hv39, u39⟩ := u38.aluG hc37 smm_at_c0 (off' := 0xC2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12] at hv39
  have qo2 : reg n39 sp = F := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo3 : reg n39 (3 : Fin 32) = G3 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo4 : reg n39 (4 : Fin 32) = G4 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo5 : reg n39 (5 : Fin 32) = v9 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo6 : reg n39 (6 : Fin 32) = v33 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo8 : reg n39 (8 : Fin 32) = v35 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo9 : reg n39 (9 : Fin 32) = v32 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo10 : reg n39 a0 = v24 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo11 : reg n39 a1 = v30 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo12 : reg n39 a2 = yp := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo13 : reg n39 a3 = v31 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo14 : reg n39 a4 = v39 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo15 : reg n39 a5 = v34 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo16 : reg n39 a6 = v27 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo17 : reg n39 a7 = v38 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo19 : reg n39 (19 : Fin 32) = yp := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo20 : reg n39 (20 : Fin 32) = v7 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo21 : reg n39 (21 : Fin 32) = v10 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo22 : reg n39 (22 : Fin 32) = v5 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo25 : reg n39 (25 : Fin 32) = xp := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo26 : reg n39 (26 : Fin 32) = v6 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo28 : reg n39 (28 : Fin 32) = v8 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo29 : reg n39 (29 : Fin 32) = v4 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo30 : reg n39 (30 : Fin 32) = v3 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have qo31 : reg n39 (31 : Fin 32) = v23 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11, q12]
  have soF8 : memLoad32 M37 (F + 0xF8) = outp := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xF8) 4 from sep_offsets F (c := 284) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0xF8) 4 from sep_offsets F (c := 272) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0xF8) 4 from sep_offsets F (c := 268) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_same]
  have so10C : memLoad32 M37 (F + 0x10C) = v21 := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x10C) 4 from sep_offsets F (c := 284) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x10C) 4 from sep_offsets F (c := 272) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_same]
  have so110 : memLoad32 M37 (F + 0x110) = v28 := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x110) 4 from sep_offsets F (c := 284) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_same]
  have so11C : memLoad32 M37 (F + 0x11C) = v36 := by
    rw [← hM37, memLoad32_store32_same]
  have so15C : memLoad32 M37 (F + 0x15C) = memLoad32 M0 (F + 0x15C) := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x15C) 4 from sep_offsets F (c := 284) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x15C) 4 from sep_offsets F (c := 272) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x15C) 4 from sep_offsets F (c := 268) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x15C) 4 from sep_offsets F (c := 248) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), sl15C]
  have so160 : memLoad32 M37 (F + 0x160) = memLoad32 M0 (F + 0x160) := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x160) 4 from sep_offsets F (c := 284) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x160) 4 from sep_offsets F (c := 272) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x160) 4 from sep_offsets F (c := 268) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x160) 4 from sep_offsets F (c := 248) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), sl160]
  have so164 : memLoad32 M37 (F + 0x164) = memLoad32 M0 (F + 0x164) := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x164) 4 from sep_offsets F (c := 284) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x164) 4 from sep_offsets F (c := 272) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x164) 4 from sep_offsets F (c := 268) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x164) 4 from sep_offsets F (c := 248) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), sl164]
  have so168 : memLoad32 M37 (F + 0x168) = memLoad32 M0 (F + 0x168) := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x168) 4 from sep_offsets F (c := 284) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x168) 4 from sep_offsets F (c := 272) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x168) 4 from sep_offsets F (c := 268) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x168) 4 from sep_offsets F (c := 248) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), sl168]
  have so16C : memLoad32 M37 (F + 0x16C) = memLoad32 M0 (F + 0x16C) := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x16C) 4 from sep_offsets F (c := 284) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x16C) 4 from sep_offsets F (c := 272) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x16C) 4 from sep_offsets F (c := 268) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x16C) 4 from sep_offsets F (c := 248) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), sl16C]
  have so170 : memLoad32 M37 (F + 0x170) = memLoad32 M0 (F + 0x170) := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x170) 4 from sep_offsets F (c := 284) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x170) 4 from sep_offsets F (c := 272) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x170) 4 from sep_offsets F (c := 268) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x170) 4 from sep_offsets F (c := 248) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), sl170]
  have so174 : memLoad32 M37 (F + 0x174) = memLoad32 M0 (F + 0x174) := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x174) 4 from sep_offsets F (c := 284) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x174) 4 from sep_offsets F (c := 272) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x174) 4 from sep_offsets F (c := 268) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x174) 4 from sep_offsets F (c := 248) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), sl174]
  have so178 : memLoad32 M37 (F + 0x178) = memLoad32 M0 (F + 0x178) := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x178) 4 from sep_offsets F (c := 284) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x178) 4 from sep_offsets F (c := 272) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x178) 4 from sep_offsets F (c := 268) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x178) 4 from sep_offsets F (c := 248) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), sl178]
  have so17C : memLoad32 M37 (F + 0x17C) = memLoad32 M0 (F + 0x17C) := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x17C) 4 from sep_offsets F (c := 284) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x17C) 4 from sep_offsets F (c := 272) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x17C) 4 from sep_offsets F (c := 268) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x17C) 4 from sep_offsets F (c := 248) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), sl17C]
  have so180 : memLoad32 M37 (F + 0x180) = memLoad32 M0 (F + 0x180) := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x180) 4 from sep_offsets F (c := 284) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x180) 4 from sep_offsets F (c := 272) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x180) 4 from sep_offsets F (c := 268) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x180) 4 from sep_offsets F (c := 248) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), sl180]
  have so184 : memLoad32 M37 (F + 0x184) = memLoad32 M0 (F + 0x184) := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x184) 4 from sep_offsets F (c := 284) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x184) 4 from sep_offsets F (c := 272) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x184) 4 from sep_offsets F (c := 268) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x184) 4 from sep_offsets F (c := 248) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), sl184]
  have so188 : memLoad32 M37 (F + 0x188) = memLoad32 M0 (F + 0x188) := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x188) 4 from sep_offsets F (c := 284) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x188) 4 from sep_offsets F (c := 272) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x188) 4 from sep_offsets F (c := 268) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x188) 4 from sep_offsets F (c := 248) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), sl188]
  have so18C : memLoad32 M37 (F + 0x18C) = memLoad32 M0 (F + 0x18C) := by
    rw [← hM37, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x18C) 4 from sep_offsets F (c := 284) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM29, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x18C) 4 from sep_offsets F (c := 272) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM22, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x18C) 4 from sep_offsets F (c := 268) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0xF8) 4 (F + 0x18C) 4 from sep_offsets F (c := 248) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), sl18C]
  exact ⟨n39, M37, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v23, v24, v25, v26, v27, v28, v30, v31, v32, v33, v34, v35, v36, v38, v39, (.cons d0 (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18 (.cons d19 (.cons d20 (.cons d21 (.cons d22 (.cons d23 (.cons d24 (.cons d25 (.cons d26 (.cons d27 (.cons d28 (.cons d29 (.cons d30 (.cons d31 (.cons d32 (.cons d33 (.cons d34 (.cons d35 (.cons d36 (.cons d37 (.cons d38 (.single d39)))))))))))))))))))))))))))))))))))))))), u39.self, hc37, fr37, qo2, qo3, qo4, qo5, qo6, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo19, qo20, qo21, qo22, qo25, qo26, qo28, qo29, qo30, qo31, soF8, so10C, so110, so11C, so15C, so160, so164, so168, so16C, so170, so174, so178, so17C, so180, so184, so188, so18C, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15, hv16, hv17, hv18, hv19, hv20, hv21, hv23, hv24, hv25, hv26, hv27, hv28, hv30, hv31, hv32, hv33, hv34, hv35, hv36, hv38, hv39⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem smm_g1 {M0 Mi : Word → BitVec 8} {B F outp xp yp G3 G4 : Word} {n : Machine} {v3 v4 v5 v6 v7 v8 v9 v10 v21 v23 v24 v27 v28 v30 v31 v32 v33 v34 v35 v36 v38 v39 : Word}
    (s : St Mi B n 0xC2 (reg n)) (hc : CodeIn Mi B scalar29MontMulCode)
    (fr : ∀ x, Sep F 0x190 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v9)
    (q6 : reg n (6 : Fin 32) = v33)
    (q8 : reg n (8 : Fin 32) = v35)
    (q9 : reg n (9 : Fin 32) = v32)
    (q10 : reg n a0 = v24)
    (q11 : reg n a1 = v30)
    (q12 : reg n a2 = yp)
    (q13 : reg n a3 = v31)
    (q14 : reg n a4 = v39)
    (q15 : reg n a5 = v34)
    (q16 : reg n a6 = v27)
    (q17 : reg n a7 = v38)
    (q19 : reg n (19 : Fin 32) = yp)
    (q20 : reg n (20 : Fin 32) = v7)
    (q21 : reg n (21 : Fin 32) = v10)
    (q22 : reg n (22 : Fin 32) = v5)
    (q25 : reg n (25 : Fin 32) = xp)
    (q26 : reg n (26 : Fin 32) = v6)
    (q28 : reg n (28 : Fin 32) = v8)
    (q29 : reg n (29 : Fin 32) = v4)
    (q30 : reg n (30 : Fin 32) = v3)
    (q31 : reg n (31 : Fin 32) = v23)
    (slF8 : memLoad32 Mi (F + 0xF8) = outp)
    (sl10C : memLoad32 Mi (F + 0x10C) = v21)
    (sl110 : memLoad32 Mi (F + 0x110) = v28)
    (sl11C : memLoad32 Mi (F + 0x11C) = v36)
    (sl15C : memLoad32 Mi (F + 0x15C) = memLoad32 M0 (F + 0x15C))
    (sl160 : memLoad32 Mi (F + 0x160) = memLoad32 M0 (F + 0x160))
    (sl164 : memLoad32 Mi (F + 0x164) = memLoad32 M0 (F + 0x164))
    (sl168 : memLoad32 Mi (F + 0x168) = memLoad32 M0 (F + 0x168))
    (sl16C : memLoad32 Mi (F + 0x16C) = memLoad32 M0 (F + 0x16C))
    (sl170 : memLoad32 Mi (F + 0x170) = memLoad32 M0 (F + 0x170))
    (sl174 : memLoad32 Mi (F + 0x174) = memLoad32 M0 (F + 0x174))
    (sl178 : memLoad32 Mi (F + 0x178) = memLoad32 M0 (F + 0x178))
    (sl17C : memLoad32 Mi (F + 0x17C) = memLoad32 M0 (F + 0x17C))
    (sl180 : memLoad32 Mi (F + 0x180) = memLoad32 M0 (F + 0x180))
    (sl184 : memLoad32 Mi (F + 0x184) = memLoad32 M0 (F + 0x184))
    (sl188 : memLoad32 Mi (F + 0x188) = memLoad32 M0 (F + 0x188))
    (sl18C : memLoad32 Mi (F + 0x18C) = memLoad32 M0 (F + 0x18C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v54 v55 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v70 v71 v73 v74 v75 v76 v77 v78 v79 : Word),
      Steps n n' ∧
      St M' B n' 0x13C (reg n') ∧
      CodeIn M' B scalar29MontMulCode ∧
      (∀ x, Sep F 0x190 x 1 → M' x = M0 x) ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v9 ∧
      reg n' (6 : Fin 32) = v66 ∧
      reg n' (7 : Fin 32) = v60 ∧
      reg n' (8 : Fin 32) = v71 ∧
      reg n' (9 : Fin 32) = v63 ∧
      reg n' a0 = v67 ∧
      reg n' a1 = v73 ∧
      reg n' a2 = yp ∧
      reg n' a3 = xp ∧
      reg n' a4 = v78 ∧
      reg n' a5 = v77 ∧
      reg n' a6 = v74 ∧
      reg n' a7 = v65 ∧
      reg n' (18 : Fin 32) = v79 ∧
      reg n' (19 : Fin 32) = yp ∧
      reg n' (20 : Fin 32) = v7 ∧
      reg n' (21 : Fin 32) = v10 ∧
      reg n' (22 : Fin 32) = v5 ∧
      reg n' (23 : Fin 32) = v76 ∧
      reg n' (24 : Fin 32) = v70 ∧
      reg n' (25 : Fin 32) = xp ∧
      reg n' (26 : Fin 32) = v6 ∧
      reg n' (28 : Fin 32) = v8 ∧
      reg n' (29 : Fin 32) = v4 ∧
      reg n' (30 : Fin 32) = v3 ∧
      reg n' (31 : Fin 32) = v62 ∧
      memLoad32 M' (F + 0x88) = v67 ∧
      memLoad32 M' (F + 0xF8) = outp ∧
      memLoad32 M' (F + 0x100) = v4 ∧
      memLoad32 M' (F + 0x108) = v55 ∧
      memLoad32 M' (F + 0x10C) = v21 ∧
      memLoad32 M' (F + 0x110) = v28 ∧
      memLoad32 M' (F + 0x118) = v52 ∧
      memLoad32 M' (F + 0x11C) = v36 ∧
      memLoad32 M' (F + 0x15C) = memLoad32 M0 (F + 0x15C) ∧
      memLoad32 M' (F + 0x160) = memLoad32 M0 (F + 0x160) ∧
      memLoad32 M' (F + 0x164) = memLoad32 M0 (F + 0x164) ∧
      memLoad32 M' (F + 0x168) = memLoad32 M0 (F + 0x168) ∧
      memLoad32 M' (F + 0x16C) = memLoad32 M0 (F + 0x16C) ∧
      memLoad32 M' (F + 0x170) = memLoad32 M0 (F + 0x170) ∧
      memLoad32 M' (F + 0x174) = memLoad32 M0 (F + 0x174) ∧
      memLoad32 M' (F + 0x178) = memLoad32 M0 (F + 0x178) ∧
      memLoad32 M' (F + 0x17C) = memLoad32 M0 (F + 0x17C) ∧
      memLoad32 M' (F + 0x180) = memLoad32 M0 (F + 0x180) ∧
      memLoad32 M' (F + 0x184) = memLoad32 M0 (F + 0x184) ∧
      memLoad32 M' (F + 0x188) = memLoad32 M0 (F + 0x188) ∧
      memLoad32 M' (F + 0x18C) = memLoad32 M0 (F + 0x18C) ∧
      aluEval .add v39 v35 = v40 ∧
      aluEval .mul v10 v6 = v41 ∧
      aluEval .mulhu v10 v6 = v42 ∧
      aluEval .add v27 v30 = v43 ∧
      aluEval .add v31 v32 = v44 ∧
      aluEval .sltu v43 v30 = v45 ∧
      aluEval .add v34 v43 = v46 ∧
      aluEval .add v44 v33 = v47 ∧
      aluEval .sltu v46 v43 = v48 ∧
      aluEval .add v45 v47 = v49 ∧
      aluEval .mulhu v8 v5 = v50 ∧
      aluEval .mulhu v9 v7 = v51 ∧
      aluEval .add v40 v38 = v52 ∧
      aluEval .add v49 v48 = v54 ∧
      aluEval .add v41 v46 = v55 ∧
      aluEval .mulhu v10 v3 = v57 ∧
      aluEval .mul v8 v5 = v58 ∧
      aluEval .mul v9 v7 = v59 ∧
      memLoad32 M0 (yp + 0x10) = v60 ∧
      aluEval .mul v10 v3 = v61 ∧
      aluEval .add v42 v54 = v62 ∧
      aluEval .sltu v55 v46 = v63 ∧
      aluEval .add v51 v50 = v64 ∧
      memLoad32 M0 (yp + 0x14) = v65 ∧
      memLoad32 M0 (yp + 0x18) = v66 ∧
      memLoad32 M0 (yp + 0x1C) = v67 ∧
      aluEval .mulhu v60 v4 = v70 ∧
      aluEval .add v64 v57 = v71 ∧
      memLoad32 M0 (xp + 0x10) = v73 ∧
      aluEval .add v59 v58 = v74 ∧
      aluEval .sltu v74 v58 = v75 ∧
      aluEval .add v61 v74 = v76 ∧
      aluEval .sltu v76 v74 = v77 ∧
      aluEval .add v75 v71 = v78 ∧
      aluEval .mul v60 v4 = v79 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n40, v40, d40, hv40, u40⟩ := s.aluG hc smm_at_c2 (off' := 0xC4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv40
  obtain ⟨n41, v41, d41, hv41, u41⟩ := u40.aluG hc smm_at_c4 (off' := 0xC8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv41
  obtain ⟨n42, v42, d42, hv42, u42⟩ := u41.aluG hc smm_at_c8 (off' := 0xCC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv42
  obtain ⟨n43, v43, d43, hv43, u43⟩ := u42.aluG hc smm_at_cc (off' := 0xCE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv43
  obtain ⟨n44, v44, d44, hv44, u44⟩ := u43.aluG hc smm_at_ce (off' := 0xD0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv44
  obtain ⟨n45, v45, d45, hv45, u45⟩ := u44.aluG hc smm_at_d0 (off' := 0xD4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv45
  obtain ⟨n46, v46, d46, hv46, u46⟩ := u45.aluG hc smm_at_d4 (off' := 0xD6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv46
  obtain ⟨n47, v47, d47, hv47, u47⟩ := u46.aluG hc smm_at_d6 (off' := 0xD8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv47
  obtain ⟨n48, v48, d48, hv48, u48⟩ := u47.aluG hc smm_at_d8 (off' := 0xDC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv48
  obtain ⟨n49, v49, d49, hv49, u49⟩ := u48.aluG hc smm_at_dc (off' := 0xDE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv49
  obtain ⟨n50, v50, d50, hv50, u50⟩ := u49.aluG hc smm_at_de (off' := 0xE2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv50
  obtain ⟨n51, v51, d51, hv51, u51⟩ := u50.aluG hc smm_at_e2 (off' := 0xE6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv51
  obtain ⟨n52, v52, d52, hv52, u52⟩ := u51.aluG hc smm_at_e6 (off' := 0xE8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv52
  obtain ⟨n53, d53, u53⟩ := u52.swG hc smm_at_e8 (off' := 0xEC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]; exact aligned_add hF (k := 280) (by decide)) (a := F + 0x118) (v := v52)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31])
  obtain ⟨M53, hM53⟩ : ∃ M', memStore32 Mi (F + 0x118) v52 = M' := ⟨_, rfl⟩
  rw [hM53] at u53
  have hc53 : CodeIn M53 B scalar29MontMulCode := by rw [← hM53]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr53 : ∀ x, Sep F 0x190 x 1 → M53 x = M0 x := fun x hx => by
    rw [← hM53, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n54, v54, d54, hv54, u54⟩ := u53.aluG hc53 smm_at_ec (off' := 0xEE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv54
  obtain ⟨n55, v55, d55, hv55, u55⟩ := u54.aluG hc53 smm_at_ee (off' := 0xF0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv55
  obtain ⟨n56, d56, u56⟩ := u55.swG hc53 smm_at_f0 (off' := 0xF4) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]; exact aligned_add hF (k := 264) (by decide)) (a := F + 0x108) (v := v55)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31])
  obtain ⟨M56, hM56⟩ : ∃ M', memStore32 M53 (F + 0x108) v55 = M' := ⟨_, rfl⟩
  rw [hM56] at u56
  have hc56 : CodeIn M56 B scalar29MontMulCode := by rw [← hM56]; exact hc53.store32 (frm_sep' sFC (by decide))
  have fr56 : ∀ x, Sep F 0x190 x 1 → M56 x = M0 x := fun x hx => by
    rw [← hM56, memStore32_get_sep (frm_sep' hx (by decide)), fr53 x hx]
  obtain ⟨n57, v57, d57, hv57, u57⟩ := u56.aluG hc56 smm_at_f4 (off' := 0xF8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv57
  obtain ⟨n58, v58, d58, hv58, u58⟩ := u57.aluG hc56 smm_at_f8 (off' := 0xFC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv58
  obtain ⟨n59, v59, d59, hv59, u59⟩ := u58.aluG hc56 smm_at_fc (off' := 0x100) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv59
  obtain ⟨n60, v60, d60, hv60, u60⟩ := u59.lwG hc56 smm_at_100 (off' := 0x104) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]; exact aligned_add hy (k := 16) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv60
  rw [load_frame fr56 (show Sep F 0x190 (yp + 0x10) 4 from sYF.symm.subR (c := 16) (l := 4) (by decide))] at hv60
  obtain ⟨n61, v61, d61, hv61, u61⟩ := u60.aluG hc56 smm_at_104 (off' := 0x108) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv61
  obtain ⟨n62, v62, d62, hv62, u62⟩ := u61.aluG hc56 smm_at_108 (off' := 0x10A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv62
  obtain ⟨n63, v63, d63, hv63, u63⟩ := u62.aluG hc56 smm_at_10a (off' := 0x10E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv63
  obtain ⟨n64, v64, d64, hv64, u64⟩ := u63.aluG hc56 smm_at_10e (off' := 0x110) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv64
  obtain ⟨n65, v65, d65, hv65, u65⟩ := u64.lwG hc56 smm_at_110 (off' := 0x114) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]; exact aligned_add hy (k := 20) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv65
  rw [load_frame fr56 (show Sep F 0x190 (yp + 0x14) 4 from sYF.symm.subR (c := 20) (l := 4) (by decide))] at hv65
  obtain ⟨n66, v66, d66, hv66, u66⟩ := u65.lwG hc56 smm_at_114 (off' := 0x118) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]; exact aligned_add hy (k := 24) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv66
  rw [load_frame fr56 (show Sep F 0x190 (yp + 0x18) 4 from sYF.symm.subR (c := 24) (l := 4) (by decide))] at hv66
  obtain ⟨n67, v67, d67, hv67, u67⟩ := u66.lwG hc56 smm_at_118 (off' := 0x11A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]; exact aligned_add hy (k := 28) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv67
  rw [load_frame fr56 (show Sep F 0x190 (yp + 0x1C) 4 from sYF.symm.subR (c := 28) (l := 4) (by decide))] at hv67
  obtain ⟨n68, d68, u68⟩ := u67.swG hc56 smm_at_11a (off' := 0x11C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]; exact aligned_add hF (k := 136) (by decide)) (a := F + 0x88) (v := v67)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31])
  obtain ⟨M68, hM68⟩ : ∃ M', memStore32 M56 (F + 0x88) v67 = M' := ⟨_, rfl⟩
  rw [hM68] at u68
  have hc68 : CodeIn M68 B scalar29MontMulCode := by rw [← hM68]; exact hc56.store32 (frm_sep' sFC (by decide))
  have fr68 : ∀ x, Sep F 0x190 x 1 → M68 x = M0 x := fun x hx => by
    rw [← hM68, memStore32_get_sep (frm_sep' hx (by decide)), fr56 x hx]
  obtain ⟨n69, d69, u69⟩ := u68.swG hc68 smm_at_11c (off' := 0x120) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]; exact aligned_add hF (k := 256) (by decide)) (a := F + 0x100) (v := v4)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31])
  obtain ⟨M69, hM69⟩ : ∃ M', memStore32 M68 (F + 0x100) v4 = M' := ⟨_, rfl⟩
  rw [hM69] at u69
  have hc69 : CodeIn M69 B scalar29MontMulCode := by rw [← hM69]; exact hc68.store32 (frm_sep' sFC (by decide))
  have fr69 : ∀ x, Sep F 0x190 x 1 → M69 x = M0 x := fun x hx => by
    rw [← hM69, memStore32_get_sep (frm_sep' hx (by decide)), fr68 x hx]
  obtain ⟨n70, v70, d70, hv70, u70⟩ := u69.aluG hc69 smm_at_120 (off' := 0x124) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv70
  obtain ⟨n71, v71, d71, hv71, u71⟩ := u70.aluG hc69 smm_at_124 (off' := 0x126) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv71
  obtain ⟨n72, d72, u72⟩ := u71.aluE hc69 smm_at_126 (off' := 0x128) (by decide) (v := xp)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n73, v73, d73, hv73, u73⟩ := u72.lwG hc69 smm_at_128 (off' := 0x12A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]; exact aligned_add hx (k := 16) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv73
  rw [load_frame fr69 (show Sep F 0x190 (xp + 0x10) 4 from sXF.symm.subR (c := 16) (l := 4) (by decide))] at hv73
  obtain ⟨n74, v74, d74, hv74, u74⟩ := u73.aluG hc69 smm_at_12a (off' := 0x12C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv74
  obtain ⟨n75, v75, d75, hv75, u75⟩ := u74.aluG hc69 smm_at_12c (off' := 0x130) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv75
  obtain ⟨n76, v76, d76, hv76, u76⟩ := u75.aluG hc69 smm_at_130 (off' := 0x132) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv76
  obtain ⟨n77, v77, d77, hv77, u77⟩ := u76.aluG hc69 smm_at_132 (off' := 0x136) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv77
  obtain ⟨n78, v78, d78, hv78, u78⟩ := u77.aluG hc69 smm_at_136 (off' := 0x138) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv78
  obtain ⟨n79, v79, d79, hv79, u79⟩ := u78.aluG hc69 smm_at_138 (off' := 0x13C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31] at hv79
  have qo2 : reg n79 sp = F := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo3 : reg n79 (3 : Fin 32) = G3 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo4 : reg n79 (4 : Fin 32) = G4 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo5 : reg n79 (5 : Fin 32) = v9 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo6 : reg n79 (6 : Fin 32) = v66 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo7 : reg n79 (7 : Fin 32) = v60 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo8 : reg n79 (8 : Fin 32) = v71 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo9 : reg n79 (9 : Fin 32) = v63 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo10 : reg n79 a0 = v67 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo11 : reg n79 a1 = v73 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo12 : reg n79 a2 = yp := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo13 : reg n79 a3 = xp := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo14 : reg n79 a4 = v78 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo15 : reg n79 a5 = v77 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo16 : reg n79 a6 = v74 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo17 : reg n79 a7 = v65 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo18 : reg n79 (18 : Fin 32) = v79 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo19 : reg n79 (19 : Fin 32) = yp := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo20 : reg n79 (20 : Fin 32) = v7 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo21 : reg n79 (21 : Fin 32) = v10 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo22 : reg n79 (22 : Fin 32) = v5 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo23 : reg n79 (23 : Fin 32) = v76 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo24 : reg n79 (24 : Fin 32) = v70 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo25 : reg n79 (25 : Fin 32) = xp := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo26 : reg n79 (26 : Fin 32) = v6 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo28 : reg n79 (28 : Fin 32) = v8 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo29 : reg n79 (29 : Fin 32) = v4 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo30 : reg n79 (30 : Fin 32) = v3 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have qo31 : reg n79 (31 : Fin 32) = v62 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q25, q26, q28, q29, q30, q31]
  have so88 : memLoad32 M69 (F + 0x88) = v67 := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x88) 4 from sep_offsets F (c := 256) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_same]
  have soF8 : memLoad32 M69 (F + 0xF8) = outp := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xF8) 4 from sep_offsets F (c := 256) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xF8) 4 from sep_offsets F (c := 136) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xF8) 4 from sep_offsets F (c := 264) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xF8) 4 from sep_offsets F (c := 280) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), slF8]
  have so100 : memLoad32 M69 (F + 0x100) = v4 := by
    rw [← hM69, memLoad32_store32_same]
  have so108 : memLoad32 M69 (F + 0x108) = v55 := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x108) 4 from sep_offsets F (c := 256) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x108) 4 from sep_offsets F (c := 136) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_same]
  have so10C : memLoad32 M69 (F + 0x10C) = v21 := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x10C) 4 from sep_offsets F (c := 256) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x10C) 4 from sep_offsets F (c := 136) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x10C) 4 from sep_offsets F (c := 264) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x10C) 4 from sep_offsets F (c := 280) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so110 : memLoad32 M69 (F + 0x110) = v28 := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x110) 4 from sep_offsets F (c := 256) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x110) 4 from sep_offsets F (c := 136) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x110) 4 from sep_offsets F (c := 264) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x110) 4 from sep_offsets F (c := 280) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so118 : memLoad32 M69 (F + 0x118) = v52 := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x118) 4 from sep_offsets F (c := 256) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x118) 4 from sep_offsets F (c := 136) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x118) 4 from sep_offsets F (c := 264) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_same]
  have so11C : memLoad32 M69 (F + 0x11C) = v36 := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x11C) 4 from sep_offsets F (c := 256) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x11C) 4 from sep_offsets F (c := 136) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x11C) 4 from sep_offsets F (c := 264) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x11C) 4 from sep_offsets F (c := 280) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), sl11C]
  have so15C : memLoad32 M69 (F + 0x15C) = memLoad32 M0 (F + 0x15C) := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x15C) 4 from sep_offsets F (c := 256) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x15C) 4 from sep_offsets F (c := 136) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x15C) 4 from sep_offsets F (c := 264) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x15C) 4 from sep_offsets F (c := 280) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), sl15C]
  have so160 : memLoad32 M69 (F + 0x160) = memLoad32 M0 (F + 0x160) := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x160) 4 from sep_offsets F (c := 256) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x160) 4 from sep_offsets F (c := 136) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x160) 4 from sep_offsets F (c := 264) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x160) 4 from sep_offsets F (c := 280) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), sl160]
  have so164 : memLoad32 M69 (F + 0x164) = memLoad32 M0 (F + 0x164) := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x164) 4 from sep_offsets F (c := 256) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x164) 4 from sep_offsets F (c := 136) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x164) 4 from sep_offsets F (c := 264) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x164) 4 from sep_offsets F (c := 280) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), sl164]
  have so168 : memLoad32 M69 (F + 0x168) = memLoad32 M0 (F + 0x168) := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x168) 4 from sep_offsets F (c := 256) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x168) 4 from sep_offsets F (c := 136) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x168) 4 from sep_offsets F (c := 264) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x168) 4 from sep_offsets F (c := 280) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), sl168]
  have so16C : memLoad32 M69 (F + 0x16C) = memLoad32 M0 (F + 0x16C) := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x16C) 4 from sep_offsets F (c := 256) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x16C) 4 from sep_offsets F (c := 136) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x16C) 4 from sep_offsets F (c := 264) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x16C) 4 from sep_offsets F (c := 280) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), sl16C]
  have so170 : memLoad32 M69 (F + 0x170) = memLoad32 M0 (F + 0x170) := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x170) 4 from sep_offsets F (c := 256) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x170) 4 from sep_offsets F (c := 136) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x170) 4 from sep_offsets F (c := 264) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x170) 4 from sep_offsets F (c := 280) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), sl170]
  have so174 : memLoad32 M69 (F + 0x174) = memLoad32 M0 (F + 0x174) := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x174) 4 from sep_offsets F (c := 256) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x174) 4 from sep_offsets F (c := 136) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x174) 4 from sep_offsets F (c := 264) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x174) 4 from sep_offsets F (c := 280) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), sl174]
  have so178 : memLoad32 M69 (F + 0x178) = memLoad32 M0 (F + 0x178) := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x178) 4 from sep_offsets F (c := 256) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x178) 4 from sep_offsets F (c := 136) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x178) 4 from sep_offsets F (c := 264) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x178) 4 from sep_offsets F (c := 280) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), sl178]
  have so17C : memLoad32 M69 (F + 0x17C) = memLoad32 M0 (F + 0x17C) := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x17C) 4 from sep_offsets F (c := 256) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x17C) 4 from sep_offsets F (c := 136) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x17C) 4 from sep_offsets F (c := 264) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x17C) 4 from sep_offsets F (c := 280) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), sl17C]
  have so180 : memLoad32 M69 (F + 0x180) = memLoad32 M0 (F + 0x180) := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x180) 4 from sep_offsets F (c := 256) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x180) 4 from sep_offsets F (c := 136) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x180) 4 from sep_offsets F (c := 264) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x180) 4 from sep_offsets F (c := 280) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), sl180]
  have so184 : memLoad32 M69 (F + 0x184) = memLoad32 M0 (F + 0x184) := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x184) 4 from sep_offsets F (c := 256) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x184) 4 from sep_offsets F (c := 136) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x184) 4 from sep_offsets F (c := 264) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x184) 4 from sep_offsets F (c := 280) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), sl184]
  have so188 : memLoad32 M69 (F + 0x188) = memLoad32 M0 (F + 0x188) := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x188) 4 from sep_offsets F (c := 256) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x188) 4 from sep_offsets F (c := 136) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x188) 4 from sep_offsets F (c := 264) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x188) 4 from sep_offsets F (c := 280) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), sl188]
  have so18C : memLoad32 M69 (F + 0x18C) = memLoad32 M0 (F + 0x18C) := by
    rw [← hM69, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x18C) 4 from sep_offsets F (c := 256) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM68, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x18C) 4 from sep_offsets F (c := 136) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM56, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x18C) 4 from sep_offsets F (c := 264) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM53, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x18C) 4 from sep_offsets F (c := 280) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), sl18C]
  exact ⟨n79, M69, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v54, v55, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v70, v71, v73, v74, v75, v76, v77, v78, v79, (.cons d40 (.cons d41 (.cons d42 (.cons d43 (.cons d44 (.cons d45 (.cons d46 (.cons d47 (.cons d48 (.cons d49 (.cons d50 (.cons d51 (.cons d52 (.cons d53 (.cons d54 (.cons d55 (.cons d56 (.cons d57 (.cons d58 (.cons d59 (.cons d60 (.cons d61 (.cons d62 (.cons d63 (.cons d64 (.cons d65 (.cons d66 (.cons d67 (.cons d68 (.cons d69 (.cons d70 (.cons d71 (.cons d72 (.cons d73 (.cons d74 (.cons d75 (.cons d76 (.cons d77 (.cons d78 (.single d79)))))))))))))))))))))))))))))))))))))))), u79.self, hc69, fr69, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo28, qo29, qo30, qo31, so88, soF8, so100, so108, so10C, so110, so118, so11C, so15C, so160, so164, so168, so16C, so170, so174, so178, so17C, so180, so184, so188, so18C, hv40, hv41, hv42, hv43, hv44, hv45, hv46, hv47, hv48, hv49, hv50, hv51, hv52, hv54, hv55, hv57, hv58, hv59, hv60, hv61, hv62, hv63, hv64, hv65, hv66, hv67, hv70, hv71, hv73, hv74, hv75, hv76, hv77, hv78, hv79⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem smm_g2 {M0 Mi : Word → BitVec 8} {B F outp xp yp G3 G4 : Word} {n : Machine} {v3 v4 v5 v6 v7 v8 v9 v10 v21 v28 v36 v52 v55 v60 v62 v63 v65 v66 v67 v70 v71 v73 v74 v76 v77 v78 v79 : Word}
    (s : St Mi B n 0x13C (reg n)) (hc : CodeIn Mi B scalar29MontMulCode)
    (fr : ∀ x, Sep F 0x190 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v9)
    (q6 : reg n (6 : Fin 32) = v66)
    (q7 : reg n (7 : Fin 32) = v60)
    (q8 : reg n (8 : Fin 32) = v71)
    (q9 : reg n (9 : Fin 32) = v63)
    (q10 : reg n a0 = v67)
    (q11 : reg n a1 = v73)
    (q12 : reg n a2 = yp)
    (q13 : reg n a3 = xp)
    (q14 : reg n a4 = v78)
    (q15 : reg n a5 = v77)
    (q16 : reg n a6 = v74)
    (q17 : reg n a7 = v65)
    (q18 : reg n (18 : Fin 32) = v79)
    (q19 : reg n (19 : Fin 32) = yp)
    (q20 : reg n (20 : Fin 32) = v7)
    (q21 : reg n (21 : Fin 32) = v10)
    (q22 : reg n (22 : Fin 32) = v5)
    (q23 : reg n (23 : Fin 32) = v76)
    (q24 : reg n (24 : Fin 32) = v70)
    (q25 : reg n (25 : Fin 32) = xp)
    (q26 : reg n (26 : Fin 32) = v6)
    (q28 : reg n (28 : Fin 32) = v8)
    (q29 : reg n (29 : Fin 32) = v4)
    (q30 : reg n (30 : Fin 32) = v3)
    (q31 : reg n (31 : Fin 32) = v62)
    (sl88 : memLoad32 Mi (F + 0x88) = v67)
    (slF8 : memLoad32 Mi (F + 0xF8) = outp)
    (sl100 : memLoad32 Mi (F + 0x100) = v4)
    (sl108 : memLoad32 Mi (F + 0x108) = v55)
    (sl10C : memLoad32 Mi (F + 0x10C) = v21)
    (sl110 : memLoad32 Mi (F + 0x110) = v28)
    (sl118 : memLoad32 Mi (F + 0x118) = v52)
    (sl11C : memLoad32 Mi (F + 0x11C) = v36)
    (sl15C : memLoad32 Mi (F + 0x15C) = memLoad32 M0 (F + 0x15C))
    (sl160 : memLoad32 Mi (F + 0x160) = memLoad32 M0 (F + 0x160))
    (sl164 : memLoad32 Mi (F + 0x164) = memLoad32 M0 (F + 0x164))
    (sl168 : memLoad32 Mi (F + 0x168) = memLoad32 M0 (F + 0x168))
    (sl16C : memLoad32 Mi (F + 0x16C) = memLoad32 M0 (F + 0x16C))
    (sl170 : memLoad32 Mi (F + 0x170) = memLoad32 M0 (F + 0x170))
    (sl174 : memLoad32 Mi (F + 0x174) = memLoad32 M0 (F + 0x174))
    (sl178 : memLoad32 Mi (F + 0x178) = memLoad32 M0 (F + 0x178))
    (sl17C : memLoad32 Mi (F + 0x17C) = memLoad32 M0 (F + 0x17C))
    (sl180 : memLoad32 Mi (F + 0x180) = memLoad32 M0 (F + 0x180))
    (sl184 : memLoad32 Mi (F + 0x184) = memLoad32 M0 (F + 0x184))
    (sl188 : memLoad32 Mi (F + 0x188) = memLoad32 M0 (F + 0x188))
    (sl18C : memLoad32 Mi (F + 0x18C) = memLoad32 M0 (F + 0x18C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v80 v81 v82 v83 v87 v88 v89 v90 v92 v93 v94 v95 v98 v99 v100 v101 v103 v104 v105 v106 v107 v108 v109 v112 v113 v114 v115 v116 v117 v118 v119 : Word),
      Steps n n' ∧
      St M' B n' 0x1B2 (reg n') ∧
      CodeIn M' B scalar29MontMulCode ∧
      (∀ x, Sep F 0x190 x 1 → M' x = M0 x) ∧
      reg n' ra = v117 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v9 ∧
      reg n' (6 : Fin 32) = v66 ∧
      reg n' (7 : Fin 32) = v60 ∧
      reg n' (8 : Fin 32) = v118 ∧
      reg n' (9 : Fin 32) = v73 ∧
      reg n' a0 = v109 ∧
      reg n' a1 = v106 ∧
      reg n' a2 = v73 ∧
      reg n' a3 = v6 ∧
      reg n' a4 = v78 ∧
      reg n' a5 = v77 ∧
      reg n' a6 = v81 ∧
      reg n' a7 = v65 ∧
      reg n' (18 : Fin 32) = v95 ∧
      reg n' (19 : Fin 32) = yp ∧
      reg n' (20 : Fin 32) = v7 ∧
      reg n' (21 : Fin 32) = v10 ∧
      reg n' (22 : Fin 32) = v114 ∧
      reg n' (23 : Fin 32) = v115 ∧
      reg n' (24 : Fin 32) = v104 ∧
      reg n' (25 : Fin 32) = xp ∧
      reg n' (26 : Fin 32) = v105 ∧
      reg n' (27 : Fin 32) = v107 ∧
      reg n' (28 : Fin 32) = v8 ∧
      reg n' (29 : Fin 32) = v82 ∧
      reg n' (30 : Fin 32) = v6 ∧
      reg n' (31 : Fin 32) = v119 ∧
      memLoad32 M' (F + 0x84) = v83 ∧
      memLoad32 M' (F + 0x88) = v67 ∧
      memLoad32 M' (F + 0xE0) = v5 ∧
      memLoad32 M' (F + 0xEC) = v3 ∧
      memLoad32 M' (F + 0xF8) = outp ∧
      memLoad32 M' (F + 0x100) = v4 ∧
      memLoad32 M' (F + 0x108) = v55 ∧
      memLoad32 M' (F + 0x10C) = v21 ∧
      memLoad32 M' (F + 0x110) = v28 ∧
      memLoad32 M' (F + 0x114) = v90 ∧
      memLoad32 M' (F + 0x118) = v52 ∧
      memLoad32 M' (F + 0x11C) = v36 ∧
      memLoad32 M' (F + 0x15C) = memLoad32 M0 (F + 0x15C) ∧
      memLoad32 M' (F + 0x160) = memLoad32 M0 (F + 0x160) ∧
      memLoad32 M' (F + 0x164) = memLoad32 M0 (F + 0x164) ∧
      memLoad32 M' (F + 0x168) = memLoad32 M0 (F + 0x168) ∧
      memLoad32 M' (F + 0x16C) = memLoad32 M0 (F + 0x16C) ∧
      memLoad32 M' (F + 0x170) = memLoad32 M0 (F + 0x170) ∧
      memLoad32 M' (F + 0x174) = memLoad32 M0 (F + 0x174) ∧
      memLoad32 M' (F + 0x178) = memLoad32 M0 (F + 0x178) ∧
      memLoad32 M' (F + 0x17C) = memLoad32 M0 (F + 0x17C) ∧
      memLoad32 M' (F + 0x180) = memLoad32 M0 (F + 0x180) ∧
      memLoad32 M' (F + 0x184) = memLoad32 M0 (F + 0x184) ∧
      memLoad32 M' (F + 0x188) = memLoad32 M0 (F + 0x188) ∧
      memLoad32 M' (F + 0x18C) = memLoad32 M0 (F + 0x18C) ∧
      aluEval .add v78 v77 = v80 ∧
      memLoad32 M0 (xp + 0x14) = v81 ∧
      memLoad32 M0 (xp + 0x18) = v82 ∧
      memLoad32 M0 (xp + 0x1C) = v83 ∧
      aluEval .mulhu v73 v6 = v87 ∧
      aluEval .mulhu v8 v9 = v88 ∧
      aluEval .mulhu v10 v7 = v89 ∧
      aluEval .add v62 v63 = v90 ∧
      aluEval .add v70 v80 = v92 ∧
      aluEval .mul v8 v9 = v93 ∧
      aluEval .mul v10 v7 = v94 ∧
      aluEval .add v79 v76 = v95 ∧
      aluEval .mulhu v60 v5 = v98 ∧
      aluEval .sltu v95 v76 = v99 ∧
      aluEval .mul v60 v5 = v100 ∧
      aluEval .add v99 v87 = v101 ∧
      aluEval .mul v73 v3 = v103 ∧
      aluEval .add v92 v101 = v104 ∧
      aluEval .add v88 v89 = v105 ∧
      aluEval .mulhu v73 v3 = v106 ∧
      aluEval .mulhu v65 v81 = v107 ∧
      aluEval .add v93 v94 = v108 ∧
      aluEval .mul v73 v6 = v109 ∧
      aluEval .add v98 v105 = v112 ∧
      aluEval .sltu v108 v94 = v113 ∧
      aluEval .add v112 v113 = v114 ∧
      aluEval .add v100 v108 = v115 ∧
      aluEval .sltu v115 v108 = v116 ∧
      aluEval .add v103 v115 = v117 ∧
      aluEval .add v116 v114 = v118 ∧
      aluEval .sltu v117 v115 = v119 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n80, v80, d80, hv80, u80⟩ := s.aluG hc smm_at_13c (off' := 0x140) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv80
  obtain ⟨n81, v81, d81, hv81, u81⟩ := u80.lwG hc smm_at_140 (off' := 0x144) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]; exact aligned_add hx (k := 20) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv81
  rw [load_frame fr (show Sep F 0x190 (xp + 0x14) 4 from sXF.symm.subR (c := 20) (l := 4) (by decide))] at hv81
  obtain ⟨n82, v82, d82, hv82, u82⟩ := u81.lwG hc smm_at_144 (off' := 0x148) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]; exact aligned_add hx (k := 24) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv82
  rw [load_frame fr (show Sep F 0x190 (xp + 0x18) 4 from sXF.symm.subR (c := 24) (l := 4) (by decide))] at hv82
  obtain ⟨n83, v83, d83, hv83, u83⟩ := u82.lwG hc smm_at_148 (off' := 0x14A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]; exact aligned_add hx (k := 28) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv83
  rw [load_frame fr (show Sep F 0x190 (xp + 0x1C) 4 from sXF.symm.subR (c := 28) (l := 4) (by decide))] at hv83
  obtain ⟨n84, d84, u84⟩ := u83.swG hc smm_at_14a (off' := 0x14C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]; exact aligned_add hF (k := 132) (by decide)) (a := F + 0x84) (v := v83)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31])
  obtain ⟨M84, hM84⟩ : ∃ M', memStore32 Mi (F + 0x84) v83 = M' := ⟨_, rfl⟩
  rw [hM84] at u84
  have hc84 : CodeIn M84 B scalar29MontMulCode := by rw [← hM84]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr84 : ∀ x, Sep F 0x190 x 1 → M84 x = M0 x := fun x hx => by
    rw [← hM84, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n85, d85, u85⟩ := u84.aluE hc84 smm_at_14c (off' := 0x14E) (by decide) (v := v73)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n86, d86, u86⟩ := u85.aluE hc84 smm_at_14e (off' := 0x150) (by decide) (v := v6)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n87, v87, d87, hv87, u87⟩ := u86.aluG hc84 smm_at_150 (off' := 0x154) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv87
  obtain ⟨n88, v88, d88, hv88, u88⟩ := u87.aluG hc84 smm_at_154 (off' := 0x158) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv88
  obtain ⟨n89, v89, d89, hv89, u89⟩ := u88.aluG hc84 smm_at_158 (off' := 0x15C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv89
  obtain ⟨n90, v90, d90, hv90, u90⟩ := u89.aluG hc84 smm_at_15c (off' := 0x15E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv90
  obtain ⟨n91, d91, u91⟩ := u90.swG hc84 smm_at_15e (off' := 0x162) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]; exact aligned_add hF (k := 276) (by decide)) (a := F + 0x114) (v := v90)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31])
  obtain ⟨M91, hM91⟩ : ∃ M', memStore32 M84 (F + 0x114) v90 = M' := ⟨_, rfl⟩
  rw [hM91] at u91
  have hc91 : CodeIn M91 B scalar29MontMulCode := by rw [← hM91]; exact hc84.store32 (frm_sep' sFC (by decide))
  have fr91 : ∀ x, Sep F 0x190 x 1 → M91 x = M0 x := fun x hx => by
    rw [← hM91, memStore32_get_sep (frm_sep' hx (by decide)), fr84 x hx]
  obtain ⟨n92, v92, d92, hv92, u92⟩ := u91.aluG hc91 smm_at_162 (off' := 0x164) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv92
  obtain ⟨n93, v93, d93, hv93, u93⟩ := u92.aluG hc91 smm_at_164 (off' := 0x168) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv93
  obtain ⟨n94, v94, d94, hv94, u94⟩ := u93.aluG hc91 smm_at_168 (off' := 0x16C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv94
  obtain ⟨n95, v95, d95, hv95, u95⟩ := u94.aluG hc91 smm_at_16c (off' := 0x16E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv95
  obtain ⟨n96, d96, u96⟩ := u95.aluE hc91 smm_at_16e (off' := 0x170) (by decide) (v := v5)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n97, d97, u97⟩ := u96.swG hc91 smm_at_170 (off' := 0x172) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]; exact aligned_add hF (k := 224) (by decide)) (a := F + 0xE0) (v := v5)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31])
  obtain ⟨M97, hM97⟩ : ∃ M', memStore32 M91 (F + 0xE0) v5 = M' := ⟨_, rfl⟩
  rw [hM97] at u97
  have hc97 : CodeIn M97 B scalar29MontMulCode := by rw [← hM97]; exact hc91.store32 (frm_sep' sFC (by decide))
  have fr97 : ∀ x, Sep F 0x190 x 1 → M97 x = M0 x := fun x hx => by
    rw [← hM97, memStore32_get_sep (frm_sep' hx (by decide)), fr91 x hx]
  obtain ⟨n98, v98, d98, hv98, u98⟩ := u97.aluG hc97 smm_at_172 (off' := 0x176) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv98
  obtain ⟨n99, v99, d99, hv99, u99⟩ := u98.aluG hc97 smm_at_176 (off' := 0x17A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv99
  obtain ⟨n100, v100, d100, hv100, u100⟩ := u99.aluG hc97 smm_at_17a (off' := 0x17E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv100
  obtain ⟨n101, v101, d101, hv101, u101⟩ := u100.aluG hc97 smm_at_17e (off' := 0x180) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv101
  obtain ⟨n102, d102, u102⟩ := u101.swG hc97 smm_at_180 (off' := 0x182) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]; exact aligned_add hF (k := 236) (by decide)) (a := F + 0xEC) (v := v3)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31])
  obtain ⟨M102, hM102⟩ : ∃ M', memStore32 M97 (F + 0xEC) v3 = M' := ⟨_, rfl⟩
  rw [hM102] at u102
  have hc102 : CodeIn M102 B scalar29MontMulCode := by rw [← hM102]; exact hc97.store32 (frm_sep' sFC (by decide))
  have fr102 : ∀ x, Sep F 0x190 x 1 → M102 x = M0 x := fun x hx => by
    rw [← hM102, memStore32_get_sep (frm_sep' hx (by decide)), fr97 x hx]
  obtain ⟨n103, v103, d103, hv103, u103⟩ := u102.aluG hc102 smm_at_182 (off' := 0x186) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv103
  obtain ⟨n104, v104, d104, hv104, u104⟩ := u103.aluG hc102 smm_at_186 (off' := 0x188) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv104
  obtain ⟨n105, v105, d105, hv105, u105⟩ := u104.aluG hc102 smm_at_188 (off' := 0x18A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv105
  obtain ⟨n106, v106, d106, hv106, u106⟩ := u105.aluG hc102 smm_at_18a (off' := 0x18E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv106
  obtain ⟨n107, v107, d107, hv107, u107⟩ := u106.aluG hc102 smm_at_18e (off' := 0x192) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv107
  obtain ⟨n108, v108, d108, hv108, u108⟩ := u107.aluG hc102 smm_at_192 (off' := 0x194) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv108
  obtain ⟨n109, v109, d109, hv109, u109⟩ := u108.aluG hc102 smm_at_194 (off' := 0x198) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv109
  obtain ⟨n110, d110, u110⟩ := u109.aluE hc102 smm_at_198 (off' := 0x19A) (by decide) (v := v6)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n111, d111, u111⟩ := u110.aluE hc102 smm_at_19a (off' := 0x19C) (by decide) (v := v73)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n112, v112, d112, hv112, u112⟩ := u111.aluG hc102 smm_at_19c (off' := 0x19E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv112
  obtain ⟨n113, v113, d113, hv113, u113⟩ := u112.aluG hc102 smm_at_19e (off' := 0x1A2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv113
  obtain ⟨n114, v114, d114, hv114, u114⟩ := u113.aluG hc102 smm_at_1a2 (off' := 0x1A4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv114
  obtain ⟨n115, v115, d115, hv115, u115⟩ := u114.aluG hc102 smm_at_1a4 (off' := 0x1A6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv115
  obtain ⟨n116, v116, d116, hv116, u116⟩ := u115.aluG hc102 smm_at_1a6 (off' := 0x1AA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv116
  obtain ⟨n117, v117, d117, hv117, u117⟩ := u116.aluG hc102 smm_at_1aa (off' := 0x1AC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv117
  obtain ⟨n118, v118, d118, hv118, u118⟩ := u117.aluG hc102 smm_at_1ac (off' := 0x1AE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv118
  obtain ⟨n119, v119, d119, hv119, u119⟩ := u118.aluG hc102 smm_at_1ae (off' := 0x1B2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31] at hv119
  have qo1 : reg n119 ra = v117 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo2 : reg n119 sp = F := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo3 : reg n119 (3 : Fin 32) = G3 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo4 : reg n119 (4 : Fin 32) = G4 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo5 : reg n119 (5 : Fin 32) = v9 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo6 : reg n119 (6 : Fin 32) = v66 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo7 : reg n119 (7 : Fin 32) = v60 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo8 : reg n119 (8 : Fin 32) = v118 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo9 : reg n119 (9 : Fin 32) = v73 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo10 : reg n119 a0 = v109 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo11 : reg n119 a1 = v106 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo12 : reg n119 a2 = v73 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo13 : reg n119 a3 = v6 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo14 : reg n119 a4 = v78 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo15 : reg n119 a5 = v77 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo16 : reg n119 a6 = v81 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo17 : reg n119 a7 = v65 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo18 : reg n119 (18 : Fin 32) = v95 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo19 : reg n119 (19 : Fin 32) = yp := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo20 : reg n119 (20 : Fin 32) = v7 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo21 : reg n119 (21 : Fin 32) = v10 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo22 : reg n119 (22 : Fin 32) = v114 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo23 : reg n119 (23 : Fin 32) = v115 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo24 : reg n119 (24 : Fin 32) = v104 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo25 : reg n119 (25 : Fin 32) = xp := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo26 : reg n119 (26 : Fin 32) = v105 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo27 : reg n119 (27 : Fin 32) = v107 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo28 : reg n119 (28 : Fin 32) = v8 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo29 : reg n119 (29 : Fin 32) = v82 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo30 : reg n119 (30 : Fin 32) = v6 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have qo31 : reg n119 (31 : Fin 32) = v119 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q28, q29, q30, q31]
  have so84 : memLoad32 M102 (F + 0x84) = v83 := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x84) 4 from sep_offsets F (c := 236) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x84) 4 from sep_offsets F (c := 224) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x84) 4 from sep_offsets F (c := 276) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_same]
  have so88 : memLoad32 M102 (F + 0x88) = v67 := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x88) 4 from sep_offsets F (c := 236) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x88) 4 from sep_offsets F (c := 224) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x88) 4 from sep_offsets F (c := 276) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x88) 4 from sep_offsets F (c := 132) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88]
  have soE0 : memLoad32 M102 (F + 0xE0) = v5 := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0xE0) 4 from sep_offsets F (c := 236) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_same]
  have soEC : memLoad32 M102 (F + 0xEC) = v3 := by
    rw [← hM102, memLoad32_store32_same]
  have soF8 : memLoad32 M102 (F + 0xF8) = outp := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0xF8) 4 from sep_offsets F (c := 236) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0xF8) 4 from sep_offsets F (c := 224) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0xF8) 4 from sep_offsets F (c := 276) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xF8) 4 from sep_offsets F (c := 132) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), slF8]
  have so100 : memLoad32 M102 (F + 0x100) = v4 := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x100) 4 from sep_offsets F (c := 236) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x100) 4 from sep_offsets F (c := 224) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x100) 4 from sep_offsets F (c := 276) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x100) 4 from sep_offsets F (c := 132) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100]
  have so108 : memLoad32 M102 (F + 0x108) = v55 := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x108) 4 from sep_offsets F (c := 236) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x108) 4 from sep_offsets F (c := 224) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x108) 4 from sep_offsets F (c := 276) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x108) 4 from sep_offsets F (c := 132) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), sl108]
  have so10C : memLoad32 M102 (F + 0x10C) = v21 := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x10C) 4 from sep_offsets F (c := 236) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x10C) 4 from sep_offsets F (c := 224) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x10C) 4 from sep_offsets F (c := 276) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x10C) 4 from sep_offsets F (c := 132) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so110 : memLoad32 M102 (F + 0x110) = v28 := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x110) 4 from sep_offsets F (c := 236) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x110) 4 from sep_offsets F (c := 224) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x110) 4 from sep_offsets F (c := 276) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x110) 4 from sep_offsets F (c := 132) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so114 : memLoad32 M102 (F + 0x114) = v90 := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x114) 4 from sep_offsets F (c := 236) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x114) 4 from sep_offsets F (c := 224) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_same]
  have so118 : memLoad32 M102 (F + 0x118) = v52 := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x118) 4 from sep_offsets F (c := 236) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x118) 4 from sep_offsets F (c := 224) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x118) 4 from sep_offsets F (c := 276) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x118) 4 from sep_offsets F (c := 132) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), sl118]
  have so11C : memLoad32 M102 (F + 0x11C) = v36 := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x11C) 4 from sep_offsets F (c := 236) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x11C) 4 from sep_offsets F (c := 224) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x11C) 4 from sep_offsets F (c := 276) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x11C) 4 from sep_offsets F (c := 132) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), sl11C]
  have so15C : memLoad32 M102 (F + 0x15C) = memLoad32 M0 (F + 0x15C) := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x15C) 4 from sep_offsets F (c := 236) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x15C) 4 from sep_offsets F (c := 224) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x15C) 4 from sep_offsets F (c := 276) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x15C) 4 from sep_offsets F (c := 132) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), sl15C]
  have so160 : memLoad32 M102 (F + 0x160) = memLoad32 M0 (F + 0x160) := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x160) 4 from sep_offsets F (c := 236) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x160) 4 from sep_offsets F (c := 224) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x160) 4 from sep_offsets F (c := 276) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x160) 4 from sep_offsets F (c := 132) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), sl160]
  have so164 : memLoad32 M102 (F + 0x164) = memLoad32 M0 (F + 0x164) := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x164) 4 from sep_offsets F (c := 236) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x164) 4 from sep_offsets F (c := 224) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x164) 4 from sep_offsets F (c := 276) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x164) 4 from sep_offsets F (c := 132) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), sl164]
  have so168 : memLoad32 M102 (F + 0x168) = memLoad32 M0 (F + 0x168) := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x168) 4 from sep_offsets F (c := 236) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x168) 4 from sep_offsets F (c := 224) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x168) 4 from sep_offsets F (c := 276) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x168) 4 from sep_offsets F (c := 132) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), sl168]
  have so16C : memLoad32 M102 (F + 0x16C) = memLoad32 M0 (F + 0x16C) := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x16C) 4 from sep_offsets F (c := 236) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x16C) 4 from sep_offsets F (c := 224) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x16C) 4 from sep_offsets F (c := 276) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x16C) 4 from sep_offsets F (c := 132) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), sl16C]
  have so170 : memLoad32 M102 (F + 0x170) = memLoad32 M0 (F + 0x170) := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x170) 4 from sep_offsets F (c := 236) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x170) 4 from sep_offsets F (c := 224) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x170) 4 from sep_offsets F (c := 276) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x170) 4 from sep_offsets F (c := 132) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), sl170]
  have so174 : memLoad32 M102 (F + 0x174) = memLoad32 M0 (F + 0x174) := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x174) 4 from sep_offsets F (c := 236) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x174) 4 from sep_offsets F (c := 224) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x174) 4 from sep_offsets F (c := 276) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x174) 4 from sep_offsets F (c := 132) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), sl174]
  have so178 : memLoad32 M102 (F + 0x178) = memLoad32 M0 (F + 0x178) := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x178) 4 from sep_offsets F (c := 236) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x178) 4 from sep_offsets F (c := 224) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x178) 4 from sep_offsets F (c := 276) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x178) 4 from sep_offsets F (c := 132) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), sl178]
  have so17C : memLoad32 M102 (F + 0x17C) = memLoad32 M0 (F + 0x17C) := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x17C) 4 from sep_offsets F (c := 236) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x17C) 4 from sep_offsets F (c := 224) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x17C) 4 from sep_offsets F (c := 276) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x17C) 4 from sep_offsets F (c := 132) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), sl17C]
  have so180 : memLoad32 M102 (F + 0x180) = memLoad32 M0 (F + 0x180) := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x180) 4 from sep_offsets F (c := 236) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x180) 4 from sep_offsets F (c := 224) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x180) 4 from sep_offsets F (c := 276) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x180) 4 from sep_offsets F (c := 132) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), sl180]
  have so184 : memLoad32 M102 (F + 0x184) = memLoad32 M0 (F + 0x184) := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x184) 4 from sep_offsets F (c := 236) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x184) 4 from sep_offsets F (c := 224) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x184) 4 from sep_offsets F (c := 276) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x184) 4 from sep_offsets F (c := 132) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), sl184]
  have so188 : memLoad32 M102 (F + 0x188) = memLoad32 M0 (F + 0x188) := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x188) 4 from sep_offsets F (c := 236) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x188) 4 from sep_offsets F (c := 224) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x188) 4 from sep_offsets F (c := 276) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x188) 4 from sep_offsets F (c := 132) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), sl188]
  have so18C : memLoad32 M102 (F + 0x18C) = memLoad32 M0 (F + 0x18C) := by
    rw [← hM102, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x18C) 4 from sep_offsets F (c := 236) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x18C) 4 from sep_offsets F (c := 224) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM91, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x18C) 4 from sep_offsets F (c := 276) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM84, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x18C) 4 from sep_offsets F (c := 132) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), sl18C]
  exact ⟨n119, M102, v80, v81, v82, v83, v87, v88, v89, v90, v92, v93, v94, v95, v98, v99, v100, v101, v103, v104, v105, v106, v107, v108, v109, v112, v113, v114, v115, v116, v117, v118, v119, (.cons d80 (.cons d81 (.cons d82 (.cons d83 (.cons d84 (.cons d85 (.cons d86 (.cons d87 (.cons d88 (.cons d89 (.cons d90 (.cons d91 (.cons d92 (.cons d93 (.cons d94 (.cons d95 (.cons d96 (.cons d97 (.cons d98 (.cons d99 (.cons d100 (.cons d101 (.cons d102 (.cons d103 (.cons d104 (.cons d105 (.cons d106 (.cons d107 (.cons d108 (.cons d109 (.cons d110 (.cons d111 (.cons d112 (.cons d113 (.cons d114 (.cons d115 (.cons d116 (.cons d117 (.cons d118 (.single d119)))))))))))))))))))))))))))))))))))))))), u119.self, hc102, fr102, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so84, so88, soE0, soEC, soF8, so100, so108, so10C, so110, so114, so118, so11C, so15C, so160, so164, so168, so16C, so170, so174, so178, so17C, so180, so184, so188, so18C, hv80, hv81, hv82, hv83, hv87, hv88, hv89, hv90, hv92, hv93, hv94, hv95, hv98, hv99, hv100, hv101, hv103, hv104, hv105, hv106, hv107, hv108, hv109, hv112, hv113, hv114, hv115, hv116, hv117, hv118, hv119⟩

end C3.RV32
