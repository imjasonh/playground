import C3BootProofs.Proofs.Fe25519Decode

/-! # The straight-line body of `FieldElement2625::square_inner`, as compiled

`scripts/gen-fe25519.py` writes this file from the decoded instructions: a
theorem for each 40 instructions, the facts for each product and sum, and
`fsq_body`, which chains them. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem fsq_g0 {M0 Mi : Word → BitVec 8} {B F zo xp G3 G4 : Word} {n : Machine}
    (s : St Mi B n 0x1C (reg n)) (hc : CodeIn Mi B feSquareInnerCode)
    (fr : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hZ : zo.toNat % 4 = 0) (hx : xp.toNat % 4 = 0)
    (sFC : Sep F 0x50 B feSquareInnerCode.length) (sZC : Sep zo 0x50 B feSquareInnerCode.length)
    (sXF : Sep xp 40 F 0x50) (sXZ : Sep xp 40 zo 0x50) (sFZ : Sep F 0x50 zo 0x50)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q10 : reg n a0 = zo)
    (q11 : reg n a1 = xp)
    (sl1C : memLoad32 Mi (F + 0x1C) = memLoad32 M0 (F + 0x1C))
    (sl20 : memLoad32 Mi (F + 0x20) = memLoad32 M0 (F + 0x20))
    (sl24 : memLoad32 Mi (F + 0x24) = memLoad32 M0 (F + 0x24))
    (sl28 : memLoad32 Mi (F + 0x28) = memLoad32 M0 (F + 0x28))
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v1 v3 v4 v6 v7 v8 v9 v10 v11 v12 v13 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v28 v29 v30 v31 v32 v33 v35 v36 v37 v38 v39 : Word),
      Steps n n' ∧
      St M' B n' 0xA0 (reg n') ∧
      CodeIn M' B feSquareInnerCode ∧
      (∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M' x = M0 x) ∧
      reg n' ra = v33 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (6 : Fin 32) = zo ∧
      reg n' (8 : Fin 32) = v25 ∧
      reg n' (9 : Fin 32) = v36 ∧
      reg n' a0 = v28 ∧
      reg n' a1 = v38 ∧
      reg n' a2 = v29 ∧
      reg n' a3 = v39 ∧
      reg n' a4 = v37 ∧
      reg n' a5 = v15 ∧
      reg n' a6 = v3 ∧
      reg n' (18 : Fin 32) = v9 ∧
      reg n' (19 : Fin 32) = v17 ∧
      reg n' (20 : Fin 32) = v16 ∧
      reg n' (21 : Fin 32) = v32 ∧
      reg n' (22 : Fin 32) = v10 ∧
      reg n' (23 : Fin 32) = v18 ∧
      reg n' (24 : Fin 32) = v21 ∧
      reg n' (25 : Fin 32) = v8 ∧
      reg n' (26 : Fin 32) = v12 ∧
      reg n' (27 : Fin 32) = v20 ∧
      reg n' (28 : Fin 32) = v30 ∧
      reg n' (29 : Fin 32) = v6 ∧
      reg n' (30 : Fin 32) = v31 ∧
      reg n' (31 : Fin 32) = v19 ∧
      memLoad32 M' (F + 0x8) = v3 ∧
      memLoad32 M' (F + 0xC) = v4 ∧
      memLoad32 M' (F + 0x10) = v28 ∧
      memLoad32 M' (F + 0x14) = v13 ∧
      memLoad32 M' (F + 0x18) = v1 ∧
      memLoad32 M' (F + 0x1C) = memLoad32 M0 (F + 0x1C) ∧
      memLoad32 M' (F + 0x20) = memLoad32 M0 (F + 0x20) ∧
      memLoad32 M' (F + 0x24) = memLoad32 M0 (F + 0x24) ∧
      memLoad32 M' (F + 0x28) = memLoad32 M0 (F + 0x28) ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M0 (xp + 0x24) = v1 ∧
      memLoad32 M0 (xp + 0x14) = v3 ∧
      memLoad32 M0 (xp + 0x1C) = v4 ∧
      memLoad32 M0 (xp + 0x18) = v6 ∧
      aluEval .add 0 0x13 = v7 ∧
      memLoad32 M0 (xp + 0x4) = v8 ∧
      memLoad32 M0 (xp + 0xC) = v9 ∧
      aluEval .mul v1 v7 = v10 ∧
      aluEval .mul v3 v7 = v11 ∧
      aluEval .mul v4 v7 = v12 ∧
      memLoad32 M0 (xp + 0x20) = v13 ∧
      memLoad32 M0 (xp + 0x0) = v15 ∧
      memLoad32 M0 (xp + 0x8) = v16 ∧
      memLoad32 M0 (xp + 0x10) = v17 ∧
      aluEval .sll v8 0x1 = v18 ∧
      aluEval .sll v9 0x1 = v19 ∧
      aluEval .mul v6 v7 = v20 ∧
      aluEval .mul v13 v7 = v21 ∧
      aluEval .mulhu v10 v18 = v22 ∧
      aluEval .mulhu v12 v19 = v23 ∧
      aluEval .mulhu v11 v3 = v24 ∧
      aluEval .mul v12 v19 = v25 ∧
      aluEval .mul v11 v3 = v26 ∧
      aluEval .sll v16 0x1 = v28 ∧
      aluEval .mul v10 v18 = v29 ∧
      aluEval .sll v17 0x1 = v30 ∧
      aluEval .mulhu v15 v15 = v31 ∧
      aluEval .mul v15 v15 = v32 ∧
      aluEval .mulhu v21 v28 = v33 ∧
      aluEval .add v23 v24 = v35 ∧
      aluEval .mulhu v20 v30 = v36 ∧
      aluEval .add v26 v25 = v37 ∧
      aluEval .add v22 v35 = v38 ∧
      aluEval .mul v20 v30 = v39 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n0, d0, u0⟩ := s.aluE hc fsq_at_1c (off' := 0x1E) (by decide) (v := zo)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n1, v1, d1, hv1, u1⟩ := u0.lwG hc fsq_at_1e (off' := 0x20) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hx (k := 36) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv1
  rw [load_frame2 fr (show Sep F 0x50 (xp + 0x24) 4 from sXF.symm.subR (c := 36) (l := 4) (by decide)) (show Sep zo 0x50 (xp + 0x24) 4 from sXZ.symm.subR (c := 36) (l := 4) (by decide))] at hv1
  obtain ⟨n2, d2, u2⟩ := u1.swG hc fsq_at_20 (off' := 0x22) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hF (k := 24) (by decide)) (a := F + 0x18) (v := v1)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11])
  obtain ⟨M2, hM2⟩ : ∃ M', memStore32 Mi (F + 0x18) v1 = M' := ⟨_, rfl⟩
  rw [hM2] at u2
  have hc2 : CodeIn M2 B feSquareInnerCode := by rw [← hM2]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr2 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M2 x = M0 x := fun x hxF hxZ => by
    rw [← hM2, memStore32_get_sep (frm_sep' hxF (by decide)), fr x hxF hxZ]
  obtain ⟨n3, v3, d3, hv3, u3⟩ := u2.lwG hc2 fsq_at_22 (off' := 0x26) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hx (k := 20) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv3
  rw [load_frame2 fr2 (show Sep F 0x50 (xp + 0x14) 4 from sXF.symm.subR (c := 20) (l := 4) (by decide)) (show Sep zo 0x50 (xp + 0x14) 4 from sXZ.symm.subR (c := 20) (l := 4) (by decide))] at hv3
  obtain ⟨n4, v4, d4, hv4, u4⟩ := u3.lwG hc2 fsq_at_26 (off' := 0x28) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hx (k := 28) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv4
  rw [load_frame2 fr2 (show Sep F 0x50 (xp + 0x1C) 4 from sXF.symm.subR (c := 28) (l := 4) (by decide)) (show Sep zo 0x50 (xp + 0x1C) 4 from sXZ.symm.subR (c := 28) (l := 4) (by decide))] at hv4
  obtain ⟨n5, d5, u5⟩ := u4.swG hc2 fsq_at_28 (off' := 0x2A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hF (k := 12) (by decide)) (a := F + 0xC) (v := v4)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11])
  obtain ⟨M5, hM5⟩ : ∃ M', memStore32 M2 (F + 0xC) v4 = M' := ⟨_, rfl⟩
  rw [hM5] at u5
  have hc5 : CodeIn M5 B feSquareInnerCode := by rw [← hM5]; exact hc2.store32 (frm_sep' sFC (by decide))
  have fr5 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M5 x = M0 x := fun x hxF hxZ => by
    rw [← hM5, memStore32_get_sep (frm_sep' hxF (by decide)), fr2 x hxF hxZ]
  obtain ⟨n6, v6, d6, hv6, u6⟩ := u5.lwG hc5 fsq_at_2a (off' := 0x2E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hx (k := 24) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv6
  rw [load_frame2 fr5 (show Sep F 0x50 (xp + 0x18) 4 from sXF.symm.subR (c := 24) (l := 4) (by decide)) (show Sep zo 0x50 (xp + 0x18) 4 from sXZ.symm.subR (c := 24) (l := 4) (by decide))] at hv6
  obtain ⟨n7, v7, d7, hv7, u7⟩ := u6.aluImmG hc5 fsq_at_2e (off' := 0x30) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv7
  obtain ⟨n8, v8, d8, hv8, u8⟩ := u7.lwG hc5 fsq_at_30 (off' := 0x34) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hx (k := 4) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv8
  rw [load_frame2 fr5 (show Sep F 0x50 (xp + 0x4) 4 from sXF.symm.subR (c := 4) (l := 4) (by decide)) (show Sep zo 0x50 (xp + 0x4) 4 from sXZ.symm.subR (c := 4) (l := 4) (by decide))] at hv8
  obtain ⟨n9, v9, d9, hv9, u9⟩ := u8.lwG hc5 fsq_at_34 (off' := 0x38) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hx (k := 12) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv9
  rw [load_frame2 fr5 (show Sep F 0x50 (xp + 0xC) 4 from sXF.symm.subR (c := 12) (l := 4) (by decide)) (show Sep zo 0x50 (xp + 0xC) 4 from sXZ.symm.subR (c := 12) (l := 4) (by decide))] at hv9
  obtain ⟨n10, v10, d10, hv10, u10⟩ := u9.aluG hc5 fsq_at_38 (off' := 0x3C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv10
  obtain ⟨n11, v11, d11, hv11, u11⟩ := u10.aluG hc5 fsq_at_3c (off' := 0x40) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv11
  obtain ⟨n12, v12, d12, hv12, u12⟩ := u11.aluG hc5 fsq_at_40 (off' := 0x44) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv12
  obtain ⟨n13, v13, d13, hv13, u13⟩ := u12.lwG hc5 fsq_at_44 (off' := 0x46) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hx (k := 32) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv13
  rw [load_frame2 fr5 (show Sep F 0x50 (xp + 0x20) 4 from sXF.symm.subR (c := 32) (l := 4) (by decide)) (show Sep zo 0x50 (xp + 0x20) 4 from sXZ.symm.subR (c := 32) (l := 4) (by decide))] at hv13
  obtain ⟨n14, d14, u14⟩ := u13.swG hc5 fsq_at_46 (off' := 0x48) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hF (k := 20) (by decide)) (a := F + 0x14) (v := v13)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11])
  obtain ⟨M14, hM14⟩ : ∃ M', memStore32 M5 (F + 0x14) v13 = M' := ⟨_, rfl⟩
  rw [hM14] at u14
  have hc14 : CodeIn M14 B feSquareInnerCode := by rw [← hM14]; exact hc5.store32 (frm_sep' sFC (by decide))
  have fr14 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M14 x = M0 x := fun x hxF hxZ => by
    rw [← hM14, memStore32_get_sep (frm_sep' hxF (by decide)), fr5 x hxF hxZ]
  obtain ⟨n15, v15, d15, hv15, u15⟩ := u14.lwG hc14 fsq_at_48 (off' := 0x4A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hx (k := 0) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv15
  rw [load_frame2 fr14 (show Sep F 0x50 (xp + 0x0) 4 from sXF.symm.subR (c := 0) (l := 4) (by decide)) (show Sep zo 0x50 (xp + 0x0) 4 from sXZ.symm.subR (c := 0) (l := 4) (by decide))] at hv15
  obtain ⟨n16, v16, d16, hv16, u16⟩ := u15.lwG hc14 fsq_at_4a (off' := 0x4E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hx (k := 8) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv16
  rw [load_frame2 fr14 (show Sep F 0x50 (xp + 0x8) 4 from sXF.symm.subR (c := 8) (l := 4) (by decide)) (show Sep zo 0x50 (xp + 0x8) 4 from sXZ.symm.subR (c := 8) (l := 4) (by decide))] at hv16
  obtain ⟨n17, v17, d17, hv17, u17⟩ := u16.lwG hc14 fsq_at_4e (off' := 0x52) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hx (k := 16) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv17
  rw [load_frame2 fr14 (show Sep F 0x50 (xp + 0x10) 4 from sXF.symm.subR (c := 16) (l := 4) (by decide)) (show Sep zo 0x50 (xp + 0x10) 4 from sXZ.symm.subR (c := 16) (l := 4) (by decide))] at hv17
  obtain ⟨n18, v18, d18, hv18, u18⟩ := u17.aluImmG hc14 fsq_at_52 (off' := 0x56) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv18
  obtain ⟨n19, v19, d19, hv19, u19⟩ := u18.aluImmG hc14 fsq_at_56 (off' := 0x5A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv19
  obtain ⟨n20, v20, d20, hv20, u20⟩ := u19.aluG hc14 fsq_at_5a (off' := 0x5E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv20
  obtain ⟨n21, v21, d21, hv21, u21⟩ := u20.aluG hc14 fsq_at_5e (off' := 0x62) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv21
  obtain ⟨n22, v22, d22, hv22, u22⟩ := u21.aluG hc14 fsq_at_62 (off' := 0x66) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv22
  obtain ⟨n23, v23, d23, hv23, u23⟩ := u22.aluG hc14 fsq_at_66 (off' := 0x6A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv23
  obtain ⟨n24, v24, d24, hv24, u24⟩ := u23.aluG hc14 fsq_at_6a (off' := 0x6E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv24
  obtain ⟨n25, v25, d25, hv25, u25⟩ := u24.aluG hc14 fsq_at_6e (off' := 0x72) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv25
  obtain ⟨n26, v26, d26, hv26, u26⟩ := u25.aluG hc14 fsq_at_72 (off' := 0x76) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv26
  obtain ⟨n27, d27, u27⟩ := u26.swG hc14 fsq_at_76 (off' := 0x78) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hF (k := 8) (by decide)) (a := F + 0x8) (v := v3)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11])
  obtain ⟨M27, hM27⟩ : ∃ M', memStore32 M14 (F + 0x8) v3 = M' := ⟨_, rfl⟩
  rw [hM27] at u27
  have hc27 : CodeIn M27 B feSquareInnerCode := by rw [← hM27]; exact hc14.store32 (frm_sep' sFC (by decide))
  have fr27 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M27 x = M0 x := fun x hxF hxZ => by
    rw [← hM27, memStore32_get_sep (frm_sep' hxF (by decide)), fr14 x hxF hxZ]
  obtain ⟨n28, v28, d28, hv28, u28⟩ := u27.aluImmG hc27 fsq_at_78 (off' := 0x7C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv28
  obtain ⟨n29, v29, d29, hv29, u29⟩ := u28.aluG hc27 fsq_at_7c (off' := 0x80) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv29
  obtain ⟨n30, v30, d30, hv30, u30⟩ := u29.aluImmG hc27 fsq_at_80 (off' := 0x84) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv30
  obtain ⟨n31, v31, d31, hv31, u31⟩ := u30.aluG hc27 fsq_at_84 (off' := 0x88) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv31
  obtain ⟨n32, v32, d32, hv32, u32⟩ := u31.aluG hc27 fsq_at_88 (off' := 0x8C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv32
  obtain ⟨n33, v33, d33, hv33, u33⟩ := u32.aluG hc27 fsq_at_8c (off' := 0x90) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv33
  obtain ⟨n34, d34, u34⟩ := u33.swG hc27 fsq_at_90 (off' := 0x92) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]; exact aligned_add hF (k := 16) (by decide)) (a := F + 0x10) (v := v28)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11])
  obtain ⟨M34, hM34⟩ : ∃ M', memStore32 M27 (F + 0x10) v28 = M' := ⟨_, rfl⟩
  rw [hM34] at u34
  have hc34 : CodeIn M34 B feSquareInnerCode := by rw [← hM34]; exact hc27.store32 (frm_sep' sFC (by decide))
  have fr34 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M34 x = M0 x := fun x hxF hxZ => by
    rw [← hM34, memStore32_get_sep (frm_sep' hxF (by decide)), fr27 x hxF hxZ]
  obtain ⟨n35, v35, d35, hv35, u35⟩ := u34.aluG hc34 fsq_at_92 (off' := 0x94) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv35
  obtain ⟨n36, v36, d36, hv36, u36⟩ := u35.aluG hc34 fsq_at_94 (off' := 0x98) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv36
  obtain ⟨n37, v37, d37, hv37, u37⟩ := u36.aluG hc34 fsq_at_98 (off' := 0x9A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv37
  obtain ⟨n38, v38, d38, hv38, u38⟩ := u37.aluG hc34 fsq_at_9a (off' := 0x9C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv38
  obtain ⟨n39, v39, d39, hv39, u39⟩ := u38.aluG hc34 fsq_at_9c (off' := 0xA0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11] at hv39
  have qo1 : reg n39 ra = v33 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo2 : reg n39 sp = F := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo3 : reg n39 (3 : Fin 32) = G3 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo4 : reg n39 (4 : Fin 32) = G4 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo6 : reg n39 (6 : Fin 32) = zo := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo8 : reg n39 (8 : Fin 32) = v25 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo9 : reg n39 (9 : Fin 32) = v36 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo10 : reg n39 a0 = v28 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo11 : reg n39 a1 = v38 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo12 : reg n39 a2 = v29 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo13 : reg n39 a3 = v39 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo14 : reg n39 a4 = v37 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo15 : reg n39 a5 = v15 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo16 : reg n39 a6 = v3 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo18 : reg n39 (18 : Fin 32) = v9 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo19 : reg n39 (19 : Fin 32) = v17 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo20 : reg n39 (20 : Fin 32) = v16 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo21 : reg n39 (21 : Fin 32) = v32 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo22 : reg n39 (22 : Fin 32) = v10 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo23 : reg n39 (23 : Fin 32) = v18 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo24 : reg n39 (24 : Fin 32) = v21 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo25 : reg n39 (25 : Fin 32) = v8 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo26 : reg n39 (26 : Fin 32) = v12 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo27 : reg n39 (27 : Fin 32) = v20 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo28 : reg n39 (28 : Fin 32) = v30 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo29 : reg n39 (29 : Fin 32) = v6 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo30 : reg n39 (30 : Fin 32) = v31 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have qo31 : reg n39 (31 : Fin 32) = v19 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q10, q11]
  have so8 : memLoad32 M34 (F + 0x8) = v3 := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x8) 4 from sep_offsets F (c := 16) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_same]
  have soC : memLoad32 M34 (F + 0xC) = v4 := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0xC) 4 from sep_offsets F (c := 16) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0xC) 4 from sep_offsets F (c := 8) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0xC) 4 from sep_offsets F (c := 20) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_same]
  have so10 : memLoad32 M34 (F + 0x10) = v28 := by
    rw [← hM34, memLoad32_store32_same]
  have so14 : memLoad32 M34 (F + 0x14) = v13 := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x14) 4 from sep_offsets F (c := 16) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x14) 4 from sep_offsets F (c := 8) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_same]
  have so18 : memLoad32 M34 (F + 0x18) = v1 := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x18) 4 from sep_offsets F (c := 16) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x18) 4 from sep_offsets F (c := 8) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x18) 4 from sep_offsets F (c := 20) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x18) 4 from sep_offsets F (c := 12) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_same]
  have so1C : memLoad32 M34 (F + 0x1C) = memLoad32 M0 (F + 0x1C) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x1C) 4 from sep_offsets F (c := 16) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x1C) 4 from sep_offsets F (c := 8) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x1C) 4 from sep_offsets F (c := 20) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x1C) 4 from sep_offsets F (c := 12) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x1C) 4 from sep_offsets F (c := 24) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), sl1C]
  have so20 : memLoad32 M34 (F + 0x20) = memLoad32 M0 (F + 0x20) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x20) 4 from sep_offsets F (c := 16) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x20) 4 from sep_offsets F (c := 8) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x20) 4 from sep_offsets F (c := 20) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x20) 4 from sep_offsets F (c := 12) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x20) 4 from sep_offsets F (c := 24) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), sl20]
  have so24 : memLoad32 M34 (F + 0x24) = memLoad32 M0 (F + 0x24) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x24) 4 from sep_offsets F (c := 16) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x24) 4 from sep_offsets F (c := 8) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x24) 4 from sep_offsets F (c := 20) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x24) 4 from sep_offsets F (c := 12) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x24) 4 from sep_offsets F (c := 24) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), sl24]
  have so28 : memLoad32 M34 (F + 0x28) = memLoad32 M0 (F + 0x28) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x28) 4 from sep_offsets F (c := 16) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x28) 4 from sep_offsets F (c := 8) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x28) 4 from sep_offsets F (c := 20) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x28) 4 from sep_offsets F (c := 12) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x28) 4 from sep_offsets F (c := 24) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), sl28]
  have so2C : memLoad32 M34 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x2C) 4 from sep_offsets F (c := 16) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x2C) 4 from sep_offsets F (c := 8) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x2C) 4 from sep_offsets F (c := 20) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x2C) 4 from sep_offsets F (c := 12) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x2C) 4 from sep_offsets F (c := 24) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), sl2C]
  have so30 : memLoad32 M34 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x30) 4 from sep_offsets F (c := 16) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x30) 4 from sep_offsets F (c := 8) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x30) 4 from sep_offsets F (c := 20) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x30) 4 from sep_offsets F (c := 12) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x30) 4 from sep_offsets F (c := 24) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), sl30]
  have so34 : memLoad32 M34 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x34) 4 from sep_offsets F (c := 16) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x34) 4 from sep_offsets F (c := 8) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x34) 4 from sep_offsets F (c := 20) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x34) 4 from sep_offsets F (c := 12) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x34) 4 from sep_offsets F (c := 24) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), sl34]
  have so38 : memLoad32 M34 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x38) 4 from sep_offsets F (c := 16) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x38) 4 from sep_offsets F (c := 8) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x38) 4 from sep_offsets F (c := 20) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x38) 4 from sep_offsets F (c := 12) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x38) 4 from sep_offsets F (c := 24) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), sl38]
  have so3C : memLoad32 M34 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x3C) 4 from sep_offsets F (c := 16) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x3C) 4 from sep_offsets F (c := 8) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x3C) 4 from sep_offsets F (c := 20) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x3C) 4 from sep_offsets F (c := 12) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x3C) 4 from sep_offsets F (c := 24) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), sl3C]
  have so40 : memLoad32 M34 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x40) 4 from sep_offsets F (c := 16) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x40) 4 from sep_offsets F (c := 8) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x40) 4 from sep_offsets F (c := 20) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x40) 4 from sep_offsets F (c := 12) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x40) 4 from sep_offsets F (c := 24) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), sl40]
  have so44 : memLoad32 M34 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x44) 4 from sep_offsets F (c := 16) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x44) 4 from sep_offsets F (c := 8) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x44) 4 from sep_offsets F (c := 20) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x44) 4 from sep_offsets F (c := 12) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x44) 4 from sep_offsets F (c := 24) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), sl44]
  have so48 : memLoad32 M34 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x48) 4 from sep_offsets F (c := 16) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x48) 4 from sep_offsets F (c := 8) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x48) 4 from sep_offsets F (c := 20) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x48) 4 from sep_offsets F (c := 12) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x48) 4 from sep_offsets F (c := 24) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), sl48]
  have so4C : memLoad32 M34 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x4C) 4 from sep_offsets F (c := 16) (n := 4) (d := 76) (k := 4) (by decide) (by decide) (by decide)), ← hM27, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x4C) 4 from sep_offsets F (c := 8) (n := 4) (d := 76) (k := 4) (by decide) (by decide) (by decide)), ← hM14, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x4C) 4 from sep_offsets F (c := 20) (n := 4) (d := 76) (k := 4) (by decide) (by decide) (by decide)), ← hM5, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x4C) 4 from sep_offsets F (c := 12) (n := 4) (d := 76) (k := 4) (by decide) (by decide) (by decide)), ← hM2, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x4C) 4 from sep_offsets F (c := 24) (n := 4) (d := 76) (k := 4) (by decide) (by decide) (by decide)), sl4C]
  exact ⟨n39, M34, v1, v3, v4, v6, v7, v8, v9, v10, v11, v12, v13, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v28, v29, v30, v31, v32, v33, v35, v36, v37, v38, v39, (.cons d0 (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18 (.cons d19 (.cons d20 (.cons d21 (.cons d22 (.cons d23 (.cons d24 (.cons d25 (.cons d26 (.cons d27 (.cons d28 (.cons d29 (.cons d30 (.cons d31 (.cons d32 (.cons d33 (.cons d34 (.cons d35 (.cons d36 (.cons d37 (.cons d38 (.single d39)))))))))))))))))))))))))))))))))))))))), u39.self, hc34, fr34, qo1, qo2, qo3, qo4, qo6, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so8, soC, so10, so14, so18, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, hv1, hv3, hv4, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv15, hv16, hv17, hv18, hv19, hv20, hv21, hv22, hv23, hv24, hv25, hv26, hv28, hv29, hv30, hv31, hv32, hv33, hv35, hv36, hv37, hv38, hv39⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem fsq_g1 {M0 Mi : Word → BitVec 8} {B F zo xp G3 G4 : Word} {n : Machine} {v1 v3 v4 v6 v8 v9 v10 v12 v13 v15 v16 v17 v18 v19 v20 v21 v25 v28 v29 v30 v31 v32 v33 v36 v37 v38 v39 : Word}
    (s : St Mi B n 0xA0 (reg n)) (hc : CodeIn Mi B feSquareInnerCode)
    (fr : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hZ : zo.toNat % 4 = 0) (hx : xp.toNat % 4 = 0)
    (sFC : Sep F 0x50 B feSquareInnerCode.length) (sZC : Sep zo 0x50 B feSquareInnerCode.length)
    (sXF : Sep xp 40 F 0x50) (sXZ : Sep xp 40 zo 0x50) (sFZ : Sep F 0x50 zo 0x50)
    (q1 : reg n ra = v33)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q6 : reg n (6 : Fin 32) = zo)
    (q8 : reg n (8 : Fin 32) = v25)
    (q9 : reg n (9 : Fin 32) = v36)
    (q10 : reg n a0 = v28)
    (q11 : reg n a1 = v38)
    (q12 : reg n a2 = v29)
    (q13 : reg n a3 = v39)
    (q14 : reg n a4 = v37)
    (q15 : reg n a5 = v15)
    (q16 : reg n a6 = v3)
    (q18 : reg n (18 : Fin 32) = v9)
    (q19 : reg n (19 : Fin 32) = v17)
    (q20 : reg n (20 : Fin 32) = v16)
    (q21 : reg n (21 : Fin 32) = v32)
    (q22 : reg n (22 : Fin 32) = v10)
    (q23 : reg n (23 : Fin 32) = v18)
    (q24 : reg n (24 : Fin 32) = v21)
    (q25 : reg n (25 : Fin 32) = v8)
    (q26 : reg n (26 : Fin 32) = v12)
    (q27 : reg n (27 : Fin 32) = v20)
    (q28 : reg n (28 : Fin 32) = v30)
    (q29 : reg n (29 : Fin 32) = v6)
    (q30 : reg n (30 : Fin 32) = v31)
    (q31 : reg n (31 : Fin 32) = v19)
    (sl8 : memLoad32 Mi (F + 0x8) = v3)
    (slC : memLoad32 Mi (F + 0xC) = v4)
    (sl10 : memLoad32 Mi (F + 0x10) = v28)
    (sl14 : memLoad32 Mi (F + 0x14) = v13)
    (sl18 : memLoad32 Mi (F + 0x18) = v1)
    (sl1C : memLoad32 Mi (F + 0x1C) = memLoad32 M0 (F + 0x1C))
    (sl20 : memLoad32 Mi (F + 0x20) = memLoad32 M0 (F + 0x20))
    (sl24 : memLoad32 Mi (F + 0x24) = memLoad32 M0 (F + 0x24))
    (sl28 : memLoad32 Mi (F + 0x28) = memLoad32 M0 (F + 0x28))
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 : Word),
      Steps n n' ∧
      St M' B n' 0x120 (reg n') ∧
      CodeIn M' B feSquareInnerCode ∧
      (∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M' x = M0 x) ∧
      reg n' ra = v67 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v48 ∧
      reg n' (6 : Fin 32) = zo ∧
      reg n' (7 : Fin 32) = v76 ∧
      reg n' (8 : Fin 32) = v66 ∧
      reg n' (9 : Fin 32) = v62 ∧
      reg n' a0 = v71 ∧
      reg n' a1 = v69 ∧
      reg n' a2 = v78 ∧
      reg n' a3 = v79 ∧
      reg n' a4 = v72 ∧
      reg n' a5 = v68 ∧
      reg n' a6 = v73 ∧
      reg n' a7 = v70 ∧
      reg n' (18 : Fin 32) = v9 ∧
      reg n' (19 : Fin 32) = v17 ∧
      reg n' (20 : Fin 32) = v16 ∧
      reg n' (21 : Fin 32) = v59 ∧
      reg n' (22 : Fin 32) = v10 ∧
      reg n' (23 : Fin 32) = v18 ∧
      reg n' (24 : Fin 32) = v21 ∧
      reg n' (25 : Fin 32) = v8 ∧
      reg n' (26 : Fin 32) = v12 ∧
      reg n' (27 : Fin 32) = v20 ∧
      reg n' (28 : Fin 32) = v30 ∧
      reg n' (29 : Fin 32) = v6 ∧
      reg n' (30 : Fin 32) = v64 ∧
      reg n' (31 : Fin 32) = v19 ∧
      memLoad32 M' (F + 0x8) = v3 ∧
      memLoad32 M' (F + 0xC) = v4 ∧
      memLoad32 M' (F + 0x10) = v28 ∧
      memLoad32 M' (F + 0x14) = v13 ∧
      memLoad32 M' (F + 0x18) = v1 ∧
      memLoad32 M' (F + 0x1C) = memLoad32 M0 (F + 0x1C) ∧
      memLoad32 M' (F + 0x20) = memLoad32 M0 (F + 0x20) ∧
      memLoad32 M' (F + 0x24) = memLoad32 M0 (F + 0x24) ∧
      memLoad32 M' (F + 0x28) = memLoad32 M0 (F + 0x28) ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      aluEval .sltu v37 v25 = v40 ∧
      aluEval .add v29 v37 = v41 ∧
      aluEval .add v38 v40 = v42 ∧
      aluEval .mul v21 v28 = v43 ∧
      aluEval .sltu v41 v37 = v44 ∧
      aluEval .add v42 v44 = v45 ∧
      aluEval .srl v41 0x1F = v46 ∧
      aluEval .sll v45 0x1 = v47 ∧
      aluEval .sll v15 0x1 = v48 ∧
      aluEval .or v47 v46 = v49 ∧
      aluEval .sll v41 0x1 = v50 ∧
      aluEval .add v32 v39 = v51 ∧
      aluEval .sltu v51 v39 = v52 ∧
      aluEval .add v31 v36 = v53 ∧
      aluEval .add v43 v51 = v54 ∧
      aluEval .add v53 v33 = v55 ∧
      aluEval .sltu v54 v51 = v56 ∧
      aluEval .add v52 v55 = v57 ∧
      aluEval .add v57 v56 = v58 ∧
      aluEval .add v54 v50 = v59 ∧
      aluEval .mul v10 v16 = v60 ∧
      aluEval .mul v12 v17 = v61 ∧
      aluEval .mulhu v10 v16 = v62 ∧
      aluEval .mulhu v12 v17 = v63 ∧
      aluEval .sll v3 0x1 = v64 ∧
      aluEval .sltu v59 v54 = v65 ∧
      aluEval .add v65 v58 = v66 ∧
      aluEval .mul v48 v8 = v67 ∧
      aluEval .mulhu v48 v8 = v68 ∧
      aluEval .mulhu v20 v64 = v69 ∧
      aluEval .mulhu v21 v19 = v70 ∧
      aluEval .mul v20 v64 = v71 ∧
      aluEval .add v61 v60 = v72 ∧
      aluEval .mul v21 v19 = v73 ∧
      aluEval .add v63 v62 = v74 ∧
      aluEval .sltu v72 v60 = v75 ∧
      aluEval .add v49 v66 = v76 ∧
      aluEval .add v75 v74 = v77 ∧
      aluEval .sll v77 0x1 = v78 ∧
      aluEval .srl v72 0x1F = v79 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n40, v40, d40, hv40, u40⟩ := s.aluG hc fsq_at_a0 (off' := 0xA4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv40
  obtain ⟨n41, v41, d41, hv41, u41⟩ := u40.aluG hc fsq_at_a4 (off' := 0xA6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv41
  obtain ⟨n42, v42, d42, hv42, u42⟩ := u41.aluG hc fsq_at_a6 (off' := 0xA8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv42
  obtain ⟨n43, v43, d43, hv43, u43⟩ := u42.aluG hc fsq_at_a8 (off' := 0xAC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv43
  obtain ⟨n44, v44, d44, hv44, u44⟩ := u43.aluG hc fsq_at_ac (off' := 0xB0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv44
  obtain ⟨n45, v45, d45, hv45, u45⟩ := u44.aluG hc fsq_at_b0 (off' := 0xB2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv45
  obtain ⟨n46, v46, d46, hv46, u46⟩ := u45.aluImmG hc fsq_at_b2 (off' := 0xB6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv46
  obtain ⟨n47, v47, d47, hv47, u47⟩ := u46.aluImmG hc fsq_at_b6 (off' := 0xB8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv47
  obtain ⟨n48, v48, d48, hv48, u48⟩ := u47.aluImmG hc fsq_at_b8 (off' := 0xBC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv48
  obtain ⟨n49, v49, d49, hv49, u49⟩ := u48.aluG hc fsq_at_bc (off' := 0xC0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv49
  obtain ⟨n50, v50, d50, hv50, u50⟩ := u49.aluImmG hc fsq_at_c0 (off' := 0xC2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv50
  obtain ⟨n51, v51, d51, hv51, u51⟩ := u50.aluG hc fsq_at_c2 (off' := 0xC4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv51
  obtain ⟨n52, v52, d52, hv52, u52⟩ := u51.aluG hc fsq_at_c4 (off' := 0xC8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv52
  obtain ⟨n53, v53, d53, hv53, u53⟩ := u52.aluG hc fsq_at_c8 (off' := 0xCA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv53
  obtain ⟨n54, v54, d54, hv54, u54⟩ := u53.aluG hc fsq_at_ca (off' := 0xCC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv54
  obtain ⟨n55, v55, d55, hv55, u55⟩ := u54.aluG hc fsq_at_cc (off' := 0xCE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv55
  obtain ⟨n56, v56, d56, hv56, u56⟩ := u55.aluG hc fsq_at_ce (off' := 0xD2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv56
  obtain ⟨n57, v57, d57, hv57, u57⟩ := u56.aluG hc fsq_at_d2 (off' := 0xD4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv57
  obtain ⟨n58, v58, d58, hv58, u58⟩ := u57.aluG hc fsq_at_d4 (off' := 0xD8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv58
  obtain ⟨n59, v59, d59, hv59, u59⟩ := u58.aluG hc fsq_at_d8 (off' := 0xDC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv59
  obtain ⟨n60, v60, d60, hv60, u60⟩ := u59.aluG hc fsq_at_dc (off' := 0xE0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv60
  obtain ⟨n61, v61, d61, hv61, u61⟩ := u60.aluG hc fsq_at_e0 (off' := 0xE4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv61
  obtain ⟨n62, v62, d62, hv62, u62⟩ := u61.aluG hc fsq_at_e4 (off' := 0xE8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv62
  obtain ⟨n63, v63, d63, hv63, u63⟩ := u62.aluG hc fsq_at_e8 (off' := 0xEC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv63
  obtain ⟨n64, v64, d64, hv64, u64⟩ := u63.aluImmG hc fsq_at_ec (off' := 0xF0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv64
  obtain ⟨n65, v65, d65, hv65, u65⟩ := u64.aluG hc fsq_at_f0 (off' := 0xF4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv65
  obtain ⟨n66, v66, d66, hv66, u66⟩ := u65.aluG hc fsq_at_f4 (off' := 0xF6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv66
  obtain ⟨n67, v67, d67, hv67, u67⟩ := u66.aluG hc fsq_at_f6 (off' := 0xFA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv67
  obtain ⟨n68, v68, d68, hv68, u68⟩ := u67.aluG hc fsq_at_fa (off' := 0xFE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv68
  obtain ⟨n69, v69, d69, hv69, u69⟩ := u68.aluG hc fsq_at_fe (off' := 0x102) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv69
  obtain ⟨n70, v70, d70, hv70, u70⟩ := u69.aluG hc fsq_at_102 (off' := 0x106) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv70
  obtain ⟨n71, v71, d71, hv71, u71⟩ := u70.aluG hc fsq_at_106 (off' := 0x10A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv71
  obtain ⟨n72, v72, d72, hv72, u72⟩ := u71.aluG hc fsq_at_10a (off' := 0x10C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv72
  obtain ⟨n73, v73, d73, hv73, u73⟩ := u72.aluG hc fsq_at_10c (off' := 0x110) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv73
  obtain ⟨n74, v74, d74, hv74, u74⟩ := u73.aluG hc fsq_at_110 (off' := 0x112) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv74
  obtain ⟨n75, v75, d75, hv75, u75⟩ := u74.aluG hc fsq_at_112 (off' := 0x116) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv75
  obtain ⟨n76, v76, d76, hv76, u76⟩ := u75.aluG hc fsq_at_116 (off' := 0x118) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv76
  obtain ⟨n77, v77, d77, hv77, u77⟩ := u76.aluG hc fsq_at_118 (off' := 0x11A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv77
  obtain ⟨n78, v78, d78, hv78, u78⟩ := u77.aluImmG hc fsq_at_11a (off' := 0x11C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv78
  obtain ⟨n79, v79, d79, hv79, u79⟩ := u78.aluImmG hc fsq_at_11c (off' := 0x120) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv79
  have qo1 : reg n79 ra = v67 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n79 sp = F := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n79 (3 : Fin 32) = G3 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n79 (4 : Fin 32) = G4 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n79 (5 : Fin 32) = v48 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n79 (6 : Fin 32) = zo := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n79 (7 : Fin 32) = v76 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n79 (8 : Fin 32) = v66 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n79 (9 : Fin 32) = v62 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n79 a0 = v71 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n79 a1 = v69 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n79 a2 = v78 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n79 a3 = v79 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n79 a4 = v72 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n79 a5 = v68 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n79 a6 = v73 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n79 a7 = v70 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n79 (18 : Fin 32) = v9 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n79 (19 : Fin 32) = v17 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n79 (20 : Fin 32) = v16 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n79 (21 : Fin 32) = v59 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n79 (22 : Fin 32) = v10 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n79 (23 : Fin 32) = v18 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n79 (24 : Fin 32) = v21 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n79 (25 : Fin 32) = v8 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n79 (26 : Fin 32) = v12 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n79 (27 : Fin 32) = v20 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n79 (28 : Fin 32) = v30 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n79 (29 : Fin 32) = v6 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n79 (30 : Fin 32) = v64 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n79 (31 : Fin 32) = v19 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q6, q8, q9, q10, q11, q12, q13, q14, q15, q16, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so8 : memLoad32 Mi (F + 0x8) = v3 := by
    rw [sl8]
  have soC : memLoad32 Mi (F + 0xC) = v4 := by
    rw [slC]
  have so10 : memLoad32 Mi (F + 0x10) = v28 := by
    rw [sl10]
  have so14 : memLoad32 Mi (F + 0x14) = v13 := by
    rw [sl14]
  have so18 : memLoad32 Mi (F + 0x18) = v1 := by
    rw [sl18]
  have so1C : memLoad32 Mi (F + 0x1C) = memLoad32 M0 (F + 0x1C) := by
    rw [sl1C]
  have so20 : memLoad32 Mi (F + 0x20) = memLoad32 M0 (F + 0x20) := by
    rw [sl20]
  have so24 : memLoad32 Mi (F + 0x24) = memLoad32 M0 (F + 0x24) := by
    rw [sl24]
  have so28 : memLoad32 Mi (F + 0x28) = memLoad32 M0 (F + 0x28) := by
    rw [sl28]
  have so2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [sl2C]
  have so30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [sl30]
  have so34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [sl34]
  have so38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [sl38]
  have so3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [sl3C]
  have so40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [sl40]
  have so44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [sl44]
  have so48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [sl48]
  have so4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [sl4C]
  exact ⟨n79, Mi, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, (.cons d40 (.cons d41 (.cons d42 (.cons d43 (.cons d44 (.cons d45 (.cons d46 (.cons d47 (.cons d48 (.cons d49 (.cons d50 (.cons d51 (.cons d52 (.cons d53 (.cons d54 (.cons d55 (.cons d56 (.cons d57 (.cons d58 (.cons d59 (.cons d60 (.cons d61 (.cons d62 (.cons d63 (.cons d64 (.cons d65 (.cons d66 (.cons d67 (.cons d68 (.cons d69 (.cons d70 (.cons d71 (.cons d72 (.cons d73 (.cons d74 (.cons d75 (.cons d76 (.cons d77 (.cons d78 (.single d79)))))))))))))))))))))))))))))))))))))))), u79.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so8, soC, so10, so14, so18, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, hv40, hv41, hv42, hv43, hv44, hv45, hv46, hv47, hv48, hv49, hv50, hv51, hv52, hv53, hv54, hv55, hv56, hv57, hv58, hv59, hv60, hv61, hv62, hv63, hv64, hv65, hv66, hv67, hv68, hv69, hv70, hv71, hv72, hv73, hv74, hv75, hv76, hv77, hv78, hv79⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem fsq_g2 {M0 Mi : Word → BitVec 8} {B F zo xp G3 G4 : Word} {n : Machine} {v1 v3 v4 v6 v8 v9 v10 v12 v13 v16 v17 v18 v19 v20 v21 v28 v30 v48 v59 v62 v64 v66 v67 v68 v69 v70 v71 v72 v73 v76 v78 v79 : Word}
    (s : St Mi B n 0x120 (reg n)) (hc : CodeIn Mi B feSquareInnerCode)
    (fr : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hZ : zo.toNat % 4 = 0) (hx : xp.toNat % 4 = 0)
    (sFC : Sep F 0x50 B feSquareInnerCode.length) (sZC : Sep zo 0x50 B feSquareInnerCode.length)
    (sXF : Sep xp 40 F 0x50) (sXZ : Sep xp 40 zo 0x50) (sFZ : Sep F 0x50 zo 0x50)
    (q1 : reg n ra = v67)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v48)
    (q6 : reg n (6 : Fin 32) = zo)
    (q7 : reg n (7 : Fin 32) = v76)
    (q8 : reg n (8 : Fin 32) = v66)
    (q9 : reg n (9 : Fin 32) = v62)
    (q10 : reg n a0 = v71)
    (q11 : reg n a1 = v69)
    (q12 : reg n a2 = v78)
    (q13 : reg n a3 = v79)
    (q14 : reg n a4 = v72)
    (q15 : reg n a5 = v68)
    (q16 : reg n a6 = v73)
    (q17 : reg n a7 = v70)
    (q18 : reg n (18 : Fin 32) = v9)
    (q19 : reg n (19 : Fin 32) = v17)
    (q20 : reg n (20 : Fin 32) = v16)
    (q21 : reg n (21 : Fin 32) = v59)
    (q22 : reg n (22 : Fin 32) = v10)
    (q23 : reg n (23 : Fin 32) = v18)
    (q24 : reg n (24 : Fin 32) = v21)
    (q25 : reg n (25 : Fin 32) = v8)
    (q26 : reg n (26 : Fin 32) = v12)
    (q27 : reg n (27 : Fin 32) = v20)
    (q28 : reg n (28 : Fin 32) = v30)
    (q29 : reg n (29 : Fin 32) = v6)
    (q30 : reg n (30 : Fin 32) = v64)
    (q31 : reg n (31 : Fin 32) = v19)
    (sl8 : memLoad32 Mi (F + 0x8) = v3)
    (slC : memLoad32 Mi (F + 0xC) = v4)
    (sl10 : memLoad32 Mi (F + 0x10) = v28)
    (sl14 : memLoad32 Mi (F + 0x14) = v13)
    (sl18 : memLoad32 Mi (F + 0x18) = v1)
    (sl1C : memLoad32 Mi (F + 0x1C) = memLoad32 M0 (F + 0x1C))
    (sl20 : memLoad32 Mi (F + 0x20) = memLoad32 M0 (F + 0x20))
    (sl24 : memLoad32 Mi (F + 0x24) = memLoad32 M0 (F + 0x24))
    (sl28 : memLoad32 Mi (F + 0x28) = memLoad32 M0 (F + 0x28))
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v99 v100 v101 v102 v103 v104 v105 v106 v109 v110 v111 v112 v113 v114 v115 v116 v118 v119 : Word),
      Steps n n' ∧
      St M' B n' 0x19A (reg n') ∧
      CodeIn M' B feSquareInnerCode ∧
      (∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M' x = M0 x) ∧
      reg n' ra = v83 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v48 ∧
      reg n' (6 : Fin 32) = zo ∧
      reg n' (7 : Fin 32) = v76 ∧
      reg n' (8 : Fin 32) = v109 ∧
      reg n' (9 : Fin 32) = v112 ∧
      reg n' a0 = v110 ∧
      reg n' a1 = v119 ∧
      reg n' a2 = v115 ∧
      reg n' a3 = v113 ∧
      reg n' a4 = v111 ∧
      reg n' a5 = v116 ∧
      reg n' a6 = v85 ∧
      reg n' a7 = v105 ∧
      reg n' (18 : Fin 32) = v9 ∧
      reg n' (19 : Fin 32) = v17 ∧
      reg n' (20 : Fin 32) = v16 ∧
      reg n' (21 : Fin 32) = v59 ∧
      reg n' (22 : Fin 32) = v10 ∧
      reg n' (23 : Fin 32) = v18 ∧
      reg n' (24 : Fin 32) = v21 ∧
      reg n' (25 : Fin 32) = v91 ∧
      reg n' (26 : Fin 32) = v12 ∧
      reg n' (27 : Fin 32) = v30 ∧
      reg n' (28 : Fin 32) = v30 ∧
      reg n' (29 : Fin 32) = v6 ∧
      reg n' (30 : Fin 32) = v64 ∧
      reg n' (31 : Fin 32) = v19 ∧
      memLoad32 M' (F + 0x8) = v3 ∧
      memLoad32 M' (F + 0xC) = v4 ∧
      memLoad32 M' (F + 0x10) = v28 ∧
      memLoad32 M' (F + 0x14) = v13 ∧
      memLoad32 M' (F + 0x18) = v1 ∧
      memLoad32 M' (F + 0x1C) = memLoad32 M0 (F + 0x1C) ∧
      memLoad32 M' (F + 0x20) = memLoad32 M0 (F + 0x20) ∧
      memLoad32 M' (F + 0x24) = memLoad32 M0 (F + 0x24) ∧
      memLoad32 M' (F + 0x28) = memLoad32 M0 (F + 0x28) ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (zo + 0x0) = v59 ∧
      memLoad32 M' (zo + 0x4) = v76 ∧
      memLoad32 M' (zo + 0x8) = v89 ∧
      memLoad32 M' (zo + 0xC) = v99 ∧
      aluEval .or v78 v79 = v80 ∧
      aluEval .add v69 v68 = v81 ∧
      aluEval .add v81 v70 = v82 ∧
      aluEval .add v67 v71 = v83 ∧
      aluEval .sll v72 0x1 = v84 ∧
      aluEval .add v73 v83 = v85 ∧
      aluEval .sltu v83 v71 = v86 ∧
      aluEval .sltu v85 v83 = v87 ∧
      aluEval .add v86 v82 = v88 ∧
      aluEval .add v84 v85 = v89 ∧
      aluEval .mul v18 v8 = v90 ∧
      aluEval .mulhu v18 v8 = v91 ∧
      aluEval .mul v16 v48 = v92 ∧
      aluEval .mulhu v16 v48 = v93 ∧
      aluEval .add v88 v87 = v94 ∧
      aluEval .sltu v89 v85 = v95 ∧
      aluEval .add v94 v95 = v96 ∧
      aluEval .add v96 v80 = v99 ∧
      aluEval .mul v10 v19 = v100 ∧
      aluEval .mul v12 v64 = v101 ∧
      aluEval .mulhu v10 v19 = v102 ∧
      aluEval .mulhu v12 v64 = v103 ∧
      aluEval .add v93 v91 = v104 ∧
      aluEval .add v90 v92 = v105 ∧
      aluEval .sltu v105 v92 = v106 ∧
      aluEval .add v104 v106 = v109 ∧
      aluEval .mulhu v20 v6 = v110 ∧
      aluEval .mul v20 v6 = v111 ∧
      aluEval .mulhu v21 v30 = v112 ∧
      aluEval .add v101 v100 = v113 ∧
      aluEval .add v102 v103 = v114 ∧
      aluEval .sltu v113 v100 = v115 ∧
      aluEval .mul v21 v30 = v116 ∧
      aluEval .add v114 v115 = v118 ∧
      aluEval .sll v118 0x1 = v119 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n80, v80, d80, hv80, u80⟩ := s.aluG hc fsq_at_120 (off' := 0x122) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv80
  obtain ⟨n81, v81, d81, hv81, u81⟩ := u80.aluG hc fsq_at_122 (off' := 0x124) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv81
  obtain ⟨n82, v82, d82, hv82, u82⟩ := u81.aluG hc fsq_at_124 (off' := 0x126) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv82
  obtain ⟨n83, v83, d83, hv83, u83⟩ := u82.aluG hc fsq_at_126 (off' := 0x128) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv83
  obtain ⟨n84, v84, d84, hv84, u84⟩ := u83.aluImmG hc fsq_at_128 (off' := 0x12A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv84
  obtain ⟨n85, v85, d85, hv85, u85⟩ := u84.aluG hc fsq_at_12a (off' := 0x12C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv85
  obtain ⟨n86, v86, d86, hv86, u86⟩ := u85.aluG hc fsq_at_12c (off' := 0x130) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv86
  obtain ⟨n87, v87, d87, hv87, u87⟩ := u86.aluG hc fsq_at_130 (off' := 0x134) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv87
  obtain ⟨n88, v88, d88, hv88, u88⟩ := u87.aluG hc fsq_at_134 (off' := 0x136) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv88
  obtain ⟨n89, v89, d89, hv89, u89⟩ := u88.aluG hc fsq_at_136 (off' := 0x138) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv89
  obtain ⟨n90, v90, d90, hv90, u90⟩ := u89.aluG hc fsq_at_138 (off' := 0x13C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv90
  obtain ⟨n91, v91, d91, hv91, u91⟩ := u90.aluG hc fsq_at_13c (off' := 0x140) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv91
  obtain ⟨n92, v92, d92, hv92, u92⟩ := u91.aluG hc fsq_at_140 (off' := 0x144) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv92
  obtain ⟨n93, v93, d93, hv93, u93⟩ := u92.aluG hc fsq_at_144 (off' := 0x148) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv93
  obtain ⟨n94, v94, d94, hv94, u94⟩ := u93.aluG hc fsq_at_148 (off' := 0x14A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv94
  obtain ⟨n95, v95, d95, hv95, u95⟩ := u94.aluG hc fsq_at_14a (off' := 0x14E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv95
  obtain ⟨n96, v96, d96, hv96, u96⟩ := u95.aluG hc fsq_at_14e (off' := 0x150) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv96
  obtain ⟨n97, d97, u97⟩ := u96.swG hc fsq_at_150 (off' := 0x154) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 0) (by decide)) (a := zo + 0x0) (v := v59)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M97, hM97⟩ : ∃ M', memStore32 Mi (zo + 0x0) v59 = M' := ⟨_, rfl⟩
  rw [hM97] at u97
  have hc97 : CodeIn M97 B feSquareInnerCode := by rw [← hM97]; exact hc.store32 (frm_sep' sZC (by decide))
  have fr97 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M97 x = M0 x := fun x hxF hxZ => by
    rw [← hM97, memStore32_get_sep (frm_sep' hxZ (by decide)), fr x hxF hxZ]
  obtain ⟨n98, d98, u98⟩ := u97.swG hc97 fsq_at_154 (off' := 0x158) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 4) (by decide)) (a := zo + 0x4) (v := v76)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M98, hM98⟩ : ∃ M', memStore32 M97 (zo + 0x4) v76 = M' := ⟨_, rfl⟩
  rw [hM98] at u98
  have hc98 : CodeIn M98 B feSquareInnerCode := by rw [← hM98]; exact hc97.store32 (frm_sep' sZC (by decide))
  have fr98 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M98 x = M0 x := fun x hxF hxZ => by
    rw [← hM98, memStore32_get_sep (frm_sep' hxZ (by decide)), fr97 x hxF hxZ]
  obtain ⟨n99, v99, d99, hv99, u99⟩ := u98.aluG hc98 fsq_at_158 (off' := 0x15A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv99
  obtain ⟨n100, v100, d100, hv100, u100⟩ := u99.aluG hc98 fsq_at_15a (off' := 0x15E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv100
  obtain ⟨n101, v101, d101, hv101, u101⟩ := u100.aluG hc98 fsq_at_15e (off' := 0x162) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv101
  obtain ⟨n102, v102, d102, hv102, u102⟩ := u101.aluG hc98 fsq_at_162 (off' := 0x166) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv102
  obtain ⟨n103, v103, d103, hv103, u103⟩ := u102.aluG hc98 fsq_at_166 (off' := 0x16A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv103
  obtain ⟨n104, v104, d104, hv104, u104⟩ := u103.aluG hc98 fsq_at_16a (off' := 0x16C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv104
  obtain ⟨n105, v105, d105, hv105, u105⟩ := u104.aluG hc98 fsq_at_16c (off' := 0x16E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv105
  obtain ⟨n106, v106, d106, hv106, u106⟩ := u105.aluG hc98 fsq_at_16e (off' := 0x172) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv106
  obtain ⟨n107, d107, u107⟩ := u106.swG hc98 fsq_at_172 (off' := 0x176) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 8) (by decide)) (a := zo + 0x8) (v := v89)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M107, hM107⟩ : ∃ M', memStore32 M98 (zo + 0x8) v89 = M' := ⟨_, rfl⟩
  rw [hM107] at u107
  have hc107 : CodeIn M107 B feSquareInnerCode := by rw [← hM107]; exact hc98.store32 (frm_sep' sZC (by decide))
  have fr107 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M107 x = M0 x := fun x hxF hxZ => by
    rw [← hM107, memStore32_get_sep (frm_sep' hxZ (by decide)), fr98 x hxF hxZ]
  obtain ⟨n108, d108, u108⟩ := u107.swG hc107 fsq_at_176 (off' := 0x17A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 12) (by decide)) (a := zo + 0xC) (v := v99)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M108, hM108⟩ : ∃ M', memStore32 M107 (zo + 0xC) v99 = M' := ⟨_, rfl⟩
  rw [hM108] at u108
  have hc108 : CodeIn M108 B feSquareInnerCode := by rw [← hM108]; exact hc107.store32 (frm_sep' sZC (by decide))
  have fr108 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M108 x = M0 x := fun x hxF hxZ => by
    rw [← hM108, memStore32_get_sep (frm_sep' hxZ (by decide)), fr107 x hxF hxZ]
  obtain ⟨n109, v109, d109, hv109, u109⟩ := u108.aluG hc108 fsq_at_17a (off' := 0x17C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv109
  obtain ⟨n110, v110, d110, hv110, u110⟩ := u109.aluG hc108 fsq_at_17c (off' := 0x180) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv110
  obtain ⟨n111, v111, d111, hv111, u111⟩ := u110.aluG hc108 fsq_at_180 (off' := 0x184) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv111
  obtain ⟨n112, v112, d112, hv112, u112⟩ := u111.aluG hc108 fsq_at_184 (off' := 0x188) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv112
  obtain ⟨n113, v113, d113, hv113, u113⟩ := u112.aluG hc108 fsq_at_188 (off' := 0x18A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv113
  obtain ⟨n114, v114, d114, hv114, u114⟩ := u113.aluG hc108 fsq_at_18a (off' := 0x18C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv114
  obtain ⟨n115, v115, d115, hv115, u115⟩ := u114.aluG hc108 fsq_at_18c (off' := 0x190) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv115
  obtain ⟨n116, v116, d116, hv116, u116⟩ := u115.aluG hc108 fsq_at_190 (off' := 0x194) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv116
  obtain ⟨n117, d117, u117⟩ := u116.aluE hc108 fsq_at_194 (off' := 0x196) (by decide) (v := v30)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n118, v118, d118, hv118, u118⟩ := u117.aluG hc108 fsq_at_196 (off' := 0x198) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv118
  obtain ⟨n119, v119, d119, hv119, u119⟩ := u118.aluImmG hc108 fsq_at_198 (off' := 0x19A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv119
  have qo1 : reg n119 ra = v83 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n119 sp = F := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n119 (3 : Fin 32) = G3 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n119 (4 : Fin 32) = G4 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n119 (5 : Fin 32) = v48 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n119 (6 : Fin 32) = zo := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n119 (7 : Fin 32) = v76 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n119 (8 : Fin 32) = v109 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n119 (9 : Fin 32) = v112 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n119 a0 = v110 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n119 a1 = v119 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n119 a2 = v115 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n119 a3 = v113 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n119 a4 = v111 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n119 a5 = v116 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n119 a6 = v85 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n119 a7 = v105 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n119 (18 : Fin 32) = v9 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n119 (19 : Fin 32) = v17 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n119 (20 : Fin 32) = v16 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n119 (21 : Fin 32) = v59 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n119 (22 : Fin 32) = v10 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n119 (23 : Fin 32) = v18 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n119 (24 : Fin 32) = v21 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n119 (25 : Fin 32) = v91 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n119 (26 : Fin 32) = v12 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n119 (27 : Fin 32) = v30 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n119 (28 : Fin 32) = v30 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n119 (29 : Fin 32) = v6 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n119 (30 : Fin 32) = v64 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n119 (31 : Fin 32) = v19 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so8 : memLoad32 M108 (F + 0x8) = v3 := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x8) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 8) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x8) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 8) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x8) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 8) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x8) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 8) (l := 4) (by decide)), sl8]
  have soC : memLoad32 M108 (F + 0xC) = v4 := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0xC) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 12) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0xC) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 12) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0xC) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 12) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0xC) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 12) (l := 4) (by decide)), slC]
  have so10 : memLoad32 M108 (F + 0x10) = v28 := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x10) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 16) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x10) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 16) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x10) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 16) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x10) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 16) (l := 4) (by decide)), sl10]
  have so14 : memLoad32 M108 (F + 0x14) = v13 := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x14) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 20) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x14) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 20) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x14) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 20) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x14) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 20) (l := 4) (by decide)), sl14]
  have so18 : memLoad32 M108 (F + 0x18) = v1 := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), sl18]
  have so1C : memLoad32 M108 (F + 0x1C) = memLoad32 M0 (F + 0x1C) := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), sl1C]
  have so20 : memLoad32 M108 (F + 0x20) = memLoad32 M0 (F + 0x20) := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), sl20]
  have so24 : memLoad32 M108 (F + 0x24) = memLoad32 M0 (F + 0x24) := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), sl24]
  have so28 : memLoad32 M108 (F + 0x28) = memLoad32 M0 (F + 0x28) := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), sl28]
  have so2C : memLoad32 M108 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), sl2C]
  have so30 : memLoad32 M108 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), sl30]
  have so34 : memLoad32 M108 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), sl34]
  have so38 : memLoad32 M108 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), sl38]
  have so3C : memLoad32 M108 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), sl3C]
  have so40 : memLoad32 M108 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), sl40]
  have so44 : memLoad32 M108 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), sl44]
  have so48 : memLoad32 M108 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), sl48]
  have so4C : memLoad32 M108 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 12) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 8) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 4) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM97, memLoad32_store32_sep (show Sep (zo + 0x0) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 0) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), sl4C]
  have sozo0 : memLoad32 M108 (zo + 0x0) = v59 := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (zo + 0x0) 4 from sep_offsets zo (c := 12) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (zo + 0x0) 4 from sep_offsets zo (c := 8) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM98, memLoad32_store32_sep (show Sep (zo + 0x4) 4 (zo + 0x0) 4 from sep_offsets zo (c := 4) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM97, memLoad32_store32_same]
  have sozo4 : memLoad32 M108 (zo + 0x4) = v76 := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (zo + 0x4) 4 from sep_offsets zo (c := 12) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM107, memLoad32_store32_sep (show Sep (zo + 0x8) 4 (zo + 0x4) 4 from sep_offsets zo (c := 8) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM98, memLoad32_store32_same]
  have sozo8 : memLoad32 M108 (zo + 0x8) = v89 := by
    rw [← hM108, memLoad32_store32_sep (show Sep (zo + 0xC) 4 (zo + 0x8) 4 from sep_offsets zo (c := 12) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM107, memLoad32_store32_same]
  have sozoC : memLoad32 M108 (zo + 0xC) = v99 := by
    rw [← hM108, memLoad32_store32_same]
  exact ⟨n119, M108, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v99, v100, v101, v102, v103, v104, v105, v106, v109, v110, v111, v112, v113, v114, v115, v116, v118, v119, (.cons d80 (.cons d81 (.cons d82 (.cons d83 (.cons d84 (.cons d85 (.cons d86 (.cons d87 (.cons d88 (.cons d89 (.cons d90 (.cons d91 (.cons d92 (.cons d93 (.cons d94 (.cons d95 (.cons d96 (.cons d97 (.cons d98 (.cons d99 (.cons d100 (.cons d101 (.cons d102 (.cons d103 (.cons d104 (.cons d105 (.cons d106 (.cons d107 (.cons d108 (.cons d109 (.cons d110 (.cons d111 (.cons d112 (.cons d113 (.cons d114 (.cons d115 (.cons d116 (.cons d117 (.cons d118 (.single d119)))))))))))))))))))))))))))))))))))))))), u119.self, hc108, fr108, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so8, soC, so10, so14, so18, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, sozo0, sozo4, sozo8, sozoC, hv80, hv81, hv82, hv83, hv84, hv85, hv86, hv87, hv88, hv89, hv90, hv91, hv92, hv93, hv94, hv95, hv96, hv99, hv100, hv101, hv102, hv103, hv104, hv105, hv106, hv109, hv110, hv111, hv112, hv113, hv114, hv115, hv116, hv118, hv119⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem fsq_g3 {M0 Mi : Word → BitVec 8} {B F zo xp G3 G4 : Word} {n : Machine} {v1 v3 v4 v6 v9 v10 v12 v13 v16 v17 v18 v19 v21 v28 v30 v48 v59 v64 v76 v83 v85 v89 v91 v99 v105 v109 v110 v111 v112 v113 v115 v116 v119 : Word}
    (s : St Mi B n 0x19A (reg n)) (hc : CodeIn Mi B feSquareInnerCode)
    (fr : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hZ : zo.toNat % 4 = 0) (hx : xp.toNat % 4 = 0)
    (sFC : Sep F 0x50 B feSquareInnerCode.length) (sZC : Sep zo 0x50 B feSquareInnerCode.length)
    (sXF : Sep xp 40 F 0x50) (sXZ : Sep xp 40 zo 0x50) (sFZ : Sep F 0x50 zo 0x50)
    (q1 : reg n ra = v83)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v48)
    (q6 : reg n (6 : Fin 32) = zo)
    (q7 : reg n (7 : Fin 32) = v76)
    (q8 : reg n (8 : Fin 32) = v109)
    (q9 : reg n (9 : Fin 32) = v112)
    (q10 : reg n a0 = v110)
    (q11 : reg n a1 = v119)
    (q12 : reg n a2 = v115)
    (q13 : reg n a3 = v113)
    (q14 : reg n a4 = v111)
    (q15 : reg n a5 = v116)
    (q16 : reg n a6 = v85)
    (q17 : reg n a7 = v105)
    (q18 : reg n (18 : Fin 32) = v9)
    (q19 : reg n (19 : Fin 32) = v17)
    (q20 : reg n (20 : Fin 32) = v16)
    (q21 : reg n (21 : Fin 32) = v59)
    (q22 : reg n (22 : Fin 32) = v10)
    (q23 : reg n (23 : Fin 32) = v18)
    (q24 : reg n (24 : Fin 32) = v21)
    (q25 : reg n (25 : Fin 32) = v91)
    (q26 : reg n (26 : Fin 32) = v12)
    (q27 : reg n (27 : Fin 32) = v30)
    (q28 : reg n (28 : Fin 32) = v30)
    (q29 : reg n (29 : Fin 32) = v6)
    (q30 : reg n (30 : Fin 32) = v64)
    (q31 : reg n (31 : Fin 32) = v19)
    (sl8 : memLoad32 Mi (F + 0x8) = v3)
    (slC : memLoad32 Mi (F + 0xC) = v4)
    (sl10 : memLoad32 Mi (F + 0x10) = v28)
    (sl14 : memLoad32 Mi (F + 0x14) = v13)
    (sl18 : memLoad32 Mi (F + 0x18) = v1)
    (sl1C : memLoad32 Mi (F + 0x1C) = memLoad32 M0 (F + 0x1C))
    (sl20 : memLoad32 Mi (F + 0x20) = memLoad32 M0 (F + 0x20))
    (sl24 : memLoad32 Mi (F + 0x24) = memLoad32 M0 (F + 0x24))
    (sl28 : memLoad32 Mi (F + 0x28) = memLoad32 M0 (F + 0x28))
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    (slzo0 : memLoad32 Mi (zo + 0x0) = v59)
    (slzo4 : memLoad32 Mi (zo + 0x4) = v76)
    (slzo8 : memLoad32 Mi (zo + 0x8) = v89)
    (slzoC : memLoad32 Mi (zo + 0xC) = v99)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v148 v149 v150 v151 v152 v153 v154 v155 v156 v157 v158 v159 : Word),
      Steps n n' ∧
      St M' B n' 0x216 (reg n') ∧
      CodeIn M' B feSquareInnerCode ∧
      (∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M' x = M0 x) ∧
      reg n' ra = v83 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v48 ∧
      reg n' (6 : Fin 32) = zo ∧
      reg n' (7 : Fin 32) = v153 ∧
      reg n' (8 : Fin 32) = v152 ∧
      reg n' (9 : Fin 32) = v146 ∧
      reg n' a0 = v147 ∧
      reg n' a1 = v159 ∧
      reg n' a2 = v149 ∧
      reg n' a3 = v158 ∧
      reg n' a4 = v154 ∧
      reg n' a5 = v144 ∧
      reg n' a6 = v151 ∧
      reg n' a7 = v132 ∧
      reg n' (18 : Fin 32) = v9 ∧
      reg n' (19 : Fin 32) = v17 ∧
      reg n' (20 : Fin 32) = v16 ∧
      reg n' (21 : Fin 32) = v134 ∧
      reg n' (22 : Fin 32) = v10 ∧
      reg n' (23 : Fin 32) = v18 ∧
      reg n' (24 : Fin 32) = v21 ∧
      reg n' (25 : Fin 32) = v137 ∧
      reg n' (26 : Fin 32) = v12 ∧
      reg n' (27 : Fin 32) = v30 ∧
      reg n' (28 : Fin 32) = v30 ∧
      reg n' (29 : Fin 32) = v6 ∧
      reg n' (30 : Fin 32) = v64 ∧
      reg n' (31 : Fin 32) = v19 ∧
      memLoad32 M' (F + 0x8) = v3 ∧
      memLoad32 M' (F + 0xC) = v4 ∧
      memLoad32 M' (F + 0x10) = v28 ∧
      memLoad32 M' (F + 0x14) = v13 ∧
      memLoad32 M' (F + 0x18) = v1 ∧
      memLoad32 M' (F + 0x1C) = memLoad32 M0 (F + 0x1C) ∧
      memLoad32 M' (F + 0x20) = memLoad32 M0 (F + 0x20) ∧
      memLoad32 M' (F + 0x24) = memLoad32 M0 (F + 0x24) ∧
      memLoad32 M' (F + 0x28) = memLoad32 M0 (F + 0x28) ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (zo + 0x0) = v59 ∧
      memLoad32 M' (zo + 0x4) = v76 ∧
      memLoad32 M' (zo + 0x8) = v89 ∧
      memLoad32 M' (zo + 0xC) = v99 ∧
      aluEval .srl v113 0x1F = v120 ∧
      aluEval .or v119 v120 = v121 ∧
      aluEval .sll v113 0x1 = v122 ∧
      aluEval .add v111 v105 = v123 ∧
      aluEval .add v110 v109 = v124 ∧
      aluEval .sltu v123 v105 = v125 ∧
      aluEval .add v124 v112 = v126 ∧
      aluEval .mul v9 v48 = v127 ∧
      aluEval .mul v18 v16 = v128 ∧
      aluEval .add v126 v125 = v129 ∧
      aluEval .add v116 v123 = v130 ∧
      aluEval .sltu v130 v123 = v131 ∧
      aluEval .add v130 v122 = v132 ∧
      aluEval .mulhu v9 v48 = v133 ∧
      aluEval .mulhu v18 v16 = v134 ∧
      aluEval .add v129 v131 = v135 ∧
      aluEval .sltu v132 v130 = v136 ∧
      aluEval .mulhu v21 v64 = v137 ∧
      aluEval .mul v21 v64 = v138 ∧
      aluEval .add v135 v136 = v139 ∧
      aluEval .add v128 v127 = v140 ∧
      aluEval .mul v10 v17 = v141 ∧
      aluEval .mul v12 v6 = v142 ∧
      aluEval .mulhu v10 v17 = v143 ∧
      aluEval .mulhu v12 v6 = v144 ∧
      aluEval .add v133 v134 = v145 ∧
      aluEval .sltu v140 v127 = v146 ∧
      aluEval .add v139 v121 = v147 ∧
      aluEval .add v145 v146 = v148 ∧
      aluEval .add v138 v140 = v149 ∧
      aluEval .add v148 v137 = v150 ∧
      aluEval .sll v6 0x1 = v151 ∧
      aluEval .sltu v149 v140 = v152 ∧
      aluEval .add v150 v152 = v153 ∧
      aluEval .add v142 v141 = v154 ∧
      aluEval .add v143 v144 = v155 ∧
      aluEval .sltu v154 v141 = v156 ∧
      aluEval .add v155 v156 = v157 ∧
      aluEval .sll v154 0x1 = v158 ∧
      aluEval .sll v157 0x1 = v159 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n120, v120, d120, hv120, u120⟩ := s.aluImmG hc fsq_at_19a (off' := 0x19E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv120
  obtain ⟨n121, v121, d121, hv121, u121⟩ := u120.aluG hc fsq_at_19e (off' := 0x1A2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv121
  obtain ⟨n122, v122, d122, hv122, u122⟩ := u121.aluImmG hc fsq_at_1a2 (off' := 0x1A6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv122
  obtain ⟨n123, v123, d123, hv123, u123⟩ := u122.aluG hc fsq_at_1a6 (off' := 0x1A8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv123
  obtain ⟨n124, v124, d124, hv124, u124⟩ := u123.aluG hc fsq_at_1a8 (off' := 0x1AA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv124
  obtain ⟨n125, v125, d125, hv125, u125⟩ := u124.aluG hc fsq_at_1aa (off' := 0x1AE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv125
  obtain ⟨n126, v126, d126, hv126, u126⟩ := u125.aluG hc fsq_at_1ae (off' := 0x1B0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv126
  obtain ⟨n127, v127, d127, hv127, u127⟩ := u126.aluG hc fsq_at_1b0 (off' := 0x1B4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv127
  obtain ⟨n128, v128, d128, hv128, u128⟩ := u127.aluG hc fsq_at_1b4 (off' := 0x1B8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv128
  obtain ⟨n129, v129, d129, hv129, u129⟩ := u128.aluG hc fsq_at_1b8 (off' := 0x1BA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv129
  obtain ⟨n130, v130, d130, hv130, u130⟩ := u129.aluG hc fsq_at_1ba (off' := 0x1BC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv130
  obtain ⟨n131, v131, d131, hv131, u131⟩ := u130.aluG hc fsq_at_1bc (off' := 0x1C0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv131
  obtain ⟨n132, v132, d132, hv132, u132⟩ := u131.aluG hc fsq_at_1c0 (off' := 0x1C4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv132
  obtain ⟨n133, v133, d133, hv133, u133⟩ := u132.aluG hc fsq_at_1c4 (off' := 0x1C8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv133
  obtain ⟨n134, v134, d134, hv134, u134⟩ := u133.aluG hc fsq_at_1c8 (off' := 0x1CC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv134
  obtain ⟨n135, v135, d135, hv135, u135⟩ := u134.aluG hc fsq_at_1cc (off' := 0x1CE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv135
  obtain ⟨n136, v136, d136, hv136, u136⟩ := u135.aluG hc fsq_at_1ce (off' := 0x1D2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv136
  obtain ⟨n137, v137, d137, hv137, u137⟩ := u136.aluG hc fsq_at_1d2 (off' := 0x1D6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv137
  obtain ⟨n138, v138, d138, hv138, u138⟩ := u137.aluG hc fsq_at_1d6 (off' := 0x1DA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv138
  obtain ⟨n139, v139, d139, hv139, u139⟩ := u138.aluG hc fsq_at_1da (off' := 0x1DC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv139
  obtain ⟨n140, v140, d140, hv140, u140⟩ := u139.aluG hc fsq_at_1dc (off' := 0x1DE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv140
  obtain ⟨n141, v141, d141, hv141, u141⟩ := u140.aluG hc fsq_at_1de (off' := 0x1E2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv141
  obtain ⟨n142, v142, d142, hv142, u142⟩ := u141.aluG hc fsq_at_1e2 (off' := 0x1E6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv142
  obtain ⟨n143, v143, d143, hv143, u143⟩ := u142.aluG hc fsq_at_1e6 (off' := 0x1EA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv143
  obtain ⟨n144, v144, d144, hv144, u144⟩ := u143.aluG hc fsq_at_1ea (off' := 0x1EE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv144
  obtain ⟨n145, v145, d145, hv145, u145⟩ := u144.aluG hc fsq_at_1ee (off' := 0x1F0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv145
  obtain ⟨n146, v146, d146, hv146, u146⟩ := u145.aluG hc fsq_at_1f0 (off' := 0x1F4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv146
  obtain ⟨n147, v147, d147, hv147, u147⟩ := u146.aluG hc fsq_at_1f4 (off' := 0x1F6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv147
  obtain ⟨n148, v148, d148, hv148, u148⟩ := u147.aluG hc fsq_at_1f6 (off' := 0x1F8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv148
  obtain ⟨n149, v149, d149, hv149, u149⟩ := u148.aluG hc fsq_at_1f8 (off' := 0x1FA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv149
  obtain ⟨n150, v150, d150, hv150, u150⟩ := u149.aluG hc fsq_at_1fa (off' := 0x1FC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv150
  obtain ⟨n151, v151, d151, hv151, u151⟩ := u150.aluImmG hc fsq_at_1fc (off' := 0x200) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv151
  obtain ⟨n152, v152, d152, hv152, u152⟩ := u151.aluG hc fsq_at_200 (off' := 0x204) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv152
  obtain ⟨n153, v153, d153, hv153, u153⟩ := u152.aluG hc fsq_at_204 (off' := 0x206) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv153
  obtain ⟨n154, v154, d154, hv154, u154⟩ := u153.aluG hc fsq_at_206 (off' := 0x208) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv154
  obtain ⟨n155, v155, d155, hv155, u155⟩ := u154.aluG hc fsq_at_208 (off' := 0x20A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv155
  obtain ⟨n156, v156, d156, hv156, u156⟩ := u155.aluG hc fsq_at_20a (off' := 0x20E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv156
  obtain ⟨n157, v157, d157, hv157, u157⟩ := u156.aluG hc fsq_at_20e (off' := 0x210) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv157
  obtain ⟨n158, v158, d158, hv158, u158⟩ := u157.aluImmG hc fsq_at_210 (off' := 0x214) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv158
  obtain ⟨n159, v159, d159, hv159, u159⟩ := u158.aluImmG hc fsq_at_214 (off' := 0x216) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv159
  have qo1 : reg n159 ra = v83 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n159 sp = F := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n159 (3 : Fin 32) = G3 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n159 (4 : Fin 32) = G4 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n159 (5 : Fin 32) = v48 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n159 (6 : Fin 32) = zo := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n159 (7 : Fin 32) = v153 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n159 (8 : Fin 32) = v152 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n159 (9 : Fin 32) = v146 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n159 a0 = v147 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n159 a1 = v159 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n159 a2 = v149 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n159 a3 = v158 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n159 a4 = v154 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n159 a5 = v144 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n159 a6 = v151 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n159 a7 = v132 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n159 (18 : Fin 32) = v9 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n159 (19 : Fin 32) = v17 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n159 (20 : Fin 32) = v16 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n159 (21 : Fin 32) = v134 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n159 (22 : Fin 32) = v10 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n159 (23 : Fin 32) = v18 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n159 (24 : Fin 32) = v21 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n159 (25 : Fin 32) = v137 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n159 (26 : Fin 32) = v12 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n159 (27 : Fin 32) = v30 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n159 (28 : Fin 32) = v30 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n159 (29 : Fin 32) = v6 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n159 (30 : Fin 32) = v64 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n159 (31 : Fin 32) = v19 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so8 : memLoad32 Mi (F + 0x8) = v3 := by
    rw [sl8]
  have soC : memLoad32 Mi (F + 0xC) = v4 := by
    rw [slC]
  have so10 : memLoad32 Mi (F + 0x10) = v28 := by
    rw [sl10]
  have so14 : memLoad32 Mi (F + 0x14) = v13 := by
    rw [sl14]
  have so18 : memLoad32 Mi (F + 0x18) = v1 := by
    rw [sl18]
  have so1C : memLoad32 Mi (F + 0x1C) = memLoad32 M0 (F + 0x1C) := by
    rw [sl1C]
  have so20 : memLoad32 Mi (F + 0x20) = memLoad32 M0 (F + 0x20) := by
    rw [sl20]
  have so24 : memLoad32 Mi (F + 0x24) = memLoad32 M0 (F + 0x24) := by
    rw [sl24]
  have so28 : memLoad32 Mi (F + 0x28) = memLoad32 M0 (F + 0x28) := by
    rw [sl28]
  have so2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [sl2C]
  have so30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [sl30]
  have so34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [sl34]
  have so38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [sl38]
  have so3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [sl3C]
  have so40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [sl40]
  have so44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [sl44]
  have so48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [sl48]
  have so4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [sl4C]
  have sozo0 : memLoad32 Mi (zo + 0x0) = v59 := by
    rw [slzo0]
  have sozo4 : memLoad32 Mi (zo + 0x4) = v76 := by
    rw [slzo4]
  have sozo8 : memLoad32 Mi (zo + 0x8) = v89 := by
    rw [slzo8]
  have sozoC : memLoad32 Mi (zo + 0xC) = v99 := by
    rw [slzoC]
  exact ⟨n159, Mi, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, (.cons d120 (.cons d121 (.cons d122 (.cons d123 (.cons d124 (.cons d125 (.cons d126 (.cons d127 (.cons d128 (.cons d129 (.cons d130 (.cons d131 (.cons d132 (.cons d133 (.cons d134 (.cons d135 (.cons d136 (.cons d137 (.cons d138 (.cons d139 (.cons d140 (.cons d141 (.cons d142 (.cons d143 (.cons d144 (.cons d145 (.cons d146 (.cons d147 (.cons d148 (.cons d149 (.cons d150 (.cons d151 (.cons d152 (.cons d153 (.cons d154 (.cons d155 (.cons d156 (.cons d157 (.cons d158 (.single d159)))))))))))))))))))))))))))))))))))))))), u159.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so8, soC, so10, so14, so18, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, sozo0, sozo4, sozo8, sozoC, hv120, hv121, hv122, hv123, hv124, hv125, hv126, hv127, hv128, hv129, hv130, hv131, hv132, hv133, hv134, hv135, hv136, hv137, hv138, hv139, hv140, hv141, hv142, hv143, hv144, hv145, hv146, hv147, hv148, hv149, hv150, hv151, hv152, hv153, hv154, hv155, hv156, hv157, hv158, hv159⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem fsq_g4 {M0 Mi : Word → BitVec 8} {B F zo xp G3 G4 : Word} {n : Machine} {v1 v3 v4 v6 v9 v10 v12 v13 v16 v17 v18 v19 v21 v28 v30 v48 v59 v64 v76 v83 v89 v99 v132 v134 v137 v144 v146 v147 v149 v151 v152 v153 v154 v158 v159 : Word}
    (s : St Mi B n 0x216 (reg n)) (hc : CodeIn Mi B feSquareInnerCode)
    (fr : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hZ : zo.toNat % 4 = 0) (hx : xp.toNat % 4 = 0)
    (sFC : Sep F 0x50 B feSquareInnerCode.length) (sZC : Sep zo 0x50 B feSquareInnerCode.length)
    (sXF : Sep xp 40 F 0x50) (sXZ : Sep xp 40 zo 0x50) (sFZ : Sep F 0x50 zo 0x50)
    (q1 : reg n ra = v83)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v48)
    (q6 : reg n (6 : Fin 32) = zo)
    (q7 : reg n (7 : Fin 32) = v153)
    (q8 : reg n (8 : Fin 32) = v152)
    (q9 : reg n (9 : Fin 32) = v146)
    (q10 : reg n a0 = v147)
    (q11 : reg n a1 = v159)
    (q12 : reg n a2 = v149)
    (q13 : reg n a3 = v158)
    (q14 : reg n a4 = v154)
    (q15 : reg n a5 = v144)
    (q16 : reg n a6 = v151)
    (q17 : reg n a7 = v132)
    (q18 : reg n (18 : Fin 32) = v9)
    (q19 : reg n (19 : Fin 32) = v17)
    (q20 : reg n (20 : Fin 32) = v16)
    (q21 : reg n (21 : Fin 32) = v134)
    (q22 : reg n (22 : Fin 32) = v10)
    (q23 : reg n (23 : Fin 32) = v18)
    (q24 : reg n (24 : Fin 32) = v21)
    (q25 : reg n (25 : Fin 32) = v137)
    (q26 : reg n (26 : Fin 32) = v12)
    (q27 : reg n (27 : Fin 32) = v30)
    (q28 : reg n (28 : Fin 32) = v30)
    (q29 : reg n (29 : Fin 32) = v6)
    (q30 : reg n (30 : Fin 32) = v64)
    (q31 : reg n (31 : Fin 32) = v19)
    (sl8 : memLoad32 Mi (F + 0x8) = v3)
    (slC : memLoad32 Mi (F + 0xC) = v4)
    (sl10 : memLoad32 Mi (F + 0x10) = v28)
    (sl14 : memLoad32 Mi (F + 0x14) = v13)
    (sl18 : memLoad32 Mi (F + 0x18) = v1)
    (sl1C : memLoad32 Mi (F + 0x1C) = memLoad32 M0 (F + 0x1C))
    (sl20 : memLoad32 Mi (F + 0x20) = memLoad32 M0 (F + 0x20))
    (sl24 : memLoad32 Mi (F + 0x24) = memLoad32 M0 (F + 0x24))
    (sl28 : memLoad32 Mi (F + 0x28) = memLoad32 M0 (F + 0x28))
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    (slzo0 : memLoad32 Mi (zo + 0x0) = v59)
    (slzo4 : memLoad32 Mi (zo + 0x4) = v76)
    (slzo8 : memLoad32 Mi (zo + 0x8) = v89)
    (slzoC : memLoad32 Mi (zo + 0xC) = v99)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v160 v161 v162 v163 v164 v165 v166 v167 v169 v170 v176 v177 v178 v179 v180 v181 v182 v183 v184 v185 v186 v187 v188 v189 v190 v191 v192 v193 v194 v195 v196 v197 v198 v199 : Word),
      Steps n n' ∧
      St M' B n' 0x294 (reg n') ∧
      CodeIn M' B feSquareInnerCode ∧
      (∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M' x = M0 x) ∧
      reg n' ra = v83 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v48 ∧
      reg n' (6 : Fin 32) = zo ∧
      reg n' (7 : Fin 32) = v195 ∧
      reg n' (8 : Fin 32) = v185 ∧
      reg n' (9 : Fin 32) = v179 ∧
      reg n' a0 = v199 ∧
      reg n' a1 = v198 ∧
      reg n' a2 = v191 ∧
      reg n' a3 = v189 ∧
      reg n' a4 = v188 ∧
      reg n' a5 = v193 ∧
      reg n' a6 = v190 ∧
      reg n' a7 = v176 ∧
      reg n' (18 : Fin 32) = v9 ∧
      reg n' (19 : Fin 32) = v17 ∧
      reg n' (20 : Fin 32) = v16 ∧
      reg n' (21 : Fin 32) = v178 ∧
      reg n' (22 : Fin 32) = v10 ∧
      reg n' (23 : Fin 32) = v18 ∧
      reg n' (24 : Fin 32) = v21 ∧
      reg n' (25 : Fin 32) = v137 ∧
      reg n' (26 : Fin 32) = v4 ∧
      reg n' (27 : Fin 32) = v30 ∧
      reg n' (28 : Fin 32) = v30 ∧
      reg n' (29 : Fin 32) = v6 ∧
      reg n' (30 : Fin 32) = v64 ∧
      reg n' (31 : Fin 32) = v19 ∧
      memLoad32 M' (F + 0x8) = v3 ∧
      memLoad32 M' (F + 0x10) = v28 ∧
      memLoad32 M' (F + 0x14) = v13 ∧
      memLoad32 M' (F + 0x18) = v1 ∧
      memLoad32 M' (F + 0x1C) = memLoad32 M0 (F + 0x1C) ∧
      memLoad32 M' (F + 0x20) = memLoad32 M0 (F + 0x20) ∧
      memLoad32 M' (F + 0x24) = memLoad32 M0 (F + 0x24) ∧
      memLoad32 M' (F + 0x28) = memLoad32 M0 (F + 0x28) ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (zo + 0x0) = v59 ∧
      memLoad32 M' (zo + 0x4) = v76 ∧
      memLoad32 M' (zo + 0x8) = v89 ∧
      memLoad32 M' (zo + 0xC) = v99 ∧
      memLoad32 M' (zo + 0x10) = v132 ∧
      memLoad32 M' (zo + 0x14) = v147 ∧
      memLoad32 M' (zo + 0x18) = v160 ∧
      memLoad32 M' (zo + 0x1C) = v165 ∧
      aluEval .add v158 v149 = v160 ∧
      aluEval .srl v154 0x1F = v161 ∧
      aluEval .sltu v160 v149 = v162 ∧
      aluEval .or v159 v161 = v163 ∧
      aluEval .add v162 v153 = v164 ∧
      aluEval .add v163 v164 = v165 ∧
      aluEval .mul v10 v64 = v166 ∧
      aluEval .mulhu v10 v64 = v167 ∧
      aluEval .mul v12 v4 = v169 ∧
      aluEval .mulhu v12 v4 = v170 ∧
      aluEval .mulhu v17 v48 = v176 ∧
      aluEval .mul v17 v48 = v177 ∧
      aluEval .mulhu v19 v18 = v178 ∧
      aluEval .mul v19 v18 = v179 ∧
      aluEval .mul v16 v16 = v180 ∧
      aluEval .mulhu v16 v16 = v181 ∧
      aluEval .add v169 v166 = v182 ∧
      aluEval .add v167 v170 = v183 ∧
      aluEval .sltu v182 v166 = v184 ∧
      aluEval .mul v21 v151 = v185 ∧
      aluEval .add v184 v183 = v186 ∧
      aluEval .sll v186 0x1 = v187 ∧
      aluEval .srl v182 0x1F = v188 ∧
      aluEval .mulhu v21 v151 = v189 ∧
      aluEval .or v187 v188 = v190 ∧
      aluEval .sll v182 0x1 = v191 ∧
      aluEval .add v180 v179 = v192 ∧
      aluEval .sltu v192 v179 = v193 ∧
      aluEval .add v181 v178 = v194 ∧
      aluEval .add v177 v192 = v195 ∧
      aluEval .add v194 v176 = v196 ∧
      aluEval .sltu v195 v192 = v197 ∧
      aluEval .add v196 v193 = v198 ∧
      aluEval .add v197 v198 = v199 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n160, v160, d160, hv160, u160⟩ := s.aluG hc fsq_at_216 (off' := 0x218) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv160
  obtain ⟨n161, v161, d161, hv161, u161⟩ := u160.aluImmG hc fsq_at_218 (off' := 0x21A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv161
  obtain ⟨n162, v162, d162, hv162, u162⟩ := u161.aluG hc fsq_at_21a (off' := 0x21E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv162
  obtain ⟨n163, v163, d163, hv163, u163⟩ := u162.aluG hc fsq_at_21e (off' := 0x220) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv163
  obtain ⟨n164, v164, d164, hv164, u164⟩ := u163.aluG hc fsq_at_220 (off' := 0x222) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv164
  obtain ⟨n165, v165, d165, hv165, u165⟩ := u164.aluG hc fsq_at_222 (off' := 0x224) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv165
  obtain ⟨n166, v166, d166, hv166, u166⟩ := u165.aluG hc fsq_at_224 (off' := 0x228) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv166
  obtain ⟨n167, v167, d167, hv167, u167⟩ := u166.aluG hc fsq_at_228 (off' := 0x22C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv167
  obtain ⟨n168, d168, u168⟩ := u167.lwE hc fsq_at_22c (off' := 0x22E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 12) (by decide)) (v := v4)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slC])
  obtain ⟨n169, v169, d169, hv169, u169⟩ := u168.aluG hc fsq_at_22e (off' := 0x232) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv169
  obtain ⟨n170, v170, d170, hv170, u170⟩ := u169.aluG hc fsq_at_232 (off' := 0x236) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv170
  obtain ⟨n171, d171, u171⟩ := u170.aluE hc fsq_at_236 (off' := 0x238) (by decide) (v := v4)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n172, d172, u172⟩ := u171.swG hc fsq_at_238 (off' := 0x23C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 16) (by decide)) (a := zo + 0x10) (v := v132)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M172, hM172⟩ : ∃ M', memStore32 Mi (zo + 0x10) v132 = M' := ⟨_, rfl⟩
  rw [hM172] at u172
  have hc172 : CodeIn M172 B feSquareInnerCode := by rw [← hM172]; exact hc.store32 (frm_sep' sZC (by decide))
  have fr172 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M172 x = M0 x := fun x hxF hxZ => by
    rw [← hM172, memStore32_get_sep (frm_sep' hxZ (by decide)), fr x hxF hxZ]
  obtain ⟨n173, d173, u173⟩ := u172.swG hc172 fsq_at_23c (off' := 0x240) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 20) (by decide)) (a := zo + 0x14) (v := v147)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M173, hM173⟩ : ∃ M', memStore32 M172 (zo + 0x14) v147 = M' := ⟨_, rfl⟩
  rw [hM173] at u173
  have hc173 : CodeIn M173 B feSquareInnerCode := by rw [← hM173]; exact hc172.store32 (frm_sep' sZC (by decide))
  have fr173 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M173 x = M0 x := fun x hxF hxZ => by
    rw [← hM173, memStore32_get_sep (frm_sep' hxZ (by decide)), fr172 x hxF hxZ]
  obtain ⟨n174, d174, u174⟩ := u173.swG hc173 fsq_at_240 (off' := 0x244) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 24) (by decide)) (a := zo + 0x18) (v := v160)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M174, hM174⟩ : ∃ M', memStore32 M173 (zo + 0x18) v160 = M' := ⟨_, rfl⟩
  rw [hM174] at u174
  have hc174 : CodeIn M174 B feSquareInnerCode := by rw [← hM174]; exact hc173.store32 (frm_sep' sZC (by decide))
  have fr174 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M174 x = M0 x := fun x hxF hxZ => by
    rw [← hM174, memStore32_get_sep (frm_sep' hxZ (by decide)), fr173 x hxF hxZ]
  obtain ⟨n175, d175, u175⟩ := u174.swG hc174 fsq_at_244 (off' := 0x248) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 28) (by decide)) (a := zo + 0x1C) (v := v165)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M175, hM175⟩ : ∃ M', memStore32 M174 (zo + 0x1C) v165 = M' := ⟨_, rfl⟩
  rw [hM175] at u175
  have hc175 : CodeIn M175 B feSquareInnerCode := by rw [← hM175]; exact hc174.store32 (frm_sep' sZC (by decide))
  have fr175 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M175 x = M0 x := fun x hxF hxZ => by
    rw [← hM175, memStore32_get_sep (frm_sep' hxZ (by decide)), fr174 x hxF hxZ]
  obtain ⟨n176, v176, d176, hv176, u176⟩ := u175.aluG hc175 fsq_at_248 (off' := 0x24C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv176
  obtain ⟨n177, v177, d177, hv177, u177⟩ := u176.aluG hc175 fsq_at_24c (off' := 0x250) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv177
  obtain ⟨n178, v178, d178, hv178, u178⟩ := u177.aluG hc175 fsq_at_250 (off' := 0x254) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv178
  obtain ⟨n179, v179, d179, hv179, u179⟩ := u178.aluG hc175 fsq_at_254 (off' := 0x258) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv179
  obtain ⟨n180, v180, d180, hv180, u180⟩ := u179.aluG hc175 fsq_at_258 (off' := 0x25C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv180
  obtain ⟨n181, v181, d181, hv181, u181⟩ := u180.aluG hc175 fsq_at_25c (off' := 0x260) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv181
  obtain ⟨n182, v182, d182, hv182, u182⟩ := u181.aluG hc175 fsq_at_260 (off' := 0x262) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv182
  obtain ⟨n183, v183, d183, hv183, u183⟩ := u182.aluG hc175 fsq_at_262 (off' := 0x264) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv183
  obtain ⟨n184, v184, d184, hv184, u184⟩ := u183.aluG hc175 fsq_at_264 (off' := 0x268) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv184
  obtain ⟨n185, v185, d185, hv185, u185⟩ := u184.aluG hc175 fsq_at_268 (off' := 0x26C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv185
  obtain ⟨n186, v186, d186, hv186, u186⟩ := u185.aluG hc175 fsq_at_26c (off' := 0x26E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv186
  obtain ⟨n187, v187, d187, hv187, u187⟩ := u186.aluImmG hc175 fsq_at_26e (off' := 0x270) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv187
  obtain ⟨n188, v188, d188, hv188, u188⟩ := u187.aluImmG hc175 fsq_at_270 (off' := 0x274) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv188
  obtain ⟨n189, v189, d189, hv189, u189⟩ := u188.aluG hc175 fsq_at_274 (off' := 0x278) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv189
  obtain ⟨n190, v190, d190, hv190, u190⟩ := u189.aluG hc175 fsq_at_278 (off' := 0x27C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv190
  obtain ⟨n191, v191, d191, hv191, u191⟩ := u190.aluImmG hc175 fsq_at_27c (off' := 0x280) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv191
  obtain ⟨n192, v192, d192, hv192, u192⟩ := u191.aluG hc175 fsq_at_280 (off' := 0x282) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv192
  obtain ⟨n193, v193, d193, hv193, u193⟩ := u192.aluG hc175 fsq_at_282 (off' := 0x286) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv193
  obtain ⟨n194, v194, d194, hv194, u194⟩ := u193.aluG hc175 fsq_at_286 (off' := 0x288) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv194
  obtain ⟨n195, v195, d195, hv195, u195⟩ := u194.aluG hc175 fsq_at_288 (off' := 0x28A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv195
  obtain ⟨n196, v196, d196, hv196, u196⟩ := u195.aluG hc175 fsq_at_28a (off' := 0x28C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv196
  obtain ⟨n197, v197, d197, hv197, u197⟩ := u196.aluG hc175 fsq_at_28c (off' := 0x290) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv197
  obtain ⟨n198, v198, d198, hv198, u198⟩ := u197.aluG hc175 fsq_at_290 (off' := 0x292) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv198
  obtain ⟨n199, v199, d199, hv199, u199⟩ := u198.aluG hc175 fsq_at_292 (off' := 0x294) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv199
  have qo1 : reg n199 ra = v83 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n199 sp = F := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n199 (3 : Fin 32) = G3 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n199 (4 : Fin 32) = G4 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n199 (5 : Fin 32) = v48 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n199 (6 : Fin 32) = zo := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n199 (7 : Fin 32) = v195 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n199 (8 : Fin 32) = v185 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n199 (9 : Fin 32) = v179 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n199 a0 = v199 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n199 a1 = v198 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n199 a2 = v191 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n199 a3 = v189 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n199 a4 = v188 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n199 a5 = v193 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n199 a6 = v190 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n199 a7 = v176 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n199 (18 : Fin 32) = v9 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n199 (19 : Fin 32) = v17 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n199 (20 : Fin 32) = v16 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n199 (21 : Fin 32) = v178 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n199 (22 : Fin 32) = v10 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n199 (23 : Fin 32) = v18 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n199 (24 : Fin 32) = v21 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n199 (25 : Fin 32) = v137 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n199 (26 : Fin 32) = v4 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n199 (27 : Fin 32) = v30 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n199 (28 : Fin 32) = v30 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n199 (29 : Fin 32) = v6 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n199 (30 : Fin 32) = v64 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n199 (31 : Fin 32) = v19 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so8 : memLoad32 M175 (F + 0x8) = v3 := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x8) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 8) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x8) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 8) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x8) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 8) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x8) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 8) (l := 4) (by decide)), sl8]
  have so10 : memLoad32 M175 (F + 0x10) = v28 := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x10) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 16) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x10) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 16) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x10) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 16) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x10) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 16) (l := 4) (by decide)), sl10]
  have so14 : memLoad32 M175 (F + 0x14) = v13 := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x14) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 20) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x14) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 20) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x14) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 20) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x14) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 20) (l := 4) (by decide)), sl14]
  have so18 : memLoad32 M175 (F + 0x18) = v1 := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), sl18]
  have so1C : memLoad32 M175 (F + 0x1C) = memLoad32 M0 (F + 0x1C) := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), sl1C]
  have so20 : memLoad32 M175 (F + 0x20) = memLoad32 M0 (F + 0x20) := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), sl20]
  have so24 : memLoad32 M175 (F + 0x24) = memLoad32 M0 (F + 0x24) := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), sl24]
  have so28 : memLoad32 M175 (F + 0x28) = memLoad32 M0 (F + 0x28) := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), sl28]
  have so2C : memLoad32 M175 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), sl2C]
  have so30 : memLoad32 M175 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), sl30]
  have so34 : memLoad32 M175 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), sl34]
  have so38 : memLoad32 M175 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), sl38]
  have so3C : memLoad32 M175 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), sl3C]
  have so40 : memLoad32 M175 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), sl40]
  have so44 : memLoad32 M175 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), sl44]
  have so48 : memLoad32 M175 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), sl48]
  have so4C : memLoad32 M175 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 28) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 24) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 20) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 16) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), sl4C]
  have sozo0 : memLoad32 M175 (zo + 0x0) = v59 := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (zo + 0x0) 4 from sep_offsets zo (c := 28) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (zo + 0x0) 4 from sep_offsets zo (c := 24) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (zo + 0x0) 4 from sep_offsets zo (c := 20) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (zo + 0x0) 4 from sep_offsets zo (c := 16) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), slzo0]
  have sozo4 : memLoad32 M175 (zo + 0x4) = v76 := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (zo + 0x4) 4 from sep_offsets zo (c := 28) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (zo + 0x4) 4 from sep_offsets zo (c := 24) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (zo + 0x4) 4 from sep_offsets zo (c := 20) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (zo + 0x4) 4 from sep_offsets zo (c := 16) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), slzo4]
  have sozo8 : memLoad32 M175 (zo + 0x8) = v89 := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (zo + 0x8) 4 from sep_offsets zo (c := 28) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (zo + 0x8) 4 from sep_offsets zo (c := 24) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (zo + 0x8) 4 from sep_offsets zo (c := 20) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (zo + 0x8) 4 from sep_offsets zo (c := 16) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), slzo8]
  have sozoC : memLoad32 M175 (zo + 0xC) = v99 := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (zo + 0xC) 4 from sep_offsets zo (c := 28) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (zo + 0xC) 4 from sep_offsets zo (c := 24) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (zo + 0xC) 4 from sep_offsets zo (c := 20) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (zo + 0x10) 4 (zo + 0xC) 4 from sep_offsets zo (c := 16) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slzoC]
  have sozo10 : memLoad32 M175 (zo + 0x10) = v132 := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (zo + 0x10) 4 from sep_offsets zo (c := 28) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (zo + 0x10) 4 from sep_offsets zo (c := 24) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (zo + 0x14) 4 (zo + 0x10) 4 from sep_offsets zo (c := 20) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_same]
  have sozo14 : memLoad32 M175 (zo + 0x14) = v147 := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (zo + 0x14) 4 from sep_offsets zo (c := 28) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), ← hM174, memLoad32_store32_sep (show Sep (zo + 0x18) 4 (zo + 0x14) 4 from sep_offsets zo (c := 24) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_same]
  have sozo18 : memLoad32 M175 (zo + 0x18) = v160 := by
    rw [← hM175, memLoad32_store32_sep (show Sep (zo + 0x1C) 4 (zo + 0x18) 4 from sep_offsets zo (c := 28) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), ← hM174, memLoad32_store32_same]
  have sozo1C : memLoad32 M175 (zo + 0x1C) = v165 := by
    rw [← hM175, memLoad32_store32_same]
  exact ⟨n199, M175, v160, v161, v162, v163, v164, v165, v166, v167, v169, v170, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198, v199, (.cons d160 (.cons d161 (.cons d162 (.cons d163 (.cons d164 (.cons d165 (.cons d166 (.cons d167 (.cons d168 (.cons d169 (.cons d170 (.cons d171 (.cons d172 (.cons d173 (.cons d174 (.cons d175 (.cons d176 (.cons d177 (.cons d178 (.cons d179 (.cons d180 (.cons d181 (.cons d182 (.cons d183 (.cons d184 (.cons d185 (.cons d186 (.cons d187 (.cons d188 (.cons d189 (.cons d190 (.cons d191 (.cons d192 (.cons d193 (.cons d194 (.cons d195 (.cons d196 (.cons d197 (.cons d198 (.single d199)))))))))))))))))))))))))))))))))))))))), u199.self, hc175, fr175, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so8, so10, so14, so18, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, sozo0, sozo4, sozo8, sozoC, sozo10, sozo14, sozo18, sozo1C, hv160, hv161, hv162, hv163, hv164, hv165, hv166, hv167, hv169, hv170, hv176, hv177, hv178, hv179, hv180, hv181, hv182, hv183, hv184, hv185, hv186, hv187, hv188, hv189, hv190, hv191, hv192, hv193, hv194, hv195, hv196, hv197, hv198, hv199⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem fsq_g5 {M0 Mi : Word → BitVec 8} {B F zo xp G3 G4 : Word} {n : Machine} {v1 v3 v4 v6 v9 v10 v13 v16 v17 v18 v19 v21 v28 v30 v48 v59 v64 v76 v83 v89 v99 v132 v137 v147 v160 v165 v176 v178 v179 v185 v188 v189 v190 v191 v193 v195 v198 v199 : Word}
    (s : St Mi B n 0x294 (reg n)) (hc : CodeIn Mi B feSquareInnerCode)
    (fr : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hZ : zo.toNat % 4 = 0) (hx : xp.toNat % 4 = 0)
    (sFC : Sep F 0x50 B feSquareInnerCode.length) (sZC : Sep zo 0x50 B feSquareInnerCode.length)
    (sXF : Sep xp 40 F 0x50) (sXZ : Sep xp 40 zo 0x50) (sFZ : Sep F 0x50 zo 0x50)
    (q1 : reg n ra = v83)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v48)
    (q6 : reg n (6 : Fin 32) = zo)
    (q7 : reg n (7 : Fin 32) = v195)
    (q8 : reg n (8 : Fin 32) = v185)
    (q9 : reg n (9 : Fin 32) = v179)
    (q10 : reg n a0 = v199)
    (q11 : reg n a1 = v198)
    (q12 : reg n a2 = v191)
    (q13 : reg n a3 = v189)
    (q14 : reg n a4 = v188)
    (q15 : reg n a5 = v193)
    (q16 : reg n a6 = v190)
    (q17 : reg n a7 = v176)
    (q18 : reg n (18 : Fin 32) = v9)
    (q19 : reg n (19 : Fin 32) = v17)
    (q20 : reg n (20 : Fin 32) = v16)
    (q21 : reg n (21 : Fin 32) = v178)
    (q22 : reg n (22 : Fin 32) = v10)
    (q23 : reg n (23 : Fin 32) = v18)
    (q24 : reg n (24 : Fin 32) = v21)
    (q25 : reg n (25 : Fin 32) = v137)
    (q26 : reg n (26 : Fin 32) = v4)
    (q27 : reg n (27 : Fin 32) = v30)
    (q28 : reg n (28 : Fin 32) = v30)
    (q29 : reg n (29 : Fin 32) = v6)
    (q30 : reg n (30 : Fin 32) = v64)
    (q31 : reg n (31 : Fin 32) = v19)
    (sl8 : memLoad32 Mi (F + 0x8) = v3)
    (sl10 : memLoad32 Mi (F + 0x10) = v28)
    (sl14 : memLoad32 Mi (F + 0x14) = v13)
    (sl18 : memLoad32 Mi (F + 0x18) = v1)
    (sl1C : memLoad32 Mi (F + 0x1C) = memLoad32 M0 (F + 0x1C))
    (sl20 : memLoad32 Mi (F + 0x20) = memLoad32 M0 (F + 0x20))
    (sl24 : memLoad32 Mi (F + 0x24) = memLoad32 M0 (F + 0x24))
    (sl28 : memLoad32 Mi (F + 0x28) = memLoad32 M0 (F + 0x28))
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    (slzo0 : memLoad32 Mi (zo + 0x0) = v59)
    (slzo4 : memLoad32 Mi (zo + 0x4) = v76)
    (slzo8 : memLoad32 Mi (zo + 0x8) = v89)
    (slzoC : memLoad32 Mi (zo + 0xC) = v99)
    (slzo10 : memLoad32 Mi (zo + 0x10) = v132)
    (slzo14 : memLoad32 Mi (zo + 0x14) = v147)
    (slzo18 : memLoad32 Mi (zo + 0x18) = v160)
    (slzo1C : memLoad32 Mi (zo + 0x1C) = v165)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v200 v201 v202 v203 v204 v205 v206 v208 v209 v210 v212 v213 v214 v215 v216 v217 v218 v219 v220 v221 v222 v223 v224 v225 v226 v227 v228 v229 v230 v231 v232 v233 v234 v235 v236 v237 v238 v239 : Word),
      Steps n n' ∧
      St M' B n' 0x30C (reg n') ∧
      CodeIn M' B feSquareInnerCode ∧
      (∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M' x = M0 x) ∧
      reg n' ra = v3 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v48 ∧
      reg n' (6 : Fin 32) = zo ∧
      reg n' (7 : Fin 32) = v232 ∧
      reg n' (8 : Fin 32) = v213 ∧
      reg n' (9 : Fin 32) = v222 ∧
      reg n' a0 = v237 ∧
      reg n' a1 = v239 ∧
      reg n' a2 = v229 ∧
      reg n' a3 = v223 ∧
      reg n' a4 = v227 ∧
      reg n' a5 = v238 ∧
      reg n' a6 = v218 ∧
      reg n' a7 = v204 ∧
      reg n' (18 : Fin 32) = v9 ∧
      reg n' (19 : Fin 32) = v17 ∧
      reg n' (20 : Fin 32) = v217 ∧
      reg n' (21 : Fin 32) = v208 ∧
      reg n' (22 : Fin 32) = v10 ∧
      reg n' (23 : Fin 32) = v18 ∧
      reg n' (24 : Fin 32) = v21 ∧
      reg n' (25 : Fin 32) = v221 ∧
      reg n' (26 : Fin 32) = v4 ∧
      reg n' (27 : Fin 32) = v30 ∧
      reg n' (28 : Fin 32) = v28 ∧
      reg n' (29 : Fin 32) = v6 ∧
      reg n' (30 : Fin 32) = v64 ∧
      reg n' (31 : Fin 32) = v19 ∧
      memLoad32 M' (F + 0x14) = v13 ∧
      memLoad32 M' (F + 0x18) = v1 ∧
      memLoad32 M' (F + 0x1C) = memLoad32 M0 (F + 0x1C) ∧
      memLoad32 M' (F + 0x20) = memLoad32 M0 (F + 0x20) ∧
      memLoad32 M' (F + 0x24) = memLoad32 M0 (F + 0x24) ∧
      memLoad32 M' (F + 0x28) = memLoad32 M0 (F + 0x28) ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (zo + 0x0) = v59 ∧
      memLoad32 M' (zo + 0x4) = v76 ∧
      memLoad32 M' (zo + 0x8) = v89 ∧
      memLoad32 M' (zo + 0xC) = v99 ∧
      memLoad32 M' (zo + 0x10) = v132 ∧
      memLoad32 M' (zo + 0x14) = v147 ∧
      memLoad32 M' (zo + 0x18) = v160 ∧
      memLoad32 M' (zo + 0x1C) = v165 ∧
      aluEval .add v185 v195 = v200 ∧
      aluEval .sltu v200 v195 = v201 ∧
      aluEval .add v199 v189 = v202 ∧
      aluEval .add v202 v201 = v203 ∧
      aluEval .add v200 v191 = v204 ∧
      aluEval .sltu v204 v200 = v205 ∧
      aluEval .mulhu v6 v10 = v206 ∧
      aluEval .mulhu v3 v48 = v208 ∧
      aluEval .mul v6 v10 = v209 ∧
      aluEval .mulhu v17 v18 = v210 ∧
      aluEval .mulhu v28 v9 = v212 ∧
      aluEval .mul v17 v18 = v213 ∧
      aluEval .mul v28 v9 = v214 ∧
      aluEval .add v203 v205 = v215 ∧
      aluEval .mul v3 v48 = v216 ∧
      aluEval .sll v4 0x1 = v217 ∧
      aluEval .add v190 v215 = v218 ∧
      aluEval .mul v21 v217 = v219 ∧
      aluEval .sll v206 0x1 = v220 ∧
      aluEval .mulhu v21 v217 = v221 ∧
      aluEval .srl v209 0x1F = v222 ∧
      aluEval .or v220 v222 = v223 ∧
      aluEval .add v212 v210 = v224 ∧
      aluEval .add v224 v208 = v225 ∧
      aluEval .add v214 v213 = v226 ∧
      aluEval .sltu v226 v213 = v227 ∧
      aluEval .add v216 v226 = v228 ∧
      aluEval .add v225 v227 = v229 ∧
      aluEval .sltu v228 v226 = v230 ∧
      aluEval .add v230 v229 = v231 ∧
      aluEval .add v219 v228 = v232 ∧
      aluEval .add v231 v221 = v233 ∧
      aluEval .sltu v232 v228 = v234 ∧
      aluEval .sll v209 0x1 = v235 ∧
      aluEval .add v233 v234 = v236 ∧
      aluEval .add v236 v223 = v237 ∧
      aluEval .add v235 v232 = v238 ∧
      aluEval .sltu v238 v232 = v239 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n200, v200, d200, hv200, u200⟩ := s.aluG hc fsq_at_294 (off' := 0x296) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv200
  obtain ⟨n201, v201, d201, hv201, u201⟩ := u200.aluG hc fsq_at_296 (off' := 0x29A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv201
  obtain ⟨n202, v202, d202, hv202, u202⟩ := u201.aluG hc fsq_at_29a (off' := 0x29C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv202
  obtain ⟨n203, v203, d203, hv203, u203⟩ := u202.aluG hc fsq_at_29c (off' := 0x2A0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv203
  obtain ⟨n204, v204, d204, hv204, u204⟩ := u203.aluG hc fsq_at_2a0 (off' := 0x2A4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv204
  obtain ⟨n205, v205, d205, hv205, u205⟩ := u204.aluG hc fsq_at_2a4 (off' := 0x2A8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv205
  obtain ⟨n206, v206, d206, hv206, u206⟩ := u205.aluG hc fsq_at_2a8 (off' := 0x2AC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv206
  obtain ⟨n207, d207, u207⟩ := u206.lwE hc fsq_at_2ac (off' := 0x2AE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 8) (by decide)) (v := v3)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl8])
  obtain ⟨n208, v208, d208, hv208, u208⟩ := u207.aluG hc fsq_at_2ae (off' := 0x2B2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv208
  obtain ⟨n209, v209, d209, hv209, u209⟩ := u208.aluG hc fsq_at_2b2 (off' := 0x2B6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv209
  obtain ⟨n210, v210, d210, hv210, u210⟩ := u209.aluG hc fsq_at_2b6 (off' := 0x2BA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv210
  obtain ⟨n211, d211, u211⟩ := u210.lwE hc fsq_at_2ba (off' := 0x2BC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 16) (by decide)) (v := v28)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl10])
  obtain ⟨n212, v212, d212, hv212, u212⟩ := u211.aluG hc fsq_at_2bc (off' := 0x2C0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv212
  obtain ⟨n213, v213, d213, hv213, u213⟩ := u212.aluG hc fsq_at_2c0 (off' := 0x2C4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv213
  obtain ⟨n214, v214, d214, hv214, u214⟩ := u213.aluG hc fsq_at_2c4 (off' := 0x2C8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv214
  obtain ⟨n215, v215, d215, hv215, u215⟩ := u214.aluG hc fsq_at_2c8 (off' := 0x2CA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv215
  obtain ⟨n216, v216, d216, hv216, u216⟩ := u215.aluG hc fsq_at_2ca (off' := 0x2CE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv216
  obtain ⟨n217, v217, d217, hv217, u217⟩ := u216.aluImmG hc fsq_at_2ce (off' := 0x2D2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv217
  obtain ⟨n218, v218, d218, hv218, u218⟩ := u217.aluG hc fsq_at_2d2 (off' := 0x2D4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv218
  obtain ⟨n219, v219, d219, hv219, u219⟩ := u218.aluG hc fsq_at_2d4 (off' := 0x2D8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv219
  obtain ⟨n220, v220, d220, hv220, u220⟩ := u219.aluImmG hc fsq_at_2d8 (off' := 0x2DA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv220
  obtain ⟨n221, v221, d221, hv221, u221⟩ := u220.aluG hc fsq_at_2da (off' := 0x2DE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv221
  obtain ⟨n222, v222, d222, hv222, u222⟩ := u221.aluImmG hc fsq_at_2de (off' := 0x2E2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv222
  obtain ⟨n223, v223, d223, hv223, u223⟩ := u222.aluG hc fsq_at_2e2 (off' := 0x2E4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv223
  obtain ⟨n224, v224, d224, hv224, u224⟩ := u223.aluG hc fsq_at_2e4 (off' := 0x2E6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv224
  obtain ⟨n225, v225, d225, hv225, u225⟩ := u224.aluG hc fsq_at_2e6 (off' := 0x2E8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv225
  obtain ⟨n226, v226, d226, hv226, u226⟩ := u225.aluG hc fsq_at_2e8 (off' := 0x2EA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv226
  obtain ⟨n227, v227, d227, hv227, u227⟩ := u226.aluG hc fsq_at_2ea (off' := 0x2EE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv227
  obtain ⟨n228, v228, d228, hv228, u228⟩ := u227.aluG hc fsq_at_2ee (off' := 0x2F0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv228
  obtain ⟨n229, v229, d229, hv229, u229⟩ := u228.aluG hc fsq_at_2f0 (off' := 0x2F2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv229
  obtain ⟨n230, v230, d230, hv230, u230⟩ := u229.aluG hc fsq_at_2f2 (off' := 0x2F6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv230
  obtain ⟨n231, v231, d231, hv231, u231⟩ := u230.aluG hc fsq_at_2f6 (off' := 0x2F8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv231
  obtain ⟨n232, v232, d232, hv232, u232⟩ := u231.aluG hc fsq_at_2f8 (off' := 0x2FA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv232
  obtain ⟨n233, v233, d233, hv233, u233⟩ := u232.aluG hc fsq_at_2fa (off' := 0x2FC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv233
  obtain ⟨n234, v234, d234, hv234, u234⟩ := u233.aluG hc fsq_at_2fc (off' := 0x300) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv234
  obtain ⟨n235, v235, d235, hv235, u235⟩ := u234.aluImmG hc fsq_at_300 (off' := 0x302) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv235
  obtain ⟨n236, v236, d236, hv236, u236⟩ := u235.aluG hc fsq_at_302 (off' := 0x304) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv236
  obtain ⟨n237, v237, d237, hv237, u237⟩ := u236.aluG hc fsq_at_304 (off' := 0x306) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv237
  obtain ⟨n238, v238, d238, hv238, u238⟩ := u237.aluG hc fsq_at_306 (off' := 0x308) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv238
  obtain ⟨n239, v239, d239, hv239, u239⟩ := u238.aluG hc fsq_at_308 (off' := 0x30C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv239
  have qo1 : reg n239 ra = v3 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n239 sp = F := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n239 (3 : Fin 32) = G3 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n239 (4 : Fin 32) = G4 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n239 (5 : Fin 32) = v48 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n239 (6 : Fin 32) = zo := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n239 (7 : Fin 32) = v232 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n239 (8 : Fin 32) = v213 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n239 (9 : Fin 32) = v222 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n239 a0 = v237 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n239 a1 = v239 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n239 a2 = v229 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n239 a3 = v223 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n239 a4 = v227 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n239 a5 = v238 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n239 a6 = v218 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n239 a7 = v204 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n239 (18 : Fin 32) = v9 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n239 (19 : Fin 32) = v17 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n239 (20 : Fin 32) = v217 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n239 (21 : Fin 32) = v208 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n239 (22 : Fin 32) = v10 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n239 (23 : Fin 32) = v18 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n239 (24 : Fin 32) = v21 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n239 (25 : Fin 32) = v221 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n239 (26 : Fin 32) = v4 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n239 (27 : Fin 32) = v30 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n239 (28 : Fin 32) = v28 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n239 (29 : Fin 32) = v6 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n239 (30 : Fin 32) = v64 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n239 (31 : Fin 32) = v19 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so14 : memLoad32 Mi (F + 0x14) = v13 := by
    rw [sl14]
  have so18 : memLoad32 Mi (F + 0x18) = v1 := by
    rw [sl18]
  have so1C : memLoad32 Mi (F + 0x1C) = memLoad32 M0 (F + 0x1C) := by
    rw [sl1C]
  have so20 : memLoad32 Mi (F + 0x20) = memLoad32 M0 (F + 0x20) := by
    rw [sl20]
  have so24 : memLoad32 Mi (F + 0x24) = memLoad32 M0 (F + 0x24) := by
    rw [sl24]
  have so28 : memLoad32 Mi (F + 0x28) = memLoad32 M0 (F + 0x28) := by
    rw [sl28]
  have so2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [sl2C]
  have so30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [sl30]
  have so34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [sl34]
  have so38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [sl38]
  have so3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [sl3C]
  have so40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [sl40]
  have so44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [sl44]
  have so48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [sl48]
  have so4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [sl4C]
  have sozo0 : memLoad32 Mi (zo + 0x0) = v59 := by
    rw [slzo0]
  have sozo4 : memLoad32 Mi (zo + 0x4) = v76 := by
    rw [slzo4]
  have sozo8 : memLoad32 Mi (zo + 0x8) = v89 := by
    rw [slzo8]
  have sozoC : memLoad32 Mi (zo + 0xC) = v99 := by
    rw [slzoC]
  have sozo10 : memLoad32 Mi (zo + 0x10) = v132 := by
    rw [slzo10]
  have sozo14 : memLoad32 Mi (zo + 0x14) = v147 := by
    rw [slzo14]
  have sozo18 : memLoad32 Mi (zo + 0x18) = v160 := by
    rw [slzo18]
  have sozo1C : memLoad32 Mi (zo + 0x1C) = v165 := by
    rw [slzo1C]
  exact ⟨n239, Mi, v200, v201, v202, v203, v204, v205, v206, v208, v209, v210, v212, v213, v214, v215, v216, v217, v218, v219, v220, v221, v222, v223, v224, v225, v226, v227, v228, v229, v230, v231, v232, v233, v234, v235, v236, v237, v238, v239, (.cons d200 (.cons d201 (.cons d202 (.cons d203 (.cons d204 (.cons d205 (.cons d206 (.cons d207 (.cons d208 (.cons d209 (.cons d210 (.cons d211 (.cons d212 (.cons d213 (.cons d214 (.cons d215 (.cons d216 (.cons d217 (.cons d218 (.cons d219 (.cons d220 (.cons d221 (.cons d222 (.cons d223 (.cons d224 (.cons d225 (.cons d226 (.cons d227 (.cons d228 (.cons d229 (.cons d230 (.cons d231 (.cons d232 (.cons d233 (.cons d234 (.cons d235 (.cons d236 (.cons d237 (.cons d238 (.single d239)))))))))))))))))))))))))))))))))))))))), u239.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so14, so18, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, sozo0, sozo4, sozo8, sozoC, sozo10, sozo14, sozo18, sozo1C, hv200, hv201, hv202, hv203, hv204, hv205, hv206, hv208, hv209, hv210, hv212, hv213, hv214, hv215, hv216, hv217, hv218, hv219, hv220, hv221, hv222, hv223, hv224, hv225, hv226, hv227, hv228, hv229, hv230, hv231, hv232, hv233, hv234, hv235, hv236, hv237, hv238, hv239⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem fsq_g6 {M0 Mi : Word → BitVec 8} {B F zo xp G3 G4 : Word} {n : Machine} {v1 v3 v4 v6 v9 v10 v13 v17 v18 v19 v21 v28 v30 v48 v59 v64 v76 v89 v99 v132 v147 v160 v165 v204 v208 v213 v217 v218 v221 v222 v223 v227 v229 v232 v237 v238 v239 : Word}
    (s : St Mi B n 0x30C (reg n)) (hc : CodeIn Mi B feSquareInnerCode)
    (fr : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hZ : zo.toNat % 4 = 0) (hx : xp.toNat % 4 = 0)
    (sFC : Sep F 0x50 B feSquareInnerCode.length) (sZC : Sep zo 0x50 B feSquareInnerCode.length)
    (sXF : Sep xp 40 F 0x50) (sXZ : Sep xp 40 zo 0x50) (sFZ : Sep F 0x50 zo 0x50)
    (q1 : reg n ra = v3)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v48)
    (q6 : reg n (6 : Fin 32) = zo)
    (q7 : reg n (7 : Fin 32) = v232)
    (q8 : reg n (8 : Fin 32) = v213)
    (q9 : reg n (9 : Fin 32) = v222)
    (q10 : reg n a0 = v237)
    (q11 : reg n a1 = v239)
    (q12 : reg n a2 = v229)
    (q13 : reg n a3 = v223)
    (q14 : reg n a4 = v227)
    (q15 : reg n a5 = v238)
    (q16 : reg n a6 = v218)
    (q17 : reg n a7 = v204)
    (q18 : reg n (18 : Fin 32) = v9)
    (q19 : reg n (19 : Fin 32) = v17)
    (q20 : reg n (20 : Fin 32) = v217)
    (q21 : reg n (21 : Fin 32) = v208)
    (q22 : reg n (22 : Fin 32) = v10)
    (q23 : reg n (23 : Fin 32) = v18)
    (q24 : reg n (24 : Fin 32) = v21)
    (q25 : reg n (25 : Fin 32) = v221)
    (q26 : reg n (26 : Fin 32) = v4)
    (q27 : reg n (27 : Fin 32) = v30)
    (q28 : reg n (28 : Fin 32) = v28)
    (q29 : reg n (29 : Fin 32) = v6)
    (q30 : reg n (30 : Fin 32) = v64)
    (q31 : reg n (31 : Fin 32) = v19)
    (sl14 : memLoad32 Mi (F + 0x14) = v13)
    (sl18 : memLoad32 Mi (F + 0x18) = v1)
    (sl1C : memLoad32 Mi (F + 0x1C) = memLoad32 M0 (F + 0x1C))
    (sl20 : memLoad32 Mi (F + 0x20) = memLoad32 M0 (F + 0x20))
    (sl24 : memLoad32 Mi (F + 0x24) = memLoad32 M0 (F + 0x24))
    (sl28 : memLoad32 Mi (F + 0x28) = memLoad32 M0 (F + 0x28))
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    (slzo0 : memLoad32 Mi (zo + 0x0) = v59)
    (slzo4 : memLoad32 Mi (zo + 0x4) = v76)
    (slzo8 : memLoad32 Mi (zo + 0x8) = v89)
    (slzoC : memLoad32 Mi (zo + 0xC) = v99)
    (slzo10 : memLoad32 Mi (zo + 0x10) = v132)
    (slzo14 : memLoad32 Mi (zo + 0x14) = v147)
    (slzo18 : memLoad32 Mi (zo + 0x18) = v160)
    (slzo1C : memLoad32 Mi (zo + 0x1C) = v165)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v240 v241 v244 v245 v246 v247 v248 v249 v252 v253 v254 v255 v256 v257 v258 v259 v261 v262 v263 v264 v265 v266 v267 v268 v269 v270 v271 v272 v273 v274 v275 v276 v277 v278 v279 : Word),
      Steps n n' ∧
      St M' B n' 0x38E (reg n') ∧
      CodeIn M' B feSquareInnerCode ∧
      (∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M' x = M0 x) ∧
      reg n' ra = v3 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v48 ∧
      reg n' (6 : Fin 32) = zo ∧
      reg n' (7 : Fin 32) = v269 ∧
      reg n' (8 : Fin 32) = v264 ∧
      reg n' (9 : Fin 32) = v275 ∧
      reg n' a0 = v274 ∧
      reg n' a1 = v276 ∧
      reg n' a2 = v272 ∧
      reg n' a3 = v262 ∧
      reg n' a4 = v278 ∧
      reg n' a5 = v279 ∧
      reg n' a6 = v277 ∧
      reg n' a7 = v255 ∧
      reg n' (18 : Fin 32) = v13 ∧
      reg n' (19 : Fin 32) = v17 ∧
      reg n' (20 : Fin 32) = v217 ∧
      reg n' (21 : Fin 32) = v208 ∧
      reg n' (22 : Fin 32) = v10 ∧
      reg n' (23 : Fin 32) = v18 ∧
      reg n' (24 : Fin 32) = v21 ∧
      reg n' (25 : Fin 32) = v221 ∧
      reg n' (26 : Fin 32) = v4 ∧
      reg n' (27 : Fin 32) = v30 ∧
      reg n' (28 : Fin 32) = v28 ∧
      reg n' (29 : Fin 32) = v6 ∧
      reg n' (30 : Fin 32) = v64 ∧
      reg n' (31 : Fin 32) = v19 ∧
      memLoad32 M' (F + 0x18) = v1 ∧
      memLoad32 M' (F + 0x1C) = memLoad32 M0 (F + 0x1C) ∧
      memLoad32 M' (F + 0x20) = memLoad32 M0 (F + 0x20) ∧
      memLoad32 M' (F + 0x24) = memLoad32 M0 (F + 0x24) ∧
      memLoad32 M' (F + 0x28) = memLoad32 M0 (F + 0x28) ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (zo + 0x0) = v59 ∧
      memLoad32 M' (zo + 0x4) = v76 ∧
      memLoad32 M' (zo + 0x8) = v89 ∧
      memLoad32 M' (zo + 0xC) = v99 ∧
      memLoad32 M' (zo + 0x10) = v132 ∧
      memLoad32 M' (zo + 0x14) = v147 ∧
      memLoad32 M' (zo + 0x18) = v160 ∧
      memLoad32 M' (zo + 0x1C) = v165 ∧
      memLoad32 M' (zo + 0x20) = v204 ∧
      memLoad32 M' (zo + 0x24) = v218 ∧
      memLoad32 M' (zo + 0x28) = v238 ∧
      memLoad32 M' (zo + 0x2C) = v244 ∧
      aluEval .mul v217 v10 = v240 ∧
      aluEval .mulhu v217 v10 = v241 ∧
      aluEval .add v237 v239 = v244 ∧
      aluEval .mulhu v17 v28 = v245 ∧
      aluEval .mulhu v19 v9 = v246 ∧
      aluEval .mulhu v64 v18 = v247 ∧
      aluEval .mul v17 v28 = v248 ∧
      aluEval .mul v19 v9 = v249 ∧
      aluEval .mul v64 v18 = v252 ∧
      aluEval .srl v240 0x1F = v253 ∧
      aluEval .sll v241 0x1 = v254 ∧
      aluEval .or v254 v253 = v255 ∧
      aluEval .mul v6 v48 = v256 ∧
      aluEval .add v245 v246 = v257 ∧
      aluEval .mulhu v6 v48 = v258 ∧
      aluEval .add v257 v247 = v259 ∧
      aluEval .mul v21 v13 = v261 ∧
      aluEval .mulhu v21 v13 = v262 ∧
      aluEval .add v248 v249 = v263 ∧
      aluEval .sltu v263 v249 = v264 ∧
      aluEval .add v252 v263 = v265 ∧
      aluEval .sltu v265 v263 = v266 ∧
      aluEval .add v259 v264 = v267 ∧
      aluEval .add v267 v266 = v268 ∧
      aluEval .add v256 v265 = v269 ∧
      aluEval .add v268 v258 = v270 ∧
      aluEval .sltu v269 v265 = v271 ∧
      aluEval .sll v240 0x1 = v272 ∧
      aluEval .add v271 v270 = v273 ∧
      aluEval .add v273 v262 = v274 ∧
      aluEval .add v261 v269 = v275 ∧
      aluEval .sltu v275 v269 = v276 ∧
      aluEval .mulhu v6 v18 = v277 ∧
      aluEval .mulhu v3 v28 = v278 ∧
      aluEval .mulhu v19 v17 = v279 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n240, v240, d240, hv240, u240⟩ := s.aluG hc fsq_at_30c (off' := 0x310) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv240
  obtain ⟨n241, v241, d241, hv241, u241⟩ := u240.aluG hc fsq_at_310 (off' := 0x314) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv241
  obtain ⟨n242, d242, u242⟩ := u241.swG hc fsq_at_314 (off' := 0x318) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 32) (by decide)) (a := zo + 0x20) (v := v204)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M242, hM242⟩ : ∃ M', memStore32 Mi (zo + 0x20) v204 = M' := ⟨_, rfl⟩
  rw [hM242] at u242
  have hc242 : CodeIn M242 B feSquareInnerCode := by rw [← hM242]; exact hc.store32 (frm_sep' sZC (by decide))
  have fr242 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M242 x = M0 x := fun x hxF hxZ => by
    rw [← hM242, memStore32_get_sep (frm_sep' hxZ (by decide)), fr x hxF hxZ]
  obtain ⟨n243, d243, u243⟩ := u242.swG hc242 fsq_at_318 (off' := 0x31C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 36) (by decide)) (a := zo + 0x24) (v := v218)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M243, hM243⟩ : ∃ M', memStore32 M242 (zo + 0x24) v218 = M' := ⟨_, rfl⟩
  rw [hM243] at u243
  have hc243 : CodeIn M243 B feSquareInnerCode := by rw [← hM243]; exact hc242.store32 (frm_sep' sZC (by decide))
  have fr243 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M243 x = M0 x := fun x hxF hxZ => by
    rw [← hM243, memStore32_get_sep (frm_sep' hxZ (by decide)), fr242 x hxF hxZ]
  obtain ⟨n244, v244, d244, hv244, u244⟩ := u243.aluG hc243 fsq_at_31c (off' := 0x31E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv244
  obtain ⟨n245, v245, d245, hv245, u245⟩ := u244.aluG hc243 fsq_at_31e (off' := 0x322) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv245
  obtain ⟨n246, v246, d246, hv246, u246⟩ := u245.aluG hc243 fsq_at_322 (off' := 0x326) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv246
  obtain ⟨n247, v247, d247, hv247, u247⟩ := u246.aluG hc243 fsq_at_326 (off' := 0x32A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv247
  obtain ⟨n248, v248, d248, hv248, u248⟩ := u247.aluG hc243 fsq_at_32a (off' := 0x32E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv248
  obtain ⟨n249, v249, d249, hv249, u249⟩ := u248.aluG hc243 fsq_at_32e (off' := 0x332) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv249
  obtain ⟨n250, d250, u250⟩ := u249.swG hc243 fsq_at_332 (off' := 0x336) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 40) (by decide)) (a := zo + 0x28) (v := v238)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M250, hM250⟩ : ∃ M', memStore32 M243 (zo + 0x28) v238 = M' := ⟨_, rfl⟩
  rw [hM250] at u250
  have hc250 : CodeIn M250 B feSquareInnerCode := by rw [← hM250]; exact hc243.store32 (frm_sep' sZC (by decide))
  have fr250 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M250 x = M0 x := fun x hxF hxZ => by
    rw [← hM250, memStore32_get_sep (frm_sep' hxZ (by decide)), fr243 x hxF hxZ]
  obtain ⟨n251, d251, u251⟩ := u250.swG hc250 fsq_at_336 (off' := 0x33A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 44) (by decide)) (a := zo + 0x2C) (v := v244)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M251, hM251⟩ : ∃ M', memStore32 M250 (zo + 0x2C) v244 = M' := ⟨_, rfl⟩
  rw [hM251] at u251
  have hc251 : CodeIn M251 B feSquareInnerCode := by rw [← hM251]; exact hc250.store32 (frm_sep' sZC (by decide))
  have fr251 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M251 x = M0 x := fun x hxF hxZ => by
    rw [← hM251, memStore32_get_sep (frm_sep' hxZ (by decide)), fr250 x hxF hxZ]
  obtain ⟨n252, v252, d252, hv252, u252⟩ := u251.aluG hc251 fsq_at_33a (off' := 0x33E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv252
  obtain ⟨n253, v253, d253, hv253, u253⟩ := u252.aluImmG hc251 fsq_at_33e (off' := 0x342) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv253
  obtain ⟨n254, v254, d254, hv254, u254⟩ := u253.aluImmG hc251 fsq_at_342 (off' := 0x344) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv254
  obtain ⟨n255, v255, d255, hv255, u255⟩ := u254.aluG hc251 fsq_at_344 (off' := 0x348) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv255
  obtain ⟨n256, v256, d256, hv256, u256⟩ := u255.aluG hc251 fsq_at_348 (off' := 0x34C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv256
  obtain ⟨n257, v257, d257, hv257, u257⟩ := u256.aluG hc251 fsq_at_34c (off' := 0x34E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv257
  obtain ⟨n258, v258, d258, hv258, u258⟩ := u257.aluG hc251 fsq_at_34e (off' := 0x352) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv258
  obtain ⟨n259, v259, d259, hv259, u259⟩ := u258.aluG hc251 fsq_at_352 (off' := 0x354) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv259
  obtain ⟨n260, d260, u260⟩ := u259.lwE hc251 fsq_at_354 (off' := 0x356) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 20) (by decide)) (v := v13)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x14) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 20) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x14) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 20) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x14) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 20) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x14) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 20) (l := 4) (by decide)), sl14])
  obtain ⟨n261, v261, d261, hv261, u261⟩ := u260.aluG hc251 fsq_at_356 (off' := 0x35A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv261
  obtain ⟨n262, v262, d262, hv262, u262⟩ := u261.aluG hc251 fsq_at_35a (off' := 0x35E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv262
  obtain ⟨n263, v263, d263, hv263, u263⟩ := u262.aluG hc251 fsq_at_35e (off' := 0x360) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv263
  obtain ⟨n264, v264, d264, hv264, u264⟩ := u263.aluG hc251 fsq_at_360 (off' := 0x364) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv264
  obtain ⟨n265, v265, d265, hv265, u265⟩ := u264.aluG hc251 fsq_at_364 (off' := 0x366) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv265
  obtain ⟨n266, v266, d266, hv266, u266⟩ := u265.aluG hc251 fsq_at_366 (off' := 0x36A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv266
  obtain ⟨n267, v267, d267, hv267, u267⟩ := u266.aluG hc251 fsq_at_36a (off' := 0x36C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv267
  obtain ⟨n268, v268, d268, hv268, u268⟩ := u267.aluG hc251 fsq_at_36c (off' := 0x36E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv268
  obtain ⟨n269, v269, d269, hv269, u269⟩ := u268.aluG hc251 fsq_at_36e (off' := 0x370) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv269
  obtain ⟨n270, v270, d270, hv270, u270⟩ := u269.aluG hc251 fsq_at_370 (off' := 0x372) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv270
  obtain ⟨n271, v271, d271, hv271, u271⟩ := u270.aluG hc251 fsq_at_372 (off' := 0x376) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv271
  obtain ⟨n272, v272, d272, hv272, u272⟩ := u271.aluImmG hc251 fsq_at_376 (off' := 0x378) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv272
  obtain ⟨n273, v273, d273, hv273, u273⟩ := u272.aluG hc251 fsq_at_378 (off' := 0x37A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv273
  obtain ⟨n274, v274, d274, hv274, u274⟩ := u273.aluG hc251 fsq_at_37a (off' := 0x37C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv274
  obtain ⟨n275, v275, d275, hv275, u275⟩ := u274.aluG hc251 fsq_at_37c (off' := 0x37E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv275
  obtain ⟨n276, v276, d276, hv276, u276⟩ := u275.aluG hc251 fsq_at_37e (off' := 0x382) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv276
  obtain ⟨n277, v277, d277, hv277, u277⟩ := u276.aluG hc251 fsq_at_382 (off' := 0x386) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv277
  obtain ⟨n278, v278, d278, hv278, u278⟩ := u277.aluG hc251 fsq_at_386 (off' := 0x38A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv278
  obtain ⟨n279, v279, d279, hv279, u279⟩ := u278.aluG hc251 fsq_at_38a (off' := 0x38E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv279
  have qo1 : reg n279 ra = v3 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n279 sp = F := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n279 (3 : Fin 32) = G3 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n279 (4 : Fin 32) = G4 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n279 (5 : Fin 32) = v48 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n279 (6 : Fin 32) = zo := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n279 (7 : Fin 32) = v269 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n279 (8 : Fin 32) = v264 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n279 (9 : Fin 32) = v275 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n279 a0 = v274 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n279 a1 = v276 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n279 a2 = v272 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n279 a3 = v262 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n279 a4 = v278 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n279 a5 = v279 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n279 a6 = v277 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n279 a7 = v255 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n279 (18 : Fin 32) = v13 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n279 (19 : Fin 32) = v17 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n279 (20 : Fin 32) = v217 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n279 (21 : Fin 32) = v208 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n279 (22 : Fin 32) = v10 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n279 (23 : Fin 32) = v18 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n279 (24 : Fin 32) = v21 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n279 (25 : Fin 32) = v221 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n279 (26 : Fin 32) = v4 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n279 (27 : Fin 32) = v30 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n279 (28 : Fin 32) = v28 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n279 (29 : Fin 32) = v6 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n279 (30 : Fin 32) = v64 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n279 (31 : Fin 32) = v19 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so18 : memLoad32 M251 (F + 0x18) = v1 := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), sl18]
  have so1C : memLoad32 M251 (F + 0x1C) = memLoad32 M0 (F + 0x1C) := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), sl1C]
  have so20 : memLoad32 M251 (F + 0x20) = memLoad32 M0 (F + 0x20) := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), sl20]
  have so24 : memLoad32 M251 (F + 0x24) = memLoad32 M0 (F + 0x24) := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), sl24]
  have so28 : memLoad32 M251 (F + 0x28) = memLoad32 M0 (F + 0x28) := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), sl28]
  have so2C : memLoad32 M251 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), sl2C]
  have so30 : memLoad32 M251 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), sl30]
  have so34 : memLoad32 M251 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), sl34]
  have so38 : memLoad32 M251 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), sl38]
  have so3C : memLoad32 M251 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), sl3C]
  have so40 : memLoad32 M251 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), sl40]
  have so44 : memLoad32 M251 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), sl44]
  have so48 : memLoad32 M251 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), sl48]
  have so4C : memLoad32 M251 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 44) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 40) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 36) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 32) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), sl4C]
  have sozo0 : memLoad32 M251 (zo + 0x0) = v59 := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (zo + 0x0) 4 from sep_offsets zo (c := 44) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (zo + 0x0) 4 from sep_offsets zo (c := 40) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (zo + 0x0) 4 from sep_offsets zo (c := 36) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (zo + 0x0) 4 from sep_offsets zo (c := 32) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), slzo0]
  have sozo4 : memLoad32 M251 (zo + 0x4) = v76 := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (zo + 0x4) 4 from sep_offsets zo (c := 44) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (zo + 0x4) 4 from sep_offsets zo (c := 40) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (zo + 0x4) 4 from sep_offsets zo (c := 36) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (zo + 0x4) 4 from sep_offsets zo (c := 32) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), slzo4]
  have sozo8 : memLoad32 M251 (zo + 0x8) = v89 := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (zo + 0x8) 4 from sep_offsets zo (c := 44) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (zo + 0x8) 4 from sep_offsets zo (c := 40) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (zo + 0x8) 4 from sep_offsets zo (c := 36) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (zo + 0x8) 4 from sep_offsets zo (c := 32) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), slzo8]
  have sozoC : memLoad32 M251 (zo + 0xC) = v99 := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (zo + 0xC) 4 from sep_offsets zo (c := 44) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (zo + 0xC) 4 from sep_offsets zo (c := 40) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (zo + 0xC) 4 from sep_offsets zo (c := 36) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (zo + 0xC) 4 from sep_offsets zo (c := 32) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slzoC]
  have sozo10 : memLoad32 M251 (zo + 0x10) = v132 := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (zo + 0x10) 4 from sep_offsets zo (c := 44) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (zo + 0x10) 4 from sep_offsets zo (c := 40) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (zo + 0x10) 4 from sep_offsets zo (c := 36) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (zo + 0x10) 4 from sep_offsets zo (c := 32) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), slzo10]
  have sozo14 : memLoad32 M251 (zo + 0x14) = v147 := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (zo + 0x14) 4 from sep_offsets zo (c := 44) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (zo + 0x14) 4 from sep_offsets zo (c := 40) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (zo + 0x14) 4 from sep_offsets zo (c := 36) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (zo + 0x14) 4 from sep_offsets zo (c := 32) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), slzo14]
  have sozo18 : memLoad32 M251 (zo + 0x18) = v160 := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (zo + 0x18) 4 from sep_offsets zo (c := 44) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (zo + 0x18) 4 from sep_offsets zo (c := 40) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (zo + 0x18) 4 from sep_offsets zo (c := 36) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (zo + 0x18) 4 from sep_offsets zo (c := 32) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), slzo18]
  have sozo1C : memLoad32 M251 (zo + 0x1C) = v165 := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (zo + 0x1C) 4 from sep_offsets zo (c := 44) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (zo + 0x1C) 4 from sep_offsets zo (c := 40) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (zo + 0x1C) 4 from sep_offsets zo (c := 36) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), ← hM242, memLoad32_store32_sep (show Sep (zo + 0x20) 4 (zo + 0x1C) 4 from sep_offsets zo (c := 32) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), slzo1C]
  have sozo20 : memLoad32 M251 (zo + 0x20) = v204 := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (zo + 0x20) 4 from sep_offsets zo (c := 44) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (zo + 0x20) 4 from sep_offsets zo (c := 40) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), ← hM243, memLoad32_store32_sep (show Sep (zo + 0x24) 4 (zo + 0x20) 4 from sep_offsets zo (c := 36) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), ← hM242, memLoad32_store32_same]
  have sozo24 : memLoad32 M251 (zo + 0x24) = v218 := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (zo + 0x24) 4 from sep_offsets zo (c := 44) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), ← hM250, memLoad32_store32_sep (show Sep (zo + 0x28) 4 (zo + 0x24) 4 from sep_offsets zo (c := 40) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), ← hM243, memLoad32_store32_same]
  have sozo28 : memLoad32 M251 (zo + 0x28) = v238 := by
    rw [← hM251, memLoad32_store32_sep (show Sep (zo + 0x2C) 4 (zo + 0x28) 4 from sep_offsets zo (c := 44) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), ← hM250, memLoad32_store32_same]
  have sozo2C : memLoad32 M251 (zo + 0x2C) = v244 := by
    rw [← hM251, memLoad32_store32_same]
  exact ⟨n279, M251, v240, v241, v244, v245, v246, v247, v248, v249, v252, v253, v254, v255, v256, v257, v258, v259, v261, v262, v263, v264, v265, v266, v267, v268, v269, v270, v271, v272, v273, v274, v275, v276, v277, v278, v279, (.cons d240 (.cons d241 (.cons d242 (.cons d243 (.cons d244 (.cons d245 (.cons d246 (.cons d247 (.cons d248 (.cons d249 (.cons d250 (.cons d251 (.cons d252 (.cons d253 (.cons d254 (.cons d255 (.cons d256 (.cons d257 (.cons d258 (.cons d259 (.cons d260 (.cons d261 (.cons d262 (.cons d263 (.cons d264 (.cons d265 (.cons d266 (.cons d267 (.cons d268 (.cons d269 (.cons d270 (.cons d271 (.cons d272 (.cons d273 (.cons d274 (.cons d275 (.cons d276 (.cons d277 (.cons d278 (.single d279)))))))))))))))))))))))))))))))))))))))), u279.self, hc251, fr251, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so18, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, sozo0, sozo4, sozo8, sozoC, sozo10, sozo14, sozo18, sozo1C, sozo20, sozo24, sozo28, sozo2C, hv240, hv241, hv244, hv245, hv246, hv247, hv248, hv249, hv252, hv253, hv254, hv255, hv256, hv257, hv258, hv259, hv261, hv262, hv263, hv264, hv265, hv266, hv267, hv268, hv269, hv270, hv271, hv272, hv273, hv274, hv275, hv276, hv277, hv278, hv279⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem fsq_g7 {M0 Mi : Word → BitVec 8} {B F zo xp G3 G4 : Word} {n : Machine} {v1 v3 v4 v6 v10 v13 v17 v18 v19 v21 v28 v30 v48 v59 v64 v76 v89 v99 v132 v147 v160 v165 v204 v208 v217 v218 v221 v238 v244 v255 v262 v264 v269 v272 v274 v275 v276 v277 v278 v279 : Word}
    (s : St Mi B n 0x38E (reg n)) (hc : CodeIn Mi B feSquareInnerCode)
    (fr : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hZ : zo.toNat % 4 = 0) (hx : xp.toNat % 4 = 0)
    (sFC : Sep F 0x50 B feSquareInnerCode.length) (sZC : Sep zo 0x50 B feSquareInnerCode.length)
    (sXF : Sep xp 40 F 0x50) (sXZ : Sep xp 40 zo 0x50) (sFZ : Sep F 0x50 zo 0x50)
    (q1 : reg n ra = v3)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v48)
    (q6 : reg n (6 : Fin 32) = zo)
    (q7 : reg n (7 : Fin 32) = v269)
    (q8 : reg n (8 : Fin 32) = v264)
    (q9 : reg n (9 : Fin 32) = v275)
    (q10 : reg n a0 = v274)
    (q11 : reg n a1 = v276)
    (q12 : reg n a2 = v272)
    (q13 : reg n a3 = v262)
    (q14 : reg n a4 = v278)
    (q15 : reg n a5 = v279)
    (q16 : reg n a6 = v277)
    (q17 : reg n a7 = v255)
    (q18 : reg n (18 : Fin 32) = v13)
    (q19 : reg n (19 : Fin 32) = v17)
    (q20 : reg n (20 : Fin 32) = v217)
    (q21 : reg n (21 : Fin 32) = v208)
    (q22 : reg n (22 : Fin 32) = v10)
    (q23 : reg n (23 : Fin 32) = v18)
    (q24 : reg n (24 : Fin 32) = v21)
    (q25 : reg n (25 : Fin 32) = v221)
    (q26 : reg n (26 : Fin 32) = v4)
    (q27 : reg n (27 : Fin 32) = v30)
    (q28 : reg n (28 : Fin 32) = v28)
    (q29 : reg n (29 : Fin 32) = v6)
    (q30 : reg n (30 : Fin 32) = v64)
    (q31 : reg n (31 : Fin 32) = v19)
    (sl18 : memLoad32 Mi (F + 0x18) = v1)
    (sl1C : memLoad32 Mi (F + 0x1C) = memLoad32 M0 (F + 0x1C))
    (sl20 : memLoad32 Mi (F + 0x20) = memLoad32 M0 (F + 0x20))
    (sl24 : memLoad32 Mi (F + 0x24) = memLoad32 M0 (F + 0x24))
    (sl28 : memLoad32 Mi (F + 0x28) = memLoad32 M0 (F + 0x28))
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    (slzo0 : memLoad32 Mi (zo + 0x0) = v59)
    (slzo4 : memLoad32 Mi (zo + 0x4) = v76)
    (slzo8 : memLoad32 Mi (zo + 0x8) = v89)
    (slzoC : memLoad32 Mi (zo + 0xC) = v99)
    (slzo10 : memLoad32 Mi (zo + 0x10) = v132)
    (slzo14 : memLoad32 Mi (zo + 0x14) = v147)
    (slzo18 : memLoad32 Mi (zo + 0x18) = v160)
    (slzo1C : memLoad32 Mi (zo + 0x1C) = v165)
    (slzo20 : memLoad32 Mi (zo + 0x20) = v204)
    (slzo24 : memLoad32 Mi (zo + 0x24) = v218)
    (slzo28 : memLoad32 Mi (zo + 0x28) = v238)
    (slzo2C : memLoad32 Mi (zo + 0x2C) = v244)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v280 v281 v282 v283 v284 v285 v286 v287 v288 v289 v290 v291 v292 v293 v294 v295 v297 v298 v299 v300 v301 v302 v303 v304 v305 v306 v307 v308 v309 v310 v311 v313 v314 v315 v316 v317 v318 v319 : Word),
      Steps n n' ∧
      St M' B n' 0x40A (reg n') ∧
      CodeIn M' B feSquareInnerCode ∧
      (∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M' x = M0 x) ∧
      reg n' ra = v3 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v48 ∧
      reg n' (6 : Fin 32) = zo ∧
      reg n' (7 : Fin 32) = v288 ∧
      reg n' (8 : Fin 32) = v317 ∧
      reg n' (9 : Fin 32) = v309 ∧
      reg n' a0 = v318 ∧
      reg n' a1 = v319 ∧
      reg n' a2 = v310 ∧
      reg n' a3 = v311 ∧
      reg n' a4 = v315 ∧
      reg n' a5 = v316 ∧
      reg n' a6 = v277 ∧
      reg n' a7 = v299 ∧
      reg n' (18 : Fin 32) = v13 ∧
      reg n' (19 : Fin 32) = v17 ∧
      reg n' (20 : Fin 32) = v217 ∧
      reg n' (21 : Fin 32) = v208 ∧
      reg n' (22 : Fin 32) = v10 ∧
      reg n' (23 : Fin 32) = v18 ∧
      reg n' (24 : Fin 32) = v21 ∧
      reg n' (25 : Fin 32) = v221 ∧
      reg n' (26 : Fin 32) = v4 ∧
      reg n' (27 : Fin 32) = v30 ∧
      reg n' (28 : Fin 32) = v28 ∧
      reg n' (29 : Fin 32) = v6 ∧
      reg n' (30 : Fin 32) = v64 ∧
      reg n' (31 : Fin 32) = v19 ∧
      memLoad32 M' (F + 0x18) = v1 ∧
      memLoad32 M' (F + 0x1C) = memLoad32 M0 (F + 0x1C) ∧
      memLoad32 M' (F + 0x20) = memLoad32 M0 (F + 0x20) ∧
      memLoad32 M' (F + 0x24) = memLoad32 M0 (F + 0x24) ∧
      memLoad32 M' (F + 0x28) = memLoad32 M0 (F + 0x28) ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (zo + 0x0) = v59 ∧
      memLoad32 M' (zo + 0x4) = v76 ∧
      memLoad32 M' (zo + 0x8) = v89 ∧
      memLoad32 M' (zo + 0xC) = v99 ∧
      memLoad32 M' (zo + 0x10) = v132 ∧
      memLoad32 M' (zo + 0x14) = v147 ∧
      memLoad32 M' (zo + 0x18) = v160 ∧
      memLoad32 M' (zo + 0x1C) = v165 ∧
      memLoad32 M' (zo + 0x20) = v204 ∧
      memLoad32 M' (zo + 0x24) = v218 ∧
      memLoad32 M' (zo + 0x28) = v238 ∧
      memLoad32 M' (zo + 0x2C) = v244 ∧
      memLoad32 M' (zo + 0x30) = v283 ∧
      memLoad32 M' (zo + 0x34) = v288 ∧
      aluEval .mul v3 v28 = v280 ∧
      aluEval .mul v19 v17 = v281 ∧
      aluEval .add v274 v276 = v282 ∧
      aluEval .add v272 v275 = v283 ∧
      aluEval .add v282 v255 = v284 ∧
      aluEval .sltu v283 v275 = v285 ∧
      aluEval .mul v6 v18 = v286 ∧
      aluEval .mul v13 v10 = v287 ∧
      aluEval .add v284 v285 = v288 ∧
      aluEval .mulhu v13 v10 = v289 ∧
      aluEval .add v278 v279 = v290 ∧
      aluEval .mul v4 v48 = v291 ∧
      aluEval .add v281 v280 = v292 ∧
      aluEval .add v290 v277 = v293 ∧
      aluEval .mulhu v4 v48 = v294 ∧
      aluEval .sltu v292 v280 = v295 ∧
      aluEval .add v293 v295 = v297 ∧
      aluEval .srl v287 0x1F = v298 ∧
      aluEval .add v286 v292 = v299 ∧
      aluEval .sll v289 0x1 = v300 ∧
      aluEval .sltu v299 v292 = v301 ∧
      aluEval .or v300 v298 = v302 ∧
      aluEval .add v301 v297 = v303 ∧
      aluEval .sll v287 0x1 = v304 ∧
      aluEval .add v291 v299 = v305 ∧
      aluEval .add v294 v303 = v306 ∧
      aluEval .sltu v305 v299 = v307 ∧
      aluEval .add v306 v307 = v308 ∧
      aluEval .add v304 v305 = v309 ∧
      aluEval .mulhu v6 v28 = v310 ∧
      aluEval .mulhu v17 v17 = v311 ∧
      aluEval .add v308 v302 = v313 ∧
      aluEval .sltu v309 v305 = v314 ∧
      aluEval .mulhu v64 v19 = v315 ∧
      aluEval .mul v6 v28 = v316 ∧
      aluEval .mul v17 v17 = v317 ∧
      aluEval .add v313 v314 = v318 ∧
      aluEval .mul v64 v19 = v319 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n280, v280, d280, hv280, u280⟩ := s.aluG hc fsq_at_38e (off' := 0x392) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv280
  obtain ⟨n281, v281, d281, hv281, u281⟩ := u280.aluG hc fsq_at_392 (off' := 0x396) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv281
  obtain ⟨n282, v282, d282, hv282, u282⟩ := u281.aluG hc fsq_at_396 (off' := 0x398) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv282
  obtain ⟨n283, v283, d283, hv283, u283⟩ := u282.aluG hc fsq_at_398 (off' := 0x39A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv283
  obtain ⟨n284, v284, d284, hv284, u284⟩ := u283.aluG hc fsq_at_39a (off' := 0x39C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv284
  obtain ⟨n285, v285, d285, hv285, u285⟩ := u284.aluG hc fsq_at_39c (off' := 0x3A0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv285
  obtain ⟨n286, v286, d286, hv286, u286⟩ := u285.aluG hc fsq_at_3a0 (off' := 0x3A4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv286
  obtain ⟨n287, v287, d287, hv287, u287⟩ := u286.aluG hc fsq_at_3a4 (off' := 0x3A8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv287
  obtain ⟨n288, v288, d288, hv288, u288⟩ := u287.aluG hc fsq_at_3a8 (off' := 0x3AC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv288
  obtain ⟨n289, v289, d289, hv289, u289⟩ := u288.aluG hc fsq_at_3ac (off' := 0x3B0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv289
  obtain ⟨n290, v290, d290, hv290, u290⟩ := u289.aluG hc fsq_at_3b0 (off' := 0x3B2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv290
  obtain ⟨n291, v291, d291, hv291, u291⟩ := u290.aluG hc fsq_at_3b2 (off' := 0x3B6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv291
  obtain ⟨n292, v292, d292, hv292, u292⟩ := u291.aluG hc fsq_at_3b6 (off' := 0x3B8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv292
  obtain ⟨n293, v293, d293, hv293, u293⟩ := u292.aluG hc fsq_at_3b8 (off' := 0x3BA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv293
  obtain ⟨n294, v294, d294, hv294, u294⟩ := u293.aluG hc fsq_at_3ba (off' := 0x3BE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv294
  obtain ⟨n295, v295, d295, hv295, u295⟩ := u294.aluG hc fsq_at_3be (off' := 0x3C2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv295
  obtain ⟨n296, d296, u296⟩ := u295.swG hc fsq_at_3c2 (off' := 0x3C6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 48) (by decide)) (a := zo + 0x30) (v := v283)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M296, hM296⟩ : ∃ M', memStore32 Mi (zo + 0x30) v283 = M' := ⟨_, rfl⟩
  rw [hM296] at u296
  have hc296 : CodeIn M296 B feSquareInnerCode := by rw [← hM296]; exact hc.store32 (frm_sep' sZC (by decide))
  have fr296 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M296 x = M0 x := fun x hxF hxZ => by
    rw [← hM296, memStore32_get_sep (frm_sep' hxZ (by decide)), fr x hxF hxZ]
  obtain ⟨n297, v297, d297, hv297, u297⟩ := u296.aluG hc296 fsq_at_3c6 (off' := 0x3C8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv297
  obtain ⟨n298, v298, d298, hv298, u298⟩ := u297.aluImmG hc296 fsq_at_3c8 (off' := 0x3CC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv298
  obtain ⟨n299, v299, d299, hv299, u299⟩ := u298.aluG hc296 fsq_at_3cc (off' := 0x3CE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv299
  obtain ⟨n300, v300, d300, hv300, u300⟩ := u299.aluImmG hc296 fsq_at_3ce (off' := 0x3D0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv300
  obtain ⟨n301, v301, d301, hv301, u301⟩ := u300.aluG hc296 fsq_at_3d0 (off' := 0x3D4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv301
  obtain ⟨n302, v302, d302, hv302, u302⟩ := u301.aluG hc296 fsq_at_3d4 (off' := 0x3D6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv302
  obtain ⟨n303, v303, d303, hv303, u303⟩ := u302.aluG hc296 fsq_at_3d6 (off' := 0x3D8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv303
  obtain ⟨n304, v304, d304, hv304, u304⟩ := u303.aluImmG hc296 fsq_at_3d8 (off' := 0x3DA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv304
  obtain ⟨n305, v305, d305, hv305, u305⟩ := u304.aluG hc296 fsq_at_3da (off' := 0x3DC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv305
  obtain ⟨n306, v306, d306, hv306, u306⟩ := u305.aluG hc296 fsq_at_3dc (off' := 0x3DE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv306
  obtain ⟨n307, v307, d307, hv307, u307⟩ := u306.aluG hc296 fsq_at_3de (off' := 0x3E2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv307
  obtain ⟨n308, v308, d308, hv308, u308⟩ := u307.aluG hc296 fsq_at_3e2 (off' := 0x3E4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv308
  obtain ⟨n309, v309, d309, hv309, u309⟩ := u308.aluG hc296 fsq_at_3e4 (off' := 0x3E6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv309
  obtain ⟨n310, v310, d310, hv310, u310⟩ := u309.aluG hc296 fsq_at_3e6 (off' := 0x3EA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv310
  obtain ⟨n311, v311, d311, hv311, u311⟩ := u310.aluG hc296 fsq_at_3ea (off' := 0x3EE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv311
  obtain ⟨n312, d312, u312⟩ := u311.swG hc296 fsq_at_3ee (off' := 0x3F2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 52) (by decide)) (a := zo + 0x34) (v := v288)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M312, hM312⟩ : ∃ M', memStore32 M296 (zo + 0x34) v288 = M' := ⟨_, rfl⟩
  rw [hM312] at u312
  have hc312 : CodeIn M312 B feSquareInnerCode := by rw [← hM312]; exact hc296.store32 (frm_sep' sZC (by decide))
  have fr312 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M312 x = M0 x := fun x hxF hxZ => by
    rw [← hM312, memStore32_get_sep (frm_sep' hxZ (by decide)), fr296 x hxF hxZ]
  obtain ⟨n313, v313, d313, hv313, u313⟩ := u312.aluG hc312 fsq_at_3f2 (off' := 0x3F4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv313
  obtain ⟨n314, v314, d314, hv314, u314⟩ := u313.aluG hc312 fsq_at_3f4 (off' := 0x3F8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv314
  obtain ⟨n315, v315, d315, hv315, u315⟩ := u314.aluG hc312 fsq_at_3f8 (off' := 0x3FC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv315
  obtain ⟨n316, v316, d316, hv316, u316⟩ := u315.aluG hc312 fsq_at_3fc (off' := 0x400) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv316
  obtain ⟨n317, v317, d317, hv317, u317⟩ := u316.aluG hc312 fsq_at_400 (off' := 0x404) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv317
  obtain ⟨n318, v318, d318, hv318, u318⟩ := u317.aluG hc312 fsq_at_404 (off' := 0x406) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv318
  obtain ⟨n319, v319, d319, hv319, u319⟩ := u318.aluG hc312 fsq_at_406 (off' := 0x40A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv319
  have qo1 : reg n319 ra = v3 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n319 sp = F := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n319 (3 : Fin 32) = G3 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n319 (4 : Fin 32) = G4 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n319 (5 : Fin 32) = v48 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n319 (6 : Fin 32) = zo := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n319 (7 : Fin 32) = v288 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n319 (8 : Fin 32) = v317 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n319 (9 : Fin 32) = v309 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n319 a0 = v318 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n319 a1 = v319 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n319 a2 = v310 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n319 a3 = v311 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n319 a4 = v315 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n319 a5 = v316 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n319 a6 = v277 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n319 a7 = v299 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n319 (18 : Fin 32) = v13 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n319 (19 : Fin 32) = v17 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n319 (20 : Fin 32) = v217 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n319 (21 : Fin 32) = v208 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n319 (22 : Fin 32) = v10 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n319 (23 : Fin 32) = v18 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n319 (24 : Fin 32) = v21 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n319 (25 : Fin 32) = v221 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n319 (26 : Fin 32) = v4 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n319 (27 : Fin 32) = v30 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n319 (28 : Fin 32) = v28 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n319 (29 : Fin 32) = v6 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n319 (30 : Fin 32) = v64 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n319 (31 : Fin 32) = v19 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so18 : memLoad32 M312 (F + 0x18) = v1 := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 52) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 48) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), sl18]
  have so1C : memLoad32 M312 (F + 0x1C) = memLoad32 M0 (F + 0x1C) := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 52) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 48) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), sl1C]
  have so20 : memLoad32 M312 (F + 0x20) = memLoad32 M0 (F + 0x20) := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 52) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 48) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), sl20]
  have so24 : memLoad32 M312 (F + 0x24) = memLoad32 M0 (F + 0x24) := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 52) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 48) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), sl24]
  have so28 : memLoad32 M312 (F + 0x28) = memLoad32 M0 (F + 0x28) := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 52) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 48) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), sl28]
  have so2C : memLoad32 M312 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 52) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 48) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), sl2C]
  have so30 : memLoad32 M312 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 52) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 48) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), sl30]
  have so34 : memLoad32 M312 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 52) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 48) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), sl34]
  have so38 : memLoad32 M312 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 52) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 48) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), sl38]
  have so3C : memLoad32 M312 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 52) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 48) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), sl3C]
  have so40 : memLoad32 M312 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 52) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 48) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), sl40]
  have so44 : memLoad32 M312 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 52) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 48) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), sl44]
  have so48 : memLoad32 M312 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 52) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 48) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), sl48]
  have so4C : memLoad32 M312 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 52) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 48) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), sl4C]
  have sozo0 : memLoad32 M312 (zo + 0x0) = v59 := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (zo + 0x0) 4 from sep_offsets zo (c := 52) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (zo + 0x0) 4 from sep_offsets zo (c := 48) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), slzo0]
  have sozo4 : memLoad32 M312 (zo + 0x4) = v76 := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (zo + 0x4) 4 from sep_offsets zo (c := 52) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (zo + 0x4) 4 from sep_offsets zo (c := 48) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), slzo4]
  have sozo8 : memLoad32 M312 (zo + 0x8) = v89 := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (zo + 0x8) 4 from sep_offsets zo (c := 52) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (zo + 0x8) 4 from sep_offsets zo (c := 48) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), slzo8]
  have sozoC : memLoad32 M312 (zo + 0xC) = v99 := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (zo + 0xC) 4 from sep_offsets zo (c := 52) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (zo + 0xC) 4 from sep_offsets zo (c := 48) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slzoC]
  have sozo10 : memLoad32 M312 (zo + 0x10) = v132 := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (zo + 0x10) 4 from sep_offsets zo (c := 52) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (zo + 0x10) 4 from sep_offsets zo (c := 48) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), slzo10]
  have sozo14 : memLoad32 M312 (zo + 0x14) = v147 := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (zo + 0x14) 4 from sep_offsets zo (c := 52) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (zo + 0x14) 4 from sep_offsets zo (c := 48) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), slzo14]
  have sozo18 : memLoad32 M312 (zo + 0x18) = v160 := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (zo + 0x18) 4 from sep_offsets zo (c := 52) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (zo + 0x18) 4 from sep_offsets zo (c := 48) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), slzo18]
  have sozo1C : memLoad32 M312 (zo + 0x1C) = v165 := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (zo + 0x1C) 4 from sep_offsets zo (c := 52) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (zo + 0x1C) 4 from sep_offsets zo (c := 48) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), slzo1C]
  have sozo20 : memLoad32 M312 (zo + 0x20) = v204 := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (zo + 0x20) 4 from sep_offsets zo (c := 52) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (zo + 0x20) 4 from sep_offsets zo (c := 48) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), slzo20]
  have sozo24 : memLoad32 M312 (zo + 0x24) = v218 := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (zo + 0x24) 4 from sep_offsets zo (c := 52) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (zo + 0x24) 4 from sep_offsets zo (c := 48) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), slzo24]
  have sozo28 : memLoad32 M312 (zo + 0x28) = v238 := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (zo + 0x28) 4 from sep_offsets zo (c := 52) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (zo + 0x28) 4 from sep_offsets zo (c := 48) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), slzo28]
  have sozo2C : memLoad32 M312 (zo + 0x2C) = v244 := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (zo + 0x2C) 4 from sep_offsets zo (c := 52) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), ← hM296, memLoad32_store32_sep (show Sep (zo + 0x30) 4 (zo + 0x2C) 4 from sep_offsets zo (c := 48) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), slzo2C]
  have sozo30 : memLoad32 M312 (zo + 0x30) = v283 := by
    rw [← hM312, memLoad32_store32_sep (show Sep (zo + 0x34) 4 (zo + 0x30) 4 from sep_offsets zo (c := 52) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), ← hM296, memLoad32_store32_same]
  have sozo34 : memLoad32 M312 (zo + 0x34) = v288 := by
    rw [← hM312, memLoad32_store32_same]
  exact ⟨n319, M312, v280, v281, v282, v283, v284, v285, v286, v287, v288, v289, v290, v291, v292, v293, v294, v295, v297, v298, v299, v300, v301, v302, v303, v304, v305, v306, v307, v308, v309, v310, v311, v313, v314, v315, v316, v317, v318, v319, (.cons d280 (.cons d281 (.cons d282 (.cons d283 (.cons d284 (.cons d285 (.cons d286 (.cons d287 (.cons d288 (.cons d289 (.cons d290 (.cons d291 (.cons d292 (.cons d293 (.cons d294 (.cons d295 (.cons d296 (.cons d297 (.cons d298 (.cons d299 (.cons d300 (.cons d301 (.cons d302 (.cons d303 (.cons d304 (.cons d305 (.cons d306 (.cons d307 (.cons d308 (.cons d309 (.cons d310 (.cons d311 (.cons d312 (.cons d313 (.cons d314 (.cons d315 (.cons d316 (.cons d317 (.cons d318 (.single d319)))))))))))))))))))))))))))))))))))))))), u319.self, hc312, fr312, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so18, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, sozo0, sozo4, sozo8, sozoC, sozo10, sozo14, sozo18, sozo1C, sozo20, sozo24, sozo28, sozo2C, sozo30, sozo34, hv280, hv281, hv282, hv283, hv284, hv285, hv286, hv287, hv288, hv289, hv290, hv291, hv292, hv293, hv294, hv295, hv297, hv298, hv299, hv300, hv301, hv302, hv303, hv304, hv305, hv306, hv307, hv308, hv309, hv310, hv311, hv313, hv314, hv315, hv316, hv317, hv318, hv319⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem fsq_g8 {M0 Mi : Word → BitVec 8} {B F zo xp G3 G4 : Word} {n : Machine} {v1 v3 v4 v6 v10 v13 v17 v18 v19 v21 v28 v30 v48 v59 v64 v76 v89 v99 v132 v147 v160 v165 v204 v208 v217 v218 v221 v238 v244 v277 v283 v288 v299 v309 v310 v311 v315 v316 v317 v318 v319 : Word}
    (s : St Mi B n 0x40A (reg n)) (hc : CodeIn Mi B feSquareInnerCode)
    (fr : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hZ : zo.toNat % 4 = 0) (hx : xp.toNat % 4 = 0)
    (sFC : Sep F 0x50 B feSquareInnerCode.length) (sZC : Sep zo 0x50 B feSquareInnerCode.length)
    (sXF : Sep xp 40 F 0x50) (sXZ : Sep xp 40 zo 0x50) (sFZ : Sep F 0x50 zo 0x50)
    (q1 : reg n ra = v3)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v48)
    (q6 : reg n (6 : Fin 32) = zo)
    (q7 : reg n (7 : Fin 32) = v288)
    (q8 : reg n (8 : Fin 32) = v317)
    (q9 : reg n (9 : Fin 32) = v309)
    (q10 : reg n a0 = v318)
    (q11 : reg n a1 = v319)
    (q12 : reg n a2 = v310)
    (q13 : reg n a3 = v311)
    (q14 : reg n a4 = v315)
    (q15 : reg n a5 = v316)
    (q16 : reg n a6 = v277)
    (q17 : reg n a7 = v299)
    (q18 : reg n (18 : Fin 32) = v13)
    (q19 : reg n (19 : Fin 32) = v17)
    (q20 : reg n (20 : Fin 32) = v217)
    (q21 : reg n (21 : Fin 32) = v208)
    (q22 : reg n (22 : Fin 32) = v10)
    (q23 : reg n (23 : Fin 32) = v18)
    (q24 : reg n (24 : Fin 32) = v21)
    (q25 : reg n (25 : Fin 32) = v221)
    (q26 : reg n (26 : Fin 32) = v4)
    (q27 : reg n (27 : Fin 32) = v30)
    (q28 : reg n (28 : Fin 32) = v28)
    (q29 : reg n (29 : Fin 32) = v6)
    (q30 : reg n (30 : Fin 32) = v64)
    (q31 : reg n (31 : Fin 32) = v19)
    (sl18 : memLoad32 Mi (F + 0x18) = v1)
    (sl1C : memLoad32 Mi (F + 0x1C) = memLoad32 M0 (F + 0x1C))
    (sl20 : memLoad32 Mi (F + 0x20) = memLoad32 M0 (F + 0x20))
    (sl24 : memLoad32 Mi (F + 0x24) = memLoad32 M0 (F + 0x24))
    (sl28 : memLoad32 Mi (F + 0x28) = memLoad32 M0 (F + 0x28))
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    (slzo0 : memLoad32 Mi (zo + 0x0) = v59)
    (slzo4 : memLoad32 Mi (zo + 0x4) = v76)
    (slzo8 : memLoad32 Mi (zo + 0x8) = v89)
    (slzoC : memLoad32 Mi (zo + 0xC) = v99)
    (slzo10 : memLoad32 Mi (zo + 0x10) = v132)
    (slzo14 : memLoad32 Mi (zo + 0x14) = v147)
    (slzo18 : memLoad32 Mi (zo + 0x18) = v160)
    (slzo1C : memLoad32 Mi (zo + 0x1C) = v165)
    (slzo20 : memLoad32 Mi (zo + 0x20) = v204)
    (slzo24 : memLoad32 Mi (zo + 0x24) = v218)
    (slzo28 : memLoad32 Mi (zo + 0x28) = v238)
    (slzo2C : memLoad32 Mi (zo + 0x2C) = v244)
    (slzo30 : memLoad32 Mi (zo + 0x30) = v283)
    (slzo34 : memLoad32 Mi (zo + 0x34) = v288)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v322 v323 v324 v325 v326 v328 v329 v330 v331 v332 v333 v334 v335 v336 v337 v338 v339 v340 v341 v342 v343 v344 v345 v346 v347 v348 v349 v350 v351 v352 v353 v354 v355 v356 v357 v358 v359 : Word),
      Steps n n' ∧
      St M' B n' 0x48E (reg n') ∧
      CodeIn M' B feSquareInnerCode ∧
      (∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M' x = M0 x) ∧
      reg n' ra = v3 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v357 ∧
      reg n' (6 : Fin 32) = zo ∧
      reg n' (7 : Fin 32) = v354 ∧
      reg n' (8 : Fin 32) = v348 ∧
      reg n' (9 : Fin 32) = v347 ∧
      reg n' a0 = v358 ∧
      reg n' a1 = v351 ∧
      reg n' a2 = v350 ∧
      reg n' a3 = v345 ∧
      reg n' a4 = v359 ∧
      reg n' a5 = v349 ∧
      reg n' a6 = v328 ∧
      reg n' a7 = v355 ∧
      reg n' (18 : Fin 32) = v13 ∧
      reg n' (19 : Fin 32) = v17 ∧
      reg n' (20 : Fin 32) = v217 ∧
      reg n' (21 : Fin 32) = v208 ∧
      reg n' (22 : Fin 32) = v10 ∧
      reg n' (23 : Fin 32) = v18 ∧
      reg n' (24 : Fin 32) = v21 ∧
      reg n' (25 : Fin 32) = v221 ∧
      reg n' (26 : Fin 32) = v4 ∧
      reg n' (27 : Fin 32) = v30 ∧
      reg n' (28 : Fin 32) = v356 ∧
      reg n' (29 : Fin 32) = v6 ∧
      reg n' (30 : Fin 32) = v1 ∧
      reg n' (31 : Fin 32) = v19 ∧
      memLoad32 M' (F + 0x1C) = memLoad32 M0 (F + 0x1C) ∧
      memLoad32 M' (F + 0x20) = memLoad32 M0 (F + 0x20) ∧
      memLoad32 M' (F + 0x24) = memLoad32 M0 (F + 0x24) ∧
      memLoad32 M' (F + 0x28) = memLoad32 M0 (F + 0x28) ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (zo + 0x0) = v59 ∧
      memLoad32 M' (zo + 0x4) = v76 ∧
      memLoad32 M' (zo + 0x8) = v89 ∧
      memLoad32 M' (zo + 0xC) = v99 ∧
      memLoad32 M' (zo + 0x10) = v132 ∧
      memLoad32 M' (zo + 0x14) = v147 ∧
      memLoad32 M' (zo + 0x18) = v160 ∧
      memLoad32 M' (zo + 0x1C) = v165 ∧
      memLoad32 M' (zo + 0x20) = v204 ∧
      memLoad32 M' (zo + 0x24) = v218 ∧
      memLoad32 M' (zo + 0x28) = v238 ∧
      memLoad32 M' (zo + 0x2C) = v244 ∧
      memLoad32 M' (zo + 0x30) = v283 ∧
      memLoad32 M' (zo + 0x34) = v288 ∧
      memLoad32 M' (zo + 0x38) = v309 ∧
      memLoad32 M' (zo + 0x3C) = v318 ∧
      aluEval .mul v217 v18 = v322 ∧
      aluEval .add v310 v311 = v323 ∧
      aluEval .mulhu v13 v48 = v324 ∧
      aluEval .mulhu v217 v18 = v325 ∧
      aluEval .add v315 v323 = v326 ∧
      aluEval .mul v1 v10 = v328 ∧
      aluEval .mulhu v1 v10 = v329 ∧
      aluEval .add v317 v316 = v330 ∧
      aluEval .sltu v330 v316 = v331 ∧
      aluEval .add v319 v330 = v332 ∧
      aluEval .add v326 v331 = v333 ∧
      aluEval .sltu v332 v330 = v334 ∧
      aluEval .add v333 v334 = v335 ∧
      aluEval .add v332 v322 = v336 ∧
      aluEval .mul v13 v48 = v337 ∧
      aluEval .sltu v336 v332 = v338 ∧
      aluEval .add v335 v325 = v339 ∧
      aluEval .add v338 v324 = v340 ∧
      aluEval .srl v328 0x1F = v341 ∧
      aluEval .sll v329 0x1 = v342 ∧
      aluEval .or v342 v341 = v343 ∧
      aluEval .add v339 v340 = v344 ∧
      aluEval .mul v6 v19 = v345 ∧
      aluEval .mulhu v6 v19 = v346 ∧
      aluEval .mul v30 v3 = v347 ∧
      aluEval .mulhu v30 v3 = v348 ∧
      aluEval .add v337 v336 = v349 ∧
      aluEval .mulhu v4 v28 = v350 ∧
      aluEval .mul v4 v28 = v351 ∧
      aluEval .sltu v349 v336 = v352 ∧
      aluEval .add v352 v344 = v353 ∧
      aluEval .mul v13 v18 = v354 ∧
      aluEval .add v343 v353 = v355 ∧
      aluEval .mul v1 v48 = v356 ∧
      aluEval .mulhu v1 v48 = v357 ∧
      aluEval .mulhu v13 v18 = v358 ∧
      aluEval .add v346 v348 = v359 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n320, d320, u320⟩ := s.swG hc fsq_at_40a (off' := 0x40E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 56) (by decide)) (a := zo + 0x38) (v := v309)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M320, hM320⟩ : ∃ M', memStore32 Mi (zo + 0x38) v309 = M' := ⟨_, rfl⟩
  rw [hM320] at u320
  have hc320 : CodeIn M320 B feSquareInnerCode := by rw [← hM320]; exact hc.store32 (frm_sep' sZC (by decide))
  have fr320 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M320 x = M0 x := fun x hxF hxZ => by
    rw [← hM320, memStore32_get_sep (frm_sep' hxZ (by decide)), fr x hxF hxZ]
  obtain ⟨n321, d321, u321⟩ := u320.swG hc320 fsq_at_40e (off' := 0x412) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 60) (by decide)) (a := zo + 0x3C) (v := v318)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M321, hM321⟩ : ∃ M', memStore32 M320 (zo + 0x3C) v318 = M' := ⟨_, rfl⟩
  rw [hM321] at u321
  have hc321 : CodeIn M321 B feSquareInnerCode := by rw [← hM321]; exact hc320.store32 (frm_sep' sZC (by decide))
  have fr321 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M321 x = M0 x := fun x hxF hxZ => by
    rw [← hM321, memStore32_get_sep (frm_sep' hxZ (by decide)), fr320 x hxF hxZ]
  obtain ⟨n322, v322, d322, hv322, u322⟩ := u321.aluG hc321 fsq_at_412 (off' := 0x416) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv322
  obtain ⟨n323, v323, d323, hv323, u323⟩ := u322.aluG hc321 fsq_at_416 (off' := 0x418) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv323
  obtain ⟨n324, v324, d324, hv324, u324⟩ := u323.aluG hc321 fsq_at_418 (off' := 0x41C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv324
  obtain ⟨n325, v325, d325, hv325, u325⟩ := u324.aluG hc321 fsq_at_41c (off' := 0x420) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv325
  obtain ⟨n326, v326, d326, hv326, u326⟩ := u325.aluG hc321 fsq_at_420 (off' := 0x422) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv326
  obtain ⟨n327, d327, u327⟩ := u326.lwE hc321 fsq_at_422 (off' := 0x424) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 24) (by decide)) (v := v1)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 60) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (F + 0x18) 4 from (sFZ.symm.sub (c := 56) (l := 4) (by decide)).subR (c := 24) (l := 4) (by decide)), sl18])
  obtain ⟨n328, v328, d328, hv328, u328⟩ := u327.aluG hc321 fsq_at_424 (off' := 0x428) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv328
  obtain ⟨n329, v329, d329, hv329, u329⟩ := u328.aluG hc321 fsq_at_428 (off' := 0x42C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv329
  obtain ⟨n330, v330, d330, hv330, u330⟩ := u329.aluG hc321 fsq_at_42c (off' := 0x42E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv330
  obtain ⟨n331, v331, d331, hv331, u331⟩ := u330.aluG hc321 fsq_at_42e (off' := 0x432) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv331
  obtain ⟨n332, v332, d332, hv332, u332⟩ := u331.aluG hc321 fsq_at_432 (off' := 0x434) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv332
  obtain ⟨n333, v333, d333, hv333, u333⟩ := u332.aluG hc321 fsq_at_434 (off' := 0x436) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv333
  obtain ⟨n334, v334, d334, hv334, u334⟩ := u333.aluG hc321 fsq_at_436 (off' := 0x43A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv334
  obtain ⟨n335, v335, d335, hv335, u335⟩ := u334.aluG hc321 fsq_at_43a (off' := 0x43C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv335
  obtain ⟨n336, v336, d336, hv336, u336⟩ := u335.aluG hc321 fsq_at_43c (off' := 0x440) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv336
  obtain ⟨n337, v337, d337, hv337, u337⟩ := u336.aluG hc321 fsq_at_440 (off' := 0x444) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv337
  obtain ⟨n338, v338, d338, hv338, u338⟩ := u337.aluG hc321 fsq_at_444 (off' := 0x448) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv338
  obtain ⟨n339, v339, d339, hv339, u339⟩ := u338.aluG hc321 fsq_at_448 (off' := 0x44A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv339
  obtain ⟨n340, v340, d340, hv340, u340⟩ := u339.aluG hc321 fsq_at_44a (off' := 0x44C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv340
  obtain ⟨n341, v341, d341, hv341, u341⟩ := u340.aluImmG hc321 fsq_at_44c (off' := 0x450) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv341
  obtain ⟨n342, v342, d342, hv342, u342⟩ := u341.aluImmG hc321 fsq_at_450 (off' := 0x452) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv342
  obtain ⟨n343, v343, d343, hv343, u343⟩ := u342.aluG hc321 fsq_at_452 (off' := 0x456) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv343
  obtain ⟨n344, v344, d344, hv344, u344⟩ := u343.aluG hc321 fsq_at_456 (off' := 0x45A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv344
  obtain ⟨n345, v345, d345, hv345, u345⟩ := u344.aluG hc321 fsq_at_45a (off' := 0x45E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv345
  obtain ⟨n346, v346, d346, hv346, u346⟩ := u345.aluG hc321 fsq_at_45e (off' := 0x462) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv346
  obtain ⟨n347, v347, d347, hv347, u347⟩ := u346.aluG hc321 fsq_at_462 (off' := 0x466) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv347
  obtain ⟨n348, v348, d348, hv348, u348⟩ := u347.aluG hc321 fsq_at_466 (off' := 0x46A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv348
  obtain ⟨n349, v349, d349, hv349, u349⟩ := u348.aluG hc321 fsq_at_46a (off' := 0x46C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv349
  obtain ⟨n350, v350, d350, hv350, u350⟩ := u349.aluG hc321 fsq_at_46c (off' := 0x470) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv350
  obtain ⟨n351, v351, d351, hv351, u351⟩ := u350.aluG hc321 fsq_at_470 (off' := 0x474) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv351
  obtain ⟨n352, v352, d352, hv352, u352⟩ := u351.aluG hc321 fsq_at_474 (off' := 0x478) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv352
  obtain ⟨n353, v353, d353, hv353, u353⟩ := u352.aluG hc321 fsq_at_478 (off' := 0x47A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv353
  obtain ⟨n354, v354, d354, hv354, u354⟩ := u353.aluG hc321 fsq_at_47a (off' := 0x47E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv354
  obtain ⟨n355, v355, d355, hv355, u355⟩ := u354.aluG hc321 fsq_at_47e (off' := 0x480) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv355
  obtain ⟨n356, v356, d356, hv356, u356⟩ := u355.aluG hc321 fsq_at_480 (off' := 0x484) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv356
  obtain ⟨n357, v357, d357, hv357, u357⟩ := u356.aluG hc321 fsq_at_484 (off' := 0x488) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv357
  obtain ⟨n358, v358, d358, hv358, u358⟩ := u357.aluG hc321 fsq_at_488 (off' := 0x48C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv358
  obtain ⟨n359, v359, d359, hv359, u359⟩ := u358.aluG hc321 fsq_at_48c (off' := 0x48E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv359
  have qo1 : reg n359 ra = v3 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n359 sp = F := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n359 (3 : Fin 32) = G3 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n359 (4 : Fin 32) = G4 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n359 (5 : Fin 32) = v357 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n359 (6 : Fin 32) = zo := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n359 (7 : Fin 32) = v354 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n359 (8 : Fin 32) = v348 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n359 (9 : Fin 32) = v347 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n359 a0 = v358 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n359 a1 = v351 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n359 a2 = v350 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n359 a3 = v345 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n359 a4 = v359 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n359 a5 = v349 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n359 a6 = v328 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n359 a7 = v355 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n359 (18 : Fin 32) = v13 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n359 (19 : Fin 32) = v17 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n359 (20 : Fin 32) = v217 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n359 (21 : Fin 32) = v208 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n359 (22 : Fin 32) = v10 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n359 (23 : Fin 32) = v18 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n359 (24 : Fin 32) = v21 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n359 (25 : Fin 32) = v221 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n359 (26 : Fin 32) = v4 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n359 (27 : Fin 32) = v30 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n359 (28 : Fin 32) = v356 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n359 (29 : Fin 32) = v6 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n359 (30 : Fin 32) = v1 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n359 (31 : Fin 32) = v19 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so1C : memLoad32 M321 (F + 0x1C) = memLoad32 M0 (F + 0x1C) := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 60) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 56) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), sl1C]
  have so20 : memLoad32 M321 (F + 0x20) = memLoad32 M0 (F + 0x20) := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 60) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 56) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), sl20]
  have so24 : memLoad32 M321 (F + 0x24) = memLoad32 M0 (F + 0x24) := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 60) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 56) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), sl24]
  have so28 : memLoad32 M321 (F + 0x28) = memLoad32 M0 (F + 0x28) := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 60) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 56) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), sl28]
  have so2C : memLoad32 M321 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 60) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 56) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), sl2C]
  have so30 : memLoad32 M321 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 60) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 56) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), sl30]
  have so34 : memLoad32 M321 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 60) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 56) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), sl34]
  have so38 : memLoad32 M321 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 60) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 56) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), sl38]
  have so3C : memLoad32 M321 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 60) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 56) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), sl3C]
  have so40 : memLoad32 M321 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 60) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 56) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), sl40]
  have so44 : memLoad32 M321 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 60) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 56) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), sl44]
  have so48 : memLoad32 M321 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 60) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 56) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), sl48]
  have so4C : memLoad32 M321 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 60) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 56) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), sl4C]
  have sozo0 : memLoad32 M321 (zo + 0x0) = v59 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0x0) 4 from sep_offsets zo (c := 60) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (zo + 0x0) 4 from sep_offsets zo (c := 56) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), slzo0]
  have sozo4 : memLoad32 M321 (zo + 0x4) = v76 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0x4) 4 from sep_offsets zo (c := 60) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (zo + 0x4) 4 from sep_offsets zo (c := 56) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), slzo4]
  have sozo8 : memLoad32 M321 (zo + 0x8) = v89 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0x8) 4 from sep_offsets zo (c := 60) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (zo + 0x8) 4 from sep_offsets zo (c := 56) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), slzo8]
  have sozoC : memLoad32 M321 (zo + 0xC) = v99 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0xC) 4 from sep_offsets zo (c := 60) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (zo + 0xC) 4 from sep_offsets zo (c := 56) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slzoC]
  have sozo10 : memLoad32 M321 (zo + 0x10) = v132 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0x10) 4 from sep_offsets zo (c := 60) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (zo + 0x10) 4 from sep_offsets zo (c := 56) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), slzo10]
  have sozo14 : memLoad32 M321 (zo + 0x14) = v147 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0x14) 4 from sep_offsets zo (c := 60) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (zo + 0x14) 4 from sep_offsets zo (c := 56) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), slzo14]
  have sozo18 : memLoad32 M321 (zo + 0x18) = v160 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0x18) 4 from sep_offsets zo (c := 60) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (zo + 0x18) 4 from sep_offsets zo (c := 56) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), slzo18]
  have sozo1C : memLoad32 M321 (zo + 0x1C) = v165 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0x1C) 4 from sep_offsets zo (c := 60) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (zo + 0x1C) 4 from sep_offsets zo (c := 56) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), slzo1C]
  have sozo20 : memLoad32 M321 (zo + 0x20) = v204 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0x20) 4 from sep_offsets zo (c := 60) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (zo + 0x20) 4 from sep_offsets zo (c := 56) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), slzo20]
  have sozo24 : memLoad32 M321 (zo + 0x24) = v218 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0x24) 4 from sep_offsets zo (c := 60) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (zo + 0x24) 4 from sep_offsets zo (c := 56) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), slzo24]
  have sozo28 : memLoad32 M321 (zo + 0x28) = v238 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0x28) 4 from sep_offsets zo (c := 60) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (zo + 0x28) 4 from sep_offsets zo (c := 56) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), slzo28]
  have sozo2C : memLoad32 M321 (zo + 0x2C) = v244 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0x2C) 4 from sep_offsets zo (c := 60) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (zo + 0x2C) 4 from sep_offsets zo (c := 56) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), slzo2C]
  have sozo30 : memLoad32 M321 (zo + 0x30) = v283 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0x30) 4 from sep_offsets zo (c := 60) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (zo + 0x30) 4 from sep_offsets zo (c := 56) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), slzo30]
  have sozo34 : memLoad32 M321 (zo + 0x34) = v288 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0x34) 4 from sep_offsets zo (c := 60) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_sep (show Sep (zo + 0x38) 4 (zo + 0x34) 4 from sep_offsets zo (c := 56) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), slzo34]
  have sozo38 : memLoad32 M321 (zo + 0x38) = v309 := by
    rw [← hM321, memLoad32_store32_sep (show Sep (zo + 0x3C) 4 (zo + 0x38) 4 from sep_offsets zo (c := 60) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), ← hM320, memLoad32_store32_same]
  have sozo3C : memLoad32 M321 (zo + 0x3C) = v318 := by
    rw [← hM321, memLoad32_store32_same]
  exact ⟨n359, M321, v322, v323, v324, v325, v326, v328, v329, v330, v331, v332, v333, v334, v335, v336, v337, v338, v339, v340, v341, v342, v343, v344, v345, v346, v347, v348, v349, v350, v351, v352, v353, v354, v355, v356, v357, v358, v359, (.cons d320 (.cons d321 (.cons d322 (.cons d323 (.cons d324 (.cons d325 (.cons d326 (.cons d327 (.cons d328 (.cons d329 (.cons d330 (.cons d331 (.cons d332 (.cons d333 (.cons d334 (.cons d335 (.cons d336 (.cons d337 (.cons d338 (.cons d339 (.cons d340 (.cons d341 (.cons d342 (.cons d343 (.cons d344 (.cons d345 (.cons d346 (.cons d347 (.cons d348 (.cons d349 (.cons d350 (.cons d351 (.cons d352 (.cons d353 (.cons d354 (.cons d355 (.cons d356 (.cons d357 (.cons d358 (.single d359)))))))))))))))))))))))))))))))))))))))), u359.self, hc321, fr321, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, sozo0, sozo4, sozo8, sozoC, sozo10, sozo14, sozo18, sozo1C, sozo20, sozo24, sozo28, sozo2C, sozo30, sozo34, sozo38, sozo3C, hv322, hv323, hv324, hv325, hv326, hv328, hv329, hv330, hv331, hv332, hv333, hv334, hv335, hv336, hv337, hv338, hv339, hv340, hv341, hv342, hv343, hv344, hv345, hv346, hv347, hv348, hv349, hv350, hv351, hv352, hv353, hv354, hv355, hv356, hv357, hv358, hv359⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem fsq_g9 {M0 Mi : Word → BitVec 8} {B F zo xp G3 G4 : Word} {n : Machine} {v1 v3 v4 v6 v10 v13 v17 v18 v19 v21 v30 v59 v76 v89 v99 v132 v147 v160 v165 v204 v208 v217 v218 v221 v238 v244 v283 v288 v309 v318 v328 v345 v347 v348 v349 v350 v351 v354 v355 v356 v357 v358 v359 : Word}
    (s : St Mi B n 0x48E (reg n)) (hc : CodeIn Mi B feSquareInnerCode)
    (fr : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hZ : zo.toNat % 4 = 0) (hx : xp.toNat % 4 = 0)
    (sFC : Sep F 0x50 B feSquareInnerCode.length) (sZC : Sep zo 0x50 B feSquareInnerCode.length)
    (sXF : Sep xp 40 F 0x50) (sXZ : Sep xp 40 zo 0x50) (sFZ : Sep F 0x50 zo 0x50)
    (q1 : reg n ra = v3)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v357)
    (q6 : reg n (6 : Fin 32) = zo)
    (q7 : reg n (7 : Fin 32) = v354)
    (q8 : reg n (8 : Fin 32) = v348)
    (q9 : reg n (9 : Fin 32) = v347)
    (q10 : reg n a0 = v358)
    (q11 : reg n a1 = v351)
    (q12 : reg n a2 = v350)
    (q13 : reg n a3 = v345)
    (q14 : reg n a4 = v359)
    (q15 : reg n a5 = v349)
    (q16 : reg n a6 = v328)
    (q17 : reg n a7 = v355)
    (q18 : reg n (18 : Fin 32) = v13)
    (q19 : reg n (19 : Fin 32) = v17)
    (q20 : reg n (20 : Fin 32) = v217)
    (q21 : reg n (21 : Fin 32) = v208)
    (q22 : reg n (22 : Fin 32) = v10)
    (q23 : reg n (23 : Fin 32) = v18)
    (q24 : reg n (24 : Fin 32) = v21)
    (q25 : reg n (25 : Fin 32) = v221)
    (q26 : reg n (26 : Fin 32) = v4)
    (q27 : reg n (27 : Fin 32) = v30)
    (q28 : reg n (28 : Fin 32) = v356)
    (q29 : reg n (29 : Fin 32) = v6)
    (q30 : reg n (30 : Fin 32) = v1)
    (q31 : reg n (31 : Fin 32) = v19)
    (sl1C : memLoad32 Mi (F + 0x1C) = memLoad32 M0 (F + 0x1C))
    (sl20 : memLoad32 Mi (F + 0x20) = memLoad32 M0 (F + 0x20))
    (sl24 : memLoad32 Mi (F + 0x24) = memLoad32 M0 (F + 0x24))
    (sl28 : memLoad32 Mi (F + 0x28) = memLoad32 M0 (F + 0x28))
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    (slzo0 : memLoad32 Mi (zo + 0x0) = v59)
    (slzo4 : memLoad32 Mi (zo + 0x4) = v76)
    (slzo8 : memLoad32 Mi (zo + 0x8) = v89)
    (slzoC : memLoad32 Mi (zo + 0xC) = v99)
    (slzo10 : memLoad32 Mi (zo + 0x10) = v132)
    (slzo14 : memLoad32 Mi (zo + 0x14) = v147)
    (slzo18 : memLoad32 Mi (zo + 0x18) = v160)
    (slzo1C : memLoad32 Mi (zo + 0x1C) = v165)
    (slzo20 : memLoad32 Mi (zo + 0x20) = v204)
    (slzo24 : memLoad32 Mi (zo + 0x24) = v218)
    (slzo28 : memLoad32 Mi (zo + 0x28) = v238)
    (slzo2C : memLoad32 Mi (zo + 0x2C) = v244)
    (slzo30 : memLoad32 Mi (zo + 0x30) = v283)
    (slzo34 : memLoad32 Mi (zo + 0x34) = v288)
    (slzo38 : memLoad32 Mi (zo + 0x38) = v309)
    (slzo3C : memLoad32 Mi (zo + 0x3C) = v318)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v360 v361 v362 v363 v364 v365 v366 v367 v368 v369 v370 v371 v372 v373 v374 v375 v376 v377 v378 : Word),
      Steps n n' ∧
      St M' B n' 0x4CC (reg n') ∧
      CodeIn M' B feSquareInnerCode ∧
      (∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M' x = M0 x) ∧
      reg n' ra = v3 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v357 ∧
      reg n' (6 : Fin 32) = zo ∧
      reg n' (7 : Fin 32) = v366 ∧
      reg n' (8 : Fin 32) = v348 ∧
      reg n' (9 : Fin 32) = v360 ∧
      reg n' a0 = v378 ∧
      reg n' a1 = v377 ∧
      reg n' a2 = zo ∧
      reg n' a3 = v365 ∧
      reg n' a4 = v359 ∧
      reg n' a5 = v349 ∧
      reg n' a6 = v373 ∧
      reg n' a7 = v355 ∧
      reg n' (18 : Fin 32) = v13 ∧
      reg n' (19 : Fin 32) = v17 ∧
      reg n' (20 : Fin 32) = v217 ∧
      reg n' (21 : Fin 32) = v208 ∧
      reg n' (22 : Fin 32) = v10 ∧
      reg n' (23 : Fin 32) = v18 ∧
      reg n' (24 : Fin 32) = v21 ∧
      reg n' (25 : Fin 32) = v221 ∧
      reg n' (26 : Fin 32) = v4 ∧
      reg n' (27 : Fin 32) = v30 ∧
      reg n' (28 : Fin 32) = v374 ∧
      reg n' (29 : Fin 32) = v6 ∧
      reg n' (30 : Fin 32) = v1 ∧
      reg n' (31 : Fin 32) = v19 ∧
      memLoad32 M' (F + 0x1C) = memLoad32 M0 (F + 0x1C) ∧
      memLoad32 M' (F + 0x20) = memLoad32 M0 (F + 0x20) ∧
      memLoad32 M' (F + 0x24) = memLoad32 M0 (F + 0x24) ∧
      memLoad32 M' (F + 0x28) = memLoad32 M0 (F + 0x28) ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (zo + 0x0) = v59 ∧
      memLoad32 M' (zo + 0x4) = v76 ∧
      memLoad32 M' (zo + 0x8) = v89 ∧
      memLoad32 M' (zo + 0xC) = v99 ∧
      memLoad32 M' (zo + 0x10) = v132 ∧
      memLoad32 M' (zo + 0x14) = v147 ∧
      memLoad32 M' (zo + 0x18) = v160 ∧
      memLoad32 M' (zo + 0x1C) = v165 ∧
      memLoad32 M' (zo + 0x20) = v204 ∧
      memLoad32 M' (zo + 0x24) = v218 ∧
      memLoad32 M' (zo + 0x28) = v238 ∧
      memLoad32 M' (zo + 0x2C) = v244 ∧
      memLoad32 M' (zo + 0x30) = v283 ∧
      memLoad32 M' (zo + 0x34) = v288 ∧
      memLoad32 M' (zo + 0x38) = v309 ∧
      memLoad32 M' (zo + 0x3C) = v318 ∧
      memLoad32 M' (zo + 0x40) = v373 ∧
      memLoad32 M' (zo + 0x44) = v377 ∧
      memLoad32 M' (zo + 0x48) = v374 ∧
      memLoad32 M' (zo + 0x4C) = v378 ∧
      aluEval .add v347 v345 = v360 ∧
      aluEval .add v350 v359 = v361 ∧
      aluEval .sltu v360 v345 = v362 ∧
      aluEval .add v361 v362 = v363 ∧
      aluEval .add v351 v360 = v364 ∧
      aluEval .sltu v364 v360 = v365 ∧
      aluEval .add v354 v364 = v366 ∧
      aluEval .add v363 v365 = v367 ∧
      aluEval .sltu v366 v364 = v368 ∧
      aluEval .add v358 v367 = v369 ∧
      aluEval .add v368 v357 = v370 ∧
      aluEval .add v369 v370 = v371 ∧
      aluEval .sll v328 0x1 = v372 ∧
      aluEval .add v372 v349 = v373 ∧
      aluEval .add v356 v366 = v374 ∧
      aluEval .sltu v373 v349 = v375 ∧
      aluEval .sltu v374 v366 = v376 ∧
      aluEval .add v375 v355 = v377 ∧
      aluEval .add v371 v376 = v378 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n360, v360, d360, hv360, u360⟩ := s.aluG hc fsq_at_48e (off' := 0x490) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv360
  obtain ⟨n361, v361, d361, hv361, u361⟩ := u360.aluG hc fsq_at_490 (off' := 0x492) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv361
  obtain ⟨n362, v362, d362, hv362, u362⟩ := u361.aluG hc fsq_at_492 (off' := 0x496) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv362
  obtain ⟨n363, v363, d363, hv363, u363⟩ := u362.aluG hc fsq_at_496 (off' := 0x498) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv363
  obtain ⟨n364, v364, d364, hv364, u364⟩ := u363.aluG hc fsq_at_498 (off' := 0x49A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv364
  obtain ⟨n365, v365, d365, hv365, u365⟩ := u364.aluG hc fsq_at_49a (off' := 0x49E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv365
  obtain ⟨n366, v366, d366, hv366, u366⟩ := u365.aluG hc fsq_at_49e (off' := 0x4A0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv366
  obtain ⟨n367, v367, d367, hv367, u367⟩ := u366.aluG hc fsq_at_4a0 (off' := 0x4A2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv367
  obtain ⟨n368, v368, d368, hv368, u368⟩ := u367.aluG hc fsq_at_4a2 (off' := 0x4A6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv368
  obtain ⟨n369, v369, d369, hv369, u369⟩ := u368.aluG hc fsq_at_4a6 (off' := 0x4A8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv369
  obtain ⟨n370, v370, d370, hv370, u370⟩ := u369.aluG hc fsq_at_4a8 (off' := 0x4AA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv370
  obtain ⟨n371, v371, d371, hv371, u371⟩ := u370.aluG hc fsq_at_4aa (off' := 0x4AC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv371
  obtain ⟨n372, v372, d372, hv372, u372⟩ := u371.aluImmG hc fsq_at_4ac (off' := 0x4AE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv372
  obtain ⟨n373, v373, d373, hv373, u373⟩ := u372.aluG hc fsq_at_4ae (off' := 0x4B0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv373
  obtain ⟨n374, v374, d374, hv374, u374⟩ := u373.aluG hc fsq_at_4b0 (off' := 0x4B2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv374
  obtain ⟨n375, v375, d375, hv375, u375⟩ := u374.aluG hc fsq_at_4b2 (off' := 0x4B6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv375
  obtain ⟨n376, v376, d376, hv376, u376⟩ := u375.aluG hc fsq_at_4b6 (off' := 0x4BA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv376
  obtain ⟨n377, v377, d377, hv377, u377⟩ := u376.aluG hc fsq_at_4ba (off' := 0x4BC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv377
  obtain ⟨n378, v378, d378, hv378, u378⟩ := u377.aluG hc fsq_at_4bc (off' := 0x4BE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv378
  obtain ⟨n379, d379, u379⟩ := u378.swG hc fsq_at_4be (off' := 0x4C2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 64) (by decide)) (a := zo + 0x40) (v := v373)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M379, hM379⟩ : ∃ M', memStore32 Mi (zo + 0x40) v373 = M' := ⟨_, rfl⟩
  rw [hM379] at u379
  have hc379 : CodeIn M379 B feSquareInnerCode := by rw [← hM379]; exact hc.store32 (frm_sep' sZC (by decide))
  have fr379 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M379 x = M0 x := fun x hxF hxZ => by
    rw [← hM379, memStore32_get_sep (frm_sep' hxZ (by decide)), fr x hxF hxZ]
  obtain ⟨n380, d380, u380⟩ := u379.aluE hc379 fsq_at_4c2 (off' := 0x4C4) (by decide) (v := zo)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n381, d381, u381⟩ := u380.swG hc379 fsq_at_4c4 (off' := 0x4C6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 68) (by decide)) (a := zo + 0x44) (v := v377)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M381, hM381⟩ : ∃ M', memStore32 M379 (zo + 0x44) v377 = M' := ⟨_, rfl⟩
  rw [hM381] at u381
  have hc381 : CodeIn M381 B feSquareInnerCode := by rw [← hM381]; exact hc379.store32 (frm_sep' sZC (by decide))
  have fr381 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M381 x = M0 x := fun x hxF hxZ => by
    rw [← hM381, memStore32_get_sep (frm_sep' hxZ (by decide)), fr379 x hxF hxZ]
  obtain ⟨n382, d382, u382⟩ := u381.swG hc381 fsq_at_4c6 (off' := 0x4CA) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 72) (by decide)) (a := zo + 0x48) (v := v374)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M382, hM382⟩ : ∃ M', memStore32 M381 (zo + 0x48) v374 = M' := ⟨_, rfl⟩
  rw [hM382] at u382
  have hc382 : CodeIn M382 B feSquareInnerCode := by rw [← hM382]; exact hc381.store32 (frm_sep' sZC (by decide))
  have fr382 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M382 x = M0 x := fun x hxF hxZ => by
    rw [← hM382, memStore32_get_sep (frm_sep' hxZ (by decide)), fr381 x hxF hxZ]
  obtain ⟨n383, d383, u383⟩ := u382.swG hc382 fsq_at_4ca (off' := 0x4CC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hZ (k := 76) (by decide)) (a := zo + 0x4C) (v := v378)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M383, hM383⟩ : ∃ M', memStore32 M382 (zo + 0x4C) v378 = M' := ⟨_, rfl⟩
  rw [hM383] at u383
  have hc383 : CodeIn M383 B feSquareInnerCode := by rw [← hM383]; exact hc382.store32 (frm_sep' sZC (by decide))
  have fr383 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M383 x = M0 x := fun x hxF hxZ => by
    rw [← hM383, memStore32_get_sep (frm_sep' hxZ (by decide)), fr382 x hxF hxZ]
  have qo1 : reg n383 ra = v3 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n383 sp = F := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n383 (3 : Fin 32) = G3 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n383 (4 : Fin 32) = G4 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n383 (5 : Fin 32) = v357 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n383 (6 : Fin 32) = zo := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n383 (7 : Fin 32) = v366 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n383 (8 : Fin 32) = v348 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n383 (9 : Fin 32) = v360 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n383 a0 = v378 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n383 a1 = v377 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n383 a2 = zo := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n383 a3 = v365 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n383 a4 = v359 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n383 a5 = v349 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n383 a6 = v373 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n383 a7 = v355 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n383 (18 : Fin 32) = v13 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n383 (19 : Fin 32) = v17 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n383 (20 : Fin 32) = v217 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n383 (21 : Fin 32) = v208 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n383 (22 : Fin 32) = v10 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n383 (23 : Fin 32) = v18 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n383 (24 : Fin 32) = v21 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n383 (25 : Fin 32) = v221 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n383 (26 : Fin 32) = v4 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n383 (27 : Fin 32) = v30 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n383 (28 : Fin 32) = v374 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n383 (29 : Fin 32) = v6 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n383 (30 : Fin 32) = v1 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n383 (31 : Fin 32) = v19 := by rw [u383.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so1C : memLoad32 M383 (F + 0x1C) = memLoad32 M0 (F + 0x1C) := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 76) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 72) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 68) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (F + 0x1C) 4 from (sFZ.symm.sub (c := 64) (l := 4) (by decide)).subR (c := 28) (l := 4) (by decide)), sl1C]
  have so20 : memLoad32 M383 (F + 0x20) = memLoad32 M0 (F + 0x20) := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 76) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 72) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 68) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (F + 0x20) 4 from (sFZ.symm.sub (c := 64) (l := 4) (by decide)).subR (c := 32) (l := 4) (by decide)), sl20]
  have so24 : memLoad32 M383 (F + 0x24) = memLoad32 M0 (F + 0x24) := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 76) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 72) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 68) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (F + 0x24) 4 from (sFZ.symm.sub (c := 64) (l := 4) (by decide)).subR (c := 36) (l := 4) (by decide)), sl24]
  have so28 : memLoad32 M383 (F + 0x28) = memLoad32 M0 (F + 0x28) := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 76) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 72) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 68) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (F + 0x28) 4 from (sFZ.symm.sub (c := 64) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), sl28]
  have so2C : memLoad32 M383 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 76) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 72) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 68) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (F + 0x2C) 4 from (sFZ.symm.sub (c := 64) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), sl2C]
  have so30 : memLoad32 M383 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 76) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 72) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 68) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (F + 0x30) 4 from (sFZ.symm.sub (c := 64) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), sl30]
  have so34 : memLoad32 M383 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 76) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 72) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 68) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (F + 0x34) 4 from (sFZ.symm.sub (c := 64) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), sl34]
  have so38 : memLoad32 M383 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 76) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 72) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 68) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (F + 0x38) 4 from (sFZ.symm.sub (c := 64) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), sl38]
  have so3C : memLoad32 M383 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 76) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 72) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 68) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (F + 0x3C) 4 from (sFZ.symm.sub (c := 64) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), sl3C]
  have so40 : memLoad32 M383 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 76) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 72) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 68) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (F + 0x40) 4 from (sFZ.symm.sub (c := 64) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), sl40]
  have so44 : memLoad32 M383 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 76) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 72) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 68) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (F + 0x44) 4 from (sFZ.symm.sub (c := 64) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), sl44]
  have so48 : memLoad32 M383 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 76) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 72) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 68) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (F + 0x48) 4 from (sFZ.symm.sub (c := 64) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), sl48]
  have so4C : memLoad32 M383 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 76) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 72) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 68) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (F + 0x4C) 4 from (sFZ.symm.sub (c := 64) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), sl4C]
  have sozo0 : memLoad32 M383 (zo + 0x0) = v59 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x0) 4 from sep_offsets zo (c := 76) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x0) 4 from sep_offsets zo (c := 72) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x0) 4 from sep_offsets zo (c := 68) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x0) 4 from sep_offsets zo (c := 64) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), slzo0]
  have sozo4 : memLoad32 M383 (zo + 0x4) = v76 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x4) 4 from sep_offsets zo (c := 76) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x4) 4 from sep_offsets zo (c := 72) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x4) 4 from sep_offsets zo (c := 68) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x4) 4 from sep_offsets zo (c := 64) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), slzo4]
  have sozo8 : memLoad32 M383 (zo + 0x8) = v89 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x8) 4 from sep_offsets zo (c := 76) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x8) 4 from sep_offsets zo (c := 72) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x8) 4 from sep_offsets zo (c := 68) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x8) 4 from sep_offsets zo (c := 64) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), slzo8]
  have sozoC : memLoad32 M383 (zo + 0xC) = v99 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0xC) 4 from sep_offsets zo (c := 76) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0xC) 4 from sep_offsets zo (c := 72) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0xC) 4 from sep_offsets zo (c := 68) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0xC) 4 from sep_offsets zo (c := 64) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slzoC]
  have sozo10 : memLoad32 M383 (zo + 0x10) = v132 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x10) 4 from sep_offsets zo (c := 76) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x10) 4 from sep_offsets zo (c := 72) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x10) 4 from sep_offsets zo (c := 68) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x10) 4 from sep_offsets zo (c := 64) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), slzo10]
  have sozo14 : memLoad32 M383 (zo + 0x14) = v147 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x14) 4 from sep_offsets zo (c := 76) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x14) 4 from sep_offsets zo (c := 72) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x14) 4 from sep_offsets zo (c := 68) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x14) 4 from sep_offsets zo (c := 64) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), slzo14]
  have sozo18 : memLoad32 M383 (zo + 0x18) = v160 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x18) 4 from sep_offsets zo (c := 76) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x18) 4 from sep_offsets zo (c := 72) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x18) 4 from sep_offsets zo (c := 68) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x18) 4 from sep_offsets zo (c := 64) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), slzo18]
  have sozo1C : memLoad32 M383 (zo + 0x1C) = v165 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x1C) 4 from sep_offsets zo (c := 76) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x1C) 4 from sep_offsets zo (c := 72) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x1C) 4 from sep_offsets zo (c := 68) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x1C) 4 from sep_offsets zo (c := 64) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), slzo1C]
  have sozo20 : memLoad32 M383 (zo + 0x20) = v204 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x20) 4 from sep_offsets zo (c := 76) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x20) 4 from sep_offsets zo (c := 72) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x20) 4 from sep_offsets zo (c := 68) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x20) 4 from sep_offsets zo (c := 64) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), slzo20]
  have sozo24 : memLoad32 M383 (zo + 0x24) = v218 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x24) 4 from sep_offsets zo (c := 76) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x24) 4 from sep_offsets zo (c := 72) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x24) 4 from sep_offsets zo (c := 68) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x24) 4 from sep_offsets zo (c := 64) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), slzo24]
  have sozo28 : memLoad32 M383 (zo + 0x28) = v238 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x28) 4 from sep_offsets zo (c := 76) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x28) 4 from sep_offsets zo (c := 72) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x28) 4 from sep_offsets zo (c := 68) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x28) 4 from sep_offsets zo (c := 64) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), slzo28]
  have sozo2C : memLoad32 M383 (zo + 0x2C) = v244 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x2C) 4 from sep_offsets zo (c := 76) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x2C) 4 from sep_offsets zo (c := 72) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x2C) 4 from sep_offsets zo (c := 68) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x2C) 4 from sep_offsets zo (c := 64) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), slzo2C]
  have sozo30 : memLoad32 M383 (zo + 0x30) = v283 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x30) 4 from sep_offsets zo (c := 76) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x30) 4 from sep_offsets zo (c := 72) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x30) 4 from sep_offsets zo (c := 68) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x30) 4 from sep_offsets zo (c := 64) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), slzo30]
  have sozo34 : memLoad32 M383 (zo + 0x34) = v288 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x34) 4 from sep_offsets zo (c := 76) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x34) 4 from sep_offsets zo (c := 72) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x34) 4 from sep_offsets zo (c := 68) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x34) 4 from sep_offsets zo (c := 64) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), slzo34]
  have sozo38 : memLoad32 M383 (zo + 0x38) = v309 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x38) 4 from sep_offsets zo (c := 76) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x38) 4 from sep_offsets zo (c := 72) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x38) 4 from sep_offsets zo (c := 68) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x38) 4 from sep_offsets zo (c := 64) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), slzo38]
  have sozo3C : memLoad32 M383 (zo + 0x3C) = v318 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x3C) 4 from sep_offsets zo (c := 76) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x3C) 4 from sep_offsets zo (c := 72) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x3C) 4 from sep_offsets zo (c := 68) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_sep (show Sep (zo + 0x40) 4 (zo + 0x3C) 4 from sep_offsets zo (c := 64) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), slzo3C]
  have sozo40 : memLoad32 M383 (zo + 0x40) = v373 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x40) 4 from sep_offsets zo (c := 76) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x40) 4 from sep_offsets zo (c := 72) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_sep (show Sep (zo + 0x44) 4 (zo + 0x40) 4 from sep_offsets zo (c := 68) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), ← hM379, memLoad32_store32_same]
  have sozo44 : memLoad32 M383 (zo + 0x44) = v377 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x44) 4 from sep_offsets zo (c := 76) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_sep (show Sep (zo + 0x48) 4 (zo + 0x44) 4 from sep_offsets zo (c := 72) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), ← hM381, memLoad32_store32_same]
  have sozo48 : memLoad32 M383 (zo + 0x48) = v374 := by
    rw [← hM383, memLoad32_store32_sep (show Sep (zo + 0x4C) 4 (zo + 0x48) 4 from sep_offsets zo (c := 76) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), ← hM382, memLoad32_store32_same]
  have sozo4C : memLoad32 M383 (zo + 0x4C) = v378 := by
    rw [← hM383, memLoad32_store32_same]
  exact ⟨n383, M383, v360, v361, v362, v363, v364, v365, v366, v367, v368, v369, v370, v371, v372, v373, v374, v375, v376, v377, v378, (.cons d360 (.cons d361 (.cons d362 (.cons d363 (.cons d364 (.cons d365 (.cons d366 (.cons d367 (.cons d368 (.cons d369 (.cons d370 (.cons d371 (.cons d372 (.cons d373 (.cons d374 (.cons d375 (.cons d376 (.cons d377 (.cons d378 (.cons d379 (.cons d380 (.cons d381 (.cons d382 (.single d383)))))))))))))))))))))))), u383.self, hc383, fr383, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, sozo0, sozo4, sozo8, sozoC, sozo10, sozo14, sozo18, sozo1C, sozo20, sozo24, sozo28, sozo2C, sozo30, sozo34, sozo38, sozo3C, sozo40, sozo44, sozo48, sozo4C, hv360, hv361, hv362, hv363, hv364, hv365, hv366, hv367, hv368, hv369, hv370, hv371, hv372, hv373, hv374, hv375, hv376, hv377, hv378⟩

theorem fsq_p0_4 {v12 v19 v23 v25 : Word}
    (t25 : v25.toNat = v12.toNat * v19.toNat % 2 ^ 32)
    (t23 : v23.toNat = v12.toNat * v19.toNat / 2 ^ 32) :
    v25.toNat + 2 ^ 32 * v23.toNat = v19.toNat * v12.toNat := by
  have := v12.isLt; have := v19.isLt; have := v23.isLt; have := v25.isLt
  rw [Nat.mul_comm v12.toNat v19.toNat] at t25
  rw [Nat.mul_comm v12.toNat v19.toNat] at t23
  generalize v12.toNat = n12 at *
  generalize v19.toNat = n19 at *
  generalize v23.toNat = n23 at *
  generalize v25.toNat = n25 at *
  omega

theorem fsq_p0_5 {v3 v11 v24 v26 : Word}
    (t26 : v26.toNat = v11.toNat * v3.toNat % 2 ^ 32)
    (t24 : v24.toNat = v11.toNat * v3.toNat / 2 ^ 32) :
    v26.toNat + 2 ^ 32 * v24.toNat = v3.toNat * v11.toNat := by
  have := v3.isLt; have := v11.isLt; have := v24.isLt; have := v26.isLt
  rw [Nat.mul_comm v11.toNat v3.toNat] at t26
  rw [Nat.mul_comm v11.toNat v3.toNat] at t24
  generalize v3.toNat = n3 at *
  generalize v11.toNat = n11 at *
  generalize v24.toNat = n24 at *
  generalize v26.toNat = n26 at *
  omega

theorem fsq_p0_3 {v10 v18 v22 v29 : Word}
    (t29 : v29.toNat = v10.toNat * v18.toNat % 2 ^ 32)
    (t22 : v22.toNat = v10.toNat * v18.toNat / 2 ^ 32) :
    v29.toNat + 2 ^ 32 * v22.toNat = v18.toNat * v10.toNat := by
  have := v10.isLt; have := v18.isLt; have := v22.isLt; have := v29.isLt
  rw [Nat.mul_comm v10.toNat v18.toNat] at t29
  rw [Nat.mul_comm v10.toNat v18.toNat] at t22
  generalize v10.toNat = n10 at *
  generalize v18.toNat = n18 at *
  generalize v22.toNat = n22 at *
  generalize v29.toNat = n29 at *
  omega

theorem fsq_p0_0 {v15 v31 v32 : Word}
    (t32 : v32.toNat = v15.toNat * v15.toNat % 2 ^ 32)
    (t31 : v31.toNat = v15.toNat * v15.toNat / 2 ^ 32) :
    v32.toNat + 2 ^ 32 * v31.toNat = v15.toNat * v15.toNat := by
  have := v15.isLt; have := v31.isLt; have := v32.isLt
  generalize v15.toNat = n15 at *
  generalize v31.toNat = n31 at *
  generalize v32.toNat = n32 at *
  omega

theorem fsq_p0_2 {v20 v30 v36 v39 : Word}
    (t39 : v39.toNat = v20.toNat * v30.toNat % 2 ^ 32)
    (t36 : v36.toNat = v20.toNat * v30.toNat / 2 ^ 32) :
    v39.toNat + 2 ^ 32 * v36.toNat = v30.toNat * v20.toNat := by
  have := v20.isLt; have := v30.isLt; have := v36.isLt; have := v39.isLt
  rw [Nat.mul_comm v20.toNat v30.toNat] at t39
  rw [Nat.mul_comm v20.toNat v30.toNat] at t36
  generalize v20.toNat = n20 at *
  generalize v30.toNat = n30 at *
  generalize v36.toNat = n36 at *
  generalize v39.toNat = n39 at *
  omega

theorem fsq_p0_1 {v21 v28 v33 v43 : Word}
    (t43 : v43.toNat = v21.toNat * v28.toNat % 2 ^ 32)
    (t33 : v33.toNat = v21.toNat * v28.toNat / 2 ^ 32) :
    v43.toNat + 2 ^ 32 * v33.toNat = v28.toNat * v21.toNat := by
  have := v21.isLt; have := v28.isLt; have := v33.isLt; have := v43.isLt
  rw [Nat.mul_comm v21.toNat v28.toNat] at t43
  rw [Nat.mul_comm v21.toNat v28.toNat] at t33
  generalize v21.toNat = n21 at *
  generalize v28.toNat = n28 at *
  generalize v33.toNat = n33 at *
  generalize v43.toNat = n43 at *
  omega

theorem fsq_p1_3 {v10 v16 v60 v62 : Word}
    (t60 : v60.toNat = v10.toNat * v16.toNat % 2 ^ 32)
    (t62 : v62.toNat = v10.toNat * v16.toNat / 2 ^ 32) :
    v60.toNat + 2 ^ 32 * v62.toNat = v16.toNat * v10.toNat := by
  have := v10.isLt; have := v16.isLt; have := v60.isLt; have := v62.isLt
  rw [Nat.mul_comm v10.toNat v16.toNat] at t60
  rw [Nat.mul_comm v10.toNat v16.toNat] at t62
  generalize v10.toNat = n10 at *
  generalize v16.toNat = n16 at *
  generalize v60.toNat = n60 at *
  generalize v62.toNat = n62 at *
  omega

theorem fsq_p1_4 {v12 v17 v61 v63 : Word}
    (t61 : v61.toNat = v12.toNat * v17.toNat % 2 ^ 32)
    (t63 : v63.toNat = v12.toNat * v17.toNat / 2 ^ 32) :
    v61.toNat + 2 ^ 32 * v63.toNat = v17.toNat * v12.toNat := by
  have := v12.isLt; have := v17.isLt; have := v61.isLt; have := v63.isLt
  rw [Nat.mul_comm v12.toNat v17.toNat] at t61
  rw [Nat.mul_comm v12.toNat v17.toNat] at t63
  generalize v12.toNat = n12 at *
  generalize v17.toNat = n17 at *
  generalize v61.toNat = n61 at *
  generalize v63.toNat = n63 at *
  omega

theorem fsq_p1_0 {v8 v48 v67 v68 : Word}
    (t67 : v67.toNat = v48.toNat * v8.toNat % 2 ^ 32)
    (t68 : v68.toNat = v48.toNat * v8.toNat / 2 ^ 32) :
    v67.toNat + 2 ^ 32 * v68.toNat = v48.toNat * v8.toNat := by
  have := v8.isLt; have := v48.isLt; have := v67.isLt; have := v68.isLt
  generalize v8.toNat = n8 at *
  generalize v48.toNat = n48 at *
  generalize v67.toNat = n67 at *
  generalize v68.toNat = n68 at *
  omega

theorem fsq_p1_2 {v20 v64 v69 v71 : Word}
    (t71 : v71.toNat = v20.toNat * v64.toNat % 2 ^ 32)
    (t69 : v69.toNat = v20.toNat * v64.toNat / 2 ^ 32) :
    v71.toNat + 2 ^ 32 * v69.toNat = v64.toNat * v20.toNat := by
  have := v20.isLt; have := v64.isLt; have := v69.isLt; have := v71.isLt
  rw [Nat.mul_comm v20.toNat v64.toNat] at t71
  rw [Nat.mul_comm v20.toNat v64.toNat] at t69
  generalize v20.toNat = n20 at *
  generalize v64.toNat = n64 at *
  generalize v69.toNat = n69 at *
  generalize v71.toNat = n71 at *
  omega

theorem fsq_p1_1 {v19 v21 v70 v73 : Word}
    (t73 : v73.toNat = v21.toNat * v19.toNat % 2 ^ 32)
    (t70 : v70.toNat = v21.toNat * v19.toNat / 2 ^ 32) :
    v73.toNat + 2 ^ 32 * v70.toNat = v19.toNat * v21.toNat := by
  have := v19.isLt; have := v21.isLt; have := v70.isLt; have := v73.isLt
  rw [Nat.mul_comm v21.toNat v19.toNat] at t73
  rw [Nat.mul_comm v21.toNat v19.toNat] at t70
  generalize v19.toNat = n19 at *
  generalize v21.toNat = n21 at *
  generalize v70.toNat = n70 at *
  generalize v73.toNat = n73 at *
  omega

theorem fsq_p2_1 {v8 v18 v90 v91 : Word}
    (t90 : v90.toNat = v18.toNat * v8.toNat % 2 ^ 32)
    (t91 : v91.toNat = v18.toNat * v8.toNat / 2 ^ 32) :
    v90.toNat + 2 ^ 32 * v91.toNat = v18.toNat * v8.toNat := by
  have := v8.isLt; have := v18.isLt; have := v90.isLt; have := v91.isLt
  generalize v8.toNat = n8 at *
  generalize v18.toNat = n18 at *
  generalize v90.toNat = n90 at *
  generalize v91.toNat = n91 at *
  omega

theorem fsq_p2_0 {v16 v48 v92 v93 : Word}
    (t92 : v92.toNat = v16.toNat * v48.toNat % 2 ^ 32)
    (t93 : v93.toNat = v16.toNat * v48.toNat / 2 ^ 32) :
    v92.toNat + 2 ^ 32 * v93.toNat = v48.toNat * v16.toNat := by
  have := v16.isLt; have := v48.isLt; have := v92.isLt; have := v93.isLt
  rw [Nat.mul_comm v16.toNat v48.toNat] at t92
  rw [Nat.mul_comm v16.toNat v48.toNat] at t93
  generalize v16.toNat = n16 at *
  generalize v48.toNat = n48 at *
  generalize v92.toNat = n92 at *
  generalize v93.toNat = n93 at *
  omega

theorem fsq_p2_4 {v10 v19 v100 v102 : Word}
    (t100 : v100.toNat = v10.toNat * v19.toNat % 2 ^ 32)
    (t102 : v102.toNat = v10.toNat * v19.toNat / 2 ^ 32) :
    v100.toNat + 2 ^ 32 * v102.toNat = v19.toNat * v10.toNat := by
  have := v10.isLt; have := v19.isLt; have := v100.isLt; have := v102.isLt
  rw [Nat.mul_comm v10.toNat v19.toNat] at t100
  rw [Nat.mul_comm v10.toNat v19.toNat] at t102
  generalize v10.toNat = n10 at *
  generalize v19.toNat = n19 at *
  generalize v100.toNat = n100 at *
  generalize v102.toNat = n102 at *
  omega

theorem fsq_p2_5 {v12 v64 v101 v103 : Word}
    (t101 : v101.toNat = v12.toNat * v64.toNat % 2 ^ 32)
    (t103 : v103.toNat = v12.toNat * v64.toNat / 2 ^ 32) :
    v101.toNat + 2 ^ 32 * v103.toNat = v64.toNat * v12.toNat := by
  have := v12.isLt; have := v64.isLt; have := v101.isLt; have := v103.isLt
  rw [Nat.mul_comm v12.toNat v64.toNat] at t101
  rw [Nat.mul_comm v12.toNat v64.toNat] at t103
  generalize v12.toNat = n12 at *
  generalize v64.toNat = n64 at *
  generalize v101.toNat = n101 at *
  generalize v103.toNat = n103 at *
  omega

theorem fsq_p2_3 {v6 v20 v110 v111 : Word}
    (t111 : v111.toNat = v20.toNat * v6.toNat % 2 ^ 32)
    (t110 : v110.toNat = v20.toNat * v6.toNat / 2 ^ 32) :
    v111.toNat + 2 ^ 32 * v110.toNat = v6.toNat * v20.toNat := by
  have := v6.isLt; have := v20.isLt; have := v110.isLt; have := v111.isLt
  rw [Nat.mul_comm v20.toNat v6.toNat] at t111
  rw [Nat.mul_comm v20.toNat v6.toNat] at t110
  generalize v6.toNat = n6 at *
  generalize v20.toNat = n20 at *
  generalize v110.toNat = n110 at *
  generalize v111.toNat = n111 at *
  omega

theorem fsq_p2_2 {v21 v30 v112 v116 : Word}
    (t116 : v116.toNat = v21.toNat * v30.toNat % 2 ^ 32)
    (t112 : v112.toNat = v21.toNat * v30.toNat / 2 ^ 32) :
    v116.toNat + 2 ^ 32 * v112.toNat = v30.toNat * v21.toNat := by
  have := v21.isLt; have := v30.isLt; have := v112.isLt; have := v116.isLt
  rw [Nat.mul_comm v21.toNat v30.toNat] at t116
  rw [Nat.mul_comm v21.toNat v30.toNat] at t112
  generalize v21.toNat = n21 at *
  generalize v30.toNat = n30 at *
  generalize v112.toNat = n112 at *
  generalize v116.toNat = n116 at *
  omega

theorem fsq_p3_0 {v9 v48 v127 v133 : Word}
    (t127 : v127.toNat = v9.toNat * v48.toNat % 2 ^ 32)
    (t133 : v133.toNat = v9.toNat * v48.toNat / 2 ^ 32) :
    v127.toNat + 2 ^ 32 * v133.toNat = v48.toNat * v9.toNat := by
  have := v9.isLt; have := v48.isLt; have := v127.isLt; have := v133.isLt
  rw [Nat.mul_comm v9.toNat v48.toNat] at t127
  rw [Nat.mul_comm v9.toNat v48.toNat] at t133
  generalize v9.toNat = n9 at *
  generalize v48.toNat = n48 at *
  generalize v127.toNat = n127 at *
  generalize v133.toNat = n133 at *
  omega

theorem fsq_p3_1 {v16 v18 v128 v134 : Word}
    (t128 : v128.toNat = v18.toNat * v16.toNat % 2 ^ 32)
    (t134 : v134.toNat = v18.toNat * v16.toNat / 2 ^ 32) :
    v128.toNat + 2 ^ 32 * v134.toNat = v18.toNat * v16.toNat := by
  have := v16.isLt; have := v18.isLt; have := v128.isLt; have := v134.isLt
  generalize v16.toNat = n16 at *
  generalize v18.toNat = n18 at *
  generalize v128.toNat = n128 at *
  generalize v134.toNat = n134 at *
  omega

theorem fsq_p3_2 {v21 v64 v137 v138 : Word}
    (t138 : v138.toNat = v21.toNat * v64.toNat % 2 ^ 32)
    (t137 : v137.toNat = v21.toNat * v64.toNat / 2 ^ 32) :
    v138.toNat + 2 ^ 32 * v137.toNat = v64.toNat * v21.toNat := by
  have := v21.isLt; have := v64.isLt; have := v137.isLt; have := v138.isLt
  rw [Nat.mul_comm v21.toNat v64.toNat] at t138
  rw [Nat.mul_comm v21.toNat v64.toNat] at t137
  generalize v21.toNat = n21 at *
  generalize v64.toNat = n64 at *
  generalize v137.toNat = n137 at *
  generalize v138.toNat = n138 at *
  omega

theorem fsq_p3_3 {v10 v17 v141 v143 : Word}
    (t141 : v141.toNat = v10.toNat * v17.toNat % 2 ^ 32)
    (t143 : v143.toNat = v10.toNat * v17.toNat / 2 ^ 32) :
    v141.toNat + 2 ^ 32 * v143.toNat = v17.toNat * v10.toNat := by
  have := v10.isLt; have := v17.isLt; have := v141.isLt; have := v143.isLt
  rw [Nat.mul_comm v10.toNat v17.toNat] at t141
  rw [Nat.mul_comm v10.toNat v17.toNat] at t143
  generalize v10.toNat = n10 at *
  generalize v17.toNat = n17 at *
  generalize v141.toNat = n141 at *
  generalize v143.toNat = n143 at *
  omega

theorem fsq_p3_4 {v6 v12 v142 v144 : Word}
    (t142 : v142.toNat = v12.toNat * v6.toNat % 2 ^ 32)
    (t144 : v144.toNat = v12.toNat * v6.toNat / 2 ^ 32) :
    v142.toNat + 2 ^ 32 * v144.toNat = v6.toNat * v12.toNat := by
  have := v6.isLt; have := v12.isLt; have := v142.isLt; have := v144.isLt
  rw [Nat.mul_comm v12.toNat v6.toNat] at t142
  rw [Nat.mul_comm v12.toNat v6.toNat] at t144
  generalize v6.toNat = n6 at *
  generalize v12.toNat = n12 at *
  generalize v142.toNat = n142 at *
  generalize v144.toNat = n144 at *
  omega

theorem fsq_p4_4 {v10 v64 v166 v167 : Word}
    (t166 : v166.toNat = v10.toNat * v64.toNat % 2 ^ 32)
    (t167 : v167.toNat = v10.toNat * v64.toNat / 2 ^ 32) :
    v166.toNat + 2 ^ 32 * v167.toNat = v64.toNat * v10.toNat := by
  have := v10.isLt; have := v64.isLt; have := v166.isLt; have := v167.isLt
  rw [Nat.mul_comm v10.toNat v64.toNat] at t166
  rw [Nat.mul_comm v10.toNat v64.toNat] at t167
  generalize v10.toNat = n10 at *
  generalize v64.toNat = n64 at *
  generalize v166.toNat = n166 at *
  generalize v167.toNat = n167 at *
  omega

theorem fsq_p4_5 {v4 v12 v169 v170 : Word}
    (t169 : v169.toNat = v12.toNat * v4.toNat % 2 ^ 32)
    (t170 : v170.toNat = v12.toNat * v4.toNat / 2 ^ 32) :
    v169.toNat + 2 ^ 32 * v170.toNat = v4.toNat * v12.toNat := by
  have := v4.isLt; have := v12.isLt; have := v169.isLt; have := v170.isLt
  rw [Nat.mul_comm v12.toNat v4.toNat] at t169
  rw [Nat.mul_comm v12.toNat v4.toNat] at t170
  generalize v4.toNat = n4 at *
  generalize v12.toNat = n12 at *
  generalize v169.toNat = n169 at *
  generalize v170.toNat = n170 at *
  omega

theorem fsq_p4_0 {v17 v48 v176 v177 : Word}
    (t177 : v177.toNat = v17.toNat * v48.toNat % 2 ^ 32)
    (t176 : v176.toNat = v17.toNat * v48.toNat / 2 ^ 32) :
    v177.toNat + 2 ^ 32 * v176.toNat = v48.toNat * v17.toNat := by
  have := v17.isLt; have := v48.isLt; have := v176.isLt; have := v177.isLt
  rw [Nat.mul_comm v17.toNat v48.toNat] at t177
  rw [Nat.mul_comm v17.toNat v48.toNat] at t176
  generalize v17.toNat = n17 at *
  generalize v48.toNat = n48 at *
  generalize v176.toNat = n176 at *
  generalize v177.toNat = n177 at *
  omega

theorem fsq_p4_1 {v18 v19 v178 v179 : Word}
    (t179 : v179.toNat = v19.toNat * v18.toNat % 2 ^ 32)
    (t178 : v178.toNat = v19.toNat * v18.toNat / 2 ^ 32) :
    v179.toNat + 2 ^ 32 * v178.toNat = v18.toNat * v19.toNat := by
  have := v18.isLt; have := v19.isLt; have := v178.isLt; have := v179.isLt
  rw [Nat.mul_comm v19.toNat v18.toNat] at t179
  rw [Nat.mul_comm v19.toNat v18.toNat] at t178
  generalize v18.toNat = n18 at *
  generalize v19.toNat = n19 at *
  generalize v178.toNat = n178 at *
  generalize v179.toNat = n179 at *
  omega

theorem fsq_p4_2 {v16 v180 v181 : Word}
    (t180 : v180.toNat = v16.toNat * v16.toNat % 2 ^ 32)
    (t181 : v181.toNat = v16.toNat * v16.toNat / 2 ^ 32) :
    v180.toNat + 2 ^ 32 * v181.toNat = v16.toNat * v16.toNat := by
  have := v16.isLt; have := v180.isLt; have := v181.isLt
  generalize v16.toNat = n16 at *
  generalize v180.toNat = n180 at *
  generalize v181.toNat = n181 at *
  omega

theorem fsq_p4_3 {v21 v151 v185 v189 : Word}
    (t185 : v185.toNat = v21.toNat * v151.toNat % 2 ^ 32)
    (t189 : v189.toNat = v21.toNat * v151.toNat / 2 ^ 32) :
    v185.toNat + 2 ^ 32 * v189.toNat = v151.toNat * v21.toNat := by
  have := v21.isLt; have := v151.isLt; have := v185.isLt; have := v189.isLt
  rw [Nat.mul_comm v21.toNat v151.toNat] at t185
  rw [Nat.mul_comm v21.toNat v151.toNat] at t189
  generalize v21.toNat = n21 at *
  generalize v151.toNat = n151 at *
  generalize v185.toNat = n185 at *
  generalize v189.toNat = n189 at *
  omega

theorem fsq_p5_4 {v6 v10 v206 v209 : Word}
    (t209 : v209.toNat = v6.toNat * v10.toNat % 2 ^ 32)
    (t206 : v206.toNat = v6.toNat * v10.toNat / 2 ^ 32) :
    v209.toNat + 2 ^ 32 * v206.toNat = v6.toNat * v10.toNat := by
  have := v6.isLt; have := v10.isLt; have := v206.isLt; have := v209.isLt
  generalize v6.toNat = n6 at *
  generalize v10.toNat = n10 at *
  generalize v206.toNat = n206 at *
  generalize v209.toNat = n209 at *
  omega

theorem fsq_p5_1 {v17 v18 v210 v213 : Word}
    (t213 : v213.toNat = v17.toNat * v18.toNat % 2 ^ 32)
    (t210 : v210.toNat = v17.toNat * v18.toNat / 2 ^ 32) :
    v213.toNat + 2 ^ 32 * v210.toNat = v18.toNat * v17.toNat := by
  have := v17.isLt; have := v18.isLt; have := v210.isLt; have := v213.isLt
  rw [Nat.mul_comm v17.toNat v18.toNat] at t213
  rw [Nat.mul_comm v17.toNat v18.toNat] at t210
  generalize v17.toNat = n17 at *
  generalize v18.toNat = n18 at *
  generalize v210.toNat = n210 at *
  generalize v213.toNat = n213 at *
  omega

theorem fsq_p5_2 {v9 v28 v212 v214 : Word}
    (t214 : v214.toNat = v28.toNat * v9.toNat % 2 ^ 32)
    (t212 : v212.toNat = v28.toNat * v9.toNat / 2 ^ 32) :
    v214.toNat + 2 ^ 32 * v212.toNat = v28.toNat * v9.toNat := by
  have := v9.isLt; have := v28.isLt; have := v212.isLt; have := v214.isLt
  generalize v9.toNat = n9 at *
  generalize v28.toNat = n28 at *
  generalize v212.toNat = n212 at *
  generalize v214.toNat = n214 at *
  omega

theorem fsq_p5_0 {v3 v48 v208 v216 : Word}
    (t216 : v216.toNat = v3.toNat * v48.toNat % 2 ^ 32)
    (t208 : v208.toNat = v3.toNat * v48.toNat / 2 ^ 32) :
    v216.toNat + 2 ^ 32 * v208.toNat = v48.toNat * v3.toNat := by
  have := v3.isLt; have := v48.isLt; have := v208.isLt; have := v216.isLt
  rw [Nat.mul_comm v3.toNat v48.toNat] at t216
  rw [Nat.mul_comm v3.toNat v48.toNat] at t208
  generalize v3.toNat = n3 at *
  generalize v48.toNat = n48 at *
  generalize v208.toNat = n208 at *
  generalize v216.toNat = n216 at *
  omega

theorem fsq_p5_3 {v21 v217 v219 v221 : Word}
    (t219 : v219.toNat = v21.toNat * v217.toNat % 2 ^ 32)
    (t221 : v221.toNat = v21.toNat * v217.toNat / 2 ^ 32) :
    v219.toNat + 2 ^ 32 * v221.toNat = v217.toNat * v21.toNat := by
  have := v21.isLt; have := v217.isLt; have := v219.isLt; have := v221.isLt
  rw [Nat.mul_comm v21.toNat v217.toNat] at t219
  rw [Nat.mul_comm v21.toNat v217.toNat] at t221
  generalize v21.toNat = n21 at *
  generalize v217.toNat = n217 at *
  generalize v219.toNat = n219 at *
  generalize v221.toNat = n221 at *
  omega

theorem fsq_p6_5 {v10 v217 v240 v241 : Word}
    (t240 : v240.toNat = v217.toNat * v10.toNat % 2 ^ 32)
    (t241 : v241.toNat = v217.toNat * v10.toNat / 2 ^ 32) :
    v240.toNat + 2 ^ 32 * v241.toNat = v217.toNat * v10.toNat := by
  have := v10.isLt; have := v217.isLt; have := v240.isLt; have := v241.isLt
  generalize v10.toNat = n10 at *
  generalize v217.toNat = n217 at *
  generalize v240.toNat = n240 at *
  generalize v241.toNat = n241 at *
  omega

theorem fsq_p6_2 {v17 v28 v245 v248 : Word}
    (t248 : v248.toNat = v17.toNat * v28.toNat % 2 ^ 32)
    (t245 : v245.toNat = v17.toNat * v28.toNat / 2 ^ 32) :
    v248.toNat + 2 ^ 32 * v245.toNat = v28.toNat * v17.toNat := by
  have := v17.isLt; have := v28.isLt; have := v245.isLt; have := v248.isLt
  rw [Nat.mul_comm v17.toNat v28.toNat] at t248
  rw [Nat.mul_comm v17.toNat v28.toNat] at t245
  generalize v17.toNat = n17 at *
  generalize v28.toNat = n28 at *
  generalize v245.toNat = n245 at *
  generalize v248.toNat = n248 at *
  omega

theorem fsq_p6_3 {v9 v19 v246 v249 : Word}
    (t249 : v249.toNat = v19.toNat * v9.toNat % 2 ^ 32)
    (t246 : v246.toNat = v19.toNat * v9.toNat / 2 ^ 32) :
    v249.toNat + 2 ^ 32 * v246.toNat = v19.toNat * v9.toNat := by
  have := v9.isLt; have := v19.isLt; have := v246.isLt; have := v249.isLt
  generalize v9.toNat = n9 at *
  generalize v19.toNat = n19 at *
  generalize v246.toNat = n246 at *
  generalize v249.toNat = n249 at *
  omega

theorem fsq_p6_1 {v18 v64 v247 v252 : Word}
    (t252 : v252.toNat = v64.toNat * v18.toNat % 2 ^ 32)
    (t247 : v247.toNat = v64.toNat * v18.toNat / 2 ^ 32) :
    v252.toNat + 2 ^ 32 * v247.toNat = v18.toNat * v64.toNat := by
  have := v18.isLt; have := v64.isLt; have := v247.isLt; have := v252.isLt
  rw [Nat.mul_comm v64.toNat v18.toNat] at t252
  rw [Nat.mul_comm v64.toNat v18.toNat] at t247
  generalize v18.toNat = n18 at *
  generalize v64.toNat = n64 at *
  generalize v247.toNat = n247 at *
  generalize v252.toNat = n252 at *
  omega

theorem fsq_p6_0 {v6 v48 v256 v258 : Word}
    (t256 : v256.toNat = v6.toNat * v48.toNat % 2 ^ 32)
    (t258 : v258.toNat = v6.toNat * v48.toNat / 2 ^ 32) :
    v256.toNat + 2 ^ 32 * v258.toNat = v48.toNat * v6.toNat := by
  have := v6.isLt; have := v48.isLt; have := v256.isLt; have := v258.isLt
  rw [Nat.mul_comm v6.toNat v48.toNat] at t256
  rw [Nat.mul_comm v6.toNat v48.toNat] at t258
  generalize v6.toNat = n6 at *
  generalize v48.toNat = n48 at *
  generalize v256.toNat = n256 at *
  generalize v258.toNat = n258 at *
  omega

theorem fsq_p6_4 {v13 v21 v261 v262 : Word}
    (t261 : v261.toNat = v21.toNat * v13.toNat % 2 ^ 32)
    (t262 : v262.toNat = v21.toNat * v13.toNat / 2 ^ 32) :
    v261.toNat + 2 ^ 32 * v262.toNat = v13.toNat * v21.toNat := by
  have := v13.isLt; have := v21.isLt; have := v261.isLt; have := v262.isLt
  rw [Nat.mul_comm v21.toNat v13.toNat] at t261
  rw [Nat.mul_comm v21.toNat v13.toNat] at t262
  generalize v13.toNat = n13 at *
  generalize v21.toNat = n21 at *
  generalize v261.toNat = n261 at *
  generalize v262.toNat = n262 at *
  omega

theorem fsq_p7_2 {v3 v28 v278 v280 : Word}
    (t280 : v280.toNat = v3.toNat * v28.toNat % 2 ^ 32)
    (t278 : v278.toNat = v3.toNat * v28.toNat / 2 ^ 32) :
    v280.toNat + 2 ^ 32 * v278.toNat = v28.toNat * v3.toNat := by
  have := v3.isLt; have := v28.isLt; have := v278.isLt; have := v280.isLt
  rw [Nat.mul_comm v3.toNat v28.toNat] at t280
  rw [Nat.mul_comm v3.toNat v28.toNat] at t278
  generalize v3.toNat = n3 at *
  generalize v28.toNat = n28 at *
  generalize v278.toNat = n278 at *
  generalize v280.toNat = n280 at *
  omega

theorem fsq_p7_3 {v17 v19 v279 v281 : Word}
    (t281 : v281.toNat = v19.toNat * v17.toNat % 2 ^ 32)
    (t279 : v279.toNat = v19.toNat * v17.toNat / 2 ^ 32) :
    v281.toNat + 2 ^ 32 * v279.toNat = v19.toNat * v17.toNat := by
  have := v17.isLt; have := v19.isLt; have := v279.isLt; have := v281.isLt
  generalize v17.toNat = n17 at *
  generalize v19.toNat = n19 at *
  generalize v279.toNat = n279 at *
  generalize v281.toNat = n281 at *
  omega

theorem fsq_p7_1 {v6 v18 v277 v286 : Word}
    (t286 : v286.toNat = v6.toNat * v18.toNat % 2 ^ 32)
    (t277 : v277.toNat = v6.toNat * v18.toNat / 2 ^ 32) :
    v286.toNat + 2 ^ 32 * v277.toNat = v18.toNat * v6.toNat := by
  have := v6.isLt; have := v18.isLt; have := v277.isLt; have := v286.isLt
  rw [Nat.mul_comm v6.toNat v18.toNat] at t286
  rw [Nat.mul_comm v6.toNat v18.toNat] at t277
  generalize v6.toNat = n6 at *
  generalize v18.toNat = n18 at *
  generalize v277.toNat = n277 at *
  generalize v286.toNat = n286 at *
  omega

theorem fsq_p7_4 {v10 v13 v287 v289 : Word}
    (t287 : v287.toNat = v13.toNat * v10.toNat % 2 ^ 32)
    (t289 : v289.toNat = v13.toNat * v10.toNat / 2 ^ 32) :
    v287.toNat + 2 ^ 32 * v289.toNat = v13.toNat * v10.toNat := by
  have := v10.isLt; have := v13.isLt; have := v287.isLt; have := v289.isLt
  generalize v10.toNat = n10 at *
  generalize v13.toNat = n13 at *
  generalize v287.toNat = n287 at *
  generalize v289.toNat = n289 at *
  omega

theorem fsq_p7_0 {v4 v48 v291 v294 : Word}
    (t291 : v291.toNat = v4.toNat * v48.toNat % 2 ^ 32)
    (t294 : v294.toNat = v4.toNat * v48.toNat / 2 ^ 32) :
    v291.toNat + 2 ^ 32 * v294.toNat = v48.toNat * v4.toNat := by
  have := v4.isLt; have := v48.isLt; have := v291.isLt; have := v294.isLt
  rw [Nat.mul_comm v4.toNat v48.toNat] at t291
  rw [Nat.mul_comm v4.toNat v48.toNat] at t294
  generalize v4.toNat = n4 at *
  generalize v48.toNat = n48 at *
  generalize v291.toNat = n291 at *
  generalize v294.toNat = n294 at *
  omega

theorem fsq_p8_2 {v6 v28 v310 v316 : Word}
    (t316 : v316.toNat = v6.toNat * v28.toNat % 2 ^ 32)
    (t310 : v310.toNat = v6.toNat * v28.toNat / 2 ^ 32) :
    v316.toNat + 2 ^ 32 * v310.toNat = v28.toNat * v6.toNat := by
  have := v6.isLt; have := v28.isLt; have := v310.isLt; have := v316.isLt
  rw [Nat.mul_comm v6.toNat v28.toNat] at t316
  rw [Nat.mul_comm v6.toNat v28.toNat] at t310
  generalize v6.toNat = n6 at *
  generalize v28.toNat = n28 at *
  generalize v310.toNat = n310 at *
  generalize v316.toNat = n316 at *
  omega

theorem fsq_p8_4 {v17 v311 v317 : Word}
    (t317 : v317.toNat = v17.toNat * v17.toNat % 2 ^ 32)
    (t311 : v311.toNat = v17.toNat * v17.toNat / 2 ^ 32) :
    v317.toNat + 2 ^ 32 * v311.toNat = v17.toNat * v17.toNat := by
  have := v17.isLt; have := v311.isLt; have := v317.isLt
  generalize v17.toNat = n17 at *
  generalize v311.toNat = n311 at *
  generalize v317.toNat = n317 at *
  omega

theorem fsq_p8_3 {v19 v64 v315 v319 : Word}
    (t319 : v319.toNat = v64.toNat * v19.toNat % 2 ^ 32)
    (t315 : v315.toNat = v64.toNat * v19.toNat / 2 ^ 32) :
    v319.toNat + 2 ^ 32 * v315.toNat = v19.toNat * v64.toNat := by
  have := v19.isLt; have := v64.isLt; have := v315.isLt; have := v319.isLt
  rw [Nat.mul_comm v64.toNat v19.toNat] at t319
  rw [Nat.mul_comm v64.toNat v19.toNat] at t315
  generalize v19.toNat = n19 at *
  generalize v64.toNat = n64 at *
  generalize v315.toNat = n315 at *
  generalize v319.toNat = n319 at *
  omega

theorem fsq_p8_1 {v18 v217 v322 v325 : Word}
    (t322 : v322.toNat = v217.toNat * v18.toNat % 2 ^ 32)
    (t325 : v325.toNat = v217.toNat * v18.toNat / 2 ^ 32) :
    v322.toNat + 2 ^ 32 * v325.toNat = v18.toNat * v217.toNat := by
  have := v18.isLt; have := v217.isLt; have := v322.isLt; have := v325.isLt
  rw [Nat.mul_comm v217.toNat v18.toNat] at t322
  rw [Nat.mul_comm v217.toNat v18.toNat] at t325
  generalize v18.toNat = n18 at *
  generalize v217.toNat = n217 at *
  generalize v322.toNat = n322 at *
  generalize v325.toNat = n325 at *
  omega

theorem fsq_p8_5 {v1 v10 v328 v329 : Word}
    (t328 : v328.toNat = v1.toNat * v10.toNat % 2 ^ 32)
    (t329 : v329.toNat = v1.toNat * v10.toNat / 2 ^ 32) :
    v328.toNat + 2 ^ 32 * v329.toNat = v1.toNat * v10.toNat := by
  have := v1.isLt; have := v10.isLt; have := v328.isLt; have := v329.isLt
  generalize v1.toNat = n1 at *
  generalize v10.toNat = n10 at *
  generalize v328.toNat = n328 at *
  generalize v329.toNat = n329 at *
  omega

theorem fsq_p8_0 {v13 v48 v324 v337 : Word}
    (t337 : v337.toNat = v13.toNat * v48.toNat % 2 ^ 32)
    (t324 : v324.toNat = v13.toNat * v48.toNat / 2 ^ 32) :
    v337.toNat + 2 ^ 32 * v324.toNat = v48.toNat * v13.toNat := by
  have := v13.isLt; have := v48.isLt; have := v324.isLt; have := v337.isLt
  rw [Nat.mul_comm v13.toNat v48.toNat] at t337
  rw [Nat.mul_comm v13.toNat v48.toNat] at t324
  generalize v13.toNat = n13 at *
  generalize v48.toNat = n48 at *
  generalize v324.toNat = n324 at *
  generalize v337.toNat = n337 at *
  omega

theorem fsq_p9_3 {v6 v19 v345 v346 : Word}
    (t345 : v345.toNat = v6.toNat * v19.toNat % 2 ^ 32)
    (t346 : v346.toNat = v6.toNat * v19.toNat / 2 ^ 32) :
    v345.toNat + 2 ^ 32 * v346.toNat = v19.toNat * v6.toNat := by
  have := v6.isLt; have := v19.isLt; have := v345.isLt; have := v346.isLt
  rw [Nat.mul_comm v6.toNat v19.toNat] at t345
  rw [Nat.mul_comm v6.toNat v19.toNat] at t346
  generalize v6.toNat = n6 at *
  generalize v19.toNat = n19 at *
  generalize v345.toNat = n345 at *
  generalize v346.toNat = n346 at *
  omega

theorem fsq_p9_4 {v3 v30 v347 v348 : Word}
    (t347 : v347.toNat = v30.toNat * v3.toNat % 2 ^ 32)
    (t348 : v348.toNat = v30.toNat * v3.toNat / 2 ^ 32) :
    v347.toNat + 2 ^ 32 * v348.toNat = v30.toNat * v3.toNat := by
  have := v3.isLt; have := v30.isLt; have := v347.isLt; have := v348.isLt
  generalize v3.toNat = n3 at *
  generalize v30.toNat = n30 at *
  generalize v347.toNat = n347 at *
  generalize v348.toNat = n348 at *
  omega

theorem fsq_p9_2 {v4 v28 v350 v351 : Word}
    (t351 : v351.toNat = v4.toNat * v28.toNat % 2 ^ 32)
    (t350 : v350.toNat = v4.toNat * v28.toNat / 2 ^ 32) :
    v351.toNat + 2 ^ 32 * v350.toNat = v28.toNat * v4.toNat := by
  have := v4.isLt; have := v28.isLt; have := v350.isLt; have := v351.isLt
  rw [Nat.mul_comm v4.toNat v28.toNat] at t351
  rw [Nat.mul_comm v4.toNat v28.toNat] at t350
  generalize v4.toNat = n4 at *
  generalize v28.toNat = n28 at *
  generalize v350.toNat = n350 at *
  generalize v351.toNat = n351 at *
  omega

theorem fsq_p9_0 {v1 v48 v356 v357 : Word}
    (t356 : v356.toNat = v1.toNat * v48.toNat % 2 ^ 32)
    (t357 : v357.toNat = v1.toNat * v48.toNat / 2 ^ 32) :
    v356.toNat + 2 ^ 32 * v357.toNat = v48.toNat * v1.toNat := by
  have := v1.isLt; have := v48.isLt; have := v356.isLt; have := v357.isLt
  rw [Nat.mul_comm v1.toNat v48.toNat] at t356
  rw [Nat.mul_comm v1.toNat v48.toNat] at t357
  generalize v1.toNat = n1 at *
  generalize v48.toNat = n48 at *
  generalize v356.toNat = n356 at *
  generalize v357.toNat = n357 at *
  omega

theorem fsq_p9_1 {v13 v18 v354 v358 : Word}
    (t354 : v354.toNat = v13.toNat * v18.toNat % 2 ^ 32)
    (t358 : v358.toNat = v13.toNat * v18.toNat / 2 ^ 32) :
    v354.toNat + 2 ^ 32 * v358.toNat = v18.toNat * v13.toNat := by
  have := v13.isLt; have := v18.isLt; have := v354.isLt; have := v358.isLt
  rw [Nat.mul_comm v13.toNat v18.toNat] at t354
  rw [Nat.mul_comm v13.toNat v18.toNat] at t358
  generalize v13.toNat = n13 at *
  generalize v18.toNat = n18 at *
  generalize v354.toNat = n354 at *
  generalize v358.toNat = n358 at *
  omega

theorem fsq_s0_3_4_5 {v3 v10 v11 v12 v18 v19 v22 v23 v24 v25 v26 v29 v35 v37 v38 v40 v41 v42 v44 v45 : Word}
    (t35 : v35.toNat = (v23.toNat + v24.toNat) % 2 ^ 32)
    (t38 : v38.toNat = (v22.toNat + v35.toNat) % 2 ^ 32)
    (t40 : v37.toNat + 2 ^ 32 * v40.toNat = v26.toNat + v25.toNat)
    (t42 : v42.toNat = (v38.toNat + v40.toNat) % 2 ^ 32)
    (t44 : v41.toNat + 2 ^ 32 * v44.toNat = v29.toNat + v37.toNat)
    (t45 : v45.toNat = (v42.toNat + v44.toNat) % 2 ^ 32)
    (hp0_3 : v29.toNat + 2 ^ 32 * v22.toNat = v18.toNat * v10.toNat)
    (hp0_4 : v25.toNat + 2 ^ 32 * v23.toNat = v19.toNat * v12.toNat)
    (hp0_5 : v26.toNat + 2 ^ 32 * v24.toNat = v3.toNat * v11.toNat) :
    v41.toNat + 2 ^ 32 * v45.toNat = (v18.toNat * v10.toNat + v19.toNat * v12.toNat + v3.toNat * v11.toNat) % 2 ^ 64 := by
  obtain ⟨q_t35, e_t35⟩ := mod_q t35; clear t35
  obtain ⟨q_t38, e_t38⟩ := mod_q t38; clear t38
  obtain ⟨q_t42, e_t42⟩ := mod_q t42; clear t42
  obtain ⟨q_t45, e_t45⟩ := mod_q t45; clear t45
  have key : v41.toNat + 2 ^ 32 * v45.toNat + 2 ^ 64 * (q_t35 + q_t38 + q_t42 + q_t45) = v18.toNat * v10.toNat + v19.toNat * v12.toNat + v3.toNat * v11.toNat := by
    generalize v3.toNat = n3 at *
    generalize v10.toNat = n10 at *
    generalize v11.toNat = n11 at *
    generalize v12.toNat = n12 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v22.toNat = n22 at *
    generalize v23.toNat = n23 at *
    generalize v24.toNat = n24 at *
    generalize v25.toNat = n25 at *
    generalize v26.toNat = n26 at *
    generalize v29.toNat = n29 at *
    generalize v35.toNat = n35 at *
    generalize v37.toNat = n37 at *
    generalize v38.toNat = n38 at *
    generalize v40.toNat = n40 at *
    generalize v41.toNat = n41 at *
    generalize v42.toNat = n42 at *
    generalize v44.toNat = n44 at *
    generalize v45.toNat = n45 at *
    omega
  exact mod64_of key

theorem fsq_w0_3_4_5 {v3 v10 v11 v12 v18 v19 v41 v45 v46 v47 v49 v50 : Word}
    (t46 : v46.toNat = v41.toNat / 2 ^ 31)
    (t47 : v47.toNat = v45.toNat * 2 ^ 1 % 2 ^ 32)
    (t49 : v49.toNat = v46.toNat + v47.toNat)
    (t50 : v50.toNat = v41.toNat * 2 ^ 1 % 2 ^ 32)
    (hs0_3_4_5 : v41.toNat + 2 ^ 32 * v45.toNat = (v18.toNat * v10.toNat + v19.toNat * v12.toNat + v3.toNat * v11.toNat) % 2 ^ 64) :
    v50.toNat + 2 ^ 32 * v49.toNat = ((v18.toNat * v10.toNat + v19.toNat * v12.toNat + v3.toNat * v11.toNat) * 2) % 2 ^ 64 := by
  have := v3.isLt; have := v10.isLt; have := v11.isLt; have := v12.isLt; have := v18.isLt; have := v19.isLt; have := v41.isLt; have := v45.isLt; have := v46.isLt; have := v47.isLt; have := v49.isLt; have := v50.isLt
  generalize v3.toNat = n3 at *
  generalize v10.toNat = n10 at *
  generalize v11.toNat = n11 at *
  generalize v12.toNat = n12 at *
  generalize v18.toNat = n18 at *
  generalize v19.toNat = n19 at *
  generalize v41.toNat = n41 at *
  generalize v45.toNat = n45 at *
  generalize v46.toNat = n46 at *
  generalize v47.toNat = n47 at *
  generalize v49.toNat = n49 at *
  generalize v50.toNat = n50 at *
  omega

theorem fsq_s0_0_1_2 {v15 v20 v21 v28 v30 v31 v32 v33 v36 v39 v43 v51 v52 v53 v54 v55 v56 v57 v58 : Word}
    (t52 : v51.toNat + 2 ^ 32 * v52.toNat = v32.toNat + v39.toNat)
    (t53 : v53.toNat = (v31.toNat + v36.toNat) % 2 ^ 32)
    (t55 : v55.toNat = (v53.toNat + v33.toNat) % 2 ^ 32)
    (t56 : v54.toNat + 2 ^ 32 * v56.toNat = v43.toNat + v51.toNat)
    (t57 : v57.toNat = (v52.toNat + v55.toNat) % 2 ^ 32)
    (t58 : v58.toNat = (v57.toNat + v56.toNat) % 2 ^ 32)
    (hp0_0 : v32.toNat + 2 ^ 32 * v31.toNat = v15.toNat * v15.toNat)
    (hp0_1 : v43.toNat + 2 ^ 32 * v33.toNat = v28.toNat * v21.toNat)
    (hp0_2 : v39.toNat + 2 ^ 32 * v36.toNat = v30.toNat * v20.toNat) :
    v54.toNat + 2 ^ 32 * v58.toNat = (v15.toNat * v15.toNat + v28.toNat * v21.toNat + v30.toNat * v20.toNat) % 2 ^ 64 := by
  obtain ⟨q_t53, e_t53⟩ := mod_q t53; clear t53
  obtain ⟨q_t55, e_t55⟩ := mod_q t55; clear t55
  obtain ⟨q_t57, e_t57⟩ := mod_q t57; clear t57
  obtain ⟨q_t58, e_t58⟩ := mod_q t58; clear t58
  have key : v54.toNat + 2 ^ 32 * v58.toNat + 2 ^ 64 * (q_t53 + q_t55 + q_t57 + q_t58) = v15.toNat * v15.toNat + v28.toNat * v21.toNat + v30.toNat * v20.toNat := by
    generalize v15.toNat = n15 at *
    generalize v20.toNat = n20 at *
    generalize v21.toNat = n21 at *
    generalize v28.toNat = n28 at *
    generalize v30.toNat = n30 at *
    generalize v31.toNat = n31 at *
    generalize v32.toNat = n32 at *
    generalize v33.toNat = n33 at *
    generalize v36.toNat = n36 at *
    generalize v39.toNat = n39 at *
    generalize v43.toNat = n43 at *
    generalize v51.toNat = n51 at *
    generalize v52.toNat = n52 at *
    generalize v53.toNat = n53 at *
    generalize v54.toNat = n54 at *
    generalize v55.toNat = n55 at *
    generalize v56.toNat = n56 at *
    generalize v57.toNat = n57 at *
    generalize v58.toNat = n58 at *
    omega
  exact mod64_of key

theorem fsq_w0_0_1_2_3_4_5 {v3 v10 v11 v12 v15 v18 v19 v20 v21 v28 v30 v49 v50 v54 v58 v59 v65 v66 v76 : Word}
    (t65 : v59.toNat + 2 ^ 32 * v65.toNat = v54.toNat + v50.toNat)
    (t66 : v66.toNat = (v65.toNat + v58.toNat) % 2 ^ 32)
    (t76 : v76.toNat = (v49.toNat + v66.toNat) % 2 ^ 32)
    (hw0_3_4_5 : v50.toNat + 2 ^ 32 * v49.toNat = ((v18.toNat * v10.toNat + v19.toNat * v12.toNat + v3.toNat * v11.toNat) * 2) % 2 ^ 64)
    (hs0_0_1_2 : v54.toNat + 2 ^ 32 * v58.toNat = (v15.toNat * v15.toNat + v28.toNat * v21.toNat + v30.toNat * v20.toNat) % 2 ^ 64) :
    v59.toNat + 2 ^ 32 * v76.toNat = (v15.toNat * v15.toNat + v28.toNat * v21.toNat + v30.toNat * v20.toNat + (v18.toNat * v10.toNat + v19.toNat * v12.toNat + v3.toNat * v11.toNat) * 2) % 2 ^ 64 := by
  obtain ⟨q_t66, e_t66⟩ := mod_q t66; clear t66
  obtain ⟨q_t76, e_t76⟩ := mod_q t76; clear t76
  obtain ⟨q_hw0_3_4_5, e_hw0_3_4_5⟩ := mod_q hw0_3_4_5; clear hw0_3_4_5
  obtain ⟨q_hs0_0_1_2, e_hs0_0_1_2⟩ := mod_q hs0_0_1_2; clear hs0_0_1_2
  have key : v59.toNat + 2 ^ 32 * v76.toNat + 2 ^ 64 * (q_t66 + q_t76 + q_hw0_3_4_5 + q_hs0_0_1_2) = v15.toNat * v15.toNat + v28.toNat * v21.toNat + v30.toNat * v20.toNat + (v18.toNat * v10.toNat + v19.toNat * v12.toNat + v3.toNat * v11.toNat) * 2 := by
    generalize v3.toNat = n3 at *
    generalize v10.toNat = n10 at *
    generalize v11.toNat = n11 at *
    generalize v12.toNat = n12 at *
    generalize v15.toNat = n15 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v20.toNat = n20 at *
    generalize v21.toNat = n21 at *
    generalize v28.toNat = n28 at *
    generalize v30.toNat = n30 at *
    generalize v49.toNat = n49 at *
    generalize v50.toNat = n50 at *
    generalize v54.toNat = n54 at *
    generalize v58.toNat = n58 at *
    generalize v59.toNat = n59 at *
    generalize v65.toNat = n65 at *
    generalize v66.toNat = n66 at *
    generalize v76.toNat = n76 at *
    omega
  exact mod64_of key

theorem fsq_s1_3_4 {v10 v12 v16 v17 v60 v61 v62 v63 v72 v74 v75 v77 : Word}
    (t74 : v74.toNat = (v63.toNat + v62.toNat) % 2 ^ 32)
    (t75 : v72.toNat + 2 ^ 32 * v75.toNat = v61.toNat + v60.toNat)
    (t77 : v77.toNat = (v75.toNat + v74.toNat) % 2 ^ 32)
    (hp1_3 : v60.toNat + 2 ^ 32 * v62.toNat = v16.toNat * v10.toNat)
    (hp1_4 : v61.toNat + 2 ^ 32 * v63.toNat = v17.toNat * v12.toNat) :
    v72.toNat + 2 ^ 32 * v77.toNat = (v16.toNat * v10.toNat + v17.toNat * v12.toNat) % 2 ^ 64 := by
  obtain ⟨q_t74, e_t74⟩ := mod_q t74; clear t74
  obtain ⟨q_t77, e_t77⟩ := mod_q t77; clear t77
  have key : v72.toNat + 2 ^ 32 * v77.toNat + 2 ^ 64 * (q_t74 + q_t77) = v16.toNat * v10.toNat + v17.toNat * v12.toNat := by
    generalize v10.toNat = n10 at *
    generalize v12.toNat = n12 at *
    generalize v16.toNat = n16 at *
    generalize v17.toNat = n17 at *
    generalize v60.toNat = n60 at *
    generalize v61.toNat = n61 at *
    generalize v62.toNat = n62 at *
    generalize v63.toNat = n63 at *
    generalize v72.toNat = n72 at *
    generalize v74.toNat = n74 at *
    generalize v75.toNat = n75 at *
    generalize v77.toNat = n77 at *
    omega
  exact mod64_of key

theorem fsq_w1_3_4 {v10 v12 v16 v17 v72 v77 v78 v79 v80 v84 : Word}
    (t78 : v78.toNat = v77.toNat * 2 ^ 1 % 2 ^ 32)
    (t79 : v79.toNat = v72.toNat / 2 ^ 31)
    (t80 : v80.toNat = v79.toNat + v78.toNat)
    (t84 : v84.toNat = v72.toNat * 2 ^ 1 % 2 ^ 32)
    (hs1_3_4 : v72.toNat + 2 ^ 32 * v77.toNat = (v16.toNat * v10.toNat + v17.toNat * v12.toNat) % 2 ^ 64) :
    v84.toNat + 2 ^ 32 * v80.toNat = ((v16.toNat * v10.toNat + v17.toNat * v12.toNat) * 2) % 2 ^ 64 := by
  have := v10.isLt; have := v12.isLt; have := v16.isLt; have := v17.isLt; have := v72.isLt; have := v77.isLt; have := v78.isLt; have := v79.isLt; have := v80.isLt; have := v84.isLt
  generalize v10.toNat = n10 at *
  generalize v12.toNat = n12 at *
  generalize v16.toNat = n16 at *
  generalize v17.toNat = n17 at *
  generalize v72.toNat = n72 at *
  generalize v77.toNat = n77 at *
  generalize v78.toNat = n78 at *
  generalize v79.toNat = n79 at *
  generalize v80.toNat = n80 at *
  generalize v84.toNat = n84 at *
  omega

theorem fsq_s1_0_1_2 {v8 v19 v20 v21 v48 v64 v67 v68 v69 v70 v71 v73 v81 v82 v83 v85 v86 v87 v88 v94 : Word}
    (t81 : v81.toNat = (v69.toNat + v68.toNat) % 2 ^ 32)
    (t82 : v82.toNat = (v81.toNat + v70.toNat) % 2 ^ 32)
    (t86 : v83.toNat + 2 ^ 32 * v86.toNat = v67.toNat + v71.toNat)
    (t87 : v85.toNat + 2 ^ 32 * v87.toNat = v73.toNat + v83.toNat)
    (t88 : v88.toNat = (v86.toNat + v82.toNat) % 2 ^ 32)
    (t94 : v94.toNat = (v88.toNat + v87.toNat) % 2 ^ 32)
    (hp1_0 : v67.toNat + 2 ^ 32 * v68.toNat = v48.toNat * v8.toNat)
    (hp1_2 : v71.toNat + 2 ^ 32 * v69.toNat = v64.toNat * v20.toNat)
    (hp1_1 : v73.toNat + 2 ^ 32 * v70.toNat = v19.toNat * v21.toNat) :
    v85.toNat + 2 ^ 32 * v94.toNat = (v48.toNat * v8.toNat + v19.toNat * v21.toNat + v64.toNat * v20.toNat) % 2 ^ 64 := by
  obtain ⟨q_t81, e_t81⟩ := mod_q t81; clear t81
  obtain ⟨q_t82, e_t82⟩ := mod_q t82; clear t82
  obtain ⟨q_t88, e_t88⟩ := mod_q t88; clear t88
  obtain ⟨q_t94, e_t94⟩ := mod_q t94; clear t94
  have key : v85.toNat + 2 ^ 32 * v94.toNat + 2 ^ 64 * (q_t81 + q_t82 + q_t88 + q_t94) = v48.toNat * v8.toNat + v19.toNat * v21.toNat + v64.toNat * v20.toNat := by
    generalize v8.toNat = n8 at *
    generalize v19.toNat = n19 at *
    generalize v20.toNat = n20 at *
    generalize v21.toNat = n21 at *
    generalize v48.toNat = n48 at *
    generalize v64.toNat = n64 at *
    generalize v67.toNat = n67 at *
    generalize v68.toNat = n68 at *
    generalize v69.toNat = n69 at *
    generalize v70.toNat = n70 at *
    generalize v71.toNat = n71 at *
    generalize v73.toNat = n73 at *
    generalize v81.toNat = n81 at *
    generalize v82.toNat = n82 at *
    generalize v83.toNat = n83 at *
    generalize v85.toNat = n85 at *
    generalize v86.toNat = n86 at *
    generalize v87.toNat = n87 at *
    generalize v88.toNat = n88 at *
    generalize v94.toNat = n94 at *
    omega
  exact mod64_of key

theorem fsq_w1_0_1_2_3_4 {v8 v10 v12 v16 v17 v19 v20 v21 v48 v64 v80 v84 v85 v89 v94 v95 v96 v99 : Word}
    (t95 : v89.toNat + 2 ^ 32 * v95.toNat = v84.toNat + v85.toNat)
    (t96 : v96.toNat = (v94.toNat + v95.toNat) % 2 ^ 32)
    (t99 : v99.toNat = (v96.toNat + v80.toNat) % 2 ^ 32)
    (hw1_3_4 : v84.toNat + 2 ^ 32 * v80.toNat = ((v16.toNat * v10.toNat + v17.toNat * v12.toNat) * 2) % 2 ^ 64)
    (hs1_0_1_2 : v85.toNat + 2 ^ 32 * v94.toNat = (v48.toNat * v8.toNat + v19.toNat * v21.toNat + v64.toNat * v20.toNat) % 2 ^ 64) :
    v89.toNat + 2 ^ 32 * v99.toNat = (v48.toNat * v8.toNat + v19.toNat * v21.toNat + v64.toNat * v20.toNat + (v16.toNat * v10.toNat + v17.toNat * v12.toNat) * 2) % 2 ^ 64 := by
  obtain ⟨q_t96, e_t96⟩ := mod_q t96; clear t96
  obtain ⟨q_t99, e_t99⟩ := mod_q t99; clear t99
  obtain ⟨q_hw1_3_4, e_hw1_3_4⟩ := mod_q hw1_3_4; clear hw1_3_4
  obtain ⟨q_hs1_0_1_2, e_hs1_0_1_2⟩ := mod_q hs1_0_1_2; clear hs1_0_1_2
  have key : v89.toNat + 2 ^ 32 * v99.toNat + 2 ^ 64 * (q_t96 + q_t99 + q_hw1_3_4 + q_hs1_0_1_2) = v48.toNat * v8.toNat + v19.toNat * v21.toNat + v64.toNat * v20.toNat + (v16.toNat * v10.toNat + v17.toNat * v12.toNat) * 2 := by
    generalize v8.toNat = n8 at *
    generalize v10.toNat = n10 at *
    generalize v12.toNat = n12 at *
    generalize v16.toNat = n16 at *
    generalize v17.toNat = n17 at *
    generalize v19.toNat = n19 at *
    generalize v20.toNat = n20 at *
    generalize v21.toNat = n21 at *
    generalize v48.toNat = n48 at *
    generalize v64.toNat = n64 at *
    generalize v80.toNat = n80 at *
    generalize v84.toNat = n84 at *
    generalize v85.toNat = n85 at *
    generalize v89.toNat = n89 at *
    generalize v94.toNat = n94 at *
    generalize v95.toNat = n95 at *
    generalize v96.toNat = n96 at *
    generalize v99.toNat = n99 at *
    omega
  exact mod64_of key

theorem fsq_s2_0_1 {v8 v16 v18 v48 v90 v91 v92 v93 v104 v105 v106 v109 : Word}
    (t104 : v104.toNat = (v93.toNat + v91.toNat) % 2 ^ 32)
    (t106 : v105.toNat + 2 ^ 32 * v106.toNat = v90.toNat + v92.toNat)
    (t109 : v109.toNat = (v104.toNat + v106.toNat) % 2 ^ 32)
    (hp2_1 : v90.toNat + 2 ^ 32 * v91.toNat = v18.toNat * v8.toNat)
    (hp2_0 : v92.toNat + 2 ^ 32 * v93.toNat = v48.toNat * v16.toNat) :
    v105.toNat + 2 ^ 32 * v109.toNat = (v48.toNat * v16.toNat + v18.toNat * v8.toNat) % 2 ^ 64 := by
  obtain ⟨q_t104, e_t104⟩ := mod_q t104; clear t104
  obtain ⟨q_t109, e_t109⟩ := mod_q t109; clear t109
  have key : v105.toNat + 2 ^ 32 * v109.toNat + 2 ^ 64 * (q_t104 + q_t109) = v48.toNat * v16.toNat + v18.toNat * v8.toNat := by
    generalize v8.toNat = n8 at *
    generalize v16.toNat = n16 at *
    generalize v18.toNat = n18 at *
    generalize v48.toNat = n48 at *
    generalize v90.toNat = n90 at *
    generalize v91.toNat = n91 at *
    generalize v92.toNat = n92 at *
    generalize v93.toNat = n93 at *
    generalize v104.toNat = n104 at *
    generalize v105.toNat = n105 at *
    generalize v106.toNat = n106 at *
    generalize v109.toNat = n109 at *
    omega
  exact mod64_of key

theorem fsq_s2_4_5 {v10 v12 v19 v64 v100 v101 v102 v103 v113 v114 v115 v118 : Word}
    (t114 : v114.toNat = (v102.toNat + v103.toNat) % 2 ^ 32)
    (t115 : v113.toNat + 2 ^ 32 * v115.toNat = v101.toNat + v100.toNat)
    (t118 : v118.toNat = (v114.toNat + v115.toNat) % 2 ^ 32)
    (hp2_4 : v100.toNat + 2 ^ 32 * v102.toNat = v19.toNat * v10.toNat)
    (hp2_5 : v101.toNat + 2 ^ 32 * v103.toNat = v64.toNat * v12.toNat) :
    v113.toNat + 2 ^ 32 * v118.toNat = (v19.toNat * v10.toNat + v64.toNat * v12.toNat) % 2 ^ 64 := by
  obtain ⟨q_t114, e_t114⟩ := mod_q t114; clear t114
  obtain ⟨q_t118, e_t118⟩ := mod_q t118; clear t118
  have key : v113.toNat + 2 ^ 32 * v118.toNat + 2 ^ 64 * (q_t114 + q_t118) = v19.toNat * v10.toNat + v64.toNat * v12.toNat := by
    generalize v10.toNat = n10 at *
    generalize v12.toNat = n12 at *
    generalize v19.toNat = n19 at *
    generalize v64.toNat = n64 at *
    generalize v100.toNat = n100 at *
    generalize v101.toNat = n101 at *
    generalize v102.toNat = n102 at *
    generalize v103.toNat = n103 at *
    generalize v113.toNat = n113 at *
    generalize v114.toNat = n114 at *
    generalize v115.toNat = n115 at *
    generalize v118.toNat = n118 at *
    omega
  exact mod64_of key

theorem fsq_w2_4_5 {v10 v12 v19 v64 v113 v118 v119 v120 v121 v122 : Word}
    (t119 : v119.toNat = v118.toNat * 2 ^ 1 % 2 ^ 32)
    (t120 : v120.toNat = v113.toNat / 2 ^ 31)
    (t121 : v121.toNat = v120.toNat + v119.toNat)
    (t122 : v122.toNat = v113.toNat * 2 ^ 1 % 2 ^ 32)
    (hs2_4_5 : v113.toNat + 2 ^ 32 * v118.toNat = (v19.toNat * v10.toNat + v64.toNat * v12.toNat) % 2 ^ 64) :
    v122.toNat + 2 ^ 32 * v121.toNat = ((v19.toNat * v10.toNat + v64.toNat * v12.toNat) * 2) % 2 ^ 64 := by
  have := v10.isLt; have := v12.isLt; have := v19.isLt; have := v64.isLt; have := v113.isLt; have := v118.isLt; have := v119.isLt; have := v120.isLt; have := v121.isLt; have := v122.isLt
  generalize v10.toNat = n10 at *
  generalize v12.toNat = n12 at *
  generalize v19.toNat = n19 at *
  generalize v64.toNat = n64 at *
  generalize v113.toNat = n113 at *
  generalize v118.toNat = n118 at *
  generalize v119.toNat = n119 at *
  generalize v120.toNat = n120 at *
  generalize v121.toNat = n121 at *
  generalize v122.toNat = n122 at *
  omega

theorem fsq_s2_0_1_2_3 {v6 v8 v16 v18 v20 v21 v30 v48 v105 v109 v110 v111 v112 v116 v123 v124 v125 v126 v129 v130 v131 v135 : Word}
    (t124 : v124.toNat = (v110.toNat + v109.toNat) % 2 ^ 32)
    (t125 : v123.toNat + 2 ^ 32 * v125.toNat = v111.toNat + v105.toNat)
    (t126 : v126.toNat = (v124.toNat + v112.toNat) % 2 ^ 32)
    (t129 : v129.toNat = (v126.toNat + v125.toNat) % 2 ^ 32)
    (t131 : v130.toNat + 2 ^ 32 * v131.toNat = v116.toNat + v123.toNat)
    (t135 : v135.toNat = (v129.toNat + v131.toNat) % 2 ^ 32)
    (hs2_0_1 : v105.toNat + 2 ^ 32 * v109.toNat = (v48.toNat * v16.toNat + v18.toNat * v8.toNat) % 2 ^ 64)
    (hp2_3 : v111.toNat + 2 ^ 32 * v110.toNat = v6.toNat * v20.toNat)
    (hp2_2 : v116.toNat + 2 ^ 32 * v112.toNat = v30.toNat * v21.toNat) :
    v130.toNat + 2 ^ 32 * v135.toNat = (v48.toNat * v16.toNat + v18.toNat * v8.toNat + v30.toNat * v21.toNat + v6.toNat * v20.toNat) % 2 ^ 64 := by
  obtain ⟨q_t124, e_t124⟩ := mod_q t124; clear t124
  obtain ⟨q_t126, e_t126⟩ := mod_q t126; clear t126
  obtain ⟨q_t129, e_t129⟩ := mod_q t129; clear t129
  obtain ⟨q_t135, e_t135⟩ := mod_q t135; clear t135
  obtain ⟨q_hs2_0_1, e_hs2_0_1⟩ := mod_q hs2_0_1; clear hs2_0_1
  have key : v130.toNat + 2 ^ 32 * v135.toNat + 2 ^ 64 * (q_t124 + q_t126 + q_t129 + q_t135 + q_hs2_0_1) = v48.toNat * v16.toNat + v18.toNat * v8.toNat + v30.toNat * v21.toNat + v6.toNat * v20.toNat := by
    generalize v6.toNat = n6 at *
    generalize v8.toNat = n8 at *
    generalize v16.toNat = n16 at *
    generalize v18.toNat = n18 at *
    generalize v20.toNat = n20 at *
    generalize v21.toNat = n21 at *
    generalize v30.toNat = n30 at *
    generalize v48.toNat = n48 at *
    generalize v105.toNat = n105 at *
    generalize v109.toNat = n109 at *
    generalize v110.toNat = n110 at *
    generalize v111.toNat = n111 at *
    generalize v112.toNat = n112 at *
    generalize v116.toNat = n116 at *
    generalize v123.toNat = n123 at *
    generalize v124.toNat = n124 at *
    generalize v125.toNat = n125 at *
    generalize v126.toNat = n126 at *
    generalize v129.toNat = n129 at *
    generalize v130.toNat = n130 at *
    generalize v131.toNat = n131 at *
    generalize v135.toNat = n135 at *
    omega
  exact mod64_of key

theorem fsq_w2_0_1_2_3_4_5 {v6 v8 v10 v12 v16 v18 v19 v20 v21 v30 v48 v64 v121 v122 v130 v132 v135 v136 v139 v147 : Word}
    (t136 : v132.toNat + 2 ^ 32 * v136.toNat = v130.toNat + v122.toNat)
    (t139 : v139.toNat = (v135.toNat + v136.toNat) % 2 ^ 32)
    (t147 : v147.toNat = (v139.toNat + v121.toNat) % 2 ^ 32)
    (hw2_4_5 : v122.toNat + 2 ^ 32 * v121.toNat = ((v19.toNat * v10.toNat + v64.toNat * v12.toNat) * 2) % 2 ^ 64)
    (hs2_0_1_2_3 : v130.toNat + 2 ^ 32 * v135.toNat = (v48.toNat * v16.toNat + v18.toNat * v8.toNat + v30.toNat * v21.toNat + v6.toNat * v20.toNat) % 2 ^ 64) :
    v132.toNat + 2 ^ 32 * v147.toNat = (v48.toNat * v16.toNat + v18.toNat * v8.toNat + v30.toNat * v21.toNat + v6.toNat * v20.toNat + (v19.toNat * v10.toNat + v64.toNat * v12.toNat) * 2) % 2 ^ 64 := by
  obtain ⟨q_t139, e_t139⟩ := mod_q t139; clear t139
  obtain ⟨q_t147, e_t147⟩ := mod_q t147; clear t147
  obtain ⟨q_hw2_4_5, e_hw2_4_5⟩ := mod_q hw2_4_5; clear hw2_4_5
  obtain ⟨q_hs2_0_1_2_3, e_hs2_0_1_2_3⟩ := mod_q hs2_0_1_2_3; clear hs2_0_1_2_3
  have key : v132.toNat + 2 ^ 32 * v147.toNat + 2 ^ 64 * (q_t139 + q_t147 + q_hw2_4_5 + q_hs2_0_1_2_3) = v48.toNat * v16.toNat + v18.toNat * v8.toNat + v30.toNat * v21.toNat + v6.toNat * v20.toNat + (v19.toNat * v10.toNat + v64.toNat * v12.toNat) * 2 := by
    generalize v6.toNat = n6 at *
    generalize v8.toNat = n8 at *
    generalize v10.toNat = n10 at *
    generalize v12.toNat = n12 at *
    generalize v16.toNat = n16 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v20.toNat = n20 at *
    generalize v21.toNat = n21 at *
    generalize v30.toNat = n30 at *
    generalize v48.toNat = n48 at *
    generalize v64.toNat = n64 at *
    generalize v121.toNat = n121 at *
    generalize v122.toNat = n122 at *
    generalize v130.toNat = n130 at *
    generalize v132.toNat = n132 at *
    generalize v135.toNat = n135 at *
    generalize v136.toNat = n136 at *
    generalize v139.toNat = n139 at *
    generalize v147.toNat = n147 at *
    omega
  exact mod64_of key

theorem fsq_s3_0_1 {v9 v16 v18 v48 v127 v128 v133 v134 v140 v145 v146 v148 : Word}
    (t145 : v145.toNat = (v133.toNat + v134.toNat) % 2 ^ 32)
    (t146 : v140.toNat + 2 ^ 32 * v146.toNat = v128.toNat + v127.toNat)
    (t148 : v148.toNat = (v145.toNat + v146.toNat) % 2 ^ 32)
    (hp3_0 : v127.toNat + 2 ^ 32 * v133.toNat = v48.toNat * v9.toNat)
    (hp3_1 : v128.toNat + 2 ^ 32 * v134.toNat = v18.toNat * v16.toNat) :
    v140.toNat + 2 ^ 32 * v148.toNat = (v48.toNat * v9.toNat + v18.toNat * v16.toNat) % 2 ^ 64 := by
  obtain ⟨q_t145, e_t145⟩ := mod_q t145; clear t145
  obtain ⟨q_t148, e_t148⟩ := mod_q t148; clear t148
  have key : v140.toNat + 2 ^ 32 * v148.toNat + 2 ^ 64 * (q_t145 + q_t148) = v48.toNat * v9.toNat + v18.toNat * v16.toNat := by
    generalize v9.toNat = n9 at *
    generalize v16.toNat = n16 at *
    generalize v18.toNat = n18 at *
    generalize v48.toNat = n48 at *
    generalize v127.toNat = n127 at *
    generalize v128.toNat = n128 at *
    generalize v133.toNat = n133 at *
    generalize v134.toNat = n134 at *
    generalize v140.toNat = n140 at *
    generalize v145.toNat = n145 at *
    generalize v146.toNat = n146 at *
    generalize v148.toNat = n148 at *
    omega
  exact mod64_of key

theorem fsq_s3_0_1_2 {v9 v16 v18 v21 v48 v64 v137 v138 v140 v148 v149 v150 v152 v153 : Word}
    (t150 : v150.toNat = (v148.toNat + v137.toNat) % 2 ^ 32)
    (t152 : v149.toNat + 2 ^ 32 * v152.toNat = v138.toNat + v140.toNat)
    (t153 : v153.toNat = (v150.toNat + v152.toNat) % 2 ^ 32)
    (hp3_2 : v138.toNat + 2 ^ 32 * v137.toNat = v64.toNat * v21.toNat)
    (hs3_0_1 : v140.toNat + 2 ^ 32 * v148.toNat = (v48.toNat * v9.toNat + v18.toNat * v16.toNat) % 2 ^ 64) :
    v149.toNat + 2 ^ 32 * v153.toNat = (v48.toNat * v9.toNat + v18.toNat * v16.toNat + v64.toNat * v21.toNat) % 2 ^ 64 := by
  obtain ⟨q_t150, e_t150⟩ := mod_q t150; clear t150
  obtain ⟨q_t153, e_t153⟩ := mod_q t153; clear t153
  obtain ⟨q_hs3_0_1, e_hs3_0_1⟩ := mod_q hs3_0_1; clear hs3_0_1
  have key : v149.toNat + 2 ^ 32 * v153.toNat + 2 ^ 64 * (q_t150 + q_t153 + q_hs3_0_1) = v48.toNat * v9.toNat + v18.toNat * v16.toNat + v64.toNat * v21.toNat := by
    generalize v9.toNat = n9 at *
    generalize v16.toNat = n16 at *
    generalize v18.toNat = n18 at *
    generalize v21.toNat = n21 at *
    generalize v48.toNat = n48 at *
    generalize v64.toNat = n64 at *
    generalize v137.toNat = n137 at *
    generalize v138.toNat = n138 at *
    generalize v140.toNat = n140 at *
    generalize v148.toNat = n148 at *
    generalize v149.toNat = n149 at *
    generalize v150.toNat = n150 at *
    generalize v152.toNat = n152 at *
    generalize v153.toNat = n153 at *
    omega
  exact mod64_of key

theorem fsq_s3_3_4 {v6 v10 v12 v17 v141 v142 v143 v144 v154 v155 v156 v157 : Word}
    (t155 : v155.toNat = (v143.toNat + v144.toNat) % 2 ^ 32)
    (t156 : v154.toNat + 2 ^ 32 * v156.toNat = v142.toNat + v141.toNat)
    (t157 : v157.toNat = (v155.toNat + v156.toNat) % 2 ^ 32)
    (hp3_3 : v141.toNat + 2 ^ 32 * v143.toNat = v17.toNat * v10.toNat)
    (hp3_4 : v142.toNat + 2 ^ 32 * v144.toNat = v6.toNat * v12.toNat) :
    v154.toNat + 2 ^ 32 * v157.toNat = (v17.toNat * v10.toNat + v6.toNat * v12.toNat) % 2 ^ 64 := by
  obtain ⟨q_t155, e_t155⟩ := mod_q t155; clear t155
  obtain ⟨q_t157, e_t157⟩ := mod_q t157; clear t157
  have key : v154.toNat + 2 ^ 32 * v157.toNat + 2 ^ 64 * (q_t155 + q_t157) = v17.toNat * v10.toNat + v6.toNat * v12.toNat := by
    generalize v6.toNat = n6 at *
    generalize v10.toNat = n10 at *
    generalize v12.toNat = n12 at *
    generalize v17.toNat = n17 at *
    generalize v141.toNat = n141 at *
    generalize v142.toNat = n142 at *
    generalize v143.toNat = n143 at *
    generalize v144.toNat = n144 at *
    generalize v154.toNat = n154 at *
    generalize v155.toNat = n155 at *
    generalize v156.toNat = n156 at *
    generalize v157.toNat = n157 at *
    omega
  exact mod64_of key

theorem fsq_w3_3_4 {v6 v10 v12 v17 v154 v157 v158 v159 v161 v163 : Word}
    (t158 : v158.toNat = v154.toNat * 2 ^ 1 % 2 ^ 32)
    (t159 : v159.toNat = v157.toNat * 2 ^ 1 % 2 ^ 32)
    (t161 : v161.toNat = v154.toNat / 2 ^ 31)
    (t163 : v163.toNat = v161.toNat + v159.toNat)
    (hs3_3_4 : v154.toNat + 2 ^ 32 * v157.toNat = (v17.toNat * v10.toNat + v6.toNat * v12.toNat) % 2 ^ 64) :
    v158.toNat + 2 ^ 32 * v163.toNat = ((v17.toNat * v10.toNat + v6.toNat * v12.toNat) * 2) % 2 ^ 64 := by
  have := v6.isLt; have := v10.isLt; have := v12.isLt; have := v17.isLt; have := v154.isLt; have := v157.isLt; have := v158.isLt; have := v159.isLt; have := v161.isLt; have := v163.isLt
  generalize v6.toNat = n6 at *
  generalize v10.toNat = n10 at *
  generalize v12.toNat = n12 at *
  generalize v17.toNat = n17 at *
  generalize v154.toNat = n154 at *
  generalize v157.toNat = n157 at *
  generalize v158.toNat = n158 at *
  generalize v159.toNat = n159 at *
  generalize v161.toNat = n161 at *
  generalize v163.toNat = n163 at *
  omega

theorem fsq_w3_0_1_2_3_4 {v6 v9 v10 v12 v16 v17 v18 v21 v48 v64 v149 v153 v158 v160 v162 v163 v164 v165 : Word}
    (t162 : v160.toNat + 2 ^ 32 * v162.toNat = v158.toNat + v149.toNat)
    (t164 : v164.toNat = (v162.toNat + v153.toNat) % 2 ^ 32)
    (t165 : v165.toNat = (v163.toNat + v164.toNat) % 2 ^ 32)
    (hs3_0_1_2 : v149.toNat + 2 ^ 32 * v153.toNat = (v48.toNat * v9.toNat + v18.toNat * v16.toNat + v64.toNat * v21.toNat) % 2 ^ 64)
    (hw3_3_4 : v158.toNat + 2 ^ 32 * v163.toNat = ((v17.toNat * v10.toNat + v6.toNat * v12.toNat) * 2) % 2 ^ 64) :
    v160.toNat + 2 ^ 32 * v165.toNat = (v48.toNat * v9.toNat + v18.toNat * v16.toNat + v64.toNat * v21.toNat + (v17.toNat * v10.toNat + v6.toNat * v12.toNat) * 2) % 2 ^ 64 := by
  obtain ⟨q_t164, e_t164⟩ := mod_q t164; clear t164
  obtain ⟨q_t165, e_t165⟩ := mod_q t165; clear t165
  obtain ⟨q_hs3_0_1_2, e_hs3_0_1_2⟩ := mod_q hs3_0_1_2; clear hs3_0_1_2
  obtain ⟨q_hw3_3_4, e_hw3_3_4⟩ := mod_q hw3_3_4; clear hw3_3_4
  have key : v160.toNat + 2 ^ 32 * v165.toNat + 2 ^ 64 * (q_t164 + q_t165 + q_hs3_0_1_2 + q_hw3_3_4) = v48.toNat * v9.toNat + v18.toNat * v16.toNat + v64.toNat * v21.toNat + (v17.toNat * v10.toNat + v6.toNat * v12.toNat) * 2 := by
    generalize v6.toNat = n6 at *
    generalize v9.toNat = n9 at *
    generalize v10.toNat = n10 at *
    generalize v12.toNat = n12 at *
    generalize v16.toNat = n16 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v21.toNat = n21 at *
    generalize v48.toNat = n48 at *
    generalize v64.toNat = n64 at *
    generalize v149.toNat = n149 at *
    generalize v153.toNat = n153 at *
    generalize v158.toNat = n158 at *
    generalize v160.toNat = n160 at *
    generalize v162.toNat = n162 at *
    generalize v163.toNat = n163 at *
    generalize v164.toNat = n164 at *
    generalize v165.toNat = n165 at *
    omega
  exact mod64_of key

theorem fsq_s4_4_5 {v4 v10 v12 v64 v166 v167 v169 v170 v182 v183 v184 v186 : Word}
    (t183 : v183.toNat = (v167.toNat + v170.toNat) % 2 ^ 32)
    (t184 : v182.toNat + 2 ^ 32 * v184.toNat = v169.toNat + v166.toNat)
    (t186 : v186.toNat = (v184.toNat + v183.toNat) % 2 ^ 32)
    (hp4_4 : v166.toNat + 2 ^ 32 * v167.toNat = v64.toNat * v10.toNat)
    (hp4_5 : v169.toNat + 2 ^ 32 * v170.toNat = v4.toNat * v12.toNat) :
    v182.toNat + 2 ^ 32 * v186.toNat = (v64.toNat * v10.toNat + v4.toNat * v12.toNat) % 2 ^ 64 := by
  obtain ⟨q_t183, e_t183⟩ := mod_q t183; clear t183
  obtain ⟨q_t186, e_t186⟩ := mod_q t186; clear t186
  have key : v182.toNat + 2 ^ 32 * v186.toNat + 2 ^ 64 * (q_t183 + q_t186) = v64.toNat * v10.toNat + v4.toNat * v12.toNat := by
    generalize v4.toNat = n4 at *
    generalize v10.toNat = n10 at *
    generalize v12.toNat = n12 at *
    generalize v64.toNat = n64 at *
    generalize v166.toNat = n166 at *
    generalize v167.toNat = n167 at *
    generalize v169.toNat = n169 at *
    generalize v170.toNat = n170 at *
    generalize v182.toNat = n182 at *
    generalize v183.toNat = n183 at *
    generalize v184.toNat = n184 at *
    generalize v186.toNat = n186 at *
    omega
  exact mod64_of key

theorem fsq_w4_4_5 {v4 v10 v12 v64 v182 v186 v187 v188 v190 v191 : Word}
    (t187 : v187.toNat = v186.toNat * 2 ^ 1 % 2 ^ 32)
    (t188 : v188.toNat = v182.toNat / 2 ^ 31)
    (t190 : v190.toNat = v188.toNat + v187.toNat)
    (t191 : v191.toNat = v182.toNat * 2 ^ 1 % 2 ^ 32)
    (hs4_4_5 : v182.toNat + 2 ^ 32 * v186.toNat = (v64.toNat * v10.toNat + v4.toNat * v12.toNat) % 2 ^ 64) :
    v191.toNat + 2 ^ 32 * v190.toNat = ((v64.toNat * v10.toNat + v4.toNat * v12.toNat) * 2) % 2 ^ 64 := by
  have := v4.isLt; have := v10.isLt; have := v12.isLt; have := v64.isLt; have := v182.isLt; have := v186.isLt; have := v187.isLt; have := v188.isLt; have := v190.isLt; have := v191.isLt
  generalize v4.toNat = n4 at *
  generalize v10.toNat = n10 at *
  generalize v12.toNat = n12 at *
  generalize v64.toNat = n64 at *
  generalize v182.toNat = n182 at *
  generalize v186.toNat = n186 at *
  generalize v187.toNat = n187 at *
  generalize v188.toNat = n188 at *
  generalize v190.toNat = n190 at *
  generalize v191.toNat = n191 at *
  omega

theorem fsq_s4_0_1_2 {v16 v17 v18 v19 v48 v176 v177 v178 v179 v180 v181 v192 v193 v194 v195 v196 v197 v198 v199 : Word}
    (t193 : v192.toNat + 2 ^ 32 * v193.toNat = v180.toNat + v179.toNat)
    (t194 : v194.toNat = (v181.toNat + v178.toNat) % 2 ^ 32)
    (t196 : v196.toNat = (v194.toNat + v176.toNat) % 2 ^ 32)
    (t197 : v195.toNat + 2 ^ 32 * v197.toNat = v177.toNat + v192.toNat)
    (t198 : v198.toNat = (v196.toNat + v193.toNat) % 2 ^ 32)
    (t199 : v199.toNat = (v197.toNat + v198.toNat) % 2 ^ 32)
    (hp4_0 : v177.toNat + 2 ^ 32 * v176.toNat = v48.toNat * v17.toNat)
    (hp4_1 : v179.toNat + 2 ^ 32 * v178.toNat = v18.toNat * v19.toNat)
    (hp4_2 : v180.toNat + 2 ^ 32 * v181.toNat = v16.toNat * v16.toNat) :
    v195.toNat + 2 ^ 32 * v199.toNat = (v48.toNat * v17.toNat + v18.toNat * v19.toNat + v16.toNat * v16.toNat) % 2 ^ 64 := by
  obtain ⟨q_t194, e_t194⟩ := mod_q t194; clear t194
  obtain ⟨q_t196, e_t196⟩ := mod_q t196; clear t196
  obtain ⟨q_t198, e_t198⟩ := mod_q t198; clear t198
  obtain ⟨q_t199, e_t199⟩ := mod_q t199; clear t199
  have key : v195.toNat + 2 ^ 32 * v199.toNat + 2 ^ 64 * (q_t194 + q_t196 + q_t198 + q_t199) = v48.toNat * v17.toNat + v18.toNat * v19.toNat + v16.toNat * v16.toNat := by
    generalize v16.toNat = n16 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v48.toNat = n48 at *
    generalize v176.toNat = n176 at *
    generalize v177.toNat = n177 at *
    generalize v178.toNat = n178 at *
    generalize v179.toNat = n179 at *
    generalize v180.toNat = n180 at *
    generalize v181.toNat = n181 at *
    generalize v192.toNat = n192 at *
    generalize v193.toNat = n193 at *
    generalize v194.toNat = n194 at *
    generalize v195.toNat = n195 at *
    generalize v196.toNat = n196 at *
    generalize v197.toNat = n197 at *
    generalize v198.toNat = n198 at *
    generalize v199.toNat = n199 at *
    omega
  exact mod64_of key

theorem fsq_s4_0_1_2_3 {v16 v17 v18 v19 v21 v48 v151 v185 v189 v195 v199 v200 v201 v202 v203 : Word}
    (t201 : v200.toNat + 2 ^ 32 * v201.toNat = v185.toNat + v195.toNat)
    (t202 : v202.toNat = (v199.toNat + v189.toNat) % 2 ^ 32)
    (t203 : v203.toNat = (v202.toNat + v201.toNat) % 2 ^ 32)
    (hp4_3 : v185.toNat + 2 ^ 32 * v189.toNat = v151.toNat * v21.toNat)
    (hs4_0_1_2 : v195.toNat + 2 ^ 32 * v199.toNat = (v48.toNat * v17.toNat + v18.toNat * v19.toNat + v16.toNat * v16.toNat) % 2 ^ 64) :
    v200.toNat + 2 ^ 32 * v203.toNat = (v48.toNat * v17.toNat + v18.toNat * v19.toNat + v16.toNat * v16.toNat + v151.toNat * v21.toNat) % 2 ^ 64 := by
  obtain ⟨q_t202, e_t202⟩ := mod_q t202; clear t202
  obtain ⟨q_t203, e_t203⟩ := mod_q t203; clear t203
  obtain ⟨q_hs4_0_1_2, e_hs4_0_1_2⟩ := mod_q hs4_0_1_2; clear hs4_0_1_2
  have key : v200.toNat + 2 ^ 32 * v203.toNat + 2 ^ 64 * (q_t202 + q_t203 + q_hs4_0_1_2) = v48.toNat * v17.toNat + v18.toNat * v19.toNat + v16.toNat * v16.toNat + v151.toNat * v21.toNat := by
    generalize v16.toNat = n16 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v21.toNat = n21 at *
    generalize v48.toNat = n48 at *
    generalize v151.toNat = n151 at *
    generalize v185.toNat = n185 at *
    generalize v189.toNat = n189 at *
    generalize v195.toNat = n195 at *
    generalize v199.toNat = n199 at *
    generalize v200.toNat = n200 at *
    generalize v201.toNat = n201 at *
    generalize v202.toNat = n202 at *
    generalize v203.toNat = n203 at *
    omega
  exact mod64_of key

theorem fsq_w4_0_1_2_3_4_5 {v4 v10 v12 v16 v17 v18 v19 v21 v48 v64 v151 v190 v191 v200 v203 v204 v205 v215 v218 : Word}
    (t205 : v204.toNat + 2 ^ 32 * v205.toNat = v200.toNat + v191.toNat)
    (t215 : v215.toNat = (v203.toNat + v205.toNat) % 2 ^ 32)
    (t218 : v218.toNat = (v190.toNat + v215.toNat) % 2 ^ 32)
    (hw4_4_5 : v191.toNat + 2 ^ 32 * v190.toNat = ((v64.toNat * v10.toNat + v4.toNat * v12.toNat) * 2) % 2 ^ 64)
    (hs4_0_1_2_3 : v200.toNat + 2 ^ 32 * v203.toNat = (v48.toNat * v17.toNat + v18.toNat * v19.toNat + v16.toNat * v16.toNat + v151.toNat * v21.toNat) % 2 ^ 64) :
    v204.toNat + 2 ^ 32 * v218.toNat = (v48.toNat * v17.toNat + v18.toNat * v19.toNat + v16.toNat * v16.toNat + v151.toNat * v21.toNat + (v64.toNat * v10.toNat + v4.toNat * v12.toNat) * 2) % 2 ^ 64 := by
  obtain ⟨q_t215, e_t215⟩ := mod_q t215; clear t215
  obtain ⟨q_t218, e_t218⟩ := mod_q t218; clear t218
  obtain ⟨q_hw4_4_5, e_hw4_4_5⟩ := mod_q hw4_4_5; clear hw4_4_5
  obtain ⟨q_hs4_0_1_2_3, e_hs4_0_1_2_3⟩ := mod_q hs4_0_1_2_3; clear hs4_0_1_2_3
  have key : v204.toNat + 2 ^ 32 * v218.toNat + 2 ^ 64 * (q_t215 + q_t218 + q_hw4_4_5 + q_hs4_0_1_2_3) = v48.toNat * v17.toNat + v18.toNat * v19.toNat + v16.toNat * v16.toNat + v151.toNat * v21.toNat + (v64.toNat * v10.toNat + v4.toNat * v12.toNat) * 2 := by
    generalize v4.toNat = n4 at *
    generalize v10.toNat = n10 at *
    generalize v12.toNat = n12 at *
    generalize v16.toNat = n16 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v21.toNat = n21 at *
    generalize v48.toNat = n48 at *
    generalize v64.toNat = n64 at *
    generalize v151.toNat = n151 at *
    generalize v190.toNat = n190 at *
    generalize v191.toNat = n191 at *
    generalize v200.toNat = n200 at *
    generalize v203.toNat = n203 at *
    generalize v204.toNat = n204 at *
    generalize v205.toNat = n205 at *
    generalize v215.toNat = n215 at *
    generalize v218.toNat = n218 at *
    omega
  exact mod64_of key

theorem fsq_s5_0_1_2 {v3 v9 v17 v18 v28 v48 v208 v210 v212 v213 v214 v216 v224 v225 v226 v227 v228 v229 v230 v231 : Word}
    (t224 : v224.toNat = (v212.toNat + v210.toNat) % 2 ^ 32)
    (t225 : v225.toNat = (v224.toNat + v208.toNat) % 2 ^ 32)
    (t227 : v226.toNat + 2 ^ 32 * v227.toNat = v214.toNat + v213.toNat)
    (t229 : v229.toNat = (v225.toNat + v227.toNat) % 2 ^ 32)
    (t230 : v228.toNat + 2 ^ 32 * v230.toNat = v216.toNat + v226.toNat)
    (t231 : v231.toNat = (v230.toNat + v229.toNat) % 2 ^ 32)
    (hp5_0 : v216.toNat + 2 ^ 32 * v208.toNat = v48.toNat * v3.toNat)
    (hp5_1 : v213.toNat + 2 ^ 32 * v210.toNat = v18.toNat * v17.toNat)
    (hp5_2 : v214.toNat + 2 ^ 32 * v212.toNat = v28.toNat * v9.toNat) :
    v228.toNat + 2 ^ 32 * v231.toNat = (v48.toNat * v3.toNat + v18.toNat * v17.toNat + v28.toNat * v9.toNat) % 2 ^ 64 := by
  obtain ⟨q_t224, e_t224⟩ := mod_q t224; clear t224
  obtain ⟨q_t225, e_t225⟩ := mod_q t225; clear t225
  obtain ⟨q_t229, e_t229⟩ := mod_q t229; clear t229
  obtain ⟨q_t231, e_t231⟩ := mod_q t231; clear t231
  have key : v228.toNat + 2 ^ 32 * v231.toNat + 2 ^ 64 * (q_t224 + q_t225 + q_t229 + q_t231) = v48.toNat * v3.toNat + v18.toNat * v17.toNat + v28.toNat * v9.toNat := by
    generalize v3.toNat = n3 at *
    generalize v9.toNat = n9 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v28.toNat = n28 at *
    generalize v48.toNat = n48 at *
    generalize v208.toNat = n208 at *
    generalize v210.toNat = n210 at *
    generalize v212.toNat = n212 at *
    generalize v213.toNat = n213 at *
    generalize v214.toNat = n214 at *
    generalize v216.toNat = n216 at *
    generalize v224.toNat = n224 at *
    generalize v225.toNat = n225 at *
    generalize v226.toNat = n226 at *
    generalize v227.toNat = n227 at *
    generalize v228.toNat = n228 at *
    generalize v229.toNat = n229 at *
    generalize v230.toNat = n230 at *
    generalize v231.toNat = n231 at *
    omega
  exact mod64_of key

theorem fsq_w5_4 {v6 v10 v206 v209 v220 v222 v223 v235 : Word}
    (t220 : v220.toNat = v206.toNat * 2 ^ 1 % 2 ^ 32)
    (t222 : v222.toNat = v209.toNat / 2 ^ 31)
    (t223 : v223.toNat = v222.toNat + v220.toNat)
    (t235 : v235.toNat = v209.toNat * 2 ^ 1 % 2 ^ 32)
    (hp5_4 : v209.toNat + 2 ^ 32 * v206.toNat = v6.toNat * v10.toNat) :
    v235.toNat + 2 ^ 32 * v223.toNat = (v6.toNat * v10.toNat * 2) % 2 ^ 64 := by
  have := v6.isLt; have := v10.isLt; have := v206.isLt; have := v209.isLt; have := v220.isLt; have := v222.isLt; have := v223.isLt; have := v235.isLt
  generalize v6.toNat = n6 at *
  generalize v10.toNat = n10 at *
  generalize v206.toNat = n206 at *
  generalize v209.toNat = n209 at *
  generalize v220.toNat = n220 at *
  generalize v222.toNat = n222 at *
  generalize v223.toNat = n223 at *
  generalize v235.toNat = n235 at *
  omega

theorem fsq_s5_0_1_2_3 {v3 v9 v17 v18 v21 v28 v48 v217 v219 v221 v228 v231 v232 v233 v234 v236 : Word}
    (t233 : v233.toNat = (v231.toNat + v221.toNat) % 2 ^ 32)
    (t234 : v232.toNat + 2 ^ 32 * v234.toNat = v219.toNat + v228.toNat)
    (t236 : v236.toNat = (v233.toNat + v234.toNat) % 2 ^ 32)
    (hp5_3 : v219.toNat + 2 ^ 32 * v221.toNat = v217.toNat * v21.toNat)
    (hs5_0_1_2 : v228.toNat + 2 ^ 32 * v231.toNat = (v48.toNat * v3.toNat + v18.toNat * v17.toNat + v28.toNat * v9.toNat) % 2 ^ 64) :
    v232.toNat + 2 ^ 32 * v236.toNat = (v48.toNat * v3.toNat + v18.toNat * v17.toNat + v28.toNat * v9.toNat + v217.toNat * v21.toNat) % 2 ^ 64 := by
  obtain ⟨q_t233, e_t233⟩ := mod_q t233; clear t233
  obtain ⟨q_t236, e_t236⟩ := mod_q t236; clear t236
  obtain ⟨q_hs5_0_1_2, e_hs5_0_1_2⟩ := mod_q hs5_0_1_2; clear hs5_0_1_2
  have key : v232.toNat + 2 ^ 32 * v236.toNat + 2 ^ 64 * (q_t233 + q_t236 + q_hs5_0_1_2) = v48.toNat * v3.toNat + v18.toNat * v17.toNat + v28.toNat * v9.toNat + v217.toNat * v21.toNat := by
    generalize v3.toNat = n3 at *
    generalize v9.toNat = n9 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v21.toNat = n21 at *
    generalize v28.toNat = n28 at *
    generalize v48.toNat = n48 at *
    generalize v217.toNat = n217 at *
    generalize v219.toNat = n219 at *
    generalize v221.toNat = n221 at *
    generalize v228.toNat = n228 at *
    generalize v231.toNat = n231 at *
    generalize v232.toNat = n232 at *
    generalize v233.toNat = n233 at *
    generalize v234.toNat = n234 at *
    generalize v236.toNat = n236 at *
    omega
  exact mod64_of key

theorem fsq_w5_0_1_2_3_4 {v3 v6 v9 v10 v17 v18 v21 v28 v48 v217 v223 v232 v235 v236 v237 v238 v239 v244 : Word}
    (t237 : v237.toNat = (v236.toNat + v223.toNat) % 2 ^ 32)
    (t239 : v238.toNat + 2 ^ 32 * v239.toNat = v235.toNat + v232.toNat)
    (t244 : v244.toNat = (v237.toNat + v239.toNat) % 2 ^ 32)
    (hw5_4 : v235.toNat + 2 ^ 32 * v223.toNat = (v6.toNat * v10.toNat * 2) % 2 ^ 64)
    (hs5_0_1_2_3 : v232.toNat + 2 ^ 32 * v236.toNat = (v48.toNat * v3.toNat + v18.toNat * v17.toNat + v28.toNat * v9.toNat + v217.toNat * v21.toNat) % 2 ^ 64) :
    v238.toNat + 2 ^ 32 * v244.toNat = (v48.toNat * v3.toNat + v18.toNat * v17.toNat + v28.toNat * v9.toNat + v217.toNat * v21.toNat + (v6.toNat * v10.toNat) * 2) % 2 ^ 64 := by
  obtain ⟨q_t237, e_t237⟩ := mod_q t237; clear t237
  obtain ⟨q_t244, e_t244⟩ := mod_q t244; clear t244
  obtain ⟨q_hw5_4, e_hw5_4⟩ := mod_q hw5_4; clear hw5_4
  obtain ⟨q_hs5_0_1_2_3, e_hs5_0_1_2_3⟩ := mod_q hs5_0_1_2_3; clear hs5_0_1_2_3
  have key : v238.toNat + 2 ^ 32 * v244.toNat + 2 ^ 64 * (q_t237 + q_t244 + q_hw5_4 + q_hs5_0_1_2_3) = v48.toNat * v3.toNat + v18.toNat * v17.toNat + v28.toNat * v9.toNat + v217.toNat * v21.toNat + (v6.toNat * v10.toNat) * 2 := by
    generalize v3.toNat = n3 at *
    generalize v6.toNat = n6 at *
    generalize v9.toNat = n9 at *
    generalize v10.toNat = n10 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v21.toNat = n21 at *
    generalize v28.toNat = n28 at *
    generalize v48.toNat = n48 at *
    generalize v217.toNat = n217 at *
    generalize v223.toNat = n223 at *
    generalize v232.toNat = n232 at *
    generalize v235.toNat = n235 at *
    generalize v236.toNat = n236 at *
    generalize v237.toNat = n237 at *
    generalize v238.toNat = n238 at *
    generalize v239.toNat = n239 at *
    generalize v244.toNat = n244 at *
    omega
  exact mod64_of key

theorem fsq_s6_1_2_3 {v9 v17 v18 v19 v28 v64 v245 v246 v247 v248 v249 v252 v257 v259 v263 v264 v265 v266 v267 v268 : Word}
    (t257 : v257.toNat = (v245.toNat + v246.toNat) % 2 ^ 32)
    (t259 : v259.toNat = (v257.toNat + v247.toNat) % 2 ^ 32)
    (t264 : v263.toNat + 2 ^ 32 * v264.toNat = v248.toNat + v249.toNat)
    (t266 : v265.toNat + 2 ^ 32 * v266.toNat = v252.toNat + v263.toNat)
    (t267 : v267.toNat = (v259.toNat + v264.toNat) % 2 ^ 32)
    (t268 : v268.toNat = (v267.toNat + v266.toNat) % 2 ^ 32)
    (hp6_2 : v248.toNat + 2 ^ 32 * v245.toNat = v28.toNat * v17.toNat)
    (hp6_3 : v249.toNat + 2 ^ 32 * v246.toNat = v19.toNat * v9.toNat)
    (hp6_1 : v252.toNat + 2 ^ 32 * v247.toNat = v18.toNat * v64.toNat) :
    v265.toNat + 2 ^ 32 * v268.toNat = (v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat) % 2 ^ 64 := by
  obtain ⟨q_t257, e_t257⟩ := mod_q t257; clear t257
  obtain ⟨q_t259, e_t259⟩ := mod_q t259; clear t259
  obtain ⟨q_t267, e_t267⟩ := mod_q t267; clear t267
  obtain ⟨q_t268, e_t268⟩ := mod_q t268; clear t268
  have key : v265.toNat + 2 ^ 32 * v268.toNat + 2 ^ 64 * (q_t257 + q_t259 + q_t267 + q_t268) = v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat := by
    generalize v9.toNat = n9 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v28.toNat = n28 at *
    generalize v64.toNat = n64 at *
    generalize v245.toNat = n245 at *
    generalize v246.toNat = n246 at *
    generalize v247.toNat = n247 at *
    generalize v248.toNat = n248 at *
    generalize v249.toNat = n249 at *
    generalize v252.toNat = n252 at *
    generalize v257.toNat = n257 at *
    generalize v259.toNat = n259 at *
    generalize v263.toNat = n263 at *
    generalize v264.toNat = n264 at *
    generalize v265.toNat = n265 at *
    generalize v266.toNat = n266 at *
    generalize v267.toNat = n267 at *
    generalize v268.toNat = n268 at *
    omega
  exact mod64_of key

theorem fsq_w6_5 {v10 v217 v240 v241 v253 v254 v255 v272 : Word}
    (t253 : v253.toNat = v240.toNat / 2 ^ 31)
    (t254 : v254.toNat = v241.toNat * 2 ^ 1 % 2 ^ 32)
    (t255 : v255.toNat = v253.toNat + v254.toNat)
    (t272 : v272.toNat = v240.toNat * 2 ^ 1 % 2 ^ 32)
    (hp6_5 : v240.toNat + 2 ^ 32 * v241.toNat = v217.toNat * v10.toNat) :
    v272.toNat + 2 ^ 32 * v255.toNat = (v217.toNat * v10.toNat * 2) % 2 ^ 64 := by
  have := v10.isLt; have := v217.isLt; have := v240.isLt; have := v241.isLt; have := v253.isLt; have := v254.isLt; have := v255.isLt; have := v272.isLt
  generalize v10.toNat = n10 at *
  generalize v217.toNat = n217 at *
  generalize v240.toNat = n240 at *
  generalize v241.toNat = n241 at *
  generalize v253.toNat = n253 at *
  generalize v254.toNat = n254 at *
  generalize v255.toNat = n255 at *
  generalize v272.toNat = n272 at *
  omega

theorem fsq_s6_0_1_2_3 {v6 v9 v17 v18 v19 v28 v48 v64 v256 v258 v265 v268 v269 v270 v271 v273 : Word}
    (t270 : v270.toNat = (v268.toNat + v258.toNat) % 2 ^ 32)
    (t271 : v269.toNat + 2 ^ 32 * v271.toNat = v256.toNat + v265.toNat)
    (t273 : v273.toNat = (v271.toNat + v270.toNat) % 2 ^ 32)
    (hp6_0 : v256.toNat + 2 ^ 32 * v258.toNat = v48.toNat * v6.toNat)
    (hs6_1_2_3 : v265.toNat + 2 ^ 32 * v268.toNat = (v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat) % 2 ^ 64) :
    v269.toNat + 2 ^ 32 * v273.toNat = (v48.toNat * v6.toNat + v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat) % 2 ^ 64 := by
  obtain ⟨q_t270, e_t270⟩ := mod_q t270; clear t270
  obtain ⟨q_t273, e_t273⟩ := mod_q t273; clear t273
  obtain ⟨q_hs6_1_2_3, e_hs6_1_2_3⟩ := mod_q hs6_1_2_3; clear hs6_1_2_3
  have key : v269.toNat + 2 ^ 32 * v273.toNat + 2 ^ 64 * (q_t270 + q_t273 + q_hs6_1_2_3) = v48.toNat * v6.toNat + v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat := by
    generalize v6.toNat = n6 at *
    generalize v9.toNat = n9 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v28.toNat = n28 at *
    generalize v48.toNat = n48 at *
    generalize v64.toNat = n64 at *
    generalize v256.toNat = n256 at *
    generalize v258.toNat = n258 at *
    generalize v265.toNat = n265 at *
    generalize v268.toNat = n268 at *
    generalize v269.toNat = n269 at *
    generalize v270.toNat = n270 at *
    generalize v271.toNat = n271 at *
    generalize v273.toNat = n273 at *
    omega
  exact mod64_of key

theorem fsq_s6_0_1_2_3_4 {v6 v9 v13 v17 v18 v19 v21 v28 v48 v64 v261 v262 v269 v273 v274 v275 v276 v282 : Word}
    (t274 : v274.toNat = (v273.toNat + v262.toNat) % 2 ^ 32)
    (t276 : v275.toNat + 2 ^ 32 * v276.toNat = v261.toNat + v269.toNat)
    (t282 : v282.toNat = (v274.toNat + v276.toNat) % 2 ^ 32)
    (hp6_4 : v261.toNat + 2 ^ 32 * v262.toNat = v13.toNat * v21.toNat)
    (hs6_0_1_2_3 : v269.toNat + 2 ^ 32 * v273.toNat = (v48.toNat * v6.toNat + v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat) % 2 ^ 64) :
    v275.toNat + 2 ^ 32 * v282.toNat = (v48.toNat * v6.toNat + v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat + v13.toNat * v21.toNat) % 2 ^ 64 := by
  obtain ⟨q_t274, e_t274⟩ := mod_q t274; clear t274
  obtain ⟨q_t282, e_t282⟩ := mod_q t282; clear t282
  obtain ⟨q_hs6_0_1_2_3, e_hs6_0_1_2_3⟩ := mod_q hs6_0_1_2_3; clear hs6_0_1_2_3
  have key : v275.toNat + 2 ^ 32 * v282.toNat + 2 ^ 64 * (q_t274 + q_t282 + q_hs6_0_1_2_3) = v48.toNat * v6.toNat + v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat + v13.toNat * v21.toNat := by
    generalize v6.toNat = n6 at *
    generalize v9.toNat = n9 at *
    generalize v13.toNat = n13 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v21.toNat = n21 at *
    generalize v28.toNat = n28 at *
    generalize v48.toNat = n48 at *
    generalize v64.toNat = n64 at *
    generalize v261.toNat = n261 at *
    generalize v262.toNat = n262 at *
    generalize v269.toNat = n269 at *
    generalize v273.toNat = n273 at *
    generalize v274.toNat = n274 at *
    generalize v275.toNat = n275 at *
    generalize v276.toNat = n276 at *
    generalize v282.toNat = n282 at *
    omega
  exact mod64_of key

theorem fsq_w6_0_1_2_3_4_5 {v6 v9 v10 v13 v17 v18 v19 v21 v28 v48 v64 v217 v255 v272 v275 v282 v283 v284 v285 v288 : Word}
    (t284 : v284.toNat = (v282.toNat + v255.toNat) % 2 ^ 32)
    (t285 : v283.toNat + 2 ^ 32 * v285.toNat = v272.toNat + v275.toNat)
    (t288 : v288.toNat = (v284.toNat + v285.toNat) % 2 ^ 32)
    (hw6_5 : v272.toNat + 2 ^ 32 * v255.toNat = (v217.toNat * v10.toNat * 2) % 2 ^ 64)
    (hs6_0_1_2_3_4 : v275.toNat + 2 ^ 32 * v282.toNat = (v48.toNat * v6.toNat + v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat + v13.toNat * v21.toNat) % 2 ^ 64) :
    v283.toNat + 2 ^ 32 * v288.toNat = (v48.toNat * v6.toNat + v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat + v13.toNat * v21.toNat + (v217.toNat * v10.toNat) * 2) % 2 ^ 64 := by
  obtain ⟨q_t284, e_t284⟩ := mod_q t284; clear t284
  obtain ⟨q_t288, e_t288⟩ := mod_q t288; clear t288
  obtain ⟨q_hw6_5, e_hw6_5⟩ := mod_q hw6_5; clear hw6_5
  obtain ⟨q_hs6_0_1_2_3_4, e_hs6_0_1_2_3_4⟩ := mod_q hs6_0_1_2_3_4; clear hs6_0_1_2_3_4
  have key : v283.toNat + 2 ^ 32 * v288.toNat + 2 ^ 64 * (q_t284 + q_t288 + q_hw6_5 + q_hs6_0_1_2_3_4) = v48.toNat * v6.toNat + v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat + v13.toNat * v21.toNat + (v217.toNat * v10.toNat) * 2 := by
    generalize v6.toNat = n6 at *
    generalize v9.toNat = n9 at *
    generalize v10.toNat = n10 at *
    generalize v13.toNat = n13 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v21.toNat = n21 at *
    generalize v28.toNat = n28 at *
    generalize v48.toNat = n48 at *
    generalize v64.toNat = n64 at *
    generalize v217.toNat = n217 at *
    generalize v255.toNat = n255 at *
    generalize v272.toNat = n272 at *
    generalize v275.toNat = n275 at *
    generalize v282.toNat = n282 at *
    generalize v283.toNat = n283 at *
    generalize v284.toNat = n284 at *
    generalize v285.toNat = n285 at *
    generalize v288.toNat = n288 at *
    omega
  exact mod64_of key

theorem fsq_s7_1_2_3 {v3 v6 v17 v18 v19 v28 v277 v278 v279 v280 v281 v286 v290 v292 v293 v295 v297 v299 v301 v303 : Word}
    (t290 : v290.toNat = (v278.toNat + v279.toNat) % 2 ^ 32)
    (t293 : v293.toNat = (v290.toNat + v277.toNat) % 2 ^ 32)
    (t295 : v292.toNat + 2 ^ 32 * v295.toNat = v281.toNat + v280.toNat)
    (t297 : v297.toNat = (v293.toNat + v295.toNat) % 2 ^ 32)
    (t301 : v299.toNat + 2 ^ 32 * v301.toNat = v286.toNat + v292.toNat)
    (t303 : v303.toNat = (v301.toNat + v297.toNat) % 2 ^ 32)
    (hp7_1 : v286.toNat + 2 ^ 32 * v277.toNat = v18.toNat * v6.toNat)
    (hp7_2 : v280.toNat + 2 ^ 32 * v278.toNat = v28.toNat * v3.toNat)
    (hp7_3 : v281.toNat + 2 ^ 32 * v279.toNat = v19.toNat * v17.toNat) :
    v299.toNat + 2 ^ 32 * v303.toNat = (v18.toNat * v6.toNat + v28.toNat * v3.toNat + v19.toNat * v17.toNat) % 2 ^ 64 := by
  obtain ⟨q_t290, e_t290⟩ := mod_q t290; clear t290
  obtain ⟨q_t293, e_t293⟩ := mod_q t293; clear t293
  obtain ⟨q_t297, e_t297⟩ := mod_q t297; clear t297
  obtain ⟨q_t303, e_t303⟩ := mod_q t303; clear t303
  have key : v299.toNat + 2 ^ 32 * v303.toNat + 2 ^ 64 * (q_t290 + q_t293 + q_t297 + q_t303) = v18.toNat * v6.toNat + v28.toNat * v3.toNat + v19.toNat * v17.toNat := by
    generalize v3.toNat = n3 at *
    generalize v6.toNat = n6 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v28.toNat = n28 at *
    generalize v277.toNat = n277 at *
    generalize v278.toNat = n278 at *
    generalize v279.toNat = n279 at *
    generalize v280.toNat = n280 at *
    generalize v281.toNat = n281 at *
    generalize v286.toNat = n286 at *
    generalize v290.toNat = n290 at *
    generalize v292.toNat = n292 at *
    generalize v293.toNat = n293 at *
    generalize v295.toNat = n295 at *
    generalize v297.toNat = n297 at *
    generalize v299.toNat = n299 at *
    generalize v301.toNat = n301 at *
    generalize v303.toNat = n303 at *
    omega
  exact mod64_of key

theorem fsq_w7_4 {v10 v13 v287 v289 v298 v300 v302 v304 : Word}
    (t298 : v298.toNat = v287.toNat / 2 ^ 31)
    (t300 : v300.toNat = v289.toNat * 2 ^ 1 % 2 ^ 32)
    (t302 : v302.toNat = v298.toNat + v300.toNat)
    (t304 : v304.toNat = v287.toNat * 2 ^ 1 % 2 ^ 32)
    (hp7_4 : v287.toNat + 2 ^ 32 * v289.toNat = v13.toNat * v10.toNat) :
    v304.toNat + 2 ^ 32 * v302.toNat = (v13.toNat * v10.toNat * 2) % 2 ^ 64 := by
  have := v10.isLt; have := v13.isLt; have := v287.isLt; have := v289.isLt; have := v298.isLt; have := v300.isLt; have := v302.isLt; have := v304.isLt
  generalize v10.toNat = n10 at *
  generalize v13.toNat = n13 at *
  generalize v287.toNat = n287 at *
  generalize v289.toNat = n289 at *
  generalize v298.toNat = n298 at *
  generalize v300.toNat = n300 at *
  generalize v302.toNat = n302 at *
  generalize v304.toNat = n304 at *
  omega

theorem fsq_s7_0_1_2_3 {v3 v4 v6 v17 v18 v19 v28 v48 v291 v294 v299 v303 v305 v306 v307 v308 : Word}
    (t306 : v306.toNat = (v294.toNat + v303.toNat) % 2 ^ 32)
    (t307 : v305.toNat + 2 ^ 32 * v307.toNat = v291.toNat + v299.toNat)
    (t308 : v308.toNat = (v306.toNat + v307.toNat) % 2 ^ 32)
    (hp7_0 : v291.toNat + 2 ^ 32 * v294.toNat = v48.toNat * v4.toNat)
    (hs7_1_2_3 : v299.toNat + 2 ^ 32 * v303.toNat = (v18.toNat * v6.toNat + v28.toNat * v3.toNat + v19.toNat * v17.toNat) % 2 ^ 64) :
    v305.toNat + 2 ^ 32 * v308.toNat = (v48.toNat * v4.toNat + v18.toNat * v6.toNat + v28.toNat * v3.toNat + v19.toNat * v17.toNat) % 2 ^ 64 := by
  obtain ⟨q_t306, e_t306⟩ := mod_q t306; clear t306
  obtain ⟨q_t308, e_t308⟩ := mod_q t308; clear t308
  obtain ⟨q_hs7_1_2_3, e_hs7_1_2_3⟩ := mod_q hs7_1_2_3; clear hs7_1_2_3
  have key : v305.toNat + 2 ^ 32 * v308.toNat + 2 ^ 64 * (q_t306 + q_t308 + q_hs7_1_2_3) = v48.toNat * v4.toNat + v18.toNat * v6.toNat + v28.toNat * v3.toNat + v19.toNat * v17.toNat := by
    generalize v3.toNat = n3 at *
    generalize v4.toNat = n4 at *
    generalize v6.toNat = n6 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v28.toNat = n28 at *
    generalize v48.toNat = n48 at *
    generalize v291.toNat = n291 at *
    generalize v294.toNat = n294 at *
    generalize v299.toNat = n299 at *
    generalize v303.toNat = n303 at *
    generalize v305.toNat = n305 at *
    generalize v306.toNat = n306 at *
    generalize v307.toNat = n307 at *
    generalize v308.toNat = n308 at *
    omega
  exact mod64_of key

theorem fsq_w7_0_1_2_3_4 {v3 v4 v6 v10 v13 v17 v18 v19 v28 v48 v302 v304 v305 v308 v309 v313 v314 v318 : Word}
    (t313 : v313.toNat = (v308.toNat + v302.toNat) % 2 ^ 32)
    (t314 : v309.toNat + 2 ^ 32 * v314.toNat = v304.toNat + v305.toNat)
    (t318 : v318.toNat = (v313.toNat + v314.toNat) % 2 ^ 32)
    (hw7_4 : v304.toNat + 2 ^ 32 * v302.toNat = (v13.toNat * v10.toNat * 2) % 2 ^ 64)
    (hs7_0_1_2_3 : v305.toNat + 2 ^ 32 * v308.toNat = (v48.toNat * v4.toNat + v18.toNat * v6.toNat + v28.toNat * v3.toNat + v19.toNat * v17.toNat) % 2 ^ 64) :
    v309.toNat + 2 ^ 32 * v318.toNat = (v48.toNat * v4.toNat + v18.toNat * v6.toNat + v28.toNat * v3.toNat + v19.toNat * v17.toNat + (v13.toNat * v10.toNat) * 2) % 2 ^ 64 := by
  obtain ⟨q_t313, e_t313⟩ := mod_q t313; clear t313
  obtain ⟨q_t318, e_t318⟩ := mod_q t318; clear t318
  obtain ⟨q_hw7_4, e_hw7_4⟩ := mod_q hw7_4; clear hw7_4
  obtain ⟨q_hs7_0_1_2_3, e_hs7_0_1_2_3⟩ := mod_q hs7_0_1_2_3; clear hs7_0_1_2_3
  have key : v309.toNat + 2 ^ 32 * v318.toNat + 2 ^ 64 * (q_t313 + q_t318 + q_hw7_4 + q_hs7_0_1_2_3) = v48.toNat * v4.toNat + v18.toNat * v6.toNat + v28.toNat * v3.toNat + v19.toNat * v17.toNat + (v13.toNat * v10.toNat) * 2 := by
    generalize v3.toNat = n3 at *
    generalize v4.toNat = n4 at *
    generalize v6.toNat = n6 at *
    generalize v10.toNat = n10 at *
    generalize v13.toNat = n13 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v28.toNat = n28 at *
    generalize v48.toNat = n48 at *
    generalize v302.toNat = n302 at *
    generalize v304.toNat = n304 at *
    generalize v305.toNat = n305 at *
    generalize v308.toNat = n308 at *
    generalize v309.toNat = n309 at *
    generalize v313.toNat = n313 at *
    generalize v314.toNat = n314 at *
    generalize v318.toNat = n318 at *
    omega
  exact mod64_of key

theorem fsq_s8_2_3_4 {v6 v17 v19 v28 v64 v310 v311 v315 v316 v317 v319 v323 v326 v330 v331 v332 v333 v334 v335 : Word}
    (t323 : v323.toNat = (v310.toNat + v311.toNat) % 2 ^ 32)
    (t326 : v326.toNat = (v315.toNat + v323.toNat) % 2 ^ 32)
    (t331 : v330.toNat + 2 ^ 32 * v331.toNat = v317.toNat + v316.toNat)
    (t333 : v333.toNat = (v326.toNat + v331.toNat) % 2 ^ 32)
    (t334 : v332.toNat + 2 ^ 32 * v334.toNat = v319.toNat + v330.toNat)
    (t335 : v335.toNat = (v333.toNat + v334.toNat) % 2 ^ 32)
    (hp8_2 : v316.toNat + 2 ^ 32 * v310.toNat = v28.toNat * v6.toNat)
    (hp8_4 : v317.toNat + 2 ^ 32 * v311.toNat = v17.toNat * v17.toNat)
    (hp8_3 : v319.toNat + 2 ^ 32 * v315.toNat = v19.toNat * v64.toNat) :
    v332.toNat + 2 ^ 32 * v335.toNat = (v28.toNat * v6.toNat + v19.toNat * v64.toNat + v17.toNat * v17.toNat) % 2 ^ 64 := by
  obtain ⟨q_t323, e_t323⟩ := mod_q t323; clear t323
  obtain ⟨q_t326, e_t326⟩ := mod_q t326; clear t326
  obtain ⟨q_t333, e_t333⟩ := mod_q t333; clear t333
  obtain ⟨q_t335, e_t335⟩ := mod_q t335; clear t335
  have key : v332.toNat + 2 ^ 32 * v335.toNat + 2 ^ 64 * (q_t323 + q_t326 + q_t333 + q_t335) = v28.toNat * v6.toNat + v19.toNat * v64.toNat + v17.toNat * v17.toNat := by
    generalize v6.toNat = n6 at *
    generalize v17.toNat = n17 at *
    generalize v19.toNat = n19 at *
    generalize v28.toNat = n28 at *
    generalize v64.toNat = n64 at *
    generalize v310.toNat = n310 at *
    generalize v311.toNat = n311 at *
    generalize v315.toNat = n315 at *
    generalize v316.toNat = n316 at *
    generalize v317.toNat = n317 at *
    generalize v319.toNat = n319 at *
    generalize v323.toNat = n323 at *
    generalize v326.toNat = n326 at *
    generalize v330.toNat = n330 at *
    generalize v331.toNat = n331 at *
    generalize v332.toNat = n332 at *
    generalize v333.toNat = n333 at *
    generalize v334.toNat = n334 at *
    generalize v335.toNat = n335 at *
    omega
  exact mod64_of key

theorem fsq_s8_0_1_2_3_4 {v6 v13 v17 v18 v19 v28 v48 v64 v217 v322 v324 v325 v332 v335 v336 v337 v338 v339 v340 v344 v349 v352 v353 : Word}
    (t338 : v336.toNat + 2 ^ 32 * v338.toNat = v332.toNat + v322.toNat)
    (t339 : v339.toNat = (v335.toNat + v325.toNat) % 2 ^ 32)
    (t340 : v340.toNat = (v338.toNat + v324.toNat) % 2 ^ 32)
    (t344 : v344.toNat = (v339.toNat + v340.toNat) % 2 ^ 32)
    (t352 : v349.toNat + 2 ^ 32 * v352.toNat = v337.toNat + v336.toNat)
    (t353 : v353.toNat = (v352.toNat + v344.toNat) % 2 ^ 32)
    (hp8_1 : v322.toNat + 2 ^ 32 * v325.toNat = v18.toNat * v217.toNat)
    (hp8_0 : v337.toNat + 2 ^ 32 * v324.toNat = v48.toNat * v13.toNat)
    (hs8_2_3_4 : v332.toNat + 2 ^ 32 * v335.toNat = (v28.toNat * v6.toNat + v19.toNat * v64.toNat + v17.toNat * v17.toNat) % 2 ^ 64) :
    v349.toNat + 2 ^ 32 * v353.toNat = (v48.toNat * v13.toNat + v18.toNat * v217.toNat + v28.toNat * v6.toNat + v19.toNat * v64.toNat + v17.toNat * v17.toNat) % 2 ^ 64 := by
  obtain ⟨q_t339, e_t339⟩ := mod_q t339; clear t339
  obtain ⟨q_t340, e_t340⟩ := mod_q t340; clear t340
  obtain ⟨q_t344, e_t344⟩ := mod_q t344; clear t344
  obtain ⟨q_t353, e_t353⟩ := mod_q t353; clear t353
  obtain ⟨q_hs8_2_3_4, e_hs8_2_3_4⟩ := mod_q hs8_2_3_4; clear hs8_2_3_4
  have key : v349.toNat + 2 ^ 32 * v353.toNat + 2 ^ 64 * (q_t339 + q_t340 + q_t344 + q_t353 + q_hs8_2_3_4) = v48.toNat * v13.toNat + v18.toNat * v217.toNat + v28.toNat * v6.toNat + v19.toNat * v64.toNat + v17.toNat * v17.toNat := by
    generalize v6.toNat = n6 at *
    generalize v13.toNat = n13 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v28.toNat = n28 at *
    generalize v48.toNat = n48 at *
    generalize v64.toNat = n64 at *
    generalize v217.toNat = n217 at *
    generalize v322.toNat = n322 at *
    generalize v324.toNat = n324 at *
    generalize v325.toNat = n325 at *
    generalize v332.toNat = n332 at *
    generalize v335.toNat = n335 at *
    generalize v336.toNat = n336 at *
    generalize v337.toNat = n337 at *
    generalize v338.toNat = n338 at *
    generalize v339.toNat = n339 at *
    generalize v340.toNat = n340 at *
    generalize v344.toNat = n344 at *
    generalize v349.toNat = n349 at *
    generalize v352.toNat = n352 at *
    generalize v353.toNat = n353 at *
    omega
  exact mod64_of key

theorem fsq_s9_2_3_4 {v3 v4 v6 v19 v28 v30 v345 v346 v347 v348 v350 v351 v359 v360 v361 v362 v363 v364 v365 v367 : Word}
    (t359 : v359.toNat = (v346.toNat + v348.toNat) % 2 ^ 32)
    (t361 : v361.toNat = (v350.toNat + v359.toNat) % 2 ^ 32)
    (t362 : v360.toNat + 2 ^ 32 * v362.toNat = v347.toNat + v345.toNat)
    (t363 : v363.toNat = (v361.toNat + v362.toNat) % 2 ^ 32)
    (t365 : v364.toNat + 2 ^ 32 * v365.toNat = v351.toNat + v360.toNat)
    (t367 : v367.toNat = (v363.toNat + v365.toNat) % 2 ^ 32)
    (hp9_3 : v345.toNat + 2 ^ 32 * v346.toNat = v19.toNat * v6.toNat)
    (hp9_4 : v347.toNat + 2 ^ 32 * v348.toNat = v30.toNat * v3.toNat)
    (hp9_2 : v351.toNat + 2 ^ 32 * v350.toNat = v28.toNat * v4.toNat) :
    v364.toNat + 2 ^ 32 * v367.toNat = (v28.toNat * v4.toNat + v19.toNat * v6.toNat + v30.toNat * v3.toNat) % 2 ^ 64 := by
  obtain ⟨q_t359, e_t359⟩ := mod_q t359; clear t359
  obtain ⟨q_t361, e_t361⟩ := mod_q t361; clear t361
  obtain ⟨q_t363, e_t363⟩ := mod_q t363; clear t363
  obtain ⟨q_t367, e_t367⟩ := mod_q t367; clear t367
  have key : v364.toNat + 2 ^ 32 * v367.toNat + 2 ^ 64 * (q_t359 + q_t361 + q_t363 + q_t367) = v28.toNat * v4.toNat + v19.toNat * v6.toNat + v30.toNat * v3.toNat := by
    generalize v3.toNat = n3 at *
    generalize v4.toNat = n4 at *
    generalize v6.toNat = n6 at *
    generalize v19.toNat = n19 at *
    generalize v28.toNat = n28 at *
    generalize v30.toNat = n30 at *
    generalize v345.toNat = n345 at *
    generalize v346.toNat = n346 at *
    generalize v347.toNat = n347 at *
    generalize v348.toNat = n348 at *
    generalize v350.toNat = n350 at *
    generalize v351.toNat = n351 at *
    generalize v359.toNat = n359 at *
    generalize v360.toNat = n360 at *
    generalize v361.toNat = n361 at *
    generalize v362.toNat = n362 at *
    generalize v363.toNat = n363 at *
    generalize v364.toNat = n364 at *
    generalize v365.toNat = n365 at *
    generalize v367.toNat = n367 at *
    omega
  exact mod64_of key

theorem fsq_w8_5 {v1 v10 v328 v329 v341 v342 v343 v372 : Word}
    (t341 : v341.toNat = v328.toNat / 2 ^ 31)
    (t342 : v342.toNat = v329.toNat * 2 ^ 1 % 2 ^ 32)
    (t343 : v343.toNat = v341.toNat + v342.toNat)
    (t372 : v372.toNat = v328.toNat * 2 ^ 1 % 2 ^ 32)
    (hp8_5 : v328.toNat + 2 ^ 32 * v329.toNat = v1.toNat * v10.toNat) :
    v372.toNat + 2 ^ 32 * v343.toNat = (v1.toNat * v10.toNat * 2) % 2 ^ 64 := by
  have := v1.isLt; have := v10.isLt; have := v328.isLt; have := v329.isLt; have := v341.isLt; have := v342.isLt; have := v343.isLt; have := v372.isLt
  generalize v1.toNat = n1 at *
  generalize v10.toNat = n10 at *
  generalize v328.toNat = n328 at *
  generalize v329.toNat = n329 at *
  generalize v341.toNat = n341 at *
  generalize v342.toNat = n342 at *
  generalize v343.toNat = n343 at *
  generalize v372.toNat = n372 at *
  omega

theorem fsq_w8_0_1_2_3_4_5 {v1 v6 v10 v13 v17 v18 v19 v28 v48 v64 v217 v343 v349 v353 v355 v372 v373 v375 v377 : Word}
    (t355 : v355.toNat = (v343.toNat + v353.toNat) % 2 ^ 32)
    (t375 : v373.toNat + 2 ^ 32 * v375.toNat = v372.toNat + v349.toNat)
    (t377 : v377.toNat = (v375.toNat + v355.toNat) % 2 ^ 32)
    (hw8_5 : v372.toNat + 2 ^ 32 * v343.toNat = (v1.toNat * v10.toNat * 2) % 2 ^ 64)
    (hs8_0_1_2_3_4 : v349.toNat + 2 ^ 32 * v353.toNat = (v48.toNat * v13.toNat + v18.toNat * v217.toNat + v28.toNat * v6.toNat + v19.toNat * v64.toNat + v17.toNat * v17.toNat) % 2 ^ 64) :
    v373.toNat + 2 ^ 32 * v377.toNat = (v48.toNat * v13.toNat + v18.toNat * v217.toNat + v28.toNat * v6.toNat + v19.toNat * v64.toNat + v17.toNat * v17.toNat + (v1.toNat * v10.toNat) * 2) % 2 ^ 64 := by
  obtain ⟨q_t355, e_t355⟩ := mod_q t355; clear t355
  obtain ⟨q_t377, e_t377⟩ := mod_q t377; clear t377
  obtain ⟨q_hw8_5, e_hw8_5⟩ := mod_q hw8_5; clear hw8_5
  obtain ⟨q_hs8_0_1_2_3_4, e_hs8_0_1_2_3_4⟩ := mod_q hs8_0_1_2_3_4; clear hs8_0_1_2_3_4
  have key : v373.toNat + 2 ^ 32 * v377.toNat + 2 ^ 64 * (q_t355 + q_t377 + q_hw8_5 + q_hs8_0_1_2_3_4) = v48.toNat * v13.toNat + v18.toNat * v217.toNat + v28.toNat * v6.toNat + v19.toNat * v64.toNat + v17.toNat * v17.toNat + (v1.toNat * v10.toNat) * 2 := by
    generalize v1.toNat = n1 at *
    generalize v6.toNat = n6 at *
    generalize v10.toNat = n10 at *
    generalize v13.toNat = n13 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v28.toNat = n28 at *
    generalize v48.toNat = n48 at *
    generalize v64.toNat = n64 at *
    generalize v217.toNat = n217 at *
    generalize v343.toNat = n343 at *
    generalize v349.toNat = n349 at *
    generalize v353.toNat = n353 at *
    generalize v355.toNat = n355 at *
    generalize v372.toNat = n372 at *
    generalize v373.toNat = n373 at *
    generalize v375.toNat = n375 at *
    generalize v377.toNat = n377 at *
    omega
  exact mod64_of key

theorem fsq_s9_0_1_2_3_4 {v1 v3 v4 v6 v13 v18 v19 v28 v30 v48 v354 v356 v357 v358 v364 v366 v367 v368 v369 v370 v371 v374 v376 v378 : Word}
    (t368 : v366.toNat + 2 ^ 32 * v368.toNat = v354.toNat + v364.toNat)
    (t369 : v369.toNat = (v358.toNat + v367.toNat) % 2 ^ 32)
    (t370 : v370.toNat = (v368.toNat + v357.toNat) % 2 ^ 32)
    (t371 : v371.toNat = (v369.toNat + v370.toNat) % 2 ^ 32)
    (t376 : v374.toNat + 2 ^ 32 * v376.toNat = v356.toNat + v366.toNat)
    (t378 : v378.toNat = (v371.toNat + v376.toNat) % 2 ^ 32)
    (hp9_1 : v354.toNat + 2 ^ 32 * v358.toNat = v18.toNat * v13.toNat)
    (hp9_0 : v356.toNat + 2 ^ 32 * v357.toNat = v48.toNat * v1.toNat)
    (hs9_2_3_4 : v364.toNat + 2 ^ 32 * v367.toNat = (v28.toNat * v4.toNat + v19.toNat * v6.toNat + v30.toNat * v3.toNat) % 2 ^ 64) :
    v374.toNat + 2 ^ 32 * v378.toNat = (v48.toNat * v1.toNat + v18.toNat * v13.toNat + v28.toNat * v4.toNat + v19.toNat * v6.toNat + v30.toNat * v3.toNat) % 2 ^ 64 := by
  obtain ⟨q_t369, e_t369⟩ := mod_q t369; clear t369
  obtain ⟨q_t370, e_t370⟩ := mod_q t370; clear t370
  obtain ⟨q_t371, e_t371⟩ := mod_q t371; clear t371
  obtain ⟨q_t378, e_t378⟩ := mod_q t378; clear t378
  obtain ⟨q_hs9_2_3_4, e_hs9_2_3_4⟩ := mod_q hs9_2_3_4; clear hs9_2_3_4
  have key : v374.toNat + 2 ^ 32 * v378.toNat + 2 ^ 64 * (q_t369 + q_t370 + q_t371 + q_t378 + q_hs9_2_3_4) = v48.toNat * v1.toNat + v18.toNat * v13.toNat + v28.toNat * v4.toNat + v19.toNat * v6.toNat + v30.toNat * v3.toNat := by
    generalize v1.toNat = n1 at *
    generalize v3.toNat = n3 at *
    generalize v4.toNat = n4 at *
    generalize v6.toNat = n6 at *
    generalize v13.toNat = n13 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v28.toNat = n28 at *
    generalize v30.toNat = n30 at *
    generalize v48.toNat = n48 at *
    generalize v354.toNat = n354 at *
    generalize v356.toNat = n356 at *
    generalize v357.toNat = n357 at *
    generalize v358.toNat = n358 at *
    generalize v364.toNat = n364 at *
    generalize v366.toNat = n366 at *
    generalize v367.toNat = n367 at *
    generalize v368.toNat = n368 at *
    generalize v369.toNat = n369 at *
    generalize v370.toNat = n370 at *
    generalize v371.toNat = n371 at *
    generalize v374.toNat = n374 at *
    generalize v376.toNat = n376 at *
    generalize v378.toNat = n378 at *
    omega
  exact mod64_of key

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **The body of `square_inner`**, from 0x1C to the restores at 0x4CC: the
ten `u64` sums it stores at `zo` are `feSqZ` of the operand's limbs, it
writes nothing outside its frame and the sums, and it leaves the frame
slots that hold the saved registers alone. -/
theorem fsq_body {M : Word → BitVec 8} {B F zo xp : Word} {n : Machine} (s : St M B n 0x1C (reg n))
    (hc : CodeIn M B feSquareInnerCode) (hsp : reg n sp = F) (ha0 : reg n a0 = zo) (ha1 : reg n a1 = xp)
    (hF : F.toNat % 4 = 0) (hZ : zo.toNat % 4 = 0) (hx : xp.toNat % 4 = 0)
    (sFC : Sep F 0x50 B feSquareInnerCode.length) (sZC : Sep zo 0x50 B feSquareInnerCode.length)
    (sXF : Sep xp 40 F 0x50) (sXZ : Sep xp 40 zo 0x50) (sFZ : Sep F 0x50 zo 0x50) :
    ∃ n' M', Steps n n' ∧ St M' B n' 0x4CC (reg n') ∧
      (∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M' x = M x) ∧
      memLoad32 M' (F + 0x1C) = memLoad32 M (F + 0x1C) ∧
      memLoad32 M' (F + 0x20) = memLoad32 M (F + 0x20) ∧
      memLoad32 M' (F + 0x24) = memLoad32 M (F + 0x24) ∧
      memLoad32 M' (F + 0x28) = memLoad32 M (F + 0x28) ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M (F + 0x4C) ∧
      [u64At M' zo 0, u64At M' zo 1, u64At M' zo 2, u64At M' zo 3, u64At M' zo 4, u64At M' zo 5,
        u64At M' zo 6, u64At M' zo 7, u64At M' zo 8, u64At M' zo 9] =
        feSqZ (limbAt M xp 0) (limbAt M xp 1) (limbAt M xp 2) (limbAt M xp 3) (limbAt M xp 4)
          (limbAt M xp 5) (limbAt M xp 6) (limbAt M xp 7) (limbAt M xp 8) (limbAt M xp 9) ∧
      reg n' sp = F ∧ reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  obtain ⟨G3, hG3⟩ : ∃ g, reg n (3 : Fin 32) = g := ⟨_, rfl⟩
  obtain ⟨G4, hG4⟩ : ∃ g, reg n (4 : Fin 32) = g := ⟨_, rfl⟩
  have fr0 : ∀ x, Sep F 0x50 x 1 → Sep zo 0x50 x 1 → M x = M x := fun _ _ _ => rfl
  have sg0_1C : memLoad32 M (F + 0x1C) = memLoad32 M (F + 0x1C) := rfl
  have sg0_20 : memLoad32 M (F + 0x20) = memLoad32 M (F + 0x20) := rfl
  have sg0_24 : memLoad32 M (F + 0x24) = memLoad32 M (F + 0x24) := rfl
  have sg0_28 : memLoad32 M (F + 0x28) = memLoad32 M (F + 0x28) := rfl
  have sg0_2C : memLoad32 M (F + 0x2C) = memLoad32 M (F + 0x2C) := rfl
  have sg0_30 : memLoad32 M (F + 0x30) = memLoad32 M (F + 0x30) := rfl
  have sg0_34 : memLoad32 M (F + 0x34) = memLoad32 M (F + 0x34) := rfl
  have sg0_38 : memLoad32 M (F + 0x38) = memLoad32 M (F + 0x38) := rfl
  have sg0_3C : memLoad32 M (F + 0x3C) = memLoad32 M (F + 0x3C) := rfl
  have sg0_40 : memLoad32 M (F + 0x40) = memLoad32 M (F + 0x40) := rfl
  have sg0_44 : memLoad32 M (F + 0x44) = memLoad32 M (F + 0x44) := rfl
  have sg0_48 : memLoad32 M (F + 0x48) = memLoad32 M (F + 0x48) := rfl
  have sg0_4C : memLoad32 M (F + 0x4C) = memLoad32 M (F + 0x4C) := rfl
  obtain ⟨ng0, Mg0, v1, v3, v4, v6, v7, v8, v9, v10, v11, v12, v13, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v28, v29, v30, v31, v32, v33, v35, v36, v37, v38, v39, hg0⟩ := fsq_g0 s hc fr0 hF hZ hx sFC sZC sXF sXZ sFZ hsp hG3 hG4 ha0 ha1 sg0_1C sg0_20 sg0_24 sg0_28 sg0_2C sg0_30 sg0_34 sg0_38 sg0_3C sg0_40 sg0_44 sg0_48 sg0_4C
  have cg0 := hg0.1
  have ug0 := hg0.2.1
  have hcg0 := hg0.2.2.1
  have frg0 := hg0.2.2.2.1
  have qg0_1 := hg0.2.2.2.2.1
  have qg0_2 := hg0.2.2.2.2.2.1
  have qg0_3 := hg0.2.2.2.2.2.2.1
  have qg0_4 := hg0.2.2.2.2.2.2.2.1
  have qg0_6 := hg0.2.2.2.2.2.2.2.2.1
  have qg0_8 := hg0.2.2.2.2.2.2.2.2.2.1
  have qg0_9 := hg0.2.2.2.2.2.2.2.2.2.2.1
  have qg0_10 := hg0.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_11 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_12 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_13 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_14 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_15 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_16 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_18 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_19 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_20 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_21 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_22 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_23 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_24 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_25 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_26 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_27 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_28 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_29 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_30 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg0_31 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_8 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_C := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_10 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_14 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_18 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_1C := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_20 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_24 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_28 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_2C := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_30 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_34 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_38 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_3C := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_40 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_44 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_48 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg1_4C := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv1 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv3 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv4 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv6 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv7 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv8 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv9 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv10 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv11 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv12 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv13 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv15 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv16 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv17 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv18 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv19 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv20 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv21 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv22 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv23 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv24 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv25 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv26 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv28 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv29 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv30 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv31 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv32 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv33 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv35 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv36 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv37 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv38 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv39 := hg0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨ng1, Mg1, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, hg1⟩ := fsq_g1 ug0 hcg0 frg0 hF hZ hx sFC sZC sXF sXZ sFZ qg0_1 qg0_2 qg0_3 qg0_4 qg0_6 qg0_8 qg0_9 qg0_10 qg0_11 qg0_12 qg0_13 qg0_14 qg0_15 qg0_16 qg0_18 qg0_19 qg0_20 qg0_21 qg0_22 qg0_23 qg0_24 qg0_25 qg0_26 qg0_27 qg0_28 qg0_29 qg0_30 qg0_31 sg1_8 sg1_C sg1_10 sg1_14 sg1_18 sg1_1C sg1_20 sg1_24 sg1_28 sg1_2C sg1_30 sg1_34 sg1_38 sg1_3C sg1_40 sg1_44 sg1_48 sg1_4C
  have cg1 := hg1.1
  have ug1 := hg1.2.1
  have hcg1 := hg1.2.2.1
  have frg1 := hg1.2.2.2.1
  have qg1_1 := hg1.2.2.2.2.1
  have qg1_2 := hg1.2.2.2.2.2.1
  have qg1_3 := hg1.2.2.2.2.2.2.1
  have qg1_4 := hg1.2.2.2.2.2.2.2.1
  have qg1_5 := hg1.2.2.2.2.2.2.2.2.1
  have qg1_6 := hg1.2.2.2.2.2.2.2.2.2.1
  have qg1_7 := hg1.2.2.2.2.2.2.2.2.2.2.1
  have qg1_8 := hg1.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_9 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_10 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_11 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_12 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_13 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_14 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_15 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_16 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_17 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_18 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_19 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_20 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_21 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_22 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_23 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_24 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_25 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_26 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_27 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_28 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_29 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_30 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg1_31 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_8 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_C := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_10 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_14 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_18 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_1C := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_20 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_24 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_28 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_2C := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_30 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_34 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_38 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_3C := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_40 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_44 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_48 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg2_4C := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv40 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv41 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv42 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv43 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv44 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv45 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv46 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv47 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv48 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv49 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv50 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv51 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv52 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv53 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv54 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv55 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv56 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv57 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv58 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv59 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv60 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv61 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv62 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv63 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv64 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv65 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv66 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv67 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv68 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv69 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv70 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv71 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv72 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv73 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv74 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv75 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv76 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv77 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv78 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv79 := hg1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨ng2, Mg2, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v99, v100, v101, v102, v103, v104, v105, v106, v109, v110, v111, v112, v113, v114, v115, v116, v118, v119, hg2⟩ := fsq_g2 ug1 hcg1 frg1 hF hZ hx sFC sZC sXF sXZ sFZ qg1_1 qg1_2 qg1_3 qg1_4 qg1_5 qg1_6 qg1_7 qg1_8 qg1_9 qg1_10 qg1_11 qg1_12 qg1_13 qg1_14 qg1_15 qg1_16 qg1_17 qg1_18 qg1_19 qg1_20 qg1_21 qg1_22 qg1_23 qg1_24 qg1_25 qg1_26 qg1_27 qg1_28 qg1_29 qg1_30 qg1_31 sg2_8 sg2_C sg2_10 sg2_14 sg2_18 sg2_1C sg2_20 sg2_24 sg2_28 sg2_2C sg2_30 sg2_34 sg2_38 sg2_3C sg2_40 sg2_44 sg2_48 sg2_4C
  have cg2 := hg2.1
  have ug2 := hg2.2.1
  have hcg2 := hg2.2.2.1
  have frg2 := hg2.2.2.2.1
  have qg2_1 := hg2.2.2.2.2.1
  have qg2_2 := hg2.2.2.2.2.2.1
  have qg2_3 := hg2.2.2.2.2.2.2.1
  have qg2_4 := hg2.2.2.2.2.2.2.2.1
  have qg2_5 := hg2.2.2.2.2.2.2.2.2.1
  have qg2_6 := hg2.2.2.2.2.2.2.2.2.2.1
  have qg2_7 := hg2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_8 := hg2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_9 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_10 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_11 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_12 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_13 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_14 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_15 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_16 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_17 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_18 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_19 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_20 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_21 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_22 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_23 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_24 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_25 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_26 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_27 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_28 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_29 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_30 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg2_31 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_8 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_C := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_10 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_14 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_18 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_1C := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_20 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_24 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_28 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_2C := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_30 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_34 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_38 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_3C := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_40 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_44 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_48 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_4C := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_zo0 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_zo4 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_zo8 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg3_zoC := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv80 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv81 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv82 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv83 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv84 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv85 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv86 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv87 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv88 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv89 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv90 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv91 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv92 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv93 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv94 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv95 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv96 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv99 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv100 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv101 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv102 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv103 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv104 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv105 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv106 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv109 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv110 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv111 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv112 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv113 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv114 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv115 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv116 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv118 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv119 := hg2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨ng3, Mg3, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, hg3⟩ := fsq_g3 ug2 hcg2 frg2 hF hZ hx sFC sZC sXF sXZ sFZ qg2_1 qg2_2 qg2_3 qg2_4 qg2_5 qg2_6 qg2_7 qg2_8 qg2_9 qg2_10 qg2_11 qg2_12 qg2_13 qg2_14 qg2_15 qg2_16 qg2_17 qg2_18 qg2_19 qg2_20 qg2_21 qg2_22 qg2_23 qg2_24 qg2_25 qg2_26 qg2_27 qg2_28 qg2_29 qg2_30 qg2_31 sg3_8 sg3_C sg3_10 sg3_14 sg3_18 sg3_1C sg3_20 sg3_24 sg3_28 sg3_2C sg3_30 sg3_34 sg3_38 sg3_3C sg3_40 sg3_44 sg3_48 sg3_4C sg3_zo0 sg3_zo4 sg3_zo8 sg3_zoC
  have cg3 := hg3.1
  have ug3 := hg3.2.1
  have hcg3 := hg3.2.2.1
  have frg3 := hg3.2.2.2.1
  have qg3_1 := hg3.2.2.2.2.1
  have qg3_2 := hg3.2.2.2.2.2.1
  have qg3_3 := hg3.2.2.2.2.2.2.1
  have qg3_4 := hg3.2.2.2.2.2.2.2.1
  have qg3_5 := hg3.2.2.2.2.2.2.2.2.1
  have qg3_6 := hg3.2.2.2.2.2.2.2.2.2.1
  have qg3_7 := hg3.2.2.2.2.2.2.2.2.2.2.1
  have qg3_8 := hg3.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_9 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_10 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_11 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_12 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_13 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_14 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_15 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_16 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_17 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_18 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_19 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_20 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_21 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_22 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_23 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_24 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_25 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_26 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_27 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_28 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_29 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_30 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg3_31 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_8 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_C := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_10 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_14 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_18 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_1C := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_20 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_24 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_28 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_2C := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_30 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_34 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_38 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_3C := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_40 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_44 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_48 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_4C := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_zo0 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_zo4 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_zo8 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg4_zoC := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv120 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv121 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv122 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv123 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv124 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv125 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv126 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv127 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv128 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv129 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv130 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv131 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv132 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv133 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv134 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv135 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv136 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv137 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv138 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv139 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv140 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv141 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv142 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv143 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv144 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv145 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv146 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv147 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv148 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv149 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv150 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv151 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv152 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv153 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv154 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv155 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv156 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv157 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv158 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv159 := hg3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨ng4, Mg4, v160, v161, v162, v163, v164, v165, v166, v167, v169, v170, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198, v199, hg4⟩ := fsq_g4 ug3 hcg3 frg3 hF hZ hx sFC sZC sXF sXZ sFZ qg3_1 qg3_2 qg3_3 qg3_4 qg3_5 qg3_6 qg3_7 qg3_8 qg3_9 qg3_10 qg3_11 qg3_12 qg3_13 qg3_14 qg3_15 qg3_16 qg3_17 qg3_18 qg3_19 qg3_20 qg3_21 qg3_22 qg3_23 qg3_24 qg3_25 qg3_26 qg3_27 qg3_28 qg3_29 qg3_30 qg3_31 sg4_8 sg4_C sg4_10 sg4_14 sg4_18 sg4_1C sg4_20 sg4_24 sg4_28 sg4_2C sg4_30 sg4_34 sg4_38 sg4_3C sg4_40 sg4_44 sg4_48 sg4_4C sg4_zo0 sg4_zo4 sg4_zo8 sg4_zoC
  have cg4 := hg4.1
  have ug4 := hg4.2.1
  have hcg4 := hg4.2.2.1
  have frg4 := hg4.2.2.2.1
  have qg4_1 := hg4.2.2.2.2.1
  have qg4_2 := hg4.2.2.2.2.2.1
  have qg4_3 := hg4.2.2.2.2.2.2.1
  have qg4_4 := hg4.2.2.2.2.2.2.2.1
  have qg4_5 := hg4.2.2.2.2.2.2.2.2.1
  have qg4_6 := hg4.2.2.2.2.2.2.2.2.2.1
  have qg4_7 := hg4.2.2.2.2.2.2.2.2.2.2.1
  have qg4_8 := hg4.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_9 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_10 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_11 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_12 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_13 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_14 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_15 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_16 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_17 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_18 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_19 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_20 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_21 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_22 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_23 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_24 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_25 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_26 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_27 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_28 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_29 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_30 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg4_31 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_8 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_10 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_14 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_18 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_1C := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_20 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_24 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_28 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_2C := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_30 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_34 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_38 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_3C := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_40 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_44 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_48 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_4C := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_zo0 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_zo4 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_zo8 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_zoC := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_zo10 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_zo14 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_zo18 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg5_zo1C := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv160 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv161 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv162 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv163 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv164 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv165 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv166 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv167 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv169 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv170 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv176 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv177 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv178 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv179 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv180 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv181 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv182 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv183 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv184 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv185 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv186 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv187 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv188 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv189 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv190 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv191 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv192 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv193 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv194 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv195 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv196 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv197 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv198 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv199 := hg4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨ng5, Mg5, v200, v201, v202, v203, v204, v205, v206, v208, v209, v210, v212, v213, v214, v215, v216, v217, v218, v219, v220, v221, v222, v223, v224, v225, v226, v227, v228, v229, v230, v231, v232, v233, v234, v235, v236, v237, v238, v239, hg5⟩ := fsq_g5 ug4 hcg4 frg4 hF hZ hx sFC sZC sXF sXZ sFZ qg4_1 qg4_2 qg4_3 qg4_4 qg4_5 qg4_6 qg4_7 qg4_8 qg4_9 qg4_10 qg4_11 qg4_12 qg4_13 qg4_14 qg4_15 qg4_16 qg4_17 qg4_18 qg4_19 qg4_20 qg4_21 qg4_22 qg4_23 qg4_24 qg4_25 qg4_26 qg4_27 qg4_28 qg4_29 qg4_30 qg4_31 sg5_8 sg5_10 sg5_14 sg5_18 sg5_1C sg5_20 sg5_24 sg5_28 sg5_2C sg5_30 sg5_34 sg5_38 sg5_3C sg5_40 sg5_44 sg5_48 sg5_4C sg5_zo0 sg5_zo4 sg5_zo8 sg5_zoC sg5_zo10 sg5_zo14 sg5_zo18 sg5_zo1C
  have cg5 := hg5.1
  have ug5 := hg5.2.1
  have hcg5 := hg5.2.2.1
  have frg5 := hg5.2.2.2.1
  have qg5_1 := hg5.2.2.2.2.1
  have qg5_2 := hg5.2.2.2.2.2.1
  have qg5_3 := hg5.2.2.2.2.2.2.1
  have qg5_4 := hg5.2.2.2.2.2.2.2.1
  have qg5_5 := hg5.2.2.2.2.2.2.2.2.1
  have qg5_6 := hg5.2.2.2.2.2.2.2.2.2.1
  have qg5_7 := hg5.2.2.2.2.2.2.2.2.2.2.1
  have qg5_8 := hg5.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_9 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_10 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_11 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_12 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_13 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_14 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_15 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_16 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_17 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_18 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_19 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_20 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_21 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_22 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_23 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_24 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_25 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_26 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_27 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_28 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_29 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_30 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg5_31 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_14 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_18 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_1C := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_20 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_24 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_28 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_2C := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_30 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_34 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_38 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_3C := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_40 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_44 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_48 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_4C := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_zo0 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_zo4 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_zo8 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_zoC := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_zo10 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_zo14 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_zo18 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg6_zo1C := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv200 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv201 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv202 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv203 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv204 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv205 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv206 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv208 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv209 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv210 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv212 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv213 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv214 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv215 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv216 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv217 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv218 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv219 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv220 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv221 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv222 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv223 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv224 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv225 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv226 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv227 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv228 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv229 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv230 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv231 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv232 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv233 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv234 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv235 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv236 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv237 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv238 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv239 := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨ng6, Mg6, v240, v241, v244, v245, v246, v247, v248, v249, v252, v253, v254, v255, v256, v257, v258, v259, v261, v262, v263, v264, v265, v266, v267, v268, v269, v270, v271, v272, v273, v274, v275, v276, v277, v278, v279, hg6⟩ := fsq_g6 ug5 hcg5 frg5 hF hZ hx sFC sZC sXF sXZ sFZ qg5_1 qg5_2 qg5_3 qg5_4 qg5_5 qg5_6 qg5_7 qg5_8 qg5_9 qg5_10 qg5_11 qg5_12 qg5_13 qg5_14 qg5_15 qg5_16 qg5_17 qg5_18 qg5_19 qg5_20 qg5_21 qg5_22 qg5_23 qg5_24 qg5_25 qg5_26 qg5_27 qg5_28 qg5_29 qg5_30 qg5_31 sg6_14 sg6_18 sg6_1C sg6_20 sg6_24 sg6_28 sg6_2C sg6_30 sg6_34 sg6_38 sg6_3C sg6_40 sg6_44 sg6_48 sg6_4C sg6_zo0 sg6_zo4 sg6_zo8 sg6_zoC sg6_zo10 sg6_zo14 sg6_zo18 sg6_zo1C
  have cg6 := hg6.1
  have ug6 := hg6.2.1
  have hcg6 := hg6.2.2.1
  have frg6 := hg6.2.2.2.1
  have qg6_1 := hg6.2.2.2.2.1
  have qg6_2 := hg6.2.2.2.2.2.1
  have qg6_3 := hg6.2.2.2.2.2.2.1
  have qg6_4 := hg6.2.2.2.2.2.2.2.1
  have qg6_5 := hg6.2.2.2.2.2.2.2.2.1
  have qg6_6 := hg6.2.2.2.2.2.2.2.2.2.1
  have qg6_7 := hg6.2.2.2.2.2.2.2.2.2.2.1
  have qg6_8 := hg6.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_9 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_10 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_11 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_12 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_13 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_14 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_15 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_16 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_17 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_18 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_19 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_20 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_21 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_22 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_23 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_24 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_25 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_26 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_27 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_28 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_29 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_30 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg6_31 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_18 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_1C := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_20 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_24 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_28 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_2C := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_30 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_34 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_38 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_3C := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_40 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_44 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_48 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_4C := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_zo0 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_zo4 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_zo8 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_zoC := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_zo10 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_zo14 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_zo18 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_zo1C := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_zo20 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_zo24 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_zo28 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg7_zo2C := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv240 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv241 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv244 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv245 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv246 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv247 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv248 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv249 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv252 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv253 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv254 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv255 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv256 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv257 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv258 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv259 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv261 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv262 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv263 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv264 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv265 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv266 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv267 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv268 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv269 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv270 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv271 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv272 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv273 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv274 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv275 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv276 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv277 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv278 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv279 := hg6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨ng7, Mg7, v280, v281, v282, v283, v284, v285, v286, v287, v288, v289, v290, v291, v292, v293, v294, v295, v297, v298, v299, v300, v301, v302, v303, v304, v305, v306, v307, v308, v309, v310, v311, v313, v314, v315, v316, v317, v318, v319, hg7⟩ := fsq_g7 ug6 hcg6 frg6 hF hZ hx sFC sZC sXF sXZ sFZ qg6_1 qg6_2 qg6_3 qg6_4 qg6_5 qg6_6 qg6_7 qg6_8 qg6_9 qg6_10 qg6_11 qg6_12 qg6_13 qg6_14 qg6_15 qg6_16 qg6_17 qg6_18 qg6_19 qg6_20 qg6_21 qg6_22 qg6_23 qg6_24 qg6_25 qg6_26 qg6_27 qg6_28 qg6_29 qg6_30 qg6_31 sg7_18 sg7_1C sg7_20 sg7_24 sg7_28 sg7_2C sg7_30 sg7_34 sg7_38 sg7_3C sg7_40 sg7_44 sg7_48 sg7_4C sg7_zo0 sg7_zo4 sg7_zo8 sg7_zoC sg7_zo10 sg7_zo14 sg7_zo18 sg7_zo1C sg7_zo20 sg7_zo24 sg7_zo28 sg7_zo2C
  have cg7 := hg7.1
  have ug7 := hg7.2.1
  have hcg7 := hg7.2.2.1
  have frg7 := hg7.2.2.2.1
  have qg7_1 := hg7.2.2.2.2.1
  have qg7_2 := hg7.2.2.2.2.2.1
  have qg7_3 := hg7.2.2.2.2.2.2.1
  have qg7_4 := hg7.2.2.2.2.2.2.2.1
  have qg7_5 := hg7.2.2.2.2.2.2.2.2.1
  have qg7_6 := hg7.2.2.2.2.2.2.2.2.2.1
  have qg7_7 := hg7.2.2.2.2.2.2.2.2.2.2.1
  have qg7_8 := hg7.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_9 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_10 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_11 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_12 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_13 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_14 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_15 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_16 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_17 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_18 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_19 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_20 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_21 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_22 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_23 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_24 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_25 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_26 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_27 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_28 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_29 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_30 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg7_31 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_18 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_1C := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_20 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_24 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_28 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_2C := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_30 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_34 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_38 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_3C := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_40 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_44 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_48 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_4C := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_zo0 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_zo4 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_zo8 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_zoC := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_zo10 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_zo14 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_zo18 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_zo1C := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_zo20 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_zo24 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_zo28 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_zo2C := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_zo30 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg8_zo34 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv280 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv281 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv282 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv283 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv284 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv285 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv286 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv287 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv288 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv289 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv290 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv291 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv292 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv293 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv294 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv295 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv297 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv298 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv299 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv300 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv301 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv302 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv303 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv304 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv305 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv306 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv307 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv308 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv309 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv310 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv311 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv313 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv314 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv315 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv316 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv317 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv318 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv319 := hg7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨ng8, Mg8, v322, v323, v324, v325, v326, v328, v329, v330, v331, v332, v333, v334, v335, v336, v337, v338, v339, v340, v341, v342, v343, v344, v345, v346, v347, v348, v349, v350, v351, v352, v353, v354, v355, v356, v357, v358, v359, hg8⟩ := fsq_g8 ug7 hcg7 frg7 hF hZ hx sFC sZC sXF sXZ sFZ qg7_1 qg7_2 qg7_3 qg7_4 qg7_5 qg7_6 qg7_7 qg7_8 qg7_9 qg7_10 qg7_11 qg7_12 qg7_13 qg7_14 qg7_15 qg7_16 qg7_17 qg7_18 qg7_19 qg7_20 qg7_21 qg7_22 qg7_23 qg7_24 qg7_25 qg7_26 qg7_27 qg7_28 qg7_29 qg7_30 qg7_31 sg8_18 sg8_1C sg8_20 sg8_24 sg8_28 sg8_2C sg8_30 sg8_34 sg8_38 sg8_3C sg8_40 sg8_44 sg8_48 sg8_4C sg8_zo0 sg8_zo4 sg8_zo8 sg8_zoC sg8_zo10 sg8_zo14 sg8_zo18 sg8_zo1C sg8_zo20 sg8_zo24 sg8_zo28 sg8_zo2C sg8_zo30 sg8_zo34
  have cg8 := hg8.1
  have ug8 := hg8.2.1
  have hcg8 := hg8.2.2.1
  have frg8 := hg8.2.2.2.1
  have qg8_1 := hg8.2.2.2.2.1
  have qg8_2 := hg8.2.2.2.2.2.1
  have qg8_3 := hg8.2.2.2.2.2.2.1
  have qg8_4 := hg8.2.2.2.2.2.2.2.1
  have qg8_5 := hg8.2.2.2.2.2.2.2.2.1
  have qg8_6 := hg8.2.2.2.2.2.2.2.2.2.1
  have qg8_7 := hg8.2.2.2.2.2.2.2.2.2.2.1
  have qg8_8 := hg8.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_9 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_10 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_11 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_12 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_13 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_14 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_15 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_16 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_17 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_18 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_19 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_20 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_21 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_22 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_23 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_24 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_25 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_26 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_27 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_28 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_29 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_30 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg8_31 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_1C := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_20 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_24 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_28 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_2C := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_30 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_34 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_38 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_3C := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_40 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_44 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_48 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_4C := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo0 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo4 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo8 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zoC := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo10 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo14 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo18 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo1C := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo20 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo24 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo28 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo2C := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo30 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo34 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo38 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg9_zo3C := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv322 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv323 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv324 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv325 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv326 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv328 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv329 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv330 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv331 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv332 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv333 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv334 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv335 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv336 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv337 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv338 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv339 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv340 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv341 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv342 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv343 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv344 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv345 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv346 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv347 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv348 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv349 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv350 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv351 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv352 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv353 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv354 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv355 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv356 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv357 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv358 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv359 := hg8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨ng9, Mg9, v360, v361, v362, v363, v364, v365, v366, v367, v368, v369, v370, v371, v372, v373, v374, v375, v376, v377, v378, hg9⟩ := fsq_g9 ug8 hcg8 frg8 hF hZ hx sFC sZC sXF sXZ sFZ qg8_1 qg8_2 qg8_3 qg8_4 qg8_5 qg8_6 qg8_7 qg8_8 qg8_9 qg8_10 qg8_11 qg8_12 qg8_13 qg8_14 qg8_15 qg8_16 qg8_17 qg8_18 qg8_19 qg8_20 qg8_21 qg8_22 qg8_23 qg8_24 qg8_25 qg8_26 qg8_27 qg8_28 qg8_29 qg8_30 qg8_31 sg9_1C sg9_20 sg9_24 sg9_28 sg9_2C sg9_30 sg9_34 sg9_38 sg9_3C sg9_40 sg9_44 sg9_48 sg9_4C sg9_zo0 sg9_zo4 sg9_zo8 sg9_zoC sg9_zo10 sg9_zo14 sg9_zo18 sg9_zo1C sg9_zo20 sg9_zo24 sg9_zo28 sg9_zo2C sg9_zo30 sg9_zo34 sg9_zo38 sg9_zo3C
  have cg9 := hg9.1
  have ug9 := hg9.2.1
  have hcg9 := hg9.2.2.1
  have frg9 := hg9.2.2.2.1
  have qg9_1 := hg9.2.2.2.2.1
  have qg9_2 := hg9.2.2.2.2.2.1
  have qg9_3 := hg9.2.2.2.2.2.2.1
  have qg9_4 := hg9.2.2.2.2.2.2.2.1
  have qg9_5 := hg9.2.2.2.2.2.2.2.2.1
  have qg9_6 := hg9.2.2.2.2.2.2.2.2.2.1
  have qg9_7 := hg9.2.2.2.2.2.2.2.2.2.2.1
  have qg9_8 := hg9.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_9 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_10 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_11 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_12 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_13 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_14 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_15 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_16 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_17 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_18 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_19 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_20 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_21 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_22 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_23 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_24 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_25 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_26 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_27 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_28 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_29 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_30 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have qg9_31 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_1C := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_20 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_24 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_28 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_2C := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_30 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_34 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_38 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_3C := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_40 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_44 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_48 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_4C := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo0 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo4 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo8 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zoC := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo10 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo14 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo18 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo1C := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo20 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo24 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo28 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo2C := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo30 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo34 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo38 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo3C := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo40 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo44 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo48 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sg10_zo4C := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv360 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv361 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv362 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv363 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv364 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv365 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv366 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv367 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv368 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv369 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv370 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv371 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv372 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv373 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv374 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv375 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv376 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv377 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv378 := hg9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have c7 : v7 = 0x13 := by rw [← hv7]; try rfl
  have t7 : v7.toNat = 19 := by rw [c7]; rfl
  have t10 : v10.toNat = v1.toNat * 19 % 2 ^ 32 := by rw [tn_mul hv10, t7]
  have t11 : v11.toNat = v3.toNat * 19 % 2 ^ 32 := by rw [tn_mul hv11, t7]
  have t12 : v12.toNat = v4.toNat * 19 % 2 ^ 32 := by rw [tn_mul hv12, t7]
  have t18 : v18.toNat = v8.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv18
  have t19 : v19.toNat = v9.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv19
  have t20 : v20.toNat = v6.toNat * 19 % 2 ^ 32 := by rw [tn_mul hv20, t7]
  have t21 : v21.toNat = v13.toNat * 19 % 2 ^ 32 := by rw [tn_mul hv21, t7]
  have t22 : v22.toNat = v10.toNat * v18.toNat / 2 ^ 32 := tn_mulhu hv22
  have t23 : v23.toNat = v12.toNat * v19.toNat / 2 ^ 32 := tn_mulhu hv23
  have t24 : v24.toNat = v11.toNat * v3.toNat / 2 ^ 32 := tn_mulhu hv24
  have t25 : v25.toNat = v12.toNat * v19.toNat % 2 ^ 32 := tn_mul hv25
  have t26 : v26.toNat = v11.toNat * v3.toNat % 2 ^ 32 := tn_mul hv26
  have t28 : v28.toNat = v16.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv28
  have t29 : v29.toNat = v10.toNat * v18.toNat % 2 ^ 32 := tn_mul hv29
  have t30 : v30.toNat = v17.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv30
  have t31 : v31.toNat = v15.toNat * v15.toNat / 2 ^ 32 := tn_mulhu hv31
  have t32 : v32.toNat = v15.toNat * v15.toNat % 2 ^ 32 := tn_mul hv32
  have t33 : v33.toNat = v21.toNat * v28.toNat / 2 ^ 32 := tn_mulhu hv33
  have t35 : v35.toNat = (v23.toNat + v24.toNat) % 2 ^ 32 := tn_add hv35
  have t36 : v36.toNat = v20.toNat * v30.toNat / 2 ^ 32 := tn_mulhu hv36
  have t37 : v37.toNat = (v26.toNat + v25.toNat) % 2 ^ 32 := tn_add hv37
  have t38 : v38.toNat = (v22.toNat + v35.toNat) % 2 ^ 32 := tn_add hv38
  have t39 : v39.toNat = v20.toNat * v30.toNat % 2 ^ 32 := tn_mul hv39
  have t40 : v37.toNat + 2 ^ 32 * v40.toNat = v26.toNat + v25.toNat := fmP1 hv37 (.inr hv40)
  have t41 : v41.toNat = (v29.toNat + v37.toNat) % 2 ^ 32 := tn_add hv41
  have t42 : v42.toNat = (v38.toNat + v40.toNat) % 2 ^ 32 := tn_add hv42
  have t43 : v43.toNat = v21.toNat * v28.toNat % 2 ^ 32 := tn_mul hv43
  have t44 : v41.toNat + 2 ^ 32 * v44.toNat = v29.toNat + v37.toNat := fmP1 hv41 (.inr hv44)
  have t45 : v45.toNat = (v42.toNat + v44.toNat) % 2 ^ 32 := tn_add hv45
  have t46 : v46.toNat = v41.toNat / 2 ^ 31 := tn_srl hv46
  have t47 : v47.toNat = v45.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv47
  have t48 : v48.toNat = v15.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv48
  have t49 : v49.toNat = v46.toNat + v47.toNat := tn_orS' 31 (by decide) hv49 t46 t47
  have t50 : v50.toNat = v41.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv50
  have t51 : v51.toNat = (v32.toNat + v39.toNat) % 2 ^ 32 := tn_add hv51
  have t52 : v51.toNat + 2 ^ 32 * v52.toNat = v32.toNat + v39.toNat := fmP1 hv51 (.inr hv52)
  have t53 : v53.toNat = (v31.toNat + v36.toNat) % 2 ^ 32 := tn_add hv53
  have t54 : v54.toNat = (v43.toNat + v51.toNat) % 2 ^ 32 := tn_add hv54
  have t55 : v55.toNat = (v53.toNat + v33.toNat) % 2 ^ 32 := tn_add hv55
  have t56 : v54.toNat + 2 ^ 32 * v56.toNat = v43.toNat + v51.toNat := fmP1 hv54 (.inr hv56)
  have t57 : v57.toNat = (v52.toNat + v55.toNat) % 2 ^ 32 := tn_add hv57
  have t58 : v58.toNat = (v57.toNat + v56.toNat) % 2 ^ 32 := tn_add hv58
  have t59 : v59.toNat = (v54.toNat + v50.toNat) % 2 ^ 32 := tn_add hv59
  have t60 : v60.toNat = v10.toNat * v16.toNat % 2 ^ 32 := tn_mul hv60
  have t61 : v61.toNat = v12.toNat * v17.toNat % 2 ^ 32 := tn_mul hv61
  have t62 : v62.toNat = v10.toNat * v16.toNat / 2 ^ 32 := tn_mulhu hv62
  have t63 : v63.toNat = v12.toNat * v17.toNat / 2 ^ 32 := tn_mulhu hv63
  have t64 : v64.toNat = v3.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv64
  have t65 : v59.toNat + 2 ^ 32 * v65.toNat = v54.toNat + v50.toNat := fmP1 hv59 (.inl hv65)
  have t66 : v66.toNat = (v65.toNat + v58.toNat) % 2 ^ 32 := tn_add hv66
  have t67 : v67.toNat = v48.toNat * v8.toNat % 2 ^ 32 := tn_mul hv67
  have t68 : v68.toNat = v48.toNat * v8.toNat / 2 ^ 32 := tn_mulhu hv68
  have t69 : v69.toNat = v20.toNat * v64.toNat / 2 ^ 32 := tn_mulhu hv69
  have t70 : v70.toNat = v21.toNat * v19.toNat / 2 ^ 32 := tn_mulhu hv70
  have t71 : v71.toNat = v20.toNat * v64.toNat % 2 ^ 32 := tn_mul hv71
  have t72 : v72.toNat = (v61.toNat + v60.toNat) % 2 ^ 32 := tn_add hv72
  have t73 : v73.toNat = v21.toNat * v19.toNat % 2 ^ 32 := tn_mul hv73
  have t74 : v74.toNat = (v63.toNat + v62.toNat) % 2 ^ 32 := tn_add hv74
  have t75 : v72.toNat + 2 ^ 32 * v75.toNat = v61.toNat + v60.toNat := fmP1 hv72 (.inr hv75)
  have t76 : v76.toNat = (v49.toNat + v66.toNat) % 2 ^ 32 := tn_add hv76
  have t77 : v77.toNat = (v75.toNat + v74.toNat) % 2 ^ 32 := tn_add hv77
  have t78 : v78.toNat = v77.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv78
  have t79 : v79.toNat = v72.toNat / 2 ^ 31 := tn_srl hv79
  have t80 : v80.toNat = v79.toNat + v78.toNat := tn_orS' 31 (by decide) hv80 t79 t78
  have t81 : v81.toNat = (v69.toNat + v68.toNat) % 2 ^ 32 := tn_add hv81
  have t82 : v82.toNat = (v81.toNat + v70.toNat) % 2 ^ 32 := tn_add hv82
  have t83 : v83.toNat = (v67.toNat + v71.toNat) % 2 ^ 32 := tn_add hv83
  have t84 : v84.toNat = v72.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv84
  have t85 : v85.toNat = (v73.toNat + v83.toNat) % 2 ^ 32 := tn_add hv85
  have t86 : v83.toNat + 2 ^ 32 * v86.toNat = v67.toNat + v71.toNat := fmP1 hv83 (.inr hv86)
  have t87 : v85.toNat + 2 ^ 32 * v87.toNat = v73.toNat + v83.toNat := fmP1 hv85 (.inr hv87)
  have t88 : v88.toNat = (v86.toNat + v82.toNat) % 2 ^ 32 := tn_add hv88
  have t89 : v89.toNat = (v84.toNat + v85.toNat) % 2 ^ 32 := tn_add hv89
  have t90 : v90.toNat = v18.toNat * v8.toNat % 2 ^ 32 := tn_mul hv90
  have t91 : v91.toNat = v18.toNat * v8.toNat / 2 ^ 32 := tn_mulhu hv91
  have t92 : v92.toNat = v16.toNat * v48.toNat % 2 ^ 32 := tn_mul hv92
  have t93 : v93.toNat = v16.toNat * v48.toNat / 2 ^ 32 := tn_mulhu hv93
  have t94 : v94.toNat = (v88.toNat + v87.toNat) % 2 ^ 32 := tn_add hv94
  have t95 : v89.toNat + 2 ^ 32 * v95.toNat = v84.toNat + v85.toNat := fmP1 hv89 (.inr hv95)
  have t96 : v96.toNat = (v94.toNat + v95.toNat) % 2 ^ 32 := tn_add hv96
  have t99 : v99.toNat = (v96.toNat + v80.toNat) % 2 ^ 32 := tn_add hv99
  have t100 : v100.toNat = v10.toNat * v19.toNat % 2 ^ 32 := tn_mul hv100
  have t101 : v101.toNat = v12.toNat * v64.toNat % 2 ^ 32 := tn_mul hv101
  have t102 : v102.toNat = v10.toNat * v19.toNat / 2 ^ 32 := tn_mulhu hv102
  have t103 : v103.toNat = v12.toNat * v64.toNat / 2 ^ 32 := tn_mulhu hv103
  have t104 : v104.toNat = (v93.toNat + v91.toNat) % 2 ^ 32 := tn_add hv104
  have t105 : v105.toNat = (v90.toNat + v92.toNat) % 2 ^ 32 := tn_add hv105
  have t106 : v105.toNat + 2 ^ 32 * v106.toNat = v90.toNat + v92.toNat := fmP1 hv105 (.inr hv106)
  have t109 : v109.toNat = (v104.toNat + v106.toNat) % 2 ^ 32 := tn_add hv109
  have t110 : v110.toNat = v20.toNat * v6.toNat / 2 ^ 32 := tn_mulhu hv110
  have t111 : v111.toNat = v20.toNat * v6.toNat % 2 ^ 32 := tn_mul hv111
  have t112 : v112.toNat = v21.toNat * v30.toNat / 2 ^ 32 := tn_mulhu hv112
  have t113 : v113.toNat = (v101.toNat + v100.toNat) % 2 ^ 32 := tn_add hv113
  have t114 : v114.toNat = (v102.toNat + v103.toNat) % 2 ^ 32 := tn_add hv114
  have t115 : v113.toNat + 2 ^ 32 * v115.toNat = v101.toNat + v100.toNat := fmP1 hv113 (.inr hv115)
  have t116 : v116.toNat = v21.toNat * v30.toNat % 2 ^ 32 := tn_mul hv116
  have t118 : v118.toNat = (v114.toNat + v115.toNat) % 2 ^ 32 := tn_add hv118
  have t119 : v119.toNat = v118.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv119
  have t120 : v120.toNat = v113.toNat / 2 ^ 31 := tn_srl hv120
  have t121 : v121.toNat = v120.toNat + v119.toNat := tn_orS' 31 (by decide) hv121 t120 t119
  have t122 : v122.toNat = v113.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv122
  have t123 : v123.toNat = (v111.toNat + v105.toNat) % 2 ^ 32 := tn_add hv123
  have t124 : v124.toNat = (v110.toNat + v109.toNat) % 2 ^ 32 := tn_add hv124
  have t125 : v123.toNat + 2 ^ 32 * v125.toNat = v111.toNat + v105.toNat := fmP1 hv123 (.inr hv125)
  have t126 : v126.toNat = (v124.toNat + v112.toNat) % 2 ^ 32 := tn_add hv126
  have t127 : v127.toNat = v9.toNat * v48.toNat % 2 ^ 32 := tn_mul hv127
  have t128 : v128.toNat = v18.toNat * v16.toNat % 2 ^ 32 := tn_mul hv128
  have t129 : v129.toNat = (v126.toNat + v125.toNat) % 2 ^ 32 := tn_add hv129
  have t130 : v130.toNat = (v116.toNat + v123.toNat) % 2 ^ 32 := tn_add hv130
  have t131 : v130.toNat + 2 ^ 32 * v131.toNat = v116.toNat + v123.toNat := fmP1 hv130 (.inr hv131)
  have t132 : v132.toNat = (v130.toNat + v122.toNat) % 2 ^ 32 := tn_add hv132
  have t133 : v133.toNat = v9.toNat * v48.toNat / 2 ^ 32 := tn_mulhu hv133
  have t134 : v134.toNat = v18.toNat * v16.toNat / 2 ^ 32 := tn_mulhu hv134
  have t135 : v135.toNat = (v129.toNat + v131.toNat) % 2 ^ 32 := tn_add hv135
  have t136 : v132.toNat + 2 ^ 32 * v136.toNat = v130.toNat + v122.toNat := fmP1 hv132 (.inl hv136)
  have t137 : v137.toNat = v21.toNat * v64.toNat / 2 ^ 32 := tn_mulhu hv137
  have t138 : v138.toNat = v21.toNat * v64.toNat % 2 ^ 32 := tn_mul hv138
  have t139 : v139.toNat = (v135.toNat + v136.toNat) % 2 ^ 32 := tn_add hv139
  have t140 : v140.toNat = (v128.toNat + v127.toNat) % 2 ^ 32 := tn_add hv140
  have t141 : v141.toNat = v10.toNat * v17.toNat % 2 ^ 32 := tn_mul hv141
  have t142 : v142.toNat = v12.toNat * v6.toNat % 2 ^ 32 := tn_mul hv142
  have t143 : v143.toNat = v10.toNat * v17.toNat / 2 ^ 32 := tn_mulhu hv143
  have t144 : v144.toNat = v12.toNat * v6.toNat / 2 ^ 32 := tn_mulhu hv144
  have t145 : v145.toNat = (v133.toNat + v134.toNat) % 2 ^ 32 := tn_add hv145
  have t146 : v140.toNat + 2 ^ 32 * v146.toNat = v128.toNat + v127.toNat := fmP1 hv140 (.inr hv146)
  have t147 : v147.toNat = (v139.toNat + v121.toNat) % 2 ^ 32 := tn_add hv147
  have t148 : v148.toNat = (v145.toNat + v146.toNat) % 2 ^ 32 := tn_add hv148
  have t149 : v149.toNat = (v138.toNat + v140.toNat) % 2 ^ 32 := tn_add hv149
  have t150 : v150.toNat = (v148.toNat + v137.toNat) % 2 ^ 32 := tn_add hv150
  have t151 : v151.toNat = v6.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv151
  have t152 : v149.toNat + 2 ^ 32 * v152.toNat = v138.toNat + v140.toNat := fmP1 hv149 (.inr hv152)
  have t153 : v153.toNat = (v150.toNat + v152.toNat) % 2 ^ 32 := tn_add hv153
  have t154 : v154.toNat = (v142.toNat + v141.toNat) % 2 ^ 32 := tn_add hv154
  have t155 : v155.toNat = (v143.toNat + v144.toNat) % 2 ^ 32 := tn_add hv155
  have t156 : v154.toNat + 2 ^ 32 * v156.toNat = v142.toNat + v141.toNat := fmP1 hv154 (.inr hv156)
  have t157 : v157.toNat = (v155.toNat + v156.toNat) % 2 ^ 32 := tn_add hv157
  have t158 : v158.toNat = v154.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv158
  have t159 : v159.toNat = v157.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv159
  have t160 : v160.toNat = (v158.toNat + v149.toNat) % 2 ^ 32 := tn_add hv160
  have t161 : v161.toNat = v154.toNat / 2 ^ 31 := tn_srl hv161
  have t162 : v160.toNat + 2 ^ 32 * v162.toNat = v158.toNat + v149.toNat := fmP1 hv160 (.inr hv162)
  have t163 : v163.toNat = v161.toNat + v159.toNat := tn_orS' 31 (by decide) hv163 t161 t159
  have t164 : v164.toNat = (v162.toNat + v153.toNat) % 2 ^ 32 := tn_add hv164
  have t165 : v165.toNat = (v163.toNat + v164.toNat) % 2 ^ 32 := tn_add hv165
  have t166 : v166.toNat = v10.toNat * v64.toNat % 2 ^ 32 := tn_mul hv166
  have t167 : v167.toNat = v10.toNat * v64.toNat / 2 ^ 32 := tn_mulhu hv167
  have t169 : v169.toNat = v12.toNat * v4.toNat % 2 ^ 32 := tn_mul hv169
  have t170 : v170.toNat = v12.toNat * v4.toNat / 2 ^ 32 := tn_mulhu hv170
  have t176 : v176.toNat = v17.toNat * v48.toNat / 2 ^ 32 := tn_mulhu hv176
  have t177 : v177.toNat = v17.toNat * v48.toNat % 2 ^ 32 := tn_mul hv177
  have t178 : v178.toNat = v19.toNat * v18.toNat / 2 ^ 32 := tn_mulhu hv178
  have t179 : v179.toNat = v19.toNat * v18.toNat % 2 ^ 32 := tn_mul hv179
  have t180 : v180.toNat = v16.toNat * v16.toNat % 2 ^ 32 := tn_mul hv180
  have t181 : v181.toNat = v16.toNat * v16.toNat / 2 ^ 32 := tn_mulhu hv181
  have t182 : v182.toNat = (v169.toNat + v166.toNat) % 2 ^ 32 := tn_add hv182
  have t183 : v183.toNat = (v167.toNat + v170.toNat) % 2 ^ 32 := tn_add hv183
  have t184 : v182.toNat + 2 ^ 32 * v184.toNat = v169.toNat + v166.toNat := fmP1 hv182 (.inr hv184)
  have t185 : v185.toNat = v21.toNat * v151.toNat % 2 ^ 32 := tn_mul hv185
  have t186 : v186.toNat = (v184.toNat + v183.toNat) % 2 ^ 32 := tn_add hv186
  have t187 : v187.toNat = v186.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv187
  have t188 : v188.toNat = v182.toNat / 2 ^ 31 := tn_srl hv188
  have t189 : v189.toNat = v21.toNat * v151.toNat / 2 ^ 32 := tn_mulhu hv189
  have t190 : v190.toNat = v188.toNat + v187.toNat := tn_orS' 31 (by decide) hv190 t188 t187
  have t191 : v191.toNat = v182.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv191
  have t192 : v192.toNat = (v180.toNat + v179.toNat) % 2 ^ 32 := tn_add hv192
  have t193 : v192.toNat + 2 ^ 32 * v193.toNat = v180.toNat + v179.toNat := fmP1 hv192 (.inr hv193)
  have t194 : v194.toNat = (v181.toNat + v178.toNat) % 2 ^ 32 := tn_add hv194
  have t195 : v195.toNat = (v177.toNat + v192.toNat) % 2 ^ 32 := tn_add hv195
  have t196 : v196.toNat = (v194.toNat + v176.toNat) % 2 ^ 32 := tn_add hv196
  have t197 : v195.toNat + 2 ^ 32 * v197.toNat = v177.toNat + v192.toNat := fmP1 hv195 (.inr hv197)
  have t198 : v198.toNat = (v196.toNat + v193.toNat) % 2 ^ 32 := tn_add hv198
  have t199 : v199.toNat = (v197.toNat + v198.toNat) % 2 ^ 32 := tn_add hv199
  have t200 : v200.toNat = (v185.toNat + v195.toNat) % 2 ^ 32 := tn_add hv200
  have t201 : v200.toNat + 2 ^ 32 * v201.toNat = v185.toNat + v195.toNat := fmP1 hv200 (.inr hv201)
  have t202 : v202.toNat = (v199.toNat + v189.toNat) % 2 ^ 32 := tn_add hv202
  have t203 : v203.toNat = (v202.toNat + v201.toNat) % 2 ^ 32 := tn_add hv203
  have t204 : v204.toNat = (v200.toNat + v191.toNat) % 2 ^ 32 := tn_add hv204
  have t205 : v204.toNat + 2 ^ 32 * v205.toNat = v200.toNat + v191.toNat := fmP1 hv204 (.inl hv205)
  have t206 : v206.toNat = v6.toNat * v10.toNat / 2 ^ 32 := tn_mulhu hv206
  have t208 : v208.toNat = v3.toNat * v48.toNat / 2 ^ 32 := tn_mulhu hv208
  have t209 : v209.toNat = v6.toNat * v10.toNat % 2 ^ 32 := tn_mul hv209
  have t210 : v210.toNat = v17.toNat * v18.toNat / 2 ^ 32 := tn_mulhu hv210
  have t212 : v212.toNat = v28.toNat * v9.toNat / 2 ^ 32 := tn_mulhu hv212
  have t213 : v213.toNat = v17.toNat * v18.toNat % 2 ^ 32 := tn_mul hv213
  have t214 : v214.toNat = v28.toNat * v9.toNat % 2 ^ 32 := tn_mul hv214
  have t215 : v215.toNat = (v203.toNat + v205.toNat) % 2 ^ 32 := tn_add hv215
  have t216 : v216.toNat = v3.toNat * v48.toNat % 2 ^ 32 := tn_mul hv216
  have t217 : v217.toNat = v4.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv217
  have t218 : v218.toNat = (v190.toNat + v215.toNat) % 2 ^ 32 := tn_add hv218
  have t219 : v219.toNat = v21.toNat * v217.toNat % 2 ^ 32 := tn_mul hv219
  have t220 : v220.toNat = v206.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv220
  have t221 : v221.toNat = v21.toNat * v217.toNat / 2 ^ 32 := tn_mulhu hv221
  have t222 : v222.toNat = v209.toNat / 2 ^ 31 := tn_srl hv222
  have t223 : v223.toNat = v222.toNat + v220.toNat := tn_orS' 31 (by decide) hv223 t222 t220
  have t224 : v224.toNat = (v212.toNat + v210.toNat) % 2 ^ 32 := tn_add hv224
  have t225 : v225.toNat = (v224.toNat + v208.toNat) % 2 ^ 32 := tn_add hv225
  have t226 : v226.toNat = (v214.toNat + v213.toNat) % 2 ^ 32 := tn_add hv226
  have t227 : v226.toNat + 2 ^ 32 * v227.toNat = v214.toNat + v213.toNat := fmP1 hv226 (.inr hv227)
  have t228 : v228.toNat = (v216.toNat + v226.toNat) % 2 ^ 32 := tn_add hv228
  have t229 : v229.toNat = (v225.toNat + v227.toNat) % 2 ^ 32 := tn_add hv229
  have t230 : v228.toNat + 2 ^ 32 * v230.toNat = v216.toNat + v226.toNat := fmP1 hv228 (.inr hv230)
  have t231 : v231.toNat = (v230.toNat + v229.toNat) % 2 ^ 32 := tn_add hv231
  have t232 : v232.toNat = (v219.toNat + v228.toNat) % 2 ^ 32 := tn_add hv232
  have t233 : v233.toNat = (v231.toNat + v221.toNat) % 2 ^ 32 := tn_add hv233
  have t234 : v232.toNat + 2 ^ 32 * v234.toNat = v219.toNat + v228.toNat := fmP1 hv232 (.inr hv234)
  have t235 : v235.toNat = v209.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv235
  have t236 : v236.toNat = (v233.toNat + v234.toNat) % 2 ^ 32 := tn_add hv236
  have t237 : v237.toNat = (v236.toNat + v223.toNat) % 2 ^ 32 := tn_add hv237
  have t238 : v238.toNat = (v235.toNat + v232.toNat) % 2 ^ 32 := tn_add hv238
  have t239 : v238.toNat + 2 ^ 32 * v239.toNat = v235.toNat + v232.toNat := fmP1 hv238 (.inr hv239)
  have t240 : v240.toNat = v217.toNat * v10.toNat % 2 ^ 32 := tn_mul hv240
  have t241 : v241.toNat = v217.toNat * v10.toNat / 2 ^ 32 := tn_mulhu hv241
  have t244 : v244.toNat = (v237.toNat + v239.toNat) % 2 ^ 32 := tn_add hv244
  have t245 : v245.toNat = v17.toNat * v28.toNat / 2 ^ 32 := tn_mulhu hv245
  have t246 : v246.toNat = v19.toNat * v9.toNat / 2 ^ 32 := tn_mulhu hv246
  have t247 : v247.toNat = v64.toNat * v18.toNat / 2 ^ 32 := tn_mulhu hv247
  have t248 : v248.toNat = v17.toNat * v28.toNat % 2 ^ 32 := tn_mul hv248
  have t249 : v249.toNat = v19.toNat * v9.toNat % 2 ^ 32 := tn_mul hv249
  have t252 : v252.toNat = v64.toNat * v18.toNat % 2 ^ 32 := tn_mul hv252
  have t253 : v253.toNat = v240.toNat / 2 ^ 31 := tn_srl hv253
  have t254 : v254.toNat = v241.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv254
  have t255 : v255.toNat = v253.toNat + v254.toNat := tn_orS' 31 (by decide) hv255 t253 t254
  have t256 : v256.toNat = v6.toNat * v48.toNat % 2 ^ 32 := tn_mul hv256
  have t257 : v257.toNat = (v245.toNat + v246.toNat) % 2 ^ 32 := tn_add hv257
  have t258 : v258.toNat = v6.toNat * v48.toNat / 2 ^ 32 := tn_mulhu hv258
  have t259 : v259.toNat = (v257.toNat + v247.toNat) % 2 ^ 32 := tn_add hv259
  have t261 : v261.toNat = v21.toNat * v13.toNat % 2 ^ 32 := tn_mul hv261
  have t262 : v262.toNat = v21.toNat * v13.toNat / 2 ^ 32 := tn_mulhu hv262
  have t263 : v263.toNat = (v248.toNat + v249.toNat) % 2 ^ 32 := tn_add hv263
  have t264 : v263.toNat + 2 ^ 32 * v264.toNat = v248.toNat + v249.toNat := fmP1 hv263 (.inr hv264)
  have t265 : v265.toNat = (v252.toNat + v263.toNat) % 2 ^ 32 := tn_add hv265
  have t266 : v265.toNat + 2 ^ 32 * v266.toNat = v252.toNat + v263.toNat := fmP1 hv265 (.inr hv266)
  have t267 : v267.toNat = (v259.toNat + v264.toNat) % 2 ^ 32 := tn_add hv267
  have t268 : v268.toNat = (v267.toNat + v266.toNat) % 2 ^ 32 := tn_add hv268
  have t269 : v269.toNat = (v256.toNat + v265.toNat) % 2 ^ 32 := tn_add hv269
  have t270 : v270.toNat = (v268.toNat + v258.toNat) % 2 ^ 32 := tn_add hv270
  have t271 : v269.toNat + 2 ^ 32 * v271.toNat = v256.toNat + v265.toNat := fmP1 hv269 (.inr hv271)
  have t272 : v272.toNat = v240.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv272
  have t273 : v273.toNat = (v271.toNat + v270.toNat) % 2 ^ 32 := tn_add hv273
  have t274 : v274.toNat = (v273.toNat + v262.toNat) % 2 ^ 32 := tn_add hv274
  have t275 : v275.toNat = (v261.toNat + v269.toNat) % 2 ^ 32 := tn_add hv275
  have t276 : v275.toNat + 2 ^ 32 * v276.toNat = v261.toNat + v269.toNat := fmP1 hv275 (.inr hv276)
  have t277 : v277.toNat = v6.toNat * v18.toNat / 2 ^ 32 := tn_mulhu hv277
  have t278 : v278.toNat = v3.toNat * v28.toNat / 2 ^ 32 := tn_mulhu hv278
  have t279 : v279.toNat = v19.toNat * v17.toNat / 2 ^ 32 := tn_mulhu hv279
  have t280 : v280.toNat = v3.toNat * v28.toNat % 2 ^ 32 := tn_mul hv280
  have t281 : v281.toNat = v19.toNat * v17.toNat % 2 ^ 32 := tn_mul hv281
  have t282 : v282.toNat = (v274.toNat + v276.toNat) % 2 ^ 32 := tn_add hv282
  have t283 : v283.toNat = (v272.toNat + v275.toNat) % 2 ^ 32 := tn_add hv283
  have t284 : v284.toNat = (v282.toNat + v255.toNat) % 2 ^ 32 := tn_add hv284
  have t285 : v283.toNat + 2 ^ 32 * v285.toNat = v272.toNat + v275.toNat := fmP1 hv283 (.inr hv285)
  have t286 : v286.toNat = v6.toNat * v18.toNat % 2 ^ 32 := tn_mul hv286
  have t287 : v287.toNat = v13.toNat * v10.toNat % 2 ^ 32 := tn_mul hv287
  have t288 : v288.toNat = (v284.toNat + v285.toNat) % 2 ^ 32 := tn_add hv288
  have t289 : v289.toNat = v13.toNat * v10.toNat / 2 ^ 32 := tn_mulhu hv289
  have t290 : v290.toNat = (v278.toNat + v279.toNat) % 2 ^ 32 := tn_add hv290
  have t291 : v291.toNat = v4.toNat * v48.toNat % 2 ^ 32 := tn_mul hv291
  have t292 : v292.toNat = (v281.toNat + v280.toNat) % 2 ^ 32 := tn_add hv292
  have t293 : v293.toNat = (v290.toNat + v277.toNat) % 2 ^ 32 := tn_add hv293
  have t294 : v294.toNat = v4.toNat * v48.toNat / 2 ^ 32 := tn_mulhu hv294
  have t295 : v292.toNat + 2 ^ 32 * v295.toNat = v281.toNat + v280.toNat := fmP1 hv292 (.inr hv295)
  have t297 : v297.toNat = (v293.toNat + v295.toNat) % 2 ^ 32 := tn_add hv297
  have t298 : v298.toNat = v287.toNat / 2 ^ 31 := tn_srl hv298
  have t299 : v299.toNat = (v286.toNat + v292.toNat) % 2 ^ 32 := tn_add hv299
  have t300 : v300.toNat = v289.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv300
  have t301 : v299.toNat + 2 ^ 32 * v301.toNat = v286.toNat + v292.toNat := fmP1 hv299 (.inr hv301)
  have t302 : v302.toNat = v298.toNat + v300.toNat := tn_orS' 31 (by decide) hv302 t298 t300
  have t303 : v303.toNat = (v301.toNat + v297.toNat) % 2 ^ 32 := tn_add hv303
  have t304 : v304.toNat = v287.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv304
  have t305 : v305.toNat = (v291.toNat + v299.toNat) % 2 ^ 32 := tn_add hv305
  have t306 : v306.toNat = (v294.toNat + v303.toNat) % 2 ^ 32 := tn_add hv306
  have t307 : v305.toNat + 2 ^ 32 * v307.toNat = v291.toNat + v299.toNat := fmP1 hv305 (.inr hv307)
  have t308 : v308.toNat = (v306.toNat + v307.toNat) % 2 ^ 32 := tn_add hv308
  have t309 : v309.toNat = (v304.toNat + v305.toNat) % 2 ^ 32 := tn_add hv309
  have t310 : v310.toNat = v6.toNat * v28.toNat / 2 ^ 32 := tn_mulhu hv310
  have t311 : v311.toNat = v17.toNat * v17.toNat / 2 ^ 32 := tn_mulhu hv311
  have t313 : v313.toNat = (v308.toNat + v302.toNat) % 2 ^ 32 := tn_add hv313
  have t314 : v309.toNat + 2 ^ 32 * v314.toNat = v304.toNat + v305.toNat := fmP1 hv309 (.inr hv314)
  have t315 : v315.toNat = v64.toNat * v19.toNat / 2 ^ 32 := tn_mulhu hv315
  have t316 : v316.toNat = v6.toNat * v28.toNat % 2 ^ 32 := tn_mul hv316
  have t317 : v317.toNat = v17.toNat * v17.toNat % 2 ^ 32 := tn_mul hv317
  have t318 : v318.toNat = (v313.toNat + v314.toNat) % 2 ^ 32 := tn_add hv318
  have t319 : v319.toNat = v64.toNat * v19.toNat % 2 ^ 32 := tn_mul hv319
  have t322 : v322.toNat = v217.toNat * v18.toNat % 2 ^ 32 := tn_mul hv322
  have t323 : v323.toNat = (v310.toNat + v311.toNat) % 2 ^ 32 := tn_add hv323
  have t324 : v324.toNat = v13.toNat * v48.toNat / 2 ^ 32 := tn_mulhu hv324
  have t325 : v325.toNat = v217.toNat * v18.toNat / 2 ^ 32 := tn_mulhu hv325
  have t326 : v326.toNat = (v315.toNat + v323.toNat) % 2 ^ 32 := tn_add hv326
  have t328 : v328.toNat = v1.toNat * v10.toNat % 2 ^ 32 := tn_mul hv328
  have t329 : v329.toNat = v1.toNat * v10.toNat / 2 ^ 32 := tn_mulhu hv329
  have t330 : v330.toNat = (v317.toNat + v316.toNat) % 2 ^ 32 := tn_add hv330
  have t331 : v330.toNat + 2 ^ 32 * v331.toNat = v317.toNat + v316.toNat := fmP1 hv330 (.inr hv331)
  have t332 : v332.toNat = (v319.toNat + v330.toNat) % 2 ^ 32 := tn_add hv332
  have t333 : v333.toNat = (v326.toNat + v331.toNat) % 2 ^ 32 := tn_add hv333
  have t334 : v332.toNat + 2 ^ 32 * v334.toNat = v319.toNat + v330.toNat := fmP1 hv332 (.inr hv334)
  have t335 : v335.toNat = (v333.toNat + v334.toNat) % 2 ^ 32 := tn_add hv335
  have t336 : v336.toNat = (v332.toNat + v322.toNat) % 2 ^ 32 := tn_add hv336
  have t337 : v337.toNat = v13.toNat * v48.toNat % 2 ^ 32 := tn_mul hv337
  have t338 : v336.toNat + 2 ^ 32 * v338.toNat = v332.toNat + v322.toNat := fmP1 hv336 (.inl hv338)
  have t339 : v339.toNat = (v335.toNat + v325.toNat) % 2 ^ 32 := tn_add hv339
  have t340 : v340.toNat = (v338.toNat + v324.toNat) % 2 ^ 32 := tn_add hv340
  have t341 : v341.toNat = v328.toNat / 2 ^ 31 := tn_srl hv341
  have t342 : v342.toNat = v329.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv342
  have t343 : v343.toNat = v341.toNat + v342.toNat := tn_orS' 31 (by decide) hv343 t341 t342
  have t344 : v344.toNat = (v339.toNat + v340.toNat) % 2 ^ 32 := tn_add hv344
  have t345 : v345.toNat = v6.toNat * v19.toNat % 2 ^ 32 := tn_mul hv345
  have t346 : v346.toNat = v6.toNat * v19.toNat / 2 ^ 32 := tn_mulhu hv346
  have t347 : v347.toNat = v30.toNat * v3.toNat % 2 ^ 32 := tn_mul hv347
  have t348 : v348.toNat = v30.toNat * v3.toNat / 2 ^ 32 := tn_mulhu hv348
  have t349 : v349.toNat = (v337.toNat + v336.toNat) % 2 ^ 32 := tn_add hv349
  have t350 : v350.toNat = v4.toNat * v28.toNat / 2 ^ 32 := tn_mulhu hv350
  have t351 : v351.toNat = v4.toNat * v28.toNat % 2 ^ 32 := tn_mul hv351
  have t352 : v349.toNat + 2 ^ 32 * v352.toNat = v337.toNat + v336.toNat := fmP1 hv349 (.inr hv352)
  have t353 : v353.toNat = (v352.toNat + v344.toNat) % 2 ^ 32 := tn_add hv353
  have t354 : v354.toNat = v13.toNat * v18.toNat % 2 ^ 32 := tn_mul hv354
  have t355 : v355.toNat = (v343.toNat + v353.toNat) % 2 ^ 32 := tn_add hv355
  have t356 : v356.toNat = v1.toNat * v48.toNat % 2 ^ 32 := tn_mul hv356
  have t357 : v357.toNat = v1.toNat * v48.toNat / 2 ^ 32 := tn_mulhu hv357
  have t358 : v358.toNat = v13.toNat * v18.toNat / 2 ^ 32 := tn_mulhu hv358
  have t359 : v359.toNat = (v346.toNat + v348.toNat) % 2 ^ 32 := tn_add hv359
  have t360 : v360.toNat = (v347.toNat + v345.toNat) % 2 ^ 32 := tn_add hv360
  have t361 : v361.toNat = (v350.toNat + v359.toNat) % 2 ^ 32 := tn_add hv361
  have t362 : v360.toNat + 2 ^ 32 * v362.toNat = v347.toNat + v345.toNat := fmP1 hv360 (.inr hv362)
  have t363 : v363.toNat = (v361.toNat + v362.toNat) % 2 ^ 32 := tn_add hv363
  have t364 : v364.toNat = (v351.toNat + v360.toNat) % 2 ^ 32 := tn_add hv364
  have t365 : v364.toNat + 2 ^ 32 * v365.toNat = v351.toNat + v360.toNat := fmP1 hv364 (.inr hv365)
  have t366 : v366.toNat = (v354.toNat + v364.toNat) % 2 ^ 32 := tn_add hv366
  have t367 : v367.toNat = (v363.toNat + v365.toNat) % 2 ^ 32 := tn_add hv367
  have t368 : v366.toNat + 2 ^ 32 * v368.toNat = v354.toNat + v364.toNat := fmP1 hv366 (.inr hv368)
  have t369 : v369.toNat = (v358.toNat + v367.toNat) % 2 ^ 32 := tn_add hv369
  have t370 : v370.toNat = (v368.toNat + v357.toNat) % 2 ^ 32 := tn_add hv370
  have t371 : v371.toNat = (v369.toNat + v370.toNat) % 2 ^ 32 := tn_add hv371
  have t372 : v372.toNat = v328.toNat * 2 ^ 1 % 2 ^ 32 := tn_sll hv372
  have t373 : v373.toNat = (v372.toNat + v349.toNat) % 2 ^ 32 := tn_add hv373
  have t374 : v374.toNat = (v356.toNat + v366.toNat) % 2 ^ 32 := tn_add hv374
  have t375 : v373.toNat + 2 ^ 32 * v375.toNat = v372.toNat + v349.toNat := fmP1 hv373 (.inr hv375)
  have t376 : v374.toNat + 2 ^ 32 * v376.toNat = v356.toNat + v366.toNat := fmP1 hv374 (.inr hv376)
  have t377 : v377.toNat = (v375.toNat + v355.toNat) % 2 ^ 32 := tn_add hv377
  have t378 : v378.toNat = (v371.toNat + v376.toNat) % 2 ^ 32 := tn_add hv378
  have hp0_4 : v25.toNat + 2 ^ 32 * v23.toNat = v19.toNat * v12.toNat := fsq_p0_4 t25 t23
  have hp0_5 : v26.toNat + 2 ^ 32 * v24.toNat = v3.toNat * v11.toNat := fsq_p0_5 t26 t24
  have hp0_3 : v29.toNat + 2 ^ 32 * v22.toNat = v18.toNat * v10.toNat := fsq_p0_3 t29 t22
  have hp0_0 : v32.toNat + 2 ^ 32 * v31.toNat = v15.toNat * v15.toNat := fsq_p0_0 t32 t31
  have hp0_2 : v39.toNat + 2 ^ 32 * v36.toNat = v30.toNat * v20.toNat := fsq_p0_2 t39 t36
  have hp0_1 : v43.toNat + 2 ^ 32 * v33.toNat = v28.toNat * v21.toNat := fsq_p0_1 t43 t33
  have hp1_3 : v60.toNat + 2 ^ 32 * v62.toNat = v16.toNat * v10.toNat := fsq_p1_3 t60 t62
  have hp1_4 : v61.toNat + 2 ^ 32 * v63.toNat = v17.toNat * v12.toNat := fsq_p1_4 t61 t63
  have hp1_0 : v67.toNat + 2 ^ 32 * v68.toNat = v48.toNat * v8.toNat := fsq_p1_0 t67 t68
  have hp1_2 : v71.toNat + 2 ^ 32 * v69.toNat = v64.toNat * v20.toNat := fsq_p1_2 t71 t69
  have hp1_1 : v73.toNat + 2 ^ 32 * v70.toNat = v19.toNat * v21.toNat := fsq_p1_1 t73 t70
  have hp2_1 : v90.toNat + 2 ^ 32 * v91.toNat = v18.toNat * v8.toNat := fsq_p2_1 t90 t91
  have hp2_0 : v92.toNat + 2 ^ 32 * v93.toNat = v48.toNat * v16.toNat := fsq_p2_0 t92 t93
  have hp2_4 : v100.toNat + 2 ^ 32 * v102.toNat = v19.toNat * v10.toNat := fsq_p2_4 t100 t102
  have hp2_5 : v101.toNat + 2 ^ 32 * v103.toNat = v64.toNat * v12.toNat := fsq_p2_5 t101 t103
  have hp2_3 : v111.toNat + 2 ^ 32 * v110.toNat = v6.toNat * v20.toNat := fsq_p2_3 t111 t110
  have hp2_2 : v116.toNat + 2 ^ 32 * v112.toNat = v30.toNat * v21.toNat := fsq_p2_2 t116 t112
  have hp3_0 : v127.toNat + 2 ^ 32 * v133.toNat = v48.toNat * v9.toNat := fsq_p3_0 t127 t133
  have hp3_1 : v128.toNat + 2 ^ 32 * v134.toNat = v18.toNat * v16.toNat := fsq_p3_1 t128 t134
  have hp3_2 : v138.toNat + 2 ^ 32 * v137.toNat = v64.toNat * v21.toNat := fsq_p3_2 t138 t137
  have hp3_3 : v141.toNat + 2 ^ 32 * v143.toNat = v17.toNat * v10.toNat := fsq_p3_3 t141 t143
  have hp3_4 : v142.toNat + 2 ^ 32 * v144.toNat = v6.toNat * v12.toNat := fsq_p3_4 t142 t144
  have hp4_4 : v166.toNat + 2 ^ 32 * v167.toNat = v64.toNat * v10.toNat := fsq_p4_4 t166 t167
  have hp4_5 : v169.toNat + 2 ^ 32 * v170.toNat = v4.toNat * v12.toNat := fsq_p4_5 t169 t170
  have hp4_0 : v177.toNat + 2 ^ 32 * v176.toNat = v48.toNat * v17.toNat := fsq_p4_0 t177 t176
  have hp4_1 : v179.toNat + 2 ^ 32 * v178.toNat = v18.toNat * v19.toNat := fsq_p4_1 t179 t178
  have hp4_2 : v180.toNat + 2 ^ 32 * v181.toNat = v16.toNat * v16.toNat := fsq_p4_2 t180 t181
  have hp4_3 : v185.toNat + 2 ^ 32 * v189.toNat = v151.toNat * v21.toNat := fsq_p4_3 t185 t189
  have hp5_4 : v209.toNat + 2 ^ 32 * v206.toNat = v6.toNat * v10.toNat := fsq_p5_4 t209 t206
  have hp5_1 : v213.toNat + 2 ^ 32 * v210.toNat = v18.toNat * v17.toNat := fsq_p5_1 t213 t210
  have hp5_2 : v214.toNat + 2 ^ 32 * v212.toNat = v28.toNat * v9.toNat := fsq_p5_2 t214 t212
  have hp5_0 : v216.toNat + 2 ^ 32 * v208.toNat = v48.toNat * v3.toNat := fsq_p5_0 t216 t208
  have hp5_3 : v219.toNat + 2 ^ 32 * v221.toNat = v217.toNat * v21.toNat := fsq_p5_3 t219 t221
  have hp6_5 : v240.toNat + 2 ^ 32 * v241.toNat = v217.toNat * v10.toNat := fsq_p6_5 t240 t241
  have hp6_2 : v248.toNat + 2 ^ 32 * v245.toNat = v28.toNat * v17.toNat := fsq_p6_2 t248 t245
  have hp6_3 : v249.toNat + 2 ^ 32 * v246.toNat = v19.toNat * v9.toNat := fsq_p6_3 t249 t246
  have hp6_1 : v252.toNat + 2 ^ 32 * v247.toNat = v18.toNat * v64.toNat := fsq_p6_1 t252 t247
  have hp6_0 : v256.toNat + 2 ^ 32 * v258.toNat = v48.toNat * v6.toNat := fsq_p6_0 t256 t258
  have hp6_4 : v261.toNat + 2 ^ 32 * v262.toNat = v13.toNat * v21.toNat := fsq_p6_4 t261 t262
  have hp7_2 : v280.toNat + 2 ^ 32 * v278.toNat = v28.toNat * v3.toNat := fsq_p7_2 t280 t278
  have hp7_3 : v281.toNat + 2 ^ 32 * v279.toNat = v19.toNat * v17.toNat := fsq_p7_3 t281 t279
  have hp7_1 : v286.toNat + 2 ^ 32 * v277.toNat = v18.toNat * v6.toNat := fsq_p7_1 t286 t277
  have hp7_4 : v287.toNat + 2 ^ 32 * v289.toNat = v13.toNat * v10.toNat := fsq_p7_4 t287 t289
  have hp7_0 : v291.toNat + 2 ^ 32 * v294.toNat = v48.toNat * v4.toNat := fsq_p7_0 t291 t294
  have hp8_2 : v316.toNat + 2 ^ 32 * v310.toNat = v28.toNat * v6.toNat := fsq_p8_2 t316 t310
  have hp8_4 : v317.toNat + 2 ^ 32 * v311.toNat = v17.toNat * v17.toNat := fsq_p8_4 t317 t311
  have hp8_3 : v319.toNat + 2 ^ 32 * v315.toNat = v19.toNat * v64.toNat := fsq_p8_3 t319 t315
  have hp8_1 : v322.toNat + 2 ^ 32 * v325.toNat = v18.toNat * v217.toNat := fsq_p8_1 t322 t325
  have hp8_5 : v328.toNat + 2 ^ 32 * v329.toNat = v1.toNat * v10.toNat := fsq_p8_5 t328 t329
  have hp8_0 : v337.toNat + 2 ^ 32 * v324.toNat = v48.toNat * v13.toNat := fsq_p8_0 t337 t324
  have hp9_3 : v345.toNat + 2 ^ 32 * v346.toNat = v19.toNat * v6.toNat := fsq_p9_3 t345 t346
  have hp9_4 : v347.toNat + 2 ^ 32 * v348.toNat = v30.toNat * v3.toNat := fsq_p9_4 t347 t348
  have hp9_2 : v351.toNat + 2 ^ 32 * v350.toNat = v28.toNat * v4.toNat := fsq_p9_2 t351 t350
  have hp9_0 : v356.toNat + 2 ^ 32 * v357.toNat = v48.toNat * v1.toNat := fsq_p9_0 t356 t357
  have hp9_1 : v354.toNat + 2 ^ 32 * v358.toNat = v18.toNat * v13.toNat := fsq_p9_1 t354 t358
  have hs0_3_4_5 : v41.toNat + 2 ^ 32 * v45.toNat = (v18.toNat * v10.toNat + v19.toNat * v12.toNat + v3.toNat * v11.toNat) % 2 ^ 64 := fsq_s0_3_4_5 t35 t38 t40 t42 t44 t45 hp0_3 hp0_4 hp0_5
  have hw0_3_4_5 : v50.toNat + 2 ^ 32 * v49.toNat = ((v18.toNat * v10.toNat + v19.toNat * v12.toNat + v3.toNat * v11.toNat) * 2) % 2 ^ 64 := fsq_w0_3_4_5 t46 t47 t49 t50 hs0_3_4_5
  have hs0_0_1_2 : v54.toNat + 2 ^ 32 * v58.toNat = (v15.toNat * v15.toNat + v28.toNat * v21.toNat + v30.toNat * v20.toNat) % 2 ^ 64 := fsq_s0_0_1_2 t52 t53 t55 t56 t57 t58 hp0_0 hp0_1 hp0_2
  have hw0_0_1_2_3_4_5 : v59.toNat + 2 ^ 32 * v76.toNat = (v15.toNat * v15.toNat + v28.toNat * v21.toNat + v30.toNat * v20.toNat + (v18.toNat * v10.toNat + v19.toNat * v12.toNat + v3.toNat * v11.toNat) * 2) % 2 ^ 64 := fsq_w0_0_1_2_3_4_5 t65 t66 t76 hw0_3_4_5 hs0_0_1_2
  have hs1_3_4 : v72.toNat + 2 ^ 32 * v77.toNat = (v16.toNat * v10.toNat + v17.toNat * v12.toNat) % 2 ^ 64 := fsq_s1_3_4 t74 t75 t77 hp1_3 hp1_4
  have hw1_3_4 : v84.toNat + 2 ^ 32 * v80.toNat = ((v16.toNat * v10.toNat + v17.toNat * v12.toNat) * 2) % 2 ^ 64 := fsq_w1_3_4 t78 t79 t80 t84 hs1_3_4
  have hs1_0_1_2 : v85.toNat + 2 ^ 32 * v94.toNat = (v48.toNat * v8.toNat + v19.toNat * v21.toNat + v64.toNat * v20.toNat) % 2 ^ 64 := fsq_s1_0_1_2 t81 t82 t86 t87 t88 t94 hp1_0 hp1_2 hp1_1
  have hw1_0_1_2_3_4 : v89.toNat + 2 ^ 32 * v99.toNat = (v48.toNat * v8.toNat + v19.toNat * v21.toNat + v64.toNat * v20.toNat + (v16.toNat * v10.toNat + v17.toNat * v12.toNat) * 2) % 2 ^ 64 := fsq_w1_0_1_2_3_4 t95 t96 t99 hw1_3_4 hs1_0_1_2
  have hs2_0_1 : v105.toNat + 2 ^ 32 * v109.toNat = (v48.toNat * v16.toNat + v18.toNat * v8.toNat) % 2 ^ 64 := fsq_s2_0_1 t104 t106 t109 hp2_1 hp2_0
  have hs2_4_5 : v113.toNat + 2 ^ 32 * v118.toNat = (v19.toNat * v10.toNat + v64.toNat * v12.toNat) % 2 ^ 64 := fsq_s2_4_5 t114 t115 t118 hp2_4 hp2_5
  have hw2_4_5 : v122.toNat + 2 ^ 32 * v121.toNat = ((v19.toNat * v10.toNat + v64.toNat * v12.toNat) * 2) % 2 ^ 64 := fsq_w2_4_5 t119 t120 t121 t122 hs2_4_5
  have hs2_0_1_2_3 : v130.toNat + 2 ^ 32 * v135.toNat = (v48.toNat * v16.toNat + v18.toNat * v8.toNat + v30.toNat * v21.toNat + v6.toNat * v20.toNat) % 2 ^ 64 := fsq_s2_0_1_2_3 t124 t125 t126 t129 t131 t135 hs2_0_1 hp2_3 hp2_2
  have hw2_0_1_2_3_4_5 : v132.toNat + 2 ^ 32 * v147.toNat = (v48.toNat * v16.toNat + v18.toNat * v8.toNat + v30.toNat * v21.toNat + v6.toNat * v20.toNat + (v19.toNat * v10.toNat + v64.toNat * v12.toNat) * 2) % 2 ^ 64 := fsq_w2_0_1_2_3_4_5 t136 t139 t147 hw2_4_5 hs2_0_1_2_3
  have hs3_0_1 : v140.toNat + 2 ^ 32 * v148.toNat = (v48.toNat * v9.toNat + v18.toNat * v16.toNat) % 2 ^ 64 := fsq_s3_0_1 t145 t146 t148 hp3_0 hp3_1
  have hs3_0_1_2 : v149.toNat + 2 ^ 32 * v153.toNat = (v48.toNat * v9.toNat + v18.toNat * v16.toNat + v64.toNat * v21.toNat) % 2 ^ 64 := fsq_s3_0_1_2 t150 t152 t153 hp3_2 hs3_0_1
  have hs3_3_4 : v154.toNat + 2 ^ 32 * v157.toNat = (v17.toNat * v10.toNat + v6.toNat * v12.toNat) % 2 ^ 64 := fsq_s3_3_4 t155 t156 t157 hp3_3 hp3_4
  have hw3_3_4 : v158.toNat + 2 ^ 32 * v163.toNat = ((v17.toNat * v10.toNat + v6.toNat * v12.toNat) * 2) % 2 ^ 64 := fsq_w3_3_4 t158 t159 t161 t163 hs3_3_4
  have hw3_0_1_2_3_4 : v160.toNat + 2 ^ 32 * v165.toNat = (v48.toNat * v9.toNat + v18.toNat * v16.toNat + v64.toNat * v21.toNat + (v17.toNat * v10.toNat + v6.toNat * v12.toNat) * 2) % 2 ^ 64 := fsq_w3_0_1_2_3_4 t162 t164 t165 hs3_0_1_2 hw3_3_4
  have hs4_4_5 : v182.toNat + 2 ^ 32 * v186.toNat = (v64.toNat * v10.toNat + v4.toNat * v12.toNat) % 2 ^ 64 := fsq_s4_4_5 t183 t184 t186 hp4_4 hp4_5
  have hw4_4_5 : v191.toNat + 2 ^ 32 * v190.toNat = ((v64.toNat * v10.toNat + v4.toNat * v12.toNat) * 2) % 2 ^ 64 := fsq_w4_4_5 t187 t188 t190 t191 hs4_4_5
  have hs4_0_1_2 : v195.toNat + 2 ^ 32 * v199.toNat = (v48.toNat * v17.toNat + v18.toNat * v19.toNat + v16.toNat * v16.toNat) % 2 ^ 64 := fsq_s4_0_1_2 t193 t194 t196 t197 t198 t199 hp4_0 hp4_1 hp4_2
  have hs4_0_1_2_3 : v200.toNat + 2 ^ 32 * v203.toNat = (v48.toNat * v17.toNat + v18.toNat * v19.toNat + v16.toNat * v16.toNat + v151.toNat * v21.toNat) % 2 ^ 64 := fsq_s4_0_1_2_3 t201 t202 t203 hp4_3 hs4_0_1_2
  have hw4_0_1_2_3_4_5 : v204.toNat + 2 ^ 32 * v218.toNat = (v48.toNat * v17.toNat + v18.toNat * v19.toNat + v16.toNat * v16.toNat + v151.toNat * v21.toNat + (v64.toNat * v10.toNat + v4.toNat * v12.toNat) * 2) % 2 ^ 64 := fsq_w4_0_1_2_3_4_5 t205 t215 t218 hw4_4_5 hs4_0_1_2_3
  have hs5_0_1_2 : v228.toNat + 2 ^ 32 * v231.toNat = (v48.toNat * v3.toNat + v18.toNat * v17.toNat + v28.toNat * v9.toNat) % 2 ^ 64 := fsq_s5_0_1_2 t224 t225 t227 t229 t230 t231 hp5_0 hp5_1 hp5_2
  have hw5_4 : v235.toNat + 2 ^ 32 * v223.toNat = (v6.toNat * v10.toNat * 2) % 2 ^ 64 := fsq_w5_4 t220 t222 t223 t235 hp5_4
  have hs5_0_1_2_3 : v232.toNat + 2 ^ 32 * v236.toNat = (v48.toNat * v3.toNat + v18.toNat * v17.toNat + v28.toNat * v9.toNat + v217.toNat * v21.toNat) % 2 ^ 64 := fsq_s5_0_1_2_3 t233 t234 t236 hp5_3 hs5_0_1_2
  have hw5_0_1_2_3_4 : v238.toNat + 2 ^ 32 * v244.toNat = (v48.toNat * v3.toNat + v18.toNat * v17.toNat + v28.toNat * v9.toNat + v217.toNat * v21.toNat + (v6.toNat * v10.toNat) * 2) % 2 ^ 64 := fsq_w5_0_1_2_3_4 t237 t239 t244 hw5_4 hs5_0_1_2_3
  have hs6_1_2_3 : v265.toNat + 2 ^ 32 * v268.toNat = (v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat) % 2 ^ 64 := fsq_s6_1_2_3 t257 t259 t264 t266 t267 t268 hp6_2 hp6_3 hp6_1
  have hw6_5 : v272.toNat + 2 ^ 32 * v255.toNat = (v217.toNat * v10.toNat * 2) % 2 ^ 64 := fsq_w6_5 t253 t254 t255 t272 hp6_5
  have hs6_0_1_2_3 : v269.toNat + 2 ^ 32 * v273.toNat = (v48.toNat * v6.toNat + v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat) % 2 ^ 64 := fsq_s6_0_1_2_3 t270 t271 t273 hp6_0 hs6_1_2_3
  have hs6_0_1_2_3_4 : v275.toNat + 2 ^ 32 * v282.toNat = (v48.toNat * v6.toNat + v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat + v13.toNat * v21.toNat) % 2 ^ 64 := fsq_s6_0_1_2_3_4 t274 t276 t282 hp6_4 hs6_0_1_2_3
  have hw6_0_1_2_3_4_5 : v283.toNat + 2 ^ 32 * v288.toNat = (v48.toNat * v6.toNat + v18.toNat * v64.toNat + v28.toNat * v17.toNat + v19.toNat * v9.toNat + v13.toNat * v21.toNat + (v217.toNat * v10.toNat) * 2) % 2 ^ 64 := fsq_w6_0_1_2_3_4_5 t284 t285 t288 hw6_5 hs6_0_1_2_3_4
  have hs7_1_2_3 : v299.toNat + 2 ^ 32 * v303.toNat = (v18.toNat * v6.toNat + v28.toNat * v3.toNat + v19.toNat * v17.toNat) % 2 ^ 64 := fsq_s7_1_2_3 t290 t293 t295 t297 t301 t303 hp7_1 hp7_2 hp7_3
  have hw7_4 : v304.toNat + 2 ^ 32 * v302.toNat = (v13.toNat * v10.toNat * 2) % 2 ^ 64 := fsq_w7_4 t298 t300 t302 t304 hp7_4
  have hs7_0_1_2_3 : v305.toNat + 2 ^ 32 * v308.toNat = (v48.toNat * v4.toNat + v18.toNat * v6.toNat + v28.toNat * v3.toNat + v19.toNat * v17.toNat) % 2 ^ 64 := fsq_s7_0_1_2_3 t306 t307 t308 hp7_0 hs7_1_2_3
  have hw7_0_1_2_3_4 : v309.toNat + 2 ^ 32 * v318.toNat = (v48.toNat * v4.toNat + v18.toNat * v6.toNat + v28.toNat * v3.toNat + v19.toNat * v17.toNat + (v13.toNat * v10.toNat) * 2) % 2 ^ 64 := fsq_w7_0_1_2_3_4 t313 t314 t318 hw7_4 hs7_0_1_2_3
  have hs8_2_3_4 : v332.toNat + 2 ^ 32 * v335.toNat = (v28.toNat * v6.toNat + v19.toNat * v64.toNat + v17.toNat * v17.toNat) % 2 ^ 64 := fsq_s8_2_3_4 t323 t326 t331 t333 t334 t335 hp8_2 hp8_4 hp8_3
  have hs8_0_1_2_3_4 : v349.toNat + 2 ^ 32 * v353.toNat = (v48.toNat * v13.toNat + v18.toNat * v217.toNat + v28.toNat * v6.toNat + v19.toNat * v64.toNat + v17.toNat * v17.toNat) % 2 ^ 64 := fsq_s8_0_1_2_3_4 t338 t339 t340 t344 t352 t353 hp8_1 hp8_0 hs8_2_3_4
  have hs9_2_3_4 : v364.toNat + 2 ^ 32 * v367.toNat = (v28.toNat * v4.toNat + v19.toNat * v6.toNat + v30.toNat * v3.toNat) % 2 ^ 64 := fsq_s9_2_3_4 t359 t361 t362 t363 t365 t367 hp9_3 hp9_4 hp9_2
  have hw8_5 : v372.toNat + 2 ^ 32 * v343.toNat = (v1.toNat * v10.toNat * 2) % 2 ^ 64 := fsq_w8_5 t341 t342 t343 t372 hp8_5
  have hw8_0_1_2_3_4_5 : v373.toNat + 2 ^ 32 * v377.toNat = (v48.toNat * v13.toNat + v18.toNat * v217.toNat + v28.toNat * v6.toNat + v19.toNat * v64.toNat + v17.toNat * v17.toNat + (v1.toNat * v10.toNat) * 2) % 2 ^ 64 := fsq_w8_0_1_2_3_4_5 t355 t375 t377 hw8_5 hs8_0_1_2_3_4
  have hs9_0_1_2_3_4 : v374.toNat + 2 ^ 32 * v378.toNat = (v48.toNat * v1.toNat + v18.toNat * v13.toNat + v28.toNat * v4.toNat + v19.toNat * v6.toNat + v30.toNat * v3.toNat) % 2 ^ 64 := fsq_s9_0_1_2_3_4 t368 t369 t370 t371 t376 t378 hp9_1 hp9_0 hs9_2_3_4
  obtain ⟨X0, eX0⟩ : ∃ X, limbAt M xp 0 = X := ⟨_, rfl⟩
  have hX0 : v15.toNat = X0 := by rw [← eX0, ← hv15]; rfl
  obtain ⟨X1, eX1⟩ : ∃ X, limbAt M xp 1 = X := ⟨_, rfl⟩
  have hX1 : v8.toNat = X1 := by rw [← eX1, ← hv8]; rfl
  obtain ⟨X2, eX2⟩ : ∃ X, limbAt M xp 2 = X := ⟨_, rfl⟩
  have hX2 : v16.toNat = X2 := by rw [← eX2, ← hv16]; rfl
  obtain ⟨X3, eX3⟩ : ∃ X, limbAt M xp 3 = X := ⟨_, rfl⟩
  have hX3 : v9.toNat = X3 := by rw [← eX3, ← hv9]; rfl
  obtain ⟨X4, eX4⟩ : ∃ X, limbAt M xp 4 = X := ⟨_, rfl⟩
  have hX4 : v17.toNat = X4 := by rw [← eX4, ← hv17]; rfl
  obtain ⟨X5, eX5⟩ : ∃ X, limbAt M xp 5 = X := ⟨_, rfl⟩
  have hX5 : v3.toNat = X5 := by rw [← eX5, ← hv3]; rfl
  obtain ⟨X6, eX6⟩ : ∃ X, limbAt M xp 6 = X := ⟨_, rfl⟩
  have hX6 : v6.toNat = X6 := by rw [← eX6, ← hv6]; rfl
  obtain ⟨X7, eX7⟩ : ∃ X, limbAt M xp 7 = X := ⟨_, rfl⟩
  have hX7 : v4.toNat = X7 := by rw [← eX7, ← hv4]; rfl
  obtain ⟨X8, eX8⟩ : ∃ X, limbAt M xp 8 = X := ⟨_, rfl⟩
  have hX8 : v13.toNat = X8 := by rw [← eX8, ← hv13]; rfl
  obtain ⟨X9, eX9⟩ : ∃ X, limbAt M xp 9 = X := ⟨_, rfl⟩
  have hX9 : v1.toNat = X9 := by rw [← eX9, ← hv1]; rfl
  have g2_0 : 2 * v15.toNat % 2 ^ 32 = v48.toNat := by rw [t48, Nat.pow_one, Nat.mul_comm]
  have g2_1 : 2 * v8.toNat % 2 ^ 32 = v18.toNat := by rw [t18, Nat.pow_one, Nat.mul_comm]
  have g2_2 : 2 * v16.toNat % 2 ^ 32 = v28.toNat := by rw [t28, Nat.pow_one, Nat.mul_comm]
  have g2_3 : 2 * v9.toNat % 2 ^ 32 = v19.toNat := by rw [t19, Nat.pow_one, Nat.mul_comm]
  have g2_4 : 2 * v17.toNat % 2 ^ 32 = v30.toNat := by rw [t30, Nat.pow_one, Nat.mul_comm]
  have g2_5 : 2 * v3.toNat % 2 ^ 32 = v64.toNat := by rw [t64, Nat.pow_one, Nat.mul_comm]
  have g2_6 : 2 * v6.toNat % 2 ^ 32 = v151.toNat := by rw [t151, Nat.pow_one, Nat.mul_comm]
  have g2_7 : 2 * v4.toNat % 2 ^ 32 = v217.toNat := by rw [t217, Nat.pow_one, Nat.mul_comm]
  have g19_5 : 19 * v3.toNat % 2 ^ 32 = v11.toNat := by rw [t11, Nat.mul_comm]
  have g19_6 : 19 * v6.toNat % 2 ^ 32 = v20.toNat := by rw [t20, Nat.mul_comm]
  have g19_7 : 19 * v4.toNat % 2 ^ 32 = v12.toNat := by rw [t12, Nat.mul_comm]
  have g19_8 : 19 * v13.toNat % 2 ^ 32 = v21.toNat := by rw [t21, Nat.mul_comm]
  have g19_9 : 19 * v1.toNat % 2 ^ 32 = v10.toNat := by rw [t10, Nat.mul_comm]
  have uz0 : u64At Mg9 zo 0 = v59.toNat + 2 ^ 32 * v76.toNat := by
    unfold u64At
    rw [show zo + BitVec.ofNat 32 (8 * 0) = zo + 0x0 from rfl,
      show zo + BitVec.ofNat 32 (8 * 0 + 4) = zo + 0x4 from rfl,
      sg10_zo0, sg10_zo4]
  have uz1 : u64At Mg9 zo 1 = v89.toNat + 2 ^ 32 * v99.toNat := by
    unfold u64At
    rw [show zo + BitVec.ofNat 32 (8 * 1) = zo + 0x8 from rfl,
      show zo + BitVec.ofNat 32 (8 * 1 + 4) = zo + 0xC from rfl,
      sg10_zo8, sg10_zoC]
  have uz2 : u64At Mg9 zo 2 = v132.toNat + 2 ^ 32 * v147.toNat := by
    unfold u64At
    rw [show zo + BitVec.ofNat 32 (8 * 2) = zo + 0x10 from rfl,
      show zo + BitVec.ofNat 32 (8 * 2 + 4) = zo + 0x14 from rfl,
      sg10_zo10, sg10_zo14]
  have uz3 : u64At Mg9 zo 3 = v160.toNat + 2 ^ 32 * v165.toNat := by
    unfold u64At
    rw [show zo + BitVec.ofNat 32 (8 * 3) = zo + 0x18 from rfl,
      show zo + BitVec.ofNat 32 (8 * 3 + 4) = zo + 0x1C from rfl,
      sg10_zo18, sg10_zo1C]
  have uz4 : u64At Mg9 zo 4 = v204.toNat + 2 ^ 32 * v218.toNat := by
    unfold u64At
    rw [show zo + BitVec.ofNat 32 (8 * 4) = zo + 0x20 from rfl,
      show zo + BitVec.ofNat 32 (8 * 4 + 4) = zo + 0x24 from rfl,
      sg10_zo20, sg10_zo24]
  have uz5 : u64At Mg9 zo 5 = v238.toNat + 2 ^ 32 * v244.toNat := by
    unfold u64At
    rw [show zo + BitVec.ofNat 32 (8 * 5) = zo + 0x28 from rfl,
      show zo + BitVec.ofNat 32 (8 * 5 + 4) = zo + 0x2C from rfl,
      sg10_zo28, sg10_zo2C]
  have uz6 : u64At Mg9 zo 6 = v283.toNat + 2 ^ 32 * v288.toNat := by
    unfold u64At
    rw [show zo + BitVec.ofNat 32 (8 * 6) = zo + 0x30 from rfl,
      show zo + BitVec.ofNat 32 (8 * 6 + 4) = zo + 0x34 from rfl,
      sg10_zo30, sg10_zo34]
  have uz7 : u64At Mg9 zo 7 = v309.toNat + 2 ^ 32 * v318.toNat := by
    unfold u64At
    rw [show zo + BitVec.ofNat 32 (8 * 7) = zo + 0x38 from rfl,
      show zo + BitVec.ofNat 32 (8 * 7 + 4) = zo + 0x3C from rfl,
      sg10_zo38, sg10_zo3C]
  have uz8 : u64At Mg9 zo 8 = v373.toNat + 2 ^ 32 * v377.toNat := by
    unfold u64At
    rw [show zo + BitVec.ofNat 32 (8 * 8) = zo + 0x40 from rfl,
      show zo + BitVec.ofNat 32 (8 * 8 + 4) = zo + 0x44 from rfl,
      sg10_zo40, sg10_zo44]
  have uz9 : u64At Mg9 zo 9 = v374.toNat + 2 ^ 32 * v378.toNat := by
    unfold u64At
    rw [show zo + BitVec.ofNat 32 (8 * 9) = zo + 0x48 from rfl,
      show zo + BitVec.ofNat 32 (8 * 9 + 4) = zo + 0x4C from rfl,
      sg10_zo48, sg10_zo4C]
  refine ⟨ng9, Mg9, cg0.trans (cg1.trans (cg2.trans (cg3.trans (cg4.trans (cg5.trans (cg6.trans (cg7.trans (cg8.trans (cg9))))))))), ug9, frg9, sg10_1C, sg10_20, sg10_24, sg10_28, sg10_2C, sg10_30, sg10_34, sg10_38, sg10_3C, sg10_40, sg10_44, sg10_48, sg10_4C, ?_, qg9_2, qg9_3.trans hG3.symm, qg9_4.trans hG4.symm⟩
  rw [uz0, uz1, uz2, uz3, uz4, uz5, uz6, uz7, uz8, uz9, eX0, eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9]
  simp only [feSqZ]
  rw [← hX0, ← hX1, ← hX2, ← hX3, ← hX4, ← hX5, ← hX6, ← hX7, ← hX8, ← hX9]
  rw [g2_0, g2_1, g2_2, g2_3, g2_4, g2_5, g2_6, g2_7, g19_5, g19_6, g19_7, g19_8, g19_9]
  rw [hw0_0_1_2_3_4_5, hw1_0_1_2_3_4, hw2_0_1_2_3_4_5, hw3_0_1_2_3_4, hw4_0_1_2_3_4_5, hw5_0_1_2_3_4, hw6_0_1_2_3_4_5, hw7_0_1_2_3_4, hw8_0_1_2_3_4_5, hs9_0_1_2_3_4]

end C3.RV32
