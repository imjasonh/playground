import C3BootProofs.Proofs.P256ScalarDecode

/-! # P-256's `Scalar::mul`, segments 0 to 3

Each theorem steps 40 instructions. `scripts/gen-p256-scalar.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g0 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine}
    (s : St Mi B n 0x28 (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (sl28 : memLoad32 Mi (F + 0x28) = outp)
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    (sl50 : memLoad32 Mi (F + 0x50) = memLoad32 M0 (F + 0x50))
    (sl54 : memLoad32 Mi (F + 0x54) = memLoad32 M0 (F + 0x54))
    (sl58 : memLoad32 Mi (F + 0x58) = memLoad32 M0 (F + 0x58))
    (sl5C : memLoad32 Mi (F + 0x5C) = memLoad32 M0 (F + 0x5C))
    (sl60 : memLoad32 Mi (F + 0x60) = memLoad32 M0 (F + 0x60))
    (sl64 : memLoad32 Mi (F + 0x64) = memLoad32 M0 (F + 0x64))
    (sl68 : memLoad32 Mi (F + 0x68) = memLoad32 M0 (F + 0x68))
    (sl6C : memLoad32 Mi (F + 0x6C) = memLoad32 M0 (F + 0x6C))
    (sl70 : memLoad32 Mi (F + 0x70) = memLoad32 M0 (F + 0x70))
    (sl74 : memLoad32 Mi (F + 0x74) = memLoad32 M0 (F + 0x74))
    (sl78 : memLoad32 Mi (F + 0x78) = memLoad32 M0 (F + 0x78))
    (sl7C : memLoad32 Mi (F + 0x7C) = memLoad32 M0 (F + 0x7C))
    (sl80 : memLoad32 Mi (F + 0x80) = memLoad32 M0 (F + 0x80))
    (sl84 : memLoad32 Mi (F + 0x84) = memLoad32 M0 (F + 0x84))
    (sl88 : memLoad32 Mi (F + 0x88) = memLoad32 M0 (F + 0x88))
    (sl8C : memLoad32 Mi (F + 0x8C) = memLoad32 M0 (F + 0x8C))
    (sl90 : memLoad32 Mi (F + 0x90) = memLoad32 M0 (F + 0x90))
    (sl94 : memLoad32 Mi (F + 0x94) = memLoad32 M0 (F + 0x94))
    (sl98 : memLoad32 Mi (F + 0x98) = memLoad32 M0 (F + 0x98))
    (sl9C : memLoad32 Mi (F + 0x9C) = memLoad32 M0 (F + 0x9C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 : Word),
      Steps n n' ∧
      St M' B n' 0xAC (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v3 ∧
      reg n' (6 : Fin 32) = v12 ∧
      reg n' (7 : Fin 32) = v27 ∧
      reg n' (8 : Fin 32) = v34 ∧
      reg n' (9 : Fin 32) = v28 ∧
      reg n' a0 = v0 ∧
      reg n' a1 = v38 ∧
      reg n' a2 = v22 ∧
      reg n' a3 = v23 ∧
      reg n' a4 = v7 ∧
      reg n' a5 = v20 ∧
      reg n' a6 = v18 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v31 ∧
      reg n' (19 : Fin 32) = v10 ∧
      reg n' (20 : Fin 32) = v35 ∧
      reg n' (21 : Fin 32) = v33 ∧
      reg n' (22 : Fin 32) = v39 ∧
      reg n' (23 : Fin 32) = v37 ∧
      reg n' (26 : Fin 32) = v9 ∧
      reg n' (27 : Fin 32) = v8 ∧
      reg n' (28 : Fin 32) = v25 ∧
      reg n' (29 : Fin 32) = v4 ∧
      reg n' (30 : Fin 32) = v19 ∧
      reg n' (31 : Fin 32) = v29 ∧
      memLoad32 M' (F + 0x28) = outp ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (F + 0x50) = memLoad32 M0 (F + 0x50) ∧
      memLoad32 M' (F + 0x54) = memLoad32 M0 (F + 0x54) ∧
      memLoad32 M' (F + 0x58) = memLoad32 M0 (F + 0x58) ∧
      memLoad32 M' (F + 0x5C) = memLoad32 M0 (F + 0x5C) ∧
      memLoad32 M' (F + 0x60) = memLoad32 M0 (F + 0x60) ∧
      memLoad32 M' (F + 0x64) = memLoad32 M0 (F + 0x64) ∧
      memLoad32 M' (F + 0x68) = memLoad32 M0 (F + 0x68) ∧
      memLoad32 M' (F + 0x6C) = memLoad32 M0 (F + 0x6C) ∧
      memLoad32 M' (F + 0x70) = memLoad32 M0 (F + 0x70) ∧
      memLoad32 M' (F + 0x74) = memLoad32 M0 (F + 0x74) ∧
      memLoad32 M' (F + 0x78) = memLoad32 M0 (F + 0x78) ∧
      memLoad32 M' (F + 0x7C) = memLoad32 M0 (F + 0x7C) ∧
      memLoad32 M' (F + 0x80) = memLoad32 M0 (F + 0x80) ∧
      memLoad32 M' (F + 0x84) = memLoad32 M0 (F + 0x84) ∧
      memLoad32 M' (F + 0x88) = memLoad32 M0 (F + 0x88) ∧
      memLoad32 M' (F + 0x8C) = memLoad32 M0 (F + 0x8C) ∧
      memLoad32 M' (F + 0x90) = memLoad32 M0 (F + 0x90) ∧
      memLoad32 M' (F + 0x94) = memLoad32 M0 (F + 0x94) ∧
      memLoad32 M' (F + 0x98) = memLoad32 M0 (F + 0x98) ∧
      memLoad32 M' (F + 0x9C) = memLoad32 M0 (F + 0x9C) ∧
      memLoad32 M0 (F + 0x48) = v0 ∧
      (0xEEDFA000 : Word) = v1 ∧
      (0x1300000 : Word) = v2 ∧
      aluEval .add v1 0xFFFFFBFE = v3 ∧
      aluEval .add v2 0xFFFFFD85 = v4 ∧
      aluEval .mulhu v0 v3 = v5 ∧
      aluEval .mul v0 v4 = v6 ∧
      memLoad32 M0 (F + 0x4C) = v7 ∧
      memLoad32 M0 (F + 0x50) = v8 ∧
      memLoad32 M0 (F + 0x54) = v9 ∧
      memLoad32 M0 (F + 0x58) = v10 ∧
      (0xDF1A7000 : Word) = v11 ∧
      aluEval .add v11 0xFFFFFC21 = v12 ∧
      aluEval .mulhu v0 v4 = v14 ∧
      (0x43190000 : Word) = v15 ∧
      aluEval .mul v0 v12 = v16 ∧
      aluEval .add 0 0xFFFFFFFF = v17 ∧
      aluEval .add 0 0xFFFFFFFE = v18 ∧
      aluEval .add v15 0x552 = v19 ∧
      aluEval .mulhu v0 v12 = v20 ∧
      aluEval .mul v0 v19 = v21 ∧
      aluEval .add v6 v5 = v22 ∧
      aluEval .mulhu v0 v19 = v23 ∧
      aluEval .sltu v22 v5 = v24 ∧
      aluEval .mulhu v0 v17 = v25 ∧
      aluEval .add v24 v14 = v26 ∧
      aluEval .mulhu v0 v18 = v27 ∧
      aluEval .add v16 v26 = v28 ∧
      aluEval .add v0 v0 = v29 ∧
      aluEval .sltu v28 v26 = v30 ∧
      aluEval .mulhu v7 v3 = v31 ∧
      aluEval .add v30 v20 = v32 ∧
      aluEval .mul v7 v3 = v33 ∧
      aluEval .add v21 v32 = v34 ∧
      aluEval .mulhu v7 v4 = v35 ∧
      aluEval .sltu v34 v32 = v36 ∧
      aluEval .mul v7 v4 = v37 ∧
      aluEval .add v36 v23 = v38 ∧
      aluEval .mulhu v7 v12 = v39 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n0, v0, d0, hv0, u0⟩ := s.lwG hc psm_at_28 (off' := 0x2A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]; exact aligned_add hF (k := 72) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv0
  rw [sl48] at hv0
  obtain ⟨n1, v1, d1, hv1, u1⟩ := u0.luiG hc psm_at_2a (off' := 0x2E) (by decide)
  obtain ⟨n2, v2, d2, hv2, u2⟩ := u1.luiG hc psm_at_2e (off' := 0x32) (by decide)
  obtain ⟨n3, v3, d3, hv3, u3⟩ := u2.aluImmG hc psm_at_32 (off' := 0x36) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv3
  obtain ⟨n4, v4, d4, hv4, u4⟩ := u3.aluImmG hc psm_at_36 (off' := 0x3A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv4
  obtain ⟨n5, v5, d5, hv5, u5⟩ := u4.aluG hc psm_at_3a (off' := 0x3E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv5
  obtain ⟨n6, v6, d6, hv6, u6⟩ := u5.aluG hc psm_at_3e (off' := 0x42) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv6
  obtain ⟨n7, v7, d7, hv7, u7⟩ := u6.lwG hc psm_at_42 (off' := 0x44) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]; exact aligned_add hF (k := 76) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv7
  rw [sl4C] at hv7
  obtain ⟨n8, v8, d8, hv8, u8⟩ := u7.lwG hc psm_at_44 (off' := 0x46) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]; exact aligned_add hF (k := 80) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv8
  rw [sl50] at hv8
  obtain ⟨n9, v9, d9, hv9, u9⟩ := u8.lwG hc psm_at_46 (off' := 0x48) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]; exact aligned_add hF (k := 84) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv9
  rw [sl54] at hv9
  obtain ⟨n10, v10, d10, hv10, u10⟩ := u9.lwG hc psm_at_48 (off' := 0x4A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]; exact aligned_add hF (k := 88) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv10
  rw [sl58] at hv10
  obtain ⟨n11, v11, d11, hv11, u11⟩ := u10.luiG hc psm_at_4a (off' := 0x4E) (by decide)
  obtain ⟨n12, v12, d12, hv12, u12⟩ := u11.aluImmG hc psm_at_4e (off' := 0x52) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv12
  obtain ⟨n13, d13, u13⟩ := u12.aluE hc psm_at_52 (off' := 0x54) (by decide) (v := v0)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n14, v14, d14, hv14, u14⟩ := u13.aluG hc psm_at_54 (off' := 0x58) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv14
  obtain ⟨n15, v15, d15, hv15, u15⟩ := u14.luiG hc psm_at_58 (off' := 0x5C) (by decide)
  obtain ⟨n16, v16, d16, hv16, u16⟩ := u15.aluG hc psm_at_5c (off' := 0x60) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv16
  obtain ⟨n17, v17, d17, hv17, u17⟩ := u16.aluImmG hc psm_at_60 (off' := 0x62) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv17
  obtain ⟨n18, v18, d18, hv18, u18⟩ := u17.aluImmG hc psm_at_62 (off' := 0x64) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv18
  obtain ⟨n19, v19, d19, hv19, u19⟩ := u18.aluImmG hc psm_at_64 (off' := 0x68) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv19
  obtain ⟨n20, v20, d20, hv20, u20⟩ := u19.aluG hc psm_at_68 (off' := 0x6C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv20
  obtain ⟨n21, v21, d21, hv21, u21⟩ := u20.aluG hc psm_at_6c (off' := 0x70) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv21
  obtain ⟨n22, v22, d22, hv22, u22⟩ := u21.aluG hc psm_at_70 (off' := 0x72) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv22
  obtain ⟨n23, v23, d23, hv23, u23⟩ := u22.aluG hc psm_at_72 (off' := 0x76) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv23
  obtain ⟨n24, v24, d24, hv24, u24⟩ := u23.aluG hc psm_at_76 (off' := 0x7A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv24
  obtain ⟨n25, v25, d25, hv25, u25⟩ := u24.aluG hc psm_at_7a (off' := 0x7E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv25
  obtain ⟨n26, v26, d26, hv26, u26⟩ := u25.aluG hc psm_at_7e (off' := 0x80) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv26
  obtain ⟨n27, v27, d27, hv27, u27⟩ := u26.aluG hc psm_at_80 (off' := 0x84) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv27
  obtain ⟨n28, v28, d28, hv28, u28⟩ := u27.aluG hc psm_at_84 (off' := 0x86) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv28
  obtain ⟨n29, v29, d29, hv29, u29⟩ := u28.aluG hc psm_at_86 (off' := 0x8A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv29
  obtain ⟨n30, v30, d30, hv30, u30⟩ := u29.aluG hc psm_at_8a (off' := 0x8E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv30
  obtain ⟨n31, v31, d31, hv31, u31⟩ := u30.aluG hc psm_at_8e (off' := 0x92) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv31
  obtain ⟨n32, v32, d32, hv32, u32⟩ := u31.aluG hc psm_at_92 (off' := 0x94) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv32
  obtain ⟨n33, v33, d33, hv33, u33⟩ := u32.aluG hc psm_at_94 (off' := 0x98) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv33
  obtain ⟨n34, v34, d34, hv34, u34⟩ := u33.aluG hc psm_at_98 (off' := 0x9A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv34
  obtain ⟨n35, v35, d35, hv35, u35⟩ := u34.aluG hc psm_at_9a (off' := 0x9E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv35
  obtain ⟨n36, v36, d36, hv36, u36⟩ := u35.aluG hc psm_at_9e (off' := 0xA2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv36
  obtain ⟨n37, v37, d37, hv37, u37⟩ := u36.aluG hc psm_at_a2 (off' := 0xA6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv37
  obtain ⟨n38, v38, d38, hv38, u38⟩ := u37.aluG hc psm_at_a6 (off' := 0xA8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv38
  obtain ⟨n39, v39, d39, hv39, u39⟩ := u38.aluG hc psm_at_a8 (off' := 0xAC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4] at hv39
  have qo2 : reg n39 sp = F := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo3 : reg n39 (3 : Fin 32) = G3 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo4 : reg n39 (4 : Fin 32) = G4 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo5 : reg n39 (5 : Fin 32) = v3 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo6 : reg n39 (6 : Fin 32) = v12 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo7 : reg n39 (7 : Fin 32) = v27 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo8 : reg n39 (8 : Fin 32) = v34 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo9 : reg n39 (9 : Fin 32) = v28 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo10 : reg n39 a0 = v0 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo11 : reg n39 a1 = v38 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo12 : reg n39 a2 = v22 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo13 : reg n39 a3 = v23 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo14 : reg n39 a4 = v7 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo15 : reg n39 a5 = v20 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo16 : reg n39 a6 = v18 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo17 : reg n39 a7 = v17 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo18 : reg n39 (18 : Fin 32) = v31 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo19 : reg n39 (19 : Fin 32) = v10 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo20 : reg n39 (20 : Fin 32) = v35 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo21 : reg n39 (21 : Fin 32) = v33 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo22 : reg n39 (22 : Fin 32) = v39 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo23 : reg n39 (23 : Fin 32) = v37 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo26 : reg n39 (26 : Fin 32) = v9 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo27 : reg n39 (27 : Fin 32) = v8 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo28 : reg n39 (28 : Fin 32) = v25 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo29 : reg n39 (29 : Fin 32) = v4 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo30 : reg n39 (30 : Fin 32) = v19 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have qo31 : reg n39 (31 : Fin 32) = v29 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4]
  have so28 : memLoad32 Mi (F + 0x28) = outp := by
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
  have so50 : memLoad32 Mi (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [sl50]
  have so54 : memLoad32 Mi (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [sl54]
  have so58 : memLoad32 Mi (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [sl58]
  have so5C : memLoad32 Mi (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [sl5C]
  have so60 : memLoad32 Mi (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [sl60]
  have so64 : memLoad32 Mi (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [sl64]
  have so68 : memLoad32 Mi (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [sl68]
  have so6C : memLoad32 Mi (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [sl6C]
  have so70 : memLoad32 Mi (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [sl70]
  have so74 : memLoad32 Mi (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [sl74]
  have so78 : memLoad32 Mi (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [sl78]
  have so7C : memLoad32 Mi (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [sl7C]
  have so80 : memLoad32 Mi (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [sl80]
  have so84 : memLoad32 Mi (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [sl84]
  have so88 : memLoad32 Mi (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [sl88]
  have so8C : memLoad32 Mi (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [sl8C]
  have so90 : memLoad32 Mi (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [sl90]
  have so94 : memLoad32 Mi (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [sl94]
  have so98 : memLoad32 Mi (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [sl98]
  have so9C : memLoad32 Mi (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [sl9C]
  exact ⟨n39, Mi, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, (.cons d0 (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18 (.cons d19 (.cons d20 (.cons d21 (.cons d22 (.cons d23 (.cons d24 (.cons d25 (.cons d26 (.cons d27 (.cons d28 (.cons d29 (.cons d30 (.cons d31 (.cons d32 (.cons d33 (.cons d34 (.cons d35 (.cons d36 (.cons d37 (.cons d38 (.single d39)))))))))))))))))))))))))))))))))))))))), u39.self, hc, fr, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo26, qo27, qo28, qo29, qo30, qo31, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv14, hv15, hv16, hv17, hv18, hv19, hv20, hv21, hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31, hv32, hv33, hv34, hv35, hv36, hv37, hv38, hv39⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g1 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v3 v4 v7 v8 v9 v10 v12 v17 v18 v19 v20 v22 v23 v25 v27 v28 v29 v31 v33 v34 v35 v37 v38 v39 : Word}
    (s : St Mi B n 0xAC (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v3)
    (q6 : reg n (6 : Fin 32) = v12)
    (q7 : reg n (7 : Fin 32) = v27)
    (q8 : reg n (8 : Fin 32) = v34)
    (q9 : reg n (9 : Fin 32) = v28)
    (q10 : reg n a0 = v0)
    (q11 : reg n a1 = v38)
    (q12 : reg n a2 = v22)
    (q13 : reg n a3 = v23)
    (q14 : reg n a4 = v7)
    (q15 : reg n a5 = v20)
    (q16 : reg n a6 = v18)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v31)
    (q19 : reg n (19 : Fin 32) = v10)
    (q20 : reg n (20 : Fin 32) = v35)
    (q21 : reg n (21 : Fin 32) = v33)
    (q22 : reg n (22 : Fin 32) = v39)
    (q23 : reg n (23 : Fin 32) = v37)
    (q26 : reg n (26 : Fin 32) = v9)
    (q27 : reg n (27 : Fin 32) = v8)
    (q28 : reg n (28 : Fin 32) = v25)
    (q29 : reg n (29 : Fin 32) = v4)
    (q30 : reg n (30 : Fin 32) = v19)
    (q31 : reg n (31 : Fin 32) = v29)
    (sl28 : memLoad32 Mi (F + 0x28) = outp)
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    (sl50 : memLoad32 Mi (F + 0x50) = memLoad32 M0 (F + 0x50))
    (sl54 : memLoad32 Mi (F + 0x54) = memLoad32 M0 (F + 0x54))
    (sl58 : memLoad32 Mi (F + 0x58) = memLoad32 M0 (F + 0x58))
    (sl5C : memLoad32 Mi (F + 0x5C) = memLoad32 M0 (F + 0x5C))
    (sl60 : memLoad32 Mi (F + 0x60) = memLoad32 M0 (F + 0x60))
    (sl64 : memLoad32 Mi (F + 0x64) = memLoad32 M0 (F + 0x64))
    (sl68 : memLoad32 Mi (F + 0x68) = memLoad32 M0 (F + 0x68))
    (sl6C : memLoad32 Mi (F + 0x6C) = memLoad32 M0 (F + 0x6C))
    (sl70 : memLoad32 Mi (F + 0x70) = memLoad32 M0 (F + 0x70))
    (sl74 : memLoad32 Mi (F + 0x74) = memLoad32 M0 (F + 0x74))
    (sl78 : memLoad32 Mi (F + 0x78) = memLoad32 M0 (F + 0x78))
    (sl7C : memLoad32 Mi (F + 0x7C) = memLoad32 M0 (F + 0x7C))
    (sl80 : memLoad32 Mi (F + 0x80) = memLoad32 M0 (F + 0x80))
    (sl84 : memLoad32 Mi (F + 0x84) = memLoad32 M0 (F + 0x84))
    (sl88 : memLoad32 Mi (F + 0x88) = memLoad32 M0 (F + 0x88))
    (sl8C : memLoad32 Mi (F + 0x8C) = memLoad32 M0 (F + 0x8C))
    (sl90 : memLoad32 Mi (F + 0x90) = memLoad32 M0 (F + 0x90))
    (sl94 : memLoad32 Mi (F + 0x94) = memLoad32 M0 (F + 0x94))
    (sl98 : memLoad32 Mi (F + 0x98) = memLoad32 M0 (F + 0x98))
    (sl9C : memLoad32 Mi (F + 0x9C) = memLoad32 M0 (F + 0x9C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 : Word),
      Steps n n' ∧
      St M' B n' 0x12C (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v0 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v3 ∧
      reg n' (6 : Fin 32) = v12 ∧
      reg n' (7 : Fin 32) = v58 ∧
      reg n' (8 : Fin 32) = v76 ∧
      reg n' (9 : Fin 32) = v77 ∧
      reg n' a0 = v7 ∧
      reg n' a1 = v69 ∧
      reg n' a2 = v74 ∧
      reg n' a3 = v78 ∧
      reg n' a4 = v7 ∧
      reg n' a5 = v79 ∧
      reg n' a6 = v18 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v75 ∧
      reg n' (19 : Fin 32) = v10 ∧
      reg n' (20 : Fin 32) = v35 ∧
      reg n' (21 : Fin 32) = v52 ∧
      reg n' (22 : Fin 32) = v39 ∧
      reg n' (23 : Fin 32) = v55 ∧
      reg n' (24 : Fin 32) = v71 ∧
      reg n' (25 : Fin 32) = v61 ∧
      reg n' (26 : Fin 32) = v9 ∧
      reg n' (27 : Fin 32) = v8 ∧
      reg n' (28 : Fin 32) = v60 ∧
      reg n' (29 : Fin 32) = v4 ∧
      reg n' (30 : Fin 32) = v19 ∧
      reg n' (31 : Fin 32) = v67 ∧
      memLoad32 M' (F + 0x24) = v0 ∧
      memLoad32 M' (F + 0x28) = outp ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (F + 0x50) = memLoad32 M0 (F + 0x50) ∧
      memLoad32 M' (F + 0x54) = memLoad32 M0 (F + 0x54) ∧
      memLoad32 M' (F + 0x58) = memLoad32 M0 (F + 0x58) ∧
      memLoad32 M' (F + 0x5C) = memLoad32 M0 (F + 0x5C) ∧
      memLoad32 M' (F + 0x60) = memLoad32 M0 (F + 0x60) ∧
      memLoad32 M' (F + 0x64) = memLoad32 M0 (F + 0x64) ∧
      memLoad32 M' (F + 0x68) = memLoad32 M0 (F + 0x68) ∧
      memLoad32 M' (F + 0x6C) = memLoad32 M0 (F + 0x6C) ∧
      memLoad32 M' (F + 0x70) = memLoad32 M0 (F + 0x70) ∧
      memLoad32 M' (F + 0x74) = memLoad32 M0 (F + 0x74) ∧
      memLoad32 M' (F + 0x78) = memLoad32 M0 (F + 0x78) ∧
      memLoad32 M' (F + 0x7C) = memLoad32 M0 (F + 0x7C) ∧
      memLoad32 M' (F + 0x80) = memLoad32 M0 (F + 0x80) ∧
      memLoad32 M' (F + 0x84) = memLoad32 M0 (F + 0x84) ∧
      memLoad32 M' (F + 0x88) = memLoad32 M0 (F + 0x88) ∧
      memLoad32 M' (F + 0x8C) = memLoad32 M0 (F + 0x8C) ∧
      memLoad32 M' (F + 0x90) = memLoad32 M0 (F + 0x90) ∧
      memLoad32 M' (F + 0x94) = memLoad32 M0 (F + 0x94) ∧
      memLoad32 M' (F + 0x98) = memLoad32 M0 (F + 0x98) ∧
      memLoad32 M' (F + 0x9C) = memLoad32 M0 (F + 0x9C) ∧
      aluEval .sub v38 v0 = v40 ∧
      aluEval .mul v7 v12 = v41 ∧
      aluEval .sltu v40 v38 = v42 ∧
      aluEval .mul v7 v19 = v43 ∧
      aluEval .add v42 v25 = v44 ∧
      aluEval .and v22 0xFFFFFFFE = v45 ∧
      aluEval .sub v44 v29 = v46 ∧
      aluEval .add v33 v45 = v47 ∧
      aluEval .sltu v46 v44 = v48 ∧
      aluEval .sltu v47 v45 = v49 ∧
      aluEval .add v48 v27 = v50 ∧
      aluEval .add v49 v31 = v51 ∧
      aluEval .sub v50 v0 = v52 ∧
      aluEval .add v37 v28 = v55 ∧
      aluEval .sltu v52 v50 = v56 ∧
      aluEval .sltu v55 v28 = v57 ∧
      aluEval .add v25 v56 = v58 ∧
      aluEval .add v57 v35 = v59 ∧
      aluEval .add v55 v51 = v60 ∧
      aluEval .add v41 v34 = v61 ∧
      aluEval .mulhu v7 v19 = v62 ∧
      aluEval .sltu v60 v55 = v63 ∧
      aluEval .sltu v61 v34 = v64 ∧
      aluEval .add v63 v59 = v65 ∧
      aluEval .add v64 v39 = v66 ∧
      aluEval .add v61 v65 = v67 ∧
      aluEval .mulhu v7 v17 = v69 ∧
      aluEval .sltu v67 v61 = v70 ∧
      aluEval .add v43 v40 = v71 ∧
      aluEval .add v66 v70 = v72 ∧
      aluEval .sltu v71 v40 = v73 ∧
      aluEval .add v62 v73 = v74 ∧
      aluEval .add v71 v72 = v75 ∧
      aluEval .sub v46 v7 = v76 ∧
      aluEval .mulhu v7 v18 = v77 ∧
      aluEval .sltu v75 v71 = v78 ∧
      aluEval .sltu v76 v46 = v79 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n40, v40, d40, hv40, u40⟩ := s.aluG hc psm_at_ac (off' := 0xB0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv40
  obtain ⟨n41, v41, d41, hv41, u41⟩ := u40.aluG hc psm_at_b0 (off' := 0xB4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv41
  obtain ⟨n42, v42, d42, hv42, u42⟩ := u41.aluG hc psm_at_b4 (off' := 0xB8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv42
  obtain ⟨n43, v43, d43, hv43, u43⟩ := u42.aluG hc psm_at_b8 (off' := 0xBC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv43
  obtain ⟨n44, v44, d44, hv44, u44⟩ := u43.aluG hc psm_at_bc (off' := 0xBE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv44
  obtain ⟨n45, v45, d45, hv45, u45⟩ := u44.aluImmG hc psm_at_be (off' := 0xC0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv45
  obtain ⟨n46, v46, d46, hv46, u46⟩ := u45.aluG hc psm_at_c0 (off' := 0xC4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv46
  obtain ⟨n47, v47, d47, hv47, u47⟩ := u46.aluG hc psm_at_c4 (off' := 0xC6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv47
  obtain ⟨n48, v48, d48, hv48, u48⟩ := u47.aluG hc psm_at_c6 (off' := 0xCA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv48
  obtain ⟨n49, v49, d49, hv49, u49⟩ := u48.aluG hc psm_at_ca (off' := 0xCE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv49
  obtain ⟨n50, v50, d50, hv50, u50⟩ := u49.aluG hc psm_at_ce (off' := 0xD0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv50
  obtain ⟨n51, v51, d51, hv51, u51⟩ := u50.aluG hc psm_at_d0 (off' := 0xD2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv51
  obtain ⟨n52, v52, d52, hv52, u52⟩ := u51.aluG hc psm_at_d2 (off' := 0xD6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv52
  obtain ⟨n53, d53, u53⟩ := u52.aluE hc psm_at_d6 (off' := 0xD8) (by decide) (v := v0)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n54, d54, u54⟩ := u53.swG hc psm_at_d8 (off' := 0xDA) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 36) (by decide)) (a := F + 0x24) (v := v0)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31])
  obtain ⟨M54, hM54⟩ : ∃ M', memStore32 Mi (F + 0x24) v0 = M' := ⟨_, rfl⟩
  rw [hM54] at u54
  have hc54 : CodeIn M54 B p256ScalarMulCode := by rw [← hM54]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr54 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M54 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM54, memStore32_get_sep (frm_sep' hx1 (by decide)), fr x hx1 hx2 hx3]
  obtain ⟨n55, v55, d55, hv55, u55⟩ := u54.aluG hc54 psm_at_da (off' := 0xDC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv55
  obtain ⟨n56, v56, d56, hv56, u56⟩ := u55.aluG hc54 psm_at_dc (off' := 0xE0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv56
  obtain ⟨n57, v57, d57, hv57, u57⟩ := u56.aluG hc54 psm_at_e0 (off' := 0xE4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv57
  obtain ⟨n58, v58, d58, hv58, u58⟩ := u57.aluG hc54 psm_at_e4 (off' := 0xE8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv58
  obtain ⟨n59, v59, d59, hv59, u59⟩ := u58.aluG hc54 psm_at_e8 (off' := 0xEA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv59
  obtain ⟨n60, v60, d60, hv60, u60⟩ := u59.aluG hc54 psm_at_ea (off' := 0xEE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv60
  obtain ⟨n61, v61, d61, hv61, u61⟩ := u60.aluG hc54 psm_at_ee (off' := 0xF0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv61
  obtain ⟨n62, v62, d62, hv62, u62⟩ := u61.aluG hc54 psm_at_f0 (off' := 0xF4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv62
  obtain ⟨n63, v63, d63, hv63, u63⟩ := u62.aluG hc54 psm_at_f4 (off' := 0xF8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv63
  obtain ⟨n64, v64, d64, hv64, u64⟩ := u63.aluG hc54 psm_at_f8 (off' := 0xFC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv64
  obtain ⟨n65, v65, d65, hv65, u65⟩ := u64.aluG hc54 psm_at_fc (off' := 0xFE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv65
  obtain ⟨n66, v66, d66, hv66, u66⟩ := u65.aluG hc54 psm_at_fe (off' := 0x100) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv66
  obtain ⟨n67, v67, d67, hv67, u67⟩ := u66.aluG hc54 psm_at_100 (off' := 0x104) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv67
  obtain ⟨n68, d68, u68⟩ := u67.aluE hc54 psm_at_104 (off' := 0x106) (by decide) (v := v7)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n69, v69, d69, hv69, u69⟩ := u68.aluG hc54 psm_at_106 (off' := 0x10A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv69
  obtain ⟨n70, v70, d70, hv70, u70⟩ := u69.aluG hc54 psm_at_10a (off' := 0x10E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv70
  obtain ⟨n71, v71, d71, hv71, u71⟩ := u70.aluG hc54 psm_at_10e (off' := 0x110) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv71
  obtain ⟨n72, v72, d72, hv72, u72⟩ := u71.aluG hc54 psm_at_110 (off' := 0x112) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv72
  obtain ⟨n73, v73, d73, hv73, u73⟩ := u72.aluG hc54 psm_at_112 (off' := 0x116) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv73
  obtain ⟨n74, v74, d74, hv74, u74⟩ := u73.aluG hc54 psm_at_116 (off' := 0x118) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv74
  obtain ⟨n75, v75, d75, hv75, u75⟩ := u74.aluG hc54 psm_at_118 (off' := 0x11C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv75
  obtain ⟨n76, v76, d76, hv76, u76⟩ := u75.aluG hc54 psm_at_11c (off' := 0x120) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv76
  obtain ⟨n77, v77, d77, hv77, u77⟩ := u76.aluG hc54 psm_at_120 (off' := 0x124) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv77
  obtain ⟨n78, v78, d78, hv78, u78⟩ := u77.aluG hc54 psm_at_124 (off' := 0x128) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv78
  obtain ⟨n79, v79, d79, hv79, u79⟩ := u78.aluG hc54 psm_at_128 (off' := 0x12C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31] at hv79
  have qo1 : reg n79 ra = v0 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n79 sp = F := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n79 (3 : Fin 32) = G3 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n79 (4 : Fin 32) = G4 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n79 (5 : Fin 32) = v3 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n79 (6 : Fin 32) = v12 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n79 (7 : Fin 32) = v58 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n79 (8 : Fin 32) = v76 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n79 (9 : Fin 32) = v77 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n79 a0 = v7 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n79 a1 = v69 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n79 a2 = v74 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n79 a3 = v78 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n79 a4 = v7 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n79 a5 = v79 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n79 a6 = v18 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n79 a7 = v17 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n79 (18 : Fin 32) = v75 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n79 (19 : Fin 32) = v10 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n79 (20 : Fin 32) = v35 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n79 (21 : Fin 32) = v52 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n79 (22 : Fin 32) = v39 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n79 (23 : Fin 32) = v55 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n79 (24 : Fin 32) = v71 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n79 (25 : Fin 32) = v61 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n79 (26 : Fin 32) = v9 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n79 (27 : Fin 32) = v8 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n79 (28 : Fin 32) = v60 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n79 (29 : Fin 32) = v4 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n79 (30 : Fin 32) = v19 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n79 (31 : Fin 32) = v67 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q26, q27, q28, q29, q30, q31]
  have so24 : memLoad32 M54 (F + 0x24) = v0 := by
    rw [← hM54, memLoad32_store32_same]
  have so28 : memLoad32 M54 (F + 0x28) = outp := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x28) 4 from sep_offsets F (c := 36) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), sl28]
  have so2C : memLoad32 M54 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x2C) 4 from sep_offsets F (c := 36) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), sl2C]
  have so30 : memLoad32 M54 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x30) 4 from sep_offsets F (c := 36) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), sl30]
  have so34 : memLoad32 M54 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x34) 4 from sep_offsets F (c := 36) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), sl34]
  have so38 : memLoad32 M54 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x38) 4 from sep_offsets F (c := 36) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), sl38]
  have so3C : memLoad32 M54 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x3C) 4 from sep_offsets F (c := 36) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), sl3C]
  have so40 : memLoad32 M54 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x40) 4 from sep_offsets F (c := 36) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), sl40]
  have so44 : memLoad32 M54 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x44) 4 from sep_offsets F (c := 36) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), sl44]
  have so48 : memLoad32 M54 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x48) 4 from sep_offsets F (c := 36) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), sl48]
  have so4C : memLoad32 M54 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x4C) 4 from sep_offsets F (c := 36) (n := 4) (d := 76) (k := 4) (by decide) (by decide) (by decide)), sl4C]
  have so50 : memLoad32 M54 (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x50) 4 from sep_offsets F (c := 36) (n := 4) (d := 80) (k := 4) (by decide) (by decide) (by decide)), sl50]
  have so54 : memLoad32 M54 (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x54) 4 from sep_offsets F (c := 36) (n := 4) (d := 84) (k := 4) (by decide) (by decide) (by decide)), sl54]
  have so58 : memLoad32 M54 (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x58) 4 from sep_offsets F (c := 36) (n := 4) (d := 88) (k := 4) (by decide) (by decide) (by decide)), sl58]
  have so5C : memLoad32 M54 (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x5C) 4 from sep_offsets F (c := 36) (n := 4) (d := 92) (k := 4) (by decide) (by decide) (by decide)), sl5C]
  have so60 : memLoad32 M54 (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x60) 4 from sep_offsets F (c := 36) (n := 4) (d := 96) (k := 4) (by decide) (by decide) (by decide)), sl60]
  have so64 : memLoad32 M54 (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x64) 4 from sep_offsets F (c := 36) (n := 4) (d := 100) (k := 4) (by decide) (by decide) (by decide)), sl64]
  have so68 : memLoad32 M54 (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x68) 4 from sep_offsets F (c := 36) (n := 4) (d := 104) (k := 4) (by decide) (by decide) (by decide)), sl68]
  have so6C : memLoad32 M54 (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x6C) 4 from sep_offsets F (c := 36) (n := 4) (d := 108) (k := 4) (by decide) (by decide) (by decide)), sl6C]
  have so70 : memLoad32 M54 (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x70) 4 from sep_offsets F (c := 36) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), sl70]
  have so74 : memLoad32 M54 (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x74) 4 from sep_offsets F (c := 36) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), sl74]
  have so78 : memLoad32 M54 (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x78) 4 from sep_offsets F (c := 36) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), sl78]
  have so7C : memLoad32 M54 (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x7C) 4 from sep_offsets F (c := 36) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), sl7C]
  have so80 : memLoad32 M54 (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x80) 4 from sep_offsets F (c := 36) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), sl80]
  have so84 : memLoad32 M54 (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x84) 4 from sep_offsets F (c := 36) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), sl84]
  have so88 : memLoad32 M54 (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x88) 4 from sep_offsets F (c := 36) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88]
  have so8C : memLoad32 M54 (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x8C) 4 from sep_offsets F (c := 36) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), sl8C]
  have so90 : memLoad32 M54 (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x90) 4 from sep_offsets F (c := 36) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), sl90]
  have so94 : memLoad32 M54 (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x94) 4 from sep_offsets F (c := 36) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94]
  have so98 : memLoad32 M54 (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x98) 4 from sep_offsets F (c := 36) (n := 4) (d := 152) (k := 4) (by decide) (by decide) (by decide)), sl98]
  have so9C : memLoad32 M54 (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [← hM54, memLoad32_store32_sep (show Sep (F + 0x24) 4 (F + 0x9C) 4 from sep_offsets F (c := 36) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  exact ⟨n79, M54, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, (.cons d40 (.cons d41 (.cons d42 (.cons d43 (.cons d44 (.cons d45 (.cons d46 (.cons d47 (.cons d48 (.cons d49 (.cons d50 (.cons d51 (.cons d52 (.cons d53 (.cons d54 (.cons d55 (.cons d56 (.cons d57 (.cons d58 (.cons d59 (.cons d60 (.cons d61 (.cons d62 (.cons d63 (.cons d64 (.cons d65 (.cons d66 (.cons d67 (.cons d68 (.cons d69 (.cons d70 (.cons d71 (.cons d72 (.cons d73 (.cons d74 (.cons d75 (.cons d76 (.cons d77 (.cons d78 (.single d79)))))))))))))))))))))))))))))))))))))))), u79.self, hc54, fr54, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv40, hv41, hv42, hv43, hv44, hv45, hv46, hv47, hv48, hv49, hv50, hv51, hv52, hv55, hv56, hv57, hv58, hv59, hv60, hv61, hv62, hv63, hv64, hv65, hv66, hv67, hv69, hv70, hv71, hv72, hv73, hv74, hv75, hv76, hv77, hv78, hv79⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g2 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v3 v4 v7 v8 v9 v10 v12 v17 v18 v19 v35 v39 v52 v55 v58 v60 v61 v67 v69 v71 v74 v75 v76 v77 v78 v79 : Word}
    (s : St Mi B n 0x12C (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q1 : reg n ra = v0)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v3)
    (q6 : reg n (6 : Fin 32) = v12)
    (q7 : reg n (7 : Fin 32) = v58)
    (q8 : reg n (8 : Fin 32) = v76)
    (q9 : reg n (9 : Fin 32) = v77)
    (q10 : reg n a0 = v7)
    (q11 : reg n a1 = v69)
    (q12 : reg n a2 = v74)
    (q13 : reg n a3 = v78)
    (q14 : reg n a4 = v7)
    (q15 : reg n a5 = v79)
    (q16 : reg n a6 = v18)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v75)
    (q19 : reg n (19 : Fin 32) = v10)
    (q20 : reg n (20 : Fin 32) = v35)
    (q21 : reg n (21 : Fin 32) = v52)
    (q22 : reg n (22 : Fin 32) = v39)
    (q23 : reg n (23 : Fin 32) = v55)
    (q24 : reg n (24 : Fin 32) = v71)
    (q25 : reg n (25 : Fin 32) = v61)
    (q26 : reg n (26 : Fin 32) = v9)
    (q27 : reg n (27 : Fin 32) = v8)
    (q28 : reg n (28 : Fin 32) = v60)
    (q29 : reg n (29 : Fin 32) = v4)
    (q30 : reg n (30 : Fin 32) = v19)
    (q31 : reg n (31 : Fin 32) = v67)
    (sl24 : memLoad32 Mi (F + 0x24) = v0)
    (sl28 : memLoad32 Mi (F + 0x28) = outp)
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    (sl50 : memLoad32 Mi (F + 0x50) = memLoad32 M0 (F + 0x50))
    (sl54 : memLoad32 Mi (F + 0x54) = memLoad32 M0 (F + 0x54))
    (sl58 : memLoad32 Mi (F + 0x58) = memLoad32 M0 (F + 0x58))
    (sl5C : memLoad32 Mi (F + 0x5C) = memLoad32 M0 (F + 0x5C))
    (sl60 : memLoad32 Mi (F + 0x60) = memLoad32 M0 (F + 0x60))
    (sl64 : memLoad32 Mi (F + 0x64) = memLoad32 M0 (F + 0x64))
    (sl68 : memLoad32 Mi (F + 0x68) = memLoad32 M0 (F + 0x68))
    (sl6C : memLoad32 Mi (F + 0x6C) = memLoad32 M0 (F + 0x6C))
    (sl70 : memLoad32 Mi (F + 0x70) = memLoad32 M0 (F + 0x70))
    (sl74 : memLoad32 Mi (F + 0x74) = memLoad32 M0 (F + 0x74))
    (sl78 : memLoad32 Mi (F + 0x78) = memLoad32 M0 (F + 0x78))
    (sl7C : memLoad32 Mi (F + 0x7C) = memLoad32 M0 (F + 0x7C))
    (sl80 : memLoad32 Mi (F + 0x80) = memLoad32 M0 (F + 0x80))
    (sl84 : memLoad32 Mi (F + 0x84) = memLoad32 M0 (F + 0x84))
    (sl88 : memLoad32 Mi (F + 0x88) = memLoad32 M0 (F + 0x88))
    (sl8C : memLoad32 Mi (F + 0x8C) = memLoad32 M0 (F + 0x8C))
    (sl90 : memLoad32 Mi (F + 0x90) = memLoad32 M0 (F + 0x90))
    (sl94 : memLoad32 Mi (F + 0x94) = memLoad32 M0 (F + 0x94))
    (sl98 : memLoad32 Mi (F + 0x98) = memLoad32 M0 (F + 0x98))
    (sl9C : memLoad32 Mi (F + 0x9C) = memLoad32 M0 (F + 0x9C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 v111 v112 v113 v114 v115 v116 v117 v118 v119 : Word),
      Steps n n' ∧
      St M' B n' 0x1B4 (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v0 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v3 ∧
      reg n' (6 : Fin 32) = v12 ∧
      reg n' (7 : Fin 32) = v103 ∧
      reg n' (8 : Fin 32) = v101 ∧
      reg n' (9 : Fin 32) = v119 ∧
      reg n' a0 = v7 ∧
      reg n' a1 = v115 ∧
      reg n' a2 = v111 ∧
      reg n' a3 = v117 ∧
      reg n' a4 = v116 ∧
      reg n' a5 = v118 ∧
      reg n' a6 = v18 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v75 ∧
      reg n' (19 : Fin 32) = v10 ∧
      reg n' (20 : Fin 32) = v108 ∧
      reg n' (21 : Fin 32) = v95 ∧
      reg n' (22 : Fin 32) = v89 ∧
      reg n' (23 : Fin 32) = v82 ∧
      reg n' (24 : Fin 32) = v71 ∧
      reg n' (25 : Fin 32) = v61 ∧
      reg n' (26 : Fin 32) = v9 ∧
      reg n' (27 : Fin 32) = v8 ∧
      reg n' (28 : Fin 32) = v60 ∧
      reg n' (29 : Fin 32) = v4 ∧
      reg n' (30 : Fin 32) = v19 ∧
      reg n' (31 : Fin 32) = v114 ∧
      memLoad32 M' (F + 0x20) = v7 ∧
      memLoad32 M' (F + 0x24) = v0 ∧
      memLoad32 M' (F + 0x28) = outp ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (F + 0x50) = memLoad32 M0 (F + 0x50) ∧
      memLoad32 M' (F + 0x54) = memLoad32 M0 (F + 0x54) ∧
      memLoad32 M' (F + 0x58) = memLoad32 M0 (F + 0x58) ∧
      memLoad32 M' (F + 0x5C) = memLoad32 M0 (F + 0x5C) ∧
      memLoad32 M' (F + 0x60) = memLoad32 M0 (F + 0x60) ∧
      memLoad32 M' (F + 0x64) = memLoad32 M0 (F + 0x64) ∧
      memLoad32 M' (F + 0x68) = memLoad32 M0 (F + 0x68) ∧
      memLoad32 M' (F + 0x6C) = memLoad32 M0 (F + 0x6C) ∧
      memLoad32 M' (F + 0x70) = memLoad32 M0 (F + 0x70) ∧
      memLoad32 M' (F + 0x74) = memLoad32 M0 (F + 0x74) ∧
      memLoad32 M' (F + 0x78) = memLoad32 M0 (F + 0x78) ∧
      memLoad32 M' (F + 0x7C) = memLoad32 M0 (F + 0x7C) ∧
      memLoad32 M' (F + 0x80) = memLoad32 M0 (F + 0x80) ∧
      memLoad32 M' (F + 0x84) = memLoad32 M0 (F + 0x84) ∧
      memLoad32 M' (F + 0x88) = memLoad32 M0 (F + 0x88) ∧
      memLoad32 M' (F + 0x8C) = memLoad32 M0 (F + 0x8C) ∧
      memLoad32 M' (F + 0x90) = memLoad32 M0 (F + 0x90) ∧
      memLoad32 M' (F + 0x94) = memLoad32 M0 (F + 0x94) ∧
      memLoad32 M' (F + 0x98) = memLoad32 M0 (F + 0x98) ∧
      memLoad32 M' (F + 0x9C) = memLoad32 M0 (F + 0x9C) ∧
      aluEval .add v74 v78 = v80 ∧
      aluEval .add v69 v79 = v81 ∧
      aluEval .add v76 v80 = v82 ∧
      aluEval .add v7 v7 = v83 ∧
      aluEval .sltu v82 v76 = v84 ∧
      aluEval .sub v52 v83 = v85 ∧
      aluEval .add v81 v84 = v86 ∧
      aluEval .sltu v85 v52 = v87 ∧
      aluEval .add v77 v87 = v88 ∧
      aluEval .add v85 v86 = v89 ∧
      aluEval .sltu v89 v85 = v90 ∧
      aluEval .sub v58 v7 = v91 ∧
      aluEval .add v90 v88 = v93 ∧
      aluEval .sltu v91 v58 = v94 ∧
      aluEval .add v91 v93 = v95 ∧
      aluEval .mul v8 v3 = v96 ∧
      aluEval .add v69 v94 = v97 ∧
      aluEval .sltu v95 v91 = v98 ∧
      aluEval .add v97 v98 = v99 ∧
      aluEval .mul v8 v4 = v100 ∧
      aluEval .add v99 v0 = v101 ∧
      aluEval .mulhu v8 v3 = v102 ∧
      aluEval .sltu v101 v99 = v103 ∧
      aluEval .and v60 0xFFFFFFFE = v104 ∧
      aluEval .mulhu v8 v4 = v105 ∧
      aluEval .add v96 v104 = v106 ∧
      aluEval .mul v8 v12 = v107 ∧
      aluEval .add v103 v7 = v108 ∧
      aluEval .sltu v106 v104 = v109 ∧
      aluEval .add v100 v67 = v110 ∧
      aluEval .mulhu v8 v12 = v111 ∧
      aluEval .add v109 v102 = v112 ∧
      aluEval .sltu v110 v67 = v113 ∧
      aluEval .add v110 v112 = v114 ∧
      aluEval .mul v8 v19 = v115 ∧
      aluEval .add v105 v113 = v116 ∧
      aluEval .sltu v114 v110 = v117 ∧
      aluEval .add v107 v75 = v118 ∧
      aluEval .mulhu v8 v19 = v119 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n80, v80, d80, hv80, u80⟩ := s.aluG hc psm_at_12c (off' := 0x12E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv80
  obtain ⟨n81, v81, d81, hv81, u81⟩ := u80.aluG hc psm_at_12e (off' := 0x132) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv81
  obtain ⟨n82, v82, d82, hv82, u82⟩ := u81.aluG hc psm_at_132 (off' := 0x136) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv82
  obtain ⟨n83, v83, d83, hv83, u83⟩ := u82.aluG hc psm_at_136 (off' := 0x13A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv83
  obtain ⟨n84, v84, d84, hv84, u84⟩ := u83.aluG hc psm_at_13a (off' := 0x13E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv84
  obtain ⟨n85, v85, d85, hv85, u85⟩ := u84.aluG hc psm_at_13e (off' := 0x142) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv85
  obtain ⟨n86, v86, d86, hv86, u86⟩ := u85.aluG hc psm_at_142 (off' := 0x144) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv86
  obtain ⟨n87, v87, d87, hv87, u87⟩ := u86.aluG hc psm_at_144 (off' := 0x148) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv87
  obtain ⟨n88, v88, d88, hv88, u88⟩ := u87.aluG hc psm_at_148 (off' := 0x14A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv88
  obtain ⟨n89, v89, d89, hv89, u89⟩ := u88.aluG hc psm_at_14a (off' := 0x14E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv89
  obtain ⟨n90, v90, d90, hv90, u90⟩ := u89.aluG hc psm_at_14e (off' := 0x152) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv90
  obtain ⟨n91, v91, d91, hv91, u91⟩ := u90.aluG hc psm_at_152 (off' := 0x156) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv91
  obtain ⟨n92, d92, u92⟩ := u91.swG hc psm_at_156 (off' := 0x158) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 32) (by decide)) (a := F + 0x20) (v := v7)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M92, hM92⟩ : ∃ M', memStore32 Mi (F + 0x20) v7 = M' := ⟨_, rfl⟩
  rw [hM92] at u92
  have hc92 : CodeIn M92 B p256ScalarMulCode := by rw [← hM92]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr92 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M92 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM92, memStore32_get_sep (frm_sep' hx1 (by decide)), fr x hx1 hx2 hx3]
  obtain ⟨n93, v93, d93, hv93, u93⟩ := u92.aluG hc92 psm_at_158 (off' := 0x15A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv93
  obtain ⟨n94, v94, d94, hv94, u94⟩ := u93.aluG hc92 psm_at_15a (off' := 0x15E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv94
  obtain ⟨n95, v95, d95, hv95, u95⟩ := u94.aluG hc92 psm_at_15e (off' := 0x162) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv95
  obtain ⟨n96, v96, d96, hv96, u96⟩ := u95.aluG hc92 psm_at_162 (off' := 0x166) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv96
  obtain ⟨n97, v97, d97, hv97, u97⟩ := u96.aluG hc92 psm_at_166 (off' := 0x168) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv97
  obtain ⟨n98, v98, d98, hv98, u98⟩ := u97.aluG hc92 psm_at_168 (off' := 0x16C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv98
  obtain ⟨n99, v99, d99, hv99, u99⟩ := u98.aluG hc92 psm_at_16c (off' := 0x16E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv99
  obtain ⟨n100, v100, d100, hv100, u100⟩ := u99.aluG hc92 psm_at_16e (off' := 0x172) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv100
  obtain ⟨n101, v101, d101, hv101, u101⟩ := u100.aluG hc92 psm_at_172 (off' := 0x176) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv101
  obtain ⟨n102, v102, d102, hv102, u102⟩ := u101.aluG hc92 psm_at_176 (off' := 0x17A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv102
  obtain ⟨n103, v103, d103, hv103, u103⟩ := u102.aluG hc92 psm_at_17a (off' := 0x17E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv103
  obtain ⟨n104, v104, d104, hv104, u104⟩ := u103.aluImmG hc92 psm_at_17e (off' := 0x182) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv104
  obtain ⟨n105, v105, d105, hv105, u105⟩ := u104.aluG hc92 psm_at_182 (off' := 0x186) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv105
  obtain ⟨n106, v106, d106, hv106, u106⟩ := u105.aluG hc92 psm_at_186 (off' := 0x188) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv106
  obtain ⟨n107, v107, d107, hv107, u107⟩ := u106.aluG hc92 psm_at_188 (off' := 0x18C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv107
  obtain ⟨n108, v108, d108, hv108, u108⟩ := u107.aluG hc92 psm_at_18c (off' := 0x190) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv108
  obtain ⟨n109, v109, d109, hv109, u109⟩ := u108.aluG hc92 psm_at_190 (off' := 0x194) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv109
  obtain ⟨n110, v110, d110, hv110, u110⟩ := u109.aluG hc92 psm_at_194 (off' := 0x196) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv110
  obtain ⟨n111, v111, d111, hv111, u111⟩ := u110.aluG hc92 psm_at_196 (off' := 0x19A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv111
  obtain ⟨n112, v112, d112, hv112, u112⟩ := u111.aluG hc92 psm_at_19a (off' := 0x19C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv112
  obtain ⟨n113, v113, d113, hv113, u113⟩ := u112.aluG hc92 psm_at_19c (off' := 0x1A0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv113
  obtain ⟨n114, v114, d114, hv114, u114⟩ := u113.aluG hc92 psm_at_1a0 (off' := 0x1A4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv114
  obtain ⟨n115, v115, d115, hv115, u115⟩ := u114.aluG hc92 psm_at_1a4 (off' := 0x1A8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv115
  obtain ⟨n116, v116, d116, hv116, u116⟩ := u115.aluG hc92 psm_at_1a8 (off' := 0x1AA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv116
  obtain ⟨n117, v117, d117, hv117, u117⟩ := u116.aluG hc92 psm_at_1aa (off' := 0x1AE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv117
  obtain ⟨n118, v118, d118, hv118, u118⟩ := u117.aluG hc92 psm_at_1ae (off' := 0x1B0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv118
  obtain ⟨n119, v119, d119, hv119, u119⟩ := u118.aluG hc92 psm_at_1b0 (off' := 0x1B4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv119
  have qo1 : reg n119 ra = v0 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n119 sp = F := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n119 (3 : Fin 32) = G3 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n119 (4 : Fin 32) = G4 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n119 (5 : Fin 32) = v3 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n119 (6 : Fin 32) = v12 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n119 (7 : Fin 32) = v103 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n119 (8 : Fin 32) = v101 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n119 (9 : Fin 32) = v119 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n119 a0 = v7 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n119 a1 = v115 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n119 a2 = v111 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n119 a3 = v117 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n119 a4 = v116 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n119 a5 = v118 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n119 a6 = v18 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n119 a7 = v17 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n119 (18 : Fin 32) = v75 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n119 (19 : Fin 32) = v10 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n119 (20 : Fin 32) = v108 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n119 (21 : Fin 32) = v95 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n119 (22 : Fin 32) = v89 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n119 (23 : Fin 32) = v82 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n119 (24 : Fin 32) = v71 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n119 (25 : Fin 32) = v61 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n119 (26 : Fin 32) = v9 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n119 (27 : Fin 32) = v8 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n119 (28 : Fin 32) = v60 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n119 (29 : Fin 32) = v4 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n119 (30 : Fin 32) = v19 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n119 (31 : Fin 32) = v114 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so20 : memLoad32 M92 (F + 0x20) = v7 := by
    rw [← hM92, memLoad32_store32_same]
  have so24 : memLoad32 M92 (F + 0x24) = v0 := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x24) 4 from sep_offsets F (c := 32) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), sl24]
  have so28 : memLoad32 M92 (F + 0x28) = outp := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x28) 4 from sep_offsets F (c := 32) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), sl28]
  have so2C : memLoad32 M92 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x2C) 4 from sep_offsets F (c := 32) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), sl2C]
  have so30 : memLoad32 M92 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x30) 4 from sep_offsets F (c := 32) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), sl30]
  have so34 : memLoad32 M92 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x34) 4 from sep_offsets F (c := 32) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), sl34]
  have so38 : memLoad32 M92 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x38) 4 from sep_offsets F (c := 32) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), sl38]
  have so3C : memLoad32 M92 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x3C) 4 from sep_offsets F (c := 32) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), sl3C]
  have so40 : memLoad32 M92 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x40) 4 from sep_offsets F (c := 32) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), sl40]
  have so44 : memLoad32 M92 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x44) 4 from sep_offsets F (c := 32) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), sl44]
  have so48 : memLoad32 M92 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x48) 4 from sep_offsets F (c := 32) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), sl48]
  have so4C : memLoad32 M92 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x4C) 4 from sep_offsets F (c := 32) (n := 4) (d := 76) (k := 4) (by decide) (by decide) (by decide)), sl4C]
  have so50 : memLoad32 M92 (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x50) 4 from sep_offsets F (c := 32) (n := 4) (d := 80) (k := 4) (by decide) (by decide) (by decide)), sl50]
  have so54 : memLoad32 M92 (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x54) 4 from sep_offsets F (c := 32) (n := 4) (d := 84) (k := 4) (by decide) (by decide) (by decide)), sl54]
  have so58 : memLoad32 M92 (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x58) 4 from sep_offsets F (c := 32) (n := 4) (d := 88) (k := 4) (by decide) (by decide) (by decide)), sl58]
  have so5C : memLoad32 M92 (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x5C) 4 from sep_offsets F (c := 32) (n := 4) (d := 92) (k := 4) (by decide) (by decide) (by decide)), sl5C]
  have so60 : memLoad32 M92 (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x60) 4 from sep_offsets F (c := 32) (n := 4) (d := 96) (k := 4) (by decide) (by decide) (by decide)), sl60]
  have so64 : memLoad32 M92 (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x64) 4 from sep_offsets F (c := 32) (n := 4) (d := 100) (k := 4) (by decide) (by decide) (by decide)), sl64]
  have so68 : memLoad32 M92 (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x68) 4 from sep_offsets F (c := 32) (n := 4) (d := 104) (k := 4) (by decide) (by decide) (by decide)), sl68]
  have so6C : memLoad32 M92 (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x6C) 4 from sep_offsets F (c := 32) (n := 4) (d := 108) (k := 4) (by decide) (by decide) (by decide)), sl6C]
  have so70 : memLoad32 M92 (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x70) 4 from sep_offsets F (c := 32) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), sl70]
  have so74 : memLoad32 M92 (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x74) 4 from sep_offsets F (c := 32) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), sl74]
  have so78 : memLoad32 M92 (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x78) 4 from sep_offsets F (c := 32) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), sl78]
  have so7C : memLoad32 M92 (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x7C) 4 from sep_offsets F (c := 32) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), sl7C]
  have so80 : memLoad32 M92 (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x80) 4 from sep_offsets F (c := 32) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), sl80]
  have so84 : memLoad32 M92 (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x84) 4 from sep_offsets F (c := 32) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), sl84]
  have so88 : memLoad32 M92 (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x88) 4 from sep_offsets F (c := 32) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88]
  have so8C : memLoad32 M92 (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x8C) 4 from sep_offsets F (c := 32) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), sl8C]
  have so90 : memLoad32 M92 (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x90) 4 from sep_offsets F (c := 32) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), sl90]
  have so94 : memLoad32 M92 (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x94) 4 from sep_offsets F (c := 32) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94]
  have so98 : memLoad32 M92 (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x98) 4 from sep_offsets F (c := 32) (n := 4) (d := 152) (k := 4) (by decide) (by decide) (by decide)), sl98]
  have so9C : memLoad32 M92 (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [← hM92, memLoad32_store32_sep (show Sep (F + 0x20) 4 (F + 0x9C) 4 from sep_offsets F (c := 32) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  exact ⟨n119, M92, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, (.cons d80 (.cons d81 (.cons d82 (.cons d83 (.cons d84 (.cons d85 (.cons d86 (.cons d87 (.cons d88 (.cons d89 (.cons d90 (.cons d91 (.cons d92 (.cons d93 (.cons d94 (.cons d95 (.cons d96 (.cons d97 (.cons d98 (.cons d99 (.cons d100 (.cons d101 (.cons d102 (.cons d103 (.cons d104 (.cons d105 (.cons d106 (.cons d107 (.cons d108 (.cons d109 (.cons d110 (.cons d111 (.cons d112 (.cons d113 (.cons d114 (.cons d115 (.cons d116 (.cons d117 (.cons d118 (.single d119)))))))))))))))))))))))))))))))))))))))), u119.self, hc92, fr92, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv80, hv81, hv82, hv83, hv84, hv85, hv86, hv87, hv88, hv89, hv90, hv91, hv93, hv94, hv95, hv96, hv97, hv98, hv99, hv100, hv101, hv102, hv103, hv104, hv105, hv106, hv107, hv108, hv109, hv110, hv111, hv112, hv113, hv114, hv115, hv116, hv117, hv118, hv119⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g3 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v3 v4 v7 v8 v9 v10 v12 v17 v18 v19 v60 v61 v71 v75 v82 v89 v95 v101 v103 v108 v111 v114 v115 v116 v117 v118 v119 : Word}
    (s : St Mi B n 0x1B4 (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q1 : reg n ra = v0)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v3)
    (q6 : reg n (6 : Fin 32) = v12)
    (q7 : reg n (7 : Fin 32) = v103)
    (q8 : reg n (8 : Fin 32) = v101)
    (q9 : reg n (9 : Fin 32) = v119)
    (q10 : reg n a0 = v7)
    (q11 : reg n a1 = v115)
    (q12 : reg n a2 = v111)
    (q13 : reg n a3 = v117)
    (q14 : reg n a4 = v116)
    (q15 : reg n a5 = v118)
    (q16 : reg n a6 = v18)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v75)
    (q19 : reg n (19 : Fin 32) = v10)
    (q20 : reg n (20 : Fin 32) = v108)
    (q21 : reg n (21 : Fin 32) = v95)
    (q22 : reg n (22 : Fin 32) = v89)
    (q23 : reg n (23 : Fin 32) = v82)
    (q24 : reg n (24 : Fin 32) = v71)
    (q25 : reg n (25 : Fin 32) = v61)
    (q26 : reg n (26 : Fin 32) = v9)
    (q27 : reg n (27 : Fin 32) = v8)
    (q28 : reg n (28 : Fin 32) = v60)
    (q29 : reg n (29 : Fin 32) = v4)
    (q30 : reg n (30 : Fin 32) = v19)
    (q31 : reg n (31 : Fin 32) = v114)
    (sl20 : memLoad32 Mi (F + 0x20) = v7)
    (sl24 : memLoad32 Mi (F + 0x24) = v0)
    (sl28 : memLoad32 Mi (F + 0x28) = outp)
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    (sl50 : memLoad32 Mi (F + 0x50) = memLoad32 M0 (F + 0x50))
    (sl54 : memLoad32 Mi (F + 0x54) = memLoad32 M0 (F + 0x54))
    (sl58 : memLoad32 Mi (F + 0x58) = memLoad32 M0 (F + 0x58))
    (sl5C : memLoad32 Mi (F + 0x5C) = memLoad32 M0 (F + 0x5C))
    (sl60 : memLoad32 Mi (F + 0x60) = memLoad32 M0 (F + 0x60))
    (sl64 : memLoad32 Mi (F + 0x64) = memLoad32 M0 (F + 0x64))
    (sl68 : memLoad32 Mi (F + 0x68) = memLoad32 M0 (F + 0x68))
    (sl6C : memLoad32 Mi (F + 0x6C) = memLoad32 M0 (F + 0x6C))
    (sl70 : memLoad32 Mi (F + 0x70) = memLoad32 M0 (F + 0x70))
    (sl74 : memLoad32 Mi (F + 0x74) = memLoad32 M0 (F + 0x74))
    (sl78 : memLoad32 Mi (F + 0x78) = memLoad32 M0 (F + 0x78))
    (sl7C : memLoad32 Mi (F + 0x7C) = memLoad32 M0 (F + 0x7C))
    (sl80 : memLoad32 Mi (F + 0x80) = memLoad32 M0 (F + 0x80))
    (sl84 : memLoad32 Mi (F + 0x84) = memLoad32 M0 (F + 0x84))
    (sl88 : memLoad32 Mi (F + 0x88) = memLoad32 M0 (F + 0x88))
    (sl8C : memLoad32 Mi (F + 0x8C) = memLoad32 M0 (F + 0x8C))
    (sl90 : memLoad32 Mi (F + 0x90) = memLoad32 M0 (F + 0x90))
    (sl94 : memLoad32 Mi (F + 0x94) = memLoad32 M0 (F + 0x94))
    (sl98 : memLoad32 Mi (F + 0x98) = memLoad32 M0 (F + 0x98))
    (sl9C : memLoad32 Mi (F + 0x9C) = memLoad32 M0 (F + 0x9C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v148 v149 v150 v151 v152 v153 v154 v155 v156 v157 v158 v159 : Word),
      Steps n n' ∧
      St M' B n' 0x236 (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v123 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v3 ∧
      reg n' (6 : Fin 32) = v12 ∧
      reg n' (7 : Fin 32) = v159 ∧
      reg n' (8 : Fin 32) = v101 ∧
      reg n' (9 : Fin 32) = v133 ∧
      reg n' a0 = v153 ∧
      reg n' a1 = v134 ∧
      reg n' a2 = v152 ∧
      reg n' a3 = v120 ∧
      reg n' a4 = v155 ∧
      reg n' a5 = v125 ∧
      reg n' a6 = v18 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v75 ∧
      reg n' (19 : Fin 32) = v10 ∧
      reg n' (20 : Fin 32) = v154 ∧
      reg n' (21 : Fin 32) = v95 ∧
      reg n' (22 : Fin 32) = v149 ∧
      reg n' (23 : Fin 32) = v143 ∧
      reg n' (24 : Fin 32) = v129 ∧
      reg n' (25 : Fin 32) = v137 ∧
      reg n' (26 : Fin 32) = v9 ∧
      reg n' (27 : Fin 32) = v157 ∧
      reg n' (28 : Fin 32) = v158 ∧
      reg n' (29 : Fin 32) = v4 ∧
      reg n' (30 : Fin 32) = v19 ∧
      reg n' (31 : Fin 32) = v114 ∧
      memLoad32 M' (F + 0x20) = v7 ∧
      memLoad32 M' (F + 0x24) = v0 ∧
      memLoad32 M' (F + 0x28) = outp ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (F + 0x50) = memLoad32 M0 (F + 0x50) ∧
      memLoad32 M' (F + 0x54) = memLoad32 M0 (F + 0x54) ∧
      memLoad32 M' (F + 0x58) = memLoad32 M0 (F + 0x58) ∧
      memLoad32 M' (F + 0x5C) = memLoad32 M0 (F + 0x5C) ∧
      memLoad32 M' (F + 0x60) = memLoad32 M0 (F + 0x60) ∧
      memLoad32 M' (F + 0x64) = memLoad32 M0 (F + 0x64) ∧
      memLoad32 M' (F + 0x68) = memLoad32 M0 (F + 0x68) ∧
      memLoad32 M' (F + 0x6C) = memLoad32 M0 (F + 0x6C) ∧
      memLoad32 M' (F + 0x70) = memLoad32 M0 (F + 0x70) ∧
      memLoad32 M' (F + 0x74) = memLoad32 M0 (F + 0x74) ∧
      memLoad32 M' (F + 0x78) = memLoad32 M0 (F + 0x78) ∧
      memLoad32 M' (F + 0x7C) = memLoad32 M0 (F + 0x7C) ∧
      memLoad32 M' (F + 0x80) = memLoad32 M0 (F + 0x80) ∧
      memLoad32 M' (F + 0x84) = memLoad32 M0 (F + 0x84) ∧
      memLoad32 M' (F + 0x88) = memLoad32 M0 (F + 0x88) ∧
      memLoad32 M' (F + 0x8C) = memLoad32 M0 (F + 0x8C) ∧
      memLoad32 M' (F + 0x90) = memLoad32 M0 (F + 0x90) ∧
      memLoad32 M' (F + 0x94) = memLoad32 M0 (F + 0x94) ∧
      memLoad32 M' (F + 0x98) = memLoad32 M0 (F + 0x98) ∧
      memLoad32 M' (F + 0x9C) = memLoad32 M0 (F + 0x9C) ∧
      aluEval .add v117 v116 = v120 ∧
      aluEval .sltu v118 v75 = v121 ∧
      aluEval .add v111 v121 = v122 ∧
      aluEval .add v118 v120 = v123 ∧
      aluEval .sltu v123 v118 = v124 ∧
      aluEval .mulhu v8 v17 = v125 ∧
      aluEval .add v122 v124 = v126 ∧
      aluEval .add v115 v82 = v127 ∧
      aluEval .sltu v127 v82 = v128 ∧
      aluEval .add v127 v126 = v129 ∧
      aluEval .add v128 v119 = v130 ∧
      aluEval .sltu v129 v127 = v131 ∧
      aluEval .sub v89 v8 = v132 ∧
      aluEval .mulhu v8 v18 = v133 ∧
      aluEval .add v131 v130 = v134 ∧
      aluEval .sltu v132 v89 = v135 ∧
      aluEval .add v135 v125 = v136 ∧
      aluEval .add v132 v134 = v137 ∧
      aluEval .sltu v137 v132 = v138 ∧
      aluEval .add v8 v8 = v139 ∧
      aluEval .add v138 v136 = v140 ∧
      aluEval .sub v95 v139 = v141 ∧
      aluEval .sltu v141 v95 = v142 ∧
      aluEval .add v141 v140 = v143 ∧
      aluEval .add v142 v133 = v144 ∧
      aluEval .sltu v143 v141 = v145 ∧
      aluEval .add v145 v144 = v146 ∧
      aluEval .sub v101 v8 = v147 ∧
      aluEval .sltu v147 v101 = v148 ∧
      aluEval .add v147 v146 = v149 ∧
      aluEval .add v148 v125 = v150 ∧
      aluEval .sltu v149 v147 = v151 ∧
      aluEval .sltu v108 v103 = v152 ∧
      aluEval .add v151 v150 = v153 ∧
      aluEval .add v108 v153 = v154 ∧
      aluEval .mul v9 v3 = v155 ∧
      aluEval .sltu v154 v153 = v156 ∧
      aluEval .add v8 v152 = v157 ∧
      aluEval .add v156 v157 = v158 ∧
      aluEval .sltu v157 v152 = v159 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n120, v120, d120, hv120, u120⟩ := s.aluG hc psm_at_1b4 (off' := 0x1B6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv120
  obtain ⟨n121, v121, d121, hv121, u121⟩ := u120.aluG hc psm_at_1b6 (off' := 0x1BA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv121
  obtain ⟨n122, v122, d122, hv122, u122⟩ := u121.aluG hc psm_at_1ba (off' := 0x1BC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv122
  obtain ⟨n123, v123, d123, hv123, u123⟩ := u122.aluG hc psm_at_1bc (off' := 0x1C0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv123
  obtain ⟨n124, v124, d124, hv124, u124⟩ := u123.aluG hc psm_at_1c0 (off' := 0x1C4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv124
  obtain ⟨n125, v125, d125, hv125, u125⟩ := u124.aluG hc psm_at_1c4 (off' := 0x1C8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv125
  obtain ⟨n126, v126, d126, hv126, u126⟩ := u125.aluG hc psm_at_1c8 (off' := 0x1CA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv126
  obtain ⟨n127, v127, d127, hv127, u127⟩ := u126.aluG hc psm_at_1ca (off' := 0x1CC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv127
  obtain ⟨n128, v128, d128, hv128, u128⟩ := u127.aluG hc psm_at_1cc (off' := 0x1D0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv128
  obtain ⟨n129, v129, d129, hv129, u129⟩ := u128.aluG hc psm_at_1d0 (off' := 0x1D4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv129
  obtain ⟨n130, v130, d130, hv130, u130⟩ := u129.aluG hc psm_at_1d4 (off' := 0x1D6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv130
  obtain ⟨n131, v131, d131, hv131, u131⟩ := u130.aluG hc psm_at_1d6 (off' := 0x1DA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv131
  obtain ⟨n132, v132, d132, hv132, u132⟩ := u131.aluG hc psm_at_1da (off' := 0x1DE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv132
  obtain ⟨n133, v133, d133, hv133, u133⟩ := u132.aluG hc psm_at_1de (off' := 0x1E2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv133
  obtain ⟨n134, v134, d134, hv134, u134⟩ := u133.aluG hc psm_at_1e2 (off' := 0x1E4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv134
  obtain ⟨n135, v135, d135, hv135, u135⟩ := u134.aluG hc psm_at_1e4 (off' := 0x1E8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv135
  obtain ⟨n136, v136, d136, hv136, u136⟩ := u135.aluG hc psm_at_1e8 (off' := 0x1EA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv136
  obtain ⟨n137, v137, d137, hv137, u137⟩ := u136.aluG hc psm_at_1ea (off' := 0x1EE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv137
  obtain ⟨n138, v138, d138, hv138, u138⟩ := u137.aluG hc psm_at_1ee (off' := 0x1F2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv138
  obtain ⟨n139, v139, d139, hv139, u139⟩ := u138.aluG hc psm_at_1f2 (off' := 0x1F6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv139
  obtain ⟨n140, v140, d140, hv140, u140⟩ := u139.aluG hc psm_at_1f6 (off' := 0x1F8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv140
  obtain ⟨n141, v141, d141, hv141, u141⟩ := u140.aluG hc psm_at_1f8 (off' := 0x1FC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv141
  obtain ⟨n142, v142, d142, hv142, u142⟩ := u141.aluG hc psm_at_1fc (off' := 0x200) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv142
  obtain ⟨n143, v143, d143, hv143, u143⟩ := u142.aluG hc psm_at_200 (off' := 0x204) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv143
  obtain ⟨n144, v144, d144, hv144, u144⟩ := u143.aluG hc psm_at_204 (off' := 0x206) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv144
  obtain ⟨n145, v145, d145, hv145, u145⟩ := u144.aluG hc psm_at_206 (off' := 0x20A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv145
  obtain ⟨n146, v146, d146, hv146, u146⟩ := u145.aluG hc psm_at_20a (off' := 0x20C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv146
  obtain ⟨n147, v147, d147, hv147, u147⟩ := u146.aluG hc psm_at_20c (off' := 0x210) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv147
  obtain ⟨n148, v148, d148, hv148, u148⟩ := u147.aluG hc psm_at_210 (off' := 0x214) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv148
  obtain ⟨n149, v149, d149, hv149, u149⟩ := u148.aluG hc psm_at_214 (off' := 0x218) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv149
  obtain ⟨n150, v150, d150, hv150, u150⟩ := u149.aluG hc psm_at_218 (off' := 0x21A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv150
  obtain ⟨n151, v151, d151, hv151, u151⟩ := u150.aluG hc psm_at_21a (off' := 0x21E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv151
  obtain ⟨n152, v152, d152, hv152, u152⟩ := u151.aluG hc psm_at_21e (off' := 0x222) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv152
  obtain ⟨n153, v153, d153, hv153, u153⟩ := u152.aluG hc psm_at_222 (off' := 0x224) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv153
  obtain ⟨n154, v154, d154, hv154, u154⟩ := u153.aluG hc psm_at_224 (off' := 0x226) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv154
  obtain ⟨n155, v155, d155, hv155, u155⟩ := u154.aluG hc psm_at_226 (off' := 0x22A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv155
  obtain ⟨n156, v156, d156, hv156, u156⟩ := u155.aluG hc psm_at_22a (off' := 0x22E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv156
  obtain ⟨n157, v157, d157, hv157, u157⟩ := u156.aluG hc psm_at_22e (off' := 0x230) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv157
  obtain ⟨n158, v158, d158, hv158, u158⟩ := u157.aluG hc psm_at_230 (off' := 0x232) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv158
  obtain ⟨n159, v159, d159, hv159, u159⟩ := u158.aluG hc psm_at_232 (off' := 0x236) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv159
  have qo1 : reg n159 ra = v123 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n159 sp = F := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n159 (3 : Fin 32) = G3 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n159 (4 : Fin 32) = G4 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n159 (5 : Fin 32) = v3 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n159 (6 : Fin 32) = v12 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n159 (7 : Fin 32) = v159 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n159 (8 : Fin 32) = v101 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n159 (9 : Fin 32) = v133 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n159 a0 = v153 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n159 a1 = v134 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n159 a2 = v152 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n159 a3 = v120 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n159 a4 = v155 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n159 a5 = v125 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n159 a6 = v18 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n159 a7 = v17 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n159 (18 : Fin 32) = v75 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n159 (19 : Fin 32) = v10 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n159 (20 : Fin 32) = v154 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n159 (21 : Fin 32) = v95 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n159 (22 : Fin 32) = v149 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n159 (23 : Fin 32) = v143 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n159 (24 : Fin 32) = v129 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n159 (25 : Fin 32) = v137 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n159 (26 : Fin 32) = v9 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n159 (27 : Fin 32) = v157 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n159 (28 : Fin 32) = v158 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n159 (29 : Fin 32) = v4 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n159 (30 : Fin 32) = v19 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n159 (31 : Fin 32) = v114 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so20 : memLoad32 Mi (F + 0x20) = v7 := by
    rw [sl20]
  have so24 : memLoad32 Mi (F + 0x24) = v0 := by
    rw [sl24]
  have so28 : memLoad32 Mi (F + 0x28) = outp := by
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
  have so50 : memLoad32 Mi (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [sl50]
  have so54 : memLoad32 Mi (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [sl54]
  have so58 : memLoad32 Mi (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [sl58]
  have so5C : memLoad32 Mi (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [sl5C]
  have so60 : memLoad32 Mi (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [sl60]
  have so64 : memLoad32 Mi (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [sl64]
  have so68 : memLoad32 Mi (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [sl68]
  have so6C : memLoad32 Mi (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [sl6C]
  have so70 : memLoad32 Mi (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [sl70]
  have so74 : memLoad32 Mi (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [sl74]
  have so78 : memLoad32 Mi (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [sl78]
  have so7C : memLoad32 Mi (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [sl7C]
  have so80 : memLoad32 Mi (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [sl80]
  have so84 : memLoad32 Mi (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [sl84]
  have so88 : memLoad32 Mi (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [sl88]
  have so8C : memLoad32 Mi (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [sl8C]
  have so90 : memLoad32 Mi (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [sl90]
  have so94 : memLoad32 Mi (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [sl94]
  have so98 : memLoad32 Mi (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [sl98]
  have so9C : memLoad32 Mi (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [sl9C]
  exact ⟨n159, Mi, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, (.cons d120 (.cons d121 (.cons d122 (.cons d123 (.cons d124 (.cons d125 (.cons d126 (.cons d127 (.cons d128 (.cons d129 (.cons d130 (.cons d131 (.cons d132 (.cons d133 (.cons d134 (.cons d135 (.cons d136 (.cons d137 (.cons d138 (.cons d139 (.cons d140 (.cons d141 (.cons d142 (.cons d143 (.cons d144 (.cons d145 (.cons d146 (.cons d147 (.cons d148 (.cons d149 (.cons d150 (.cons d151 (.cons d152 (.cons d153 (.cons d154 (.cons d155 (.cons d156 (.cons d157 (.cons d158 (.single d159)))))))))))))))))))))))))))))))))))))))), u159.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv120, hv121, hv122, hv123, hv124, hv125, hv126, hv127, hv128, hv129, hv130, hv131, hv132, hv133, hv134, hv135, hv136, hv137, hv138, hv139, hv140, hv141, hv142, hv143, hv144, hv145, hv146, hv147, hv148, hv149, hv150, hv151, hv152, hv153, hv154, hv155, hv156, hv157, hv158, hv159⟩

end C3.RV32
