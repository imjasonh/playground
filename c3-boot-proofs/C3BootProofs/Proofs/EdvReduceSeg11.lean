import C3BootProofs.Proofs.EdvReduceFacts

/-! # The inlined `Scalar::reduce` in `ed25519_verify`, segments 33 to 34

Each theorem steps 40 instructions. `scripts/gen-ev-reduce.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g33 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v302 v357 v481 v485 v540 v545 v557 v559 v572 v579 v582 v702 v722 v803 v819 v945 v991 v997 v1014 v1022 v1026 v1038 v1060 v1064 v1069 v1072 v1074 v1076 v1077 v1079 : Word}
    (s : St Mi B n 0xE4E (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v357)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v1060)
    (q6 : reg n (6 : Fin 32) = v1038)
    (q7 : reg n (7 : Fin 32) = v991)
    (q8 : reg n (8 : Fin 32) = v1022)
    (q9 : reg n (9 : Fin 32) = v1072)
    (q10 : reg n a0 = v1079)
    (q11 : reg n a1 = v1077)
    (q12 : reg n a2 = v1064)
    (q13 : reg n a3 = v1074)
    (q14 : reg n a4 = v1069)
    (q15 : reg n a5 = v1026)
    (q16 : reg n a6 = v945)
    (q17 : reg n a7 = v485)
    (q18 : reg n (18 : Fin 32) = v7)
    (q19 : reg n (19 : Fin 32) = v572)
    (q20 : reg n (20 : Fin 32) = v722)
    (q21 : reg n (21 : Fin 32) = v579)
    (q22 : reg n (22 : Fin 32) = v557)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v582)
    (q25 : reg n (25 : Fin 32) = v559)
    (q26 : reg n (26 : Fin 32) = v545)
    (q27 : reg n (27 : Fin 32) = v1014)
    (q28 : reg n (28 : Fin 32) = v1076)
    (q29 : reg n (29 : Fin 32) = v819)
    (q30 : reg n (30 : Fin 32) = v997)
    (q31 : reg n (31 : Fin 32) = v481)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (sl100 : memLoad32 Mi (F + 0x100) = v540)
    (sl110 : memLoad32 Mi (F + 0x110) = v702)
    (sl118 : memLoad32 Mi (F + 0x118) = v803)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v1080 v1081 v1084 v1085 v1086 v1087 v1088 v1089 v1090 v1091 v1092 v1093 v1094 v1095 v1096 v1097 v1099 v1100 v1101 v1104 v1105 v1106 v1107 v1108 v1109 v1110 v1111 v1112 v1113 v1114 v1116 v1117 v1118 v1119 : Word),
      Steps n n' ∧
      St M' B n' 0xEC8 (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v357 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v1060 ∧
      reg n' (6 : Fin 32) = v1038 ∧
      reg n' (7 : Fin 32) = v991 ∧
      reg n' (8 : Fin 32) = v1109 ∧
      reg n' (9 : Fin 32) = v1092 ∧
      reg n' a0 = v1112 ∧
      reg n' a1 = v1119 ∧
      reg n' a2 = v1113 ∧
      reg n' a3 = v1118 ∧
      reg n' a4 = v1117 ∧
      reg n' a5 = F + 0x100 ∧
      reg n' a6 = v945 ∧
      reg n' a7 = v1116 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = F + 0x90F ∧
      reg n' (20 : Fin 32) = v722 ∧
      reg n' (21 : Fin 32) = v579 ∧
      reg n' (22 : Fin 32) = v557 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v582 ∧
      reg n' (25 : Fin 32) = v559 ∧
      reg n' (26 : Fin 32) = v545 ∧
      reg n' (27 : Fin 32) = v1014 ∧
      reg n' (28 : Fin 32) = v1076 ∧
      reg n' (29 : Fin 32) = v819 ∧
      reg n' (30 : Fin 32) = v997 ∧
      reg n' (31 : Fin 32) = v481 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      aluEval .sll v1079 0x3 = v1080 ∧
      aluEval .srl v557 0xC = v1081 ∧
      aluEval .sll v540 0x14 = v1084 ∧
      aluEval .add v1084 v481 = v1085 ∧
      aluEval .add v1081 v545 = v1086 ∧
      aluEval .srl v1076 0x1D = v1087 ∧
      aluEval .sltu v1085 v1084 = v1088 ∧
      aluEval .or v1080 v1087 = v1089 ∧
      aluEval .add v1086 v1088 = v1090 ∧
      aluEval .srl v1079 0x1D = v1091 ∧
      aluEval .add v1085 v1089 = v1092 ∧
      aluEval .add v1091 v1090 = v1093 ∧
      aluEval .sltu v1092 v1085 = v1094 ∧
      aluEval .add v1093 v1094 = v1095 ∧
      aluEval .sll v1095 0x3 = v1096 ∧
      aluEval .srl v722 0xC = v1097 ∧
      aluEval .sll v702 0x14 = v1099 ∧
      aluEval .add v1099 v559 = v1100 ∧
      aluEval .add v1097 v572 = v1101 ∧
      aluEval .srl v1092 0x1D = v1104 ∧
      aluEval .sltu v1100 v1099 = v1105 ∧
      aluEval .or v1096 v1104 = v1106 ∧
      aluEval .add v1101 v1105 = v1107 ∧
      aluEval .srl v1095 0x1D = v1108 ∧
      aluEval .add v1100 v1106 = v1109 ∧
      aluEval .add v1108 v1107 = v1110 ∧
      aluEval .sltu v1109 v1100 = v1111 ∧
      aluEval .add v1110 v1111 = v1112 ∧
      aluEval .sll v1112 0x3 = v1113 ∧
      aluEval .srl v819 0xC = v1114 ∧
      aluEval .sll v803 0x14 = v1116 ∧
      aluEval .add v1116 v582 = v1117 ∧
      aluEval .add v1114 v579 = v1118 ∧
      aluEval .srl v1109 0x1D = v1119 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n1080, v1080, d1080, hv1080, u1080⟩ := s.aluImmG hc ev_at_e4e (off' := 0xE52) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1080
  obtain ⟨n1081, v1081, d1081, hv1081, u1081⟩ := u1080.aluImmG hc ev_at_e52 (off' := 0xE56) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1081
  obtain ⟨n1082, d1082, u1082⟩ := u1081.aluImmE hc ev_at_e56 (off' := 0xE58) (by decide) (v := F + 0x100)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rfl)
  obtain ⟨n1083, d1083, u1083⟩ := u1082.lwE hc ev_at_e58 (off' := 0xE5A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [show F + 0x100 + 0x0 = F + 0x100 from by rw [BitVec.add_assoc]; rfl]; exact aligned_add hF (k := 256) (by decide)) (v := v540)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [show F + 0x100 + 0x0 = F + 0x100 from by rw [BitVec.add_assoc]; rfl]; rw [sl100])
  obtain ⟨n1084, v1084, d1084, hv1084, u1084⟩ := u1083.aluImmG hc ev_at_e5a (off' := 0xE5C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1084
  obtain ⟨n1085, v1085, d1085, hv1085, u1085⟩ := u1084.aluG hc ev_at_e5c (off' := 0xE60) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1085
  obtain ⟨n1086, v1086, d1086, hv1086, u1086⟩ := u1085.aluG hc ev_at_e60 (off' := 0xE62) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1086
  obtain ⟨n1087, v1087, d1087, hv1087, u1087⟩ := u1086.aluImmG hc ev_at_e62 (off' := 0xE66) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1087
  obtain ⟨n1088, v1088, d1088, hv1088, u1088⟩ := u1087.aluG hc ev_at_e66 (off' := 0xE6A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1088
  obtain ⟨n1089, v1089, d1089, hv1089, u1089⟩ := u1088.aluG hc ev_at_e6a (off' := 0xE6C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1089
  obtain ⟨n1090, v1090, d1090, hv1090, u1090⟩ := u1089.aluG hc ev_at_e6c (off' := 0xE6E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1090
  obtain ⟨n1091, v1091, d1091, hv1091, u1091⟩ := u1090.aluImmG hc ev_at_e6e (off' := 0xE70) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1091
  obtain ⟨n1092, v1092, d1092, hv1092, u1092⟩ := u1091.aluG hc ev_at_e70 (off' := 0xE74) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1092
  obtain ⟨n1093, v1093, d1093, hv1093, u1093⟩ := u1092.aluG hc ev_at_e74 (off' := 0xE76) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1093
  obtain ⟨n1094, v1094, d1094, hv1094, u1094⟩ := u1093.aluG hc ev_at_e76 (off' := 0xE7A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1094
  obtain ⟨n1095, v1095, d1095, hv1095, u1095⟩ := u1094.aluG hc ev_at_e7a (off' := 0xE7C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1095
  obtain ⟨n1096, v1096, d1096, hv1096, u1096⟩ := u1095.aluImmG hc ev_at_e7c (off' := 0xE80) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1096
  obtain ⟨n1097, v1097, d1097, hv1097, u1097⟩ := u1096.aluImmG hc ev_at_e80 (off' := 0xE84) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1097
  obtain ⟨n1098, d1098, u1098⟩ := u1097.lwE hc ev_at_e84 (off' := 0xE86) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [show F + 0x100 + 0x10 = F + 0x110 from by rw [BitVec.add_assoc]; rfl]; exact aligned_add hF (k := 272) (by decide)) (v := v702)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [show F + 0x100 + 0x10 = F + 0x110 from by rw [BitVec.add_assoc]; rfl]; rw [sl110])
  obtain ⟨n1099, v1099, d1099, hv1099, u1099⟩ := u1098.aluImmG hc ev_at_e86 (off' := 0xE88) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1099
  obtain ⟨n1100, v1100, d1100, hv1100, u1100⟩ := u1099.aluG hc ev_at_e88 (off' := 0xE8C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1100
  obtain ⟨n1101, v1101, d1101, hv1101, u1101⟩ := u1100.aluG hc ev_at_e8c (off' := 0xE8E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1101
  obtain ⟨n1102, d1102, u1102⟩ := u1101.aluImmE hc ev_at_e8e (off' := 0xE92) (by decide) (v := F + 0x7FF)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rfl)
  obtain ⟨n1103, d1103, u1103⟩ := u1102.aluImmE hc ev_at_e92 (off' := 0xE96) (by decide) (v := F + 0x90F)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; show F + 0x7FF + 0x110 = _; rw [BitVec.add_assoc]; rfl)
  obtain ⟨n1104, v1104, d1104, hv1104, u1104⟩ := u1103.aluImmG hc ev_at_e96 (off' := 0xE9A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1104
  obtain ⟨n1105, v1105, d1105, hv1105, u1105⟩ := u1104.aluG hc ev_at_e9a (off' := 0xE9E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1105
  obtain ⟨n1106, v1106, d1106, hv1106, u1106⟩ := u1105.aluG hc ev_at_e9e (off' := 0xEA0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1106
  obtain ⟨n1107, v1107, d1107, hv1107, u1107⟩ := u1106.aluG hc ev_at_ea0 (off' := 0xEA2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1107
  obtain ⟨n1108, v1108, d1108, hv1108, u1108⟩ := u1107.aluImmG hc ev_at_ea2 (off' := 0xEA4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1108
  obtain ⟨n1109, v1109, d1109, hv1109, u1109⟩ := u1108.aluG hc ev_at_ea4 (off' := 0xEA8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1109
  obtain ⟨n1110, v1110, d1110, hv1110, u1110⟩ := u1109.aluG hc ev_at_ea8 (off' := 0xEAA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1110
  obtain ⟨n1111, v1111, d1111, hv1111, u1111⟩ := u1110.aluG hc ev_at_eaa (off' := 0xEAE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1111
  obtain ⟨n1112, v1112, d1112, hv1112, u1112⟩ := u1111.aluG hc ev_at_eae (off' := 0xEB0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1112
  obtain ⟨n1113, v1113, d1113, hv1113, u1113⟩ := u1112.aluImmG hc ev_at_eb0 (off' := 0xEB4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1113
  obtain ⟨n1114, v1114, d1114, hv1114, u1114⟩ := u1113.aluImmG hc ev_at_eb4 (off' := 0xEB8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1114
  obtain ⟨n1115, d1115, u1115⟩ := u1114.lwE hc ev_at_eb8 (off' := 0xEBC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [show F + 0x100 + 0x18 = F + 0x118 from by rw [BitVec.add_assoc]; rfl]; exact aligned_add hF (k := 280) (by decide)) (v := v803)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [show F + 0x100 + 0x18 = F + 0x118 from by rw [BitVec.add_assoc]; rfl]; rw [sl118])
  obtain ⟨n1116, v1116, d1116, hv1116, u1116⟩ := u1115.aluImmG hc ev_at_ebc (off' := 0xEBE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1116
  obtain ⟨n1117, v1117, d1117, hv1117, u1117⟩ := u1116.aluG hc ev_at_ebe (off' := 0xEC2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1117
  obtain ⟨n1118, v1118, d1118, hv1118, u1118⟩ := u1117.aluG hc ev_at_ec2 (off' := 0xEC4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1118
  obtain ⟨n1119, v1119, d1119, hv1119, u1119⟩ := u1118.aluImmG hc ev_at_ec4 (off' := 0xEC8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1119
  have qo1 : reg n1119 ra = v357 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n1119 sp = F := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n1119 (3 : Fin 32) = G3 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n1119 (4 : Fin 32) = G4 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n1119 (5 : Fin 32) = v1060 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n1119 (6 : Fin 32) = v1038 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n1119 (7 : Fin 32) = v991 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n1119 (8 : Fin 32) = v1109 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n1119 (9 : Fin 32) = v1092 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n1119 a0 = v1112 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n1119 a1 = v1119 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n1119 a2 = v1113 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n1119 a3 = v1118 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n1119 a4 = v1117 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n1119 a5 = F + 0x100 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n1119 a6 = v945 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n1119 a7 = v1116 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n1119 (18 : Fin 32) = v7 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n1119 (19 : Fin 32) = F + 0x90F := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n1119 (20 : Fin 32) = v722 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n1119 (21 : Fin 32) = v579 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n1119 (22 : Fin 32) = v557 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n1119 (23 : Fin 32) = v302 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n1119 (24 : Fin 32) = v582 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n1119 (25 : Fin 32) = v559 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n1119 (26 : Fin 32) = v545 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n1119 (27 : Fin 32) = v1014 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n1119 (28 : Fin 32) = v1076 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n1119 (29 : Fin 32) = v819 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n1119 (30 : Fin 32) = v997 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n1119 (31 : Fin 32) = v481 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mi (F + 0xC) = G21 := by
    rw [slC]
  have so10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [sl10]
  have soD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [slD0]
  exact ⟨n1119, Mi, v1080, v1081, v1084, v1085, v1086, v1087, v1088, v1089, v1090, v1091, v1092, v1093, v1094, v1095, v1096, v1097, v1099, v1100, v1101, v1104, v1105, v1106, v1107, v1108, v1109, v1110, v1111, v1112, v1113, v1114, v1116, v1117, v1118, v1119, (.cons d1080 (.cons d1081 (.cons d1082 (.cons d1083 (.cons d1084 (.cons d1085 (.cons d1086 (.cons d1087 (.cons d1088 (.cons d1089 (.cons d1090 (.cons d1091 (.cons d1092 (.cons d1093 (.cons d1094 (.cons d1095 (.cons d1096 (.cons d1097 (.cons d1098 (.cons d1099 (.cons d1100 (.cons d1101 (.cons d1102 (.cons d1103 (.cons d1104 (.cons d1105 (.cons d1106 (.cons d1107 (.cons d1108 (.cons d1109 (.cons d1110 (.cons d1111 (.cons d1112 (.cons d1113 (.cons d1114 (.cons d1115 (.cons d1116 (.cons d1117 (.cons d1118 (.single d1119)))))))))))))))))))))))))))))))))))))))), u1119.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, soD0, hv1080, hv1081, hv1084, hv1085, hv1086, hv1087, hv1088, hv1089, hv1090, hv1091, hv1092, hv1093, hv1094, hv1095, hv1096, hv1097, hv1099, hv1100, hv1101, hv1104, hv1105, hv1106, hv1107, hv1108, hv1109, hv1110, hv1111, hv1112, hv1113, hv1114, hv1116, hv1117, hv1118, hv1119⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g34 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v302 v357 v481 v545 v557 v559 v579 v582 v722 v819 v945 v991 v997 v1014 v1038 v1060 v1076 v1092 v1109 v1112 v1113 v1116 v1117 v1118 v1119 : Word}
    (s : St Mi B n 0xEC8 (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v357)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v1060)
    (q6 : reg n (6 : Fin 32) = v1038)
    (q7 : reg n (7 : Fin 32) = v991)
    (q8 : reg n (8 : Fin 32) = v1109)
    (q9 : reg n (9 : Fin 32) = v1092)
    (q10 : reg n a0 = v1112)
    (q11 : reg n a1 = v1119)
    (q12 : reg n a2 = v1113)
    (q13 : reg n a3 = v1118)
    (q14 : reg n a4 = v1117)
    (q15 : reg n a5 = F + 0x100)
    (q16 : reg n a6 = v945)
    (q17 : reg n a7 = v1116)
    (q18 : reg n (18 : Fin 32) = v7)
    (q19 : reg n (19 : Fin 32) = F + 0x90F)
    (q20 : reg n (20 : Fin 32) = v722)
    (q21 : reg n (21 : Fin 32) = v579)
    (q22 : reg n (22 : Fin 32) = v557)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v582)
    (q25 : reg n (25 : Fin 32) = v559)
    (q26 : reg n (26 : Fin 32) = v545)
    (q27 : reg n (27 : Fin 32) = v1014)
    (q28 : reg n (28 : Fin 32) = v1076)
    (q29 : reg n (29 : Fin 32) = v819)
    (q30 : reg n (30 : Fin 32) = v997)
    (q31 : reg n (31 : Fin 32) = v481)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v1120 v1121 v1122 v1123 v1124 v1125 v1126 v1127 v1128 v1129 v1130 : Word),
      Steps n n' ∧
      St M' B n' 0xEE4 (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v357 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v1060 ∧
      reg n' (6 : Fin 32) = v1038 ∧
      reg n' (7 : Fin 32) = v991 ∧
      reg n' (8 : Fin 32) = v1109 ∧
      reg n' (9 : Fin 32) = v1092 ∧
      reg n' a0 = v1130 ∧
      reg n' a1 = v1124 ∧
      reg n' a2 = v1129 ∧
      reg n' a3 = v1122 ∧
      reg n' a4 = v1117 ∧
      reg n' a5 = v1120 ∧
      reg n' a6 = v945 ∧
      reg n' a7 = v1116 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = F + 0x90F ∧
      reg n' (20 : Fin 32) = v722 ∧
      reg n' (21 : Fin 32) = v579 ∧
      reg n' (22 : Fin 32) = v557 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v582 ∧
      reg n' (25 : Fin 32) = v559 ∧
      reg n' (26 : Fin 32) = v545 ∧
      reg n' (27 : Fin 32) = v1014 ∧
      reg n' (28 : Fin 32) = v1076 ∧
      reg n' (29 : Fin 32) = v819 ∧
      reg n' (30 : Fin 32) = v997 ∧
      reg n' (31 : Fin 32) = v481 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      aluEval .sltu v1117 v1116 = v1120 ∧
      aluEval .or v1119 v1113 = v1121 ∧
      aluEval .add v1118 v1120 = v1122 ∧
      aluEval .srl v1112 0x1D = v1123 ∧
      aluEval .add v1121 v1117 = v1124 ∧
      aluEval .add v1123 v1122 = v1125 ∧
      aluEval .sltu v1124 v1117 = v1126 ∧
      aluEval .add v1125 v1126 = v1127 ∧
      aluEval .sll v1127 0x3 = v1128 ∧
      aluEval .srl v1124 0x1D = v1129 ∧
      aluEval .or v1128 v1129 = v1130 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n1120, v1120, d1120, hv1120, u1120⟩ := s.aluG hc ev_at_ec8 (off' := 0xECC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1120
  obtain ⟨n1121, v1121, d1121, hv1121, u1121⟩ := u1120.aluG hc ev_at_ecc (off' := 0xECE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1121
  obtain ⟨n1122, v1122, d1122, hv1122, u1122⟩ := u1121.aluG hc ev_at_ece (off' := 0xED0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1122
  obtain ⟨n1123, v1123, d1123, hv1123, u1123⟩ := u1122.aluImmG hc ev_at_ed0 (off' := 0xED2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1123
  obtain ⟨n1124, v1124, d1124, hv1124, u1124⟩ := u1123.aluG hc ev_at_ed2 (off' := 0xED4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1124
  obtain ⟨n1125, v1125, d1125, hv1125, u1125⟩ := u1124.aluG hc ev_at_ed4 (off' := 0xED6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1125
  obtain ⟨n1126, v1126, d1126, hv1126, u1126⟩ := u1125.aluG hc ev_at_ed6 (off' := 0xEDA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1126
  obtain ⟨n1127, v1127, d1127, hv1127, u1127⟩ := u1126.aluG hc ev_at_eda (off' := 0xEDC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1127
  obtain ⟨n1128, v1128, d1128, hv1128, u1128⟩ := u1127.aluImmG hc ev_at_edc (off' := 0xEDE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1128
  obtain ⟨n1129, v1129, d1129, hv1129, u1129⟩ := u1128.aluImmG hc ev_at_ede (off' := 0xEE2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1129
  obtain ⟨n1130, v1130, d1130, hv1130, u1130⟩ := u1129.aluG hc ev_at_ee2 (off' := 0xEE4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1130
  have qo1 : reg n1130 ra = v357 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n1130 sp = F := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n1130 (3 : Fin 32) = G3 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n1130 (4 : Fin 32) = G4 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n1130 (5 : Fin 32) = v1060 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n1130 (6 : Fin 32) = v1038 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n1130 (7 : Fin 32) = v991 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n1130 (8 : Fin 32) = v1109 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n1130 (9 : Fin 32) = v1092 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n1130 a0 = v1130 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n1130 a1 = v1124 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n1130 a2 = v1129 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n1130 a3 = v1122 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n1130 a4 = v1117 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n1130 a5 = v1120 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n1130 a6 = v945 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n1130 a7 = v1116 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n1130 (18 : Fin 32) = v7 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n1130 (19 : Fin 32) = F + 0x90F := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n1130 (20 : Fin 32) = v722 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n1130 (21 : Fin 32) = v579 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n1130 (22 : Fin 32) = v557 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n1130 (23 : Fin 32) = v302 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n1130 (24 : Fin 32) = v582 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n1130 (25 : Fin 32) = v559 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n1130 (26 : Fin 32) = v545 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n1130 (27 : Fin 32) = v1014 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n1130 (28 : Fin 32) = v1076 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n1130 (29 : Fin 32) = v819 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n1130 (30 : Fin 32) = v997 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n1130 (31 : Fin 32) = v481 := by rw [u1130.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mi (F + 0xC) = G21 := by
    rw [slC]
  have so10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [sl10]
  have soD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [slD0]
  exact ⟨n1130, Mi, v1120, v1121, v1122, v1123, v1124, v1125, v1126, v1127, v1128, v1129, v1130, (.cons d1120 (.cons d1121 (.cons d1122 (.cons d1123 (.cons d1124 (.cons d1125 (.cons d1126 (.cons d1127 (.cons d1128 (.cons d1129 (.single d1130))))))))))), u1130.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, soD0, hv1120, hv1121, hv1122, hv1123, hv1124, hv1125, hv1126, hv1127, hv1128, hv1129, hv1130⟩

end C3.RV32
