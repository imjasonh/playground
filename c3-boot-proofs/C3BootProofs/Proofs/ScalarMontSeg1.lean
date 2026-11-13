import C3BootProofs.Proofs.ScalarMontFacts

/-! # `montgomery_mul`'s body, segments 3 to 5

Each theorem steps 40 instructions. `scripts/gen-scalar-mont.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem smm_g3 {M0 Mi : Word → BitVec 8} {B F outp xp yp G3 G4 : Word} {n : Machine} {v3 v4 v5 v6 v7 v8 v9 v10 v21 v28 v36 v52 v55 v60 v65 v66 v67 v73 v77 v78 v81 v82 v83 v90 v95 v104 v105 v106 v107 v109 v114 v115 v117 v118 v119 : Word}
    (s : St Mi B n 0x1B2 (reg n)) (hc : CodeIn Mi B scalar29MontMulCode)
    (fr : ∀ x, Sep F 0x190 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190)
    (q1 : reg n ra = v117)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v9)
    (q6 : reg n (6 : Fin 32) = v66)
    (q7 : reg n (7 : Fin 32) = v60)
    (q8 : reg n (8 : Fin 32) = v118)
    (q9 : reg n (9 : Fin 32) = v73)
    (q10 : reg n a0 = v109)
    (q11 : reg n a1 = v106)
    (q12 : reg n a2 = v73)
    (q13 : reg n a3 = v6)
    (q14 : reg n a4 = v78)
    (q15 : reg n a5 = v77)
    (q16 : reg n a6 = v81)
    (q17 : reg n a7 = v65)
    (q18 : reg n (18 : Fin 32) = v95)
    (q19 : reg n (19 : Fin 32) = yp)
    (q20 : reg n (20 : Fin 32) = v7)
    (q21 : reg n (21 : Fin 32) = v10)
    (q22 : reg n (22 : Fin 32) = v114)
    (q23 : reg n (23 : Fin 32) = v115)
    (q24 : reg n (24 : Fin 32) = v104)
    (q25 : reg n (25 : Fin 32) = xp)
    (q26 : reg n (26 : Fin 32) = v105)
    (q27 : reg n (27 : Fin 32) = v107)
    (q28 : reg n (28 : Fin 32) = v8)
    (q29 : reg n (29 : Fin 32) = v82)
    (q30 : reg n (30 : Fin 32) = v6)
    (q31 : reg n (31 : Fin 32) = v119)
    (sl84 : memLoad32 Mi (F + 0x84) = v83)
    (sl88 : memLoad32 Mi (F + 0x88) = v67)
    (slE0 : memLoad32 Mi (F + 0xE0) = v5)
    (slEC : memLoad32 Mi (F + 0xEC) = v3)
    (slF8 : memLoad32 Mi (F + 0xF8) = outp)
    (sl100 : memLoad32 Mi (F + 0x100) = v4)
    (sl108 : memLoad32 Mi (F + 0x108) = v55)
    (sl10C : memLoad32 Mi (F + 0x10C) = v21)
    (sl110 : memLoad32 Mi (F + 0x110) = v28)
    (sl114 : memLoad32 Mi (F + 0x114) = v90)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v120 v121 v122 v124 v125 v126 v127 v128 v129 v130 v132 v133 v134 v135 v137 v138 v139 v141 v143 v144 v145 v146 v147 v149 v150 v151 v152 v153 v154 v156 v157 v158 v159 : Word),
      Steps n n' ∧
      St M' B n' 0x236 (reg n') ∧
      CodeIn M' B scalar29MontMulCode ∧
      (∀ x, Sep F 0x190 x 1 → M' x = M0 x) ∧
      reg n' ra = v117 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v67 ∧
      reg n' (6 : Fin 32) = v66 ∧
      reg n' (7 : Fin 32) = v60 ∧
      reg n' (8 : Fin 32) = v156 ∧
      reg n' (9 : Fin 32) = v73 ∧
      reg n' a0 = v158 ∧
      reg n' a1 = v146 ∧
      reg n' a2 = v157 ∧
      reg n' a3 = v159 ∧
      reg n' a4 = v154 ∧
      reg n' a5 = v151 ∧
      reg n' a6 = v81 ∧
      reg n' a7 = v65 ∧
      reg n' (18 : Fin 32) = v143 ∧
      reg n' (19 : Fin 32) = yp ∧
      reg n' (20 : Fin 32) = v7 ∧
      reg n' (21 : Fin 32) = v10 ∧
      reg n' (22 : Fin 32) = v149 ∧
      reg n' (23 : Fin 32) = v130 ∧
      reg n' (24 : Fin 32) = v139 ∧
      reg n' (25 : Fin 32) = xp ∧
      reg n' (26 : Fin 32) = v126 ∧
      reg n' (27 : Fin 32) = v133 ∧
      reg n' (28 : Fin 32) = v8 ∧
      reg n' (29 : Fin 32) = v82 ∧
      reg n' (30 : Fin 32) = v6 ∧
      reg n' (31 : Fin 32) = v125 ∧
      memLoad32 M' (F + 0x84) = v83 ∧
      memLoad32 M' (F + 0xAC) = v9 ∧
      memLoad32 M' (F + 0xE0) = v5 ∧
      memLoad32 M' (F + 0xE8) = v7 ∧
      memLoad32 M' (F + 0xEC) = v3 ∧
      memLoad32 M' (F + 0xF8) = outp ∧
      memLoad32 M' (F + 0x100) = v4 ∧
      memLoad32 M' (F + 0x104) = v122 ∧
      memLoad32 M' (F + 0x108) = v55 ∧
      memLoad32 M' (F + 0x10C) = v21 ∧
      memLoad32 M' (F + 0x110) = v28 ∧
      memLoad32 M' (F + 0x114) = v90 ∧
      memLoad32 M' (F + 0x118) = v52 ∧
      memLoad32 M' (F + 0x11C) = v36 ∧
      memLoad32 M' (F + 0x120) = v139 ∧
      memLoad32 M' (F + 0x124) = v141 ∧
      memLoad32 M' (F + 0x134) = v147 ∧
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
      aluEval .add v106 v118 = v120 ∧
      aluEval .sub v119 v107 = v121 ∧
      aluEval .add v109 v95 = v122 ∧
      aluEval .mul v65 v81 = v124 ∧
      aluEval .add v120 v121 = v125 ∧
      aluEval .sltu v122 v95 = v126 ∧
      aluEval .mul v66 v81 = v127 ∧
      aluEval .mul v82 v65 = v128 ∧
      aluEval .mulhu v66 v81 = v129 ∧
      aluEval .mulhu v82 v65 = v130 ∧
      aluEval .mul v60 v9 = v132 ∧
      aluEval .mulhu v60 v9 = v133 ∧
      aluEval .mul v10 v8 = v134 ∧
      aluEval .mulhu v10 v8 = v135 ∧
      aluEval .mulhu v73 v7 = v137 ∧
      aluEval .sltu v117 v124 = v138 ∧
      aluEval .add v104 v126 = v139 ∧
      aluEval .sub v125 v138 = v141 ∧
      aluEval .add v127 v128 = v143 ∧
      aluEval .mul v73 v7 = v144 ∧
      aluEval .add v129 v130 = v145 ∧
      aluEval .sltu v143 v128 = v146 ∧
      aluEval .sub v117 v124 = v147 ∧
      aluEval .add v145 v146 = v149 ∧
      aluEval .add v135 v133 = v150 ∧
      aluEval .add v134 v132 = v151 ∧
      aluEval .add v150 v137 = v152 ∧
      aluEval .sltu v151 v132 = v153 ∧
      aluEval .mulhu v82 v66 = v154 ∧
      aluEval .mulhu v67 v81 = v156 ∧
      aluEval .add v153 v152 = v157 ∧
      aluEval .add v144 v151 = v158 ∧
      aluEval .sltu v158 v151 = v159 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n120, v120, d120, hv120, u120⟩ := s.aluG hc smm_at_1b2 (off' := 0x1B4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv120
  obtain ⟨n121, v121, d121, hv121, u121⟩ := u120.aluG hc smm_at_1b4 (off' := 0x1B8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv121
  obtain ⟨n122, v122, d122, hv122, u122⟩ := u121.aluG hc smm_at_1b8 (off' := 0x1BA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv122
  obtain ⟨n123, d123, u123⟩ := u122.swG hc smm_at_1ba (off' := 0x1BE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 260) (by decide)) (a := F + 0x104) (v := v122)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M123, hM123⟩ : ∃ M', memStore32 Mi (F + 0x104) v122 = M' := ⟨_, rfl⟩
  rw [hM123] at u123
  have hc123 : CodeIn M123 B scalar29MontMulCode := by rw [← hM123]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr123 : ∀ x, Sep F 0x190 x 1 → M123 x = M0 x := fun x hx => by
    rw [← hM123, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n124, v124, d124, hv124, u124⟩ := u123.aluG hc123 smm_at_1be (off' := 0x1C2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv124
  obtain ⟨n125, v125, d125, hv125, u125⟩ := u124.aluG hc123 smm_at_1c2 (off' := 0x1C6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv125
  obtain ⟨n126, v126, d126, hv126, u126⟩ := u125.aluG hc123 smm_at_1c6 (off' := 0x1CA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv126
  obtain ⟨n127, v127, d127, hv127, u127⟩ := u126.aluG hc123 smm_at_1ca (off' := 0x1CE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv127
  obtain ⟨n128, v128, d128, hv128, u128⟩ := u127.aluG hc123 smm_at_1ce (off' := 0x1D2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv128
  obtain ⟨n129, v129, d129, hv129, u129⟩ := u128.aluG hc123 smm_at_1d2 (off' := 0x1D6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv129
  obtain ⟨n130, v130, d130, hv130, u130⟩ := u129.aluG hc123 smm_at_1d6 (off' := 0x1DA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv130
  obtain ⟨n131, d131, u131⟩ := u130.swG hc123 smm_at_1da (off' := 0x1DC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 172) (by decide)) (a := F + 0xAC) (v := v9)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M131, hM131⟩ : ∃ M', memStore32 M123 (F + 0xAC) v9 = M' := ⟨_, rfl⟩
  rw [hM131] at u131
  have hc131 : CodeIn M131 B scalar29MontMulCode := by rw [← hM131]; exact hc123.store32 (frm_sep' sFC (by decide))
  have fr131 : ∀ x, Sep F 0x190 x 1 → M131 x = M0 x := fun x hx => by
    rw [← hM131, memStore32_get_sep (frm_sep' hx (by decide)), fr123 x hx]
  obtain ⟨n132, v132, d132, hv132, u132⟩ := u131.aluG hc131 smm_at_1dc (off' := 0x1E0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv132
  obtain ⟨n133, v133, d133, hv133, u133⟩ := u132.aluG hc131 smm_at_1e0 (off' := 0x1E4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv133
  obtain ⟨n134, v134, d134, hv134, u134⟩ := u133.aluG hc131 smm_at_1e4 (off' := 0x1E8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv134
  obtain ⟨n135, v135, d135, hv135, u135⟩ := u134.aluG hc131 smm_at_1e8 (off' := 0x1EC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv135
  obtain ⟨n136, d136, u136⟩ := u135.swG hc131 smm_at_1ec (off' := 0x1EE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 232) (by decide)) (a := F + 0xE8) (v := v7)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M136, hM136⟩ : ∃ M', memStore32 M131 (F + 0xE8) v7 = M' := ⟨_, rfl⟩
  rw [hM136] at u136
  have hc136 : CodeIn M136 B scalar29MontMulCode := by rw [← hM136]; exact hc131.store32 (frm_sep' sFC (by decide))
  have fr136 : ∀ x, Sep F 0x190 x 1 → M136 x = M0 x := fun x hx => by
    rw [← hM136, memStore32_get_sep (frm_sep' hx (by decide)), fr131 x hx]
  obtain ⟨n137, v137, d137, hv137, u137⟩ := u136.aluG hc136 smm_at_1ee (off' := 0x1F2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv137
  obtain ⟨n138, v138, d138, hv138, u138⟩ := u137.aluG hc136 smm_at_1f2 (off' := 0x1F6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv138
  obtain ⟨n139, v139, d139, hv139, u139⟩ := u138.aluG hc136 smm_at_1f6 (off' := 0x1F8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv139
  obtain ⟨n140, d140, u140⟩ := u139.swG hc136 smm_at_1f8 (off' := 0x1FC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 288) (by decide)) (a := F + 0x120) (v := v139)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M140, hM140⟩ : ∃ M', memStore32 M136 (F + 0x120) v139 = M' := ⟨_, rfl⟩
  rw [hM140] at u140
  have hc140 : CodeIn M140 B scalar29MontMulCode := by rw [← hM140]; exact hc136.store32 (frm_sep' sFC (by decide))
  have fr140 : ∀ x, Sep F 0x190 x 1 → M140 x = M0 x := fun x hx => by
    rw [← hM140, memStore32_get_sep (frm_sep' hx (by decide)), fr136 x hx]
  obtain ⟨n141, v141, d141, hv141, u141⟩ := u140.aluG hc140 smm_at_1fc (off' := 0x200) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv141
  obtain ⟨n142, d142, u142⟩ := u141.swG hc140 smm_at_200 (off' := 0x204) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 292) (by decide)) (a := F + 0x124) (v := v141)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M142, hM142⟩ : ∃ M', memStore32 M140 (F + 0x124) v141 = M' := ⟨_, rfl⟩
  rw [hM142] at u142
  have hc142 : CodeIn M142 B scalar29MontMulCode := by rw [← hM142]; exact hc140.store32 (frm_sep' sFC (by decide))
  have fr142 : ∀ x, Sep F 0x190 x 1 → M142 x = M0 x := fun x hx => by
    rw [← hM142, memStore32_get_sep (frm_sep' hx (by decide)), fr140 x hx]
  obtain ⟨n143, v143, d143, hv143, u143⟩ := u142.aluG hc142 smm_at_204 (off' := 0x206) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv143
  obtain ⟨n144, v144, d144, hv144, u144⟩ := u143.aluG hc142 smm_at_206 (off' := 0x20A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv144
  obtain ⟨n145, v145, d145, hv145, u145⟩ := u144.aluG hc142 smm_at_20a (off' := 0x20C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv145
  obtain ⟨n146, v146, d146, hv146, u146⟩ := u145.aluG hc142 smm_at_20c (off' := 0x210) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv146
  obtain ⟨n147, v147, d147, hv147, u147⟩ := u146.aluG hc142 smm_at_210 (off' := 0x214) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv147
  obtain ⟨n148, d148, u148⟩ := u147.swG hc142 smm_at_214 (off' := 0x218) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 308) (by decide)) (a := F + 0x134) (v := v147)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M148, hM148⟩ : ∃ M', memStore32 M142 (F + 0x134) v147 = M' := ⟨_, rfl⟩
  rw [hM148] at u148
  have hc148 : CodeIn M148 B scalar29MontMulCode := by rw [← hM148]; exact hc142.store32 (frm_sep' sFC (by decide))
  have fr148 : ∀ x, Sep F 0x190 x 1 → M148 x = M0 x := fun x hx => by
    rw [← hM148, memStore32_get_sep (frm_sep' hx (by decide)), fr142 x hx]
  obtain ⟨n149, v149, d149, hv149, u149⟩ := u148.aluG hc148 smm_at_218 (off' := 0x21A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv149
  obtain ⟨n150, v150, d150, hv150, u150⟩ := u149.aluG hc148 smm_at_21a (off' := 0x21C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv150
  obtain ⟨n151, v151, d151, hv151, u151⟩ := u150.aluG hc148 smm_at_21c (off' := 0x21E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv151
  obtain ⟨n152, v152, d152, hv152, u152⟩ := u151.aluG hc148 smm_at_21e (off' := 0x220) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv152
  obtain ⟨n153, v153, d153, hv153, u153⟩ := u152.aluG hc148 smm_at_220 (off' := 0x224) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv153
  obtain ⟨n154, v154, d154, hv154, u154⟩ := u153.aluG hc148 smm_at_224 (off' := 0x228) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv154
  obtain ⟨n155, d155, u155⟩ := u154.lwE hc148 smm_at_228 (off' := 0x22A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 136) (by decide)) (v := v67)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x88) 4 from sep_offsets F (c := 308) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x88) 4 from sep_offsets F (c := 292) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x88) 4 from sep_offsets F (c := 288) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x88) 4 from sep_offsets F (c := 232) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x88) 4 from sep_offsets F (c := 172) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x88) 4 from sep_offsets F (c := 260) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88])
  obtain ⟨n156, v156, d156, hv156, u156⟩ := u155.aluG hc148 smm_at_22a (off' := 0x22E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv156
  obtain ⟨n157, v157, d157, hv157, u157⟩ := u156.aluG hc148 smm_at_22e (off' := 0x230) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv157
  obtain ⟨n158, v158, d158, hv158, u158⟩ := u157.aluG hc148 smm_at_230 (off' := 0x232) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv158
  obtain ⟨n159, v159, d159, hv159, u159⟩ := u158.aluG hc148 smm_at_232 (off' := 0x236) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv159
  have qo1 : reg n159 ra = v117 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n159 sp = F := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n159 (3 : Fin 32) = G3 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n159 (4 : Fin 32) = G4 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n159 (5 : Fin 32) = v67 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n159 (6 : Fin 32) = v66 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n159 (7 : Fin 32) = v60 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n159 (8 : Fin 32) = v156 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n159 (9 : Fin 32) = v73 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n159 a0 = v158 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n159 a1 = v146 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n159 a2 = v157 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n159 a3 = v159 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n159 a4 = v154 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n159 a5 = v151 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n159 a6 = v81 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n159 a7 = v65 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n159 (18 : Fin 32) = v143 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n159 (19 : Fin 32) = yp := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n159 (20 : Fin 32) = v7 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n159 (21 : Fin 32) = v10 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n159 (22 : Fin 32) = v149 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n159 (23 : Fin 32) = v130 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n159 (24 : Fin 32) = v139 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n159 (25 : Fin 32) = xp := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n159 (26 : Fin 32) = v126 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n159 (27 : Fin 32) = v133 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n159 (28 : Fin 32) = v8 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n159 (29 : Fin 32) = v82 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n159 (30 : Fin 32) = v6 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n159 (31 : Fin 32) = v125 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so84 : memLoad32 M148 (F + 0x84) = v83 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x84) 4 from sep_offsets F (c := 308) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x84) 4 from sep_offsets F (c := 292) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x84) 4 from sep_offsets F (c := 288) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x84) 4 from sep_offsets F (c := 232) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x84) 4 from sep_offsets F (c := 172) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x84) 4 from sep_offsets F (c := 260) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), sl84]
  have soAC : memLoad32 M148 (F + 0xAC) = v9 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0xAC) 4 from sep_offsets F (c := 308) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0xAC) 4 from sep_offsets F (c := 292) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0xAC) 4 from sep_offsets F (c := 288) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xAC) 4 from sep_offsets F (c := 232) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_same]
  have soE0 : memLoad32 M148 (F + 0xE0) = v5 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0xE0) 4 from sep_offsets F (c := 308) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0xE0) 4 from sep_offsets F (c := 292) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0xE0) 4 from sep_offsets F (c := 288) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xE0) 4 from sep_offsets F (c := 232) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0xE0) 4 from sep_offsets F (c := 172) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0xE0) 4 from sep_offsets F (c := 260) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), slE0]
  have soE8 : memLoad32 M148 (F + 0xE8) = v7 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0xE8) 4 from sep_offsets F (c := 308) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0xE8) 4 from sep_offsets F (c := 292) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0xE8) 4 from sep_offsets F (c := 288) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_same]
  have soEC : memLoad32 M148 (F + 0xEC) = v3 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0xEC) 4 from sep_offsets F (c := 308) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0xEC) 4 from sep_offsets F (c := 292) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0xEC) 4 from sep_offsets F (c := 288) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xEC) 4 from sep_offsets F (c := 232) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0xEC) 4 from sep_offsets F (c := 172) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0xEC) 4 from sep_offsets F (c := 260) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soF8 : memLoad32 M148 (F + 0xF8) = outp := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0xF8) 4 from sep_offsets F (c := 308) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0xF8) 4 from sep_offsets F (c := 292) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0xF8) 4 from sep_offsets F (c := 288) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xF8) 4 from sep_offsets F (c := 232) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0xF8) 4 from sep_offsets F (c := 172) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0xF8) 4 from sep_offsets F (c := 260) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), slF8]
  have so100 : memLoad32 M148 (F + 0x100) = v4 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x100) 4 from sep_offsets F (c := 308) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x100) 4 from sep_offsets F (c := 292) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x100) 4 from sep_offsets F (c := 288) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x100) 4 from sep_offsets F (c := 232) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x100) 4 from sep_offsets F (c := 172) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x100) 4 from sep_offsets F (c := 260) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100]
  have so104 : memLoad32 M148 (F + 0x104) = v122 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x104) 4 from sep_offsets F (c := 308) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x104) 4 from sep_offsets F (c := 292) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x104) 4 from sep_offsets F (c := 288) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x104) 4 from sep_offsets F (c := 232) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x104) 4 from sep_offsets F (c := 172) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_same]
  have so108 : memLoad32 M148 (F + 0x108) = v55 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x108) 4 from sep_offsets F (c := 308) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x108) 4 from sep_offsets F (c := 292) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x108) 4 from sep_offsets F (c := 288) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x108) 4 from sep_offsets F (c := 232) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x108) 4 from sep_offsets F (c := 172) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x108) 4 from sep_offsets F (c := 260) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), sl108]
  have so10C : memLoad32 M148 (F + 0x10C) = v21 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x10C) 4 from sep_offsets F (c := 308) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x10C) 4 from sep_offsets F (c := 292) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x10C) 4 from sep_offsets F (c := 288) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x10C) 4 from sep_offsets F (c := 232) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x10C) 4 from sep_offsets F (c := 172) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x10C) 4 from sep_offsets F (c := 260) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so110 : memLoad32 M148 (F + 0x110) = v28 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x110) 4 from sep_offsets F (c := 308) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x110) 4 from sep_offsets F (c := 292) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x110) 4 from sep_offsets F (c := 288) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x110) 4 from sep_offsets F (c := 232) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x110) 4 from sep_offsets F (c := 172) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x110) 4 from sep_offsets F (c := 260) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so114 : memLoad32 M148 (F + 0x114) = v90 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x114) 4 from sep_offsets F (c := 308) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x114) 4 from sep_offsets F (c := 292) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x114) 4 from sep_offsets F (c := 288) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x114) 4 from sep_offsets F (c := 232) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x114) 4 from sep_offsets F (c := 172) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x114) 4 from sep_offsets F (c := 260) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), sl114]
  have so118 : memLoad32 M148 (F + 0x118) = v52 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x118) 4 from sep_offsets F (c := 308) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x118) 4 from sep_offsets F (c := 292) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x118) 4 from sep_offsets F (c := 288) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x118) 4 from sep_offsets F (c := 232) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x118) 4 from sep_offsets F (c := 172) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x118) 4 from sep_offsets F (c := 260) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), sl118]
  have so11C : memLoad32 M148 (F + 0x11C) = v36 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x11C) 4 from sep_offsets F (c := 308) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x11C) 4 from sep_offsets F (c := 292) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x11C) 4 from sep_offsets F (c := 288) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x11C) 4 from sep_offsets F (c := 232) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x11C) 4 from sep_offsets F (c := 172) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x11C) 4 from sep_offsets F (c := 260) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), sl11C]
  have so120 : memLoad32 M148 (F + 0x120) = v139 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x120) 4 from sep_offsets F (c := 308) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x120) 4 from sep_offsets F (c := 292) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_same]
  have so124 : memLoad32 M148 (F + 0x124) = v141 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x124) 4 from sep_offsets F (c := 308) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_same]
  have so134 : memLoad32 M148 (F + 0x134) = v147 := by
    rw [← hM148, memLoad32_store32_same]
  have so15C : memLoad32 M148 (F + 0x15C) = memLoad32 M0 (F + 0x15C) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x15C) 4 from sep_offsets F (c := 308) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x15C) 4 from sep_offsets F (c := 292) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x15C) 4 from sep_offsets F (c := 288) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x15C) 4 from sep_offsets F (c := 232) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x15C) 4 from sep_offsets F (c := 172) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x15C) 4 from sep_offsets F (c := 260) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), sl15C]
  have so160 : memLoad32 M148 (F + 0x160) = memLoad32 M0 (F + 0x160) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x160) 4 from sep_offsets F (c := 308) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x160) 4 from sep_offsets F (c := 292) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x160) 4 from sep_offsets F (c := 288) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x160) 4 from sep_offsets F (c := 232) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x160) 4 from sep_offsets F (c := 172) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x160) 4 from sep_offsets F (c := 260) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), sl160]
  have so164 : memLoad32 M148 (F + 0x164) = memLoad32 M0 (F + 0x164) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x164) 4 from sep_offsets F (c := 308) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x164) 4 from sep_offsets F (c := 292) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x164) 4 from sep_offsets F (c := 288) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x164) 4 from sep_offsets F (c := 232) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x164) 4 from sep_offsets F (c := 172) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x164) 4 from sep_offsets F (c := 260) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), sl164]
  have so168 : memLoad32 M148 (F + 0x168) = memLoad32 M0 (F + 0x168) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x168) 4 from sep_offsets F (c := 308) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x168) 4 from sep_offsets F (c := 292) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x168) 4 from sep_offsets F (c := 288) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x168) 4 from sep_offsets F (c := 232) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x168) 4 from sep_offsets F (c := 172) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x168) 4 from sep_offsets F (c := 260) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), sl168]
  have so16C : memLoad32 M148 (F + 0x16C) = memLoad32 M0 (F + 0x16C) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x16C) 4 from sep_offsets F (c := 308) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x16C) 4 from sep_offsets F (c := 292) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x16C) 4 from sep_offsets F (c := 288) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x16C) 4 from sep_offsets F (c := 232) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x16C) 4 from sep_offsets F (c := 172) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x16C) 4 from sep_offsets F (c := 260) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), sl16C]
  have so170 : memLoad32 M148 (F + 0x170) = memLoad32 M0 (F + 0x170) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x170) 4 from sep_offsets F (c := 308) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x170) 4 from sep_offsets F (c := 292) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x170) 4 from sep_offsets F (c := 288) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x170) 4 from sep_offsets F (c := 232) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x170) 4 from sep_offsets F (c := 172) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x170) 4 from sep_offsets F (c := 260) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), sl170]
  have so174 : memLoad32 M148 (F + 0x174) = memLoad32 M0 (F + 0x174) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x174) 4 from sep_offsets F (c := 308) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x174) 4 from sep_offsets F (c := 292) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x174) 4 from sep_offsets F (c := 288) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x174) 4 from sep_offsets F (c := 232) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x174) 4 from sep_offsets F (c := 172) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x174) 4 from sep_offsets F (c := 260) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), sl174]
  have so178 : memLoad32 M148 (F + 0x178) = memLoad32 M0 (F + 0x178) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x178) 4 from sep_offsets F (c := 308) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x178) 4 from sep_offsets F (c := 292) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x178) 4 from sep_offsets F (c := 288) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x178) 4 from sep_offsets F (c := 232) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x178) 4 from sep_offsets F (c := 172) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x178) 4 from sep_offsets F (c := 260) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), sl178]
  have so17C : memLoad32 M148 (F + 0x17C) = memLoad32 M0 (F + 0x17C) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x17C) 4 from sep_offsets F (c := 308) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x17C) 4 from sep_offsets F (c := 292) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x17C) 4 from sep_offsets F (c := 288) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x17C) 4 from sep_offsets F (c := 232) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x17C) 4 from sep_offsets F (c := 172) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x17C) 4 from sep_offsets F (c := 260) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), sl17C]
  have so180 : memLoad32 M148 (F + 0x180) = memLoad32 M0 (F + 0x180) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x180) 4 from sep_offsets F (c := 308) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x180) 4 from sep_offsets F (c := 292) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x180) 4 from sep_offsets F (c := 288) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x180) 4 from sep_offsets F (c := 232) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x180) 4 from sep_offsets F (c := 172) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x180) 4 from sep_offsets F (c := 260) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), sl180]
  have so184 : memLoad32 M148 (F + 0x184) = memLoad32 M0 (F + 0x184) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x184) 4 from sep_offsets F (c := 308) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x184) 4 from sep_offsets F (c := 292) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x184) 4 from sep_offsets F (c := 288) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x184) 4 from sep_offsets F (c := 232) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x184) 4 from sep_offsets F (c := 172) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x184) 4 from sep_offsets F (c := 260) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), sl184]
  have so188 : memLoad32 M148 (F + 0x188) = memLoad32 M0 (F + 0x188) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x188) 4 from sep_offsets F (c := 308) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x188) 4 from sep_offsets F (c := 292) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x188) 4 from sep_offsets F (c := 288) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x188) 4 from sep_offsets F (c := 232) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x188) 4 from sep_offsets F (c := 172) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x188) 4 from sep_offsets F (c := 260) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), sl188]
  have so18C : memLoad32 M148 (F + 0x18C) = memLoad32 M0 (F + 0x18C) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x18C) 4 from sep_offsets F (c := 308) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM142, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x18C) 4 from sep_offsets F (c := 292) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM140, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x18C) 4 from sep_offsets F (c := 288) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM136, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x18C) 4 from sep_offsets F (c := 232) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM131, memLoad32_store32_sep (show Sep (F + 0xAC) 4 (F + 0x18C) 4 from sep_offsets F (c := 172) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x18C) 4 from sep_offsets F (c := 260) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), sl18C]
  exact ⟨n159, M148, v120, v121, v122, v124, v125, v126, v127, v128, v129, v130, v132, v133, v134, v135, v137, v138, v139, v141, v143, v144, v145, v146, v147, v149, v150, v151, v152, v153, v154, v156, v157, v158, v159, (.cons d120 (.cons d121 (.cons d122 (.cons d123 (.cons d124 (.cons d125 (.cons d126 (.cons d127 (.cons d128 (.cons d129 (.cons d130 (.cons d131 (.cons d132 (.cons d133 (.cons d134 (.cons d135 (.cons d136 (.cons d137 (.cons d138 (.cons d139 (.cons d140 (.cons d141 (.cons d142 (.cons d143 (.cons d144 (.cons d145 (.cons d146 (.cons d147 (.cons d148 (.cons d149 (.cons d150 (.cons d151 (.cons d152 (.cons d153 (.cons d154 (.cons d155 (.cons d156 (.cons d157 (.cons d158 (.single d159)))))))))))))))))))))))))))))))))))))))), u159.self, hc148, fr148, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so84, soAC, soE0, soE8, soEC, soF8, so100, so104, so108, so10C, so110, so114, so118, so11C, so120, so124, so134, so15C, so160, so164, so168, so16C, so170, so174, so178, so17C, so180, so184, so188, so18C, hv120, hv121, hv122, hv124, hv125, hv126, hv127, hv128, hv129, hv130, hv132, hv133, hv134, hv135, hv137, hv138, hv139, hv141, hv143, hv144, hv145, hv146, hv147, hv149, hv150, hv151, hv152, hv153, hv154, hv156, hv157, hv158, hv159⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem smm_g4 {M0 Mi : Word → BitVec 8} {B F outp xp yp G3 G4 : Word} {n : Machine} {v3 v4 v5 v6 v7 v8 v9 v10 v21 v28 v36 v52 v55 v60 v65 v66 v67 v73 v81 v82 v83 v90 v117 v122 v125 v126 v130 v133 v139 v141 v143 v146 v147 v149 v151 v154 v156 v157 v158 v159 : Word}
    (s : St Mi B n 0x236 (reg n)) (hc : CodeIn Mi B scalar29MontMulCode)
    (fr : ∀ x, Sep F 0x190 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190)
    (q1 : reg n ra = v117)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v67)
    (q6 : reg n (6 : Fin 32) = v66)
    (q7 : reg n (7 : Fin 32) = v60)
    (q8 : reg n (8 : Fin 32) = v156)
    (q9 : reg n (9 : Fin 32) = v73)
    (q10 : reg n a0 = v158)
    (q11 : reg n a1 = v146)
    (q12 : reg n a2 = v157)
    (q13 : reg n a3 = v159)
    (q14 : reg n a4 = v154)
    (q15 : reg n a5 = v151)
    (q16 : reg n a6 = v81)
    (q17 : reg n a7 = v65)
    (q18 : reg n (18 : Fin 32) = v143)
    (q19 : reg n (19 : Fin 32) = yp)
    (q20 : reg n (20 : Fin 32) = v7)
    (q21 : reg n (21 : Fin 32) = v10)
    (q22 : reg n (22 : Fin 32) = v149)
    (q23 : reg n (23 : Fin 32) = v130)
    (q24 : reg n (24 : Fin 32) = v139)
    (q25 : reg n (25 : Fin 32) = xp)
    (q26 : reg n (26 : Fin 32) = v126)
    (q27 : reg n (27 : Fin 32) = v133)
    (q28 : reg n (28 : Fin 32) = v8)
    (q29 : reg n (29 : Fin 32) = v82)
    (q30 : reg n (30 : Fin 32) = v6)
    (q31 : reg n (31 : Fin 32) = v125)
    (sl84 : memLoad32 Mi (F + 0x84) = v83)
    (slAC : memLoad32 Mi (F + 0xAC) = v9)
    (slE0 : memLoad32 Mi (F + 0xE0) = v5)
    (slE8 : memLoad32 Mi (F + 0xE8) = v7)
    (slEC : memLoad32 Mi (F + 0xEC) = v3)
    (slF8 : memLoad32 Mi (F + 0xF8) = outp)
    (sl100 : memLoad32 Mi (F + 0x100) = v4)
    (sl104 : memLoad32 Mi (F + 0x104) = v122)
    (sl108 : memLoad32 Mi (F + 0x108) = v55)
    (sl10C : memLoad32 Mi (F + 0x10C) = v21)
    (sl110 : memLoad32 Mi (F + 0x110) = v28)
    (sl114 : memLoad32 Mi (F + 0x114) = v90)
    (sl118 : memLoad32 Mi (F + 0x118) = v52)
    (sl11C : memLoad32 Mi (F + 0x11C) = v36)
    (sl120 : memLoad32 Mi (F + 0x120) = v139)
    (sl124 : memLoad32 Mi (F + 0x124) = v141)
    (sl134 : memLoad32 Mi (F + 0x134) = v147)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v160 v161 v163 v164 v165 v167 v168 v169 v171 v174 v177 v178 v179 v180 v181 v182 v183 v184 v185 v186 v188 v189 v190 v191 v193 : Word),
      Steps n n' ∧
      St M' B n' 0x2A2 (reg n') ∧
      CodeIn M' B scalar29MontMulCode ∧
      (∀ x, Sep F 0x190 x 1 → M' x = M0 x) ∧
      reg n' ra = v83 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v67 ∧
      reg n' (6 : Fin 32) = v66 ∧
      reg n' (7 : Fin 32) = v60 ∧
      reg n' (8 : Fin 32) = v178 ∧
      reg n' (9 : Fin 32) = v193 ∧
      reg n' a0 = v186 ∧
      reg n' a1 = v188 ∧
      reg n' a2 = v174 ∧
      reg n' a3 = v189 ∧
      reg n' a4 = v185 ∧
      reg n' a5 = v179 ∧
      reg n' a6 = v81 ∧
      reg n' a7 = v4 ∧
      reg n' (18 : Fin 32) = v143 ∧
      reg n' (19 : Fin 32) = yp ∧
      reg n' (20 : Fin 32) = v190 ∧
      reg n' (21 : Fin 32) = v10 ∧
      reg n' (22 : Fin 32) = v183 ∧
      reg n' (23 : Fin 32) = v163 ∧
      reg n' (24 : Fin 32) = v165 ∧
      reg n' (25 : Fin 32) = xp ∧
      reg n' (26 : Fin 32) = v65 ∧
      reg n' (27 : Fin 32) = v191 ∧
      reg n' (28 : Fin 32) = v6 ∧
      reg n' (29 : Fin 32) = v82 ∧
      reg n' (30 : Fin 32) = v6 ∧
      reg n' (31 : Fin 32) = v181 ∧
      memLoad32 M' (F + 0xAC) = v9 ∧
      memLoad32 M' (F + 0xB8) = v60 ∧
      memLoad32 M' (F + 0xC0) = v73 ∧
      memLoad32 M' (F + 0xC8) = v10 ∧
      memLoad32 M' (F + 0xD4) = v8 ∧
      memLoad32 M' (F + 0xE0) = v5 ∧
      memLoad32 M' (F + 0xE8) = v7 ∧
      memLoad32 M' (F + 0xEC) = v3 ∧
      memLoad32 M' (F + 0xF8) = outp ∧
      memLoad32 M' (F + 0x100) = v4 ∧
      memLoad32 M' (F + 0x104) = v122 ∧
      memLoad32 M' (F + 0x108) = v55 ∧
      memLoad32 M' (F + 0x10C) = v21 ∧
      memLoad32 M' (F + 0x110) = v28 ∧
      memLoad32 M' (F + 0x114) = v90 ∧
      memLoad32 M' (F + 0x118) = v52 ∧
      memLoad32 M' (F + 0x11C) = v36 ∧
      memLoad32 M' (F + 0x120) = v139 ∧
      memLoad32 M' (F + 0x124) = v141 ∧
      memLoad32 M' (F + 0x128) = v186 ∧
      memLoad32 M' (F + 0x12C) = v169 ∧
      memLoad32 M' (F + 0x134) = v147 ∧
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
      aluEval .mul v82 v66 = v160 ∧
      aluEval .mul v67 v81 = v161 ∧
      aluEval .mulhu v83 v65 = v163 ∧
      aluEval .sltu v158 v143 = v164 ∧
      aluEval .mul v83 v65 = v165 ∧
      aluEval .add v157 v159 = v167 ∧
      aluEval .add v164 v149 = v168 ∧
      aluEval .sub v167 v168 = v169 ∧
      aluEval .add v154 v156 = v171 ∧
      aluEval .mulhu v60 v10 = v174 ∧
      aluEval .mulhu v73 v8 = v177 ∧
      aluEval .mul v60 v10 = v178 ∧
      aluEval .mul v73 v8 = v179 ∧
      aluEval .add v171 v163 = v180 ∧
      aluEval .add v160 v161 = v181 ∧
      aluEval .sltu v181 v161 = v182 ∧
      aluEval .add v181 v165 = v183 ∧
      aluEval .add v182 v180 = v184 ∧
      aluEval .sltu v183 v181 = v185 ∧
      aluEval .sub v158 v143 = v186 ∧
      aluEval .add v184 v185 = v188 ∧
      aluEval .add v177 v174 = v189 ∧
      memLoad32 M0 (yp + 0x20) = v190 ∧
      aluEval .add v179 v178 = v191 ∧
      aluEval .mul v6 v4 = v193 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n160, v160, d160, hv160, u160⟩ := s.aluG hc smm_at_236 (off' := 0x23A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv160
  obtain ⟨n161, v161, d161, hv161, u161⟩ := u160.aluG hc smm_at_23a (off' := 0x23E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv161
  obtain ⟨n162, d162, u162⟩ := u161.lwE hc smm_at_23e (off' := 0x240) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 132) (by decide)) (v := v83)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl84])
  obtain ⟨n163, v163, d163, hv163, u163⟩ := u162.aluG hc smm_at_240 (off' := 0x244) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv163
  obtain ⟨n164, v164, d164, hv164, u164⟩ := u163.aluG hc smm_at_244 (off' := 0x248) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv164
  obtain ⟨n165, v165, d165, hv165, u165⟩ := u164.aluG hc smm_at_248 (off' := 0x24C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv165
  obtain ⟨n166, d166, u166⟩ := u165.aluE hc smm_at_24c (off' := 0x24E) (by decide) (v := v65)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n167, v167, d167, hv167, u167⟩ := u166.aluG hc smm_at_24e (off' := 0x250) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv167
  obtain ⟨n168, v168, d168, hv168, u168⟩ := u167.aluG hc smm_at_250 (off' := 0x252) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv168
  obtain ⟨n169, v169, d169, hv169, u169⟩ := u168.aluG hc smm_at_252 (off' := 0x254) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv169
  obtain ⟨n170, d170, u170⟩ := u169.swG hc smm_at_254 (off' := 0x258) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 300) (by decide)) (a := F + 0x12C) (v := v169)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M170, hM170⟩ : ∃ M', memStore32 Mi (F + 0x12C) v169 = M' := ⟨_, rfl⟩
  rw [hM170] at u170
  have hc170 : CodeIn M170 B scalar29MontMulCode := by rw [← hM170]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr170 : ∀ x, Sep F 0x190 x 1 → M170 x = M0 x := fun x hx => by
    rw [← hM170, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n171, v171, d171, hv171, u171⟩ := u170.aluG hc170 smm_at_258 (off' := 0x25A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv171
  obtain ⟨n172, d172, u172⟩ := u171.swG hc170 smm_at_25a (off' := 0x25C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 184) (by decide)) (a := F + 0xB8) (v := v60)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M172, hM172⟩ : ∃ M', memStore32 M170 (F + 0xB8) v60 = M' := ⟨_, rfl⟩
  rw [hM172] at u172
  have hc172 : CodeIn M172 B scalar29MontMulCode := by rw [← hM172]; exact hc170.store32 (frm_sep' sFC (by decide))
  have fr172 : ∀ x, Sep F 0x190 x 1 → M172 x = M0 x := fun x hx => by
    rw [← hM172, memStore32_get_sep (frm_sep' hx (by decide)), fr170 x hx]
  obtain ⟨n173, d173, u173⟩ := u172.swG hc172 smm_at_25c (off' := 0x25E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 200) (by decide)) (a := F + 0xC8) (v := v10)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M173, hM173⟩ : ∃ M', memStore32 M172 (F + 0xC8) v10 = M' := ⟨_, rfl⟩
  rw [hM173] at u173
  have hc173 : CodeIn M173 B scalar29MontMulCode := by rw [← hM173]; exact hc172.store32 (frm_sep' sFC (by decide))
  have fr173 : ∀ x, Sep F 0x190 x 1 → M173 x = M0 x := fun x hx => by
    rw [← hM173, memStore32_get_sep (frm_sep' hx (by decide)), fr172 x hx]
  obtain ⟨n174, v174, d174, hv174, u174⟩ := u173.aluG hc173 smm_at_25e (off' := 0x262) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv174
  obtain ⟨n175, d175, u175⟩ := u174.swG hc173 smm_at_262 (off' := 0x264) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 192) (by decide)) (a := F + 0xC0) (v := v73)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M175, hM175⟩ : ∃ M', memStore32 M173 (F + 0xC0) v73 = M' := ⟨_, rfl⟩
  rw [hM175] at u175
  have hc175 : CodeIn M175 B scalar29MontMulCode := by rw [← hM175]; exact hc173.store32 (frm_sep' sFC (by decide))
  have fr175 : ∀ x, Sep F 0x190 x 1 → M175 x = M0 x := fun x hx => by
    rw [← hM175, memStore32_get_sep (frm_sep' hx (by decide)), fr173 x hx]
  obtain ⟨n176, d176, u176⟩ := u175.swG hc175 smm_at_264 (off' := 0x266) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 212) (by decide)) (a := F + 0xD4) (v := v8)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M176, hM176⟩ : ∃ M', memStore32 M175 (F + 0xD4) v8 = M' := ⟨_, rfl⟩
  rw [hM176] at u176
  have hc176 : CodeIn M176 B scalar29MontMulCode := by rw [← hM176]; exact hc175.store32 (frm_sep' sFC (by decide))
  have fr176 : ∀ x, Sep F 0x190 x 1 → M176 x = M0 x := fun x hx => by
    rw [← hM176, memStore32_get_sep (frm_sep' hx (by decide)), fr175 x hx]
  obtain ⟨n177, v177, d177, hv177, u177⟩ := u176.aluG hc176 smm_at_266 (off' := 0x26A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv177
  obtain ⟨n178, v178, d178, hv178, u178⟩ := u177.aluG hc176 smm_at_26a (off' := 0x26E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv178
  obtain ⟨n179, v179, d179, hv179, u179⟩ := u178.aluG hc176 smm_at_26e (off' := 0x272) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv179
  obtain ⟨n180, v180, d180, hv180, u180⟩ := u179.aluG hc176 smm_at_272 (off' := 0x274) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv180
  obtain ⟨n181, v181, d181, hv181, u181⟩ := u180.aluG hc176 smm_at_274 (off' := 0x276) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv181
  obtain ⟨n182, v182, d182, hv182, u182⟩ := u181.aluG hc176 smm_at_276 (off' := 0x27A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv182
  obtain ⟨n183, v183, d183, hv183, u183⟩ := u182.aluG hc176 smm_at_27a (off' := 0x27E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv183
  obtain ⟨n184, v184, d184, hv184, u184⟩ := u183.aluG hc176 smm_at_27e (off' := 0x280) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv184
  obtain ⟨n185, v185, d185, hv185, u185⟩ := u184.aluG hc176 smm_at_280 (off' := 0x284) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv185
  obtain ⟨n186, v186, d186, hv186, u186⟩ := u185.aluG hc176 smm_at_284 (off' := 0x288) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv186
  obtain ⟨n187, d187, u187⟩ := u186.swG hc176 smm_at_288 (off' := 0x28C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 296) (by decide)) (a := F + 0x128) (v := v186)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M187, hM187⟩ : ∃ M', memStore32 M176 (F + 0x128) v186 = M' := ⟨_, rfl⟩
  rw [hM187] at u187
  have hc187 : CodeIn M187 B scalar29MontMulCode := by rw [← hM187]; exact hc176.store32 (frm_sep' sFC (by decide))
  have fr187 : ∀ x, Sep F 0x190 x 1 → M187 x = M0 x := fun x hx => by
    rw [← hM187, memStore32_get_sep (frm_sep' hx (by decide)), fr176 x hx]
  obtain ⟨n188, v188, d188, hv188, u188⟩ := u187.aluG hc187 smm_at_28c (off' := 0x28E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv188
  obtain ⟨n189, v189, d189, hv189, u189⟩ := u188.aluG hc187 smm_at_28e (off' := 0x290) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv189
  obtain ⟨n190, v190, d190, hv190, u190⟩ := u189.lwG hc187 smm_at_290 (off' := 0x294) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hy (k := 32) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv190
  rw [load_frame fr187 (show Sep F 0x190 (yp + 0x20) 4 from sYF.symm.subR (c := 32) (l := 4) (by decide))] at hv190
  obtain ⟨n191, v191, d191, hv191, u191⟩ := u190.aluG hc187 smm_at_294 (off' := 0x298) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv191
  obtain ⟨n192, d192, u192⟩ := u191.lwE hc187 smm_at_298 (off' := 0x29C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 256) (by decide)) (v := v4)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x100) 4 from sep_offsets F (c := 296) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x100) 4 from sep_offsets F (c := 212) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x100) 4 from sep_offsets F (c := 192) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x100) 4 from sep_offsets F (c := 200) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x100) 4 from sep_offsets F (c := 184) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x100) 4 from sep_offsets F (c := 300) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100])
  obtain ⟨n193, v193, d193, hv193, u193⟩ := u192.aluG hc187 smm_at_29c (off' := 0x2A0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv193
  obtain ⟨n194, d194, u194⟩ := u193.aluE hc187 smm_at_2a0 (off' := 0x2A2) (by decide) (v := v6)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  have qo1 : reg n194 ra = v83 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n194 sp = F := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n194 (3 : Fin 32) = G3 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n194 (4 : Fin 32) = G4 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n194 (5 : Fin 32) = v67 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n194 (6 : Fin 32) = v66 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n194 (7 : Fin 32) = v60 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n194 (8 : Fin 32) = v178 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n194 (9 : Fin 32) = v193 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n194 a0 = v186 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n194 a1 = v188 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n194 a2 = v174 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n194 a3 = v189 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n194 a4 = v185 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n194 a5 = v179 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n194 a6 = v81 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n194 a7 = v4 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n194 (18 : Fin 32) = v143 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n194 (19 : Fin 32) = yp := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n194 (20 : Fin 32) = v190 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n194 (21 : Fin 32) = v10 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n194 (22 : Fin 32) = v183 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n194 (23 : Fin 32) = v163 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n194 (24 : Fin 32) = v165 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n194 (25 : Fin 32) = xp := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n194 (26 : Fin 32) = v65 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n194 (27 : Fin 32) = v191 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n194 (28 : Fin 32) = v6 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n194 (29 : Fin 32) = v82 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n194 (30 : Fin 32) = v6 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n194 (31 : Fin 32) = v181 := by rw [u194.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soAC : memLoad32 M187 (F + 0xAC) = v9 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0xAC) 4 from sep_offsets F (c := 296) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xAC) 4 from sep_offsets F (c := 212) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xAC) 4 from sep_offsets F (c := 192) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xAC) 4 from sep_offsets F (c := 200) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0xAC) 4 from sep_offsets F (c := 184) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0xAC) 4 from sep_offsets F (c := 300) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), slAC]
  have soB8 : memLoad32 M187 (F + 0xB8) = v60 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0xB8) 4 from sep_offsets F (c := 296) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xB8) 4 from sep_offsets F (c := 212) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xB8) 4 from sep_offsets F (c := 192) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xB8) 4 from sep_offsets F (c := 200) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_same]
  have soC0 : memLoad32 M187 (F + 0xC0) = v73 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0xC0) 4 from sep_offsets F (c := 296) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xC0) 4 from sep_offsets F (c := 212) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_same]
  have soC8 : memLoad32 M187 (F + 0xC8) = v10 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0xC8) 4 from sep_offsets F (c := 296) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xC8) 4 from sep_offsets F (c := 212) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xC8) 4 from sep_offsets F (c := 192) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_same]
  have soD4 : memLoad32 M187 (F + 0xD4) = v8 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0xD4) 4 from sep_offsets F (c := 296) (n := 4) (d := 212) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_same]
  have soE0 : memLoad32 M187 (F + 0xE0) = v5 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0xE0) 4 from sep_offsets F (c := 296) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xE0) 4 from sep_offsets F (c := 212) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xE0) 4 from sep_offsets F (c := 192) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xE0) 4 from sep_offsets F (c := 200) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0xE0) 4 from sep_offsets F (c := 184) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0xE0) 4 from sep_offsets F (c := 300) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), slE0]
  have soE8 : memLoad32 M187 (F + 0xE8) = v7 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0xE8) 4 from sep_offsets F (c := 296) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xE8) 4 from sep_offsets F (c := 212) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xE8) 4 from sep_offsets F (c := 192) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xE8) 4 from sep_offsets F (c := 200) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0xE8) 4 from sep_offsets F (c := 184) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0xE8) 4 from sep_offsets F (c := 300) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), slE8]
  have soEC : memLoad32 M187 (F + 0xEC) = v3 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0xEC) 4 from sep_offsets F (c := 296) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xEC) 4 from sep_offsets F (c := 212) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xEC) 4 from sep_offsets F (c := 192) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xEC) 4 from sep_offsets F (c := 200) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0xEC) 4 from sep_offsets F (c := 184) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0xEC) 4 from sep_offsets F (c := 300) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soF8 : memLoad32 M187 (F + 0xF8) = outp := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0xF8) 4 from sep_offsets F (c := 296) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xF8) 4 from sep_offsets F (c := 212) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xF8) 4 from sep_offsets F (c := 192) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xF8) 4 from sep_offsets F (c := 200) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0xF8) 4 from sep_offsets F (c := 184) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0xF8) 4 from sep_offsets F (c := 300) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), slF8]
  have so100 : memLoad32 M187 (F + 0x100) = v4 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x100) 4 from sep_offsets F (c := 296) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x100) 4 from sep_offsets F (c := 212) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x100) 4 from sep_offsets F (c := 192) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x100) 4 from sep_offsets F (c := 200) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x100) 4 from sep_offsets F (c := 184) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x100) 4 from sep_offsets F (c := 300) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100]
  have so104 : memLoad32 M187 (F + 0x104) = v122 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x104) 4 from sep_offsets F (c := 296) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x104) 4 from sep_offsets F (c := 212) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x104) 4 from sep_offsets F (c := 192) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x104) 4 from sep_offsets F (c := 200) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x104) 4 from sep_offsets F (c := 184) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x104) 4 from sep_offsets F (c := 300) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), sl104]
  have so108 : memLoad32 M187 (F + 0x108) = v55 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x108) 4 from sep_offsets F (c := 296) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x108) 4 from sep_offsets F (c := 212) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x108) 4 from sep_offsets F (c := 192) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x108) 4 from sep_offsets F (c := 200) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x108) 4 from sep_offsets F (c := 184) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x108) 4 from sep_offsets F (c := 300) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), sl108]
  have so10C : memLoad32 M187 (F + 0x10C) = v21 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x10C) 4 from sep_offsets F (c := 296) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x10C) 4 from sep_offsets F (c := 212) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x10C) 4 from sep_offsets F (c := 192) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x10C) 4 from sep_offsets F (c := 200) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x10C) 4 from sep_offsets F (c := 184) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x10C) 4 from sep_offsets F (c := 300) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so110 : memLoad32 M187 (F + 0x110) = v28 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x110) 4 from sep_offsets F (c := 296) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x110) 4 from sep_offsets F (c := 212) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x110) 4 from sep_offsets F (c := 192) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x110) 4 from sep_offsets F (c := 200) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x110) 4 from sep_offsets F (c := 184) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x110) 4 from sep_offsets F (c := 300) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so114 : memLoad32 M187 (F + 0x114) = v90 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x114) 4 from sep_offsets F (c := 296) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x114) 4 from sep_offsets F (c := 212) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x114) 4 from sep_offsets F (c := 192) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x114) 4 from sep_offsets F (c := 200) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x114) 4 from sep_offsets F (c := 184) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x114) 4 from sep_offsets F (c := 300) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), sl114]
  have so118 : memLoad32 M187 (F + 0x118) = v52 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x118) 4 from sep_offsets F (c := 296) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x118) 4 from sep_offsets F (c := 212) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x118) 4 from sep_offsets F (c := 192) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x118) 4 from sep_offsets F (c := 200) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x118) 4 from sep_offsets F (c := 184) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x118) 4 from sep_offsets F (c := 300) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), sl118]
  have so11C : memLoad32 M187 (F + 0x11C) = v36 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x11C) 4 from sep_offsets F (c := 296) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x11C) 4 from sep_offsets F (c := 212) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x11C) 4 from sep_offsets F (c := 192) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x11C) 4 from sep_offsets F (c := 200) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x11C) 4 from sep_offsets F (c := 184) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x11C) 4 from sep_offsets F (c := 300) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), sl11C]
  have so120 : memLoad32 M187 (F + 0x120) = v139 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x120) 4 from sep_offsets F (c := 296) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x120) 4 from sep_offsets F (c := 212) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x120) 4 from sep_offsets F (c := 192) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x120) 4 from sep_offsets F (c := 200) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x120) 4 from sep_offsets F (c := 184) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x120) 4 from sep_offsets F (c := 300) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), sl120]
  have so124 : memLoad32 M187 (F + 0x124) = v141 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x124) 4 from sep_offsets F (c := 296) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x124) 4 from sep_offsets F (c := 212) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x124) 4 from sep_offsets F (c := 192) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x124) 4 from sep_offsets F (c := 200) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x124) 4 from sep_offsets F (c := 184) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x124) 4 from sep_offsets F (c := 300) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), sl124]
  have so128 : memLoad32 M187 (F + 0x128) = v186 := by
    rw [← hM187, memLoad32_store32_same]
  have so12C : memLoad32 M187 (F + 0x12C) = v169 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x12C) 4 from sep_offsets F (c := 296) (n := 4) (d := 300) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x12C) 4 from sep_offsets F (c := 212) (n := 4) (d := 300) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x12C) 4 from sep_offsets F (c := 192) (n := 4) (d := 300) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x12C) 4 from sep_offsets F (c := 200) (n := 4) (d := 300) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x12C) 4 from sep_offsets F (c := 184) (n := 4) (d := 300) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_same]
  have so134 : memLoad32 M187 (F + 0x134) = v147 := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x134) 4 from sep_offsets F (c := 296) (n := 4) (d := 308) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x134) 4 from sep_offsets F (c := 212) (n := 4) (d := 308) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x134) 4 from sep_offsets F (c := 192) (n := 4) (d := 308) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x134) 4 from sep_offsets F (c := 200) (n := 4) (d := 308) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x134) 4 from sep_offsets F (c := 184) (n := 4) (d := 308) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x134) 4 from sep_offsets F (c := 300) (n := 4) (d := 308) (k := 4) (by decide) (by decide) (by decide)), sl134]
  have so15C : memLoad32 M187 (F + 0x15C) = memLoad32 M0 (F + 0x15C) := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x15C) 4 from sep_offsets F (c := 296) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x15C) 4 from sep_offsets F (c := 212) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x15C) 4 from sep_offsets F (c := 192) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x15C) 4 from sep_offsets F (c := 200) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x15C) 4 from sep_offsets F (c := 184) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x15C) 4 from sep_offsets F (c := 300) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), sl15C]
  have so160 : memLoad32 M187 (F + 0x160) = memLoad32 M0 (F + 0x160) := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x160) 4 from sep_offsets F (c := 296) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x160) 4 from sep_offsets F (c := 212) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x160) 4 from sep_offsets F (c := 192) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x160) 4 from sep_offsets F (c := 200) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x160) 4 from sep_offsets F (c := 184) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x160) 4 from sep_offsets F (c := 300) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), sl160]
  have so164 : memLoad32 M187 (F + 0x164) = memLoad32 M0 (F + 0x164) := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x164) 4 from sep_offsets F (c := 296) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x164) 4 from sep_offsets F (c := 212) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x164) 4 from sep_offsets F (c := 192) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x164) 4 from sep_offsets F (c := 200) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x164) 4 from sep_offsets F (c := 184) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x164) 4 from sep_offsets F (c := 300) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), sl164]
  have so168 : memLoad32 M187 (F + 0x168) = memLoad32 M0 (F + 0x168) := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x168) 4 from sep_offsets F (c := 296) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x168) 4 from sep_offsets F (c := 212) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x168) 4 from sep_offsets F (c := 192) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x168) 4 from sep_offsets F (c := 200) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x168) 4 from sep_offsets F (c := 184) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x168) 4 from sep_offsets F (c := 300) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), sl168]
  have so16C : memLoad32 M187 (F + 0x16C) = memLoad32 M0 (F + 0x16C) := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x16C) 4 from sep_offsets F (c := 296) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x16C) 4 from sep_offsets F (c := 212) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x16C) 4 from sep_offsets F (c := 192) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x16C) 4 from sep_offsets F (c := 200) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x16C) 4 from sep_offsets F (c := 184) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x16C) 4 from sep_offsets F (c := 300) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), sl16C]
  have so170 : memLoad32 M187 (F + 0x170) = memLoad32 M0 (F + 0x170) := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x170) 4 from sep_offsets F (c := 296) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x170) 4 from sep_offsets F (c := 212) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x170) 4 from sep_offsets F (c := 192) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x170) 4 from sep_offsets F (c := 200) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x170) 4 from sep_offsets F (c := 184) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x170) 4 from sep_offsets F (c := 300) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), sl170]
  have so174 : memLoad32 M187 (F + 0x174) = memLoad32 M0 (F + 0x174) := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x174) 4 from sep_offsets F (c := 296) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x174) 4 from sep_offsets F (c := 212) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x174) 4 from sep_offsets F (c := 192) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x174) 4 from sep_offsets F (c := 200) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x174) 4 from sep_offsets F (c := 184) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x174) 4 from sep_offsets F (c := 300) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), sl174]
  have so178 : memLoad32 M187 (F + 0x178) = memLoad32 M0 (F + 0x178) := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x178) 4 from sep_offsets F (c := 296) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x178) 4 from sep_offsets F (c := 212) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x178) 4 from sep_offsets F (c := 192) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x178) 4 from sep_offsets F (c := 200) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x178) 4 from sep_offsets F (c := 184) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x178) 4 from sep_offsets F (c := 300) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), sl178]
  have so17C : memLoad32 M187 (F + 0x17C) = memLoad32 M0 (F + 0x17C) := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x17C) 4 from sep_offsets F (c := 296) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x17C) 4 from sep_offsets F (c := 212) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x17C) 4 from sep_offsets F (c := 192) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x17C) 4 from sep_offsets F (c := 200) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x17C) 4 from sep_offsets F (c := 184) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x17C) 4 from sep_offsets F (c := 300) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), sl17C]
  have so180 : memLoad32 M187 (F + 0x180) = memLoad32 M0 (F + 0x180) := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x180) 4 from sep_offsets F (c := 296) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x180) 4 from sep_offsets F (c := 212) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x180) 4 from sep_offsets F (c := 192) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x180) 4 from sep_offsets F (c := 200) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x180) 4 from sep_offsets F (c := 184) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x180) 4 from sep_offsets F (c := 300) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), sl180]
  have so184 : memLoad32 M187 (F + 0x184) = memLoad32 M0 (F + 0x184) := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x184) 4 from sep_offsets F (c := 296) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x184) 4 from sep_offsets F (c := 212) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x184) 4 from sep_offsets F (c := 192) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x184) 4 from sep_offsets F (c := 200) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x184) 4 from sep_offsets F (c := 184) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x184) 4 from sep_offsets F (c := 300) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), sl184]
  have so188 : memLoad32 M187 (F + 0x188) = memLoad32 M0 (F + 0x188) := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x188) 4 from sep_offsets F (c := 296) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x188) 4 from sep_offsets F (c := 212) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x188) 4 from sep_offsets F (c := 192) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x188) 4 from sep_offsets F (c := 200) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x188) 4 from sep_offsets F (c := 184) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x188) 4 from sep_offsets F (c := 300) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), sl188]
  have so18C : memLoad32 M187 (F + 0x18C) = memLoad32 M0 (F + 0x18C) := by
    rw [← hM187, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x18C) 4 from sep_offsets F (c := 296) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM176, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x18C) 4 from sep_offsets F (c := 212) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM175, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x18C) 4 from sep_offsets F (c := 192) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM173, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x18C) 4 from sep_offsets F (c := 200) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM172, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x18C) 4 from sep_offsets F (c := 184) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x18C) 4 from sep_offsets F (c := 300) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), sl18C]
  exact ⟨n194, M187, v160, v161, v163, v164, v165, v167, v168, v169, v171, v174, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v188, v189, v190, v191, v193, (.cons d160 (.cons d161 (.cons d162 (.cons d163 (.cons d164 (.cons d165 (.cons d166 (.cons d167 (.cons d168 (.cons d169 (.cons d170 (.cons d171 (.cons d172 (.cons d173 (.cons d174 (.cons d175 (.cons d176 (.cons d177 (.cons d178 (.cons d179 (.cons d180 (.cons d181 (.cons d182 (.cons d183 (.cons d184 (.cons d185 (.cons d186 (.cons d187 (.cons d188 (.cons d189 (.cons d190 (.cons d191 (.cons d192 (.cons d193 (.single d194))))))))))))))))))))))))))))))))))), u194.self, hc187, fr187, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soAC, soB8, soC0, soC8, soD4, soE0, soE8, soEC, soF8, so100, so104, so108, so10C, so110, so114, so118, so11C, so120, so124, so128, so12C, so134, so15C, so160, so164, so168, so16C, so170, so174, so178, so17C, so180, so184, so188, so18C, hv160, hv161, hv163, hv164, hv165, hv167, hv168, hv169, hv171, hv174, hv177, hv178, hv179, hv180, hv181, hv182, hv183, hv184, hv185, hv186, hv188, hv189, hv190, hv191, hv193⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem smm_g5 {M0 Mi : Word → BitVec 8} {B F outp xp yp G3 G4 : Word} {n : Machine} {v3 v4 v5 v6 v7 v8 v9 v10 v21 v28 v36 v52 v55 v60 v65 v66 v67 v73 v81 v82 v83 v90 v122 v139 v141 v143 v147 v163 v165 v169 v174 v178 v179 v181 v183 v185 v186 v188 v189 v190 v191 v193 : Word}
    (s : St Mi B n 0x2A2 (reg n)) (hc : CodeIn Mi B scalar29MontMulCode)
    (fr : ∀ x, Sep F 0x190 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190)
    (q1 : reg n ra = v83)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v67)
    (q6 : reg n (6 : Fin 32) = v66)
    (q7 : reg n (7 : Fin 32) = v60)
    (q8 : reg n (8 : Fin 32) = v178)
    (q9 : reg n (9 : Fin 32) = v193)
    (q10 : reg n a0 = v186)
    (q11 : reg n a1 = v188)
    (q12 : reg n a2 = v174)
    (q13 : reg n a3 = v189)
    (q14 : reg n a4 = v185)
    (q15 : reg n a5 = v179)
    (q16 : reg n a6 = v81)
    (q17 : reg n a7 = v4)
    (q18 : reg n (18 : Fin 32) = v143)
    (q19 : reg n (19 : Fin 32) = yp)
    (q20 : reg n (20 : Fin 32) = v190)
    (q21 : reg n (21 : Fin 32) = v10)
    (q22 : reg n (22 : Fin 32) = v183)
    (q23 : reg n (23 : Fin 32) = v163)
    (q24 : reg n (24 : Fin 32) = v165)
    (q25 : reg n (25 : Fin 32) = xp)
    (q26 : reg n (26 : Fin 32) = v65)
    (q27 : reg n (27 : Fin 32) = v191)
    (q28 : reg n (28 : Fin 32) = v6)
    (q29 : reg n (29 : Fin 32) = v82)
    (q30 : reg n (30 : Fin 32) = v6)
    (q31 : reg n (31 : Fin 32) = v181)
    (slAC : memLoad32 Mi (F + 0xAC) = v9)
    (slB8 : memLoad32 Mi (F + 0xB8) = v60)
    (slC0 : memLoad32 Mi (F + 0xC0) = v73)
    (slC8 : memLoad32 Mi (F + 0xC8) = v10)
    (slD4 : memLoad32 Mi (F + 0xD4) = v8)
    (slE0 : memLoad32 Mi (F + 0xE0) = v5)
    (slE8 : memLoad32 Mi (F + 0xE8) = v7)
    (slEC : memLoad32 Mi (F + 0xEC) = v3)
    (slF8 : memLoad32 Mi (F + 0xF8) = outp)
    (sl100 : memLoad32 Mi (F + 0x100) = v4)
    (sl104 : memLoad32 Mi (F + 0x104) = v122)
    (sl108 : memLoad32 Mi (F + 0x108) = v55)
    (sl10C : memLoad32 Mi (F + 0x10C) = v21)
    (sl110 : memLoad32 Mi (F + 0x110) = v28)
    (sl114 : memLoad32 Mi (F + 0x114) = v90)
    (sl118 : memLoad32 Mi (F + 0x118) = v52)
    (sl11C : memLoad32 Mi (F + 0x11C) = v36)
    (sl120 : memLoad32 Mi (F + 0x120) = v139)
    (sl124 : memLoad32 Mi (F + 0x124) = v141)
    (sl128 : memLoad32 Mi (F + 0x128) = v186)
    (sl12C : memLoad32 Mi (F + 0x12C) = v169)
    (sl134 : memLoad32 Mi (F + 0x134) = v147)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v196 v197 v198 v199 : Word),
      Steps n n' ∧
      St M' B n' 0x2B4 (reg n') ∧
      CodeIn M' B scalar29MontMulCode ∧
      (∀ x, Sep F 0x190 x 1 → M' x = M0 x) ∧
      reg n' ra = v83 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v67 ∧
      reg n' (6 : Fin 32) = v66 ∧
      reg n' (7 : Fin 32) = v60 ∧
      reg n' (8 : Fin 32) = v178 ∧
      reg n' (9 : Fin 32) = v193 ∧
      reg n' a0 = v199 ∧
      reg n' a1 = v188 ∧
      reg n' a2 = v174 ∧
      reg n' a3 = v189 ∧
      reg n' a4 = v185 ∧
      reg n' a5 = v179 ∧
      reg n' a6 = v81 ∧
      reg n' a7 = v4 ∧
      reg n' (18 : Fin 32) = v143 ∧
      reg n' (19 : Fin 32) = yp ∧
      reg n' (20 : Fin 32) = v190 ∧
      reg n' (21 : Fin 32) = v10 ∧
      reg n' (22 : Fin 32) = v183 ∧
      reg n' (23 : Fin 32) = v198 ∧
      reg n' (24 : Fin 32) = v197 ∧
      reg n' (25 : Fin 32) = xp ∧
      reg n' (26 : Fin 32) = v65 ∧
      reg n' (27 : Fin 32) = v191 ∧
      reg n' (28 : Fin 32) = v6 ∧
      reg n' (29 : Fin 32) = v82 ∧
      reg n' (30 : Fin 32) = v6 ∧
      reg n' (31 : Fin 32) = v196 ∧
      memLoad32 M' (F + 0x9C) = v6 ∧
      memLoad32 M' (F + 0xAC) = v9 ∧
      memLoad32 M' (F + 0xB8) = v60 ∧
      memLoad32 M' (F + 0xC0) = v73 ∧
      memLoad32 M' (F + 0xC8) = v10 ∧
      memLoad32 M' (F + 0xD4) = v8 ∧
      memLoad32 M' (F + 0xE0) = v5 ∧
      memLoad32 M' (F + 0xE8) = v7 ∧
      memLoad32 M' (F + 0xEC) = v3 ∧
      memLoad32 M' (F + 0xF8) = outp ∧
      memLoad32 M' (F + 0x100) = v4 ∧
      memLoad32 M' (F + 0x104) = v122 ∧
      memLoad32 M' (F + 0x108) = v55 ∧
      memLoad32 M' (F + 0x10C) = v21 ∧
      memLoad32 M' (F + 0x110) = v28 ∧
      memLoad32 M' (F + 0x114) = v90 ∧
      memLoad32 M' (F + 0x118) = v52 ∧
      memLoad32 M' (F + 0x11C) = v36 ∧
      memLoad32 M' (F + 0x120) = v139 ∧
      memLoad32 M' (F + 0x124) = v141 ∧
      memLoad32 M' (F + 0x128) = v186 ∧
      memLoad32 M' (F + 0x12C) = v169 ∧
      memLoad32 M' (F + 0x134) = v147 ∧
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
      aluEval .mulhu v67 v82 = v196 ∧
      aluEval .mulhu v83 v66 = v197 ∧
      aluEval .mul v67 v82 = v198 ∧
      aluEval .mul v83 v66 = v199 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n195, d195, u195⟩ := s.swG hc smm_at_2a2 (off' := 0x2A4) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 156) (by decide)) (a := F + 0x9C) (v := v6)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M195, hM195⟩ : ∃ M', memStore32 Mi (F + 0x9C) v6 = M' := ⟨_, rfl⟩
  rw [hM195] at u195
  have hc195 : CodeIn M195 B scalar29MontMulCode := by rw [← hM195]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr195 : ∀ x, Sep F 0x190 x 1 → M195 x = M0 x := fun x hx => by
    rw [← hM195, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n196, v196, d196, hv196, u196⟩ := u195.aluG hc195 smm_at_2a4 (off' := 0x2A8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv196
  obtain ⟨n197, v197, d197, hv197, u197⟩ := u196.aluG hc195 smm_at_2a8 (off' := 0x2AC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv197
  obtain ⟨n198, v198, d198, hv198, u198⟩ := u197.aluG hc195 smm_at_2ac (off' := 0x2B0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv198
  obtain ⟨n199, v199, d199, hv199, u199⟩ := u198.aluG hc195 smm_at_2b0 (off' := 0x2B4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv199
  have qo1 : reg n199 ra = v83 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n199 sp = F := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n199 (3 : Fin 32) = G3 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n199 (4 : Fin 32) = G4 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n199 (5 : Fin 32) = v67 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n199 (6 : Fin 32) = v66 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n199 (7 : Fin 32) = v60 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n199 (8 : Fin 32) = v178 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n199 (9 : Fin 32) = v193 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n199 a0 = v199 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n199 a1 = v188 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n199 a2 = v174 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n199 a3 = v189 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n199 a4 = v185 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n199 a5 = v179 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n199 a6 = v81 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n199 a7 = v4 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n199 (18 : Fin 32) = v143 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n199 (19 : Fin 32) = yp := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n199 (20 : Fin 32) = v190 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n199 (21 : Fin 32) = v10 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n199 (22 : Fin 32) = v183 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n199 (23 : Fin 32) = v198 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n199 (24 : Fin 32) = v197 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n199 (25 : Fin 32) = xp := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n199 (26 : Fin 32) = v65 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n199 (27 : Fin 32) = v191 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n199 (28 : Fin 32) = v6 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n199 (29 : Fin 32) = v82 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n199 (30 : Fin 32) = v6 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n199 (31 : Fin 32) = v196 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so9C : memLoad32 M195 (F + 0x9C) = v6 := by
    rw [← hM195, memLoad32_store32_same]
  have soAC : memLoad32 M195 (F + 0xAC) = v9 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xAC) 4 from sep_offsets F (c := 156) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), slAC]
  have soB8 : memLoad32 M195 (F + 0xB8) = v60 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xB8) 4 from sep_offsets F (c := 156) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), slB8]
  have soC0 : memLoad32 M195 (F + 0xC0) = v73 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xC0) 4 from sep_offsets F (c := 156) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), slC0]
  have soC8 : memLoad32 M195 (F + 0xC8) = v10 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xC8) 4 from sep_offsets F (c := 156) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), slC8]
  have soD4 : memLoad32 M195 (F + 0xD4) = v8 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xD4) 4 from sep_offsets F (c := 156) (n := 4) (d := 212) (k := 4) (by decide) (by decide) (by decide)), slD4]
  have soE0 : memLoad32 M195 (F + 0xE0) = v5 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xE0) 4 from sep_offsets F (c := 156) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), slE0]
  have soE8 : memLoad32 M195 (F + 0xE8) = v7 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xE8) 4 from sep_offsets F (c := 156) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), slE8]
  have soEC : memLoad32 M195 (F + 0xEC) = v3 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xEC) 4 from sep_offsets F (c := 156) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soF8 : memLoad32 M195 (F + 0xF8) = outp := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xF8) 4 from sep_offsets F (c := 156) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), slF8]
  have so100 : memLoad32 M195 (F + 0x100) = v4 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x100) 4 from sep_offsets F (c := 156) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100]
  have so104 : memLoad32 M195 (F + 0x104) = v122 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x104) 4 from sep_offsets F (c := 156) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), sl104]
  have so108 : memLoad32 M195 (F + 0x108) = v55 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x108) 4 from sep_offsets F (c := 156) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), sl108]
  have so10C : memLoad32 M195 (F + 0x10C) = v21 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x10C) 4 from sep_offsets F (c := 156) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so110 : memLoad32 M195 (F + 0x110) = v28 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x110) 4 from sep_offsets F (c := 156) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so114 : memLoad32 M195 (F + 0x114) = v90 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x114) 4 from sep_offsets F (c := 156) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), sl114]
  have so118 : memLoad32 M195 (F + 0x118) = v52 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x118) 4 from sep_offsets F (c := 156) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), sl118]
  have so11C : memLoad32 M195 (F + 0x11C) = v36 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x11C) 4 from sep_offsets F (c := 156) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), sl11C]
  have so120 : memLoad32 M195 (F + 0x120) = v139 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x120) 4 from sep_offsets F (c := 156) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), sl120]
  have so124 : memLoad32 M195 (F + 0x124) = v141 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x124) 4 from sep_offsets F (c := 156) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), sl124]
  have so128 : memLoad32 M195 (F + 0x128) = v186 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x128) 4 from sep_offsets F (c := 156) (n := 4) (d := 296) (k := 4) (by decide) (by decide) (by decide)), sl128]
  have so12C : memLoad32 M195 (F + 0x12C) = v169 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x12C) 4 from sep_offsets F (c := 156) (n := 4) (d := 300) (k := 4) (by decide) (by decide) (by decide)), sl12C]
  have so134 : memLoad32 M195 (F + 0x134) = v147 := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x134) 4 from sep_offsets F (c := 156) (n := 4) (d := 308) (k := 4) (by decide) (by decide) (by decide)), sl134]
  have so15C : memLoad32 M195 (F + 0x15C) = memLoad32 M0 (F + 0x15C) := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x15C) 4 from sep_offsets F (c := 156) (n := 4) (d := 348) (k := 4) (by decide) (by decide) (by decide)), sl15C]
  have so160 : memLoad32 M195 (F + 0x160) = memLoad32 M0 (F + 0x160) := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x160) 4 from sep_offsets F (c := 156) (n := 4) (d := 352) (k := 4) (by decide) (by decide) (by decide)), sl160]
  have so164 : memLoad32 M195 (F + 0x164) = memLoad32 M0 (F + 0x164) := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x164) 4 from sep_offsets F (c := 156) (n := 4) (d := 356) (k := 4) (by decide) (by decide) (by decide)), sl164]
  have so168 : memLoad32 M195 (F + 0x168) = memLoad32 M0 (F + 0x168) := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x168) 4 from sep_offsets F (c := 156) (n := 4) (d := 360) (k := 4) (by decide) (by decide) (by decide)), sl168]
  have so16C : memLoad32 M195 (F + 0x16C) = memLoad32 M0 (F + 0x16C) := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x16C) 4 from sep_offsets F (c := 156) (n := 4) (d := 364) (k := 4) (by decide) (by decide) (by decide)), sl16C]
  have so170 : memLoad32 M195 (F + 0x170) = memLoad32 M0 (F + 0x170) := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x170) 4 from sep_offsets F (c := 156) (n := 4) (d := 368) (k := 4) (by decide) (by decide) (by decide)), sl170]
  have so174 : memLoad32 M195 (F + 0x174) = memLoad32 M0 (F + 0x174) := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x174) 4 from sep_offsets F (c := 156) (n := 4) (d := 372) (k := 4) (by decide) (by decide) (by decide)), sl174]
  have so178 : memLoad32 M195 (F + 0x178) = memLoad32 M0 (F + 0x178) := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x178) 4 from sep_offsets F (c := 156) (n := 4) (d := 376) (k := 4) (by decide) (by decide) (by decide)), sl178]
  have so17C : memLoad32 M195 (F + 0x17C) = memLoad32 M0 (F + 0x17C) := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x17C) 4 from sep_offsets F (c := 156) (n := 4) (d := 380) (k := 4) (by decide) (by decide) (by decide)), sl17C]
  have so180 : memLoad32 M195 (F + 0x180) = memLoad32 M0 (F + 0x180) := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x180) 4 from sep_offsets F (c := 156) (n := 4) (d := 384) (k := 4) (by decide) (by decide) (by decide)), sl180]
  have so184 : memLoad32 M195 (F + 0x184) = memLoad32 M0 (F + 0x184) := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x184) 4 from sep_offsets F (c := 156) (n := 4) (d := 388) (k := 4) (by decide) (by decide) (by decide)), sl184]
  have so188 : memLoad32 M195 (F + 0x188) = memLoad32 M0 (F + 0x188) := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x188) 4 from sep_offsets F (c := 156) (n := 4) (d := 392) (k := 4) (by decide) (by decide) (by decide)), sl188]
  have so18C : memLoad32 M195 (F + 0x18C) = memLoad32 M0 (F + 0x18C) := by
    rw [← hM195, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x18C) 4 from sep_offsets F (c := 156) (n := 4) (d := 396) (k := 4) (by decide) (by decide) (by decide)), sl18C]
  exact ⟨n199, M195, v196, v197, v198, v199, (.cons d195 (.cons d196 (.cons d197 (.cons d198 (.single d199))))), u199.self, hc195, fr195, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so9C, soAC, soB8, soC0, soC8, soD4, soE0, soE8, soEC, soF8, so100, so104, so108, so10C, so110, so114, so118, so11C, so120, so124, so128, so12C, so134, so15C, so160, so164, so168, so16C, so170, so174, so178, so17C, so180, so184, so188, so18C, hv196, hv197, hv198, hv199⟩

end C3.RV32
