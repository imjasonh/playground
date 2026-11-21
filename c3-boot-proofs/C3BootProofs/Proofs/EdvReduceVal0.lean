import C3BootProofs.Proofs.EdvReduceFacts

/-! # The inlined `Scalar::reduce`'s values, part 0

Each lemma proves one value the code holds in words from its instructions' facts. `scripts/gen-ev-reduce.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option maxHeartbeats 10000000 in
theorem evr_v_A0 {v2 v8 : Word}
    (t8 : v8.toNat = v2.toNat % 2 ^ 29) :
    v8.toNat = v2.toNat % 2 ^ 29 := by
  have := v2.isLt; have := v8.isLt
  generalize v2.toNat = n2 at *
  generalize v8.toNat = n8 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_SR1 {v2 v9 : Word}
    (t9 : v9.toNat = v2.toNat / 2 ^ 29) :
    v9.toNat = v2.toNat / 2 ^ 29 := by
  have := v2.isLt; have := v9.isLt
  generalize v2.toNat = n2 at *
  generalize v9.toNat = n9 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_SL1 {v3 v10 : Word}
    (t10 : v10.toNat = v3.toNat * 2 ^ 3 % 2 ^ 32) :
    v10.toNat = v3.toNat * 2 ^ 3 % 2 ^ 32 := by
  have := v3.isLt; have := v10.isLt
  generalize v3.toNat = n3 at *
  generalize v10.toNat = n10 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_O1 {v9 v10 v13 : Word}
    (t13 : v13.toNat = v9.toNat + v10.toNat) :
    v13.toNat = v9.toNat + v10.toNat := by
  have := v9.isLt; have := v10.isLt; have := v13.isLt
  generalize v9.toNat = n9 at *
  generalize v10.toNat = n10 at *
  generalize v13.toNat = n13 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_A1 {v13 v15 : Word}
    (t15 : v15.toNat = v13.toNat % 2 ^ 29) :
    v15.toNat = v13.toNat % 2 ^ 29 := by
  have := v13.isLt; have := v15.isLt
  generalize v13.toNat = n13 at *
  generalize v15.toNat = n15 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_SR2 {v3 v11 : Word}
    (t11 : v11.toNat = v3.toNat / 2 ^ 26) :
    v11.toNat = v3.toNat / 2 ^ 26 := by
  have := v3.isLt; have := v11.isLt
  generalize v3.toNat = n3 at *
  generalize v11.toNat = n11 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_SL2 {v5 v12 : Word}
    (t12 : v12.toNat = v5.toNat * 2 ^ 6 % 2 ^ 32) :
    v12.toNat = v5.toNat * 2 ^ 6 % 2 ^ 32 := by
  have := v5.isLt; have := v12.isLt
  generalize v5.toNat = n5 at *
  generalize v12.toNat = n12 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_O2 {v11 v12 v14 : Word}
    (t14 : v14.toNat = v11.toNat + v12.toNat) :
    v14.toNat = v11.toNat + v12.toNat := by
  have := v11.isLt; have := v12.isLt; have := v14.isLt
  generalize v11.toNat = n11 at *
  generalize v12.toNat = n12 at *
  generalize v14.toNat = n14 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_A2 {v14 v16 : Word}
    (t16 : v16.toNat = v14.toNat % 2 ^ 29) :
    v16.toNat = v14.toNat % 2 ^ 29 := by
  have := v14.isLt; have := v16.isLt
  generalize v14.toNat = n14 at *
  generalize v16.toNat = n16 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_SR3 {v5 v17 : Word}
    (t17 : v17.toNat = v5.toNat / 2 ^ 23) :
    v17.toNat = v5.toNat / 2 ^ 23 := by
  have := v5.isLt; have := v17.isLt
  generalize v5.toNat = n5 at *
  generalize v17.toNat = n17 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_SL3 {v6 v18 : Word}
    (t18 : v18.toNat = v6.toNat * 2 ^ 9 % 2 ^ 32) :
    v18.toNat = v6.toNat * 2 ^ 9 % 2 ^ 32 := by
  have := v6.isLt; have := v18.isLt
  generalize v6.toNat = n6 at *
  generalize v18.toNat = n18 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_O3 {v17 v18 v28 : Word}
    (t28 : v28.toNat = v17.toNat + v18.toNat) :
    v28.toNat = v17.toNat + v18.toNat := by
  have := v17.isLt; have := v18.isLt; have := v28.isLt
  generalize v17.toNat = n17 at *
  generalize v18.toNat = n18 at *
  generalize v28.toNat = n28 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_A3 {v28 v36 : Word}
    (t36 : v36.toNat = v28.toNat % 2 ^ 29) :
    v36.toNat = v28.toNat % 2 ^ 29 := by
  have := v28.isLt; have := v36.isLt
  generalize v28.toNat = n28 at *
  generalize v36.toNat = n36 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_SR4 {v6 v29 : Word}
    (t29 : v29.toNat = v6.toNat / 2 ^ 20) :
    v29.toNat = v6.toNat / 2 ^ 20 := by
  have := v6.isLt; have := v29.isLt
  generalize v6.toNat = n6 at *
  generalize v29.toNat = n29 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_SL4 {v19 v35 : Word}
    (t35 : v35.toNat = v19.toNat * 2 ^ 12 % 2 ^ 32) :
    v35.toNat = v19.toNat * 2 ^ 12 % 2 ^ 32 := by
  have := v19.isLt; have := v35.isLt
  generalize v19.toNat = n19 at *
  generalize v35.toNat = n35 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_O4 {v29 v35 v37 : Word}
    (t37 : v37.toNat = v29.toNat + v35.toNat) :
    v37.toNat = v29.toNat + v35.toNat := by
  have := v29.isLt; have := v35.isLt; have := v37.isLt
  generalize v29.toNat = n29 at *
  generalize v35.toNat = n35 at *
  generalize v37.toNat = n37 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_A4 {v37 v87 : Word}
    (t87 : v87.toNat = v37.toNat % 2 ^ 29) :
    v87.toNat = v37.toNat % 2 ^ 29 := by
  have := v37.isLt; have := v87.isLt
  generalize v37.toNat = n37 at *
  generalize v87.toNat = n87 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_SR5 {v19 v163 : Word}
    (t163 : v163.toNat = v19.toNat / 2 ^ 17) :
    v163.toNat = v19.toNat / 2 ^ 17 := by
  have := v19.isLt; have := v163.isLt
  generalize v19.toNat = n19 at *
  generalize v163.toNat = n163 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_SL5 {v30 v167 : Word}
    (t167 : v167.toNat = v30.toNat * 2 ^ 15 % 2 ^ 32) :
    v167.toNat = v30.toNat * 2 ^ 15 % 2 ^ 32 := by
  have := v30.isLt; have := v167.isLt
  generalize v30.toNat = n30 at *
  generalize v167.toNat = n167 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_O5 {v163 v167 v169 : Word}
    (t169 : v169.toNat = v163.toNat + v167.toNat) :
    v169.toNat = v163.toNat + v167.toNat := by
  have := v163.isLt; have := v167.isLt; have := v169.isLt
  generalize v163.toNat = n163 at *
  generalize v167.toNat = n167 at *
  generalize v169.toNat = n169 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_A5 {v169 v173 : Word}
    (t173 : v173.toNat = v169.toNat % 2 ^ 29) :
    v173.toNat = v169.toNat % 2 ^ 29 := by
  have := v169.isLt; have := v173.isLt
  generalize v169.toNat = n169 at *
  generalize v173.toNat = n173 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_SR6 {v30 v175 : Word}
    (t175 : v175.toNat = v30.toNat / 2 ^ 14) :
    v175.toNat = v30.toNat / 2 ^ 14 := by
  have := v30.isLt; have := v175.isLt
  generalize v30.toNat = n30 at *
  generalize v175.toNat = n175 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_SL6 {v31 v180 : Word}
    (t180 : v180.toNat = v31.toNat * 2 ^ 18 % 2 ^ 32) :
    v180.toNat = v31.toNat * 2 ^ 18 % 2 ^ 32 := by
  have := v31.isLt; have := v180.isLt
  generalize v31.toNat = n31 at *
  generalize v180.toNat = n180 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_O6 {v175 v180 v183 : Word}
    (t183 : v183.toNat = v175.toNat + v180.toNat) :
    v183.toNat = v175.toNat + v180.toNat := by
  have := v175.isLt; have := v180.isLt; have := v183.isLt
  generalize v175.toNat = n175 at *
  generalize v180.toNat = n180 at *
  generalize v183.toNat = n183 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_A6 {v183 v185 : Word}
    (t185 : v185.toNat = v183.toNat % 2 ^ 29) :
    v185.toNat = v183.toNat % 2 ^ 29 := by
  have := v183.isLt; have := v185.isLt
  generalize v183.toNat = n183 at *
  generalize v185.toNat = n185 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_SR7 {v31 v236 : Word}
    (t236 : v236.toNat = v31.toNat / 2 ^ 11) :
    v236.toNat = v31.toNat / 2 ^ 11 := by
  have := v31.isLt; have := v236.isLt
  generalize v31.toNat = n31 at *
  generalize v236.toNat = n236 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_SL7 {v33 v243 : Word}
    (t243 : v243.toNat = v33.toNat * 2 ^ 21 % 2 ^ 32) :
    v243.toNat = v33.toNat * 2 ^ 21 % 2 ^ 32 := by
  have := v33.isLt; have := v243.isLt
  generalize v33.toNat = n33 at *
  generalize v243.toNat = n243 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_O7 {v236 v243 v246 : Word}
    (t246 : v246.toNat = v236.toNat + v243.toNat) :
    v246.toNat = v236.toNat + v243.toNat := by
  have := v236.isLt; have := v243.isLt; have := v246.isLt
  generalize v236.toNat = n236 at *
  generalize v243.toNat = n243 at *
  generalize v246.toNat = n246 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_A7 {v246 v254 : Word}
    (t254 : v254.toNat = v246.toNat % 2 ^ 29) :
    v254.toNat = v246.toNat % 2 ^ 29 := by
  have := v246.isLt; have := v254.isLt
  generalize v246.toNat = n246 at *
  generalize v254.toNat = n254 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_A8 {v33 v308 : Word}
    (t308 : v308.toNat = v33.toNat / 2 ^ 8) :
    v308.toNat = v33.toNat / 2 ^ 8 := by
  have := v33.isLt; have := v308.isLt
  generalize v33.toNat = n33 at *
  generalize v308.toNat = n308 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA0B0 {v8 v120 v147 : Word}
    (t120 : v120.toNat = v8.toNat * 290322925 % 2 ^ 32)
    (t147 : v147.toNat = v8.toNat * 290322925 / 2 ^ 32) :
    v120.toNat + 2 ^ 32 * v147.toNat = v8.toNat * (290322925) := by
  have := v8.isLt; have := v120.isLt; have := v147.isLt
  generalize v8.toNat = n8 at *
  generalize v120.toNat = n120 at *
  generalize v147.toNat = n147 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA0B1 {v8 v24 v26 : Word}
    (t24 : v24.toNat = v8.toNat * 442594051 / 2 ^ 32)
    (t26 : v26.toNat = v8.toNat * 442594051 % 2 ^ 32) :
    v26.toNat + 2 ^ 32 * v24.toNat = v8.toNat * (442594051) := by
  have := v8.isLt; have := v24.isLt; have := v26.isLt
  generalize v8.toNat = n8 at *
  generalize v24.toNat = n24 at *
  generalize v26.toNat = n26 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA1B0 {v15 v25 v27 : Word}
    (t25 : v25.toNat = v15.toNat * 290322925 / 2 ^ 32)
    (t27 : v27.toNat = v15.toNat * 290322925 % 2 ^ 32) :
    v27.toNat + 2 ^ 32 * v25.toNat = v15.toNat * (290322925) := by
  have := v15.isLt; have := v25.isLt; have := v27.isLt
  generalize v15.toNat = n15 at *
  generalize v25.toNat = n25 at *
  generalize v27.toNat = n27 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z1 {v24 v25 v26 v27 v38 v40 v43 v51 : Word}
    (t38 : v38.toNat = (v25.toNat + v24.toNat) % 2 ^ 32)
    (t43 : v40.toNat + 2 ^ 32 * v43.toNat = v27.toNat + v26.toNat)
    (t51 : v51.toNat = (v38.toNat + v43.toNat) % 2 ^ 32) :
    v40.toNat + 2 ^ 32 * v51.toNat = ((v26.toNat + 2 ^ 32 * v24.toNat) + (v27.toNat + 2 ^ 32 * v25.toNat)) % 2 ^ 64 := by
  obtain ⟨q38, eq38⟩ := mod_q t38; clear t38
  obtain ⟨q51, eq51⟩ := mod_q t51; clear t51
  have key : v40.toNat + 2 ^ 32 * v51.toNat + 2 ^ 64 * (q38 + q51) = ((v26.toNat + 2 ^ 32 * v24.toNat) + (v27.toNat + 2 ^ 32 * v25.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v24.toNat = n24 at *
    generalize v25.toNat = n25 at *
    generalize v26.toNat = n26 at *
    generalize v27.toNat = n27 at *
    generalize v38.toNat = n38 at *
    generalize v40.toNat = n40 at *
    generalize v43.toNat = n43 at *
    generalize v51.toNat = n51 at *
    omega
  exact smm_key key (smm_lt v40 v51)

set_option maxHeartbeats 10000000 in
theorem evr_v_PA0B2 {v8 v44 v45 : Word}
    (t44 : v44.toNat = v8.toNat * 259787148 % 2 ^ 32)
    (t45 : v45.toNat = v8.toNat * 259787148 / 2 ^ 32) :
    v44.toNat + 2 ^ 32 * v45.toNat = v8.toNat * (259787148) := by
  have := v8.isLt; have := v44.isLt; have := v45.isLt
  generalize v8.toNat = n8 at *
  generalize v44.toNat = n44 at *
  generalize v45.toNat = n45 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA1B1 {v15 v46 v47 : Word}
    (t46 : v46.toNat = v15.toNat * 442594051 % 2 ^ 32)
    (t47 : v47.toNat = v15.toNat * 442594051 / 2 ^ 32) :
    v46.toNat + 2 ^ 32 * v47.toNat = v15.toNat * (442594051) := by
  have := v15.isLt; have := v46.isLt; have := v47.isLt
  generalize v15.toNat = n15 at *
  generalize v46.toNat = n46 at *
  generalize v47.toNat = n47 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA2B0 {v16 v48 v49 : Word}
    (t48 : v48.toNat = v16.toNat * 290322925 / 2 ^ 32)
    (t49 : v49.toNat = v16.toNat * 290322925 % 2 ^ 32) :
    v49.toNat + 2 ^ 32 * v48.toNat = v16.toNat * (290322925) := by
  have := v16.isLt; have := v48.isLt; have := v49.isLt
  generalize v16.toNat = n16 at *
  generalize v48.toNat = n48 at *
  generalize v49.toNat = n49 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z2 {v44 v45 v46 v47 v48 v49 v58 v60 v61 v62 v64 v65 v66 v67 : Word}
    (t60 : v60.toNat = (v45.toNat + v47.toNat) % 2 ^ 32)
    (t61 : v58.toNat + 2 ^ 32 * v61.toNat = v44.toNat + v46.toNat)
    (t64 : v64.toNat = (v60.toNat + v48.toNat) % 2 ^ 32)
    (t65 : v62.toNat + 2 ^ 32 * v65.toNat = v49.toNat + v58.toNat)
    (t66 : v66.toNat = (v61.toNat + v64.toNat) % 2 ^ 32)
    (t67 : v67.toNat = (v65.toNat + v66.toNat) % 2 ^ 32) :
    v62.toNat + 2 ^ 32 * v67.toNat = ((v44.toNat + 2 ^ 32 * v45.toNat) + (v46.toNat + 2 ^ 32 * v47.toNat) + (v49.toNat + 2 ^ 32 * v48.toNat)) % 2 ^ 64 := by
  obtain ⟨q60, eq60⟩ := mod_q t60; clear t60
  obtain ⟨q64, eq64⟩ := mod_q t64; clear t64
  obtain ⟨q66, eq66⟩ := mod_q t66; clear t66
  obtain ⟨q67, eq67⟩ := mod_q t67; clear t67
  have key : v62.toNat + 2 ^ 32 * v67.toNat + 2 ^ 64 * (q60 + q64 + q66 + q67) = ((v44.toNat + 2 ^ 32 * v45.toNat) + (v46.toNat + 2 ^ 32 * v47.toNat) + (v49.toNat + 2 ^ 32 * v48.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v44.toNat = n44 at *
    generalize v45.toNat = n45 at *
    generalize v46.toNat = n46 at *
    generalize v47.toNat = n47 at *
    generalize v48.toNat = n48 at *
    generalize v49.toNat = n49 at *
    generalize v58.toNat = n58 at *
    generalize v60.toNat = n60 at *
    generalize v61.toNat = n61 at *
    generalize v62.toNat = n62 at *
    generalize v64.toNat = n64 at *
    generalize v65.toNat = n65 at *
    generalize v66.toNat = n66 at *
    generalize v67.toNat = n67 at *
    omega
  exact smm_key key (smm_lt v62 v67)

set_option maxHeartbeats 10000000 in
theorem evr_v_PA0B3 {v8 v54 v55 : Word}
    (t54 : v54.toNat = v8.toNat * 377041255 % 2 ^ 32)
    (t55 : v55.toNat = v8.toNat * 377041255 / 2 ^ 32) :
    v54.toNat + 2 ^ 32 * v55.toNat = v8.toNat * (377041255) := by
  have := v8.isLt; have := v54.isLt; have := v55.isLt
  generalize v8.toNat = n8 at *
  generalize v54.toNat = n54 at *
  generalize v55.toNat = n55 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA1B2 {v15 v56 v57 : Word}
    (t56 : v56.toNat = v15.toNat * 259787148 % 2 ^ 32)
    (t57 : v57.toNat = v15.toNat * 259787148 / 2 ^ 32) :
    v56.toNat + 2 ^ 32 * v57.toNat = v15.toNat * (259787148) := by
  have := v15.isLt; have := v56.isLt; have := v57.isLt
  generalize v15.toNat = n15 at *
  generalize v56.toNat = n56 at *
  generalize v57.toNat = n57 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA2B1 {v16 v59 v69 : Word}
    (t59 : v59.toNat = v16.toNat * 442594051 / 2 ^ 32)
    (t69 : v69.toNat = v16.toNat * 442594051 % 2 ^ 32) :
    v69.toNat + 2 ^ 32 * v59.toNat = v16.toNat * (442594051) := by
  have := v16.isLt; have := v59.isLt; have := v69.isLt
  generalize v16.toNat = n16 at *
  generalize v59.toNat = n59 at *
  generalize v69.toNat = n69 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA3B0 {v36 v74 v98 : Word}
    (t74 : v74.toNat = v36.toNat * 290322925 / 2 ^ 32)
    (t98 : v98.toNat = v36.toNat * 290322925 % 2 ^ 32) :
    v98.toNat + 2 ^ 32 * v74.toNat = v36.toNat * (290322925) := by
  have := v36.isLt; have := v74.isLt; have := v98.isLt
  generalize v36.toNat = n36 at *
  generalize v74.toNat = n74 at *
  generalize v98.toNat = n98 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z3 {v54 v55 v56 v57 v59 v69 v70 v71 v72 v74 v80 v81 v82 v84 v86 v88 v98 v111 v115 v122 : Word}
    (t70 : v70.toNat = (v57.toNat + v55.toNat) % 2 ^ 32)
    (t72 : v72.toNat = (v70.toNat + v59.toNat) % 2 ^ 32)
    (t80 : v71.toNat + 2 ^ 32 * v80.toNat = v56.toNat + v54.toNat)
    (t82 : v82.toNat = (v72.toNat + v80.toNat) % 2 ^ 32)
    (t84 : v81.toNat + 2 ^ 32 * v84.toNat = v69.toNat + v71.toNat)
    (t86 : v86.toNat = (v82.toNat + v84.toNat) % 2 ^ 32)
    (t88 : v88.toNat = (v86.toNat + v74.toNat) % 2 ^ 32)
    (t115 : v111.toNat + 2 ^ 32 * v115.toNat = v81.toNat + v98.toNat)
    (t122 : v122.toNat = (v115.toNat + v88.toNat) % 2 ^ 32) :
    v111.toNat + 2 ^ 32 * v122.toNat = ((v54.toNat + 2 ^ 32 * v55.toNat) + (v56.toNat + 2 ^ 32 * v57.toNat) + (v69.toNat + 2 ^ 32 * v59.toNat) + (v98.toNat + 2 ^ 32 * v74.toNat)) % 2 ^ 64 := by
  obtain ⟨q70, eq70⟩ := mod_q t70; clear t70
  obtain ⟨q72, eq72⟩ := mod_q t72; clear t72
  obtain ⟨q82, eq82⟩ := mod_q t82; clear t82
  obtain ⟨q86, eq86⟩ := mod_q t86; clear t86
  obtain ⟨q88, eq88⟩ := mod_q t88; clear t88
  obtain ⟨q122, eq122⟩ := mod_q t122; clear t122
  have key : v111.toNat + 2 ^ 32 * v122.toNat + 2 ^ 64 * (q70 + q72 + q82 + q86 + q88 + q122) = ((v54.toNat + 2 ^ 32 * v55.toNat) + (v56.toNat + 2 ^ 32 * v57.toNat) + (v69.toNat + 2 ^ 32 * v59.toNat) + (v98.toNat + 2 ^ 32 * v74.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v54.toNat = n54 at *
    generalize v55.toNat = n55 at *
    generalize v56.toNat = n56 at *
    generalize v57.toNat = n57 at *
    generalize v59.toNat = n59 at *
    generalize v69.toNat = n69 at *
    generalize v70.toNat = n70 at *
    generalize v71.toNat = n71 at *
    generalize v72.toNat = n72 at *
    generalize v74.toNat = n74 at *
    generalize v80.toNat = n80 at *
    generalize v81.toNat = n81 at *
    generalize v82.toNat = n82 at *
    generalize v84.toNat = n84 at *
    generalize v86.toNat = n86 at *
    generalize v88.toNat = n88 at *
    generalize v98.toNat = n98 at *
    generalize v111.toNat = n111 at *
    generalize v115.toNat = n115 at *
    generalize v122.toNat = n122 at *
    omega
  exact smm_key key (smm_lt v111 v122)

set_option maxHeartbeats 10000000 in
theorem evr_v_PA0B4 {v8 v76 v77 : Word}
    (t76 : v76.toNat = v8.toNat * 536700270 % 2 ^ 32)
    (t77 : v77.toNat = v8.toNat * 536700270 / 2 ^ 32) :
    v76.toNat + 2 ^ 32 * v77.toNat = v8.toNat * (536700270) := by
  have := v8.isLt; have := v76.isLt; have := v77.isLt
  generalize v8.toNat = n8 at *
  generalize v76.toNat = n76 at *
  generalize v77.toNat = n77 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA1B3 {v15 v78 v79 : Word}
    (t78 : v78.toNat = v15.toNat * 377041255 % 2 ^ 32)
    (t79 : v79.toNat = v15.toNat * 377041255 / 2 ^ 32) :
    v78.toNat + 2 ^ 32 * v79.toNat = v15.toNat * (377041255) := by
  have := v15.isLt; have := v78.isLt; have := v79.isLt
  generalize v15.toNat = n15 at *
  generalize v78.toNat = n78 at *
  generalize v79.toNat = n79 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA2B2 {v16 v83 v85 : Word}
    (t83 : v83.toNat = v16.toNat * 259787148 / 2 ^ 32)
    (t85 : v85.toNat = v16.toNat * 259787148 % 2 ^ 32) :
    v85.toNat + 2 ^ 32 * v83.toNat = v16.toNat * (259787148) := by
  have := v16.isLt; have := v83.isLt; have := v85.isLt
  generalize v16.toNat = n16 at *
  generalize v83.toNat = n83 at *
  generalize v85.toNat = n85 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA3B1 {v36 v89 v92 : Word}
    (t89 : v89.toNat = v36.toNat * 442594051 % 2 ^ 32)
    (t92 : v92.toNat = v36.toNat * 442594051 / 2 ^ 32) :
    v89.toNat + 2 ^ 32 * v92.toNat = v36.toNat * (442594051) := by
  have := v36.isLt; have := v89.isLt; have := v92.isLt
  generalize v36.toNat = n36 at *
  generalize v89.toNat = n89 at *
  generalize v92.toNat = n92 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA4B0 {v87 v93 v103 : Word}
    (t93 : v93.toNat = v87.toNat * 290322925 / 2 ^ 32)
    (t103 : v103.toNat = v87.toNat * 290322925 % 2 ^ 32) :
    v103.toNat + 2 ^ 32 * v93.toNat = v87.toNat * (290322925) := by
  have := v87.isLt; have := v93.isLt; have := v103.isLt
  generalize v87.toNat = n87 at *
  generalize v93.toNat = n93 at *
  generalize v103.toNat = n103 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z4 {v76 v77 v78 v79 v83 v85 v89 v90 v91 v92 v93 v94 v95 v96 v97 v99 v100 v101 v102 v103 v104 v105 v114 v116 v119 v124 : Word}
    (t90 : v90.toNat = (v79.toNat + v77.toNat) % 2 ^ 32)
    (t94 : v94.toNat = (v83.toNat + v90.toNat) % 2 ^ 32)
    (t95 : v91.toNat + 2 ^ 32 * v95.toNat = v76.toNat + v78.toNat)
    (t97 : v97.toNat = (v95.toNat + v94.toNat) % 2 ^ 32)
    (t99 : v96.toNat + 2 ^ 32 * v99.toNat = v85.toNat + v91.toNat)
    (t100 : v100.toNat = (v97.toNat + v99.toNat) % 2 ^ 32)
    (t102 : v101.toNat + 2 ^ 32 * v102.toNat = v89.toNat + v96.toNat)
    (t104 : v104.toNat = (v100.toNat + v92.toNat) % 2 ^ 32)
    (t105 : v105.toNat = (v93.toNat + v102.toNat) % 2 ^ 32)
    (t114 : v114.toNat = (v105.toNat + v104.toNat) % 2 ^ 32)
    (t119 : v116.toNat + 2 ^ 32 * v119.toNat = v103.toNat + v101.toNat)
    (t124 : v124.toNat = (v114.toNat + v119.toNat) % 2 ^ 32) :
    v116.toNat + 2 ^ 32 * v124.toNat = ((v76.toNat + 2 ^ 32 * v77.toNat) + (v78.toNat + 2 ^ 32 * v79.toNat) + (v85.toNat + 2 ^ 32 * v83.toNat) + (v89.toNat + 2 ^ 32 * v92.toNat) + (v103.toNat + 2 ^ 32 * v93.toNat)) % 2 ^ 64 := by
  obtain ⟨q90, eq90⟩ := mod_q t90; clear t90
  obtain ⟨q94, eq94⟩ := mod_q t94; clear t94
  obtain ⟨q97, eq97⟩ := mod_q t97; clear t97
  obtain ⟨q100, eq100⟩ := mod_q t100; clear t100
  obtain ⟨q104, eq104⟩ := mod_q t104; clear t104
  obtain ⟨q105, eq105⟩ := mod_q t105; clear t105
  obtain ⟨q114, eq114⟩ := mod_q t114; clear t114
  obtain ⟨q124, eq124⟩ := mod_q t124; clear t124
  have key : v116.toNat + 2 ^ 32 * v124.toNat + 2 ^ 64 * (q105 + q90 + q94 + q97 + q100 + q104 + q114 + q124) = ((v76.toNat + 2 ^ 32 * v77.toNat) + (v78.toNat + 2 ^ 32 * v79.toNat) + (v85.toNat + 2 ^ 32 * v83.toNat) + (v89.toNat + 2 ^ 32 * v92.toNat) + (v103.toNat + 2 ^ 32 * v93.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v76.toNat = n76 at *
    generalize v77.toNat = n77 at *
    generalize v78.toNat = n78 at *
    generalize v79.toNat = n79 at *
    generalize v83.toNat = n83 at *
    generalize v85.toNat = n85 at *
    generalize v89.toNat = n89 at *
    generalize v90.toNat = n90 at *
    generalize v91.toNat = n91 at *
    generalize v92.toNat = n92 at *
    generalize v93.toNat = n93 at *
    generalize v94.toNat = n94 at *
    generalize v95.toNat = n95 at *
    generalize v96.toNat = n96 at *
    generalize v97.toNat = n97 at *
    generalize v99.toNat = n99 at *
    generalize v100.toNat = n100 at *
    generalize v101.toNat = n101 at *
    generalize v102.toNat = n102 at *
    generalize v103.toNat = n103 at *
    generalize v104.toNat = n104 at *
    generalize v105.toNat = n105 at *
    generalize v114.toNat = n114 at *
    generalize v116.toNat = n116 at *
    generalize v119.toNat = n119 at *
    generalize v124.toNat = n124 at *
    omega
  exact smm_key key (smm_lt v116 v124)

set_option maxHeartbeats 10000000 in
theorem evr_v_PA1B4 {v15 v107 v108 : Word}
    (t107 : v107.toNat = v15.toNat * 536700270 % 2 ^ 32)
    (t108 : v108.toNat = v15.toNat * 536700270 / 2 ^ 32) :
    v107.toNat + 2 ^ 32 * v108.toNat = v15.toNat * (536700270) := by
  have := v15.isLt; have := v107.isLt; have := v108.isLt
  generalize v15.toNat = n15 at *
  generalize v107.toNat = n107 at *
  generalize v108.toNat = n108 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA2B3 {v16 v109 v110 : Word}
    (t109 : v109.toNat = v16.toNat * 377041255 % 2 ^ 32)
    (t110 : v110.toNat = v16.toNat * 377041255 / 2 ^ 32) :
    v109.toNat + 2 ^ 32 * v110.toNat = v16.toNat * (377041255) := by
  have := v16.isLt; have := v109.isLt; have := v110.isLt
  generalize v16.toNat = n16 at *
  generalize v109.toNat = n109 at *
  generalize v110.toNat = n110 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA3B2 {v36 v113 v118 : Word}
    (t113 : v113.toNat = v36.toNat * 259787148 / 2 ^ 32)
    (t118 : v118.toNat = v36.toNat * 259787148 % 2 ^ 32) :
    v118.toNat + 2 ^ 32 * v113.toNat = v36.toNat * (259787148) := by
  have := v36.isLt; have := v113.isLt; have := v118.isLt
  generalize v36.toNat = n36 at *
  generalize v113.toNat = n113 at *
  generalize v118.toNat = n118 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA4B1 {v87 v138 v171 : Word}
    (t138 : v138.toNat = v87.toNat * 442594051 / 2 ^ 32)
    (t171 : v171.toNat = v87.toNat * 442594051 % 2 ^ 32) :
    v171.toNat + 2 ^ 32 * v138.toNat = v87.toNat * (442594051) := by
  have := v87.isLt; have := v138.isLt; have := v171.isLt
  generalize v87.toNat = n87 at *
  generalize v138.toNat = n138 at *
  generalize v171.toNat = n171 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA2B4 {v16 v140 v141 : Word}
    (t140 : v140.toNat = v16.toNat * 536700270 % 2 ^ 32)
    (t141 : v141.toNat = v16.toNat * 536700270 / 2 ^ 32) :
    v140.toNat + 2 ^ 32 * v141.toNat = v16.toNat * (536700270) := by
  have := v16.isLt; have := v140.isLt; have := v141.isLt
  generalize v16.toNat = n16 at *
  generalize v140.toNat = n140 at *
  generalize v141.toNat = n141 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA3B3 {v36 v142 v143 : Word}
    (t142 : v142.toNat = v36.toNat * 377041255 / 2 ^ 32)
    (t143 : v143.toNat = v36.toNat * 377041255 % 2 ^ 32) :
    v143.toNat + 2 ^ 32 * v142.toNat = v36.toNat * (377041255) := by
  have := v36.isLt; have := v142.isLt; have := v143.isLt
  generalize v36.toNat = n36 at *
  generalize v142.toNat = n142 at *
  generalize v143.toNat = n143 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA4B2 {v87 v144 v146 : Word}
    (t144 : v144.toNat = v87.toNat * 259787148 / 2 ^ 32)
    (t146 : v146.toNat = v87.toNat * 259787148 % 2 ^ 32) :
    v146.toNat + 2 ^ 32 * v144.toNat = v87.toNat * (259787148) := by
  have := v87.isLt; have := v144.isLt; have := v146.isLt
  generalize v87.toNat = n87 at *
  generalize v144.toNat = n144 at *
  generalize v146.toNat = n146 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z6a {v140 v141 v142 v143 v144 v146 v155 v156 v157 v158 v159 v160 v161 v162 : Word}
    (t155 : v155.toNat = (v141.toNat + v142.toNat) % 2 ^ 32)
    (t156 : v156.toNat = (v144.toNat + v155.toNat) % 2 ^ 32)
    (t158 : v157.toNat + 2 ^ 32 * v158.toNat = v140.toNat + v143.toNat)
    (t160 : v160.toNat = (v158.toNat + v156.toNat) % 2 ^ 32)
    (t161 : v159.toNat + 2 ^ 32 * v161.toNat = v146.toNat + v157.toNat)
    (t162 : v162.toNat = (v161.toNat + v160.toNat) % 2 ^ 32) :
    v159.toNat + 2 ^ 32 * v162.toNat = ((v140.toNat + 2 ^ 32 * v141.toNat) + (v143.toNat + 2 ^ 32 * v142.toNat) + (v146.toNat + 2 ^ 32 * v144.toNat)) % 2 ^ 64 := by
  obtain ⟨q155, eq155⟩ := mod_q t155; clear t155
  obtain ⟨q156, eq156⟩ := mod_q t156; clear t156
  obtain ⟨q160, eq160⟩ := mod_q t160; clear t160
  obtain ⟨q162, eq162⟩ := mod_q t162; clear t162
  have key : v159.toNat + 2 ^ 32 * v162.toNat + 2 ^ 64 * (q155 + q156 + q160 + q162) = ((v140.toNat + 2 ^ 32 * v141.toNat) + (v143.toNat + 2 ^ 32 * v142.toNat) + (v146.toNat + 2 ^ 32 * v144.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v140.toNat = n140 at *
    generalize v141.toNat = n141 at *
    generalize v142.toNat = n142 at *
    generalize v143.toNat = n143 at *
    generalize v144.toNat = n144 at *
    generalize v146.toNat = n146 at *
    generalize v155.toNat = n155 at *
    generalize v156.toNat = n156 at *
    generalize v157.toNat = n157 at *
    generalize v158.toNat = n158 at *
    generalize v159.toNat = n159 at *
    generalize v160.toNat = n160 at *
    generalize v161.toNat = n161 at *
    generalize v162.toNat = n162 at *
    omega
  exact smm_key key (smm_lt v159 v162)

set_option maxHeartbeats 10000000 in
theorem evr_v_PA3B4 {v36 v215 v250 : Word}
    (t215 : v215.toNat = v36.toNat * 536700270 / 2 ^ 32)
    (t250 : v250.toNat = v36.toNat * 536700270 % 2 ^ 32) :
    v250.toNat + 2 ^ 32 * v215.toNat = v36.toNat * (536700270) := by
  have := v36.isLt; have := v215.isLt; have := v250.isLt
  generalize v36.toNat = n36 at *
  generalize v215.toNat = n215 at *
  generalize v250.toNat = n250 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA4B3 {v87 v216 v248 : Word}
    (t216 : v216.toNat = v87.toNat * 377041255 / 2 ^ 32)
    (t248 : v248.toNat = v87.toNat * 377041255 % 2 ^ 32) :
    v248.toNat + 2 ^ 32 * v216.toNat = v87.toNat * (377041255) := by
  have := v87.isLt; have := v216.isLt; have := v248.isLt
  generalize v87.toNat = n87 at *
  generalize v216.toNat = n216 at *
  generalize v248.toNat = n248 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z7a {v215 v216 v234 v248 v250 v266 v268 v270 : Word}
    (t234 : v234.toNat = (v216.toNat + v215.toNat) % 2 ^ 32)
    (t268 : v266.toNat + 2 ^ 32 * v268.toNat = v250.toNat + v248.toNat)
    (t270 : v270.toNat = (v268.toNat + v234.toNat) % 2 ^ 32) :
    v266.toNat + 2 ^ 32 * v270.toNat = ((v250.toNat + 2 ^ 32 * v215.toNat) + (v248.toNat + 2 ^ 32 * v216.toNat)) % 2 ^ 64 := by
  obtain ⟨q234, eq234⟩ := mod_q t234; clear t234
  obtain ⟨q270, eq270⟩ := mod_q t270; clear t270
  have key : v266.toNat + 2 ^ 32 * v270.toNat + 2 ^ 64 * (q234 + q270) = ((v250.toNat + 2 ^ 32 * v215.toNat) + (v248.toNat + 2 ^ 32 * v216.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v215.toNat = n215 at *
    generalize v216.toNat = n216 at *
    generalize v234.toNat = n234 at *
    generalize v248.toNat = n248 at *
    generalize v250.toNat = n250 at *
    generalize v266.toNat = n266 at *
    generalize v268.toNat = n268 at *
    generalize v270.toNat = n270 at *
    omega
  exact smm_key key (smm_lt v266 v270)

set_option maxHeartbeats 10000000 in
theorem evr_v_PA4B4 {v87 v699 v700 : Word}
    (t699 : v699.toNat = v87.toNat * 536700270 % 2 ^ 32)
    (t700 : v700.toNat = v87.toNat * 536700270 / 2 ^ 32) :
    v699.toNat + 2 ^ 32 * v700.toNat = v87.toNat * (536700270) := by
  have := v87.isLt; have := v699.isLt; have := v700.isLt
  generalize v87.toNat = n87 at *
  generalize v699.toNat = n699 at *
  generalize v700.toNat = n700 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z8a {v111 v122 v699 v700 v740 v742 v747 v748 : Word}
    (t740 : v748.toNat + v111.toNat = v699.toNat + 2 ^ 32 * v740.toNat)
    (t742 : v742.toNat = (v700.toNat + 2 ^ 32 - v740.toNat) % 2 ^ 32)
    (t747 : v747.toNat = (v742.toNat + 2 ^ 32 - v122.toNat) % 2 ^ 32) :
    v748.toNat + 2 ^ 32 * v747.toNat = ((v699.toNat + 2 ^ 32 * v700.toNat) + (2 ^ 64 - (v111.toNat + 2 ^ 32 * v122.toNat))) % 2 ^ 64 := by
  obtain ⟨q742, eq742⟩ := mod_q t742; clear t742
  obtain ⟨q747, eq747⟩ := mod_q t747; clear t747
  have key : v748.toNat + 2 ^ 32 * v747.toNat + 2 ^ 64 * (q742 + q747) = ((v699.toNat + 2 ^ 32 * v700.toNat) + (2 ^ 64 - (v111.toNat + 2 ^ 32 * v122.toNat))) + 2 ^ 64 * (1) := by
    have := v111.isLt; have := v122.isLt; have := v740.isLt; skip
    generalize v111.toNat = n111 at *
    generalize v122.toNat = n122 at *
    generalize v699.toNat = n699 at *
    generalize v700.toNat = n700 at *
    generalize v740.toNat = n740 at *
    generalize v742.toNat = n742 at *
    generalize v747.toNat = n747 at *
    generalize v748.toNat = n748 at *
    omega
  exact smm_key key (smm_lt v748 v747)

set_option maxHeartbeats 10000000 in
theorem evr_v_PA5B5 {v19 v30 v163 v167 v169 v173 v181 v188 v194 : Word}
    (t181 : v181.toNat = v173.toNat * 536870911 / 2 ^ 32)
    (t188 : v188.toNat = v163.toNat * 2 ^ 29 % 2 ^ 32)
    (t194 : v194.toNat = (v188.toNat + 2 ^ 32 - v173.toNat) % 2 ^ 32)
    (wA5 : v173.toNat = v169.toNat % 2 ^ 29)
    (wO5 : v169.toNat = v163.toNat + v167.toNat)
    (wSR5 : v163.toNat = v19.toNat / 2 ^ 17)
    (wSL5 : v167.toNat = v30.toNat * 2 ^ 15 % 2 ^ 32) :
    v194.toNat + 2 ^ 32 * v181.toNat = v173.toNat * (536870911) := by
  have := v19.isLt; have := v30.isLt; have := v163.isLt; have := v167.isLt; have := v169.isLt; have := v173.isLt; have := v181.isLt; have := v188.isLt; have := v194.isLt
  generalize v19.toNat = n19 at *
  generalize v30.toNat = n30 at *
  generalize v163.toNat = n163 at *
  generalize v167.toNat = n167 at *
  generalize v169.toNat = n169 at *
  generalize v173.toNat = n173 at *
  generalize v181.toNat = n181 at *
  generalize v188.toNat = n188 at *
  generalize v194.toNat = n194 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z10a {v107 v108 v109 v110 v113 v118 v126 v127 v128 v129 v130 v132 v134 v138 v145 v154 v171 v181 v186 v187 v194 v196 v201 v202 v203 v206 : Word}
    (t126 : v126.toNat = (v108.toNat + v110.toNat) % 2 ^ 32)
    (t128 : v128.toNat = (v113.toNat + v126.toNat) % 2 ^ 32)
    (t129 : v127.toNat + 2 ^ 32 * v129.toNat = v109.toNat + v107.toNat)
    (t130 : v130.toNat = (v128.toNat + v129.toNat) % 2 ^ 32)
    (t134 : v132.toNat + 2 ^ 32 * v134.toNat = v127.toNat + v118.toNat)
    (t145 : v145.toNat = (v134.toNat + v130.toNat) % 2 ^ 32)
    (t154 : v154.toNat = (v138.toNat + v145.toNat) % 2 ^ 32)
    (t187 : v186.toNat + 2 ^ 32 * v187.toNat = v171.toNat + v132.toNat)
    (t196 : v196.toNat = (v187.toNat + 2 ^ 32 - v181.toNat) % 2 ^ 32)
    (t201 : v201.toNat = (v196.toNat + v154.toNat) % 2 ^ 32)
    (t202 : v206.toNat + v194.toNat = v186.toNat + 2 ^ 32 * v202.toNat)
    (t203 : v203.toNat = (v201.toNat + 2 ^ 32 - v202.toNat) % 2 ^ 32) :
    v206.toNat + 2 ^ 32 * v203.toNat = ((((v107.toNat + 2 ^ 32 * v108.toNat) + (v109.toNat + 2 ^ 32 * v110.toNat) + (v118.toNat + 2 ^ 32 * v113.toNat) + (v171.toNat + 2 ^ 32 * v138.toNat)) % 2 ^ 64) + (2 ^ 64 - (v194.toNat + 2 ^ 32 * v181.toNat))) % 2 ^ 64 := by
  obtain ⟨q126, eq126⟩ := mod_q t126; clear t126
  obtain ⟨q128, eq128⟩ := mod_q t128; clear t128
  obtain ⟨q130, eq130⟩ := mod_q t130; clear t130
  obtain ⟨q145, eq145⟩ := mod_q t145; clear t145
  obtain ⟨q154, eq154⟩ := mod_q t154; clear t154
  obtain ⟨q196, eq196⟩ := mod_q t196; clear t196
  obtain ⟨q201, eq201⟩ := mod_q t201; clear t201
  obtain ⟨q203, eq203⟩ := mod_q t203; clear t203
  obtain ⟨k0, ek0⟩ : ∃ k, ((v107.toNat + 2 ^ 32 * v108.toNat) + (v109.toNat + 2 ^ 32 * v110.toNat) + (v118.toNat + 2 ^ 32 * v113.toNat) + (v171.toNat + 2 ^ 32 * v138.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v107.toNat + 2 ^ 32 * v108.toNat) + (v109.toNat + 2 ^ 32 * v110.toNat) + (v118.toNat + 2 ^ 32 * v113.toNat) + (v171.toNat + 2 ^ 32 * v138.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v206.toNat + 2 ^ 32 * v203.toNat + 2 ^ 64 * (q196 + q126 + q128 + q130 + q145 + q154 + q201 + q203) = ((((v107.toNat + 2 ^ 32 * v108.toNat) + (v109.toNat + 2 ^ 32 * v110.toNat) + (v118.toNat + 2 ^ 32 * v113.toNat) + (v171.toNat + 2 ^ 32 * v138.toNat)) % 2 ^ 64) + (2 ^ 64 - (v194.toNat + 2 ^ 32 * v181.toNat))) + 2 ^ 64 * (k0 + 1) := by
    have := v181.isLt; have := v194.isLt; have := v202.isLt; skip
    generalize v107.toNat = n107 at *
    generalize v108.toNat = n108 at *
    generalize v109.toNat = n109 at *
    generalize v110.toNat = n110 at *
    generalize v113.toNat = n113 at *
    generalize v118.toNat = n118 at *
    generalize v126.toNat = n126 at *
    generalize v127.toNat = n127 at *
    generalize v128.toNat = n128 at *
    generalize v129.toNat = n129 at *
    generalize v130.toNat = n130 at *
    generalize v132.toNat = n132 at *
    generalize v134.toNat = n134 at *
    generalize v138.toNat = n138 at *
    generalize v145.toNat = n145 at *
    generalize v154.toNat = n154 at *
    generalize v171.toNat = n171 at *
    generalize v181.toNat = n181 at *
    generalize v186.toNat = n186 at *
    generalize v187.toNat = n187 at *
    generalize v194.toNat = n194 at *
    generalize v196.toNat = n196 at *
    generalize v201.toNat = n201 at *
    generalize v202.toNat = n202 at *
    generalize v203.toNat = n203 at *
    generalize v206.toNat = n206 at *
    omega
  exact smm_key key (smm_lt v206 v203)

set_option maxHeartbeats 10000000 in
theorem evr_v_PA5B6 {v19 v30 v163 v167 v169 v173 v181 v188 v194 : Word}
    (t181 : v181.toNat = v173.toNat * 536870911 / 2 ^ 32)
    (t188 : v188.toNat = v163.toNat * 2 ^ 29 % 2 ^ 32)
    (t194 : v194.toNat = (v188.toNat + 2 ^ 32 - v173.toNat) % 2 ^ 32)
    (wA5 : v173.toNat = v169.toNat % 2 ^ 29)
    (wO5 : v169.toNat = v163.toNat + v167.toNat)
    (wSR5 : v163.toNat = v19.toNat / 2 ^ 17)
    (wSL5 : v167.toNat = v30.toNat * 2 ^ 15 % 2 ^ 32) :
    v194.toNat + 2 ^ 32 * v181.toNat = v173.toNat * (536870911) := by
  have := v19.isLt; have := v30.isLt; have := v163.isLt; have := v167.isLt; have := v169.isLt; have := v173.isLt; have := v181.isLt; have := v188.isLt; have := v194.isLt
  generalize v19.toNat = n19 at *
  generalize v30.toNat = n30 at *
  generalize v163.toNat = n163 at *
  generalize v167.toNat = n167 at *
  generalize v169.toNat = n169 at *
  generalize v173.toNat = n173 at *
  generalize v181.toNat = n181 at *
  generalize v188.toNat = n188 at *
  generalize v194.toNat = n194 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA6B5 {v30 v31 v175 v180 v183 v185 v189 v208 v209 : Word}
    (t189 : v189.toNat = v185.toNat * 536870911 / 2 ^ 32)
    (t208 : v208.toNat = v175.toNat * 2 ^ 29 % 2 ^ 32)
    (t209 : v209.toNat = (v208.toNat + 2 ^ 32 - v185.toNat) % 2 ^ 32)
    (wA6 : v185.toNat = v183.toNat % 2 ^ 29)
    (wO6 : v183.toNat = v175.toNat + v180.toNat)
    (wSR6 : v175.toNat = v30.toNat / 2 ^ 14)
    (wSL6 : v180.toNat = v31.toNat * 2 ^ 18 % 2 ^ 32) :
    v209.toNat + 2 ^ 32 * v189.toNat = v185.toNat * (536870911) := by
  have := v30.isLt; have := v31.isLt; have := v175.isLt; have := v180.isLt; have := v183.isLt; have := v185.isLt; have := v189.isLt; have := v208.isLt; have := v209.isLt
  generalize v30.toNat = n30 at *
  generalize v31.toNat = n31 at *
  generalize v175.toNat = n175 at *
  generalize v180.toNat = n180 at *
  generalize v183.toNat = n183 at *
  generalize v185.toNat = n185 at *
  generalize v189.toNat = n189 at *
  generalize v208.toNat = n208 at *
  generalize v209.toNat = n209 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Q11 {v181 v189 v194 v209 v210 v211 v220 v222 : Word}
    (t210 : v210.toNat = (v189.toNat + v181.toNat) % 2 ^ 32)
    (t220 : v211.toNat + 2 ^ 32 * v220.toNat = v209.toNat + v194.toNat)
    (t222 : v222.toNat = (v210.toNat + v220.toNat) % 2 ^ 32) :
    v211.toNat + 2 ^ 32 * v222.toNat = ((v194.toNat + 2 ^ 32 * v181.toNat) + (v209.toNat + 2 ^ 32 * v189.toNat)) % 2 ^ 64 := by
  obtain ⟨q210, eq210⟩ := mod_q t210; clear t210
  obtain ⟨q222, eq222⟩ := mod_q t222; clear t222
  have key : v211.toNat + 2 ^ 32 * v222.toNat + 2 ^ 64 * (q210 + q222) = ((v194.toNat + 2 ^ 32 * v181.toNat) + (v209.toNat + 2 ^ 32 * v189.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v181.toNat = n181 at *
    generalize v189.toNat = n189 at *
    generalize v194.toNat = n194 at *
    generalize v209.toNat = n209 at *
    generalize v210.toNat = n210 at *
    generalize v211.toNat = n211 at *
    generalize v220.toNat = n220 at *
    generalize v222.toNat = n222 at *
    omega
  exact smm_key key (smm_lt v211 v222)

set_option maxHeartbeats 10000000 in
theorem evr_v_Z11a {v159 v162 v211 v222 v228 v229 v231 v274 : Word}
    (t228 : v274.toNat + v211.toNat = v159.toNat + 2 ^ 32 * v228.toNat)
    (t229 : v229.toNat = (v228.toNat + v222.toNat) % 2 ^ 32)
    (t231 : v231.toNat = (v162.toNat + 2 ^ 32 - v229.toNat) % 2 ^ 32) :
    v274.toNat + 2 ^ 32 * v231.toNat = ((v159.toNat + 2 ^ 32 * v162.toNat) + (2 ^ 64 - (v211.toNat + 2 ^ 32 * v222.toNat))) % 2 ^ 64 := by
  obtain ⟨q229, eq229⟩ := mod_q t229; clear t229
  obtain ⟨q231, eq231⟩ := mod_q t231; clear t231
  have key : v274.toNat + 2 ^ 32 * v231.toNat + 2 ^ 64 * (q231) = ((v159.toNat + 2 ^ 32 * v162.toNat) + (2 ^ 64 - (v211.toNat + 2 ^ 32 * v222.toNat))) + 2 ^ 64 * (q229) := by
    have := v211.isLt; have := v222.isLt; have := v229.isLt; skip
    generalize v159.toNat = n159 at *
    generalize v162.toNat = n162 at *
    generalize v211.toNat = n211 at *
    generalize v222.toNat = n222 at *
    generalize v228.toNat = n228 at *
    generalize v229.toNat = n229 at *
    generalize v231.toNat = n231 at *
    generalize v274.toNat = n274 at *
    omega
  exact smm_key key (smm_lt v274 v231)

set_option maxHeartbeats 10000000 in
theorem evr_v_PA7B5 {v31 v33 v236 v243 v246 v254 v255 v260 v261 : Word}
    (t255 : v255.toNat = v254.toNat * 536870911 / 2 ^ 32)
    (t260 : v260.toNat = v236.toNat * 2 ^ 29 % 2 ^ 32)
    (t261 : v261.toNat = (v260.toNat + 2 ^ 32 - v254.toNat) % 2 ^ 32)
    (wA7 : v254.toNat = v246.toNat % 2 ^ 29)
    (wO7 : v246.toNat = v236.toNat + v243.toNat)
    (wSR7 : v236.toNat = v31.toNat / 2 ^ 11)
    (wSL7 : v243.toNat = v33.toNat * 2 ^ 21 % 2 ^ 32) :
    v261.toNat + 2 ^ 32 * v255.toNat = v254.toNat * (536870911) := by
  have := v31.isLt; have := v33.isLt; have := v236.isLt; have := v243.isLt; have := v246.isLt; have := v254.isLt; have := v255.isLt; have := v260.isLt; have := v261.isLt
  generalize v31.toNat = n31 at *
  generalize v33.toNat = n33 at *
  generalize v236.toNat = n236 at *
  generalize v243.toNat = n243 at *
  generalize v246.toNat = n246 at *
  generalize v254.toNat = n254 at *
  generalize v255.toNat = n255 at *
  generalize v260.toNat = n260 at *
  generalize v261.toNat = n261 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Q12 {v211 v222 v255 v261 v267 v269 v271 v272 : Word}
    (t269 : v267.toNat + 2 ^ 32 * v269.toNat = v261.toNat + v211.toNat)
    (t271 : v271.toNat = (v269.toNat + v255.toNat) % 2 ^ 32)
    (t272 : v272.toNat = (v271.toNat + v222.toNat) % 2 ^ 32) :
    v267.toNat + 2 ^ 32 * v272.toNat = ((v211.toNat + 2 ^ 32 * v222.toNat) + (v261.toNat + 2 ^ 32 * v255.toNat)) % 2 ^ 64 := by
  obtain ⟨q271, eq271⟩ := mod_q t271; clear t271
  obtain ⟨q272, eq272⟩ := mod_q t272; clear t272
  have key : v267.toNat + 2 ^ 32 * v272.toNat + 2 ^ 64 * (q271 + q272) = ((v211.toNat + 2 ^ 32 * v222.toNat) + (v261.toNat + 2 ^ 32 * v255.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v211.toNat = n211 at *
    generalize v222.toNat = n222 at *
    generalize v255.toNat = n255 at *
    generalize v261.toNat = n261 at *
    generalize v267.toNat = n267 at *
    generalize v269.toNat = n269 at *
    generalize v271.toNat = n271 at *
    generalize v272.toNat = n272 at *
    omega
  exact smm_key key (smm_lt v267 v272)

end C3.RV32
