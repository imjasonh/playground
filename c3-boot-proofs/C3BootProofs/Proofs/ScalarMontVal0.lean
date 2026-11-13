import C3BootProofs.Proofs.ScalarMontFacts

/-! # `montgomery_mul`'s values, part 0

Each lemma proves one value the code holds in words from its instructions' facts. `scripts/gen-scalar-mont.py` writes this file. -/

namespace C3.RV32

open C3.Image

theorem smm_v_PA0B0 {v4 v6 v193 v232 : Word}
    (t193 : v193.toNat = v6.toNat * v4.toNat % 2 ^ 32)
    (t232 : v232.toNat = v6.toNat * v4.toNat / 2 ^ 32) :
    v193.toNat + 2 ^ 32 * v232.toNat = v4.toNat * v6.toNat := by
  have := Nat.mul_comm v4.toNat v6.toNat
  have := v4.isLt; have := v6.isLt; have := v193.isLt; have := v232.isLt
  generalize v4.toNat = n4 at *
  generalize v6.toNat = n6 at *
  generalize v193.toNat = n193 at *
  generalize v232.toNat = n232 at *
  omega

theorem smm_v_PA0B1 {v3 v4 v11 v12 : Word}
    (t11 : v11.toNat = v3.toNat * v4.toNat % 2 ^ 32)
    (t12 : v12.toNat = v3.toNat * v4.toNat / 2 ^ 32) :
    v11.toNat + 2 ^ 32 * v12.toNat = v4.toNat * v3.toNat := by
  have := Nat.mul_comm v3.toNat v4.toNat
  have := v3.isLt; have := v4.isLt; have := v11.isLt; have := v12.isLt
  generalize v3.toNat = n3 at *
  generalize v4.toNat = n4 at *
  generalize v11.toNat = n11 at *
  generalize v12.toNat = n12 at *
  omega

theorem smm_v_PA1B0 {v5 v6 v13 v14 : Word}
    (t13 : v13.toNat = v5.toNat * v6.toNat % 2 ^ 32)
    (t14 : v14.toNat = v5.toNat * v6.toNat / 2 ^ 32) :
    v13.toNat + 2 ^ 32 * v14.toNat = v5.toNat * v6.toNat := by
  have := v5.isLt; have := v6.isLt; have := v13.isLt; have := v14.isLt
  generalize v5.toNat = n5 at *
  generalize v6.toNat = n6 at *
  generalize v13.toNat = n13 at *
  generalize v14.toNat = n14 at *
  omega

theorem smm_v_Z1 {v11 v12 v13 v14 v20 v21 v26 v28 : Word}
    (t20 : v20.toNat = (v12.toNat + v14.toNat) % 2 ^ 32)
    (t26 : v21.toNat + 2 ^ 32 * v26.toNat = v11.toNat + v13.toNat)
    (t28 : v28.toNat = (v20.toNat + v26.toNat) % 2 ^ 32) :
    v21.toNat + 2 ^ 32 * v28.toNat = ((v11.toNat + 2 ^ 32 * v12.toNat) + (v13.toNat + 2 ^ 32 * v14.toNat)) % 2 ^ 64 := by
  obtain ⟨q20, eq20⟩ := mod_q t20; clear t20
  obtain ⟨q28, eq28⟩ := mod_q t28; clear t28
  have key : v21.toNat + 2 ^ 32 * v28.toNat + 2 ^ 64 * (q20 + q28) = ((v11.toNat + 2 ^ 32 * v12.toNat) + (v13.toNat + 2 ^ 32 * v14.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v11.toNat = n11 at *
    generalize v12.toNat = n12 at *
    generalize v13.toNat = n13 at *
    generalize v14.toNat = n14 at *
    generalize v20.toNat = n20 at *
    generalize v21.toNat = n21 at *
    generalize v26.toNat = n26 at *
    generalize v28.toNat = n28 at *
    omega
  exact smm_key key (smm_lt v21 v28)

theorem smm_v_PA0B2 {v4 v7 v15 v17 : Word}
    (t15 : v15.toNat = v7.toNat * v4.toNat / 2 ^ 32)
    (t17 : v17.toNat = v7.toNat * v4.toNat % 2 ^ 32) :
    v17.toNat + 2 ^ 32 * v15.toNat = v4.toNat * v7.toNat := by
  have := Nat.mul_comm v4.toNat v7.toNat
  have := v4.isLt; have := v7.isLt; have := v15.isLt; have := v17.isLt
  generalize v4.toNat = n4 at *
  generalize v7.toNat = n7 at *
  generalize v15.toNat = n15 at *
  generalize v17.toNat = n17 at *
  omega

theorem smm_v_PA1B1 {v3 v5 v16 v18 : Word}
    (t16 : v16.toNat = v5.toNat * v3.toNat / 2 ^ 32)
    (t18 : v18.toNat = v5.toNat * v3.toNat % 2 ^ 32) :
    v18.toNat + 2 ^ 32 * v16.toNat = v5.toNat * v3.toNat := by
  have := v3.isLt; have := v5.isLt; have := v16.isLt; have := v18.isLt
  generalize v3.toNat = n3 at *
  generalize v5.toNat = n5 at *
  generalize v16.toNat = n16 at *
  generalize v18.toNat = n18 at *
  omega

theorem smm_v_PA2B0 {v6 v9 v19 v25 : Word}
    (t19 : v19.toNat = v9.toNat * v6.toNat % 2 ^ 32)
    (t25 : v25.toNat = v9.toNat * v6.toNat / 2 ^ 32) :
    v19.toNat + 2 ^ 32 * v25.toNat = v9.toNat * v6.toNat := by
  have := v6.isLt; have := v9.isLt; have := v19.isLt; have := v25.isLt
  generalize v6.toNat = n6 at *
  generalize v9.toNat = n9 at *
  generalize v19.toNat = n19 at *
  generalize v25.toNat = n25 at *
  omega

theorem smm_v_Z2 {v15 v16 v17 v18 v19 v23 v24 v25 v35 v36 v38 v39 v40 v52 : Word}
    (t23 : v23.toNat = (v15.toNat + v16.toNat) % 2 ^ 32)
    (t35 : v24.toNat + 2 ^ 32 * v35.toNat = v18.toNat + v17.toNat)
    (t38 : v36.toNat + 2 ^ 32 * v38.toNat = v19.toNat + v24.toNat)
    (t39 : v39.toNat = (v25.toNat + v23.toNat) % 2 ^ 32)
    (t40 : v40.toNat = (v39.toNat + v35.toNat) % 2 ^ 32)
    (t52 : v52.toNat = (v40.toNat + v38.toNat) % 2 ^ 32) :
    v36.toNat + 2 ^ 32 * v52.toNat = ((v17.toNat + 2 ^ 32 * v15.toNat) + (v18.toNat + 2 ^ 32 * v16.toNat) + (v19.toNat + 2 ^ 32 * v25.toNat)) % 2 ^ 64 := by
  obtain ⟨q23, eq23⟩ := mod_q t23; clear t23
  obtain ⟨q39, eq39⟩ := mod_q t39; clear t39
  obtain ⟨q40, eq40⟩ := mod_q t40; clear t40
  obtain ⟨q52, eq52⟩ := mod_q t52; clear t52
  have key : v36.toNat + 2 ^ 32 * v52.toNat + 2 ^ 64 * (q23 + q39 + q40 + q52) = ((v17.toNat + 2 ^ 32 * v15.toNat) + (v18.toNat + 2 ^ 32 * v16.toNat) + (v19.toNat + 2 ^ 32 * v25.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v15.toNat = n15 at *
    generalize v16.toNat = n16 at *
    generalize v17.toNat = n17 at *
    generalize v18.toNat = n18 at *
    generalize v19.toNat = n19 at *
    generalize v23.toNat = n23 at *
    generalize v24.toNat = n24 at *
    generalize v25.toNat = n25 at *
    generalize v35.toNat = n35 at *
    generalize v36.toNat = n36 at *
    generalize v38.toNat = n38 at *
    generalize v39.toNat = n39 at *
    generalize v40.toNat = n40 at *
    generalize v52.toNat = n52 at *
    omega
  exact smm_key key (smm_lt v36 v52)

theorem smm_v_PA0B3 {v4 v8 v33 v34 : Word}
    (t33 : v33.toNat = v8.toNat * v4.toNat / 2 ^ 32)
    (t34 : v34.toNat = v8.toNat * v4.toNat % 2 ^ 32) :
    v34.toNat + 2 ^ 32 * v33.toNat = v4.toNat * v8.toNat := by
  have := Nat.mul_comm v4.toNat v8.toNat
  have := v4.isLt; have := v8.isLt; have := v33.isLt; have := v34.isLt
  generalize v4.toNat = n4 at *
  generalize v8.toNat = n8 at *
  generalize v33.toNat = n33 at *
  generalize v34.toNat = n34 at *
  omega

theorem smm_v_PA1B2 {v5 v7 v27 v31 : Word}
    (t27 : v27.toNat = v7.toNat * v5.toNat % 2 ^ 32)
    (t31 : v31.toNat = v7.toNat * v5.toNat / 2 ^ 32) :
    v27.toNat + 2 ^ 32 * v31.toNat = v5.toNat * v7.toNat := by
  have := Nat.mul_comm v5.toNat v7.toNat
  have := v5.isLt; have := v7.isLt; have := v27.isLt; have := v31.isLt
  generalize v5.toNat = n5 at *
  generalize v7.toNat = n7 at *
  generalize v27.toNat = n27 at *
  generalize v31.toNat = n31 at *
  omega

theorem smm_v_PA2B1 {v3 v9 v30 v32 : Word}
    (t30 : v30.toNat = v9.toNat * v3.toNat % 2 ^ 32)
    (t32 : v32.toNat = v9.toNat * v3.toNat / 2 ^ 32) :
    v30.toNat + 2 ^ 32 * v32.toNat = v9.toNat * v3.toNat := by
  have := v3.isLt; have := v9.isLt; have := v30.isLt; have := v32.isLt
  generalize v3.toNat = n3 at *
  generalize v9.toNat = n9 at *
  generalize v30.toNat = n30 at *
  generalize v32.toNat = n32 at *
  omega

theorem smm_v_PA3B0 {v6 v10 v41 v42 : Word}
    (t41 : v41.toNat = v10.toNat * v6.toNat % 2 ^ 32)
    (t42 : v42.toNat = v10.toNat * v6.toNat / 2 ^ 32) :
    v41.toNat + 2 ^ 32 * v42.toNat = v10.toNat * v6.toNat := by
  have := v6.isLt; have := v10.isLt; have := v41.isLt; have := v42.isLt
  generalize v6.toNat = n6 at *
  generalize v10.toNat = n10 at *
  generalize v41.toNat = n41 at *
  generalize v42.toNat = n42 at *
  omega

theorem smm_v_Z3 {v27 v30 v31 v32 v33 v34 v41 v42 v43 v44 v45 v46 v47 v48 v49 v54 v55 v62 v63 v90 : Word}
    (t44 : v44.toNat = (v31.toNat + v32.toNat) % 2 ^ 32)
    (t45 : v43.toNat + 2 ^ 32 * v45.toNat = v27.toNat + v30.toNat)
    (t47 : v47.toNat = (v44.toNat + v33.toNat) % 2 ^ 32)
    (t48 : v46.toNat + 2 ^ 32 * v48.toNat = v34.toNat + v43.toNat)
    (t49 : v49.toNat = (v45.toNat + v47.toNat) % 2 ^ 32)
    (t54 : v54.toNat = (v49.toNat + v48.toNat) % 2 ^ 32)
    (t62 : v62.toNat = (v42.toNat + v54.toNat) % 2 ^ 32)
    (t63 : v55.toNat + 2 ^ 32 * v63.toNat = v41.toNat + v46.toNat)
    (t90 : v90.toNat = (v62.toNat + v63.toNat) % 2 ^ 32) :
    v55.toNat + 2 ^ 32 * v90.toNat = ((v34.toNat + 2 ^ 32 * v33.toNat) + (v27.toNat + 2 ^ 32 * v31.toNat) + (v30.toNat + 2 ^ 32 * v32.toNat) + (v41.toNat + 2 ^ 32 * v42.toNat)) % 2 ^ 64 := by
  obtain ⟨q44, eq44⟩ := mod_q t44; clear t44
  obtain ⟨q47, eq47⟩ := mod_q t47; clear t47
  obtain ⟨q49, eq49⟩ := mod_q t49; clear t49
  obtain ⟨q54, eq54⟩ := mod_q t54; clear t54
  obtain ⟨q62, eq62⟩ := mod_q t62; clear t62
  obtain ⟨q90, eq90⟩ := mod_q t90; clear t90
  have key : v55.toNat + 2 ^ 32 * v90.toNat + 2 ^ 64 * (q44 + q47 + q49 + q54 + q62 + q90) = ((v34.toNat + 2 ^ 32 * v33.toNat) + (v27.toNat + 2 ^ 32 * v31.toNat) + (v30.toNat + 2 ^ 32 * v32.toNat) + (v41.toNat + 2 ^ 32 * v42.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v27.toNat = n27 at *
    generalize v30.toNat = n30 at *
    generalize v31.toNat = n31 at *
    generalize v32.toNat = n32 at *
    generalize v33.toNat = n33 at *
    generalize v34.toNat = n34 at *
    generalize v41.toNat = n41 at *
    generalize v42.toNat = n42 at *
    generalize v43.toNat = n43 at *
    generalize v44.toNat = n44 at *
    generalize v45.toNat = n45 at *
    generalize v46.toNat = n46 at *
    generalize v47.toNat = n47 at *
    generalize v48.toNat = n48 at *
    generalize v49.toNat = n49 at *
    generalize v54.toNat = n54 at *
    generalize v55.toNat = n55 at *
    generalize v62.toNat = n62 at *
    generalize v63.toNat = n63 at *
    generalize v90.toNat = n90 at *
    omega
  exact smm_key key (smm_lt v55 v90)

theorem smm_v_PA0B4 {v4 v60 v70 v79 : Word}
    (t70 : v70.toNat = v60.toNat * v4.toNat / 2 ^ 32)
    (t79 : v79.toNat = v60.toNat * v4.toNat % 2 ^ 32) :
    v79.toNat + 2 ^ 32 * v70.toNat = v4.toNat * v60.toNat := by
  have := Nat.mul_comm v4.toNat v60.toNat
  have := v4.isLt; have := v60.isLt; have := v70.isLt; have := v79.isLt
  generalize v4.toNat = n4 at *
  generalize v60.toNat = n60 at *
  generalize v70.toNat = n70 at *
  generalize v79.toNat = n79 at *
  omega

theorem smm_v_PA1B3 {v5 v8 v50 v58 : Word}
    (t50 : v50.toNat = v8.toNat * v5.toNat / 2 ^ 32)
    (t58 : v58.toNat = v8.toNat * v5.toNat % 2 ^ 32) :
    v58.toNat + 2 ^ 32 * v50.toNat = v5.toNat * v8.toNat := by
  have := Nat.mul_comm v5.toNat v8.toNat
  have := v5.isLt; have := v8.isLt; have := v50.isLt; have := v58.isLt
  generalize v5.toNat = n5 at *
  generalize v8.toNat = n8 at *
  generalize v50.toNat = n50 at *
  generalize v58.toNat = n58 at *
  omega

theorem smm_v_PA2B2 {v7 v9 v51 v59 : Word}
    (t51 : v51.toNat = v9.toNat * v7.toNat / 2 ^ 32)
    (t59 : v59.toNat = v9.toNat * v7.toNat % 2 ^ 32) :
    v59.toNat + 2 ^ 32 * v51.toNat = v9.toNat * v7.toNat := by
  have := v7.isLt; have := v9.isLt; have := v51.isLt; have := v59.isLt
  generalize v7.toNat = n7 at *
  generalize v9.toNat = n9 at *
  generalize v51.toNat = n51 at *
  generalize v59.toNat = n59 at *
  omega

theorem smm_v_PA3B1 {v3 v10 v57 v61 : Word}
    (t57 : v57.toNat = v10.toNat * v3.toNat / 2 ^ 32)
    (t61 : v61.toNat = v10.toNat * v3.toNat % 2 ^ 32) :
    v61.toNat + 2 ^ 32 * v57.toNat = v10.toNat * v3.toNat := by
  have := v3.isLt; have := v10.isLt; have := v57.isLt; have := v61.isLt
  generalize v3.toNat = n3 at *
  generalize v10.toNat = n10 at *
  generalize v57.toNat = n57 at *
  generalize v61.toNat = n61 at *
  omega

theorem smm_v_PA4B0 {v6 v73 v87 v109 : Word}
    (t87 : v87.toNat = v73.toNat * v6.toNat / 2 ^ 32)
    (t109 : v109.toNat = v73.toNat * v6.toNat % 2 ^ 32) :
    v109.toNat + 2 ^ 32 * v87.toNat = v73.toNat * v6.toNat := by
  have := v6.isLt; have := v73.isLt; have := v87.isLt; have := v109.isLt
  generalize v6.toNat = n6 at *
  generalize v73.toNat = n73 at *
  generalize v87.toNat = n87 at *
  generalize v109.toNat = n109 at *
  omega

theorem smm_v_Z4 {v50 v51 v57 v58 v59 v61 v64 v70 v71 v74 v75 v76 v77 v78 v79 v80 v87 v92 v95 v99 v101 v104 v109 v122 v126 v139 : Word}
    (t64 : v64.toNat = (v51.toNat + v50.toNat) % 2 ^ 32)
    (t71 : v71.toNat = (v64.toNat + v57.toNat) % 2 ^ 32)
    (t75 : v74.toNat + 2 ^ 32 * v75.toNat = v59.toNat + v58.toNat)
    (t77 : v76.toNat + 2 ^ 32 * v77.toNat = v61.toNat + v74.toNat)
    (t78 : v78.toNat = (v75.toNat + v71.toNat) % 2 ^ 32)
    (t80 : v80.toNat = (v78.toNat + v77.toNat) % 2 ^ 32)
    (t92 : v92.toNat = (v70.toNat + v80.toNat) % 2 ^ 32)
    (t99 : v95.toNat + 2 ^ 32 * v99.toNat = v79.toNat + v76.toNat)
    (t101 : v101.toNat = (v99.toNat + v87.toNat) % 2 ^ 32)
    (t104 : v104.toNat = (v92.toNat + v101.toNat) % 2 ^ 32)
    (t126 : v122.toNat + 2 ^ 32 * v126.toNat = v109.toNat + v95.toNat)
    (t139 : v139.toNat = (v104.toNat + v126.toNat) % 2 ^ 32) :
    v122.toNat + 2 ^ 32 * v139.toNat = ((v79.toNat + 2 ^ 32 * v70.toNat) + (v58.toNat + 2 ^ 32 * v50.toNat) + (v59.toNat + 2 ^ 32 * v51.toNat) + (v61.toNat + 2 ^ 32 * v57.toNat) + (v109.toNat + 2 ^ 32 * v87.toNat)) % 2 ^ 64 := by
  obtain ⟨q64, eq64⟩ := mod_q t64; clear t64
  obtain ⟨q71, eq71⟩ := mod_q t71; clear t71
  obtain ⟨q78, eq78⟩ := mod_q t78; clear t78
  obtain ⟨q80, eq80⟩ := mod_q t80; clear t80
  obtain ⟨q92, eq92⟩ := mod_q t92; clear t92
  obtain ⟨q101, eq101⟩ := mod_q t101; clear t101
  obtain ⟨q104, eq104⟩ := mod_q t104; clear t104
  obtain ⟨q139, eq139⟩ := mod_q t139; clear t139
  have key : v122.toNat + 2 ^ 32 * v139.toNat + 2 ^ 64 * (q64 + q71 + q78 + q80 + q92 + q101 + q104 + q139) = ((v79.toNat + 2 ^ 32 * v70.toNat) + (v58.toNat + 2 ^ 32 * v50.toNat) + (v59.toNat + 2 ^ 32 * v51.toNat) + (v61.toNat + 2 ^ 32 * v57.toNat) + (v109.toNat + 2 ^ 32 * v87.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v50.toNat = n50 at *
    generalize v51.toNat = n51 at *
    generalize v57.toNat = n57 at *
    generalize v58.toNat = n58 at *
    generalize v59.toNat = n59 at *
    generalize v61.toNat = n61 at *
    generalize v64.toNat = n64 at *
    generalize v70.toNat = n70 at *
    generalize v71.toNat = n71 at *
    generalize v74.toNat = n74 at *
    generalize v75.toNat = n75 at *
    generalize v76.toNat = n76 at *
    generalize v77.toNat = n77 at *
    generalize v78.toNat = n78 at *
    generalize v79.toNat = n79 at *
    generalize v80.toNat = n80 at *
    generalize v87.toNat = n87 at *
    generalize v92.toNat = n92 at *
    generalize v95.toNat = n95 at *
    generalize v99.toNat = n99 at *
    generalize v101.toNat = n101 at *
    generalize v104.toNat = n104 at *
    generalize v109.toNat = n109 at *
    generalize v122.toNat = n122 at *
    generalize v126.toNat = n126 at *
    generalize v139.toNat = n139 at *
    omega
  exact smm_key key (smm_lt v122 v139)

theorem smm_v_PA1B4 {v5 v60 v98 v100 : Word}
    (t98 : v98.toNat = v60.toNat * v5.toNat / 2 ^ 32)
    (t100 : v100.toNat = v60.toNat * v5.toNat % 2 ^ 32) :
    v100.toNat + 2 ^ 32 * v98.toNat = v5.toNat * v60.toNat := by
  have := Nat.mul_comm v5.toNat v60.toNat
  have := v5.isLt; have := v60.isLt; have := v98.isLt; have := v100.isLt
  generalize v5.toNat = n5 at *
  generalize v60.toNat = n60 at *
  generalize v98.toNat = n98 at *
  generalize v100.toNat = n100 at *
  omega

theorem smm_v_PA2B3 {v8 v9 v88 v93 : Word}
    (t88 : v88.toNat = v8.toNat * v9.toNat / 2 ^ 32)
    (t93 : v93.toNat = v8.toNat * v9.toNat % 2 ^ 32) :
    v93.toNat + 2 ^ 32 * v88.toNat = v9.toNat * v8.toNat := by
  have := Nat.mul_comm v8.toNat v9.toNat
  have := v8.isLt; have := v9.isLt; have := v88.isLt; have := v93.isLt
  generalize v8.toNat = n8 at *
  generalize v9.toNat = n9 at *
  generalize v88.toNat = n88 at *
  generalize v93.toNat = n93 at *
  omega

theorem smm_v_PA3B2 {v7 v10 v89 v94 : Word}
    (t89 : v89.toNat = v10.toNat * v7.toNat / 2 ^ 32)
    (t94 : v94.toNat = v10.toNat * v7.toNat % 2 ^ 32) :
    v94.toNat + 2 ^ 32 * v89.toNat = v10.toNat * v7.toNat := by
  have := v7.isLt; have := v10.isLt; have := v89.isLt; have := v94.isLt
  generalize v7.toNat = n7 at *
  generalize v10.toNat = n10 at *
  generalize v89.toNat = n89 at *
  generalize v94.toNat = n94 at *
  omega

theorem smm_v_PA4B1 {v3 v73 v103 v106 : Word}
    (t103 : v103.toNat = v73.toNat * v3.toNat % 2 ^ 32)
    (t106 : v106.toNat = v73.toNat * v3.toNat / 2 ^ 32) :
    v103.toNat + 2 ^ 32 * v106.toNat = v73.toNat * v3.toNat := by
  have := v3.isLt; have := v73.isLt; have := v103.isLt; have := v106.isLt
  generalize v3.toNat = n3 at *
  generalize v73.toNat = n73 at *
  generalize v103.toNat = n103 at *
  generalize v106.toNat = n106 at *
  omega

theorem smm_v_PA2B4 {v9 v60 v132 v133 : Word}
    (t132 : v132.toNat = v60.toNat * v9.toNat % 2 ^ 32)
    (t133 : v133.toNat = v60.toNat * v9.toNat / 2 ^ 32) :
    v132.toNat + 2 ^ 32 * v133.toNat = v9.toNat * v60.toNat := by
  have := Nat.mul_comm v60.toNat v9.toNat
  have := v9.isLt; have := v60.isLt; have := v132.isLt; have := v133.isLt
  generalize v9.toNat = n9 at *
  generalize v60.toNat = n60 at *
  generalize v132.toNat = n132 at *
  generalize v133.toNat = n133 at *
  omega

theorem smm_v_PA3B3 {v8 v10 v134 v135 : Word}
    (t134 : v134.toNat = v10.toNat * v8.toNat % 2 ^ 32)
    (t135 : v135.toNat = v10.toNat * v8.toNat / 2 ^ 32) :
    v134.toNat + 2 ^ 32 * v135.toNat = v10.toNat * v8.toNat := by
  have := v8.isLt; have := v10.isLt; have := v134.isLt; have := v135.isLt
  generalize v8.toNat = n8 at *
  generalize v10.toNat = n10 at *
  generalize v134.toNat = n134 at *
  generalize v135.toNat = n135 at *
  omega

theorem smm_v_PA4B2 {v7 v73 v137 v144 : Word}
    (t137 : v137.toNat = v73.toNat * v7.toNat / 2 ^ 32)
    (t144 : v144.toNat = v73.toNat * v7.toNat % 2 ^ 32) :
    v144.toNat + 2 ^ 32 * v137.toNat = v73.toNat * v7.toNat := by
  have := v7.isLt; have := v73.isLt; have := v137.isLt; have := v144.isLt
  generalize v7.toNat = n7 at *
  generalize v73.toNat = n73 at *
  generalize v137.toNat = n137 at *
  generalize v144.toNat = n144 at *
  omega

theorem smm_v_Z6a {v132 v133 v134 v135 v137 v144 v150 v151 v152 v153 v157 v158 v159 v167 : Word}
    (t150 : v150.toNat = (v135.toNat + v133.toNat) % 2 ^ 32)
    (t152 : v152.toNat = (v150.toNat + v137.toNat) % 2 ^ 32)
    (t153 : v151.toNat + 2 ^ 32 * v153.toNat = v134.toNat + v132.toNat)
    (t157 : v157.toNat = (v153.toNat + v152.toNat) % 2 ^ 32)
    (t159 : v158.toNat + 2 ^ 32 * v159.toNat = v144.toNat + v151.toNat)
    (t167 : v167.toNat = (v157.toNat + v159.toNat) % 2 ^ 32) :
    v158.toNat + 2 ^ 32 * v167.toNat = ((v132.toNat + 2 ^ 32 * v133.toNat) + (v134.toNat + 2 ^ 32 * v135.toNat) + (v144.toNat + 2 ^ 32 * v137.toNat)) % 2 ^ 64 := by
  obtain ⟨q150, eq150⟩ := mod_q t150; clear t150
  obtain ⟨q152, eq152⟩ := mod_q t152; clear t152
  obtain ⟨q157, eq157⟩ := mod_q t157; clear t157
  obtain ⟨q167, eq167⟩ := mod_q t167; clear t167
  have key : v158.toNat + 2 ^ 32 * v167.toNat + 2 ^ 64 * (q150 + q152 + q157 + q167) = ((v132.toNat + 2 ^ 32 * v133.toNat) + (v134.toNat + 2 ^ 32 * v135.toNat) + (v144.toNat + 2 ^ 32 * v137.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v132.toNat = n132 at *
    generalize v133.toNat = n133 at *
    generalize v134.toNat = n134 at *
    generalize v135.toNat = n135 at *
    generalize v137.toNat = n137 at *
    generalize v144.toNat = n144 at *
    generalize v150.toNat = n150 at *
    generalize v151.toNat = n151 at *
    generalize v152.toNat = n152 at *
    generalize v153.toNat = n153 at *
    generalize v157.toNat = n157 at *
    generalize v158.toNat = n158 at *
    generalize v159.toNat = n159 at *
    generalize v167.toNat = n167 at *
    omega
  exact smm_key key (smm_lt v158 v167)

theorem smm_v_PA3B4 {v10 v60 v174 v178 : Word}
    (t174 : v174.toNat = v60.toNat * v10.toNat / 2 ^ 32)
    (t178 : v178.toNat = v60.toNat * v10.toNat % 2 ^ 32) :
    v178.toNat + 2 ^ 32 * v174.toNat = v10.toNat * v60.toNat := by
  have := Nat.mul_comm v10.toNat v60.toNat
  have := v10.isLt; have := v60.isLt; have := v174.isLt; have := v178.isLt
  generalize v10.toNat = n10 at *
  generalize v60.toNat = n60 at *
  generalize v174.toNat = n174 at *
  generalize v178.toNat = n178 at *
  omega

theorem smm_v_PA4B3 {v8 v73 v177 v179 : Word}
    (t177 : v177.toNat = v73.toNat * v8.toNat / 2 ^ 32)
    (t179 : v179.toNat = v73.toNat * v8.toNat % 2 ^ 32) :
    v179.toNat + 2 ^ 32 * v177.toNat = v73.toNat * v8.toNat := by
  have := v8.isLt; have := v73.isLt; have := v177.isLt; have := v179.isLt
  generalize v8.toNat = n8 at *
  generalize v73.toNat = n73 at *
  generalize v177.toNat = n177 at *
  generalize v179.toNat = n179 at *
  omega

theorem smm_v_Z7a {v174 v177 v178 v179 v189 v191 v201 v204 : Word}
    (t189 : v189.toNat = (v177.toNat + v174.toNat) % 2 ^ 32)
    (t201 : v191.toNat + 2 ^ 32 * v201.toNat = v179.toNat + v178.toNat)
    (t204 : v204.toNat = (v189.toNat + v201.toNat) % 2 ^ 32) :
    v191.toNat + 2 ^ 32 * v204.toNat = ((v178.toNat + 2 ^ 32 * v174.toNat) + (v179.toNat + 2 ^ 32 * v177.toNat)) % 2 ^ 64 := by
  obtain ⟨q189, eq189⟩ := mod_q t189; clear t189
  obtain ⟨q204, eq204⟩ := mod_q t204; clear t204
  have key : v191.toNat + 2 ^ 32 * v204.toNat + 2 ^ 64 * (q189 + q204) = ((v178.toNat + 2 ^ 32 * v174.toNat) + (v179.toNat + 2 ^ 32 * v177.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v174.toNat = n174 at *
    generalize v177.toNat = n177 at *
    generalize v178.toNat = n178 at *
    generalize v179.toNat = n179 at *
    generalize v189.toNat = n189 at *
    generalize v191.toNat = n191 at *
    generalize v201.toNat = n201 at *
    generalize v204.toNat = n204 at *
    omega
  exact smm_key key (smm_lt v191 v204)

theorem smm_v_PA4B4 {v60 v73 v628 v630 : Word}
    (t628 : v628.toNat = v73.toNat * v60.toNat % 2 ^ 32)
    (t630 : v630.toNat = v73.toNat * v60.toNat / 2 ^ 32) :
    v628.toNat + 2 ^ 32 * v630.toNat = v73.toNat * v60.toNat := by
  have := v60.isLt; have := v73.isLt; have := v628.isLt; have := v630.isLt
  generalize v60.toNat = n60 at *
  generalize v73.toNat = n73 at *
  generalize v628.toNat = n628 at *
  generalize v630.toNat = n630 at *
  omega

theorem smm_v_PA5B5 {v65 v81 v107 v124 : Word}
    (t107 : v107.toNat = v65.toNat * v81.toNat / 2 ^ 32)
    (t124 : v124.toNat = v65.toNat * v81.toNat % 2 ^ 32) :
    v124.toNat + 2 ^ 32 * v107.toNat = v81.toNat * v65.toNat := by
  have := Nat.mul_comm v65.toNat v81.toNat
  have := v65.isLt; have := v81.isLt; have := v107.isLt; have := v124.isLt
  generalize v65.toNat = n65 at *
  generalize v81.toNat = n81 at *
  generalize v107.toNat = n107 at *
  generalize v124.toNat = n124 at *
  omega

theorem smm_v_Z10a {v88 v89 v93 v94 v98 v100 v103 v105 v106 v107 v108 v112 v113 v114 v115 v116 v117 v118 v119 v120 v121 v124 v125 v138 v141 v147 : Word}
    (t105 : v105.toNat = (v88.toNat + v89.toNat) % 2 ^ 32)
    (t112 : v112.toNat = (v98.toNat + v105.toNat) % 2 ^ 32)
    (t113 : v108.toNat + 2 ^ 32 * v113.toNat = v93.toNat + v94.toNat)
    (t114 : v114.toNat = (v112.toNat + v113.toNat) % 2 ^ 32)
    (t116 : v115.toNat + 2 ^ 32 * v116.toNat = v100.toNat + v108.toNat)
    (t118 : v118.toNat = (v116.toNat + v114.toNat) % 2 ^ 32)
    (t119 : v117.toNat + 2 ^ 32 * v119.toNat = v103.toNat + v115.toNat)
    (t120 : v120.toNat = (v106.toNat + v118.toNat) % 2 ^ 32)
    (t121 : v121.toNat = (v119.toNat + 2 ^ 32 - v107.toNat) % 2 ^ 32)
    (t125 : v125.toNat = (v120.toNat + v121.toNat) % 2 ^ 32)
    (t138 : v147.toNat + v124.toNat = v117.toNat + 2 ^ 32 * v138.toNat)
    (t141 : v141.toNat = (v125.toNat + 2 ^ 32 - v138.toNat) % 2 ^ 32) :
    v147.toNat + 2 ^ 32 * v141.toNat = ((((v100.toNat + 2 ^ 32 * v98.toNat) + (v93.toNat + 2 ^ 32 * v88.toNat) + (v94.toNat + 2 ^ 32 * v89.toNat) + (v103.toNat + 2 ^ 32 * v106.toNat)) % 2 ^ 64) + (2 ^ 64 - (v124.toNat + 2 ^ 32 * v107.toNat))) % 2 ^ 64 := by
  obtain ⟨q105, eq105⟩ := mod_q t105; clear t105
  obtain ⟨q112, eq112⟩ := mod_q t112; clear t112
  obtain ⟨q114, eq114⟩ := mod_q t114; clear t114
  obtain ⟨q118, eq118⟩ := mod_q t118; clear t118
  obtain ⟨q120, eq120⟩ := mod_q t120; clear t120
  obtain ⟨q121, eq121⟩ := mod_q t121; clear t121
  obtain ⟨q125, eq125⟩ := mod_q t125; clear t125
  obtain ⟨q141, eq141⟩ := mod_q t141; clear t141
  obtain ⟨k0, ek0⟩ : ∃ k, ((v100.toNat + 2 ^ 32 * v98.toNat) + (v93.toNat + 2 ^ 32 * v88.toNat) + (v94.toNat + 2 ^ 32 * v89.toNat) + (v103.toNat + 2 ^ 32 * v106.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v100.toNat + 2 ^ 32 * v98.toNat) + (v93.toNat + 2 ^ 32 * v88.toNat) + (v94.toNat + 2 ^ 32 * v89.toNat) + (v103.toNat + 2 ^ 32 * v106.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v147.toNat + 2 ^ 32 * v141.toNat + 2 ^ 64 * (q105 + q112 + q114 + q118 + q120 + q121 + q125 + q141) = ((((v100.toNat + 2 ^ 32 * v98.toNat) + (v93.toNat + 2 ^ 32 * v88.toNat) + (v94.toNat + 2 ^ 32 * v89.toNat) + (v103.toNat + 2 ^ 32 * v106.toNat)) % 2 ^ 64) + (2 ^ 64 - (v124.toNat + 2 ^ 32 * v107.toNat))) + 2 ^ 64 * (k0 + 1) := by
    have := v107.isLt; have := v124.isLt; have := v138.isLt; skip
    generalize v88.toNat = n88 at *
    generalize v89.toNat = n89 at *
    generalize v93.toNat = n93 at *
    generalize v94.toNat = n94 at *
    generalize v98.toNat = n98 at *
    generalize v100.toNat = n100 at *
    generalize v103.toNat = n103 at *
    generalize v105.toNat = n105 at *
    generalize v106.toNat = n106 at *
    generalize v107.toNat = n107 at *
    generalize v108.toNat = n108 at *
    generalize v112.toNat = n112 at *
    generalize v113.toNat = n113 at *
    generalize v114.toNat = n114 at *
    generalize v115.toNat = n115 at *
    generalize v116.toNat = n116 at *
    generalize v117.toNat = n117 at *
    generalize v118.toNat = n118 at *
    generalize v119.toNat = n119 at *
    generalize v120.toNat = n120 at *
    generalize v121.toNat = n121 at *
    generalize v124.toNat = n124 at *
    generalize v125.toNat = n125 at *
    generalize v138.toNat = n138 at *
    generalize v141.toNat = n141 at *
    generalize v147.toNat = n147 at *
    omega
  exact smm_key key (smm_lt v147 v141)

theorem smm_v_PA5B6 {v66 v81 v127 v129 : Word}
    (t127 : v127.toNat = v66.toNat * v81.toNat % 2 ^ 32)
    (t129 : v129.toNat = v66.toNat * v81.toNat / 2 ^ 32) :
    v127.toNat + 2 ^ 32 * v129.toNat = v81.toNat * v66.toNat := by
  have := Nat.mul_comm v66.toNat v81.toNat
  have := v66.isLt; have := v81.isLt; have := v127.isLt; have := v129.isLt
  generalize v66.toNat = n66 at *
  generalize v81.toNat = n81 at *
  generalize v127.toNat = n127 at *
  generalize v129.toNat = n129 at *
  omega

theorem smm_v_PA6B5 {v65 v82 v128 v130 : Word}
    (t128 : v128.toNat = v82.toNat * v65.toNat % 2 ^ 32)
    (t130 : v130.toNat = v82.toNat * v65.toNat / 2 ^ 32) :
    v128.toNat + 2 ^ 32 * v130.toNat = v82.toNat * v65.toNat := by
  have := v65.isLt; have := v82.isLt; have := v128.isLt; have := v130.isLt
  generalize v65.toNat = n65 at *
  generalize v82.toNat = n82 at *
  generalize v128.toNat = n128 at *
  generalize v130.toNat = n130 at *
  omega

theorem smm_v_Q11 {v127 v128 v129 v130 v143 v145 v146 v149 : Word}
    (t145 : v145.toNat = (v129.toNat + v130.toNat) % 2 ^ 32)
    (t146 : v143.toNat + 2 ^ 32 * v146.toNat = v127.toNat + v128.toNat)
    (t149 : v149.toNat = (v145.toNat + v146.toNat) % 2 ^ 32) :
    v143.toNat + 2 ^ 32 * v149.toNat = ((v127.toNat + 2 ^ 32 * v129.toNat) + (v128.toNat + 2 ^ 32 * v130.toNat)) % 2 ^ 64 := by
  obtain ⟨q145, eq145⟩ := mod_q t145; clear t145
  obtain ⟨q149, eq149⟩ := mod_q t149; clear t149
  have key : v143.toNat + 2 ^ 32 * v149.toNat + 2 ^ 64 * (q145 + q149) = ((v127.toNat + 2 ^ 32 * v129.toNat) + (v128.toNat + 2 ^ 32 * v130.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v127.toNat = n127 at *
    generalize v128.toNat = n128 at *
    generalize v129.toNat = n129 at *
    generalize v130.toNat = n130 at *
    generalize v143.toNat = n143 at *
    generalize v145.toNat = n145 at *
    generalize v146.toNat = n146 at *
    generalize v149.toNat = n149 at *
    omega
  exact smm_key key (smm_lt v143 v149)

theorem smm_v_Z11a {v143 v149 v158 v164 v167 v168 v169 v186 : Word}
    (t164 : v186.toNat + v143.toNat = v158.toNat + 2 ^ 32 * v164.toNat)
    (t168 : v168.toNat = (v164.toNat + v149.toNat) % 2 ^ 32)
    (t169 : v169.toNat = (v167.toNat + 2 ^ 32 - v168.toNat) % 2 ^ 32) :
    v186.toNat + 2 ^ 32 * v169.toNat = ((v158.toNat + 2 ^ 32 * v167.toNat) + (2 ^ 64 - (v143.toNat + 2 ^ 32 * v149.toNat))) % 2 ^ 64 := by
  obtain ⟨q168, eq168⟩ := mod_q t168; clear t168
  obtain ⟨q169, eq169⟩ := mod_q t169; clear t169
  have key : v186.toNat + 2 ^ 32 * v169.toNat + 2 ^ 64 * (q169) = ((v158.toNat + 2 ^ 32 * v167.toNat) + (2 ^ 64 - (v143.toNat + 2 ^ 32 * v149.toNat))) + 2 ^ 64 * (q168) := by
    have := v143.isLt; have := v149.isLt; have := v168.isLt; skip
    generalize v143.toNat = n143 at *
    generalize v149.toNat = n149 at *
    generalize v158.toNat = n158 at *
    generalize v164.toNat = n164 at *
    generalize v167.toNat = n167 at *
    generalize v168.toNat = n168 at *
    generalize v169.toNat = n169 at *
    generalize v186.toNat = n186 at *
    omega
  exact smm_key key (smm_lt v186 v169)

theorem smm_v_PA5B7 {v67 v81 v156 v161 : Word}
    (t156 : v156.toNat = v67.toNat * v81.toNat / 2 ^ 32)
    (t161 : v161.toNat = v67.toNat * v81.toNat % 2 ^ 32) :
    v161.toNat + 2 ^ 32 * v156.toNat = v81.toNat * v67.toNat := by
  have := Nat.mul_comm v67.toNat v81.toNat
  have := v67.isLt; have := v81.isLt; have := v156.isLt; have := v161.isLt
  generalize v67.toNat = n67 at *
  generalize v81.toNat = n81 at *
  generalize v156.toNat = n156 at *
  generalize v161.toNat = n161 at *
  omega

theorem smm_v_PA6B6 {v66 v82 v154 v160 : Word}
    (t154 : v154.toNat = v82.toNat * v66.toNat / 2 ^ 32)
    (t160 : v160.toNat = v82.toNat * v66.toNat % 2 ^ 32) :
    v160.toNat + 2 ^ 32 * v154.toNat = v82.toNat * v66.toNat := by
  have := v66.isLt; have := v82.isLt; have := v154.isLt; have := v160.isLt
  generalize v66.toNat = n66 at *
  generalize v82.toNat = n82 at *
  generalize v154.toNat = n154 at *
  generalize v160.toNat = n160 at *
  omega

theorem smm_v_PA7B5 {v65 v83 v163 v165 : Word}
    (t163 : v163.toNat = v83.toNat * v65.toNat / 2 ^ 32)
    (t165 : v165.toNat = v83.toNat * v65.toNat % 2 ^ 32) :
    v165.toNat + 2 ^ 32 * v163.toNat = v83.toNat * v65.toNat := by
  have := v65.isLt; have := v83.isLt; have := v163.isLt; have := v165.isLt
  generalize v65.toNat = n65 at *
  generalize v83.toNat = n83 at *
  generalize v163.toNat = n163 at *
  generalize v165.toNat = n165 at *
  omega

theorem smm_v_Q12 {v154 v156 v160 v161 v163 v165 v171 v180 v181 v182 v183 v184 v185 v188 : Word}
    (t171 : v171.toNat = (v154.toNat + v156.toNat) % 2 ^ 32)
    (t180 : v180.toNat = (v171.toNat + v163.toNat) % 2 ^ 32)
    (t182 : v181.toNat + 2 ^ 32 * v182.toNat = v160.toNat + v161.toNat)
    (t184 : v184.toNat = (v182.toNat + v180.toNat) % 2 ^ 32)
    (t185 : v183.toNat + 2 ^ 32 * v185.toNat = v181.toNat + v165.toNat)
    (t188 : v188.toNat = (v184.toNat + v185.toNat) % 2 ^ 32) :
    v183.toNat + 2 ^ 32 * v188.toNat = ((v161.toNat + 2 ^ 32 * v156.toNat) + (v160.toNat + 2 ^ 32 * v154.toNat) + (v165.toNat + 2 ^ 32 * v163.toNat)) % 2 ^ 64 := by
  obtain ⟨q171, eq171⟩ := mod_q t171; clear t171
  obtain ⟨q180, eq180⟩ := mod_q t180; clear t180
  obtain ⟨q184, eq184⟩ := mod_q t184; clear t184
  obtain ⟨q188, eq188⟩ := mod_q t188; clear t188
  have key : v183.toNat + 2 ^ 32 * v188.toNat + 2 ^ 64 * (q171 + q180 + q184 + q188) = ((v161.toNat + 2 ^ 32 * v156.toNat) + (v160.toNat + 2 ^ 32 * v154.toNat) + (v165.toNat + 2 ^ 32 * v163.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v154.toNat = n154 at *
    generalize v156.toNat = n156 at *
    generalize v160.toNat = n160 at *
    generalize v161.toNat = n161 at *
    generalize v163.toNat = n163 at *
    generalize v165.toNat = n165 at *
    generalize v171.toNat = n171 at *
    generalize v180.toNat = n180 at *
    generalize v181.toNat = n181 at *
    generalize v182.toNat = n182 at *
    generalize v183.toNat = n183 at *
    generalize v184.toNat = n184 at *
    generalize v185.toNat = n185 at *
    generalize v188.toNat = n188 at *
    omega
  exact smm_key key (smm_lt v183 v188)

theorem smm_v_Z12a {v183 v188 v191 v204 v205 v206 v208 v234 : Word}
    (t205 : v234.toNat + v183.toNat = v191.toNat + 2 ^ 32 * v205.toNat)
    (t206 : v206.toNat = (v204.toNat + 2 ^ 32 - v205.toNat) % 2 ^ 32)
    (t208 : v208.toNat = (v206.toNat + 2 ^ 32 - v188.toNat) % 2 ^ 32) :
    v234.toNat + 2 ^ 32 * v208.toNat = ((v191.toNat + 2 ^ 32 * v204.toNat) + (2 ^ 64 - (v183.toNat + 2 ^ 32 * v188.toNat))) % 2 ^ 64 := by
  obtain ⟨q206, eq206⟩ := mod_q t206; clear t206
  obtain ⟨q208, eq208⟩ := mod_q t208; clear t208
  have key : v234.toNat + 2 ^ 32 * v208.toNat + 2 ^ 64 * (q206 + q208) = ((v191.toNat + 2 ^ 32 * v204.toNat) + (2 ^ 64 - (v183.toNat + 2 ^ 32 * v188.toNat))) + 2 ^ 64 * (1) := by
    have := v183.isLt; have := v188.isLt; have := v205.isLt; skip
    generalize v183.toNat = n183 at *
    generalize v188.toNat = n188 at *
    generalize v191.toNat = n191 at *
    generalize v204.toNat = n204 at *
    generalize v205.toNat = n205 at *
    generalize v206.toNat = n206 at *
    generalize v208.toNat = n208 at *
    generalize v234.toNat = n234 at *
    omega
  exact smm_key key (smm_lt v234 v208)

theorem smm_v_PA5B8 {v81 v190 v203 v207 : Word}
    (t203 : v203.toNat = v190.toNat * v81.toNat / 2 ^ 32)
    (t207 : v207.toNat = v190.toNat * v81.toNat % 2 ^ 32) :
    v207.toNat + 2 ^ 32 * v203.toNat = v81.toNat * v190.toNat := by
  have := Nat.mul_comm v190.toNat v81.toNat
  have := v81.isLt; have := v190.isLt; have := v203.isLt; have := v207.isLt
  generalize v81.toNat = n81 at *
  generalize v190.toNat = n190 at *
  generalize v203.toNat = n203 at *
  generalize v207.toNat = n207 at *
  omega

theorem smm_v_PA6B7 {v67 v82 v196 v198 : Word}
    (t196 : v196.toNat = v67.toNat * v82.toNat / 2 ^ 32)
    (t198 : v198.toNat = v67.toNat * v82.toNat % 2 ^ 32) :
    v198.toNat + 2 ^ 32 * v196.toNat = v82.toNat * v67.toNat := by
  have := Nat.mul_comm v67.toNat v82.toNat
  have := v67.isLt; have := v82.isLt; have := v196.isLt; have := v198.isLt
  generalize v67.toNat = n67 at *
  generalize v82.toNat = n82 at *
  generalize v196.toNat = n196 at *
  generalize v198.toNat = n198 at *
  omega

theorem smm_v_PA7B6 {v66 v83 v197 v199 : Word}
    (t197 : v197.toNat = v83.toNat * v66.toNat / 2 ^ 32)
    (t199 : v199.toNat = v83.toNat * v66.toNat % 2 ^ 32) :
    v199.toNat + 2 ^ 32 * v197.toNat = v83.toNat * v66.toNat := by
  have := v66.isLt; have := v83.isLt; have := v197.isLt; have := v199.isLt
  generalize v66.toNat = n66 at *
  generalize v83.toNat = n83 at *
  generalize v197.toNat = n197 at *
  generalize v199.toNat = n199 at *
  omega

theorem smm_v_PA8B5 {v65 v219 v253 v257 : Word}
    (t253 : v253.toNat = v219.toNat * v65.toNat / 2 ^ 32)
    (t257 : v257.toNat = v219.toNat * v65.toNat % 2 ^ 32) :
    v257.toNat + 2 ^ 32 * v253.toNat = v219.toNat * v65.toNat := by
  have := v65.isLt; have := v219.isLt; have := v253.isLt; have := v257.isLt
  generalize v65.toNat = n65 at *
  generalize v219.toNat = n219 at *
  generalize v253.toNat = n253 at *
  generalize v257.toNat = n257 at *
  omega

theorem smm_v_Z13 {v196 v197 v198 v199 v203 v207 v211 v213 v216 v217 v218 v220 v230 v236 v253 v257 v268 v272 v276 v278 : Word}
    (t211 : v211.toNat = (v196.toNat + v197.toNat) % 2 ^ 32)
    (t216 : v216.toNat = (v203.toNat + v211.toNat) % 2 ^ 32)
    (t217 : v213.toNat + 2 ^ 32 * v217.toNat = v199.toNat + v198.toNat)
    (t218 : v218.toNat = (v216.toNat + v217.toNat) % 2 ^ 32)
    (t230 : v220.toNat + 2 ^ 32 * v230.toNat = v213.toNat + v207.toNat)
    (t236 : v236.toNat = (v218.toNat + v230.toNat) % 2 ^ 32)
    (t268 : v268.toNat = (v253.toNat + v236.toNat) % 2 ^ 32)
    (t276 : v272.toNat + 2 ^ 32 * v276.toNat = v257.toNat + v220.toNat)
    (t278 : v278.toNat = (v276.toNat + v268.toNat) % 2 ^ 32) :
    v272.toNat + 2 ^ 32 * v278.toNat = ((v207.toNat + 2 ^ 32 * v203.toNat) + (v198.toNat + 2 ^ 32 * v196.toNat) + (v199.toNat + 2 ^ 32 * v197.toNat) + (v257.toNat + 2 ^ 32 * v253.toNat)) % 2 ^ 64 := by
  obtain ⟨q211, eq211⟩ := mod_q t211; clear t211
  obtain ⟨q216, eq216⟩ := mod_q t216; clear t216
  obtain ⟨q218, eq218⟩ := mod_q t218; clear t218
  obtain ⟨q236, eq236⟩ := mod_q t236; clear t236
  obtain ⟨q268, eq268⟩ := mod_q t268; clear t268
  obtain ⟨q278, eq278⟩ := mod_q t278; clear t278
  have key : v272.toNat + 2 ^ 32 * v278.toNat + 2 ^ 64 * (q211 + q216 + q218 + q236 + q268 + q278) = ((v207.toNat + 2 ^ 32 * v203.toNat) + (v198.toNat + 2 ^ 32 * v196.toNat) + (v199.toNat + 2 ^ 32 * v197.toNat) + (v257.toNat + 2 ^ 32 * v253.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v196.toNat = n196 at *
    generalize v197.toNat = n197 at *
    generalize v198.toNat = n198 at *
    generalize v199.toNat = n199 at *
    generalize v203.toNat = n203 at *
    generalize v207.toNat = n207 at *
    generalize v211.toNat = n211 at *
    generalize v213.toNat = n213 at *
    generalize v216.toNat = n216 at *
    generalize v217.toNat = n217 at *
    generalize v218.toNat = n218 at *
    generalize v220.toNat = n220 at *
    generalize v230.toNat = n230 at *
    generalize v236.toNat = n236 at *
    generalize v253.toNat = n253 at *
    generalize v257.toNat = n257 at *
    generalize v268.toNat = n268 at *
    generalize v272.toNat = n272 at *
    generalize v276.toNat = n276 at *
    generalize v278.toNat = n278 at *
    omega
  exact smm_key key (smm_lt v272 v278)

theorem smm_v_PA6B8 {v82 v190 v222 v242 : Word}
    (t222 : v222.toNat = v190.toNat * v82.toNat / 2 ^ 32)
    (t242 : v242.toNat = v190.toNat * v82.toNat % 2 ^ 32) :
    v242.toNat + 2 ^ 32 * v222.toNat = v82.toNat * v190.toNat := by
  have := Nat.mul_comm v190.toNat v82.toNat
  have := v82.isLt; have := v190.isLt; have := v222.isLt; have := v242.isLt
  generalize v82.toNat = n82 at *
  generalize v190.toNat = n190 at *
  generalize v222.toNat = n222 at *
  generalize v242.toNat = n242 at *
  omega

theorem smm_v_PA7B7 {v67 v83 v224 v243 : Word}
    (t224 : v224.toNat = v83.toNat * v67.toNat / 2 ^ 32)
    (t243 : v243.toNat = v83.toNat * v67.toNat % 2 ^ 32) :
    v243.toNat + 2 ^ 32 * v224.toNat = v83.toNat * v67.toNat := by
  have := v67.isLt; have := v83.isLt; have := v224.isLt; have := v243.isLt
  generalize v67.toNat = n67 at *
  generalize v83.toNat = n83 at *
  generalize v224.toNat = n224 at *
  generalize v243.toNat = n243 at *
  omega

theorem smm_v_PA8B6 {v66 v219 v241 v258 : Word}
    (t241 : v241.toNat = v219.toNat * v66.toNat / 2 ^ 32)
    (t258 : v258.toNat = v219.toNat * v66.toNat % 2 ^ 32) :
    v258.toNat + 2 ^ 32 * v241.toNat = v219.toNat * v66.toNat := by
  have := v66.isLt; have := v219.isLt; have := v241.isLt; have := v258.isLt
  generalize v66.toNat = n66 at *
  generalize v219.toNat = n219 at *
  generalize v241.toNat = n241 at *
  generalize v258.toNat = n258 at *
  omega

theorem smm_v_Z14 {v222 v224 v237 v241 v242 v243 v255 v258 v259 v262 v269 v274 v277 v280 : Word}
    (t237 : v237.toNat = (v222.toNat + v224.toNat) % 2 ^ 32)
    (t255 : v255.toNat = (v241.toNat + v237.toNat) % 2 ^ 32)
    (t262 : v259.toNat + 2 ^ 32 * v262.toNat = v243.toNat + v242.toNat)
    (t269 : v269.toNat = (v255.toNat + v262.toNat) % 2 ^ 32)
    (t277 : v274.toNat + 2 ^ 32 * v277.toNat = v258.toNat + v259.toNat)
    (t280 : v280.toNat = (v277.toNat + v269.toNat) % 2 ^ 32) :
    v274.toNat + 2 ^ 32 * v280.toNat = ((v242.toNat + 2 ^ 32 * v222.toNat) + (v243.toNat + 2 ^ 32 * v224.toNat) + (v258.toNat + 2 ^ 32 * v241.toNat)) % 2 ^ 64 := by
  obtain ⟨q237, eq237⟩ := mod_q t237; clear t237
  obtain ⟨q255, eq255⟩ := mod_q t255; clear t255
  obtain ⟨q269, eq269⟩ := mod_q t269; clear t269
  obtain ⟨q280, eq280⟩ := mod_q t280; clear t280
  have key : v274.toNat + 2 ^ 32 * v280.toNat + 2 ^ 64 * (q237 + q255 + q269 + q280) = ((v242.toNat + 2 ^ 32 * v222.toNat) + (v243.toNat + 2 ^ 32 * v224.toNat) + (v258.toNat + 2 ^ 32 * v241.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v222.toNat = n222 at *
    generalize v224.toNat = n224 at *
    generalize v237.toNat = n237 at *
    generalize v241.toNat = n241 at *
    generalize v242.toNat = n242 at *
    generalize v243.toNat = n243 at *
    generalize v255.toNat = n255 at *
    generalize v258.toNat = n258 at *
    generalize v259.toNat = n259 at *
    generalize v262.toNat = n262 at *
    generalize v269.toNat = n269 at *
    generalize v274.toNat = n274 at *
    generalize v277.toNat = n277 at *
    generalize v280.toNat = n280 at *
    omega
  exact smm_key key (smm_lt v274 v280)

theorem smm_v_PA7B8 {v83 v190 v270 v300 : Word}
    (t270 : v270.toNat = v190.toNat * v83.toNat / 2 ^ 32)
    (t300 : v300.toNat = v190.toNat * v83.toNat % 2 ^ 32) :
    v300.toNat + 2 ^ 32 * v270.toNat = v83.toNat * v190.toNat := by
  have := Nat.mul_comm v190.toNat v83.toNat
  have := v83.isLt; have := v190.isLt; have := v270.isLt; have := v300.isLt
  generalize v83.toNat = n83 at *
  generalize v190.toNat = n190 at *
  generalize v270.toNat = n270 at *
  generalize v300.toNat = n300 at *
  omega

theorem smm_v_PA8B7 {v67 v219 v271 v301 : Word}
    (t271 : v271.toNat = v219.toNat * v67.toNat / 2 ^ 32)
    (t301 : v301.toNat = v219.toNat * v67.toNat % 2 ^ 32) :
    v301.toNat + 2 ^ 32 * v271.toNat = v219.toNat * v67.toNat := by
  have := v67.isLt; have := v219.isLt; have := v271.isLt; have := v301.isLt
  generalize v67.toNat = n67 at *
  generalize v219.toNat = n219 at *
  generalize v271.toNat = n271 at *
  generalize v301.toNat = n301 at *
  omega

theorem smm_v_Z15 {v270 v271 v288 v300 v301 v314 v320 v322 : Word}
    (t288 : v288.toNat = (v270.toNat + v271.toNat) % 2 ^ 32)
    (t320 : v314.toNat + 2 ^ 32 * v320.toNat = v300.toNat + v301.toNat)
    (t322 : v322.toNat = (v320.toNat + v288.toNat) % 2 ^ 32) :
    v314.toNat + 2 ^ 32 * v322.toNat = ((v300.toNat + 2 ^ 32 * v270.toNat) + (v301.toNat + 2 ^ 32 * v271.toNat)) % 2 ^ 64 := by
  obtain ⟨q288, eq288⟩ := mod_q t288; clear t288
  obtain ⟨q322, eq322⟩ := mod_q t322; clear t322
  have key : v314.toNat + 2 ^ 32 * v322.toNat + 2 ^ 64 * (q288 + q322) = ((v300.toNat + 2 ^ 32 * v270.toNat) + (v301.toNat + 2 ^ 32 * v271.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v270.toNat = n270 at *
    generalize v271.toNat = n271 at *
    generalize v288.toNat = n288 at *
    generalize v300.toNat = n300 at *
    generalize v301.toNat = n301 at *
    generalize v314.toNat = n314 at *
    generalize v320.toNat = n320 at *
    generalize v322.toNat = n322 at *
    omega
  exact smm_key key (smm_lt v314 v322)

theorem smm_v_PA8B8 {v190 v219 v384 v386 : Word}
    (t384 : v384.toNat = v219.toNat * v190.toNat / 2 ^ 32)
    (t386 : v386.toNat = v219.toNat * v190.toNat % 2 ^ 32) :
    v386.toNat + 2 ^ 32 * v384.toNat = v219.toNat * v190.toNat := by
  have := v190.isLt; have := v219.isLt; have := v384.isLt; have := v386.isLt
  generalize v190.toNat = n190 at *
  generalize v219.toNat = n219 at *
  generalize v384.toNat = n384 at *
  generalize v386.toNat = n386 at *
  omega

theorem smm_v_Z11b {v169 v186 v384 v386 v995 v1000 v1003 v1004 : Word}
    (t1000 : v995.toNat + 2 ^ 32 * v1000.toNat = v186.toNat + v386.toNat)
    (t1003 : v1003.toNat = (v169.toNat + v384.toNat) % 2 ^ 32)
    (t1004 : v1004.toNat = (v1000.toNat + v1003.toNat) % 2 ^ 32) :
    v995.toNat + 2 ^ 32 * v1004.toNat = ((v386.toNat + 2 ^ 32 * v384.toNat) + (v186.toNat + 2 ^ 32 * v169.toNat)) % 2 ^ 64 := by
  obtain ⟨q1003, eq1003⟩ := mod_q t1003; clear t1003
  obtain ⟨q1004, eq1004⟩ := mod_q t1004; clear t1004
  have key : v995.toNat + 2 ^ 32 * v1004.toNat + 2 ^ 64 * (q1003 + q1004) = ((v386.toNat + 2 ^ 32 * v384.toNat) + (v186.toNat + 2 ^ 32 * v169.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v169.toNat = n169 at *
    generalize v186.toNat = n186 at *
    generalize v384.toNat = n384 at *
    generalize v386.toNat = n386 at *
    generalize v995.toNat = n995 at *
    generalize v1000.toNat = n1000 at *
    generalize v1003.toNat = n1003 at *
    generalize v1004.toNat = n1004 at *
    omega
  exact smm_key key (smm_lt v995 v1004)

theorem smm_v_AA0 {v4 v81 v330 : Word}
    (t330 : v330.toNat = (v81.toNat + v4.toNat) % 2 ^ 32) :
    v330.toNat = (v4.toNat + v81.toNat) % 2 ^ 32 := by
  have := v4.isLt; have := v81.isLt; have := v330.isLt
  generalize v4.toNat = n4 at *
  generalize v81.toNat = n81 at *
  generalize v330.toNat = n330 at *
  omega

theorem smm_v_AA1 {v5 v82 v333 : Word}
    (t333 : v333.toNat = (v5.toNat + v82.toNat) % 2 ^ 32) :
    v333.toNat = (v5.toNat + v82.toNat) % 2 ^ 32 := by
  have := v5.isLt; have := v82.isLt; have := v333.isLt
  generalize v5.toNat = n5 at *
  generalize v82.toNat = n82 at *
  generalize v333.toNat = n333 at *
  omega

theorem smm_v_AA2 {v9 v83 v335 : Word}
    (t335 : v335.toNat = (v9.toNat + v83.toNat) % 2 ^ 32) :
    v335.toNat = (v9.toNat + v83.toNat) % 2 ^ 32 := by
  have := v9.isLt; have := v83.isLt; have := v335.isLt
  generalize v9.toNat = n9 at *
  generalize v83.toNat = n83 at *
  generalize v335.toNat = n335 at *
  omega

theorem smm_v_AA3 {v10 v219 v375 : Word}
    (t375 : v375.toNat = (v10.toNat + v219.toNat) % 2 ^ 32) :
    v375.toNat = (v10.toNat + v219.toNat) % 2 ^ 32 := by
  have := v10.isLt; have := v219.isLt; have := v375.isLt
  generalize v10.toNat = n10 at *
  generalize v219.toNat = n219 at *
  generalize v375.toNat = n375 at *
  omega

theorem smm_v_BB0 {v6 v65 v350 : Word}
    (t350 : v350.toNat = (v6.toNat + v65.toNat) % 2 ^ 32) :
    v350.toNat = (v6.toNat + v65.toNat) % 2 ^ 32 := by
  have := v6.isLt; have := v65.isLt; have := v350.isLt
  generalize v6.toNat = n6 at *
  generalize v65.toNat = n65 at *
  generalize v350.toNat = n350 at *
  omega

theorem smm_v_BB1 {v3 v66 v364 : Word}
    (t364 : v364.toNat = (v3.toNat + v66.toNat) % 2 ^ 32) :
    v364.toNat = (v3.toNat + v66.toNat) % 2 ^ 32 := by
  have := v3.isLt; have := v66.isLt; have := v364.isLt
  generalize v3.toNat = n3 at *
  generalize v66.toNat = n66 at *
  generalize v364.toNat = n364 at *
  omega

theorem smm_v_BB2 {v7 v67 v369 : Word}
    (t369 : v369.toNat = (v7.toNat + v67.toNat) % 2 ^ 32) :
    v369.toNat = (v7.toNat + v67.toNat) % 2 ^ 32 := by
  have := v7.isLt; have := v67.isLt; have := v369.isLt
  generalize v7.toNat = n7 at *
  generalize v67.toNat = n67 at *
  generalize v369.toNat = n369 at *
  omega

theorem smm_v_BB3 {v8 v190 v392 : Word}
    (t392 : v392.toNat = (v190.toNat + v8.toNat) % 2 ^ 32) :
    v392.toNat = (v8.toNat + v190.toNat) % 2 ^ 32 := by
  have := v8.isLt; have := v190.isLt; have := v392.isLt
  generalize v8.toNat = n8 at *
  generalize v190.toNat = n190 at *
  generalize v392.toNat = n392 at *
  omega

theorem smm_v_PAA0BB0 {v330 v350 v380 v442 : Word}
    (t380 : v380.toNat = v350.toNat * v330.toNat / 2 ^ 32)
    (t442 : v442.toNat = v350.toNat * v330.toNat % 2 ^ 32) :
    v442.toNat + 2 ^ 32 * v380.toNat = v330.toNat * v350.toNat := by
  have := Nat.mul_comm v330.toNat v350.toNat
  have := v330.isLt; have := v350.isLt; have := v380.isLt; have := v442.isLt
  generalize v330.toNat = n330 at *
  generalize v350.toNat = n350 at *
  generalize v380.toNat = n380 at *
  generalize v442.toNat = n442 at *
  omega

theorem smm_v_Z5 {v141 v147 v193 v232 v325 v326 v380 v397 v442 v453 v458 v459 v460 v466 : Word}
    (t325 : v453.toNat + v193.toNat = v147.toNat + 2 ^ 32 * v325.toNat)
    (t326 : v326.toNat = (v325.toNat + v232.toNat) % 2 ^ 32)
    (t397 : v397.toNat = (v326.toNat + 2 ^ 32 - v380.toNat) % 2 ^ 32)
    (t458 : v458.toNat = (v141.toNat + 2 ^ 32 - v397.toNat) % 2 ^ 32)
    (t460 : v459.toNat + 2 ^ 32 * v460.toNat = v442.toNat + v453.toNat)
    (t466 : v466.toNat = (v460.toNat + v458.toNat) % 2 ^ 32) :
    v459.toNat + 2 ^ 32 * v466.toNat = ((v442.toNat + 2 ^ 32 * v380.toNat) + (((v147.toNat + 2 ^ 32 * v141.toNat) + (2 ^ 64 - (v193.toNat + 2 ^ 32 * v232.toNat))) % 2 ^ 64)) % 2 ^ 64 := by
  obtain ⟨q326, eq326⟩ := mod_q t326; clear t326
  obtain ⟨q397, eq397⟩ := mod_q t397; clear t397
  obtain ⟨q458, eq458⟩ := mod_q t458; clear t458
  obtain ⟨q466, eq466⟩ := mod_q t466; clear t466
  obtain ⟨k0, ek0⟩ : ∃ k, ((v147.toNat + 2 ^ 32 * v141.toNat) + (2 ^ 64 - (v193.toNat + 2 ^ 32 * v232.toNat))) % 2 ^ 64 + 2 ^ 64 * k = ((v147.toNat + 2 ^ 32 * v141.toNat) + (2 ^ 64 - (v193.toNat + 2 ^ 32 * v232.toNat))) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v459.toNat + 2 ^ 32 * v466.toNat + 2 ^ 64 * (q458 + q466 + 1) = ((v442.toNat + 2 ^ 32 * v380.toNat) + (((v147.toNat + 2 ^ 32 * v141.toNat) + (2 ^ 64 - (v193.toNat + 2 ^ 32 * v232.toNat))) % 2 ^ 64)) + 2 ^ 64 * (q326 + q397 + k0) := by
    have := v193.isLt; have := v232.isLt; have := v380.isLt; have := v397.isLt; skip
    generalize v141.toNat = n141 at *
    generalize v147.toNat = n147 at *
    generalize v193.toNat = n193 at *
    generalize v232.toNat = n232 at *
    generalize v325.toNat = n325 at *
    generalize v326.toNat = n326 at *
    generalize v380.toNat = n380 at *
    generalize v397.toNat = n397 at *
    generalize v442.toNat = n442 at *
    generalize v453.toNat = n453 at *
    generalize v458.toNat = n458 at *
    generalize v459.toNat = n459 at *
    generalize v460.toNat = n460 at *
    generalize v466.toNat = n466 at *
    omega
  exact smm_key key (smm_lt v459 v466)

theorem smm_v_PAA0BB1 {v330 v364 v501 v503 : Word}
    (t501 : v501.toNat = v364.toNat * v330.toNat % 2 ^ 32)
    (t503 : v503.toNat = v364.toNat * v330.toNat / 2 ^ 32) :
    v501.toNat + 2 ^ 32 * v503.toNat = v330.toNat * v364.toNat := by
  have := Nat.mul_comm v330.toNat v364.toNat
  have := v330.isLt; have := v364.isLt; have := v501.isLt; have := v503.isLt
  generalize v330.toNat = n330 at *
  generalize v364.toNat = n364 at *
  generalize v501.toNat = n501 at *
  generalize v503.toNat = n503 at *
  omega

theorem smm_v_PAA1BB0 {v333 v350 v506 v514 : Word}
    (t506 : v506.toNat = v333.toNat * v350.toNat % 2 ^ 32)
    (t514 : v514.toNat = v333.toNat * v350.toNat / 2 ^ 32) :
    v506.toNat + 2 ^ 32 * v514.toNat = v333.toNat * v350.toNat := by
  have := v333.isLt; have := v350.isLt; have := v506.isLt; have := v514.isLt
  generalize v333.toNat = n333 at *
  generalize v350.toNat = n350 at *
  generalize v506.toNat = n506 at *
  generalize v514.toNat = n514 at *
  omega

theorem smm_v_Z6 {v21 v28 v169 v186 v501 v503 v506 v514 v516 v518 v520 v521 v522 v531 v533 v534 v535 v536 v538 v539 : Word}
    (t516 : v521.toNat + v21.toNat = v501.toNat + 2 ^ 32 * v516.toNat)
    (t518 : v518.toNat = (v503.toNat + 2 ^ 32 - v516.toNat) % 2 ^ 32)
    (t520 : v520.toNat = (v518.toNat + 2 ^ 32 - v28.toNat) % 2 ^ 32)
    (t531 : v531.toNat = (v514.toNat + v520.toNat) % 2 ^ 32)
    (t534 : v522.toNat + 2 ^ 32 * v534.toNat = v506.toNat + v521.toNat)
    (t535 : v533.toNat + 2 ^ 32 * v535.toNat = v186.toNat + v522.toNat)
    (t536 : v536.toNat = (v534.toNat + v531.toNat) % 2 ^ 32)
    (t538 : v538.toNat = (v535.toNat + v169.toNat) % 2 ^ 32)
    (t539 : v539.toNat = (v536.toNat + v538.toNat) % 2 ^ 32) :
    v533.toNat + 2 ^ 32 * v539.toNat = ((((v501.toNat + 2 ^ 32 * v503.toNat) + (v506.toNat + 2 ^ 32 * v514.toNat)) % 2 ^ 64) + (((v186.toNat + 2 ^ 32 * v169.toNat) + (2 ^ 64 - (v21.toNat + 2 ^ 32 * v28.toNat))) % 2 ^ 64)) % 2 ^ 64 := by
  obtain ⟨q518, eq518⟩ := mod_q t518; clear t518
  obtain ⟨q520, eq520⟩ := mod_q t520; clear t520
  obtain ⟨q531, eq531⟩ := mod_q t531; clear t531
  obtain ⟨q536, eq536⟩ := mod_q t536; clear t536
  obtain ⟨q538, eq538⟩ := mod_q t538; clear t538
  obtain ⟨q539, eq539⟩ := mod_q t539; clear t539
  obtain ⟨k0, ek0⟩ : ∃ k, ((v501.toNat + 2 ^ 32 * v503.toNat) + (v506.toNat + 2 ^ 32 * v514.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v501.toNat + 2 ^ 32 * v503.toNat) + (v506.toNat + 2 ^ 32 * v514.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  obtain ⟨k1, ek1⟩ : ∃ k, ((v186.toNat + 2 ^ 32 * v169.toNat) + (2 ^ 64 - (v21.toNat + 2 ^ 32 * v28.toNat))) % 2 ^ 64 + 2 ^ 64 * k = ((v186.toNat + 2 ^ 32 * v169.toNat) + (2 ^ 64 - (v21.toNat + 2 ^ 32 * v28.toNat))) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v533.toNat + 2 ^ 32 * v539.toNat + 2 ^ 64 * (q518 + q520 + q531 + q536 + q538 + q539) = ((((v501.toNat + 2 ^ 32 * v503.toNat) + (v506.toNat + 2 ^ 32 * v514.toNat)) % 2 ^ 64) + (((v186.toNat + 2 ^ 32 * v169.toNat) + (2 ^ 64 - (v21.toNat + 2 ^ 32 * v28.toNat))) % 2 ^ 64)) + 2 ^ 64 * (k1 + k0 + 1) := by
    have := v21.isLt; have := v28.isLt; have := v516.isLt; skip
    generalize v21.toNat = n21 at *
    generalize v28.toNat = n28 at *
    generalize v169.toNat = n169 at *
    generalize v186.toNat = n186 at *
    generalize v501.toNat = n501 at *
    generalize v503.toNat = n503 at *
    generalize v506.toNat = n506 at *
    generalize v514.toNat = n514 at *
    generalize v516.toNat = n516 at *
    generalize v518.toNat = n518 at *
    generalize v520.toNat = n520 at *
    generalize v521.toNat = n521 at *
    generalize v522.toNat = n522 at *
    generalize v531.toNat = n531 at *
    generalize v533.toNat = n533 at *
    generalize v534.toNat = n534 at *
    generalize v535.toNat = n535 at *
    generalize v536.toNat = n536 at *
    generalize v538.toNat = n538 at *
    generalize v539.toNat = n539 at *
    omega
  exact smm_key key (smm_lt v533 v539)

theorem smm_v_PAA0BB2 {v330 v369 v555 v557 : Word}
    (t555 : v555.toNat = v369.toNat * v330.toNat / 2 ^ 32)
    (t557 : v557.toNat = v369.toNat * v330.toNat % 2 ^ 32) :
    v557.toNat + 2 ^ 32 * v555.toNat = v330.toNat * v369.toNat := by
  have := Nat.mul_comm v330.toNat v369.toNat
  have := v330.isLt; have := v369.isLt; have := v555.isLt; have := v557.isLt
  generalize v330.toNat = n330 at *
  generalize v369.toNat = n369 at *
  generalize v555.toNat = n555 at *
  generalize v557.toNat = n557 at *
  omega

end C3.RV32
