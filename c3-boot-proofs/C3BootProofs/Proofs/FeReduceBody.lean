import C3BootProofs.Proofs.Fe25519Decode

/-! # The straight-line body of `FieldElement2625::reduce`, as compiled

`scripts/gen-fe25519.py` writes this file from the decoded instructions. -/

namespace C3.RV32

open C3.Image

theorem fr_s0 {v0 v1 v3 v4 v7 v8 v9 v10 v11 v12 v15 v17 : Word} {Z0 Z1 X1 : Nat}
    (t7 : v7.toNat = v1.toNat * 2 ^ 6 % 2 ^ 32)
    (t8 : v8.toNat = v0.toNat / 2 ^ 26)
    (t9 : v9.toNat = v1.toNat / 2 ^ 26)
    (t10 : v10.toNat = v8.toNat + v7.toNat)
    (t11 : v11.toNat = (v4.toNat + v9.toNat) % 2 ^ 32)
    (t12 : v12.toNat = (v3.toNat + v10.toNat) % 2 ^ 32)
    (t15 : (v12.toNat < v3.toNat ∧ v15.toNat = 1) ∨ (v3.toNat ≤ v12.toNat ∧ v15.toNat = 0))
    (t17 : v17.toNat = (v11.toNat + v15.toNat) % 2 ^ 32)
    (hZ0 : v0.toNat + 2 ^ 32 * v1.toNat = Z0)
    (hZ1 : v3.toNat + 2 ^ 32 * v4.toNat = Z1)
    (eX1 : (Z1 + Z0 / 2 ^ 26) % 2 ^ 64 = X1) :
    v12.toNat + 2 ^ 32 * v17.toNat = X1 := by
  have := v0.isLt; have := v1.isLt; have := v3.isLt; have := v4.isLt; have := v7.isLt; have := v8.isLt; have := v9.isLt; have := v10.isLt; have := v11.isLt; have := v12.isLt; have := v15.isLt; have := v17.isLt
  generalize v0.toNat = n0 at *
  generalize v1.toNat = n1 at *
  generalize v3.toNat = n3 at *
  generalize v4.toNat = n4 at *
  generalize v7.toNat = n7 at *
  generalize v8.toNat = n8 at *
  generalize v9.toNat = n9 at *
  generalize v10.toNat = n10 at *
  generalize v11.toNat = n11 at *
  generalize v12.toNat = n12 at *
  generalize v15.toNat = n15 at *
  generalize v17.toNat = n17 at *
  omega

theorem fr_s1 {v0 v1 v103 : Word} {Z0 X2 : Nat}
    (t103 : v103.toNat = v0.toNat % 2 ^ 26)
    (hZ0 : v0.toNat + 2 ^ 32 * v1.toNat = Z0)
    (eX2 : Z0 % 2 ^ 26 = X2) :
    v103.toNat = X2 := by
  have := v0.isLt; have := v1.isLt; have := v103.isLt
  generalize v0.toNat = n0 at *
  generalize v1.toNat = n1 at *
  generalize v103.toNat = n103 at *
  omega

theorem fr_s2 {v5 v6 v13 v14 v16 v18 v20 v21 v22 v23 v24 v25 : Word} {Z4 Z5 X3 : Nat}
    (t16 : v16.toNat = v6.toNat * 2 ^ 6 % 2 ^ 32)
    (t18 : v18.toNat = v5.toNat / 2 ^ 26)
    (t20 : v20.toNat = v18.toNat + v16.toNat)
    (t21 : v21.toNat = v6.toNat / 2 ^ 26)
    (t22 : v22.toNat = (v13.toNat + v20.toNat) % 2 ^ 32)
    (t23 : v23.toNat = (v21.toNat + v14.toNat) % 2 ^ 32)
    (t24 : (v22.toNat < v13.toNat ∧ v24.toNat = 1) ∨ (v13.toNat ≤ v22.toNat ∧ v24.toNat = 0))
    (t25 : v25.toNat = (v24.toNat + v23.toNat) % 2 ^ 32)
    (hZ4 : v5.toNat + 2 ^ 32 * v6.toNat = Z4)
    (hZ5 : v13.toNat + 2 ^ 32 * v14.toNat = Z5)
    (eX3 : (Z5 + Z4 / 2 ^ 26) % 2 ^ 64 = X3) :
    v22.toNat + 2 ^ 32 * v25.toNat = X3 := by
  have := v5.isLt; have := v6.isLt; have := v13.isLt; have := v14.isLt; have := v16.isLt; have := v18.isLt; have := v20.isLt; have := v21.isLt; have := v22.isLt; have := v23.isLt; have := v24.isLt; have := v25.isLt
  generalize v5.toNat = n5 at *
  generalize v6.toNat = n6 at *
  generalize v13.toNat = n13 at *
  generalize v14.toNat = n14 at *
  generalize v16.toNat = n16 at *
  generalize v18.toNat = n18 at *
  generalize v20.toNat = n20 at *
  generalize v21.toNat = n21 at *
  generalize v22.toNat = n22 at *
  generalize v23.toNat = n23 at *
  generalize v24.toNat = n24 at *
  generalize v25.toNat = n25 at *
  omega

theorem fr_s3 {v5 v6 v26 : Word} {Z4 X4 : Nat}
    (t26 : v26.toNat = v5.toNat % 2 ^ 26)
    (hZ4 : v5.toNat + 2 ^ 32 * v6.toNat = Z4)
    (eX4 : Z4 % 2 ^ 26 = X4) :
    v26.toNat = X4 := by
  have := v5.isLt; have := v6.isLt; have := v26.isLt
  generalize v5.toNat = n5 at *
  generalize v6.toNat = n6 at *
  generalize v26.toNat = n26 at *
  omega

theorem fr_s4 {v12 v17 v27 v28 v29 v30 v31 v32 v35 v36 v41 v49 : Word} {X1 Z2 X5 : Nat}
    (t29 : v29.toNat = v17.toNat * 2 ^ 7 % 2 ^ 32)
    (t30 : v30.toNat = v12.toNat / 2 ^ 25)
    (t31 : v31.toNat = v30.toNat + v29.toNat)
    (t32 : v32.toNat = v17.toNat / 2 ^ 25)
    (t35 : v35.toNat = (v28.toNat + v32.toNat) % 2 ^ 32)
    (t36 : v36.toNat = (v27.toNat + v31.toNat) % 2 ^ 32)
    (t41 : (v36.toNat < v27.toNat ∧ v41.toNat = 1) ∨ (v27.toNat ≤ v36.toNat ∧ v41.toNat = 0))
    (t49 : v49.toNat = (v35.toNat + v41.toNat) % 2 ^ 32)
    (hX1 : v12.toNat + 2 ^ 32 * v17.toNat = X1)
    (hZ2 : v27.toNat + 2 ^ 32 * v28.toNat = Z2)
    (eX5 : (Z2 + X1 / 2 ^ 25) % 2 ^ 64 = X5) :
    v36.toNat + 2 ^ 32 * v49.toNat = X5 := by
  have := v12.isLt; have := v17.isLt; have := v27.isLt; have := v28.isLt; have := v29.isLt; have := v30.isLt; have := v31.isLt; have := v32.isLt; have := v35.isLt; have := v36.isLt; have := v41.isLt; have := v49.isLt
  generalize v12.toNat = n12 at *
  generalize v17.toNat = n17 at *
  generalize v27.toNat = n27 at *
  generalize v28.toNat = n28 at *
  generalize v29.toNat = n29 at *
  generalize v30.toNat = n30 at *
  generalize v31.toNat = n31 at *
  generalize v32.toNat = n32 at *
  generalize v35.toNat = n35 at *
  generalize v36.toNat = n36 at *
  generalize v41.toNat = n41 at *
  generalize v49.toNat = n49 at *
  omega

theorem fr_s5 {v12 v17 v105 : Word} {X1 X6 : Nat}
    (t105 : v105.toNat = v12.toNat % 2 ^ 25)
    (hX1 : v12.toNat + 2 ^ 32 * v17.toNat = X1)
    (eX6 : X1 % 2 ^ 25 = X6) :
    v105.toNat = X6 := by
  have := v12.isLt; have := v17.isLt; have := v105.isLt
  generalize v12.toNat = n12 at *
  generalize v17.toNat = n17 at *
  generalize v105.toNat = n105 at *
  omega

theorem fr_s6 {v22 v25 v37 v38 v39 v40 v42 v43 v46 v47 v48 v50 : Word} {X3 Z6 X7 : Nat}
    (t37 : v37.toNat = v25.toNat * 2 ^ 7 % 2 ^ 32)
    (t39 : v39.toNat = v22.toNat / 2 ^ 25)
    (t42 : v42.toNat = v39.toNat + v37.toNat)
    (t43 : v43.toNat = v25.toNat / 2 ^ 25)
    (t46 : v46.toNat = (v38.toNat + v42.toNat) % 2 ^ 32)
    (t47 : v47.toNat = (v43.toNat + v40.toNat) % 2 ^ 32)
    (t48 : (v46.toNat < v38.toNat ∧ v48.toNat = 1) ∨ (v38.toNat ≤ v46.toNat ∧ v48.toNat = 0))
    (t50 : v50.toNat = (v47.toNat + v48.toNat) % 2 ^ 32)
    (hX3 : v22.toNat + 2 ^ 32 * v25.toNat = X3)
    (hZ6 : v38.toNat + 2 ^ 32 * v40.toNat = Z6)
    (eX7 : (Z6 + X3 / 2 ^ 25) % 2 ^ 64 = X7) :
    v46.toNat + 2 ^ 32 * v50.toNat = X7 := by
  have := v22.isLt; have := v25.isLt; have := v37.isLt; have := v38.isLt; have := v39.isLt; have := v40.isLt; have := v42.isLt; have := v43.isLt; have := v46.isLt; have := v47.isLt; have := v48.isLt; have := v50.isLt
  generalize v22.toNat = n22 at *
  generalize v25.toNat = n25 at *
  generalize v37.toNat = n37 at *
  generalize v38.toNat = n38 at *
  generalize v39.toNat = n39 at *
  generalize v40.toNat = n40 at *
  generalize v42.toNat = n42 at *
  generalize v43.toNat = n43 at *
  generalize v46.toNat = n46 at *
  generalize v47.toNat = n47 at *
  generalize v48.toNat = n48 at *
  generalize v50.toNat = n50 at *
  omega

theorem fr_s7 {v22 v25 v106 : Word} {X3 X8 : Nat}
    (t106 : v106.toNat = v22.toNat % 2 ^ 25)
    (hX3 : v22.toNat + 2 ^ 32 * v25.toNat = X3)
    (eX8 : X3 % 2 ^ 25 = X8) :
    v106.toNat = X8 := by
  have := v22.isLt; have := v25.isLt; have := v106.isLt
  generalize v22.toNat = n22 at *
  generalize v25.toNat = n25 at *
  generalize v106.toNat = n106 at *
  omega

theorem fr_s8 {v33 v34 v36 v49 v51 v52 v53 v54 v57 v63 v69 v77 : Word} {X5 Z3 X9 : Nat}
    (t51 : v51.toNat = v49.toNat * 2 ^ 6 % 2 ^ 32)
    (t52 : v52.toNat = v36.toNat / 2 ^ 26)
    (t53 : v53.toNat = v52.toNat + v51.toNat)
    (t54 : v54.toNat = v49.toNat / 2 ^ 26)
    (t57 : v57.toNat = (v34.toNat + v54.toNat) % 2 ^ 32)
    (t63 : v63.toNat = (v33.toNat + v53.toNat) % 2 ^ 32)
    (t69 : (v63.toNat < v33.toNat ∧ v69.toNat = 1) ∨ (v33.toNat ≤ v63.toNat ∧ v69.toNat = 0))
    (t77 : v77.toNat = (v57.toNat + v69.toNat) % 2 ^ 32)
    (hX5 : v36.toNat + 2 ^ 32 * v49.toNat = X5)
    (hZ3 : v33.toNat + 2 ^ 32 * v34.toNat = Z3)
    (eX9 : (Z3 + X5 / 2 ^ 26) % 2 ^ 64 = X9) :
    v63.toNat + 2 ^ 32 * v77.toNat = X9 := by
  have := v33.isLt; have := v34.isLt; have := v36.isLt; have := v49.isLt; have := v51.isLt; have := v52.isLt; have := v53.isLt; have := v54.isLt; have := v57.isLt; have := v63.isLt; have := v69.isLt; have := v77.isLt
  generalize v33.toNat = n33 at *
  generalize v34.toNat = n34 at *
  generalize v36.toNat = n36 at *
  generalize v49.toNat = n49 at *
  generalize v51.toNat = n51 at *
  generalize v52.toNat = n52 at *
  generalize v53.toNat = n53 at *
  generalize v54.toNat = n54 at *
  generalize v57.toNat = n57 at *
  generalize v63.toNat = n63 at *
  generalize v69.toNat = n69 at *
  generalize v77.toNat = n77 at *
  omega

theorem fr_s9 {v36 v49 v120 : Word} {X5 X10 : Nat}
    (t120 : v120.toNat = v36.toNat % 2 ^ 26)
    (hX5 : v36.toNat + 2 ^ 32 * v49.toNat = X5)
    (eX10 : X5 % 2 ^ 26 = X10) :
    v120.toNat = X10 := by
  have := v36.isLt; have := v49.isLt; have := v120.isLt
  generalize v36.toNat = n36 at *
  generalize v49.toNat = n49 at *
  generalize v120.toNat = n120 at *
  omega

theorem fr_s10 {v44 v45 v46 v50 v55 v56 v58 v59 v60 v61 v62 v64 : Word} {X7 Z7 X11 : Nat}
    (t55 : v55.toNat = v50.toNat * 2 ^ 6 % 2 ^ 32)
    (t56 : v56.toNat = v46.toNat / 2 ^ 26)
    (t58 : v58.toNat = v56.toNat + v55.toNat)
    (t59 : v59.toNat = v50.toNat / 2 ^ 26)
    (t60 : v60.toNat = (v44.toNat + v58.toNat) % 2 ^ 32)
    (t61 : v61.toNat = (v45.toNat + v59.toNat) % 2 ^ 32)
    (t62 : (v60.toNat < v44.toNat ∧ v62.toNat = 1) ∨ (v44.toNat ≤ v60.toNat ∧ v62.toNat = 0))
    (t64 : v64.toNat = (v62.toNat + v61.toNat) % 2 ^ 32)
    (hX7 : v46.toNat + 2 ^ 32 * v50.toNat = X7)
    (hZ7 : v44.toNat + 2 ^ 32 * v45.toNat = Z7)
    (eX11 : (Z7 + X7 / 2 ^ 26) % 2 ^ 64 = X11) :
    v60.toNat + 2 ^ 32 * v64.toNat = X11 := by
  have := v44.isLt; have := v45.isLt; have := v46.isLt; have := v50.isLt; have := v55.isLt; have := v56.isLt; have := v58.isLt; have := v59.isLt; have := v60.isLt; have := v61.isLt; have := v62.isLt; have := v64.isLt
  generalize v44.toNat = n44 at *
  generalize v45.toNat = n45 at *
  generalize v46.toNat = n46 at *
  generalize v50.toNat = n50 at *
  generalize v55.toNat = n55 at *
  generalize v56.toNat = n56 at *
  generalize v58.toNat = n58 at *
  generalize v59.toNat = n59 at *
  generalize v60.toNat = n60 at *
  generalize v61.toNat = n61 at *
  generalize v62.toNat = n62 at *
  generalize v64.toNat = n64 at *
  omega

theorem fr_s11 {v46 v50 v123 : Word} {X7 X12 : Nat}
    (t123 : v123.toNat = v46.toNat % 2 ^ 26)
    (hX7 : v46.toNat + 2 ^ 32 * v50.toNat = X7)
    (eX12 : X7 % 2 ^ 26 = X12) :
    v123.toNat = X12 := by
  have := v46.isLt; have := v50.isLt; have := v123.isLt
  generalize v46.toNat = n46 at *
  generalize v50.toNat = n50 at *
  generalize v123.toNat = n123 at *
  omega

theorem fr_s12 {v26 v63 v77 v81 v87 v91 v98 v99 v100 v101 : Word} {X4 X9 X13 : Nat}
    (t81 : v81.toNat = v77.toNat * 2 ^ 7 % 2 ^ 32)
    (t87 : v87.toNat = v63.toNat / 2 ^ 25)
    (t91 : v91.toNat = v87.toNat + v81.toNat)
    (t98 : v98.toNat = (v91.toNat + v26.toNat) % 2 ^ 32)
    (t99 : v99.toNat = v77.toNat / 2 ^ 25)
    (t100 : (v98.toNat < v26.toNat ∧ v100.toNat = 1) ∨ (v26.toNat ≤ v98.toNat ∧ v100.toNat = 0))
    (t101 : v101.toNat = (v99.toNat + v100.toNat) % 2 ^ 32)
    (hX4 : v26.toNat = X4)
    (hX9 : v63.toNat + 2 ^ 32 * v77.toNat = X9)
    (eX13 : (X4 + X9 / 2 ^ 25) % 2 ^ 64 = X13) :
    v98.toNat + 2 ^ 32 * v101.toNat = X13 := by
  have := v26.isLt; have := v63.isLt; have := v77.isLt; have := v81.isLt; have := v87.isLt; have := v91.isLt; have := v98.isLt; have := v99.isLt; have := v100.isLt; have := v101.isLt
  generalize v26.toNat = n26 at *
  generalize v63.toNat = n63 at *
  generalize v77.toNat = n77 at *
  generalize v81.toNat = n81 at *
  generalize v87.toNat = n87 at *
  generalize v91.toNat = n91 at *
  generalize v98.toNat = n98 at *
  generalize v99.toNat = n99 at *
  generalize v100.toNat = n100 at *
  generalize v101.toNat = n101 at *
  omega

theorem fr_s13 {v63 v77 v121 : Word} {X9 X14 : Nat}
    (t121 : v121.toNat = v63.toNat % 2 ^ 25)
    (hX9 : v63.toNat + 2 ^ 32 * v77.toNat = X9)
    (eX14 : X9 % 2 ^ 25 = X14) :
    v121.toNat = X14 := by
  have := v63.isLt; have := v77.isLt; have := v121.isLt
  generalize v63.toNat = n63 at *
  generalize v77.toNat = n77 at *
  generalize v121.toNat = n121 at *
  omega

theorem fr_s14 {v60 v64 v65 v66 v67 v68 v70 v71 v74 v75 v76 v78 : Word} {X11 Z8 X15 : Nat}
    (t65 : v65.toNat = v64.toNat * 2 ^ 7 % 2 ^ 32)
    (t67 : v67.toNat = v60.toNat / 2 ^ 25)
    (t70 : v70.toNat = v67.toNat + v65.toNat)
    (t71 : v71.toNat = v64.toNat / 2 ^ 25)
    (t74 : v74.toNat = (v66.toNat + v70.toNat) % 2 ^ 32)
    (t75 : v75.toNat = (v71.toNat + v68.toNat) % 2 ^ 32)
    (t76 : (v74.toNat < v66.toNat ∧ v76.toNat = 1) ∨ (v66.toNat ≤ v74.toNat ∧ v76.toNat = 0))
    (t78 : v78.toNat = (v75.toNat + v76.toNat) % 2 ^ 32)
    (hX11 : v60.toNat + 2 ^ 32 * v64.toNat = X11)
    (hZ8 : v66.toNat + 2 ^ 32 * v68.toNat = Z8)
    (eX15 : (Z8 + X11 / 2 ^ 25) % 2 ^ 64 = X15) :
    v74.toNat + 2 ^ 32 * v78.toNat = X15 := by
  have := v60.isLt; have := v64.isLt; have := v65.isLt; have := v66.isLt; have := v67.isLt; have := v68.isLt; have := v70.isLt; have := v71.isLt; have := v74.isLt; have := v75.isLt; have := v76.isLt; have := v78.isLt
  generalize v60.toNat = n60 at *
  generalize v64.toNat = n64 at *
  generalize v65.toNat = n65 at *
  generalize v66.toNat = n66 at *
  generalize v67.toNat = n67 at *
  generalize v68.toNat = n68 at *
  generalize v70.toNat = n70 at *
  generalize v71.toNat = n71 at *
  generalize v74.toNat = n74 at *
  generalize v75.toNat = n75 at *
  generalize v76.toNat = n76 at *
  generalize v78.toNat = n78 at *
  omega

theorem fr_s15 {v60 v64 v124 : Word} {X11 X16 : Nat}
    (t124 : v124.toNat = v60.toNat % 2 ^ 25)
    (hX11 : v60.toNat + 2 ^ 32 * v64.toNat = X11)
    (eX16 : X11 % 2 ^ 25 = X16) :
    v124.toNat = X16 := by
  have := v60.isLt; have := v64.isLt; have := v124.isLt
  generalize v60.toNat = n60 at *
  generalize v64.toNat = n64 at *
  generalize v124.toNat = n124 at *
  omega

theorem fr_s16 {v98 v101 v106 v107 v111 v115 v117 : Word} {X8 X13 X17 : Nat}
    (t107 : v107.toNat = v101.toNat * 2 ^ 6 % 2 ^ 32)
    (t111 : v111.toNat = v98.toNat / 2 ^ 26)
    (t115 : v115.toNat = v111.toNat + v107.toNat)
    (t117 : v117.toNat = (v106.toNat + v115.toNat) % 2 ^ 32)
    (hX8 : v106.toNat = X8)
    (hX13 : v98.toNat + 2 ^ 32 * v101.toNat = X13)
    (eX17 : (X8 + X13 / 2 ^ 26) % 2 ^ 64 = X17) :
    v117.toNat = X17 % 2 ^ 32 := by
  have := v98.isLt; have := v101.isLt; have := v106.isLt; have := v107.isLt; have := v111.isLt; have := v115.isLt; have := v117.isLt
  generalize v98.toNat = n98 at *
  generalize v101.toNat = n101 at *
  generalize v106.toNat = n106 at *
  generalize v107.toNat = n107 at *
  generalize v111.toNat = n111 at *
  generalize v115.toNat = n115 at *
  generalize v117.toNat = n117 at *
  omega

theorem fr_s17 {v98 v101 v122 : Word} {X13 X18 : Nat}
    (t122 : v122.toNat = v98.toNat % 2 ^ 26)
    (hX13 : v98.toNat + 2 ^ 32 * v101.toNat = X13)
    (eX18 : X13 % 2 ^ 26 = X18) :
    v122.toNat = X18 := by
  have := v98.isLt; have := v101.isLt; have := v122.isLt
  generalize v98.toNat = n98 at *
  generalize v101.toNat = n101 at *
  generalize v122.toNat = n122 at *
  omega

theorem fr_s18 {v72 v73 v74 v78 v79 v80 v82 v83 v84 v85 v86 v88 : Word} {X15 Z9 X19 : Nat}
    (t79 : v79.toNat = v78.toNat * 2 ^ 6 % 2 ^ 32)
    (t80 : v80.toNat = v74.toNat / 2 ^ 26)
    (t82 : v82.toNat = v80.toNat + v79.toNat)
    (t83 : v83.toNat = v78.toNat / 2 ^ 26)
    (t84 : v84.toNat = (v72.toNat + v82.toNat) % 2 ^ 32)
    (t85 : v85.toNat = (v73.toNat + v83.toNat) % 2 ^ 32)
    (t86 : (v84.toNat < v72.toNat ∧ v86.toNat = 1) ∨ (v72.toNat ≤ v84.toNat ∧ v86.toNat = 0))
    (t88 : v88.toNat = (v85.toNat + v86.toNat) % 2 ^ 32)
    (hX15 : v74.toNat + 2 ^ 32 * v78.toNat = X15)
    (hZ9 : v72.toNat + 2 ^ 32 * v73.toNat = Z9)
    (eX19 : (Z9 + X15 / 2 ^ 26) % 2 ^ 64 = X19) :
    v84.toNat + 2 ^ 32 * v88.toNat = X19 := by
  have := v72.isLt; have := v73.isLt; have := v74.isLt; have := v78.isLt; have := v79.isLt; have := v80.isLt; have := v82.isLt; have := v83.isLt; have := v84.isLt; have := v85.isLt; have := v86.isLt; have := v88.isLt
  generalize v72.toNat = n72 at *
  generalize v73.toNat = n73 at *
  generalize v74.toNat = n74 at *
  generalize v78.toNat = n78 at *
  generalize v79.toNat = n79 at *
  generalize v80.toNat = n80 at *
  generalize v82.toNat = n82 at *
  generalize v83.toNat = n83 at *
  generalize v84.toNat = n84 at *
  generalize v85.toNat = n85 at *
  generalize v86.toNat = n86 at *
  generalize v88.toNat = n88 at *
  omega

theorem fr_s19 {v74 v78 v125 : Word} {X15 X20 : Nat}
    (t125 : v125.toNat = v74.toNat % 2 ^ 26)
    (hX15 : v74.toNat + 2 ^ 32 * v78.toNat = X15)
    (eX20 : X15 % 2 ^ 26 = X20) :
    v125.toNat = X20 := by
  have := v74.isLt; have := v78.isLt; have := v125.isLt
  generalize v74.toNat = n74 at *
  generalize v78.toNat = n78 at *
  generalize v125.toNat = n125 at *
  omega

theorem fr_s20 {v84 v88 v89 v90 v92 v93 : Word} {X19 X21 : Nat}
    (t89 : v89.toNat = v88.toNat * 2 ^ 7 % 2 ^ 32)
    (t90 : v90.toNat = v84.toNat / 2 ^ 25)
    (t92 : v92.toNat = v90.toNat + v89.toNat)
    (t93 : v93.toNat = v88.toNat / 2 ^ 25)
    (hX19 : v84.toNat + 2 ^ 32 * v88.toNat = X19)
    (eX21 : X19 / 2 ^ 25 = X21) :
    v92.toNat + 2 ^ 32 * v93.toNat = X21 := by
  have := v84.isLt; have := v88.isLt; have := v89.isLt; have := v90.isLt; have := v92.isLt; have := v93.isLt
  generalize v84.toNat = n84 at *
  generalize v88.toNat = n88 at *
  generalize v89.toNat = n89 at *
  generalize v90.toNat = n90 at *
  generalize v92.toNat = n92 at *
  generalize v93.toNat = n93 at *
  omega

theorem fr_s21 {v92 v93 v95 v96 v97 v109 : Word} {X21 X22 : Nat}
    (t95 : v95.toNat = v93.toNat * 19 % 2 ^ 32)
    (t96 : v96.toNat = v92.toNat * 19 % 2 ^ 32)
    (t97 : v97.toNat = v92.toNat * 19 / 2 ^ 32)
    (t109 : v109.toNat = (v97.toNat + v95.toNat) % 2 ^ 32)
    (hX21 : v92.toNat + 2 ^ 32 * v93.toNat = X21)
    (eX22 : 19 * X21 % 2 ^ 64 = X22) :
    v96.toNat + 2 ^ 32 * v109.toNat = X22 := by
  have := v92.isLt; have := v93.isLt; have := v95.isLt; have := v96.isLt; have := v97.isLt; have := v109.isLt
  generalize v92.toNat = n92 at *
  generalize v93.toNat = n93 at *
  generalize v95.toNat = n95 at *
  generalize v96.toNat = n96 at *
  generalize v97.toNat = n97 at *
  generalize v109.toNat = n109 at *
  omega

theorem fr_s22 {v96 v103 v108 v109 v110 v112 : Word} {X2 X22 X23 : Nat}
    (t108 : v108.toNat = (v103.toNat + v96.toNat) % 2 ^ 32)
    (t110 : (v108.toNat < v96.toNat ∧ v110.toNat = 1) ∨ (v96.toNat ≤ v108.toNat ∧ v110.toNat = 0))
    (t112 : v112.toNat = (v109.toNat + v110.toNat) % 2 ^ 32)
    (hX2 : v103.toNat = X2)
    (hX22 : v96.toNat + 2 ^ 32 * v109.toNat = X22)
    (eX23 : (X2 + X22) % 2 ^ 64 = X23) :
    v108.toNat + 2 ^ 32 * v112.toNat = X23 := by
  have := v96.isLt; have := v103.isLt; have := v108.isLt; have := v109.isLt; have := v110.isLt; have := v112.isLt
  generalize v96.toNat = n96 at *
  generalize v103.toNat = n103 at *
  generalize v108.toNat = n108 at *
  generalize v109.toNat = n109 at *
  generalize v110.toNat = n110 at *
  generalize v112.toNat = n112 at *
  omega

theorem fr_s23 {v84 v88 v126 : Word} {X19 X24 : Nat}
    (t126 : v126.toNat = v84.toNat % 2 ^ 25)
    (hX19 : v84.toNat + 2 ^ 32 * v88.toNat = X19)
    (eX24 : X19 % 2 ^ 25 = X24) :
    v126.toNat = X24 := by
  have := v84.isLt; have := v88.isLt; have := v126.isLt
  generalize v84.toNat = n84 at *
  generalize v88.toNat = n88 at *
  generalize v126.toNat = n126 at *
  omega

theorem fr_s24 {v105 v108 v112 v113 v114 v116 v118 : Word} {X6 X23 X25 : Nat}
    (t113 : v113.toNat = v112.toNat * 2 ^ 6 % 2 ^ 32)
    (t114 : v114.toNat = v108.toNat / 2 ^ 26)
    (t116 : v116.toNat = v114.toNat + v113.toNat)
    (t118 : v118.toNat = (v116.toNat + v105.toNat) % 2 ^ 32)
    (hX6 : v105.toNat = X6)
    (hX23 : v108.toNat + 2 ^ 32 * v112.toNat = X23)
    (eX25 : (X6 + X23 / 2 ^ 26) % 2 ^ 64 = X25) :
    v118.toNat = X25 % 2 ^ 32 := by
  have := v105.isLt; have := v108.isLt; have := v112.isLt; have := v113.isLt; have := v114.isLt; have := v116.isLt; have := v118.isLt
  generalize v105.toNat = n105 at *
  generalize v108.toNat = n108 at *
  generalize v112.toNat = n112 at *
  generalize v113.toNat = n113 at *
  generalize v114.toNat = n114 at *
  generalize v116.toNat = n116 at *
  generalize v118.toNat = n118 at *
  omega

theorem fr_s25 {v108 v112 v119 : Word} {X23 X26 : Nat}
    (t119 : v119.toNat = v108.toNat % 2 ^ 26)
    (hX23 : v108.toNat + 2 ^ 32 * v112.toNat = X23)
    (eX26 : X23 % 2 ^ 26 = X26) :
    v119.toNat = X26 := by
  have := v108.isLt; have := v112.isLt; have := v119.isLt
  generalize v108.toNat = n108 at *
  generalize v112.toNat = n112 at *
  generalize v119.toNat = n119 at *
  omega

/-- The registers `reduce`'s body leaves alone. -/
def frBodyKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 28, 29, 30, 31]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **The body of `reduce`**, from the first load at 0xC to the first store at
0x1A4: the ten words it leaves for the stores are `feReduceSpec` of the ten
`u64` limbs at `zp`. -/
theorem fr_body {M : Word → BitVec 8} {B zp : Word} {n : Machine} (s : St M B n 0xC (reg n))
    (hc : CodeIn M B feReduceCode) (ha1 : reg n a1 = zp) (hz : zp.toNat % 4 = 0) :
    ∃ n', Steps n n' ∧ St M B n' 0x1A4 (reg n') ∧
      [reg n' a2, reg n' a3, reg n' a4, reg n' (8 : Fin 32), reg n' a5, reg n' (5 : Fin 32), reg n' a1, reg n' a6, reg n' (6 : Fin 32), reg n' (9 : Fin 32)].map BitVec.toNat =
        feReduceSpec (u64At M zp 0) (u64At M zp 1) (u64At M zp 2) (u64At M zp 3) (u64At M zp 4)
          (u64At M zp 5) (u64At M zp 6) (u64At M zp 7) (u64At M zp 8) (u64At M zp 9) ∧
      ∀ q, frBodyKeep q = true → reg n' q = reg n q := by
  obtain ⟨n0, v0, d0, hv0, u0⟩ := s.lwG hc fr_at_c (off' := 0x10) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 0) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv0
  obtain ⟨n1, v1, d1, hv1, u1⟩ := u0.lwG hc fr_at_10 (off' := 0x14) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 4) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv1
  obtain ⟨n2, v2, d2, hv2, u2⟩ := u1.luiG hc fr_at_14 (off' := 0x18) (by decide)
  obtain ⟨n3, v3, d3, hv3, u3⟩ := u2.lwG hc fr_at_18 (off' := 0x1A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 8) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv3
  obtain ⟨n4, v4, d4, hv4, u4⟩ := u3.lwG hc fr_at_1a (off' := 0x1E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 12) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv4
  obtain ⟨n5, v5, d5, hv5, u5⟩ := u4.lwG hc fr_at_1e (off' := 0x22) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 32) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv5
  obtain ⟨n6, v6, d6, hv6, u6⟩ := u5.lwG hc fr_at_22 (off' := 0x26) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 36) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv6
  obtain ⟨n7, v7, d7, hv7, u7⟩ := u6.aluImmG hc fr_at_26 (off' := 0x2A) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv7
  obtain ⟨n8, v8, d8, hv8, u8⟩ := u7.aluImmG hc fr_at_2a (off' := 0x2E) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv8
  obtain ⟨n9, v9, d9, hv9, u9⟩ := u8.aluImmG hc fr_at_2e (off' := 0x32) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv9
  obtain ⟨n10, v10, d10, hv10, u10⟩ := u9.aluG hc fr_at_32 (off' := 0x34) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv10
  obtain ⟨n11, v11, d11, hv11, u11⟩ := u10.aluG hc fr_at_34 (off' := 0x38) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv11
  obtain ⟨n12, v12, d12, hv12, u12⟩ := u11.aluG hc fr_at_38 (off' := 0x3C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv12
  obtain ⟨n13, v13, d13, hv13, u13⟩ := u12.lwG hc fr_at_3c (off' := 0x3E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 40) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv13
  obtain ⟨n14, v14, d14, hv14, u14⟩ := u13.lwG hc fr_at_3e (off' := 0x42) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 44) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv14
  obtain ⟨n15, v15, d15, hv15, u15⟩ := u14.aluG hc fr_at_42 (off' := 0x46) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv15
  obtain ⟨n16, v16, d16, hv16, u16⟩ := u15.aluImmG hc fr_at_46 (off' := 0x4A) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv16
  obtain ⟨n17, v17, d17, hv17, u17⟩ := u16.aluG hc fr_at_4a (off' := 0x4E) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv17
  obtain ⟨n18, v18, d18, hv18, u18⟩ := u17.aluImmG hc fr_at_4e (off' := 0x52) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv18
  obtain ⟨n19, v19, d19, hv19, u19⟩ := u18.aluImmG hc fr_at_52 (off' := 0x56) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv19
  obtain ⟨n20, v20, d20, hv20, u20⟩ := u19.aluG hc fr_at_56 (off' := 0x58) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv20
  obtain ⟨n21, v21, d21, hv21, u21⟩ := u20.aluImmG hc fr_at_58 (off' := 0x5C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv21
  obtain ⟨n22, v22, d22, hv22, u22⟩ := u21.aluG hc fr_at_5c (off' := 0x60) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv22
  obtain ⟨n23, v23, d23, hv23, u23⟩ := u22.aluG hc fr_at_60 (off' := 0x62) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv23
  obtain ⟨n24, v24, d24, hv24, u24⟩ := u23.aluG hc fr_at_62 (off' := 0x66) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv24
  obtain ⟨n25, v25, d25, hv25, u25⟩ := u24.aluG hc fr_at_66 (off' := 0x68) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv25
  obtain ⟨n26, v26, d26, hv26, u26⟩ := u25.aluG hc fr_at_68 (off' := 0x6C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv26
  obtain ⟨n27, v27, d27, hv27, u27⟩ := u26.lwG hc fr_at_6c (off' := 0x6E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 16) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv27
  obtain ⟨n28, v28, d28, hv28, u28⟩ := u27.lwG hc fr_at_6e (off' := 0x72) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 20) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv28
  obtain ⟨n29, v29, d29, hv29, u29⟩ := u28.aluImmG hc fr_at_72 (off' := 0x76) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv29
  obtain ⟨n30, v30, d30, hv30, u30⟩ := u29.aluImmG hc fr_at_76 (off' := 0x7A) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv30
  obtain ⟨n31, v31, d31, hv31, u31⟩ := u30.aluG hc fr_at_7a (off' := 0x7C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv31
  obtain ⟨n32, v32, d32, hv32, u32⟩ := u31.aluImmG hc fr_at_7c (off' := 0x80) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv32
  obtain ⟨n33, v33, d33, hv33, u33⟩ := u32.lwG hc fr_at_80 (off' := 0x84) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 24) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv33
  obtain ⟨n34, v34, d34, hv34, u34⟩ := u33.lwG hc fr_at_84 (off' := 0x88) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 28) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv34
  obtain ⟨n35, v35, d35, hv35, u35⟩ := u34.aluG hc fr_at_88 (off' := 0x8C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv35
  obtain ⟨n36, v36, d36, hv36, u36⟩ := u35.aluG hc fr_at_8c (off' := 0x90) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv36
  obtain ⟨n37, v37, d37, hv37, u37⟩ := u36.aluImmG hc fr_at_90 (off' := 0x94) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv37
  obtain ⟨n38, v38, d38, hv38, u38⟩ := u37.lwG hc fr_at_94 (off' := 0x96) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 48) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv38
  obtain ⟨n39, v39, d39, hv39, u39⟩ := u38.aluImmG hc fr_at_96 (off' := 0x9A) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv39
  obtain ⟨n40, v40, d40, hv40, u40⟩ := u39.lwG hc fr_at_9a (off' := 0x9C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 52) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv40
  obtain ⟨n41, v41, d41, hv41, u41⟩ := u40.aluG hc fr_at_9c (off' := 0xA0) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv41
  obtain ⟨n42, v42, d42, hv42, u42⟩ := u41.aluG hc fr_at_a0 (off' := 0xA2) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv42
  obtain ⟨n43, v43, d43, hv43, u43⟩ := u42.aluImmG hc fr_at_a2 (off' := 0xA4) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv43
  obtain ⟨n44, v44, d44, hv44, u44⟩ := u43.lwG hc fr_at_a4 (off' := 0xA6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 56) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv44
  obtain ⟨n45, v45, d45, hv45, u45⟩ := u44.lwG hc fr_at_a6 (off' := 0xAA) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 60) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv45
  obtain ⟨n46, v46, d46, hv46, u46⟩ := u45.aluG hc fr_at_aa (off' := 0xAE) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv46
  obtain ⟨n47, v47, d47, hv47, u47⟩ := u46.aluG hc fr_at_ae (off' := 0xB0) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv47
  obtain ⟨n48, v48, d48, hv48, u48⟩ := u47.aluG hc fr_at_b0 (off' := 0xB4) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv48
  obtain ⟨n49, v49, d49, hv49, u49⟩ := u48.aluG hc fr_at_b4 (off' := 0xB6) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv49
  obtain ⟨n50, v50, d50, hv50, u50⟩ := u49.aluG hc fr_at_b6 (off' := 0xB8) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv50
  obtain ⟨n51, v51, d51, hv51, u51⟩ := u50.aluImmG hc fr_at_b8 (off' := 0xBC) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv51
  obtain ⟨n52, v52, d52, hv52, u52⟩ := u51.aluImmG hc fr_at_bc (off' := 0xC0) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv52
  obtain ⟨n53, v53, d53, hv53, u53⟩ := u52.aluG hc fr_at_c0 (off' := 0xC2) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv53
  obtain ⟨n54, v54, d54, hv54, u54⟩ := u53.aluImmG hc fr_at_c2 (off' := 0xC6) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv54
  obtain ⟨n55, v55, d55, hv55, u55⟩ := u54.aluImmG hc fr_at_c6 (off' := 0xCA) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv55
  obtain ⟨n56, v56, d56, hv56, u56⟩ := u55.aluImmG hc fr_at_ca (off' := 0xCE) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv56
  obtain ⟨n57, v57, d57, hv57, u57⟩ := u56.aluG hc fr_at_ce (off' := 0xD0) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv57
  obtain ⟨n58, v58, d58, hv58, u58⟩ := u57.aluG hc fr_at_d0 (off' := 0xD4) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv58
  obtain ⟨n59, v59, d59, hv59, u59⟩ := u58.aluImmG hc fr_at_d4 (off' := 0xD6) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv59
  obtain ⟨n60, v60, d60, hv60, u60⟩ := u59.aluG hc fr_at_d6 (off' := 0xDA) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv60
  obtain ⟨n61, v61, d61, hv61, u61⟩ := u60.aluG hc fr_at_da (off' := 0xDC) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv61
  obtain ⟨n62, v62, d62, hv62, u62⟩ := u61.aluG hc fr_at_dc (off' := 0xE0) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv62
  obtain ⟨n63, v63, d63, hv63, u63⟩ := u62.aluG hc fr_at_e0 (off' := 0xE4) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv63
  obtain ⟨n64, v64, d64, hv64, u64⟩ := u63.aluG hc fr_at_e4 (off' := 0xE6) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv64
  obtain ⟨n65, v65, d65, hv65, u65⟩ := u64.aluImmG hc fr_at_e6 (off' := 0xEA) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv65
  obtain ⟨n66, v66, d66, hv66, u66⟩ := u65.lwG hc fr_at_ea (off' := 0xEC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 64) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv66
  obtain ⟨n67, v67, d67, hv67, u67⟩ := u66.aluImmG hc fr_at_ec (off' := 0xF0) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv67
  obtain ⟨n68, v68, d68, hv68, u68⟩ := u67.lwG hc fr_at_f0 (off' := 0xF2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 68) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv68
  obtain ⟨n69, v69, d69, hv69, u69⟩ := u68.aluG hc fr_at_f2 (off' := 0xF6) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv69
  obtain ⟨n70, v70, d70, hv70, u70⟩ := u69.aluG hc fr_at_f6 (off' := 0xF8) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv70
  obtain ⟨n71, v71, d71, hv71, u71⟩ := u70.aluImmG hc fr_at_f8 (off' := 0xFA) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv71
  obtain ⟨n72, v72, d72, hv72, u72⟩ := u71.lwG hc fr_at_fa (off' := 0xFC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 72) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv72
  obtain ⟨n73, v73, d73, hv73, u73⟩ := u72.lwG hc fr_at_fc (off' := 0xFE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, ha1]; exact aligned_add hz (k := 76) (by decide))
  simp +decide only [upd, ↓reduceIte, ha1] at hv73
  obtain ⟨n74, v74, d74, hv74, u74⟩ := u73.aluG hc fr_at_fe (off' := 0x102) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv74
  obtain ⟨n75, v75, d75, hv75, u75⟩ := u74.aluG hc fr_at_102 (off' := 0x104) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv75
  obtain ⟨n76, v76, d76, hv76, u76⟩ := u75.aluG hc fr_at_104 (off' := 0x108) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv76
  obtain ⟨n77, v77, d77, hv77, u77⟩ := u76.aluG hc fr_at_108 (off' := 0x10C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv77
  obtain ⟨n78, v78, d78, hv78, u78⟩ := u77.aluG hc fr_at_10c (off' := 0x10E) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv78
  obtain ⟨n79, v79, d79, hv79, u79⟩ := u78.aluImmG hc fr_at_10e (off' := 0x112) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv79
  obtain ⟨n80, v80, d80, hv80, u80⟩ := u79.aluImmG hc fr_at_112 (off' := 0x116) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv80
  obtain ⟨n81, v81, d81, hv81, u81⟩ := u80.aluImmG hc fr_at_116 (off' := 0x11A) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv81
  obtain ⟨n82, v82, d82, hv82, u82⟩ := u81.aluG hc fr_at_11a (off' := 0x11C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv82
  obtain ⟨n83, v83, d83, hv83, u83⟩ := u82.aluImmG hc fr_at_11c (off' := 0x11E) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv83
  obtain ⟨n84, v84, d84, hv84, u84⟩ := u83.aluG hc fr_at_11e (off' := 0x122) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv84
  obtain ⟨n85, v85, d85, hv85, u85⟩ := u84.aluG hc fr_at_122 (off' := 0x124) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv85
  obtain ⟨n86, v86, d86, hv86, u86⟩ := u85.aluG hc fr_at_124 (off' := 0x128) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv86
  obtain ⟨n87, v87, d87, hv87, u87⟩ := u86.aluImmG hc fr_at_128 (off' := 0x12C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv87
  obtain ⟨n88, v88, d88, hv88, u88⟩ := u87.aluG hc fr_at_12c (off' := 0x12E) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv88
  obtain ⟨n89, v89, d89, hv89, u89⟩ := u88.aluImmG hc fr_at_12e (off' := 0x132) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv89
  obtain ⟨n90, v90, d90, hv90, u90⟩ := u89.aluImmG hc fr_at_132 (off' := 0x136) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv90
  obtain ⟨n91, v91, d91, hv91, u91⟩ := u90.aluG hc fr_at_136 (off' := 0x138) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv91
  obtain ⟨n92, v92, d92, hv92, u92⟩ := u91.aluG hc fr_at_138 (off' := 0x13A) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv92
  obtain ⟨n93, v93, d93, hv93, u93⟩ := u92.aluImmG hc fr_at_13a (off' := 0x13C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv93
  obtain ⟨n94, v94, d94, hv94, u94⟩ := u93.aluImmG hc fr_at_13c (off' := 0x13E) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv94
  obtain ⟨n95, v95, d95, hv95, u95⟩ := u94.aluG hc fr_at_13e (off' := 0x142) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv95
  obtain ⟨n96, v96, d96, hv96, u96⟩ := u95.aluG hc fr_at_142 (off' := 0x146) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv96
  obtain ⟨n97, v97, d97, hv97, u97⟩ := u96.aluG hc fr_at_146 (off' := 0x14A) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv97
  obtain ⟨n98, v98, d98, hv98, u98⟩ := u97.aluG hc fr_at_14a (off' := 0x14C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv98
  obtain ⟨n99, v99, d99, hv99, u99⟩ := u98.aluImmG hc fr_at_14c (off' := 0x14E) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv99
  obtain ⟨n100, v100, d100, hv100, u100⟩ := u99.aluG hc fr_at_14e (off' := 0x152) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv100
  obtain ⟨n101, v101, d101, hv101, u101⟩ := u100.aluG hc fr_at_152 (off' := 0x154) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv101
  obtain ⟨n102, v102, d102, hv102, u102⟩ := u101.luiG hc fr_at_154 (off' := 0x158) (by decide)
  obtain ⟨n103, v103, d103, hv103, u103⟩ := u102.aluG hc fr_at_158 (off' := 0x15C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv103
  obtain ⟨n104, v104, d104, hv104, u104⟩ := u103.aluImmG hc fr_at_15c (off' := 0x15E) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv104
  obtain ⟨n105, v105, d105, hv105, u105⟩ := u104.aluG hc fr_at_15e (off' := 0x162) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv105
  obtain ⟨n106, v106, d106, hv106, u106⟩ := u105.aluG hc fr_at_162 (off' := 0x166) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv106
  obtain ⟨n107, v107, d107, hv107, u107⟩ := u106.aluImmG hc fr_at_166 (off' := 0x168) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv107
  obtain ⟨n108, v108, d108, hv108, u108⟩ := u107.aluG hc fr_at_168 (off' := 0x16A) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv108
  obtain ⟨n109, v109, d109, hv109, u109⟩ := u108.aluG hc fr_at_16a (off' := 0x16C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv109
  obtain ⟨n110, v110, d110, hv110, u110⟩ := u109.aluG hc fr_at_16c (off' := 0x170) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv110
  obtain ⟨n111, v111, d111, hv111, u111⟩ := u110.aluImmG hc fr_at_170 (off' := 0x174) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv111
  obtain ⟨n112, v112, d112, hv112, u112⟩ := u111.aluG hc fr_at_174 (off' := 0x176) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv112
  obtain ⟨n113, v113, d113, hv113, u113⟩ := u112.aluImmG hc fr_at_176 (off' := 0x178) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv113
  obtain ⟨n114, v114, d114, hv114, u114⟩ := u113.aluImmG hc fr_at_178 (off' := 0x17C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv114
  obtain ⟨n115, v115, d115, hv115, u115⟩ := u114.aluG hc fr_at_17c (off' := 0x17E) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv115
  obtain ⟨n116, v116, d116, hv116, u116⟩ := u115.aluG hc fr_at_17e (off' := 0x180) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv116
  obtain ⟨n117, v117, d117, hv117, u117⟩ := u116.aluG hc fr_at_180 (off' := 0x182) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv117
  obtain ⟨n118, v118, d118, hv118, u118⟩ := u117.aluG hc fr_at_182 (off' := 0x184) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv118
  obtain ⟨n119, v119, d119, hv119, u119⟩ := u118.aluG hc fr_at_184 (off' := 0x188) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv119
  obtain ⟨n120, v120, d120, hv120, u120⟩ := u119.aluG hc fr_at_188 (off' := 0x18C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv120
  obtain ⟨n121, v121, d121, hv121, u121⟩ := u120.aluG hc fr_at_18c (off' := 0x190) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv121
  obtain ⟨n122, v122, d122, hv122, u122⟩ := u121.aluG hc fr_at_190 (off' := 0x194) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv122
  obtain ⟨n123, v123, d123, hv123, u123⟩ := u122.aluG hc fr_at_194 (off' := 0x198) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv123
  obtain ⟨n124, v124, d124, hv124, u124⟩ := u123.aluG hc fr_at_198 (off' := 0x19C) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv124
  obtain ⟨n125, v125, d125, hv125, u125⟩ := u124.aluG hc fr_at_19c (off' := 0x1A0) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv125
  obtain ⟨n126, v126, d126, hv126, u126⟩ := u125.aluG hc fr_at_1a0 (off' := 0x1A4) (by decide)
  simp +decide only [upd, ↓reduceIte, ha1] at hv126
  have c2 : v2 = 0x4000000 := by rw [← hv2]; try rfl
  have t2 : v2.toNat = 67108864 := by rw [c2]; rfl
  have t7 : v7.toNat = v1.toNat * 2 ^ 6 % 2 ^ 32 := tn_sll hv7
  have t8 : v8.toNat = v0.toNat / 2 ^ 26 := tn_srl hv8
  have t9 : v9.toNat = v1.toNat / 2 ^ 26 := tn_srl hv9
  have t10 : v10.toNat = v8.toNat + v7.toNat := tn_orS' 26 (by decide) hv10 t8 t7
  have t11 : v11.toNat = (v4.toNat + v9.toNat) % 2 ^ 32 := tn_add hv11
  have t12 : v12.toNat = (v3.toNat + v10.toNat) % 2 ^ 32 := tn_add hv12
  have t15 : (v12.toNat < v3.toNat ∧ v15.toNat = 1) ∨ (v3.toNat ≤ v12.toNat ∧ v15.toNat = 0) := tn_sltu hv15
  have t16 : v16.toNat = v6.toNat * 2 ^ 6 % 2 ^ 32 := tn_sll hv16
  have t17 : v17.toNat = (v11.toNat + v15.toNat) % 2 ^ 32 := tn_add hv17
  have t18 : v18.toNat = v5.toNat / 2 ^ 26 := tn_srl hv18
  have c19 : v19 = 0x3FFFFFF := by rw [← hv19, c2]; try rfl
  have t19 : v19.toNat = 67108863 := by rw [c19]; rfl
  have t20 : v20.toNat = v18.toNat + v16.toNat := tn_orS' 26 (by decide) hv20 t18 t16
  have t21 : v21.toNat = v6.toNat / 2 ^ 26 := tn_srl hv21
  have t22 : v22.toNat = (v13.toNat + v20.toNat) % 2 ^ 32 := tn_add hv22
  have t23 : v23.toNat = (v21.toNat + v14.toNat) % 2 ^ 32 := tn_add hv23
  have t24 : (v22.toNat < v13.toNat ∧ v24.toNat = 1) ∨ (v13.toNat ≤ v22.toNat ∧ v24.toNat = 0) := tn_sltu hv24
  have t25 : v25.toNat = (v24.toNat + v23.toNat) % 2 ^ 32 := tn_add hv25
  have t26 : v26.toNat = v5.toNat % 2 ^ 26 := tn_and26 hv26 c19
  have t29 : v29.toNat = v17.toNat * 2 ^ 7 % 2 ^ 32 := tn_sll hv29
  have t30 : v30.toNat = v12.toNat / 2 ^ 25 := tn_srl hv30
  have t31 : v31.toNat = v30.toNat + v29.toNat := tn_orS' 25 (by decide) hv31 t30 t29
  have t32 : v32.toNat = v17.toNat / 2 ^ 25 := tn_srl hv32
  have t35 : v35.toNat = (v28.toNat + v32.toNat) % 2 ^ 32 := tn_add hv35
  have t36 : v36.toNat = (v27.toNat + v31.toNat) % 2 ^ 32 := tn_add hv36
  have t37 : v37.toNat = v25.toNat * 2 ^ 7 % 2 ^ 32 := tn_sll hv37
  have t39 : v39.toNat = v22.toNat / 2 ^ 25 := tn_srl hv39
  have t41 : (v36.toNat < v27.toNat ∧ v41.toNat = 1) ∨ (v27.toNat ≤ v36.toNat ∧ v41.toNat = 0) := tn_sltu hv41
  have t42 : v42.toNat = v39.toNat + v37.toNat := tn_orS' 25 (by decide) hv42 t39 t37
  have t43 : v43.toNat = v25.toNat / 2 ^ 25 := tn_srl hv43
  have t46 : v46.toNat = (v38.toNat + v42.toNat) % 2 ^ 32 := tn_add hv46
  have t47 : v47.toNat = (v43.toNat + v40.toNat) % 2 ^ 32 := tn_add hv47
  have t48 : (v46.toNat < v38.toNat ∧ v48.toNat = 1) ∨ (v38.toNat ≤ v46.toNat ∧ v48.toNat = 0) := tn_sltu hv48
  have t49 : v49.toNat = (v35.toNat + v41.toNat) % 2 ^ 32 := tn_add hv49
  have t50 : v50.toNat = (v47.toNat + v48.toNat) % 2 ^ 32 := tn_add hv50
  have t51 : v51.toNat = v49.toNat * 2 ^ 6 % 2 ^ 32 := tn_sll hv51
  have t52 : v52.toNat = v36.toNat / 2 ^ 26 := tn_srl hv52
  have t53 : v53.toNat = v52.toNat + v51.toNat := tn_orS 26 (by decide) hv53 t52 t51
  have t54 : v54.toNat = v49.toNat / 2 ^ 26 := tn_srl hv54
  have t55 : v55.toNat = v50.toNat * 2 ^ 6 % 2 ^ 32 := tn_sll hv55
  have t56 : v56.toNat = v46.toNat / 2 ^ 26 := tn_srl hv56
  have t57 : v57.toNat = (v34.toNat + v54.toNat) % 2 ^ 32 := tn_add hv57
  have t58 : v58.toNat = v56.toNat + v55.toNat := tn_orS 26 (by decide) hv58 t56 t55
  have t59 : v59.toNat = v50.toNat / 2 ^ 26 := tn_srl hv59
  have t60 : v60.toNat = (v44.toNat + v58.toNat) % 2 ^ 32 := tn_add hv60
  have t61 : v61.toNat = (v45.toNat + v59.toNat) % 2 ^ 32 := tn_add hv61
  have t62 : (v60.toNat < v44.toNat ∧ v62.toNat = 1) ∨ (v44.toNat ≤ v60.toNat ∧ v62.toNat = 0) := tn_sltu hv62
  have t63 : v63.toNat = (v33.toNat + v53.toNat) % 2 ^ 32 := tn_add hv63
  have t64 : v64.toNat = (v62.toNat + v61.toNat) % 2 ^ 32 := tn_add hv64
  have t65 : v65.toNat = v64.toNat * 2 ^ 7 % 2 ^ 32 := tn_sll hv65
  have t67 : v67.toNat = v60.toNat / 2 ^ 25 := tn_srl hv67
  have t69 : (v63.toNat < v33.toNat ∧ v69.toNat = 1) ∨ (v33.toNat ≤ v63.toNat ∧ v69.toNat = 0) := tn_sltu hv69
  have t70 : v70.toNat = v67.toNat + v65.toNat := tn_orS 25 (by decide) hv70 t67 t65
  have t71 : v71.toNat = v64.toNat / 2 ^ 25 := tn_srl hv71
  have t74 : v74.toNat = (v66.toNat + v70.toNat) % 2 ^ 32 := tn_add hv74
  have t75 : v75.toNat = (v71.toNat + v68.toNat) % 2 ^ 32 := tn_add hv75
  have t76 : (v74.toNat < v66.toNat ∧ v76.toNat = 1) ∨ (v66.toNat ≤ v74.toNat ∧ v76.toNat = 0) := tn_sltu hv76
  have t77 : v77.toNat = (v57.toNat + v69.toNat) % 2 ^ 32 := tn_add hv77
  have t78 : v78.toNat = (v75.toNat + v76.toNat) % 2 ^ 32 := tn_add hv78
  have t79 : v79.toNat = v78.toNat * 2 ^ 6 % 2 ^ 32 := tn_sll hv79
  have t80 : v80.toNat = v74.toNat / 2 ^ 26 := tn_srl hv80
  have t81 : v81.toNat = v77.toNat * 2 ^ 7 % 2 ^ 32 := tn_sll hv81
  have t82 : v82.toNat = v80.toNat + v79.toNat := tn_orS 26 (by decide) hv82 t80 t79
  have t83 : v83.toNat = v78.toNat / 2 ^ 26 := tn_srl hv83
  have t84 : v84.toNat = (v72.toNat + v82.toNat) % 2 ^ 32 := tn_add hv84
  have t85 : v85.toNat = (v73.toNat + v83.toNat) % 2 ^ 32 := tn_add hv85
  have t86 : (v84.toNat < v72.toNat ∧ v86.toNat = 1) ∨ (v72.toNat ≤ v84.toNat ∧ v86.toNat = 0) := tn_sltu hv86
  have t87 : v87.toNat = v63.toNat / 2 ^ 25 := tn_srl hv87
  have t88 : v88.toNat = (v85.toNat + v86.toNat) % 2 ^ 32 := tn_add hv88
  have t89 : v89.toNat = v88.toNat * 2 ^ 7 % 2 ^ 32 := tn_sll hv89
  have t90 : v90.toNat = v84.toNat / 2 ^ 25 := tn_srl hv90
  have t91 : v91.toNat = v87.toNat + v81.toNat := tn_orS 25 (by decide) hv91 t87 t81
  have t92 : v92.toNat = v90.toNat + v89.toNat := tn_orS 25 (by decide) hv92 t90 t89
  have t93 : v93.toNat = v88.toNat / 2 ^ 25 := tn_srl hv93
  have c94 : v94 = 0x13 := by rw [← hv94]; try rfl
  have t94 : v94.toNat = 19 := by rw [c94]; rfl
  have t95 : v95.toNat = v93.toNat * 19 % 2 ^ 32 := by rw [tn_mul hv95, t94]
  have t96 : v96.toNat = v92.toNat * 19 % 2 ^ 32 := by rw [tn_mul hv96, t94]
  have t97 : v97.toNat = v92.toNat * 19 / 2 ^ 32 := by rw [tn_mulhu hv97, t94]
  have t98 : v98.toNat = (v91.toNat + v26.toNat) % 2 ^ 32 := tn_add hv98
  have t99 : v99.toNat = v77.toNat / 2 ^ 25 := tn_srl hv99
  have t100 : (v98.toNat < v26.toNat ∧ v100.toNat = 1) ∨ (v26.toNat ≤ v98.toNat ∧ v100.toNat = 0) := tn_sltu hv100
  have t101 : v101.toNat = (v99.toNat + v100.toNat) % 2 ^ 32 := tn_add hv101
  have c102 : v102 = 0x2000000 := by rw [← hv102]; try rfl
  have t102 : v102.toNat = 33554432 := by rw [c102]; rfl
  have t103 : v103.toNat = v0.toNat % 2 ^ 26 := tn_and26 hv103 c19
  have c104 : v104 = 0x1FFFFFF := by rw [← hv104, c102]; try rfl
  have t104 : v104.toNat = 33554431 := by rw [c104]; rfl
  have t105 : v105.toNat = v12.toNat % 2 ^ 25 := tn_and25 hv105 c104
  have t106 : v106.toNat = v22.toNat % 2 ^ 25 := tn_and25 hv106 c104
  have t107 : v107.toNat = v101.toNat * 2 ^ 6 % 2 ^ 32 := tn_sll hv107
  have t108 : v108.toNat = (v103.toNat + v96.toNat) % 2 ^ 32 := tn_add hv108
  have t109 : v109.toNat = (v97.toNat + v95.toNat) % 2 ^ 32 := tn_add hv109
  have t110 : (v108.toNat < v96.toNat ∧ v110.toNat = 1) ∨ (v96.toNat ≤ v108.toNat ∧ v110.toNat = 0) := tn_sltu hv110
  have t111 : v111.toNat = v98.toNat / 2 ^ 26 := tn_srl hv111
  have t112 : v112.toNat = (v109.toNat + v110.toNat) % 2 ^ 32 := tn_add hv112
  have t113 : v113.toNat = v112.toNat * 2 ^ 6 % 2 ^ 32 := tn_sll hv113
  have t114 : v114.toNat = v108.toNat / 2 ^ 26 := tn_srl hv114
  have t115 : v115.toNat = v111.toNat + v107.toNat := tn_orS 26 (by decide) hv115 t111 t107
  have t116 : v116.toNat = v114.toNat + v113.toNat := tn_orS' 26 (by decide) hv116 t114 t113
  have t117 : v117.toNat = (v106.toNat + v115.toNat) % 2 ^ 32 := tn_add hv117
  have t118 : v118.toNat = (v116.toNat + v105.toNat) % 2 ^ 32 := tn_add hv118
  have t119 : v119.toNat = v108.toNat % 2 ^ 26 := tn_and26 hv119 c19
  have t120 : v120.toNat = v36.toNat % 2 ^ 26 := tn_and26 hv120 c19
  have t121 : v121.toNat = v63.toNat % 2 ^ 25 := tn_and25 hv121 c104
  have t122 : v122.toNat = v98.toNat % 2 ^ 26 := tn_and26 hv122 c19
  have t123 : v123.toNat = v46.toNat % 2 ^ 26 := tn_and26 hv123 c19
  have t124 : v124.toNat = v60.toNat % 2 ^ 25 := tn_and25 hv124 c104
  have t125 : v125.toNat = v74.toNat % 2 ^ 26 := tn_and26 hv125 c19
  have t126 : v126.toNat = v84.toNat % 2 ^ 25 := tn_and25 hv126 c104
  obtain ⟨Z0, eZ0⟩ : ∃ Z, u64At M zp 0 = Z := ⟨_, rfl⟩
  have hZ0 : v0.toNat + 2 ^ 32 * v1.toNat = Z0 := by
    rw [← eZ0, ← hv0, ← hv1]; rfl
  obtain ⟨Z1, eZ1⟩ : ∃ Z, u64At M zp 1 = Z := ⟨_, rfl⟩
  have hZ1 : v3.toNat + 2 ^ 32 * v4.toNat = Z1 := by
    rw [← eZ1, ← hv3, ← hv4]; rfl
  obtain ⟨Z2, eZ2⟩ : ∃ Z, u64At M zp 2 = Z := ⟨_, rfl⟩
  have hZ2 : v27.toNat + 2 ^ 32 * v28.toNat = Z2 := by
    rw [← eZ2, ← hv27, ← hv28]; rfl
  obtain ⟨Z3, eZ3⟩ : ∃ Z, u64At M zp 3 = Z := ⟨_, rfl⟩
  have hZ3 : v33.toNat + 2 ^ 32 * v34.toNat = Z3 := by
    rw [← eZ3, ← hv33, ← hv34]; rfl
  obtain ⟨Z4, eZ4⟩ : ∃ Z, u64At M zp 4 = Z := ⟨_, rfl⟩
  have hZ4 : v5.toNat + 2 ^ 32 * v6.toNat = Z4 := by
    rw [← eZ4, ← hv5, ← hv6]; rfl
  obtain ⟨Z5, eZ5⟩ : ∃ Z, u64At M zp 5 = Z := ⟨_, rfl⟩
  have hZ5 : v13.toNat + 2 ^ 32 * v14.toNat = Z5 := by
    rw [← eZ5, ← hv13, ← hv14]; rfl
  obtain ⟨Z6, eZ6⟩ : ∃ Z, u64At M zp 6 = Z := ⟨_, rfl⟩
  have hZ6 : v38.toNat + 2 ^ 32 * v40.toNat = Z6 := by
    rw [← eZ6, ← hv38, ← hv40]; rfl
  obtain ⟨Z7, eZ7⟩ : ∃ Z, u64At M zp 7 = Z := ⟨_, rfl⟩
  have hZ7 : v44.toNat + 2 ^ 32 * v45.toNat = Z7 := by
    rw [← eZ7, ← hv44, ← hv45]; rfl
  obtain ⟨Z8, eZ8⟩ : ∃ Z, u64At M zp 8 = Z := ⟨_, rfl⟩
  have hZ8 : v66.toNat + 2 ^ 32 * v68.toNat = Z8 := by
    rw [← eZ8, ← hv66, ← hv68]; rfl
  obtain ⟨Z9, eZ9⟩ : ∃ Z, u64At M zp 9 = Z := ⟨_, rfl⟩
  have hZ9 : v72.toNat + 2 ^ 32 * v73.toNat = Z9 := by
    rw [← eZ9, ← hv72, ← hv73]; rfl
  obtain ⟨X1, eX1⟩ : ∃ X, (Z1 + Z0 / 2 ^ 26) % 2 ^ 64 = X := ⟨_, rfl⟩
  have hX1 : v12.toNat + 2 ^ 32 * v17.toNat = X1 := fr_s0 t7 t8 t9 t10 t11 t12 t15 t17 hZ0 hZ1 eX1
  obtain ⟨X2, eX2⟩ : ∃ X, Z0 % 2 ^ 26 = X := ⟨_, rfl⟩
  have hX2 : v103.toNat = X2 := fr_s1 t103 hZ0 eX2
  obtain ⟨X3, eX3⟩ : ∃ X, (Z5 + Z4 / 2 ^ 26) % 2 ^ 64 = X := ⟨_, rfl⟩
  have hX3 : v22.toNat + 2 ^ 32 * v25.toNat = X3 := fr_s2 t16 t18 t20 t21 t22 t23 t24 t25 hZ4 hZ5 eX3
  obtain ⟨X4, eX4⟩ : ∃ X, Z4 % 2 ^ 26 = X := ⟨_, rfl⟩
  have hX4 : v26.toNat = X4 := fr_s3 t26 hZ4 eX4
  obtain ⟨X5, eX5⟩ : ∃ X, (Z2 + X1 / 2 ^ 25) % 2 ^ 64 = X := ⟨_, rfl⟩
  have hX5 : v36.toNat + 2 ^ 32 * v49.toNat = X5 := fr_s4 t29 t30 t31 t32 t35 t36 t41 t49 hX1 hZ2 eX5
  obtain ⟨X6, eX6⟩ : ∃ X, X1 % 2 ^ 25 = X := ⟨_, rfl⟩
  have hX6 : v105.toNat = X6 := fr_s5 t105 hX1 eX6
  obtain ⟨X7, eX7⟩ : ∃ X, (Z6 + X3 / 2 ^ 25) % 2 ^ 64 = X := ⟨_, rfl⟩
  have hX7 : v46.toNat + 2 ^ 32 * v50.toNat = X7 := fr_s6 t37 t39 t42 t43 t46 t47 t48 t50 hX3 hZ6 eX7
  obtain ⟨X8, eX8⟩ : ∃ X, X3 % 2 ^ 25 = X := ⟨_, rfl⟩
  have hX8 : v106.toNat = X8 := fr_s7 t106 hX3 eX8
  obtain ⟨X9, eX9⟩ : ∃ X, (Z3 + X5 / 2 ^ 26) % 2 ^ 64 = X := ⟨_, rfl⟩
  have hX9 : v63.toNat + 2 ^ 32 * v77.toNat = X9 := fr_s8 t51 t52 t53 t54 t57 t63 t69 t77 hX5 hZ3 eX9
  obtain ⟨X10, eX10⟩ : ∃ X, X5 % 2 ^ 26 = X := ⟨_, rfl⟩
  have hX10 : v120.toNat = X10 := fr_s9 t120 hX5 eX10
  obtain ⟨X11, eX11⟩ : ∃ X, (Z7 + X7 / 2 ^ 26) % 2 ^ 64 = X := ⟨_, rfl⟩
  have hX11 : v60.toNat + 2 ^ 32 * v64.toNat = X11 := fr_s10 t55 t56 t58 t59 t60 t61 t62 t64 hX7 hZ7 eX11
  obtain ⟨X12, eX12⟩ : ∃ X, X7 % 2 ^ 26 = X := ⟨_, rfl⟩
  have hX12 : v123.toNat = X12 := fr_s11 t123 hX7 eX12
  obtain ⟨X13, eX13⟩ : ∃ X, (X4 + X9 / 2 ^ 25) % 2 ^ 64 = X := ⟨_, rfl⟩
  have hX13 : v98.toNat + 2 ^ 32 * v101.toNat = X13 := fr_s12 t81 t87 t91 t98 t99 t100 t101 hX4 hX9 eX13
  obtain ⟨X14, eX14⟩ : ∃ X, X9 % 2 ^ 25 = X := ⟨_, rfl⟩
  have hX14 : v121.toNat = X14 := fr_s13 t121 hX9 eX14
  obtain ⟨X15, eX15⟩ : ∃ X, (Z8 + X11 / 2 ^ 25) % 2 ^ 64 = X := ⟨_, rfl⟩
  have hX15 : v74.toNat + 2 ^ 32 * v78.toNat = X15 := fr_s14 t65 t67 t70 t71 t74 t75 t76 t78 hX11 hZ8 eX15
  obtain ⟨X16, eX16⟩ : ∃ X, X11 % 2 ^ 25 = X := ⟨_, rfl⟩
  have hX16 : v124.toNat = X16 := fr_s15 t124 hX11 eX16
  obtain ⟨X17, eX17⟩ : ∃ X, (X8 + X13 / 2 ^ 26) % 2 ^ 64 = X := ⟨_, rfl⟩
  have hX17 : v117.toNat = X17 % 2 ^ 32 := fr_s16 t107 t111 t115 t117 hX8 hX13 eX17
  obtain ⟨X18, eX18⟩ : ∃ X, X13 % 2 ^ 26 = X := ⟨_, rfl⟩
  have hX18 : v122.toNat = X18 := fr_s17 t122 hX13 eX18
  obtain ⟨X19, eX19⟩ : ∃ X, (Z9 + X15 / 2 ^ 26) % 2 ^ 64 = X := ⟨_, rfl⟩
  have hX19 : v84.toNat + 2 ^ 32 * v88.toNat = X19 := fr_s18 t79 t80 t82 t83 t84 t85 t86 t88 hX15 hZ9 eX19
  obtain ⟨X20, eX20⟩ : ∃ X, X15 % 2 ^ 26 = X := ⟨_, rfl⟩
  have hX20 : v125.toNat = X20 := fr_s19 t125 hX15 eX20
  obtain ⟨X21, eX21⟩ : ∃ X, X19 / 2 ^ 25 = X := ⟨_, rfl⟩
  have hX21 : v92.toNat + 2 ^ 32 * v93.toNat = X21 := fr_s20 t89 t90 t92 t93 hX19 eX21
  obtain ⟨X22, eX22⟩ : ∃ X, 19 * X21 % 2 ^ 64 = X := ⟨_, rfl⟩
  have hX22 : v96.toNat + 2 ^ 32 * v109.toNat = X22 := fr_s21 t95 t96 t97 t109 hX21 eX22
  obtain ⟨X23, eX23⟩ : ∃ X, (X2 + X22) % 2 ^ 64 = X := ⟨_, rfl⟩
  have hX23 : v108.toNat + 2 ^ 32 * v112.toNat = X23 := fr_s22 t108 t110 t112 hX2 hX22 eX23
  obtain ⟨X24, eX24⟩ : ∃ X, X19 % 2 ^ 25 = X := ⟨_, rfl⟩
  have hX24 : v126.toNat = X24 := fr_s23 t126 hX19 eX24
  obtain ⟨X25, eX25⟩ : ∃ X, (X6 + X23 / 2 ^ 26) % 2 ^ 64 = X := ⟨_, rfl⟩
  have hX25 : v118.toNat = X25 % 2 ^ 32 := fr_s24 t113 t114 t116 t118 hX6 hX23 eX25
  obtain ⟨X26, eX26⟩ : ∃ X, X23 % 2 ^ 26 = X := ⟨_, rfl⟩
  have hX26 : v119.toNat = X26 := fr_s25 t119 hX23 eX26
  have o12 : reg n126 a2 = v119 := by rw [u126.regs]; simp +decide only [upd, ↓reduceIte]
  have o13 : reg n126 a3 = v118 := by rw [u126.regs]; simp +decide only [upd, ↓reduceIte]
  have o14 : reg n126 a4 = v120 := by rw [u126.regs]; simp +decide only [upd, ↓reduceIte]
  have o8 : reg n126 (8 : Fin 32) = v121 := by rw [u126.regs]; simp +decide only [upd, ↓reduceIte]
  have o15 : reg n126 a5 = v122 := by rw [u126.regs]; simp +decide only [upd, ↓reduceIte]
  have o5 : reg n126 (5 : Fin 32) = v117 := by rw [u126.regs]; simp +decide only [upd, ↓reduceIte]
  have o11 : reg n126 a1 = v123 := by rw [u126.regs]; simp +decide only [upd, ↓reduceIte]
  have o16 : reg n126 a6 = v124 := by rw [u126.regs]; simp +decide only [upd, ↓reduceIte]
  have o6 : reg n126 (6 : Fin 32) = v125 := by rw [u126.regs]; simp +decide only [upd, ↓reduceIte]
  have o9 : reg n126 (9 : Fin 32) = v126 := by rw [u126.regs]; simp +decide only [upd, ↓reduceIte]
  refine ⟨n126, (.cons d0 (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18 (.cons d19 (.cons d20 (.cons d21 (.cons d22 (.cons d23 (.cons d24 (.cons d25 (.cons d26 (.cons d27 (.cons d28 (.cons d29 (.cons d30 (.cons d31 (.cons d32 (.cons d33 (.cons d34 (.cons d35 (.cons d36 (.cons d37 (.cons d38 (.cons d39 (.cons d40 (.cons d41 (.cons d42 (.cons d43 (.cons d44 (.cons d45 (.cons d46 (.cons d47 (.cons d48 (.cons d49 (.cons d50 (.cons d51 (.cons d52 (.cons d53 (.cons d54 (.cons d55 (.cons d56 (.cons d57 (.cons d58 (.cons d59 (.cons d60 (.cons d61 (.cons d62 (.cons d63 (.cons d64 (.cons d65 (.cons d66 (.cons d67 (.cons d68 (.cons d69 (.cons d70 (.cons d71 (.cons d72 (.cons d73 (.cons d74 (.cons d75 (.cons d76 (.cons d77 (.cons d78 (.cons d79 (.cons d80 (.cons d81 (.cons d82 (.cons d83 (.cons d84 (.cons d85 (.cons d86 (.cons d87 (.cons d88 (.cons d89 (.cons d90 (.cons d91 (.cons d92 (.cons d93 (.cons d94 (.cons d95 (.cons d96 (.cons d97 (.cons d98 (.cons d99 (.cons d100 (.cons d101 (.cons d102 (.cons d103 (.cons d104 (.cons d105 (.cons d106 (.cons d107 (.cons d108 (.cons d109 (.cons d110 (.cons d111 (.cons d112 (.cons d113 (.cons d114 (.cons d115 (.cons d116 (.cons d117 (.cons d118 (.cons d119 (.cons d120 (.cons d121 (.cons d122 (.cons d123 (.cons d124 (.cons d125 (.single d126))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), u126.self, ?_, ?_⟩
  · rw [o12, o13, o14, o8, o15, o5, o11, o16, o6, o9, eZ0, eZ1, eZ2, eZ3, eZ4, eZ5, eZ6, eZ7, eZ8, eZ9]
    simp only [List.map_cons, List.map_nil, feReduceSpec]
    rw [eX1, eX2, eX3, eX4, eX5, eX6, eX7, eX8, eX9, eX10, eX11, eX12, eX13, eX14, eX15, eX16, eX17, eX18, eX19, eX20, eX21, eX22, eX23, eX24, eX25, eX26]
    rw [hX26, hX25, hX10, hX14, hX18, hX17, hX12, hX16, hX20, hX24]
    rw [small_mod (by decide) eX26, small_mod (by decide) eX10, small_mod (by decide) eX14, small_mod (by decide) eX18, small_mod (by decide) eX12, small_mod (by decide) eX16, small_mod (by decide) eX20, small_mod (by decide) eX24]
  · intro q hq
    rw [u126.regs]
    have ⟨q5, q6, q7, q8, q9, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q28, q29, q30, q31⟩ : q ≠ (5 : Fin 32) ∧ q ≠ (6 : Fin 32) ∧ q ≠ (7 : Fin 32) ∧ q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ (18 : Fin 32) ∧ q ≠ (19 : Fin 32) ∧ q ≠ (20 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ (31 : Fin 32) :=
      ⟨bkeep_ne hq (r := (5 : Fin 32)) rfl, bkeep_ne hq (r := (6 : Fin 32)) rfl, bkeep_ne hq (r := (7 : Fin 32)) rfl, bkeep_ne hq (r := (8 : Fin 32)) rfl, bkeep_ne hq (r := (9 : Fin 32)) rfl, bkeep_ne hq (r := a1) rfl, bkeep_ne hq (r := a2) rfl, bkeep_ne hq (r := a3) rfl, bkeep_ne hq (r := a4) rfl, bkeep_ne hq (r := a5) rfl, bkeep_ne hq (r := a6) rfl, bkeep_ne hq (r := a7) rfl, bkeep_ne hq (r := (18 : Fin 32)) rfl, bkeep_ne hq (r := (19 : Fin 32)) rfl, bkeep_ne hq (r := (20 : Fin 32)) rfl, bkeep_ne hq (r := (28 : Fin 32)) rfl, bkeep_ne hq (r := (29 : Fin 32)) rfl, bkeep_ne hq (r := (30 : Fin 32)) rfl, bkeep_ne hq (r := (31 : Fin 32)) rfl⟩
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact s.zero.symm
    · simp [upd, h0, q5, q6, q7, q8, q9, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q28, q29, q30, q31]

end C3.RV32
