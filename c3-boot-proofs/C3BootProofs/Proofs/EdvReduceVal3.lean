import C3BootProofs.Proofs.EdvReduceFacts

/-! # The inlined `Scalar::reduce`'s values, part 3

Each lemma proves one value the code holds in words from its instructions' facts. `scripts/gen-ev-reduce.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option maxHeartbeats 10000000 in
theorem evr_v_R1 {v991 v997 : Word}
     :
    v991.toNat = (v991.toNat + 2 ^ 32 * v997.toNat) % 2 ^ 32 := by
  have := v991.isLt; have := v997.isLt
  generalize v991.toNat = n991 at *
  generalize v997.toNat = n997 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_C10 {v991 v997 v1033 v1034 v1035 v1037 : Word}
    (t1033 : v1033.toNat = v997.toNat * 2 ^ 3 % 2 ^ 32)
    (t1034 : v1034.toNat = v991.toNat / 2 ^ 29)
    (t1035 : v1035.toNat = v1034.toNat + v1033.toNat)
    (t1037 : v1037.toNat = v997.toNat / 2 ^ 29) :
    v1035.toNat + 2 ^ 32 * v1037.toNat = (v991.toNat + 2 ^ 32 * v997.toNat) / 2 ^ 29 := by
  have := v991.isLt; have := v997.isLt; have := v1033.isLt; have := v1034.isLt; have := v1035.isLt; have := v1037.isLt
  generalize v991.toNat = n991 at *
  generalize v997.toNat = n997 at *
  generalize v1033.toNat = n1033 at *
  generalize v1034.toNat = n1034 at *
  generalize v1035.toNat = n1035 at *
  generalize v1037.toNat = n1037 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN3L8 {v8 v15 v16 v36 v54 v55 v56 v57 v59 v69 v74 v98 v111 v120 v122 v147 v151 v195 v219 v233 v262 v279 v281 v283 v293 v294 v299 v304 v305 v307 v315 v328 v332 v333 v335 v347 v352 v363 v366 v1018 v1021 : Word}
    (t335 : v335.toNat = v332.toNat * 307527195 % 2 ^ 32)
    (t1018 : v1018.toNat = v335.toNat * 2 ^ 20 % 2 ^ 32)
    (t1021 : v1021.toNat = v352.toNat / 2 ^ 12)
    (wN3 : v352.toNat = ((v332.toNat + 2 ^ 32 * v366.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wS3 : v332.toNat + 2 ^ 32 * v366.toNat = ((v304.toNat + 2 ^ 32 * v363.toNat) + (v111.toNat + 2 ^ 32 * v122.toNat) + (v305.toNat + 2 ^ 32 * v328.toNat) + (v307.toNat + 2 ^ 32 * v333.toNat) + (v315.toNat + 2 ^ 32 * v347.toNat)) % 2 ^ 64)
    (wC2 : v304.toNat + 2 ^ 32 * v363.toNat = (v294.toNat + 2 ^ 32 * v299.toNat) / 2 ^ 29)
    (wZ3 : v111.toNat + 2 ^ 32 * v122.toNat = ((v54.toNat + 2 ^ 32 * v55.toNat) + (v56.toNat + 2 ^ 32 * v57.toNat) + (v69.toNat + 2 ^ 32 * v59.toNat) + (v98.toNat + 2 ^ 32 * v74.toNat)) % 2 ^ 64)
    (wPN0L3 : v305.toNat + 2 ^ 32 * v328.toNat = v151.toNat * 502512965)
    (wPN1L2 : v307.toNat + 2 ^ 32 * v333.toNat = v219.toNat * 501691798)
    (wPN2L1 : v315.toNat + 2 ^ 32 * v347.toNat = v279.toNat * 9640146)
    (wT2 : v294.toNat + 2 ^ 32 * v299.toNat = ((v262.toNat + 2 ^ 32 * v293.toNat) + (v281.toNat + 2 ^ 32 * v283.toNat)) % 2 ^ 64)
    (wPA0B3 : v54.toNat + 2 ^ 32 * v55.toNat = v8.toNat * (377041255))
    (wPA1B2 : v56.toNat + 2 ^ 32 * v57.toNat = v15.toNat * (259787148))
    (wPA2B1 : v69.toNat + 2 ^ 32 * v59.toNat = v16.toNat * (442594051))
    (wPA3B0 : v98.toNat + 2 ^ 32 * v74.toNat = v36.toNat * (290322925))
    (wN0 : v151.toNat = ((v120.toNat + 2 ^ 32 * v147.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN1 : v219.toNat = ((v195.toNat + 2 ^ 32 * v233.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN2 : v279.toNat = ((v262.toNat + 2 ^ 32 * v293.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v1018.toNat + 2 ^ 32 * v1021.toNat = v352.toNat * 1048576 := by
  have := v8.isLt; have := v15.isLt; have := v16.isLt; have := v36.isLt; have := v54.isLt; have := v55.isLt; have := v56.isLt; have := v57.isLt; have := v59.isLt; have := v69.isLt; have := v74.isLt; have := v98.isLt; have := v111.isLt; have := v120.isLt; have := v122.isLt; have := v147.isLt; have := v151.isLt; have := v195.isLt; have := v219.isLt; have := v233.isLt; have := v262.isLt; have := v279.isLt; have := v281.isLt; have := v283.isLt; have := v293.isLt; have := v294.isLt; have := v299.isLt; have := v304.isLt; have := v305.isLt; have := v307.isLt; have := v315.isLt; have := v328.isLt; have := v332.isLt; have := v333.isLt; have := v335.isLt; have := v347.isLt; have := v352.isLt; have := v363.isLt; have := v366.isLt; have := v1018.isLt; have := v1021.isLt
  generalize v8.toNat = n8 at *
  generalize v15.toNat = n15 at *
  generalize v16.toNat = n16 at *
  generalize v36.toNat = n36 at *
  generalize v54.toNat = n54 at *
  generalize v55.toNat = n55 at *
  generalize v56.toNat = n56 at *
  generalize v57.toNat = n57 at *
  generalize v59.toNat = n59 at *
  generalize v69.toNat = n69 at *
  generalize v74.toNat = n74 at *
  generalize v98.toNat = n98 at *
  generalize v111.toNat = n111 at *
  generalize v120.toNat = n120 at *
  generalize v122.toNat = n122 at *
  generalize v147.toNat = n147 at *
  generalize v151.toNat = n151 at *
  generalize v195.toNat = n195 at *
  generalize v219.toNat = n219 at *
  generalize v233.toNat = n233 at *
  generalize v262.toNat = n262 at *
  generalize v279.toNat = n279 at *
  generalize v281.toNat = n281 at *
  generalize v283.toNat = n283 at *
  generalize v293.toNat = n293 at *
  generalize v294.toNat = n294 at *
  generalize v299.toNat = n299 at *
  generalize v304.toNat = n304 at *
  generalize v305.toNat = n305 at *
  generalize v307.toNat = n307 at *
  generalize v315.toNat = n315 at *
  generalize v328.toNat = n328 at *
  generalize v332.toNat = n332 at *
  generalize v333.toNat = n333 at *
  generalize v335.toNat = n335 at *
  generalize v347.toNat = n347 at *
  generalize v352.toNat = n352 at *
  generalize v363.toNat = n363 at *
  generalize v366.toNat = n366 at *
  generalize v1018.toNat = n1018 at *
  generalize v1021.toNat = n1021 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN7L4 {v722 v1011 v1013 : Word}
    (t1011 : v1011.toNat = v722.toNat * 333 % 2 ^ 32)
    (t1013 : v1013.toNat = v722.toNat * 333 / 2 ^ 32) :
    v1011.toNat + 2 ^ 32 * v1013.toNat = v722.toNat * 333 := by
  have := v722.isLt; have := v1011.isLt; have := v1013.isLt
  generalize v722.toNat = n722 at *
  generalize v1011.toNat = n1011 at *
  generalize v1013.toNat = n1013 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN8L3 {v819 v1016 v1019 : Word}
    (t1016 : v1016.toNat = v819.toNat * 502512965 % 2 ^ 32)
    (t1019 : v1019.toNat = v819.toNat * 502512965 / 2 ^ 32) :
    v1016.toNat + 2 ^ 32 * v1019.toNat = v819.toNat * 502512965 := by
  have := v819.isLt; have := v1016.isLt; have := v1019.isLt
  generalize v819.toNat = n819 at *
  generalize v1016.toNat = n1016 at *
  generalize v1019.toNat = n1019 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S11 {v1009 v1011 v1013 v1015 v1016 v1018 v1019 v1021 v1022 v1023 v1024 v1025 v1026 v1027 v1028 v1029 v1030 v1031 v1032 v1035 v1036 v1037 v1038 v1041 v1042 v1043 : Word}
    (t1023 : v1023.toNat = (v1021.toNat + v1015.toNat) % 2 ^ 32)
    (t1024 : v1022.toNat + 2 ^ 32 * v1024.toNat = v1018.toNat + v1009.toNat)
    (t1025 : v1025.toNat = (v1023.toNat + v1024.toNat) % 2 ^ 32)
    (t1027 : v1027.toNat = (v1025.toNat + v1013.toNat) % 2 ^ 32)
    (t1028 : v1026.toNat + 2 ^ 32 * v1028.toNat = v1011.toNat + v1022.toNat)
    (t1029 : v1029.toNat = (v1027.toNat + v1028.toNat) % 2 ^ 32)
    (t1031 : v1031.toNat = (v1029.toNat + v1019.toNat) % 2 ^ 32)
    (t1032 : v1030.toNat + 2 ^ 32 * v1032.toNat = v1016.toNat + v1026.toNat)
    (t1036 : v1036.toNat = (v1031.toNat + v1032.toNat) % 2 ^ 32)
    (t1041 : v1041.toNat = (v1036.toNat + v1037.toNat) % 2 ^ 32)
    (t1042 : v1038.toNat + 2 ^ 32 * v1042.toNat = v1030.toNat + v1035.toNat)
    (t1043 : v1043.toNat = (v1041.toNat + v1042.toNat) % 2 ^ 32) :
    v1038.toNat + 2 ^ 32 * v1043.toNat = ((v1035.toNat + 2 ^ 32 * v1037.toNat) + (v1009.toNat + 2 ^ 32 * v1015.toNat) + (v1018.toNat + 2 ^ 32 * v1021.toNat) + (v1011.toNat + 2 ^ 32 * v1013.toNat) + (v1016.toNat + 2 ^ 32 * v1019.toNat)) % 2 ^ 64 := by
  obtain ⟨q1023, eq1023⟩ := mod_q t1023; clear t1023
  obtain ⟨q1025, eq1025⟩ := mod_q t1025; clear t1025
  obtain ⟨q1027, eq1027⟩ := mod_q t1027; clear t1027
  obtain ⟨q1029, eq1029⟩ := mod_q t1029; clear t1029
  obtain ⟨q1031, eq1031⟩ := mod_q t1031; clear t1031
  obtain ⟨q1036, eq1036⟩ := mod_q t1036; clear t1036
  obtain ⟨q1041, eq1041⟩ := mod_q t1041; clear t1041
  obtain ⟨q1043, eq1043⟩ := mod_q t1043; clear t1043
  have key : v1038.toNat + 2 ^ 32 * v1043.toNat + 2 ^ 64 * (q1023 + q1025 + q1027 + q1029 + q1031 + q1036 + q1041 + q1043) = ((v1035.toNat + 2 ^ 32 * v1037.toNat) + (v1009.toNat + 2 ^ 32 * v1015.toNat) + (v1018.toNat + 2 ^ 32 * v1021.toNat) + (v1011.toNat + 2 ^ 32 * v1013.toNat) + (v1016.toNat + 2 ^ 32 * v1019.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v1009.toNat = n1009 at *
    generalize v1011.toNat = n1011 at *
    generalize v1013.toNat = n1013 at *
    generalize v1015.toNat = n1015 at *
    generalize v1016.toNat = n1016 at *
    generalize v1018.toNat = n1018 at *
    generalize v1019.toNat = n1019 at *
    generalize v1021.toNat = n1021 at *
    generalize v1022.toNat = n1022 at *
    generalize v1023.toNat = n1023 at *
    generalize v1024.toNat = n1024 at *
    generalize v1025.toNat = n1025 at *
    generalize v1026.toNat = n1026 at *
    generalize v1027.toNat = n1027 at *
    generalize v1028.toNat = n1028 at *
    generalize v1029.toNat = n1029 at *
    generalize v1030.toNat = n1030 at *
    generalize v1031.toNat = n1031 at *
    generalize v1032.toNat = n1032 at *
    generalize v1035.toNat = n1035 at *
    generalize v1036.toNat = n1036 at *
    generalize v1037.toNat = n1037 at *
    generalize v1038.toNat = n1038 at *
    generalize v1041.toNat = n1041 at *
    generalize v1042.toNat = n1042 at *
    generalize v1043.toNat = n1043 at *
    omega
  exact smm_key key (smm_lt v1038 v1043)

set_option maxHeartbeats 10000000 in
theorem evr_v_R2 {v1038 v1043 : Word}
     :
    v1038.toNat = (v1038.toNat + 2 ^ 32 * v1043.toNat) % 2 ^ 32 := by
  have := v1038.isLt; have := v1043.isLt
  generalize v1038.toNat = n1038 at *
  generalize v1043.toNat = n1043 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_C11 {v1038 v1043 v1052 v1055 v1057 v1059 : Word}
    (t1052 : v1052.toNat = v1043.toNat * 2 ^ 3 % 2 ^ 32)
    (t1055 : v1055.toNat = v1038.toNat / 2 ^ 29)
    (t1057 : v1057.toNat = v1055.toNat + v1052.toNat)
    (t1059 : v1059.toNat = v1043.toNat / 2 ^ 29) :
    v1057.toNat + 2 ^ 32 * v1059.toNat = (v1038.toNat + 2 ^ 32 * v1043.toNat) / 2 ^ 29 := by
  have := v1038.isLt; have := v1043.isLt; have := v1052.isLt; have := v1055.isLt; have := v1057.isLt; have := v1059.isLt
  generalize v1038.toNat = n1038 at *
  generalize v1043.toNat = n1043 at *
  generalize v1052.toNat = n1052 at *
  generalize v1055.toNat = n1055 at *
  generalize v1057.toNat = n1057 at *
  generalize v1059.toNat = n1059 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN4L8 {v8 v15 v16 v36 v76 v77 v78 v79 v83 v85 v87 v89 v92 v93 v103 v116 v120 v124 v147 v151 v195 v219 v233 v262 v279 v293 v332 v352 v354 v356 v366 v367 v375 v376 v379 v381 v382 v384 v386 v389 v395 v401 v403 v405 v417 v419 v425 v1045 v1047 : Word}
    (t405 : v405.toNat = v403.toNat * 307527195 % 2 ^ 32)
    (t1045 : v1045.toNat = v405.toNat * 2 ^ 20 % 2 ^ 32)
    (t1047 : v1047.toNat = v419.toNat / 2 ^ 12)
    (wN4 : v419.toNat = ((v403.toNat + 2 ^ 32 * v425.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wS4 : v403.toNat + 2 ^ 32 * v425.toNat = ((v389.toNat + 2 ^ 32 * v417.toNat) + (v116.toNat + 2 ^ 32 * v124.toNat) + (v375.toNat + 2 ^ 32 * v376.toNat) + (v381.toNat + 2 ^ 32 * v382.toNat) + (v384.toNat + 2 ^ 32 * v395.toNat) + (v386.toNat + 2 ^ 32 * v401.toNat)) % 2 ^ 64)
    (wC3 : v389.toNat + 2 ^ 32 * v417.toNat = (v367.toNat + 2 ^ 32 * v379.toNat) / 2 ^ 29)
    (wZ4 : v116.toNat + 2 ^ 32 * v124.toNat = ((v76.toNat + 2 ^ 32 * v77.toNat) + (v78.toNat + 2 ^ 32 * v79.toNat) + (v85.toNat + 2 ^ 32 * v83.toNat) + (v89.toNat + 2 ^ 32 * v92.toNat) + (v103.toNat + 2 ^ 32 * v93.toNat)) % 2 ^ 64)
    (wPN0L4 : v375.toNat + 2 ^ 32 * v376.toNat = v151.toNat * 333)
    (wPN1L3 : v381.toNat + 2 ^ 32 * v382.toNat = v219.toNat * 502512965)
    (wPN2L2 : v384.toNat + 2 ^ 32 * v395.toNat = v279.toNat * 501691798)
    (wPN3L1 : v386.toNat + 2 ^ 32 * v401.toNat = v352.toNat * 9640146)
    (wT3 : v367.toNat + 2 ^ 32 * v379.toNat = ((v332.toNat + 2 ^ 32 * v366.toNat) + (v354.toNat + 2 ^ 32 * v356.toNat)) % 2 ^ 64)
    (wPA0B4 : v76.toNat + 2 ^ 32 * v77.toNat = v8.toNat * (536700270))
    (wPA1B3 : v78.toNat + 2 ^ 32 * v79.toNat = v15.toNat * (377041255))
    (wPA2B2 : v85.toNat + 2 ^ 32 * v83.toNat = v16.toNat * (259787148))
    (wPA3B1 : v89.toNat + 2 ^ 32 * v92.toNat = v36.toNat * (442594051))
    (wPA4B0 : v103.toNat + 2 ^ 32 * v93.toNat = v87.toNat * (290322925))
    (wN0 : v151.toNat = ((v120.toNat + 2 ^ 32 * v147.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN1 : v219.toNat = ((v195.toNat + 2 ^ 32 * v233.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN2 : v279.toNat = ((v262.toNat + 2 ^ 32 * v293.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN3 : v352.toNat = ((v332.toNat + 2 ^ 32 * v366.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v1045.toNat + 2 ^ 32 * v1047.toNat = v419.toNat * 1048576 := by
  have := v8.isLt; have := v15.isLt; have := v16.isLt; have := v36.isLt; have := v76.isLt; have := v77.isLt; have := v78.isLt; have := v79.isLt; have := v83.isLt; have := v85.isLt; have := v87.isLt; have := v89.isLt; have := v92.isLt; have := v93.isLt; have := v103.isLt; have := v116.isLt; have := v120.isLt; have := v124.isLt; have := v147.isLt; have := v151.isLt; have := v195.isLt; have := v219.isLt; have := v233.isLt; have := v262.isLt; have := v279.isLt; have := v293.isLt; have := v332.isLt; have := v352.isLt; have := v354.isLt; have := v356.isLt; have := v366.isLt; have := v367.isLt; have := v375.isLt; have := v376.isLt; have := v379.isLt; have := v381.isLt; have := v382.isLt; have := v384.isLt; have := v386.isLt; have := v389.isLt; have := v395.isLt; have := v401.isLt; have := v403.isLt; have := v405.isLt; have := v417.isLt; have := v419.isLt; have := v425.isLt; have := v1045.isLt; have := v1047.isLt
  generalize v8.toNat = n8 at *
  generalize v15.toNat = n15 at *
  generalize v16.toNat = n16 at *
  generalize v36.toNat = n36 at *
  generalize v76.toNat = n76 at *
  generalize v77.toNat = n77 at *
  generalize v78.toNat = n78 at *
  generalize v79.toNat = n79 at *
  generalize v83.toNat = n83 at *
  generalize v85.toNat = n85 at *
  generalize v87.toNat = n87 at *
  generalize v89.toNat = n89 at *
  generalize v92.toNat = n92 at *
  generalize v93.toNat = n93 at *
  generalize v103.toNat = n103 at *
  generalize v116.toNat = n116 at *
  generalize v120.toNat = n120 at *
  generalize v124.toNat = n124 at *
  generalize v147.toNat = n147 at *
  generalize v151.toNat = n151 at *
  generalize v195.toNat = n195 at *
  generalize v219.toNat = n219 at *
  generalize v233.toNat = n233 at *
  generalize v262.toNat = n262 at *
  generalize v279.toNat = n279 at *
  generalize v293.toNat = n293 at *
  generalize v332.toNat = n332 at *
  generalize v352.toNat = n352 at *
  generalize v354.toNat = n354 at *
  generalize v356.toNat = n356 at *
  generalize v366.toNat = n366 at *
  generalize v367.toNat = n367 at *
  generalize v375.toNat = n375 at *
  generalize v376.toNat = n376 at *
  generalize v379.toNat = n379 at *
  generalize v381.toNat = n381 at *
  generalize v382.toNat = n382 at *
  generalize v384.toNat = n384 at *
  generalize v386.toNat = n386 at *
  generalize v389.toNat = n389 at *
  generalize v395.toNat = n395 at *
  generalize v401.toNat = n401 at *
  generalize v403.toNat = n403 at *
  generalize v405.toNat = n405 at *
  generalize v417.toNat = n417 at *
  generalize v419.toNat = n419 at *
  generalize v425.toNat = n425 at *
  generalize v1045.toNat = n1045 at *
  generalize v1047.toNat = n1047 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN8L4 {v819 v1039 v1040 : Word}
    (t1039 : v1039.toNat = v819.toNat * 333 % 2 ^ 32)
    (t1040 : v1040.toNat = v819.toNat * 333 / 2 ^ 32) :
    v1039.toNat + 2 ^ 32 * v1040.toNat = v819.toNat * 333 := by
  have := v819.isLt; have := v1039.isLt; have := v1040.isLt
  generalize v819.toNat = n819 at *
  generalize v1039.toNat = n1039 at *
  generalize v1040.toNat = n1040 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S12 {v823 v831 v1039 v1040 v1045 v1047 v1048 v1049 v1050 v1051 v1053 v1054 v1056 v1057 v1058 v1059 v1060 v1061 v1062 v1063 : Word}
    (t1049 : v1049.toNat = (v1047.toNat + v823.toNat) % 2 ^ 32)
    (t1050 : v1048.toNat + 2 ^ 32 * v1050.toNat = v1045.toNat + v831.toNat)
    (t1051 : v1051.toNat = (v1049.toNat + v1050.toNat) % 2 ^ 32)
    (t1053 : v1053.toNat = (v1040.toNat + v1051.toNat) % 2 ^ 32)
    (t1056 : v1054.toNat + 2 ^ 32 * v1056.toNat = v1039.toNat + v1048.toNat)
    (t1058 : v1058.toNat = (v1056.toNat + v1053.toNat) % 2 ^ 32)
    (t1061 : v1061.toNat = (v1058.toNat + v1059.toNat) % 2 ^ 32)
    (t1062 : v1060.toNat + 2 ^ 32 * v1062.toNat = v1054.toNat + v1057.toNat)
    (t1063 : v1063.toNat = (v1061.toNat + v1062.toNat) % 2 ^ 32) :
    v1060.toNat + 2 ^ 32 * v1063.toNat = ((v1057.toNat + 2 ^ 32 * v1059.toNat) + (v831.toNat + 2 ^ 32 * v823.toNat) + (v1045.toNat + 2 ^ 32 * v1047.toNat) + (v1039.toNat + 2 ^ 32 * v1040.toNat)) % 2 ^ 64 := by
  obtain ⟨q1049, eq1049⟩ := mod_q t1049; clear t1049
  obtain ⟨q1051, eq1051⟩ := mod_q t1051; clear t1051
  obtain ⟨q1053, eq1053⟩ := mod_q t1053; clear t1053
  obtain ⟨q1058, eq1058⟩ := mod_q t1058; clear t1058
  obtain ⟨q1061, eq1061⟩ := mod_q t1061; clear t1061
  obtain ⟨q1063, eq1063⟩ := mod_q t1063; clear t1063
  have key : v1060.toNat + 2 ^ 32 * v1063.toNat + 2 ^ 64 * (q1049 + q1051 + q1053 + q1058 + q1061 + q1063) = ((v1057.toNat + 2 ^ 32 * v1059.toNat) + (v831.toNat + 2 ^ 32 * v823.toNat) + (v1045.toNat + 2 ^ 32 * v1047.toNat) + (v1039.toNat + 2 ^ 32 * v1040.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v823.toNat = n823 at *
    generalize v831.toNat = n831 at *
    generalize v1039.toNat = n1039 at *
    generalize v1040.toNat = n1040 at *
    generalize v1045.toNat = n1045 at *
    generalize v1047.toNat = n1047 at *
    generalize v1048.toNat = n1048 at *
    generalize v1049.toNat = n1049 at *
    generalize v1050.toNat = n1050 at *
    generalize v1051.toNat = n1051 at *
    generalize v1053.toNat = n1053 at *
    generalize v1054.toNat = n1054 at *
    generalize v1056.toNat = n1056 at *
    generalize v1057.toNat = n1057 at *
    generalize v1058.toNat = n1058 at *
    generalize v1059.toNat = n1059 at *
    generalize v1060.toNat = n1060 at *
    generalize v1061.toNat = n1061 at *
    generalize v1062.toNat = n1062 at *
    generalize v1063.toNat = n1063 at *
    omega
  exact smm_key key (smm_lt v1060 v1063)

set_option maxHeartbeats 10000000 in
theorem evr_v_R3 {v1060 v1063 : Word}
     :
    v1060.toNat = (v1060.toNat + 2 ^ 32 * v1063.toNat) % 2 ^ 32 := by
  have := v1060.isLt; have := v1063.isLt
  generalize v1060.toNat = n1060 at *
  generalize v1063.toNat = n1063 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_C12 {v1060 v1063 v1064 v1071 v1073 v1075 : Word}
    (t1064 : v1064.toNat = v1063.toNat * 2 ^ 3 % 2 ^ 32)
    (t1071 : v1071.toNat = v1060.toNat / 2 ^ 29)
    (t1073 : v1073.toNat = v1071.toNat + v1064.toNat)
    (t1075 : v1075.toNat = v1063.toNat / 2 ^ 29) :
    v1073.toNat + 2 ^ 32 * v1075.toNat = (v1060.toNat + 2 ^ 32 * v1063.toNat) / 2 ^ 29 := by
  have := v1060.isLt; have := v1063.isLt; have := v1064.isLt; have := v1071.isLt; have := v1073.isLt; have := v1075.isLt
  generalize v1060.toNat = n1060 at *
  generalize v1063.toNat = n1063 at *
  generalize v1064.toNat = n1064 at *
  generalize v1071.toNat = n1071 at *
  generalize v1073.toNat = n1073 at *
  generalize v1075.toNat = n1075 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN5L8 {v8 v107 v108 v109 v110 v113 v118 v120 v138 v147 v171 v181 v194 v195 v203 v206 v219 v233 v262 v279 v293 v332 v352 v366 v388 v403 v412 v416 v419 v421 v423 v425 v429 v430 v431 v435 v437 v438 v440 v441 v445 v446 v451 v455 v458 v465 v467 v485 v489 v498 v1065 v1067 : Word}
    (t467 : v467.toNat = v465.toNat * 307527195 % 2 ^ 32)
    (t1065 : v1065.toNat = v485.toNat / 2 ^ 12)
    (t1067 : v1067.toNat = v467.toNat * 2 ^ 20 % 2 ^ 32)
    (wN5 : v485.toNat = ((v465.toNat + 2 ^ 32 * v498.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wS5 : v465.toNat + 2 ^ 32 * v498.toNat = ((v458.toNat + 2 ^ 32 * v489.toNat) + (v430.toNat + 2 ^ 32 * v435.toNat) + (v429.toNat + 2 ^ 32 * v431.toNat) + (v440.toNat + 2 ^ 32 * v438.toNat) + (v445.toNat + 2 ^ 32 * v446.toNat) + (v451.toNat + 2 ^ 32 * v455.toNat)) % 2 ^ 64)
    (wC4 : v458.toNat + 2 ^ 32 * v489.toNat = (v437.toNat + 2 ^ 32 * v441.toNat) / 2 ^ 29)
    (wZ5 : v430.toNat + 2 ^ 32 * v435.toNat = ((v416.toNat + 2 ^ 32 * v412.toNat) + (((v206.toNat + 2 ^ 32 * v203.toNat) + (2 ^ 64 - (v120.toNat + 2 ^ 32 * v147.toNat))) % 2 ^ 64)) % 2 ^ 64)
    (wPN1L4 : v429.toNat + 2 ^ 32 * v431.toNat = v219.toNat * 333)
    (wPN2L3 : v440.toNat + 2 ^ 32 * v438.toNat = v279.toNat * 502512965)
    (wPN3L2 : v445.toNat + 2 ^ 32 * v446.toNat = v352.toNat * 501691798)
    (wPN4L1 : v451.toNat + 2 ^ 32 * v455.toNat = v419.toNat * 9640146)
    (wT4 : v437.toNat + 2 ^ 32 * v441.toNat = ((v403.toNat + 2 ^ 32 * v425.toNat) + (v423.toNat + 2 ^ 32 * v421.toNat)) % 2 ^ 64)
    (wPAA0BB0 : v416.toNat + 2 ^ 32 * v412.toNat = v388.toNat * (((290322925) + (536870911)) % 2 ^ 32))
    (wZ10a : v206.toNat + 2 ^ 32 * v203.toNat = ((((v107.toNat + 2 ^ 32 * v108.toNat) + (v109.toNat + 2 ^ 32 * v110.toNat) + (v118.toNat + 2 ^ 32 * v113.toNat) + (v171.toNat + 2 ^ 32 * v138.toNat)) % 2 ^ 64) + (2 ^ 64 - (v194.toNat + 2 ^ 32 * v181.toNat))) % 2 ^ 64)
    (wPA0B0 : v120.toNat + 2 ^ 32 * v147.toNat = v8.toNat * (290322925))
    (wN1 : v219.toNat = ((v195.toNat + 2 ^ 32 * v233.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN2 : v279.toNat = ((v262.toNat + 2 ^ 32 * v293.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN3 : v352.toNat = ((v332.toNat + 2 ^ 32 * v366.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN4 : v419.toNat = ((v403.toNat + 2 ^ 32 * v425.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v1067.toNat + 2 ^ 32 * v1065.toNat = v485.toNat * 1048576 := by
  have := v8.isLt; have := v107.isLt; have := v108.isLt; have := v109.isLt; have := v110.isLt; have := v113.isLt; have := v118.isLt; have := v120.isLt; have := v138.isLt; have := v147.isLt; have := v171.isLt; have := v181.isLt; have := v194.isLt; have := v195.isLt; have := v203.isLt; have := v206.isLt; have := v219.isLt; have := v233.isLt; have := v262.isLt; have := v279.isLt; have := v293.isLt; have := v332.isLt; have := v352.isLt; have := v366.isLt; have := v388.isLt; have := v403.isLt; have := v412.isLt; have := v416.isLt; have := v419.isLt; have := v421.isLt; have := v423.isLt; have := v425.isLt; have := v429.isLt; have := v430.isLt; have := v431.isLt; have := v435.isLt; have := v437.isLt; have := v438.isLt; have := v440.isLt; have := v441.isLt; have := v445.isLt; have := v446.isLt; have := v451.isLt; have := v455.isLt; have := v458.isLt; have := v465.isLt; have := v467.isLt; have := v485.isLt; have := v489.isLt; have := v498.isLt; have := v1065.isLt; have := v1067.isLt
  generalize v8.toNat = n8 at *
  generalize v107.toNat = n107 at *
  generalize v108.toNat = n108 at *
  generalize v109.toNat = n109 at *
  generalize v110.toNat = n110 at *
  generalize v113.toNat = n113 at *
  generalize v118.toNat = n118 at *
  generalize v120.toNat = n120 at *
  generalize v138.toNat = n138 at *
  generalize v147.toNat = n147 at *
  generalize v171.toNat = n171 at *
  generalize v181.toNat = n181 at *
  generalize v194.toNat = n194 at *
  generalize v195.toNat = n195 at *
  generalize v203.toNat = n203 at *
  generalize v206.toNat = n206 at *
  generalize v219.toNat = n219 at *
  generalize v233.toNat = n233 at *
  generalize v262.toNat = n262 at *
  generalize v279.toNat = n279 at *
  generalize v293.toNat = n293 at *
  generalize v332.toNat = n332 at *
  generalize v352.toNat = n352 at *
  generalize v366.toNat = n366 at *
  generalize v388.toNat = n388 at *
  generalize v403.toNat = n403 at *
  generalize v412.toNat = n412 at *
  generalize v416.toNat = n416 at *
  generalize v419.toNat = n419 at *
  generalize v421.toNat = n421 at *
  generalize v423.toNat = n423 at *
  generalize v425.toNat = n425 at *
  generalize v429.toNat = n429 at *
  generalize v430.toNat = n430 at *
  generalize v431.toNat = n431 at *
  generalize v435.toNat = n435 at *
  generalize v437.toNat = n437 at *
  generalize v438.toNat = n438 at *
  generalize v440.toNat = n440 at *
  generalize v441.toNat = n441 at *
  generalize v445.toNat = n445 at *
  generalize v446.toNat = n446 at *
  generalize v451.toNat = n451 at *
  generalize v455.toNat = n455 at *
  generalize v458.toNat = n458 at *
  generalize v465.toNat = n465 at *
  generalize v467.toNat = n467 at *
  generalize v485.toNat = n485 at *
  generalize v489.toNat = n489 at *
  generalize v498.toNat = n498 at *
  generalize v1065.toNat = n1065 at *
  generalize v1067.toNat = n1067 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S13 {v341 v357 v1065 v1067 v1069 v1070 v1072 v1073 v1074 v1075 v1076 v1077 v1078 v1079 : Word}
    (t1070 : v1070.toNat = (v1065.toNat + v357.toNat) % 2 ^ 32)
    (t1072 : v1069.toNat + 2 ^ 32 * v1072.toNat = v341.toNat + v1067.toNat)
    (t1074 : v1074.toNat = (v1070.toNat + v1072.toNat) % 2 ^ 32)
    (t1077 : v1077.toNat = (v1075.toNat + v1074.toNat) % 2 ^ 32)
    (t1078 : v1076.toNat + 2 ^ 32 * v1078.toNat = v1069.toNat + v1073.toNat)
    (t1079 : v1079.toNat = (v1078.toNat + v1077.toNat) % 2 ^ 32) :
    v1076.toNat + 2 ^ 32 * v1079.toNat = ((v1073.toNat + 2 ^ 32 * v1075.toNat) + (v341.toNat + 2 ^ 32 * v357.toNat) + (v1067.toNat + 2 ^ 32 * v1065.toNat)) % 2 ^ 64 := by
  obtain ⟨q1070, eq1070⟩ := mod_q t1070; clear t1070
  obtain ⟨q1074, eq1074⟩ := mod_q t1074; clear t1074
  obtain ⟨q1077, eq1077⟩ := mod_q t1077; clear t1077
  obtain ⟨q1079, eq1079⟩ := mod_q t1079; clear t1079
  have key : v1076.toNat + 2 ^ 32 * v1079.toNat + 2 ^ 64 * (q1070 + q1074 + q1077 + q1079) = ((v1073.toNat + 2 ^ 32 * v1075.toNat) + (v341.toNat + 2 ^ 32 * v357.toNat) + (v1067.toNat + 2 ^ 32 * v1065.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v341.toNat = n341 at *
    generalize v357.toNat = n357 at *
    generalize v1065.toNat = n1065 at *
    generalize v1067.toNat = n1067 at *
    generalize v1069.toNat = n1069 at *
    generalize v1070.toNat = n1070 at *
    generalize v1072.toNat = n1072 at *
    generalize v1073.toNat = n1073 at *
    generalize v1074.toNat = n1074 at *
    generalize v1075.toNat = n1075 at *
    generalize v1076.toNat = n1076 at *
    generalize v1077.toNat = n1077 at *
    generalize v1078.toNat = n1078 at *
    generalize v1079.toNat = n1079 at *
    omega
  exact smm_key key (smm_lt v1076 v1079)

set_option maxHeartbeats 10000000 in
theorem evr_v_R4 {v1076 v1079 : Word}
     :
    v1076.toNat = (v1076.toNat + 2 ^ 32 * v1079.toNat) % 2 ^ 32 := by
  have := v1076.isLt; have := v1079.isLt
  generalize v1076.toNat = n1076 at *
  generalize v1079.toNat = n1079 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_C13 {v1076 v1079 v1080 v1087 v1089 v1091 : Word}
    (t1080 : v1080.toNat = v1079.toNat * 2 ^ 3 % 2 ^ 32)
    (t1087 : v1087.toNat = v1076.toNat / 2 ^ 29)
    (t1089 : v1089.toNat = v1087.toNat + v1080.toNat)
    (t1091 : v1091.toNat = v1079.toNat / 2 ^ 29) :
    v1089.toNat + 2 ^ 32 * v1091.toNat = (v1076.toNat + 2 ^ 32 * v1079.toNat) / 2 ^ 29 := by
  have := v1076.isLt; have := v1079.isLt; have := v1080.isLt; have := v1087.isLt; have := v1089.isLt; have := v1091.isLt
  generalize v1076.toNat = n1076 at *
  generalize v1079.toNat = n1079 at *
  generalize v1080.toNat = n1080 at *
  generalize v1087.toNat = n1087 at *
  generalize v1089.toNat = n1089 at *
  generalize v1091.toNat = n1091 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN6L8 {v24 v25 v26 v27 v40 v51 v159 v162 v211 v222 v231 v262 v274 v279 v293 v332 v352 v366 v388 v403 v419 v425 v465 v476 v483 v484 v485 v488 v490 v491 v492 v498 v505 v509 v514 v515 v516 v518 v520 v523 v527 v528 v530 v534 v537 v538 v540 v557 v568 v574 v1081 v1084 : Word}
    (t540 : v540.toNat = v537.toNat * 307527195 % 2 ^ 32)
    (t1081 : v1081.toNat = v557.toNat / 2 ^ 12)
    (t1084 : v1084.toNat = v540.toNat * 2 ^ 20 % 2 ^ 32)
    (wN6 : v557.toNat = ((v537.toNat + 2 ^ 32 * v574.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wS6 : v537.toNat + 2 ^ 32 * v574.toNat = ((v527.toNat + 2 ^ 32 * v568.toNat) + (v520.toNat + 2 ^ 32 * v528.toNat) + (v514.toNat + 2 ^ 32 * v515.toNat) + (v516.toNat + 2 ^ 32 * v530.toNat) + (v518.toNat + 2 ^ 32 * v534.toNat) + (v523.toNat + 2 ^ 32 * v538.toNat)) % 2 ^ 64)
    (wC5 : v527.toNat + 2 ^ 32 * v568.toNat = (v505.toNat + 2 ^ 32 * v509.toNat) / 2 ^ 29)
    (wZ6 : v520.toNat + 2 ^ 32 * v528.toNat = ((((v483.toNat + 2 ^ 32 * v484.toNat) + (v491.toNat + 2 ^ 32 * v490.toNat)) % 2 ^ 64) + (((v274.toNat + 2 ^ 32 * v231.toNat) + (2 ^ 64 - (v40.toNat + 2 ^ 32 * v51.toNat))) % 2 ^ 64)) % 2 ^ 64)
    (wPN2L4 : v514.toNat + 2 ^ 32 * v515.toNat = v279.toNat * 333)
    (wPN3L3 : v516.toNat + 2 ^ 32 * v530.toNat = v352.toNat * 502512965)
    (wPN4L2 : v518.toNat + 2 ^ 32 * v534.toNat = v419.toNat * 501691798)
    (wPN5L1 : v523.toNat + 2 ^ 32 * v538.toNat = v485.toNat * 9640146)
    (wT5 : v505.toNat + 2 ^ 32 * v509.toNat = ((v465.toNat + 2 ^ 32 * v498.toNat) + (v492.toNat + 2 ^ 32 * v488.toNat)) % 2 ^ 64)
    (wPAA0BB1 : v483.toNat + 2 ^ 32 * v484.toNat = v388.toNat * (((442594051) + (536870911)) % 2 ^ 32))
    (wPAA1BB0 : v491.toNat + 2 ^ 32 * v490.toNat = v476.toNat * (((290322925) + (536870911)) % 2 ^ 32))
    (wZ11a : v274.toNat + 2 ^ 32 * v231.toNat = ((v159.toNat + 2 ^ 32 * v162.toNat) + (2 ^ 64 - (v211.toNat + 2 ^ 32 * v222.toNat))) % 2 ^ 64)
    (wZ1 : v40.toNat + 2 ^ 32 * v51.toNat = ((v26.toNat + 2 ^ 32 * v24.toNat) + (v27.toNat + 2 ^ 32 * v25.toNat)) % 2 ^ 64)
    (wN2 : v279.toNat = ((v262.toNat + 2 ^ 32 * v293.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN3 : v352.toNat = ((v332.toNat + 2 ^ 32 * v366.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN4 : v419.toNat = ((v403.toNat + 2 ^ 32 * v425.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN5 : v485.toNat = ((v465.toNat + 2 ^ 32 * v498.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v1084.toNat + 2 ^ 32 * v1081.toNat = v557.toNat * 1048576 := by
  have := v24.isLt; have := v25.isLt; have := v26.isLt; have := v27.isLt; have := v40.isLt; have := v51.isLt; have := v159.isLt; have := v162.isLt; have := v211.isLt; have := v222.isLt; have := v231.isLt; have := v262.isLt; have := v274.isLt; have := v279.isLt; have := v293.isLt; have := v332.isLt; have := v352.isLt; have := v366.isLt; have := v388.isLt; have := v403.isLt; have := v419.isLt; have := v425.isLt; have := v465.isLt; have := v476.isLt; have := v483.isLt; have := v484.isLt; have := v485.isLt; have := v488.isLt; have := v490.isLt; have := v491.isLt; have := v492.isLt; have := v498.isLt; have := v505.isLt; have := v509.isLt; have := v514.isLt; have := v515.isLt; have := v516.isLt; have := v518.isLt; have := v520.isLt; have := v523.isLt; have := v527.isLt; have := v528.isLt; have := v530.isLt; have := v534.isLt; have := v537.isLt; have := v538.isLt; have := v540.isLt; have := v557.isLt; have := v568.isLt; have := v574.isLt; have := v1081.isLt; have := v1084.isLt
  generalize v24.toNat = n24 at *
  generalize v25.toNat = n25 at *
  generalize v26.toNat = n26 at *
  generalize v27.toNat = n27 at *
  generalize v40.toNat = n40 at *
  generalize v51.toNat = n51 at *
  generalize v159.toNat = n159 at *
  generalize v162.toNat = n162 at *
  generalize v211.toNat = n211 at *
  generalize v222.toNat = n222 at *
  generalize v231.toNat = n231 at *
  generalize v262.toNat = n262 at *
  generalize v274.toNat = n274 at *
  generalize v279.toNat = n279 at *
  generalize v293.toNat = n293 at *
  generalize v332.toNat = n332 at *
  generalize v352.toNat = n352 at *
  generalize v366.toNat = n366 at *
  generalize v388.toNat = n388 at *
  generalize v403.toNat = n403 at *
  generalize v419.toNat = n419 at *
  generalize v425.toNat = n425 at *
  generalize v465.toNat = n465 at *
  generalize v476.toNat = n476 at *
  generalize v483.toNat = n483 at *
  generalize v484.toNat = n484 at *
  generalize v485.toNat = n485 at *
  generalize v488.toNat = n488 at *
  generalize v490.toNat = n490 at *
  generalize v491.toNat = n491 at *
  generalize v492.toNat = n492 at *
  generalize v498.toNat = n498 at *
  generalize v505.toNat = n505 at *
  generalize v509.toNat = n509 at *
  generalize v514.toNat = n514 at *
  generalize v515.toNat = n515 at *
  generalize v516.toNat = n516 at *
  generalize v518.toNat = n518 at *
  generalize v520.toNat = n520 at *
  generalize v523.toNat = n523 at *
  generalize v527.toNat = n527 at *
  generalize v528.toNat = n528 at *
  generalize v530.toNat = n530 at *
  generalize v534.toNat = n534 at *
  generalize v537.toNat = n537 at *
  generalize v538.toNat = n538 at *
  generalize v540.toNat = n540 at *
  generalize v557.toNat = n557 at *
  generalize v568.toNat = n568 at *
  generalize v574.toNat = n574 at *
  generalize v1081.toNat = n1081 at *
  generalize v1084.toNat = n1084 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S14 {v481 v545 v1081 v1084 v1085 v1086 v1088 v1089 v1090 v1091 v1092 v1093 v1094 v1095 : Word}
    (t1086 : v1086.toNat = (v1081.toNat + v545.toNat) % 2 ^ 32)
    (t1088 : v1085.toNat + 2 ^ 32 * v1088.toNat = v1084.toNat + v481.toNat)
    (t1090 : v1090.toNat = (v1086.toNat + v1088.toNat) % 2 ^ 32)
    (t1093 : v1093.toNat = (v1091.toNat + v1090.toNat) % 2 ^ 32)
    (t1094 : v1092.toNat + 2 ^ 32 * v1094.toNat = v1085.toNat + v1089.toNat)
    (t1095 : v1095.toNat = (v1093.toNat + v1094.toNat) % 2 ^ 32) :
    v1092.toNat + 2 ^ 32 * v1095.toNat = ((v1089.toNat + 2 ^ 32 * v1091.toNat) + (v481.toNat + 2 ^ 32 * v545.toNat) + (v1084.toNat + 2 ^ 32 * v1081.toNat)) % 2 ^ 64 := by
  obtain ⟨q1086, eq1086⟩ := mod_q t1086; clear t1086
  obtain ⟨q1090, eq1090⟩ := mod_q t1090; clear t1090
  obtain ⟨q1093, eq1093⟩ := mod_q t1093; clear t1093
  obtain ⟨q1095, eq1095⟩ := mod_q t1095; clear t1095
  have key : v1092.toNat + 2 ^ 32 * v1095.toNat + 2 ^ 64 * (q1086 + q1090 + q1093 + q1095) = ((v1089.toNat + 2 ^ 32 * v1091.toNat) + (v481.toNat + 2 ^ 32 * v545.toNat) + (v1084.toNat + 2 ^ 32 * v1081.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v481.toNat = n481 at *
    generalize v545.toNat = n545 at *
    generalize v1081.toNat = n1081 at *
    generalize v1084.toNat = n1084 at *
    generalize v1085.toNat = n1085 at *
    generalize v1086.toNat = n1086 at *
    generalize v1088.toNat = n1088 at *
    generalize v1089.toNat = n1089 at *
    generalize v1090.toNat = n1090 at *
    generalize v1091.toNat = n1091 at *
    generalize v1092.toNat = n1092 at *
    generalize v1093.toNat = n1093 at *
    generalize v1094.toNat = n1094 at *
    generalize v1095.toNat = n1095 at *
    omega
  exact smm_key key (smm_lt v1092 v1095)

set_option maxHeartbeats 10000000 in
theorem evr_v_R5 {v1092 v1095 : Word}
     :
    v1092.toNat = (v1092.toNat + 2 ^ 32 * v1095.toNat) % 2 ^ 32 := by
  have := v1092.isLt; have := v1095.isLt
  generalize v1092.toNat = n1092 at *
  generalize v1095.toNat = n1095 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_C14 {v1092 v1095 v1096 v1104 v1106 v1108 : Word}
    (t1096 : v1096.toNat = v1095.toNat * 2 ^ 3 % 2 ^ 32)
    (t1104 : v1104.toNat = v1092.toNat / 2 ^ 29)
    (t1106 : v1106.toNat = v1104.toNat + v1096.toNat)
    (t1108 : v1108.toNat = v1095.toNat / 2 ^ 29) :
    v1106.toNat + 2 ^ 32 * v1108.toNat = (v1092.toNat + 2 ^ 32 * v1095.toNat) / 2 ^ 29 := by
  have := v1092.isLt; have := v1095.isLt; have := v1096.isLt; have := v1104.isLt; have := v1106.isLt; have := v1108.isLt
  generalize v1092.toNat = n1092 at *
  generalize v1095.toNat = n1095 at *
  generalize v1096.toNat = n1096 at *
  generalize v1104.toNat = n1104 at *
  generalize v1106.toNat = n1106 at *
  generalize v1108.toNat = n1108 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN7L8 {v44 v45 v46 v47 v48 v49 v62 v67 v266 v267 v270 v272 v284 v297 v332 v352 v366 v388 v403 v419 v425 v465 v476 v485 v498 v537 v557 v562 v569 v574 v576 v586 v588 v589 v590 v593 v594 v595 v598 v599 v613 v615 v618 v621 v624 v627 v628 v664 v675 v698 v702 v712 v722 v731 v735 v1097 v1099 : Word}
    (t702 : v702.toNat = v698.toNat * 307527195 % 2 ^ 32)
    (t1097 : v1097.toNat = v722.toNat / 2 ^ 12)
    (t1099 : v1099.toNat = v702.toNat * 2 ^ 20 % 2 ^ 32)
    (wN7 : v722.toNat = ((v698.toNat + 2 ^ 32 * v735.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wS7 : v698.toNat + 2 ^ 32 * v735.toNat = ((v598.toNat + 2 ^ 32 * v731.toNat) + (v624.toNat + 2 ^ 32 * v628.toNat) + (v613.toNat + 2 ^ 32 * v615.toNat) + (v618.toNat + 2 ^ 32 * v621.toNat) + (v664.toNat + 2 ^ 32 * v627.toNat) + (v675.toNat + 2 ^ 32 * v712.toNat)) % 2 ^ 64)
    (wC6 : v598.toNat + 2 ^ 32 * v731.toNat = (v586.toNat + 2 ^ 32 * v593.toNat) / 2 ^ 29)
    (wZ7 : v624.toNat + 2 ^ 32 * v628.toNat = ((((v588.toNat + 2 ^ 32 * v589.toNat) + (v590.toNat + 2 ^ 32 * v594.toNat) + (v599.toNat + 2 ^ 32 * v595.toNat)) % 2 ^ 64) + (((v297.toNat + 2 ^ 32 * v284.toNat) + (2 ^ 64 - (v62.toNat + 2 ^ 32 * v67.toNat))) % 2 ^ 64)) % 2 ^ 64)
    (wPN3L4 : v613.toNat + 2 ^ 32 * v615.toNat = v352.toNat * 333)
    (wPN4L3 : v618.toNat + 2 ^ 32 * v621.toNat = v419.toNat * 502512965)
    (wPN5L2 : v664.toNat + 2 ^ 32 * v627.toNat = v485.toNat * 501691798)
    (wPN6L1 : v675.toNat + 2 ^ 32 * v712.toNat = v557.toNat * 9640146)
    (wT6 : v586.toNat + 2 ^ 32 * v593.toNat = ((v537.toNat + 2 ^ 32 * v574.toNat) + (v569.toNat + 2 ^ 32 * v562.toNat)) % 2 ^ 64)
    (wPAA0BB2 : v588.toNat + 2 ^ 32 * v589.toNat = v388.toNat * (((259787148) + (536870911)) % 2 ^ 32))
    (wPAA1BB1 : v590.toNat + 2 ^ 32 * v594.toNat = v476.toNat * (((442594051) + (536870911)) % 2 ^ 32))
    (wPAA2BB0 : v599.toNat + 2 ^ 32 * v595.toNat = v576.toNat * (((290322925) + (536870911)) % 2 ^ 32))
    (wZ12a : v297.toNat + 2 ^ 32 * v284.toNat = ((v266.toNat + 2 ^ 32 * v270.toNat) + (2 ^ 64 - (v267.toNat + 2 ^ 32 * v272.toNat))) % 2 ^ 64)
    (wZ2 : v62.toNat + 2 ^ 32 * v67.toNat = ((v44.toNat + 2 ^ 32 * v45.toNat) + (v46.toNat + 2 ^ 32 * v47.toNat) + (v49.toNat + 2 ^ 32 * v48.toNat)) % 2 ^ 64)
    (wN3 : v352.toNat = ((v332.toNat + 2 ^ 32 * v366.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN4 : v419.toNat = ((v403.toNat + 2 ^ 32 * v425.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN5 : v485.toNat = ((v465.toNat + 2 ^ 32 * v498.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN6 : v557.toNat = ((v537.toNat + 2 ^ 32 * v574.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v1099.toNat + 2 ^ 32 * v1097.toNat = v722.toNat * 1048576 := by
  have := v44.isLt; have := v45.isLt; have := v46.isLt; have := v47.isLt; have := v48.isLt; have := v49.isLt; have := v62.isLt; have := v67.isLt; have := v266.isLt; have := v267.isLt; have := v270.isLt; have := v272.isLt; have := v284.isLt; have := v297.isLt; have := v332.isLt; have := v352.isLt; have := v366.isLt; have := v388.isLt; have := v403.isLt; have := v419.isLt; have := v425.isLt; have := v465.isLt; have := v476.isLt; have := v485.isLt; have := v498.isLt; have := v537.isLt; have := v557.isLt; have := v562.isLt; have := v569.isLt; have := v574.isLt; have := v576.isLt; have := v586.isLt; have := v588.isLt; have := v589.isLt; have := v590.isLt; have := v593.isLt; have := v594.isLt; have := v595.isLt; have := v598.isLt; have := v599.isLt; have := v613.isLt; have := v615.isLt; have := v618.isLt; have := v621.isLt; have := v624.isLt; have := v627.isLt; have := v628.isLt; have := v664.isLt; have := v675.isLt; have := v698.isLt; have := v702.isLt; have := v712.isLt; have := v722.isLt; have := v731.isLt; have := v735.isLt; have := v1097.isLt; have := v1099.isLt
  generalize v44.toNat = n44 at *
  generalize v45.toNat = n45 at *
  generalize v46.toNat = n46 at *
  generalize v47.toNat = n47 at *
  generalize v48.toNat = n48 at *
  generalize v49.toNat = n49 at *
  generalize v62.toNat = n62 at *
  generalize v67.toNat = n67 at *
  generalize v266.toNat = n266 at *
  generalize v267.toNat = n267 at *
  generalize v270.toNat = n270 at *
  generalize v272.toNat = n272 at *
  generalize v284.toNat = n284 at *
  generalize v297.toNat = n297 at *
  generalize v332.toNat = n332 at *
  generalize v352.toNat = n352 at *
  generalize v366.toNat = n366 at *
  generalize v388.toNat = n388 at *
  generalize v403.toNat = n403 at *
  generalize v419.toNat = n419 at *
  generalize v425.toNat = n425 at *
  generalize v465.toNat = n465 at *
  generalize v476.toNat = n476 at *
  generalize v485.toNat = n485 at *
  generalize v498.toNat = n498 at *
  generalize v537.toNat = n537 at *
  generalize v557.toNat = n557 at *
  generalize v562.toNat = n562 at *
  generalize v569.toNat = n569 at *
  generalize v574.toNat = n574 at *
  generalize v576.toNat = n576 at *
  generalize v586.toNat = n586 at *
  generalize v588.toNat = n588 at *
  generalize v589.toNat = n589 at *
  generalize v590.toNat = n590 at *
  generalize v593.toNat = n593 at *
  generalize v594.toNat = n594 at *
  generalize v595.toNat = n595 at *
  generalize v598.toNat = n598 at *
  generalize v599.toNat = n599 at *
  generalize v613.toNat = n613 at *
  generalize v615.toNat = n615 at *
  generalize v618.toNat = n618 at *
  generalize v621.toNat = n621 at *
  generalize v624.toNat = n624 at *
  generalize v627.toNat = n627 at *
  generalize v628.toNat = n628 at *
  generalize v664.toNat = n664 at *
  generalize v675.toNat = n675 at *
  generalize v698.toNat = n698 at *
  generalize v702.toNat = n702 at *
  generalize v712.toNat = n712 at *
  generalize v722.toNat = n722 at *
  generalize v731.toNat = n731 at *
  generalize v735.toNat = n735 at *
  generalize v1097.toNat = n1097 at *
  generalize v1099.toNat = n1099 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S15 {v559 v572 v1097 v1099 v1100 v1101 v1105 v1106 v1107 v1108 v1109 v1110 v1111 v1112 : Word}
    (t1101 : v1101.toNat = (v1097.toNat + v572.toNat) % 2 ^ 32)
    (t1105 : v1100.toNat + 2 ^ 32 * v1105.toNat = v1099.toNat + v559.toNat)
    (t1107 : v1107.toNat = (v1101.toNat + v1105.toNat) % 2 ^ 32)
    (t1110 : v1110.toNat = (v1108.toNat + v1107.toNat) % 2 ^ 32)
    (t1111 : v1109.toNat + 2 ^ 32 * v1111.toNat = v1100.toNat + v1106.toNat)
    (t1112 : v1112.toNat = (v1110.toNat + v1111.toNat) % 2 ^ 32) :
    v1109.toNat + 2 ^ 32 * v1112.toNat = ((v1106.toNat + 2 ^ 32 * v1108.toNat) + (v559.toNat + 2 ^ 32 * v572.toNat) + (v1099.toNat + 2 ^ 32 * v1097.toNat)) % 2 ^ 64 := by
  obtain ⟨q1101, eq1101⟩ := mod_q t1101; clear t1101
  obtain ⟨q1107, eq1107⟩ := mod_q t1107; clear t1107
  obtain ⟨q1110, eq1110⟩ := mod_q t1110; clear t1110
  obtain ⟨q1112, eq1112⟩ := mod_q t1112; clear t1112
  have key : v1109.toNat + 2 ^ 32 * v1112.toNat + 2 ^ 64 * (q1101 + q1107 + q1110 + q1112) = ((v1106.toNat + 2 ^ 32 * v1108.toNat) + (v559.toNat + 2 ^ 32 * v572.toNat) + (v1099.toNat + 2 ^ 32 * v1097.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v559.toNat = n559 at *
    generalize v572.toNat = n572 at *
    generalize v1097.toNat = n1097 at *
    generalize v1099.toNat = n1099 at *
    generalize v1100.toNat = n1100 at *
    generalize v1101.toNat = n1101 at *
    generalize v1105.toNat = n1105 at *
    generalize v1106.toNat = n1106 at *
    generalize v1107.toNat = n1107 at *
    generalize v1108.toNat = n1108 at *
    generalize v1109.toNat = n1109 at *
    generalize v1110.toNat = n1110 at *
    generalize v1111.toNat = n1111 at *
    generalize v1112.toNat = n1112 at *
    omega
  exact smm_key key (smm_lt v1109 v1112)

set_option maxHeartbeats 10000000 in
theorem evr_v_R6 {v1109 v1112 : Word}
     :
    v1109.toNat = (v1109.toNat + 2 ^ 32 * v1112.toNat) % 2 ^ 32 := by
  have := v1109.isLt; have := v1112.isLt
  generalize v1109.toNat = n1109 at *
  generalize v1112.toNat = n1112 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_C15 {v1109 v1112 v1113 v1119 v1121 v1123 : Word}
    (t1113 : v1113.toNat = v1112.toNat * 2 ^ 3 % 2 ^ 32)
    (t1119 : v1119.toNat = v1109.toNat / 2 ^ 29)
    (t1121 : v1121.toNat = v1119.toNat + v1113.toNat)
    (t1123 : v1123.toNat = v1112.toNat / 2 ^ 29) :
    v1121.toNat + 2 ^ 32 * v1123.toNat = (v1109.toNat + 2 ^ 32 * v1112.toNat) / 2 ^ 29 := by
  have := v1109.isLt; have := v1112.isLt; have := v1113.isLt; have := v1119.isLt; have := v1121.isLt; have := v1123.isLt
  generalize v1109.toNat = n1109 at *
  generalize v1112.toNat = n1112 at *
  generalize v1113.toNat = n1113 at *
  generalize v1119.toNat = n1119 at *
  generalize v1121.toNat = n1121 at *
  generalize v1123.toNat = n1123 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN8L8 {v8 v15 v16 v36 v54 v55 v56 v57 v59 v69 v74 v87 v98 v111 v120 v122 v147 v151 v173 v185 v189 v209 v254 v255 v261 v308 v312 v319 v320 v326 v341 v357 v388 v403 v419 v425 v465 v476 v485 v498 v537 v557 v574 v576 v592 v640 v642 v649 v651 v658 v660 v671 v673 v698 v699 v700 v722 v724 v725 v735 v737 v741 v745 v747 v748 v750 v752 v778 v781 v784 v785 v786 v798 v802 v803 v805 v812 v819 v828 v832 v1114 v1116 : Word}
    (t803 : v803.toNat = v802.toNat * 307527195 % 2 ^ 32)
    (t1114 : v1114.toNat = v819.toNat / 2 ^ 12)
    (t1116 : v1116.toNat = v803.toNat * 2 ^ 20 % 2 ^ 32)
    (wN8 : v819.toNat = ((v802.toNat + 2 ^ 32 * v832.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wS8 : v802.toNat + 2 ^ 32 * v832.toNat = ((v745.toNat + 2 ^ 32 * v828.toNat) + (((((v640.toNat + 2 ^ 32 * v642.toNat) + (v660.toNat + 2 ^ 32 * v658.toNat) + (v671.toNat + 2 ^ 32 * v673.toNat) + (v649.toNat + 2 ^ 32 * v651.toNat)) % 2 ^ 64) + (((v748.toNat + 2 ^ 32 * v747.toNat) + (2 ^ 64 - (v341.toNat + 2 ^ 32 * v357.toNat))) % 2 ^ 64)) % 2 ^ 64) + (v750.toNat + 2 ^ 32 * v752.toNat) + (v778.toNat + 2 ^ 32 * v785.toNat) + (v781.toNat + 2 ^ 32 * v798.toNat) + (v784.toNat + 2 ^ 32 * v805.toNat) + (v786.toNat + 2 ^ 32 * v812.toNat)) % 2 ^ 64)
    (wC7 : v745.toNat + 2 ^ 32 * v828.toNat = (v737.toNat + 2 ^ 32 * v741.toNat) / 2 ^ 29)
    (wPAA0BB3 : v640.toNat + 2 ^ 32 * v642.toNat = v388.toNat * (((377041255) + (1048575)) % 2 ^ 32))
    (wPAA1BB2 : v660.toNat + 2 ^ 32 * v658.toNat = v476.toNat * (((259787148) + (536870911)) % 2 ^ 32))
    (wPAA2BB1 : v671.toNat + 2 ^ 32 * v673.toNat = v576.toNat * (((442594051) + (536870911)) % 2 ^ 32))
    (wPAA3BB0 : v649.toNat + 2 ^ 32 * v651.toNat = v592.toNat * (((290322925) + (536870911)) % 2 ^ 32))
    (wZ8a : v748.toNat + 2 ^ 32 * v747.toNat = ((v699.toNat + 2 ^ 32 * v700.toNat) + (2 ^ 64 - (v111.toNat + 2 ^ 32 * v122.toNat))) % 2 ^ 64)
    (wZ13 : v341.toNat + 2 ^ 32 * v357.toNat = ((v319.toNat + 2 ^ 32 * v326.toNat) + (v209.toNat + 2 ^ 32 * v189.toNat) + (v261.toNat + 2 ^ 32 * v255.toNat) + (v320.toNat + 2 ^ 32 * v312.toNat)) % 2 ^ 64)
    (wPN0L8 : v750.toNat + 2 ^ 32 * v752.toNat = v151.toNat * 1048576)
    (wPN4L4 : v778.toNat + 2 ^ 32 * v785.toNat = v419.toNat * 333)
    (wPN5L3 : v781.toNat + 2 ^ 32 * v798.toNat = v485.toNat * 502512965)
    (wPN6L2 : v784.toNat + 2 ^ 32 * v805.toNat = v557.toNat * 501691798)
    (wPN7L1 : v786.toNat + 2 ^ 32 * v812.toNat = v722.toNat * 9640146)
    (wT7 : v737.toNat + 2 ^ 32 * v741.toNat = ((v698.toNat + 2 ^ 32 * v735.toNat) + (v724.toNat + 2 ^ 32 * v725.toNat)) % 2 ^ 64)
    (wAA0 : v388.toNat = (v8.toNat + v173.toNat) % 2 ^ 32)
    (wAA1 : v476.toNat = (v15.toNat + v185.toNat) % 2 ^ 32)
    (wAA2 : v576.toNat = (v16.toNat + v254.toNat) % 2 ^ 32)
    (wAA3 : v592.toNat = (v36.toNat + v308.toNat) % 2 ^ 32)
    (wPA4B4 : v699.toNat + 2 ^ 32 * v700.toNat = v87.toNat * (536700270))
    (wZ3 : v111.toNat + 2 ^ 32 * v122.toNat = ((v54.toNat + 2 ^ 32 * v55.toNat) + (v56.toNat + 2 ^ 32 * v57.toNat) + (v69.toNat + 2 ^ 32 * v59.toNat) + (v98.toNat + 2 ^ 32 * v74.toNat)) % 2 ^ 64)
    (wPA5B8 : v319.toNat + 2 ^ 32 * v326.toNat = v173.toNat * (1048575))
    (wPA6B5 : v209.toNat + 2 ^ 32 * v189.toNat = v185.toNat * (536870911))
    (wPA7B5 : v261.toNat + 2 ^ 32 * v255.toNat = v254.toNat * (536870911))
    (wPA8B5 : v320.toNat + 2 ^ 32 * v312.toNat = v308.toNat * (536870911))
    (wN0 : v151.toNat = ((v120.toNat + 2 ^ 32 * v147.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN4 : v419.toNat = ((v403.toNat + 2 ^ 32 * v425.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN5 : v485.toNat = ((v465.toNat + 2 ^ 32 * v498.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN6 : v557.toNat = ((v537.toNat + 2 ^ 32 * v574.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN7 : v722.toNat = ((v698.toNat + 2 ^ 32 * v735.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v1116.toNat + 2 ^ 32 * v1114.toNat = v819.toNat * 1048576 := by
  have := v8.isLt; have := v15.isLt; have := v16.isLt; have := v36.isLt; have := v54.isLt; have := v55.isLt; have := v56.isLt; have := v57.isLt; have := v59.isLt; have := v69.isLt; have := v74.isLt; have := v87.isLt; have := v98.isLt; have := v111.isLt; have := v120.isLt; have := v122.isLt; have := v147.isLt; have := v151.isLt; have := v173.isLt; have := v185.isLt; have := v189.isLt; have := v209.isLt; have := v254.isLt; have := v255.isLt; have := v261.isLt; have := v308.isLt; have := v312.isLt; have := v319.isLt; have := v320.isLt; have := v326.isLt; have := v341.isLt; have := v357.isLt; have := v388.isLt; have := v403.isLt; have := v419.isLt; have := v425.isLt; have := v465.isLt; have := v476.isLt; have := v485.isLt; have := v498.isLt; have := v537.isLt; have := v557.isLt; have := v574.isLt; have := v576.isLt; have := v592.isLt; have := v640.isLt; have := v642.isLt; have := v649.isLt; have := v651.isLt; have := v658.isLt; have := v660.isLt; have := v671.isLt; have := v673.isLt; have := v698.isLt; have := v699.isLt; have := v700.isLt; have := v722.isLt; have := v724.isLt; have := v725.isLt; have := v735.isLt; have := v737.isLt; have := v741.isLt; have := v745.isLt; have := v747.isLt; have := v748.isLt; have := v750.isLt; have := v752.isLt; have := v778.isLt; have := v781.isLt; have := v784.isLt; have := v785.isLt; have := v786.isLt; have := v798.isLt; have := v802.isLt; have := v803.isLt; have := v805.isLt; have := v812.isLt; have := v819.isLt; have := v828.isLt; have := v832.isLt; have := v1114.isLt; have := v1116.isLt
  generalize v8.toNat = n8 at *
  generalize v15.toNat = n15 at *
  generalize v16.toNat = n16 at *
  generalize v36.toNat = n36 at *
  generalize v54.toNat = n54 at *
  generalize v55.toNat = n55 at *
  generalize v56.toNat = n56 at *
  generalize v57.toNat = n57 at *
  generalize v59.toNat = n59 at *
  generalize v69.toNat = n69 at *
  generalize v74.toNat = n74 at *
  generalize v87.toNat = n87 at *
  generalize v98.toNat = n98 at *
  generalize v111.toNat = n111 at *
  generalize v120.toNat = n120 at *
  generalize v122.toNat = n122 at *
  generalize v147.toNat = n147 at *
  generalize v151.toNat = n151 at *
  generalize v173.toNat = n173 at *
  generalize v185.toNat = n185 at *
  generalize v189.toNat = n189 at *
  generalize v209.toNat = n209 at *
  generalize v254.toNat = n254 at *
  generalize v255.toNat = n255 at *
  generalize v261.toNat = n261 at *
  generalize v308.toNat = n308 at *
  generalize v312.toNat = n312 at *
  generalize v319.toNat = n319 at *
  generalize v320.toNat = n320 at *
  generalize v326.toNat = n326 at *
  generalize v341.toNat = n341 at *
  generalize v357.toNat = n357 at *
  generalize v388.toNat = n388 at *
  generalize v403.toNat = n403 at *
  generalize v419.toNat = n419 at *
  generalize v425.toNat = n425 at *
  generalize v465.toNat = n465 at *
  generalize v476.toNat = n476 at *
  generalize v485.toNat = n485 at *
  generalize v498.toNat = n498 at *
  generalize v537.toNat = n537 at *
  generalize v557.toNat = n557 at *
  generalize v574.toNat = n574 at *
  generalize v576.toNat = n576 at *
  generalize v592.toNat = n592 at *
  generalize v640.toNat = n640 at *
  generalize v642.toNat = n642 at *
  generalize v649.toNat = n649 at *
  generalize v651.toNat = n651 at *
  generalize v658.toNat = n658 at *
  generalize v660.toNat = n660 at *
  generalize v671.toNat = n671 at *
  generalize v673.toNat = n673 at *
  generalize v698.toNat = n698 at *
  generalize v699.toNat = n699 at *
  generalize v700.toNat = n700 at *
  generalize v722.toNat = n722 at *
  generalize v724.toNat = n724 at *
  generalize v725.toNat = n725 at *
  generalize v735.toNat = n735 at *
  generalize v737.toNat = n737 at *
  generalize v741.toNat = n741 at *
  generalize v745.toNat = n745 at *
  generalize v747.toNat = n747 at *
  generalize v748.toNat = n748 at *
  generalize v750.toNat = n750 at *
  generalize v752.toNat = n752 at *
  generalize v778.toNat = n778 at *
  generalize v781.toNat = n781 at *
  generalize v784.toNat = n784 at *
  generalize v785.toNat = n785 at *
  generalize v786.toNat = n786 at *
  generalize v798.toNat = n798 at *
  generalize v802.toNat = n802 at *
  generalize v803.toNat = n803 at *
  generalize v805.toNat = n805 at *
  generalize v812.toNat = n812 at *
  generalize v819.toNat = n819 at *
  generalize v828.toNat = n828 at *
  generalize v832.toNat = n832 at *
  generalize v1114.toNat = n1114 at *
  generalize v1116.toNat = n1116 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S16 {v579 v582 v1114 v1116 v1117 v1118 v1120 v1121 v1122 v1123 v1124 v1125 v1126 v1127 : Word}
    (t1118 : v1118.toNat = (v1114.toNat + v579.toNat) % 2 ^ 32)
    (t1120 : v1117.toNat + 2 ^ 32 * v1120.toNat = v1116.toNat + v582.toNat)
    (t1122 : v1122.toNat = (v1118.toNat + v1120.toNat) % 2 ^ 32)
    (t1125 : v1125.toNat = (v1123.toNat + v1122.toNat) % 2 ^ 32)
    (t1126 : v1124.toNat + 2 ^ 32 * v1126.toNat = v1121.toNat + v1117.toNat)
    (t1127 : v1127.toNat = (v1125.toNat + v1126.toNat) % 2 ^ 32) :
    v1124.toNat + 2 ^ 32 * v1127.toNat = ((v1121.toNat + 2 ^ 32 * v1123.toNat) + (v582.toNat + 2 ^ 32 * v579.toNat) + (v1116.toNat + 2 ^ 32 * v1114.toNat)) % 2 ^ 64 := by
  obtain ⟨q1118, eq1118⟩ := mod_q t1118; clear t1118
  obtain ⟨q1122, eq1122⟩ := mod_q t1122; clear t1122
  obtain ⟨q1125, eq1125⟩ := mod_q t1125; clear t1125
  obtain ⟨q1127, eq1127⟩ := mod_q t1127; clear t1127
  have key : v1124.toNat + 2 ^ 32 * v1127.toNat + 2 ^ 64 * (q1118 + q1122 + q1125 + q1127) = ((v1121.toNat + 2 ^ 32 * v1123.toNat) + (v582.toNat + 2 ^ 32 * v579.toNat) + (v1116.toNat + 2 ^ 32 * v1114.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v579.toNat = n579 at *
    generalize v582.toNat = n582 at *
    generalize v1114.toNat = n1114 at *
    generalize v1116.toNat = n1116 at *
    generalize v1117.toNat = n1117 at *
    generalize v1118.toNat = n1118 at *
    generalize v1120.toNat = n1120 at *
    generalize v1121.toNat = n1121 at *
    generalize v1122.toNat = n1122 at *
    generalize v1123.toNat = n1123 at *
    generalize v1124.toNat = n1124 at *
    generalize v1125.toNat = n1125 at *
    generalize v1126.toNat = n1126 at *
    generalize v1127.toNat = n1127 at *
    omega
  exact smm_key key (smm_lt v1124 v1127)

set_option maxHeartbeats 10000000 in
theorem evr_v_R7 {v1124 v1127 : Word}
     :
    v1124.toNat = (v1124.toNat + 2 ^ 32 * v1127.toNat) % 2 ^ 32 := by
  have := v1124.isLt; have := v1127.isLt
  generalize v1124.toNat = n1124 at *
  generalize v1127.toNat = n1127 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S16h {v1124 v1127 : Word}
     :
    v1127.toNat = (v1124.toNat + 2 ^ 32 * v1127.toNat) / 2 ^ 32 := by
  have := v1124.isLt; have := v1127.isLt
  generalize v1124.toNat = n1124 at *
  generalize v1127.toNat = n1127 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_R8 {v1124 v1127 v1128 v1129 v1130 : Word}
    (t1128 : v1128.toNat = v1127.toNat * 2 ^ 3 % 2 ^ 32)
    (t1129 : v1129.toNat = v1124.toNat / 2 ^ 29)
    (t1130 : v1130.toNat = v1129.toNat + v1128.toNat) :
    v1130.toNat = (v1124.toNat / 2 ^ 29 + v1127.toNat * 2 ^ 3) % 2 ^ 32 := by
  have := v1124.isLt; have := v1127.isLt; have := v1128.isLt; have := v1129.isLt; have := v1130.isLt
  generalize v1124.toNat = n1124 at *
  generalize v1127.toNat = n1127 at *
  generalize v1128.toNat = n1128 at *
  generalize v1129.toNat = n1129 at *
  generalize v1130.toNat = n1130 at *
  omega

end C3.RV32
