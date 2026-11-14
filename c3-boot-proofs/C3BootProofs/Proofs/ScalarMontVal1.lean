import C3BootProofs.Proofs.ScalarMontFacts

/-! # `montgomery_mul`'s values, part 1

Each lemma proves one value the code holds in words from its instructions' facts. `scripts/gen-scalar-mont.py` writes this file. -/

namespace C3.RV32

open C3.Image

theorem smm_v_PAA1BB1 {v333 v364 v582 v583 : Word}
    (t582 : v582.toNat = v333.toNat * v364.toNat % 2 ^ 32)
    (t583 : v583.toNat = v333.toNat * v364.toNat / 2 ^ 32) :
    v582.toNat + 2 ^ 32 * v583.toNat = v333.toNat * v364.toNat := by
  have := v333.isLt; have := v364.isLt; have := v582.isLt; have := v583.isLt
  generalize v333.toNat = n333 at *
  generalize v364.toNat = n364 at *
  generalize v582.toNat = n582 at *
  generalize v583.toNat = n583 at *
  omega

theorem smm_v_PAA2BB0 {v335 v350 v569 v571 : Word}
    (t569 : v569.toNat = v335.toNat * v350.toNat % 2 ^ 32)
    (t571 : v571.toNat = v335.toNat * v350.toNat / 2 ^ 32) :
    v569.toNat + 2 ^ 32 * v571.toNat = v335.toNat * v350.toNat := by
  have := v335.isLt; have := v350.isLt; have := v569.isLt; have := v571.isLt
  generalize v335.toNat = n335 at *
  generalize v350.toNat = n350 at *
  generalize v569.toNat = n569 at *
  generalize v571.toNat = n571 at *
  omega

theorem smm_v_Z7 {v36 v52 v208 v234 v555 v557 v569 v571 v582 v583 v676 v679 v681 v682 v684 v686 v688 v690 v693 v695 v698 v702 v704 v705 v706 v707 : Word}
    (t676 : v682.toNat + v36.toNat = v582.toNat + 2 ^ 32 * v676.toNat)
    (t679 : v679.toNat = (v583.toNat + 2 ^ 32 - v676.toNat) % 2 ^ 32)
    (t681 : v681.toNat = (v679.toNat + 2 ^ 32 - v52.toNat) % 2 ^ 32)
    (t684 : v684.toNat = (v681.toNat + v555.toNat) % 2 ^ 32)
    (t688 : v686.toNat + 2 ^ 32 * v688.toNat = v557.toNat + v682.toNat)
    (t690 : v690.toNat = (v688.toNat + v571.toNat) % 2 ^ 32)
    (t693 : v693.toNat = (v684.toNat + v690.toNat) % 2 ^ 32)
    (t698 : v695.toNat + 2 ^ 32 * v698.toNat = v569.toNat + v686.toNat)
    (t702 : v702.toNat = (v698.toNat + v208.toNat) % 2 ^ 32)
    (t705 : v705.toNat = (v693.toNat + v702.toNat) % 2 ^ 32)
    (t706 : v704.toNat + 2 ^ 32 * v706.toNat = v695.toNat + v234.toNat)
    (t707 : v707.toNat = (v705.toNat + v706.toNat) % 2 ^ 32) :
    v704.toNat + 2 ^ 32 * v707.toNat = ((((v557.toNat + 2 ^ 32 * v555.toNat) + (v582.toNat + 2 ^ 32 * v583.toNat) + (v569.toNat + 2 ^ 32 * v571.toNat)) % 2 ^ 64) + (((v234.toNat + 2 ^ 32 * v208.toNat) + (2 ^ 64 - (v36.toNat + 2 ^ 32 * v52.toNat))) % 2 ^ 64)) % 2 ^ 64 := by
  obtain ⟨q679, eq679⟩ := mod_q t679; clear t679
  obtain ⟨q681, eq681⟩ := mod_q t681; clear t681
  obtain ⟨q684, eq684⟩ := mod_q t684; clear t684
  obtain ⟨q690, eq690⟩ := mod_q t690; clear t690
  obtain ⟨q693, eq693⟩ := mod_q t693; clear t693
  obtain ⟨q702, eq702⟩ := mod_q t702; clear t702
  obtain ⟨q705, eq705⟩ := mod_q t705; clear t705
  obtain ⟨q707, eq707⟩ := mod_q t707; clear t707
  obtain ⟨k0, ek0⟩ : ∃ k, ((v234.toNat + 2 ^ 32 * v208.toNat) + (2 ^ 64 - (v36.toNat + 2 ^ 32 * v52.toNat))) % 2 ^ 64 + 2 ^ 64 * k = ((v234.toNat + 2 ^ 32 * v208.toNat) + (2 ^ 64 - (v36.toNat + 2 ^ 32 * v52.toNat))) := ⟨_, Nat.mod_add_div _ _⟩
  obtain ⟨k1, ek1⟩ : ∃ k, ((v557.toNat + 2 ^ 32 * v555.toNat) + (v582.toNat + 2 ^ 32 * v583.toNat) + (v569.toNat + 2 ^ 32 * v571.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v557.toNat + 2 ^ 32 * v555.toNat) + (v582.toNat + 2 ^ 32 * v583.toNat) + (v569.toNat + 2 ^ 32 * v571.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v704.toNat + 2 ^ 32 * v707.toNat + 2 ^ 64 * (q679 + q681 + q684 + q690 + q693 + q702 + q705 + q707) = ((((v557.toNat + 2 ^ 32 * v555.toNat) + (v582.toNat + 2 ^ 32 * v583.toNat) + (v569.toNat + 2 ^ 32 * v571.toNat)) % 2 ^ 64) + (((v234.toNat + 2 ^ 32 * v208.toNat) + (2 ^ 64 - (v36.toNat + 2 ^ 32 * v52.toNat))) % 2 ^ 64)) + 2 ^ 64 * (k1 + k0 + 1) := by
    have := v36.isLt; have := v52.isLt; have := v676.isLt; skip
    generalize v36.toNat = n36 at *
    generalize v52.toNat = n52 at *
    generalize v208.toNat = n208 at *
    generalize v234.toNat = n234 at *
    generalize v555.toNat = n555 at *
    generalize v557.toNat = n557 at *
    generalize v569.toNat = n569 at *
    generalize v571.toNat = n571 at *
    generalize v582.toNat = n582 at *
    generalize v583.toNat = n583 at *
    generalize v676.toNat = n676 at *
    generalize v679.toNat = n679 at *
    generalize v681.toNat = n681 at *
    generalize v682.toNat = n682 at *
    generalize v684.toNat = n684 at *
    generalize v686.toNat = n686 at *
    generalize v688.toNat = n688 at *
    generalize v690.toNat = n690 at *
    generalize v693.toNat = n693 at *
    generalize v695.toNat = n695 at *
    generalize v698.toNat = n698 at *
    generalize v702.toNat = n702 at *
    generalize v704.toNat = n704 at *
    generalize v705.toNat = n705 at *
    generalize v706.toNat = n706 at *
    generalize v707.toNat = n707 at *
    omega
  exact smm_key key (smm_lt v704 v707)

theorem smm_v_PAA0BB3 {v330 v392 v559 v561 : Word}
    (t559 : v559.toNat = v392.toNat * v330.toNat % 2 ^ 32)
    (t561 : v561.toNat = v392.toNat * v330.toNat / 2 ^ 32) :
    v559.toNat + 2 ^ 32 * v561.toNat = v330.toNat * v392.toNat := by
  have := Nat.mul_comm v330.toNat v392.toNat
  have := v330.isLt; have := v392.isLt; have := v559.isLt; have := v561.isLt
  generalize v330.toNat = n330 at *
  generalize v392.toNat = n392 at *
  generalize v559.toNat = n559 at *
  generalize v561.toNat = n561 at *
  omega

theorem smm_v_PAA1BB2 {v333 v369 v585 v587 : Word}
    (t585 : v585.toNat = v369.toNat * v333.toNat % 2 ^ 32)
    (t587 : v587.toNat = v369.toNat * v333.toNat / 2 ^ 32) :
    v585.toNat + 2 ^ 32 * v587.toNat = v333.toNat * v369.toNat := by
  have := Nat.mul_comm v333.toNat v369.toNat
  have := v333.isLt; have := v369.isLt; have := v585.isLt; have := v587.isLt
  generalize v333.toNat = n333 at *
  generalize v369.toNat = n369 at *
  generalize v585.toNat = n585 at *
  generalize v587.toNat = n587 at *
  omega

theorem smm_v_PAA2BB1 {v335 v364 v597 v599 : Word}
    (t597 : v597.toNat = v335.toNat * v364.toNat / 2 ^ 32)
    (t599 : v599.toNat = v335.toNat * v364.toNat % 2 ^ 32) :
    v599.toNat + 2 ^ 32 * v597.toNat = v335.toNat * v364.toNat := by
  have := v335.isLt; have := v364.isLt; have := v597.isLt; have := v599.isLt
  generalize v335.toNat = n335 at *
  generalize v364.toNat = n364 at *
  generalize v597.toNat = n597 at *
  generalize v599.toNat = n599 at *
  omega

theorem smm_v_PAA3BB0 {v350 v375 v573 v575 : Word}
    (t573 : v573.toNat = v375.toNat * v350.toNat % 2 ^ 32)
    (t575 : v575.toNat = v375.toNat * v350.toNat / 2 ^ 32) :
    v573.toNat + 2 ^ 32 * v575.toNat = v375.toNat * v350.toNat := by
  have := v350.isLt; have := v375.isLt; have := v573.isLt; have := v575.isLt
  generalize v350.toNat = n350 at *
  generalize v375.toNat = n375 at *
  generalize v573.toNat = n573 at *
  generalize v575.toNat = n575 at *
  omega

theorem smm_v_PAA0B4 {v60 v330 v564 v566 : Word}
    (t564 : v564.toNat = v330.toNat * v60.toNat % 2 ^ 32)
    (t566 : v566.toNat = v330.toNat * v60.toNat / 2 ^ 32) :
    v564.toNat + 2 ^ 32 * v566.toNat = v330.toNat * v60.toNat := by
  have := v60.isLt; have := v330.isLt; have := v564.isLt; have := v566.isLt
  generalize v60.toNat = n60 at *
  generalize v330.toNat = n330 at *
  generalize v564.toNat = n564 at *
  generalize v566.toNat = n566 at *
  omega

theorem smm_v_PAA1BB3 {v333 v392 v589 v591 : Word}
    (t589 : v589.toNat = v392.toNat * v333.toNat % 2 ^ 32)
    (t591 : v591.toNat = v392.toNat * v333.toNat / 2 ^ 32) :
    v589.toNat + 2 ^ 32 * v591.toNat = v333.toNat * v392.toNat := by
  have := Nat.mul_comm v333.toNat v392.toNat
  have := v333.isLt; have := v392.isLt; have := v589.isLt; have := v591.isLt
  generalize v333.toNat = n333 at *
  generalize v392.toNat = n392 at *
  generalize v589.toNat = n589 at *
  generalize v591.toNat = n591 at *
  omega

theorem smm_v_PAA2BB2 {v335 v369 v612 v616 : Word}
    (t612 : v612.toNat = v335.toNat * v369.toNat / 2 ^ 32)
    (t616 : v616.toNat = v335.toNat * v369.toNat % 2 ^ 32) :
    v616.toNat + 2 ^ 32 * v612.toNat = v335.toNat * v369.toNat := by
  have := v335.isLt; have := v369.isLt; have := v612.isLt; have := v616.isLt
  generalize v335.toNat = n335 at *
  generalize v369.toNat = n369 at *
  generalize v612.toNat = n612 at *
  generalize v616.toNat = n616 at *
  omega

theorem smm_v_PAA3BB1 {v364 v375 v601 v604 : Word}
    (t601 : v601.toNat = v375.toNat * v364.toNat % 2 ^ 32)
    (t604 : v604.toNat = v375.toNat * v364.toNat / 2 ^ 32) :
    v601.toNat + 2 ^ 32 * v604.toNat = v375.toNat * v364.toNat := by
  have := v364.isLt; have := v375.isLt; have := v601.isLt; have := v604.isLt
  generalize v364.toNat = n364 at *
  generalize v375.toNat = n375 at *
  generalize v601.toNat = n601 at *
  generalize v604.toNat = n604 at *
  omega

theorem smm_v_PA4BB0 {v73 v350 v578 v580 : Word}
    (t578 : v578.toNat = v350.toNat * v73.toNat % 2 ^ 32)
    (t580 : v580.toNat = v350.toNat * v73.toNat / 2 ^ 32) :
    v578.toNat + 2 ^ 32 * v580.toNat = v73.toNat * v350.toNat := by
  have := Nat.mul_comm v350.toNat v73.toNat
  have := v73.isLt; have := v350.isLt; have := v578.isLt; have := v580.isLt
  generalize v73.toNat = n73 at *
  generalize v350.toNat = n350 at *
  generalize v578.toNat = n578 at *
  generalize v580.toNat = n580 at *
  omega

theorem smm_v_PAA1B4 {v60 v333 v593 v595 : Word}
    (t593 : v593.toNat = v333.toNat * v60.toNat % 2 ^ 32)
    (t595 : v595.toNat = v333.toNat * v60.toNat / 2 ^ 32) :
    v593.toNat + 2 ^ 32 * v595.toNat = v333.toNat * v60.toNat := by
  have := v60.isLt; have := v333.isLt; have := v593.isLt; have := v595.isLt
  generalize v60.toNat = n60 at *
  generalize v333.toNat = n333 at *
  generalize v593.toNat = n593 at *
  generalize v595.toNat = n595 at *
  omega

theorem smm_v_PAA2BB3 {v335 v392 v618 v620 : Word}
    (t618 : v618.toNat = v392.toNat * v335.toNat % 2 ^ 32)
    (t620 : v620.toNat = v392.toNat * v335.toNat / 2 ^ 32) :
    v618.toNat + 2 ^ 32 * v620.toNat = v335.toNat * v392.toNat := by
  have := Nat.mul_comm v335.toNat v392.toNat
  have := v335.isLt; have := v392.isLt; have := v618.isLt; have := v620.isLt
  generalize v335.toNat = n335 at *
  generalize v392.toNat = n392 at *
  generalize v618.toNat = n618 at *
  generalize v620.toNat = n620 at *
  omega

theorem smm_v_PAA3BB2 {v369 v375 v636 v638 : Word}
    (t636 : v636.toNat = v375.toNat * v369.toNat / 2 ^ 32)
    (t638 : v638.toNat = v375.toNat * v369.toNat % 2 ^ 32) :
    v638.toNat + 2 ^ 32 * v636.toNat = v375.toNat * v369.toNat := by
  have := v369.isLt; have := v375.isLt; have := v636.isLt; have := v638.isLt
  generalize v369.toNat = n369 at *
  generalize v375.toNat = n375 at *
  generalize v636.toNat = n636 at *
  generalize v638.toNat = n638 at *
  omega

theorem smm_v_PA4BB1 {v73 v364 v608 v610 : Word}
    (t608 : v608.toNat = v364.toNat * v73.toNat % 2 ^ 32)
    (t610 : v610.toNat = v364.toNat * v73.toNat / 2 ^ 32) :
    v608.toNat + 2 ^ 32 * v610.toNat = v73.toNat * v364.toNat := by
  have := Nat.mul_comm v364.toNat v73.toNat
  have := v73.isLt; have := v364.isLt; have := v608.isLt; have := v610.isLt
  generalize v73.toNat = n73 at *
  generalize v364.toNat = n364 at *
  generalize v608.toNat = n608 at *
  generalize v610.toNat = n610 at *
  omega

theorem smm_v_Z10 {v141 v147 v314 v322 v593 v595 v608 v610 v618 v620 v636 v638 v920 v921 v923 v925 v927 v928 v930 v932 v933 v935 v936 v938 v940 v941 v942 v944 v945 v949 v951 v960 : Word}
    (t920 : v921.toNat + v147.toNat = v608.toNat + 2 ^ 32 * v920.toNat)
    (t923 : v923.toNat = (v610.toNat + 2 ^ 32 - v920.toNat) % 2 ^ 32)
    (t927 : v927.toNat = (v923.toNat + v595.toNat) % 2 ^ 32)
    (t928 : v925.toNat + 2 ^ 32 * v928.toNat = v593.toNat + v921.toNat)
    (t930 : v930.toNat = (v927.toNat + 2 ^ 32 - v141.toNat) % 2 ^ 32)
    (t932 : v932.toNat = (v928.toNat + v620.toNat) % 2 ^ 32)
    (t933 : v933.toNat = (v930.toNat + v932.toNat) % 2 ^ 32)
    (t936 : v935.toNat + 2 ^ 32 * v936.toNat = v618.toNat + v925.toNat)
    (t940 : v940.toNat = (v636.toNat + v936.toNat) % 2 ^ 32)
    (t941 : v938.toNat + 2 ^ 32 * v941.toNat = v638.toNat + v935.toNat)
    (t942 : v942.toNat = (v933.toNat + v940.toNat) % 2 ^ 32)
    (t944 : v944.toNat = (v941.toNat + 2 ^ 32 - v322.toNat) % 2 ^ 32)
    (t945 : v945.toNat = (v942.toNat + v944.toNat) % 2 ^ 32)
    (t949 : v960.toNat + v314.toNat = v938.toNat + 2 ^ 32 * v949.toNat)
    (t951 : v951.toNat = (v945.toNat + 2 ^ 32 - v949.toNat) % 2 ^ 32) :
    v960.toNat + 2 ^ 32 * v951.toNat = ((((v593.toNat + 2 ^ 32 * v595.toNat) + (v618.toNat + 2 ^ 32 * v620.toNat) + (v638.toNat + 2 ^ 32 * v636.toNat) + (v608.toNat + 2 ^ 32 * v610.toNat)) % 2 ^ 64) + (2 ^ 64 - (((v314.toNat + 2 ^ 32 * v322.toNat) + (v147.toNat + 2 ^ 32 * v141.toNat)) % 2 ^ 64))) % 2 ^ 64 := by
  obtain ⟨q923, eq923⟩ := mod_q t923; clear t923
  obtain ⟨q927, eq927⟩ := mod_q t927; clear t927
  obtain ⟨q930, eq930⟩ := mod_q t930; clear t930
  obtain ⟨q932, eq932⟩ := mod_q t932; clear t932
  obtain ⟨q933, eq933⟩ := mod_q t933; clear t933
  obtain ⟨q940, eq940⟩ := mod_q t940; clear t940
  obtain ⟨q942, eq942⟩ := mod_q t942; clear t942
  obtain ⟨q944, eq944⟩ := mod_q t944; clear t944
  obtain ⟨q945, eq945⟩ := mod_q t945; clear t945
  obtain ⟨q951, eq951⟩ := mod_q t951; clear t951
  obtain ⟨k0, ek0⟩ : ∃ k, ((v314.toNat + 2 ^ 32 * v322.toNat) + (v147.toNat + 2 ^ 32 * v141.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v314.toNat + 2 ^ 32 * v322.toNat) + (v147.toNat + 2 ^ 32 * v141.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  obtain ⟨k1, ek1⟩ : ∃ k, ((v593.toNat + 2 ^ 32 * v595.toNat) + (v618.toNat + 2 ^ 32 * v620.toNat) + (v638.toNat + 2 ^ 32 * v636.toNat) + (v608.toNat + 2 ^ 32 * v610.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v593.toNat + 2 ^ 32 * v595.toNat) + (v618.toNat + 2 ^ 32 * v620.toNat) + (v638.toNat + 2 ^ 32 * v636.toNat) + (v608.toNat + 2 ^ 32 * v610.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v960.toNat + 2 ^ 32 * v951.toNat + 2 ^ 64 * (q923 + q927 + q930 + q932 + q933 + q940 + q942 + q944 + q945 + q951 + k0) = ((((v593.toNat + 2 ^ 32 * v595.toNat) + (v618.toNat + 2 ^ 32 * v620.toNat) + (v638.toNat + 2 ^ 32 * v636.toNat) + (v608.toNat + 2 ^ 32 * v610.toNat)) % 2 ^ 64) + (2 ^ 64 - (((v314.toNat + 2 ^ 32 * v322.toNat) + (v147.toNat + 2 ^ 32 * v141.toNat)) % 2 ^ 64))) + 2 ^ 64 * (k1 + 3) := by
    have := v141.isLt; have := v147.isLt; have := v314.isLt; have := v322.isLt; have := v920.isLt; have := v949.isLt; skip
    generalize v141.toNat = n141 at *
    generalize v147.toNat = n147 at *
    generalize v314.toNat = n314 at *
    generalize v322.toNat = n322 at *
    generalize v593.toNat = n593 at *
    generalize v595.toNat = n595 at *
    generalize v608.toNat = n608 at *
    generalize v610.toNat = n610 at *
    generalize v618.toNat = n618 at *
    generalize v620.toNat = n620 at *
    generalize v636.toNat = n636 at *
    generalize v638.toNat = n638 at *
    generalize v920.toNat = n920 at *
    generalize v921.toNat = n921 at *
    generalize v923.toNat = n923 at *
    generalize v925.toNat = n925 at *
    generalize v927.toNat = n927 at *
    generalize v928.toNat = n928 at *
    generalize v930.toNat = n930 at *
    generalize v932.toNat = n932 at *
    generalize v933.toNat = n933 at *
    generalize v935.toNat = n935 at *
    generalize v936.toNat = n936 at *
    generalize v938.toNat = n938 at *
    generalize v940.toNat = n940 at *
    generalize v941.toNat = n941 at *
    generalize v942.toNat = n942 at *
    generalize v944.toNat = n944 at *
    generalize v945.toNat = n945 at *
    generalize v949.toNat = n949 at *
    generalize v951.toNat = n951 at *
    generalize v960.toNat = n960 at *
    omega
  exact smm_key key (smm_lt v960 v951)

theorem smm_v_PAA2B4 {v60 v335 v622 v624 : Word}
    (t622 : v622.toNat = v335.toNat * v60.toNat % 2 ^ 32)
    (t624 : v624.toNat = v335.toNat * v60.toNat / 2 ^ 32) :
    v622.toNat + 2 ^ 32 * v624.toNat = v335.toNat * v60.toNat := by
  have := v60.isLt; have := v335.isLt; have := v622.isLt; have := v624.isLt
  generalize v60.toNat = n60 at *
  generalize v335.toNat = n335 at *
  generalize v622.toNat = n622 at *
  generalize v624.toNat = n624 at *
  omega

theorem smm_v_PAA3BB3 {v375 v392 v641 v647 : Word}
    (t641 : v641.toNat = v375.toNat * v392.toNat % 2 ^ 32)
    (t647 : v647.toNat = v375.toNat * v392.toNat / 2 ^ 32) :
    v641.toNat + 2 ^ 32 * v647.toNat = v375.toNat * v392.toNat := by
  have := v375.isLt; have := v392.isLt; have := v641.isLt; have := v647.isLt
  generalize v375.toNat = n375 at *
  generalize v392.toNat = n392 at *
  generalize v641.toNat = n641 at *
  generalize v647.toNat = n647 at *
  omega

theorem smm_v_PA4BB2 {v73 v369 v651 v653 : Word}
    (t651 : v651.toNat = v369.toNat * v73.toNat % 2 ^ 32)
    (t653 : v653.toNat = v369.toNat * v73.toNat / 2 ^ 32) :
    v651.toNat + 2 ^ 32 * v653.toNat = v73.toNat * v369.toNat := by
  have := Nat.mul_comm v369.toNat v73.toNat
  have := v73.isLt; have := v369.isLt; have := v651.isLt; have := v653.isLt
  generalize v73.toNat = n73 at *
  generalize v369.toNat = n369 at *
  generalize v651.toNat = n651 at *
  generalize v653.toNat = n653 at *
  omega

theorem smm_v_Z11 {v622 v624 v641 v647 v651 v653 v984 v987 v989 v991 v995 v997 v999 v1004 v1006 v1007 v1008 v1010 v1012 v1014 : Word}
    (t984 : v984.toNat = (v624.toNat + v653.toNat) % 2 ^ 32)
    (t989 : v987.toNat + 2 ^ 32 * v989.toNat = v622.toNat + v651.toNat)
    (t991 : v991.toNat = (v984.toNat + v989.toNat) % 2 ^ 32)
    (t997 : v1007.toNat + v995.toNat = v987.toNat + 2 ^ 32 * v997.toNat)
    (t999 : v999.toNat = (v991.toNat + 2 ^ 32 - v997.toNat) % 2 ^ 32)
    (t1006 : v1006.toNat = (v999.toNat + v647.toNat) % 2 ^ 32)
    (t1008 : v1008.toNat = (v1006.toNat + 2 ^ 32 - v1004.toNat) % 2 ^ 32)
    (t1012 : v1010.toNat + 2 ^ 32 * v1012.toNat = v641.toNat + v1007.toNat)
    (t1014 : v1014.toNat = (v1008.toNat + v1012.toNat) % 2 ^ 32) :
    v1010.toNat + 2 ^ 32 * v1014.toNat = ((((v622.toNat + 2 ^ 32 * v624.toNat) + (v641.toNat + 2 ^ 32 * v647.toNat) + (v651.toNat + 2 ^ 32 * v653.toNat)) % 2 ^ 64) + (2 ^ 64 - (v995.toNat + 2 ^ 32 * v1004.toNat))) % 2 ^ 64 := by
  obtain ⟨q984, eq984⟩ := mod_q t984; clear t984
  obtain ⟨q991, eq991⟩ := mod_q t991; clear t991
  obtain ⟨q999, eq999⟩ := mod_q t999; clear t999
  obtain ⟨q1006, eq1006⟩ := mod_q t1006; clear t1006
  obtain ⟨q1008, eq1008⟩ := mod_q t1008; clear t1008
  obtain ⟨q1014, eq1014⟩ := mod_q t1014; clear t1014
  obtain ⟨k0, ek0⟩ : ∃ k, ((v622.toNat + 2 ^ 32 * v624.toNat) + (v641.toNat + 2 ^ 32 * v647.toNat) + (v651.toNat + 2 ^ 32 * v653.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v622.toNat + 2 ^ 32 * v624.toNat) + (v641.toNat + 2 ^ 32 * v647.toNat) + (v651.toNat + 2 ^ 32 * v653.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v1010.toNat + 2 ^ 32 * v1014.toNat + 2 ^ 64 * (q984 + q991 + q999 + q1006 + q1008 + q1014) = ((((v622.toNat + 2 ^ 32 * v624.toNat) + (v641.toNat + 2 ^ 32 * v647.toNat) + (v651.toNat + 2 ^ 32 * v653.toNat)) % 2 ^ 64) + (2 ^ 64 - (v995.toNat + 2 ^ 32 * v1004.toNat))) + 2 ^ 64 * (k0 + 1) := by
    have := v995.isLt; have := v997.isLt; have := v1004.isLt; skip
    generalize v622.toNat = n622 at *
    generalize v624.toNat = n624 at *
    generalize v641.toNat = n641 at *
    generalize v647.toNat = n647 at *
    generalize v651.toNat = n651 at *
    generalize v653.toNat = n653 at *
    generalize v984.toNat = n984 at *
    generalize v987.toNat = n987 at *
    generalize v989.toNat = n989 at *
    generalize v991.toNat = n991 at *
    generalize v995.toNat = n995 at *
    generalize v997.toNat = n997 at *
    generalize v999.toNat = n999 at *
    generalize v1004.toNat = n1004 at *
    generalize v1006.toNat = n1006 at *
    generalize v1007.toNat = n1007 at *
    generalize v1008.toNat = n1008 at *
    generalize v1010.toNat = n1010 at *
    generalize v1012.toNat = n1012 at *
    generalize v1014.toNat = n1014 at *
    omega
  exact smm_key key (smm_lt v1010 v1014)

theorem smm_v_PAA3B4 {v60 v375 v632 v633 : Word}
    (t632 : v632.toNat = v375.toNat * v60.toNat % 2 ^ 32)
    (t633 : v633.toNat = v375.toNat * v60.toNat / 2 ^ 32) :
    v632.toNat + 2 ^ 32 * v633.toNat = v375.toNat * v60.toNat := by
  have := v60.isLt; have := v375.isLt; have := v632.isLt; have := v633.isLt
  generalize v60.toNat = n60 at *
  generalize v375.toNat = n375 at *
  generalize v632.toNat = n632 at *
  generalize v633.toNat = n633 at *
  omega

theorem smm_v_PA4BB3 {v73 v392 v643 v649 : Word}
    (t643 : v643.toNat = v392.toNat * v73.toNat / 2 ^ 32)
    (t649 : v649.toNat = v392.toNat * v73.toNat % 2 ^ 32) :
    v649.toNat + 2 ^ 32 * v643.toNat = v73.toNat * v392.toNat := by
  have := Nat.mul_comm v392.toNat v73.toNat
  have := v73.isLt; have := v392.isLt; have := v643.isLt; have := v649.isLt
  generalize v73.toNat = n73 at *
  generalize v392.toNat = n392 at *
  generalize v643.toNat = n643 at *
  generalize v649.toNat = n649 at *
  omega

theorem smm_v_K12 {v632 v633 v643 v649 v658 v663 v666 v668 : Word}
    (t658 : v658.toNat = (v643.toNat + v633.toNat) % 2 ^ 32)
    (t666 : v663.toNat + 2 ^ 32 * v666.toNat = v649.toNat + v632.toNat)
    (t668 : v668.toNat = (v658.toNat + v666.toNat) % 2 ^ 32) :
    v663.toNat + 2 ^ 32 * v668.toNat = ((v632.toNat + 2 ^ 32 * v633.toNat) + (v649.toNat + 2 ^ 32 * v643.toNat)) % 2 ^ 64 := by
  obtain ⟨q658, eq658⟩ := mod_q t658; clear t658
  obtain ⟨q668, eq668⟩ := mod_q t668; clear t668
  have key : v663.toNat + 2 ^ 32 * v668.toNat + 2 ^ 64 * (q658 + q668) = ((v632.toNat + 2 ^ 32 * v633.toNat) + (v649.toNat + 2 ^ 32 * v643.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v632.toNat = n632 at *
    generalize v633.toNat = n633 at *
    generalize v643.toNat = n643 at *
    generalize v649.toNat = n649 at *
    generalize v658.toNat = n658 at *
    generalize v663.toNat = n663 at *
    generalize v666.toNat = n666 at *
    generalize v668.toNat = n668 at *
    omega
  exact smm_key key (smm_lt v663 v668)

theorem smm_v_Z12 {v208 v234 v663 v668 v731 v735 v739 v830 : Word}
    (t731 : v830.toNat + v234.toNat = v663.toNat + 2 ^ 32 * v731.toNat)
    (t735 : v735.toNat = (v668.toNat + 2 ^ 32 - v731.toNat) % 2 ^ 32)
    (t739 : v739.toNat = (v735.toNat + 2 ^ 32 - v208.toNat) % 2 ^ 32) :
    v830.toNat + 2 ^ 32 * v739.toNat = ((v663.toNat + 2 ^ 32 * v668.toNat) + (2 ^ 64 - (v234.toNat + 2 ^ 32 * v208.toNat))) % 2 ^ 64 := by
  obtain ⟨q735, eq735⟩ := mod_q t735; clear t735
  obtain ⟨q739, eq739⟩ := mod_q t739; clear t739
  have key : v830.toNat + 2 ^ 32 * v739.toNat + 2 ^ 64 * (q735 + q739) = ((v663.toNat + 2 ^ 32 * v668.toNat) + (2 ^ 64 - (v234.toNat + 2 ^ 32 * v208.toNat))) + 2 ^ 64 * (1) := by
    have := v208.isLt; have := v234.isLt; have := v731.isLt; skip
    generalize v208.toNat = n208 at *
    generalize v234.toNat = n234 at *
    generalize v663.toNat = n663 at *
    generalize v668.toNat = n668 at *
    generalize v731.toNat = n731 at *
    generalize v735.toNat = n735 at *
    generalize v739.toNat = n739 at *
    generalize v830.toNat = n830 at *
    omega
  exact smm_key key (smm_lt v830 v739)

theorem smm_v_N0 {v193 v214 v229 v232 : Word}
    (t214 : v214.toNat = v193.toNat * 307527195 % 2 ^ 32)
    (t229 : v229.toNat = v214.toNat % 2 ^ 29) :
    v229.toNat = ((v193.toNat + 2 ^ 32 * v232.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v193.isLt; have := v214.isLt; have := v229.isLt; have := v232.isLt
  generalize v193.toNat = n193 at *
  generalize v214.toNat = n214 at *
  generalize v229.toNat = n229 at *
  generalize v232.toNat = n232 at *
  omega

theorem smm_v_PN0L0 {v229 v231 v233 : Word}
    (t231 : v231.toNat = v229.toNat * 485872621 % 2 ^ 32)
    (t233 : v233.toNat = v229.toNat * 485872621 / 2 ^ 32) :
    v231.toNat + 2 ^ 32 * v233.toNat = v229.toNat * 485872621 := by
  have := v229.isLt; have := v231.isLt; have := v233.isLt
  generalize v229.toNat = n229 at *
  generalize v231.toNat = n231 at *
  generalize v233.toNat = n233 at *
  omega

theorem smm_v_T0 {v193 v231 v232 v233 v244 v248 v249 v250 : Word}
    (t248 : v248.toNat = (v233.toNat + v232.toNat) % 2 ^ 32)
    (t249 : v244.toNat + 2 ^ 32 * v249.toNat = v231.toNat + v193.toNat)
    (t250 : v250.toNat = (v248.toNat + v249.toNat) % 2 ^ 32) :
    v244.toNat + 2 ^ 32 * v250.toNat = ((v193.toNat + 2 ^ 32 * v232.toNat) + (v231.toNat + 2 ^ 32 * v233.toNat)) % 2 ^ 64 := by
  obtain ⟨q248, eq248⟩ := mod_q t248; clear t248
  obtain ⟨q250, eq250⟩ := mod_q t250; clear t250
  have key : v244.toNat + 2 ^ 32 * v250.toNat + 2 ^ 64 * (q248 + q250) = ((v193.toNat + 2 ^ 32 * v232.toNat) + (v231.toNat + 2 ^ 32 * v233.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v193.toNat = n193 at *
    generalize v231.toNat = n231 at *
    generalize v232.toNat = n232 at *
    generalize v233.toNat = n233 at *
    generalize v244.toNat = n244 at *
    generalize v248.toNat = n248 at *
    generalize v249.toNat = n249 at *
    generalize v250.toNat = n250 at *
    omega
  exact smm_key key (smm_lt v244 v250)

theorem smm_v_C0 {v244 v250 v251 v254 v256 v292 : Word}
    (t251 : v251.toNat = v244.toNat / 2 ^ 29)
    (t254 : v254.toNat = v250.toNat * 2 ^ 3 % 2 ^ 32)
    (t256 : v256.toNat = v251.toNat + v254.toNat)
    (t292 : v292.toNat = v250.toNat / 2 ^ 29) :
    v256.toNat + 2 ^ 32 * v292.toNat = (v244.toNat + 2 ^ 32 * v250.toNat) / 2 ^ 29 := by
  have := v244.isLt; have := v250.isLt; have := v251.isLt; have := v254.isLt; have := v256.isLt; have := v292.isLt
  generalize v244.toNat = n244 at *
  generalize v250.toNat = n250 at *
  generalize v251.toNat = n251 at *
  generalize v254.toNat = n254 at *
  generalize v256.toNat = n256 at *
  generalize v292.toNat = n292 at *
  omega

theorem smm_v_PN0L1 {v229 v247 v264 : Word}
    (t247 : v247.toNat = v229.toNat * 9640146 % 2 ^ 32)
    (t264 : v264.toNat = v229.toNat * 9640146 / 2 ^ 32) :
    v247.toNat + 2 ^ 32 * v264.toNat = v229.toNat * 9640146 := by
  have := v229.isLt; have := v247.isLt; have := v264.isLt
  generalize v229.toNat = n229 at *
  generalize v247.toNat = n247 at *
  generalize v264.toNat = n264 at *
  omega

theorem smm_v_S1 {v21 v28 v247 v256 v261 v263 v264 v283 v286 v289 v292 v294 v296 v298 : Word}
    (t283 : v283.toNat = (v264.toNat + v28.toNat) % 2 ^ 32)
    (t286 : v261.toNat + 2 ^ 32 * v286.toNat = v21.toNat + v247.toNat)
    (t289 : v289.toNat = (v286.toNat + v283.toNat) % 2 ^ 32)
    (t294 : v294.toNat = (v289.toNat + v292.toNat) % 2 ^ 32)
    (t296 : v263.toNat + 2 ^ 32 * v296.toNat = v261.toNat + v256.toNat)
    (t298 : v298.toNat = (v294.toNat + v296.toNat) % 2 ^ 32) :
    v263.toNat + 2 ^ 32 * v298.toNat = ((v256.toNat + 2 ^ 32 * v292.toNat) + (v21.toNat + 2 ^ 32 * v28.toNat) + (v247.toNat + 2 ^ 32 * v264.toNat)) % 2 ^ 64 := by
  obtain ⟨q283, eq283⟩ := mod_q t283; clear t283
  obtain ⟨q289, eq289⟩ := mod_q t289; clear t289
  obtain ⟨q294, eq294⟩ := mod_q t294; clear t294
  obtain ⟨q298, eq298⟩ := mod_q t298; clear t298
  have key : v263.toNat + 2 ^ 32 * v298.toNat + 2 ^ 64 * (q283 + q289 + q294 + q298) = ((v256.toNat + 2 ^ 32 * v292.toNat) + (v21.toNat + 2 ^ 32 * v28.toNat) + (v247.toNat + 2 ^ 32 * v264.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v21.toNat = n21 at *
    generalize v28.toNat = n28 at *
    generalize v247.toNat = n247 at *
    generalize v256.toNat = n256 at *
    generalize v261.toNat = n261 at *
    generalize v263.toNat = n263 at *
    generalize v264.toNat = n264 at *
    generalize v283.toNat = n283 at *
    generalize v286.toNat = n286 at *
    generalize v289.toNat = n289 at *
    generalize v292.toNat = n292 at *
    generalize v294.toNat = n294 at *
    generalize v296.toNat = n296 at *
    generalize v298.toNat = n298 at *
    omega
  exact smm_key key (smm_lt v263 v298)

theorem smm_v_N1 {v263 v266 v285 v298 : Word}
    (t266 : v266.toNat = v263.toNat * 307527195 % 2 ^ 32)
    (t285 : v285.toNat = v266.toNat % 2 ^ 29) :
    v285.toNat = ((v263.toNat + 2 ^ 32 * v298.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v263.isLt; have := v266.isLt; have := v285.isLt; have := v298.isLt
  generalize v263.toNat = n263 at *
  generalize v266.toNat = n266 at *
  generalize v285.toNat = n285 at *
  generalize v298.toNat = n298 at *
  omega

theorem smm_v_PN1L0 {v285 v287 v290 : Word}
    (t287 : v287.toNat = v285.toNat * 485872621 % 2 ^ 32)
    (t290 : v290.toNat = v285.toNat * 485872621 / 2 ^ 32) :
    v287.toNat + 2 ^ 32 * v290.toNat = v285.toNat * 485872621 := by
  have := v285.isLt; have := v287.isLt; have := v290.isLt
  generalize v285.toNat = n285 at *
  generalize v287.toNat = n287 at *
  generalize v290.toNat = n290 at *
  omega

theorem smm_v_T1 {v263 v287 v290 v298 v299 v303 v304 v305 : Word}
    (t303 : v303.toNat = (v298.toNat + v290.toNat) % 2 ^ 32)
    (t304 : v299.toNat + 2 ^ 32 * v304.toNat = v263.toNat + v287.toNat)
    (t305 : v305.toNat = (v303.toNat + v304.toNat) % 2 ^ 32) :
    v299.toNat + 2 ^ 32 * v305.toNat = ((v263.toNat + 2 ^ 32 * v298.toNat) + (v287.toNat + 2 ^ 32 * v290.toNat)) % 2 ^ 64 := by
  obtain ⟨q303, eq303⟩ := mod_q t303; clear t303
  obtain ⟨q305, eq305⟩ := mod_q t305; clear t305
  have key : v299.toNat + 2 ^ 32 * v305.toNat + 2 ^ 64 * (q303 + q305) = ((v263.toNat + 2 ^ 32 * v298.toNat) + (v287.toNat + 2 ^ 32 * v290.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v263.toNat = n263 at *
    generalize v287.toNat = n287 at *
    generalize v290.toNat = n290 at *
    generalize v298.toNat = n298 at *
    generalize v299.toNat = n299 at *
    generalize v303.toNat = n303 at *
    generalize v304.toNat = n304 at *
    generalize v305.toNat = n305 at *
    omega
  exact smm_key key (smm_lt v299 v305)

theorem smm_v_C1 {v299 v305 v306 v307 v310 v347 : Word}
    (t306 : v306.toNat = v299.toNat / 2 ^ 29)
    (t307 : v307.toNat = v305.toNat * 2 ^ 3 % 2 ^ 32)
    (t310 : v310.toNat = v306.toNat + v307.toNat)
    (t347 : v347.toNat = v305.toNat / 2 ^ 29) :
    v310.toNat + 2 ^ 32 * v347.toNat = (v299.toNat + 2 ^ 32 * v305.toNat) / 2 ^ 29 := by
  have := v299.isLt; have := v305.isLt; have := v306.isLt; have := v307.isLt; have := v310.isLt; have := v347.isLt
  generalize v299.toNat = n299 at *
  generalize v305.toNat = n305 at *
  generalize v306.toNat = n306 at *
  generalize v307.toNat = n307 at *
  generalize v310.toNat = n310 at *
  generalize v347.toNat = n347 at *
  omega

theorem smm_v_PN0L2 {v229 v295 v313 : Word}
    (t295 : v295.toNat = v229.toNat * 501691798 % 2 ^ 32)
    (t313 : v313.toNat = v229.toNat * 501691798 / 2 ^ 32) :
    v295.toNat + 2 ^ 32 * v313.toNat = v229.toNat * 501691798 := by
  have := v229.isLt; have := v295.isLt; have := v313.isLt
  generalize v229.toNat = n229 at *
  generalize v295.toNat = n295 at *
  generalize v313.toNat = n313 at *
  omega

theorem smm_v_PN1L1 {v285 v297 v321 : Word}
    (t297 : v297.toNat = v285.toNat * 9640146 % 2 ^ 32)
    (t321 : v321.toNat = v285.toNat * 9640146 / 2 ^ 32) :
    v297.toNat + 2 ^ 32 * v321.toNat = v285.toNat * 9640146 := by
  have := v285.isLt; have := v297.isLt; have := v321.isLt
  generalize v285.toNat = n285 at *
  generalize v297.toNat = n297 at *
  generalize v321.toNat = n321 at *
  omega

theorem smm_v_S2 {v36 v52 v295 v297 v309 v310 v311 v312 v313 v321 v338 v339 v340 v342 v344 v346 v347 v351 v352 v354 : Word}
    (t338 : v338.toNat = (v313.toNat + v52.toNat) % 2 ^ 32)
    (t339 : v309.toNat + 2 ^ 32 * v339.toNat = v36.toNat + v295.toNat)
    (t340 : v340.toNat = (v338.toNat + v339.toNat) % 2 ^ 32)
    (t342 : v342.toNat = (v340.toNat + v321.toNat) % 2 ^ 32)
    (t344 : v311.toNat + 2 ^ 32 * v344.toNat = v297.toNat + v309.toNat)
    (t346 : v346.toNat = (v342.toNat + v344.toNat) % 2 ^ 32)
    (t351 : v351.toNat = (v347.toNat + v346.toNat) % 2 ^ 32)
    (t352 : v312.toNat + 2 ^ 32 * v352.toNat = v310.toNat + v311.toNat)
    (t354 : v354.toNat = (v351.toNat + v352.toNat) % 2 ^ 32) :
    v312.toNat + 2 ^ 32 * v354.toNat = ((v310.toNat + 2 ^ 32 * v347.toNat) + (v36.toNat + 2 ^ 32 * v52.toNat) + (v295.toNat + 2 ^ 32 * v313.toNat) + (v297.toNat + 2 ^ 32 * v321.toNat)) % 2 ^ 64 := by
  obtain ⟨q338, eq338⟩ := mod_q t338; clear t338
  obtain ⟨q340, eq340⟩ := mod_q t340; clear t340
  obtain ⟨q342, eq342⟩ := mod_q t342; clear t342
  obtain ⟨q346, eq346⟩ := mod_q t346; clear t346
  obtain ⟨q351, eq351⟩ := mod_q t351; clear t351
  obtain ⟨q354, eq354⟩ := mod_q t354; clear t354
  have key : v312.toNat + 2 ^ 32 * v354.toNat + 2 ^ 64 * (q338 + q340 + q342 + q346 + q351 + q354) = ((v310.toNat + 2 ^ 32 * v347.toNat) + (v36.toNat + 2 ^ 32 * v52.toNat) + (v295.toNat + 2 ^ 32 * v313.toNat) + (v297.toNat + 2 ^ 32 * v321.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v36.toNat = n36 at *
    generalize v52.toNat = n52 at *
    generalize v295.toNat = n295 at *
    generalize v297.toNat = n297 at *
    generalize v309.toNat = n309 at *
    generalize v310.toNat = n310 at *
    generalize v311.toNat = n311 at *
    generalize v312.toNat = n312 at *
    generalize v313.toNat = n313 at *
    generalize v321.toNat = n321 at *
    generalize v338.toNat = n338 at *
    generalize v339.toNat = n339 at *
    generalize v340.toNat = n340 at *
    generalize v342.toNat = n342 at *
    generalize v344.toNat = n344 at *
    generalize v346.toNat = n346 at *
    generalize v347.toNat = n347 at *
    generalize v351.toNat = n351 at *
    generalize v352.toNat = n352 at *
    generalize v354.toNat = n354 at *
    omega
  exact smm_key key (smm_lt v312 v354)

theorem smm_v_N2 {v312 v316 v341 v354 : Word}
    (t316 : v316.toNat = v312.toNat * 307527195 % 2 ^ 32)
    (t341 : v341.toNat = v316.toNat % 2 ^ 29) :
    v341.toNat = ((v312.toNat + 2 ^ 32 * v354.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v312.isLt; have := v316.isLt; have := v341.isLt; have := v354.isLt
  generalize v312.toNat = n312 at *
  generalize v316.toNat = n316 at *
  generalize v341.toNat = n341 at *
  generalize v354.toNat = n354 at *
  omega

theorem smm_v_PN2L0 {v341 v343 v345 : Word}
    (t343 : v343.toNat = v341.toNat * 485872621 / 2 ^ 32)
    (t345 : v345.toNat = v341.toNat * 485872621 % 2 ^ 32) :
    v345.toNat + 2 ^ 32 * v343.toNat = v341.toNat * 485872621 := by
  have := v341.isLt; have := v343.isLt; have := v345.isLt
  generalize v341.toNat = n341 at *
  generalize v343.toNat = n343 at *
  generalize v345.toNat = n345 at *
  omega

theorem smm_v_T2 {v312 v343 v345 v354 v356 v358 v360 v365 : Word}
    (t356 : v356.toNat = (v354.toNat + v343.toNat) % 2 ^ 32)
    (t360 : v358.toNat + 2 ^ 32 * v360.toNat = v312.toNat + v345.toNat)
    (t365 : v365.toNat = (v356.toNat + v360.toNat) % 2 ^ 32) :
    v358.toNat + 2 ^ 32 * v365.toNat = ((v312.toNat + 2 ^ 32 * v354.toNat) + (v345.toNat + 2 ^ 32 * v343.toNat)) % 2 ^ 64 := by
  obtain ⟨q356, eq356⟩ := mod_q t356; clear t356
  obtain ⟨q365, eq365⟩ := mod_q t365; clear t365
  have key : v358.toNat + 2 ^ 32 * v365.toNat + 2 ^ 64 * (q356 + q365) = ((v312.toNat + 2 ^ 32 * v354.toNat) + (v345.toNat + 2 ^ 32 * v343.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v312.toNat = n312 at *
    generalize v343.toNat = n343 at *
    generalize v345.toNat = n345 at *
    generalize v354.toNat = n354 at *
    generalize v356.toNat = n356 at *
    generalize v358.toNat = n358 at *
    generalize v360.toNat = n360 at *
    generalize v365.toNat = n365 at *
    omega
  exact smm_key key (smm_lt v358 v365)

theorem smm_v_C2 {v358 v365 v366 v367 v370 v411 : Word}
    (t366 : v366.toNat = v358.toNat / 2 ^ 29)
    (t367 : v367.toNat = v365.toNat * 2 ^ 3 % 2 ^ 32)
    (t370 : v370.toNat = v366.toNat + v367.toNat)
    (t411 : v411.toNat = v365.toNat / 2 ^ 29) :
    v370.toNat + 2 ^ 32 * v411.toNat = (v358.toNat + 2 ^ 32 * v365.toNat) / 2 ^ 29 := by
  have := v358.isLt; have := v365.isLt; have := v366.isLt; have := v367.isLt; have := v370.isLt; have := v411.isLt
  generalize v358.toNat = n358 at *
  generalize v365.toNat = n365 at *
  generalize v366.toNat = n366 at *
  generalize v367.toNat = n367 at *
  generalize v370.toNat = n370 at *
  generalize v411.toNat = n411 at *
  omega

theorem smm_v_PN0L3 {v229 v357 v373 : Word}
    (t357 : v357.toNat = v229.toNat * 502512965 % 2 ^ 32)
    (t373 : v373.toNat = v229.toNat * 502512965 / 2 ^ 32) :
    v357.toNat + 2 ^ 32 * v373.toNat = v229.toNat * 502512965 := by
  have := v229.isLt; have := v357.isLt; have := v373.isLt
  generalize v229.toNat = n229 at *
  generalize v357.toNat = n357 at *
  generalize v373.toNat = n373 at *
  omega

theorem smm_v_PN1L2 {v285 v359 v378 : Word}
    (t359 : v359.toNat = v285.toNat * 501691798 % 2 ^ 32)
    (t378 : v378.toNat = v285.toNat * 501691798 / 2 ^ 32) :
    v359.toNat + 2 ^ 32 * v378.toNat = v285.toNat * 501691798 := by
  have := v285.isLt; have := v359.isLt; have := v378.isLt
  generalize v285.toNat = n285 at *
  generalize v359.toNat = n359 at *
  generalize v378.toNat = n378 at *
  omega

theorem smm_v_PN2L1 {v341 v361 v381 : Word}
    (t361 : v361.toNat = v341.toNat * 9640146 % 2 ^ 32)
    (t381 : v381.toNat = v341.toNat * 9640146 / 2 ^ 32) :
    v361.toNat + 2 ^ 32 * v381.toNat = v341.toNat * 9640146 := by
  have := v341.isLt; have := v361.isLt; have := v381.isLt
  generalize v341.toNat = n341 at *
  generalize v361.toNat = n361 at *
  generalize v381.toNat = n381 at *
  omega

theorem smm_v_S3 {v55 v90 v357 v359 v361 v370 v372 v373 v376 v377 v378 v379 v381 v389 v390 v393 v394 v395 v398 v399 v406 v408 v411 v413 v414 v415 : Word}
    (t389 : v389.toNat = (v373.toNat + v90.toNat) % 2 ^ 32)
    (t390 : v372.toNat + 2 ^ 32 * v390.toNat = v357.toNat + v55.toNat)
    (t393 : v393.toNat = (v390.toNat + v389.toNat) % 2 ^ 32)
    (t394 : v394.toNat = (v393.toNat + v378.toNat) % 2 ^ 32)
    (t395 : v376.toNat + 2 ^ 32 * v395.toNat = v359.toNat + v372.toNat)
    (t398 : v398.toNat = (v395.toNat + v394.toNat) % 2 ^ 32)
    (t399 : v399.toNat = (v381.toNat + v398.toNat) % 2 ^ 32)
    (t406 : v377.toNat + 2 ^ 32 * v406.toNat = v361.toNat + v376.toNat)
    (t408 : v408.toNat = (v399.toNat + v406.toNat) % 2 ^ 32)
    (t413 : v413.toNat = (v411.toNat + v408.toNat) % 2 ^ 32)
    (t414 : v379.toNat + 2 ^ 32 * v414.toNat = v377.toNat + v370.toNat)
    (t415 : v415.toNat = (v413.toNat + v414.toNat) % 2 ^ 32) :
    v379.toNat + 2 ^ 32 * v415.toNat = ((v370.toNat + 2 ^ 32 * v411.toNat) + (v55.toNat + 2 ^ 32 * v90.toNat) + (v357.toNat + 2 ^ 32 * v373.toNat) + (v359.toNat + 2 ^ 32 * v378.toNat) + (v361.toNat + 2 ^ 32 * v381.toNat)) % 2 ^ 64 := by
  obtain ⟨q389, eq389⟩ := mod_q t389; clear t389
  obtain ⟨q393, eq393⟩ := mod_q t393; clear t393
  obtain ⟨q394, eq394⟩ := mod_q t394; clear t394
  obtain ⟨q398, eq398⟩ := mod_q t398; clear t398
  obtain ⟨q399, eq399⟩ := mod_q t399; clear t399
  obtain ⟨q408, eq408⟩ := mod_q t408; clear t408
  obtain ⟨q413, eq413⟩ := mod_q t413; clear t413
  obtain ⟨q415, eq415⟩ := mod_q t415; clear t415
  have key : v379.toNat + 2 ^ 32 * v415.toNat + 2 ^ 64 * (q389 + q393 + q394 + q398 + q399 + q408 + q413 + q415) = ((v370.toNat + 2 ^ 32 * v411.toNat) + (v55.toNat + 2 ^ 32 * v90.toNat) + (v357.toNat + 2 ^ 32 * v373.toNat) + (v359.toNat + 2 ^ 32 * v378.toNat) + (v361.toNat + 2 ^ 32 * v381.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v55.toNat = n55 at *
    generalize v90.toNat = n90 at *
    generalize v357.toNat = n357 at *
    generalize v359.toNat = n359 at *
    generalize v361.toNat = n361 at *
    generalize v370.toNat = n370 at *
    generalize v372.toNat = n372 at *
    generalize v373.toNat = n373 at *
    generalize v376.toNat = n376 at *
    generalize v377.toNat = n377 at *
    generalize v378.toNat = n378 at *
    generalize v379.toNat = n379 at *
    generalize v381.toNat = n381 at *
    generalize v389.toNat = n389 at *
    generalize v390.toNat = n390 at *
    generalize v393.toNat = n393 at *
    generalize v394.toNat = n394 at *
    generalize v395.toNat = n395 at *
    generalize v398.toNat = n398 at *
    generalize v399.toNat = n399 at *
    generalize v406.toNat = n406 at *
    generalize v408.toNat = n408 at *
    generalize v411.toNat = n411 at *
    generalize v413.toNat = n413 at *
    generalize v414.toNat = n414 at *
    generalize v415.toNat = n415 at *
    omega
  exact smm_key key (smm_lt v379 v415)

theorem smm_v_N3 {v379 v382 v401 v415 : Word}
    (t382 : v382.toNat = v379.toNat * 307527195 % 2 ^ 32)
    (t401 : v401.toNat = v382.toNat % 2 ^ 29) :
    v401.toNat = ((v379.toNat + 2 ^ 32 * v415.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v379.isLt; have := v382.isLt; have := v401.isLt; have := v415.isLt
  generalize v379.toNat = n379 at *
  generalize v382.toNat = n382 at *
  generalize v401.toNat = n401 at *
  generalize v415.toNat = n415 at *
  omega

theorem smm_v_PN3L0 {v401 v402 v403 : Word}
    (t402 : v402.toNat = v401.toNat * 485872621 % 2 ^ 32)
    (t403 : v403.toNat = v401.toNat * 485872621 / 2 ^ 32) :
    v402.toNat + 2 ^ 32 * v403.toNat = v401.toNat * 485872621 := by
  have := v401.isLt; have := v402.isLt; have := v403.isLt
  generalize v401.toNat = n401 at *
  generalize v402.toNat = n402 at *
  generalize v403.toNat = n403 at *
  omega

theorem smm_v_T3 {v379 v402 v403 v415 v417 v418 v419 v421 : Word}
    (t417 : v417.toNat = (v415.toNat + v403.toNat) % 2 ^ 32)
    (t419 : v418.toNat + 2 ^ 32 * v419.toNat = v402.toNat + v379.toNat)
    (t421 : v421.toNat = (v417.toNat + v419.toNat) % 2 ^ 32) :
    v418.toNat + 2 ^ 32 * v421.toNat = ((v379.toNat + 2 ^ 32 * v415.toNat) + (v402.toNat + 2 ^ 32 * v403.toNat)) % 2 ^ 64 := by
  obtain ⟨q417, eq417⟩ := mod_q t417; clear t417
  obtain ⟨q421, eq421⟩ := mod_q t421; clear t421
  have key : v418.toNat + 2 ^ 32 * v421.toNat + 2 ^ 64 * (q417 + q421) = ((v379.toNat + 2 ^ 32 * v415.toNat) + (v402.toNat + 2 ^ 32 * v403.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v379.toNat = n379 at *
    generalize v402.toNat = n402 at *
    generalize v403.toNat = n403 at *
    generalize v415.toNat = n415 at *
    generalize v417.toNat = n417 at *
    generalize v418.toNat = n418 at *
    generalize v419.toNat = n419 at *
    generalize v421.toNat = n421 at *
    omega
  exact smm_key key (smm_lt v418 v421)

theorem smm_v_C3 {v418 v421 v431 v438 v439 v464 : Word}
    (t431 : v431.toNat = v418.toNat / 2 ^ 29)
    (t438 : v438.toNat = v421.toNat * 2 ^ 3 % 2 ^ 32)
    (t439 : v439.toNat = v431.toNat + v438.toNat)
    (t464 : v464.toNat = v421.toNat / 2 ^ 29) :
    v439.toNat + 2 ^ 32 * v464.toNat = (v418.toNat + 2 ^ 32 * v421.toNat) / 2 ^ 29 := by
  have := v418.isLt; have := v421.isLt; have := v431.isLt; have := v438.isLt; have := v439.isLt; have := v464.isLt
  generalize v418.toNat = n418 at *
  generalize v421.toNat = n421 at *
  generalize v431.toNat = n431 at *
  generalize v438.toNat = n438 at *
  generalize v439.toNat = n439 at *
  generalize v464.toNat = n464 at *
  omega

theorem smm_v_PN0L4 {v229 v410 v412 : Word}
    (t410 : v410.toNat = v229.toNat * 333 % 2 ^ 32)
    (t412 : v412.toNat = v229.toNat * 333 / 2 ^ 32) :
    v410.toNat + 2 ^ 32 * v412.toNat = v229.toNat * 333 := by
  have := v229.isLt; have := v410.isLt; have := v412.isLt
  generalize v229.toNat = n229 at *
  generalize v410.toNat = n410 at *
  generalize v412.toNat = n412 at *
  omega

theorem smm_v_PN1L3 {v285 v416 v420 : Word}
    (t416 : v416.toNat = v285.toNat * 502512965 / 2 ^ 32)
    (t420 : v420.toNat = v285.toNat * 502512965 % 2 ^ 32) :
    v420.toNat + 2 ^ 32 * v416.toNat = v285.toNat * 502512965 := by
  have := v285.isLt; have := v416.isLt; have := v420.isLt
  generalize v285.toNat = n285 at *
  generalize v416.toNat = n416 at *
  generalize v420.toNat = n420 at *
  omega

theorem smm_v_PN2L2 {v341 v428 v430 : Word}
    (t428 : v428.toNat = v341.toNat * 501691798 % 2 ^ 32)
    (t430 : v430.toNat = v341.toNat * 501691798 / 2 ^ 32) :
    v428.toNat + 2 ^ 32 * v430.toNat = v341.toNat * 501691798 := by
  have := v341.isLt; have := v428.isLt; have := v430.isLt
  generalize v341.toNat = n341 at *
  generalize v428.toNat = n428 at *
  generalize v430.toNat = n430 at *
  omega

theorem smm_v_PN3L1 {v401 v432 v434 : Word}
    (t432 : v432.toNat = v401.toNat * 9640146 % 2 ^ 32)
    (t434 : v434.toNat = v401.toNat * 9640146 / 2 ^ 32) :
    v432.toNat + 2 ^ 32 * v434.toNat = v401.toNat * 9640146 := by
  have := v401.isLt; have := v432.isLt; have := v434.isLt
  generalize v401.toNat = n401 at *
  generalize v432.toNat = n432 at *
  generalize v434.toNat = n434 at *
  omega

theorem smm_v_S4 {v122 v139 v410 v412 v416 v420 v423 v425 v426 v427 v428 v429 v430 v432 v433 v434 v437 v439 v440 v441 v443 v444 v445 v446 v447 v448 v449 v450 v464 v467 v468 v472 : Word}
    (t425 : v425.toNat = (v412.toNat + v139.toNat) % 2 ^ 32)
    (t426 : v423.toNat + 2 ^ 32 * v426.toNat = v410.toNat + v122.toNat)
    (t427 : v427.toNat = (v426.toNat + v425.toNat) % 2 ^ 32)
    (t429 : v429.toNat = (v416.toNat + v427.toNat) % 2 ^ 32)
    (t437 : v433.toNat + 2 ^ 32 * v437.toNat = v420.toNat + v423.toNat)
    (t440 : v440.toNat = (v429.toNat + v437.toNat) % 2 ^ 32)
    (t443 : v443.toNat = (v440.toNat + v430.toNat) % 2 ^ 32)
    (t444 : v441.toNat + 2 ^ 32 * v444.toNat = v428.toNat + v433.toNat)
    (t445 : v445.toNat = (v443.toNat + v444.toNat) % 2 ^ 32)
    (t447 : v447.toNat = (v434.toNat + v445.toNat) % 2 ^ 32)
    (t448 : v446.toNat + 2 ^ 32 * v448.toNat = v432.toNat + v441.toNat)
    (t449 : v449.toNat = (v447.toNat + v448.toNat) % 2 ^ 32)
    (t467 : v467.toNat = (v449.toNat + v464.toNat) % 2 ^ 32)
    (t468 : v450.toNat + 2 ^ 32 * v468.toNat = v439.toNat + v446.toNat)
    (t472 : v472.toNat = (v467.toNat + v468.toNat) % 2 ^ 32) :
    v450.toNat + 2 ^ 32 * v472.toNat = ((v439.toNat + 2 ^ 32 * v464.toNat) + (v122.toNat + 2 ^ 32 * v139.toNat) + (v410.toNat + 2 ^ 32 * v412.toNat) + (v420.toNat + 2 ^ 32 * v416.toNat) + (v428.toNat + 2 ^ 32 * v430.toNat) + (v432.toNat + 2 ^ 32 * v434.toNat)) % 2 ^ 64 := by
  obtain ⟨q425, eq425⟩ := mod_q t425; clear t425
  obtain ⟨q427, eq427⟩ := mod_q t427; clear t427
  obtain ⟨q429, eq429⟩ := mod_q t429; clear t429
  obtain ⟨q440, eq440⟩ := mod_q t440; clear t440
  obtain ⟨q443, eq443⟩ := mod_q t443; clear t443
  obtain ⟨q445, eq445⟩ := mod_q t445; clear t445
  obtain ⟨q447, eq447⟩ := mod_q t447; clear t447
  obtain ⟨q449, eq449⟩ := mod_q t449; clear t449
  obtain ⟨q467, eq467⟩ := mod_q t467; clear t467
  obtain ⟨q472, eq472⟩ := mod_q t472; clear t472
  have key : v450.toNat + 2 ^ 32 * v472.toNat + 2 ^ 64 * (q425 + q427 + q429 + q440 + q443 + q445 + q447 + q449 + q467 + q472) = ((v439.toNat + 2 ^ 32 * v464.toNat) + (v122.toNat + 2 ^ 32 * v139.toNat) + (v410.toNat + 2 ^ 32 * v412.toNat) + (v420.toNat + 2 ^ 32 * v416.toNat) + (v428.toNat + 2 ^ 32 * v430.toNat) + (v432.toNat + 2 ^ 32 * v434.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v122.toNat = n122 at *
    generalize v139.toNat = n139 at *
    generalize v410.toNat = n410 at *
    generalize v412.toNat = n412 at *
    generalize v416.toNat = n416 at *
    generalize v420.toNat = n420 at *
    generalize v423.toNat = n423 at *
    generalize v425.toNat = n425 at *
    generalize v426.toNat = n426 at *
    generalize v427.toNat = n427 at *
    generalize v428.toNat = n428 at *
    generalize v429.toNat = n429 at *
    generalize v430.toNat = n430 at *
    generalize v432.toNat = n432 at *
    generalize v433.toNat = n433 at *
    generalize v434.toNat = n434 at *
    generalize v437.toNat = n437 at *
    generalize v439.toNat = n439 at *
    generalize v440.toNat = n440 at *
    generalize v441.toNat = n441 at *
    generalize v443.toNat = n443 at *
    generalize v444.toNat = n444 at *
    generalize v445.toNat = n445 at *
    generalize v446.toNat = n446 at *
    generalize v447.toNat = n447 at *
    generalize v448.toNat = n448 at *
    generalize v449.toNat = n449 at *
    generalize v450.toNat = n450 at *
    generalize v464.toNat = n464 at *
    generalize v467.toNat = n467 at *
    generalize v468.toNat = n468 at *
    generalize v472.toNat = n472 at *
    omega
  exact smm_key key (smm_lt v450 v472)

theorem smm_v_N4 {v450 v455 v470 v472 : Word}
    (t455 : v455.toNat = v450.toNat * 307527195 % 2 ^ 32)
    (t470 : v470.toNat = v455.toNat % 2 ^ 29) :
    v470.toNat = ((v450.toNat + 2 ^ 32 * v472.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v450.isLt; have := v455.isLt; have := v470.isLt; have := v472.isLt
  generalize v450.toNat = n450 at *
  generalize v455.toNat = n455 at *
  generalize v470.toNat = n470 at *
  generalize v472.toNat = n472 at *
  omega

theorem smm_v_PN4L0 {v470 v473 v475 : Word}
    (t473 : v473.toNat = v470.toNat * 485872621 / 2 ^ 32)
    (t475 : v475.toNat = v470.toNat * 485872621 % 2 ^ 32) :
    v475.toNat + 2 ^ 32 * v473.toNat = v470.toNat * 485872621 := by
  have := v470.isLt; have := v473.isLt; have := v475.isLt
  generalize v470.toNat = n470 at *
  generalize v473.toNat = n473 at *
  generalize v475.toNat = n475 at *
  omega

theorem smm_v_T4 {v450 v472 v473 v475 v486 v488 v490 v492 : Word}
    (t486 : v486.toNat = (v473.toNat + v472.toNat) % 2 ^ 32)
    (t490 : v488.toNat + 2 ^ 32 * v490.toNat = v450.toNat + v475.toNat)
    (t492 : v492.toNat = (v486.toNat + v490.toNat) % 2 ^ 32) :
    v488.toNat + 2 ^ 32 * v492.toNat = ((v450.toNat + 2 ^ 32 * v472.toNat) + (v475.toNat + 2 ^ 32 * v473.toNat)) % 2 ^ 64 := by
  obtain ⟨q486, eq486⟩ := mod_q t486; clear t486
  obtain ⟨q492, eq492⟩ := mod_q t492; clear t492
  have key : v488.toNat + 2 ^ 32 * v492.toNat + 2 ^ 64 * (q486 + q492) = ((v450.toNat + 2 ^ 32 * v472.toNat) + (v475.toNat + 2 ^ 32 * v473.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v450.toNat = n450 at *
    generalize v472.toNat = n472 at *
    generalize v473.toNat = n473 at *
    generalize v475.toNat = n475 at *
    generalize v486.toNat = n486 at *
    generalize v488.toNat = n488 at *
    generalize v490.toNat = n490 at *
    generalize v492.toNat = n492 at *
    omega
  exact smm_key key (smm_lt v488 v492)

theorem smm_v_C4 {v488 v492 v494 v497 v498 v511 : Word}
    (t494 : v494.toNat = v488.toNat / 2 ^ 29)
    (t497 : v497.toNat = v492.toNat * 2 ^ 3 % 2 ^ 32)
    (t498 : v498.toNat = v494.toNat + v497.toNat)
    (t511 : v511.toNat = v492.toNat / 2 ^ 29) :
    v498.toNat + 2 ^ 32 * v511.toNat = (v488.toNat + 2 ^ 32 * v492.toNat) / 2 ^ 29 := by
  have := v488.isLt; have := v492.isLt; have := v494.isLt; have := v497.isLt; have := v498.isLt; have := v511.isLt
  generalize v488.toNat = n488 at *
  generalize v492.toNat = n492 at *
  generalize v494.toNat = n494 at *
  generalize v497.toNat = n497 at *
  generalize v498.toNat = n498 at *
  generalize v511.toNat = n511 at *
  omega

theorem smm_v_PN1L4 {v285 v463 v465 : Word}
    (t463 : v463.toNat = v285.toNat * 333 % 2 ^ 32)
    (t465 : v465.toNat = v285.toNat * 333 / 2 ^ 32) :
    v463.toNat + 2 ^ 32 * v465.toNat = v285.toNat * 333 := by
  have := v285.isLt; have := v463.isLt; have := v465.isLt
  generalize v285.toNat = n285 at *
  generalize v463.toNat = n463 at *
  generalize v465.toNat = n465 at *
  omega

theorem smm_v_PN2L3 {v341 v469 v471 : Word}
    (t469 : v469.toNat = v341.toNat * 502512965 % 2 ^ 32)
    (t471 : v471.toNat = v341.toNat * 502512965 / 2 ^ 32) :
    v469.toNat + 2 ^ 32 * v471.toNat = v341.toNat * 502512965 := by
  have := v341.isLt; have := v469.isLt; have := v471.isLt
  generalize v341.toNat = n341 at *
  generalize v469.toNat = n469 at *
  generalize v471.toNat = n471 at *
  omega

theorem smm_v_PN3L2 {v401 v481 v483 : Word}
    (t481 : v481.toNat = v401.toNat * 501691798 / 2 ^ 32)
    (t483 : v483.toNat = v401.toNat * 501691798 % 2 ^ 32) :
    v483.toNat + 2 ^ 32 * v481.toNat = v401.toNat * 501691798 := by
  have := v401.isLt; have := v481.isLt; have := v483.isLt
  generalize v401.toNat = n401 at *
  generalize v481.toNat = n481 at *
  generalize v483.toNat = n483 at *
  omega

theorem smm_v_PN4L1 {v470 v489 v491 : Word}
    (t489 : v489.toNat = v470.toNat * 9640146 / 2 ^ 32)
    (t491 : v491.toNat = v470.toNat * 9640146 % 2 ^ 32) :
    v491.toNat + 2 ^ 32 * v489.toNat = v470.toNat * 9640146 := by
  have := v470.isLt; have := v489.isLt; have := v491.isLt
  generalize v470.toNat = n470 at *
  generalize v489.toNat = n489 at *
  generalize v491.toNat = n491 at *
  omega

theorem smm_v_S5 {v459 v463 v465 v466 v469 v471 v474 v476 v477 v478 v481 v482 v483 v484 v485 v487 v489 v491 v493 v495 v496 v498 v499 v500 v502 v504 v505 v510 v511 v512 v513 v517 : Word}
    (t476 : v476.toNat = (v466.toNat + v465.toNat) % 2 ^ 32)
    (t477 : v474.toNat + 2 ^ 32 * v477.toNat = v463.toNat + v459.toNat)
    (t478 : v478.toNat = (v476.toNat + v477.toNat) % 2 ^ 32)
    (t484 : v484.toNat = (v478.toNat + v471.toNat) % 2 ^ 32)
    (t485 : v482.toNat + 2 ^ 32 * v485.toNat = v469.toNat + v474.toNat)
    (t487 : v487.toNat = (v484.toNat + v485.toNat) % 2 ^ 32)
    (t493 : v493.toNat = (v487.toNat + v481.toNat) % 2 ^ 32)
    (t496 : v495.toNat + 2 ^ 32 * v496.toNat = v483.toNat + v482.toNat)
    (t499 : v499.toNat = (v493.toNat + v496.toNat) % 2 ^ 32)
    (t500 : v500.toNat = (v499.toNat + v489.toNat) % 2 ^ 32)
    (t504 : v502.toNat + 2 ^ 32 * v504.toNat = v491.toNat + v495.toNat)
    (t510 : v510.toNat = (v500.toNat + v504.toNat) % 2 ^ 32)
    (t512 : v512.toNat = (v510.toNat + v511.toNat) % 2 ^ 32)
    (t513 : v505.toNat + 2 ^ 32 * v513.toNat = v502.toNat + v498.toNat)
    (t517 : v517.toNat = (v512.toNat + v513.toNat) % 2 ^ 32) :
    v505.toNat + 2 ^ 32 * v517.toNat = ((v498.toNat + 2 ^ 32 * v511.toNat) + (v459.toNat + 2 ^ 32 * v466.toNat) + (v463.toNat + 2 ^ 32 * v465.toNat) + (v469.toNat + 2 ^ 32 * v471.toNat) + (v483.toNat + 2 ^ 32 * v481.toNat) + (v491.toNat + 2 ^ 32 * v489.toNat)) % 2 ^ 64 := by
  obtain ⟨q476, eq476⟩ := mod_q t476; clear t476
  obtain ⟨q478, eq478⟩ := mod_q t478; clear t478
  obtain ⟨q484, eq484⟩ := mod_q t484; clear t484
  obtain ⟨q487, eq487⟩ := mod_q t487; clear t487
  obtain ⟨q493, eq493⟩ := mod_q t493; clear t493
  obtain ⟨q499, eq499⟩ := mod_q t499; clear t499
  obtain ⟨q500, eq500⟩ := mod_q t500; clear t500
  obtain ⟨q510, eq510⟩ := mod_q t510; clear t510
  obtain ⟨q512, eq512⟩ := mod_q t512; clear t512
  obtain ⟨q517, eq517⟩ := mod_q t517; clear t517
  have key : v505.toNat + 2 ^ 32 * v517.toNat + 2 ^ 64 * (q476 + q478 + q484 + q487 + q493 + q499 + q500 + q510 + q512 + q517) = ((v498.toNat + 2 ^ 32 * v511.toNat) + (v459.toNat + 2 ^ 32 * v466.toNat) + (v463.toNat + 2 ^ 32 * v465.toNat) + (v469.toNat + 2 ^ 32 * v471.toNat) + (v483.toNat + 2 ^ 32 * v481.toNat) + (v491.toNat + 2 ^ 32 * v489.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v459.toNat = n459 at *
    generalize v463.toNat = n463 at *
    generalize v465.toNat = n465 at *
    generalize v466.toNat = n466 at *
    generalize v469.toNat = n469 at *
    generalize v471.toNat = n471 at *
    generalize v474.toNat = n474 at *
    generalize v476.toNat = n476 at *
    generalize v477.toNat = n477 at *
    generalize v478.toNat = n478 at *
    generalize v481.toNat = n481 at *
    generalize v482.toNat = n482 at *
    generalize v483.toNat = n483 at *
    generalize v484.toNat = n484 at *
    generalize v485.toNat = n485 at *
    generalize v487.toNat = n487 at *
    generalize v489.toNat = n489 at *
    generalize v491.toNat = n491 at *
    generalize v493.toNat = n493 at *
    generalize v495.toNat = n495 at *
    generalize v496.toNat = n496 at *
    generalize v498.toNat = n498 at *
    generalize v499.toNat = n499 at *
    generalize v500.toNat = n500 at *
    generalize v502.toNat = n502 at *
    generalize v504.toNat = n504 at *
    generalize v505.toNat = n505 at *
    generalize v510.toNat = n510 at *
    generalize v511.toNat = n511 at *
    generalize v512.toNat = n512 at *
    generalize v513.toNat = n513 at *
    generalize v517.toNat = n517 at *
    omega
  exact smm_key key (smm_lt v505 v517)

theorem smm_v_N5 {v505 v507 v517 v523 : Word}
    (t507 : v507.toNat = v505.toNat * 307527195 % 2 ^ 32)
    (t523 : v523.toNat = v507.toNat % 2 ^ 29) :
    v523.toNat = ((v505.toNat + 2 ^ 32 * v517.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v505.isLt; have := v507.isLt; have := v517.isLt; have := v523.isLt
  generalize v505.toNat = n505 at *
  generalize v507.toNat = n507 at *
  generalize v517.toNat = n517 at *
  generalize v523.toNat = n523 at *
  omega

theorem smm_v_PN5L0 {v523 v525 v529 : Word}
    (t525 : v525.toNat = v523.toNat * 485872621 / 2 ^ 32)
    (t529 : v529.toNat = v523.toNat * 485872621 % 2 ^ 32) :
    v529.toNat + 2 ^ 32 * v525.toNat = v523.toNat * 485872621 := by
  have := v523.isLt; have := v525.isLt; have := v529.isLt
  generalize v523.toNat = n523 at *
  generalize v525.toNat = n525 at *
  generalize v529.toNat = n529 at *
  omega

theorem smm_v_T5 {v505 v517 v525 v529 v543 v545 v547 v549 : Word}
    (t543 : v543.toNat = (v517.toNat + v525.toNat) % 2 ^ 32)
    (t547 : v545.toNat + 2 ^ 32 * v547.toNat = v529.toNat + v505.toNat)
    (t549 : v549.toNat = (v543.toNat + v547.toNat) % 2 ^ 32) :
    v545.toNat + 2 ^ 32 * v549.toNat = ((v505.toNat + 2 ^ 32 * v517.toNat) + (v529.toNat + 2 ^ 32 * v525.toNat)) % 2 ^ 64 := by
  obtain ⟨q543, eq543⟩ := mod_q t543; clear t543
  obtain ⟨q549, eq549⟩ := mod_q t549; clear t549
  have key : v545.toNat + 2 ^ 32 * v549.toNat + 2 ^ 64 * (q543 + q549) = ((v505.toNat + 2 ^ 32 * v517.toNat) + (v529.toNat + 2 ^ 32 * v525.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v505.toNat = n505 at *
    generalize v517.toNat = n517 at *
    generalize v525.toNat = n525 at *
    generalize v529.toNat = n529 at *
    generalize v543.toNat = n543 at *
    generalize v545.toNat = n545 at *
    generalize v547.toNat = n547 at *
    generalize v549.toNat = n549 at *
    omega
  exact smm_key key (smm_lt v545 v549)

theorem smm_v_C5 {v545 v549 v551 v552 v553 v670 : Word}
    (t551 : v551.toNat = v545.toNat / 2 ^ 29)
    (t552 : v552.toNat = v549.toNat * 2 ^ 3 % 2 ^ 32)
    (t553 : v553.toNat = v551.toNat + v552.toNat)
    (t670 : v670.toNat = v549.toNat / 2 ^ 29) :
    v553.toNat + 2 ^ 32 * v670.toNat = (v545.toNat + 2 ^ 32 * v549.toNat) / 2 ^ 29 := by
  have := v545.isLt; have := v549.isLt; have := v551.isLt; have := v552.isLt; have := v553.isLt; have := v670.isLt
  generalize v545.toNat = n545 at *
  generalize v549.toNat = n549 at *
  generalize v551.toNat = n551 at *
  generalize v552.toNat = n552 at *
  generalize v553.toNat = n553 at *
  generalize v670.toNat = n670 at *
  omega

theorem smm_v_PN2L4 {v341 v528 v530 : Word}
    (t528 : v528.toNat = v341.toNat * 333 / 2 ^ 32)
    (t530 : v530.toNat = v341.toNat * 333 % 2 ^ 32) :
    v530.toNat + 2 ^ 32 * v528.toNat = v341.toNat * 333 := by
  have := v341.isLt; have := v528.isLt; have := v530.isLt
  generalize v341.toNat = n341 at *
  generalize v528.toNat = n528 at *
  generalize v530.toNat = n530 at *
  omega

theorem smm_v_PN3L3 {v401 v542 v603 : Word}
    (t542 : v542.toNat = v401.toNat * 502512965 / 2 ^ 32)
    (t603 : v603.toNat = v401.toNat * 502512965 % 2 ^ 32) :
    v603.toNat + 2 ^ 32 * v542.toNat = v401.toNat * 502512965 := by
  have := v401.isLt; have := v542.isLt; have := v603.isLt
  generalize v401.toNat = n401 at *
  generalize v542.toNat = n542 at *
  generalize v603.toNat = n603 at *
  omega

end C3.RV32
