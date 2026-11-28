import C3BootProofs.Proofs.EdvReduceFacts

/-! # The inlined `Scalar::reduce`'s values, part 2

Each lemma proves one value the code holds in words from its instructions' facts. `scripts/gen-ev-reduce.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option maxHeartbeats 10000000 in
theorem evr_v_PN2L0 {v279 v281 v283 : Word}
    (t281 : v281.toNat = v279.toNat * 485872621 % 2 ^ 32)
    (t283 : v283.toNat = v279.toNat * 485872621 / 2 ^ 32) :
    v281.toNat + 2 ^ 32 * v283.toNat = v279.toNat * 485872621 := by
  have := v279.isLt; have := v281.isLt; have := v283.isLt
  generalize v279.toNat = n279 at *
  generalize v281.toNat = n281 at *
  generalize v283.toNat = n283 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_T2 {v262 v281 v283 v293 v294 v295 v296 v299 : Word}
    (t295 : v295.toNat = (v293.toNat + v283.toNat) % 2 ^ 32)
    (t296 : v294.toNat + 2 ^ 32 * v296.toNat = v262.toNat + v281.toNat)
    (t299 : v299.toNat = (v295.toNat + v296.toNat) % 2 ^ 32) :
    v294.toNat + 2 ^ 32 * v299.toNat = ((v262.toNat + 2 ^ 32 * v293.toNat) + (v281.toNat + 2 ^ 32 * v283.toNat)) % 2 ^ 64 := by
  obtain ⟨q295, eq295⟩ := mod_q t295; clear t295
  obtain ⟨q299, eq299⟩ := mod_q t299; clear t299
  have key : v294.toNat + 2 ^ 32 * v299.toNat + 2 ^ 64 * (q295 + q299) = ((v262.toNat + 2 ^ 32 * v293.toNat) + (v281.toNat + 2 ^ 32 * v283.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v262.toNat = n262 at *
    generalize v281.toNat = n281 at *
    generalize v283.toNat = n283 at *
    generalize v293.toNat = n293 at *
    generalize v294.toNat = n294 at *
    generalize v295.toNat = n295 at *
    generalize v296.toNat = n296 at *
    generalize v299.toNat = n299 at *
    omega
  exact smm_key key (smm_lt v294 v299)

set_option maxHeartbeats 10000000 in
theorem evr_v_C2 {v294 v299 v300 v303 v304 v363 : Word}
    (t300 : v300.toNat = v294.toNat / 2 ^ 29)
    (t303 : v303.toNat = v299.toNat * 2 ^ 3 % 2 ^ 32)
    (t304 : v304.toNat = v300.toNat + v303.toNat)
    (t363 : v363.toNat = v299.toNat / 2 ^ 29) :
    v304.toNat + 2 ^ 32 * v363.toNat = (v294.toNat + 2 ^ 32 * v299.toNat) / 2 ^ 29 := by
  have := v294.isLt; have := v299.isLt; have := v300.isLt; have := v303.isLt; have := v304.isLt; have := v363.isLt
  generalize v294.toNat = n294 at *
  generalize v299.toNat = n299 at *
  generalize v300.toNat = n300 at *
  generalize v303.toNat = n303 at *
  generalize v304.toNat = n304 at *
  generalize v363.toNat = n363 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN0L3 {v151 v305 v328 : Word}
    (t305 : v305.toNat = v151.toNat * 502512965 % 2 ^ 32)
    (t328 : v328.toNat = v151.toNat * 502512965 / 2 ^ 32) :
    v305.toNat + 2 ^ 32 * v328.toNat = v151.toNat * 502512965 := by
  have := v151.isLt; have := v305.isLt; have := v328.isLt
  generalize v151.toNat = n151 at *
  generalize v305.toNat = n305 at *
  generalize v328.toNat = n328 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN1L2 {v219 v307 v333 : Word}
    (t307 : v307.toNat = v219.toNat * 501691798 % 2 ^ 32)
    (t333 : v333.toNat = v219.toNat * 501691798 / 2 ^ 32) :
    v307.toNat + 2 ^ 32 * v333.toNat = v219.toNat * 501691798 := by
  have := v219.isLt; have := v307.isLt; have := v333.isLt
  generalize v219.toNat = n219 at *
  generalize v307.toNat = n307 at *
  generalize v333.toNat = n333 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN2L1 {v279 v315 v347 : Word}
    (t315 : v315.toNat = v279.toNat * 9640146 % 2 ^ 32)
    (t347 : v347.toNat = v279.toNat * 9640146 / 2 ^ 32) :
    v315.toNat + 2 ^ 32 * v347.toNat = v279.toNat * 9640146 := by
  have := v279.isLt; have := v315.isLt; have := v347.isLt
  generalize v279.toNat = n279 at *
  generalize v315.toNat = n315 at *
  generalize v347.toNat = n347 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S3 {v111 v122 v304 v305 v307 v315 v324 v325 v328 v330 v332 v333 v345 v346 v347 v350 v351 v355 v359 v360 v361 v362 v363 v364 v365 v366 : Word}
    (t345 : v345.toNat = (v328.toNat + v122.toNat) % 2 ^ 32)
    (t346 : v324.toNat + 2 ^ 32 * v346.toNat = v111.toNat + v305.toNat)
    (t350 : v350.toNat = (v346.toNat + v345.toNat) % 2 ^ 32)
    (t351 : v351.toNat = (v333.toNat + v350.toNat) % 2 ^ 32)
    (t355 : v325.toNat + 2 ^ 32 * v355.toNat = v324.toNat + v307.toNat)
    (t359 : v359.toNat = (v351.toNat + v355.toNat) % 2 ^ 32)
    (t360 : v360.toNat = (v359.toNat + v347.toNat) % 2 ^ 32)
    (t361 : v330.toNat + 2 ^ 32 * v361.toNat = v315.toNat + v325.toNat)
    (t362 : v362.toNat = (v361.toNat + v360.toNat) % 2 ^ 32)
    (t364 : v364.toNat = (v362.toNat + v363.toNat) % 2 ^ 32)
    (t365 : v332.toNat + 2 ^ 32 * v365.toNat = v304.toNat + v330.toNat)
    (t366 : v366.toNat = (v364.toNat + v365.toNat) % 2 ^ 32) :
    v332.toNat + 2 ^ 32 * v366.toNat = ((v304.toNat + 2 ^ 32 * v363.toNat) + (v111.toNat + 2 ^ 32 * v122.toNat) + (v305.toNat + 2 ^ 32 * v328.toNat) + (v307.toNat + 2 ^ 32 * v333.toNat) + (v315.toNat + 2 ^ 32 * v347.toNat)) % 2 ^ 64 := by
  obtain ⟨q345, eq345⟩ := mod_q t345; clear t345
  obtain ⟨q350, eq350⟩ := mod_q t350; clear t350
  obtain ⟨q351, eq351⟩ := mod_q t351; clear t351
  obtain ⟨q359, eq359⟩ := mod_q t359; clear t359
  obtain ⟨q360, eq360⟩ := mod_q t360; clear t360
  obtain ⟨q362, eq362⟩ := mod_q t362; clear t362
  obtain ⟨q364, eq364⟩ := mod_q t364; clear t364
  obtain ⟨q366, eq366⟩ := mod_q t366; clear t366
  have key : v332.toNat + 2 ^ 32 * v366.toNat + 2 ^ 64 * (q345 + q350 + q351 + q359 + q360 + q362 + q364 + q366) = ((v304.toNat + 2 ^ 32 * v363.toNat) + (v111.toNat + 2 ^ 32 * v122.toNat) + (v305.toNat + 2 ^ 32 * v328.toNat) + (v307.toNat + 2 ^ 32 * v333.toNat) + (v315.toNat + 2 ^ 32 * v347.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v111.toNat = n111 at *
    generalize v122.toNat = n122 at *
    generalize v304.toNat = n304 at *
    generalize v305.toNat = n305 at *
    generalize v307.toNat = n307 at *
    generalize v315.toNat = n315 at *
    generalize v324.toNat = n324 at *
    generalize v325.toNat = n325 at *
    generalize v328.toNat = n328 at *
    generalize v330.toNat = n330 at *
    generalize v332.toNat = n332 at *
    generalize v333.toNat = n333 at *
    generalize v345.toNat = n345 at *
    generalize v346.toNat = n346 at *
    generalize v347.toNat = n347 at *
    generalize v350.toNat = n350 at *
    generalize v351.toNat = n351 at *
    generalize v355.toNat = n355 at *
    generalize v359.toNat = n359 at *
    generalize v360.toNat = n360 at *
    generalize v361.toNat = n361 at *
    generalize v362.toNat = n362 at *
    generalize v363.toNat = n363 at *
    generalize v364.toNat = n364 at *
    generalize v365.toNat = n365 at *
    generalize v366.toNat = n366 at *
    omega
  exact smm_key key (smm_lt v332 v366)

set_option maxHeartbeats 10000000 in
theorem evr_v_N3 {v332 v335 v352 v366 : Word}
    (t335 : v335.toNat = v332.toNat * 307527195 % 2 ^ 32)
    (t352 : v352.toNat = v335.toNat % 2 ^ 29) :
    v352.toNat = ((v332.toNat + 2 ^ 32 * v366.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v332.isLt; have := v335.isLt; have := v352.isLt; have := v366.isLt
  generalize v332.toNat = n332 at *
  generalize v335.toNat = n335 at *
  generalize v352.toNat = n352 at *
  generalize v366.toNat = n366 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN3L0 {v352 v354 v356 : Word}
    (t354 : v354.toNat = v352.toNat * 485872621 % 2 ^ 32)
    (t356 : v356.toNat = v352.toNat * 485872621 / 2 ^ 32) :
    v354.toNat + 2 ^ 32 * v356.toNat = v352.toNat * 485872621 := by
  have := v352.isLt; have := v354.isLt; have := v356.isLt
  generalize v352.toNat = n352 at *
  generalize v354.toNat = n354 at *
  generalize v356.toNat = n356 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_T3 {v332 v354 v356 v366 v367 v368 v369 v379 : Word}
    (t368 : v368.toNat = (v366.toNat + v356.toNat) % 2 ^ 32)
    (t369 : v367.toNat + 2 ^ 32 * v369.toNat = v332.toNat + v354.toNat)
    (t379 : v379.toNat = (v368.toNat + v369.toNat) % 2 ^ 32) :
    v367.toNat + 2 ^ 32 * v379.toNat = ((v332.toNat + 2 ^ 32 * v366.toNat) + (v354.toNat + 2 ^ 32 * v356.toNat)) % 2 ^ 64 := by
  obtain ⟨q368, eq368⟩ := mod_q t368; clear t368
  obtain ⟨q379, eq379⟩ := mod_q t379; clear t379
  have key : v367.toNat + 2 ^ 32 * v379.toNat + 2 ^ 64 * (q368 + q379) = ((v332.toNat + 2 ^ 32 * v366.toNat) + (v354.toNat + 2 ^ 32 * v356.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v332.toNat = n332 at *
    generalize v354.toNat = n354 at *
    generalize v356.toNat = n356 at *
    generalize v366.toNat = n366 at *
    generalize v367.toNat = n367 at *
    generalize v368.toNat = n368 at *
    generalize v369.toNat = n369 at *
    generalize v379.toNat = n379 at *
    omega
  exact smm_key key (smm_lt v367 v379)

set_option maxHeartbeats 10000000 in
theorem evr_v_C3 {v367 v379 v380 v385 v389 v417 : Word}
    (t380 : v380.toNat = v367.toNat / 2 ^ 29)
    (t385 : v385.toNat = v379.toNat * 2 ^ 3 % 2 ^ 32)
    (t389 : v389.toNat = v380.toNat + v385.toNat)
    (t417 : v417.toNat = v379.toNat / 2 ^ 29) :
    v389.toNat + 2 ^ 32 * v417.toNat = (v367.toNat + 2 ^ 32 * v379.toNat) / 2 ^ 29 := by
  have := v367.isLt; have := v379.isLt; have := v380.isLt; have := v385.isLt; have := v389.isLt; have := v417.isLt
  generalize v367.toNat = n367 at *
  generalize v379.toNat = n379 at *
  generalize v380.toNat = n380 at *
  generalize v385.toNat = n385 at *
  generalize v389.toNat = n389 at *
  generalize v417.toNat = n417 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN0L4 {v151 v375 v376 : Word}
    (t375 : v375.toNat = v151.toNat * 333 % 2 ^ 32)
    (t376 : v376.toNat = v151.toNat * 333 / 2 ^ 32) :
    v375.toNat + 2 ^ 32 * v376.toNat = v151.toNat * 333 := by
  have := v151.isLt; have := v375.isLt; have := v376.isLt
  generalize v151.toNat = n151 at *
  generalize v375.toNat = n375 at *
  generalize v376.toNat = n376 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN1L3 {v219 v381 v382 : Word}
    (t381 : v381.toNat = v219.toNat * 502512965 % 2 ^ 32)
    (t382 : v382.toNat = v219.toNat * 502512965 / 2 ^ 32) :
    v381.toNat + 2 ^ 32 * v382.toNat = v219.toNat * 502512965 := by
  have := v219.isLt; have := v381.isLt; have := v382.isLt
  generalize v219.toNat = n219 at *
  generalize v381.toNat = n381 at *
  generalize v382.toNat = n382 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN2L2 {v279 v384 v395 : Word}
    (t384 : v384.toNat = v279.toNat * 501691798 % 2 ^ 32)
    (t395 : v395.toNat = v279.toNat * 501691798 / 2 ^ 32) :
    v384.toNat + 2 ^ 32 * v395.toNat = v279.toNat * 501691798 := by
  have := v279.isLt; have := v384.isLt; have := v395.isLt
  generalize v279.toNat = n279 at *
  generalize v384.toNat = n384 at *
  generalize v395.toNat = n395 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN3L1 {v352 v386 v401 : Word}
    (t386 : v386.toNat = v352.toNat * 9640146 % 2 ^ 32)
    (t401 : v401.toNat = v352.toNat * 9640146 / 2 ^ 32) :
    v386.toNat + 2 ^ 32 * v401.toNat = v352.toNat * 9640146 := by
  have := v352.isLt; have := v386.isLt; have := v401.isLt
  generalize v352.toNat = n352 at *
  generalize v386.toNat = n386 at *
  generalize v401.toNat = n401 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S4 {v116 v124 v375 v376 v381 v382 v384 v386 v389 v391 v393 v394 v395 v396 v397 v398 v399 v400 v401 v402 v403 v404 v407 v410 v411 v413 v414 v415 v417 v420 v422 v425 : Word}
    (t391 : v391.toNat = (v376.toNat + v124.toNat) % 2 ^ 32)
    (t394 : v393.toNat + 2 ^ 32 * v394.toNat = v116.toNat + v375.toNat)
    (t396 : v396.toNat = (v394.toNat + v391.toNat) % 2 ^ 32)
    (t398 : v398.toNat = (v396.toNat + v382.toNat) % 2 ^ 32)
    (t402 : v397.toNat + 2 ^ 32 * v402.toNat = v381.toNat + v393.toNat)
    (t404 : v404.toNat = (v402.toNat + v398.toNat) % 2 ^ 32)
    (t407 : v407.toNat = (v404.toNat + v395.toNat) % 2 ^ 32)
    (t410 : v399.toNat + 2 ^ 32 * v410.toNat = v384.toNat + v397.toNat)
    (t411 : v411.toNat = (v407.toNat + v410.toNat) % 2 ^ 32)
    (t413 : v413.toNat = (v411.toNat + v401.toNat) % 2 ^ 32)
    (t414 : v400.toNat + 2 ^ 32 * v414.toNat = v386.toNat + v399.toNat)
    (t415 : v415.toNat = (v413.toNat + v414.toNat) % 2 ^ 32)
    (t420 : v420.toNat = (v415.toNat + v417.toNat) % 2 ^ 32)
    (t422 : v403.toNat + 2 ^ 32 * v422.toNat = v389.toNat + v400.toNat)
    (t425 : v425.toNat = (v420.toNat + v422.toNat) % 2 ^ 32) :
    v403.toNat + 2 ^ 32 * v425.toNat = ((v389.toNat + 2 ^ 32 * v417.toNat) + (v116.toNat + 2 ^ 32 * v124.toNat) + (v375.toNat + 2 ^ 32 * v376.toNat) + (v381.toNat + 2 ^ 32 * v382.toNat) + (v384.toNat + 2 ^ 32 * v395.toNat) + (v386.toNat + 2 ^ 32 * v401.toNat)) % 2 ^ 64 := by
  obtain ⟨q391, eq391⟩ := mod_q t391; clear t391
  obtain ⟨q396, eq396⟩ := mod_q t396; clear t396
  obtain ⟨q398, eq398⟩ := mod_q t398; clear t398
  obtain ⟨q404, eq404⟩ := mod_q t404; clear t404
  obtain ⟨q407, eq407⟩ := mod_q t407; clear t407
  obtain ⟨q411, eq411⟩ := mod_q t411; clear t411
  obtain ⟨q413, eq413⟩ := mod_q t413; clear t413
  obtain ⟨q415, eq415⟩ := mod_q t415; clear t415
  obtain ⟨q420, eq420⟩ := mod_q t420; clear t420
  obtain ⟨q425, eq425⟩ := mod_q t425; clear t425
  have key : v403.toNat + 2 ^ 32 * v425.toNat + 2 ^ 64 * (q391 + q396 + q398 + q404 + q407 + q411 + q413 + q415 + q420 + q425) = ((v389.toNat + 2 ^ 32 * v417.toNat) + (v116.toNat + 2 ^ 32 * v124.toNat) + (v375.toNat + 2 ^ 32 * v376.toNat) + (v381.toNat + 2 ^ 32 * v382.toNat) + (v384.toNat + 2 ^ 32 * v395.toNat) + (v386.toNat + 2 ^ 32 * v401.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v116.toNat = n116 at *
    generalize v124.toNat = n124 at *
    generalize v375.toNat = n375 at *
    generalize v376.toNat = n376 at *
    generalize v381.toNat = n381 at *
    generalize v382.toNat = n382 at *
    generalize v384.toNat = n384 at *
    generalize v386.toNat = n386 at *
    generalize v389.toNat = n389 at *
    generalize v391.toNat = n391 at *
    generalize v393.toNat = n393 at *
    generalize v394.toNat = n394 at *
    generalize v395.toNat = n395 at *
    generalize v396.toNat = n396 at *
    generalize v397.toNat = n397 at *
    generalize v398.toNat = n398 at *
    generalize v399.toNat = n399 at *
    generalize v400.toNat = n400 at *
    generalize v401.toNat = n401 at *
    generalize v402.toNat = n402 at *
    generalize v403.toNat = n403 at *
    generalize v404.toNat = n404 at *
    generalize v407.toNat = n407 at *
    generalize v410.toNat = n410 at *
    generalize v411.toNat = n411 at *
    generalize v413.toNat = n413 at *
    generalize v414.toNat = n414 at *
    generalize v415.toNat = n415 at *
    generalize v417.toNat = n417 at *
    generalize v420.toNat = n420 at *
    generalize v422.toNat = n422 at *
    generalize v425.toNat = n425 at *
    omega
  exact smm_key key (smm_lt v403 v425)

set_option maxHeartbeats 10000000 in
theorem evr_v_N4 {v403 v405 v419 v425 : Word}
    (t405 : v405.toNat = v403.toNat * 307527195 % 2 ^ 32)
    (t419 : v419.toNat = v405.toNat % 2 ^ 29) :
    v419.toNat = ((v403.toNat + 2 ^ 32 * v425.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v403.isLt; have := v405.isLt; have := v419.isLt; have := v425.isLt
  generalize v403.toNat = n403 at *
  generalize v405.toNat = n405 at *
  generalize v419.toNat = n419 at *
  generalize v425.toNat = n425 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN4L0 {v419 v421 v423 : Word}
    (t421 : v421.toNat = v419.toNat * 485872621 / 2 ^ 32)
    (t423 : v423.toNat = v419.toNat * 485872621 % 2 ^ 32) :
    v423.toNat + 2 ^ 32 * v421.toNat = v419.toNat * 485872621 := by
  have := v419.isLt; have := v421.isLt; have := v423.isLt
  generalize v419.toNat = n419 at *
  generalize v421.toNat = n421 at *
  generalize v423.toNat = n423 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_T4 {v403 v421 v423 v425 v436 v437 v439 v441 : Word}
    (t436 : v436.toNat = (v425.toNat + v421.toNat) % 2 ^ 32)
    (t439 : v437.toNat + 2 ^ 32 * v439.toNat = v403.toNat + v423.toNat)
    (t441 : v441.toNat = (v436.toNat + v439.toNat) % 2 ^ 32) :
    v437.toNat + 2 ^ 32 * v441.toNat = ((v403.toNat + 2 ^ 32 * v425.toNat) + (v423.toNat + 2 ^ 32 * v421.toNat)) % 2 ^ 64 := by
  obtain ⟨q436, eq436⟩ := mod_q t436; clear t436
  obtain ⟨q441, eq441⟩ := mod_q t441; clear t441
  have key : v437.toNat + 2 ^ 32 * v441.toNat + 2 ^ 64 * (q436 + q441) = ((v403.toNat + 2 ^ 32 * v425.toNat) + (v423.toNat + 2 ^ 32 * v421.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v403.toNat = n403 at *
    generalize v421.toNat = n421 at *
    generalize v423.toNat = n423 at *
    generalize v425.toNat = n425 at *
    generalize v436.toNat = n436 at *
    generalize v437.toNat = n437 at *
    generalize v439.toNat = n439 at *
    generalize v441.toNat = n441 at *
    omega
  exact smm_key key (smm_lt v437 v441)

set_option maxHeartbeats 10000000 in
theorem evr_v_C4 {v437 v441 v453 v457 v458 v489 : Word}
    (t453 : v453.toNat = v437.toNat / 2 ^ 29)
    (t457 : v457.toNat = v441.toNat * 2 ^ 3 % 2 ^ 32)
    (t458 : v458.toNat = v453.toNat + v457.toNat)
    (t489 : v489.toNat = v441.toNat / 2 ^ 29) :
    v458.toNat + 2 ^ 32 * v489.toNat = (v437.toNat + 2 ^ 32 * v441.toNat) / 2 ^ 29 := by
  have := v437.isLt; have := v441.isLt; have := v453.isLt; have := v457.isLt; have := v458.isLt; have := v489.isLt
  generalize v437.toNat = n437 at *
  generalize v441.toNat = n441 at *
  generalize v453.toNat = n453 at *
  generalize v457.toNat = n457 at *
  generalize v458.toNat = n458 at *
  generalize v489.toNat = n489 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN1L4 {v219 v429 v431 : Word}
    (t429 : v429.toNat = v219.toNat * 333 % 2 ^ 32)
    (t431 : v431.toNat = v219.toNat * 333 / 2 ^ 32) :
    v429.toNat + 2 ^ 32 * v431.toNat = v219.toNat * 333 := by
  have := v219.isLt; have := v429.isLt; have := v431.isLt
  generalize v219.toNat = n219 at *
  generalize v429.toNat = n429 at *
  generalize v431.toNat = n431 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN2L3 {v279 v438 v440 : Word}
    (t438 : v438.toNat = v279.toNat * 502512965 / 2 ^ 32)
    (t440 : v440.toNat = v279.toNat * 502512965 % 2 ^ 32) :
    v440.toNat + 2 ^ 32 * v438.toNat = v279.toNat * 502512965 := by
  have := v279.isLt; have := v438.isLt; have := v440.isLt
  generalize v279.toNat = n279 at *
  generalize v438.toNat = n438 at *
  generalize v440.toNat = n440 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN3L2 {v352 v445 v446 : Word}
    (t445 : v445.toNat = v352.toNat * 501691798 % 2 ^ 32)
    (t446 : v446.toNat = v352.toNat * 501691798 / 2 ^ 32) :
    v445.toNat + 2 ^ 32 * v446.toNat = v352.toNat * 501691798 := by
  have := v352.isLt; have := v445.isLt; have := v446.isLt
  generalize v352.toNat = n352 at *
  generalize v445.toNat = n445 at *
  generalize v446.toNat = n446 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN4L1 {v419 v451 v455 : Word}
    (t451 : v451.toNat = v419.toNat * 9640146 % 2 ^ 32)
    (t455 : v455.toNat = v419.toNat * 9640146 / 2 ^ 32) :
    v451.toNat + 2 ^ 32 * v455.toNat = v419.toNat * 9640146 := by
  have := v419.isLt; have := v451.isLt; have := v455.isLt
  generalize v419.toNat = n419 at *
  generalize v451.toNat = n451 at *
  generalize v455.toNat = n455 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S5 {v429 v430 v431 v435 v438 v440 v442 v443 v444 v445 v446 v449 v451 v452 v454 v455 v456 v458 v459 v460 v461 v462 v463 v464 v465 v466 v471 v472 v489 v494 v495 v498 : Word}
    (t443 : v443.toNat = (v435.toNat + v431.toNat) % 2 ^ 32)
    (t444 : v442.toNat + 2 ^ 32 * v444.toNat = v429.toNat + v430.toNat)
    (t449 : v449.toNat = (v443.toNat + v444.toNat) % 2 ^ 32)
    (t452 : v452.toNat = (v449.toNat + v438.toNat) % 2 ^ 32)
    (t456 : v454.toNat + 2 ^ 32 * v456.toNat = v440.toNat + v442.toNat)
    (t459 : v459.toNat = (v452.toNat + v456.toNat) % 2 ^ 32)
    (t460 : v460.toNat = (v446.toNat + v459.toNat) % 2 ^ 32)
    (t462 : v461.toNat + 2 ^ 32 * v462.toNat = v445.toNat + v454.toNat)
    (t464 : v464.toNat = (v460.toNat + v462.toNat) % 2 ^ 32)
    (t466 : v466.toNat = (v464.toNat + v455.toNat) % 2 ^ 32)
    (t471 : v463.toNat + 2 ^ 32 * v471.toNat = v451.toNat + v461.toNat)
    (t472 : v472.toNat = (v466.toNat + v471.toNat) % 2 ^ 32)
    (t494 : v494.toNat = (v472.toNat + v489.toNat) % 2 ^ 32)
    (t495 : v465.toNat + 2 ^ 32 * v495.toNat = v463.toNat + v458.toNat)
    (t498 : v498.toNat = (v494.toNat + v495.toNat) % 2 ^ 32) :
    v465.toNat + 2 ^ 32 * v498.toNat = ((v458.toNat + 2 ^ 32 * v489.toNat) + (v430.toNat + 2 ^ 32 * v435.toNat) + (v429.toNat + 2 ^ 32 * v431.toNat) + (v440.toNat + 2 ^ 32 * v438.toNat) + (v445.toNat + 2 ^ 32 * v446.toNat) + (v451.toNat + 2 ^ 32 * v455.toNat)) % 2 ^ 64 := by
  obtain ⟨q443, eq443⟩ := mod_q t443; clear t443
  obtain ⟨q449, eq449⟩ := mod_q t449; clear t449
  obtain ⟨q452, eq452⟩ := mod_q t452; clear t452
  obtain ⟨q459, eq459⟩ := mod_q t459; clear t459
  obtain ⟨q460, eq460⟩ := mod_q t460; clear t460
  obtain ⟨q464, eq464⟩ := mod_q t464; clear t464
  obtain ⟨q466, eq466⟩ := mod_q t466; clear t466
  obtain ⟨q472, eq472⟩ := mod_q t472; clear t472
  obtain ⟨q494, eq494⟩ := mod_q t494; clear t494
  obtain ⟨q498, eq498⟩ := mod_q t498; clear t498
  have key : v465.toNat + 2 ^ 32 * v498.toNat + 2 ^ 64 * (q443 + q449 + q452 + q459 + q460 + q464 + q466 + q472 + q494 + q498) = ((v458.toNat + 2 ^ 32 * v489.toNat) + (v430.toNat + 2 ^ 32 * v435.toNat) + (v429.toNat + 2 ^ 32 * v431.toNat) + (v440.toNat + 2 ^ 32 * v438.toNat) + (v445.toNat + 2 ^ 32 * v446.toNat) + (v451.toNat + 2 ^ 32 * v455.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v429.toNat = n429 at *
    generalize v430.toNat = n430 at *
    generalize v431.toNat = n431 at *
    generalize v435.toNat = n435 at *
    generalize v438.toNat = n438 at *
    generalize v440.toNat = n440 at *
    generalize v442.toNat = n442 at *
    generalize v443.toNat = n443 at *
    generalize v444.toNat = n444 at *
    generalize v445.toNat = n445 at *
    generalize v446.toNat = n446 at *
    generalize v449.toNat = n449 at *
    generalize v451.toNat = n451 at *
    generalize v452.toNat = n452 at *
    generalize v454.toNat = n454 at *
    generalize v455.toNat = n455 at *
    generalize v456.toNat = n456 at *
    generalize v458.toNat = n458 at *
    generalize v459.toNat = n459 at *
    generalize v460.toNat = n460 at *
    generalize v461.toNat = n461 at *
    generalize v462.toNat = n462 at *
    generalize v463.toNat = n463 at *
    generalize v464.toNat = n464 at *
    generalize v465.toNat = n465 at *
    generalize v466.toNat = n466 at *
    generalize v471.toNat = n471 at *
    generalize v472.toNat = n472 at *
    generalize v489.toNat = n489 at *
    generalize v494.toNat = n494 at *
    generalize v495.toNat = n495 at *
    generalize v498.toNat = n498 at *
    omega
  exact smm_key key (smm_lt v465 v498)

set_option maxHeartbeats 10000000 in
theorem evr_v_N5 {v465 v467 v485 v498 : Word}
    (t467 : v467.toNat = v465.toNat * 307527195 % 2 ^ 32)
    (t485 : v485.toNat = v467.toNat % 2 ^ 29) :
    v485.toNat = ((v465.toNat + 2 ^ 32 * v498.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v465.isLt; have := v467.isLt; have := v485.isLt; have := v498.isLt
  generalize v465.toNat = n465 at *
  generalize v467.toNat = n467 at *
  generalize v485.toNat = n485 at *
  generalize v498.toNat = n498 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN5L0 {v485 v488 v492 : Word}
    (t488 : v488.toNat = v485.toNat * 485872621 / 2 ^ 32)
    (t492 : v492.toNat = v485.toNat * 485872621 % 2 ^ 32) :
    v492.toNat + 2 ^ 32 * v488.toNat = v485.toNat * 485872621 := by
  have := v485.isLt; have := v488.isLt; have := v492.isLt
  generalize v485.toNat = n485 at *
  generalize v488.toNat = n488 at *
  generalize v492.toNat = n492 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_T5 {v465 v488 v492 v498 v500 v505 v507 v509 : Word}
    (t500 : v500.toNat = (v498.toNat + v488.toNat) % 2 ^ 32)
    (t507 : v505.toNat + 2 ^ 32 * v507.toNat = v465.toNat + v492.toNat)
    (t509 : v509.toNat = (v500.toNat + v507.toNat) % 2 ^ 32) :
    v505.toNat + 2 ^ 32 * v509.toNat = ((v465.toNat + 2 ^ 32 * v498.toNat) + (v492.toNat + 2 ^ 32 * v488.toNat)) % 2 ^ 64 := by
  obtain ⟨q500, eq500⟩ := mod_q t500; clear t500
  obtain ⟨q509, eq509⟩ := mod_q t509; clear t509
  have key : v505.toNat + 2 ^ 32 * v509.toNat + 2 ^ 64 * (q500 + q509) = ((v465.toNat + 2 ^ 32 * v498.toNat) + (v492.toNat + 2 ^ 32 * v488.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v465.toNat = n465 at *
    generalize v488.toNat = n488 at *
    generalize v492.toNat = n492 at *
    generalize v498.toNat = n498 at *
    generalize v500.toNat = n500 at *
    generalize v505.toNat = n505 at *
    generalize v507.toNat = n507 at *
    generalize v509.toNat = n509 at *
    omega
  exact smm_key key (smm_lt v505 v509)

set_option maxHeartbeats 10000000 in
theorem evr_v_C5 {v505 v509 v511 v526 v527 v568 : Word}
    (t511 : v511.toNat = v505.toNat / 2 ^ 29)
    (t526 : v526.toNat = v509.toNat * 2 ^ 3 % 2 ^ 32)
    (t527 : v527.toNat = v511.toNat + v526.toNat)
    (t568 : v568.toNat = v509.toNat / 2 ^ 29) :
    v527.toNat + 2 ^ 32 * v568.toNat = (v505.toNat + 2 ^ 32 * v509.toNat) / 2 ^ 29 := by
  have := v505.isLt; have := v509.isLt; have := v511.isLt; have := v526.isLt; have := v527.isLt; have := v568.isLt
  generalize v505.toNat = n505 at *
  generalize v509.toNat = n509 at *
  generalize v511.toNat = n511 at *
  generalize v526.toNat = n526 at *
  generalize v527.toNat = n527 at *
  generalize v568.toNat = n568 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN2L4 {v279 v514 v515 : Word}
    (t514 : v514.toNat = v279.toNat * 333 % 2 ^ 32)
    (t515 : v515.toNat = v279.toNat * 333 / 2 ^ 32) :
    v514.toNat + 2 ^ 32 * v515.toNat = v279.toNat * 333 := by
  have := v279.isLt; have := v514.isLt; have := v515.isLt
  generalize v279.toNat = n279 at *
  generalize v514.toNat = n514 at *
  generalize v515.toNat = n515 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN3L3 {v352 v516 v530 : Word}
    (t516 : v516.toNat = v352.toNat * 502512965 % 2 ^ 32)
    (t530 : v530.toNat = v352.toNat * 502512965 / 2 ^ 32) :
    v516.toNat + 2 ^ 32 * v530.toNat = v352.toNat * 502512965 := by
  have := v352.isLt; have := v516.isLt; have := v530.isLt
  generalize v352.toNat = n352 at *
  generalize v516.toNat = n516 at *
  generalize v530.toNat = n530 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN4L2 {v419 v518 v534 : Word}
    (t518 : v518.toNat = v419.toNat * 501691798 % 2 ^ 32)
    (t534 : v534.toNat = v419.toNat * 501691798 / 2 ^ 32) :
    v518.toNat + 2 ^ 32 * v534.toNat = v419.toNat * 501691798 := by
  have := v419.isLt; have := v518.isLt; have := v534.isLt
  generalize v419.toNat = n419 at *
  generalize v518.toNat = n518 at *
  generalize v534.toNat = n534 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN5L1 {v485 v523 v538 : Word}
    (t523 : v523.toNat = v485.toNat * 9640146 % 2 ^ 32)
    (t538 : v538.toNat = v485.toNat * 9640146 / 2 ^ 32) :
    v523.toNat + 2 ^ 32 * v538.toNat = v485.toNat * 9640146 := by
  have := v485.isLt; have := v523.isLt; have := v538.isLt
  generalize v485.toNat = n485 at *
  generalize v523.toNat = n523 at *
  generalize v538.toNat = n538 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S6 {v514 v515 v516 v518 v520 v523 v527 v528 v529 v530 v531 v532 v533 v534 v535 v536 v537 v538 v539 v542 v543 v547 v548 v549 v550 v553 v564 v567 v568 v570 v571 v574 : Word}
    (t531 : v531.toNat = (v528.toNat + v515.toNat) % 2 ^ 32)
    (t535 : v529.toNat + 2 ^ 32 * v535.toNat = v514.toNat + v520.toNat)
    (t539 : v539.toNat = (v535.toNat + v531.toNat) % 2 ^ 32)
    (t542 : v542.toNat = (v539.toNat + v530.toNat) % 2 ^ 32)
    (t543 : v532.toNat + 2 ^ 32 * v543.toNat = v516.toNat + v529.toNat)
    (t547 : v547.toNat = (v542.toNat + v543.toNat) % 2 ^ 32)
    (t548 : v548.toNat = (v547.toNat + v534.toNat) % 2 ^ 32)
    (t549 : v533.toNat + 2 ^ 32 * v549.toNat = v518.toNat + v532.toNat)
    (t550 : v550.toNat = (v548.toNat + v549.toNat) % 2 ^ 32)
    (t553 : v553.toNat = (v550.toNat + v538.toNat) % 2 ^ 32)
    (t564 : v536.toNat + 2 ^ 32 * v564.toNat = v533.toNat + v523.toNat)
    (t567 : v567.toNat = (v553.toNat + v564.toNat) % 2 ^ 32)
    (t570 : v570.toNat = (v567.toNat + v568.toNat) % 2 ^ 32)
    (t571 : v537.toNat + 2 ^ 32 * v571.toNat = v536.toNat + v527.toNat)
    (t574 : v574.toNat = (v570.toNat + v571.toNat) % 2 ^ 32) :
    v537.toNat + 2 ^ 32 * v574.toNat = ((v527.toNat + 2 ^ 32 * v568.toNat) + (v520.toNat + 2 ^ 32 * v528.toNat) + (v514.toNat + 2 ^ 32 * v515.toNat) + (v516.toNat + 2 ^ 32 * v530.toNat) + (v518.toNat + 2 ^ 32 * v534.toNat) + (v523.toNat + 2 ^ 32 * v538.toNat)) % 2 ^ 64 := by
  obtain ⟨q531, eq531⟩ := mod_q t531; clear t531
  obtain ⟨q539, eq539⟩ := mod_q t539; clear t539
  obtain ⟨q542, eq542⟩ := mod_q t542; clear t542
  obtain ⟨q547, eq547⟩ := mod_q t547; clear t547
  obtain ⟨q548, eq548⟩ := mod_q t548; clear t548
  obtain ⟨q550, eq550⟩ := mod_q t550; clear t550
  obtain ⟨q553, eq553⟩ := mod_q t553; clear t553
  obtain ⟨q567, eq567⟩ := mod_q t567; clear t567
  obtain ⟨q570, eq570⟩ := mod_q t570; clear t570
  obtain ⟨q574, eq574⟩ := mod_q t574; clear t574
  have key : v537.toNat + 2 ^ 32 * v574.toNat + 2 ^ 64 * (q531 + q539 + q542 + q547 + q548 + q550 + q553 + q567 + q570 + q574) = ((v527.toNat + 2 ^ 32 * v568.toNat) + (v520.toNat + 2 ^ 32 * v528.toNat) + (v514.toNat + 2 ^ 32 * v515.toNat) + (v516.toNat + 2 ^ 32 * v530.toNat) + (v518.toNat + 2 ^ 32 * v534.toNat) + (v523.toNat + 2 ^ 32 * v538.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v514.toNat = n514 at *
    generalize v515.toNat = n515 at *
    generalize v516.toNat = n516 at *
    generalize v518.toNat = n518 at *
    generalize v520.toNat = n520 at *
    generalize v523.toNat = n523 at *
    generalize v527.toNat = n527 at *
    generalize v528.toNat = n528 at *
    generalize v529.toNat = n529 at *
    generalize v530.toNat = n530 at *
    generalize v531.toNat = n531 at *
    generalize v532.toNat = n532 at *
    generalize v533.toNat = n533 at *
    generalize v534.toNat = n534 at *
    generalize v535.toNat = n535 at *
    generalize v536.toNat = n536 at *
    generalize v537.toNat = n537 at *
    generalize v538.toNat = n538 at *
    generalize v539.toNat = n539 at *
    generalize v542.toNat = n542 at *
    generalize v543.toNat = n543 at *
    generalize v547.toNat = n547 at *
    generalize v548.toNat = n548 at *
    generalize v549.toNat = n549 at *
    generalize v550.toNat = n550 at *
    generalize v553.toNat = n553 at *
    generalize v564.toNat = n564 at *
    generalize v567.toNat = n567 at *
    generalize v568.toNat = n568 at *
    generalize v570.toNat = n570 at *
    generalize v571.toNat = n571 at *
    generalize v574.toNat = n574 at *
    omega
  exact smm_key key (smm_lt v537 v574)

set_option maxHeartbeats 10000000 in
theorem evr_v_N6 {v537 v540 v557 v574 : Word}
    (t540 : v540.toNat = v537.toNat * 307527195 % 2 ^ 32)
    (t557 : v557.toNat = v540.toNat % 2 ^ 29) :
    v557.toNat = ((v537.toNat + 2 ^ 32 * v574.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v537.isLt; have := v540.isLt; have := v557.isLt; have := v574.isLt
  generalize v537.toNat = n537 at *
  generalize v540.toNat = n540 at *
  generalize v557.toNat = n557 at *
  generalize v574.toNat = n574 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN6L0 {v557 v562 v569 : Word}
    (t562 : v562.toNat = v557.toNat * 485872621 / 2 ^ 32)
    (t569 : v569.toNat = v557.toNat * 485872621 % 2 ^ 32) :
    v569.toNat + 2 ^ 32 * v562.toNat = v557.toNat * 485872621 := by
  have := v557.isLt; have := v562.isLt; have := v569.isLt
  generalize v557.toNat = n557 at *
  generalize v562.toNat = n562 at *
  generalize v569.toNat = n569 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_T6 {v537 v562 v569 v574 v577 v586 v587 v593 : Word}
    (t577 : v577.toNat = (v574.toNat + v562.toNat) % 2 ^ 32)
    (t587 : v586.toNat + 2 ^ 32 * v587.toNat = v569.toNat + v537.toNat)
    (t593 : v593.toNat = (v577.toNat + v587.toNat) % 2 ^ 32) :
    v586.toNat + 2 ^ 32 * v593.toNat = ((v537.toNat + 2 ^ 32 * v574.toNat) + (v569.toNat + 2 ^ 32 * v562.toNat)) % 2 ^ 64 := by
  obtain ⟨q577, eq577⟩ := mod_q t577; clear t577
  obtain ⟨q593, eq593⟩ := mod_q t593; clear t593
  have key : v586.toNat + 2 ^ 32 * v593.toNat + 2 ^ 64 * (q577 + q593) = ((v537.toNat + 2 ^ 32 * v574.toNat) + (v569.toNat + 2 ^ 32 * v562.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v537.toNat = n537 at *
    generalize v562.toNat = n562 at *
    generalize v569.toNat = n569 at *
    generalize v574.toNat = n574 at *
    generalize v577.toNat = n577 at *
    generalize v586.toNat = n586 at *
    generalize v587.toNat = n587 at *
    generalize v593.toNat = n593 at *
    omega
  exact smm_key key (smm_lt v586 v593)

set_option maxHeartbeats 10000000 in
theorem evr_v_C6 {v586 v593 v596 v597 v598 v731 : Word}
    (t596 : v596.toNat = v586.toNat / 2 ^ 29)
    (t597 : v597.toNat = v593.toNat * 2 ^ 3 % 2 ^ 32)
    (t598 : v598.toNat = v596.toNat + v597.toNat)
    (t731 : v731.toNat = v593.toNat / 2 ^ 29) :
    v598.toNat + 2 ^ 32 * v731.toNat = (v586.toNat + 2 ^ 32 * v593.toNat) / 2 ^ 29 := by
  have := v586.isLt; have := v593.isLt; have := v596.isLt; have := v597.isLt; have := v598.isLt; have := v731.isLt
  generalize v586.toNat = n586 at *
  generalize v593.toNat = n593 at *
  generalize v596.toNat = n596 at *
  generalize v597.toNat = n597 at *
  generalize v598.toNat = n598 at *
  generalize v731.toNat = n731 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN3L4 {v352 v613 v615 : Word}
    (t613 : v613.toNat = v352.toNat * 333 % 2 ^ 32)
    (t615 : v615.toNat = v352.toNat * 333 / 2 ^ 32) :
    v613.toNat + 2 ^ 32 * v615.toNat = v352.toNat * 333 := by
  have := v352.isLt; have := v613.isLt; have := v615.isLt
  generalize v352.toNat = n352 at *
  generalize v613.toNat = n613 at *
  generalize v615.toNat = n615 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN4L3 {v419 v618 v621 : Word}
    (t618 : v618.toNat = v419.toNat * 502512965 % 2 ^ 32)
    (t621 : v621.toNat = v419.toNat * 502512965 / 2 ^ 32) :
    v618.toNat + 2 ^ 32 * v621.toNat = v419.toNat * 502512965 := by
  have := v419.isLt; have := v618.isLt; have := v621.isLt
  generalize v419.toNat = n419 at *
  generalize v618.toNat = n618 at *
  generalize v621.toNat = n621 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN5L2 {v485 v627 v664 : Word}
    (t627 : v627.toNat = v485.toNat * 501691798 / 2 ^ 32)
    (t664 : v664.toNat = v485.toNat * 501691798 % 2 ^ 32) :
    v664.toNat + 2 ^ 32 * v627.toNat = v485.toNat * 501691798 := by
  have := v485.isLt; have := v627.isLt; have := v664.isLt
  generalize v485.toNat = n485 at *
  generalize v627.toNat = n627 at *
  generalize v664.toNat = n664 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN6L1 {v557 v675 v712 : Word}
    (t675 : v675.toNat = v557.toNat * 9640146 % 2 ^ 32)
    (t712 : v712.toNat = v557.toNat * 9640146 / 2 ^ 32) :
    v675.toNat + 2 ^ 32 * v712.toNat = v557.toNat * 9640146 := by
  have := v557.isLt; have := v675.isLt; have := v712.isLt
  generalize v557.toNat = n557 at *
  generalize v675.toNat = n675 at *
  generalize v712.toNat = n712 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S7 {v598 v613 v615 v618 v621 v624 v627 v628 v629 v630 v631 v632 v633 v634 v635 v636 v638 v664 v675 v684 v697 v698 v712 v719 v727 v728 v729 v730 v731 v732 v733 v735 : Word}
    (t630 : v630.toNat = (v628.toNat + v615.toNat) % 2 ^ 32)
    (t631 : v629.toNat + 2 ^ 32 * v631.toNat = v613.toNat + v624.toNat)
    (t632 : v632.toNat = (v631.toNat + v630.toNat) % 2 ^ 32)
    (t634 : v634.toNat = (v632.toNat + v621.toNat) % 2 ^ 32)
    (t635 : v633.toNat + 2 ^ 32 * v635.toNat = v618.toNat + v629.toNat)
    (t636 : v636.toNat = (v634.toNat + v635.toNat) % 2 ^ 32)
    (t638 : v638.toNat = (v636.toNat + v627.toNat) % 2 ^ 32)
    (t719 : v684.toNat + 2 ^ 32 * v719.toNat = v664.toNat + v633.toNat)
    (t727 : v727.toNat = (v719.toNat + v638.toNat) % 2 ^ 32)
    (t728 : v728.toNat = (v727.toNat + v712.toNat) % 2 ^ 32)
    (t729 : v697.toNat + 2 ^ 32 * v729.toNat = v675.toNat + v684.toNat)
    (t730 : v730.toNat = (v729.toNat + v728.toNat) % 2 ^ 32)
    (t732 : v732.toNat = (v730.toNat + v731.toNat) % 2 ^ 32)
    (t733 : v698.toNat + 2 ^ 32 * v733.toNat = v697.toNat + v598.toNat)
    (t735 : v735.toNat = (v732.toNat + v733.toNat) % 2 ^ 32) :
    v698.toNat + 2 ^ 32 * v735.toNat = ((v598.toNat + 2 ^ 32 * v731.toNat) + (v624.toNat + 2 ^ 32 * v628.toNat) + (v613.toNat + 2 ^ 32 * v615.toNat) + (v618.toNat + 2 ^ 32 * v621.toNat) + (v664.toNat + 2 ^ 32 * v627.toNat) + (v675.toNat + 2 ^ 32 * v712.toNat)) % 2 ^ 64 := by
  obtain ⟨q630, eq630⟩ := mod_q t630; clear t630
  obtain ⟨q632, eq632⟩ := mod_q t632; clear t632
  obtain ⟨q634, eq634⟩ := mod_q t634; clear t634
  obtain ⟨q636, eq636⟩ := mod_q t636; clear t636
  obtain ⟨q638, eq638⟩ := mod_q t638; clear t638
  obtain ⟨q727, eq727⟩ := mod_q t727; clear t727
  obtain ⟨q728, eq728⟩ := mod_q t728; clear t728
  obtain ⟨q730, eq730⟩ := mod_q t730; clear t730
  obtain ⟨q732, eq732⟩ := mod_q t732; clear t732
  obtain ⟨q735, eq735⟩ := mod_q t735; clear t735
  have key : v698.toNat + 2 ^ 32 * v735.toNat + 2 ^ 64 * (q630 + q632 + q634 + q636 + q638 + q727 + q728 + q730 + q732 + q735) = ((v598.toNat + 2 ^ 32 * v731.toNat) + (v624.toNat + 2 ^ 32 * v628.toNat) + (v613.toNat + 2 ^ 32 * v615.toNat) + (v618.toNat + 2 ^ 32 * v621.toNat) + (v664.toNat + 2 ^ 32 * v627.toNat) + (v675.toNat + 2 ^ 32 * v712.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v598.toNat = n598 at *
    generalize v613.toNat = n613 at *
    generalize v615.toNat = n615 at *
    generalize v618.toNat = n618 at *
    generalize v621.toNat = n621 at *
    generalize v624.toNat = n624 at *
    generalize v627.toNat = n627 at *
    generalize v628.toNat = n628 at *
    generalize v629.toNat = n629 at *
    generalize v630.toNat = n630 at *
    generalize v631.toNat = n631 at *
    generalize v632.toNat = n632 at *
    generalize v633.toNat = n633 at *
    generalize v634.toNat = n634 at *
    generalize v635.toNat = n635 at *
    generalize v636.toNat = n636 at *
    generalize v638.toNat = n638 at *
    generalize v664.toNat = n664 at *
    generalize v675.toNat = n675 at *
    generalize v684.toNat = n684 at *
    generalize v697.toNat = n697 at *
    generalize v698.toNat = n698 at *
    generalize v712.toNat = n712 at *
    generalize v719.toNat = n719 at *
    generalize v727.toNat = n727 at *
    generalize v728.toNat = n728 at *
    generalize v729.toNat = n729 at *
    generalize v730.toNat = n730 at *
    generalize v731.toNat = n731 at *
    generalize v732.toNat = n732 at *
    generalize v733.toNat = n733 at *
    generalize v735.toNat = n735 at *
    omega
  exact smm_key key (smm_lt v698 v735)

set_option maxHeartbeats 10000000 in
theorem evr_v_N7 {v698 v702 v722 v735 : Word}
    (t702 : v702.toNat = v698.toNat * 307527195 % 2 ^ 32)
    (t722 : v722.toNat = v702.toNat % 2 ^ 29) :
    v722.toNat = ((v698.toNat + 2 ^ 32 * v735.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v698.isLt; have := v702.isLt; have := v722.isLt; have := v735.isLt
  generalize v698.toNat = n698 at *
  generalize v702.toNat = n702 at *
  generalize v722.toNat = n722 at *
  generalize v735.toNat = n735 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN7L0 {v722 v724 v725 : Word}
    (t724 : v724.toNat = v722.toNat * 485872621 % 2 ^ 32)
    (t725 : v725.toNat = v722.toNat * 485872621 / 2 ^ 32) :
    v724.toNat + 2 ^ 32 * v725.toNat = v722.toNat * 485872621 := by
  have := v722.isLt; have := v724.isLt; have := v725.isLt
  generalize v722.toNat = n722 at *
  generalize v724.toNat = n724 at *
  generalize v725.toNat = n725 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_T7 {v698 v724 v725 v735 v736 v737 v738 v741 : Word}
    (t736 : v736.toNat = (v735.toNat + v725.toNat) % 2 ^ 32)
    (t738 : v737.toNat + 2 ^ 32 * v738.toNat = v698.toNat + v724.toNat)
    (t741 : v741.toNat = (v736.toNat + v738.toNat) % 2 ^ 32) :
    v737.toNat + 2 ^ 32 * v741.toNat = ((v698.toNat + 2 ^ 32 * v735.toNat) + (v724.toNat + 2 ^ 32 * v725.toNat)) % 2 ^ 64 := by
  obtain ⟨q736, eq736⟩ := mod_q t736; clear t736
  obtain ⟨q741, eq741⟩ := mod_q t741; clear t741
  have key : v737.toNat + 2 ^ 32 * v741.toNat + 2 ^ 64 * (q736 + q741) = ((v698.toNat + 2 ^ 32 * v735.toNat) + (v724.toNat + 2 ^ 32 * v725.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v698.toNat = n698 at *
    generalize v724.toNat = n724 at *
    generalize v725.toNat = n725 at *
    generalize v735.toNat = n735 at *
    generalize v736.toNat = n736 at *
    generalize v737.toNat = n737 at *
    generalize v738.toNat = n738 at *
    generalize v741.toNat = n741 at *
    omega
  exact smm_key key (smm_lt v737 v741)

set_option maxHeartbeats 10000000 in
theorem evr_v_C7 {v737 v741 v743 v744 v745 v828 : Word}
    (t743 : v743.toNat = v737.toNat / 2 ^ 29)
    (t744 : v744.toNat = v741.toNat * 2 ^ 3 % 2 ^ 32)
    (t745 : v745.toNat = v743.toNat + v744.toNat)
    (t828 : v828.toNat = v741.toNat / 2 ^ 29) :
    v745.toNat + 2 ^ 32 * v828.toNat = (v737.toNat + 2 ^ 32 * v741.toNat) / 2 ^ 29 := by
  have := v737.isLt; have := v741.isLt; have := v743.isLt; have := v744.isLt; have := v745.isLt; have := v828.isLt
  generalize v737.toNat = n737 at *
  generalize v741.toNat = n741 at *
  generalize v743.toNat = n743 at *
  generalize v744.toNat = n744 at *
  generalize v745.toNat = n745 at *
  generalize v828.toNat = n828 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN0L8 {v2 v8 v120 v136 v147 v151 v750 v752 : Word}
    (t136 : v136.toNat = v120.toNat * 307527195 % 2 ^ 32)
    (t750 : v750.toNat = v136.toNat * 2 ^ 20 % 2 ^ 32)
    (t752 : v752.toNat = v151.toNat / 2 ^ 12)
    (wN0 : v151.toNat = ((v120.toNat + 2 ^ 32 * v147.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wPA0B0 : v120.toNat + 2 ^ 32 * v147.toNat = v8.toNat * (290322925))
    (wA0 : v8.toNat = v2.toNat % 2 ^ 29) :
    v750.toNat + 2 ^ 32 * v752.toNat = v151.toNat * 1048576 := by
  have := v2.isLt; have := v8.isLt; have := v120.isLt; have := v136.isLt; have := v147.isLt; have := v151.isLt; have := v750.isLt; have := v752.isLt
  generalize v2.toNat = n2 at *
  generalize v8.toNat = n8 at *
  generalize v120.toNat = n120 at *
  generalize v136.toNat = n136 at *
  generalize v147.toNat = n147 at *
  generalize v151.toNat = n151 at *
  generalize v750.toNat = n750 at *
  generalize v752.toNat = n752 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN4L4 {v419 v778 v785 : Word}
    (t778 : v778.toNat = v419.toNat * 333 % 2 ^ 32)
    (t785 : v785.toNat = v419.toNat * 333 / 2 ^ 32) :
    v778.toNat + 2 ^ 32 * v785.toNat = v419.toNat * 333 := by
  have := v419.isLt; have := v778.isLt; have := v785.isLt
  generalize v419.toNat = n419 at *
  generalize v778.toNat = n778 at *
  generalize v785.toNat = n785 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN5L3 {v485 v781 v798 : Word}
    (t781 : v781.toNat = v485.toNat * 502512965 % 2 ^ 32)
    (t798 : v798.toNat = v485.toNat * 502512965 / 2 ^ 32) :
    v781.toNat + 2 ^ 32 * v798.toNat = v485.toNat * 502512965 := by
  have := v485.isLt; have := v781.isLt; have := v798.isLt
  generalize v485.toNat = n485 at *
  generalize v781.toNat = n781 at *
  generalize v798.toNat = n798 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN6L2 {v557 v784 v805 : Word}
    (t784 : v784.toNat = v557.toNat * 501691798 % 2 ^ 32)
    (t805 : v805.toNat = v557.toNat * 501691798 / 2 ^ 32) :
    v784.toNat + 2 ^ 32 * v805.toNat = v557.toNat * 501691798 := by
  have := v557.isLt; have := v784.isLt; have := v805.isLt
  generalize v557.toNat = n557 at *
  generalize v784.toNat = n784 at *
  generalize v805.toNat = n805 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN7L1 {v722 v786 v812 : Word}
    (t786 : v786.toNat = v722.toNat * 9640146 % 2 ^ 32)
    (t812 : v812.toNat = v722.toNat * 9640146 / 2 ^ 32) :
    v786.toNat + 2 ^ 32 * v812.toNat = v722.toNat * 9640146 := by
  have := v722.isLt; have := v786.isLt; have := v812.isLt
  generalize v722.toNat = n722 at *
  generalize v786.toNat = n786 at *
  generalize v812.toNat = n812 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S8 {v341 v357 v640 v642 v649 v651 v658 v660 v671 v673 v745 v747 v748 v750 v752 v753 v754 v755 v757 v759 v760 v761 v763 v765 v766 v767 v768 v770 v771 v772 v775 v778 v780 v781 v782 v784 v785 v786 v787 v789 v790 v792 v793 v794 v795 v796 v797 v798 v799 v800 v802 v805 v808 v810 v811 v812 v813 v817 v818 v820 v824 v825 v826 v827 v828 v829 v830 v832 : Word}
    (t754 : v754.toNat = (v747.toNat + v752.toNat) % 2 ^ 32)
    (t755 : v753.toNat + 2 ^ 32 * v755.toNat = v750.toNat + v748.toNat)
    (t757 : v757.toNat = (v755.toNat + v642.toNat) % 2 ^ 32)
    (t760 : v760.toNat = (v754.toNat + v757.toNat) % 2 ^ 32)
    (t761 : v759.toNat + 2 ^ 32 * v761.toNat = v640.toNat + v753.toNat)
    (t763 : v763.toNat = (v761.toNat + v658.toNat) % 2 ^ 32)
    (t766 : v766.toNat = (v760.toNat + v763.toNat) % 2 ^ 32)
    (t767 : v765.toNat + 2 ^ 32 * v767.toNat = v660.toNat + v759.toNat)
    (t768 : v768.toNat = (v767.toNat + v673.toNat) % 2 ^ 32)
    (t771 : v771.toNat = (v766.toNat + v768.toNat) % 2 ^ 32)
    (t772 : v770.toNat + 2 ^ 32 * v772.toNat = v671.toNat + v765.toNat)
    (t775 : v775.toNat = (v772.toNat + v651.toNat) % 2 ^ 32)
    (t782 : v780.toNat + 2 ^ 32 * v782.toNat = v649.toNat + v770.toNat)
    (t787 : v787.toNat = (v771.toNat + v775.toNat) % 2 ^ 32)
    (t789 : v789.toNat = (v782.toNat + 2 ^ 32 - v357.toNat) % 2 ^ 32)
    (t790 : v790.toNat = (v787.toNat + v789.toNat) % 2 ^ 32)
    (t793 : v792.toNat + v341.toNat = v780.toNat + 2 ^ 32 * v793.toNat)
    (t795 : v795.toNat = (v790.toNat + 2 ^ 32 - v793.toNat) % 2 ^ 32)
    (t799 : v799.toNat = (v795.toNat + v785.toNat) % 2 ^ 32)
    (t808 : v794.toNat + 2 ^ 32 * v808.toNat = v778.toNat + v792.toNat)
    (t810 : v810.toNat = (v799.toNat + v808.toNat) % 2 ^ 32)
    (t811 : v811.toNat = (v810.toNat + v798.toNat) % 2 ^ 32)
    (t813 : v796.toNat + 2 ^ 32 * v813.toNat = v794.toNat + v781.toNat)
    (t817 : v817.toNat = (v811.toNat + v813.toNat) % 2 ^ 32)
    (t818 : v818.toNat = (v817.toNat + v805.toNat) % 2 ^ 32)
    (t820 : v797.toNat + 2 ^ 32 * v820.toNat = v784.toNat + v796.toNat)
    (t824 : v824.toNat = (v818.toNat + v820.toNat) % 2 ^ 32)
    (t825 : v825.toNat = (v824.toNat + v812.toNat) % 2 ^ 32)
    (t826 : v800.toNat + 2 ^ 32 * v826.toNat = v797.toNat + v786.toNat)
    (t827 : v827.toNat = (v825.toNat + v826.toNat) % 2 ^ 32)
    (t829 : v829.toNat = (v828.toNat + v827.toNat) % 2 ^ 32)
    (t830 : v802.toNat + 2 ^ 32 * v830.toNat = v745.toNat + v800.toNat)
    (t832 : v832.toNat = (v830.toNat + v829.toNat) % 2 ^ 32) :
    v802.toNat + 2 ^ 32 * v832.toNat = ((v745.toNat + 2 ^ 32 * v828.toNat) + (((((v640.toNat + 2 ^ 32 * v642.toNat) + (v660.toNat + 2 ^ 32 * v658.toNat) + (v671.toNat + 2 ^ 32 * v673.toNat) + (v649.toNat + 2 ^ 32 * v651.toNat)) % 2 ^ 64) + (((v748.toNat + 2 ^ 32 * v747.toNat) + (2 ^ 64 - (v341.toNat + 2 ^ 32 * v357.toNat))) % 2 ^ 64)) % 2 ^ 64) + (v750.toNat + 2 ^ 32 * v752.toNat) + (v778.toNat + 2 ^ 32 * v785.toNat) + (v781.toNat + 2 ^ 32 * v798.toNat) + (v784.toNat + 2 ^ 32 * v805.toNat) + (v786.toNat + 2 ^ 32 * v812.toNat)) % 2 ^ 64 := by
  obtain ⟨q754, eq754⟩ := mod_q t754; clear t754
  obtain ⟨q757, eq757⟩ := mod_q t757; clear t757
  obtain ⟨q760, eq760⟩ := mod_q t760; clear t760
  obtain ⟨q763, eq763⟩ := mod_q t763; clear t763
  obtain ⟨q766, eq766⟩ := mod_q t766; clear t766
  obtain ⟨q768, eq768⟩ := mod_q t768; clear t768
  obtain ⟨q771, eq771⟩ := mod_q t771; clear t771
  obtain ⟨q775, eq775⟩ := mod_q t775; clear t775
  obtain ⟨q787, eq787⟩ := mod_q t787; clear t787
  obtain ⟨q789, eq789⟩ := mod_q t789; clear t789
  obtain ⟨q790, eq790⟩ := mod_q t790; clear t790
  obtain ⟨q795, eq795⟩ := mod_q t795; clear t795
  obtain ⟨q799, eq799⟩ := mod_q t799; clear t799
  obtain ⟨q810, eq810⟩ := mod_q t810; clear t810
  obtain ⟨q811, eq811⟩ := mod_q t811; clear t811
  obtain ⟨q817, eq817⟩ := mod_q t817; clear t817
  obtain ⟨q818, eq818⟩ := mod_q t818; clear t818
  obtain ⟨q824, eq824⟩ := mod_q t824; clear t824
  obtain ⟨q825, eq825⟩ := mod_q t825; clear t825
  obtain ⟨q827, eq827⟩ := mod_q t827; clear t827
  obtain ⟨q829, eq829⟩ := mod_q t829; clear t829
  obtain ⟨q832, eq832⟩ := mod_q t832; clear t832
  obtain ⟨k0, ek0⟩ : ∃ k, ((v748.toNat + 2 ^ 32 * v747.toNat) + (2 ^ 64 - (v341.toNat + 2 ^ 32 * v357.toNat))) % 2 ^ 64 + 2 ^ 64 * k = ((v748.toNat + 2 ^ 32 * v747.toNat) + (2 ^ 64 - (v341.toNat + 2 ^ 32 * v357.toNat))) := ⟨_, Nat.mod_add_div _ _⟩
  obtain ⟨k1, ek1⟩ : ∃ k, ((v640.toNat + 2 ^ 32 * v642.toNat) + (v660.toNat + 2 ^ 32 * v658.toNat) + (v671.toNat + 2 ^ 32 * v673.toNat) + (v649.toNat + 2 ^ 32 * v651.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v640.toNat + 2 ^ 32 * v642.toNat) + (v660.toNat + 2 ^ 32 * v658.toNat) + (v671.toNat + 2 ^ 32 * v673.toNat) + (v649.toNat + 2 ^ 32 * v651.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  obtain ⟨k2, ek2⟩ : ∃ k, ((((v640.toNat + 2 ^ 32 * v642.toNat) + (v660.toNat + 2 ^ 32 * v658.toNat) + (v671.toNat + 2 ^ 32 * v673.toNat) + (v649.toNat + 2 ^ 32 * v651.toNat)) % 2 ^ 64) + (((v748.toNat + 2 ^ 32 * v747.toNat) + (2 ^ 64 - (v341.toNat + 2 ^ 32 * v357.toNat))) % 2 ^ 64)) % 2 ^ 64 + 2 ^ 64 * k = ((((v640.toNat + 2 ^ 32 * v642.toNat) + (v660.toNat + 2 ^ 32 * v658.toNat) + (v671.toNat + 2 ^ 32 * v673.toNat) + (v649.toNat + 2 ^ 32 * v651.toNat)) % 2 ^ 64) + (((v748.toNat + 2 ^ 32 * v747.toNat) + (2 ^ 64 - (v341.toNat + 2 ^ 32 * v357.toNat))) % 2 ^ 64)) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v802.toNat + 2 ^ 32 * v832.toNat + 2 ^ 64 * (q754 + q757 + q760 + q763 + q766 + q768 + q771 + q775 + q787 + q789 + q790 + q795 + q799 + q810 + q811 + q817 + q818 + q824 + q825 + q827 + q829 + q832) = ((v745.toNat + 2 ^ 32 * v828.toNat) + (((((v640.toNat + 2 ^ 32 * v642.toNat) + (v660.toNat + 2 ^ 32 * v658.toNat) + (v671.toNat + 2 ^ 32 * v673.toNat) + (v649.toNat + 2 ^ 32 * v651.toNat)) % 2 ^ 64) + (((v748.toNat + 2 ^ 32 * v747.toNat) + (2 ^ 64 - (v341.toNat + 2 ^ 32 * v357.toNat))) % 2 ^ 64)) % 2 ^ 64) + (v750.toNat + 2 ^ 32 * v752.toNat) + (v778.toNat + 2 ^ 32 * v785.toNat) + (v781.toNat + 2 ^ 32 * v798.toNat) + (v784.toNat + 2 ^ 32 * v805.toNat) + (v786.toNat + 2 ^ 32 * v812.toNat)) + 2 ^ 64 * (k2 + k1 + k0 + 1) := by
    have := v341.isLt; have := v357.isLt; have := v793.isLt; skip
    generalize v341.toNat = n341 at *
    generalize v357.toNat = n357 at *
    generalize v640.toNat = n640 at *
    generalize v642.toNat = n642 at *
    generalize v649.toNat = n649 at *
    generalize v651.toNat = n651 at *
    generalize v658.toNat = n658 at *
    generalize v660.toNat = n660 at *
    generalize v671.toNat = n671 at *
    generalize v673.toNat = n673 at *
    generalize v745.toNat = n745 at *
    generalize v747.toNat = n747 at *
    generalize v748.toNat = n748 at *
    generalize v750.toNat = n750 at *
    generalize v752.toNat = n752 at *
    generalize v753.toNat = n753 at *
    generalize v754.toNat = n754 at *
    generalize v755.toNat = n755 at *
    generalize v757.toNat = n757 at *
    generalize v759.toNat = n759 at *
    generalize v760.toNat = n760 at *
    generalize v761.toNat = n761 at *
    generalize v763.toNat = n763 at *
    generalize v765.toNat = n765 at *
    generalize v766.toNat = n766 at *
    generalize v767.toNat = n767 at *
    generalize v768.toNat = n768 at *
    generalize v770.toNat = n770 at *
    generalize v771.toNat = n771 at *
    generalize v772.toNat = n772 at *
    generalize v775.toNat = n775 at *
    generalize v778.toNat = n778 at *
    generalize v780.toNat = n780 at *
    generalize v781.toNat = n781 at *
    generalize v782.toNat = n782 at *
    generalize v784.toNat = n784 at *
    generalize v785.toNat = n785 at *
    generalize v786.toNat = n786 at *
    generalize v787.toNat = n787 at *
    generalize v789.toNat = n789 at *
    generalize v790.toNat = n790 at *
    generalize v792.toNat = n792 at *
    generalize v793.toNat = n793 at *
    generalize v794.toNat = n794 at *
    generalize v795.toNat = n795 at *
    generalize v796.toNat = n796 at *
    generalize v797.toNat = n797 at *
    generalize v798.toNat = n798 at *
    generalize v799.toNat = n799 at *
    generalize v800.toNat = n800 at *
    generalize v802.toNat = n802 at *
    generalize v805.toNat = n805 at *
    generalize v808.toNat = n808 at *
    generalize v810.toNat = n810 at *
    generalize v811.toNat = n811 at *
    generalize v812.toNat = n812 at *
    generalize v813.toNat = n813 at *
    generalize v817.toNat = n817 at *
    generalize v818.toNat = n818 at *
    generalize v820.toNat = n820 at *
    generalize v824.toNat = n824 at *
    generalize v825.toNat = n825 at *
    generalize v826.toNat = n826 at *
    generalize v827.toNat = n827 at *
    generalize v828.toNat = n828 at *
    generalize v829.toNat = n829 at *
    generalize v830.toNat = n830 at *
    generalize v832.toNat = n832 at *
    omega
  exact smm_key key (smm_lt v802 v832)

set_option maxHeartbeats 10000000 in
theorem evr_v_N8 {v802 v803 v819 v832 : Word}
    (t803 : v803.toNat = v802.toNat * 307527195 % 2 ^ 32)
    (t819 : v819.toNat = v803.toNat % 2 ^ 29) :
    v819.toNat = ((v802.toNat + 2 ^ 32 * v832.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v802.isLt; have := v803.isLt; have := v819.isLt; have := v832.isLt
  generalize v802.toNat = n802 at *
  generalize v803.toNat = n803 at *
  generalize v819.toNat = n819 at *
  generalize v832.toNat = n832 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN8L0 {v819 v821 v851 : Word}
    (t821 : v821.toNat = v819.toNat * 485872621 / 2 ^ 32)
    (t851 : v851.toNat = v819.toNat * 485872621 % 2 ^ 32) :
    v851.toNat + 2 ^ 32 * v821.toNat = v819.toNat * 485872621 := by
  have := v819.isLt; have := v821.isLt; have := v851.isLt
  generalize v819.toNat = n819 at *
  generalize v821.toNat = n821 at *
  generalize v851.toNat = n851 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_T8 {v802 v821 v832 v833 v851 v869 v870 v873 : Word}
    (t833 : v833.toNat = (v832.toNat + v821.toNat) % 2 ^ 32)
    (t870 : v869.toNat + 2 ^ 32 * v870.toNat = v802.toNat + v851.toNat)
    (t873 : v873.toNat = (v833.toNat + v870.toNat) % 2 ^ 32) :
    v869.toNat + 2 ^ 32 * v873.toNat = ((v802.toNat + 2 ^ 32 * v832.toNat) + (v851.toNat + 2 ^ 32 * v821.toNat)) % 2 ^ 64 := by
  obtain ⟨q833, eq833⟩ := mod_q t833; clear t833
  obtain ⟨q873, eq873⟩ := mod_q t873; clear t873
  have key : v869.toNat + 2 ^ 32 * v873.toNat + 2 ^ 64 * (q833 + q873) = ((v802.toNat + 2 ^ 32 * v832.toNat) + (v851.toNat + 2 ^ 32 * v821.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v802.toNat = n802 at *
    generalize v821.toNat = n821 at *
    generalize v832.toNat = n832 at *
    generalize v833.toNat = n833 at *
    generalize v851.toNat = n851 at *
    generalize v869.toNat = n869 at *
    generalize v870.toNat = n870 at *
    generalize v873.toNat = n873 at *
    omega
  exact smm_key key (smm_lt v869 v873)

set_option maxHeartbeats 10000000 in
theorem evr_v_C8 {v869 v873 v912 v913 v914 v915 : Word}
    (t912 : v912.toNat = v869.toNat / 2 ^ 29)
    (t913 : v913.toNat = v873.toNat * 2 ^ 3 % 2 ^ 32)
    (t914 : v914.toNat = v873.toNat / 2 ^ 29)
    (t915 : v915.toNat = v912.toNat + v913.toNat) :
    v915.toNat + 2 ^ 32 * v914.toNat = (v869.toNat + 2 ^ 32 * v873.toNat) / 2 ^ 29 := by
  have := v869.isLt; have := v873.isLt; have := v912.isLt; have := v913.isLt; have := v914.isLt; have := v915.isLt
  generalize v869.toNat = n869 at *
  generalize v873.toNat = n873 at *
  generalize v912.toNat = n912 at *
  generalize v913.toNat = n913 at *
  generalize v914.toNat = n914 at *
  generalize v915.toNat = n915 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN1L8 {v8 v15 v24 v25 v26 v27 v40 v51 v120 v147 v151 v152 v153 v165 v168 v176 v182 v195 v199 v205 v219 v233 v876 v884 : Word}
    (t199 : v199.toNat = v195.toNat * 307527195 % 2 ^ 32)
    (t876 : v876.toNat = v219.toNat / 2 ^ 12)
    (t884 : v884.toNat = v199.toNat * 2 ^ 20 % 2 ^ 32)
    (wN1 : v219.toNat = ((v195.toNat + 2 ^ 32 * v233.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wS1 : v195.toNat + 2 ^ 32 * v233.toNat = (v182.toNat + (v40.toNat + 2 ^ 32 * v51.toNat) + (v176.toNat + 2 ^ 32 * v205.toNat)) % 2 ^ 64)
    (wC0 : v182.toNat = (v165.toNat + 2 ^ 32 * v168.toNat) / 2 ^ 29)
    (wZ1 : v40.toNat + 2 ^ 32 * v51.toNat = ((v26.toNat + 2 ^ 32 * v24.toNat) + (v27.toNat + 2 ^ 32 * v25.toNat)) % 2 ^ 64)
    (wPN0L1 : v176.toNat + 2 ^ 32 * v205.toNat = v151.toNat * 9640146)
    (wT0 : v165.toNat + 2 ^ 32 * v168.toNat = ((v120.toNat + 2 ^ 32 * v147.toNat) + (v152.toNat + 2 ^ 32 * v153.toNat)) % 2 ^ 64)
    (wPA0B1 : v26.toNat + 2 ^ 32 * v24.toNat = v8.toNat * (442594051))
    (wPA1B0 : v27.toNat + 2 ^ 32 * v25.toNat = v15.toNat * (290322925))
    (wN0 : v151.toNat = ((v120.toNat + 2 ^ 32 * v147.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v884.toNat + 2 ^ 32 * v876.toNat = v219.toNat * 1048576 := by
  have := v8.isLt; have := v15.isLt; have := v24.isLt; have := v25.isLt; have := v26.isLt; have := v27.isLt; have := v40.isLt; have := v51.isLt; have := v120.isLt; have := v147.isLt; have := v151.isLt; have := v152.isLt; have := v153.isLt; have := v165.isLt; have := v168.isLt; have := v176.isLt; have := v182.isLt; have := v195.isLt; have := v199.isLt; have := v205.isLt; have := v219.isLt; have := v233.isLt; have := v876.isLt; have := v884.isLt
  generalize v8.toNat = n8 at *
  generalize v15.toNat = n15 at *
  generalize v24.toNat = n24 at *
  generalize v25.toNat = n25 at *
  generalize v26.toNat = n26 at *
  generalize v27.toNat = n27 at *
  generalize v40.toNat = n40 at *
  generalize v51.toNat = n51 at *
  generalize v120.toNat = n120 at *
  generalize v147.toNat = n147 at *
  generalize v151.toNat = n151 at *
  generalize v152.toNat = n152 at *
  generalize v153.toNat = n153 at *
  generalize v165.toNat = n165 at *
  generalize v168.toNat = n168 at *
  generalize v176.toNat = n176 at *
  generalize v182.toNat = n182 at *
  generalize v195.toNat = n195 at *
  generalize v199.toNat = n199 at *
  generalize v205.toNat = n205 at *
  generalize v219.toNat = n219 at *
  generalize v233.toNat = n233 at *
  generalize v876.toNat = n876 at *
  generalize v884.toNat = n884 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN5L4 {v485 v879 v881 : Word}
    (t879 : v879.toNat = v485.toNat * 333 / 2 ^ 32)
    (t881 : v881.toNat = v485.toNat * 333 % 2 ^ 32) :
    v881.toNat + 2 ^ 32 * v879.toNat = v485.toNat * 333 := by
  have := v485.isLt; have := v879.isLt; have := v881.isLt
  generalize v485.toNat = n485 at *
  generalize v879.toNat = n879 at *
  generalize v881.toNat = n881 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN6L3 {v557 v887 v889 : Word}
    (t887 : v887.toNat = v557.toNat * 502512965 % 2 ^ 32)
    (t889 : v889.toNat = v557.toNat * 502512965 / 2 ^ 32) :
    v887.toNat + 2 ^ 32 * v889.toNat = v557.toNat * 502512965 := by
  have := v557.isLt; have := v887.isLt; have := v889.isLt
  generalize v557.toNat = n557 at *
  generalize v887.toNat = n887 at *
  generalize v889.toNat = n889 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN7L2 {v722 v892 v894 : Word}
    (t892 : v892.toNat = v722.toNat * 501691798 % 2 ^ 32)
    (t894 : v894.toNat = v722.toNat * 501691798 / 2 ^ 32) :
    v892.toNat + 2 ^ 32 * v894.toNat = v722.toNat * 501691798 := by
  have := v722.isLt; have := v892.isLt; have := v894.isLt
  generalize v722.toNat = n722 at *
  generalize v892.toNat = n892 at *
  generalize v894.toNat = n894 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN8L1 {v819 v896 v897 : Word}
    (t896 : v896.toNat = v819.toNat * 9640146 % 2 ^ 32)
    (t897 : v897.toNat = v819.toNat * 9640146 / 2 ^ 32) :
    v896.toNat + 2 ^ 32 * v897.toNat = v819.toNat * 9640146 := by
  have := v819.isLt; have := v896.isLt; have := v897.isLt
  generalize v819.toNat = n819 at *
  generalize v896.toNat = n896 at *
  generalize v897.toNat = n897 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S9 {v874 v876 v879 v880 v881 v884 v885 v886 v887 v888 v889 v890 v892 v893 v894 v895 v896 v897 v898 v899 v900 v901 v902 v903 v904 v905 v906 v907 v908 v909 v910 v911 v914 v915 v916 v945 v946 v949 : Word}
    (t880 : v880.toNat = (v874.toNat + v876.toNat) % 2 ^ 32)
    (t888 : v886.toNat + 2 ^ 32 * v888.toNat = v884.toNat + v885.toNat)
    (t890 : v890.toNat = (v880.toNat + v888.toNat) % 2 ^ 32)
    (t893 : v893.toNat = (v890.toNat + v879.toNat) % 2 ^ 32)
    (t898 : v895.toNat + 2 ^ 32 * v898.toNat = v881.toNat + v886.toNat)
    (t899 : v899.toNat = (v893.toNat + v898.toNat) % 2 ^ 32)
    (t901 : v901.toNat = (v889.toNat + v899.toNat) % 2 ^ 32)
    (t902 : v900.toNat + 2 ^ 32 * v902.toNat = v887.toNat + v895.toNat)
    (t903 : v903.toNat = (v901.toNat + v902.toNat) % 2 ^ 32)
    (t905 : v905.toNat = (v903.toNat + v894.toNat) % 2 ^ 32)
    (t906 : v904.toNat + 2 ^ 32 * v906.toNat = v892.toNat + v900.toNat)
    (t907 : v907.toNat = (v906.toNat + v905.toNat) % 2 ^ 32)
    (t909 : v909.toNat = (v907.toNat + v897.toNat) % 2 ^ 32)
    (t910 : v908.toNat + 2 ^ 32 * v910.toNat = v904.toNat + v896.toNat)
    (t911 : v911.toNat = (v909.toNat + v910.toNat) % 2 ^ 32)
    (t916 : v916.toNat = (v911.toNat + v914.toNat) % 2 ^ 32)
    (t946 : v945.toNat + 2 ^ 32 * v946.toNat = v908.toNat + v915.toNat)
    (t949 : v949.toNat = (v916.toNat + v946.toNat) % 2 ^ 32) :
    v945.toNat + 2 ^ 32 * v949.toNat = ((v915.toNat + 2 ^ 32 * v914.toNat) + (v885.toNat + 2 ^ 32 * v874.toNat) + (v884.toNat + 2 ^ 32 * v876.toNat) + (v881.toNat + 2 ^ 32 * v879.toNat) + (v887.toNat + 2 ^ 32 * v889.toNat) + (v892.toNat + 2 ^ 32 * v894.toNat) + (v896.toNat + 2 ^ 32 * v897.toNat)) % 2 ^ 64 := by
  obtain ⟨q880, eq880⟩ := mod_q t880; clear t880
  obtain ⟨q890, eq890⟩ := mod_q t890; clear t890
  obtain ⟨q893, eq893⟩ := mod_q t893; clear t893
  obtain ⟨q899, eq899⟩ := mod_q t899; clear t899
  obtain ⟨q901, eq901⟩ := mod_q t901; clear t901
  obtain ⟨q903, eq903⟩ := mod_q t903; clear t903
  obtain ⟨q905, eq905⟩ := mod_q t905; clear t905
  obtain ⟨q907, eq907⟩ := mod_q t907; clear t907
  obtain ⟨q909, eq909⟩ := mod_q t909; clear t909
  obtain ⟨q911, eq911⟩ := mod_q t911; clear t911
  obtain ⟨q916, eq916⟩ := mod_q t916; clear t916
  obtain ⟨q949, eq949⟩ := mod_q t949; clear t949
  have key : v945.toNat + 2 ^ 32 * v949.toNat + 2 ^ 64 * (q880 + q890 + q893 + q899 + q901 + q903 + q905 + q907 + q909 + q911 + q916 + q949) = ((v915.toNat + 2 ^ 32 * v914.toNat) + (v885.toNat + 2 ^ 32 * v874.toNat) + (v884.toNat + 2 ^ 32 * v876.toNat) + (v881.toNat + 2 ^ 32 * v879.toNat) + (v887.toNat + 2 ^ 32 * v889.toNat) + (v892.toNat + 2 ^ 32 * v894.toNat) + (v896.toNat + 2 ^ 32 * v897.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v874.toNat = n874 at *
    generalize v876.toNat = n876 at *
    generalize v879.toNat = n879 at *
    generalize v880.toNat = n880 at *
    generalize v881.toNat = n881 at *
    generalize v884.toNat = n884 at *
    generalize v885.toNat = n885 at *
    generalize v886.toNat = n886 at *
    generalize v887.toNat = n887 at *
    generalize v888.toNat = n888 at *
    generalize v889.toNat = n889 at *
    generalize v890.toNat = n890 at *
    generalize v892.toNat = n892 at *
    generalize v893.toNat = n893 at *
    generalize v894.toNat = n894 at *
    generalize v895.toNat = n895 at *
    generalize v896.toNat = n896 at *
    generalize v897.toNat = n897 at *
    generalize v898.toNat = n898 at *
    generalize v899.toNat = n899 at *
    generalize v900.toNat = n900 at *
    generalize v901.toNat = n901 at *
    generalize v902.toNat = n902 at *
    generalize v903.toNat = n903 at *
    generalize v904.toNat = n904 at *
    generalize v905.toNat = n905 at *
    generalize v906.toNat = n906 at *
    generalize v907.toNat = n907 at *
    generalize v908.toNat = n908 at *
    generalize v909.toNat = n909 at *
    generalize v910.toNat = n910 at *
    generalize v911.toNat = n911 at *
    generalize v914.toNat = n914 at *
    generalize v915.toNat = n915 at *
    generalize v916.toNat = n916 at *
    generalize v945.toNat = n945 at *
    generalize v946.toNat = n946 at *
    generalize v949.toNat = n949 at *
    omega
  exact smm_key key (smm_lt v945 v949)

set_option maxHeartbeats 10000000 in
theorem evr_v_R0 {v945 v949 : Word}
     :
    v945.toNat = (v945.toNat + 2 ^ 32 * v949.toNat) % 2 ^ 32 := by
  have := v945.isLt; have := v949.isLt
  generalize v945.toNat = n945 at *
  generalize v949.toNat = n949 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_C9 {v945 v949 v977 v978 v979 v987 : Word}
    (t977 : v977.toNat = v949.toNat * 2 ^ 3 % 2 ^ 32)
    (t978 : v978.toNat = v945.toNat / 2 ^ 29)
    (t979 : v979.toNat = v978.toNat + v977.toNat)
    (t987 : v987.toNat = v949.toNat / 2 ^ 29) :
    v979.toNat + 2 ^ 32 * v987.toNat = (v945.toNat + 2 ^ 32 * v949.toNat) / 2 ^ 29 := by
  have := v945.isLt; have := v949.isLt; have := v977.isLt; have := v978.isLt; have := v979.isLt; have := v987.isLt
  generalize v945.toNat = n945 at *
  generalize v949.toNat = n949 at *
  generalize v977.toNat = n977 at *
  generalize v978.toNat = n978 at *
  generalize v979.toNat = n979 at *
  generalize v987.toNat = n987 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN2L8 {v8 v15 v16 v44 v45 v46 v47 v48 v49 v62 v67 v120 v147 v151 v195 v219 v221 v226 v233 v238 v241 v244 v245 v252 v262 v263 v264 v273 v279 v290 v293 v952 v957 : Word}
    (t264 : v264.toNat = v262.toNat * 307527195 % 2 ^ 32)
    (t952 : v952.toNat = v279.toNat / 2 ^ 12)
    (t957 : v957.toNat = v264.toNat * 2 ^ 20 % 2 ^ 32)
    (wN2 : v279.toNat = ((v262.toNat + 2 ^ 32 * v293.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wS2 : v262.toNat + 2 ^ 32 * v293.toNat = ((v252.toNat + 2 ^ 32 * v290.toNat) + (v62.toNat + 2 ^ 32 * v67.toNat) + (v241.toNat + 2 ^ 32 * v263.toNat) + (v244.toNat + 2 ^ 32 * v273.toNat)) % 2 ^ 64)
    (wC1 : v252.toNat + 2 ^ 32 * v290.toNat = (v238.toNat + 2 ^ 32 * v245.toNat) / 2 ^ 29)
    (wZ2 : v62.toNat + 2 ^ 32 * v67.toNat = ((v44.toNat + 2 ^ 32 * v45.toNat) + (v46.toNat + 2 ^ 32 * v47.toNat) + (v49.toNat + 2 ^ 32 * v48.toNat)) % 2 ^ 64)
    (wPN0L2 : v241.toNat + 2 ^ 32 * v263.toNat = v151.toNat * 501691798)
    (wPN1L1 : v244.toNat + 2 ^ 32 * v273.toNat = v219.toNat * 9640146)
    (wT1 : v238.toNat + 2 ^ 32 * v245.toNat = ((v195.toNat + 2 ^ 32 * v233.toNat) + (v226.toNat + 2 ^ 32 * v221.toNat)) % 2 ^ 64)
    (wPA0B2 : v44.toNat + 2 ^ 32 * v45.toNat = v8.toNat * (259787148))
    (wPA1B1 : v46.toNat + 2 ^ 32 * v47.toNat = v15.toNat * (442594051))
    (wPA2B0 : v49.toNat + 2 ^ 32 * v48.toNat = v16.toNat * (290322925))
    (wN0 : v151.toNat = ((v120.toNat + 2 ^ 32 * v147.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (wN1 : v219.toNat = ((v195.toNat + 2 ^ 32 * v233.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v957.toNat + 2 ^ 32 * v952.toNat = v279.toNat * 1048576 := by
  have := v8.isLt; have := v15.isLt; have := v16.isLt; have := v44.isLt; have := v45.isLt; have := v46.isLt; have := v47.isLt; have := v48.isLt; have := v49.isLt; have := v62.isLt; have := v67.isLt; have := v120.isLt; have := v147.isLt; have := v151.isLt; have := v195.isLt; have := v219.isLt; have := v221.isLt; have := v226.isLt; have := v233.isLt; have := v238.isLt; have := v241.isLt; have := v244.isLt; have := v245.isLt; have := v252.isLt; have := v262.isLt; have := v263.isLt; have := v264.isLt; have := v273.isLt; have := v279.isLt; have := v290.isLt; have := v293.isLt; have := v952.isLt; have := v957.isLt
  generalize v8.toNat = n8 at *
  generalize v15.toNat = n15 at *
  generalize v16.toNat = n16 at *
  generalize v44.toNat = n44 at *
  generalize v45.toNat = n45 at *
  generalize v46.toNat = n46 at *
  generalize v47.toNat = n47 at *
  generalize v48.toNat = n48 at *
  generalize v49.toNat = n49 at *
  generalize v62.toNat = n62 at *
  generalize v67.toNat = n67 at *
  generalize v120.toNat = n120 at *
  generalize v147.toNat = n147 at *
  generalize v151.toNat = n151 at *
  generalize v195.toNat = n195 at *
  generalize v219.toNat = n219 at *
  generalize v221.toNat = n221 at *
  generalize v226.toNat = n226 at *
  generalize v233.toNat = n233 at *
  generalize v238.toNat = n238 at *
  generalize v241.toNat = n241 at *
  generalize v244.toNat = n244 at *
  generalize v245.toNat = n245 at *
  generalize v252.toNat = n252 at *
  generalize v262.toNat = n262 at *
  generalize v263.toNat = n263 at *
  generalize v264.toNat = n264 at *
  generalize v273.toNat = n273 at *
  generalize v279.toNat = n279 at *
  generalize v290.toNat = n290 at *
  generalize v293.toNat = n293 at *
  generalize v952.toNat = n952 at *
  generalize v957.toNat = n957 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN6L4 {v557 v953 v955 : Word}
    (t953 : v953.toNat = v557.toNat * 333 % 2 ^ 32)
    (t955 : v955.toNat = v557.toNat * 333 / 2 ^ 32) :
    v953.toNat + 2 ^ 32 * v955.toNat = v557.toNat * 333 := by
  have := v557.isLt; have := v953.isLt; have := v955.isLt
  generalize v557.toNat = n557 at *
  generalize v953.toNat = n953 at *
  generalize v955.toNat = n955 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN7L3 {v722 v958 v960 : Word}
    (t958 : v958.toNat = v722.toNat * 502512965 % 2 ^ 32)
    (t960 : v960.toNat = v722.toNat * 502512965 / 2 ^ 32) :
    v958.toNat + 2 ^ 32 * v960.toNat = v722.toNat * 502512965 := by
  have := v722.isLt; have := v958.isLt; have := v960.isLt
  generalize v722.toNat = n722 at *
  generalize v958.toNat = n958 at *
  generalize v960.toNat = n960 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN8L2 {v819 v962 v963 : Word}
    (t962 : v962.toNat = v819.toNat * 501691798 % 2 ^ 32)
    (t963 : v963.toNat = v819.toNat * 501691798 / 2 ^ 32) :
    v962.toNat + 2 ^ 32 * v963.toNat = v819.toNat * 501691798 := by
  have := v819.isLt; have := v962.isLt; have := v963.isLt
  generalize v819.toNat = n819 at *
  generalize v962.toNat = n962 at *
  generalize v963.toNat = n963 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S10 {v950 v952 v953 v954 v955 v957 v958 v959 v960 v961 v962 v963 v964 v965 v966 v967 v968 v969 v970 v971 v972 v973 v974 v975 v976 v979 v980 v987 v989 v991 v995 v997 : Word}
    (t954 : v954.toNat = (v952.toNat + v950.toNat) % 2 ^ 32)
    (t964 : v961.toNat + 2 ^ 32 * v964.toNat = v957.toNat + v959.toNat)
    (t965 : v965.toNat = (v954.toNat + v964.toNat) % 2 ^ 32)
    (t967 : v967.toNat = (v965.toNat + v955.toNat) % 2 ^ 32)
    (t968 : v966.toNat + 2 ^ 32 * v968.toNat = v953.toNat + v961.toNat)
    (t969 : v969.toNat = (v967.toNat + v968.toNat) % 2 ^ 32)
    (t971 : v971.toNat = (v969.toNat + v960.toNat) % 2 ^ 32)
    (t972 : v970.toNat + 2 ^ 32 * v972.toNat = v958.toNat + v966.toNat)
    (t973 : v973.toNat = (v971.toNat + v972.toNat) % 2 ^ 32)
    (t975 : v975.toNat = (v973.toNat + v963.toNat) % 2 ^ 32)
    (t976 : v974.toNat + 2 ^ 32 * v976.toNat = v962.toNat + v970.toNat)
    (t980 : v980.toNat = (v975.toNat + v976.toNat) % 2 ^ 32)
    (t989 : v989.toNat = (v980.toNat + v987.toNat) % 2 ^ 32)
    (t995 : v991.toNat + 2 ^ 32 * v995.toNat = v974.toNat + v979.toNat)
    (t997 : v997.toNat = (v989.toNat + v995.toNat) % 2 ^ 32) :
    v991.toNat + 2 ^ 32 * v997.toNat = ((v979.toNat + 2 ^ 32 * v987.toNat) + (v959.toNat + 2 ^ 32 * v950.toNat) + (v957.toNat + 2 ^ 32 * v952.toNat) + (v953.toNat + 2 ^ 32 * v955.toNat) + (v958.toNat + 2 ^ 32 * v960.toNat) + (v962.toNat + 2 ^ 32 * v963.toNat)) % 2 ^ 64 := by
  obtain ⟨q954, eq954⟩ := mod_q t954; clear t954
  obtain ⟨q965, eq965⟩ := mod_q t965; clear t965
  obtain ⟨q967, eq967⟩ := mod_q t967; clear t967
  obtain ⟨q969, eq969⟩ := mod_q t969; clear t969
  obtain ⟨q971, eq971⟩ := mod_q t971; clear t971
  obtain ⟨q973, eq973⟩ := mod_q t973; clear t973
  obtain ⟨q975, eq975⟩ := mod_q t975; clear t975
  obtain ⟨q980, eq980⟩ := mod_q t980; clear t980
  obtain ⟨q989, eq989⟩ := mod_q t989; clear t989
  obtain ⟨q997, eq997⟩ := mod_q t997; clear t997
  have key : v991.toNat + 2 ^ 32 * v997.toNat + 2 ^ 64 * (q954 + q965 + q967 + q969 + q971 + q973 + q975 + q980 + q989 + q997) = ((v979.toNat + 2 ^ 32 * v987.toNat) + (v959.toNat + 2 ^ 32 * v950.toNat) + (v957.toNat + 2 ^ 32 * v952.toNat) + (v953.toNat + 2 ^ 32 * v955.toNat) + (v958.toNat + 2 ^ 32 * v960.toNat) + (v962.toNat + 2 ^ 32 * v963.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v950.toNat = n950 at *
    generalize v952.toNat = n952 at *
    generalize v953.toNat = n953 at *
    generalize v954.toNat = n954 at *
    generalize v955.toNat = n955 at *
    generalize v957.toNat = n957 at *
    generalize v958.toNat = n958 at *
    generalize v959.toNat = n959 at *
    generalize v960.toNat = n960 at *
    generalize v961.toNat = n961 at *
    generalize v962.toNat = n962 at *
    generalize v963.toNat = n963 at *
    generalize v964.toNat = n964 at *
    generalize v965.toNat = n965 at *
    generalize v966.toNat = n966 at *
    generalize v967.toNat = n967 at *
    generalize v968.toNat = n968 at *
    generalize v969.toNat = n969 at *
    generalize v970.toNat = n970 at *
    generalize v971.toNat = n971 at *
    generalize v972.toNat = n972 at *
    generalize v973.toNat = n973 at *
    generalize v974.toNat = n974 at *
    generalize v975.toNat = n975 at *
    generalize v976.toNat = n976 at *
    generalize v979.toNat = n979 at *
    generalize v980.toNat = n980 at *
    generalize v987.toNat = n987 at *
    generalize v989.toNat = n989 at *
    generalize v991.toNat = n991 at *
    generalize v995.toNat = n995 at *
    generalize v997.toNat = n997 at *
    omega
  exact smm_key key (smm_lt v991 v997)

end C3.RV32
