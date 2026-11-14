import C3BootProofs.Proofs.P256ScalarDecode

/-! # P-256's `Scalar::mul`, values, part 2

Each lemma proves one value the code holds in words from its instructions' facts. `scripts/gen-p256-scalar.py` writes this file. -/

namespace C3.RV32

open C3.Image

theorem psm_v_S51h {v285 v330 v331 v334 : Word}
    (t334 : v331.toNat + 2 ^ 32 * v334.toNat = v285.toNat + v330.toNat)
    (wS51 : v331.toNat + 2 ^ 32 * v334.toNat = v285.toNat + v330.toNat) :
    v334.toNat = (v331.toNat + 2 ^ 32 * v334.toNat) / 2 ^ 32 := by
  have := v285.isLt; have := v330.isLt; have := v331.isLt; have := v334.isLt
  generalize v285.toNat = n285 at *
  generalize v330.toNat = n330 at *
  generalize v331.toNat = n331 at *
  generalize v334.toNat = n334 at *
  omega

theorem psm_v_S52 {v168 v333 v334 v335 v337 v339 v340 v345 : Word}
    (t335 : v335.toNat = (v168.toNat + v333.toNat) % 2 ^ 32)
    (t337 : v337.toNat = (v334.toNat + v335.toNat) % 2 ^ 32)
    (t339 : v335.toNat + 2 ^ 32 * v339.toNat = v168.toNat + v333.toNat)
    (t340 : v337.toNat + 2 ^ 32 * v340.toNat = v334.toNat + v335.toNat)
    (t345 : v345.toNat = (v339.toNat + v340.toNat) % 2 ^ 32) :
    v337.toNat + 2 ^ 32 * v345.toNat = v333.toNat + v168.toNat + v334.toNat := by
  have := v168.isLt; have := v333.isLt; have := v334.isLt; have := v335.isLt; have := v337.isLt; have := v339.isLt; have := v340.isLt; have := v345.isLt
  generalize v168.toNat = n168 at *
  generalize v333.toNat = n333 at *
  generalize v334.toNat = n334 at *
  generalize v335.toNat = n335 at *
  generalize v337.toNat = n337 at *
  generalize v339.toNat = n339 at *
  generalize v340.toNat = n340 at *
  generalize v345.toNat = n345 at *
  first
    | omega
    | (obtain ⟨qt335, et335⟩ := mod_q t335; clear t335; obtain ⟨qt337, et337⟩ := mod_q t337; clear t337; omega)

theorem psm_v_S52l {v168 v333 v334 v335 v337 v345 : Word}
    (t335 : v335.toNat = (v168.toNat + v333.toNat) % 2 ^ 32)
    (t337 : v337.toNat = (v334.toNat + v335.toNat) % 2 ^ 32)
    (wS52 : v337.toNat + 2 ^ 32 * v345.toNat = v333.toNat + v168.toNat + v334.toNat) :
    v337.toNat = (v337.toNat + 2 ^ 32 * v345.toNat) % 2 ^ 32 := by
  have := v168.isLt; have := v333.isLt; have := v334.isLt; have := v335.isLt; have := v337.isLt; have := v345.isLt
  generalize v168.toNat = n168 at *
  generalize v333.toNat = n333 at *
  generalize v334.toNat = n334 at *
  generalize v335.toNat = n335 at *
  generalize v337.toNat = n337 at *
  generalize v345.toNat = n345 at *
  first
    | omega
    | (obtain ⟨qt335, et335⟩ := mod_q t335; clear t335; obtain ⟨qt337, et337⟩ := mod_q t337; clear t337; omega)

theorem psm_v_S52h {v168 v333 v334 v335 v337 v339 v340 v345 : Word}
    (t335 : v335.toNat = (v168.toNat + v333.toNat) % 2 ^ 32)
    (t339 : v335.toNat + 2 ^ 32 * v339.toNat = v168.toNat + v333.toNat)
    (t340 : v337.toNat + 2 ^ 32 * v340.toNat = v334.toNat + v335.toNat)
    (t345 : v345.toNat = (v339.toNat + v340.toNat) % 2 ^ 32)
    (wS52 : v337.toNat + 2 ^ 32 * v345.toNat = v333.toNat + v168.toNat + v334.toNat) :
    v345.toNat = (v337.toNat + 2 ^ 32 * v345.toNat) / 2 ^ 32 := by
  have := v168.isLt; have := v333.isLt; have := v334.isLt; have := v335.isLt; have := v337.isLt; have := v339.isLt; have := v340.isLt; have := v345.isLt
  generalize v168.toNat = n168 at *
  generalize v333.toNat = n333 at *
  generalize v334.toNat = n334 at *
  generalize v335.toNat = n335 at *
  generalize v337.toNat = n337 at *
  generalize v339.toNat = n339 at *
  generalize v340.toNat = n340 at *
  generalize v345.toNat = n345 at *
  first
    | omega
    | (obtain ⟨qt335, et335⟩ := mod_q t335; clear t335; obtain ⟨qt345, et345⟩ := mod_q t345; clear t345; omega)

theorem psm_v_P53h {v169 v291 v332 v338 v341 v343 v346 v349 : Word}
    (t332 : v332.toNat = v169.toNat * 4007631870 % 2 ^ 32)
    (t338 : v338.toNat = v169.toNat * 4007631870 / 2 ^ 32)
    (t341 : v341.toNat = v291.toNat / 2 * 2)
    (t343 : v343.toNat = (v332.toNat + v341.toNat) % 2 ^ 32)
    (t346 : v343.toNat + 2 ^ 32 * v346.toNat = v332.toNat + v341.toNat)
    (t349 : v349.toNat = (v346.toNat + v338.toNat) % 2 ^ 32) :
    v349.toNat = (v169.toNat * 4007631870 + v291.toNat) / 2 ^ 32 := by
  have := v169.isLt; have := v291.isLt; have := v332.isLt; have := v338.isLt; have := v341.isLt; have := v343.isLt; have := v346.isLt; have := v349.isLt
  generalize v169.toNat = n169 at *
  generalize v291.toNat = n291 at *
  generalize v332.toNat = n332 at *
  generalize v338.toNat = n338 at *
  generalize v341.toNat = n341 at *
  generalize v343.toNat = n343 at *
  generalize v346.toNat = n346 at *
  generalize v349.toNat = n349 at *
  first
    | omega
    | (obtain ⟨qt332, et332⟩ := mod_q t332; clear t332; obtain ⟨qt343, et343⟩ := mod_q t343; clear t343; omega)

theorem psm_v_P54 {v169 v300 v336 v342 v347 v349 v350 v351 v353 v354 v357 : Word}
    (t336 : v336.toNat = v169.toNat * 19922309 % 2 ^ 32)
    (t342 : v342.toNat = v169.toNat * 19922309 / 2 ^ 32)
    (t347 : v347.toNat = (v336.toNat + v300.toNat) % 2 ^ 32)
    (t350 : v347.toNat + 2 ^ 32 * v350.toNat = v336.toNat + v300.toNat)
    (t351 : v351.toNat = (v347.toNat + v349.toNat) % 2 ^ 32)
    (t353 : v353.toNat = (v350.toNat + v342.toNat) % 2 ^ 32)
    (t354 : v351.toNat + 2 ^ 32 * v354.toNat = v347.toNat + v349.toNat)
    (t357 : v357.toNat = (v354.toNat + v353.toNat) % 2 ^ 32) :
    v351.toNat + 2 ^ 32 * v357.toNat = v169.toNat * 19922309 + v300.toNat + v349.toNat := by
  have := v169.isLt; have := v300.isLt; have := v336.isLt; have := v342.isLt; have := v347.isLt; have := v349.isLt; have := v350.isLt; have := v351.isLt; have := v353.isLt; have := v354.isLt; have := v357.isLt
  generalize v169.toNat = n169 at *
  generalize v300.toNat = n300 at *
  generalize v336.toNat = n336 at *
  generalize v342.toNat = n342 at *
  generalize v347.toNat = n347 at *
  generalize v349.toNat = n349 at *
  generalize v350.toNat = n350 at *
  generalize v351.toNat = n351 at *
  generalize v353.toNat = n353 at *
  generalize v354.toNat = n354 at *
  generalize v357.toNat = n357 at *
  first
    | omega
    | (obtain ⟨qt336, et336⟩ := mod_q t336; clear t336; obtain ⟨qt347, et347⟩ := mod_q t347; clear t347; obtain ⟨qt351, et351⟩ := mod_q t351; clear t351; obtain ⟨qt353, et353⟩ := mod_q t353; clear t353; omega)

theorem psm_v_P54l {v169 v300 v336 v347 v349 v351 v357 : Word}
    (t336 : v336.toNat = v169.toNat * 19922309 % 2 ^ 32)
    (t347 : v347.toNat = (v336.toNat + v300.toNat) % 2 ^ 32)
    (t351 : v351.toNat = (v347.toNat + v349.toNat) % 2 ^ 32)
    (wP54 : v351.toNat + 2 ^ 32 * v357.toNat = v169.toNat * 19922309 + v300.toNat + v349.toNat) :
    v351.toNat = (v351.toNat + 2 ^ 32 * v357.toNat) % 2 ^ 32 := by
  have := v169.isLt; have := v300.isLt; have := v336.isLt; have := v347.isLt; have := v349.isLt; have := v351.isLt; have := v357.isLt
  generalize v169.toNat = n169 at *
  generalize v300.toNat = n300 at *
  generalize v336.toNat = n336 at *
  generalize v347.toNat = n347 at *
  generalize v349.toNat = n349 at *
  generalize v351.toNat = n351 at *
  generalize v357.toNat = n357 at *
  first
    | omega
    | (obtain ⟨qt336, et336⟩ := mod_q t336; clear t336; obtain ⟨qt347, et347⟩ := mod_q t347; clear t347; obtain ⟨qt351, et351⟩ := mod_q t351; clear t351; omega)

theorem psm_v_P54h {v169 v300 v336 v342 v347 v349 v350 v351 v353 v354 v357 : Word}
    (t336 : v336.toNat = v169.toNat * 19922309 % 2 ^ 32)
    (t342 : v342.toNat = v169.toNat * 19922309 / 2 ^ 32)
    (t347 : v347.toNat = (v336.toNat + v300.toNat) % 2 ^ 32)
    (t350 : v347.toNat + 2 ^ 32 * v350.toNat = v336.toNat + v300.toNat)
    (t353 : v353.toNat = (v350.toNat + v342.toNat) % 2 ^ 32)
    (t354 : v351.toNat + 2 ^ 32 * v354.toNat = v347.toNat + v349.toNat)
    (t357 : v357.toNat = (v354.toNat + v353.toNat) % 2 ^ 32)
    (wP54 : v351.toNat + 2 ^ 32 * v357.toNat = v169.toNat * 19922309 + v300.toNat + v349.toNat) :
    v357.toNat = (v351.toNat + 2 ^ 32 * v357.toNat) / 2 ^ 32 := by
  have := v169.isLt; have := v300.isLt; have := v336.isLt; have := v342.isLt; have := v347.isLt; have := v349.isLt; have := v350.isLt; have := v351.isLt; have := v353.isLt; have := v354.isLt; have := v357.isLt
  generalize v169.toNat = n169 at *
  generalize v300.toNat = n300 at *
  generalize v336.toNat = n336 at *
  generalize v342.toNat = n342 at *
  generalize v347.toNat = n347 at *
  generalize v349.toNat = n349 at *
  generalize v350.toNat = n350 at *
  generalize v351.toNat = n351 at *
  generalize v353.toNat = n353 at *
  generalize v354.toNat = n354 at *
  generalize v357.toNat = n357 at *
  first
    | omega
    | (obtain ⟨qt336, et336⟩ := mod_q t336; clear t336; obtain ⟨qt347, et347⟩ := mod_q t347; clear t347; obtain ⟨qt353, et353⟩ := mod_q t353; clear t353; obtain ⟨qt357, et357⟩ := mod_q t357; clear t357; omega)

theorem psm_v_P55 {v169 v306 v344 v348 v355 v357 v358 v359 v360 v361 v363 : Word}
    (t344 : v344.toNat = v169.toNat * 3743050785 % 2 ^ 32)
    (t348 : v348.toNat = v169.toNat * 3743050785 / 2 ^ 32)
    (t355 : v355.toNat = (v344.toNat + v306.toNat) % 2 ^ 32)
    (t358 : v355.toNat + 2 ^ 32 * v358.toNat = v344.toNat + v306.toNat)
    (t359 : v359.toNat = (v358.toNat + v348.toNat) % 2 ^ 32)
    (t360 : v360.toNat = (v355.toNat + v357.toNat) % 2 ^ 32)
    (t361 : v360.toNat + 2 ^ 32 * v361.toNat = v355.toNat + v357.toNat)
    (t363 : v363.toNat = (v361.toNat + v359.toNat) % 2 ^ 32) :
    v360.toNat + 2 ^ 32 * v363.toNat = v169.toNat * 3743050785 + v306.toNat + v357.toNat := by
  have := v169.isLt; have := v306.isLt; have := v344.isLt; have := v348.isLt; have := v355.isLt; have := v357.isLt; have := v358.isLt; have := v359.isLt; have := v360.isLt; have := v361.isLt; have := v363.isLt
  generalize v169.toNat = n169 at *
  generalize v306.toNat = n306 at *
  generalize v344.toNat = n344 at *
  generalize v348.toNat = n348 at *
  generalize v355.toNat = n355 at *
  generalize v357.toNat = n357 at *
  generalize v358.toNat = n358 at *
  generalize v359.toNat = n359 at *
  generalize v360.toNat = n360 at *
  generalize v361.toNat = n361 at *
  generalize v363.toNat = n363 at *
  first
    | omega
    | (obtain ⟨qt344, et344⟩ := mod_q t344; clear t344; obtain ⟨qt355, et355⟩ := mod_q t355; clear t355; obtain ⟨qt359, et359⟩ := mod_q t359; clear t359; obtain ⟨qt360, et360⟩ := mod_q t360; clear t360; omega)

theorem psm_v_P55l {v169 v306 v344 v355 v357 v360 v363 : Word}
    (t344 : v344.toNat = v169.toNat * 3743050785 % 2 ^ 32)
    (t355 : v355.toNat = (v344.toNat + v306.toNat) % 2 ^ 32)
    (t360 : v360.toNat = (v355.toNat + v357.toNat) % 2 ^ 32)
    (wP55 : v360.toNat + 2 ^ 32 * v363.toNat = v169.toNat * 3743050785 + v306.toNat + v357.toNat) :
    v360.toNat = (v360.toNat + 2 ^ 32 * v363.toNat) % 2 ^ 32 := by
  have := v169.isLt; have := v306.isLt; have := v344.isLt; have := v355.isLt; have := v357.isLt; have := v360.isLt; have := v363.isLt
  generalize v169.toNat = n169 at *
  generalize v306.toNat = n306 at *
  generalize v344.toNat = n344 at *
  generalize v355.toNat = n355 at *
  generalize v357.toNat = n357 at *
  generalize v360.toNat = n360 at *
  generalize v363.toNat = n363 at *
  first
    | omega
    | (obtain ⟨qt344, et344⟩ := mod_q t344; clear t344; obtain ⟨qt355, et355⟩ := mod_q t355; clear t355; obtain ⟨qt360, et360⟩ := mod_q t360; clear t360; omega)

theorem psm_v_P55h {v169 v306 v344 v348 v355 v357 v358 v359 v360 v361 v363 : Word}
    (t344 : v344.toNat = v169.toNat * 3743050785 % 2 ^ 32)
    (t348 : v348.toNat = v169.toNat * 3743050785 / 2 ^ 32)
    (t355 : v355.toNat = (v344.toNat + v306.toNat) % 2 ^ 32)
    (t358 : v355.toNat + 2 ^ 32 * v358.toNat = v344.toNat + v306.toNat)
    (t359 : v359.toNat = (v358.toNat + v348.toNat) % 2 ^ 32)
    (t361 : v360.toNat + 2 ^ 32 * v361.toNat = v355.toNat + v357.toNat)
    (t363 : v363.toNat = (v361.toNat + v359.toNat) % 2 ^ 32)
    (wP55 : v360.toNat + 2 ^ 32 * v363.toNat = v169.toNat * 3743050785 + v306.toNat + v357.toNat) :
    v363.toNat = (v360.toNat + 2 ^ 32 * v363.toNat) / 2 ^ 32 := by
  have := v169.isLt; have := v306.isLt; have := v344.isLt; have := v348.isLt; have := v355.isLt; have := v357.isLt; have := v358.isLt; have := v359.isLt; have := v360.isLt; have := v361.isLt; have := v363.isLt
  generalize v169.toNat = n169 at *
  generalize v306.toNat = n306 at *
  generalize v344.toNat = n344 at *
  generalize v348.toNat = n348 at *
  generalize v355.toNat = n355 at *
  generalize v357.toNat = n357 at *
  generalize v358.toNat = n358 at *
  generalize v359.toNat = n359 at *
  generalize v360.toNat = n360 at *
  generalize v361.toNat = n361 at *
  generalize v363.toNat = n363 at *
  first
    | omega
    | (obtain ⟨qt344, et344⟩ := mod_q t344; clear t344; obtain ⟨qt355, et355⟩ := mod_q t355; clear t355; obtain ⟨qt359, et359⟩ := mod_q t359; clear t359; obtain ⟨qt363, et363⟩ := mod_q t363; clear t363; omega)

theorem psm_v_P56 {v169 v314 v352 v356 v363 v364 v365 v366 v367 v368 v371 : Word}
    (t352 : v352.toNat = v169.toNat * 1125713234 % 2 ^ 32)
    (t356 : v356.toNat = v169.toNat * 1125713234 / 2 ^ 32)
    (t364 : v364.toNat = (v352.toNat + v314.toNat) % 2 ^ 32)
    (t365 : v364.toNat + 2 ^ 32 * v365.toNat = v352.toNat + v314.toNat)
    (t366 : v366.toNat = (v364.toNat + v363.toNat) % 2 ^ 32)
    (t367 : v367.toNat = (v365.toNat + v356.toNat) % 2 ^ 32)
    (t368 : v366.toNat + 2 ^ 32 * v368.toNat = v364.toNat + v363.toNat)
    (t371 : v371.toNat = (v368.toNat + v367.toNat) % 2 ^ 32) :
    v366.toNat + 2 ^ 32 * v371.toNat = v169.toNat * 1125713234 + v314.toNat + v363.toNat := by
  have := v169.isLt; have := v314.isLt; have := v352.isLt; have := v356.isLt; have := v363.isLt; have := v364.isLt; have := v365.isLt; have := v366.isLt; have := v367.isLt; have := v368.isLt; have := v371.isLt
  generalize v169.toNat = n169 at *
  generalize v314.toNat = n314 at *
  generalize v352.toNat = n352 at *
  generalize v356.toNat = n356 at *
  generalize v363.toNat = n363 at *
  generalize v364.toNat = n364 at *
  generalize v365.toNat = n365 at *
  generalize v366.toNat = n366 at *
  generalize v367.toNat = n367 at *
  generalize v368.toNat = n368 at *
  generalize v371.toNat = n371 at *
  first
    | omega
    | (obtain ⟨qt352, et352⟩ := mod_q t352; clear t352; obtain ⟨qt364, et364⟩ := mod_q t364; clear t364; obtain ⟨qt366, et366⟩ := mod_q t366; clear t366; obtain ⟨qt367, et367⟩ := mod_q t367; clear t367; omega)

theorem psm_v_P56l {v169 v314 v352 v363 v364 v366 v371 : Word}
    (t352 : v352.toNat = v169.toNat * 1125713234 % 2 ^ 32)
    (t364 : v364.toNat = (v352.toNat + v314.toNat) % 2 ^ 32)
    (t366 : v366.toNat = (v364.toNat + v363.toNat) % 2 ^ 32)
    (wP56 : v366.toNat + 2 ^ 32 * v371.toNat = v169.toNat * 1125713234 + v314.toNat + v363.toNat) :
    v366.toNat = (v366.toNat + 2 ^ 32 * v371.toNat) % 2 ^ 32 := by
  have := v169.isLt; have := v314.isLt; have := v352.isLt; have := v363.isLt; have := v364.isLt; have := v366.isLt; have := v371.isLt
  generalize v169.toNat = n169 at *
  generalize v314.toNat = n314 at *
  generalize v352.toNat = n352 at *
  generalize v363.toNat = n363 at *
  generalize v364.toNat = n364 at *
  generalize v366.toNat = n366 at *
  generalize v371.toNat = n371 at *
  first
    | omega
    | (obtain ⟨qt352, et352⟩ := mod_q t352; clear t352; obtain ⟨qt364, et364⟩ := mod_q t364; clear t364; obtain ⟨qt366, et366⟩ := mod_q t366; clear t366; omega)

theorem psm_v_P56h {v169 v314 v352 v356 v363 v364 v365 v366 v367 v368 v371 : Word}
    (t352 : v352.toNat = v169.toNat * 1125713234 % 2 ^ 32)
    (t356 : v356.toNat = v169.toNat * 1125713234 / 2 ^ 32)
    (t364 : v364.toNat = (v352.toNat + v314.toNat) % 2 ^ 32)
    (t365 : v364.toNat + 2 ^ 32 * v365.toNat = v352.toNat + v314.toNat)
    (t367 : v367.toNat = (v365.toNat + v356.toNat) % 2 ^ 32)
    (t368 : v366.toNat + 2 ^ 32 * v368.toNat = v364.toNat + v363.toNat)
    (t371 : v371.toNat = (v368.toNat + v367.toNat) % 2 ^ 32)
    (wP56 : v366.toNat + 2 ^ 32 * v371.toNat = v169.toNat * 1125713234 + v314.toNat + v363.toNat) :
    v371.toNat = (v366.toNat + 2 ^ 32 * v371.toNat) / 2 ^ 32 := by
  have := v169.isLt; have := v314.isLt; have := v352.isLt; have := v356.isLt; have := v363.isLt; have := v364.isLt; have := v365.isLt; have := v366.isLt; have := v367.isLt; have := v368.isLt; have := v371.isLt
  generalize v169.toNat = n169 at *
  generalize v314.toNat = n314 at *
  generalize v352.toNat = n352 at *
  generalize v356.toNat = n356 at *
  generalize v363.toNat = n363 at *
  generalize v364.toNat = n364 at *
  generalize v365.toNat = n365 at *
  generalize v366.toNat = n366 at *
  generalize v367.toNat = n367 at *
  generalize v368.toNat = n368 at *
  generalize v371.toNat = n371 at *
  first
    | omega
    | (obtain ⟨qt352, et352⟩ := mod_q t352; clear t352; obtain ⟨qt364, et364⟩ := mod_q t364; clear t364; obtain ⟨qt367, et367⟩ := mod_q t367; clear t367; obtain ⟨qt371, et371⟩ := mod_q t371; clear t371; omega)

theorem psm_v_P57 {v169 v320 v362 v369 v371 v372 v373 v374 v375 v377 : Word}
    (t362 : v362.toNat = v169.toNat * 4294967295 / 2 ^ 32 ∧ v362.toNat + (v169.toNat + 4294967295) / 4294967296 = v169.toNat)
    (t369 : v369.toNat = (v320.toNat + 2 ^ 32 - v169.toNat) % 2 ^ 32)
    (t372 : (v369.toNat < v320.toNat ∧ v372.toNat = 1) ∨ (v320.toNat ≤ v369.toNat ∧ v372.toNat = 0))
    (t373 : v373.toNat = (v372.toNat + v362.toNat) % 2 ^ 32)
    (t374 : v374.toNat = (v369.toNat + v371.toNat) % 2 ^ 32)
    (t375 : v374.toNat + 2 ^ 32 * v375.toNat = v369.toNat + v371.toNat)
    (t377 : v377.toNat = (v375.toNat + v373.toNat) % 2 ^ 32) :
    v374.toNat + 2 ^ 32 * v377.toNat = v169.toNat * 4294967295 + v320.toNat + v371.toNat := by
  have := v169.isLt; have := v320.isLt; have := v362.isLt; have := v369.isLt; have := v371.isLt; have := v372.isLt; have := v373.isLt; have := v374.isLt; have := v375.isLt; have := v377.isLt
  generalize v169.toNat = n169 at *
  generalize v320.toNat = n320 at *
  generalize v362.toNat = n362 at *
  generalize v369.toNat = n369 at *
  generalize v371.toNat = n371 at *
  generalize v372.toNat = n372 at *
  generalize v373.toNat = n373 at *
  generalize v374.toNat = n374 at *
  generalize v375.toNat = n375 at *
  generalize v377.toNat = n377 at *
  first
    | omega
    | (obtain ⟨t362a, t362b⟩ := t362; rcases Nat.eq_zero_or_pos n169 with _ | _ <;> rcases t372 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t362a, t362b⟩ := t362; obtain ⟨qt369, et369⟩ := mod_q t369; clear t369; obtain ⟨qt373, et373⟩ := mod_q t373; clear t373; obtain ⟨qt374, et374⟩ := mod_q t374; clear t374; omega)
    | (obtain ⟨t362a, t362b⟩ := t362; obtain ⟨qt369, et369⟩ := mod_q t369; clear t369; obtain ⟨qt373, et373⟩ := mod_q t373; clear t373; obtain ⟨qt374, et374⟩ := mod_q t374; clear t374; rcases Nat.eq_zero_or_pos n169 with _ | _ <;> rcases t372 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P57l {v169 v320 v369 v371 v374 v377 : Word}
    (t369 : v369.toNat = (v320.toNat + 2 ^ 32 - v169.toNat) % 2 ^ 32)
    (t374 : v374.toNat = (v369.toNat + v371.toNat) % 2 ^ 32)
    (wP57 : v374.toNat + 2 ^ 32 * v377.toNat = v169.toNat * 4294967295 + v320.toNat + v371.toNat) :
    v374.toNat = (v374.toNat + 2 ^ 32 * v377.toNat) % 2 ^ 32 := by
  have := v169.isLt; have := v320.isLt; have := v369.isLt; have := v371.isLt; have := v374.isLt; have := v377.isLt
  generalize v169.toNat = n169 at *
  generalize v320.toNat = n320 at *
  generalize v369.toNat = n369 at *
  generalize v371.toNat = n371 at *
  generalize v374.toNat = n374 at *
  generalize v377.toNat = n377 at *
  first
    | omega
    | (obtain ⟨qt369, et369⟩ := mod_q t369; clear t369; obtain ⟨qt374, et374⟩ := mod_q t374; clear t374; omega)

theorem psm_v_P57h {v169 v320 v362 v369 v371 v372 v373 v374 v375 v377 : Word}
    (t362 : v362.toNat = v169.toNat * 4294967295 / 2 ^ 32 ∧ v362.toNat + (v169.toNat + 4294967295) / 4294967296 = v169.toNat)
    (t369 : v369.toNat = (v320.toNat + 2 ^ 32 - v169.toNat) % 2 ^ 32)
    (t372 : (v369.toNat < v320.toNat ∧ v372.toNat = 1) ∨ (v320.toNat ≤ v369.toNat ∧ v372.toNat = 0))
    (t373 : v373.toNat = (v372.toNat + v362.toNat) % 2 ^ 32)
    (t375 : v374.toNat + 2 ^ 32 * v375.toNat = v369.toNat + v371.toNat)
    (t377 : v377.toNat = (v375.toNat + v373.toNat) % 2 ^ 32)
    (wP57 : v374.toNat + 2 ^ 32 * v377.toNat = v169.toNat * 4294967295 + v320.toNat + v371.toNat) :
    v377.toNat = (v374.toNat + 2 ^ 32 * v377.toNat) / 2 ^ 32 := by
  have := v169.isLt; have := v320.isLt; have := v362.isLt; have := v369.isLt; have := v371.isLt; have := v372.isLt; have := v373.isLt; have := v374.isLt; have := v375.isLt; have := v377.isLt
  generalize v169.toNat = n169 at *
  generalize v320.toNat = n320 at *
  generalize v362.toNat = n362 at *
  generalize v369.toNat = n369 at *
  generalize v371.toNat = n371 at *
  generalize v372.toNat = n372 at *
  generalize v373.toNat = n373 at *
  generalize v374.toNat = n374 at *
  generalize v375.toNat = n375 at *
  generalize v377.toNat = n377 at *
  first
    | omega
    | (obtain ⟨t362a, t362b⟩ := t362; rcases Nat.eq_zero_or_pos n169 with _ | _ <;> rcases t372 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t362a, t362b⟩ := t362; obtain ⟨qt369, et369⟩ := mod_q t369; clear t369; obtain ⟨qt373, et373⟩ := mod_q t373; clear t373; obtain ⟨qt377, et377⟩ := mod_q t377; clear t377; omega)
    | (obtain ⟨t362a, t362b⟩ := t362; obtain ⟨qt369, et369⟩ := mod_q t369; clear t369; obtain ⟨qt373, et373⟩ := mod_q t373; clear t373; obtain ⟨qt377, et377⟩ := mod_q t377; clear t377; rcases Nat.eq_zero_or_pos n169 with _ | _ <;> rcases t372 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P58 {v169 v326 v370 v376 v377 v378 v379 v380 v381 v382 v383 : Word}
    (t370 : v370.toNat = v169.toNat * 4294967294 / 2 ^ 32 ∧ v370.toNat + (2 * v169.toNat + 4294967295) / 4294967296 = v169.toNat)
    (t376 : v376.toNat = (v169.toNat + v169.toNat) % 2 ^ 32)
    (t378 : v378.toNat = (v326.toNat + 2 ^ 32 - v376.toNat) % 2 ^ 32)
    (t379 : (v378.toNat < v326.toNat ∧ v379.toNat = 1) ∨ (v326.toNat ≤ v378.toNat ∧ v379.toNat = 0))
    (t380 : v380.toNat = (v378.toNat + v377.toNat) % 2 ^ 32)
    (t381 : v381.toNat = (v379.toNat + v370.toNat) % 2 ^ 32)
    (t382 : v380.toNat + 2 ^ 32 * v382.toNat = v378.toNat + v377.toNat)
    (t383 : v383.toNat = (v382.toNat + v381.toNat) % 2 ^ 32) :
    v380.toNat + 2 ^ 32 * v383.toNat = v169.toNat * 4294967294 + v326.toNat + v377.toNat := by
  have := v169.isLt; have := v326.isLt; have := v370.isLt; have := v376.isLt; have := v377.isLt; have := v378.isLt; have := v379.isLt; have := v380.isLt; have := v381.isLt; have := v382.isLt; have := v383.isLt
  generalize v169.toNat = n169 at *
  generalize v326.toNat = n326 at *
  generalize v370.toNat = n370 at *
  generalize v376.toNat = n376 at *
  generalize v377.toNat = n377 at *
  generalize v378.toNat = n378 at *
  generalize v379.toNat = n379 at *
  generalize v380.toNat = n380 at *
  generalize v381.toNat = n381 at *
  generalize v382.toNat = n382 at *
  generalize v383.toNat = n383 at *
  first
    | omega
    | (obtain ⟨t370a, t370b⟩ := t370; rcases (by omega : n169 = 0 ∨ (0 < n169 ∧ n169 ≤ 2147483648) ∨ 2147483648 < n169) with _ | _ | _ <;> rcases t379 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t370a, t370b⟩ := t370; obtain ⟨qt376, et376⟩ := mod_q t376; clear t376; obtain ⟨qt378, et378⟩ := mod_q t378; clear t378; obtain ⟨qt380, et380⟩ := mod_q t380; clear t380; obtain ⟨qt381, et381⟩ := mod_q t381; clear t381; omega)
    | (obtain ⟨t370a, t370b⟩ := t370; obtain ⟨qt376, et376⟩ := mod_q t376; clear t376; obtain ⟨qt378, et378⟩ := mod_q t378; clear t378; obtain ⟨qt380, et380⟩ := mod_q t380; clear t380; obtain ⟨qt381, et381⟩ := mod_q t381; clear t381; rcases (by omega : n169 = 0 ∨ (0 < n169 ∧ n169 ≤ 2147483648) ∨ 2147483648 < n169) with _ | _ | _ <;> rcases t379 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P58l {v169 v326 v376 v377 v378 v380 v383 : Word}
    (t376 : v376.toNat = (v169.toNat + v169.toNat) % 2 ^ 32)
    (t378 : v378.toNat = (v326.toNat + 2 ^ 32 - v376.toNat) % 2 ^ 32)
    (t380 : v380.toNat = (v378.toNat + v377.toNat) % 2 ^ 32)
    (wP58 : v380.toNat + 2 ^ 32 * v383.toNat = v169.toNat * 4294967294 + v326.toNat + v377.toNat) :
    v380.toNat = (v380.toNat + 2 ^ 32 * v383.toNat) % 2 ^ 32 := by
  have := v169.isLt; have := v326.isLt; have := v376.isLt; have := v377.isLt; have := v378.isLt; have := v380.isLt; have := v383.isLt
  generalize v169.toNat = n169 at *
  generalize v326.toNat = n326 at *
  generalize v376.toNat = n376 at *
  generalize v377.toNat = n377 at *
  generalize v378.toNat = n378 at *
  generalize v380.toNat = n380 at *
  generalize v383.toNat = n383 at *
  first
    | omega
    | (obtain ⟨qt376, et376⟩ := mod_q t376; clear t376; obtain ⟨qt378, et378⟩ := mod_q t378; clear t378; obtain ⟨qt380, et380⟩ := mod_q t380; clear t380; omega)

theorem psm_v_P58h {v169 v326 v370 v376 v377 v378 v379 v380 v381 v382 v383 : Word}
    (t370 : v370.toNat = v169.toNat * 4294967294 / 2 ^ 32 ∧ v370.toNat + (2 * v169.toNat + 4294967295) / 4294967296 = v169.toNat)
    (t376 : v376.toNat = (v169.toNat + v169.toNat) % 2 ^ 32)
    (t378 : v378.toNat = (v326.toNat + 2 ^ 32 - v376.toNat) % 2 ^ 32)
    (t379 : (v378.toNat < v326.toNat ∧ v379.toNat = 1) ∨ (v326.toNat ≤ v378.toNat ∧ v379.toNat = 0))
    (t381 : v381.toNat = (v379.toNat + v370.toNat) % 2 ^ 32)
    (t382 : v380.toNat + 2 ^ 32 * v382.toNat = v378.toNat + v377.toNat)
    (t383 : v383.toNat = (v382.toNat + v381.toNat) % 2 ^ 32)
    (wP58 : v380.toNat + 2 ^ 32 * v383.toNat = v169.toNat * 4294967294 + v326.toNat + v377.toNat) :
    v383.toNat = (v380.toNat + 2 ^ 32 * v383.toNat) / 2 ^ 32 := by
  have := v169.isLt; have := v326.isLt; have := v370.isLt; have := v376.isLt; have := v377.isLt; have := v378.isLt; have := v379.isLt; have := v380.isLt; have := v381.isLt; have := v382.isLt; have := v383.isLt
  generalize v169.toNat = n169 at *
  generalize v326.toNat = n326 at *
  generalize v370.toNat = n370 at *
  generalize v376.toNat = n376 at *
  generalize v377.toNat = n377 at *
  generalize v378.toNat = n378 at *
  generalize v379.toNat = n379 at *
  generalize v380.toNat = n380 at *
  generalize v381.toNat = n381 at *
  generalize v382.toNat = n382 at *
  generalize v383.toNat = n383 at *
  first
    | omega
    | (obtain ⟨t370a, t370b⟩ := t370; rcases (by omega : n169 = 0 ∨ (0 < n169 ∧ n169 ≤ 2147483648) ∨ 2147483648 < n169) with _ | _ | _ <;> rcases t379 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t370a, t370b⟩ := t370; obtain ⟨qt376, et376⟩ := mod_q t376; clear t376; obtain ⟨qt378, et378⟩ := mod_q t378; clear t378; obtain ⟨qt381, et381⟩ := mod_q t381; clear t381; obtain ⟨qt383, et383⟩ := mod_q t383; clear t383; omega)
    | (obtain ⟨t370a, t370b⟩ := t370; obtain ⟨qt376, et376⟩ := mod_q t376; clear t376; obtain ⟨qt378, et378⟩ := mod_q t378; clear t378; obtain ⟨qt381, et381⟩ := mod_q t381; clear t381; obtain ⟨qt383, et383⟩ := mod_q t383; clear t383; rcases (by omega : n169 = 0 ∨ (0 < n169 ∧ n169 ≤ 2147483648) ∨ 2147483648 < n169) with _ | _ | _ <;> rcases t379 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P59 {v169 v331 v362 v383 v384 v385 v386 v387 v388 v389 : Word}
    (t362 : v362.toNat = v169.toNat * 4294967295 / 2 ^ 32 ∧ v362.toNat + (v169.toNat + 4294967295) / 4294967296 = v169.toNat)
    (t384 : v384.toNat = (v331.toNat + 2 ^ 32 - v169.toNat) % 2 ^ 32)
    (t385 : (v384.toNat < v331.toNat ∧ v385.toNat = 1) ∨ (v331.toNat ≤ v384.toNat ∧ v385.toNat = 0))
    (t386 : v386.toNat = (v384.toNat + v383.toNat) % 2 ^ 32)
    (t387 : v387.toNat = (v385.toNat + v362.toNat) % 2 ^ 32)
    (t388 : v386.toNat + 2 ^ 32 * v388.toNat = v384.toNat + v383.toNat)
    (t389 : v389.toNat = (v388.toNat + v387.toNat) % 2 ^ 32) :
    v386.toNat + 2 ^ 32 * v389.toNat = v169.toNat * 4294967295 + v331.toNat + v383.toNat := by
  have := v169.isLt; have := v331.isLt; have := v362.isLt; have := v383.isLt; have := v384.isLt; have := v385.isLt; have := v386.isLt; have := v387.isLt; have := v388.isLt; have := v389.isLt
  generalize v169.toNat = n169 at *
  generalize v331.toNat = n331 at *
  generalize v362.toNat = n362 at *
  generalize v383.toNat = n383 at *
  generalize v384.toNat = n384 at *
  generalize v385.toNat = n385 at *
  generalize v386.toNat = n386 at *
  generalize v387.toNat = n387 at *
  generalize v388.toNat = n388 at *
  generalize v389.toNat = n389 at *
  first
    | omega
    | (obtain ⟨t362a, t362b⟩ := t362; rcases Nat.eq_zero_or_pos n169 with _ | _ <;> rcases t385 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t362a, t362b⟩ := t362; obtain ⟨qt384, et384⟩ := mod_q t384; clear t384; obtain ⟨qt386, et386⟩ := mod_q t386; clear t386; obtain ⟨qt387, et387⟩ := mod_q t387; clear t387; omega)
    | (obtain ⟨t362a, t362b⟩ := t362; obtain ⟨qt384, et384⟩ := mod_q t384; clear t384; obtain ⟨qt386, et386⟩ := mod_q t386; clear t386; obtain ⟨qt387, et387⟩ := mod_q t387; clear t387; rcases Nat.eq_zero_or_pos n169 with _ | _ <;> rcases t385 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P59l {v169 v331 v383 v384 v386 v389 : Word}
    (t384 : v384.toNat = (v331.toNat + 2 ^ 32 - v169.toNat) % 2 ^ 32)
    (t386 : v386.toNat = (v384.toNat + v383.toNat) % 2 ^ 32)
    (wP59 : v386.toNat + 2 ^ 32 * v389.toNat = v169.toNat * 4294967295 + v331.toNat + v383.toNat) :
    v386.toNat = (v386.toNat + 2 ^ 32 * v389.toNat) % 2 ^ 32 := by
  have := v169.isLt; have := v331.isLt; have := v383.isLt; have := v384.isLt; have := v386.isLt; have := v389.isLt
  generalize v169.toNat = n169 at *
  generalize v331.toNat = n331 at *
  generalize v383.toNat = n383 at *
  generalize v384.toNat = n384 at *
  generalize v386.toNat = n386 at *
  generalize v389.toNat = n389 at *
  first
    | omega
    | (obtain ⟨qt384, et384⟩ := mod_q t384; clear t384; obtain ⟨qt386, et386⟩ := mod_q t386; clear t386; omega)

theorem psm_v_P59h {v169 v331 v362 v383 v384 v385 v386 v387 v388 v389 : Word}
    (t362 : v362.toNat = v169.toNat * 4294967295 / 2 ^ 32 ∧ v362.toNat + (v169.toNat + 4294967295) / 4294967296 = v169.toNat)
    (t384 : v384.toNat = (v331.toNat + 2 ^ 32 - v169.toNat) % 2 ^ 32)
    (t385 : (v384.toNat < v331.toNat ∧ v385.toNat = 1) ∨ (v331.toNat ≤ v384.toNat ∧ v385.toNat = 0))
    (t387 : v387.toNat = (v385.toNat + v362.toNat) % 2 ^ 32)
    (t388 : v386.toNat + 2 ^ 32 * v388.toNat = v384.toNat + v383.toNat)
    (t389 : v389.toNat = (v388.toNat + v387.toNat) % 2 ^ 32)
    (wP59 : v386.toNat + 2 ^ 32 * v389.toNat = v169.toNat * 4294967295 + v331.toNat + v383.toNat) :
    v389.toNat = (v386.toNat + 2 ^ 32 * v389.toNat) / 2 ^ 32 := by
  have := v169.isLt; have := v331.isLt; have := v362.isLt; have := v383.isLt; have := v384.isLt; have := v385.isLt; have := v386.isLt; have := v387.isLt; have := v388.isLt; have := v389.isLt
  generalize v169.toNat = n169 at *
  generalize v331.toNat = n331 at *
  generalize v362.toNat = n362 at *
  generalize v383.toNat = n383 at *
  generalize v384.toNat = n384 at *
  generalize v385.toNat = n385 at *
  generalize v386.toNat = n386 at *
  generalize v387.toNat = n387 at *
  generalize v388.toNat = n388 at *
  generalize v389.toNat = n389 at *
  first
    | omega
    | (obtain ⟨t362a, t362b⟩ := t362; rcases Nat.eq_zero_or_pos n169 with _ | _ <;> rcases t385 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t362a, t362b⟩ := t362; obtain ⟨qt384, et384⟩ := mod_q t384; clear t384; obtain ⟨qt387, et387⟩ := mod_q t387; clear t387; obtain ⟨qt389, et389⟩ := mod_q t389; clear t389; omega)
    | (obtain ⟨t362a, t362b⟩ := t362; obtain ⟨qt384, et384⟩ := mod_q t384; clear t384; obtain ⟨qt387, et387⟩ := mod_q t387; clear t387; obtain ⟨qt389, et389⟩ := mod_q t389; clear t389; rcases Nat.eq_zero_or_pos n169 with _ | _ <;> rcases t385 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_S60 {v337 v389 v391 v395 : Word}
    (t391 : v391.toNat = (v337.toNat + v389.toNat) % 2 ^ 32)
    (t395 : v391.toNat + 2 ^ 32 * v395.toNat = v337.toNat + v389.toNat) :
    v391.toNat + 2 ^ 32 * v395.toNat = v337.toNat + v389.toNat := by
  have := v337.isLt; have := v389.isLt; have := v391.isLt; have := v395.isLt
  generalize v337.toNat = n337 at *
  generalize v389.toNat = n389 at *
  generalize v391.toNat = n391 at *
  generalize v395.toNat = n395 at *
  first
    | omega
    | (obtain ⟨qt391, et391⟩ := mod_q t391; clear t391; omega)

theorem psm_v_S60l {v337 v389 v391 v395 : Word}
    (t391 : v391.toNat = (v337.toNat + v389.toNat) % 2 ^ 32)
    (wS60 : v391.toNat + 2 ^ 32 * v395.toNat = v337.toNat + v389.toNat) :
    v391.toNat = (v391.toNat + 2 ^ 32 * v395.toNat) % 2 ^ 32 := by
  have := v337.isLt; have := v389.isLt; have := v391.isLt; have := v395.isLt
  generalize v337.toNat = n337 at *
  generalize v389.toNat = n389 at *
  generalize v391.toNat = n391 at *
  generalize v395.toNat = n395 at *
  first
    | omega
    | (obtain ⟨qt391, et391⟩ := mod_q t391; clear t391; omega)

theorem psm_v_S60h {v337 v389 v391 v395 : Word}
    (t395 : v391.toNat + 2 ^ 32 * v395.toNat = v337.toNat + v389.toNat)
    (wS60 : v391.toNat + 2 ^ 32 * v395.toNat = v337.toNat + v389.toNat) :
    v395.toNat = (v391.toNat + 2 ^ 32 * v395.toNat) / 2 ^ 32 := by
  have := v337.isLt; have := v389.isLt; have := v391.isLt; have := v395.isLt
  generalize v337.toNat = n337 at *
  generalize v389.toNat = n389 at *
  generalize v391.toNat = n391 at *
  generalize v395.toNat = n395 at *
  omega

theorem psm_v_S61 {v169 v345 v392 v395 v396 v397 v401 v447 : Word}
    (t392 : v392.toNat = (v169.toNat + v345.toNat) % 2 ^ 32)
    (t396 : v392.toNat + 2 ^ 32 * v396.toNat = v169.toNat + v345.toNat)
    (t397 : v397.toNat = (v395.toNat + v392.toNat) % 2 ^ 32)
    (t401 : v397.toNat + 2 ^ 32 * v401.toNat = v395.toNat + v392.toNat)
    (t447 : v447.toNat = (v396.toNat + v401.toNat) % 2 ^ 32) :
    v397.toNat + 2 ^ 32 * v447.toNat = v345.toNat + v169.toNat + v395.toNat := by
  have := v169.isLt; have := v345.isLt; have := v392.isLt; have := v395.isLt; have := v396.isLt; have := v397.isLt; have := v401.isLt; have := v447.isLt
  generalize v169.toNat = n169 at *
  generalize v345.toNat = n345 at *
  generalize v392.toNat = n392 at *
  generalize v395.toNat = n395 at *
  generalize v396.toNat = n396 at *
  generalize v397.toNat = n397 at *
  generalize v401.toNat = n401 at *
  generalize v447.toNat = n447 at *
  first
    | omega
    | (obtain ⟨qt392, et392⟩ := mod_q t392; clear t392; obtain ⟨qt397, et397⟩ := mod_q t397; clear t397; omega)

theorem psm_v_S61l {v169 v345 v392 v395 v397 v447 : Word}
    (t392 : v392.toNat = (v169.toNat + v345.toNat) % 2 ^ 32)
    (t397 : v397.toNat = (v395.toNat + v392.toNat) % 2 ^ 32)
    (wS61 : v397.toNat + 2 ^ 32 * v447.toNat = v345.toNat + v169.toNat + v395.toNat) :
    v397.toNat = (v397.toNat + 2 ^ 32 * v447.toNat) % 2 ^ 32 := by
  have := v169.isLt; have := v345.isLt; have := v392.isLt; have := v395.isLt; have := v397.isLt; have := v447.isLt
  generalize v169.toNat = n169 at *
  generalize v345.toNat = n345 at *
  generalize v392.toNat = n392 at *
  generalize v395.toNat = n395 at *
  generalize v397.toNat = n397 at *
  generalize v447.toNat = n447 at *
  first
    | omega
    | (obtain ⟨qt392, et392⟩ := mod_q t392; clear t392; obtain ⟨qt397, et397⟩ := mod_q t397; clear t397; omega)

theorem psm_v_S61h {v169 v345 v392 v395 v396 v397 v401 v447 : Word}
    (t392 : v392.toNat = (v169.toNat + v345.toNat) % 2 ^ 32)
    (t396 : v392.toNat + 2 ^ 32 * v396.toNat = v169.toNat + v345.toNat)
    (t401 : v397.toNat + 2 ^ 32 * v401.toNat = v395.toNat + v392.toNat)
    (t447 : v447.toNat = (v396.toNat + v401.toNat) % 2 ^ 32)
    (wS61 : v397.toNat + 2 ^ 32 * v447.toNat = v345.toNat + v169.toNat + v395.toNat) :
    v447.toNat = (v397.toNat + 2 ^ 32 * v447.toNat) / 2 ^ 32 := by
  have := v169.isLt; have := v345.isLt; have := v392.isLt; have := v395.isLt; have := v396.isLt; have := v397.isLt; have := v401.isLt; have := v447.isLt
  generalize v169.toNat = n169 at *
  generalize v345.toNat = n345 at *
  generalize v392.toNat = n392 at *
  generalize v395.toNat = n395 at *
  generalize v396.toNat = n396 at *
  generalize v397.toNat = n397 at *
  generalize v401.toNat = n401 at *
  generalize v447.toNat = n447 at *
  first
    | omega
    | (obtain ⟨qt392, et392⟩ := mod_q t392; clear t392; obtain ⟨qt447, et447⟩ := mod_q t447; clear t447; omega)

theorem psm_v_P62h {v170 v351 v390 v393 v399 v402 v403 v405 : Word}
    (t390 : v390.toNat = v170.toNat * 4007631870 % 2 ^ 32)
    (t393 : v393.toNat = v170.toNat * 4007631870 / 2 ^ 32)
    (t399 : v399.toNat = v351.toNat / 2 * 2)
    (t402 : v402.toNat = (v390.toNat + v399.toNat) % 2 ^ 32)
    (t403 : v402.toNat + 2 ^ 32 * v403.toNat = v390.toNat + v399.toNat)
    (t405 : v405.toNat = (v403.toNat + v393.toNat) % 2 ^ 32) :
    v405.toNat = (v170.toNat * 4007631870 + v351.toNat) / 2 ^ 32 := by
  have := v170.isLt; have := v351.isLt; have := v390.isLt; have := v393.isLt; have := v399.isLt; have := v402.isLt; have := v403.isLt; have := v405.isLt
  generalize v170.toNat = n170 at *
  generalize v351.toNat = n351 at *
  generalize v390.toNat = n390 at *
  generalize v393.toNat = n393 at *
  generalize v399.toNat = n399 at *
  generalize v402.toNat = n402 at *
  generalize v403.toNat = n403 at *
  generalize v405.toNat = n405 at *
  first
    | omega
    | (obtain ⟨qt390, et390⟩ := mod_q t390; clear t390; obtain ⟨qt402, et402⟩ := mod_q t402; clear t402; omega)

theorem psm_v_P63 {v170 v360 v394 v398 v405 v406 v407 v409 v410 v413 v415 : Word}
    (t394 : v394.toNat = v170.toNat * 19922309 % 2 ^ 32)
    (t398 : v398.toNat = v170.toNat * 19922309 / 2 ^ 32)
    (t406 : v406.toNat = (v394.toNat + v360.toNat) % 2 ^ 32)
    (t407 : v406.toNat + 2 ^ 32 * v407.toNat = v394.toNat + v360.toNat)
    (t409 : v409.toNat = (v407.toNat + v398.toNat) % 2 ^ 32)
    (t410 : v410.toNat = (v406.toNat + v405.toNat) % 2 ^ 32)
    (t413 : v410.toNat + 2 ^ 32 * v413.toNat = v406.toNat + v405.toNat)
    (t415 : v415.toNat = (v413.toNat + v409.toNat) % 2 ^ 32) :
    v410.toNat + 2 ^ 32 * v415.toNat = v170.toNat * 19922309 + v360.toNat + v405.toNat := by
  have := v170.isLt; have := v360.isLt; have := v394.isLt; have := v398.isLt; have := v405.isLt; have := v406.isLt; have := v407.isLt; have := v409.isLt; have := v410.isLt; have := v413.isLt; have := v415.isLt
  generalize v170.toNat = n170 at *
  generalize v360.toNat = n360 at *
  generalize v394.toNat = n394 at *
  generalize v398.toNat = n398 at *
  generalize v405.toNat = n405 at *
  generalize v406.toNat = n406 at *
  generalize v407.toNat = n407 at *
  generalize v409.toNat = n409 at *
  generalize v410.toNat = n410 at *
  generalize v413.toNat = n413 at *
  generalize v415.toNat = n415 at *
  first
    | omega
    | (obtain ⟨qt394, et394⟩ := mod_q t394; clear t394; obtain ⟨qt406, et406⟩ := mod_q t406; clear t406; obtain ⟨qt409, et409⟩ := mod_q t409; clear t409; obtain ⟨qt410, et410⟩ := mod_q t410; clear t410; omega)

theorem psm_v_P63l {v170 v360 v394 v405 v406 v410 v415 : Word}
    (t394 : v394.toNat = v170.toNat * 19922309 % 2 ^ 32)
    (t406 : v406.toNat = (v394.toNat + v360.toNat) % 2 ^ 32)
    (t410 : v410.toNat = (v406.toNat + v405.toNat) % 2 ^ 32)
    (wP63 : v410.toNat + 2 ^ 32 * v415.toNat = v170.toNat * 19922309 + v360.toNat + v405.toNat) :
    v410.toNat = (v410.toNat + 2 ^ 32 * v415.toNat) % 2 ^ 32 := by
  have := v170.isLt; have := v360.isLt; have := v394.isLt; have := v405.isLt; have := v406.isLt; have := v410.isLt; have := v415.isLt
  generalize v170.toNat = n170 at *
  generalize v360.toNat = n360 at *
  generalize v394.toNat = n394 at *
  generalize v405.toNat = n405 at *
  generalize v406.toNat = n406 at *
  generalize v410.toNat = n410 at *
  generalize v415.toNat = n415 at *
  first
    | omega
    | (obtain ⟨qt394, et394⟩ := mod_q t394; clear t394; obtain ⟨qt406, et406⟩ := mod_q t406; clear t406; obtain ⟨qt410, et410⟩ := mod_q t410; clear t410; omega)

theorem psm_v_P63h {v170 v360 v394 v398 v405 v406 v407 v409 v410 v413 v415 : Word}
    (t394 : v394.toNat = v170.toNat * 19922309 % 2 ^ 32)
    (t398 : v398.toNat = v170.toNat * 19922309 / 2 ^ 32)
    (t406 : v406.toNat = (v394.toNat + v360.toNat) % 2 ^ 32)
    (t407 : v406.toNat + 2 ^ 32 * v407.toNat = v394.toNat + v360.toNat)
    (t409 : v409.toNat = (v407.toNat + v398.toNat) % 2 ^ 32)
    (t413 : v410.toNat + 2 ^ 32 * v413.toNat = v406.toNat + v405.toNat)
    (t415 : v415.toNat = (v413.toNat + v409.toNat) % 2 ^ 32)
    (wP63 : v410.toNat + 2 ^ 32 * v415.toNat = v170.toNat * 19922309 + v360.toNat + v405.toNat) :
    v415.toNat = (v410.toNat + 2 ^ 32 * v415.toNat) / 2 ^ 32 := by
  have := v170.isLt; have := v360.isLt; have := v394.isLt; have := v398.isLt; have := v405.isLt; have := v406.isLt; have := v407.isLt; have := v409.isLt; have := v410.isLt; have := v413.isLt; have := v415.isLt
  generalize v170.toNat = n170 at *
  generalize v360.toNat = n360 at *
  generalize v394.toNat = n394 at *
  generalize v398.toNat = n398 at *
  generalize v405.toNat = n405 at *
  generalize v406.toNat = n406 at *
  generalize v407.toNat = n407 at *
  generalize v409.toNat = n409 at *
  generalize v410.toNat = n410 at *
  generalize v413.toNat = n413 at *
  generalize v415.toNat = n415 at *
  first
    | omega
    | (obtain ⟨qt394, et394⟩ := mod_q t394; clear t394; obtain ⟨qt406, et406⟩ := mod_q t406; clear t406; obtain ⟨qt409, et409⟩ := mod_q t409; clear t409; obtain ⟨qt415, et415⟩ := mod_q t415; clear t415; omega)

theorem psm_v_P64 {v170 v366 v400 v404 v411 v414 v415 v416 v417 v419 v421 : Word}
    (t400 : v400.toNat = v170.toNat * 3743050785 % 2 ^ 32)
    (t404 : v404.toNat = v170.toNat * 3743050785 / 2 ^ 32)
    (t411 : v411.toNat = (v400.toNat + v366.toNat) % 2 ^ 32)
    (t414 : v411.toNat + 2 ^ 32 * v414.toNat = v400.toNat + v366.toNat)
    (t416 : v416.toNat = (v404.toNat + v414.toNat) % 2 ^ 32)
    (t417 : v417.toNat = (v411.toNat + v415.toNat) % 2 ^ 32)
    (t419 : v417.toNat + 2 ^ 32 * v419.toNat = v411.toNat + v415.toNat)
    (t421 : v421.toNat = (v419.toNat + v416.toNat) % 2 ^ 32) :
    v417.toNat + 2 ^ 32 * v421.toNat = v170.toNat * 3743050785 + v366.toNat + v415.toNat := by
  have := v170.isLt; have := v366.isLt; have := v400.isLt; have := v404.isLt; have := v411.isLt; have := v414.isLt; have := v415.isLt; have := v416.isLt; have := v417.isLt; have := v419.isLt; have := v421.isLt
  generalize v170.toNat = n170 at *
  generalize v366.toNat = n366 at *
  generalize v400.toNat = n400 at *
  generalize v404.toNat = n404 at *
  generalize v411.toNat = n411 at *
  generalize v414.toNat = n414 at *
  generalize v415.toNat = n415 at *
  generalize v416.toNat = n416 at *
  generalize v417.toNat = n417 at *
  generalize v419.toNat = n419 at *
  generalize v421.toNat = n421 at *
  first
    | omega
    | (obtain ⟨qt400, et400⟩ := mod_q t400; clear t400; obtain ⟨qt411, et411⟩ := mod_q t411; clear t411; obtain ⟨qt416, et416⟩ := mod_q t416; clear t416; obtain ⟨qt417, et417⟩ := mod_q t417; clear t417; omega)

theorem psm_v_P64l {v170 v366 v400 v411 v415 v417 v421 : Word}
    (t400 : v400.toNat = v170.toNat * 3743050785 % 2 ^ 32)
    (t411 : v411.toNat = (v400.toNat + v366.toNat) % 2 ^ 32)
    (t417 : v417.toNat = (v411.toNat + v415.toNat) % 2 ^ 32)
    (wP64 : v417.toNat + 2 ^ 32 * v421.toNat = v170.toNat * 3743050785 + v366.toNat + v415.toNat) :
    v417.toNat = (v417.toNat + 2 ^ 32 * v421.toNat) % 2 ^ 32 := by
  have := v170.isLt; have := v366.isLt; have := v400.isLt; have := v411.isLt; have := v415.isLt; have := v417.isLt; have := v421.isLt
  generalize v170.toNat = n170 at *
  generalize v366.toNat = n366 at *
  generalize v400.toNat = n400 at *
  generalize v411.toNat = n411 at *
  generalize v415.toNat = n415 at *
  generalize v417.toNat = n417 at *
  generalize v421.toNat = n421 at *
  first
    | omega
    | (obtain ⟨qt400, et400⟩ := mod_q t400; clear t400; obtain ⟨qt411, et411⟩ := mod_q t411; clear t411; obtain ⟨qt417, et417⟩ := mod_q t417; clear t417; omega)

theorem psm_v_P64h {v170 v366 v400 v404 v411 v414 v415 v416 v417 v419 v421 : Word}
    (t400 : v400.toNat = v170.toNat * 3743050785 % 2 ^ 32)
    (t404 : v404.toNat = v170.toNat * 3743050785 / 2 ^ 32)
    (t411 : v411.toNat = (v400.toNat + v366.toNat) % 2 ^ 32)
    (t414 : v411.toNat + 2 ^ 32 * v414.toNat = v400.toNat + v366.toNat)
    (t416 : v416.toNat = (v404.toNat + v414.toNat) % 2 ^ 32)
    (t419 : v417.toNat + 2 ^ 32 * v419.toNat = v411.toNat + v415.toNat)
    (t421 : v421.toNat = (v419.toNat + v416.toNat) % 2 ^ 32)
    (wP64 : v417.toNat + 2 ^ 32 * v421.toNat = v170.toNat * 3743050785 + v366.toNat + v415.toNat) :
    v421.toNat = (v417.toNat + 2 ^ 32 * v421.toNat) / 2 ^ 32 := by
  have := v170.isLt; have := v366.isLt; have := v400.isLt; have := v404.isLt; have := v411.isLt; have := v414.isLt; have := v415.isLt; have := v416.isLt; have := v417.isLt; have := v419.isLt; have := v421.isLt
  generalize v170.toNat = n170 at *
  generalize v366.toNat = n366 at *
  generalize v400.toNat = n400 at *
  generalize v404.toNat = n404 at *
  generalize v411.toNat = n411 at *
  generalize v414.toNat = n414 at *
  generalize v415.toNat = n415 at *
  generalize v416.toNat = n416 at *
  generalize v417.toNat = n417 at *
  generalize v419.toNat = n419 at *
  generalize v421.toNat = n421 at *
  first
    | omega
    | (obtain ⟨qt400, et400⟩ := mod_q t400; clear t400; obtain ⟨qt411, et411⟩ := mod_q t411; clear t411; obtain ⟨qt416, et416⟩ := mod_q t416; clear t416; obtain ⟨qt421, et421⟩ := mod_q t421; clear t421; omega)

theorem psm_v_P65 {v170 v374 v408 v412 v420 v421 v422 v423 v424 v427 v429 : Word}
    (t408 : v408.toNat = v170.toNat * 1125713234 % 2 ^ 32)
    (t412 : v412.toNat = v170.toNat * 1125713234 / 2 ^ 32)
    (t420 : v420.toNat = (v408.toNat + v374.toNat) % 2 ^ 32)
    (t422 : v420.toNat + 2 ^ 32 * v422.toNat = v408.toNat + v374.toNat)
    (t423 : v423.toNat = (v412.toNat + v422.toNat) % 2 ^ 32)
    (t424 : v424.toNat = (v420.toNat + v421.toNat) % 2 ^ 32)
    (t427 : v424.toNat + 2 ^ 32 * v427.toNat = v420.toNat + v421.toNat)
    (t429 : v429.toNat = (v423.toNat + v427.toNat) % 2 ^ 32) :
    v424.toNat + 2 ^ 32 * v429.toNat = v170.toNat * 1125713234 + v374.toNat + v421.toNat := by
  have := v170.isLt; have := v374.isLt; have := v408.isLt; have := v412.isLt; have := v420.isLt; have := v421.isLt; have := v422.isLt; have := v423.isLt; have := v424.isLt; have := v427.isLt; have := v429.isLt
  generalize v170.toNat = n170 at *
  generalize v374.toNat = n374 at *
  generalize v408.toNat = n408 at *
  generalize v412.toNat = n412 at *
  generalize v420.toNat = n420 at *
  generalize v421.toNat = n421 at *
  generalize v422.toNat = n422 at *
  generalize v423.toNat = n423 at *
  generalize v424.toNat = n424 at *
  generalize v427.toNat = n427 at *
  generalize v429.toNat = n429 at *
  first
    | omega
    | (obtain ⟨qt408, et408⟩ := mod_q t408; clear t408; obtain ⟨qt420, et420⟩ := mod_q t420; clear t420; obtain ⟨qt423, et423⟩ := mod_q t423; clear t423; obtain ⟨qt424, et424⟩ := mod_q t424; clear t424; omega)

theorem psm_v_P65l {v170 v374 v408 v420 v421 v424 v429 : Word}
    (t408 : v408.toNat = v170.toNat * 1125713234 % 2 ^ 32)
    (t420 : v420.toNat = (v408.toNat + v374.toNat) % 2 ^ 32)
    (t424 : v424.toNat = (v420.toNat + v421.toNat) % 2 ^ 32)
    (wP65 : v424.toNat + 2 ^ 32 * v429.toNat = v170.toNat * 1125713234 + v374.toNat + v421.toNat) :
    v424.toNat = (v424.toNat + 2 ^ 32 * v429.toNat) % 2 ^ 32 := by
  have := v170.isLt; have := v374.isLt; have := v408.isLt; have := v420.isLt; have := v421.isLt; have := v424.isLt; have := v429.isLt
  generalize v170.toNat = n170 at *
  generalize v374.toNat = n374 at *
  generalize v408.toNat = n408 at *
  generalize v420.toNat = n420 at *
  generalize v421.toNat = n421 at *
  generalize v424.toNat = n424 at *
  generalize v429.toNat = n429 at *
  first
    | omega
    | (obtain ⟨qt408, et408⟩ := mod_q t408; clear t408; obtain ⟨qt420, et420⟩ := mod_q t420; clear t420; obtain ⟨qt424, et424⟩ := mod_q t424; clear t424; omega)

theorem psm_v_P65h {v170 v374 v408 v412 v420 v421 v422 v423 v424 v427 v429 : Word}
    (t408 : v408.toNat = v170.toNat * 1125713234 % 2 ^ 32)
    (t412 : v412.toNat = v170.toNat * 1125713234 / 2 ^ 32)
    (t420 : v420.toNat = (v408.toNat + v374.toNat) % 2 ^ 32)
    (t422 : v420.toNat + 2 ^ 32 * v422.toNat = v408.toNat + v374.toNat)
    (t423 : v423.toNat = (v412.toNat + v422.toNat) % 2 ^ 32)
    (t427 : v424.toNat + 2 ^ 32 * v427.toNat = v420.toNat + v421.toNat)
    (t429 : v429.toNat = (v423.toNat + v427.toNat) % 2 ^ 32)
    (wP65 : v424.toNat + 2 ^ 32 * v429.toNat = v170.toNat * 1125713234 + v374.toNat + v421.toNat) :
    v429.toNat = (v424.toNat + 2 ^ 32 * v429.toNat) / 2 ^ 32 := by
  have := v170.isLt; have := v374.isLt; have := v408.isLt; have := v412.isLt; have := v420.isLt; have := v421.isLt; have := v422.isLt; have := v423.isLt; have := v424.isLt; have := v427.isLt; have := v429.isLt
  generalize v170.toNat = n170 at *
  generalize v374.toNat = n374 at *
  generalize v408.toNat = n408 at *
  generalize v412.toNat = n412 at *
  generalize v420.toNat = n420 at *
  generalize v421.toNat = n421 at *
  generalize v422.toNat = n422 at *
  generalize v423.toNat = n423 at *
  generalize v424.toNat = n424 at *
  generalize v427.toNat = n427 at *
  generalize v429.toNat = n429 at *
  first
    | omega
    | (obtain ⟨qt408, et408⟩ := mod_q t408; clear t408; obtain ⟨qt420, et420⟩ := mod_q t420; clear t420; obtain ⟨qt423, et423⟩ := mod_q t423; clear t423; obtain ⟨qt429, et429⟩ := mod_q t429; clear t429; omega)

theorem psm_v_P66 {v170 v380 v418 v425 v428 v429 v430 v431 v433 v435 : Word}
    (t418 : v418.toNat = v170.toNat * 4294967295 / 2 ^ 32 ∧ v418.toNat + (v170.toNat + 4294967295) / 4294967296 = v170.toNat)
    (t425 : v425.toNat = (v380.toNat + 2 ^ 32 - v170.toNat) % 2 ^ 32)
    (t428 : (v425.toNat < v380.toNat ∧ v428.toNat = 1) ∨ (v380.toNat ≤ v425.toNat ∧ v428.toNat = 0))
    (t430 : v430.toNat = (v428.toNat + v418.toNat) % 2 ^ 32)
    (t431 : v431.toNat = (v425.toNat + v429.toNat) % 2 ^ 32)
    (t433 : v431.toNat + 2 ^ 32 * v433.toNat = v425.toNat + v429.toNat)
    (t435 : v435.toNat = (v433.toNat + v430.toNat) % 2 ^ 32) :
    v431.toNat + 2 ^ 32 * v435.toNat = v170.toNat * 4294967295 + v380.toNat + v429.toNat := by
  have := v170.isLt; have := v380.isLt; have := v418.isLt; have := v425.isLt; have := v428.isLt; have := v429.isLt; have := v430.isLt; have := v431.isLt; have := v433.isLt; have := v435.isLt
  generalize v170.toNat = n170 at *
  generalize v380.toNat = n380 at *
  generalize v418.toNat = n418 at *
  generalize v425.toNat = n425 at *
  generalize v428.toNat = n428 at *
  generalize v429.toNat = n429 at *
  generalize v430.toNat = n430 at *
  generalize v431.toNat = n431 at *
  generalize v433.toNat = n433 at *
  generalize v435.toNat = n435 at *
  first
    | omega
    | (obtain ⟨t418a, t418b⟩ := t418; rcases Nat.eq_zero_or_pos n170 with _ | _ <;> rcases t428 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t418a, t418b⟩ := t418; obtain ⟨qt425, et425⟩ := mod_q t425; clear t425; obtain ⟨qt430, et430⟩ := mod_q t430; clear t430; obtain ⟨qt431, et431⟩ := mod_q t431; clear t431; omega)
    | (obtain ⟨t418a, t418b⟩ := t418; obtain ⟨qt425, et425⟩ := mod_q t425; clear t425; obtain ⟨qt430, et430⟩ := mod_q t430; clear t430; obtain ⟨qt431, et431⟩ := mod_q t431; clear t431; rcases Nat.eq_zero_or_pos n170 with _ | _ <;> rcases t428 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P66l {v170 v380 v425 v429 v431 v435 : Word}
    (t425 : v425.toNat = (v380.toNat + 2 ^ 32 - v170.toNat) % 2 ^ 32)
    (t431 : v431.toNat = (v425.toNat + v429.toNat) % 2 ^ 32)
    (wP66 : v431.toNat + 2 ^ 32 * v435.toNat = v170.toNat * 4294967295 + v380.toNat + v429.toNat) :
    v431.toNat = (v431.toNat + 2 ^ 32 * v435.toNat) % 2 ^ 32 := by
  have := v170.isLt; have := v380.isLt; have := v425.isLt; have := v429.isLt; have := v431.isLt; have := v435.isLt
  generalize v170.toNat = n170 at *
  generalize v380.toNat = n380 at *
  generalize v425.toNat = n425 at *
  generalize v429.toNat = n429 at *
  generalize v431.toNat = n431 at *
  generalize v435.toNat = n435 at *
  first
    | omega
    | (obtain ⟨qt425, et425⟩ := mod_q t425; clear t425; obtain ⟨qt431, et431⟩ := mod_q t431; clear t431; omega)

theorem psm_v_P66h {v170 v380 v418 v425 v428 v429 v430 v431 v433 v435 : Word}
    (t418 : v418.toNat = v170.toNat * 4294967295 / 2 ^ 32 ∧ v418.toNat + (v170.toNat + 4294967295) / 4294967296 = v170.toNat)
    (t425 : v425.toNat = (v380.toNat + 2 ^ 32 - v170.toNat) % 2 ^ 32)
    (t428 : (v425.toNat < v380.toNat ∧ v428.toNat = 1) ∨ (v380.toNat ≤ v425.toNat ∧ v428.toNat = 0))
    (t430 : v430.toNat = (v428.toNat + v418.toNat) % 2 ^ 32)
    (t433 : v431.toNat + 2 ^ 32 * v433.toNat = v425.toNat + v429.toNat)
    (t435 : v435.toNat = (v433.toNat + v430.toNat) % 2 ^ 32)
    (wP66 : v431.toNat + 2 ^ 32 * v435.toNat = v170.toNat * 4294967295 + v380.toNat + v429.toNat) :
    v435.toNat = (v431.toNat + 2 ^ 32 * v435.toNat) / 2 ^ 32 := by
  have := v170.isLt; have := v380.isLt; have := v418.isLt; have := v425.isLt; have := v428.isLt; have := v429.isLt; have := v430.isLt; have := v431.isLt; have := v433.isLt; have := v435.isLt
  generalize v170.toNat = n170 at *
  generalize v380.toNat = n380 at *
  generalize v418.toNat = n418 at *
  generalize v425.toNat = n425 at *
  generalize v428.toNat = n428 at *
  generalize v429.toNat = n429 at *
  generalize v430.toNat = n430 at *
  generalize v431.toNat = n431 at *
  generalize v433.toNat = n433 at *
  generalize v435.toNat = n435 at *
  first
    | omega
    | (obtain ⟨t418a, t418b⟩ := t418; rcases Nat.eq_zero_or_pos n170 with _ | _ <;> rcases t428 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t418a, t418b⟩ := t418; obtain ⟨qt425, et425⟩ := mod_q t425; clear t425; obtain ⟨qt430, et430⟩ := mod_q t430; clear t430; obtain ⟨qt435, et435⟩ := mod_q t435; clear t435; omega)
    | (obtain ⟨t418a, t418b⟩ := t418; obtain ⟨qt425, et425⟩ := mod_q t425; clear t425; obtain ⟨qt430, et430⟩ := mod_q t430; clear t430; obtain ⟨qt435, et435⟩ := mod_q t435; clear t435; rcases Nat.eq_zero_or_pos n170 with _ | _ <;> rcases t428 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P67 {v170 v386 v426 v432 v434 v435 v436 v437 v438 v439 v441 : Word}
    (t426 : v426.toNat = v170.toNat * 4294967294 / 2 ^ 32 ∧ v426.toNat + (2 * v170.toNat + 4294967295) / 4294967296 = v170.toNat)
    (t432 : v432.toNat = (v170.toNat + v170.toNat) % 2 ^ 32)
    (t434 : v434.toNat = (v386.toNat + 2 ^ 32 - v432.toNat) % 2 ^ 32)
    (t436 : (v434.toNat < v386.toNat ∧ v436.toNat = 1) ∨ (v386.toNat ≤ v434.toNat ∧ v436.toNat = 0))
    (t437 : v437.toNat = (v436.toNat + v426.toNat) % 2 ^ 32)
    (t438 : v438.toNat = (v434.toNat + v435.toNat) % 2 ^ 32)
    (t439 : v438.toNat + 2 ^ 32 * v439.toNat = v434.toNat + v435.toNat)
    (t441 : v441.toNat = (v439.toNat + v437.toNat) % 2 ^ 32) :
    v438.toNat + 2 ^ 32 * v441.toNat = v170.toNat * 4294967294 + v386.toNat + v435.toNat := by
  have := v170.isLt; have := v386.isLt; have := v426.isLt; have := v432.isLt; have := v434.isLt; have := v435.isLt; have := v436.isLt; have := v437.isLt; have := v438.isLt; have := v439.isLt; have := v441.isLt
  generalize v170.toNat = n170 at *
  generalize v386.toNat = n386 at *
  generalize v426.toNat = n426 at *
  generalize v432.toNat = n432 at *
  generalize v434.toNat = n434 at *
  generalize v435.toNat = n435 at *
  generalize v436.toNat = n436 at *
  generalize v437.toNat = n437 at *
  generalize v438.toNat = n438 at *
  generalize v439.toNat = n439 at *
  generalize v441.toNat = n441 at *
  first
    | omega
    | (obtain ⟨t426a, t426b⟩ := t426; rcases (by omega : n170 = 0 ∨ (0 < n170 ∧ n170 ≤ 2147483648) ∨ 2147483648 < n170) with _ | _ | _ <;> rcases t436 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t426a, t426b⟩ := t426; obtain ⟨qt432, et432⟩ := mod_q t432; clear t432; obtain ⟨qt434, et434⟩ := mod_q t434; clear t434; obtain ⟨qt437, et437⟩ := mod_q t437; clear t437; obtain ⟨qt438, et438⟩ := mod_q t438; clear t438; omega)
    | (obtain ⟨t426a, t426b⟩ := t426; obtain ⟨qt432, et432⟩ := mod_q t432; clear t432; obtain ⟨qt434, et434⟩ := mod_q t434; clear t434; obtain ⟨qt437, et437⟩ := mod_q t437; clear t437; obtain ⟨qt438, et438⟩ := mod_q t438; clear t438; rcases (by omega : n170 = 0 ∨ (0 < n170 ∧ n170 ≤ 2147483648) ∨ 2147483648 < n170) with _ | _ | _ <;> rcases t436 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P67l {v170 v386 v432 v434 v435 v438 v441 : Word}
    (t432 : v432.toNat = (v170.toNat + v170.toNat) % 2 ^ 32)
    (t434 : v434.toNat = (v386.toNat + 2 ^ 32 - v432.toNat) % 2 ^ 32)
    (t438 : v438.toNat = (v434.toNat + v435.toNat) % 2 ^ 32)
    (wP67 : v438.toNat + 2 ^ 32 * v441.toNat = v170.toNat * 4294967294 + v386.toNat + v435.toNat) :
    v438.toNat = (v438.toNat + 2 ^ 32 * v441.toNat) % 2 ^ 32 := by
  have := v170.isLt; have := v386.isLt; have := v432.isLt; have := v434.isLt; have := v435.isLt; have := v438.isLt; have := v441.isLt
  generalize v170.toNat = n170 at *
  generalize v386.toNat = n386 at *
  generalize v432.toNat = n432 at *
  generalize v434.toNat = n434 at *
  generalize v435.toNat = n435 at *
  generalize v438.toNat = n438 at *
  generalize v441.toNat = n441 at *
  first
    | omega
    | (obtain ⟨qt432, et432⟩ := mod_q t432; clear t432; obtain ⟨qt434, et434⟩ := mod_q t434; clear t434; obtain ⟨qt438, et438⟩ := mod_q t438; clear t438; omega)

theorem psm_v_P67h {v170 v386 v426 v432 v434 v435 v436 v437 v438 v439 v441 : Word}
    (t426 : v426.toNat = v170.toNat * 4294967294 / 2 ^ 32 ∧ v426.toNat + (2 * v170.toNat + 4294967295) / 4294967296 = v170.toNat)
    (t432 : v432.toNat = (v170.toNat + v170.toNat) % 2 ^ 32)
    (t434 : v434.toNat = (v386.toNat + 2 ^ 32 - v432.toNat) % 2 ^ 32)
    (t436 : (v434.toNat < v386.toNat ∧ v436.toNat = 1) ∨ (v386.toNat ≤ v434.toNat ∧ v436.toNat = 0))
    (t437 : v437.toNat = (v436.toNat + v426.toNat) % 2 ^ 32)
    (t439 : v438.toNat + 2 ^ 32 * v439.toNat = v434.toNat + v435.toNat)
    (t441 : v441.toNat = (v439.toNat + v437.toNat) % 2 ^ 32)
    (wP67 : v438.toNat + 2 ^ 32 * v441.toNat = v170.toNat * 4294967294 + v386.toNat + v435.toNat) :
    v441.toNat = (v438.toNat + 2 ^ 32 * v441.toNat) / 2 ^ 32 := by
  have := v170.isLt; have := v386.isLt; have := v426.isLt; have := v432.isLt; have := v434.isLt; have := v435.isLt; have := v436.isLt; have := v437.isLt; have := v438.isLt; have := v439.isLt; have := v441.isLt
  generalize v170.toNat = n170 at *
  generalize v386.toNat = n386 at *
  generalize v426.toNat = n426 at *
  generalize v432.toNat = n432 at *
  generalize v434.toNat = n434 at *
  generalize v435.toNat = n435 at *
  generalize v436.toNat = n436 at *
  generalize v437.toNat = n437 at *
  generalize v438.toNat = n438 at *
  generalize v439.toNat = n439 at *
  generalize v441.toNat = n441 at *
  first
    | omega
    | (obtain ⟨t426a, t426b⟩ := t426; rcases (by omega : n170 = 0 ∨ (0 < n170 ∧ n170 ≤ 2147483648) ∨ 2147483648 < n170) with _ | _ | _ <;> rcases t436 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t426a, t426b⟩ := t426; obtain ⟨qt432, et432⟩ := mod_q t432; clear t432; obtain ⟨qt434, et434⟩ := mod_q t434; clear t434; obtain ⟨qt437, et437⟩ := mod_q t437; clear t437; obtain ⟨qt441, et441⟩ := mod_q t441; clear t441; omega)
    | (obtain ⟨t426a, t426b⟩ := t426; obtain ⟨qt432, et432⟩ := mod_q t432; clear t432; obtain ⟨qt434, et434⟩ := mod_q t434; clear t434; obtain ⟨qt437, et437⟩ := mod_q t437; clear t437; obtain ⟨qt441, et441⟩ := mod_q t441; clear t441; rcases (by omega : n170 = 0 ∨ (0 < n170 ∧ n170 ≤ 2147483648) ∨ 2147483648 < n170) with _ | _ | _ <;> rcases t436 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P68 {v170 v391 v418 v440 v441 v442 v443 v444 v445 v448 : Word}
    (t418 : v418.toNat = v170.toNat * 4294967295 / 2 ^ 32 ∧ v418.toNat + (v170.toNat + 4294967295) / 4294967296 = v170.toNat)
    (t440 : v440.toNat = (v391.toNat + 2 ^ 32 - v170.toNat) % 2 ^ 32)
    (t442 : (v440.toNat < v391.toNat ∧ v442.toNat = 1) ∨ (v391.toNat ≤ v440.toNat ∧ v442.toNat = 0))
    (t443 : v443.toNat = (v418.toNat + v442.toNat) % 2 ^ 32)
    (t444 : v444.toNat = (v440.toNat + v441.toNat) % 2 ^ 32)
    (t445 : v444.toNat + 2 ^ 32 * v445.toNat = v440.toNat + v441.toNat)
    (t448 : v448.toNat = (v443.toNat + v445.toNat) % 2 ^ 32) :
    v444.toNat + 2 ^ 32 * v448.toNat = v170.toNat * 4294967295 + v391.toNat + v441.toNat := by
  have := v170.isLt; have := v391.isLt; have := v418.isLt; have := v440.isLt; have := v441.isLt; have := v442.isLt; have := v443.isLt; have := v444.isLt; have := v445.isLt; have := v448.isLt
  generalize v170.toNat = n170 at *
  generalize v391.toNat = n391 at *
  generalize v418.toNat = n418 at *
  generalize v440.toNat = n440 at *
  generalize v441.toNat = n441 at *
  generalize v442.toNat = n442 at *
  generalize v443.toNat = n443 at *
  generalize v444.toNat = n444 at *
  generalize v445.toNat = n445 at *
  generalize v448.toNat = n448 at *
  first
    | omega
    | (obtain ⟨t418a, t418b⟩ := t418; rcases Nat.eq_zero_or_pos n170 with _ | _ <;> rcases t442 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t418a, t418b⟩ := t418; obtain ⟨qt440, et440⟩ := mod_q t440; clear t440; obtain ⟨qt443, et443⟩ := mod_q t443; clear t443; obtain ⟨qt444, et444⟩ := mod_q t444; clear t444; omega)
    | (obtain ⟨t418a, t418b⟩ := t418; obtain ⟨qt440, et440⟩ := mod_q t440; clear t440; obtain ⟨qt443, et443⟩ := mod_q t443; clear t443; obtain ⟨qt444, et444⟩ := mod_q t444; clear t444; rcases Nat.eq_zero_or_pos n170 with _ | _ <;> rcases t442 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P68l {v170 v391 v440 v441 v444 v448 : Word}
    (t440 : v440.toNat = (v391.toNat + 2 ^ 32 - v170.toNat) % 2 ^ 32)
    (t444 : v444.toNat = (v440.toNat + v441.toNat) % 2 ^ 32)
    (wP68 : v444.toNat + 2 ^ 32 * v448.toNat = v170.toNat * 4294967295 + v391.toNat + v441.toNat) :
    v444.toNat = (v444.toNat + 2 ^ 32 * v448.toNat) % 2 ^ 32 := by
  have := v170.isLt; have := v391.isLt; have := v440.isLt; have := v441.isLt; have := v444.isLt; have := v448.isLt
  generalize v170.toNat = n170 at *
  generalize v391.toNat = n391 at *
  generalize v440.toNat = n440 at *
  generalize v441.toNat = n441 at *
  generalize v444.toNat = n444 at *
  generalize v448.toNat = n448 at *
  first
    | omega
    | (obtain ⟨qt440, et440⟩ := mod_q t440; clear t440; obtain ⟨qt444, et444⟩ := mod_q t444; clear t444; omega)

theorem psm_v_P68h {v170 v391 v418 v440 v441 v442 v443 v444 v445 v448 : Word}
    (t418 : v418.toNat = v170.toNat * 4294967295 / 2 ^ 32 ∧ v418.toNat + (v170.toNat + 4294967295) / 4294967296 = v170.toNat)
    (t440 : v440.toNat = (v391.toNat + 2 ^ 32 - v170.toNat) % 2 ^ 32)
    (t442 : (v440.toNat < v391.toNat ∧ v442.toNat = 1) ∨ (v391.toNat ≤ v440.toNat ∧ v442.toNat = 0))
    (t443 : v443.toNat = (v418.toNat + v442.toNat) % 2 ^ 32)
    (t445 : v444.toNat + 2 ^ 32 * v445.toNat = v440.toNat + v441.toNat)
    (t448 : v448.toNat = (v443.toNat + v445.toNat) % 2 ^ 32)
    (wP68 : v444.toNat + 2 ^ 32 * v448.toNat = v170.toNat * 4294967295 + v391.toNat + v441.toNat) :
    v448.toNat = (v444.toNat + 2 ^ 32 * v448.toNat) / 2 ^ 32 := by
  have := v170.isLt; have := v391.isLt; have := v418.isLt; have := v440.isLt; have := v441.isLt; have := v442.isLt; have := v443.isLt; have := v444.isLt; have := v445.isLt; have := v448.isLt
  generalize v170.toNat = n170 at *
  generalize v391.toNat = n391 at *
  generalize v418.toNat = n418 at *
  generalize v440.toNat = n440 at *
  generalize v441.toNat = n441 at *
  generalize v442.toNat = n442 at *
  generalize v443.toNat = n443 at *
  generalize v444.toNat = n444 at *
  generalize v445.toNat = n445 at *
  generalize v448.toNat = n448 at *
  first
    | omega
    | (obtain ⟨t418a, t418b⟩ := t418; rcases Nat.eq_zero_or_pos n170 with _ | _ <;> rcases t442 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t418a, t418b⟩ := t418; obtain ⟨qt440, et440⟩ := mod_q t440; clear t440; obtain ⟨qt443, et443⟩ := mod_q t443; clear t443; obtain ⟨qt448, et448⟩ := mod_q t448; clear t448; omega)
    | (obtain ⟨t418a, t418b⟩ := t418; obtain ⟨qt440, et440⟩ := mod_q t440; clear t440; obtain ⟨qt443, et443⟩ := mod_q t443; clear t443; obtain ⟨qt448, et448⟩ := mod_q t448; clear t448; rcases Nat.eq_zero_or_pos n170 with _ | _ <;> rcases t442 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_S69 {v397 v448 v449 v453 : Word}
    (t449 : v449.toNat = (v448.toNat + v397.toNat) % 2 ^ 32)
    (t453 : v449.toNat + 2 ^ 32 * v453.toNat = v448.toNat + v397.toNat) :
    v449.toNat + 2 ^ 32 * v453.toNat = v397.toNat + v448.toNat := by
  have := v397.isLt; have := v448.isLt; have := v449.isLt; have := v453.isLt
  generalize v397.toNat = n397 at *
  generalize v448.toNat = n448 at *
  generalize v449.toNat = n449 at *
  generalize v453.toNat = n453 at *
  first
    | omega
    | (obtain ⟨qt449, et449⟩ := mod_q t449; clear t449; omega)

theorem psm_v_S69l {v397 v448 v449 v453 : Word}
    (t449 : v449.toNat = (v448.toNat + v397.toNat) % 2 ^ 32)
    (wS69 : v449.toNat + 2 ^ 32 * v453.toNat = v397.toNat + v448.toNat) :
    v449.toNat = (v449.toNat + 2 ^ 32 * v453.toNat) % 2 ^ 32 := by
  have := v397.isLt; have := v448.isLt; have := v449.isLt; have := v453.isLt
  generalize v397.toNat = n397 at *
  generalize v448.toNat = n448 at *
  generalize v449.toNat = n449 at *
  generalize v453.toNat = n453 at *
  first
    | omega
    | (obtain ⟨qt449, et449⟩ := mod_q t449; clear t449; omega)

theorem psm_v_S69h {v397 v448 v449 v453 : Word}
    (t453 : v449.toNat + 2 ^ 32 * v453.toNat = v448.toNat + v397.toNat)
    (wS69 : v449.toNat + 2 ^ 32 * v453.toNat = v397.toNat + v448.toNat) :
    v453.toNat = (v449.toNat + 2 ^ 32 * v453.toNat) / 2 ^ 32 := by
  have := v397.isLt; have := v448.isLt; have := v449.isLt; have := v453.isLt
  generalize v397.toNat = n397 at *
  generalize v448.toNat = n448 at *
  generalize v449.toNat = n449 at *
  generalize v453.toNat = n453 at *
  omega

theorem psm_v_S70 {v170 v447 v451 v453 v454 v459 v503 v505 : Word}
    (t451 : v451.toNat = (v170.toNat + v447.toNat) % 2 ^ 32)
    (t454 : v451.toNat + 2 ^ 32 * v454.toNat = v170.toNat + v447.toNat)
    (t459 : v459.toNat = (v453.toNat + v451.toNat) % 2 ^ 32)
    (t503 : v459.toNat + 2 ^ 32 * v503.toNat = v453.toNat + v451.toNat)
    (t505 : v505.toNat = (v503.toNat + v454.toNat) % 2 ^ 32) :
    v459.toNat + 2 ^ 32 * v505.toNat = v447.toNat + v170.toNat + v453.toNat := by
  have := v170.isLt; have := v447.isLt; have := v451.isLt; have := v453.isLt; have := v454.isLt; have := v459.isLt; have := v503.isLt; have := v505.isLt
  generalize v170.toNat = n170 at *
  generalize v447.toNat = n447 at *
  generalize v451.toNat = n451 at *
  generalize v453.toNat = n453 at *
  generalize v454.toNat = n454 at *
  generalize v459.toNat = n459 at *
  generalize v503.toNat = n503 at *
  generalize v505.toNat = n505 at *
  first
    | omega
    | (obtain ⟨qt451, et451⟩ := mod_q t451; clear t451; obtain ⟨qt459, et459⟩ := mod_q t459; clear t459; omega)

theorem psm_v_S70l {v170 v447 v451 v453 v459 v505 : Word}
    (t451 : v451.toNat = (v170.toNat + v447.toNat) % 2 ^ 32)
    (t459 : v459.toNat = (v453.toNat + v451.toNat) % 2 ^ 32)
    (wS70 : v459.toNat + 2 ^ 32 * v505.toNat = v447.toNat + v170.toNat + v453.toNat) :
    v459.toNat = (v459.toNat + 2 ^ 32 * v505.toNat) % 2 ^ 32 := by
  have := v170.isLt; have := v447.isLt; have := v451.isLt; have := v453.isLt; have := v459.isLt; have := v505.isLt
  generalize v170.toNat = n170 at *
  generalize v447.toNat = n447 at *
  generalize v451.toNat = n451 at *
  generalize v453.toNat = n453 at *
  generalize v459.toNat = n459 at *
  generalize v505.toNat = n505 at *
  first
    | omega
    | (obtain ⟨qt451, et451⟩ := mod_q t451; clear t451; obtain ⟨qt459, et459⟩ := mod_q t459; clear t459; omega)

theorem psm_v_S70h {v170 v447 v451 v453 v454 v459 v503 v505 : Word}
    (t451 : v451.toNat = (v170.toNat + v447.toNat) % 2 ^ 32)
    (t454 : v451.toNat + 2 ^ 32 * v454.toNat = v170.toNat + v447.toNat)
    (t503 : v459.toNat + 2 ^ 32 * v503.toNat = v453.toNat + v451.toNat)
    (t505 : v505.toNat = (v503.toNat + v454.toNat) % 2 ^ 32)
    (wS70 : v459.toNat + 2 ^ 32 * v505.toNat = v447.toNat + v170.toNat + v453.toNat) :
    v505.toNat = (v459.toNat + 2 ^ 32 * v505.toNat) / 2 ^ 32 := by
  have := v170.isLt; have := v447.isLt; have := v451.isLt; have := v453.isLt; have := v454.isLt; have := v459.isLt; have := v503.isLt; have := v505.isLt
  generalize v170.toNat = n170 at *
  generalize v447.toNat = n447 at *
  generalize v451.toNat = n451 at *
  generalize v453.toNat = n453 at *
  generalize v454.toNat = n454 at *
  generalize v459.toNat = n459 at *
  generalize v503.toNat = n503 at *
  generalize v505.toNat = n505 at *
  first
    | omega
    | (obtain ⟨qt451, et451⟩ := mod_q t451; clear t451; obtain ⟨qt505, et505⟩ := mod_q t505; clear t505; omega)

theorem psm_v_P71h {v171 v410 v446 v452 v455 v457 v460 v463 : Word}
    (t446 : v446.toNat = v171.toNat * 4007631870 % 2 ^ 32)
    (t452 : v452.toNat = v171.toNat * 4007631870 / 2 ^ 32)
    (t455 : v455.toNat = v410.toNat / 2 * 2)
    (t457 : v457.toNat = (v446.toNat + v455.toNat) % 2 ^ 32)
    (t460 : v457.toNat + 2 ^ 32 * v460.toNat = v446.toNat + v455.toNat)
    (t463 : v463.toNat = (v460.toNat + v452.toNat) % 2 ^ 32) :
    v463.toNat = (v171.toNat * 4007631870 + v410.toNat) / 2 ^ 32 := by
  have := v171.isLt; have := v410.isLt; have := v446.isLt; have := v452.isLt; have := v455.isLt; have := v457.isLt; have := v460.isLt; have := v463.isLt
  generalize v171.toNat = n171 at *
  generalize v410.toNat = n410 at *
  generalize v446.toNat = n446 at *
  generalize v452.toNat = n452 at *
  generalize v455.toNat = n455 at *
  generalize v457.toNat = n457 at *
  generalize v460.toNat = n460 at *
  generalize v463.toNat = n463 at *
  first
    | omega
    | (obtain ⟨qt446, et446⟩ := mod_q t446; clear t446; obtain ⟨qt457, et457⟩ := mod_q t457; clear t457; omega)

theorem psm_v_P72 {v171 v417 v450 v456 v461 v463 v464 v465 v467 v468 v471 : Word}
    (t450 : v450.toNat = v171.toNat * 19922309 % 2 ^ 32)
    (t456 : v456.toNat = v171.toNat * 19922309 / 2 ^ 32)
    (t461 : v461.toNat = (v450.toNat + v417.toNat) % 2 ^ 32)
    (t464 : v461.toNat + 2 ^ 32 * v464.toNat = v450.toNat + v417.toNat)
    (t465 : v465.toNat = (v461.toNat + v463.toNat) % 2 ^ 32)
    (t467 : v467.toNat = (v464.toNat + v456.toNat) % 2 ^ 32)
    (t468 : v465.toNat + 2 ^ 32 * v468.toNat = v461.toNat + v463.toNat)
    (t471 : v471.toNat = (v468.toNat + v467.toNat) % 2 ^ 32) :
    v465.toNat + 2 ^ 32 * v471.toNat = v171.toNat * 19922309 + v417.toNat + v463.toNat := by
  have := v171.isLt; have := v417.isLt; have := v450.isLt; have := v456.isLt; have := v461.isLt; have := v463.isLt; have := v464.isLt; have := v465.isLt; have := v467.isLt; have := v468.isLt; have := v471.isLt
  generalize v171.toNat = n171 at *
  generalize v417.toNat = n417 at *
  generalize v450.toNat = n450 at *
  generalize v456.toNat = n456 at *
  generalize v461.toNat = n461 at *
  generalize v463.toNat = n463 at *
  generalize v464.toNat = n464 at *
  generalize v465.toNat = n465 at *
  generalize v467.toNat = n467 at *
  generalize v468.toNat = n468 at *
  generalize v471.toNat = n471 at *
  first
    | omega
    | (obtain ⟨qt450, et450⟩ := mod_q t450; clear t450; obtain ⟨qt461, et461⟩ := mod_q t461; clear t461; obtain ⟨qt465, et465⟩ := mod_q t465; clear t465; obtain ⟨qt467, et467⟩ := mod_q t467; clear t467; omega)

theorem psm_v_P72l {v171 v417 v450 v461 v463 v465 v471 : Word}
    (t450 : v450.toNat = v171.toNat * 19922309 % 2 ^ 32)
    (t461 : v461.toNat = (v450.toNat + v417.toNat) % 2 ^ 32)
    (t465 : v465.toNat = (v461.toNat + v463.toNat) % 2 ^ 32)
    (wP72 : v465.toNat + 2 ^ 32 * v471.toNat = v171.toNat * 19922309 + v417.toNat + v463.toNat) :
    v465.toNat = (v465.toNat + 2 ^ 32 * v471.toNat) % 2 ^ 32 := by
  have := v171.isLt; have := v417.isLt; have := v450.isLt; have := v461.isLt; have := v463.isLt; have := v465.isLt; have := v471.isLt
  generalize v171.toNat = n171 at *
  generalize v417.toNat = n417 at *
  generalize v450.toNat = n450 at *
  generalize v461.toNat = n461 at *
  generalize v463.toNat = n463 at *
  generalize v465.toNat = n465 at *
  generalize v471.toNat = n471 at *
  first
    | omega
    | (obtain ⟨qt450, et450⟩ := mod_q t450; clear t450; obtain ⟨qt461, et461⟩ := mod_q t461; clear t461; obtain ⟨qt465, et465⟩ := mod_q t465; clear t465; omega)

theorem psm_v_P72h {v171 v417 v450 v456 v461 v463 v464 v465 v467 v468 v471 : Word}
    (t450 : v450.toNat = v171.toNat * 19922309 % 2 ^ 32)
    (t456 : v456.toNat = v171.toNat * 19922309 / 2 ^ 32)
    (t461 : v461.toNat = (v450.toNat + v417.toNat) % 2 ^ 32)
    (t464 : v461.toNat + 2 ^ 32 * v464.toNat = v450.toNat + v417.toNat)
    (t467 : v467.toNat = (v464.toNat + v456.toNat) % 2 ^ 32)
    (t468 : v465.toNat + 2 ^ 32 * v468.toNat = v461.toNat + v463.toNat)
    (t471 : v471.toNat = (v468.toNat + v467.toNat) % 2 ^ 32)
    (wP72 : v465.toNat + 2 ^ 32 * v471.toNat = v171.toNat * 19922309 + v417.toNat + v463.toNat) :
    v471.toNat = (v465.toNat + 2 ^ 32 * v471.toNat) / 2 ^ 32 := by
  have := v171.isLt; have := v417.isLt; have := v450.isLt; have := v456.isLt; have := v461.isLt; have := v463.isLt; have := v464.isLt; have := v465.isLt; have := v467.isLt; have := v468.isLt; have := v471.isLt
  generalize v171.toNat = n171 at *
  generalize v417.toNat = n417 at *
  generalize v450.toNat = n450 at *
  generalize v456.toNat = n456 at *
  generalize v461.toNat = n461 at *
  generalize v463.toNat = n463 at *
  generalize v464.toNat = n464 at *
  generalize v465.toNat = n465 at *
  generalize v467.toNat = n467 at *
  generalize v468.toNat = n468 at *
  generalize v471.toNat = n471 at *
  first
    | omega
    | (obtain ⟨qt450, et450⟩ := mod_q t450; clear t450; obtain ⟨qt461, et461⟩ := mod_q t461; clear t461; obtain ⟨qt467, et467⟩ := mod_q t467; clear t467; obtain ⟨qt471, et471⟩ := mod_q t471; clear t471; omega)

theorem psm_v_P73 {v171 v424 v458 v462 v469 v471 v472 v473 v474 v475 v477 : Word}
    (t458 : v458.toNat = v171.toNat * 3743050785 % 2 ^ 32)
    (t462 : v462.toNat = v171.toNat * 3743050785 / 2 ^ 32)
    (t469 : v469.toNat = (v458.toNat + v424.toNat) % 2 ^ 32)
    (t472 : v469.toNat + 2 ^ 32 * v472.toNat = v458.toNat + v424.toNat)
    (t473 : v473.toNat = (v472.toNat + v462.toNat) % 2 ^ 32)
    (t474 : v474.toNat = (v471.toNat + v469.toNat) % 2 ^ 32)
    (t475 : v474.toNat + 2 ^ 32 * v475.toNat = v471.toNat + v469.toNat)
    (t477 : v477.toNat = (v473.toNat + v475.toNat) % 2 ^ 32) :
    v474.toNat + 2 ^ 32 * v477.toNat = v171.toNat * 3743050785 + v424.toNat + v471.toNat := by
  have := v171.isLt; have := v424.isLt; have := v458.isLt; have := v462.isLt; have := v469.isLt; have := v471.isLt; have := v472.isLt; have := v473.isLt; have := v474.isLt; have := v475.isLt; have := v477.isLt
  generalize v171.toNat = n171 at *
  generalize v424.toNat = n424 at *
  generalize v458.toNat = n458 at *
  generalize v462.toNat = n462 at *
  generalize v469.toNat = n469 at *
  generalize v471.toNat = n471 at *
  generalize v472.toNat = n472 at *
  generalize v473.toNat = n473 at *
  generalize v474.toNat = n474 at *
  generalize v475.toNat = n475 at *
  generalize v477.toNat = n477 at *
  first
    | omega
    | (obtain ⟨qt458, et458⟩ := mod_q t458; clear t458; obtain ⟨qt469, et469⟩ := mod_q t469; clear t469; obtain ⟨qt473, et473⟩ := mod_q t473; clear t473; obtain ⟨qt474, et474⟩ := mod_q t474; clear t474; omega)

theorem psm_v_P73l {v171 v424 v458 v469 v471 v474 v477 : Word}
    (t458 : v458.toNat = v171.toNat * 3743050785 % 2 ^ 32)
    (t469 : v469.toNat = (v458.toNat + v424.toNat) % 2 ^ 32)
    (t474 : v474.toNat = (v471.toNat + v469.toNat) % 2 ^ 32)
    (wP73 : v474.toNat + 2 ^ 32 * v477.toNat = v171.toNat * 3743050785 + v424.toNat + v471.toNat) :
    v474.toNat = (v474.toNat + 2 ^ 32 * v477.toNat) % 2 ^ 32 := by
  have := v171.isLt; have := v424.isLt; have := v458.isLt; have := v469.isLt; have := v471.isLt; have := v474.isLt; have := v477.isLt
  generalize v171.toNat = n171 at *
  generalize v424.toNat = n424 at *
  generalize v458.toNat = n458 at *
  generalize v469.toNat = n469 at *
  generalize v471.toNat = n471 at *
  generalize v474.toNat = n474 at *
  generalize v477.toNat = n477 at *
  first
    | omega
    | (obtain ⟨qt458, et458⟩ := mod_q t458; clear t458; obtain ⟨qt469, et469⟩ := mod_q t469; clear t469; obtain ⟨qt474, et474⟩ := mod_q t474; clear t474; omega)

theorem psm_v_P73h {v171 v424 v458 v462 v469 v471 v472 v473 v474 v475 v477 : Word}
    (t458 : v458.toNat = v171.toNat * 3743050785 % 2 ^ 32)
    (t462 : v462.toNat = v171.toNat * 3743050785 / 2 ^ 32)
    (t469 : v469.toNat = (v458.toNat + v424.toNat) % 2 ^ 32)
    (t472 : v469.toNat + 2 ^ 32 * v472.toNat = v458.toNat + v424.toNat)
    (t473 : v473.toNat = (v472.toNat + v462.toNat) % 2 ^ 32)
    (t475 : v474.toNat + 2 ^ 32 * v475.toNat = v471.toNat + v469.toNat)
    (t477 : v477.toNat = (v473.toNat + v475.toNat) % 2 ^ 32)
    (wP73 : v474.toNat + 2 ^ 32 * v477.toNat = v171.toNat * 3743050785 + v424.toNat + v471.toNat) :
    v477.toNat = (v474.toNat + 2 ^ 32 * v477.toNat) / 2 ^ 32 := by
  have := v171.isLt; have := v424.isLt; have := v458.isLt; have := v462.isLt; have := v469.isLt; have := v471.isLt; have := v472.isLt; have := v473.isLt; have := v474.isLt; have := v475.isLt; have := v477.isLt
  generalize v171.toNat = n171 at *
  generalize v424.toNat = n424 at *
  generalize v458.toNat = n458 at *
  generalize v462.toNat = n462 at *
  generalize v469.toNat = n469 at *
  generalize v471.toNat = n471 at *
  generalize v472.toNat = n472 at *
  generalize v473.toNat = n473 at *
  generalize v474.toNat = n474 at *
  generalize v475.toNat = n475 at *
  generalize v477.toNat = n477 at *
  first
    | omega
    | (obtain ⟨qt458, et458⟩ := mod_q t458; clear t458; obtain ⟨qt469, et469⟩ := mod_q t469; clear t469; obtain ⟨qt473, et473⟩ := mod_q t473; clear t473; obtain ⟨qt477, et477⟩ := mod_q t477; clear t477; omega)

theorem psm_v_P74 {v171 v431 v466 v470 v477 v478 v479 v480 v481 v482 v485 : Word}
    (t466 : v466.toNat = v171.toNat * 1125713234 % 2 ^ 32)
    (t470 : v470.toNat = v171.toNat * 1125713234 / 2 ^ 32)
    (t478 : v478.toNat = (v466.toNat + v431.toNat) % 2 ^ 32)
    (t479 : v478.toNat + 2 ^ 32 * v479.toNat = v466.toNat + v431.toNat)
    (t480 : v480.toNat = (v478.toNat + v477.toNat) % 2 ^ 32)
    (t481 : v481.toNat = (v470.toNat + v479.toNat) % 2 ^ 32)
    (t482 : v480.toNat + 2 ^ 32 * v482.toNat = v478.toNat + v477.toNat)
    (t485 : v485.toNat = (v481.toNat + v482.toNat) % 2 ^ 32) :
    v480.toNat + 2 ^ 32 * v485.toNat = v171.toNat * 1125713234 + v431.toNat + v477.toNat := by
  have := v171.isLt; have := v431.isLt; have := v466.isLt; have := v470.isLt; have := v477.isLt; have := v478.isLt; have := v479.isLt; have := v480.isLt; have := v481.isLt; have := v482.isLt; have := v485.isLt
  generalize v171.toNat = n171 at *
  generalize v431.toNat = n431 at *
  generalize v466.toNat = n466 at *
  generalize v470.toNat = n470 at *
  generalize v477.toNat = n477 at *
  generalize v478.toNat = n478 at *
  generalize v479.toNat = n479 at *
  generalize v480.toNat = n480 at *
  generalize v481.toNat = n481 at *
  generalize v482.toNat = n482 at *
  generalize v485.toNat = n485 at *
  first
    | omega
    | (obtain ⟨qt466, et466⟩ := mod_q t466; clear t466; obtain ⟨qt478, et478⟩ := mod_q t478; clear t478; obtain ⟨qt480, et480⟩ := mod_q t480; clear t480; obtain ⟨qt481, et481⟩ := mod_q t481; clear t481; omega)

theorem psm_v_P74l {v171 v431 v466 v477 v478 v480 v485 : Word}
    (t466 : v466.toNat = v171.toNat * 1125713234 % 2 ^ 32)
    (t478 : v478.toNat = (v466.toNat + v431.toNat) % 2 ^ 32)
    (t480 : v480.toNat = (v478.toNat + v477.toNat) % 2 ^ 32)
    (wP74 : v480.toNat + 2 ^ 32 * v485.toNat = v171.toNat * 1125713234 + v431.toNat + v477.toNat) :
    v480.toNat = (v480.toNat + 2 ^ 32 * v485.toNat) % 2 ^ 32 := by
  have := v171.isLt; have := v431.isLt; have := v466.isLt; have := v477.isLt; have := v478.isLt; have := v480.isLt; have := v485.isLt
  generalize v171.toNat = n171 at *
  generalize v431.toNat = n431 at *
  generalize v466.toNat = n466 at *
  generalize v477.toNat = n477 at *
  generalize v478.toNat = n478 at *
  generalize v480.toNat = n480 at *
  generalize v485.toNat = n485 at *
  first
    | omega
    | (obtain ⟨qt466, et466⟩ := mod_q t466; clear t466; obtain ⟨qt478, et478⟩ := mod_q t478; clear t478; obtain ⟨qt480, et480⟩ := mod_q t480; clear t480; omega)

theorem psm_v_P74h {v171 v431 v466 v470 v477 v478 v479 v480 v481 v482 v485 : Word}
    (t466 : v466.toNat = v171.toNat * 1125713234 % 2 ^ 32)
    (t470 : v470.toNat = v171.toNat * 1125713234 / 2 ^ 32)
    (t478 : v478.toNat = (v466.toNat + v431.toNat) % 2 ^ 32)
    (t479 : v478.toNat + 2 ^ 32 * v479.toNat = v466.toNat + v431.toNat)
    (t481 : v481.toNat = (v470.toNat + v479.toNat) % 2 ^ 32)
    (t482 : v480.toNat + 2 ^ 32 * v482.toNat = v478.toNat + v477.toNat)
    (t485 : v485.toNat = (v481.toNat + v482.toNat) % 2 ^ 32)
    (wP74 : v480.toNat + 2 ^ 32 * v485.toNat = v171.toNat * 1125713234 + v431.toNat + v477.toNat) :
    v485.toNat = (v480.toNat + 2 ^ 32 * v485.toNat) / 2 ^ 32 := by
  have := v171.isLt; have := v431.isLt; have := v466.isLt; have := v470.isLt; have := v477.isLt; have := v478.isLt; have := v479.isLt; have := v480.isLt; have := v481.isLt; have := v482.isLt; have := v485.isLt
  generalize v171.toNat = n171 at *
  generalize v431.toNat = n431 at *
  generalize v466.toNat = n466 at *
  generalize v470.toNat = n470 at *
  generalize v477.toNat = n477 at *
  generalize v478.toNat = n478 at *
  generalize v479.toNat = n479 at *
  generalize v480.toNat = n480 at *
  generalize v481.toNat = n481 at *
  generalize v482.toNat = n482 at *
  generalize v485.toNat = n485 at *
  first
    | omega
    | (obtain ⟨qt466, et466⟩ := mod_q t466; clear t466; obtain ⟨qt478, et478⟩ := mod_q t478; clear t478; obtain ⟨qt481, et481⟩ := mod_q t481; clear t481; obtain ⟨qt485, et485⟩ := mod_q t485; clear t485; omega)

theorem psm_v_P75 {v171 v438 v476 v483 v485 v486 v487 v488 v489 v491 : Word}
    (t476 : v476.toNat = v171.toNat * 4294967295 / 2 ^ 32 ∧ v476.toNat + (v171.toNat + 4294967295) / 4294967296 = v171.toNat)
    (t483 : v483.toNat = (v438.toNat + 2 ^ 32 - v171.toNat) % 2 ^ 32)
    (t486 : (v483.toNat < v438.toNat ∧ v486.toNat = 1) ∨ (v438.toNat ≤ v483.toNat ∧ v486.toNat = 0))
    (t487 : v487.toNat = (v486.toNat + v476.toNat) % 2 ^ 32)
    (t488 : v488.toNat = (v483.toNat + v485.toNat) % 2 ^ 32)
    (t489 : v488.toNat + 2 ^ 32 * v489.toNat = v483.toNat + v485.toNat)
    (t491 : v491.toNat = (v487.toNat + v489.toNat) % 2 ^ 32) :
    v488.toNat + 2 ^ 32 * v491.toNat = v171.toNat * 4294967295 + v438.toNat + v485.toNat := by
  have := v171.isLt; have := v438.isLt; have := v476.isLt; have := v483.isLt; have := v485.isLt; have := v486.isLt; have := v487.isLt; have := v488.isLt; have := v489.isLt; have := v491.isLt
  generalize v171.toNat = n171 at *
  generalize v438.toNat = n438 at *
  generalize v476.toNat = n476 at *
  generalize v483.toNat = n483 at *
  generalize v485.toNat = n485 at *
  generalize v486.toNat = n486 at *
  generalize v487.toNat = n487 at *
  generalize v488.toNat = n488 at *
  generalize v489.toNat = n489 at *
  generalize v491.toNat = n491 at *
  first
    | omega
    | (obtain ⟨t476a, t476b⟩ := t476; rcases Nat.eq_zero_or_pos n171 with _ | _ <;> rcases t486 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t476a, t476b⟩ := t476; obtain ⟨qt483, et483⟩ := mod_q t483; clear t483; obtain ⟨qt487, et487⟩ := mod_q t487; clear t487; obtain ⟨qt488, et488⟩ := mod_q t488; clear t488; omega)
    | (obtain ⟨t476a, t476b⟩ := t476; obtain ⟨qt483, et483⟩ := mod_q t483; clear t483; obtain ⟨qt487, et487⟩ := mod_q t487; clear t487; obtain ⟨qt488, et488⟩ := mod_q t488; clear t488; rcases Nat.eq_zero_or_pos n171 with _ | _ <;> rcases t486 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P75l {v171 v438 v483 v485 v488 v491 : Word}
    (t483 : v483.toNat = (v438.toNat + 2 ^ 32 - v171.toNat) % 2 ^ 32)
    (t488 : v488.toNat = (v483.toNat + v485.toNat) % 2 ^ 32)
    (wP75 : v488.toNat + 2 ^ 32 * v491.toNat = v171.toNat * 4294967295 + v438.toNat + v485.toNat) :
    v488.toNat = (v488.toNat + 2 ^ 32 * v491.toNat) % 2 ^ 32 := by
  have := v171.isLt; have := v438.isLt; have := v483.isLt; have := v485.isLt; have := v488.isLt; have := v491.isLt
  generalize v171.toNat = n171 at *
  generalize v438.toNat = n438 at *
  generalize v483.toNat = n483 at *
  generalize v485.toNat = n485 at *
  generalize v488.toNat = n488 at *
  generalize v491.toNat = n491 at *
  first
    | omega
    | (obtain ⟨qt483, et483⟩ := mod_q t483; clear t483; obtain ⟨qt488, et488⟩ := mod_q t488; clear t488; omega)

theorem psm_v_P75h {v171 v438 v476 v483 v485 v486 v487 v488 v489 v491 : Word}
    (t476 : v476.toNat = v171.toNat * 4294967295 / 2 ^ 32 ∧ v476.toNat + (v171.toNat + 4294967295) / 4294967296 = v171.toNat)
    (t483 : v483.toNat = (v438.toNat + 2 ^ 32 - v171.toNat) % 2 ^ 32)
    (t486 : (v483.toNat < v438.toNat ∧ v486.toNat = 1) ∨ (v438.toNat ≤ v483.toNat ∧ v486.toNat = 0))
    (t487 : v487.toNat = (v486.toNat + v476.toNat) % 2 ^ 32)
    (t489 : v488.toNat + 2 ^ 32 * v489.toNat = v483.toNat + v485.toNat)
    (t491 : v491.toNat = (v487.toNat + v489.toNat) % 2 ^ 32)
    (wP75 : v488.toNat + 2 ^ 32 * v491.toNat = v171.toNat * 4294967295 + v438.toNat + v485.toNat) :
    v491.toNat = (v488.toNat + 2 ^ 32 * v491.toNat) / 2 ^ 32 := by
  have := v171.isLt; have := v438.isLt; have := v476.isLt; have := v483.isLt; have := v485.isLt; have := v486.isLt; have := v487.isLt; have := v488.isLt; have := v489.isLt; have := v491.isLt
  generalize v171.toNat = n171 at *
  generalize v438.toNat = n438 at *
  generalize v476.toNat = n476 at *
  generalize v483.toNat = n483 at *
  generalize v485.toNat = n485 at *
  generalize v486.toNat = n486 at *
  generalize v487.toNat = n487 at *
  generalize v488.toNat = n488 at *
  generalize v489.toNat = n489 at *
  generalize v491.toNat = n491 at *
  first
    | omega
    | (obtain ⟨t476a, t476b⟩ := t476; rcases Nat.eq_zero_or_pos n171 with _ | _ <;> rcases t486 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t476a, t476b⟩ := t476; obtain ⟨qt483, et483⟩ := mod_q t483; clear t483; obtain ⟨qt487, et487⟩ := mod_q t487; clear t487; obtain ⟨qt491, et491⟩ := mod_q t491; clear t491; omega)
    | (obtain ⟨t476a, t476b⟩ := t476; obtain ⟨qt483, et483⟩ := mod_q t483; clear t483; obtain ⟨qt487, et487⟩ := mod_q t487; clear t487; obtain ⟨qt491, et491⟩ := mod_q t491; clear t491; rcases Nat.eq_zero_or_pos n171 with _ | _ <;> rcases t486 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P76 {v171 v444 v484 v490 v491 v492 v493 v494 v495 v496 v497 : Word}
    (t484 : v484.toNat = v171.toNat * 4294967294 / 2 ^ 32 ∧ v484.toNat + (2 * v171.toNat + 4294967295) / 4294967296 = v171.toNat)
    (t490 : v490.toNat = (v171.toNat + v171.toNat) % 2 ^ 32)
    (t492 : v492.toNat = (v444.toNat + 2 ^ 32 - v490.toNat) % 2 ^ 32)
    (t493 : (v492.toNat < v444.toNat ∧ v493.toNat = 1) ∨ (v444.toNat ≤ v492.toNat ∧ v493.toNat = 0))
    (t494 : v494.toNat = (v492.toNat + v491.toNat) % 2 ^ 32)
    (t495 : v495.toNat = (v493.toNat + v484.toNat) % 2 ^ 32)
    (t496 : v494.toNat + 2 ^ 32 * v496.toNat = v492.toNat + v491.toNat)
    (t497 : v497.toNat = (v496.toNat + v495.toNat) % 2 ^ 32) :
    v494.toNat + 2 ^ 32 * v497.toNat = v171.toNat * 4294967294 + v444.toNat + v491.toNat := by
  have := v171.isLt; have := v444.isLt; have := v484.isLt; have := v490.isLt; have := v491.isLt; have := v492.isLt; have := v493.isLt; have := v494.isLt; have := v495.isLt; have := v496.isLt; have := v497.isLt
  generalize v171.toNat = n171 at *
  generalize v444.toNat = n444 at *
  generalize v484.toNat = n484 at *
  generalize v490.toNat = n490 at *
  generalize v491.toNat = n491 at *
  generalize v492.toNat = n492 at *
  generalize v493.toNat = n493 at *
  generalize v494.toNat = n494 at *
  generalize v495.toNat = n495 at *
  generalize v496.toNat = n496 at *
  generalize v497.toNat = n497 at *
  first
    | omega
    | (obtain ⟨t484a, t484b⟩ := t484; rcases (by omega : n171 = 0 ∨ (0 < n171 ∧ n171 ≤ 2147483648) ∨ 2147483648 < n171) with _ | _ | _ <;> rcases t493 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t484a, t484b⟩ := t484; obtain ⟨qt490, et490⟩ := mod_q t490; clear t490; obtain ⟨qt492, et492⟩ := mod_q t492; clear t492; obtain ⟨qt494, et494⟩ := mod_q t494; clear t494; obtain ⟨qt495, et495⟩ := mod_q t495; clear t495; omega)
    | (obtain ⟨t484a, t484b⟩ := t484; obtain ⟨qt490, et490⟩ := mod_q t490; clear t490; obtain ⟨qt492, et492⟩ := mod_q t492; clear t492; obtain ⟨qt494, et494⟩ := mod_q t494; clear t494; obtain ⟨qt495, et495⟩ := mod_q t495; clear t495; rcases (by omega : n171 = 0 ∨ (0 < n171 ∧ n171 ≤ 2147483648) ∨ 2147483648 < n171) with _ | _ | _ <;> rcases t493 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P76l {v171 v444 v490 v491 v492 v494 v497 : Word}
    (t490 : v490.toNat = (v171.toNat + v171.toNat) % 2 ^ 32)
    (t492 : v492.toNat = (v444.toNat + 2 ^ 32 - v490.toNat) % 2 ^ 32)
    (t494 : v494.toNat = (v492.toNat + v491.toNat) % 2 ^ 32)
    (wP76 : v494.toNat + 2 ^ 32 * v497.toNat = v171.toNat * 4294967294 + v444.toNat + v491.toNat) :
    v494.toNat = (v494.toNat + 2 ^ 32 * v497.toNat) % 2 ^ 32 := by
  have := v171.isLt; have := v444.isLt; have := v490.isLt; have := v491.isLt; have := v492.isLt; have := v494.isLt; have := v497.isLt
  generalize v171.toNat = n171 at *
  generalize v444.toNat = n444 at *
  generalize v490.toNat = n490 at *
  generalize v491.toNat = n491 at *
  generalize v492.toNat = n492 at *
  generalize v494.toNat = n494 at *
  generalize v497.toNat = n497 at *
  first
    | omega
    | (obtain ⟨qt490, et490⟩ := mod_q t490; clear t490; obtain ⟨qt492, et492⟩ := mod_q t492; clear t492; obtain ⟨qt494, et494⟩ := mod_q t494; clear t494; omega)

theorem psm_v_P76h {v171 v444 v484 v490 v491 v492 v493 v494 v495 v496 v497 : Word}
    (t484 : v484.toNat = v171.toNat * 4294967294 / 2 ^ 32 ∧ v484.toNat + (2 * v171.toNat + 4294967295) / 4294967296 = v171.toNat)
    (t490 : v490.toNat = (v171.toNat + v171.toNat) % 2 ^ 32)
    (t492 : v492.toNat = (v444.toNat + 2 ^ 32 - v490.toNat) % 2 ^ 32)
    (t493 : (v492.toNat < v444.toNat ∧ v493.toNat = 1) ∨ (v444.toNat ≤ v492.toNat ∧ v493.toNat = 0))
    (t495 : v495.toNat = (v493.toNat + v484.toNat) % 2 ^ 32)
    (t496 : v494.toNat + 2 ^ 32 * v496.toNat = v492.toNat + v491.toNat)
    (t497 : v497.toNat = (v496.toNat + v495.toNat) % 2 ^ 32)
    (wP76 : v494.toNat + 2 ^ 32 * v497.toNat = v171.toNat * 4294967294 + v444.toNat + v491.toNat) :
    v497.toNat = (v494.toNat + 2 ^ 32 * v497.toNat) / 2 ^ 32 := by
  have := v171.isLt; have := v444.isLt; have := v484.isLt; have := v490.isLt; have := v491.isLt; have := v492.isLt; have := v493.isLt; have := v494.isLt; have := v495.isLt; have := v496.isLt; have := v497.isLt
  generalize v171.toNat = n171 at *
  generalize v444.toNat = n444 at *
  generalize v484.toNat = n484 at *
  generalize v490.toNat = n490 at *
  generalize v491.toNat = n491 at *
  generalize v492.toNat = n492 at *
  generalize v493.toNat = n493 at *
  generalize v494.toNat = n494 at *
  generalize v495.toNat = n495 at *
  generalize v496.toNat = n496 at *
  generalize v497.toNat = n497 at *
  first
    | omega
    | (obtain ⟨t484a, t484b⟩ := t484; rcases (by omega : n171 = 0 ∨ (0 < n171 ∧ n171 ≤ 2147483648) ∨ 2147483648 < n171) with _ | _ | _ <;> rcases t493 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t484a, t484b⟩ := t484; obtain ⟨qt490, et490⟩ := mod_q t490; clear t490; obtain ⟨qt492, et492⟩ := mod_q t492; clear t492; obtain ⟨qt495, et495⟩ := mod_q t495; clear t495; obtain ⟨qt497, et497⟩ := mod_q t497; clear t497; omega)
    | (obtain ⟨t484a, t484b⟩ := t484; obtain ⟨qt490, et490⟩ := mod_q t490; clear t490; obtain ⟨qt492, et492⟩ := mod_q t492; clear t492; obtain ⟨qt495, et495⟩ := mod_q t495; clear t495; obtain ⟨qt497, et497⟩ := mod_q t497; clear t497; rcases (by omega : n171 = 0 ∨ (0 < n171 ∧ n171 ≤ 2147483648) ∨ 2147483648 < n171) with _ | _ | _ <;> rcases t493 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

end C3.RV32
