import C3BootProofs.Proofs.EdvReduceFacts

/-! # The inlined `Scalar::reduce`'s values, part 1

Each lemma proves one value the code holds in words from its instructions' facts. `scripts/gen-ev-reduce.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option maxHeartbeats 10000000 in
theorem evr_v_Z12a {v266 v267 v270 v272 v276 v282 v284 v297 : Word}
    (t276 : v276.toNat = (v270.toNat + 2 ^ 32 - v272.toNat) % 2 ^ 32)
    (t282 : v297.toNat + v267.toNat = v266.toNat + 2 ^ 32 * v282.toNat)
    (t284 : v284.toNat = (v276.toNat + 2 ^ 32 - v282.toNat) % 2 ^ 32) :
    v297.toNat + 2 ^ 32 * v284.toNat = ((v266.toNat + 2 ^ 32 * v270.toNat) + (2 ^ 64 - (v267.toNat + 2 ^ 32 * v272.toNat))) % 2 ^ 64 := by
  obtain ⟨q276, eq276⟩ := mod_q t276; clear t276
  obtain ⟨q284, eq284⟩ := mod_q t284; clear t284
  have key : v297.toNat + 2 ^ 32 * v284.toNat + 2 ^ 64 * (q276 + q284) = ((v266.toNat + 2 ^ 32 * v270.toNat) + (2 ^ 64 - (v267.toNat + 2 ^ 32 * v272.toNat))) + 2 ^ 64 * (1) := by
    have := v267.isLt; have := v272.isLt; have := v282.isLt; skip
    generalize v266.toNat = n266 at *
    generalize v267.toNat = n267 at *
    generalize v270.toNat = n270 at *
    generalize v272.toNat = n272 at *
    generalize v276.toNat = n276 at *
    generalize v282.toNat = n282 at *
    generalize v284.toNat = n284 at *
    generalize v297.toNat = n297 at *
    omega
  exact smm_key key (smm_lt v297 v284)

set_option maxHeartbeats 10000000 in
theorem evr_v_PA5B8 {v19 v30 v163 v167 v169 v173 v317 v319 v326 : Word}
    (t317 : v317.toNat = v163.toNat * 2 ^ 20 % 2 ^ 32)
    (t319 : v319.toNat = (v317.toNat + 2 ^ 32 - v173.toNat) % 2 ^ 32)
    (t326 : v326.toNat = v173.toNat * 1048575 / 2 ^ 32)
    (wA5 : v173.toNat = v169.toNat % 2 ^ 29)
    (wO5 : v169.toNat = v163.toNat + v167.toNat)
    (wSR5 : v163.toNat = v19.toNat / 2 ^ 17)
    (wSL5 : v167.toNat = v30.toNat * 2 ^ 15 % 2 ^ 32) :
    v319.toNat + 2 ^ 32 * v326.toNat = v173.toNat * (1048575) := by
  have := v19.isLt; have := v30.isLt; have := v163.isLt; have := v167.isLt; have := v169.isLt; have := v173.isLt; have := v317.isLt; have := v319.isLt; have := v326.isLt
  generalize v19.toNat = n19 at *
  generalize v30.toNat = n30 at *
  generalize v163.toNat = n163 at *
  generalize v167.toNat = n167 at *
  generalize v169.toNat = n169 at *
  generalize v173.toNat = n173 at *
  generalize v317.toNat = n317 at *
  generalize v319.toNat = n319 at *
  generalize v326.toNat = n326 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA6B7 {v30 v31 v175 v180 v183 v185 v189 v208 v209 : Word}
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
theorem evr_v_PA7B6 {v31 v33 v236 v243 v246 v254 v255 v260 v261 : Word}
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
theorem evr_v_PA8B5 {v308 v312 v318 v320 : Word}
    (t312 : v312.toNat = v308.toNat * 536870911 / 2 ^ 32)
    (t318 : v318.toNat = v308.toNat * 2 ^ 29 % 2 ^ 32)
    (t320 : v320.toNat = (v318.toNat + 2 ^ 32 - v308.toNat) % 2 ^ 32) :
    v320.toNat + 2 ^ 32 * v312.toNat = v308.toNat * (536870911) := by
  have := v308.isLt; have := v312.isLt; have := v318.isLt; have := v320.isLt
  generalize v308.toNat = n308 at *
  generalize v312.toNat = n312 at *
  generalize v318.toNat = n318 at *
  generalize v320.toNat = n320 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z13 {v189 v209 v255 v261 v312 v319 v320 v321 v326 v327 v329 v331 v337 v339 v340 v341 v343 v349 v353 v357 : Word}
    (t327 : v321.toNat + 2 ^ 32 * v327.toNat = v320.toNat + v261.toNat)
    (t329 : v329.toNat = (v327.toNat + v312.toNat) % 2 ^ 32)
    (t337 : v337.toNat = (v329.toNat + v255.toNat) % 2 ^ 32)
    (t339 : v331.toNat + 2 ^ 32 * v339.toNat = v319.toNat + v321.toNat)
    (t340 : v340.toNat = (v339.toNat + v326.toNat) % 2 ^ 32)
    (t343 : v341.toNat + 2 ^ 32 * v343.toNat = v209.toNat + v331.toNat)
    (t349 : v349.toNat = (v343.toNat + v189.toNat) % 2 ^ 32)
    (t353 : v353.toNat = (v340.toNat + v337.toNat) % 2 ^ 32)
    (t357 : v357.toNat = (v349.toNat + v353.toNat) % 2 ^ 32) :
    v341.toNat + 2 ^ 32 * v357.toNat = ((v319.toNat + 2 ^ 32 * v326.toNat) + (v209.toNat + 2 ^ 32 * v189.toNat) + (v261.toNat + 2 ^ 32 * v255.toNat) + (v320.toNat + 2 ^ 32 * v312.toNat)) % 2 ^ 64 := by
  obtain ⟨q329, eq329⟩ := mod_q t329; clear t329
  obtain ⟨q337, eq337⟩ := mod_q t337; clear t337
  obtain ⟨q340, eq340⟩ := mod_q t340; clear t340
  obtain ⟨q349, eq349⟩ := mod_q t349; clear t349
  obtain ⟨q353, eq353⟩ := mod_q t353; clear t353
  obtain ⟨q357, eq357⟩ := mod_q t357; clear t357
  have key : v341.toNat + 2 ^ 32 * v357.toNat + 2 ^ 64 * (q349 + q340 + q329 + q337 + q353 + q357) = ((v319.toNat + 2 ^ 32 * v326.toNat) + (v209.toNat + 2 ^ 32 * v189.toNat) + (v261.toNat + 2 ^ 32 * v255.toNat) + (v320.toNat + 2 ^ 32 * v312.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v189.toNat = n189 at *
    generalize v209.toNat = n209 at *
    generalize v255.toNat = n255 at *
    generalize v261.toNat = n261 at *
    generalize v312.toNat = n312 at *
    generalize v319.toNat = n319 at *
    generalize v320.toNat = n320 at *
    generalize v321.toNat = n321 at *
    generalize v326.toNat = n326 at *
    generalize v327.toNat = n327 at *
    generalize v329.toNat = n329 at *
    generalize v331.toNat = n331 at *
    generalize v337.toNat = n337 at *
    generalize v339.toNat = n339 at *
    generalize v340.toNat = n340 at *
    generalize v341.toNat = n341 at *
    generalize v343.toNat = n343 at *
    generalize v349.toNat = n349 at *
    generalize v353.toNat = n353 at *
    generalize v357.toNat = n357 at *
    omega
  exact smm_key key (smm_lt v341 v357)

set_option maxHeartbeats 10000000 in
theorem evr_v_PA6B8 {v30 v31 v175 v180 v183 v185 v470 v474 v479 : Word}
    (t470 : v470.toNat = v175.toNat * 2 ^ 20 % 2 ^ 32)
    (t474 : v474.toNat = (v470.toNat + 2 ^ 32 - v185.toNat) % 2 ^ 32)
    (t479 : v479.toNat = v185.toNat * 1048575 / 2 ^ 32)
    (wA6 : v185.toNat = v183.toNat % 2 ^ 29)
    (wO6 : v183.toNat = v175.toNat + v180.toNat)
    (wSR6 : v175.toNat = v30.toNat / 2 ^ 14)
    (wSL6 : v180.toNat = v31.toNat * 2 ^ 18 % 2 ^ 32) :
    v474.toNat + 2 ^ 32 * v479.toNat = v185.toNat * (1048575) := by
  have := v30.isLt; have := v31.isLt; have := v175.isLt; have := v180.isLt; have := v183.isLt; have := v185.isLt; have := v470.isLt; have := v474.isLt; have := v479.isLt
  generalize v30.toNat = n30 at *
  generalize v31.toNat = n31 at *
  generalize v175.toNat = n175 at *
  generalize v180.toNat = n180 at *
  generalize v183.toNat = n183 at *
  generalize v185.toNat = n185 at *
  generalize v470.toNat = n470 at *
  generalize v474.toNat = n474 at *
  generalize v479.toNat = n479 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA7B7 {v31 v33 v236 v243 v246 v254 v255 v260 v261 : Word}
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
theorem evr_v_PA8B6 {v308 v312 v318 v320 : Word}
    (t312 : v312.toNat = v308.toNat * 536870911 / 2 ^ 32)
    (t318 : v318.toNat = v308.toNat * 2 ^ 29 % 2 ^ 32)
    (t320 : v320.toNat = (v318.toNat + 2 ^ 32 - v308.toNat) % 2 ^ 32) :
    v320.toNat + 2 ^ 32 * v312.toNat = v308.toNat * (536870911) := by
  have := v308.isLt; have := v312.isLt; have := v318.isLt; have := v320.isLt
  generalize v308.toNat = n308 at *
  generalize v312.toNat = n312 at *
  generalize v318.toNat = n318 at *
  generalize v320.toNat = n320 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z14 {v255 v261 v312 v320 v321 v327 v329 v337 v474 v479 v481 v486 v493 v545 : Word}
    (t327 : v321.toNat + 2 ^ 32 * v327.toNat = v320.toNat + v261.toNat)
    (t329 : v329.toNat = (v327.toNat + v312.toNat) % 2 ^ 32)
    (t337 : v337.toNat = (v329.toNat + v255.toNat) % 2 ^ 32)
    (t486 : v481.toNat + 2 ^ 32 * v486.toNat = v474.toNat + v321.toNat)
    (t493 : v493.toNat = (v486.toNat + v479.toNat) % 2 ^ 32)
    (t545 : v545.toNat = (v493.toNat + v337.toNat) % 2 ^ 32) :
    v481.toNat + 2 ^ 32 * v545.toNat = ((v474.toNat + 2 ^ 32 * v479.toNat) + (v261.toNat + 2 ^ 32 * v255.toNat) + (v320.toNat + 2 ^ 32 * v312.toNat)) % 2 ^ 64 := by
  obtain ⟨q329, eq329⟩ := mod_q t329; clear t329
  obtain ⟨q337, eq337⟩ := mod_q t337; clear t337
  obtain ⟨q493, eq493⟩ := mod_q t493; clear t493
  obtain ⟨q545, eq545⟩ := mod_q t545; clear t545
  have key : v481.toNat + 2 ^ 32 * v545.toNat + 2 ^ 64 * (q493 + q329 + q337 + q545) = ((v474.toNat + 2 ^ 32 * v479.toNat) + (v261.toNat + 2 ^ 32 * v255.toNat) + (v320.toNat + 2 ^ 32 * v312.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v255.toNat = n255 at *
    generalize v261.toNat = n261 at *
    generalize v312.toNat = n312 at *
    generalize v320.toNat = n320 at *
    generalize v321.toNat = n321 at *
    generalize v327.toNat = n327 at *
    generalize v329.toNat = n329 at *
    generalize v337.toNat = n337 at *
    generalize v474.toNat = n474 at *
    generalize v479.toNat = n479 at *
    generalize v481.toNat = n481 at *
    generalize v486.toNat = n486 at *
    generalize v493.toNat = n493 at *
    generalize v545.toNat = n545 at *
    omega
  exact smm_key key (smm_lt v481 v545)

set_option maxHeartbeats 10000000 in
theorem evr_v_PA7B8 {v31 v33 v236 v243 v246 v254 v552 v555 v556 : Word}
    (t552 : v552.toNat = v236.toNat * 2 ^ 20 % 2 ^ 32)
    (t555 : v555.toNat = (v552.toNat + 2 ^ 32 - v254.toNat) % 2 ^ 32)
    (t556 : v556.toNat = v254.toNat * 1048575 / 2 ^ 32)
    (wA7 : v254.toNat = v246.toNat % 2 ^ 29)
    (wO7 : v246.toNat = v236.toNat + v243.toNat)
    (wSR7 : v236.toNat = v31.toNat / 2 ^ 11)
    (wSL7 : v243.toNat = v33.toNat * 2 ^ 21 % 2 ^ 32) :
    v555.toNat + 2 ^ 32 * v556.toNat = v254.toNat * (1048575) := by
  have := v31.isLt; have := v33.isLt; have := v236.isLt; have := v243.isLt; have := v246.isLt; have := v254.isLt; have := v552.isLt; have := v555.isLt; have := v556.isLt
  generalize v31.toNat = n31 at *
  generalize v33.toNat = n33 at *
  generalize v236.toNat = n236 at *
  generalize v243.toNat = n243 at *
  generalize v246.toNat = n246 at *
  generalize v254.toNat = n254 at *
  generalize v552.toNat = n552 at *
  generalize v555.toNat = n555 at *
  generalize v556.toNat = n556 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA8B7 {v308 v312 v318 v320 : Word}
    (t312 : v312.toNat = v308.toNat * 536870911 / 2 ^ 32)
    (t318 : v318.toNat = v308.toNat * 2 ^ 29 % 2 ^ 32)
    (t320 : v320.toNat = (v318.toNat + 2 ^ 32 - v308.toNat) % 2 ^ 32) :
    v320.toNat + 2 ^ 32 * v312.toNat = v308.toNat * (536870911) := by
  have := v308.isLt; have := v312.isLt; have := v318.isLt; have := v320.isLt
  generalize v308.toNat = n308 at *
  generalize v312.toNat = n312 at *
  generalize v318.toNat = n318 at *
  generalize v320.toNat = n320 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z15 {v312 v320 v555 v556 v559 v563 v566 v572 : Word}
    (t563 : v559.toNat + 2 ^ 32 * v563.toNat = v320.toNat + v555.toNat)
    (t566 : v566.toNat = (v563.toNat + v312.toNat) % 2 ^ 32)
    (t572 : v572.toNat = (v566.toNat + v556.toNat) % 2 ^ 32) :
    v559.toNat + 2 ^ 32 * v572.toNat = ((v555.toNat + 2 ^ 32 * v556.toNat) + (v320.toNat + 2 ^ 32 * v312.toNat)) % 2 ^ 64 := by
  obtain ⟨q566, eq566⟩ := mod_q t566; clear t566
  obtain ⟨q572, eq572⟩ := mod_q t572; clear t572
  have key : v559.toNat + 2 ^ 32 * v572.toNat + 2 ^ 64 * (q566 + q572) = ((v555.toNat + 2 ^ 32 * v556.toNat) + (v320.toNat + 2 ^ 32 * v312.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v312.toNat = n312 at *
    generalize v320.toNat = n320 at *
    generalize v555.toNat = n555 at *
    generalize v556.toNat = n556 at *
    generalize v559.toNat = n559 at *
    generalize v563.toNat = n563 at *
    generalize v566.toNat = n566 at *
    generalize v572.toNat = n572 at *
    omega
  exact smm_key key (smm_lt v559 v572)

set_option maxHeartbeats 10000000 in
theorem evr_v_PA8B8 {v308 v579 v581 v582 : Word}
    (t579 : v579.toNat = v308.toNat * 1048575 / 2 ^ 32)
    (t581 : v581.toNat = v308.toNat * 2 ^ 20 % 2 ^ 32)
    (t582 : v582.toNat = (v581.toNat + 2 ^ 32 - v308.toNat) % 2 ^ 32) :
    v582.toNat + 2 ^ 32 * v579.toNat = v308.toNat * (1048575) := by
  have := v308.isLt; have := v579.isLt; have := v581.isLt; have := v582.isLt
  generalize v308.toNat = n308 at *
  generalize v579.toNat = n579 at *
  generalize v581.toNat = n581 at *
  generalize v582.toNat = n582 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z11b {v231 v274 v579 v582 v994 v999 v1002 v1003 : Word}
    (t999 : v994.toNat + 2 ^ 32 * v999.toNat = v274.toNat + v582.toNat)
    (t1002 : v1002.toNat = (v231.toNat + v579.toNat) % 2 ^ 32)
    (t1003 : v1003.toNat = (v999.toNat + v1002.toNat) % 2 ^ 32) :
    v994.toNat + 2 ^ 32 * v1003.toNat = ((v582.toNat + 2 ^ 32 * v579.toNat) + (v274.toNat + 2 ^ 32 * v231.toNat)) % 2 ^ 64 := by
  obtain ⟨q1002, eq1002⟩ := mod_q t1002; clear t1002
  obtain ⟨q1003, eq1003⟩ := mod_q t1003; clear t1003
  have key : v994.toNat + 2 ^ 32 * v1003.toNat + 2 ^ 64 * (q1002 + q1003) = ((v582.toNat + 2 ^ 32 * v579.toNat) + (v274.toNat + 2 ^ 32 * v231.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v231.toNat = n231 at *
    generalize v274.toNat = n274 at *
    generalize v579.toNat = n579 at *
    generalize v582.toNat = n582 at *
    generalize v994.toNat = n994 at *
    generalize v999.toNat = n999 at *
    generalize v1002.toNat = n1002 at *
    generalize v1003.toNat = n1003 at *
    omega
  exact smm_key key (smm_lt v994 v1003)

set_option maxHeartbeats 10000000 in
theorem evr_v_AA0 {v8 v173 v388 : Word}
    (t388 : v388.toNat = (v8.toNat + v173.toNat) % 2 ^ 32) :
    v388.toNat = (v8.toNat + v173.toNat) % 2 ^ 32 := by
  have := v8.isLt; have := v173.isLt; have := v388.isLt
  generalize v8.toNat = n8 at *
  generalize v173.toNat = n173 at *
  generalize v388.toNat = n388 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_AA1 {v15 v185 v476 : Word}
    (t476 : v476.toNat = (v15.toNat + v185.toNat) % 2 ^ 32) :
    v476.toNat = (v15.toNat + v185.toNat) % 2 ^ 32 := by
  have := v15.isLt; have := v185.isLt; have := v476.isLt
  generalize v15.toNat = n15 at *
  generalize v185.toNat = n185 at *
  generalize v476.toNat = n476 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_AA2 {v16 v254 v576 : Word}
    (t576 : v576.toNat = (v16.toNat + v254.toNat) % 2 ^ 32) :
    v576.toNat = (v16.toNat + v254.toNat) % 2 ^ 32 := by
  have := v16.isLt; have := v254.isLt; have := v576.isLt
  generalize v16.toNat = n16 at *
  generalize v254.toNat = n254 at *
  generalize v576.toNat = n576 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_AA3 {v36 v308 v592 : Word}
    (t592 : v592.toNat = (v36.toNat + v308.toNat) % 2 ^ 32) :
    v592.toNat = (v36.toNat + v308.toNat) % 2 ^ 32 := by
  have := v36.isLt; have := v308.isLt; have := v592.isLt
  generalize v36.toNat = n36 at *
  generalize v308.toNat = n308 at *
  generalize v592.toNat = n592 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA0BB0 {v388 v412 v416 : Word}
    (t412 : v412.toNat = v388.toNat * 827193836 / 2 ^ 32)
    (t416 : v416.toNat = v388.toNat * 827193836 % 2 ^ 32) :
    v416.toNat + 2 ^ 32 * v412.toNat = v388.toNat * (((290322925) + (536870911)) % 2 ^ 32) := by
  have := v388.isLt; have := v412.isLt; have := v416.isLt
  generalize v388.toNat = n388 at *
  generalize v412.toNat = n412 at *
  generalize v416.toNat = n416 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z5 {v120 v147 v203 v206 v372 v378 v412 v416 v424 v426 v430 v433 v434 v435 : Word}
    (t372 : v426.toNat + v120.toNat = v206.toNat + 2 ^ 32 * v372.toNat)
    (t378 : v378.toNat = (v147.toNat + v372.toNat) % 2 ^ 32)
    (t424 : v424.toNat = (v378.toNat + 2 ^ 32 - v412.toNat) % 2 ^ 32)
    (t433 : v433.toNat = (v203.toNat + 2 ^ 32 - v424.toNat) % 2 ^ 32)
    (t434 : v430.toNat + 2 ^ 32 * v434.toNat = v416.toNat + v426.toNat)
    (t435 : v435.toNat = (v433.toNat + v434.toNat) % 2 ^ 32) :
    v430.toNat + 2 ^ 32 * v435.toNat = ((v416.toNat + 2 ^ 32 * v412.toNat) + (((v206.toNat + 2 ^ 32 * v203.toNat) + (2 ^ 64 - (v120.toNat + 2 ^ 32 * v147.toNat))) % 2 ^ 64)) % 2 ^ 64 := by
  obtain ⟨q378, eq378⟩ := mod_q t378; clear t378
  obtain ⟨q424, eq424⟩ := mod_q t424; clear t424
  obtain ⟨q433, eq433⟩ := mod_q t433; clear t433
  obtain ⟨q435, eq435⟩ := mod_q t435; clear t435
  obtain ⟨k0, ek0⟩ : ∃ k, ((v206.toNat + 2 ^ 32 * v203.toNat) + (2 ^ 64 - (v120.toNat + 2 ^ 32 * v147.toNat))) % 2 ^ 64 + 2 ^ 64 * k = ((v206.toNat + 2 ^ 32 * v203.toNat) + (2 ^ 64 - (v120.toNat + 2 ^ 32 * v147.toNat))) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v430.toNat + 2 ^ 32 * v435.toNat + 2 ^ 64 * (q433 + q435 + 1) = ((v416.toNat + 2 ^ 32 * v412.toNat) + (((v206.toNat + 2 ^ 32 * v203.toNat) + (2 ^ 64 - (v120.toNat + 2 ^ 32 * v147.toNat))) % 2 ^ 64)) + 2 ^ 64 * (q378 + q424 + k0) := by
    have := v120.isLt; have := v147.isLt; have := v412.isLt; have := v424.isLt; skip
    generalize v120.toNat = n120 at *
    generalize v147.toNat = n147 at *
    generalize v203.toNat = n203 at *
    generalize v206.toNat = n206 at *
    generalize v372.toNat = n372 at *
    generalize v378.toNat = n378 at *
    generalize v412.toNat = n412 at *
    generalize v416.toNat = n416 at *
    generalize v424.toNat = n424 at *
    generalize v426.toNat = n426 at *
    generalize v430.toNat = n430 at *
    generalize v433.toNat = n433 at *
    generalize v434.toNat = n434 at *
    generalize v435.toNat = n435 at *
    omega
  exact smm_key key (smm_lt v430 v435)

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA0BB1 {v388 v483 v484 : Word}
    (t483 : v483.toNat = v388.toNat * 979464962 % 2 ^ 32)
    (t484 : v484.toNat = v388.toNat * 979464962 / 2 ^ 32) :
    v483.toNat + 2 ^ 32 * v484.toNat = v388.toNat * (((442594051) + (536870911)) % 2 ^ 32) := by
  have := v388.isLt; have := v483.isLt; have := v484.isLt
  generalize v388.toNat = n388 at *
  generalize v483.toNat = n483 at *
  generalize v484.toNat = n484 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA1BB0 {v476 v490 v491 : Word}
    (t490 : v490.toNat = v476.toNat * 827193836 / 2 ^ 32)
    (t491 : v491.toNat = v476.toNat * 827193836 % 2 ^ 32) :
    v491.toNat + 2 ^ 32 * v490.toNat = v476.toNat * (((290322925) + (536870911)) % 2 ^ 32) := by
  have := v476.isLt; have := v490.isLt; have := v491.isLt
  generalize v476.toNat = n476 at *
  generalize v490.toNat = n490 at *
  generalize v491.toNat = n491 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z6 {v40 v51 v231 v274 v483 v484 v490 v491 v497 v499 v502 v503 v504 v506 v508 v510 v520 v521 v525 v528 : Word}
    (t497 : v503.toNat + v40.toNat = v483.toNat + 2 ^ 32 * v497.toNat)
    (t499 : v499.toNat = (v484.toNat + 2 ^ 32 - v497.toNat) % 2 ^ 32)
    (t502 : v502.toNat = (v499.toNat + 2 ^ 32 - v51.toNat) % 2 ^ 32)
    (t504 : v504.toNat = (v502.toNat + v490.toNat) % 2 ^ 32)
    (t508 : v506.toNat + 2 ^ 32 * v508.toNat = v491.toNat + v503.toNat)
    (t510 : v510.toNat = (v508.toNat + v504.toNat) % 2 ^ 32)
    (t521 : v520.toNat + 2 ^ 32 * v521.toNat = v274.toNat + v506.toNat)
    (t525 : v525.toNat = (v521.toNat + v231.toNat) % 2 ^ 32)
    (t528 : v528.toNat = (v510.toNat + v525.toNat) % 2 ^ 32) :
    v520.toNat + 2 ^ 32 * v528.toNat = ((((v483.toNat + 2 ^ 32 * v484.toNat) + (v491.toNat + 2 ^ 32 * v490.toNat)) % 2 ^ 64) + (((v274.toNat + 2 ^ 32 * v231.toNat) + (2 ^ 64 - (v40.toNat + 2 ^ 32 * v51.toNat))) % 2 ^ 64)) % 2 ^ 64 := by
  obtain ⟨q499, eq499⟩ := mod_q t499; clear t499
  obtain ⟨q502, eq502⟩ := mod_q t502; clear t502
  obtain ⟨q504, eq504⟩ := mod_q t504; clear t504
  obtain ⟨q510, eq510⟩ := mod_q t510; clear t510
  obtain ⟨q525, eq525⟩ := mod_q t525; clear t525
  obtain ⟨q528, eq528⟩ := mod_q t528; clear t528
  obtain ⟨k0, ek0⟩ : ∃ k, ((v483.toNat + 2 ^ 32 * v484.toNat) + (v491.toNat + 2 ^ 32 * v490.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v483.toNat + 2 ^ 32 * v484.toNat) + (v491.toNat + 2 ^ 32 * v490.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  obtain ⟨k1, ek1⟩ : ∃ k, ((v274.toNat + 2 ^ 32 * v231.toNat) + (2 ^ 64 - (v40.toNat + 2 ^ 32 * v51.toNat))) % 2 ^ 64 + 2 ^ 64 * k = ((v274.toNat + 2 ^ 32 * v231.toNat) + (2 ^ 64 - (v40.toNat + 2 ^ 32 * v51.toNat))) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v520.toNat + 2 ^ 32 * v528.toNat + 2 ^ 64 * (q499 + q502 + q504 + q510 + q525 + q528) = ((((v483.toNat + 2 ^ 32 * v484.toNat) + (v491.toNat + 2 ^ 32 * v490.toNat)) % 2 ^ 64) + (((v274.toNat + 2 ^ 32 * v231.toNat) + (2 ^ 64 - (v40.toNat + 2 ^ 32 * v51.toNat))) % 2 ^ 64)) + 2 ^ 64 * (k1 + k0 + 1) := by
    have := v40.isLt; have := v51.isLt; have := v497.isLt; skip
    generalize v40.toNat = n40 at *
    generalize v51.toNat = n51 at *
    generalize v231.toNat = n231 at *
    generalize v274.toNat = n274 at *
    generalize v483.toNat = n483 at *
    generalize v484.toNat = n484 at *
    generalize v490.toNat = n490 at *
    generalize v491.toNat = n491 at *
    generalize v497.toNat = n497 at *
    generalize v499.toNat = n499 at *
    generalize v502.toNat = n502 at *
    generalize v503.toNat = n503 at *
    generalize v504.toNat = n504 at *
    generalize v506.toNat = n506 at *
    generalize v508.toNat = n508 at *
    generalize v510.toNat = n510 at *
    generalize v520.toNat = n520 at *
    generalize v521.toNat = n521 at *
    generalize v525.toNat = n525 at *
    generalize v528.toNat = n528 at *
    omega
  exact smm_key key (smm_lt v520 v528)

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA0BB2 {v388 v588 v589 : Word}
    (t588 : v588.toNat = v388.toNat * 796658059 % 2 ^ 32)
    (t589 : v589.toNat = v388.toNat * 796658059 / 2 ^ 32) :
    v588.toNat + 2 ^ 32 * v589.toNat = v388.toNat * (((259787148) + (536870911)) % 2 ^ 32) := by
  have := v388.isLt; have := v588.isLt; have := v589.isLt
  generalize v388.toNat = n388 at *
  generalize v588.toNat = n588 at *
  generalize v589.toNat = n589 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA1BB1 {v476 v590 v594 : Word}
    (t590 : v590.toNat = v476.toNat * 979464962 % 2 ^ 32)
    (t594 : v594.toNat = v476.toNat * 979464962 / 2 ^ 32) :
    v590.toNat + 2 ^ 32 * v594.toNat = v476.toNat * (((442594051) + (536870911)) % 2 ^ 32) := by
  have := v476.isLt; have := v590.isLt; have := v594.isLt
  generalize v476.toNat = n476 at *
  generalize v590.toNat = n590 at *
  generalize v594.toNat = n594 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA2BB0 {v576 v595 v599 : Word}
    (t595 : v595.toNat = v576.toNat * 827193836 / 2 ^ 32)
    (t599 : v599.toNat = v576.toNat * 827193836 % 2 ^ 32) :
    v599.toNat + 2 ^ 32 * v595.toNat = v576.toNat * (((290322925) + (536870911)) % 2 ^ 32) := by
  have := v576.isLt; have := v595.isLt; have := v599.isLt
  generalize v576.toNat = n576 at *
  generalize v595.toNat = n595 at *
  generalize v599.toNat = n599 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z7 {v62 v67 v284 v297 v588 v589 v590 v594 v595 v599 v601 v602 v603 v604 v606 v607 v608 v609 v610 v614 v616 v620 v622 v624 v625 v628 : Word}
    (t601 : v602.toNat + v62.toNat = v588.toNat + 2 ^ 32 * v601.toNat)
    (t603 : v603.toNat = (v589.toNat + 2 ^ 32 - v601.toNat) % 2 ^ 32)
    (t606 : v606.toNat = (v603.toNat + 2 ^ 32 - v67.toNat) % 2 ^ 32)
    (t607 : v604.toNat + 2 ^ 32 * v607.toNat = v602.toNat + v590.toNat)
    (t608 : v608.toNat = (v606.toNat + v594.toNat) % 2 ^ 32)
    (t609 : v609.toNat = (v607.toNat + v595.toNat) % 2 ^ 32)
    (t610 : v610.toNat = (v609.toNat + v608.toNat) % 2 ^ 32)
    (t616 : v614.toNat + 2 ^ 32 * v616.toNat = v604.toNat + v599.toNat)
    (t620 : v620.toNat = (v284.toNat + v616.toNat) % 2 ^ 32)
    (t622 : v622.toNat = (v610.toNat + v620.toNat) % 2 ^ 32)
    (t625 : v624.toNat + 2 ^ 32 * v625.toNat = v297.toNat + v614.toNat)
    (t628 : v628.toNat = (v622.toNat + v625.toNat) % 2 ^ 32) :
    v624.toNat + 2 ^ 32 * v628.toNat = ((((v588.toNat + 2 ^ 32 * v589.toNat) + (v590.toNat + 2 ^ 32 * v594.toNat) + (v599.toNat + 2 ^ 32 * v595.toNat)) % 2 ^ 64) + (((v297.toNat + 2 ^ 32 * v284.toNat) + (2 ^ 64 - (v62.toNat + 2 ^ 32 * v67.toNat))) % 2 ^ 64)) % 2 ^ 64 := by
  obtain ⟨q603, eq603⟩ := mod_q t603; clear t603
  obtain ⟨q606, eq606⟩ := mod_q t606; clear t606
  obtain ⟨q608, eq608⟩ := mod_q t608; clear t608
  obtain ⟨q609, eq609⟩ := mod_q t609; clear t609
  obtain ⟨q610, eq610⟩ := mod_q t610; clear t610
  obtain ⟨q620, eq620⟩ := mod_q t620; clear t620
  obtain ⟨q622, eq622⟩ := mod_q t622; clear t622
  obtain ⟨q628, eq628⟩ := mod_q t628; clear t628
  obtain ⟨k0, ek0⟩ : ∃ k, ((v297.toNat + 2 ^ 32 * v284.toNat) + (2 ^ 64 - (v62.toNat + 2 ^ 32 * v67.toNat))) % 2 ^ 64 + 2 ^ 64 * k = ((v297.toNat + 2 ^ 32 * v284.toNat) + (2 ^ 64 - (v62.toNat + 2 ^ 32 * v67.toNat))) := ⟨_, Nat.mod_add_div _ _⟩
  obtain ⟨k1, ek1⟩ : ∃ k, ((v588.toNat + 2 ^ 32 * v589.toNat) + (v590.toNat + 2 ^ 32 * v594.toNat) + (v599.toNat + 2 ^ 32 * v595.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v588.toNat + 2 ^ 32 * v589.toNat) + (v590.toNat + 2 ^ 32 * v594.toNat) + (v599.toNat + 2 ^ 32 * v595.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v624.toNat + 2 ^ 32 * v628.toNat + 2 ^ 64 * (q609 + q603 + q606 + q608 + q610 + q620 + q622 + q628) = ((((v588.toNat + 2 ^ 32 * v589.toNat) + (v590.toNat + 2 ^ 32 * v594.toNat) + (v599.toNat + 2 ^ 32 * v595.toNat)) % 2 ^ 64) + (((v297.toNat + 2 ^ 32 * v284.toNat) + (2 ^ 64 - (v62.toNat + 2 ^ 32 * v67.toNat))) % 2 ^ 64)) + 2 ^ 64 * (k1 + k0 + 1) := by
    have := v62.isLt; have := v67.isLt; have := v601.isLt; skip
    generalize v62.toNat = n62 at *
    generalize v67.toNat = n67 at *
    generalize v284.toNat = n284 at *
    generalize v297.toNat = n297 at *
    generalize v588.toNat = n588 at *
    generalize v589.toNat = n589 at *
    generalize v590.toNat = n590 at *
    generalize v594.toNat = n594 at *
    generalize v595.toNat = n595 at *
    generalize v599.toNat = n599 at *
    generalize v601.toNat = n601 at *
    generalize v602.toNat = n602 at *
    generalize v603.toNat = n603 at *
    generalize v604.toNat = n604 at *
    generalize v606.toNat = n606 at *
    generalize v607.toNat = n607 at *
    generalize v608.toNat = n608 at *
    generalize v609.toNat = n609 at *
    generalize v610.toNat = n610 at *
    generalize v614.toNat = n614 at *
    generalize v616.toNat = n616 at *
    generalize v620.toNat = n620 at *
    generalize v622.toNat = n622 at *
    generalize v624.toNat = n624 at *
    generalize v625.toNat = n625 at *
    generalize v628.toNat = n628 at *
    omega
  exact smm_key key (smm_lt v624 v628)

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA0BB3 {v388 v640 v642 : Word}
    (t640 : v640.toNat = v388.toNat * 378089830 % 2 ^ 32)
    (t642 : v642.toNat = v388.toNat * 378089830 / 2 ^ 32) :
    v640.toNat + 2 ^ 32 * v642.toNat = v388.toNat * (((377041255) + (1048575)) % 2 ^ 32) := by
  have := v388.isLt; have := v640.isLt; have := v642.isLt
  generalize v388.toNat = n388 at *
  generalize v640.toNat = n640 at *
  generalize v642.toNat = n642 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA1BB2 {v476 v658 v660 : Word}
    (t658 : v658.toNat = v476.toNat * 796658059 / 2 ^ 32)
    (t660 : v660.toNat = v476.toNat * 796658059 % 2 ^ 32) :
    v660.toNat + 2 ^ 32 * v658.toNat = v476.toNat * (((259787148) + (536870911)) % 2 ^ 32) := by
  have := v476.isLt; have := v658.isLt; have := v660.isLt
  generalize v476.toNat = n476 at *
  generalize v658.toNat = n658 at *
  generalize v660.toNat = n660 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA2BB1 {v576 v671 v673 : Word}
    (t671 : v671.toNat = v576.toNat * 979464962 % 2 ^ 32)
    (t673 : v673.toNat = v576.toNat * 979464962 / 2 ^ 32) :
    v671.toNat + 2 ^ 32 * v673.toNat = v576.toNat * (((442594051) + (536870911)) % 2 ^ 32) := by
  have := v576.isLt; have := v671.isLt; have := v673.isLt
  generalize v576.toNat = n576 at *
  generalize v671.toNat = n671 at *
  generalize v673.toNat = n673 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA3BB0 {v592 v649 v651 : Word}
    (t649 : v649.toNat = v592.toNat * 827193836 % 2 ^ 32)
    (t651 : v651.toNat = v592.toNat * 827193836 / 2 ^ 32) :
    v649.toNat + 2 ^ 32 * v651.toNat = v592.toNat * (((290322925) + (536870911)) % 2 ^ 32) := by
  have := v592.isLt; have := v649.isLt; have := v651.isLt
  generalize v592.toNat = n592 at *
  generalize v649.toNat = n649 at *
  generalize v651.toNat = n651 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA0B4 {v388 v645 v647 : Word}
    (t645 : v645.toNat = v388.toNat * 536700270 % 2 ^ 32)
    (t647 : v647.toNat = v388.toNat * 536700270 / 2 ^ 32) :
    v645.toNat + 2 ^ 32 * v647.toNat = v388.toNat * (536700270) := by
  have := v388.isLt; have := v645.isLt; have := v647.isLt
  generalize v388.toNat = n388 at *
  generalize v645.toNat = n645 at *
  generalize v647.toNat = n647 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA1BB3 {v476 v662 v665 : Word}
    (t662 : v662.toNat = v476.toNat * 378089830 / 2 ^ 32)
    (t665 : v665.toNat = v476.toNat * 378089830 % 2 ^ 32) :
    v665.toNat + 2 ^ 32 * v662.toNat = v476.toNat * (((377041255) + (1048575)) % 2 ^ 32) := by
  have := v476.isLt; have := v662.isLt; have := v665.isLt
  generalize v476.toNat = n476 at *
  generalize v662.toNat = n662 at *
  generalize v665.toNat = n665 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA2BB2 {v576 v685 v687 : Word}
    (t685 : v685.toNat = v576.toNat * 796658059 % 2 ^ 32)
    (t687 : v687.toNat = v576.toNat * 796658059 / 2 ^ 32) :
    v685.toNat + 2 ^ 32 * v687.toNat = v576.toNat * (((259787148) + (536870911)) % 2 ^ 32) := by
  have := v576.isLt; have := v685.isLt; have := v687.isLt
  generalize v576.toNat = n576 at *
  generalize v685.toNat = n685 at *
  generalize v687.toNat = n687 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA3BB1 {v592 v676 v678 : Word}
    (t676 : v676.toNat = v592.toNat * 979464962 % 2 ^ 32)
    (t678 : v678.toNat = v592.toNat * 979464962 / 2 ^ 32) :
    v676.toNat + 2 ^ 32 * v678.toNat = v592.toNat * (((442594051) + (536870911)) % 2 ^ 32) := by
  have := v592.isLt; have := v676.isLt; have := v678.isLt
  generalize v592.toNat = n592 at *
  generalize v676.toNat = n676 at *
  generalize v678.toNat = n678 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA4BB0 {v87 v654 v656 : Word}
    (t654 : v654.toNat = v87.toNat * 827193836 % 2 ^ 32)
    (t656 : v656.toNat = v87.toNat * 827193836 / 2 ^ 32) :
    v654.toNat + 2 ^ 32 * v656.toNat = v87.toNat * (((290322925) + (536870911)) % 2 ^ 32) := by
  have := v87.isLt; have := v654.isLt; have := v656.isLt
  generalize v87.toNat = n87 at *
  generalize v654.toNat = n654 at *
  generalize v656.toNat = n656 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z9 {v116 v124 v481 v545 v645 v647 v654 v656 v662 v665 v676 v678 v685 v687 v836 v838 v839 v841 v843 v845 v846 v848 v850 v852 v853 v855 v856 v858 v859 v861 v863 v864 v865 v867 v868 v872 v874 v885 : Word}
    (t836 : v839.toNat + v116.toNat = v654.toNat + 2 ^ 32 * v836.toNat)
    (t838 : v838.toNat = (v656.toNat + 2 ^ 32 - v836.toNat) % 2 ^ 32)
    (t841 : v841.toNat = (v838.toNat + v647.toNat) % 2 ^ 32)
    (t845 : v845.toNat = (v841.toNat + 2 ^ 32 - v124.toNat) % 2 ^ 32)
    (t846 : v843.toNat + 2 ^ 32 * v846.toNat = v645.toNat + v839.toNat)
    (t848 : v848.toNat = (v846.toNat + v662.toNat) % 2 ^ 32)
    (t852 : v850.toNat + 2 ^ 32 * v852.toNat = v665.toNat + v843.toNat)
    (t853 : v853.toNat = (v845.toNat + v848.toNat) % 2 ^ 32)
    (t855 : v855.toNat = (v852.toNat + v687.toNat) % 2 ^ 32)
    (t856 : v856.toNat = (v853.toNat + v855.toNat) % 2 ^ 32)
    (t859 : v858.toNat + 2 ^ 32 * v859.toNat = v685.toNat + v850.toNat)
    (t863 : v863.toNat = (v859.toNat + v678.toNat) % 2 ^ 32)
    (t864 : v861.toNat + 2 ^ 32 * v864.toNat = v676.toNat + v858.toNat)
    (t865 : v865.toNat = (v856.toNat + v863.toNat) % 2 ^ 32)
    (t867 : v867.toNat = (v864.toNat + 2 ^ 32 - v545.toNat) % 2 ^ 32)
    (t868 : v868.toNat = (v865.toNat + v867.toNat) % 2 ^ 32)
    (t872 : v885.toNat + v481.toNat = v861.toNat + 2 ^ 32 * v872.toNat)
    (t874 : v874.toNat = (v868.toNat + 2 ^ 32 - v872.toNat) % 2 ^ 32) :
    v885.toNat + 2 ^ 32 * v874.toNat = ((((v645.toNat + 2 ^ 32 * v647.toNat) + (v665.toNat + 2 ^ 32 * v662.toNat) + (v685.toNat + 2 ^ 32 * v687.toNat) + (v676.toNat + 2 ^ 32 * v678.toNat) + (v654.toNat + 2 ^ 32 * v656.toNat)) % 2 ^ 64) + (2 ^ 64 - (((v481.toNat + 2 ^ 32 * v545.toNat) + (v116.toNat + 2 ^ 32 * v124.toNat)) % 2 ^ 64))) % 2 ^ 64 := by
  obtain ⟨q838, eq838⟩ := mod_q t838; clear t838
  obtain ⟨q841, eq841⟩ := mod_q t841; clear t841
  obtain ⟨q845, eq845⟩ := mod_q t845; clear t845
  obtain ⟨q848, eq848⟩ := mod_q t848; clear t848
  obtain ⟨q853, eq853⟩ := mod_q t853; clear t853
  obtain ⟨q855, eq855⟩ := mod_q t855; clear t855
  obtain ⟨q856, eq856⟩ := mod_q t856; clear t856
  obtain ⟨q863, eq863⟩ := mod_q t863; clear t863
  obtain ⟨q865, eq865⟩ := mod_q t865; clear t865
  obtain ⟨q867, eq867⟩ := mod_q t867; clear t867
  obtain ⟨q868, eq868⟩ := mod_q t868; clear t868
  obtain ⟨q874, eq874⟩ := mod_q t874; clear t874
  obtain ⟨k0, ek0⟩ : ∃ k, ((v481.toNat + 2 ^ 32 * v545.toNat) + (v116.toNat + 2 ^ 32 * v124.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v481.toNat + 2 ^ 32 * v545.toNat) + (v116.toNat + 2 ^ 32 * v124.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  obtain ⟨k1, ek1⟩ : ∃ k, ((v645.toNat + 2 ^ 32 * v647.toNat) + (v665.toNat + 2 ^ 32 * v662.toNat) + (v685.toNat + 2 ^ 32 * v687.toNat) + (v676.toNat + 2 ^ 32 * v678.toNat) + (v654.toNat + 2 ^ 32 * v656.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v645.toNat + 2 ^ 32 * v647.toNat) + (v665.toNat + 2 ^ 32 * v662.toNat) + (v685.toNat + 2 ^ 32 * v687.toNat) + (v676.toNat + 2 ^ 32 * v678.toNat) + (v654.toNat + 2 ^ 32 * v656.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v885.toNat + 2 ^ 32 * v874.toNat + 2 ^ 64 * (q838 + q841 + q845 + q848 + q853 + q855 + q856 + q863 + q865 + q867 + q868 + q874 + k0) = ((((v645.toNat + 2 ^ 32 * v647.toNat) + (v665.toNat + 2 ^ 32 * v662.toNat) + (v685.toNat + 2 ^ 32 * v687.toNat) + (v676.toNat + 2 ^ 32 * v678.toNat) + (v654.toNat + 2 ^ 32 * v656.toNat)) % 2 ^ 64) + (2 ^ 64 - (((v481.toNat + 2 ^ 32 * v545.toNat) + (v116.toNat + 2 ^ 32 * v124.toNat)) % 2 ^ 64))) + 2 ^ 64 * (k1 + 3) := by
    have := v116.isLt; have := v124.isLt; have := v481.isLt; have := v545.isLt; have := v836.isLt; have := v872.isLt; skip
    generalize v116.toNat = n116 at *
    generalize v124.toNat = n124 at *
    generalize v481.toNat = n481 at *
    generalize v545.toNat = n545 at *
    generalize v645.toNat = n645 at *
    generalize v647.toNat = n647 at *
    generalize v654.toNat = n654 at *
    generalize v656.toNat = n656 at *
    generalize v662.toNat = n662 at *
    generalize v665.toNat = n665 at *
    generalize v676.toNat = n676 at *
    generalize v678.toNat = n678 at *
    generalize v685.toNat = n685 at *
    generalize v687.toNat = n687 at *
    generalize v836.toNat = n836 at *
    generalize v838.toNat = n838 at *
    generalize v839.toNat = n839 at *
    generalize v841.toNat = n841 at *
    generalize v843.toNat = n843 at *
    generalize v845.toNat = n845 at *
    generalize v846.toNat = n846 at *
    generalize v848.toNat = n848 at *
    generalize v850.toNat = n850 at *
    generalize v852.toNat = n852 at *
    generalize v853.toNat = n853 at *
    generalize v855.toNat = n855 at *
    generalize v856.toNat = n856 at *
    generalize v858.toNat = n858 at *
    generalize v859.toNat = n859 at *
    generalize v861.toNat = n861 at *
    generalize v863.toNat = n863 at *
    generalize v864.toNat = n864 at *
    generalize v865.toNat = n865 at *
    generalize v867.toNat = n867 at *
    generalize v868.toNat = n868 at *
    generalize v872.toNat = n872 at *
    generalize v874.toNat = n874 at *
    generalize v885.toNat = n885 at *
    omega
  exact smm_key key (smm_lt v885 v874)

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA1B4 {v476 v667 v669 : Word}
    (t667 : v667.toNat = v476.toNat * 536700270 % 2 ^ 32)
    (t669 : v669.toNat = v476.toNat * 536700270 / 2 ^ 32) :
    v667.toNat + 2 ^ 32 * v669.toNat = v476.toNat * (536700270) := by
  have := v476.isLt; have := v667.isLt; have := v669.isLt
  generalize v476.toNat = n476 at *
  generalize v667.toNat = n667 at *
  generalize v669.toNat = n669 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA2BB3 {v576 v689 v691 : Word}
    (t689 : v689.toNat = v576.toNat * 378089830 / 2 ^ 32)
    (t691 : v691.toNat = v576.toNat * 378089830 % 2 ^ 32) :
    v691.toNat + 2 ^ 32 * v689.toNat = v576.toNat * (((377041255) + (1048575)) % 2 ^ 32) := by
  have := v576.isLt; have := v689.isLt; have := v691.isLt
  generalize v576.toNat = n576 at *
  generalize v689.toNat = n689 at *
  generalize v691.toNat = n691 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA3BB2 {v592 v706 v708 : Word}
    (t706 : v706.toNat = v592.toNat * 796658059 % 2 ^ 32)
    (t708 : v708.toNat = v592.toNat * 796658059 / 2 ^ 32) :
    v706.toNat + 2 ^ 32 * v708.toNat = v592.toNat * (((259787148) + (536870911)) % 2 ^ 32) := by
  have := v592.isLt; have := v706.isLt; have := v708.isLt
  generalize v592.toNat = n592 at *
  generalize v706.toNat = n706 at *
  generalize v708.toNat = n708 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA4BB1 {v87 v680 v682 : Word}
    (t680 : v680.toNat = v87.toNat * 979464962 % 2 ^ 32)
    (t682 : v682.toNat = v87.toNat * 979464962 / 2 ^ 32) :
    v680.toNat + 2 ^ 32 * v682.toNat = v87.toNat * (((442594051) + (536870911)) % 2 ^ 32) := by
  have := v87.isLt; have := v680.isLt; have := v682.isLt
  generalize v87.toNat = n87 at *
  generalize v680.toNat = n680 at *
  generalize v682.toNat = n682 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z10 {v203 v206 v559 v572 v667 v669 v680 v682 v689 v691 v706 v708 v919 v920 v922 v924 v926 v927 v929 v931 v932 v934 v935 v937 v939 v940 v941 v943 v944 v948 v950 v959 : Word}
    (t919 : v920.toNat + v206.toNat = v680.toNat + 2 ^ 32 * v919.toNat)
    (t922 : v922.toNat = (v682.toNat + 2 ^ 32 - v919.toNat) % 2 ^ 32)
    (t926 : v926.toNat = (v669.toNat + v922.toNat) % 2 ^ 32)
    (t927 : v924.toNat + 2 ^ 32 * v927.toNat = v667.toNat + v920.toNat)
    (t929 : v929.toNat = (v926.toNat + 2 ^ 32 - v203.toNat) % 2 ^ 32)
    (t931 : v931.toNat = (v689.toNat + v927.toNat) % 2 ^ 32)
    (t932 : v932.toNat = (v929.toNat + v931.toNat) % 2 ^ 32)
    (t935 : v934.toNat + 2 ^ 32 * v935.toNat = v691.toNat + v924.toNat)
    (t939 : v939.toNat = (v708.toNat + v935.toNat) % 2 ^ 32)
    (t940 : v937.toNat + 2 ^ 32 * v940.toNat = v706.toNat + v934.toNat)
    (t941 : v941.toNat = (v932.toNat + v939.toNat) % 2 ^ 32)
    (t943 : v943.toNat = (v940.toNat + 2 ^ 32 - v572.toNat) % 2 ^ 32)
    (t944 : v944.toNat = (v941.toNat + v943.toNat) % 2 ^ 32)
    (t948 : v959.toNat + v559.toNat = v937.toNat + 2 ^ 32 * v948.toNat)
    (t950 : v950.toNat = (v944.toNat + 2 ^ 32 - v948.toNat) % 2 ^ 32) :
    v959.toNat + 2 ^ 32 * v950.toNat = ((((v667.toNat + 2 ^ 32 * v669.toNat) + (v691.toNat + 2 ^ 32 * v689.toNat) + (v706.toNat + 2 ^ 32 * v708.toNat) + (v680.toNat + 2 ^ 32 * v682.toNat)) % 2 ^ 64) + (2 ^ 64 - (((v559.toNat + 2 ^ 32 * v572.toNat) + (v206.toNat + 2 ^ 32 * v203.toNat)) % 2 ^ 64))) % 2 ^ 64 := by
  obtain ⟨q922, eq922⟩ := mod_q t922; clear t922
  obtain ⟨q926, eq926⟩ := mod_q t926; clear t926
  obtain ⟨q929, eq929⟩ := mod_q t929; clear t929
  obtain ⟨q931, eq931⟩ := mod_q t931; clear t931
  obtain ⟨q932, eq932⟩ := mod_q t932; clear t932
  obtain ⟨q939, eq939⟩ := mod_q t939; clear t939
  obtain ⟨q941, eq941⟩ := mod_q t941; clear t941
  obtain ⟨q943, eq943⟩ := mod_q t943; clear t943
  obtain ⟨q944, eq944⟩ := mod_q t944; clear t944
  obtain ⟨q950, eq950⟩ := mod_q t950; clear t950
  obtain ⟨k0, ek0⟩ : ∃ k, ((v559.toNat + 2 ^ 32 * v572.toNat) + (v206.toNat + 2 ^ 32 * v203.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v559.toNat + 2 ^ 32 * v572.toNat) + (v206.toNat + 2 ^ 32 * v203.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  obtain ⟨k1, ek1⟩ : ∃ k, ((v667.toNat + 2 ^ 32 * v669.toNat) + (v691.toNat + 2 ^ 32 * v689.toNat) + (v706.toNat + 2 ^ 32 * v708.toNat) + (v680.toNat + 2 ^ 32 * v682.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v667.toNat + 2 ^ 32 * v669.toNat) + (v691.toNat + 2 ^ 32 * v689.toNat) + (v706.toNat + 2 ^ 32 * v708.toNat) + (v680.toNat + 2 ^ 32 * v682.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v959.toNat + 2 ^ 32 * v950.toNat + 2 ^ 64 * (q922 + q926 + q929 + q931 + q932 + q939 + q941 + q943 + q944 + q950 + k0) = ((((v667.toNat + 2 ^ 32 * v669.toNat) + (v691.toNat + 2 ^ 32 * v689.toNat) + (v706.toNat + 2 ^ 32 * v708.toNat) + (v680.toNat + 2 ^ 32 * v682.toNat)) % 2 ^ 64) + (2 ^ 64 - (((v559.toNat + 2 ^ 32 * v572.toNat) + (v206.toNat + 2 ^ 32 * v203.toNat)) % 2 ^ 64))) + 2 ^ 64 * (k1 + 3) := by
    have := v203.isLt; have := v206.isLt; have := v559.isLt; have := v572.isLt; have := v919.isLt; have := v948.isLt; skip
    generalize v203.toNat = n203 at *
    generalize v206.toNat = n206 at *
    generalize v559.toNat = n559 at *
    generalize v572.toNat = n572 at *
    generalize v667.toNat = n667 at *
    generalize v669.toNat = n669 at *
    generalize v680.toNat = n680 at *
    generalize v682.toNat = n682 at *
    generalize v689.toNat = n689 at *
    generalize v691.toNat = n691 at *
    generalize v706.toNat = n706 at *
    generalize v708.toNat = n708 at *
    generalize v919.toNat = n919 at *
    generalize v920.toNat = n920 at *
    generalize v922.toNat = n922 at *
    generalize v924.toNat = n924 at *
    generalize v926.toNat = n926 at *
    generalize v927.toNat = n927 at *
    generalize v929.toNat = n929 at *
    generalize v931.toNat = n931 at *
    generalize v932.toNat = n932 at *
    generalize v934.toNat = n934 at *
    generalize v935.toNat = n935 at *
    generalize v937.toNat = n937 at *
    generalize v939.toNat = n939 at *
    generalize v940.toNat = n940 at *
    generalize v941.toNat = n941 at *
    generalize v943.toNat = n943 at *
    generalize v944.toNat = n944 at *
    generalize v948.toNat = n948 at *
    generalize v950.toNat = n950 at *
    generalize v959.toNat = n959 at *
    omega
  exact smm_key key (smm_lt v959 v950)

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA2B4 {v576 v693 v695 : Word}
    (t693 : v693.toNat = v576.toNat * 536700270 / 2 ^ 32)
    (t695 : v695.toNat = v576.toNat * 536700270 % 2 ^ 32) :
    v695.toNat + 2 ^ 32 * v693.toNat = v576.toNat * (536700270) := by
  have := v576.isLt; have := v693.isLt; have := v695.isLt
  generalize v576.toNat = n576 at *
  generalize v693.toNat = n693 at *
  generalize v695.toNat = n695 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA3BB3 {v592 v710 v713 : Word}
    (t710 : v710.toNat = v592.toNat * 378089830 % 2 ^ 32)
    (t713 : v713.toNat = v592.toNat * 378089830 / 2 ^ 32) :
    v710.toNat + 2 ^ 32 * v713.toNat = v592.toNat * (((377041255) + (1048575)) % 2 ^ 32) := by
  have := v592.isLt; have := v710.isLt; have := v713.isLt
  generalize v592.toNat = n592 at *
  generalize v710.toNat = n710 at *
  generalize v713.toNat = n713 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA4BB2 {v87 v715 v717 : Word}
    (t715 : v715.toNat = v87.toNat * 796658059 / 2 ^ 32)
    (t717 : v717.toNat = v87.toNat * 796658059 % 2 ^ 32) :
    v717.toNat + 2 ^ 32 * v715.toNat = v87.toNat * (((259787148) + (536870911)) % 2 ^ 32) := by
  have := v87.isLt; have := v715.isLt; have := v717.isLt
  generalize v87.toNat = n87 at *
  generalize v715.toNat = n715 at *
  generalize v717.toNat = n717 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_Z11 {v693 v695 v710 v713 v715 v717 v983 v986 v988 v990 v994 v996 v998 v1003 v1005 v1006 v1007 v1009 v1012 v1015 : Word}
    (t983 : v983.toNat = (v693.toNat + v715.toNat) % 2 ^ 32)
    (t988 : v986.toNat + 2 ^ 32 * v988.toNat = v717.toNat + v695.toNat)
    (t990 : v990.toNat = (v983.toNat + v988.toNat) % 2 ^ 32)
    (t996 : v1006.toNat + v994.toNat = v986.toNat + 2 ^ 32 * v996.toNat)
    (t998 : v998.toNat = (v990.toNat + 2 ^ 32 - v996.toNat) % 2 ^ 32)
    (t1005 : v1005.toNat = (v998.toNat + v713.toNat) % 2 ^ 32)
    (t1007 : v1007.toNat = (v1005.toNat + 2 ^ 32 - v1003.toNat) % 2 ^ 32)
    (t1012 : v1009.toNat + 2 ^ 32 * v1012.toNat = v710.toNat + v1006.toNat)
    (t1015 : v1015.toNat = (v1007.toNat + v1012.toNat) % 2 ^ 32) :
    v1009.toNat + 2 ^ 32 * v1015.toNat = ((((v695.toNat + 2 ^ 32 * v693.toNat) + (v710.toNat + 2 ^ 32 * v713.toNat) + (v717.toNat + 2 ^ 32 * v715.toNat)) % 2 ^ 64) + (2 ^ 64 - (v994.toNat + 2 ^ 32 * v1003.toNat))) % 2 ^ 64 := by
  obtain ⟨q983, eq983⟩ := mod_q t983; clear t983
  obtain ⟨q990, eq990⟩ := mod_q t990; clear t990
  obtain ⟨q998, eq998⟩ := mod_q t998; clear t998
  obtain ⟨q1005, eq1005⟩ := mod_q t1005; clear t1005
  obtain ⟨q1007, eq1007⟩ := mod_q t1007; clear t1007
  obtain ⟨q1015, eq1015⟩ := mod_q t1015; clear t1015
  obtain ⟨k0, ek0⟩ : ∃ k, ((v695.toNat + 2 ^ 32 * v693.toNat) + (v710.toNat + 2 ^ 32 * v713.toNat) + (v717.toNat + 2 ^ 32 * v715.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v695.toNat + 2 ^ 32 * v693.toNat) + (v710.toNat + 2 ^ 32 * v713.toNat) + (v717.toNat + 2 ^ 32 * v715.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v1009.toNat + 2 ^ 32 * v1015.toNat + 2 ^ 64 * (q983 + q990 + q998 + q1005 + q1007 + q1015) = ((((v695.toNat + 2 ^ 32 * v693.toNat) + (v710.toNat + 2 ^ 32 * v713.toNat) + (v717.toNat + 2 ^ 32 * v715.toNat)) % 2 ^ 64) + (2 ^ 64 - (v994.toNat + 2 ^ 32 * v1003.toNat))) + 2 ^ 64 * (k0 + 1) := by
    have := v994.isLt; have := v996.isLt; have := v1003.isLt; skip
    generalize v693.toNat = n693 at *
    generalize v695.toNat = n695 at *
    generalize v710.toNat = n710 at *
    generalize v713.toNat = n713 at *
    generalize v715.toNat = n715 at *
    generalize v717.toNat = n717 at *
    generalize v983.toNat = n983 at *
    generalize v986.toNat = n986 at *
    generalize v988.toNat = n988 at *
    generalize v990.toNat = n990 at *
    generalize v994.toNat = n994 at *
    generalize v996.toNat = n996 at *
    generalize v998.toNat = n998 at *
    generalize v1003.toNat = n1003 at *
    generalize v1005.toNat = n1005 at *
    generalize v1006.toNat = n1006 at *
    generalize v1007.toNat = n1007 at *
    generalize v1009.toNat = n1009 at *
    generalize v1012.toNat = n1012 at *
    generalize v1015.toNat = n1015 at *
    omega
  exact smm_key key (smm_lt v1009 v1015)

set_option maxHeartbeats 10000000 in
theorem evr_v_PAA3B4 {v592 v704 v705 : Word}
    (t704 : v704.toNat = v592.toNat * 536700270 % 2 ^ 32)
    (t705 : v705.toNat = v592.toNat * 536700270 / 2 ^ 32) :
    v704.toNat + 2 ^ 32 * v705.toNat = v592.toNat * (536700270) := by
  have := v592.isLt; have := v704.isLt; have := v705.isLt
  generalize v592.toNat = n592 at *
  generalize v704.toNat = n704 at *
  generalize v705.toNat = n705 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PA4BB3 {v87 v720 v726 : Word}
    (t720 : v720.toNat = v87.toNat * 378089830 / 2 ^ 32)
    (t726 : v726.toNat = v87.toNat * 378089830 % 2 ^ 32) :
    v726.toNat + 2 ^ 32 * v720.toNat = v87.toNat * (((377041255) + (1048575)) % 2 ^ 32) := by
  have := v87.isLt; have := v720.isLt; have := v726.isLt
  generalize v87.toNat = n87 at *
  generalize v720.toNat = n720 at *
  generalize v726.toNat = n726 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_K12 {v704 v705 v720 v726 v734 v801 v807 v809 : Word}
    (t734 : v734.toNat = (v720.toNat + v705.toNat) % 2 ^ 32)
    (t807 : v801.toNat + 2 ^ 32 * v807.toNat = v726.toNat + v704.toNat)
    (t809 : v809.toNat = (v734.toNat + v807.toNat) % 2 ^ 32) :
    v801.toNat + 2 ^ 32 * v809.toNat = ((v704.toNat + 2 ^ 32 * v705.toNat) + (v726.toNat + 2 ^ 32 * v720.toNat)) % 2 ^ 64 := by
  obtain ⟨q734, eq734⟩ := mod_q t734; clear t734
  obtain ⟨q809, eq809⟩ := mod_q t809; clear t809
  have key : v801.toNat + 2 ^ 32 * v809.toNat + 2 ^ 64 * (q734 + q809) = ((v704.toNat + 2 ^ 32 * v705.toNat) + (v726.toNat + 2 ^ 32 * v720.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v704.toNat = n704 at *
    generalize v705.toNat = n705 at *
    generalize v720.toNat = n720 at *
    generalize v726.toNat = n726 at *
    generalize v734.toNat = n734 at *
    generalize v801.toNat = n801 at *
    generalize v807.toNat = n807 at *
    generalize v809.toNat = n809 at *
    omega
  exact smm_key key (smm_lt v801 v809)

set_option maxHeartbeats 10000000 in
theorem evr_v_Z12 {v284 v297 v801 v809 v815 v816 v823 v831 : Word}
    (t815 : v831.toNat + v297.toNat = v801.toNat + 2 ^ 32 * v815.toNat)
    (t816 : v816.toNat = (v809.toNat + 2 ^ 32 - v815.toNat) % 2 ^ 32)
    (t823 : v823.toNat = (v816.toNat + 2 ^ 32 - v284.toNat) % 2 ^ 32) :
    v831.toNat + 2 ^ 32 * v823.toNat = ((v801.toNat + 2 ^ 32 * v809.toNat) + (2 ^ 64 - (v297.toNat + 2 ^ 32 * v284.toNat))) % 2 ^ 64 := by
  obtain ⟨q816, eq816⟩ := mod_q t816; clear t816
  obtain ⟨q823, eq823⟩ := mod_q t823; clear t823
  have key : v831.toNat + 2 ^ 32 * v823.toNat + 2 ^ 64 * (q816 + q823) = ((v801.toNat + 2 ^ 32 * v809.toNat) + (2 ^ 64 - (v297.toNat + 2 ^ 32 * v284.toNat))) + 2 ^ 64 * (1) := by
    have := v284.isLt; have := v297.isLt; have := v815.isLt; skip
    generalize v284.toNat = n284 at *
    generalize v297.toNat = n297 at *
    generalize v801.toNat = n801 at *
    generalize v809.toNat = n809 at *
    generalize v815.toNat = n815 at *
    generalize v816.toNat = n816 at *
    generalize v823.toNat = n823 at *
    generalize v831.toNat = n831 at *
    omega
  exact smm_key key (smm_lt v831 v823)

set_option maxHeartbeats 10000000 in
theorem evr_v_N0 {v120 v136 v147 v151 : Word}
    (t136 : v136.toNat = v120.toNat * 307527195 % 2 ^ 32)
    (t151 : v151.toNat = v136.toNat % 2 ^ 29) :
    v151.toNat = ((v120.toNat + 2 ^ 32 * v147.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v120.isLt; have := v136.isLt; have := v147.isLt; have := v151.isLt
  generalize v120.toNat = n120 at *
  generalize v136.toNat = n136 at *
  generalize v147.toNat = n147 at *
  generalize v151.toNat = n151 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN0L0 {v151 v152 v153 : Word}
    (t152 : v152.toNat = v151.toNat * 485872621 % 2 ^ 32)
    (t153 : v153.toNat = v151.toNat * 485872621 / 2 ^ 32) :
    v152.toNat + 2 ^ 32 * v153.toNat = v151.toNat * 485872621 := by
  have := v151.isLt; have := v152.isLt; have := v153.isLt
  generalize v151.toNat = n151 at *
  generalize v152.toNat = n152 at *
  generalize v153.toNat = n153 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_T0 {v120 v147 v152 v153 v164 v165 v166 v168 : Word}
    (t164 : v164.toNat = (v153.toNat + v147.toNat) % 2 ^ 32)
    (t166 : v165.toNat + 2 ^ 32 * v166.toNat = v152.toNat + v120.toNat)
    (t168 : v168.toNat = (v166.toNat + v164.toNat) % 2 ^ 32) :
    v165.toNat + 2 ^ 32 * v168.toNat = ((v120.toNat + 2 ^ 32 * v147.toNat) + (v152.toNat + 2 ^ 32 * v153.toNat)) % 2 ^ 64 := by
  obtain ⟨q164, eq164⟩ := mod_q t164; clear t164
  obtain ⟨q168, eq168⟩ := mod_q t168; clear t168
  have key : v165.toNat + 2 ^ 32 * v168.toNat + 2 ^ 64 * (q164 + q168) = ((v120.toNat + 2 ^ 32 * v147.toNat) + (v152.toNat + 2 ^ 32 * v153.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v120.toNat = n120 at *
    generalize v147.toNat = n147 at *
    generalize v152.toNat = n152 at *
    generalize v153.toNat = n153 at *
    generalize v164.toNat = n164 at *
    generalize v165.toNat = n165 at *
    generalize v166.toNat = n166 at *
    generalize v168.toNat = n168 at *
    omega
  exact smm_key key (smm_lt v165 v168)

set_option maxHeartbeats 10000000 in
theorem evr_b_A0 {v2 v8 : Word}
    (wA0 : v8.toNat = v2.toNat % 2 ^ 29) :
    v8.toNat ≤ 536870911 := by
  have := v2.isLt; have := v8.isLt
  generalize v2.toNat = n2 at *
  generalize v8.toNat = n8 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_b_PA0B0 {v8 v120 v147 : Word}
    (wPA0B0 : v120.toNat + 2 ^ 32 * v147.toNat = v8.toNat * (290322925))
    (bA0 : v8.toNat ≤ 536870911) :
    v120.toNat + 2 ^ 32 * v147.toNat ≤ 155865933228934675 := by
  have := v8.isLt; have := v120.isLt; have := v147.isLt
  generalize v8.toNat = n8 at *
  generalize v120.toNat = n120 at *
  generalize v147.toNat = n147 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_b_N0 {v120 v147 v151 : Word}
    (wN0 : v151.toNat = ((v120.toNat + 2 ^ 32 * v147.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29)
    (bPA0B0 : v120.toNat + 2 ^ 32 * v147.toNat ≤ 155865933228934675) :
    v151.toNat ≤ 536870911 := by
  have := v120.isLt; have := v147.isLt; have := v151.isLt
  generalize v120.toNat = n120 at *
  generalize v147.toNat = n147 at *
  generalize v151.toNat = n151 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_b_PN0L0 {v151 v152 v153 : Word}
    (wPN0L0 : v152.toNat + 2 ^ 32 * v153.toNat = v151.toNat * 485872621)
    (bN0 : v151.toNat ≤ 536870911) :
    v152.toNat + 2 ^ 32 * v153.toNat ≤ 260850876666227731 := by
  have := v151.isLt; have := v152.isLt; have := v153.isLt
  generalize v151.toNat = n151 at *
  generalize v152.toNat = n152 at *
  generalize v153.toNat = n153 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_b_T0 {v120 v147 v152 v153 v165 v168 : Word}
    (wT0 : v165.toNat + 2 ^ 32 * v168.toNat = ((v120.toNat + 2 ^ 32 * v147.toNat) + (v152.toNat + 2 ^ 32 * v153.toNat)) % 2 ^ 64)
    (bPA0B0 : v120.toNat + 2 ^ 32 * v147.toNat ≤ 155865933228934675)
    (bPN0L0 : v152.toNat + 2 ^ 32 * v153.toNat ≤ 260850876666227731) :
    v165.toNat + 2 ^ 32 * v168.toNat ≤ 416716809895162406 := by
  have := v120.isLt; have := v147.isLt; have := v152.isLt; have := v153.isLt; have := v165.isLt; have := v168.isLt
  generalize v120.toNat = n120 at *
  generalize v147.toNat = n147 at *
  generalize v152.toNat = n152 at *
  generalize v153.toNat = n153 at *
  generalize v165.toNat = n165 at *
  generalize v168.toNat = n168 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_C0 {v165 v168 v177 v178 v182 : Word}
    (t177 : v177.toNat = v168.toNat * 2 ^ 3 % 2 ^ 32)
    (t178 : v178.toNat = v165.toNat / 2 ^ 29)
    (t182 : v182.toNat = v178.toNat + v177.toNat)
    (bT0 : v165.toNat + 2 ^ 32 * v168.toNat ≤ 416716809895162406) :
    v182.toNat = (v165.toNat + 2 ^ 32 * v168.toNat) / 2 ^ 29 := by
  have := v165.isLt; have := v168.isLt; have := v177.isLt; have := v178.isLt; have := v182.isLt
  generalize v165.toNat = n165 at *
  generalize v168.toNat = n168 at *
  generalize v177.toNat = n177 at *
  generalize v178.toNat = n178 at *
  generalize v182.toNat = n182 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN0L1 {v151 v176 v205 : Word}
    (t176 : v176.toNat = v151.toNat * 9640146 % 2 ^ 32)
    (t205 : v205.toNat = v151.toNat * 9640146 / 2 ^ 32) :
    v176.toNat + 2 ^ 32 * v205.toNat = v151.toNat * 9640146 := by
  have := v151.isLt; have := v176.isLt; have := v205.isLt
  generalize v151.toNat = n151 at *
  generalize v176.toNat = n176 at *
  generalize v205.toNat = n205 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S1 {v40 v51 v176 v182 v193 v195 v205 v224 v225 v227 v230 v233 : Word}
    (t224 : v224.toNat = (v205.toNat + v51.toNat) % 2 ^ 32)
    (t225 : v193.toNat + 2 ^ 32 * v225.toNat = v40.toNat + v176.toNat)
    (t227 : v227.toNat = (v225.toNat + v224.toNat) % 2 ^ 32)
    (t230 : v195.toNat + 2 ^ 32 * v230.toNat = v193.toNat + v182.toNat)
    (t233 : v233.toNat = (v230.toNat + v227.toNat) % 2 ^ 32) :
    v195.toNat + 2 ^ 32 * v233.toNat = (v182.toNat + (v40.toNat + 2 ^ 32 * v51.toNat) + (v176.toNat + 2 ^ 32 * v205.toNat)) % 2 ^ 64 := by
  obtain ⟨q224, eq224⟩ := mod_q t224; clear t224
  obtain ⟨q227, eq227⟩ := mod_q t227; clear t227
  obtain ⟨q233, eq233⟩ := mod_q t233; clear t233
  have key : v195.toNat + 2 ^ 32 * v233.toNat + 2 ^ 64 * (q224 + q227 + q233) = (v182.toNat + (v40.toNat + 2 ^ 32 * v51.toNat) + (v176.toNat + 2 ^ 32 * v205.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v40.toNat = n40 at *
    generalize v51.toNat = n51 at *
    generalize v176.toNat = n176 at *
    generalize v182.toNat = n182 at *
    generalize v193.toNat = n193 at *
    generalize v195.toNat = n195 at *
    generalize v205.toNat = n205 at *
    generalize v224.toNat = n224 at *
    generalize v225.toNat = n225 at *
    generalize v227.toNat = n227 at *
    generalize v230.toNat = n230 at *
    generalize v233.toNat = n233 at *
    omega
  exact smm_key key (smm_lt v195 v233)

set_option maxHeartbeats 10000000 in
theorem evr_v_N1 {v195 v199 v219 v233 : Word}
    (t199 : v199.toNat = v195.toNat * 307527195 % 2 ^ 32)
    (t219 : v219.toNat = v199.toNat % 2 ^ 29) :
    v219.toNat = ((v195.toNat + 2 ^ 32 * v233.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v195.isLt; have := v199.isLt; have := v219.isLt; have := v233.isLt
  generalize v195.toNat = n195 at *
  generalize v199.toNat = n199 at *
  generalize v219.toNat = n219 at *
  generalize v233.toNat = n233 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN1L0 {v219 v221 v226 : Word}
    (t221 : v221.toNat = v219.toNat * 485872621 / 2 ^ 32)
    (t226 : v226.toNat = v219.toNat * 485872621 % 2 ^ 32) :
    v226.toNat + 2 ^ 32 * v221.toNat = v219.toNat * 485872621 := by
  have := v219.isLt; have := v221.isLt; have := v226.isLt
  generalize v219.toNat = n219 at *
  generalize v221.toNat = n221 at *
  generalize v226.toNat = n226 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_T1 {v195 v221 v226 v233 v235 v238 v240 v245 : Word}
    (t235 : v235.toNat = (v221.toNat + v233.toNat) % 2 ^ 32)
    (t240 : v238.toNat + 2 ^ 32 * v240.toNat = v195.toNat + v226.toNat)
    (t245 : v245.toNat = (v235.toNat + v240.toNat) % 2 ^ 32) :
    v238.toNat + 2 ^ 32 * v245.toNat = ((v195.toNat + 2 ^ 32 * v233.toNat) + (v226.toNat + 2 ^ 32 * v221.toNat)) % 2 ^ 64 := by
  obtain ⟨q235, eq235⟩ := mod_q t235; clear t235
  obtain ⟨q245, eq245⟩ := mod_q t245; clear t245
  have key : v238.toNat + 2 ^ 32 * v245.toNat + 2 ^ 64 * (q235 + q245) = ((v195.toNat + 2 ^ 32 * v233.toNat) + (v226.toNat + 2 ^ 32 * v221.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v195.toNat = n195 at *
    generalize v221.toNat = n221 at *
    generalize v226.toNat = n226 at *
    generalize v233.toNat = n233 at *
    generalize v235.toNat = n235 at *
    generalize v238.toNat = n238 at *
    generalize v240.toNat = n240 at *
    generalize v245.toNat = n245 at *
    omega
  exact smm_key key (smm_lt v238 v245)

set_option maxHeartbeats 10000000 in
theorem evr_v_C1 {v238 v245 v249 v251 v252 v290 : Word}
    (t249 : v249.toNat = v238.toNat / 2 ^ 29)
    (t251 : v251.toNat = v245.toNat * 2 ^ 3 % 2 ^ 32)
    (t252 : v252.toNat = v249.toNat + v251.toNat)
    (t290 : v290.toNat = v245.toNat / 2 ^ 29) :
    v252.toNat + 2 ^ 32 * v290.toNat = (v238.toNat + 2 ^ 32 * v245.toNat) / 2 ^ 29 := by
  have := v238.isLt; have := v245.isLt; have := v249.isLt; have := v251.isLt; have := v252.isLt; have := v290.isLt
  generalize v238.toNat = n238 at *
  generalize v245.toNat = n245 at *
  generalize v249.toNat = n249 at *
  generalize v251.toNat = n251 at *
  generalize v252.toNat = n252 at *
  generalize v290.toNat = n290 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN0L2 {v151 v241 v263 : Word}
    (t241 : v241.toNat = v151.toNat * 501691798 % 2 ^ 32)
    (t263 : v263.toNat = v151.toNat * 501691798 / 2 ^ 32) :
    v241.toNat + 2 ^ 32 * v263.toNat = v151.toNat * 501691798 := by
  have := v151.isLt; have := v241.isLt; have := v263.isLt
  generalize v151.toNat = n151 at *
  generalize v241.toNat = n241 at *
  generalize v263.toNat = n263 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_PN1L1 {v219 v244 v273 : Word}
    (t244 : v244.toNat = v219.toNat * 9640146 % 2 ^ 32)
    (t273 : v273.toNat = v219.toNat * 9640146 / 2 ^ 32) :
    v244.toNat + 2 ^ 32 * v273.toNat = v219.toNat * 9640146 := by
  have := v219.isLt; have := v244.isLt; have := v273.isLt
  generalize v219.toNat = n219 at *
  generalize v244.toNat = n244 at *
  generalize v273.toNat = n273 at *
  omega

set_option maxHeartbeats 10000000 in
theorem evr_v_S2 {v62 v67 v241 v244 v252 v258 v259 v262 v263 v273 v278 v280 v286 v287 v288 v289 v290 v291 v292 v293 : Word}
    (t278 : v278.toNat = (v67.toNat + v263.toNat) % 2 ^ 32)
    (t280 : v258.toNat + 2 ^ 32 * v280.toNat = v62.toNat + v241.toNat)
    (t286 : v286.toNat = (v280.toNat + v278.toNat) % 2 ^ 32)
    (t287 : v287.toNat = (v286.toNat + v273.toNat) % 2 ^ 32)
    (t288 : v259.toNat + 2 ^ 32 * v288.toNat = v244.toNat + v258.toNat)
    (t289 : v289.toNat = (v287.toNat + v288.toNat) % 2 ^ 32)
    (t291 : v291.toNat = (v289.toNat + v290.toNat) % 2 ^ 32)
    (t292 : v262.toNat + 2 ^ 32 * v292.toNat = v259.toNat + v252.toNat)
    (t293 : v293.toNat = (v291.toNat + v292.toNat) % 2 ^ 32) :
    v262.toNat + 2 ^ 32 * v293.toNat = ((v252.toNat + 2 ^ 32 * v290.toNat) + (v62.toNat + 2 ^ 32 * v67.toNat) + (v241.toNat + 2 ^ 32 * v263.toNat) + (v244.toNat + 2 ^ 32 * v273.toNat)) % 2 ^ 64 := by
  obtain ⟨q278, eq278⟩ := mod_q t278; clear t278
  obtain ⟨q286, eq286⟩ := mod_q t286; clear t286
  obtain ⟨q287, eq287⟩ := mod_q t287; clear t287
  obtain ⟨q289, eq289⟩ := mod_q t289; clear t289
  obtain ⟨q291, eq291⟩ := mod_q t291; clear t291
  obtain ⟨q293, eq293⟩ := mod_q t293; clear t293
  have key : v262.toNat + 2 ^ 32 * v293.toNat + 2 ^ 64 * (q278 + q286 + q287 + q289 + q291 + q293) = ((v252.toNat + 2 ^ 32 * v290.toNat) + (v62.toNat + 2 ^ 32 * v67.toNat) + (v241.toNat + 2 ^ 32 * v263.toNat) + (v244.toNat + 2 ^ 32 * v273.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v62.toNat = n62 at *
    generalize v67.toNat = n67 at *
    generalize v241.toNat = n241 at *
    generalize v244.toNat = n244 at *
    generalize v252.toNat = n252 at *
    generalize v258.toNat = n258 at *
    generalize v259.toNat = n259 at *
    generalize v262.toNat = n262 at *
    generalize v263.toNat = n263 at *
    generalize v273.toNat = n273 at *
    generalize v278.toNat = n278 at *
    generalize v280.toNat = n280 at *
    generalize v286.toNat = n286 at *
    generalize v287.toNat = n287 at *
    generalize v288.toNat = n288 at *
    generalize v289.toNat = n289 at *
    generalize v290.toNat = n290 at *
    generalize v291.toNat = n291 at *
    generalize v292.toNat = n292 at *
    generalize v293.toNat = n293 at *
    omega
  exact smm_key key (smm_lt v262 v293)

set_option maxHeartbeats 10000000 in
theorem evr_v_N2 {v262 v264 v279 v293 : Word}
    (t264 : v264.toNat = v262.toNat * 307527195 % 2 ^ 32)
    (t279 : v279.toNat = v264.toNat % 2 ^ 29) :
    v279.toNat = ((v262.toNat + 2 ^ 32 * v293.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v262.isLt; have := v264.isLt; have := v279.isLt; have := v293.isLt
  generalize v262.toNat = n262 at *
  generalize v264.toNat = n264 at *
  generalize v279.toNat = n279 at *
  generalize v293.toNat = n293 at *
  omega

end C3.RV32
