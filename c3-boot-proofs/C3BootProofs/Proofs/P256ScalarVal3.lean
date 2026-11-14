import C3BootProofs.Proofs.P256ScalarDecode

/-! # P-256's `Scalar::mul`, values, part 3

Each lemma proves one value the code holds in words from its instructions' facts. `scripts/gen-p256-scalar.py` writes this file. -/

namespace C3.RV32

open C3.Image

theorem psm_v_P77 {v171 v449 v476 v497 v498 v499 v500 v501 v502 v504 : Word}
    (t476 : v476.toNat = v171.toNat * 4294967295 / 2 ^ 32 ∧ v476.toNat + (v171.toNat + 4294967295) / 4294967296 = v171.toNat)
    (t498 : v498.toNat = (v449.toNat + 2 ^ 32 - v171.toNat) % 2 ^ 32)
    (t499 : (v498.toNat < v449.toNat ∧ v499.toNat = 1) ∨ (v449.toNat ≤ v498.toNat ∧ v499.toNat = 0))
    (t500 : v500.toNat = (v498.toNat + v497.toNat) % 2 ^ 32)
    (t501 : v501.toNat = (v499.toNat + v476.toNat) % 2 ^ 32)
    (t502 : v500.toNat + 2 ^ 32 * v502.toNat = v498.toNat + v497.toNat)
    (t504 : v504.toNat = (v502.toNat + v501.toNat) % 2 ^ 32) :
    v500.toNat + 2 ^ 32 * v504.toNat = v171.toNat * 4294967295 + v449.toNat + v497.toNat := by
  have := v171.isLt; have := v449.isLt; have := v476.isLt; have := v497.isLt; have := v498.isLt; have := v499.isLt; have := v500.isLt; have := v501.isLt; have := v502.isLt; have := v504.isLt
  generalize v171.toNat = n171 at *
  generalize v449.toNat = n449 at *
  generalize v476.toNat = n476 at *
  generalize v497.toNat = n497 at *
  generalize v498.toNat = n498 at *
  generalize v499.toNat = n499 at *
  generalize v500.toNat = n500 at *
  generalize v501.toNat = n501 at *
  generalize v502.toNat = n502 at *
  generalize v504.toNat = n504 at *
  first
    | omega
    | (obtain ⟨t476a, t476b⟩ := t476; rcases Nat.eq_zero_or_pos n171 with _ | _ <;> rcases t499 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t476a, t476b⟩ := t476; obtain ⟨qt498, et498⟩ := mod_q t498; clear t498; obtain ⟨qt500, et500⟩ := mod_q t500; clear t500; obtain ⟨qt501, et501⟩ := mod_q t501; clear t501; omega)
    | (obtain ⟨t476a, t476b⟩ := t476; obtain ⟨qt498, et498⟩ := mod_q t498; clear t498; obtain ⟨qt500, et500⟩ := mod_q t500; clear t500; obtain ⟨qt501, et501⟩ := mod_q t501; clear t501; rcases Nat.eq_zero_or_pos n171 with _ | _ <;> rcases t499 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P77l {v171 v449 v497 v498 v500 v504 : Word}
    (t498 : v498.toNat = (v449.toNat + 2 ^ 32 - v171.toNat) % 2 ^ 32)
    (t500 : v500.toNat = (v498.toNat + v497.toNat) % 2 ^ 32)
    (wP77 : v500.toNat + 2 ^ 32 * v504.toNat = v171.toNat * 4294967295 + v449.toNat + v497.toNat) :
    v500.toNat = (v500.toNat + 2 ^ 32 * v504.toNat) % 2 ^ 32 := by
  have := v171.isLt; have := v449.isLt; have := v497.isLt; have := v498.isLt; have := v500.isLt; have := v504.isLt
  generalize v171.toNat = n171 at *
  generalize v449.toNat = n449 at *
  generalize v497.toNat = n497 at *
  generalize v498.toNat = n498 at *
  generalize v500.toNat = n500 at *
  generalize v504.toNat = n504 at *
  first
    | omega
    | (obtain ⟨qt498, et498⟩ := mod_q t498; clear t498; obtain ⟨qt500, et500⟩ := mod_q t500; clear t500; omega)

theorem psm_v_P77h {v171 v449 v476 v497 v498 v499 v500 v501 v502 v504 : Word}
    (t476 : v476.toNat = v171.toNat * 4294967295 / 2 ^ 32 ∧ v476.toNat + (v171.toNat + 4294967295) / 4294967296 = v171.toNat)
    (t498 : v498.toNat = (v449.toNat + 2 ^ 32 - v171.toNat) % 2 ^ 32)
    (t499 : (v498.toNat < v449.toNat ∧ v499.toNat = 1) ∨ (v449.toNat ≤ v498.toNat ∧ v499.toNat = 0))
    (t501 : v501.toNat = (v499.toNat + v476.toNat) % 2 ^ 32)
    (t502 : v500.toNat + 2 ^ 32 * v502.toNat = v498.toNat + v497.toNat)
    (t504 : v504.toNat = (v502.toNat + v501.toNat) % 2 ^ 32)
    (wP77 : v500.toNat + 2 ^ 32 * v504.toNat = v171.toNat * 4294967295 + v449.toNat + v497.toNat) :
    v504.toNat = (v500.toNat + 2 ^ 32 * v504.toNat) / 2 ^ 32 := by
  have := v171.isLt; have := v449.isLt; have := v476.isLt; have := v497.isLt; have := v498.isLt; have := v499.isLt; have := v500.isLt; have := v501.isLt; have := v502.isLt; have := v504.isLt
  generalize v171.toNat = n171 at *
  generalize v449.toNat = n449 at *
  generalize v476.toNat = n476 at *
  generalize v497.toNat = n497 at *
  generalize v498.toNat = n498 at *
  generalize v499.toNat = n499 at *
  generalize v500.toNat = n500 at *
  generalize v501.toNat = n501 at *
  generalize v502.toNat = n502 at *
  generalize v504.toNat = n504 at *
  first
    | omega
    | (obtain ⟨t476a, t476b⟩ := t476; rcases Nat.eq_zero_or_pos n171 with _ | _ <;> rcases t499 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t476a, t476b⟩ := t476; obtain ⟨qt498, et498⟩ := mod_q t498; clear t498; obtain ⟨qt501, et501⟩ := mod_q t501; clear t501; obtain ⟨qt504, et504⟩ := mod_q t504; clear t504; omega)
    | (obtain ⟨t476a, t476b⟩ := t476; obtain ⟨qt498, et498⟩ := mod_q t498; clear t498; obtain ⟨qt501, et501⟩ := mod_q t501; clear t501; obtain ⟨qt504, et504⟩ := mod_q t504; clear t504; rcases Nat.eq_zero_or_pos n171 with _ | _ <;> rcases t499 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_S78 {v459 v504 v506 v513 : Word}
    (t506 : v506.toNat = (v459.toNat + v504.toNat) % 2 ^ 32)
    (t513 : v506.toNat + 2 ^ 32 * v513.toNat = v459.toNat + v504.toNat) :
    v506.toNat + 2 ^ 32 * v513.toNat = v459.toNat + v504.toNat := by
  have := v459.isLt; have := v504.isLt; have := v506.isLt; have := v513.isLt
  generalize v459.toNat = n459 at *
  generalize v504.toNat = n504 at *
  generalize v506.toNat = n506 at *
  generalize v513.toNat = n513 at *
  first
    | omega
    | (obtain ⟨qt506, et506⟩ := mod_q t506; clear t506; omega)

theorem psm_v_S78l {v459 v504 v506 v513 : Word}
    (t506 : v506.toNat = (v459.toNat + v504.toNat) % 2 ^ 32)
    (wS78 : v506.toNat + 2 ^ 32 * v513.toNat = v459.toNat + v504.toNat) :
    v506.toNat = (v506.toNat + 2 ^ 32 * v513.toNat) % 2 ^ 32 := by
  have := v459.isLt; have := v504.isLt; have := v506.isLt; have := v513.isLt
  generalize v459.toNat = n459 at *
  generalize v504.toNat = n504 at *
  generalize v506.toNat = n506 at *
  generalize v513.toNat = n513 at *
  first
    | omega
    | (obtain ⟨qt506, et506⟩ := mod_q t506; clear t506; omega)

theorem psm_v_S78h {v459 v504 v506 v513 : Word}
    (t513 : v506.toNat + 2 ^ 32 * v513.toNat = v459.toNat + v504.toNat)
    (wS78 : v506.toNat + 2 ^ 32 * v513.toNat = v459.toNat + v504.toNat) :
    v513.toNat = (v506.toNat + 2 ^ 32 * v513.toNat) / 2 ^ 32 := by
  have := v459.isLt; have := v504.isLt; have := v506.isLt; have := v513.isLt
  generalize v459.toNat = n459 at *
  generalize v504.toNat = n504 at *
  generalize v506.toNat = n506 at *
  generalize v513.toNat = n513 at *
  omega

theorem psm_v_S79 {v171 v505 v513 v517 v519 v525 v529 v541 : Word}
    (t517 : v517.toNat = (v171.toNat + v505.toNat) % 2 ^ 32)
    (t519 : v517.toNat + 2 ^ 32 * v519.toNat = v171.toNat + v505.toNat)
    (t525 : v525.toNat = (v513.toNat + v517.toNat) % 2 ^ 32)
    (t529 : v525.toNat + 2 ^ 32 * v529.toNat = v513.toNat + v517.toNat)
    (t541 : v541.toNat = (v519.toNat + v529.toNat) % 2 ^ 32) :
    v525.toNat + 2 ^ 32 * v541.toNat = v505.toNat + v171.toNat + v513.toNat := by
  have := v171.isLt; have := v505.isLt; have := v513.isLt; have := v517.isLt; have := v519.isLt; have := v525.isLt; have := v529.isLt; have := v541.isLt
  generalize v171.toNat = n171 at *
  generalize v505.toNat = n505 at *
  generalize v513.toNat = n513 at *
  generalize v517.toNat = n517 at *
  generalize v519.toNat = n519 at *
  generalize v525.toNat = n525 at *
  generalize v529.toNat = n529 at *
  generalize v541.toNat = n541 at *
  first
    | omega
    | (obtain ⟨qt517, et517⟩ := mod_q t517; clear t517; obtain ⟨qt525, et525⟩ := mod_q t525; clear t525; omega)

theorem psm_v_S79l {v171 v505 v513 v517 v525 v541 : Word}
    (t517 : v517.toNat = (v171.toNat + v505.toNat) % 2 ^ 32)
    (t525 : v525.toNat = (v513.toNat + v517.toNat) % 2 ^ 32)
    (wS79 : v525.toNat + 2 ^ 32 * v541.toNat = v505.toNat + v171.toNat + v513.toNat) :
    v525.toNat = (v525.toNat + 2 ^ 32 * v541.toNat) % 2 ^ 32 := by
  have := v171.isLt; have := v505.isLt; have := v513.isLt; have := v517.isLt; have := v525.isLt; have := v541.isLt
  generalize v171.toNat = n171 at *
  generalize v505.toNat = n505 at *
  generalize v513.toNat = n513 at *
  generalize v517.toNat = n517 at *
  generalize v525.toNat = n525 at *
  generalize v541.toNat = n541 at *
  first
    | omega
    | (obtain ⟨qt517, et517⟩ := mod_q t517; clear t517; obtain ⟨qt525, et525⟩ := mod_q t525; clear t525; omega)

theorem psm_v_S79h {v171 v505 v513 v517 v519 v525 v529 v541 : Word}
    (t517 : v517.toNat = (v171.toNat + v505.toNat) % 2 ^ 32)
    (t519 : v517.toNat + 2 ^ 32 * v519.toNat = v171.toNat + v505.toNat)
    (t529 : v525.toNat + 2 ^ 32 * v529.toNat = v513.toNat + v517.toNat)
    (t541 : v541.toNat = (v519.toNat + v529.toNat) % 2 ^ 32)
    (wS79 : v525.toNat + 2 ^ 32 * v541.toNat = v505.toNat + v171.toNat + v513.toNat) :
    v541.toNat = (v525.toNat + 2 ^ 32 * v541.toNat) / 2 ^ 32 := by
  have := v171.isLt; have := v505.isLt; have := v513.isLt; have := v517.isLt; have := v519.isLt; have := v525.isLt; have := v529.isLt; have := v541.isLt
  generalize v171.toNat = n171 at *
  generalize v505.toNat = n505 at *
  generalize v513.toNat = n513 at *
  generalize v517.toNat = n517 at *
  generalize v519.toNat = n519 at *
  generalize v525.toNat = n525 at *
  generalize v529.toNat = n529 at *
  generalize v541.toNat = n541 at *
  first
    | omega
    | (obtain ⟨qt517, et517⟩ := mod_q t517; clear t517; obtain ⟨qt541, et541⟩ := mod_q t541; clear t541; omega)

theorem psm_v_P80 {v465 v511 v749 : Word}
    (t511 : v511.toNat = v465.toNat * 4234356049 / 2 ^ 32)
    (t749 : v749.toNat = v465.toNat * 4234356049 % 2 ^ 32) :
    v749.toNat + 2 ^ 32 * v511.toNat = v465.toNat * 4234356049 := by
  have := v465.isLt; have := v511.isLt; have := v749.isLt
  generalize v465.toNat = n465 at *
  generalize v511.toNat = n511 at *
  generalize v749.toNat = n749 at *
  omega

theorem psm_v_P80l {v465 v511 v749 : Word}
    (t749 : v749.toNat = v465.toNat * 4234356049 % 2 ^ 32)
    (wP80 : v749.toNat + 2 ^ 32 * v511.toNat = v465.toNat * 4234356049) :
    v749.toNat = (v749.toNat + 2 ^ 32 * v511.toNat) % 2 ^ 32 := by
  have := v465.isLt; have := v511.isLt; have := v749.isLt
  generalize v465.toNat = n465 at *
  generalize v511.toNat = n511 at *
  generalize v749.toNat = n749 at *
  first
    | omega
    | (obtain ⟨qt749, et749⟩ := mod_q t749; clear t749; omega)

theorem psm_v_P80h {v465 v511 v749 : Word}
    (t511 : v511.toNat = v465.toNat * 4234356049 / 2 ^ 32)
    (wP80 : v749.toNat + 2 ^ 32 * v511.toNat = v465.toNat * 4234356049) :
    v511.toNat = (v749.toNat + 2 ^ 32 * v511.toNat) / 2 ^ 32 := by
  have := v465.isLt; have := v511.isLt; have := v749.isLt
  generalize v465.toNat = n465 at *
  generalize v511.toNat = n511 at *
  generalize v749.toNat = n749 at *
  omega

theorem psm_v_P81 {v465 v511 v512 v515 v523 v526 v527 : Word}
    (t512 : v512.toNat = v465.toNat * 4089039554 % 2 ^ 32)
    (t515 : v515.toNat = v465.toNat * 4089039554 / 2 ^ 32)
    (t523 : v523.toNat = (v512.toNat + v511.toNat) % 2 ^ 32)
    (t526 : v523.toNat + 2 ^ 32 * v526.toNat = v512.toNat + v511.toNat)
    (t527 : v527.toNat = (v526.toNat + v515.toNat) % 2 ^ 32) :
    v523.toNat + 2 ^ 32 * v527.toNat = v465.toNat * 4089039554 + v511.toNat := by
  have := v465.isLt; have := v511.isLt; have := v512.isLt; have := v515.isLt; have := v523.isLt; have := v526.isLt; have := v527.isLt
  generalize v465.toNat = n465 at *
  generalize v511.toNat = n511 at *
  generalize v512.toNat = n512 at *
  generalize v515.toNat = n515 at *
  generalize v523.toNat = n523 at *
  generalize v526.toNat = n526 at *
  generalize v527.toNat = n527 at *
  first
    | omega
    | (obtain ⟨qt512, et512⟩ := mod_q t512; clear t512; obtain ⟨qt523, et523⟩ := mod_q t523; clear t523; omega)

theorem psm_v_P81l {v465 v511 v512 v523 v527 : Word}
    (t512 : v512.toNat = v465.toNat * 4089039554 % 2 ^ 32)
    (t523 : v523.toNat = (v512.toNat + v511.toNat) % 2 ^ 32)
    (wP81 : v523.toNat + 2 ^ 32 * v527.toNat = v465.toNat * 4089039554 + v511.toNat) :
    v523.toNat = (v523.toNat + 2 ^ 32 * v527.toNat) % 2 ^ 32 := by
  have := v465.isLt; have := v511.isLt; have := v512.isLt; have := v523.isLt; have := v527.isLt
  generalize v465.toNat = n465 at *
  generalize v511.toNat = n511 at *
  generalize v512.toNat = n512 at *
  generalize v523.toNat = n523 at *
  generalize v527.toNat = n527 at *
  first
    | omega
    | (obtain ⟨qt512, et512⟩ := mod_q t512; clear t512; obtain ⟨qt523, et523⟩ := mod_q t523; clear t523; omega)

theorem psm_v_P81h {v465 v511 v512 v515 v523 v526 v527 : Word}
    (t515 : v515.toNat = v465.toNat * 4089039554 / 2 ^ 32)
    (t526 : v523.toNat + 2 ^ 32 * v526.toNat = v512.toNat + v511.toNat)
    (t527 : v527.toNat = (v526.toNat + v515.toNat) % 2 ^ 32)
    (wP81 : v523.toNat + 2 ^ 32 * v527.toNat = v465.toNat * 4089039554 + v511.toNat) :
    v527.toNat = (v523.toNat + 2 ^ 32 * v527.toNat) / 2 ^ 32 := by
  have := v465.isLt; have := v511.isLt; have := v512.isLt; have := v515.isLt; have := v523.isLt; have := v526.isLt; have := v527.isLt
  generalize v465.toNat = n465 at *
  generalize v511.toNat = n511 at *
  generalize v512.toNat = n512 at *
  generalize v515.toNat = n515 at *
  generalize v523.toNat = n523 at *
  generalize v526.toNat = n526 at *
  generalize v527.toNat = n527 at *
  first
    | omega
    | (obtain ⟨qt527, et527⟩ := mod_q t527; clear t527; omega)

theorem psm_v_P82 {v465 v518 v521 v527 v530 v531 v533 : Word}
    (t518 : v518.toNat = v465.toNat * 2803342980 % 2 ^ 32)
    (t521 : v521.toNat = v465.toNat * 2803342980 / 2 ^ 32)
    (t530 : v530.toNat = (v518.toNat + v527.toNat) % 2 ^ 32)
    (t531 : v530.toNat + 2 ^ 32 * v531.toNat = v518.toNat + v527.toNat)
    (t533 : v533.toNat = (v531.toNat + v521.toNat) % 2 ^ 32) :
    v530.toNat + 2 ^ 32 * v533.toNat = v465.toNat * 2803342980 + v527.toNat := by
  have := v465.isLt; have := v518.isLt; have := v521.isLt; have := v527.isLt; have := v530.isLt; have := v531.isLt; have := v533.isLt
  generalize v465.toNat = n465 at *
  generalize v518.toNat = n518 at *
  generalize v521.toNat = n521 at *
  generalize v527.toNat = n527 at *
  generalize v530.toNat = n530 at *
  generalize v531.toNat = n531 at *
  generalize v533.toNat = n533 at *
  first
    | omega
    | (obtain ⟨qt518, et518⟩ := mod_q t518; clear t518; obtain ⟨qt530, et530⟩ := mod_q t530; clear t530; omega)

theorem psm_v_P82l {v465 v518 v527 v530 v533 : Word}
    (t518 : v518.toNat = v465.toNat * 2803342980 % 2 ^ 32)
    (t530 : v530.toNat = (v518.toNat + v527.toNat) % 2 ^ 32)
    (wP82 : v530.toNat + 2 ^ 32 * v533.toNat = v465.toNat * 2803342980 + v527.toNat) :
    v530.toNat = (v530.toNat + 2 ^ 32 * v533.toNat) % 2 ^ 32 := by
  have := v465.isLt; have := v518.isLt; have := v527.isLt; have := v530.isLt; have := v533.isLt
  generalize v465.toNat = n465 at *
  generalize v518.toNat = n518 at *
  generalize v527.toNat = n527 at *
  generalize v530.toNat = n530 at *
  generalize v533.toNat = n533 at *
  first
    | omega
    | (obtain ⟨qt518, et518⟩ := mod_q t518; clear t518; obtain ⟨qt530, et530⟩ := mod_q t530; clear t530; omega)

theorem psm_v_P82h {v465 v518 v521 v527 v530 v531 v533 : Word}
    (t521 : v521.toNat = v465.toNat * 2803342980 / 2 ^ 32)
    (t531 : v530.toNat + 2 ^ 32 * v531.toNat = v518.toNat + v527.toNat)
    (t533 : v533.toNat = (v531.toNat + v521.toNat) % 2 ^ 32)
    (wP82 : v530.toNat + 2 ^ 32 * v533.toNat = v465.toNat * 2803342980 + v527.toNat) :
    v533.toNat = (v530.toNat + 2 ^ 32 * v533.toNat) / 2 ^ 32 := by
  have := v465.isLt; have := v518.isLt; have := v521.isLt; have := v527.isLt; have := v530.isLt; have := v531.isLt; have := v533.isLt
  generalize v465.toNat = n465 at *
  generalize v518.toNat = n518 at *
  generalize v521.toNat = n521 at *
  generalize v527.toNat = n527 at *
  generalize v530.toNat = n530 at *
  generalize v531.toNat = n531 at *
  generalize v533.toNat = n533 at *
  first
    | omega
    | (obtain ⟨qt533, et533⟩ := mod_q t533; clear t533; omega)

theorem psm_v_P83 {v465 v524 v528 v533 v535 v537 v539 : Word}
    (t524 : v524.toNat = v465.toNat * 3169254061 % 2 ^ 32)
    (t528 : v528.toNat = v465.toNat * 3169254061 / 2 ^ 32)
    (t535 : v535.toNat = (v524.toNat + v533.toNat) % 2 ^ 32)
    (t537 : v535.toNat + 2 ^ 32 * v537.toNat = v524.toNat + v533.toNat)
    (t539 : v539.toNat = (v537.toNat + v528.toNat) % 2 ^ 32) :
    v535.toNat + 2 ^ 32 * v539.toNat = v465.toNat * 3169254061 + v533.toNat := by
  have := v465.isLt; have := v524.isLt; have := v528.isLt; have := v533.isLt; have := v535.isLt; have := v537.isLt; have := v539.isLt
  generalize v465.toNat = n465 at *
  generalize v524.toNat = n524 at *
  generalize v528.toNat = n528 at *
  generalize v533.toNat = n533 at *
  generalize v535.toNat = n535 at *
  generalize v537.toNat = n537 at *
  generalize v539.toNat = n539 at *
  first
    | omega
    | (obtain ⟨qt524, et524⟩ := mod_q t524; clear t524; obtain ⟨qt535, et535⟩ := mod_q t535; clear t535; omega)

theorem psm_v_P83l {v465 v524 v533 v535 v539 : Word}
    (t524 : v524.toNat = v465.toNat * 3169254061 % 2 ^ 32)
    (t535 : v535.toNat = (v524.toNat + v533.toNat) % 2 ^ 32)
    (wP83 : v535.toNat + 2 ^ 32 * v539.toNat = v465.toNat * 3169254061 + v533.toNat) :
    v535.toNat = (v535.toNat + 2 ^ 32 * v539.toNat) % 2 ^ 32 := by
  have := v465.isLt; have := v524.isLt; have := v533.isLt; have := v535.isLt; have := v539.isLt
  generalize v465.toNat = n465 at *
  generalize v524.toNat = n524 at *
  generalize v533.toNat = n533 at *
  generalize v535.toNat = n535 at *
  generalize v539.toNat = n539 at *
  first
    | omega
    | (obtain ⟨qt524, et524⟩ := mod_q t524; clear t524; obtain ⟨qt535, et535⟩ := mod_q t535; clear t535; omega)

theorem psm_v_P83h {v465 v524 v528 v533 v535 v537 v539 : Word}
    (t528 : v528.toNat = v465.toNat * 3169254061 / 2 ^ 32)
    (t537 : v535.toNat + 2 ^ 32 * v537.toNat = v524.toNat + v533.toNat)
    (t539 : v539.toNat = (v537.toNat + v528.toNat) % 2 ^ 32)
    (wP83 : v535.toNat + 2 ^ 32 * v539.toNat = v465.toNat * 3169254061 + v533.toNat) :
    v539.toNat = (v535.toNat + 2 ^ 32 * v539.toNat) / 2 ^ 32 := by
  have := v465.isLt; have := v524.isLt; have := v528.isLt; have := v533.isLt; have := v535.isLt; have := v537.isLt; have := v539.isLt
  generalize v465.toNat = n465 at *
  generalize v524.toNat = n524 at *
  generalize v528.toNat = n528 at *
  generalize v533.toNat = n533 at *
  generalize v535.toNat = n535 at *
  generalize v537.toNat = n537 at *
  generalize v539.toNat = n539 at *
  first
    | omega
    | (obtain ⟨qt539, et539⟩ := mod_q t539; clear t539; omega)

theorem psm_v_P84 {v465 v534 v539 v542 v543 v546 : Word}
    (t534 : v534.toNat = v465.toNat * 4294967295 / 2 ^ 32 ∧ v534.toNat + (v465.toNat + 4294967295) / 4294967296 = v465.toNat)
    (t542 : v542.toNat = (v539.toNat + 2 ^ 32 - v465.toNat) % 2 ^ 32)
    (t543 : (v542.toNat < v539.toNat ∧ v543.toNat = 1) ∨ (v539.toNat ≤ v542.toNat ∧ v543.toNat = 0))
    (t546 : v546.toNat = (v543.toNat + v534.toNat) % 2 ^ 32) :
    v542.toNat + 2 ^ 32 * v546.toNat = v465.toNat * 4294967295 + v539.toNat := by
  have := v465.isLt; have := v534.isLt; have := v539.isLt; have := v542.isLt; have := v543.isLt; have := v546.isLt
  generalize v465.toNat = n465 at *
  generalize v534.toNat = n534 at *
  generalize v539.toNat = n539 at *
  generalize v542.toNat = n542 at *
  generalize v543.toNat = n543 at *
  generalize v546.toNat = n546 at *
  first
    | omega
    | (obtain ⟨t534a, t534b⟩ := t534; rcases Nat.eq_zero_or_pos n465 with _ | _ <;> rcases t543 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t534a, t534b⟩ := t534; obtain ⟨qt542, et542⟩ := mod_q t542; clear t542; omega)
    | (obtain ⟨t534a, t534b⟩ := t534; obtain ⟨qt542, et542⟩ := mod_q t542; clear t542; rcases Nat.eq_zero_or_pos n465 with _ | _ <;> rcases t543 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P84l {v465 v539 v542 v546 : Word}
    (t542 : v542.toNat = (v539.toNat + 2 ^ 32 - v465.toNat) % 2 ^ 32)
    (wP84 : v542.toNat + 2 ^ 32 * v546.toNat = v465.toNat * 4294967295 + v539.toNat) :
    v542.toNat = (v542.toNat + 2 ^ 32 * v546.toNat) % 2 ^ 32 := by
  have := v465.isLt; have := v539.isLt; have := v542.isLt; have := v546.isLt
  generalize v465.toNat = n465 at *
  generalize v539.toNat = n539 at *
  generalize v542.toNat = n542 at *
  generalize v546.toNat = n546 at *
  first
    | omega
    | (obtain ⟨qt542, et542⟩ := mod_q t542; clear t542; omega)

theorem psm_v_P84h {v465 v534 v539 v542 v543 v546 : Word}
    (t534 : v534.toNat = v465.toNat * 4294967295 / 2 ^ 32 ∧ v534.toNat + (v465.toNat + 4294967295) / 4294967296 = v465.toNat)
    (t543 : (v542.toNat < v539.toNat ∧ v543.toNat = 1) ∨ (v539.toNat ≤ v542.toNat ∧ v543.toNat = 0))
    (t546 : v546.toNat = (v543.toNat + v534.toNat) % 2 ^ 32)
    (wP84 : v542.toNat + 2 ^ 32 * v546.toNat = v465.toNat * 4294967295 + v539.toNat) :
    v546.toNat = (v542.toNat + 2 ^ 32 * v546.toNat) / 2 ^ 32 := by
  have := v465.isLt; have := v534.isLt; have := v539.isLt; have := v542.isLt; have := v543.isLt; have := v546.isLt
  generalize v465.toNat = n465 at *
  generalize v534.toNat = n534 at *
  generalize v539.toNat = n539 at *
  generalize v542.toNat = n542 at *
  generalize v543.toNat = n543 at *
  generalize v546.toNat = n546 at *
  first
    | omega
    | (obtain ⟨t534a, t534b⟩ := t534; rcases Nat.eq_zero_or_pos n465 with _ | _ <;> rcases t543 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t534a, t534b⟩ := t534; obtain ⟨qt546, et546⟩ := mod_q t546; clear t546; omega)
    | (obtain ⟨t534a, t534b⟩ := t534; obtain ⟨qt546, et546⟩ := mod_q t546; clear t546; rcases Nat.eq_zero_or_pos n465 with _ | _ <;> rcases t543 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P85 {v465 v534 v546 v556 v560 v562 : Word}
    (t534 : v534.toNat = v465.toNat * 4294967295 / 2 ^ 32 ∧ v534.toNat + (v465.toNat + 4294967295) / 4294967296 = v465.toNat)
    (t556 : v556.toNat = (v546.toNat + 2 ^ 32 - v465.toNat) % 2 ^ 32)
    (t560 : (v556.toNat < v546.toNat ∧ v560.toNat = 1) ∨ (v546.toNat ≤ v556.toNat ∧ v560.toNat = 0))
    (t562 : v562.toNat = (v534.toNat + v560.toNat) % 2 ^ 32) :
    v556.toNat + 2 ^ 32 * v562.toNat = v465.toNat * 4294967295 + v546.toNat := by
  have := v465.isLt; have := v534.isLt; have := v546.isLt; have := v556.isLt; have := v560.isLt; have := v562.isLt
  generalize v465.toNat = n465 at *
  generalize v534.toNat = n534 at *
  generalize v546.toNat = n546 at *
  generalize v556.toNat = n556 at *
  generalize v560.toNat = n560 at *
  generalize v562.toNat = n562 at *
  first
    | omega
    | (obtain ⟨t534a, t534b⟩ := t534; rcases Nat.eq_zero_or_pos n465 with _ | _ <;> rcases t560 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t534a, t534b⟩ := t534; obtain ⟨qt556, et556⟩ := mod_q t556; clear t556; omega)
    | (obtain ⟨t534a, t534b⟩ := t534; obtain ⟨qt556, et556⟩ := mod_q t556; clear t556; rcases Nat.eq_zero_or_pos n465 with _ | _ <;> rcases t560 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P85l {v465 v546 v556 v562 : Word}
    (t556 : v556.toNat = (v546.toNat + 2 ^ 32 - v465.toNat) % 2 ^ 32)
    (wP85 : v556.toNat + 2 ^ 32 * v562.toNat = v465.toNat * 4294967295 + v546.toNat) :
    v556.toNat = (v556.toNat + 2 ^ 32 * v562.toNat) % 2 ^ 32 := by
  have := v465.isLt; have := v546.isLt; have := v556.isLt; have := v562.isLt
  generalize v465.toNat = n465 at *
  generalize v546.toNat = n546 at *
  generalize v556.toNat = n556 at *
  generalize v562.toNat = n562 at *
  first
    | omega
    | (obtain ⟨qt556, et556⟩ := mod_q t556; clear t556; omega)

theorem psm_v_P85h {v465 v534 v546 v556 v560 v562 : Word}
    (t534 : v534.toNat = v465.toNat * 4294967295 / 2 ^ 32 ∧ v534.toNat + (v465.toNat + 4294967295) / 4294967296 = v465.toNat)
    (t560 : (v556.toNat < v546.toNat ∧ v560.toNat = 1) ∨ (v546.toNat ≤ v556.toNat ∧ v560.toNat = 0))
    (t562 : v562.toNat = (v534.toNat + v560.toNat) % 2 ^ 32)
    (wP85 : v556.toNat + 2 ^ 32 * v562.toNat = v465.toNat * 4294967295 + v546.toNat) :
    v562.toNat = (v556.toNat + 2 ^ 32 * v562.toNat) / 2 ^ 32 := by
  have := v465.isLt; have := v534.isLt; have := v546.isLt; have := v556.isLt; have := v560.isLt; have := v562.isLt
  generalize v465.toNat = n465 at *
  generalize v534.toNat = n534 at *
  generalize v546.toNat = n546 at *
  generalize v556.toNat = n556 at *
  generalize v560.toNat = n560 at *
  generalize v562.toNat = n562 at *
  first
    | omega
    | (obtain ⟨t534a, t534b⟩ := t534; rcases Nat.eq_zero_or_pos n465 with _ | _ <;> rcases t560 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t534a, t534b⟩ := t534; obtain ⟨qt562, et562⟩ := mod_q t562; clear t562; omega)
    | (obtain ⟨t534a, t534b⟩ := t534; obtain ⟨qt562, et562⟩ := mod_q t562; clear t562; rcases Nat.eq_zero_or_pos n465 with _ | _ <;> rcases t560 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P86h {v465 v534 : Word}
    (t534 : v534.toNat = v465.toNat * 4294967295 / 2 ^ 32 ∧ v534.toNat + (v465.toNat + 4294967295) / 4294967296 = v465.toNat) :
    v534.toNat = (v465.toNat * 4294967295) / 2 ^ 32 := by
  have := v465.isLt; have := v534.isLt
  generalize v465.toNat = n465 at *
  generalize v534.toNat = n534 at *
  first
    | omega
    | (obtain ⟨t534a, t534b⟩ := t534; rcases Nat.eq_zero_or_pos n465 with _ | _ <;> omega)

theorem psm_v_P87 {v474 v523 v532 v538 v544 v547 v550 : Word}
    (t532 : v532.toNat = v474.toNat * 4234356049 % 2 ^ 32)
    (t538 : v538.toNat = v474.toNat * 4234356049 / 2 ^ 32)
    (t544 : v544.toNat = (v532.toNat + v523.toNat) % 2 ^ 32)
    (t547 : v544.toNat + 2 ^ 32 * v547.toNat = v532.toNat + v523.toNat)
    (t550 : v550.toNat = (v547.toNat + v538.toNat) % 2 ^ 32) :
    v544.toNat + 2 ^ 32 * v550.toNat = v474.toNat * 4234356049 + v523.toNat := by
  have := v474.isLt; have := v523.isLt; have := v532.isLt; have := v538.isLt; have := v544.isLt; have := v547.isLt; have := v550.isLt
  generalize v474.toNat = n474 at *
  generalize v523.toNat = n523 at *
  generalize v532.toNat = n532 at *
  generalize v538.toNat = n538 at *
  generalize v544.toNat = n544 at *
  generalize v547.toNat = n547 at *
  generalize v550.toNat = n550 at *
  first
    | omega
    | (obtain ⟨qt532, et532⟩ := mod_q t532; clear t532; obtain ⟨qt544, et544⟩ := mod_q t544; clear t544; omega)

theorem psm_v_P87l {v474 v523 v532 v544 v550 : Word}
    (t532 : v532.toNat = v474.toNat * 4234356049 % 2 ^ 32)
    (t544 : v544.toNat = (v532.toNat + v523.toNat) % 2 ^ 32)
    (wP87 : v544.toNat + 2 ^ 32 * v550.toNat = v474.toNat * 4234356049 + v523.toNat) :
    v544.toNat = (v544.toNat + 2 ^ 32 * v550.toNat) % 2 ^ 32 := by
  have := v474.isLt; have := v523.isLt; have := v532.isLt; have := v544.isLt; have := v550.isLt
  generalize v474.toNat = n474 at *
  generalize v523.toNat = n523 at *
  generalize v532.toNat = n532 at *
  generalize v544.toNat = n544 at *
  generalize v550.toNat = n550 at *
  first
    | omega
    | (obtain ⟨qt532, et532⟩ := mod_q t532; clear t532; obtain ⟨qt544, et544⟩ := mod_q t544; clear t544; omega)

theorem psm_v_P87h {v474 v523 v532 v538 v544 v547 v550 : Word}
    (t538 : v538.toNat = v474.toNat * 4234356049 / 2 ^ 32)
    (t547 : v544.toNat + 2 ^ 32 * v547.toNat = v532.toNat + v523.toNat)
    (t550 : v550.toNat = (v547.toNat + v538.toNat) % 2 ^ 32)
    (wP87 : v544.toNat + 2 ^ 32 * v550.toNat = v474.toNat * 4234356049 + v523.toNat) :
    v550.toNat = (v544.toNat + 2 ^ 32 * v550.toNat) / 2 ^ 32 := by
  have := v474.isLt; have := v523.isLt; have := v532.isLt; have := v538.isLt; have := v544.isLt; have := v547.isLt; have := v550.isLt
  generalize v474.toNat = n474 at *
  generalize v523.toNat = n523 at *
  generalize v532.toNat = n532 at *
  generalize v538.toNat = n538 at *
  generalize v544.toNat = n544 at *
  generalize v547.toNat = n547 at *
  generalize v550.toNat = n550 at *
  first
    | omega
    | (obtain ⟨qt550, et550⟩ := mod_q t550; clear t550; omega)

theorem psm_v_P88 {v474 v530 v536 v540 v548 v550 v551 v552 v554 v557 v558 : Word}
    (t536 : v536.toNat = v474.toNat * 4089039554 % 2 ^ 32)
    (t540 : v540.toNat = v474.toNat * 4089039554 / 2 ^ 32)
    (t548 : v548.toNat = (v536.toNat + v530.toNat) % 2 ^ 32)
    (t551 : v548.toNat + 2 ^ 32 * v551.toNat = v536.toNat + v530.toNat)
    (t552 : v552.toNat = (v540.toNat + v551.toNat) % 2 ^ 32)
    (t554 : v554.toNat = (v548.toNat + v550.toNat) % 2 ^ 32)
    (t557 : v554.toNat + 2 ^ 32 * v557.toNat = v548.toNat + v550.toNat)
    (t558 : v558.toNat = (v552.toNat + v557.toNat) % 2 ^ 32) :
    v554.toNat + 2 ^ 32 * v558.toNat = v474.toNat * 4089039554 + v530.toNat + v550.toNat := by
  have := v474.isLt; have := v530.isLt; have := v536.isLt; have := v540.isLt; have := v548.isLt; have := v550.isLt; have := v551.isLt; have := v552.isLt; have := v554.isLt; have := v557.isLt; have := v558.isLt
  generalize v474.toNat = n474 at *
  generalize v530.toNat = n530 at *
  generalize v536.toNat = n536 at *
  generalize v540.toNat = n540 at *
  generalize v548.toNat = n548 at *
  generalize v550.toNat = n550 at *
  generalize v551.toNat = n551 at *
  generalize v552.toNat = n552 at *
  generalize v554.toNat = n554 at *
  generalize v557.toNat = n557 at *
  generalize v558.toNat = n558 at *
  first
    | omega
    | (obtain ⟨qt536, et536⟩ := mod_q t536; clear t536; obtain ⟨qt548, et548⟩ := mod_q t548; clear t548; obtain ⟨qt552, et552⟩ := mod_q t552; clear t552; obtain ⟨qt554, et554⟩ := mod_q t554; clear t554; omega)

theorem psm_v_P88l {v474 v530 v536 v548 v550 v554 v558 : Word}
    (t536 : v536.toNat = v474.toNat * 4089039554 % 2 ^ 32)
    (t548 : v548.toNat = (v536.toNat + v530.toNat) % 2 ^ 32)
    (t554 : v554.toNat = (v548.toNat + v550.toNat) % 2 ^ 32)
    (wP88 : v554.toNat + 2 ^ 32 * v558.toNat = v474.toNat * 4089039554 + v530.toNat + v550.toNat) :
    v554.toNat = (v554.toNat + 2 ^ 32 * v558.toNat) % 2 ^ 32 := by
  have := v474.isLt; have := v530.isLt; have := v536.isLt; have := v548.isLt; have := v550.isLt; have := v554.isLt; have := v558.isLt
  generalize v474.toNat = n474 at *
  generalize v530.toNat = n530 at *
  generalize v536.toNat = n536 at *
  generalize v548.toNat = n548 at *
  generalize v550.toNat = n550 at *
  generalize v554.toNat = n554 at *
  generalize v558.toNat = n558 at *
  first
    | omega
    | (obtain ⟨qt536, et536⟩ := mod_q t536; clear t536; obtain ⟨qt548, et548⟩ := mod_q t548; clear t548; obtain ⟨qt554, et554⟩ := mod_q t554; clear t554; omega)

theorem psm_v_P88h {v474 v530 v536 v540 v548 v550 v551 v552 v554 v557 v558 : Word}
    (t536 : v536.toNat = v474.toNat * 4089039554 % 2 ^ 32)
    (t540 : v540.toNat = v474.toNat * 4089039554 / 2 ^ 32)
    (t548 : v548.toNat = (v536.toNat + v530.toNat) % 2 ^ 32)
    (t551 : v548.toNat + 2 ^ 32 * v551.toNat = v536.toNat + v530.toNat)
    (t552 : v552.toNat = (v540.toNat + v551.toNat) % 2 ^ 32)
    (t557 : v554.toNat + 2 ^ 32 * v557.toNat = v548.toNat + v550.toNat)
    (t558 : v558.toNat = (v552.toNat + v557.toNat) % 2 ^ 32)
    (wP88 : v554.toNat + 2 ^ 32 * v558.toNat = v474.toNat * 4089039554 + v530.toNat + v550.toNat) :
    v558.toNat = (v554.toNat + 2 ^ 32 * v558.toNat) / 2 ^ 32 := by
  have := v474.isLt; have := v530.isLt; have := v536.isLt; have := v540.isLt; have := v548.isLt; have := v550.isLt; have := v551.isLt; have := v552.isLt; have := v554.isLt; have := v557.isLt; have := v558.isLt
  generalize v474.toNat = n474 at *
  generalize v530.toNat = n530 at *
  generalize v536.toNat = n536 at *
  generalize v540.toNat = n540 at *
  generalize v548.toNat = n548 at *
  generalize v550.toNat = n550 at *
  generalize v551.toNat = n551 at *
  generalize v552.toNat = n552 at *
  generalize v554.toNat = n554 at *
  generalize v557.toNat = n557 at *
  generalize v558.toNat = n558 at *
  first
    | omega
    | (obtain ⟨qt536, et536⟩ := mod_q t536; clear t536; obtain ⟨qt548, et548⟩ := mod_q t548; clear t548; obtain ⟨qt552, et552⟩ := mod_q t552; clear t552; obtain ⟨qt558, et558⟩ := mod_q t558; clear t558; omega)

theorem psm_v_P89 {v474 v535 v549 v553 v558 v561 v563 v564 v566 v568 v570 : Word}
    (t549 : v549.toNat = v474.toNat * 2803342980 % 2 ^ 32)
    (t553 : v553.toNat = v474.toNat * 2803342980 / 2 ^ 32)
    (t561 : v561.toNat = (v549.toNat + v535.toNat) % 2 ^ 32)
    (t563 : v561.toNat + 2 ^ 32 * v563.toNat = v549.toNat + v535.toNat)
    (t564 : v564.toNat = (v553.toNat + v563.toNat) % 2 ^ 32)
    (t566 : v566.toNat = (v558.toNat + v561.toNat) % 2 ^ 32)
    (t568 : v566.toNat + 2 ^ 32 * v568.toNat = v558.toNat + v561.toNat)
    (t570 : v570.toNat = (v564.toNat + v568.toNat) % 2 ^ 32) :
    v566.toNat + 2 ^ 32 * v570.toNat = v474.toNat * 2803342980 + v535.toNat + v558.toNat := by
  have := v474.isLt; have := v535.isLt; have := v549.isLt; have := v553.isLt; have := v558.isLt; have := v561.isLt; have := v563.isLt; have := v564.isLt; have := v566.isLt; have := v568.isLt; have := v570.isLt
  generalize v474.toNat = n474 at *
  generalize v535.toNat = n535 at *
  generalize v549.toNat = n549 at *
  generalize v553.toNat = n553 at *
  generalize v558.toNat = n558 at *
  generalize v561.toNat = n561 at *
  generalize v563.toNat = n563 at *
  generalize v564.toNat = n564 at *
  generalize v566.toNat = n566 at *
  generalize v568.toNat = n568 at *
  generalize v570.toNat = n570 at *
  first
    | omega
    | (obtain ⟨qt549, et549⟩ := mod_q t549; clear t549; obtain ⟨qt561, et561⟩ := mod_q t561; clear t561; obtain ⟨qt564, et564⟩ := mod_q t564; clear t564; obtain ⟨qt566, et566⟩ := mod_q t566; clear t566; omega)

theorem psm_v_P89l {v474 v535 v549 v558 v561 v566 v570 : Word}
    (t549 : v549.toNat = v474.toNat * 2803342980 % 2 ^ 32)
    (t561 : v561.toNat = (v549.toNat + v535.toNat) % 2 ^ 32)
    (t566 : v566.toNat = (v558.toNat + v561.toNat) % 2 ^ 32)
    (wP89 : v566.toNat + 2 ^ 32 * v570.toNat = v474.toNat * 2803342980 + v535.toNat + v558.toNat) :
    v566.toNat = (v566.toNat + 2 ^ 32 * v570.toNat) % 2 ^ 32 := by
  have := v474.isLt; have := v535.isLt; have := v549.isLt; have := v558.isLt; have := v561.isLt; have := v566.isLt; have := v570.isLt
  generalize v474.toNat = n474 at *
  generalize v535.toNat = n535 at *
  generalize v549.toNat = n549 at *
  generalize v558.toNat = n558 at *
  generalize v561.toNat = n561 at *
  generalize v566.toNat = n566 at *
  generalize v570.toNat = n570 at *
  first
    | omega
    | (obtain ⟨qt549, et549⟩ := mod_q t549; clear t549; obtain ⟨qt561, et561⟩ := mod_q t561; clear t561; obtain ⟨qt566, et566⟩ := mod_q t566; clear t566; omega)

theorem psm_v_P89h {v474 v535 v549 v553 v558 v561 v563 v564 v566 v568 v570 : Word}
    (t549 : v549.toNat = v474.toNat * 2803342980 % 2 ^ 32)
    (t553 : v553.toNat = v474.toNat * 2803342980 / 2 ^ 32)
    (t561 : v561.toNat = (v549.toNat + v535.toNat) % 2 ^ 32)
    (t563 : v561.toNat + 2 ^ 32 * v563.toNat = v549.toNat + v535.toNat)
    (t564 : v564.toNat = (v553.toNat + v563.toNat) % 2 ^ 32)
    (t568 : v566.toNat + 2 ^ 32 * v568.toNat = v558.toNat + v561.toNat)
    (t570 : v570.toNat = (v564.toNat + v568.toNat) % 2 ^ 32)
    (wP89 : v566.toNat + 2 ^ 32 * v570.toNat = v474.toNat * 2803342980 + v535.toNat + v558.toNat) :
    v570.toNat = (v566.toNat + 2 ^ 32 * v570.toNat) / 2 ^ 32 := by
  have := v474.isLt; have := v535.isLt; have := v549.isLt; have := v553.isLt; have := v558.isLt; have := v561.isLt; have := v563.isLt; have := v564.isLt; have := v566.isLt; have := v568.isLt; have := v570.isLt
  generalize v474.toNat = n474 at *
  generalize v535.toNat = n535 at *
  generalize v549.toNat = n549 at *
  generalize v553.toNat = n553 at *
  generalize v558.toNat = n558 at *
  generalize v561.toNat = n561 at *
  generalize v563.toNat = n563 at *
  generalize v564.toNat = n564 at *
  generalize v566.toNat = n566 at *
  generalize v568.toNat = n568 at *
  generalize v570.toNat = n570 at *
  first
    | omega
    | (obtain ⟨qt549, et549⟩ := mod_q t549; clear t549; obtain ⟨qt561, et561⟩ := mod_q t561; clear t561; obtain ⟨qt564, et564⟩ := mod_q t564; clear t564; obtain ⟨qt570, et570⟩ := mod_q t570; clear t570; omega)

theorem psm_v_P90 {v474 v542 v555 v559 v567 v569 v570 v571 v572 v574 v576 : Word}
    (t555 : v555.toNat = v474.toNat * 3169254061 % 2 ^ 32)
    (t559 : v559.toNat = v474.toNat * 3169254061 / 2 ^ 32)
    (t567 : v567.toNat = (v555.toNat + v542.toNat) % 2 ^ 32)
    (t569 : v567.toNat + 2 ^ 32 * v569.toNat = v555.toNat + v542.toNat)
    (t571 : v571.toNat = (v569.toNat + v559.toNat) % 2 ^ 32)
    (t572 : v572.toNat = (v567.toNat + v570.toNat) % 2 ^ 32)
    (t574 : v572.toNat + 2 ^ 32 * v574.toNat = v567.toNat + v570.toNat)
    (t576 : v576.toNat = (v574.toNat + v571.toNat) % 2 ^ 32) :
    v572.toNat + 2 ^ 32 * v576.toNat = v474.toNat * 3169254061 + v542.toNat + v570.toNat := by
  have := v474.isLt; have := v542.isLt; have := v555.isLt; have := v559.isLt; have := v567.isLt; have := v569.isLt; have := v570.isLt; have := v571.isLt; have := v572.isLt; have := v574.isLt; have := v576.isLt
  generalize v474.toNat = n474 at *
  generalize v542.toNat = n542 at *
  generalize v555.toNat = n555 at *
  generalize v559.toNat = n559 at *
  generalize v567.toNat = n567 at *
  generalize v569.toNat = n569 at *
  generalize v570.toNat = n570 at *
  generalize v571.toNat = n571 at *
  generalize v572.toNat = n572 at *
  generalize v574.toNat = n574 at *
  generalize v576.toNat = n576 at *
  first
    | omega
    | (obtain ⟨qt555, et555⟩ := mod_q t555; clear t555; obtain ⟨qt567, et567⟩ := mod_q t567; clear t567; obtain ⟨qt571, et571⟩ := mod_q t571; clear t571; obtain ⟨qt572, et572⟩ := mod_q t572; clear t572; omega)

theorem psm_v_P90l {v474 v542 v555 v567 v570 v572 v576 : Word}
    (t555 : v555.toNat = v474.toNat * 3169254061 % 2 ^ 32)
    (t567 : v567.toNat = (v555.toNat + v542.toNat) % 2 ^ 32)
    (t572 : v572.toNat = (v567.toNat + v570.toNat) % 2 ^ 32)
    (wP90 : v572.toNat + 2 ^ 32 * v576.toNat = v474.toNat * 3169254061 + v542.toNat + v570.toNat) :
    v572.toNat = (v572.toNat + 2 ^ 32 * v576.toNat) % 2 ^ 32 := by
  have := v474.isLt; have := v542.isLt; have := v555.isLt; have := v567.isLt; have := v570.isLt; have := v572.isLt; have := v576.isLt
  generalize v474.toNat = n474 at *
  generalize v542.toNat = n542 at *
  generalize v555.toNat = n555 at *
  generalize v567.toNat = n567 at *
  generalize v570.toNat = n570 at *
  generalize v572.toNat = n572 at *
  generalize v576.toNat = n576 at *
  first
    | omega
    | (obtain ⟨qt555, et555⟩ := mod_q t555; clear t555; obtain ⟨qt567, et567⟩ := mod_q t567; clear t567; obtain ⟨qt572, et572⟩ := mod_q t572; clear t572; omega)

theorem psm_v_P90h {v474 v542 v555 v559 v567 v569 v570 v571 v572 v574 v576 : Word}
    (t555 : v555.toNat = v474.toNat * 3169254061 % 2 ^ 32)
    (t559 : v559.toNat = v474.toNat * 3169254061 / 2 ^ 32)
    (t567 : v567.toNat = (v555.toNat + v542.toNat) % 2 ^ 32)
    (t569 : v567.toNat + 2 ^ 32 * v569.toNat = v555.toNat + v542.toNat)
    (t571 : v571.toNat = (v569.toNat + v559.toNat) % 2 ^ 32)
    (t574 : v572.toNat + 2 ^ 32 * v574.toNat = v567.toNat + v570.toNat)
    (t576 : v576.toNat = (v574.toNat + v571.toNat) % 2 ^ 32)
    (wP90 : v572.toNat + 2 ^ 32 * v576.toNat = v474.toNat * 3169254061 + v542.toNat + v570.toNat) :
    v576.toNat = (v572.toNat + 2 ^ 32 * v576.toNat) / 2 ^ 32 := by
  have := v474.isLt; have := v542.isLt; have := v555.isLt; have := v559.isLt; have := v567.isLt; have := v569.isLt; have := v570.isLt; have := v571.isLt; have := v572.isLt; have := v574.isLt; have := v576.isLt
  generalize v474.toNat = n474 at *
  generalize v542.toNat = n542 at *
  generalize v555.toNat = n555 at *
  generalize v559.toNat = n559 at *
  generalize v567.toNat = n567 at *
  generalize v569.toNat = n569 at *
  generalize v570.toNat = n570 at *
  generalize v571.toNat = n571 at *
  generalize v572.toNat = n572 at *
  generalize v574.toNat = n574 at *
  generalize v576.toNat = n576 at *
  first
    | omega
    | (obtain ⟨qt555, et555⟩ := mod_q t555; clear t555; obtain ⟨qt567, et567⟩ := mod_q t567; clear t567; obtain ⟨qt571, et571⟩ := mod_q t571; clear t571; obtain ⟨qt576, et576⟩ := mod_q t576; clear t576; omega)

theorem psm_v_P91 {v474 v556 v565 v573 v575 v576 v577 v578 v580 v584 : Word}
    (t565 : v565.toNat = v474.toNat * 4294967295 / 2 ^ 32 ∧ v565.toNat + (v474.toNat + 4294967295) / 4294967296 = v474.toNat)
    (t573 : v573.toNat = (v556.toNat + 2 ^ 32 - v474.toNat) % 2 ^ 32)
    (t575 : (v573.toNat < v556.toNat ∧ v575.toNat = 1) ∨ (v556.toNat ≤ v573.toNat ∧ v575.toNat = 0))
    (t577 : v577.toNat = (v575.toNat + v565.toNat) % 2 ^ 32)
    (t578 : v578.toNat = (v573.toNat + v576.toNat) % 2 ^ 32)
    (t580 : v578.toNat + 2 ^ 32 * v580.toNat = v573.toNat + v576.toNat)
    (t584 : v584.toNat = (v577.toNat + v580.toNat) % 2 ^ 32) :
    v578.toNat + 2 ^ 32 * v584.toNat = v474.toNat * 4294967295 + v556.toNat + v576.toNat := by
  have := v474.isLt; have := v556.isLt; have := v565.isLt; have := v573.isLt; have := v575.isLt; have := v576.isLt; have := v577.isLt; have := v578.isLt; have := v580.isLt; have := v584.isLt
  generalize v474.toNat = n474 at *
  generalize v556.toNat = n556 at *
  generalize v565.toNat = n565 at *
  generalize v573.toNat = n573 at *
  generalize v575.toNat = n575 at *
  generalize v576.toNat = n576 at *
  generalize v577.toNat = n577 at *
  generalize v578.toNat = n578 at *
  generalize v580.toNat = n580 at *
  generalize v584.toNat = n584 at *
  first
    | omega
    | (obtain ⟨t565a, t565b⟩ := t565; rcases Nat.eq_zero_or_pos n474 with _ | _ <;> rcases t575 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t565a, t565b⟩ := t565; obtain ⟨qt573, et573⟩ := mod_q t573; clear t573; obtain ⟨qt577, et577⟩ := mod_q t577; clear t577; obtain ⟨qt578, et578⟩ := mod_q t578; clear t578; omega)
    | (obtain ⟨t565a, t565b⟩ := t565; obtain ⟨qt573, et573⟩ := mod_q t573; clear t573; obtain ⟨qt577, et577⟩ := mod_q t577; clear t577; obtain ⟨qt578, et578⟩ := mod_q t578; clear t578; rcases Nat.eq_zero_or_pos n474 with _ | _ <;> rcases t575 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P91l {v474 v556 v573 v576 v578 v584 : Word}
    (t573 : v573.toNat = (v556.toNat + 2 ^ 32 - v474.toNat) % 2 ^ 32)
    (t578 : v578.toNat = (v573.toNat + v576.toNat) % 2 ^ 32)
    (wP91 : v578.toNat + 2 ^ 32 * v584.toNat = v474.toNat * 4294967295 + v556.toNat + v576.toNat) :
    v578.toNat = (v578.toNat + 2 ^ 32 * v584.toNat) % 2 ^ 32 := by
  have := v474.isLt; have := v556.isLt; have := v573.isLt; have := v576.isLt; have := v578.isLt; have := v584.isLt
  generalize v474.toNat = n474 at *
  generalize v556.toNat = n556 at *
  generalize v573.toNat = n573 at *
  generalize v576.toNat = n576 at *
  generalize v578.toNat = n578 at *
  generalize v584.toNat = n584 at *
  first
    | omega
    | (obtain ⟨qt573, et573⟩ := mod_q t573; clear t573; obtain ⟨qt578, et578⟩ := mod_q t578; clear t578; omega)

theorem psm_v_P91h {v474 v556 v565 v573 v575 v576 v577 v578 v580 v584 : Word}
    (t565 : v565.toNat = v474.toNat * 4294967295 / 2 ^ 32 ∧ v565.toNat + (v474.toNat + 4294967295) / 4294967296 = v474.toNat)
    (t573 : v573.toNat = (v556.toNat + 2 ^ 32 - v474.toNat) % 2 ^ 32)
    (t575 : (v573.toNat < v556.toNat ∧ v575.toNat = 1) ∨ (v556.toNat ≤ v573.toNat ∧ v575.toNat = 0))
    (t577 : v577.toNat = (v575.toNat + v565.toNat) % 2 ^ 32)
    (t580 : v578.toNat + 2 ^ 32 * v580.toNat = v573.toNat + v576.toNat)
    (t584 : v584.toNat = (v577.toNat + v580.toNat) % 2 ^ 32)
    (wP91 : v578.toNat + 2 ^ 32 * v584.toNat = v474.toNat * 4294967295 + v556.toNat + v576.toNat) :
    v584.toNat = (v578.toNat + 2 ^ 32 * v584.toNat) / 2 ^ 32 := by
  have := v474.isLt; have := v556.isLt; have := v565.isLt; have := v573.isLt; have := v575.isLt; have := v576.isLt; have := v577.isLt; have := v578.isLt; have := v580.isLt; have := v584.isLt
  generalize v474.toNat = n474 at *
  generalize v556.toNat = n556 at *
  generalize v565.toNat = n565 at *
  generalize v573.toNat = n573 at *
  generalize v575.toNat = n575 at *
  generalize v576.toNat = n576 at *
  generalize v577.toNat = n577 at *
  generalize v578.toNat = n578 at *
  generalize v580.toNat = n580 at *
  generalize v584.toNat = n584 at *
  first
    | omega
    | (obtain ⟨t565a, t565b⟩ := t565; rcases Nat.eq_zero_or_pos n474 with _ | _ <;> rcases t575 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t565a, t565b⟩ := t565; obtain ⟨qt573, et573⟩ := mod_q t573; clear t573; obtain ⟨qt577, et577⟩ := mod_q t577; clear t577; obtain ⟨qt584, et584⟩ := mod_q t584; clear t584; omega)
    | (obtain ⟨t565a, t565b⟩ := t565; obtain ⟨qt573, et573⟩ := mod_q t573; clear t573; obtain ⟨qt577, et577⟩ := mod_q t577; clear t577; obtain ⟨qt584, et584⟩ := mod_q t584; clear t584; rcases Nat.eq_zero_or_pos n474 with _ | _ <;> rcases t575 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P92 {v474 v562 v565 v581 v584 v585 v586 v588 v589 v590 : Word}
    (t565 : v565.toNat = v474.toNat * 4294967295 / 2 ^ 32 ∧ v565.toNat + (v474.toNat + 4294967295) / 4294967296 = v474.toNat)
    (t581 : v581.toNat = (v562.toNat + 2 ^ 32 - v474.toNat) % 2 ^ 32)
    (t585 : (v581.toNat < v562.toNat ∧ v585.toNat = 1) ∨ (v562.toNat ≤ v581.toNat ∧ v585.toNat = 0))
    (t586 : v586.toNat = (v584.toNat + v581.toNat) % 2 ^ 32)
    (t588 : v588.toNat = (v565.toNat + v585.toNat) % 2 ^ 32)
    (t589 : v586.toNat + 2 ^ 32 * v589.toNat = v584.toNat + v581.toNat)
    (t590 : v590.toNat = (v588.toNat + v589.toNat) % 2 ^ 32) :
    v586.toNat + 2 ^ 32 * v590.toNat = v474.toNat * 4294967295 + v562.toNat + v584.toNat := by
  have := v474.isLt; have := v562.isLt; have := v565.isLt; have := v581.isLt; have := v584.isLt; have := v585.isLt; have := v586.isLt; have := v588.isLt; have := v589.isLt; have := v590.isLt
  generalize v474.toNat = n474 at *
  generalize v562.toNat = n562 at *
  generalize v565.toNat = n565 at *
  generalize v581.toNat = n581 at *
  generalize v584.toNat = n584 at *
  generalize v585.toNat = n585 at *
  generalize v586.toNat = n586 at *
  generalize v588.toNat = n588 at *
  generalize v589.toNat = n589 at *
  generalize v590.toNat = n590 at *
  first
    | omega
    | (obtain ⟨t565a, t565b⟩ := t565; rcases Nat.eq_zero_or_pos n474 with _ | _ <;> rcases t585 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t565a, t565b⟩ := t565; obtain ⟨qt581, et581⟩ := mod_q t581; clear t581; obtain ⟨qt586, et586⟩ := mod_q t586; clear t586; obtain ⟨qt588, et588⟩ := mod_q t588; clear t588; omega)
    | (obtain ⟨t565a, t565b⟩ := t565; obtain ⟨qt581, et581⟩ := mod_q t581; clear t581; obtain ⟨qt586, et586⟩ := mod_q t586; clear t586; obtain ⟨qt588, et588⟩ := mod_q t588; clear t588; rcases Nat.eq_zero_or_pos n474 with _ | _ <;> rcases t585 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P92l {v474 v562 v581 v584 v586 v590 : Word}
    (t581 : v581.toNat = (v562.toNat + 2 ^ 32 - v474.toNat) % 2 ^ 32)
    (t586 : v586.toNat = (v584.toNat + v581.toNat) % 2 ^ 32)
    (wP92 : v586.toNat + 2 ^ 32 * v590.toNat = v474.toNat * 4294967295 + v562.toNat + v584.toNat) :
    v586.toNat = (v586.toNat + 2 ^ 32 * v590.toNat) % 2 ^ 32 := by
  have := v474.isLt; have := v562.isLt; have := v581.isLt; have := v584.isLt; have := v586.isLt; have := v590.isLt
  generalize v474.toNat = n474 at *
  generalize v562.toNat = n562 at *
  generalize v581.toNat = n581 at *
  generalize v584.toNat = n584 at *
  generalize v586.toNat = n586 at *
  generalize v590.toNat = n590 at *
  first
    | omega
    | (obtain ⟨qt581, et581⟩ := mod_q t581; clear t581; obtain ⟨qt586, et586⟩ := mod_q t586; clear t586; omega)

theorem psm_v_P92h {v474 v562 v565 v581 v584 v585 v586 v588 v589 v590 : Word}
    (t565 : v565.toNat = v474.toNat * 4294967295 / 2 ^ 32 ∧ v565.toNat + (v474.toNat + 4294967295) / 4294967296 = v474.toNat)
    (t581 : v581.toNat = (v562.toNat + 2 ^ 32 - v474.toNat) % 2 ^ 32)
    (t585 : (v581.toNat < v562.toNat ∧ v585.toNat = 1) ∨ (v562.toNat ≤ v581.toNat ∧ v585.toNat = 0))
    (t588 : v588.toNat = (v565.toNat + v585.toNat) % 2 ^ 32)
    (t589 : v586.toNat + 2 ^ 32 * v589.toNat = v584.toNat + v581.toNat)
    (t590 : v590.toNat = (v588.toNat + v589.toNat) % 2 ^ 32)
    (wP92 : v586.toNat + 2 ^ 32 * v590.toNat = v474.toNat * 4294967295 + v562.toNat + v584.toNat) :
    v590.toNat = (v586.toNat + 2 ^ 32 * v590.toNat) / 2 ^ 32 := by
  have := v474.isLt; have := v562.isLt; have := v565.isLt; have := v581.isLt; have := v584.isLt; have := v585.isLt; have := v586.isLt; have := v588.isLt; have := v589.isLt; have := v590.isLt
  generalize v474.toNat = n474 at *
  generalize v562.toNat = n562 at *
  generalize v565.toNat = n565 at *
  generalize v581.toNat = n581 at *
  generalize v584.toNat = n584 at *
  generalize v585.toNat = n585 at *
  generalize v586.toNat = n586 at *
  generalize v588.toNat = n588 at *
  generalize v589.toNat = n589 at *
  generalize v590.toNat = n590 at *
  first
    | omega
    | (obtain ⟨t565a, t565b⟩ := t565; rcases Nat.eq_zero_or_pos n474 with _ | _ <;> rcases t585 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t565a, t565b⟩ := t565; obtain ⟨qt581, et581⟩ := mod_q t581; clear t581; obtain ⟨qt588, et588⟩ := mod_q t588; clear t588; obtain ⟨qt590, et590⟩ := mod_q t590; clear t590; omega)
    | (obtain ⟨t565a, t565b⟩ := t565; obtain ⟨qt581, et581⟩ := mod_q t581; clear t581; obtain ⟨qt588, et588⟩ := mod_q t588; clear t588; obtain ⟨qt590, et590⟩ := mod_q t590; clear t590; rcases Nat.eq_zero_or_pos n474 with _ | _ <;> rcases t585 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_S93 {v465 v590 v611 v615 : Word}
    (t611 : v611.toNat = (v590.toNat + 2 ^ 32 - v465.toNat) % 2 ^ 32)
    (t615 : (v611.toNat < v590.toNat ∧ v615.toNat = 1) ∨ (v590.toNat ≤ v611.toNat ∧ v615.toNat = 0)) :
    v611.toNat + 2 ^ 32 * v615.toNat = ((v465.toNat * 4294967295) % 2 ^ 32) + v590.toNat := by
  have := v465.isLt; have := v590.isLt; have := v611.isLt; have := v615.isLt
  generalize v465.toNat = n465 at *
  generalize v590.toNat = n590 at *
  generalize v611.toNat = n611 at *
  generalize v615.toNat = n615 at *
  first
    | omega
    | (rcases t615 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨qt611, et611⟩ := mod_q t611; clear t611; omega)
    | (obtain ⟨qt611, et611⟩ := mod_q t611; clear t611; rcases t615 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_S93l {v465 v590 v611 v615 : Word}
    (t611 : v611.toNat = (v590.toNat + 2 ^ 32 - v465.toNat) % 2 ^ 32)
    (wS93 : v611.toNat + 2 ^ 32 * v615.toNat = ((v465.toNat * 4294967295) % 2 ^ 32) + v590.toNat) :
    v611.toNat = (v611.toNat + 2 ^ 32 * v615.toNat) % 2 ^ 32 := by
  have := v465.isLt; have := v590.isLt; have := v611.isLt; have := v615.isLt
  generalize v465.toNat = n465 at *
  generalize v590.toNat = n590 at *
  generalize v611.toNat = n611 at *
  generalize v615.toNat = n615 at *
  first
    | omega
    | (obtain ⟨qt611, et611⟩ := mod_q t611; clear t611; omega)

theorem psm_v_S93h {v465 v590 v611 v615 : Word}
    (t615 : (v611.toNat < v590.toNat ∧ v615.toNat = 1) ∨ (v590.toNat ≤ v611.toNat ∧ v615.toNat = 0))
    (wS93 : v611.toNat + 2 ^ 32 * v615.toNat = ((v465.toNat * 4294967295) % 2 ^ 32) + v590.toNat) :
    v615.toNat = (v611.toNat + 2 ^ 32 * v615.toNat) / 2 ^ 32 := by
  have := v465.isLt; have := v590.isLt; have := v611.isLt; have := v615.isLt
  generalize v465.toNat = n465 at *
  generalize v590.toNat = n590 at *
  generalize v611.toNat = n611 at *
  generalize v615.toNat = n615 at *
  first
    | omega
    | (rcases t615 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P95 {v480 v554 v579 v582 v591 v593 v595 : Word}
    (t579 : v579.toNat = v480.toNat * 4234356049 % 2 ^ 32)
    (t582 : v582.toNat = v480.toNat * 4234356049 / 2 ^ 32)
    (t591 : v591.toNat = (v579.toNat + v554.toNat) % 2 ^ 32)
    (t593 : v591.toNat + 2 ^ 32 * v593.toNat = v579.toNat + v554.toNat)
    (t595 : v595.toNat = (v593.toNat + v582.toNat) % 2 ^ 32) :
    v591.toNat + 2 ^ 32 * v595.toNat = v480.toNat * 4234356049 + v554.toNat := by
  have := v480.isLt; have := v554.isLt; have := v579.isLt; have := v582.isLt; have := v591.isLt; have := v593.isLt; have := v595.isLt
  generalize v480.toNat = n480 at *
  generalize v554.toNat = n554 at *
  generalize v579.toNat = n579 at *
  generalize v582.toNat = n582 at *
  generalize v591.toNat = n591 at *
  generalize v593.toNat = n593 at *
  generalize v595.toNat = n595 at *
  first
    | omega
    | (obtain ⟨qt579, et579⟩ := mod_q t579; clear t579; obtain ⟨qt591, et591⟩ := mod_q t591; clear t591; omega)

theorem psm_v_P95l {v480 v554 v579 v591 v595 : Word}
    (t579 : v579.toNat = v480.toNat * 4234356049 % 2 ^ 32)
    (t591 : v591.toNat = (v579.toNat + v554.toNat) % 2 ^ 32)
    (wP95 : v591.toNat + 2 ^ 32 * v595.toNat = v480.toNat * 4234356049 + v554.toNat) :
    v591.toNat = (v591.toNat + 2 ^ 32 * v595.toNat) % 2 ^ 32 := by
  have := v480.isLt; have := v554.isLt; have := v579.isLt; have := v591.isLt; have := v595.isLt
  generalize v480.toNat = n480 at *
  generalize v554.toNat = n554 at *
  generalize v579.toNat = n579 at *
  generalize v591.toNat = n591 at *
  generalize v595.toNat = n595 at *
  first
    | omega
    | (obtain ⟨qt579, et579⟩ := mod_q t579; clear t579; obtain ⟨qt591, et591⟩ := mod_q t591; clear t591; omega)

theorem psm_v_P95h {v480 v554 v579 v582 v591 v593 v595 : Word}
    (t582 : v582.toNat = v480.toNat * 4234356049 / 2 ^ 32)
    (t593 : v591.toNat + 2 ^ 32 * v593.toNat = v579.toNat + v554.toNat)
    (t595 : v595.toNat = (v593.toNat + v582.toNat) % 2 ^ 32)
    (wP95 : v591.toNat + 2 ^ 32 * v595.toNat = v480.toNat * 4234356049 + v554.toNat) :
    v595.toNat = (v591.toNat + 2 ^ 32 * v595.toNat) / 2 ^ 32 := by
  have := v480.isLt; have := v554.isLt; have := v579.isLt; have := v582.isLt; have := v591.isLt; have := v593.isLt; have := v595.isLt
  generalize v480.toNat = n480 at *
  generalize v554.toNat = n554 at *
  generalize v579.toNat = n579 at *
  generalize v582.toNat = n582 at *
  generalize v591.toNat = n591 at *
  generalize v593.toNat = n593 at *
  generalize v595.toNat = n595 at *
  first
    | omega
    | (obtain ⟨qt595, et595⟩ := mod_q t595; clear t595; omega)

theorem psm_v_P96 {v480 v566 v583 v587 v595 v596 v597 v599 v600 v601 v604 : Word}
    (t583 : v583.toNat = v480.toNat * 4089039554 % 2 ^ 32)
    (t587 : v587.toNat = v480.toNat * 4089039554 / 2 ^ 32)
    (t596 : v596.toNat = (v583.toNat + v566.toNat) % 2 ^ 32)
    (t597 : v596.toNat + 2 ^ 32 * v597.toNat = v583.toNat + v566.toNat)
    (t599 : v599.toNat = (v587.toNat + v597.toNat) % 2 ^ 32)
    (t600 : v600.toNat = (v596.toNat + v595.toNat) % 2 ^ 32)
    (t601 : v600.toNat + 2 ^ 32 * v601.toNat = v596.toNat + v595.toNat)
    (t604 : v604.toNat = (v601.toNat + v599.toNat) % 2 ^ 32) :
    v600.toNat + 2 ^ 32 * v604.toNat = v480.toNat * 4089039554 + v566.toNat + v595.toNat := by
  have := v480.isLt; have := v566.isLt; have := v583.isLt; have := v587.isLt; have := v595.isLt; have := v596.isLt; have := v597.isLt; have := v599.isLt; have := v600.isLt; have := v601.isLt; have := v604.isLt
  generalize v480.toNat = n480 at *
  generalize v566.toNat = n566 at *
  generalize v583.toNat = n583 at *
  generalize v587.toNat = n587 at *
  generalize v595.toNat = n595 at *
  generalize v596.toNat = n596 at *
  generalize v597.toNat = n597 at *
  generalize v599.toNat = n599 at *
  generalize v600.toNat = n600 at *
  generalize v601.toNat = n601 at *
  generalize v604.toNat = n604 at *
  first
    | omega
    | (obtain ⟨qt583, et583⟩ := mod_q t583; clear t583; obtain ⟨qt596, et596⟩ := mod_q t596; clear t596; obtain ⟨qt599, et599⟩ := mod_q t599; clear t599; obtain ⟨qt600, et600⟩ := mod_q t600; clear t600; omega)

theorem psm_v_P96l {v480 v566 v583 v595 v596 v600 v604 : Word}
    (t583 : v583.toNat = v480.toNat * 4089039554 % 2 ^ 32)
    (t596 : v596.toNat = (v583.toNat + v566.toNat) % 2 ^ 32)
    (t600 : v600.toNat = (v596.toNat + v595.toNat) % 2 ^ 32)
    (wP96 : v600.toNat + 2 ^ 32 * v604.toNat = v480.toNat * 4089039554 + v566.toNat + v595.toNat) :
    v600.toNat = (v600.toNat + 2 ^ 32 * v604.toNat) % 2 ^ 32 := by
  have := v480.isLt; have := v566.isLt; have := v583.isLt; have := v595.isLt; have := v596.isLt; have := v600.isLt; have := v604.isLt
  generalize v480.toNat = n480 at *
  generalize v566.toNat = n566 at *
  generalize v583.toNat = n583 at *
  generalize v595.toNat = n595 at *
  generalize v596.toNat = n596 at *
  generalize v600.toNat = n600 at *
  generalize v604.toNat = n604 at *
  first
    | omega
    | (obtain ⟨qt583, et583⟩ := mod_q t583; clear t583; obtain ⟨qt596, et596⟩ := mod_q t596; clear t596; obtain ⟨qt600, et600⟩ := mod_q t600; clear t600; omega)

theorem psm_v_P96h {v480 v566 v583 v587 v595 v596 v597 v599 v600 v601 v604 : Word}
    (t583 : v583.toNat = v480.toNat * 4089039554 % 2 ^ 32)
    (t587 : v587.toNat = v480.toNat * 4089039554 / 2 ^ 32)
    (t596 : v596.toNat = (v583.toNat + v566.toNat) % 2 ^ 32)
    (t597 : v596.toNat + 2 ^ 32 * v597.toNat = v583.toNat + v566.toNat)
    (t599 : v599.toNat = (v587.toNat + v597.toNat) % 2 ^ 32)
    (t601 : v600.toNat + 2 ^ 32 * v601.toNat = v596.toNat + v595.toNat)
    (t604 : v604.toNat = (v601.toNat + v599.toNat) % 2 ^ 32)
    (wP96 : v600.toNat + 2 ^ 32 * v604.toNat = v480.toNat * 4089039554 + v566.toNat + v595.toNat) :
    v604.toNat = (v600.toNat + 2 ^ 32 * v604.toNat) / 2 ^ 32 := by
  have := v480.isLt; have := v566.isLt; have := v583.isLt; have := v587.isLt; have := v595.isLt; have := v596.isLt; have := v597.isLt; have := v599.isLt; have := v600.isLt; have := v601.isLt; have := v604.isLt
  generalize v480.toNat = n480 at *
  generalize v566.toNat = n566 at *
  generalize v583.toNat = n583 at *
  generalize v587.toNat = n587 at *
  generalize v595.toNat = n595 at *
  generalize v596.toNat = n596 at *
  generalize v597.toNat = n597 at *
  generalize v599.toNat = n599 at *
  generalize v600.toNat = n600 at *
  generalize v601.toNat = n601 at *
  generalize v604.toNat = n604 at *
  first
    | omega
    | (obtain ⟨qt583, et583⟩ := mod_q t583; clear t583; obtain ⟨qt596, et596⟩ := mod_q t596; clear t596; obtain ⟨qt599, et599⟩ := mod_q t599; clear t599; obtain ⟨qt604, et604⟩ := mod_q t604; clear t604; omega)

theorem psm_v_P97 {v480 v572 v594 v598 v604 v605 v607 v608 v609 v610 v612 : Word}
    (t594 : v594.toNat = v480.toNat * 2803342980 % 2 ^ 32)
    (t598 : v598.toNat = v480.toNat * 2803342980 / 2 ^ 32)
    (t605 : v605.toNat = (v594.toNat + v572.toNat) % 2 ^ 32)
    (t607 : v605.toNat + 2 ^ 32 * v607.toNat = v594.toNat + v572.toNat)
    (t608 : v608.toNat = (v605.toNat + v604.toNat) % 2 ^ 32)
    (t609 : v609.toNat = (v598.toNat + v607.toNat) % 2 ^ 32)
    (t610 : v608.toNat + 2 ^ 32 * v610.toNat = v605.toNat + v604.toNat)
    (t612 : v612.toNat = (v610.toNat + v609.toNat) % 2 ^ 32) :
    v608.toNat + 2 ^ 32 * v612.toNat = v480.toNat * 2803342980 + v572.toNat + v604.toNat := by
  have := v480.isLt; have := v572.isLt; have := v594.isLt; have := v598.isLt; have := v604.isLt; have := v605.isLt; have := v607.isLt; have := v608.isLt; have := v609.isLt; have := v610.isLt; have := v612.isLt
  generalize v480.toNat = n480 at *
  generalize v572.toNat = n572 at *
  generalize v594.toNat = n594 at *
  generalize v598.toNat = n598 at *
  generalize v604.toNat = n604 at *
  generalize v605.toNat = n605 at *
  generalize v607.toNat = n607 at *
  generalize v608.toNat = n608 at *
  generalize v609.toNat = n609 at *
  generalize v610.toNat = n610 at *
  generalize v612.toNat = n612 at *
  first
    | omega
    | (obtain ⟨qt594, et594⟩ := mod_q t594; clear t594; obtain ⟨qt605, et605⟩ := mod_q t605; clear t605; obtain ⟨qt608, et608⟩ := mod_q t608; clear t608; obtain ⟨qt609, et609⟩ := mod_q t609; clear t609; omega)

theorem psm_v_P97l {v480 v572 v594 v604 v605 v608 v612 : Word}
    (t594 : v594.toNat = v480.toNat * 2803342980 % 2 ^ 32)
    (t605 : v605.toNat = (v594.toNat + v572.toNat) % 2 ^ 32)
    (t608 : v608.toNat = (v605.toNat + v604.toNat) % 2 ^ 32)
    (wP97 : v608.toNat + 2 ^ 32 * v612.toNat = v480.toNat * 2803342980 + v572.toNat + v604.toNat) :
    v608.toNat = (v608.toNat + 2 ^ 32 * v612.toNat) % 2 ^ 32 := by
  have := v480.isLt; have := v572.isLt; have := v594.isLt; have := v604.isLt; have := v605.isLt; have := v608.isLt; have := v612.isLt
  generalize v480.toNat = n480 at *
  generalize v572.toNat = n572 at *
  generalize v594.toNat = n594 at *
  generalize v604.toNat = n604 at *
  generalize v605.toNat = n605 at *
  generalize v608.toNat = n608 at *
  generalize v612.toNat = n612 at *
  first
    | omega
    | (obtain ⟨qt594, et594⟩ := mod_q t594; clear t594; obtain ⟨qt605, et605⟩ := mod_q t605; clear t605; obtain ⟨qt608, et608⟩ := mod_q t608; clear t608; omega)

theorem psm_v_P97h {v480 v572 v594 v598 v604 v605 v607 v608 v609 v610 v612 : Word}
    (t594 : v594.toNat = v480.toNat * 2803342980 % 2 ^ 32)
    (t598 : v598.toNat = v480.toNat * 2803342980 / 2 ^ 32)
    (t605 : v605.toNat = (v594.toNat + v572.toNat) % 2 ^ 32)
    (t607 : v605.toNat + 2 ^ 32 * v607.toNat = v594.toNat + v572.toNat)
    (t609 : v609.toNat = (v598.toNat + v607.toNat) % 2 ^ 32)
    (t610 : v608.toNat + 2 ^ 32 * v610.toNat = v605.toNat + v604.toNat)
    (t612 : v612.toNat = (v610.toNat + v609.toNat) % 2 ^ 32)
    (wP97 : v608.toNat + 2 ^ 32 * v612.toNat = v480.toNat * 2803342980 + v572.toNat + v604.toNat) :
    v612.toNat = (v608.toNat + 2 ^ 32 * v612.toNat) / 2 ^ 32 := by
  have := v480.isLt; have := v572.isLt; have := v594.isLt; have := v598.isLt; have := v604.isLt; have := v605.isLt; have := v607.isLt; have := v608.isLt; have := v609.isLt; have := v610.isLt; have := v612.isLt
  generalize v480.toNat = n480 at *
  generalize v572.toNat = n572 at *
  generalize v594.toNat = n594 at *
  generalize v598.toNat = n598 at *
  generalize v604.toNat = n604 at *
  generalize v605.toNat = n605 at *
  generalize v607.toNat = n607 at *
  generalize v608.toNat = n608 at *
  generalize v609.toNat = n609 at *
  generalize v610.toNat = n610 at *
  generalize v612.toNat = n612 at *
  first
    | omega
    | (obtain ⟨qt594, et594⟩ := mod_q t594; clear t594; obtain ⟨qt605, et605⟩ := mod_q t605; clear t605; obtain ⟨qt609, et609⟩ := mod_q t609; clear t609; obtain ⟨qt612, et612⟩ := mod_q t612; clear t612; omega)

theorem psm_v_P98 {v480 v578 v602 v606 v612 v613 v616 v617 v618 v619 v621 : Word}
    (t602 : v602.toNat = v480.toNat * 3169254061 % 2 ^ 32)
    (t606 : v606.toNat = v480.toNat * 3169254061 / 2 ^ 32)
    (t613 : v613.toNat = (v602.toNat + v578.toNat) % 2 ^ 32)
    (t616 : v613.toNat + 2 ^ 32 * v616.toNat = v602.toNat + v578.toNat)
    (t617 : v617.toNat = (v616.toNat + v606.toNat) % 2 ^ 32)
    (t618 : v618.toNat = (v612.toNat + v613.toNat) % 2 ^ 32)
    (t619 : v618.toNat + 2 ^ 32 * v619.toNat = v612.toNat + v613.toNat)
    (t621 : v621.toNat = (v619.toNat + v617.toNat) % 2 ^ 32) :
    v618.toNat + 2 ^ 32 * v621.toNat = v480.toNat * 3169254061 + v578.toNat + v612.toNat := by
  have := v480.isLt; have := v578.isLt; have := v602.isLt; have := v606.isLt; have := v612.isLt; have := v613.isLt; have := v616.isLt; have := v617.isLt; have := v618.isLt; have := v619.isLt; have := v621.isLt
  generalize v480.toNat = n480 at *
  generalize v578.toNat = n578 at *
  generalize v602.toNat = n602 at *
  generalize v606.toNat = n606 at *
  generalize v612.toNat = n612 at *
  generalize v613.toNat = n613 at *
  generalize v616.toNat = n616 at *
  generalize v617.toNat = n617 at *
  generalize v618.toNat = n618 at *
  generalize v619.toNat = n619 at *
  generalize v621.toNat = n621 at *
  first
    | omega
    | (obtain ⟨qt602, et602⟩ := mod_q t602; clear t602; obtain ⟨qt613, et613⟩ := mod_q t613; clear t613; obtain ⟨qt617, et617⟩ := mod_q t617; clear t617; obtain ⟨qt618, et618⟩ := mod_q t618; clear t618; omega)

theorem psm_v_P98l {v480 v578 v602 v612 v613 v618 v621 : Word}
    (t602 : v602.toNat = v480.toNat * 3169254061 % 2 ^ 32)
    (t613 : v613.toNat = (v602.toNat + v578.toNat) % 2 ^ 32)
    (t618 : v618.toNat = (v612.toNat + v613.toNat) % 2 ^ 32)
    (wP98 : v618.toNat + 2 ^ 32 * v621.toNat = v480.toNat * 3169254061 + v578.toNat + v612.toNat) :
    v618.toNat = (v618.toNat + 2 ^ 32 * v621.toNat) % 2 ^ 32 := by
  have := v480.isLt; have := v578.isLt; have := v602.isLt; have := v612.isLt; have := v613.isLt; have := v618.isLt; have := v621.isLt
  generalize v480.toNat = n480 at *
  generalize v578.toNat = n578 at *
  generalize v602.toNat = n602 at *
  generalize v612.toNat = n612 at *
  generalize v613.toNat = n613 at *
  generalize v618.toNat = n618 at *
  generalize v621.toNat = n621 at *
  first
    | omega
    | (obtain ⟨qt602, et602⟩ := mod_q t602; clear t602; obtain ⟨qt613, et613⟩ := mod_q t613; clear t613; obtain ⟨qt618, et618⟩ := mod_q t618; clear t618; omega)

theorem psm_v_P98h {v480 v578 v602 v606 v612 v613 v616 v617 v618 v619 v621 : Word}
    (t602 : v602.toNat = v480.toNat * 3169254061 % 2 ^ 32)
    (t606 : v606.toNat = v480.toNat * 3169254061 / 2 ^ 32)
    (t613 : v613.toNat = (v602.toNat + v578.toNat) % 2 ^ 32)
    (t616 : v613.toNat + 2 ^ 32 * v616.toNat = v602.toNat + v578.toNat)
    (t617 : v617.toNat = (v616.toNat + v606.toNat) % 2 ^ 32)
    (t619 : v618.toNat + 2 ^ 32 * v619.toNat = v612.toNat + v613.toNat)
    (t621 : v621.toNat = (v619.toNat + v617.toNat) % 2 ^ 32)
    (wP98 : v618.toNat + 2 ^ 32 * v621.toNat = v480.toNat * 3169254061 + v578.toNat + v612.toNat) :
    v621.toNat = (v618.toNat + 2 ^ 32 * v621.toNat) / 2 ^ 32 := by
  have := v480.isLt; have := v578.isLt; have := v602.isLt; have := v606.isLt; have := v612.isLt; have := v613.isLt; have := v616.isLt; have := v617.isLt; have := v618.isLt; have := v619.isLt; have := v621.isLt
  generalize v480.toNat = n480 at *
  generalize v578.toNat = n578 at *
  generalize v602.toNat = n602 at *
  generalize v606.toNat = n606 at *
  generalize v612.toNat = n612 at *
  generalize v613.toNat = n613 at *
  generalize v616.toNat = n616 at *
  generalize v617.toNat = n617 at *
  generalize v618.toNat = n618 at *
  generalize v619.toNat = n619 at *
  generalize v621.toNat = n621 at *
  first
    | omega
    | (obtain ⟨qt602, et602⟩ := mod_q t602; clear t602; obtain ⟨qt613, et613⟩ := mod_q t613; clear t613; obtain ⟨qt617, et617⟩ := mod_q t617; clear t617; obtain ⟨qt621, et621⟩ := mod_q t621; clear t621; omega)

theorem psm_v_P99 {v480 v586 v614 v620 v621 v622 v623 v625 v626 v631 : Word}
    (t614 : v614.toNat = v480.toNat * 4294967295 / 2 ^ 32 ∧ v614.toNat + (v480.toNat + 4294967295) / 4294967296 = v480.toNat)
    (t620 : v620.toNat = (v586.toNat + 2 ^ 32 - v480.toNat) % 2 ^ 32)
    (t622 : (v620.toNat < v586.toNat ∧ v622.toNat = 1) ∨ (v586.toNat ≤ v620.toNat ∧ v622.toNat = 0))
    (t623 : v623.toNat = (v620.toNat + v621.toNat) % 2 ^ 32)
    (t625 : v625.toNat = (v622.toNat + v614.toNat) % 2 ^ 32)
    (t626 : v623.toNat + 2 ^ 32 * v626.toNat = v620.toNat + v621.toNat)
    (t631 : v631.toNat = (v626.toNat + v625.toNat) % 2 ^ 32) :
    v623.toNat + 2 ^ 32 * v631.toNat = v480.toNat * 4294967295 + v586.toNat + v621.toNat := by
  have := v480.isLt; have := v586.isLt; have := v614.isLt; have := v620.isLt; have := v621.isLt; have := v622.isLt; have := v623.isLt; have := v625.isLt; have := v626.isLt; have := v631.isLt
  generalize v480.toNat = n480 at *
  generalize v586.toNat = n586 at *
  generalize v614.toNat = n614 at *
  generalize v620.toNat = n620 at *
  generalize v621.toNat = n621 at *
  generalize v622.toNat = n622 at *
  generalize v623.toNat = n623 at *
  generalize v625.toNat = n625 at *
  generalize v626.toNat = n626 at *
  generalize v631.toNat = n631 at *
  first
    | omega
    | (obtain ⟨t614a, t614b⟩ := t614; rcases Nat.eq_zero_or_pos n480 with _ | _ <;> rcases t622 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t614a, t614b⟩ := t614; obtain ⟨qt620, et620⟩ := mod_q t620; clear t620; obtain ⟨qt623, et623⟩ := mod_q t623; clear t623; obtain ⟨qt625, et625⟩ := mod_q t625; clear t625; omega)
    | (obtain ⟨t614a, t614b⟩ := t614; obtain ⟨qt620, et620⟩ := mod_q t620; clear t620; obtain ⟨qt623, et623⟩ := mod_q t623; clear t623; obtain ⟨qt625, et625⟩ := mod_q t625; clear t625; rcases Nat.eq_zero_or_pos n480 with _ | _ <;> rcases t622 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P99l {v480 v586 v620 v621 v623 v631 : Word}
    (t620 : v620.toNat = (v586.toNat + 2 ^ 32 - v480.toNat) % 2 ^ 32)
    (t623 : v623.toNat = (v620.toNat + v621.toNat) % 2 ^ 32)
    (wP99 : v623.toNat + 2 ^ 32 * v631.toNat = v480.toNat * 4294967295 + v586.toNat + v621.toNat) :
    v623.toNat = (v623.toNat + 2 ^ 32 * v631.toNat) % 2 ^ 32 := by
  have := v480.isLt; have := v586.isLt; have := v620.isLt; have := v621.isLt; have := v623.isLt; have := v631.isLt
  generalize v480.toNat = n480 at *
  generalize v586.toNat = n586 at *
  generalize v620.toNat = n620 at *
  generalize v621.toNat = n621 at *
  generalize v623.toNat = n623 at *
  generalize v631.toNat = n631 at *
  first
    | omega
    | (obtain ⟨qt620, et620⟩ := mod_q t620; clear t620; obtain ⟨qt623, et623⟩ := mod_q t623; clear t623; omega)

theorem psm_v_P99h {v480 v586 v614 v620 v621 v622 v623 v625 v626 v631 : Word}
    (t614 : v614.toNat = v480.toNat * 4294967295 / 2 ^ 32 ∧ v614.toNat + (v480.toNat + 4294967295) / 4294967296 = v480.toNat)
    (t620 : v620.toNat = (v586.toNat + 2 ^ 32 - v480.toNat) % 2 ^ 32)
    (t622 : (v620.toNat < v586.toNat ∧ v622.toNat = 1) ∨ (v586.toNat ≤ v620.toNat ∧ v622.toNat = 0))
    (t625 : v625.toNat = (v622.toNat + v614.toNat) % 2 ^ 32)
    (t626 : v623.toNat + 2 ^ 32 * v626.toNat = v620.toNat + v621.toNat)
    (t631 : v631.toNat = (v626.toNat + v625.toNat) % 2 ^ 32)
    (wP99 : v623.toNat + 2 ^ 32 * v631.toNat = v480.toNat * 4294967295 + v586.toNat + v621.toNat) :
    v631.toNat = (v623.toNat + 2 ^ 32 * v631.toNat) / 2 ^ 32 := by
  have := v480.isLt; have := v586.isLt; have := v614.isLt; have := v620.isLt; have := v621.isLt; have := v622.isLt; have := v623.isLt; have := v625.isLt; have := v626.isLt; have := v631.isLt
  generalize v480.toNat = n480 at *
  generalize v586.toNat = n586 at *
  generalize v614.toNat = n614 at *
  generalize v620.toNat = n620 at *
  generalize v621.toNat = n621 at *
  generalize v622.toNat = n622 at *
  generalize v623.toNat = n623 at *
  generalize v625.toNat = n625 at *
  generalize v626.toNat = n626 at *
  generalize v631.toNat = n631 at *
  first
    | omega
    | (obtain ⟨t614a, t614b⟩ := t614; rcases Nat.eq_zero_or_pos n480 with _ | _ <;> rcases t622 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t614a, t614b⟩ := t614; obtain ⟨qt620, et620⟩ := mod_q t620; clear t620; obtain ⟨qt625, et625⟩ := mod_q t625; clear t625; obtain ⟨qt631, et631⟩ := mod_q t631; clear t631; omega)
    | (obtain ⟨t614a, t614b⟩ := t614; obtain ⟨qt620, et620⟩ := mod_q t620; clear t620; obtain ⟨qt625, et625⟩ := mod_q t625; clear t625; obtain ⟨qt631, et631⟩ := mod_q t631; clear t631; rcases Nat.eq_zero_or_pos n480 with _ | _ <;> rcases t622 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P100 {v480 v611 v614 v627 v629 v631 v632 v633 v635 v640 : Word}
    (t614 : v614.toNat = v480.toNat * 4294967295 / 2 ^ 32 ∧ v614.toNat + (v480.toNat + 4294967295) / 4294967296 = v480.toNat)
    (t627 : v627.toNat = (v611.toNat + 2 ^ 32 - v480.toNat) % 2 ^ 32)
    (t629 : (v627.toNat < v611.toNat ∧ v629.toNat = 1) ∨ (v611.toNat ≤ v627.toNat ∧ v629.toNat = 0))
    (t632 : v632.toNat = (v614.toNat + v629.toNat) % 2 ^ 32)
    (t633 : v633.toNat = (v631.toNat + v627.toNat) % 2 ^ 32)
    (t635 : v633.toNat + 2 ^ 32 * v635.toNat = v631.toNat + v627.toNat)
    (t640 : v640.toNat = (v632.toNat + v635.toNat) % 2 ^ 32) :
    v633.toNat + 2 ^ 32 * v640.toNat = v480.toNat * 4294967295 + v611.toNat + v631.toNat := by
  have := v480.isLt; have := v611.isLt; have := v614.isLt; have := v627.isLt; have := v629.isLt; have := v631.isLt; have := v632.isLt; have := v633.isLt; have := v635.isLt; have := v640.isLt
  generalize v480.toNat = n480 at *
  generalize v611.toNat = n611 at *
  generalize v614.toNat = n614 at *
  generalize v627.toNat = n627 at *
  generalize v629.toNat = n629 at *
  generalize v631.toNat = n631 at *
  generalize v632.toNat = n632 at *
  generalize v633.toNat = n633 at *
  generalize v635.toNat = n635 at *
  generalize v640.toNat = n640 at *
  first
    | omega
    | (obtain ⟨t614a, t614b⟩ := t614; rcases Nat.eq_zero_or_pos n480 with _ | _ <;> rcases t629 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t614a, t614b⟩ := t614; obtain ⟨qt627, et627⟩ := mod_q t627; clear t627; obtain ⟨qt632, et632⟩ := mod_q t632; clear t632; obtain ⟨qt633, et633⟩ := mod_q t633; clear t633; omega)
    | (obtain ⟨t614a, t614b⟩ := t614; obtain ⟨qt627, et627⟩ := mod_q t627; clear t627; obtain ⟨qt632, et632⟩ := mod_q t632; clear t632; obtain ⟨qt633, et633⟩ := mod_q t633; clear t633; rcases Nat.eq_zero_or_pos n480 with _ | _ <;> rcases t629 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P100l {v480 v611 v627 v631 v633 v640 : Word}
    (t627 : v627.toNat = (v611.toNat + 2 ^ 32 - v480.toNat) % 2 ^ 32)
    (t633 : v633.toNat = (v631.toNat + v627.toNat) % 2 ^ 32)
    (wP100 : v633.toNat + 2 ^ 32 * v640.toNat = v480.toNat * 4294967295 + v611.toNat + v631.toNat) :
    v633.toNat = (v633.toNat + 2 ^ 32 * v640.toNat) % 2 ^ 32 := by
  have := v480.isLt; have := v611.isLt; have := v627.isLt; have := v631.isLt; have := v633.isLt; have := v640.isLt
  generalize v480.toNat = n480 at *
  generalize v611.toNat = n611 at *
  generalize v627.toNat = n627 at *
  generalize v631.toNat = n631 at *
  generalize v633.toNat = n633 at *
  generalize v640.toNat = n640 at *
  first
    | omega
    | (obtain ⟨qt627, et627⟩ := mod_q t627; clear t627; obtain ⟨qt633, et633⟩ := mod_q t633; clear t633; omega)

theorem psm_v_P100h {v480 v611 v614 v627 v629 v631 v632 v633 v635 v640 : Word}
    (t614 : v614.toNat = v480.toNat * 4294967295 / 2 ^ 32 ∧ v614.toNat + (v480.toNat + 4294967295) / 4294967296 = v480.toNat)
    (t627 : v627.toNat = (v611.toNat + 2 ^ 32 - v480.toNat) % 2 ^ 32)
    (t629 : (v627.toNat < v611.toNat ∧ v629.toNat = 1) ∨ (v611.toNat ≤ v627.toNat ∧ v629.toNat = 0))
    (t632 : v632.toNat = (v614.toNat + v629.toNat) % 2 ^ 32)
    (t635 : v633.toNat + 2 ^ 32 * v635.toNat = v631.toNat + v627.toNat)
    (t640 : v640.toNat = (v632.toNat + v635.toNat) % 2 ^ 32)
    (wP100 : v633.toNat + 2 ^ 32 * v640.toNat = v480.toNat * 4294967295 + v611.toNat + v631.toNat) :
    v640.toNat = (v633.toNat + 2 ^ 32 * v640.toNat) / 2 ^ 32 := by
  have := v480.isLt; have := v611.isLt; have := v614.isLt; have := v627.isLt; have := v629.isLt; have := v631.isLt; have := v632.isLt; have := v633.isLt; have := v635.isLt; have := v640.isLt
  generalize v480.toNat = n480 at *
  generalize v611.toNat = n611 at *
  generalize v614.toNat = n614 at *
  generalize v627.toNat = n627 at *
  generalize v629.toNat = n629 at *
  generalize v631.toNat = n631 at *
  generalize v632.toNat = n632 at *
  generalize v633.toNat = n633 at *
  generalize v635.toNat = n635 at *
  generalize v640.toNat = n640 at *
  first
    | omega
    | (obtain ⟨t614a, t614b⟩ := t614; rcases Nat.eq_zero_or_pos n480 with _ | _ <;> rcases t629 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t614a, t614b⟩ := t614; obtain ⟨qt627, et627⟩ := mod_q t627; clear t627; obtain ⟨qt632, et632⟩ := mod_q t632; clear t632; obtain ⟨qt640, et640⟩ := mod_q t640; clear t640; omega)
    | (obtain ⟨t614a, t614b⟩ := t614; obtain ⟨qt627, et627⟩ := mod_q t627; clear t627; obtain ⟨qt632, et632⟩ := mod_q t632; clear t632; obtain ⟨qt640, et640⟩ := mod_q t640; clear t640; rcases Nat.eq_zero_or_pos n480 with _ | _ <;> rcases t629 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P102 {v488 v600 v624 v628 v636 v638 v641 : Word}
    (t624 : v624.toNat = v488.toNat * 4234356049 % 2 ^ 32)
    (t628 : v628.toNat = v488.toNat * 4234356049 / 2 ^ 32)
    (t636 : v636.toNat = (v624.toNat + v600.toNat) % 2 ^ 32)
    (t638 : v636.toNat + 2 ^ 32 * v638.toNat = v624.toNat + v600.toNat)
    (t641 : v641.toNat = (v638.toNat + v628.toNat) % 2 ^ 32) :
    v636.toNat + 2 ^ 32 * v641.toNat = v488.toNat * 4234356049 + v600.toNat := by
  have := v488.isLt; have := v600.isLt; have := v624.isLt; have := v628.isLt; have := v636.isLt; have := v638.isLt; have := v641.isLt
  generalize v488.toNat = n488 at *
  generalize v600.toNat = n600 at *
  generalize v624.toNat = n624 at *
  generalize v628.toNat = n628 at *
  generalize v636.toNat = n636 at *
  generalize v638.toNat = n638 at *
  generalize v641.toNat = n641 at *
  first
    | omega
    | (obtain ⟨qt624, et624⟩ := mod_q t624; clear t624; obtain ⟨qt636, et636⟩ := mod_q t636; clear t636; omega)

theorem psm_v_P102l {v488 v600 v624 v636 v641 : Word}
    (t624 : v624.toNat = v488.toNat * 4234356049 % 2 ^ 32)
    (t636 : v636.toNat = (v624.toNat + v600.toNat) % 2 ^ 32)
    (wP102 : v636.toNat + 2 ^ 32 * v641.toNat = v488.toNat * 4234356049 + v600.toNat) :
    v636.toNat = (v636.toNat + 2 ^ 32 * v641.toNat) % 2 ^ 32 := by
  have := v488.isLt; have := v600.isLt; have := v624.isLt; have := v636.isLt; have := v641.isLt
  generalize v488.toNat = n488 at *
  generalize v600.toNat = n600 at *
  generalize v624.toNat = n624 at *
  generalize v636.toNat = n636 at *
  generalize v641.toNat = n641 at *
  first
    | omega
    | (obtain ⟨qt624, et624⟩ := mod_q t624; clear t624; obtain ⟨qt636, et636⟩ := mod_q t636; clear t636; omega)

theorem psm_v_P102h {v488 v600 v624 v628 v636 v638 v641 : Word}
    (t628 : v628.toNat = v488.toNat * 4234356049 / 2 ^ 32)
    (t638 : v636.toNat + 2 ^ 32 * v638.toNat = v624.toNat + v600.toNat)
    (t641 : v641.toNat = (v638.toNat + v628.toNat) % 2 ^ 32)
    (wP102 : v636.toNat + 2 ^ 32 * v641.toNat = v488.toNat * 4234356049 + v600.toNat) :
    v641.toNat = (v636.toNat + 2 ^ 32 * v641.toNat) / 2 ^ 32 := by
  have := v488.isLt; have := v600.isLt; have := v624.isLt; have := v628.isLt; have := v636.isLt; have := v638.isLt; have := v641.isLt
  generalize v488.toNat = n488 at *
  generalize v600.toNat = n600 at *
  generalize v624.toNat = n624 at *
  generalize v628.toNat = n628 at *
  generalize v636.toNat = n636 at *
  generalize v638.toNat = n638 at *
  generalize v641.toNat = n641 at *
  first
    | omega
    | (obtain ⟨qt641, et641⟩ := mod_q t641; clear t641; omega)

end C3.RV32
