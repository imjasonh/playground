//! Dice helpers. House rule: a natural 1 always fails, a natural 6 always
//! succeeds, regardless of the target number or strength-vs-armor math.

/// Whether a d6 success roll passes a `need`+ target.
///
/// A natural 1 always fails. A natural 6 always succeeds.
pub fn succeeds(roll: i32, need: i32) -> bool {
    debug_assert!((1..=6).contains(&roll));
    if roll == 1 {
        return false;
    }
    if roll == 6 {
        return true;
    }
    roll >= need
}

/// Whether a penetration roll beats armor (`roll + strength > armor`).
///
/// A natural 1 always glances. A natural 6 always penetrates.
pub fn penetrates(roll: i32, strength: i32, armor: i32) -> bool {
    debug_assert!((1..=6).contains(&roll));
    if roll == 1 {
        return false;
    }
    if roll == 6 {
        return true;
    }
    roll + strength > armor
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one_always_fails_hit() {
        assert!(!succeeds(1, 2));
        assert!(!succeeds(1, 1));
    }

    #[test]
    fn six_always_hits() {
        assert!(succeeds(6, 6));
        assert!(succeeds(6, 7));
        assert!(succeeds(6, 99));
    }

    #[test]
    fn middle_uses_target() {
        assert!(!succeeds(3, 4));
        assert!(succeeds(4, 4));
    }

    #[test]
    fn one_always_glances_even_when_math_pens() {
        // Stock AT 6 vs armor 6: 1+6=7 > 6 would pen without the house rule.
        assert!(!penetrates(1, 6, 6));
    }

    #[test]
    fn six_always_pens_even_when_math_fails() {
        assert!(penetrates(6, 4, 20));
    }
}
