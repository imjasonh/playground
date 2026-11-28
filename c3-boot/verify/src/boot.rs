//! The bootloader's decision: which slot to boot, which boot-state record to
//! write, and the security level to reach before the jump.

use crate::bootstate::Slot;
use crate::bootstate::State;
use crate::bootstate::plan;
use crate::level::burn_target;

/// What the bootloader does once it has checked slots.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome<A> {
    /// Raise the eFuse level to `level_target`, then load `slot` and jump.
    Boot {
        /// The slot to boot.
        slot: Slot,
        /// What the slot check accepted.
        accepted: A,
        /// The level the eFuses must reach before the jump.
        level_target: u8,
    },
    /// No slot passed its checks.
    Halt,
}

/// Decides one boot from the boot state in use and the eFuse level.
///
/// `check` checks one slot against `efuse_level` and returns what it
/// accepted with the slot's level. `decide` calls it for the first slot that
/// `plan` names and, if that fails, for the other slot. `write` writes a
/// boot-state record, and `decide` calls it at most once, at the point
/// `docs/formats.md` gives: before any check to end an expired trial, after
/// a trial slot passes to use one of its boots, and after a trial slot fails
/// to end the trial before the other slot is checked.
pub fn decide<A>(
    state: &State,
    efuse_level: u8,
    mut check: impl FnMut(Slot) -> Option<(A, u8)>,
    mut write: impl FnMut(&State),
) -> Outcome<A> {
    let p = plan(state);
    let boot = |slot: Slot, accepted: A, level: u8| Outcome::Boot {
        slot,
        accepted,
        level_target: burn_target(level, state.is_confirmed(slot), efuse_level),
    };
    if let Some(first) = &p.write_first {
        write(first);
    }
    if let Some((accepted, level)) = check(p.first) {
        if p.is_trial {
            write(&state.with_trial_boot_used());
        }
        return boot(p.first, accepted, level);
    }
    if p.is_trial {
        write(&state.without_trial());
    }
    let other = p.first.other();
    match check(other) {
        Some((accepted, level)) => boot(other, accepted, level),
        None => Outcome::Halt,
    }
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;
    use crate::bootstate::Trial;

    fn trial_on_b(boots_left: u8) -> State {
        let mut s = State::DEFAULT.with_confirmed(Slot::A);
        s.trial = Some(Trial {
            slot: Slot::B,
            boots_left,
        });
        s
    }

    #[derive(Debug, PartialEq, Eq)]
    enum Call {
        Check(Slot),
        Write(State),
    }

    /// Runs `decide` and returns its outcome and every call it made, in
    /// order.
    fn run(
        state: &State,
        efuse_level: u8,
        a: Option<u8>,
        b: Option<u8>,
    ) -> (Outcome<()>, Vec<Call>) {
        let calls = core::cell::RefCell::new(Vec::new());
        let outcome = decide(
            state,
            efuse_level,
            |s| {
                calls.borrow_mut().push(Call::Check(s));
                match s {
                    Slot::A => a,
                    Slot::B => b,
                }
                .map(|l| ((), l))
            },
            |w| calls.borrow_mut().push(Call::Write(*w)),
        );
        (outcome, calls.into_inner())
    }

    fn boot(slot: Slot, level_target: u8) -> Outcome<()> {
        Outcome::Boot {
            slot,
            accepted: (),
            level_target,
        }
    }

    #[test]
    fn trial_boot_uses_a_boot_and_does_not_raise() {
        let s = trial_on_b(3);
        let (outcome, calls) = run(&s, 0, Some(0), Some(2));
        assert_eq!(outcome, boot(Slot::B, 0));
        assert_eq!(
            calls,
            [Call::Check(Slot::B), Call::Write(s.with_trial_boot_used())]
        );
    }

    #[test]
    fn failed_trial_ends_before_the_other_slot_is_checked() {
        let s = trial_on_b(3);
        let (outcome, calls) = run(&s, 1, Some(1), None);
        assert_eq!(outcome, boot(Slot::A, 1));
        assert_eq!(
            calls,
            [
                Call::Check(Slot::B),
                Call::Write(s.without_trial()),
                Call::Check(Slot::A)
            ]
        );
    }

    #[test]
    fn expired_trial_ends_before_any_check() {
        let s = trial_on_b(0);
        let (outcome, calls) = run(&s, 0, None, Some(4));
        assert_eq!(outcome, boot(Slot::B, 0));
        assert_eq!(
            calls,
            [
                Call::Write(s.without_trial()),
                Call::Check(Slot::A),
                Call::Check(Slot::B)
            ]
        );
    }

    #[test]
    fn confirmed_slot_raises_and_nothing_halts() {
        let s = State::DEFAULT.with_confirmed(Slot::A);
        let (outcome, calls) = run(&s, 1, Some(5), None);
        assert_eq!(outcome, boot(Slot::A, 5));
        assert_eq!(calls, [Call::Check(Slot::A)]);
        let (outcome, calls) = run(&s, 1, None, None);
        assert_eq!(outcome, Outcome::Halt);
        assert_eq!(calls, [Call::Check(Slot::A), Call::Check(Slot::B)]);
    }
}
