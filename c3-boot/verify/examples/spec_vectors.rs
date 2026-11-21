//! Prints `c3-verify`'s answers for every input in a fixed grid, in the
//! format of `c3-boot-proofs/Vectors.lean`, so that CI can compare the Rust
//! code with the Lean specification line by line.

use std::io::BufWriter;
use std::io::Write;

use c3_verify::boot::Outcome;
use c3_verify::boot::decide;
use c3_verify::bootstate::Slot;
use c3_verify::bootstate::State;
use c3_verify::bootstate::Trial;
use c3_verify::level::burn_target;
use c3_verify::level::check_slot;
use c3_verify::level::level_of;
use c3_verify::level::next_bit;

fn slot_name(s: Slot) -> &'static str {
    match s {
        Slot::A => "A",
        Slot::B => "B",
    }
}

fn opt(o: Option<u8>) -> String {
    o.map_or_else(|| "-".to_string(), |n| n.to_string())
}

fn confirmed(s: &State) -> u8 {
    u8::from(s.is_confirmed(Slot::A)) | (u8::from(s.is_confirmed(Slot::B)) << 1)
}

fn state(s: &State) -> String {
    let trial = s.trial.map_or_else(
        || "-".to_string(),
        |t| format!("{}{}", slot_name(t.slot), t.boots_left),
    );
    format!(
        "g={} p={} t={} c={}",
        s.generation,
        slot_name(s.preferred),
        trial,
        confirmed(s)
    )
}

fn main() -> std::io::Result<()> {
    let mut out = BufWriter::new(std::io::stdout().lock());
    for v in 0..=u16::MAX {
        let mask = next_bit(v).map_or_else(|| "-".to_string(), |m| m.to_string());
        writeln!(out, "level {v} {} {mask}", level_of(v))?;
    }
    for c in 0..=16u8 {
        for b in 0..=16u8 {
            for s in 0..=16u8 {
                for e in 0..=16u8 {
                    let ok = u8::from(check_slot(c, b, s, e).is_ok());
                    writeln!(out, "check {c} {b} {s} {e} {ok}")?;
                }
            }
        }
    }
    for l in 0..=16u8 {
        for c in [false, true] {
            for e in 0..=16u8 {
                writeln!(
                    out,
                    "target {l} {} {e} {}",
                    u8::from(c),
                    burn_target(l, c, e)
                )?;
            }
        }
    }
    let mut trials = vec![None];
    for slot in [Slot::A, Slot::B] {
        for boots_left in 0..4 {
            trials.push(Some(Trial { slot, boots_left }));
        }
    }
    let slot_levels = [None, Some(0), Some(1), Some(5), Some(16)];
    for generation in [0, 7, u32::MAX] {
        for preferred in [Slot::A, Slot::B] {
            for trial in &trials {
                for c in 0..4u8 {
                    let mut st = State::DEFAULT;
                    if c & 1 != 0 {
                        st = st.with_confirmed(Slot::A);
                    }
                    if c & 2 != 0 {
                        st = st.with_confirmed(Slot::B);
                    }
                    st.generation = generation;
                    st.preferred = preferred;
                    st.trial = *trial;
                    for e in [0u8, 1, 5, 16] {
                        for la in slot_levels {
                            for lb in slot_levels {
                                let mut written = Vec::new();
                                let outcome = decide(
                                    &st,
                                    e,
                                    |s| {
                                        match s {
                                            Slot::A => la,
                                            Slot::B => lb,
                                        }
                                        .filter(|&l| e <= l && l <= 16)
                                        .map(|l| ((), l))
                                    },
                                    |w| written.push(*w),
                                );
                                assert!(written.len() <= 1, "decide wrote more than one record");
                                let write = written.first().map_or_else(|| "-".to_string(), state);
                                let outcome = match outcome {
                                    Outcome::Boot {
                                        slot, level_target, ..
                                    } => format!("boot {} {level_target}", slot_name(slot)),
                                    Outcome::Halt => "halt".to_string(),
                                };
                                writeln!(
                                    out,
                                    "decide {} e={e} a={} b={} | {write} | {outcome}",
                                    state(&st),
                                    opt(la),
                                    opt(lb)
                                )?;
                            }
                        }
                    }
                }
            }
        }
    }
    out.flush()
}
