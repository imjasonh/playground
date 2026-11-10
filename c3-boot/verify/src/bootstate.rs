//! The boot-state record, which the bootloader treats as a hint.
//!
//! The application can write anything here. Nothing in this module decides
//! whether a slot is authentic; it only decides which slot to try first and
//! when to raise the security level for a confirmed slot.

use crate::error::Error;
use crate::reader::Reader;

/// The length of one boot-state copy.
pub const RECORD_LEN: usize = 32;
/// The most trial boots a trial slot can have left.
pub const MAX_TRIAL_BOOTS: u8 = 3;
const NO_TRIAL: u8 = 0xFF;

/// One of the two OTA slots.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Slot {
    /// Slot A.
    A,
    /// Slot B.
    B,
}

impl Slot {
    /// The other slot.
    pub fn other(self) -> Slot {
        match self {
            Slot::A => Slot::B,
            Slot::B => Slot::A,
        }
    }

    fn from_byte(b: u8) -> Result<Slot, Error> {
        match b {
            0 => Ok(Slot::A),
            1 => Ok(Slot::B),
            _ => Err(Error::OutOfRange),
        }
    }

    fn to_byte(self) -> u8 {
        match self {
            Slot::A => 0,
            Slot::B => 1,
        }
    }

    fn bit(self) -> u8 {
        match self {
            Slot::A => 0b01,
            Slot::B => 0b10,
        }
    }
}

/// A slot on trial, with the boots it has left.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Trial {
    /// The slot on trial.
    pub slot: Slot,
    /// Trial boots left, 0 through [`MAX_TRIAL_BOOTS`].
    pub boots_left: u8,
}

/// A decoded boot state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct State {
    /// The copy's generation.
    pub generation: u32,
    /// The slot to boot when no trial is running.
    pub preferred: Slot,
    /// The slot on trial, if any.
    pub trial: Option<Trial>,
    confirmed: u8,
}

impl State {
    /// The state used when neither copy is valid.
    pub const DEFAULT: State = State {
        generation: 0,
        preferred: Slot::A,
        trial: None,
        confirmed: 0,
    };

    /// Reports whether the record marks `slot` confirmed.
    pub fn is_confirmed(&self, slot: Slot) -> bool {
        self.confirmed & slot.bit() != 0
    }

    /// This state with the next generation, saturating at the maximum.
    fn next(&self) -> State {
        State {
            generation: self.generation.saturating_add(1),
            ..*self
        }
    }

    /// The state to write before jumping to a trial slot.
    pub fn with_trial_boot_used(&self) -> State {
        let trial = self.trial.map(|t| Trial {
            boots_left: t.boots_left.saturating_sub(1),
            ..t
        });
        State {
            trial,
            ..self.next()
        }
    }

    /// The state to write to end a trial.
    pub fn without_trial(&self) -> State {
        State {
            trial: None,
            ..self.next()
        }
    }
}

/// CRC-32 with the IEEE 802.3 polynomial, as zlib computes it.
pub fn crc32(data: &[u8]) -> u32 {
    let mut crc = 0xFFFF_FFFFu32;
    for &byte in data {
        crc ^= u32::from(byte);
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
        }
    }
    !crc
}

/// Decodes one copy. Fails unless every rule in `docs/formats.md` holds.
pub fn decode(bytes: &[u8; RECORD_LEN]) -> Result<State, Error> {
    let (body, crc) = bytes.split_last_chunk::<4>().ok_or(Error::Truncated)?;
    if crc32(body) != u32::from_le_bytes(*crc) {
        return Err(Error::BadChecksum);
    }
    let mut r = Reader::new(body);
    r.magic(b"C3BS")?;
    r.version_1()?;
    r.reserved(2)?;
    let generation = r.u32()?;
    let preferred = Slot::from_byte(r.u8()?)?;
    let trial_slot = r.u8()?;
    let boots_left = r.u8()?;
    let confirmed = r.u8()?;
    r.reserved(12)?;
    r.finish()?;

    if boots_left > MAX_TRIAL_BOOTS || confirmed & !0b11 != 0 {
        return Err(Error::OutOfRange);
    }
    let trial = if trial_slot == NO_TRIAL {
        if boots_left != 0 {
            return Err(Error::OutOfRange);
        }
        None
    } else {
        Some(Trial {
            slot: Slot::from_byte(trial_slot)?,
            boots_left,
        })
    };
    Ok(State {
        generation,
        preferred,
        trial,
        confirmed,
    })
}

/// Encodes a state as one copy.
pub fn encode(state: &State) -> [u8; RECORD_LEN] {
    let mut out = [0u8; RECORD_LEN];
    let (trial_slot, boots_left) = match state.trial {
        Some(t) => (t.slot.to_byte(), t.boots_left),
        None => (NO_TRIAL, 0),
    };
    let generation = state.generation.to_le_bytes();
    let fields: [(usize, &[u8]); 6] = [
        (0, b"C3BS"),
        (4, &[1, 0]),
        (8, &generation),
        (12, &[state.preferred.to_byte(), trial_slot]),
        (14, &[boots_left]),
        (15, &[state.confirmed]),
    ];
    for (at, value) in fields {
        let end = at.saturating_add(value.len());
        if let Some(dst) = out.get_mut(at..end) {
            dst.copy_from_slice(value);
        }
    }
    let crc = match out.split_last_chunk::<4>() {
        Some((body, _)) => crc32(body),
        None => 0,
    };
    if let Some((_, dst)) = out.split_last_chunk_mut::<4>() {
        *dst = crc.to_le_bytes();
    }
    out
}

/// Which copy holds the state in use.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Copy {
    /// Copy A.
    A,
    /// Copy B.
    B,
}

/// The state in use and where it came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Current {
    /// The state in use.
    pub state: State,
    /// The copy it came from, or `None` for the default state.
    pub copy: Option<Copy>,
}

impl Current {
    /// The copy to erase and rewrite for the next state.
    ///
    /// That is the copy not in use, or copy A if neither copy is valid.
    pub fn write_target(&self) -> Copy {
        match self.copy {
            Some(Copy::A) => Copy::B,
            Some(Copy::B) | None => Copy::A,
        }
    }
}

/// Chooses the state in use from the two copies.
pub fn read(a: &[u8; RECORD_LEN], b: &[u8; RECORD_LEN]) -> Current {
    match (decode(a), decode(b)) {
        (Ok(sa), Ok(sb)) if sb.generation > sa.generation => Current {
            state: sb,
            copy: Some(Copy::B),
        },
        (Ok(sa), _) => Current {
            state: sa,
            copy: Some(Copy::A),
        },
        (Err(_), Ok(sb)) => Current {
            state: sb,
            copy: Some(Copy::B),
        },
        (Err(_), Err(_)) => Current {
            state: State::DEFAULT,
            copy: None,
        },
    }
}

/// The first slot to try, and any state to write before trying it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Plan {
    /// The first slot to try.
    pub first: Slot,
    /// Whether `first` is a trial slot with boots left.
    pub is_trial: bool,
    /// A state to write before checking any slot. Set when an expired trial
    /// must be ended.
    pub write_first: Option<State>,
}

/// Decides which slot to try first, following `docs/formats.md`.
pub fn plan(state: &State) -> Plan {
    match state.trial {
        Some(t) if t.boots_left > 0 => Plan {
            first: t.slot,
            is_trial: true,
            write_first: None,
        },
        Some(_) => Plan {
            first: state.preferred,
            is_trial: false,
            write_first: Some(state.without_trial()),
        },
        None => Plan {
            first: state.preferred,
            is_trial: false,
            write_first: None,
        },
    }
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;

    fn state(generation: u32, preferred: Slot, trial: Option<Trial>, confirmed: u8) -> State {
        State {
            generation,
            preferred,
            trial,
            confirmed,
        }
    }

    #[test]
    fn crc_matches_zlib() {
        assert_eq!(crc32(b"123456789"), 0xCBF4_3926);
        assert_eq!(crc32(b""), 0);
    }

    #[test]
    fn round_trips() {
        let s = state(
            7,
            Slot::B,
            Some(Trial {
                slot: Slot::A,
                boots_left: 2,
            }),
            0b10,
        );
        assert_eq!(decode(&encode(&s)), Ok(s));
        assert_eq!(decode(&encode(&State::DEFAULT)), Ok(State::DEFAULT));
    }

    #[test]
    fn rejects_corruption_and_bad_fields() {
        let s = state(1, Slot::A, None, 0);
        let mut bytes = encode(&s);
        bytes[9] ^= 1;
        assert_eq!(decode(&bytes), Err(Error::BadChecksum));

        let mut bad = encode(&s);
        bad[14] = 1;
        let crc = crc32(&bad[..28]).to_le_bytes();
        bad[28..].copy_from_slice(&crc);
        assert_eq!(decode(&bad), Err(Error::OutOfRange));

        let mut bad = encode(&s);
        bad[15] = 0b100;
        let crc = crc32(&bad[..28]).to_le_bytes();
        bad[28..].copy_from_slice(&crc);
        assert_eq!(decode(&bad), Err(Error::OutOfRange));

        let mut bad = encode(&s);
        bad[20] = 1;
        let crc = crc32(&bad[..28]).to_le_bytes();
        bad[28..].copy_from_slice(&crc);
        assert_eq!(decode(&bad), Err(Error::NonzeroReserved));

        assert!(decode(&[0xFF; RECORD_LEN]).is_err());
    }

    #[test]
    fn reads_newer_copy_and_falls_back() {
        let old = encode(&state(1, Slot::A, None, 0));
        let new = encode(&state(2, Slot::B, None, 0));
        let erased = [0xFF; RECORD_LEN];
        assert_eq!(read(&old, &new).copy, Some(Copy::B));
        assert_eq!(read(&new, &old).copy, Some(Copy::A));
        assert_eq!(read(&old, &old).copy, Some(Copy::A));
        assert_eq!(read(&erased, &new).copy, Some(Copy::B));
        let none = read(&erased, &erased);
        assert_eq!(none.state, State::DEFAULT);
        assert_eq!(none.write_target(), Copy::A);
        assert_eq!(read(&old, &new).write_target(), Copy::A);
        assert_eq!(read(&new, &old).write_target(), Copy::B);
    }

    #[test]
    fn plans_trial_and_expiry() {
        let trial = state(
            5,
            Slot::A,
            Some(Trial {
                slot: Slot::B,
                boots_left: 1,
            }),
            0b01,
        );
        let p = plan(&trial);
        assert_eq!((p.first, p.is_trial, p.write_first), (Slot::B, true, None));
        let used = trial.with_trial_boot_used();
        assert_eq!(used.generation, 6);
        assert_eq!(used.trial.map(|t| t.boots_left), Some(0));

        let p = plan(&used);
        assert_eq!((p.first, p.is_trial), (Slot::A, false));
        assert_eq!(
            p.write_first.map(|s| (s.trial, s.generation)),
            Some((None, 7))
        );
    }

    #[test]
    fn generation_saturates() {
        let s = state(u32::MAX, Slot::A, None, 0);
        assert_eq!(s.without_trial().generation, u32::MAX);
    }
}
