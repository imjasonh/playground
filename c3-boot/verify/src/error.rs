//! The reasons a check rejects its input.

/// Why a check rejected its input.
///
/// Every rejection is final for the slot being checked. The variants exist so
/// that tests can assert which rule fired.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The input ended before a field did.
    Truncated,
    /// Bytes remain after the last field.
    TrailingBytes,
    /// A magic number didn't match.
    BadMagic,
    /// A format version isn't 1.
    BadVersion,
    /// A reserved field isn't zero.
    NonzeroReserved,
    /// A field is outside the range its format allows.
    OutOfRange,
    /// An offset plus a length overflowed.
    Overflow,
    /// Regions are out of order, overlap, or leave the slot.
    BadLayout,
    /// The image header names a different chip.
    WrongChip,
    /// A segment breaks a segment rule.
    BadSegment,
    /// Two segments overlap in memory.
    SegmentOverlap,
    /// The entry point isn't in an executable segment.
    BadEntryPoint,
    /// A string contains a byte that isn't printable ASCII.
    NotPrintable,
    /// A key set lists the same key twice, or a blob lists the same entry
    /// twice.
    DuplicateKey,
    /// A public key can't verify any signature.
    BadKey,
    /// Signature key indexes aren't strictly increasing or are out of range.
    BadKeyIndex,
    /// A signature doesn't verify.
    BadSignature,
    /// A checksum doesn't match.
    BadChecksum,
    /// A level rule failed.
    BadLevel,
    /// A message doesn't fit in the scratch buffer.
    ScratchTooSmall,
}
