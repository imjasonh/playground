//! A bounds-checked cursor over a byte slice.

use crate::error::Error;

/// Reads little-endian fields from a byte slice, failing instead of panicking
/// when a field runs past the end.
pub(crate) struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    pub(crate) fn new(buf: &'a [u8]) -> Self {
        Reader { buf, pos: 0 }
    }

    /// The number of bytes read so far.
    pub(crate) fn position(&self) -> usize {
        self.pos
    }

    /// The bytes from `start` up to the current position.
    pub(crate) fn since(&self, start: usize) -> Result<&'a [u8], Error> {
        self.buf.get(start..self.pos).ok_or(Error::Truncated)
    }

    pub(crate) fn bytes(&mut self, n: usize) -> Result<&'a [u8], Error> {
        let end = self.pos.checked_add(n).ok_or(Error::Truncated)?;
        let out = self.buf.get(self.pos..end).ok_or(Error::Truncated)?;
        self.pos = end;
        Ok(out)
    }

    pub(crate) fn array<const N: usize>(&mut self) -> Result<&'a [u8; N], Error> {
        self.bytes(N)?.try_into().map_err(|_| Error::Truncated)
    }

    pub(crate) fn u8(&mut self) -> Result<u8, Error> {
        Ok(u8::from_le_bytes(*self.array::<1>()?))
    }

    pub(crate) fn u16(&mut self) -> Result<u16, Error> {
        Ok(u16::from_le_bytes(*self.array::<2>()?))
    }

    pub(crate) fn u32(&mut self) -> Result<u32, Error> {
        Ok(u32::from_le_bytes(*self.array::<4>()?))
    }

    pub(crate) fn u64(&mut self) -> Result<u64, Error> {
        Ok(u64::from_le_bytes(*self.array::<8>()?))
    }

    /// Reads a magic number and fails unless it equals `magic`.
    pub(crate) fn magic(&mut self, magic: &[u8; 4]) -> Result<(), Error> {
        if self.array::<4>()? == magic {
            Ok(())
        } else {
            Err(Error::BadMagic)
        }
    }

    /// Reads a 2-byte format version and fails unless it is 1.
    pub(crate) fn version_1(&mut self) -> Result<(), Error> {
        if self.u16()? == 1 {
            Ok(())
        } else {
            Err(Error::BadVersion)
        }
    }

    /// Reads `n` reserved bytes and fails unless all are zero.
    pub(crate) fn reserved(&mut self, n: usize) -> Result<(), Error> {
        if self.bytes(n)?.iter().all(|&b| b == 0) {
            Ok(())
        } else {
            Err(Error::NonzeroReserved)
        }
    }

    /// Fails unless every byte has been read.
    pub(crate) fn finish(&self) -> Result<(), Error> {
        if self.pos == self.buf.len() {
            Ok(())
        } else {
            Err(Error::TrailingBytes)
        }
    }
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;

    #[test]
    fn reads_fields_and_rejects_overrun() {
        let mut r = Reader::new(&[1, 2, 0, 3, 0, 0]);
        assert_eq!(r.u8(), Ok(1));
        assert_eq!(r.u16(), Ok(2));
        assert_eq!(r.u32(), Err(Error::Truncated));
        assert_eq!(r.position(), 3);
        assert_eq!(r.finish(), Err(Error::TrailingBytes));
    }

    #[test]
    fn rejects_nonzero_reserved() {
        assert_eq!(
            Reader::new(&[0, 1]).reserved(2),
            Err(Error::NonzeroReserved)
        );
        assert_eq!(Reader::new(&[0, 0]).reserved(2), Ok(()));
    }
}
