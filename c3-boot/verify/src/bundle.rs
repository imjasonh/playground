//! The bundle container that CI builds from a Sigstore bundle.

use crate::error::Error;
use crate::reader::Reader;

/// The signed byte strings from a Sigstore bundle, in a fixed order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bundle<'a> {
    /// The Fulcio leaf certificate, DER.
    pub leaf_certificate: &'a [u8],
    /// The image signature, DER `ECDSA-Sig-Value`.
    pub image_signature: &'a [u8],
    /// The entry's index in the log.
    pub log_index: u64,
    /// The inclusion proof's hashes, concatenated.
    pub inclusion_proof: &'a [u8],
    /// The signed checkpoint note.
    pub checkpoint: &'a [u8],
    /// The RFC 3161 `TimeStampResp`, DER.
    pub timestamp: &'a [u8],
}

fn field<'a>(r: &mut Reader<'a>, min: usize, max: usize) -> Result<&'a [u8], Error> {
    let len = usize::try_from(r.u32()?).map_err(|_| Error::OutOfRange)?;
    if len < min || len > max {
        return Err(Error::OutOfRange);
    }
    r.bytes(len)
}

/// Parses a bundle container, checking each field's length rule.
pub fn parse(bytes: &[u8]) -> Result<Bundle<'_>, Error> {
    let mut r = Reader::new(bytes);
    r.magic(b"C3BN")?;
    r.version_1()?;
    let leaf_certificate = field(&mut r, 1, 4_096)?;
    let image_signature = field(&mut r, 8, 72)?;
    let log_index_bytes: [u8; 8] = field(&mut r, 8, 8)?
        .try_into()
        .map_err(|_| Error::OutOfRange)?;
    let inclusion_proof = field(
        &mut r,
        0,
        crate::merkle::MAX_PROOF_HASHES.saturating_mul(32),
    )?;
    if !inclusion_proof.len().is_multiple_of(32) {
        return Err(Error::OutOfRange);
    }
    let checkpoint = field(&mut r, 1, 1_024)?;
    let timestamp = field(&mut r, 1, 8_192)?;
    r.finish()?;
    Ok(Bundle {
        leaf_certificate,
        image_signature,
        log_index: u64::from_le_bytes(log_index_bytes),
        inclusion_proof,
        checkpoint,
        timestamp,
    })
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
pub(crate) mod tests {
    use super::*;

    pub(crate) fn encode(fields: [&[u8]; 6]) -> Vec<u8> {
        let mut out = b"C3BN".to_vec();
        out.extend_from_slice(&1u16.to_le_bytes());
        for f in fields {
            out.extend_from_slice(&(f.len() as u32).to_le_bytes());
            out.extend_from_slice(f);
        }
        out
    }

    #[test]
    fn parses_minimum_container() {
        let bytes = encode([b"c", &[1; 8], &7u64.to_le_bytes(), &[], b"k", b"t"]);
        assert_eq!(bytes.len(), 49);
        let b = parse(&bytes).unwrap();
        assert_eq!(b.log_index, 7);
        assert!(b.inclusion_proof.is_empty());
    }

    #[test]
    fn rejects_bad_fields() {
        let ok = [
            &b"c"[..],
            &[1; 8],
            &7u64.to_le_bytes(),
            &[0; 32],
            b"k",
            b"t",
        ];
        assert!(parse(&encode(ok)).is_ok());
        let mut f = ok;
        f[3] = &[0; 31];
        assert_eq!(parse(&encode(f)), Err(Error::OutOfRange));
        let mut f = ok;
        f[2] = &[0; 9];
        assert_eq!(parse(&encode(f)), Err(Error::OutOfRange));
        let mut f = ok;
        f[1] = &[0; 7];
        assert_eq!(parse(&encode(f)), Err(Error::OutOfRange));
        let mut bytes = encode(ok);
        bytes.push(0);
        assert_eq!(parse(&bytes), Err(Error::TrailingBytes));
    }
}
