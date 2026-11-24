//! Every check on one slot, composed into one decision. Trust comes from
//! Sigstore's TUF root, which the bootloader pins, and the release identity
//! from a compiled-in policy.

use crate::error::Error;
use crate::image::Header;
use crate::trustroot::Policy;
use crate::tuf::Source;
use crate::tuf::TufError;

/// The parts of a slot that the bootloader reads from flash.
#[derive(Clone, Copy, Debug)]
pub struct TufSlotParts<'a, S> {
    /// At least the image header and segment table, from the start of the
    /// image.
    pub image_header: &'a [u8],
    /// The manifest's image length.
    pub image_length: u32,
    /// The SHA-256 digest of the whole signed image.
    pub image_digest: [u8; 32],
    /// The bundle container.
    pub bundle: &'a [u8],
    /// Where the TUF part is read from, one document at a time.
    pub tuf: S,
    /// The manifest's TUF part length.
    pub tuf_length: u32,
}

/// A slot that passed every check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Accepted {
    /// The checked image header.
    pub header: Header,
    /// The slot's level: the image's security version.
    pub level: u8,
    /// The TSA's signed time for the image signature.
    pub signed_time: u64,
}

/// Checks one slot: the image header, the image's security version against
/// `efuse_level`, the TUF metadata from `pinned_root`, the keys in
/// `trusted_root.json` with `policy`, the Sigstore bundle against the image
/// digest, and that the TSA's signed time is before the metadata expired.
///
/// `doc` holds each TUF document in turn and must hold
/// [`crate::tuf::MAX_DOC_LEN`] bytes, or the longest document in the part.
/// `buf` holds the certificates read from `trusted_root.json` and must hold
/// [`crate::trusted_root::buffer_len`] of its length.
pub fn accept_slot<'a, S: Source>(
    parts: TufSlotParts<'a, S>,
    pinned_root: &'a [u8],
    policy: &Policy<'a>,
    efuse_level: u8,
    doc: &'a mut [u8],
    buf: &'a mut [u8],
) -> Result<Accepted, TufError> {
    let mut tuf = parts.tuf;
    let header = crate::image::parse(parts.image_header, parts.image_length)?;
    if header.security_version < efuse_level {
        return Err(Error::BadLevel.into());
    }
    let (verified, trusted_root) =
        crate::tuf::verify(pinned_root, &mut tuf, parts.tuf_length, doc)?;
    let root = crate::trusted_root::extract(trusted_root, *policy, buf)?;
    let bundle = crate::bundle::parse(parts.bundle)?;
    let signed = crate::sigstore::verify(&bundle, &root, &parts.image_digest)?;
    if signed.signed_time > verified.expires {
        return Err(TufError::Expired);
    }
    Ok(Accepted {
        header,
        level: header.security_version,
        signed_time: signed.signed_time,
    })
}
