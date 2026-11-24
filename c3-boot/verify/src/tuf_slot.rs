//! Every check on one slot whose trust comes from Sigstore's TUF root,
//! composed into one decision.
//!
//! This replaces the key-set chain and trust-root blob of
//! [`crate::accept`] with TUF metadata that the device checks from a pinned
//! root, and the release identity with a compiled-in policy. The bootloader
//! doesn't call it yet; the cutover plan is in c3-boot's task list.

use crate::accept::Accepted;
use crate::error::Error;
use crate::trustroot::Policy;
use crate::tuf::TufError;

/// The parts of a slot that the bootloader reads from flash.
#[derive(Clone, Copy, Debug)]
pub struct TufSlotParts<'a> {
    /// At least the image header and segment table, from the start of the
    /// image.
    pub image_header: &'a [u8],
    /// The manifest's image length.
    pub image_length: u32,
    /// The SHA-256 digest of the whole signed image.
    pub image_digest: [u8; 32],
    /// The bundle container.
    pub bundle: &'a [u8],
    /// The TUF part, which [`crate::tuf::parse_parts`] reads.
    pub tuf: &'a [u8],
}

/// Checks one slot: the image header, the image's security version against
/// `efuse_level`, the TUF metadata from `pinned_root`, the keys in
/// `trusted_root.json` with `policy`, the Sigstore bundle against the image
/// digest, and that the TSA's signed time is before the metadata expired.
///
/// `buf` holds the certificates read from `trusted_root.json` and must hold
/// [`crate::trusted_root::buffer_len`] of its length.
pub fn accept_slot<'a>(
    parts: &TufSlotParts<'a>,
    pinned_root: &'a [u8],
    policy: &Policy<'a>,
    efuse_level: u8,
    buf: &'a mut [u8],
) -> Result<Accepted, TufError> {
    let header = crate::image::parse(parts.image_header, parts.image_length)?;
    if header.security_version < efuse_level {
        return Err(Error::BadLevel.into());
    }
    let tuf = crate::tuf::parse_parts(parts.tuf)?;
    let verified = crate::tuf::verify(pinned_root, &tuf)?;
    let root = crate::trusted_root::extract(tuf.trusted_root, *policy, buf)?;
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
