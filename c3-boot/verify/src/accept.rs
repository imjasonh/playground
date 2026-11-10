//! Every check on one slot, composed into one decision.

use crate::error::Error;
use crate::image::Header;
use crate::keys::KeySet;

/// The parts of a slot that the bootloader read from flash.
#[derive(Clone, Copy, Debug)]
pub struct SlotParts<'a> {
    /// At least the image header and segment table, from the start of the
    /// image.
    pub image_header: &'a [u8],
    /// The manifest's image length.
    pub image_length: u32,
    /// The SHA-256 digest of the whole signed image.
    pub image_digest: [u8; 32],
    /// The bundle container.
    pub bundle: &'a [u8],
    /// The key-set chain.
    pub chain: &'a [u8],
    /// The trust-root blob.
    pub blob: &'a [u8],
}

/// A slot that passed every check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Accepted {
    /// The checked image header.
    pub header: Header,
    /// The slot's level: the image's security version, which equals the
    /// blob's level.
    pub level: u8,
    /// The TSA's signed time for the image signature.
    pub signed_time: u64,
}

/// Checks one slot: the image header, the key-set chain from `genesis`, the
/// trust-root blob, the level rules against `efuse_level`, and the Sigstore
/// bundle against the image digest.
///
/// `scratch` must hold the largest domain-separated message, 4,120 bytes.
pub fn accept_slot(
    parts: &SlotParts<'_>,
    genesis: KeySet<'_>,
    efuse_level: u8,
    scratch: &mut [u8],
) -> Result<Accepted, Error> {
    let header = crate::image::parse(parts.image_header, parts.image_length)?;
    let chain = crate::chain::parse(parts.chain)?;
    let tip = crate::chain::verify(&chain, genesis, scratch)?;
    let root = crate::trustroot::parse(parts.blob)?;
    crate::trustroot::verify(&root, &tip, scratch)?;
    crate::level::check_slot(tip.level, root.level, header.security_version, efuse_level)?;
    let bundle = crate::bundle::parse(parts.bundle)?;
    let verified = crate::sigstore::verify(&bundle, &root, &parts.image_digest)?;
    Ok(Accepted {
        header,
        level: root.level,
        signed_time: verified.signed_time,
    })
}
