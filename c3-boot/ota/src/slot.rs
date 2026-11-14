//! Assembles slots and whole flash images, and checks a slot on the host.

use c3_verify::accept::Accepted;
use c3_verify::accept::SlotParts;
use c3_verify::keys::KeySet;
use c3_verify::layout;

/// The flash size the layout assumes.
pub const FLASH_SIZE: usize = 0x40_0000;

fn align4(n: usize) -> usize {
    n.div_ceil(4) * 4
}

/// Lays out a slot: the manifest, the image at `0x10000`, then the bundle,
/// chain, and blob, each on a 4-byte boundary. Unused bytes are `0xFF`, as
/// erased flash reads.
pub fn assemble(image: &[u8], bundle: &[u8], chain: &[u8], blob: &[u8]) -> Result<Vec<u8>, String> {
    let image_off = layout::IMAGE_OFFSET as usize;
    let bundle_off = align4(image_off + image.len());
    let chain_off = align4(bundle_off + bundle.len());
    let blob_off = align4(chain_off + chain.len());
    let end = blob_off + blob.len();
    if end > layout::SLOT_SIZE as usize {
        return Err(format!(
            "slot needs {end:#x} bytes, more than {:#x}",
            layout::SLOT_SIZE
        ));
    }
    let mut out = vec![0xFF; end];
    let mut manifest = b"C3SL".to_vec();
    manifest.extend_from_slice(&1u16.to_le_bytes());
    manifest.extend_from_slice(&[0, 0]);
    for (off, part) in [
        (image_off, image),
        (bundle_off, bundle),
        (chain_off, chain),
        (blob_off, blob),
    ] {
        manifest.extend_from_slice(&(off as u32).to_le_bytes());
        manifest.extend_from_slice(&(part.len() as u32).to_le_bytes());
        out[off..off + part.len()].copy_from_slice(part);
    }
    out[..manifest.len()].copy_from_slice(&manifest);
    c3_verify::manifest::parse(&manifest)
        .map_err(|e| format!("manifest fails its own checks: {e:?}"))?;
    Ok(out)
}

/// Checks `slot` with the same `c3-verify` code the bootloader runs.
pub fn verify(slot: &[u8], genesis: &[u8; 128], efuse_level: u8) -> Result<Accepted, String> {
    let raw = slot
        .get(..c3_verify::manifest::MANIFEST_LEN)
        .ok_or("slot too short")?;
    let m = c3_verify::manifest::parse(raw).map_err(|e| format!("manifest: {e:?}"))?;
    let part = |p: c3_verify::manifest::Part| -> Result<&[u8], String> {
        slot.get(p.offset as usize..(p.offset + p.length) as usize)
            .ok_or_else(|| "part past end of slot".to_string())
    };
    let image = part(m.image)?;
    let parts = SlotParts {
        image_header: image,
        image_length: m.image.length,
        image_digest: c3_crypto::sha256(image),
        bundle: part(m.bundle)?,
        chain: part(m.chain)?,
        blob: part(m.blob)?,
    };
    let genesis = KeySet::new(genesis).map_err(|e| format!("genesis keys: {e:?}"))?;
    let mut scratch = vec![0u8; 4_120];
    c3_verify::accept::accept_slot(&parts, genesis, efuse_level, &mut scratch)
        .map_err(|e| format!("{e:?}"))
}

/// Builds a whole flash image: the bootloader at 0, an optional boot-state
/// record in copy A, and the slots. Everything else is `0xFF`.
pub fn flash_image(
    bootloader: &[u8],
    record: Option<&[u8]>,
    slot_a: Option<&[u8]>,
    slot_b: Option<&[u8]>,
) -> Result<Vec<u8>, String> {
    let mut out = vec![0xFF; FLASH_SIZE];
    let mut put = |at: u32, max: u32, bytes: &[u8]| -> Result<(), String> {
        if bytes.len() > max as usize {
            return Err(format!("{} bytes don't fit in {max:#x}", bytes.len()));
        }
        let at = at as usize;
        out[at..at + bytes.len()].copy_from_slice(bytes);
        Ok(())
    };
    put(0, layout::BOOT_STATE_A_OFFSET, bootloader)?;
    if let Some(r) = record {
        put(layout::BOOT_STATE_A_OFFSET, layout::SECTOR_SIZE, r)?;
    }
    if let Some(s) = slot_a {
        put(layout::SLOT_A_OFFSET, layout::SLOT_SIZE, s)?;
    }
    if let Some(s) = slot_b {
        put(layout::SLOT_B_OFFSET, layout::SLOT_SIZE, s)?;
    }
    Ok(out)
}
