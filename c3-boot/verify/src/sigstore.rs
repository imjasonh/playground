//! Composes the Sigstore checks on one slot's bundle.

use crate::bundle::Bundle;
use crate::error::Error;
use crate::trustroot::TrustRoot;
use crate::trustroot::Window;

/// What a verified bundle proves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Verified {
    /// The TSA's signed time for the signature, in seconds since the Unix
    /// epoch.
    pub signed_time: u64,
    /// The entry's index in the log.
    pub log_index: u64,
}

fn require(ok: bool, err: Error) -> Result<(), Error> {
    if ok { Ok(()) } else { Err(err) }
}

/// Verifies that `bundle` proves the release workflow signed an image whose
/// SHA-256 digest is `image_digest`, under the keys and policy in `root`.
///
/// The checks are the ones `docs/esp32c3-verified-ota-plan.md` lists for a
/// slot: the leaf certificate chains to a listed Fulcio intermediate and
/// matches the identity policy, the leaf key signed the digest, a listed TSA
/// timestamped that signature, a listed log's checkpoint includes the
/// rebuilt entry, and the signed time is inside every validity window that
/// took part.
pub fn verify(
    bundle: &Bundle<'_>,
    root: &TrustRoot<'_>,
    image_digest: &[u8; 32],
) -> Result<Verified, Error> {
    let leaf = crate::x509::parse_leaf(bundle.leaf_certificate)?;
    let intermediate = root
        .fulcio()
        .find(|f| f.subject == leaf.issuer)
        .ok_or(Error::NoMatchingKey)?;
    crate::x509::verify_leaf(&leaf, intermediate)?;

    let policy = &root.policy;
    let identity_ok = leaf.issuer_v2 == policy.issuer
        && leaf.build_signer_uri == policy.build_signer_uri
        && leaf.repository_id == policy.repository_id
        && leaf.owner_id == policy.owner_id
        && leaf.trigger == policy.trigger;
    require(identity_ok, Error::PolicyMismatch)?;

    let (r, s) = crate::der::ecdsa_signature::<32>(bundle.image_signature)?;
    require(
        c3_crypto::p256_verify_prehash(leaf.public_key, image_digest, &r, &s),
        Error::BadSignature,
    )?;

    let ts = crate::tsa::parse_timestamp(bundle.timestamp)?;
    let tsa = root
        .tsas()
        .find(|t| t.signer_id == ts.signer_id)
        .ok_or(Error::NoMatchingKey)?;
    crate::tsa::verify_timestamp(&ts, tsa, bundle.image_signature)?;

    let checkpoint = crate::checkpoint::verify(bundle.checkpoint, root)?;
    require(bundle.log_index < checkpoint.size, Error::BadProof)?;
    let leaf_hash = crate::rekor::entry_leaf_hash(
        image_digest,
        bundle.image_signature,
        bundle.leaf_certificate,
    );
    let computed = crate::merkle::root_from_inclusion(
        bundle.log_index,
        checkpoint.size,
        &leaf_hash,
        bundle.inclusion_proof,
    )?;
    require(computed == checkpoint.root, Error::BadProof)?;

    let t = ts.gen_time;
    let leaf_window = Window {
        not_before: leaf.not_before,
        not_after: leaf.not_after,
    };
    let in_windows = leaf_window.contains(t)
        && intermediate.window.contains(t)
        && tsa.window.contains(t)
        && checkpoint.log.window.contains(t);
    require(in_windows, Error::OutsideWindow)?;

    Ok(Verified {
        signed_time: t,
        log_index: bundle.log_index,
    })
}
