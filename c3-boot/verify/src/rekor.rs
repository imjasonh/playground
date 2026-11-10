//! The Rekor v2 `hashedrekord` entry and its RFC 6962 leaf hash.

use crate::base64::Sink;
use crate::base64::encode_to;

/// Writes the RFC 8785 canonical JSON form of the Rekor v2 `hashedrekord`
/// entry that `docs/formats.md` defines.
pub fn write_entry<S: Sink>(digest: &[u8; 32], signature: &[u8], certificate: &[u8], sink: &mut S) {
    sink.write(br#"{"apiVersion":"0.0.2","kind":"hashedrekord","spec":{"hashedRekordV002":{"data":{"algorithm":"SHA2_256","digest":""#);
    encode_to(digest, sink);
    sink.write(br#""},"signature":{"content":""#);
    encode_to(signature, sink);
    sink.write(
        br#"","verifier":{"keyDetails":"PKIX_ECDSA_P256_SHA_256","x509Certificate":{"rawBytes":""#,
    );
    encode_to(certificate, sink);
    sink.write(br#""}}}}}}"#);
}

/// The RFC 6962 leaf hash of the entry, `SHA-256(0x00 || entry)`.
pub fn entry_leaf_hash(digest: &[u8; 32], signature: &[u8], certificate: &[u8]) -> [u8; 32] {
    let mut h = c3_crypto::Sha256::new();
    h.update(&[0x00]);
    write_entry(digest, signature, certificate, &mut h);
    h.finish()
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;
    use base64::Engine;
    use base64::engine::general_purpose::STANDARD;

    #[test]
    fn matches_logged_entry() {
        let bundle: serde_json::Value = serde_json::from_str(include_str!(
            "../../testdata/conformance/rekor2-happy-path/bundle.sigstore.json"
        ))
        .unwrap();
        let b64 = |v: &serde_json::Value| STANDARD.decode(v.as_str().unwrap()).unwrap();
        let digest: [u8; 32] = b64(&bundle["messageSignature"]["messageDigest"]["digest"])
            .try_into()
            .unwrap();
        let signature = b64(&bundle["messageSignature"]["signature"]);
        let cert = b64(&bundle["verificationMaterial"]["certificate"]["rawBytes"]);
        let logged = b64(&bundle["verificationMaterial"]["tlogEntries"][0]["canonicalizedBody"]);
        let mut out = Vec::new();
        write_entry(&digest, &signature, &cert, &mut out);
        assert_eq!(
            String::from_utf8(out).unwrap(),
            String::from_utf8(logged.clone()).unwrap()
        );
        let mut prefixed = vec![0u8];
        prefixed.extend_from_slice(&logged);
        assert_eq!(
            entry_leaf_hash(&digest, &signature, &cert),
            c3_crypto::sha256(&prefixed)
        );
    }
}
