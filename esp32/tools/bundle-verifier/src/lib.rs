//! Host test harness for the exact verifier source compiled into firmware.

pub mod trust {
    #[derive(Clone, Debug)]
    pub struct TrustedIdentity {
        pub identity: String,
        pub issuer: String,
    }

    #[derive(Clone)]
    pub struct TrustConfig {
        pub identities: Vec<TrustedIdentity>,
        pub fulcio_root_pem: Vec<u8>,
        pub fulcio_intermediate_pem: Vec<u8>,
        pub rekor_public_key_der: Vec<u8>,
        pub rekor_log_id: [u8; 32],
        pub rekor_valid_from: u64,
        pub rekor_checkpoint_origin: String,
    }
}

#[path = "../../../src/sig.rs"]
pub mod sig;

#[cfg(test)]
mod tests {
    use base64::{Engine as _, engine::general_purpose};
    use sha2::{Digest, Sha256};

    use super::trust::{TrustConfig, TrustedIdentity};

    const MANIFEST_DIGEST: &str =
        "db49840533ab409d875dd0007c99448f71ba61cce3cecdeb2b7f7176850cf190";
    const BUNDLE: &[u8] = include_bytes!("../tests/fixtures/cosign-v03-rekor-bundle.json");

    fn trust() -> TrustConfig {
        let rekor_pem = include_bytes!("../../../trust/rekor.pub");
        let (label, rekor_public_key_der) = x509_cert::der::pem::decode_vec(rekor_pem).unwrap();
        assert_eq!(label, "PUBLIC KEY");
        let rekor_log_id = Sha256::digest(&rekor_public_key_der).into();

        TrustConfig {
            identities: vec![TrustedIdentity {
                identity: "https://github.com/imjasonh/esp32/.github/workflows/publish.yml@refs/heads/main".into(),
                issuer: "https://token.actions.githubusercontent.com".into(),
            }],
            fulcio_root_pem: include_bytes!("../../../trust/fulcio_root.pem").to_vec(),
            fulcio_intermediate_pem: include_bytes!("../../../trust/fulcio_intermediate.pem")
                .to_vec(),
            rekor_public_key_der,
            rekor_log_id,
            rekor_valid_from: 1_610_452_407,
            rekor_checkpoint_origin: "rekor.sigstore.dev".into(),
        }
    }

    #[test]
    fn verifies_expired_fulcio_certificate_at_offline_rekor_time() {
        super::sig::verify_bundle(BUNDLE, MANIFEST_DIGEST, &trust()).unwrap();
    }

    #[test]
    fn rejects_tampered_inclusion_root() {
        let mut bundle: serde_json::Value = serde_json::from_slice(BUNDLE).unwrap();
        bundle["verificationMaterial"]["tlogEntries"][0]["inclusionProof"]["rootHash"] =
            serde_json::Value::String(general_purpose::STANDARD.encode([0_u8; 32]));
        let tampered = serde_json::to_vec(&bundle).unwrap();
        assert!(super::sig::verify_bundle(&tampered, MANIFEST_DIGEST, &trust()).is_err());
    }
}
