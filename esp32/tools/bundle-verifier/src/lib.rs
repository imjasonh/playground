//! Host test harness for the exact verifier source compiled into firmware.

pub mod trust {
    #[derive(Clone, Debug)]
    pub struct TrustedIdentity {
        pub identity: String,
        pub issuer: String,
    }

    #[derive(Clone)]
    pub enum RekorPublicKey {
        EcdsaP256(Vec<u8>),
        Ed25519([u8; 32]),
    }

    #[derive(Clone)]
    pub struct TrustedRekorLog {
        pub log_id: [u8; 32],
        pub valid_from: u64,
        pub valid_until: Option<u64>,
        pub checkpoint_origin: &'static str,
        pub public_key: RekorPublicKey,
    }

    #[derive(Clone)]
    pub struct TrustedTimestampAuthority {
        pub leaf_der: Vec<u8>,
        pub root_der: Vec<u8>,
        pub valid_from: u64,
        pub valid_until: Option<u64>,
        pub policy_oid: &'static str,
    }

    #[derive(Clone)]
    pub struct TrustConfig {
        pub identities: Vec<TrustedIdentity>,
        pub fulcio_root_pem: Vec<u8>,
        pub fulcio_intermediate_pem: Vec<u8>,
        pub rekor_logs: Vec<TrustedRekorLog>,
        pub timestamp_authority: TrustedTimestampAuthority,
    }
}

#[path = "../../../src/sig.rs"]
pub mod sig;

#[cfg(test)]
mod tests {
    use base64::{Engine as _, engine::general_purpose};
    use sha2::{Digest, Sha256};

    use super::trust::{
        RekorPublicKey, TrustConfig, TrustedIdentity, TrustedRekorLog, TrustedTimestampAuthority,
    };

    const V1_MANIFEST_DIGEST: &str =
        "db49840533ab409d875dd0007c99448f71ba61cce3cecdeb2b7f7176850cf190";
    const V1_BUNDLE: &[u8] = include_bytes!("../tests/fixtures/cosign-v03-rekor-bundle.json");
    const V2_SUBJECT_DIGEST: &str =
        "a0cfc71271d6e278e57cd332ff957c3f7043fdda354c4cbb190a30d56efa01bf";
    const V2_BUNDLE: &[u8] = include_bytes!("../tests/fixtures/rekor-v2-bundle.json");

    fn pem_der(pem: &[u8], expected_label: &str) -> Vec<u8> {
        let (label, der) = x509_cert::der::pem::decode_vec(pem).unwrap();
        assert_eq!(label, expected_label);
        der
    }

    fn production_tsa() -> TrustedTimestampAuthority {
        TrustedTimestampAuthority {
            leaf_der: pem_der(include_bytes!("../../../trust/tsa-leaf.pem"), "CERTIFICATE"),
            root_der: pem_der(include_bytes!("../../../trust/tsa-root.pem"), "CERTIFICATE"),
            valid_from: 1_751_587_200,
            valid_until: None,
            policy_oid: "1.3.6.1.4.1.57264.2",
        }
    }

    fn v1_trust() -> TrustConfig {
        let key_der = pem_der(include_bytes!("../../../trust/rekor.pub"), "PUBLIC KEY");
        TrustConfig {
            identities: vec![TrustedIdentity {
                identity: "https://github.com/imjasonh/esp32/.github/workflows/publish.yml@refs/heads/main".into(),
                issuer: "https://token.actions.githubusercontent.com".into(),
            }],
            fulcio_root_pem: include_bytes!("../../../trust/fulcio_root.pem").to_vec(),
            fulcio_intermediate_pem: include_bytes!("../../../trust/fulcio_intermediate.pem")
                .to_vec(),
            rekor_logs: vec![TrustedRekorLog {
                log_id: Sha256::digest(&key_der).into(),
                valid_from: 1_610_452_407,
                valid_until: None,
                checkpoint_origin: "rekor.sigstore.dev",
                public_key: RekorPublicKey::EcdsaP256(key_der),
            }],
            timestamp_authority: production_tsa(),
        }
    }

    fn v2_trust() -> TrustConfig {
        const ORIGIN: &str = "log2025-alpha3.rekor.sigstage.dev";
        let key_der = pem_der(
            include_bytes!("../tests/fixtures/staging-rekor-v2.pub"),
            "PUBLIC KEY",
        );
        let key_bytes: [u8; 32] = key_der[12..].try_into().unwrap();
        let key = ed25519_dalek::VerifyingKey::from_bytes(&key_bytes).unwrap();
        let mut id_hasher = Sha256::new();
        id_hasher.update(ORIGIN.as_bytes());
        id_hasher.update(b"\n\x01");
        id_hasher.update(key.to_bytes());

        TrustConfig {
            identities: vec![TrustedIdentity {
                identity: "https://github.com/sigstore-conformance/extremely-dangerous-public-oidc-beacon/.github/workflows/extremely-dangerous-oidc-beacon.yml@refs/heads/main".into(),
                issuer: "https://token.actions.githubusercontent.com".into(),
            }],
            fulcio_root_pem: include_bytes!("../tests/fixtures/staging-fulcio-root.pem").to_vec(),
            fulcio_intermediate_pem: include_bytes!(
                "../tests/fixtures/staging-fulcio-intermediate.pem"
            )
            .to_vec(),
            rekor_logs: vec![TrustedRekorLog {
                log_id: id_hasher.finalize().into(),
                valid_from: 1_758_499_200,
                valid_until: None,
                checkpoint_origin: ORIGIN,
                public_key: RekorPublicKey::Ed25519(key.to_bytes()),
            }],
            timestamp_authority: TrustedTimestampAuthority {
                leaf_der: pem_der(
                    include_bytes!("../tests/fixtures/staging-tsa-leaf.pem"),
                    "CERTIFICATE",
                ),
                root_der: pem_der(
                    include_bytes!("../tests/fixtures/staging-tsa-root.pem"),
                    "CERTIFICATE",
                ),
                valid_from: 1_744_156_800,
                valid_until: None,
                policy_oid: "1.3.6.1.4.1.57264.2",
            },
        }
    }

    #[test]
    fn verifies_expired_fulcio_certificate_at_offline_rekor_time() {
        super::sig::verify_bundle(V1_BUNDLE, V1_MANIFEST_DIGEST, &v1_trust()).unwrap();
    }

    #[test]
    fn verifies_rekor_v2_with_rfc3161_timestamp() {
        super::sig::verify_bundle(V2_BUNDLE, V2_SUBJECT_DIGEST, &v2_trust()).unwrap();
    }

    #[test]
    fn rejects_tampered_inclusion_hash() {
        let mut bundle: serde_json::Value = serde_json::from_slice(V2_BUNDLE).unwrap();
        bundle["verificationMaterial"]["tlogEntries"][0]["inclusionProof"]["hashes"][0] =
            serde_json::Value::String(general_purpose::STANDARD.encode([0_u8; 32]));
        let tampered = serde_json::to_vec(&bundle).unwrap();
        assert!(super::sig::verify_bundle(&tampered, V2_SUBJECT_DIGEST, &v2_trust()).is_err());
    }
}
