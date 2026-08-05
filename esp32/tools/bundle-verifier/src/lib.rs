//! Host test harness for the exact verifier source compiled into firmware.

pub mod trust {
    #[derive(Clone, Debug)]
    pub struct TrustedIdentity {
        pub identity: String,
        pub issuer: String,
    }

    #[derive(Clone)]
    pub struct TrustedRekorLog {
        pub log_id: [u8; 32],
        pub valid_from: u64,
        pub valid_until: Option<u64>,
        pub checkpoint_origin: &'static str,
        pub public_key: [u8; 32],
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
    use base64::{engine::general_purpose, Engine as _};
    use sha2::{Digest, Sha256};

    use super::trust::{TrustConfig, TrustedIdentity, TrustedRekorLog, TrustedTimestampAuthority};

    const V2_SUBJECT_DIGEST: &str =
        "a0cfc71271d6e278e57cd332ff957c3f7043fdda354c4cbb190a30d56efa01bf";
    const V2_BUNDLE: &[u8] = include_bytes!("../tests/fixtures/rekor-v2-bundle.json");

    fn pem_der(pem: &[u8], expected_label: &str) -> Vec<u8> {
        let (label, der) = x509_cert::der::pem::decode_vec(pem).unwrap();
        assert_eq!(label, expected_label);
        der
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
                public_key: key.to_bytes(),
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

    #[test]
    fn production_signing_config_matches_embedded_v2_key() {
        let config: serde_json::Value = serde_json::from_slice(include_bytes!(
            "../../../trust/signing-config-rekor-v2.json"
        ))
        .unwrap();
        let logs = config["rekorTlogUrls"].as_array().unwrap();
        assert_eq!(logs.len(), 1);
        assert_eq!(logs[0]["majorApiVersion"], 2);
        let origin = logs[0]["url"]
            .as_str()
            .unwrap()
            .strip_prefix("https://")
            .unwrap();

        let key_der = pem_der(include_bytes!("../../../trust/rekor-v2.pub"), "PUBLIC KEY");
        let key_bytes: [u8; 32] = key_der[12..].try_into().unwrap();
        let mut id_hasher = Sha256::new();
        id_hasher.update(origin.as_bytes());
        id_hasher.update(b"\n\x01");
        id_hasher.update(key_bytes);
        assert_eq!(
            hex::encode(id_hasher.finalize()),
            "cf1199155bddd051268d1f16ac5c0c75c009f6fb5a63f4177f8e18d7051e3fa0"
        );
    }
}
