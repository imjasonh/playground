//! End-to-end attestation using a generated test CA (not Apple's root).

use app_attest_worker::api::{self, ApiConfig, ApiRequest};
use app_attest_worker::attest::{self, VerifyInput};
use app_attest_worker::b64;
use app_attest_worker::certs;
use app_attest_worker::client_data;
use app_attest_worker::store::{ChallengeStore, InMemoryStore};
use rcgen::{
    BasicConstraints, CertificateParams, CustomExtension, DistinguishedName, DnType, IsCa, KeyPair,
    KeyUsagePurpose, PKCS_ECDSA_P256_SHA256, PKCS_ECDSA_P384_SHA384,
};
use serde_json::json;
use sha2::{Digest, Sha256};
use x509_parser::prelude::*;

const APP_ID: &str = "TEAMIDTEST.io.github.imjasonh.playground";
const NOW: u64 = 1_700_000_100;

fn keypair() -> KeyPair {
    KeyPair::generate_for(&PKCS_ECDSA_P256_SHA256).expect("P-256 key")
}

fn cn_params(cn: &str, ca: bool) -> CertificateParams {
    let mut params = CertificateParams::new(Vec::<String>::new()).expect("params");
    params.distinguished_name = DistinguishedName::new();
    params.distinguished_name.push(DnType::CommonName, cn);
    if ca {
        params.is_ca = IsCa::Ca(BasicConstraints::Unconstrained);
        params.key_usages = vec![
            KeyUsagePurpose::KeyCertSign,
            KeyUsagePurpose::DigitalSignature,
        ];
    }
    params
}

fn public_key_bytes(key: &KeyPair) -> Vec<u8> {
    let der = key.public_key_der();
    let (_, spki) = SubjectPublicKeyInfo::from_der(&der).expect("spki");
    spki.subject_public_key.data.to_vec()
}

fn nonce_extension(nonce: &[u8; 32]) -> CustomExtension {
    let mut content = vec![0x30, 0x24, 0xa1, 0x22, 0x04, 0x20];
    content.extend_from_slice(nonce);
    CustomExtension::from_oid_content(&[1, 2, 840, 113635, 100, 8, 2], content)
}

struct Fixture {
    roots: Vec<Vec<u8>>,
    attestation: Vec<u8>,
    key_id: String,
    client_raw: Vec<u8>,
}

fn mint_fixture(user_id: &str, device_id: &str, challenge: &str) -> Fixture {
    let client_raw = serde_json::to_vec(&json!({
        "challenge": challenge,
        "userId": user_id,
        "deviceId": device_id,
    }))
    .unwrap();
    let client_hash = client_data::hash(&client_raw);

    let root_key = keypair();
    let root_params = cn_params("Test App Attest Root", true);
    let root_cert = root_params.self_signed(&root_key).expect("root");

    let int_key = keypair();
    let int_params = cn_params("Test App Attest Intermediate", true);
    let int_cert = int_params
        .signed_by(&int_key, &root_cert, &root_key)
        .expect("intermediate");

    let leaf_key = keypair();
    let public_key = public_key_bytes(&leaf_key);
    let key_id_raw = certs::key_id_bytes(&public_key);
    let auth_data = attest::encode_auth_data(APP_ID, &key_id_raw, true);

    let mut composite = auth_data.clone();
    composite.extend_from_slice(&client_hash);
    let nonce: [u8; 32] = Sha256::digest(&composite).into();

    let mut leaf_params = cn_params("credCert", false);
    leaf_params.custom_extensions = vec![nonce_extension(&nonce)];
    let leaf_cert = leaf_params
        .signed_by(&leaf_key, &int_cert, &int_key)
        .expect("leaf");

    let attestation = attest::encode_attestation_object(
        &auth_data,
        vec![leaf_cert.der().to_vec(), int_cert.der().to_vec()],
    );

    Fixture {
        roots: vec![root_cert.der().to_vec()],
        attestation,
        key_id: b64::encode_std(key_id_raw),
        client_raw,
    }
}

#[test]
fn p384_intermediate_chain_verifies() {
    let root_key = KeyPair::generate_for(&PKCS_ECDSA_P384_SHA384).expect("P-384 root");
    let root_params = cn_params("Test App Attest Root P384", true);
    let root_cert = root_params.self_signed(&root_key).expect("root");

    let int_key = KeyPair::generate_for(&PKCS_ECDSA_P384_SHA384).expect("P-384 intermediate");
    let int_params = cn_params("Test App Attest Intermediate P384", true);
    let int_cert = int_params
        .signed_by(&int_key, &root_cert, &root_key)
        .expect("intermediate");

    let leaf_key = keypair();
    let public_key = public_key_bytes(&leaf_key);
    let mut leaf_params = cn_params("credCert", false);
    leaf_params.custom_extensions = vec![nonce_extension(&[0xab; 32])];
    let leaf_cert = leaf_params
        .signed_by(&leaf_key, &int_cert, &int_key)
        .expect("leaf");

    let leaf = certs::verify_chain(
        &[leaf_cert.der().to_vec(), int_cert.der().to_vec()],
        &[root_cert.der().to_vec()],
        NOW,
    )
    .expect("P-384 CA chain should verify");
    assert_eq!(leaf.public_key, public_key);
}

#[test]
fn generated_chain_verifies() {
    let fixture = mint_fixture("ada", "iphone-1", "challenge-1");
    let hash = client_data::hash(&fixture.client_raw);
    attest::verify(&VerifyInput {
        app_id: APP_ID,
        key_id: &fixture.key_id,
        attestation_object: &fixture.attestation,
        client_data_hash: &hash,
        roots: &fixture.roots,
        now_unix: NOW,
    })
    .expect("fixture should verify");
}

#[test]
fn tampered_client_data_fails() {
    let fixture = mint_fixture("ada", "iphone-1", "challenge-1");
    let other = br#"{"challenge":"challenge-1","userId":"eve","deviceId":"iphone-1"}"#;
    let hash = client_data::hash(other);
    let err = attest::verify(&VerifyInput {
        app_id: APP_ID,
        key_id: &fixture.key_id,
        attestation_object: &fixture.attestation,
        client_data_hash: &hash,
        roots: &fixture.roots,
        now_unix: NOW,
    })
    .unwrap_err();
    assert!(err.to_string().contains("nonce"));
}

#[test]
fn token_exchange_then_whoami() {
    let store = InMemoryStore::new();
    let challenge = "nOnceValue0000000000000000000001";
    let fixture = mint_fixture("ada", "iphone-1", challenge);
    let config = ApiConfig {
        app_id: APP_ID.into(),
        jwt_secret: "fixture-secret".into(),
        token_ttl_seconds: 120,
        allow_unattested: false,
        root_certs: fixture.roots.clone(),
    };

    futures::executor::block_on(async {
        store
            .put_challenge(
                challenge,
                &app_attest_worker::store::ChallengeRecord {
                    challenge: challenge.into(),
                    expires_at: NOW + 60,
                },
            )
            .await
            .unwrap();

        let body = json!({
            "keyId": fixture.key_id,
            "attestationObject": b64::encode_url(&fixture.attestation),
            "clientData": String::from_utf8(fixture.client_raw.clone()).unwrap(),
        });
        let token_res = api::handle(
            ApiRequest {
                method: "POST".into(),
                path: "/v1/token".into(),
                body: serde_json::to_vec(&body).unwrap(),
                authorization: None,
            },
            &store,
            &config,
            NOW,
        )
        .await;
        assert_eq!(
            token_res.status,
            200,
            "{}",
            String::from_utf8_lossy(&token_res.body)
        );
        let token_json: serde_json::Value = serde_json::from_slice(&token_res.body).unwrap();
        let token = token_json["token"].as_str().unwrap();

        let me = api::handle(
            ApiRequest {
                method: "GET".into(),
                path: "/v1/whoami".into(),
                body: Vec::new(),
                authorization: Some(format!("Bearer {token}")),
            },
            &store,
            &config,
            NOW + 1,
        )
        .await;
        assert_eq!(me.status, 200);
        let me_json: serde_json::Value = serde_json::from_slice(&me.body).unwrap();
        assert_eq!(me_json["userId"], "ada");
        assert_eq!(me_json["deviceId"], "iphone-1");
        assert_eq!(me_json["keyId"], fixture.key_id);
        assert_eq!(me_json["unattested"], false);
        assert_eq!(store.device_count(), 1);
    });
}
