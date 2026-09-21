//! End-to-end attestation and assertion using a generated test CA.

use app_attest_worker::api::{self, ApiConfig, ApiRequest};
use app_attest_worker::assert;
use app_attest_worker::attest::{self, VerifyInput};
use app_attest_worker::b64;
use app_attest_worker::certs;
use app_attest_worker::client_data;
use app_attest_worker::fraud::{FraudRefreshResult, RefreshedReceipt, ScriptedFraudClient};
use app_attest_worker::receipt;
use app_attest_worker::store::{ChallengeStore, InMemoryStore};
use p256::ecdsa::signature::Signer;
use p256::ecdsa::{Signature, SigningKey};
use p256::pkcs8::DecodePrivateKey;
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
    leaf_key: KeyPair,
}

fn mint_fixture(user_id: &str, device_id: &str, challenge: &str) -> Fixture {
    mint_fixture_with_receipt(user_id, device_id, challenge, &[0])
}

fn mint_fixture_with_receipt(
    user_id: &str,
    device_id: &str,
    challenge: &str,
    receipt: &[u8],
) -> Fixture {
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

    let attestation = attest::encode_attestation_object_with_receipt(
        &auth_data,
        vec![leaf_cert.der().to_vec(), int_cert.der().to_vec()],
        receipt,
    );

    Fixture {
        roots: vec![root_cert.der().to_vec()],
        attestation,
        key_id: b64::encode_std(key_id_raw),
        client_raw,
        leaf_key,
    }
}

fn mint_assertion(leaf_key: &KeyPair, client_raw: &[u8], counter: u32) -> Vec<u8> {
    let signing = SigningKey::from_pkcs8_der(&leaf_key.serialize_der()).expect("leaf pkcs8");
    let hash = client_data::hash(client_raw);
    let auth = assert::encode_auth_data(APP_ID, counter);
    let mut msg = auth.clone();
    msg.extend_from_slice(&hash);
    let sig: Signature = signing.sign(&msg);
    assert::encode_assertion_object(&auth, sig.to_der().as_bytes())
}

fn config(roots: Vec<Vec<u8>>, max_risk_metric: Option<u32>) -> ApiConfig {
    ApiConfig {
        app_id: APP_ID.into(),
        allow_unattested: false,
        root_certs: roots,
        max_risk_metric,
    }
}

fn req(method: &str, path: &str, body: &[u8]) -> ApiRequest {
    ApiRequest {
        method: method.into(),
        path: path.into(),
        body: body.to_vec(),
    }
}

async fn seed_challenge(store: &InMemoryStore, challenge: &str, now: u64) {
    store
        .put_challenge(
            challenge,
            &app_attest_worker::store::ChallengeRecord {
                challenge: challenge.into(),
                expires_at: now + 60,
            },
        )
        .await
        .unwrap();
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
fn register_then_asserted_whoami() {
    let store = InMemoryStore::new();
    let challenge = "nOnceValue0000000000000000000001";
    let fixture = mint_fixture("ada", "iphone-1", challenge);
    let config = config(fixture.roots.clone(), None);

    futures::executor::block_on(async {
        seed_challenge(&store, challenge, NOW).await;

        let body = json!({
            "keyId": fixture.key_id,
            "attestationObject": b64::encode_url(&fixture.attestation),
            "clientData": String::from_utf8(fixture.client_raw.clone()).unwrap(),
        });
        let token_res = api::handle(
            req("POST", "/v1/token", &serde_json::to_vec(&body).unwrap()),
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
        assert!(token_json.get("token").is_none());
        assert_eq!(token_json["userId"], "ada");

        let who_challenge = "nOnceValue0000000000000000000002";
        seed_challenge(&store, who_challenge, NOW + 1).await;
        let who_client = serde_json::to_vec(&json!({
            "action": "whoami",
            "challenge": who_challenge,
        }))
        .unwrap();
        let assertion = mint_assertion(&fixture.leaf_key, &who_client, 1);
        let who_body = json!({
            "keyId": fixture.key_id,
            "assertionObject": b64::encode_url(&assertion),
            "clientData": String::from_utf8(who_client).unwrap(),
        });
        let me = api::handle(
            req(
                "POST",
                "/v1/whoami",
                &serde_json::to_vec(&who_body).unwrap(),
            ),
            &store,
            &config,
            NOW + 1,
        )
        .await;
        assert_eq!(me.status, 200, "{}", String::from_utf8_lossy(&me.body));
        let me_json: serde_json::Value = serde_json::from_slice(&me.body).unwrap();
        assert_eq!(me_json["userId"], "ada");
        assert_eq!(me_json["deviceId"], "iphone-1");
        assert_eq!(me_json["keyId"], fixture.key_id);
        assert_eq!(me_json["unattested"], false);
        assert_eq!(me_json["counter"], 1);
        assert_eq!(store.device(&fixture.key_id).unwrap().counter, 1);
    });
}

#[test]
fn replayed_assertion_fails() {
    let store = InMemoryStore::new();
    let challenge = "nOnceValue0000000000000000000001";
    let fixture = mint_fixture("ada", "iphone-1", challenge);
    let config = config(fixture.roots.clone(), None);

    futures::executor::block_on(async {
        seed_challenge(&store, challenge, NOW).await;
        let body = json!({
            "keyId": fixture.key_id,
            "attestationObject": b64::encode_url(&fixture.attestation),
            "clientData": String::from_utf8(fixture.client_raw.clone()).unwrap(),
        });
        let token_res = api::handle(
            req("POST", "/v1/token", &serde_json::to_vec(&body).unwrap()),
            &store,
            &config,
            NOW,
        )
        .await;
        assert_eq!(token_res.status, 200);

        let who_challenge = "nOnceValue0000000000000000000002";
        seed_challenge(&store, who_challenge, NOW + 1).await;
        let who_client = serde_json::to_vec(&json!({
            "action": "whoami",
            "challenge": who_challenge,
        }))
        .unwrap();
        let assertion = mint_assertion(&fixture.leaf_key, &who_client, 1);
        let who_body = json!({
            "keyId": fixture.key_id,
            "assertionObject": b64::encode_url(&assertion),
            "clientData": String::from_utf8(who_client.clone()).unwrap(),
        });
        let first = api::handle(
            req(
                "POST",
                "/v1/whoami",
                &serde_json::to_vec(&who_body).unwrap(),
            ),
            &store,
            &config,
            NOW + 1,
        )
        .await;
        assert_eq!(first.status, 200);

        let replay_challenge = "nOnceValue0000000000000000000003";
        seed_challenge(&store, replay_challenge, NOW + 2).await;
        // Same assertion bytes, new challenge in clientData would fail the signature.
        // Reuse the same counter by signing the new client data with counter 1.
        let replay_client = serde_json::to_vec(&json!({
            "action": "whoami",
            "challenge": replay_challenge,
        }))
        .unwrap();
        let replay_assertion = mint_assertion(&fixture.leaf_key, &replay_client, 1);
        let replay_body = json!({
            "keyId": fixture.key_id,
            "assertionObject": b64::encode_url(&replay_assertion),
            "clientData": String::from_utf8(replay_client).unwrap(),
        });
        let second = api::handle(
            req(
                "POST",
                "/v1/whoami",
                &serde_json::to_vec(&replay_body).unwrap(),
            ),
            &store,
            &config,
            NOW + 2,
        )
        .await;
        assert_eq!(second.status, 400);
        assert!(String::from_utf8_lossy(&second.body).contains("counter"));
    });
}

#[test]
fn fraud_metric_is_stored_and_can_reject() {
    let store = InMemoryStore::new();
    let challenge = "nOnceValue0000000000000000000001";
    let attest_receipt = receipt::encode_attribute_set(&[(6, b"ATTEST")]);
    let fixture = mint_fixture_with_receipt("ada", "iphone-1", challenge, &attest_receipt);
    let refreshed = receipt::encode_attribute_set(&[
        (6, b"RECEIPT"),
        (17, b"9"),
        (19, b"2020-07-22T14:40:38Z"),
    ]);
    let fraud = ScriptedFraudClient::new(vec![FraudRefreshResult::Updated(RefreshedReceipt {
        receipt: refreshed,
        risk_metric: 9,
        not_before_unix: Some(NOW + 3_600),
    })]);
    let mut config = config(fixture.roots.clone(), Some(3));

    futures::executor::block_on(async {
        seed_challenge(&store, challenge, NOW).await;
        let body = json!({
            "keyId": fixture.key_id,
            "attestationObject": b64::encode_url(&fixture.attestation),
            "clientData": String::from_utf8(fixture.client_raw.clone()).unwrap(),
        });
        let token_res = api::handle_with_fraud(
            req("POST", "/v1/token", &serde_json::to_vec(&body).unwrap()),
            &store,
            &config,
            &fraud,
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
        assert_eq!(token_json["riskMetric"], 9);

        let who_challenge = "nOnceValue0000000000000000000002";
        seed_challenge(&store, who_challenge, NOW + 1).await;
        let who_client = serde_json::to_vec(&json!({
            "action": "whoami",
            "challenge": who_challenge,
        }))
        .unwrap();
        let assertion = mint_assertion(&fixture.leaf_key, &who_client, 1);
        let who_body = json!({
            "keyId": fixture.key_id,
            "assertionObject": b64::encode_url(&assertion),
            "clientData": String::from_utf8(who_client).unwrap(),
        });
        let me = api::handle(
            req(
                "POST",
                "/v1/whoami",
                &serde_json::to_vec(&who_body).unwrap(),
            ),
            &store,
            &config,
            NOW + 1,
        )
        .await;
        assert_eq!(me.status, 403, "{}", String::from_utf8_lossy(&me.body));

        config.max_risk_metric = None;
        let who_challenge_2 = "nOnceValue0000000000000000000003";
        seed_challenge(&store, who_challenge_2, NOW + 2).await;
        let who_client_2 = serde_json::to_vec(&json!({
            "action": "whoami",
            "challenge": who_challenge_2,
        }))
        .unwrap();
        let assertion_2 = mint_assertion(&fixture.leaf_key, &who_client_2, 2);
        let who_body_2 = json!({
            "keyId": fixture.key_id,
            "assertionObject": b64::encode_url(&assertion_2),
            "clientData": String::from_utf8(who_client_2).unwrap(),
        });
        let me_ok = api::handle(
            req(
                "POST",
                "/v1/whoami",
                &serde_json::to_vec(&who_body_2).unwrap(),
            ),
            &store,
            &config,
            NOW + 2,
        )
        .await;
        assert_eq!(
            me_ok.status,
            200,
            "{}",
            String::from_utf8_lossy(&me_ok.body)
        );
        let me_json: serde_json::Value = serde_json::from_slice(&me_ok.body).unwrap();
        assert_eq!(me_json["riskMetric"], 9);
        assert_eq!(me_json["counter"], 2);
    });
}
