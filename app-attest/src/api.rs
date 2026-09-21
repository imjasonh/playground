//! HTTP API, written against storage traits so it is testable without Workers.

use serde::Deserialize;
use serde_json::{json, Value};

use crate::assert::{self, VerifyInput as AssertionInput};
use crate::attest::{self, VerifyInput as AttestInput};
use crate::b64;
use crate::certs;
use crate::challenge;
use crate::client_data::{self, AssertionClientData, ClientData, WHOAMI_ACTION};
use crate::error::Error;
use crate::fraud::{self, FraudMetricClient, NoopFraudClient};
use crate::store::{AttestStore, DeviceRecord};

const UNATTESTED_KEY_PREFIX: &str = "unattested:";

/// Runtime configuration for the API.
pub struct ApiConfig {
    pub app_id: String,
    pub allow_unattested: bool,
    pub root_certs: Vec<Vec<u8>>,
    /// When set, `whoami` returns 403 if the stored Apple risk metric is above this.
    pub max_risk_metric: Option<u32>,
}

impl ApiConfig {
    pub fn production(app_id: String) -> Result<Self, Error> {
        Ok(Self {
            app_id,
            allow_unattested: false,
            root_certs: vec![certs::apple_root_der()?],
            max_risk_metric: None,
        })
    }
}

/// A transport-agnostic request handed to [`handle`].
#[derive(Debug, Clone)]
pub struct ApiRequest {
    pub method: String,
    pub path: String,
    pub body: Vec<u8>,
}

/// A transport-agnostic response produced by [`handle`].
#[derive(Debug, Clone)]
pub struct ApiResponse {
    pub status: u16,
    pub content_type: String,
    pub body: Vec<u8>,
}

impl ApiResponse {
    pub fn json(status: u16, value: Value) -> Self {
        Self {
            status,
            content_type: "application/json".into(),
            body: serde_json::to_vec(&value).unwrap_or_default(),
        }
    }

    pub fn error(err: Error) -> Self {
        Self::json(err.status(), json!({ "error": err.to_string() }))
    }
}

/// `clientData` is the exact JSON the iOS app hashed. A string keeps those
/// bytes intact. An object is accepted for tests and is re-serialized compactly.
#[derive(Debug, Deserialize)]
#[serde(untagged)]
enum ClientDataField {
    Raw(String),
    Object(Value),
}

impl ClientDataField {
    fn raw_bytes(&self) -> Result<Vec<u8>, Error> {
        match self {
            ClientDataField::Raw(s) => Ok(s.as_bytes().to_vec()),
            ClientDataField::Object(v) => serde_json::to_vec(v)
                .map_err(|_| Error::BadRequest("clientData is not JSON".into())),
        }
    }
}

#[derive(Debug, Deserialize)]
struct RegisterRequest {
    #[serde(rename = "keyId")]
    key_id: String,
    #[serde(rename = "attestationObject")]
    attestation_object: String,
    #[serde(rename = "clientData")]
    client_data: ClientDataField,
}

#[derive(Debug, Deserialize)]
struct UnattestedRequest {
    #[serde(rename = "clientData")]
    client_data: ClientDataField,
}

#[derive(Debug, Deserialize)]
struct WhoamiRequest {
    #[serde(rename = "keyId")]
    key_id: String,
    #[serde(rename = "assertionObject")]
    assertion_object: Option<String>,
    #[serde(rename = "clientData")]
    client_data: ClientDataField,
}

/// Strip an optional trailing slash and `/api` prefix.
fn normalize_path(path: &str) -> String {
    let trimmed = path.strip_suffix('/').unwrap_or(path);
    let without_prefix = trimmed.strip_prefix("/api").unwrap_or(trimmed);
    if without_prefix.is_empty() {
        "/".to_string()
    } else {
        without_prefix.to_string()
    }
}

/// Route and handle a single API request with no Apple fraud-metric client.
pub async fn handle(
    request: ApiRequest,
    store: &dyn AttestStore,
    config: &ApiConfig,
    now_unix: u64,
) -> ApiResponse {
    handle_with_fraud(request, store, config, &NoopFraudClient, now_unix).await
}

/// Route and handle a single API request.
pub async fn handle_with_fraud(
    request: ApiRequest,
    store: &dyn AttestStore,
    config: &ApiConfig,
    fraud: &dyn FraudMetricClient,
    now_unix: u64,
) -> ApiResponse {
    let path = normalize_path(&request.path);
    let result = match (request.method.as_str(), path.as_str()) {
        ("GET", "/") | ("GET", "/health") => Ok(health(config)),
        ("POST", "/v1/challenge") => issue_challenge(store, now_unix).await,
        ("POST", "/v1/token") => register(&request.body, store, config, fraud, now_unix).await,
        ("POST", "/v1/unattested-token") => {
            register_unattested(&request.body, store, config, now_unix).await
        }
        ("POST", "/v1/whoami") => whoami(&request.body, store, config, fraud, now_unix).await,
        ("GET", "/v1/whoami") => Ok(ApiResponse::json(
            405,
            json!({ "error": "whoami requires POST with a fresh assertion" }),
        )),
        _ => Ok(ApiResponse::json(404, json!({ "error": "not found" }))),
    };
    match result {
        Ok(response) => response,
        Err(err) => ApiResponse::error(err),
    }
}

fn health(config: &ApiConfig) -> ApiResponse {
    ApiResponse::json(
        200,
        json!({
            "service": "app-attest",
            "appId": config.app_id,
            "allowUnattested": config.allow_unattested,
        }),
    )
}

async fn issue_challenge(store: &dyn AttestStore, now_unix: u64) -> Result<ApiResponse, Error> {
    let (challenge, expires_at) = challenge::issue(store, now_unix).await?;
    Ok(ApiResponse::json(
        200,
        json!({ "challenge": challenge, "expiresAt": expires_at }),
    ))
}

async fn register(
    body: &[u8],
    store: &dyn AttestStore,
    config: &ApiConfig,
    fraud: &dyn FraudMetricClient,
    now_unix: u64,
) -> Result<ApiResponse, Error> {
    let req: RegisterRequest = serde_json::from_slice(body)
        .map_err(|_| Error::BadRequest("invalid token request".into()))?;
    let client_raw = req.client_data.raw_bytes()?;
    let client = ClientData::parse(&client_raw)?;
    challenge::consume(store, &client.challenge, now_unix).await?;

    let attestation = b64::decode(&req.attestation_object)?;
    let client_hash = client_data::hash(&client_raw);
    let verified = attest::verify(&AttestInput {
        app_id: &config.app_id,
        key_id: &req.key_id,
        attestation_object: &attestation,
        client_data_hash: &client_hash,
        roots: &config.root_certs,
        now_unix,
    })?;

    let receipt = if verified.receipt.len() > 1 {
        Some(b64::encode_std(&verified.receipt))
    } else {
        None
    };
    let mut record = DeviceRecord {
        key_id: req.key_id.clone(),
        user_id: client.user_id.clone(),
        device_id: client.device_id.clone(),
        public_key: b64::encode_std(&verified.public_key),
        counter: 0,
        created_at: now_unix,
        unattested: false,
        receipt,
        risk_metric: None,
        risk_metric_not_before: None,
        development: verified.development,
    };
    refresh_fraud(&mut record, store, fraud, now_unix).await;
    store
        .put_device(&record)
        .await
        .map_err(|e| Error::Store(e.0))?;
    Ok(registered_response(&record))
}

async fn register_unattested(
    body: &[u8],
    store: &dyn AttestStore,
    config: &ApiConfig,
    now_unix: u64,
) -> Result<ApiResponse, Error> {
    if !config.allow_unattested {
        return Err(Error::BadRequest(
            "unattested tokens are disabled on this worker".into(),
        ));
    }
    let req: UnattestedRequest = serde_json::from_slice(body)
        .map_err(|_| Error::BadRequest("invalid unattested request".into()))?;
    let client_raw = req.client_data.raw_bytes()?;
    let client = ClientData::parse(&client_raw)?;
    challenge::consume(store, &client.challenge, now_unix).await?;
    let record = DeviceRecord {
        key_id: format!("{UNATTESTED_KEY_PREFIX}{}", client.device_id),
        user_id: client.user_id.clone(),
        device_id: client.device_id.clone(),
        public_key: String::new(),
        counter: 0,
        created_at: now_unix,
        unattested: true,
        receipt: None,
        risk_metric: None,
        risk_metric_not_before: None,
        development: true,
    };
    store
        .put_device(&record)
        .await
        .map_err(|e| Error::Store(e.0))?;
    Ok(registered_response(&record))
}

async fn whoami(
    body: &[u8],
    store: &dyn AttestStore,
    config: &ApiConfig,
    fraud: &dyn FraudMetricClient,
    now_unix: u64,
) -> Result<ApiResponse, Error> {
    let req: WhoamiRequest = serde_json::from_slice(body)
        .map_err(|_| Error::BadRequest("invalid whoami request".into()))?;
    let client_raw = req.client_data.raw_bytes()?;
    let client = AssertionClientData::parse(&client_raw)?;
    client.require_action(WHOAMI_ACTION)?;
    challenge::consume(store, &client.challenge, now_unix).await?;

    let mut record = store
        .get_device(&req.key_id)
        .await
        .map_err(|e| Error::Store(e.0))?
        .ok_or(Error::Assertion("unknown key"))?;

    if record.unattested {
        if !config.allow_unattested {
            return Err(Error::BadRequest(
                "unattested tokens are disabled on this worker".into(),
            ));
        }
        return Ok(whoami_response(&record));
    }

    let assertion_b64 = req
        .assertion_object
        .as_deref()
        .ok_or(Error::BadRequest("assertionObject is required".into()))?;
    let assertion = b64::decode(assertion_b64)?;
    let public_key = b64::decode(&record.public_key)?;
    let client_hash = client_data::hash(&client_raw);
    let verified = assert::verify(&AssertionInput {
        app_id: &config.app_id,
        public_key: &public_key,
        assertion_object: &assertion,
        client_data_hash: &client_hash,
        previous_counter: record.counter,
    })?;
    record.counter = verified.counter;
    refresh_fraud(&mut record, store, fraud, now_unix).await;
    fraud::check_max_metric(&record, config.max_risk_metric)?;
    store
        .put_device(&record)
        .await
        .map_err(|e| Error::Store(e.0))?;
    Ok(whoami_response(&record))
}

async fn refresh_fraud(
    record: &mut DeviceRecord,
    store: &dyn AttestStore,
    fraud: &dyn FraudMetricClient,
    now_unix: u64,
) {
    if !fraud::ready_to_refresh(record, now_unix) {
        return;
    }
    let Some(receipt_b64) = record.receipt.clone() else {
        return;
    };
    let Ok(receipt) = b64::decode(&receipt_b64) else {
        return;
    };
    let result = fraud.refresh(&receipt, record.development, now_unix).await;
    if fraud::apply_refresh(record, &result) {
        let _ = store.put_device(record).await;
    }
}

fn registered_response(record: &DeviceRecord) -> ApiResponse {
    ApiResponse::json(200, device_json(record))
}

fn whoami_response(record: &DeviceRecord) -> ApiResponse {
    ApiResponse::json(200, device_json(record))
}

fn device_json(record: &DeviceRecord) -> Value {
    json!({
        "userId": record.user_id,
        "deviceId": record.device_id,
        "keyId": record.key_id,
        "unattested": record.unattested,
        "counter": record.counter,
        "riskMetric": record.risk_metric,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::InMemoryStore;

    fn config(allow_unattested: bool) -> ApiConfig {
        ApiConfig {
            app_id: "TEAMIDTEST.io.github.imjasonh.playground".into(),
            allow_unattested,
            root_certs: vec![certs::apple_root_der().unwrap()],
            max_risk_metric: None,
        }
    }

    fn req(method: &str, path: &str, body: &[u8]) -> ApiRequest {
        ApiRequest {
            method: method.into(),
            path: path.into(),
            body: body.to_vec(),
        }
    }

    #[test]
    fn challenge_then_unattested_whoami() {
        let store = InMemoryStore::new();
        let config = config(true);
        futures::executor::block_on(async {
            let issued = handle(req("POST", "/v1/challenge", b""), &store, &config, 10).await;
            assert_eq!(issued.status, 200);
            let issued_json: Value = serde_json::from_slice(&issued.body).unwrap();
            let challenge = issued_json["challenge"].as_str().unwrap();

            let body = json!({
                "clientData": {
                    "challenge": challenge,
                    "userId": "ada",
                    "deviceId": "iphone-1",
                }
            });
            let token_res = handle(
                req(
                    "POST",
                    "/v1/unattested-token",
                    &serde_json::to_vec(&body).unwrap(),
                ),
                &store,
                &config,
                11,
            )
            .await;
            assert_eq!(
                token_res.status,
                200,
                "{}",
                String::from_utf8_lossy(&token_res.body)
            );
            let token_json: Value = serde_json::from_slice(&token_res.body).unwrap();
            assert_eq!(token_json["keyId"], "unattested:iphone-1");
            assert!(token_json.get("token").is_none());

            let who_chal = handle(req("POST", "/v1/challenge", b""), &store, &config, 12).await;
            let who_chal_json: Value = serde_json::from_slice(&who_chal.body).unwrap();
            let who_challenge = who_chal_json["challenge"].as_str().unwrap();
            let who_body = json!({
                "keyId": "unattested:iphone-1",
                "clientData": {
                    "action": "whoami",
                    "challenge": who_challenge,
                }
            });
            let me = handle(
                req(
                    "POST",
                    "/v1/whoami",
                    &serde_json::to_vec(&who_body).unwrap(),
                ),
                &store,
                &config,
                13,
            )
            .await;
            assert_eq!(me.status, 200);
            let me_json: Value = serde_json::from_slice(&me.body).unwrap();
            assert_eq!(me_json["userId"], "ada");
            assert_eq!(me_json["deviceId"], "iphone-1");
            assert_eq!(me_json["unattested"], true);
        });
    }

    #[test]
    fn unattested_disabled() {
        let store = InMemoryStore::new();
        let config = config(false);
        futures::executor::block_on(async {
            let res = handle(
                req("POST", "/v1/unattested-token", br#"{"clientData":{}}"#),
                &store,
                &config,
                1,
            )
            .await;
            assert_eq!(res.status, 400);
        });
    }

    #[test]
    fn whoami_get_is_gone() {
        let store = InMemoryStore::new();
        let config = config(true);
        futures::executor::block_on(async {
            let res = handle(req("GET", "/v1/whoami", b""), &store, &config, 1).await;
            assert_eq!(res.status, 405);
        });
    }

    #[test]
    fn whoami_requires_registered_key() {
        let store = InMemoryStore::new();
        let config = config(true);
        futures::executor::block_on(async {
            let issued = handle(req("POST", "/v1/challenge", b""), &store, &config, 1).await;
            let issued_json: Value = serde_json::from_slice(&issued.body).unwrap();
            let challenge = issued_json["challenge"].as_str().unwrap();
            let body = json!({
                "keyId": "missing",
                "clientData": { "action": "whoami", "challenge": challenge }
            });
            let res = handle(
                req("POST", "/v1/whoami", &serde_json::to_vec(&body).unwrap()),
                &store,
                &config,
                2,
            )
            .await;
            assert_eq!(res.status, 401);
        });
    }
}
