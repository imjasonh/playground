//! HTTP API, written against storage traits so it is testable without Workers.

use serde::Deserialize;
use serde_json::{json, Value};

use crate::attest::{self, VerifyInput};
use crate::b64;
use crate::certs;
use crate::challenge;
use crate::client_data::{self, ClientData};
use crate::error::Error;
use crate::jwt::{self, Claims};
use crate::store::{AttestStore, DeviceRecord};

/// Default access-token lifetime.
pub const DEFAULT_TOKEN_TTL_SECONDS: u64 = 60 * 60;
const ISSUER: &str = "app-attest";
const UNATTESTED_KEY_ID: &str = "unattested";

/// Runtime configuration for the API.
pub struct ApiConfig {
    pub app_id: String,
    pub jwt_secret: String,
    pub token_ttl_seconds: u64,
    pub allow_unattested: bool,
    pub root_certs: Vec<Vec<u8>>,
}

impl ApiConfig {
    pub fn production(
        app_id: String,
        jwt_secret: String,
        token_ttl_seconds: u64,
    ) -> Result<Self, Error> {
        Ok(Self {
            app_id,
            jwt_secret,
            token_ttl_seconds,
            allow_unattested: false,
            root_certs: vec![certs::apple_root_der()?],
        })
    }
}

/// A transport-agnostic request handed to [`handle`].
#[derive(Debug, Clone)]
pub struct ApiRequest {
    pub method: String,
    pub path: String,
    pub body: Vec<u8>,
    /// Raw `Authorization` header, if present.
    pub authorization: Option<String>,
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
struct TokenRequest {
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

/// Route and handle a single API request.
pub async fn handle(
    request: ApiRequest,
    store: &dyn AttestStore,
    config: &ApiConfig,
    now_unix: u64,
) -> ApiResponse {
    let path = normalize_path(&request.path);
    let result = match (request.method.as_str(), path.as_str()) {
        ("GET", "/") | ("GET", "/health") => Ok(health(config)),
        ("POST", "/v1/challenge") => issue_challenge(store, now_unix).await,
        ("POST", "/v1/token") => exchange_token(&request.body, store, config, now_unix).await,
        ("POST", "/v1/unattested-token") => {
            unattested_token(&request.body, store, config, now_unix).await
        }
        ("GET", "/v1/whoami") => whoami(request.authorization.as_deref(), config, now_unix),
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

async fn exchange_token(
    body: &[u8],
    store: &dyn AttestStore,
    config: &ApiConfig,
    now_unix: u64,
) -> Result<ApiResponse, Error> {
    let req: TokenRequest = serde_json::from_slice(body)
        .map_err(|_| Error::BadRequest("invalid token request".into()))?;
    let client_raw = req.client_data.raw_bytes()?;
    let client = ClientData::parse(&client_raw)?;
    challenge::consume(store, &client.challenge, now_unix).await?;

    let attestation = b64::decode(&req.attestation_object)?;
    let client_hash = client_data::hash(&client_raw);
    let verified = attest::verify(&VerifyInput {
        app_id: &config.app_id,
        key_id: &req.key_id,
        attestation_object: &attestation,
        client_data_hash: &client_hash,
        roots: &config.root_certs,
        now_unix,
    })?;

    let record = DeviceRecord {
        key_id: req.key_id.clone(),
        user_id: client.user_id.clone(),
        device_id: client.device_id.clone(),
        public_key: b64::encode_std(&verified.public_key),
        counter: 0,
        created_at: now_unix,
    };
    store
        .put_device(&record)
        .await
        .map_err(|e| Error::Store(e.0))?;

    minted_token(
        config,
        &client.user_id,
        &client.device_id,
        &req.key_id,
        false,
        now_unix,
    )
}

async fn unattested_token(
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
    minted_token(
        config,
        &client.user_id,
        &client.device_id,
        UNATTESTED_KEY_ID,
        true,
        now_unix,
    )
}

fn minted_token(
    config: &ApiConfig,
    user_id: &str,
    device_id: &str,
    key_id: &str,
    unattested: bool,
    now_unix: u64,
) -> Result<ApiResponse, Error> {
    let exp = now_unix.saturating_add(config.token_ttl_seconds);
    let token = jwt::mint(
        &config.jwt_secret,
        &Claims {
            iss: ISSUER.into(),
            sub: user_id.to_string(),
            device_id: device_id.to_string(),
            key_id: key_id.to_string(),
            iat: now_unix,
            exp,
            unattested,
        },
    )?;
    Ok(ApiResponse::json(
        200,
        json!({
            "token": token,
            "expiresAt": exp,
            "userId": user_id,
            "deviceId": device_id,
            "keyId": key_id,
            "unattested": unattested,
        }),
    ))
}

fn whoami(
    authorization: Option<&str>,
    config: &ApiConfig,
    now_unix: u64,
) -> Result<ApiResponse, Error> {
    let token = bearer(authorization).ok_or(Error::Token("missing"))?;
    let claims = jwt::verify(&config.jwt_secret, token, now_unix)?;
    Ok(ApiResponse::json(
        200,
        json!({
            "userId": claims.sub,
            "deviceId": claims.device_id,
            "keyId": claims.key_id,
            "unattested": claims.unattested,
        }),
    ))
}

fn bearer(authorization: Option<&str>) -> Option<&str> {
    let raw = authorization?.trim();
    raw.strip_prefix("Bearer ")
        .or_else(|| raw.strip_prefix("bearer "))
        .map(str::trim)
        .filter(|s| !s.is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::InMemoryStore;

    fn config(allow_unattested: bool) -> ApiConfig {
        ApiConfig {
            app_id: "TEAMIDTEST.io.github.imjasonh.playground".into(),
            jwt_secret: "test-secret".into(),
            token_ttl_seconds: 60,
            allow_unattested,
            root_certs: vec![certs::apple_root_der().unwrap()],
        }
    }

    fn req(method: &str, path: &str, body: &[u8], authorization: Option<&str>) -> ApiRequest {
        ApiRequest {
            method: method.into(),
            path: path.into(),
            body: body.to_vec(),
            authorization: authorization.map(str::to_string),
        }
    }

    #[test]
    fn challenge_then_unattested_whoami() {
        let store = InMemoryStore::new();
        let config = config(true);
        futures::executor::block_on(async {
            let issued = handle(req("POST", "/v1/challenge", b"", None), &store, &config, 10).await;
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
                    None,
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
            let token = token_json["token"].as_str().unwrap();

            let me = handle(
                req("GET", "/v1/whoami", b"", Some(&format!("Bearer {token}"))),
                &store,
                &config,
                12,
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
                req(
                    "POST",
                    "/v1/unattested-token",
                    br#"{"clientData":{}}"#,
                    None,
                ),
                &store,
                &config,
                1,
            )
            .await;
            assert_eq!(res.status, 400);
        });
    }

    #[test]
    fn whoami_requires_token() {
        let store = InMemoryStore::new();
        let config = config(true);
        futures::executor::block_on(async {
            let res = handle(req("GET", "/v1/whoami", b"", None), &store, &config, 1).await;
            assert_eq!(res.status, 401);
        });
    }
}
