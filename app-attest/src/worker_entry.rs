//! Cloudflare Workers entry point (compiled only for `wasm32`).
//!
//! Thin glue: read env bindings, back storage with KV, and call [`crate::api`].

use async_trait::async_trait;
use js_sys::Uint8Array;
use worker::kv::{KvError, KvStore};
use worker::{event, Context, Env, Fetch, Headers, Method, Request, RequestInit, Response};

use crate::api::{self, ApiConfig, ApiRequest};
use crate::b64;
use crate::certs;
use crate::fraud::{self, FraudMetricClient, FraudRefreshResult, NoopFraudClient};
use crate::store::{ChallengeRecord, ChallengeStore, DeviceRecord, DeviceStore, StoreError};

const KV_BINDING: &str = "STORE";
const CHALLENGE_PREFIX: &str = "challenge:";
const DEVICE_PREFIX: &str = "device:";

#[event(fetch)]
async fn fetch(mut req: Request, env: Env, _ctx: Context) -> worker::Result<Response> {
    if req.method() == Method::Options {
        return Ok(Response::empty()?
            .with_status(204)
            .with_headers(cors_headers()));
    }

    let config = match build_config(&env) {
        Ok(config) => config,
        Err(message) => return json_error(500, &message),
    };
    let store = match env.kv(KV_BINDING) {
        Ok(kv) => KvAttestStore { kv },
        Err(_) => return json_error(500, "KV namespace 'STORE' is not bound"),
    };

    let body = req.bytes().await.unwrap_or_default();
    let api_request = ApiRequest {
        method: req.method().as_ref().to_string(),
        path: req.path(),
        body,
    };

    let now_unix = (worker::js_sys::Date::now() / 1000.0) as u64;
    let response = if let Some(apple) = apple_fraud_client(&env) {
        api::handle_with_fraud(api_request, &store, &config, &apple, now_unix).await
    } else {
        api::handle_with_fraud(api_request, &store, &config, &NoopFraudClient, now_unix).await
    };

    let headers = cors_headers();
    headers.set("Content-Type", &response.content_type)?;
    Ok(Response::from_bytes(response.body)?
        .with_status(response.status)
        .with_headers(headers))
}

fn build_config(env: &Env) -> Result<ApiConfig, String> {
    let app_id = env
        .var("APP_ID")
        .map(|v| v.to_string())
        .unwrap_or_else(|_| "W5LPA2QM2W.io.github.imjasonh.playground".into());

    let allow_unattested = env
        .var("ALLOW_UNATTESTED")
        .map(|v| matches!(v.to_string().as_str(), "1" | "true" | "TRUE"))
        .unwrap_or(false);

    let max_risk_metric = env
        .var("MAX_RISK_METRIC")
        .ok()
        .and_then(|v| v.to_string().parse().ok());

    let root_certs = vec![certs::apple_root_der().map_err(|e| e.to_string())?];
    Ok(ApiConfig {
        app_id,
        allow_unattested,
        root_certs,
        max_risk_metric,
    })
}

fn apple_fraud_client(env: &Env) -> Option<AppleFraudClient> {
    let key_id = env
        .secret("DEVICECHECK_KEY_ID")
        .or_else(|_| env.var("DEVICECHECK_KEY_ID"))
        .ok()?
        .to_string();
    let private_key = env
        .secret("DEVICECHECK_PRIVATE_KEY")
        .or_else(|_| env.var("DEVICECHECK_PRIVATE_KEY"))
        .ok()?
        .to_string();
    if key_id.trim().is_empty() || private_key.trim().is_empty() {
        return None;
    }
    let app_id = env
        .var("APP_ID")
        .map(|v| v.to_string())
        .unwrap_or_else(|_| "W5LPA2QM2W.io.github.imjasonh.playground".into());
    let team_id = fraud::team_id_from_app_id(&app_id)?.to_string();
    Some(AppleFraudClient {
        team_id,
        key_id,
        private_key,
    })
}

struct AppleFraudClient {
    team_id: String,
    key_id: String,
    private_key: String,
}

#[async_trait(?Send)]
impl FraudMetricClient for AppleFraudClient {
    async fn refresh(
        &self,
        receipt: &[u8],
        development: bool,
        now_unix: u64,
    ) -> FraudRefreshResult {
        let jwt =
            match fraud::device_check_jwt(&self.team_id, &self.key_id, &self.private_key, now_unix)
            {
                Ok(jwt) => jwt,
                Err(err) => return FraudRefreshResult::Failed(err.to_string()),
            };
        let url = fraud::apple_data_url(development);
        let headers = Headers::new();
        let _ = headers.set("Authorization", &format!("Bearer {jwt}"));
        let _ = headers.set("Content-Type", "text/plain");
        let mut init = RequestInit::new();
        init.with_method(Method::Post).with_headers(headers);
        let body = b64::encode_std(receipt);
        let array = Uint8Array::new_with_length(body.len() as u32);
        array.copy_from(body.as_bytes());
        init.with_body(Some(array.into()));
        let request = match Request::new_with_init(url, &init) {
            Ok(request) => request,
            Err(err) => return FraudRefreshResult::Failed(err.to_string()),
        };
        let mut response = match Fetch::Request(request).send().await {
            Ok(response) => response,
            Err(err) => return FraudRefreshResult::Failed(err.to_string()),
        };
        let status = response.status_code();
        if status == 304 {
            return FraudRefreshResult::NotModified;
        }
        let text = match response.text().await {
            Ok(text) => text,
            Err(err) => return FraudRefreshResult::Failed(err.to_string()),
        };
        if status != 200 {
            return FraudRefreshResult::Failed(format!("Apple HTTP {status}"));
        }
        match b64::decode(text.trim()) {
            Ok(bytes) => match fraud::parse_refreshed(&bytes) {
                Ok(updated) => FraudRefreshResult::Updated(updated),
                Err(err) => FraudRefreshResult::Failed(err.to_string()),
            },
            Err(_) => FraudRefreshResult::Failed("Apple receipt is not base64".into()),
        }
    }
}

fn cors_headers() -> Headers {
    let headers = Headers::new();
    let _ = headers.set("Access-Control-Allow-Origin", "*");
    let _ = headers.set("Access-Control-Allow-Methods", "GET, POST, OPTIONS");
    let _ = headers.set("Access-Control-Allow-Headers", "Content-Type");
    let _ = headers.set("Access-Control-Max-Age", "86400");
    let _ = headers.set("Cache-Control", "no-store");
    headers
}

fn json_error(status: u16, message: &str) -> worker::Result<Response> {
    let headers = cors_headers();
    headers.set("Content-Type", "application/json")?;
    let body = serde_json::json!({ "error": message })
        .to_string()
        .into_bytes();
    Ok(Response::from_bytes(body)?
        .with_status(status)
        .with_headers(headers))
}

fn kv_err(e: KvError) -> StoreError {
    StoreError(e.to_string())
}

struct KvAttestStore {
    kv: KvStore,
}

impl KvAttestStore {
    fn challenge_key(id: &str) -> String {
        format!("{CHALLENGE_PREFIX}{id}")
    }

    fn device_key(id: &str) -> String {
        format!("{DEVICE_PREFIX}{id}")
    }
}

#[async_trait(?Send)]
impl ChallengeStore for KvAttestStore {
    async fn put_challenge(&self, id: &str, record: &ChallengeRecord) -> Result<(), StoreError> {
        let value = serde_json::to_string(record).map_err(|e| StoreError(e.to_string()))?;
        let ttl = record.expires_at.saturating_sub(now_hint()).max(60);
        self.kv
            .put(&Self::challenge_key(id), value)
            .map_err(kv_err)?
            .expiration_ttl(ttl)
            .execute()
            .await
            .map_err(kv_err)
    }

    async fn take_challenge(&self, id: &str) -> Result<Option<ChallengeRecord>, StoreError> {
        let key = Self::challenge_key(id);
        let text = self.kv.get(&key).text().await.map_err(kv_err)?;
        self.kv.delete(&key).await.map_err(kv_err)?;
        match text {
            Some(text) => serde_json::from_str(&text)
                .map(Some)
                .map_err(|e| StoreError(e.to_string())),
            None => Ok(None),
        }
    }
}

#[async_trait(?Send)]
impl DeviceStore for KvAttestStore {
    async fn put_device(&self, record: &DeviceRecord) -> Result<(), StoreError> {
        let value = serde_json::to_string(record).map_err(|e| StoreError(e.to_string()))?;
        self.kv
            .put(&Self::device_key(&record.key_id), value)
            .map_err(kv_err)?
            .execute()
            .await
            .map_err(kv_err)
    }

    async fn get_device(&self, key_id: &str) -> Result<Option<DeviceRecord>, StoreError> {
        let text = self
            .kv
            .get(&Self::device_key(key_id))
            .text()
            .await
            .map_err(kv_err)?;
        match text {
            Some(text) => serde_json::from_str(&text)
                .map(Some)
                .map_err(|e| StoreError(e.to_string())),
            None => Ok(None),
        }
    }
}

/// KV TTL needs a relative second count. The Worker clock is fine here; a
/// slightly stale hint only changes when the row expires, not correctness.
fn now_hint() -> u64 {
    (worker::js_sys::Date::now() / 1000.0) as u64
}
