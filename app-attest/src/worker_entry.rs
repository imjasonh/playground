//! Cloudflare Workers entry point (compiled only for `wasm32`).
//!
//! Thin glue: read env bindings, back storage with KV, and call [`crate::api`].

use async_trait::async_trait;
use worker::kv::{KvError, KvStore};
use worker::{event, Context, Env, Headers, Method, Request, Response};

use crate::api::{self, ApiConfig, ApiRequest};
use crate::certs;
use crate::store::{ChallengeRecord, ChallengeStore, DeviceRecord, DeviceStore, StoreError};

const KV_BINDING: &str = "STORE";
const CHALLENGE_PREFIX: &str = "challenge:";
const DEVICE_PREFIX: &str = "device:";
const DEFAULT_TOKEN_TTL: u64 = api::DEFAULT_TOKEN_TTL_SECONDS;

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

    let authorization = req.headers().get("Authorization").ok().flatten();
    let body = req.bytes().await.unwrap_or_default();
    let api_request = ApiRequest {
        method: req.method().as_ref().to_string(),
        path: req.path(),
        body,
        authorization,
    };

    let now_unix = (worker::js_sys::Date::now() / 1000.0) as u64;
    let response = api::handle(api_request, &store, &config, now_unix).await;

    let headers = cors_headers();
    headers.set("Content-Type", &response.content_type)?;
    Ok(Response::from_bytes(response.body)?
        .with_status(response.status)
        .with_headers(headers))
}

fn build_config(env: &Env) -> Result<ApiConfig, String> {
    let jwt_secret = env
        .secret("JWT_SECRET")
        .map(|s| s.to_string())
        .or_else(|_| env.var("JWT_SECRET").map(|s| s.to_string()))
        .map_err(|_| "JWT_SECRET is not configured".to_string())?;
    if jwt_secret.trim().is_empty() {
        return Err("JWT_SECRET is empty".into());
    }

    let app_id = env
        .var("APP_ID")
        .map(|v| v.to_string())
        .unwrap_or_else(|_| "XXXXXXXXXX.io.github.imjasonh.playground".into());

    let token_ttl_seconds = env
        .var("TOKEN_TTL_SECONDS")
        .ok()
        .and_then(|v| v.to_string().parse().ok())
        .filter(|n: &u64| *n > 0)
        .unwrap_or(DEFAULT_TOKEN_TTL);

    let allow_unattested = env
        .var("ALLOW_UNATTESTED")
        .map(|v| matches!(v.to_string().as_str(), "1" | "true" | "TRUE"))
        .unwrap_or(false);

    let root_certs = vec![certs::apple_root_der().map_err(|e| e.to_string())?];
    Ok(ApiConfig {
        app_id,
        jwt_secret,
        token_ttl_seconds,
        allow_unattested,
        root_certs,
    })
}

fn cors_headers() -> Headers {
    let headers = Headers::new();
    let _ = headers.set("Access-Control-Allow-Origin", "*");
    let _ = headers.set("Access-Control-Allow-Methods", "GET, POST, OPTIONS");
    let _ = headers.set(
        "Access-Control-Allow-Headers",
        "Authorization, Content-Type",
    );
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
