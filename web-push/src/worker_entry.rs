//! Cloudflare Workers entry point (compiled only for `wasm32`).
//!
//! This is the thin glue between the Workers runtime and the transport-agnostic
//! [`crate::api`] logic: it reads configuration from the environment, backs
//! storage with Workers KV, and delivers pushes with the `fetch` API.
//!
//! Expected bindings (see `wrangler.toml`):
//! * KV namespace `SUBSCRIPTIONS`
//! * secret `VAPID_PRIVATE_KEY` (base64url 32-byte P-256 scalar)
//! * var `VAPID_SUBJECT` (a `mailto:`/`https:` contact; optional)

use async_trait::async_trait;
use worker::js_sys::Uint8Array;
use worker::kv::{KvError, KvStore};
use worker::{event, Context, Env, Fetch, Headers, Method, Request, RequestInit, Response};

use crate::api::{self, ApiConfig, ApiRequest};
use crate::push::WebPushClient;
use crate::sender::{PushResponse, PushSender, SenderError};
use crate::store::{StoreError, StoredSubscription, SubscriptionStore};
use crate::vapid::VapidKey;

const KV_BINDING: &str = "SUBSCRIPTIONS";
const KEY_PREFIX: &str = "sub:";
const DEFAULT_SUBJECT: &str = "mailto:admin@example.com";
const JWT_TTL_SECS: u64 = 12 * 60 * 60;
const DEFAULT_PUSH_TTL: u32 = 24 * 60 * 60;

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
        Ok(kv) => KvSubscriptionStore { kv },
        Err(_) => return json_error(500, "KV namespace 'SUBSCRIPTIONS' is not bound"),
    };
    let sender = WorkerSender;

    let body = req.bytes().await.unwrap_or_default();
    let api_request = ApiRequest {
        method: req.method().as_ref().to_string(),
        path: req.path(),
        body,
    };

    let now_unix = (worker::js_sys::Date::now() / 1000.0) as u64;
    let response = api::handle(api_request, &store, &sender, &config, now_unix).await;

    let headers = cors_headers();
    headers.set("Content-Type", &response.content_type)?;
    Ok(Response::from_bytes(response.body)?
        .with_status(response.status)
        .with_headers(headers))
}

/// Assemble the API configuration from environment bindings.
fn build_config(env: &Env) -> Result<ApiConfig, String> {
    let private_key = env
        .secret("VAPID_PRIVATE_KEY")
        .map(|s| s.to_string())
        .or_else(|_| env.var("VAPID_PRIVATE_KEY").map(|s| s.to_string()))
        .map_err(|_| "VAPID_PRIVATE_KEY is not configured".to_string())?;

    let vapid = VapidKey::from_base64url(private_key.trim())
        .map_err(|e| format!("invalid VAPID_PRIVATE_KEY: {e}"))?;

    let subject = env
        .var("VAPID_SUBJECT")
        .map(|s| s.to_string())
        .unwrap_or_else(|_| DEFAULT_SUBJECT.to_string());

    Ok(ApiConfig {
        client: WebPushClient::new(vapid, subject, JWT_TTL_SECS),
        default_ttl: DEFAULT_PUSH_TTL,
    })
}

/// CORS headers applied to every response (the API is meant to be called from a
/// browser front-end on a different origin).
///
/// worker >= 0.6: `Headers::set` takes `&self` (interior mutability).
fn cors_headers() -> Headers {
    let headers = Headers::new();
    let _ = headers.set("Access-Control-Allow-Origin", "*");
    let _ = headers.set("Access-Control-Allow-Methods", "GET, POST, OPTIONS");
    let _ = headers.set("Access-Control-Allow-Headers", "Content-Type");
    let _ = headers.set("Access-Control-Max-Age", "86400");
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

/// Workers KV-backed subscription store.
struct KvSubscriptionStore {
    kv: KvStore,
}

impl KvSubscriptionStore {
    fn key(id: &str) -> String {
        format!("{KEY_PREFIX}{id}")
    }
}

#[async_trait(?Send)]
impl SubscriptionStore for KvSubscriptionStore {
    async fn put(&self, sub: &StoredSubscription) -> Result<(), StoreError> {
        let value = serde_json::to_string(sub).map_err(|e| StoreError(e.to_string()))?;
        self.kv
            .put(&Self::key(&sub.id), value)
            .map_err(kv_err)?
            .execute()
            .await
            .map_err(kv_err)
    }

    async fn get(&self, id: &str) -> Result<Option<StoredSubscription>, StoreError> {
        let text = self.kv.get(&Self::key(id)).text().await.map_err(kv_err)?;
        match text {
            Some(text) => serde_json::from_str(&text)
                .map(Some)
                .map_err(|e| StoreError(e.to_string())),
            None => Ok(None),
        }
    }

    async fn delete(&self, id: &str) -> Result<(), StoreError> {
        self.kv.delete(&Self::key(id)).await.map_err(kv_err)
    }

    async fn list(&self) -> Result<Vec<StoredSubscription>, StoreError> {
        let mut out = Vec::new();
        let mut cursor: Option<String> = None;
        loop {
            let mut builder = self.kv.list().prefix(KEY_PREFIX.to_string());
            if let Some(c) = cursor.take() {
                builder = builder.cursor(c);
            }
            let response = builder.execute().await.map_err(kv_err)?;
            for key in response.keys {
                if let Some(text) = self.kv.get(&key.name).text().await.map_err(kv_err)? {
                    if let Ok(sub) = serde_json::from_str::<StoredSubscription>(&text) {
                        out.push(sub);
                    }
                }
            }
            if response.list_complete {
                break;
            }
            cursor = response.cursor;
            if cursor.is_none() {
                break;
            }
        }
        Ok(out)
    }
}

/// Delivers push requests using the Workers `fetch` API.
struct WorkerSender;

fn worker_err(e: worker::Error) -> SenderError {
    SenderError(e.to_string())
}

#[async_trait(?Send)]
impl PushSender for WorkerSender {
    async fn send(
        &self,
        request: &crate::push::WebPushRequest,
    ) -> Result<PushResponse, SenderError> {
        let headers = Headers::new();
        for (name, value) in &request.headers {
            headers.set(name, value).map_err(worker_err)?;
        }

        let array = Uint8Array::new_with_length(request.body.len() as u32);
        array.copy_from(&request.body);

        let mut init = RequestInit::new();
        init.with_method(Method::Post)
            .with_headers(headers)
            .with_body(Some(array.into()));

        let outbound = Request::new_with_init(&request.endpoint, &init).map_err(worker_err)?;
        let mut response = Fetch::Request(outbound).send().await.map_err(worker_err)?;
        let status = response.status_code();
        let body = response.text().await.ok();
        Ok(PushResponse { status, body })
    }
}
