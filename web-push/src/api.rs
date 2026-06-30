//! The HTTP API for the push backend, written against the storage and sender
//! traits so it is fully testable without the Workers runtime.
//!
//! Routes (an optional `/api` prefix and trailing slash are accepted):
//!
//! | Method | Path               | Purpose                                   |
//! |--------|--------------------|-------------------------------------------|
//! | GET    | `/health`          | Liveness + subscription count             |
//! | GET    | `/vapidPublicKey`  | VAPID public key for `applicationServerKey` |
//! | POST   | `/subscribe`       | Store a `PushSubscription`                |
//! | POST   | `/unsubscribe`     | Remove a subscription by id or endpoint   |
//! | GET    | `/subscriptions`   | List stored subscriptions                 |
//! | POST   | `/notify`          | Encrypt + send to one or all subscriptions |

use serde::Deserialize;
use serde_json::{json, Value};

use crate::push::{Urgency, WebPushClient, WebPushMessage};
use crate::sender::PushSender;
use crate::store::{StoredSubscription, SubscriptionStore};
use crate::subscription::{id_for_endpoint, Subscription};

/// Runtime configuration for the API.
pub struct ApiConfig {
    /// The push client (VAPID identity + encryption).
    pub client: WebPushClient,
    /// Default push TTL (seconds) when a notify request omits one.
    pub default_ttl: u32,
}

/// A transport-agnostic request handed to [`handle`].
#[derive(Debug, Clone)]
pub struct ApiRequest {
    /// Uppercase HTTP method.
    pub method: String,
    /// Request path (query string already stripped).
    pub path: String,
    /// Raw request body.
    pub body: Vec<u8>,
}

/// A transport-agnostic response produced by [`handle`].
#[derive(Debug, Clone)]
pub struct ApiResponse {
    /// HTTP status code.
    pub status: u16,
    /// `Content-Type` for the body.
    pub content_type: String,
    /// Serialized response body.
    pub body: Vec<u8>,
}

impl ApiResponse {
    /// A JSON response.
    pub fn json(status: u16, value: Value) -> Self {
        Self {
            status,
            content_type: "application/json".to_string(),
            body: serde_json::to_vec(&value).unwrap_or_default(),
        }
    }

    /// A JSON `{ "error": ... }` response.
    pub fn error(status: u16, message: impl Into<String>) -> Self {
        Self::json(status, json!({ "error": message.into() }))
    }
}

/// Strip an optional trailing slash and `/api` prefix so routes can be matched
/// whether the worker is mounted at `/` or behind `/api`.
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
    store: &dyn SubscriptionStore,
    sender: &dyn PushSender,
    config: &ApiConfig,
    now_unix: u64,
) -> ApiResponse {
    let path = normalize_path(&request.path);
    match (request.method.as_str(), path.as_str()) {
        ("GET", "/") | ("GET", "/health") => health(store, config).await,
        ("GET", "/vapidPublicKey") => ApiResponse::json(
            200,
            json!({ "publicKey": config.client.vapid_public_key() }),
        ),
        ("POST", "/subscribe") => subscribe(&request.body, store, now_unix).await,
        ("POST", "/unsubscribe") => unsubscribe(&request.body, store).await,
        ("GET", "/subscriptions") => list_subscriptions(store).await,
        ("POST", "/notify") => notify(&request.body, store, sender, config, now_unix).await,
        _ => ApiResponse::error(404, "not found"),
    }
}

async fn health(store: &dyn SubscriptionStore, config: &ApiConfig) -> ApiResponse {
    let count = store.list().await.map(|v| v.len()).unwrap_or(0);
    ApiResponse::json(
        200,
        json!({
            "status": "ok",
            "subscriptions": count,
            "vapidPublicKey": config.client.vapid_public_key(),
        }),
    )
}

async fn subscribe(body: &[u8], store: &dyn SubscriptionStore, now_unix: u64) -> ApiResponse {
    let subscription = match Subscription::parse(body) {
        Ok(sub) => sub,
        Err(e) => return ApiResponse::error(400, e.to_string()),
    };
    if let Err(e) = subscription.validate() {
        return ApiResponse::error(400, e.to_string());
    }

    let stored = StoredSubscription::new(subscription, now_unix);
    let id = stored.id.clone();
    match store.put(&stored).await {
        Ok(()) => ApiResponse::json(201, json!({ "id": id })),
        Err(e) => ApiResponse::error(500, e.to_string()),
    }
}

#[derive(Deserialize)]
struct UnsubscribeRequest {
    #[serde(default)]
    id: Option<String>,
    #[serde(default)]
    endpoint: Option<String>,
}

async fn unsubscribe(body: &[u8], store: &dyn SubscriptionStore) -> ApiResponse {
    let request: UnsubscribeRequest = match serde_json::from_slice(body) {
        Ok(r) => r,
        Err(e) => return ApiResponse::error(400, format!("invalid request JSON: {e}")),
    };
    let id = request
        .id
        .or_else(|| request.endpoint.as_deref().map(id_for_endpoint));
    let Some(id) = id else {
        return ApiResponse::error(400, "id or endpoint is required");
    };

    let existed = matches!(store.get(&id).await, Ok(Some(_)));
    if let Err(e) = store.delete(&id).await {
        return ApiResponse::error(500, e.to_string());
    }
    ApiResponse::json(200, json!({ "removed": existed, "id": id }))
}

async fn list_subscriptions(store: &dyn SubscriptionStore) -> ApiResponse {
    match store.list().await {
        Ok(subs) => {
            let items: Vec<Value> = subs
                .iter()
                .map(|s| {
                    json!({
                        "id": s.id,
                        "endpoint": s.subscription.endpoint,
                        "createdAt": s.created_at,
                    })
                })
                .collect();
            ApiResponse::json(200, json!({ "count": items.len(), "subscriptions": items }))
        }
        Err(e) => ApiResponse::error(500, e.to_string()),
    }
}

#[derive(Deserialize)]
struct NotifyRequest {
    /// Arbitrary JSON delivered (encrypted) to the service worker.
    payload: Value,
    #[serde(default)]
    ttl: Option<u32>,
    #[serde(default)]
    urgency: Option<String>,
    #[serde(default)]
    topic: Option<String>,
    /// Target a single subscription; if absent, broadcast to all.
    #[serde(default)]
    id: Option<String>,
}

async fn notify(
    body: &[u8],
    store: &dyn SubscriptionStore,
    sender: &dyn PushSender,
    config: &ApiConfig,
    now_unix: u64,
) -> ApiResponse {
    let request: NotifyRequest = match serde_json::from_slice(body) {
        Ok(r) => r,
        Err(e) => return ApiResponse::error(400, format!("invalid notify JSON: {e}")),
    };
    if request.payload.is_null() {
        return ApiResponse::error(400, "payload is required");
    }
    let payload = serde_json::to_vec(&request.payload).unwrap_or_default();

    let ttl = request.ttl.unwrap_or(config.default_ttl);
    let urgency = match request.urgency.as_deref() {
        Some(u) => match Urgency::parse(u) {
            Some(parsed) => Some(parsed),
            None => return ApiResponse::error(400, "invalid urgency"),
        },
        None => None,
    };

    let targets = match &request.id {
        Some(id) => match store.get(id).await {
            Ok(Some(sub)) => vec![sub],
            Ok(None) => return ApiResponse::error(404, "subscription not found"),
            Err(e) => return ApiResponse::error(500, e.to_string()),
        },
        None => match store.list().await {
            Ok(subs) => subs,
            Err(e) => return ApiResponse::error(500, e.to_string()),
        },
    };

    let mut results = Vec::with_capacity(targets.len());
    let mut succeeded = 0usize;
    let mut failed = 0usize;

    for stored in &targets {
        let message = WebPushMessage {
            payload: payload.clone(),
            ttl,
            urgency,
            topic: request.topic.clone(),
        };

        let push_request =
            match config
                .client
                .build_request(&stored.subscription, &message, now_unix)
            {
                Ok(req) => req,
                Err(e) => {
                    failed += 1;
                    results.push(json!({
                        "id": stored.id,
                        "endpoint": stored.subscription.endpoint,
                        "ok": false,
                        "error": e.to_string(),
                    }));
                    continue;
                }
            };

        match sender.send(&push_request).await {
            Ok(response) => {
                let ok = response.is_success();
                if ok {
                    succeeded += 1;
                } else {
                    failed += 1;
                }
                let mut removed = false;
                if response.is_gone() {
                    let _ = store.delete(&stored.id).await;
                    removed = true;
                }
                results.push(json!({
                    "id": stored.id,
                    "endpoint": stored.subscription.endpoint,
                    "status": response.status,
                    "ok": ok,
                    "removed": removed,
                }));
            }
            Err(e) => {
                failed += 1;
                results.push(json!({
                    "id": stored.id,
                    "endpoint": stored.subscription.endpoint,
                    "ok": false,
                    "error": e.to_string(),
                }));
            }
        }
    }

    ApiResponse::json(
        200,
        json!({
            "requested": targets.len(),
            "succeeded": succeeded,
            "failed": failed,
            "results": results,
        }),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalize_path_handles_prefix_and_slash() {
        assert_eq!(normalize_path("/api/subscribe"), "/subscribe");
        assert_eq!(normalize_path("/api/subscribe/"), "/subscribe");
        assert_eq!(normalize_path("/subscribe"), "/subscribe");
        assert_eq!(normalize_path("/api"), "/");
        assert_eq!(normalize_path("/api/"), "/");
        assert_eq!(normalize_path("/"), "/");
    }
}
