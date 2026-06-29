//! End-to-end integration tests for the push backend.
//!
//! These drive the real API ([`web_push_worker::handle`]) over an in-memory
//! store and a recording sender — the same code paths the Worker uses — and
//! then act as the *user agent*: decrypting the captured push body with the
//! subscription's private key and verifying the VAPID JWT with the configured
//! public key. No network or deployment is involved.

use std::cell::RefCell;

use async_trait::async_trait;
use futures::executor::block_on;
use p256::ecdsa::signature::Verifier;
use p256::ecdsa::Signature;
use p256::SecretKey;
use rand_core::OsRng;
use serde_json::{json, Value};

use web_push_worker::{
    b64, ece, endpoint_origin, handle, ApiConfig, ApiRequest, ApiResponse, InMemoryStore,
    PushResponse, PushSender, SenderError, Subscription, VapidKey, WebPushClient, WebPushRequest,
};

/// A sender that records every request and returns a fixed status code.
struct RecordingSender {
    requests: RefCell<Vec<WebPushRequest>>,
    status: u16,
}

impl RecordingSender {
    fn new(status: u16) -> Self {
        Self {
            requests: RefCell::new(Vec::new()),
            status,
        }
    }
}

#[async_trait(?Send)]
impl PushSender for RecordingSender {
    async fn send(&self, request: &WebPushRequest) -> Result<PushResponse, SenderError> {
        self.requests.borrow_mut().push(request.clone());
        Ok(PushResponse {
            status: self.status,
            body: None,
        })
    }
}

const SUBJECT: &str = "mailto:test@example.com";

fn make_config() -> (ApiConfig, VapidKey) {
    let vapid = VapidKey::generate();
    let client = WebPushClient::new(vapid.clone(), SUBJECT, 12 * 60 * 60);
    (
        ApiConfig {
            client,
            default_ttl: 3600,
        },
        vapid,
    )
}

/// Build a subscription tied to a freshly generated user-agent key pair, and
/// return the private key + auth secret so the test can decrypt what it sends.
fn make_subscription(endpoint: &str) -> (Subscription, SecretKey, [u8; 16]) {
    let ua_secret = SecretKey::random(&mut OsRng);
    let p256dh = b64::encode(ece::public_key_bytes(&ua_secret.public_key()));
    let auth = [0x42u8; 16];
    let sub_json = json!({
        "endpoint": endpoint,
        "expirationTime": Value::Null,
        "keys": { "p256dh": p256dh, "auth": b64::encode(auth) },
    });
    let sub = Subscription::parse(sub_json.to_string().as_bytes()).unwrap();
    (sub, ua_secret, auth)
}

fn req(method: &str, path: &str, body: Vec<u8>) -> ApiRequest {
    ApiRequest {
        method: method.to_string(),
        path: path.to_string(),
        body,
    }
}

fn body_json(resp: &ApiResponse) -> Value {
    serde_json::from_slice(&resp.body).expect("response body is JSON")
}

/// Parse `vapid t=<jwt>, k=<key>`, verify the JWT signature against `vapid`'s
/// public key, and check the audience/subject claims.
fn verify_vapid_header(header: &str, endpoint: &str, vapid: &VapidKey) {
    let rest = header.strip_prefix("vapid ").expect("vapid scheme");
    let mut token = None;
    let mut key = None;
    for part in rest.split(',') {
        let part = part.trim();
        if let Some(v) = part.strip_prefix("t=") {
            token = Some(v.to_string());
        } else if let Some(v) = part.strip_prefix("k=") {
            key = Some(v.to_string());
        }
    }
    let token = token.expect("t= present");
    assert_eq!(key.as_deref(), Some(vapid.public_key_base64url().as_str()));

    let parts: Vec<&str> = token.split('.').collect();
    assert_eq!(parts.len(), 3, "JWT has three segments");
    let signing_input = format!("{}.{}", parts[0], parts[1]);
    let signature = Signature::from_slice(&b64::decode(parts[2]).unwrap()).unwrap();
    vapid
        .verifying_key()
        .verify(signing_input.as_bytes(), &signature)
        .expect("VAPID JWT must verify against the published key");

    let claims: Value = serde_json::from_slice(&b64::decode(parts[1]).unwrap()).unwrap();
    assert_eq!(claims["aud"], endpoint_origin(endpoint).unwrap());
    assert_eq!(claims["sub"], SUBJECT);
}

#[test]
fn end_to_end_subscribe_notify_and_decrypt() {
    block_on(async {
        let store = InMemoryStore::new();
        let sender = RecordingSender::new(201);
        let (config, vapid) = make_config();
        let endpoint = "https://push.example.com/sub/abc123";
        let (subscription, ua_secret, auth) = make_subscription(endpoint);

        // Subscribe.
        let resp = handle(
            req(
                "POST",
                "/subscribe",
                serde_json::to_vec(&subscription).unwrap(),
            ),
            &store,
            &sender,
            &config,
            1_000,
        )
        .await;
        assert_eq!(resp.status, 201);
        assert_eq!(store.len(), 1);

        // Broadcast a notification.
        let notify = json!({ "payload": { "title": "Hello", "body": "World" } });
        let resp = handle(
            req("POST", "/notify", notify.to_string().into_bytes()),
            &store,
            &sender,
            &config,
            1_000,
        )
        .await;
        assert_eq!(resp.status, 200);
        let summary = body_json(&resp);
        assert_eq!(summary["requested"], 1);
        assert_eq!(summary["succeeded"], 1);
        assert_eq!(summary["failed"], 0);

        // Inspect the single recorded push request.
        let requests = sender.requests.borrow();
        assert_eq!(requests.len(), 1);
        let push = &requests[0];
        assert_eq!(push.endpoint, endpoint);
        assert_eq!(push.header("Content-Encoding"), Some("aes128gcm"));
        assert_eq!(push.header("TTL"), Some("3600"));
        assert_eq!(
            push.header("Content-Type"),
            Some("application/octet-stream")
        );

        // Act as the user agent: decrypt with the subscription's private key.
        let plaintext = ece::decrypt(&ua_secret, &auth, &push.body).unwrap();
        let payload: Value = serde_json::from_slice(&plaintext).unwrap();
        assert_eq!(payload["title"], "Hello");
        assert_eq!(payload["body"], "World");

        // Verify the VAPID Authorization header end-to-end.
        verify_vapid_header(push.header("Authorization").unwrap(), endpoint, &vapid);
    });
}

#[test]
fn notify_with_options_sets_headers() {
    block_on(async {
        let store = InMemoryStore::new();
        let sender = RecordingSender::new(201);
        let (config, _) = make_config();
        let (subscription, _, _) = make_subscription("https://push.example.com/opts");
        handle(
            req(
                "POST",
                "/subscribe",
                serde_json::to_vec(&subscription).unwrap(),
            ),
            &store,
            &sender,
            &config,
            0,
        )
        .await;

        let notify = json!({
            "payload": { "msg": 1 },
            "ttl": 60,
            "urgency": "high",
            "topic": "news",
        });
        handle(
            req("POST", "/notify", notify.to_string().into_bytes()),
            &store,
            &sender,
            &config,
            0,
        )
        .await;

        let requests = sender.requests.borrow();
        let push = &requests[0];
        assert_eq!(push.header("TTL"), Some("60"));
        assert_eq!(push.header("Urgency"), Some("high"));
        assert_eq!(push.header("Topic"), Some("news"));
    });
}

#[test]
fn notify_prunes_gone_subscriptions() {
    block_on(async {
        let store = InMemoryStore::new();
        let sender = RecordingSender::new(410); // Gone
        let (config, _) = make_config();
        let (subscription, _, _) = make_subscription("https://push.example.com/gone");
        handle(
            req(
                "POST",
                "/subscribe",
                serde_json::to_vec(&subscription).unwrap(),
            ),
            &store,
            &sender,
            &config,
            0,
        )
        .await;
        assert_eq!(store.len(), 1);

        let notify = json!({ "payload": { "m": 1 } });
        let resp = handle(
            req("POST", "/notify", notify.to_string().into_bytes()),
            &store,
            &sender,
            &config,
            0,
        )
        .await;
        let summary = body_json(&resp);
        assert_eq!(summary["failed"], 1);
        assert_eq!(summary["results"][0]["removed"], true);
        assert_eq!(store.len(), 0, "410 Gone subscriptions are pruned");
    });
}

#[test]
fn lifecycle_subscribe_idempotent_and_unsubscribe() {
    block_on(async {
        let store = InMemoryStore::new();
        let sender = RecordingSender::new(201);
        let (config, vapid) = make_config();

        // VAPID public key endpoint.
        let resp = handle(
            req("GET", "/vapidPublicKey", vec![]),
            &store,
            &sender,
            &config,
            0,
        )
        .await;
        assert_eq!(resp.status, 200);
        assert_eq!(body_json(&resp)["publicKey"], vapid.public_key_base64url());

        // Subscribing twice with the same endpoint is idempotent.
        let endpoint = "https://push.example.com/dup";
        let (subscription, _, _) = make_subscription(endpoint);
        let body = serde_json::to_vec(&subscription).unwrap();
        let r1 = handle(
            req("POST", "/subscribe", body.clone()),
            &store,
            &sender,
            &config,
            0,
        )
        .await;
        let r2 = handle(req("POST", "/subscribe", body), &store, &sender, &config, 0).await;
        assert_eq!(body_json(&r1)["id"], body_json(&r2)["id"]);
        assert_eq!(store.len(), 1);

        // Health (with the `/api` prefix) reports the count.
        let resp = handle(
            req("GET", "/api/health", vec![]),
            &store,
            &sender,
            &config,
            0,
        )
        .await;
        let health = body_json(&resp);
        assert_eq!(health["status"], "ok");
        assert_eq!(health["subscriptions"], 1);

        // Unsubscribe by endpoint.
        let unsub = json!({ "endpoint": endpoint });
        let resp = handle(
            req("POST", "/unsubscribe", unsub.to_string().into_bytes()),
            &store,
            &sender,
            &config,
            0,
        )
        .await;
        assert_eq!(body_json(&resp)["removed"], true);
        assert_eq!(store.len(), 0);
    });
}

#[test]
fn rejects_invalid_subscription_and_bad_requests() {
    block_on(async {
        let store = InMemoryStore::new();
        let sender = RecordingSender::new(201);
        let (config, _) = make_config();

        // Invalid keys.
        let bad = json!({
            "endpoint": "https://push.example.com/x",
            "keys": { "p256dh": "AAAA", "auth": "AAAA" },
        });
        let resp = handle(
            req("POST", "/subscribe", bad.to_string().into_bytes()),
            &store,
            &sender,
            &config,
            0,
        )
        .await;
        assert_eq!(resp.status, 400);
        assert_eq!(store.len(), 0);

        // Unknown route.
        let resp = handle(req("GET", "/nope", vec![]), &store, &sender, &config, 0).await;
        assert_eq!(resp.status, 404);

        // Notify without a payload.
        let resp = handle(
            req("POST", "/notify", b"{}".to_vec()),
            &store,
            &sender,
            &config,
            0,
        )
        .await;
        assert_eq!(resp.status, 400);
    });
}
