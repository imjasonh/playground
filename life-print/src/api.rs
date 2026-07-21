//! HTTP API for quoting STLs, written against [`StlStore`] + [`SlantClient`]
//! so it is fully testable without the Workers runtime.
//!
//! | Method | Path | Purpose |
//! |--------|------|---------|
//! | `GET` | `/` or `/health` | Liveness + whether `SLANT_API_KEY` is configured |
//! | `POST` | `/quote` | Upload binary STL → `{ price, currency, triangles, id }` |
//! | `GET` | `/files/{id}` | Serve a parked STL (public; Slant fetches this) |

use serde_json::{json, Value};

use crate::slant::{SlantClient, SlantError};
use crate::stl::validate_binary_stl;
use crate::store::{new_file_id, StlStore};

/// Default max inbound STL size (15 MiB).
pub const DEFAULT_MAX_STL_BYTES: usize = 15 * 1024 * 1024;

/// Runtime configuration for the API.
#[derive(Debug, Clone)]
pub struct ApiConfig {
    /// Public base URL of *this* Worker (no trailing slash), used to build the
    /// `fileURL` Slant will fetch. Derived from the inbound request in
    /// production.
    pub public_base: String,
    /// True when a Slant API key is configured. Quote fails with 503 otherwise.
    pub slant_configured: bool,
    /// Reject STL bodies larger than this.
    pub max_stl_bytes: usize,
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
    pub status: u16,
    pub content_type: String,
    pub body: Vec<u8>,
    /// Optional filename hint for `Content-Disposition` (file downloads).
    pub content_disposition: Option<String>,
}

impl ApiResponse {
    pub fn json(status: u16, value: Value) -> Self {
        Self {
            status,
            content_type: "application/json".into(),
            body: serde_json::to_vec(&value).unwrap_or_default(),
            content_disposition: None,
        }
    }

    pub fn error(status: u16, message: impl Into<String>) -> Self {
        Self::json(status, json!({ "error": message.into() }))
    }

    pub fn bytes(status: u16, content_type: &str, body: Vec<u8>) -> Self {
        Self {
            status,
            content_type: content_type.into(),
            body,
            content_disposition: None,
        }
    }
}

/// Strip an optional trailing slash and `/api` prefix.
fn normalize_path(path: &str) -> String {
    let trimmed = path.strip_suffix('/').unwrap_or(path);
    let without_prefix = trimmed.strip_prefix("/api").unwrap_or(trimmed);
    if without_prefix.is_empty() {
        "/".into()
    } else {
        without_prefix.into()
    }
}

/// Route and handle a single API request.
pub async fn handle(
    request: ApiRequest,
    store: &dyn StlStore,
    slant: &dyn SlantClient,
    config: &ApiConfig,
) -> ApiResponse {
    let path = normalize_path(&request.path);
    match (request.method.as_str(), path.as_str()) {
        ("GET", "/") | ("GET", "/health") => health(config),
        ("POST", "/quote") => quote(&request.body, store, slant, config).await,
        (method, path) if method == "GET" && path.starts_with("/files/") => {
            let id = &path["/files/".len()..];
            get_file(id, store).await
        }
        _ => ApiResponse::error(404, "not found"),
    }
}

fn health(config: &ApiConfig) -> ApiResponse {
    ApiResponse::json(
        200,
        json!({
            "ok": true,
            "service": "life-print",
            "slantConfigured": config.slant_configured,
            "maxStlBytes": config.max_stl_bytes,
            "usage": {
                "quote": "POST /quote with a binary STL body (Content-Type: model/stl or application/octet-stream)",
                "file": "GET /files/{id} — temporary public URL used by Slant during quoting",
            }
        }),
    )
}

async fn quote(
    body: &[u8],
    store: &dyn StlStore,
    slant: &dyn SlantClient,
    config: &ApiConfig,
) -> ApiResponse {
    if !config.slant_configured {
        return ApiResponse::error(
            503,
            "SLANT_API_KEY is not configured on this Worker (wrangler secret put SLANT_API_KEY)",
        );
    }
    if body.is_empty() {
        return ApiResponse::error(400, "empty body; expected a binary STL");
    }
    if body.len() > config.max_stl_bytes {
        return ApiResponse::error(
            413,
            format!("STL exceeds max size of {} bytes", config.max_stl_bytes),
        );
    }

    let triangles = match validate_binary_stl(body) {
        Ok(n) => n,
        Err(e) => return ApiResponse::error(400, e.message()),
    };

    let id = match new_file_id() {
        Ok(id) => id,
        Err(e) => return ApiResponse::error(500, format!("id generation failed: {e}")),
    };

    if let Err(e) = store.put(&id, body.to_vec()).await {
        return ApiResponse::error(500, format!("failed to store STL: {e}"));
    }

    let file_url = format!("{}/files/{}", config.public_base.trim_end_matches('/'), id);

    let quote = match slant.slice(&file_url).await {
        Ok(q) => q,
        Err(e) => {
            let _ = store.delete(&id).await;
            return slant_error_response(e);
        }
    };

    // Slant fetches the file synchronously during /api/slicer, so the blob can
    // go away immediately. Best-effort — a leftover object is harmless.
    let _ = store.delete(&id).await;

    ApiResponse::json(
        200,
        json!({
            "price": quote.price,
            "currency": "USD",
            "triangles": triangles,
            "id": id,
            "message": quote.message,
            "provider": "slant3d",
        }),
    )
}

fn slant_error_response(err: SlantError) -> ApiResponse {
    match err {
        SlantError::Status { status, body } => {
            let upstream = status;
            // Surface 4xx from Slant as 502 with detail; 5xx likewise.
            let detail = if body.len() > 500 {
                format!("{}…", &body[..500])
            } else {
                body
            };
            ApiResponse::json(
                502,
                json!({
                    "error": format!("slant returned HTTP {upstream}"),
                    "upstreamStatus": upstream,
                    "upstreamBody": detail,
                }),
            )
        }
        other => ApiResponse::error(502, other.to_string()),
    }
}

async fn get_file(id: &str, store: &dyn StlStore) -> ApiResponse {
    if id.is_empty() || !id.chars().all(|c| c.is_ascii_hexdigit()) || id.len() > 64 {
        return ApiResponse::error(400, "invalid file id");
    }
    match store.get(id).await {
        Ok(Some(bytes)) => {
            let mut resp = ApiResponse::bytes(200, "model/stl", bytes);
            resp.content_disposition = Some(format!("attachment; filename=\"{id}.stl\""));
            resp
        }
        Ok(None) => ApiResponse::error(404, "file not found"),
        Err(e) => ApiResponse::error(500, format!("store error: {e}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::slant::{MockSlant, SlantError};
    use crate::store::InMemoryStore;
    use futures::executor::block_on;

    fn binary_stl(triangles: u32) -> Vec<u8> {
        let mut out = vec![0u8; 80];
        out.extend_from_slice(&triangles.to_le_bytes());
        out.resize(84 + (triangles as usize) * 50, 0);
        out
    }

    fn cfg() -> ApiConfig {
        ApiConfig {
            public_base: "https://life-print.example.workers.dev".into(),
            slant_configured: true,
            max_stl_bytes: DEFAULT_MAX_STL_BYTES,
        }
    }

    #[test]
    fn health_reports_configuration() {
        block_on(async {
            let store = InMemoryStore::new();
            let slant = MockSlant::with_price(1.0);
            let mut config = cfg();
            config.slant_configured = false;
            let resp = handle(
                ApiRequest {
                    method: "GET".into(),
                    path: "/health".into(),
                    body: vec![],
                },
                &store,
                &slant,
                &config,
            )
            .await;
            assert_eq!(resp.status, 200);
            let v: Value = serde_json::from_slice(&resp.body).unwrap();
            assert_eq!(v["ok"], true);
            assert_eq!(v["slantConfigured"], false);
        });
    }

    #[test]
    fn quote_returns_price_and_cleans_up() {
        block_on(async {
            let store = InMemoryStore::new();
            let slant = MockSlant::with_price(5.2);
            let stl = binary_stl(2);
            let resp = handle(
                ApiRequest {
                    method: "POST".into(),
                    path: "/quote".into(),
                    body: stl,
                },
                &store,
                &slant,
                &cfg(),
            )
            .await;
            assert_eq!(resp.status, 200);
            let v: Value = serde_json::from_slice(&resp.body).unwrap();
            assert_eq!(v["price"], 5.2);
            assert_eq!(v["currency"], "USD");
            assert_eq!(v["triangles"], 2);
            assert_eq!(v["provider"], "slant3d");
            assert!(store.is_empty(), "blob should be deleted after quote");
            let urls = slant.urls();
            assert_eq!(urls.len(), 1);
            assert!(urls[0].starts_with("https://life-print.example.workers.dev/files/"));
        });
    }

    #[test]
    fn quote_requires_api_key() {
        block_on(async {
            let store = InMemoryStore::new();
            let slant = MockSlant::with_price(1.0);
            let mut config = cfg();
            config.slant_configured = false;
            let resp = handle(
                ApiRequest {
                    method: "POST".into(),
                    path: "/quote".into(),
                    body: binary_stl(1),
                },
                &store,
                &slant,
                &config,
            )
            .await;
            assert_eq!(resp.status, 503);
        });
    }

    #[test]
    fn quote_rejects_bad_stl() {
        block_on(async {
            let store = InMemoryStore::new();
            let slant = MockSlant::with_price(1.0);
            let resp = handle(
                ApiRequest {
                    method: "POST".into(),
                    path: "/quote".into(),
                    body: b"not an stl".to_vec(),
                },
                &store,
                &slant,
                &cfg(),
            )
            .await;
            assert_eq!(resp.status, 400);
        });
    }

    #[test]
    fn quote_maps_slant_failure() {
        block_on(async {
            let store = InMemoryStore::new();
            let slant = MockSlant::with_price(1.0);
            slant.fail_next(SlantError::Status {
                status: 400,
                body: "bad mesh".into(),
            });
            let resp = handle(
                ApiRequest {
                    method: "POST".into(),
                    path: "/quote".into(),
                    body: binary_stl(1),
                },
                &store,
                &slant,
                &cfg(),
            )
            .await;
            assert_eq!(resp.status, 502);
            assert!(store.is_empty());
        });
    }

    #[test]
    fn serves_and_404s_files() {
        block_on(async {
            let store = InMemoryStore::new();
            let slant = MockSlant::with_price(1.0);
            store.put("abcd", binary_stl(1)).await.unwrap();
            let ok = handle(
                ApiRequest {
                    method: "GET".into(),
                    path: "/files/abcd".into(),
                    body: vec![],
                },
                &store,
                &slant,
                &cfg(),
            )
            .await;
            assert_eq!(ok.status, 200);
            assert_eq!(ok.content_type, "model/stl");

            let missing = handle(
                ApiRequest {
                    method: "GET".into(),
                    path: "/files/deadbeef".into(),
                    body: vec![],
                },
                &store,
                &slant,
                &cfg(),
            )
            .await;
            assert_eq!(missing.status, 404);
        });
    }
}
