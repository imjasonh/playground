//! Cloudflare Workers entry point (compiled only for `wasm32`).
//!
//! Thin glue: R2-backed [`StlStore`], `fetch`-backed [`SlantClient`], CORS, and
//! deriving the public base URL from the inbound request so Slant can pull
//! `/files/{id}` during a quote.

use async_trait::async_trait;
use worker::js_sys::Uint8Array;
use worker::{event, Bucket, Context, Env, Fetch, Headers, Method, Request, RequestInit, Response};

use crate::api::{self, ApiConfig, ApiRequest, DEFAULT_MAX_STL_BYTES};
use crate::slant::{parse_slice_response, slice_request_body, SlantClient, SlantError};
use crate::store::{StlStore, StoreError};

const BUCKET_BINDING: &str = "STL_BUCKET";
const DEFAULT_SLANT_BASE: &str = "https://www.slant3dapi.com";

#[event(fetch)]
async fn fetch(mut req: Request, env: Env, _ctx: Context) -> worker::Result<Response> {
    let request_origin = req.headers().get("Origin").ok().flatten();
    let allowed = env
        .var("ALLOWED_ORIGINS")
        .map(|v| v.to_string())
        .unwrap_or_else(|_| "*".into());

    if req.method() == Method::Options {
        return preflight(request_origin.as_deref(), &allowed);
    }

    if !origin_allowed(request_origin.as_deref(), &allowed) {
        return json_response(
            403,
            r#"{"error":"origin not allowed"}"#,
            request_origin.as_deref(),
            &allowed,
        );
    }

    let public_base = match public_base_from_request(&req) {
        Ok(base) => base,
        Err(msg) => {
            return json_response(
                500,
                &format!(r#"{{"error":"{}"}}"#, json_escape(&msg)),
                request_origin.as_deref(),
                &allowed,
            );
        }
    };

    let max_stl_bytes = env
        .var("MAX_STL_BYTES")
        .ok()
        .and_then(|v| v.to_string().trim().parse::<usize>().ok())
        .filter(|n| *n > 0)
        .unwrap_or(DEFAULT_MAX_STL_BYTES);

    let api_key = env
        .secret("SLANT_API_KEY")
        .map(|s| s.to_string())
        .or_else(|_| env.var("SLANT_API_KEY").map(|v| v.to_string()))
        .ok()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty());

    let slant_base = env
        .var("SLANT_API_BASE")
        .map(|v| v.to_string())
        .unwrap_or_else(|_| DEFAULT_SLANT_BASE.into());

    let config = ApiConfig {
        public_base,
        slant_configured: api_key.is_some(),
        max_stl_bytes,
    };

    let store = match env.bucket(BUCKET_BINDING) {
        Ok(bucket) => R2StlStore { bucket },
        Err(_) => {
            return json_response(
                500,
                r#"{"error":"R2 bucket 'STL_BUCKET' is not bound"}"#,
                request_origin.as_deref(),
                &allowed,
            );
        }
    };

    let slant = WorkerSlant {
        api_key: api_key.unwrap_or_default(),
        api_base: slant_base.trim_end_matches('/').to_string(),
    };

    // Cap the inbound body before buffering the whole thing when Content-Length
    // is present; still re-check after the read for chunked uploads.
    if content_length_exceeds(&req, max_stl_bytes) {
        return json_response(
            413,
            &format!(r#"{{"error":"STL exceeds max size of {max_stl_bytes} bytes"}}"#),
            request_origin.as_deref(),
            &allowed,
        );
    }

    let body = req.bytes().await.unwrap_or_default();
    let api_request = ApiRequest {
        method: req.method().as_ref().to_string(),
        path: req.path(),
        body,
    };

    let response = api::handle(api_request, &store, &slant, &config).await;
    into_worker_response(response, request_origin.as_deref(), &allowed)
}

fn public_base_from_request(req: &Request) -> Result<String, String> {
    let url = req.url().map_err(|e| e.to_string())?;
    let scheme = url.scheme();
    let host = url
        .host_str()
        .ok_or_else(|| "request URL missing host".to_string())?;
    Ok(format!("{scheme}://{host}"))
}

fn content_length_exceeds(req: &Request, max: usize) -> bool {
    req.headers()
        .get("Content-Length")
        .ok()
        .flatten()
        .and_then(|v| v.parse::<usize>().ok())
        .is_some_and(|n| n > max)
}

struct R2StlStore {
    bucket: Bucket,
}

#[async_trait(?Send)]
impl StlStore for R2StlStore {
    async fn put(&self, id: &str, bytes: Vec<u8>) -> Result<(), StoreError> {
        self.bucket
            .put(format!("stl/{id}"), bytes)
            .execute()
            .await
            .map(|_| ())
            .map_err(|e| StoreError(e.to_string()))
    }

    async fn get(&self, id: &str) -> Result<Option<Vec<u8>>, StoreError> {
        let got = self
            .bucket
            .get(format!("stl/{id}"))
            .execute()
            .await
            .map_err(|e| StoreError(e.to_string()))?;
        match got {
            Some(obj) => {
                let bytes = obj
                    .body()
                    .ok_or_else(|| StoreError("R2 object missing body".into()))?
                    .bytes()
                    .await
                    .map_err(|e| StoreError(e.to_string()))?;
                Ok(Some(bytes))
            }
            None => Ok(None),
        }
    }

    async fn delete(&self, id: &str) -> Result<(), StoreError> {
        self.bucket
            .delete(format!("stl/{id}"))
            .await
            .map_err(|e| StoreError(e.to_string()))
    }
}

struct WorkerSlant {
    api_key: String,
    api_base: String,
}

#[async_trait(?Send)]
impl SlantClient for WorkerSlant {
    async fn slice(&self, file_url: &str) -> Result<crate::slant::SliceQuote, SlantError> {
        if self.api_key.is_empty() {
            return Err(SlantError::Transport("SLANT_API_KEY missing".into()));
        }

        let url = format!("{}/api/slicer", self.api_base);
        let body = slice_request_body(file_url);

        let headers = Headers::new();
        headers
            .set("Content-Type", "application/json")
            .map_err(|e| SlantError::Transport(e.to_string()))?;
        headers
            .set("api-key", &self.api_key)
            .map_err(|e| SlantError::Transport(e.to_string()))?;

        let array = Uint8Array::new_with_length(body.len() as u32);
        array.copy_from(&body);

        let mut init = RequestInit::new();
        init.with_method(Method::Post)
            .with_headers(headers)
            .with_body(Some(array.into()));

        let request = Request::new_with_init(&url, &init)
            .map_err(|e| SlantError::Transport(e.to_string()))?;
        let mut response = Fetch::Request(request)
            .send()
            .await
            .map_err(|e| SlantError::Transport(e.to_string()))?;

        let status = response.status_code();
        let bytes = response
            .bytes()
            .await
            .map_err(|e| SlantError::Transport(e.to_string()))?;

        if !(200..300).contains(&status) {
            let body = String::from_utf8_lossy(&bytes).into_owned();
            return Err(SlantError::Status { status, body });
        }
        parse_slice_response(&bytes)
    }
}

fn origin_allowed(origin: Option<&str>, allowed: &str) -> bool {
    let allowed = allowed.trim();
    if allowed == "*" {
        return true;
    }
    let Some(origin) = origin else {
        // Non-browser clients (curl, Slant fetching /files) omit Origin.
        return true;
    };
    allowed
        .split(',')
        .map(str::trim)
        .any(|entry| entry == origin)
}

fn cors_headers(origin: Option<&str>, allowed: &str) -> Headers {
    let headers = Headers::new();
    let allow = if allowed.trim() == "*" {
        "*".to_string()
    } else {
        origin.unwrap_or("").to_string()
    };
    let _ = headers.set("Access-Control-Allow-Origin", &allow);
    let _ = headers.set("Access-Control-Allow-Methods", "GET, POST, OPTIONS");
    let _ = headers.set("Access-Control-Allow-Headers", "Content-Type");
    let _ = headers.set("Access-Control-Max-Age", "86400");
    headers
}

fn preflight(origin: Option<&str>, allowed: &str) -> worker::Result<Response> {
    if !origin_allowed(origin, allowed) {
        return json_response(403, r#"{"error":"origin not allowed"}"#, origin, allowed);
    }
    Ok(Response::empty()?
        .with_status(204)
        .with_headers(cors_headers(origin, allowed)))
}

fn into_worker_response(
    response: api::ApiResponse,
    origin: Option<&str>,
    allowed: &str,
) -> worker::Result<Response> {
    let headers = cors_headers(origin, allowed);
    let _ = headers.set("Content-Type", &response.content_type);
    if let Some(disp) = &response.content_disposition {
        let _ = headers.set("Content-Disposition", disp);
    }
    Ok(Response::from_bytes(response.body)?
        .with_status(response.status)
        .with_headers(headers))
}

fn json_response(
    status: u16,
    body: &str,
    origin: Option<&str>,
    allowed: &str,
) -> worker::Result<Response> {
    let headers = cors_headers(origin, allowed);
    let _ = headers.set("Content-Type", "application/json");
    Ok(Response::from_bytes(body.as_bytes().to_vec())?
        .with_status(status)
        .with_headers(headers))
}

fn json_escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}
