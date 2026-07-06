//! Cloudflare Workers entry point (compiled only for `wasm32`).
//!
//! This is the thin glue between the Workers runtime and the transport-agnostic
//! [`crate::proxy`] / [`crate::url_guard`] logic. It:
//!
//! * reads configuration from environment vars (`ALLOWED_ORIGINS`,
//!   `MAX_RESPONSE_BYTES`);
//! * answers CORS preflights and enforces the origin allow-list;
//! * validates the target URL, then fetches it with `redirect: manual`,
//!   re-validating every `Location` hop against the SSRF guard;
//! * relays the response with sanitized headers and our own CORS headers.

use serde_json::json;
use worker::js_sys::Uint8Array;
use worker::{
    event, Context, Env, Fetch, Headers, Method, Request, RequestInit, RequestRedirect, Response,
    Result, Url,
};

use crate::error::GuardError;
use crate::proxy::{
    content_length_exceeds, decide_cors, extract_target, filtered_response_headers,
    outbound_request_headers, usage_json, CorsDecision, DEFAULT_MAX_RESPONSE_BYTES, MAX_REDIRECTS,
};
use crate::url_guard;

/// Runtime configuration read from the environment.
struct Config {
    allowed_origins: String,
    max_response_bytes: usize,
}

impl Config {
    fn from_env(env: &Env) -> Self {
        let allowed_origins = env
            .var("ALLOWED_ORIGINS")
            .map(|v| v.to_string())
            .unwrap_or_else(|_| "*".to_string());
        let max_response_bytes = env
            .var("MAX_RESPONSE_BYTES")
            .ok()
            .and_then(|v| v.to_string().trim().parse::<usize>().ok())
            .filter(|n| *n > 0)
            .unwrap_or(DEFAULT_MAX_RESPONSE_BYTES);
        Config {
            allowed_origins,
            max_response_bytes,
        }
    }
}

/// A fetched upstream response, reduced to plain data.
struct Upstream {
    status: u16,
    headers: Vec<(String, String)>,
    body: Vec<u8>,
}

enum ProxyError {
    Guard(GuardError),
    TooLarge(usize),
    Upstream(String),
}

#[event(fetch)]
async fn fetch(mut req: Request, env: Env, _ctx: Context) -> Result<Response> {
    let config = Config::from_env(&env);
    let request_origin = req.headers().get("Origin").ok().flatten();

    if req.method() == Method::Options {
        return preflight(&req, request_origin.as_deref(), &config);
    }

    let cors = decide_cors(request_origin.as_deref(), &config.allowed_origins);
    if cors == CorsDecision::Denied {
        return json_response(403, json!({ "error": "origin not allowed" }), &cors);
    }

    let request_url = req.url()?.to_string();
    let target_raw = match extract_target(&request_url) {
        Some(target) => target,
        None => return json_response(200, usage_json(config.max_response_bytes), &cors),
    };

    let target = match url_guard::validate(&target_raw) {
        Ok(url) => url,
        Err(e) => return guard_error(&e, &cors),
    };

    let method = req.method();
    let req_headers: Vec<(String, String)> = req.headers().entries().collect();
    let body = if method_has_body(&method) {
        req.bytes().await.unwrap_or_default()
    } else {
        Vec::new()
    };

    match proxy_fetch(target, method, req_headers, body, &config).await {
        Ok(upstream) => relay(upstream, &cors),
        Err(ProxyError::Guard(e)) => guard_error(&e, &cors),
        Err(ProxyError::TooLarge(max)) => json_response(
            413,
            json!({ "error": format!("upstream response exceeds {max} bytes") }),
            &cors,
        ),
        Err(ProxyError::Upstream(message)) => json_response(
            502,
            json!({ "error": "upstream fetch failed", "detail": message }),
            &cors,
        ),
    }
}

/// Fetch `target`, following up to [`MAX_REDIRECTS`] redirects manually and
/// re-validating each hop through the SSRF guard.
async fn proxy_fetch(
    mut target: Url,
    method: Method,
    req_headers: Vec<(String, String)>,
    body: Vec<u8>,
    config: &Config,
) -> std::result::Result<Upstream, ProxyError> {
    let outbound = outbound_request_headers(&req_headers);
    let mut cur_method = method;
    let mut cur_body = body;

    for _ in 0..=MAX_REDIRECTS {
        let mut headers = Headers::new();
        for (name, value) in &outbound {
            let _ = headers.set(name, value);
        }

        let mut init = RequestInit::new();
        init.with_method(cur_method.clone())
            .with_headers(headers)
            .with_redirect(RequestRedirect::Manual);

        if method_has_body(&cur_method) && !cur_body.is_empty() {
            let array = Uint8Array::new_with_length(cur_body.len() as u32);
            array.copy_from(&cur_body);
            init.with_body(Some(array.into()));
        }

        let request = Request::new_with_init(target.as_str(), &init)
            .map_err(|e| ProxyError::Upstream(e.to_string()))?;
        let mut response = Fetch::Request(request)
            .send()
            .await
            .map_err(|e| ProxyError::Upstream(e.to_string()))?;
        let status = response.status_code();

        if is_redirect(status) {
            if let Some(location) = response.headers().get("location").ok().flatten() {
                let next = target
                    .join(&location)
                    .map_err(|_| ProxyError::Guard(GuardError::InvalidUrl))?;
                url_guard::validate_url(&next).map_err(ProxyError::Guard)?;
                // 303 (and, by long-standing convention, 301/302) turn the
                // follow-up into a bodyless GET; 307/308 preserve method+body.
                if status != 307 && status != 308 {
                    cur_method = Method::Get;
                    cur_body = Vec::new();
                }
                target = next;
                continue;
            }
        }

        let resp_headers: Vec<(String, String)> = response.headers().entries().collect();
        if content_length_exceeds(&resp_headers, config.max_response_bytes) {
            return Err(ProxyError::TooLarge(config.max_response_bytes));
        }
        let bytes = response
            .bytes()
            .await
            .map_err(|e| ProxyError::Upstream(e.to_string()))?;
        if bytes.len() > config.max_response_bytes {
            return Err(ProxyError::TooLarge(config.max_response_bytes));
        }

        return Ok(Upstream {
            status,
            headers: resp_headers,
            body: bytes,
        });
    }

    Err(ProxyError::Guard(GuardError::TooManyRedirects))
}

/// Build the browser-facing response from an upstream result.
fn relay(upstream: Upstream, cors: &CorsDecision) -> Result<Response> {
    let mut headers = Headers::new();
    for (name, value) in filtered_response_headers(&upstream.headers) {
        let _ = headers.set(&name, &value);
    }
    apply_cors(&mut headers, cors);
    Ok(Response::from_bytes(upstream.body)?
        .with_status(upstream.status)
        .with_headers(headers))
}

fn preflight(req: &Request, origin: Option<&str>, config: &Config) -> Result<Response> {
    let cors = decide_cors(origin, &config.allowed_origins);
    if cors == CorsDecision::Denied {
        return Ok(Response::empty()?.with_status(403));
    }
    let mut headers = Headers::new();
    apply_cors(&mut headers, &cors);
    // Echo the requested headers so arbitrary custom request headers are allowed.
    let requested = req
        .headers()
        .get("Access-Control-Request-Headers")
        .ok()
        .flatten()
        .unwrap_or_else(|| "*".to_string());
    let _ = headers.set("Access-Control-Allow-Headers", &requested);
    Ok(Response::empty()?.with_status(204).with_headers(headers))
}

/// Apply our CORS headers according to the allow-list decision.
fn apply_cors(headers: &mut Headers, cors: &CorsDecision) {
    let origin = match cors {
        CorsDecision::Wildcard => Some("*".to_string()),
        CorsDecision::Reflect(o) => {
            let _ = headers.set("Vary", "Origin");
            Some(o.clone())
        }
        CorsDecision::OmitHeader | CorsDecision::Denied => None,
    };
    if let Some(origin) = origin {
        let _ = headers.set("Access-Control-Allow-Origin", &origin);
        let _ = headers.set(
            "Access-Control-Allow-Methods",
            "GET, POST, PUT, PATCH, DELETE, HEAD, OPTIONS",
        );
        let _ = headers.set("Access-Control-Allow-Headers", "*");
        let _ = headers.set("Access-Control-Expose-Headers", "*");
        let _ = headers.set("Access-Control-Max-Age", "86400");
    }
}

fn guard_error(err: &GuardError, cors: &CorsDecision) -> Result<Response> {
    json_response(err.status(), json!({ "error": err.to_string() }), cors)
}

fn json_response(status: u16, value: serde_json::Value, cors: &CorsDecision) -> Result<Response> {
    let mut headers = Headers::new();
    let _ = headers.set("Content-Type", "application/json");
    apply_cors(&mut headers, cors);
    Ok(Response::from_bytes(value.to_string().into_bytes())?
        .with_status(status)
        .with_headers(headers))
}

fn is_redirect(status: u16) -> bool {
    matches!(status, 301 | 302 | 303 | 307 | 308)
}

fn method_has_body(method: &Method) -> bool {
    !matches!(
        method,
        Method::Get | Method::Head | Method::Options | Method::Connect | Method::Trace
    )
}
