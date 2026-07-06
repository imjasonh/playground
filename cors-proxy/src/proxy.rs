//! Transport-agnostic proxy logic: target extraction, request/response header
//! sanitization, CORS decisions, and size limits.
//!
//! None of this depends on the Workers runtime, so it is all unit-tested
//! natively. The wasm entry point (`worker_entry`) wires these helpers to the
//! `fetch` API.

use serde_json::{json, Value};

/// Maximum redirects to follow before giving up. Each hop is re-validated by
/// [`crate::url_guard::validate_url`].
pub const MAX_REDIRECTS: usize = 5;

/// Default cap on the upstream response size (25 MiB), used when the
/// `MAX_RESPONSE_BYTES` var is unset or unparseable.
pub const DEFAULT_MAX_RESPONSE_BYTES: usize = 25 * 1024 * 1024;

/// Default cap on the inbound request body the proxy will read and forward
/// (10 MiB), used when the `MAX_REQUEST_BYTES` var is unset or unparseable.
pub const DEFAULT_MAX_REQUEST_BYTES: usize = 10 * 1024 * 1024;

/// Headers carrying caller credentials. They are forwarded on the first hop but
/// dropped when a redirect crosses to a different origin, so a redirect to an
/// attacker-controlled host cannot harvest them.
const CREDENTIAL_HEADERS: &[&str] = &[
    "authorization",
    "proxy-authorization",
    "cookie",
    "x-api-key",
];

/// Request headers that must never be forwarded to the upstream: hop-by-hop
/// headers, identity/forwarding leakage, and headers the runtime sets itself.
const STRIP_REQUEST_HEADERS: &[&str] = &[
    // Hop-by-hop (RFC 7230 §6.1).
    "connection",
    "keep-alive",
    "proxy-authenticate",
    "proxy-authorization",
    "te",
    "trailer",
    "transfer-encoding",
    "upgrade",
    // Set by the runtime from the target URL / body.
    "host",
    "content-length",
    // Let the runtime negotiate encoding so we never receive bytes we would
    // then mislabel to the client.
    "accept-encoding",
    // Don't leak the caller's identity, origin, or cookies to the upstream.
    "origin",
    "referer",
    "cookie",
    "forwarded",
    "x-forwarded-for",
    "x-forwarded-host",
    "x-forwarded-proto",
    "x-real-ip",
    "via",
];

/// Response headers that must not be relayed back to the browser.
const STRIP_RESPONSE_HEADERS: &[&str] = &[
    // Never relay upstream cookies to a cross-origin caller.
    "set-cookie",
    "set-cookie2",
    // Hop-by-hop.
    "connection",
    "keep-alive",
    "proxy-authenticate",
    "te",
    "trailer",
    "transfer-encoding",
    "upgrade",
    // The runtime has already decoded the body and will recompute length, so
    // relaying the upstream values would corrupt the response.
    "content-encoding",
    "content-length",
];

fn is_stripped(name: &str, list: &[&str]) -> bool {
    let lower = name.to_ascii_lowercase();
    list.contains(&lower.as_str()) || lower.starts_with("cf-") || lower.starts_with("x-forwarded-")
}

/// The set of request headers to forward to the upstream.
pub fn outbound_request_headers(headers: &[(String, String)]) -> Vec<(String, String)> {
    headers
        .iter()
        .filter(|(name, _)| !is_stripped(name, STRIP_REQUEST_HEADERS))
        .cloned()
        .collect()
}

/// The set of upstream response headers to relay back to the browser, with all
/// existing `access-control-*` headers removed (we set our own).
pub fn filtered_response_headers(headers: &[(String, String)]) -> Vec<(String, String)> {
    headers
        .iter()
        .filter(|(name, _)| {
            let lower = name.to_ascii_lowercase();
            !is_stripped(&lower, STRIP_RESPONSE_HEADERS) && !lower.starts_with("access-control-")
        })
        .cloned()
        .collect()
}

/// Whether a header name carries caller credentials (see [`CREDENTIAL_HEADERS`]).
pub fn is_credential_header(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    CREDENTIAL_HEADERS.contains(&lower.as_str())
}

/// Remove credential-bearing headers from an outbound header set in place.
pub fn strip_credential_headers(headers: &mut Vec<(String, String)>) {
    headers.retain(|(name, _)| !is_credential_header(name));
}

/// Whether two URLs share an origin (scheme + host + effective port). Used to
/// decide when a redirect crosses an origin boundary.
pub fn same_origin(a: &url::Url, b: &url::Url) -> bool {
    a.scheme() == b.scheme()
        && a.host_str() == b.host_str()
        && a.port_or_known_default() == b.port_or_known_default()
}

/// Whether an upstream `Content-Length` header advertises a body larger than
/// `max` bytes. A missing or unparseable value returns `false` (we then rely on
/// the streaming read cap in the entry point).
pub fn content_length_exceeds(headers: &[(String, String)], max: usize) -> bool {
    headers
        .iter()
        .find(|(name, _)| name.eq_ignore_ascii_case("content-length"))
        .and_then(|(_, value)| value.trim().parse::<u64>().ok())
        .is_some_and(|len| len > max as u64)
}

/// The outcome of matching a request's `Origin` against the configured
/// allow-list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CorsDecision {
    /// Allow any origin (`Access-Control-Allow-Origin: *`).
    Wildcard,
    /// Reflect this specific origin (allow-list matched).
    Reflect(String),
    /// Proxy, but send no CORS header (a non-browser caller with no `Origin`).
    OmitHeader,
    /// The browser origin is not on the allow-list; refuse the request.
    Denied,
}

/// Decide how to handle CORS for a request given the configured allow-list.
///
/// `allowed_config` is either `*` (allow any origin) or a comma-separated list
/// of exact origins (e.g. `https://a.example,https://b.example`).
pub fn decide_cors(request_origin: Option<&str>, allowed_config: &str) -> CorsDecision {
    if allowed_config.trim() == "*" {
        return CorsDecision::Wildcard;
    }
    match request_origin {
        None => CorsDecision::OmitHeader,
        Some(origin) => {
            let matches = allowed_config
                .split(',')
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .any(|allowed| allowed.eq_ignore_ascii_case(origin));
            if matches {
                CorsDecision::Reflect(origin.to_string())
            } else {
                CorsDecision::Denied
            }
        }
    }
}

/// Extract the target URL from a proxy request URL. Supports the primary
/// `?url=<encoded>` form and a best-effort path style
/// (`https://proxy/https://target/...`).
pub fn extract_target(request_url: &str) -> Option<String> {
    if let Ok(parsed) = url::Url::parse(request_url) {
        if let Some((_, value)) = parsed.query_pairs().find(|(key, _)| key == "url") {
            let value = value.trim().to_string();
            if !value.is_empty() {
                return Some(value);
            }
        }
    }
    path_style_target(request_url)
}

fn path_style_target(request_url: &str) -> Option<String> {
    let scheme_end = request_url.find("://")? + 3;
    let rest = &request_url[scheme_end..];
    let slash = rest.find('/')?;
    let remainder = &rest[slash + 1..];
    if remainder.is_empty() {
        return None;
    }
    let decoded = percent_decode(remainder);
    if decoded.starts_with("http://") || decoded.starts_with("https://") {
        Some(decoded)
    } else {
        None
    }
}

/// Decode `%XX` escapes in a string, interpreting the resulting bytes as UTF-8
/// (lossily). Sufficient for un-escaping a target URL carried in the path.
fn percent_decode(input: &str) -> String {
    let bytes = input.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' && i + 2 < bytes.len() {
            if let (Some(hi), Some(lo)) = (hex_val(bytes[i + 1]), hex_val(bytes[i + 2])) {
                out.push((hi << 4) | lo);
                i += 3;
                continue;
            }
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn hex_val(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

/// A JSON usage/help document returned from `GET /` with no target.
pub fn usage_json(max_response_bytes: usize, max_request_bytes: usize) -> Value {
    json!({
        "service": "cors-proxy",
        "description": "An SSRF-hardened CORS proxy for Cloudflare Workers.",
        "usage": {
            "query": "GET or POST /?url=<url-encoded absolute URL>",
            "path": "GET or POST /<absolute URL>",
            "example": "/?url=https%3A%2F%2Fapi.github.com%2Fusers%2Foctocat",
        },
        "limits": {
            "schemes": ["http", "https"],
            "maxResponseBytes": max_response_bytes,
            "maxRequestBytes": max_request_bytes,
            "maxRedirects": MAX_REDIRECTS,
        },
        "notes": [
            "Requests to loopback, private, link-local, and cloud-metadata addresses are refused.",
            "Cookies are not forwarded upstream and Set-Cookie is stripped from responses.",
            "This proxy can read all traffic passing through it — never send secrets or authenticated requests through a shared deployment.",
        ],
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn h(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
        pairs
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect()
    }

    fn names(headers: &[(String, String)]) -> Vec<String> {
        headers
            .iter()
            .map(|(k, _)| k.to_ascii_lowercase())
            .collect()
    }

    #[test]
    fn strips_dangerous_request_headers() {
        let input = h(&[
            ("Accept", "application/json"),
            ("Content-Type", "application/json"),
            ("Host", "proxy.example"),
            ("Cookie", "session=secret"),
            ("Origin", "https://caller.example"),
            ("Referer", "https://caller.example/page"),
            ("X-Forwarded-For", "1.2.3.4"),
            ("CF-Connecting-IP", "1.2.3.4"),
            ("Accept-Encoding", "gzip"),
        ]);
        let out = names(&outbound_request_headers(&input));
        assert!(out.contains(&"accept".to_string()));
        assert!(out.contains(&"content-type".to_string()));
        for banned in [
            "host",
            "cookie",
            "origin",
            "referer",
            "x-forwarded-for",
            "cf-connecting-ip",
            "accept-encoding",
        ] {
            assert!(!out.contains(&banned.to_string()), "leaked {banned}");
        }
    }

    #[test]
    fn strips_set_cookie_and_cors_from_response() {
        let input = h(&[
            ("Content-Type", "application/json"),
            ("Set-Cookie", "a=b"),
            ("set-cookie2", "c=d"),
            ("Content-Length", "123"),
            ("Content-Encoding", "gzip"),
            ("Access-Control-Allow-Origin", "https://upstream"),
            ("Transfer-Encoding", "chunked"),
        ]);
        let out = names(&filtered_response_headers(&input));
        assert_eq!(out, vec!["content-type".to_string()]);
    }

    #[test]
    fn content_length_limit() {
        let headers = h(&[("Content-Length", "1048577")]);
        assert!(content_length_exceeds(&headers, 1024 * 1024));
        assert!(!content_length_exceeds(
            &h(&[("Content-Length", "10")]),
            1024 * 1024
        ));
        assert!(!content_length_exceeds(&h(&[]), 1024 * 1024));
        assert!(!content_length_exceeds(
            &h(&[("Content-Length", "nope")]),
            1024
        ));
    }

    #[test]
    fn cors_wildcard() {
        assert_eq!(
            decide_cors(Some("https://a.example"), "*"),
            CorsDecision::Wildcard
        );
        assert_eq!(decide_cors(None, "*"), CorsDecision::Wildcard);
    }

    #[test]
    fn cors_allow_list() {
        let cfg = "https://a.example, https://b.example";
        assert_eq!(
            decide_cors(Some("https://a.example"), cfg),
            CorsDecision::Reflect("https://a.example".to_string())
        );
        assert_eq!(
            decide_cors(Some("https://B.EXAMPLE"), cfg),
            CorsDecision::Reflect("https://B.EXAMPLE".to_string())
        );
        assert_eq!(
            decide_cors(Some("https://evil.example"), cfg),
            CorsDecision::Denied
        );
        assert_eq!(decide_cors(None, cfg), CorsDecision::OmitHeader);
    }

    #[test]
    fn extract_target_query_form() {
        assert_eq!(
            extract_target("https://proxy.dev/?url=https%3A%2F%2Fapi.example%2Fx"),
            Some("https://api.example/x".to_string())
        );
        assert_eq!(
            extract_target("https://proxy.dev/?url=https://api.example/x"),
            Some("https://api.example/x".to_string())
        );
    }

    #[test]
    fn extract_target_path_form() {
        assert_eq!(
            extract_target("https://proxy.dev/https://api.example/x?y=1"),
            Some("https://api.example/x?y=1".to_string())
        );
        assert_eq!(
            extract_target("https://proxy.dev/https%3A%2F%2Fapi.example%2Fx"),
            Some("https://api.example/x".to_string())
        );
    }

    #[test]
    fn extract_target_none_when_absent() {
        assert_eq!(extract_target("https://proxy.dev/"), None);
        assert_eq!(extract_target("https://proxy.dev/favicon.ico"), None);
        assert_eq!(extract_target("https://proxy.dev/?url="), None);
    }

    #[test]
    fn credential_headers_detected_and_stripped() {
        assert!(is_credential_header("Authorization"));
        assert!(is_credential_header("cookie"));
        assert!(is_credential_header("X-API-Key"));
        assert!(!is_credential_header("Accept"));
        assert!(!is_credential_header("Content-Type"));

        let mut headers = h(&[
            ("Accept", "*/*"),
            ("Authorization", "Bearer secret"),
            ("X-Api-Key", "k"),
        ]);
        strip_credential_headers(&mut headers);
        let names = names(&headers);
        assert_eq!(names, vec!["accept".to_string()]);
    }

    #[test]
    fn same_origin_compares_scheme_host_port() {
        let a = url::Url::parse("https://example.com/a").unwrap();
        let b = url::Url::parse("https://example.com/b?x=1").unwrap();
        let c = url::Url::parse("https://example.com:8443/a").unwrap();
        let d = url::Url::parse("http://example.com/a").unwrap();
        let e = url::Url::parse("https://evil.com/a").unwrap();
        let f = url::Url::parse("https://example.com:443/a").unwrap();
        assert!(same_origin(&a, &b));
        assert!(same_origin(&a, &f)); // 443 is the default https port
        assert!(!same_origin(&a, &c));
        assert!(!same_origin(&a, &d));
        assert!(!same_origin(&a, &e));
    }

    #[test]
    fn percent_decode_basics() {
        assert_eq!(percent_decode("a%20b"), "a b");
        assert_eq!(percent_decode("https%3A%2F%2Fx"), "https://x");
        assert_eq!(percent_decode("no-escapes"), "no-escapes");
        assert_eq!(percent_decode("trailing%"), "trailing%");
    }
}
