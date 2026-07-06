//! End-to-end tests of the transport-agnostic pipeline: extract a target from a
//! proxy request URL, run it through the SSRF guard, and sanitize headers. The
//! wasm `fetch` glue is not exercised here (it needs the Workers runtime); these
//! cover the security-critical decisions that gate every real request.

use cors_proxy_worker::error::GuardError;
use cors_proxy_worker::proxy::{
    decide_cors, extract_target, filtered_response_headers, outbound_request_headers, CorsDecision,
};
use cors_proxy_worker::url_guard;

fn headers(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
    pairs
        .iter()
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect()
}

#[test]
fn public_target_is_accepted_and_headers_are_cleaned() {
    let request_url = "https://proxy.dev/?url=https%3A%2F%2Fapi.github.com%2Fusers%2Foctocat";
    let target = extract_target(request_url).expect("target");
    let url = url_guard::validate(&target).expect("valid");
    assert_eq!(url.host_str(), Some("api.github.com"));

    let outbound = outbound_request_headers(&headers(&[
        ("Accept", "application/json"),
        ("Cookie", "session=secret"),
        ("CF-Connecting-IP", "9.9.9.9"),
    ]));
    let names: Vec<String> = outbound.iter().map(|(k, _)| k.to_lowercase()).collect();
    assert!(names.contains(&"accept".to_string()));
    assert!(!names.contains(&"cookie".to_string()));
    assert!(!names.contains(&"cf-connecting-ip".to_string()));
}

#[test]
fn metadata_target_is_refused_end_to_end() {
    let request_url = "https://proxy.dev/?url=http%3A%2F%2F169.254.169.254%2Flatest%2Fmeta-data%2F";
    let target = extract_target(request_url).expect("target");
    let err = url_guard::validate(&target).unwrap_err();
    assert!(matches!(err, GuardError::BlockedIp(_)));
    assert_eq!(err.status(), 403);
}

#[test]
fn path_style_loopback_is_refused() {
    let request_url = "https://proxy.dev/http://127.0.0.1:8080/admin";
    let target = extract_target(request_url).expect("target");
    let err = url_guard::validate(&target).unwrap_err();
    assert!(matches!(err, GuardError::BlockedIp(_)));
}

#[test]
fn set_cookie_never_reaches_the_browser() {
    let relayed = filtered_response_headers(&headers(&[
        ("Content-Type", "text/plain"),
        ("Set-Cookie", "a=b; HttpOnly"),
    ]));
    let names: Vec<String> = relayed.iter().map(|(k, _)| k.to_lowercase()).collect();
    assert!(names.contains(&"content-type".to_string()));
    assert!(!names.contains(&"set-cookie".to_string()));
}

#[test]
fn allow_list_blocks_unknown_origin() {
    let cfg = "https://app.example";
    assert_eq!(
        decide_cors(Some("https://app.example"), cfg),
        CorsDecision::Reflect("https://app.example".to_string())
    );
    assert_eq!(
        decide_cors(Some("https://attacker.example"), cfg),
        CorsDecision::Denied
    );
}
