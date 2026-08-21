//! HTTP routing that does not depend on the Workers runtime.

use serde::Deserialize;
use url::form_urlencoded;

use crate::error::Error;
use crate::maps::{EnvelopeSize, MapStyle};

const FORM_HTML: &str = include_str!("form.html");

const LIVE_STATUS: &str =
    "This Worker has a Google Maps key. The envelope background is the driving route between the two addresses.";
const DOWN_STATUS: &str =
    "GOOGLE_MAPS_API_KEY is missing or unusable. Envelope generation is disabled until a usable key is bound to this Worker.";

/// A request reduced to method, path, query, and body.
#[derive(Debug, Clone)]
pub struct ApiRequest {
    pub method: String,
    pub path: String,
    pub query: Vec<(String, String)>,
    pub content_type: Option<String>,
    pub body: Vec<u8>,
}

/// What the caller asked for, after parsing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Classified {
    Health,
    Form,
    Envelope {
        from: String,
        to: String,
        style: MapStyle,
        size: EnvelopeSize,
    },
    BadRequest(String),
    NotFound,
}

/// Classify a request. Fetching maps and writing the PDF happen at the edge
/// (Worker or CLI) so this stays synchronous and testable.
pub fn classify(req: &ApiRequest) -> Classified {
    let method = req.method.to_ascii_uppercase();
    let path = normalize_path(&req.path);
    match (method.as_str(), path) {
        ("GET" | "HEAD", "/health") => Classified::Health,
        ("GET" | "HEAD", "/") => Classified::Form,
        ("GET" | "HEAD", "/envelope") => envelope_from_pairs(&req.query),
        ("POST", "/envelope") => envelope_from_post(req),
        _ => Classified::NotFound,
    }
}

fn normalize_path(path: &str) -> &str {
    let p = path.trim_end_matches('/');
    if p.is_empty() {
        "/"
    } else {
        p
    }
}

fn envelope_from_pairs(pairs: &[(String, String)]) -> Classified {
    let from = pair_value(pairs, "from").unwrap_or_default();
    let to = pair_value(pairs, "to").unwrap_or_default();
    if from.trim().is_empty() || to.trim().is_empty() {
        return Classified::BadRequest("from and to are required".into());
    }
    let style = match MapStyle::parse(pair_value(pairs, "style").as_deref()) {
        Ok(style) => style,
        Err(e) => return Classified::BadRequest(e.to_string()),
    };
    let size = match EnvelopeSize::parse(pair_value(pairs, "size").as_deref()) {
        Ok(size) => size,
        Err(e) => return Classified::BadRequest(e.to_string()),
    };
    Classified::Envelope {
        from,
        to,
        style,
        size,
    }
}

fn envelope_from_post(req: &ApiRequest) -> Classified {
    let ctype = req
        .content_type
        .as_deref()
        .unwrap_or("")
        .to_ascii_lowercase();
    if ctype.contains("application/json") {
        return match serde_json::from_slice::<EnvelopeJson>(&req.body) {
            Ok(body) => {
                if body.from.trim().is_empty() || body.to.trim().is_empty() {
                    Classified::BadRequest("from and to are required".into())
                } else {
                    let style = match MapStyle::parse(body.style.as_deref()) {
                        Ok(style) => style,
                        Err(e) => return Classified::BadRequest(e.to_string()),
                    };
                    let size = match EnvelopeSize::parse(body.size.as_deref()) {
                        Ok(size) => size,
                        Err(e) => return Classified::BadRequest(e.to_string()),
                    };
                    Classified::Envelope {
                        from: body.from,
                        to: body.to,
                        style,
                        size,
                    }
                }
            }
            Err(e) => Classified::BadRequest(format!("JSON: {e}")),
        };
    }
    let pairs: Vec<(String, String)> = form_urlencoded::parse(&req.body).into_owned().collect();
    envelope_from_pairs(&pairs)
}

#[derive(Debug, Deserialize)]
struct EnvelopeJson {
    from: String,
    to: String,
    #[serde(default)]
    style: Option<String>,
    #[serde(default)]
    size: Option<String>,
}

fn pair_value(pairs: &[(String, String)], key: &str) -> Option<String> {
    pairs
        .iter()
        .find(|(k, _)| k.eq_ignore_ascii_case(key))
        .map(|(_, v)| v.clone())
}

/// JSON body for `GET /health`.
pub fn health_json(maps_live: bool) -> Vec<u8> {
    if maps_live {
        serde_json::json!({ "ok": true, "maps": "google" })
    } else {
        serde_json::json!({
            "ok": false,
            "maps": "none",
            "error": "GOOGLE_MAPS_API_KEY is missing or unusable",
        })
    }
    .to_string()
    .into_bytes()
}

/// HTML form, with a status line that says whether Google Maps is live.
pub fn form_html(maps_live: bool) -> Vec<u8> {
    let status = if maps_live { LIVE_STATUS } else { DOWN_STATUS };
    let mut html = FORM_HTML.replace("__MAPS_STATUS__", status);
    if !maps_live {
        if let (Some(start), Some(end)) = (html.find("<form"), html.find("</form>")) {
            html.replace_range(start..end + "</form>".len(), "");
        }
    }
    html.into_bytes()
}

/// JSON error body.
pub fn error_json(err: &Error) -> Vec<u8> {
    serde_json::json!({ "error": err.to_string() })
        .to_string()
        .into_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn req(method: &str, path: &str) -> ApiRequest {
        ApiRequest {
            method: method.into(),
            path: path.into(),
            query: Vec::new(),
            content_type: None,
            body: Vec::new(),
        }
    }

    #[test]
    fn get_root_is_form() {
        assert_eq!(classify(&req("GET", "/")), Classified::Form);
        assert_eq!(classify(&req("get", "/")), Classified::Form);
    }

    #[test]
    fn health() {
        assert_eq!(classify(&req("GET", "/health/")), Classified::Health);
        let body = String::from_utf8(health_json(false)).unwrap();
        assert!(body.contains("none"));
        assert!(body.contains("false"));
        assert!(String::from_utf8(health_json(true))
            .unwrap()
            .contains("google"));
    }

    #[test]
    fn get_envelope_query() {
        let mut r = req("GET", "/envelope");
        r.query = vec![
            ("from".into(), "Mountain View, CA".into()),
            ("to".into(), "New York, NY".into()),
        ];
        match classify(&r) {
            Classified::Envelope {
                from,
                to,
                style,
                size,
            } => {
                assert!(from.contains("Mountain View"));
                assert!(to.contains("New York"));
                assert_eq!(style, MapStyle::Google);
                assert_eq!(size, EnvelopeSize::Ten);
            }
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn post_form() {
        let mut r = req("POST", "/envelope");
        r.content_type = Some("application/x-www-form-urlencoded".into());
        r.body = b"from=Ada%0AMountain+View%2C+CA&to=Bob%0ANew+York%2C+NY".to_vec();
        match classify(&r) {
            Classified::Envelope {
                from,
                to,
                style,
                size,
            } => {
                assert!(from.contains("Ada"));
                assert!(from.contains("Mountain View"));
                assert!(to.contains("Bob"));
                assert_eq!(style, MapStyle::Google);
                assert_eq!(size, EnvelopeSize::Ten);
            }
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn post_json() {
        let mut r = req("POST", "/envelope");
        r.content_type = Some("application/json".into());
        r.body = br#"{"from":"A","to":"B"}"#.to_vec();
        assert_eq!(
            classify(&r),
            Classified::Envelope {
                from: "A".into(),
                to: "B".into(),
                style: MapStyle::Google,
                size: EnvelopeSize::Ten,
            }
        );
    }

    #[test]
    fn missing_fields() {
        let mut r = req("POST", "/envelope");
        r.body = b"from=only".to_vec();
        assert!(matches!(classify(&r), Classified::BadRequest(_)));
    }

    #[test]
    fn form_html_splices_status() {
        let html = String::from_utf8(form_html(false)).unwrap();
        assert!(html.contains("<html lang=\"en\">"));
        assert!(html.contains("GOOGLE_MAPS_API_KEY"));
        assert!(!html.contains("<form"));
        assert!(!html.contains("__MAPS_STATUS__"));
        let live = String::from_utf8(form_html(true)).unwrap();
        assert!(live.contains("Google Maps key"));
        assert!(live.contains("<form"));
        assert!(live.contains("name=\"style\""));
        assert!(live.contains("value=\"paper\""));
        assert!(live.contains("name=\"size\""));
        assert!(live.contains("value=\"a7\""));
        assert!(live.contains("value=\"6-3/4\""));
    }

    #[test]
    fn post_form_style() {
        let mut r = req("POST", "/envelope");
        r.content_type = Some("application/x-www-form-urlencoded".into());
        r.body = b"from=Ada&to=Bob&style=hybrid".to_vec();
        match classify(&r) {
            Classified::Envelope { style, .. } => assert_eq!(style, MapStyle::Hybrid),
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn unknown_style_is_bad_request() {
        let mut r = req("GET", "/envelope");
        r.query = vec![
            ("from".into(), "A".into()),
            ("to".into(), "B".into()),
            ("style".into(), "oil".into()),
        ];
        assert!(matches!(classify(&r), Classified::BadRequest(_)));
    }

    #[test]
    fn post_form_size() {
        let mut r = req("POST", "/envelope");
        r.content_type = Some("application/x-www-form-urlencoded".into());
        r.body = b"from=Ada&to=Bob&size=a7".to_vec();
        match classify(&r) {
            Classified::Envelope { size, .. } => assert_eq!(size, EnvelopeSize::A7),
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn post_json_size() {
        let mut r = req("POST", "/envelope");
        r.content_type = Some("application/json".into());
        r.body = br#"{"from":"A","to":"B","size":"6-3/4"}"#.to_vec();
        match classify(&r) {
            Classified::Envelope { size, style, .. } => {
                assert_eq!(size, EnvelopeSize::SixThreeQuarter);
                assert_eq!(style, MapStyle::Google);
            }
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn unknown_size_is_bad_request() {
        let mut r = req("GET", "/envelope");
        r.query = vec![
            ("from".into(), "A".into()),
            ("to".into(), "B".into()),
            ("size".into(), "c5".into()),
        ];
        assert!(matches!(classify(&r), Classified::BadRequest(_)));
    }
}
