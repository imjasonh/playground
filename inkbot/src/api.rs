//! Transport-agnostic HTTP routing for inkbot.

use crate::auth::{authorize_upload, verify_slack_signature};
use crate::panel::{self, PanelImage, PanelSpec};
use crate::slack::{self, AppMention, SlackEvent};

/// Stored frame the Worker persists in R2.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StoredFrame {
    pub png: Vec<u8>,
    pub etag: String,
}

/// Side-effectful frame storage. Unit tests use an in-memory fake.
pub trait FrameStore {
    fn get(&self) -> Option<StoredFrame>;
    fn put(&mut self, frame: StoredFrame);
}

#[derive(Debug, Clone)]
pub struct ApiRequest {
    pub method: String,
    pub path: String,
    pub authorization: Option<String>,
    pub if_none_match: Option<String>,
    pub slack_timestamp: Option<String>,
    pub slack_signature: Option<String>,
    pub body: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ApiResponse {
    pub status: u16,
    pub content_type: &'static str,
    pub body: Vec<u8>,
    pub etag: Option<String>,
    pub cache_control: Option<&'static str>,
}

impl ApiResponse {
    pub fn text(status: u16, body: impl Into<String>) -> Self {
        Self {
            status,
            content_type: "text/plain; charset=utf-8",
            body: body.into().into_bytes(),
            etag: None,
            cache_control: None,
        }
    }

    pub fn json(status: u16, body: impl Into<String>) -> Self {
        Self {
            status,
            content_type: "application/json; charset=utf-8",
            body: body.into().into_bytes(),
            etag: None,
            cache_control: None,
        }
    }

    pub fn png(frame: &StoredFrame) -> Self {
        Self {
            status: 200,
            content_type: "image/png",
            body: frame.png.clone(),
            etag: Some(frame.etag.clone()),
            cache_control: Some("no-cache"),
        }
    }

    pub fn not_modified(etag: &str) -> Self {
        Self {
            status: 304,
            content_type: "image/png",
            body: Vec::new(),
            etag: Some(etag.to_string()),
            cache_control: Some("no-cache"),
        }
    }
}

/// Config shared by the simple (non-Slack-I/O) routes.
pub struct HandlerConfig<'a, S: FrameStore> {
    pub store: &'a mut S,
    pub upload_secret: &'a str,
    pub panel: PanelSpec,
}

/// Route GET/POST image and health checks. Slack Events are handled by
/// [`begin_slack_event`] + [`finish_app_mention`] so the Worker can await
/// Slack's file download / chat.postMessage without a sync HTTP client.
pub fn handle<S: FrameStore>(req: ApiRequest, cfg: &mut HandlerConfig<'_, S>) -> ApiResponse {
    let path = normalize_path(&req.path);
    let method = req.method.to_ascii_uppercase();

    match (method.as_str(), path.as_str()) {
        ("GET", "/") | ("GET", "/health") => ApiResponse::text(200, "inkbot ok\n"),
        ("GET", "/image.png") => get_image(&req, cfg.store),
        ("POST", "/image.png") => post_image(&req, cfg),
        ("OPTIONS", _) => ApiResponse::text(204, ""),
        _ => ApiResponse::text(404, "not found\n"),
    }
}

/// Result of verifying + parsing a Slack Events API request, before any
/// outbound Slack HTTP I/O.
#[derive(Debug)]
pub enum SlackBegin {
    Respond(ApiResponse),
    Mention(AppMention),
}

pub fn begin_slack_event(
    req: &ApiRequest,
    signing_secret: Option<&str>,
    now_unix: i64,
) -> SlackBegin {
    let Some(signing) = signing_secret.filter(|s| !s.is_empty()) else {
        return SlackBegin::Respond(ApiResponse::text(503, "slack not configured\n"));
    };
    let Some(ts) = req.slack_timestamp.as_deref() else {
        return SlackBegin::Respond(ApiResponse::text(401, "missing slack timestamp\n"));
    };
    let Some(sig) = req.slack_signature.as_deref() else {
        return SlackBegin::Respond(ApiResponse::text(401, "missing slack signature\n"));
    };
    if !verify_slack_signature(signing, ts, &req.body, sig, now_unix) {
        return SlackBegin::Respond(ApiResponse::text(401, "bad slack signature\n"));
    }

    match slack::parse_event(&req.body) {
        Ok(SlackEvent::UrlVerification { challenge }) => SlackBegin::Respond(ApiResponse::json(
            200,
            serde_json::json!({ "challenge": challenge }).to_string(),
        )),
        Ok(SlackEvent::Ignored) => SlackBegin::Respond(ApiResponse::json(200, r#"{"ok":true}"#)),
        Ok(SlackEvent::AppMention(mention)) => SlackBegin::Mention(mention),
        Err(e) => SlackBegin::Respond(ApiResponse::text(400, format!("{e}\n"))),
    }
}

/// Apply a downloaded Slack attachment to the panel store and return the
/// reply text to post back into the thread.
pub fn finish_app_mention<S: FrameStore>(
    image_bytes: Option<Result<Vec<u8>, String>>,
    store: &mut S,
    panel: PanelSpec,
) -> String {
    match image_bytes {
        None => "Attach an image and mention me — I'll dither it to the e-ink frame.".into(),
        Some(Err(e)) => format!("Couldn't download the attachment: {e}"),
        Some(Ok(bytes)) => match panel::transform_for_panel(&bytes, panel) {
            Ok(PanelImage { png, etag }) => {
                store.put(StoredFrame {
                    png,
                    etag: etag.clone(),
                });
                format!(
                    "Displayed on the e-ink frame ({}×{}, etag {}).",
                    panel.width, panel.height, etag
                )
            }
            Err(e) => format!("Couldn't transform that image: {e}"),
        },
    }
}

fn normalize_path(path: &str) -> String {
    let p = path.split('?').next().unwrap_or(path);
    if p.is_empty() {
        "/".into()
    } else {
        p.to_string()
    }
}

fn get_image<S: FrameStore>(req: &ApiRequest, store: &S) -> ApiResponse {
    let Some(frame) = store.get() else {
        return ApiResponse::text(404, "no image yet\n");
    };
    if let Some(inm) = req.if_none_match.as_deref() {
        if etags_match(inm, &frame.etag) {
            return ApiResponse::not_modified(&frame.etag);
        }
    }
    ApiResponse::png(&frame)
}

fn post_image<S: FrameStore>(req: &ApiRequest, cfg: &mut HandlerConfig<'_, S>) -> ApiResponse {
    if cfg.upload_secret.is_empty() {
        return ApiResponse::text(500, "UPLOAD_SECRET is not configured\n");
    }
    if !authorize_upload(req.authorization.as_deref(), cfg.upload_secret) {
        return ApiResponse::text(401, "unauthorized\n");
    }
    if req.body.is_empty() {
        return ApiResponse::text(400, "empty body\n");
    }
    match panel::accept_upload(&req.body, cfg.panel) {
        Ok(PanelImage { png, etag }) => {
            cfg.store.put(StoredFrame {
                png,
                etag: etag.clone(),
            });
            ApiResponse::json(
                200,
                format!(
                    r#"{{"ok":true,"etag":{}}}"#,
                    serde_json::to_string(&etag).unwrap()
                ),
            )
        }
        Err(e) => ApiResponse::text(400, format!("{e}\n")),
    }
}

fn etags_match(if_none_match: &str, etag: &str) -> bool {
    if_none_match.split(',').map(str::trim).any(|candidate| {
        candidate == "*" || candidate == etag || strip_weak(candidate) == strip_weak(etag)
    })
}

fn strip_weak(etag: &str) -> &str {
    etag.strip_prefix("W/").unwrap_or(etag)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::panel::{encode_bw_png, PanelSpec};
    use image::{GrayImage, Luma};

    struct MemStore(Option<StoredFrame>);
    impl FrameStore for MemStore {
        fn get(&self) -> Option<StoredFrame> {
            self.0.clone()
        }
        fn put(&mut self, frame: StoredFrame) {
            self.0 = Some(frame);
        }
    }

    fn solid_png() -> Vec<u8> {
        let img = GrayImage::from_pixel(800, 480, Luma([255]));
        encode_bw_png(&img, PanelSpec::default()).unwrap()
    }

    #[test]
    fn post_then_get_with_etag() {
        let mut store = MemStore(None);
        let mut cfg = HandlerConfig {
            store: &mut store,
            upload_secret: "secret",
            panel: PanelSpec::default(),
        };
        let post = handle(
            ApiRequest {
                method: "POST".into(),
                path: "/image.png".into(),
                authorization: Some("Bearer secret".into()),
                if_none_match: None,
                slack_timestamp: None,
                slack_signature: None,
                body: solid_png(),
            },
            &mut cfg,
        );
        assert_eq!(post.status, 200);

        let etag = cfg.store.get().unwrap().etag;
        let get = handle(
            ApiRequest {
                method: "GET".into(),
                path: "/image.png".into(),
                authorization: None,
                if_none_match: Some(etag),
                slack_timestamp: None,
                slack_signature: None,
                body: vec![],
            },
            &mut cfg,
        );
        assert_eq!(get.status, 304);
    }

    #[test]
    fn post_rejects_bad_auth() {
        let mut store = MemStore(None);
        let mut cfg = HandlerConfig {
            store: &mut store,
            upload_secret: "secret",
            panel: PanelSpec::default(),
        };
        let resp = handle(
            ApiRequest {
                method: "POST".into(),
                path: "/image.png".into(),
                authorization: Some("Bearer wrong".into()),
                if_none_match: None,
                slack_timestamp: None,
                slack_signature: None,
                body: solid_png(),
            },
            &mut cfg,
        );
        assert_eq!(resp.status, 401);
    }

    #[test]
    fn finish_mention_stores_transformed_image() {
        let mut src = GrayImage::new(100, 50);
        for (x, y, p) in src.enumerate_pixels_mut() {
            p.0 = [((x + y) % 256) as u8];
        }
        let mut src_png = Vec::new();
        image::DynamicImage::ImageLuma8(src)
            .write_to(
                &mut std::io::Cursor::new(&mut src_png),
                image::ImageFormat::Png,
            )
            .unwrap();

        let body = br#"{
            "type":"event_callback",
            "event":{
                "type":"app_mention",
                "user":"U1","text":"hi","ts":"1.0","channel":"C1",
                "files":[{"id":"F","name":"a.png","mimetype":"image/png",
                    "url_private_download":"https://example/a.png"}]
            }
        }"#;
        let SlackEvent::AppMention(mention) = slack::parse_event(body).unwrap() else {
            panic!("expected mention");
        };

        let mut store = MemStore(None);
        let reply = finish_app_mention(Some(Ok(src_png)), &mut store, PanelSpec::default());
        assert!(reply.contains("Displayed"));
        assert!(store.get().is_some());
        assert!(mention.first_image().is_some());
    }
}
