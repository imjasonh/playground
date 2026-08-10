//! Transport-agnostic HTTP routing for inkbot.

use crate::auth::{authorize_upload, verify_slack_signature};
use crate::panel::{self, PanelImage, PanelSpec};
use crate::slack::{self, AppMention, SlackEvent};
use serde::{Deserialize, Serialize};

/// One named frame in the rotation library.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StoredFrame {
    pub name: String,
    pub png: Vec<u8>,
    /// Packed 1-bit framebuffer for the ESP32 (`/{name}.bin`).
    pub packed: Vec<u8>,
    pub etag: String,
}

/// Catalog returned by `GET /` — device polls this every minute.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Catalog {
    /// Monotonic counter bumped on every add/replace/delete.
    pub revision: u64,
    /// Most recently added/replaced image name (device shows this immediately).
    pub latest: Option<String>,
    /// All image names currently in the rotation (sorted).
    pub images: Vec<String>,
}

impl Catalog {
    pub fn empty() -> Self {
        Self {
            revision: 0,
            latest: None,
            images: Vec::new(),
        }
    }
}

/// Side-effectful image library. Unit tests use an in-memory fake.
pub trait ImageStore {
    fn catalog(&self) -> Catalog;
    fn get(&self, name: &str) -> Option<StoredFrame>;
    fn put(&mut self, frame: StoredFrame);
    fn delete(&mut self, name: &str) -> bool;
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

    pub fn packed(frame: &StoredFrame) -> Self {
        Self {
            status: 200,
            content_type: "application/octet-stream",
            body: frame.packed.clone(),
            etag: Some(frame.etag.clone()),
            cache_control: Some("no-cache"),
        }
    }

    pub fn not_modified(etag: &str) -> Self {
        Self {
            status: 304,
            content_type: "application/octet-stream",
            body: Vec::new(),
            etag: Some(etag.to_string()),
            cache_control: Some("no-cache"),
        }
    }
}

/// Config shared by the simple (non-Slack-I/O) routes.
pub struct HandlerConfig<'a, S: ImageStore> {
    pub store: &'a mut S,
    pub upload_secret: &'a str,
    pub panel: PanelSpec,
}

/// Route catalog / image CRUD and health checks. Slack Events are handled by
/// [`begin_slack_event`] + [`finish_app_mention`].
pub fn handle<S: ImageStore>(req: ApiRequest, cfg: &mut HandlerConfig<'_, S>) -> ApiResponse {
    let path = normalize_path(&req.path);
    let method = req.method.to_ascii_uppercase();

    match (method.as_str(), path.as_str()) {
        ("GET", "/") => list_catalog(cfg.store),
        ("GET", "/health") => ApiResponse::text(200, "inkbot ok\n"),
        ("OPTIONS", _) => ApiResponse::text(204, ""),
        (m, p) => match parse_image_path(p) {
            Some((name, kind)) => match (m, kind) {
                ("GET", ImageKind::Bin) => get_image_bin(&req, cfg.store, &name),
                ("GET", ImageKind::Png) => get_image_png(&req, cfg.store, &name),
                ("POST", ImageKind::Bin) | ("POST", ImageKind::Png) => post_image(&req, cfg, &name),
                ("DELETE", ImageKind::Bin) | ("DELETE", ImageKind::Png) => {
                    delete_image(&req, cfg, &name)
                }
                _ => ApiResponse::text(405, "method not allowed\n"),
            },
            None => ApiResponse::text(404, "not found\n"),
        },
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ImageKind {
    Bin,
    Png,
}

/// `/{name}.bin` or `/{name}.png` → validated name + kind.
fn parse_image_path(path: &str) -> Option<(String, ImageKind)> {
    let rest = path.strip_prefix('/')?;
    if rest.contains('/') {
        return None;
    }
    let (stem, kind) = if let Some(stem) = rest.strip_suffix(".bin") {
        (stem, ImageKind::Bin)
    } else if let Some(stem) = rest.strip_suffix(".png") {
        (stem, ImageKind::Png)
    } else {
        return None;
    };
    let name = validate_name(stem)?;
    Some((name, kind))
}

/// Image names: start with alphanumeric; then `[A-Za-z0-9_-]{0,62}`.
pub fn validate_name(raw: &str) -> Option<String> {
    let name = raw.trim();
    if name.is_empty() || name.len() > 63 {
        return None;
    }
    let mut chars = name.chars();
    let first = chars.next()?;
    if !first.is_ascii_alphanumeric() {
        return None;
    }
    if !chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-') {
        return None;
    }
    // Reserved route stems.
    match name {
        "health" | "slack" | "events" => None,
        _ => Some(name.to_string()),
    }
}

/// Sanitize a Slack/upload filename into a valid image name.
pub fn name_from_filename(filename: &str) -> String {
    let base = filename.rsplit('/').next().unwrap_or(filename);
    let stem = match base.rfind('.') {
        Some(i) if i > 0 => &base[..i],
        _ => base,
    };
    let mut out = String::new();
    for c in stem.chars() {
        if out.len() >= 63 {
            break;
        }
        if c.is_ascii_alphanumeric() {
            out.push(c.to_ascii_lowercase());
        } else if (c == '_' || c == '-' || c == ' ') && !out.is_empty() && !out.ends_with('-') {
            out.push('-');
        }
    }
    let out = out.trim_matches('-').to_string();
    if validate_name(&out).is_some() {
        out
    } else {
        "image".into()
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SlackCommand {
    List,
    Delete { name: String },
    AddImage { name: String },
    Help,
}

/// Parse `@inkbot …` text into a command. Leading `<@U…>` mentions are stripped.
pub fn parse_slack_command(text: &str, attachment_name: Option<&str>) -> SlackCommand {
    let stripped = strip_slack_mentions(text);
    let mut parts = stripped.split_whitespace();
    match parts.next().map(|s| s.to_ascii_lowercase()).as_deref() {
        Some("list") => SlackCommand::List,
        Some("delete") => {
            let raw = parts.next().unwrap_or("");
            let raw = raw.strip_suffix(".bin").unwrap_or(raw);
            let raw = raw.strip_suffix(".png").unwrap_or(raw);
            match validate_name(raw) {
                Some(name) => SlackCommand::Delete { name },
                None => SlackCommand::Help,
            }
        }
        Some("help") => SlackCommand::Help,
        _ => {
            if let Some(filename) = attachment_name {
                SlackCommand::AddImage {
                    name: name_from_filename(filename),
                }
            } else if stripped.is_empty() {
                SlackCommand::Help
            } else {
                // Bare mention with no attachment and unknown verb.
                SlackCommand::Help
            }
        }
    }
}

fn strip_slack_mentions(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while let Some(start) = rest.find("<@") {
        out.push_str(&rest[..start]);
        match rest[start..].find('>') {
            Some(end) => rest = &rest[start + end + 1..],
            None => {
                rest = &rest[start + 2..];
                break;
            }
        }
    }
    out.push_str(rest);
    out.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Handle a Slack mention after any attachment bytes have been downloaded.
pub fn finish_app_mention<S: ImageStore>(
    mention: &AppMention,
    image_bytes: Option<Result<Vec<u8>, String>>,
    store: &mut S,
    panel: PanelSpec,
) -> String {
    let attachment_name = mention.first_image().map(|f| f.name.as_str());
    let cmd = parse_slack_command(&mention.text, attachment_name);

    match cmd {
        SlackCommand::List => {
            let cat = store.catalog();
            if cat.images.is_empty() {
                "No images in the rotation yet. Attach a picture and mention me to add one.".into()
            } else {
                format!(
                    "Images ({}): {}\nLatest: {}",
                    cat.images.len(),
                    cat.images.join(", "),
                    cat.latest.as_deref().unwrap_or("—")
                )
            }
        }
        SlackCommand::Delete { name } => {
            if store.delete(&name) {
                format!("Deleted `{name}` from the rotation.")
            } else {
                format!("No image named `{name}`.")
            }
        }
        SlackCommand::Help => {
            "Commands: attach an image to add it · `list` · `delete <name>`".into()
        }
        SlackCommand::AddImage { name } => match image_bytes {
            None => "Attach an image and mention me — I'll dither it into the rotation.".into(),
            Some(Err(e)) => format!("Couldn't download the attachment: {e}"),
            Some(Ok(bytes)) => match panel::transform_for_panel(&bytes, panel) {
                Ok(PanelImage { png, packed, etag }) => {
                    store.put(StoredFrame {
                        name: name.clone(),
                        png,
                        packed,
                        etag: etag.clone(),
                    });
                    format!(
                        "Added `{name}` to the rotation ({}×{}, etag {}).",
                        panel.width, panel.height, etag
                    )
                }
                Err(e) => format!("Couldn't transform that image: {e}"),
            },
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

fn list_catalog<S: ImageStore>(store: &S) -> ApiResponse {
    let body = serde_json::to_string(&store.catalog()).unwrap_or_else(|_| "{}".into());
    ApiResponse::json(200, body)
}

fn get_image_png<S: ImageStore>(req: &ApiRequest, store: &S, name: &str) -> ApiResponse {
    let Some(frame) = store.get(name) else {
        return ApiResponse::text(404, "no such image\n");
    };
    if let Some(inm) = req.if_none_match.as_deref() {
        if etags_match(inm, &frame.etag) {
            return ApiResponse::not_modified(&frame.etag);
        }
    }
    ApiResponse::png(&frame)
}

fn get_image_bin<S: ImageStore>(req: &ApiRequest, store: &S, name: &str) -> ApiResponse {
    let Some(frame) = store.get(name) else {
        return ApiResponse::text(404, "no such image\n");
    };
    if let Some(inm) = req.if_none_match.as_deref() {
        if etags_match(inm, &frame.etag) {
            return ApiResponse::not_modified(&frame.etag);
        }
    }
    ApiResponse::packed(&frame)
}

fn post_image<S: ImageStore>(
    req: &ApiRequest,
    cfg: &mut HandlerConfig<'_, S>,
    name: &str,
) -> ApiResponse {
    if cfg.upload_secret.is_empty() {
        return ApiResponse::text(500, "UPLOAD_SECRET is not configured\n");
    }
    if !authorize_upload(req.authorization.as_deref(), cfg.upload_secret) {
        return ApiResponse::text(401, "unauthorized\n");
    }
    if req.body.is_empty() {
        return ApiResponse::text(400, "empty body\n");
    }
    // Accept either a strict panel PNG or an arbitrary photo (dithered).
    let panel_image = match panel::accept_upload(&req.body, cfg.panel) {
        Ok(img) => img,
        Err(_) => match panel::transform_for_panel(&req.body, cfg.panel) {
            Ok(img) => img,
            Err(e) => return ApiResponse::text(400, format!("{e}\n")),
        },
    };
    let PanelImage { png, packed, etag } = panel_image;
    cfg.store.put(StoredFrame {
        name: name.to_string(),
        png,
        packed,
        etag: etag.clone(),
    });
    ApiResponse::json(
        200,
        serde_json::json!({ "ok": true, "name": name, "etag": etag }).to_string(),
    )
}

fn delete_image<S: ImageStore>(
    req: &ApiRequest,
    cfg: &mut HandlerConfig<'_, S>,
    name: &str,
) -> ApiResponse {
    if cfg.upload_secret.is_empty() {
        return ApiResponse::text(500, "UPLOAD_SECRET is not configured\n");
    }
    if !authorize_upload(req.authorization.as_deref(), cfg.upload_secret) {
        return ApiResponse::text(401, "unauthorized\n");
    }
    if cfg.store.delete(name) {
        ApiResponse::json(
            200,
            serde_json::json!({ "ok": true, "deleted": name }).to_string(),
        )
    } else {
        ApiResponse::text(404, "no such image\n")
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
    use std::collections::BTreeMap;

    struct MemStore {
        frames: BTreeMap<String, StoredFrame>,
        revision: u64,
        latest: Option<String>,
    }

    impl MemStore {
        fn new() -> Self {
            Self {
                frames: BTreeMap::new(),
                revision: 0,
                latest: None,
            }
        }
    }

    impl ImageStore for MemStore {
        fn catalog(&self) -> Catalog {
            Catalog {
                revision: self.revision,
                latest: self.latest.clone(),
                images: self.frames.keys().cloned().collect(),
            }
        }
        fn get(&self, name: &str) -> Option<StoredFrame> {
            self.frames.get(name).cloned()
        }
        fn put(&mut self, frame: StoredFrame) {
            self.latest = Some(frame.name.clone());
            self.revision += 1;
            self.frames.insert(frame.name.clone(), frame);
        }
        fn delete(&mut self, name: &str) -> bool {
            if self.frames.remove(name).is_none() {
                return false;
            }
            self.revision += 1;
            if self.latest.as_deref() == Some(name) {
                self.latest = self.frames.keys().next().cloned();
            }
            true
        }
    }

    fn solid_png() -> Vec<u8> {
        let img = GrayImage::from_pixel(800, 480, Luma([255]));
        encode_bw_png(&img, PanelSpec::default()).unwrap().0
    }

    fn cfg<'a>(store: &'a mut MemStore) -> HandlerConfig<'a, MemStore> {
        HandlerConfig {
            store,
            upload_secret: "secret",
            panel: PanelSpec::default(),
        }
    }

    #[test]
    fn validate_and_sanitize_names() {
        assert_eq!(validate_name("sgt-pepper"), Some("sgt-pepper".into()));
        assert_eq!(validate_name("health"), None);
        assert_eq!(name_from_filename("Sgt Pepper!.PNG"), "sgt-pepper");
        assert_eq!(name_from_filename("a.png"), "a");
    }

    #[test]
    fn post_list_get_delete() {
        let mut store = MemStore::new();
        let mut c = cfg(&mut store);
        let post = handle(
            ApiRequest {
                method: "POST".into(),
                path: "/foo.bin".into(),
                authorization: Some("Bearer secret".into()),
                if_none_match: None,
                slack_timestamp: None,
                slack_signature: None,
                body: solid_png(),
            },
            &mut c,
        );
        assert_eq!(post.status, 200);

        let list = handle(
            ApiRequest {
                method: "GET".into(),
                path: "/".into(),
                authorization: None,
                if_none_match: None,
                slack_timestamp: None,
                slack_signature: None,
                body: vec![],
            },
            &mut c,
        );
        assert_eq!(list.status, 200);
        let cat: Catalog = serde_json::from_slice(&list.body).unwrap();
        assert_eq!(cat.images, vec!["foo".to_string()]);
        assert_eq!(cat.latest.as_deref(), Some("foo"));
        assert_eq!(cat.revision, 1);

        let bin = handle(
            ApiRequest {
                method: "GET".into(),
                path: "/foo.bin".into(),
                authorization: None,
                if_none_match: None,
                slack_timestamp: None,
                slack_signature: None,
                body: vec![],
            },
            &mut c,
        );
        assert_eq!(bin.status, 200);
        assert_eq!(bin.body.len(), 800 * 480 / 8);

        let del = handle(
            ApiRequest {
                method: "DELETE".into(),
                path: "/foo.bin".into(),
                authorization: Some("Bearer secret".into()),
                if_none_match: None,
                slack_timestamp: None,
                slack_signature: None,
                body: vec![],
            },
            &mut c,
        );
        assert_eq!(del.status, 200);
        assert!(c.store.catalog().images.is_empty());
    }

    #[test]
    fn post_rejects_bad_auth() {
        let mut store = MemStore::new();
        let mut c = cfg(&mut store);
        let resp = handle(
            ApiRequest {
                method: "POST".into(),
                path: "/foo.bin".into(),
                authorization: Some("Bearer wrong".into()),
                if_none_match: None,
                slack_timestamp: None,
                slack_signature: None,
                body: solid_png(),
            },
            &mut c,
        );
        assert_eq!(resp.status, 401);
    }

    #[test]
    fn slack_commands() {
        assert_eq!(
            parse_slack_command("<@Ubot> list", None),
            SlackCommand::List
        );
        assert_eq!(
            parse_slack_command("<@Ubot> delete sgt-pepper.bin", None),
            SlackCommand::Delete {
                name: "sgt-pepper".into()
            }
        );
        assert_eq!(
            parse_slack_command("<@Ubot> look", Some("Abbey Road.png")),
            SlackCommand::AddImage {
                name: "abbey-road".into()
            }
        );
    }

    #[test]
    fn finish_mention_list_and_add() {
        let mut store = MemStore::new();
        let body = br#"{
            "type":"event_callback",
            "event":{
                "type":"app_mention",
                "user":"U1","text":"<@Ubot> list","ts":"1.0","channel":"C1"
            }
        }"#;
        let SlackEvent::AppMention(mention) = slack::parse_event(body).unwrap() else {
            panic!("expected mention");
        };
        let reply = finish_app_mention(&mention, None, &mut store, PanelSpec::default());
        assert!(reply.contains("No images"));

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
                "user":"U1","text":"<@Ubot>","ts":"1.0","channel":"C1",
                "files":[{"id":"F","name":"a.png","mimetype":"image/png",
                    "url_private_download":"https://example/a.png"}]
            }
        }"#;
        let SlackEvent::AppMention(mention) = slack::parse_event(body).unwrap() else {
            panic!("expected mention");
        };
        let reply = finish_app_mention(
            &mention,
            Some(Ok(src_png)),
            &mut store,
            PanelSpec::default(),
        );
        assert!(reply.contains("Added `a`"));
        assert_eq!(store.catalog().images, vec!["a".to_string()]);
    }
}
