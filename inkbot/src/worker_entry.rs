//! Cloudflare Workers entry point (compiled only for `wasm32`).

use std::collections::BTreeMap;

use worker::js_sys::Uint8Array;
use worker::{
    event, Bucket, Context, Env, Fetch, Headers, Method, Request, RequestInit, Response, Result,
};

use crate::api::{
    self, begin_slack_event, finish_app_mention, ApiRequest, ApiResponse, Catalog, HandlerConfig,
    ImageStore, SlackBegin, StoredFrame,
};
use crate::auth::now_unix;
use crate::panel::PanelSpec;
use crate::slack;

const BUCKET_BINDING: &str = "IMAGES";
const CATALOG_KEY: &str = "catalog.json";
const FRAMES_PREFIX: &str = "frames/";

// Legacy single-image keys from before the multi-image library.
const LEGACY_PNG: &str = "image.png";
const LEGACY_BIN: &str = "image.bin";
const LEGACY_ETAG: &str = "image.etag";

#[event(fetch)]
async fn fetch(mut req: Request, env: Env, _ctx: Context) -> Result<Response> {
    let path = req.path();
    let method = req.method();

    if method == Method::Options {
        return into_worker_response(ApiResponse::text(204, ""));
    }

    let upload_secret = env
        .secret("UPLOAD_SECRET")
        .map(|s| s.to_string())
        .or_else(|_| env.var("UPLOAD_SECRET").map(|s| s.to_string()))
        .unwrap_or_default();

    let panel = PanelSpec::new(
        parse_u32_var(&env, "PANEL_WIDTH", crate::panel::DEFAULT_WIDTH),
        parse_u32_var(&env, "PANEL_HEIGHT", crate::panel::DEFAULT_HEIGHT),
    )
    .unwrap_or_default();

    let bucket = match env.bucket(BUCKET_BINDING) {
        Ok(b) => b,
        Err(_) => return text_response(500, "R2 bucket 'IMAGES' is not bound\n"),
    };

    let authorization = header_from(&req, "Authorization");
    let if_none_match = header_from(&req, "If-None-Match");
    let slack_timestamp = header_from(&req, "X-Slack-Request-Timestamp");
    let slack_signature = header_from(&req, "X-Slack-Signature");
    let body = req.bytes().await.unwrap_or_default();
    let api_req = ApiRequest {
        method: method.as_ref().to_string(),
        path: path.clone(),
        authorization,
        if_none_match,
        slack_timestamp,
        slack_signature,
        body,
    };

    if method == Method::Post && normalize_path(&path) == "/slack/events" {
        return handle_slack(api_req, &env, &bucket, panel).await;
    }

    let mut store = R2ImageStore::load(&bucket).await?;
    let mut cfg = HandlerConfig {
        store: &mut store,
        upload_secret: upload_secret.as_str(),
        panel,
    };
    let response = api::handle(api_req, &mut cfg);
    store.flush(&bucket).await?;
    into_worker_response(response)
}

async fn handle_slack(
    api_req: ApiRequest,
    env: &Env,
    bucket: &Bucket,
    panel: PanelSpec,
) -> Result<Response> {
    let signing = env
        .secret("SLACK_SIGNING_SECRET")
        .map(|s| s.to_string())
        .ok();
    let bot_token = env.secret("SLACK_BOT_TOKEN").map(|s| s.to_string()).ok();

    match begin_slack_event(&api_req, signing.as_deref(), now_unix()) {
        SlackBegin::Respond(resp) => into_worker_response(resp),
        SlackBegin::Mention(mention) => {
            let Some(token) = bot_token.filter(|t| !t.is_empty()) else {
                return text_response(503, "slack bot token not configured\n");
            };

            let image_bytes = match mention.first_image() {
                Some(file) => Some(download_slack_file(&token, &file.url_private_download).await),
                None => None,
            };

            let mut store = R2ImageStore::load(bucket).await?;
            let reply_text = finish_app_mention(&mention, image_bytes, &mut store, panel);
            store.flush(bucket).await?;

            if let Err(e) = post_slack_reply(
                &token,
                &mention.channel,
                mention.reply_thread_ts(),
                &reply_text,
            )
            .await
            {
                return text_response(502, &format!("slack reply failed: {e}\n"));
            }
            into_worker_response(ApiResponse::json(200, r#"{"ok":true}"#))
        }
    }
}

async fn download_slack_file(token: &str, url: &str) -> std::result::Result<Vec<u8>, String> {
    let headers = Headers::new();
    headers
        .set("Authorization", &format!("Bearer {token}"))
        .map_err(|e| e.to_string())?;
    let mut init = RequestInit::new();
    init.with_method(Method::Get).with_headers(headers);
    let request = Request::new_with_init(url, &init).map_err(|e| e.to_string())?;
    let mut resp = Fetch::Request(request)
        .send()
        .await
        .map_err(|e| e.to_string())?;
    if resp.status_code() < 200 || resp.status_code() >= 300 {
        return Err(format!("download HTTP {}", resp.status_code()));
    }
    resp.bytes().await.map_err(|e| e.to_string())
}

async fn post_slack_reply(
    token: &str,
    channel: &str,
    thread_ts: &str,
    text: &str,
) -> std::result::Result<(), String> {
    let payload = slack::reply_payload(channel, thread_ts, text).to_string();
    let headers = Headers::new();
    headers
        .set("Authorization", &format!("Bearer {token}"))
        .map_err(|e| e.to_string())?;
    headers
        .set("Content-Type", "application/json; charset=utf-8")
        .map_err(|e| e.to_string())?;
    let array = Uint8Array::new_with_length(payload.len() as u32);
    array.copy_from(payload.as_bytes());
    let mut init = RequestInit::new();
    init.with_method(Method::Post)
        .with_headers(headers)
        .with_body(Some(array.into()));
    let request = Request::new_with_init("https://slack.com/api/chat.postMessage", &init)
        .map_err(|e| e.to_string())?;
    let mut resp = Fetch::Request(request)
        .send()
        .await
        .map_err(|e| e.to_string())?;
    let body = resp.text().await.map_err(|e| e.to_string())?;
    let ok = serde_json::from_str::<serde_json::Value>(&body)
        .ok()
        .and_then(|v| v.get("ok").and_then(|o| o.as_bool()))
        .unwrap_or(false);
    if !ok {
        return Err(body);
    }
    Ok(())
}

struct R2ImageStore {
    frames: BTreeMap<String, StoredFrame>,
    catalog: Catalog,
    /// Names whose PNG+bin must be written on flush.
    dirty_names: BTreeMap<String, bool>, // true = upsert, false = delete
    catalog_dirty: bool,
}

impl R2ImageStore {
    async fn load(bucket: &Bucket) -> Result<Self> {
        let mut frames = BTreeMap::new();
        let mut catalog = match bucket.get(CATALOG_KEY).execute().await? {
            Some(obj) => {
                let bytes = obj
                    .body()
                    .ok_or_else(|| worker::Error::RustError("missing catalog body".into()))?
                    .bytes()
                    .await?;
                serde_json::from_slice(&bytes).unwrap_or_else(|_| Catalog::empty())
            }
            None => Catalog::empty(),
        };

        // Load each named frame listed in the catalog.
        for name in catalog.images.clone() {
            if let Some(frame) = load_frame(bucket, &name).await? {
                frames.insert(name, frame);
            }
        }

        let mut catalog_dirty = false;
        // Migrate legacy single-image objects into `image`.
        if frames.is_empty() {
            if let Some(frame) = load_legacy_frame(bucket).await? {
                catalog.revision = 1;
                catalog.latest = Some(frame.name.clone());
                catalog.images = vec![frame.name.clone()];
                frames.insert(frame.name.clone(), frame);
                catalog_dirty = true;
            }
        }

        // Reconcile catalog.images with what we actually loaded.
        catalog.images = frames.keys().cloned().collect();
        if let Some(latest) = &catalog.latest {
            if !frames.contains_key(latest) {
                catalog.latest = catalog.images.first().cloned();
                catalog_dirty = true;
            }
        }

        let dirty_names = if catalog_dirty {
            // Persist migrated legacy frame.
            frames.keys().map(|n| (n.clone(), true)).collect()
        } else {
            BTreeMap::new()
        };

        Ok(Self {
            frames,
            catalog,
            dirty_names,
            catalog_dirty,
        })
    }

    async fn flush(&self, bucket: &Bucket) -> Result<()> {
        for (name, upsert) in &self.dirty_names {
            if *upsert {
                let Some(frame) = self.frames.get(name) else {
                    continue;
                };
                bucket
                    .put(png_key(name), frame.png.clone())
                    .http_metadata(worker::HttpMetadata {
                        content_type: Some("image/png".into()),
                        ..Default::default()
                    })
                    .execute()
                    .await?;
                bucket
                    .put(bin_key(name), frame.packed.clone())
                    .http_metadata(worker::HttpMetadata {
                        content_type: Some("application/octet-stream".into()),
                        ..Default::default()
                    })
                    .execute()
                    .await?;
            } else {
                let _ = bucket.delete(png_key(name)).await;
                let _ = bucket.delete(bin_key(name)).await;
            }
        }
        if self.catalog_dirty || !self.dirty_names.is_empty() {
            let bytes = serde_json::to_vec(&self.catalog)
                .map_err(|e| worker::Error::RustError(format!("catalog encode: {e}")))?;
            bucket
                .put(CATALOG_KEY, bytes)
                .http_metadata(worker::HttpMetadata {
                    content_type: Some("application/json".into()),
                    ..Default::default()
                })
                .execute()
                .await?;
        }
        Ok(())
    }
}

impl ImageStore for R2ImageStore {
    fn catalog(&self) -> Catalog {
        self.catalog.clone()
    }

    fn get(&self, name: &str) -> Option<StoredFrame> {
        self.frames.get(name).cloned()
    }

    fn put(&mut self, frame: StoredFrame) {
        self.catalog.latest = Some(frame.name.clone());
        self.catalog.revision = self.catalog.revision.saturating_add(1);
        self.dirty_names.insert(frame.name.clone(), true);
        self.frames.insert(frame.name.clone(), frame);
        self.catalog.images = self.frames.keys().cloned().collect();
        self.catalog_dirty = true;
    }

    fn delete(&mut self, name: &str) -> bool {
        if self.frames.remove(name).is_none() {
            return false;
        }
        self.catalog.revision = self.catalog.revision.saturating_add(1);
        self.dirty_names.insert(name.to_string(), false);
        self.catalog.images = self.frames.keys().cloned().collect();
        if self.catalog.latest.as_deref() == Some(name) {
            self.catalog.latest = self.catalog.images.first().cloned();
        }
        self.catalog_dirty = true;
        true
    }
}

async fn load_frame(bucket: &Bucket, name: &str) -> Result<Option<StoredFrame>> {
    let png_obj = match bucket.get(png_key(name)).execute().await? {
        Some(o) => o,
        None => return Ok(None),
    };
    let png = png_obj
        .body()
        .ok_or_else(|| worker::Error::RustError("missing png body".into()))?
        .bytes()
        .await?;
    let packed = match bucket.get(bin_key(name)).execute().await? {
        Some(obj) => {
            obj.body()
                .ok_or_else(|| worker::Error::RustError("missing bin body".into()))?
                .bytes()
                .await?
        }
        None => crate::panel::packed_from_panel_png(&png, PanelSpec::default())
            .map_err(|e| worker::Error::RustError(format!("recover packed: {e}")))?,
    };
    let etag = crate::panel::etag_for(&png);
    Ok(Some(StoredFrame {
        name: name.to_string(),
        png,
        packed,
        etag,
    }))
}

async fn load_legacy_frame(bucket: &Bucket) -> Result<Option<StoredFrame>> {
    let Some(obj) = bucket.get(LEGACY_PNG).execute().await? else {
        return Ok(None);
    };
    let png = obj
        .body()
        .ok_or_else(|| worker::Error::RustError("missing legacy png".into()))?
        .bytes()
        .await?;
    let etag = match bucket.get(LEGACY_ETAG).execute().await? {
        Some(meta) => {
            let bytes = meta
                .body()
                .ok_or_else(|| worker::Error::RustError("missing legacy etag".into()))?
                .bytes()
                .await?;
            String::from_utf8(bytes).unwrap_or_else(|_| crate::panel::etag_for(&png))
        }
        None => crate::panel::etag_for(&png),
    };
    let packed = match bucket.get(LEGACY_BIN).execute().await? {
        Some(obj) => {
            obj.body()
                .ok_or_else(|| worker::Error::RustError("missing legacy bin".into()))?
                .bytes()
                .await?
        }
        None => crate::panel::packed_from_panel_png(&png, PanelSpec::default())
            .map_err(|e| worker::Error::RustError(format!("recover legacy packed: {e}")))?,
    };
    Ok(Some(StoredFrame {
        name: "image".into(),
        png,
        packed,
        etag,
    }))
}

fn png_key(name: &str) -> String {
    format!("{FRAMES_PREFIX}{name}.png")
}

fn bin_key(name: &str) -> String {
    format!("{FRAMES_PREFIX}{name}.bin")
}

fn header_from(req: &Request, name: &str) -> Option<String> {
    req.headers().get(name).ok().flatten()
}

fn parse_u32_var(env: &Env, name: &str, default: u32) -> u32 {
    env.var(name)
        .ok()
        .and_then(|v| v.to_string().trim().parse().ok())
        .filter(|n| *n > 0)
        .unwrap_or(default)
}

fn normalize_path(path: &str) -> String {
    let p = path.split('?').next().unwrap_or(path);
    if p.is_empty() {
        "/".into()
    } else {
        p.to_string()
    }
}

fn into_worker_response(response: ApiResponse) -> Result<Response> {
    let headers = Headers::new();
    headers.set("Content-Type", response.content_type)?;
    if let Some(etag) = &response.etag {
        headers.set("ETag", etag)?;
    }
    if let Some(cc) = response.cache_control {
        headers.set("Cache-Control", cc)?;
    }
    headers.set("Access-Control-Allow-Origin", "*")?;
    headers.set("Access-Control-Allow-Methods", "GET, POST, DELETE, OPTIONS")?;
    headers.set(
        "Access-Control-Allow-Headers",
        "Authorization, Content-Type, If-None-Match",
    )?;

    if response.status == 304 {
        return Ok(Response::empty()?.with_status(304).with_headers(headers));
    }

    Ok(Response::from_bytes(response.body)?
        .with_status(response.status)
        .with_headers(headers))
}

fn text_response(status: u16, body: &str) -> Result<Response> {
    into_worker_response(ApiResponse::text(status, body))
}
