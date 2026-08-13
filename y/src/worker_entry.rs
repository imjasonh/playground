//! Cloudflare Workers entry point (compiled only for `wasm32`).
//!
//! Thin glue: D1 for posts/subscribers/credentials, R2 for images, signed
//! cookies for admin auth. HTML and WebAuthn live in the host-tested modules.

use serde::Deserialize;
use worker::d1::D1Database;
use worker::wasm_bindgen::JsValue;
use worker::{
    event, Bucket, Context, Env, FormEntry, Headers, Method, Request, Response, Result,
    SendEmailBuilder,
};

use crate::auth::{
    challenge_cookie_header, clear_cookie_header, make_challenge_cookie, make_session_cookie,
    session_cookie_header, verify_challenge_cookie, verify_password, verify_session_cookie,
    CHALLENGE_COOKIE, SESSION_COOKIE,
};
use crate::html::{
    admin_compose, edit_page, grouped_has_images, image_ext_for, index_view, is_allowed_image_type,
    is_valid_email, login_page, passkeys_page, post_view, rss_feed, subscribe_form,
    subscribe_thanks, unsubscribe_confirm, unsubscribe_done, validate_post_body, Post, PostImage,
    PAPERCLIP_KEY,
};
use crate::policy;
use crate::route::{self, Route};
use crate::webauthn::{
    authentication_options, registration_options, verify_authentication, verify_registration,
    AuthenticationResponse, Credential, RegistrationResponse, RpContext,
};

const PAPERCLIP_PNG: &[u8] = include_bytes!("../paperclip.png");

struct Site {
    title: String,
    url: String,
    session_secret: String,
    password_hash: String,
    mail_from: String,
}

impl Site {
    fn from_env(env: &Env) -> Result<Self> {
        let session_secret = env
            .secret("SESSION_SECRET")
            .map(|v| v.to_string())
            .unwrap_or_default();
        policy::require_session_secret(&session_secret).map_err(worker::Error::RustError)?;
        let password_hash = env
            .secret("ADMIN_PASSWORD_HASH")
            .map(|v| v.to_string())
            .unwrap_or_default();
        policy::require_password_hash(&password_hash).map_err(worker::Error::RustError)?;
        Ok(Self {
            title: env
                .var("SITE_TITLE")
                .map(|v| v.to_string())
                .unwrap_or_else(|_| "y".into()),
            url: env
                .var("SITE_URL")
                .map(|v| v.to_string())
                .unwrap_or_else(|_| "https://y.imjasonh.workers.dev".into()),
            session_secret,
            password_hash,
            mail_from: env
                .var("MAIL_FROM")
                .map(|v| v.to_string())
                .unwrap_or_default(),
        })
    }

    fn rp(&self) -> std::result::Result<RpContext, String> {
        RpContext::from_site(&self.url, &self.title)
    }

    fn origin(&self) -> std::result::Result<String, String> {
        Ok(self.rp()?.origin)
    }
}

#[event(fetch)]
async fn fetch(req: Request, env: Env, ctx: Context) -> Result<Response> {
    match handle_fetch(req, env, ctx).await {
        Ok(resp) => apply_security(resp),
        Err(e) => {
            worker::console_error!("{}", e);
            apply_security(text(500, "internal error")?)
        }
    }
}

/// Every minute: email subscribers about posts whose 1-minute undo window ended.
#[event(scheduled)]
async fn scheduled(_event: worker::ScheduledEvent, env: Env, _ctx: worker::ScheduleContext) {
    if let Err(e) = send_due_notifications(&env).await {
        worker::console_error!("notify: {e}");
    }
}

fn apply_security(resp: Response) -> Result<Response> {
    for (name, value) in policy::security_headers() {
        resp.headers().set(name, value)?;
    }
    Ok(resp)
}

async fn handle_fetch(mut req: Request, env: Env, _ctx: Context) -> Result<Response> {
    let method = req.method();
    let url = req.url()?;
    let path = url.path().to_string();
    let site = Site::from_env(&env)?;
    let db = env.d1("DB")?;
    let images = env.bucket("IMAGES")?;
    let now = js_now() as u64;

    let Some(route) = route::parse(method.as_ref(), &path) else {
        return text(404, "not found");
    };

    if method == Method::Post && route != Route::Unsubscribe {
        let site_origin = site.origin().map_err(worker::Error::RustError)?;
        let req_origin = url.origin().ascii_serialization();
        let origin = req.headers().get("Origin").ok().flatten();
        let referer = req.headers().get("Referer").ok().flatten();
        if !policy::origin_allowed_any(
            &[&site_origin, &req_origin],
            origin.as_deref(),
            referer.as_deref(),
        ) {
            return text(403, "bad origin");
        }
    }

    match route {
        Route::Home => handle_home(&req, &db, &site, now).await,
        Route::Post { id } => handle_post(&req, &db, &site, now, id).await,
        Route::Feed => handle_feed(&db, &site, now).await,
        Route::Image { key } => handle_image(&images, &key).await,
        Route::Subscribe if method == Method::Get => Ok(html(200, subscribe_form(&site.title))?),
        Route::Subscribe => handle_subscribe_post(&mut req, &db, &site, now).await,
        Route::Unsubscribe if method == Method::Get => {
            handle_unsubscribe_get(&req, &db, &site).await
        }
        Route::Unsubscribe => handle_unsubscribe_post(&req, &db, &site).await,
        Route::AdminLogin if method == Method::Get => handle_login_get(&req, &db, &site, now).await,
        Route::AdminLogin => handle_login_post(&mut req, &db, &site, now).await,
        Route::LoginPasskeyOptions => handle_login_passkey_options(&req, &db, &site, now).await,
        Route::LoginPasskeyVerify => handle_login_passkey_verify(&mut req, &db, &site, now).await,
        Route::AdminLogout => {
            if !logged_in(&req, &site, now) {
                return redirect("/admin/login");
            }
            let resp = redirect("/")?;
            clear_cookie(resp.headers(), SESSION_COOKIE, "/")?;
            Ok(resp)
        }
        Route::Admin => {
            if !logged_in(&req, &site, now) {
                return redirect("/admin/login");
            }
            handle_admin_get(&req, &db, &site).await
        }
        Route::AdminPasskeys => {
            if !logged_in(&req, &site, now) {
                return redirect("/admin/login");
            }
            handle_passkeys_get(&req, &db, &site).await
        }
        Route::AdminPasskeyRegisterOptions => {
            if !logged_in(&req, &site, now) {
                return redirect("/admin/login");
            }
            handle_register_options(&req, &db, &site, now).await
        }
        Route::AdminPasskeyRegisterVerify => {
            if !logged_in(&req, &site, now) {
                return redirect("/admin/login");
            }
            handle_register_verify(&mut req, &db, &site, now).await
        }
        Route::AdminPasskeyDelete { id } => {
            if !logged_in(&req, &site, now) {
                return redirect("/admin/login");
            }
            handle_delete_passkey(&db, id).await
        }
        Route::AdminPosts => {
            if !logged_in(&req, &site, now) {
                return redirect("/admin/login");
            }
            handle_create_post(&mut req, &db, &images, now).await
        }
        Route::AdminPostDelete { id } => {
            if !logged_in(&req, &site, now) {
                return redirect("/admin/login");
            }
            handle_delete_post(&db, &images, id).await
        }
        Route::AdminPostEdit { id } if method == Method::Get => {
            if !logged_in(&req, &site, now) {
                return redirect("/admin/login");
            }
            handle_edit_get(&db, &site, id).await
        }
        Route::AdminPostEdit { id } => {
            if !logged_in(&req, &site, now) {
                return redirect("/admin/login");
            }
            handle_edit_post(&mut req, &db, id).await
        }
    }
}

fn js_now() -> f64 {
    worker::js_sys::Date::now() / 1000.0
}

fn logged_in(req: &Request, site: &Site, now: u64) -> bool {
    verify_session_cookie(
        &site.session_secret,
        cookie(req, SESSION_COOKIE).as_deref(),
        now,
    )
}

fn cookie(req: &Request, name: &str) -> Option<String> {
    let header = req.headers().get("Cookie").ok().flatten()?;
    for part in header.split(';') {
        let part = part.trim();
        if let Some((k, v)) = part.split_once('=') {
            if k == name {
                return Some(v.to_string());
            }
        }
    }
    None
}

fn client_ip(req: &Request) -> String {
    req.headers()
        .get("CF-Connecting-IP")
        .ok()
        .flatten()
        .or_else(|| {
            req.headers()
                .get("X-Forwarded-For")
                .ok()
                .flatten()
                .and_then(|s| s.split(',').next().map(|p| p.trim().to_string()))
                .filter(|s| !s.is_empty())
        })
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "unknown".into())
}

fn query(req: &Request, name: &str) -> Option<String> {
    req.url()
        .ok()?
        .query_pairs()
        .find(|(k, _)| k == name)
        .map(|(_, v)| v.into_owned())
}

fn text(status: u16, body: &str) -> Result<Response> {
    let headers = Headers::new();
    headers.set("Content-Type", "text/plain; charset=utf-8")?;
    Ok(Response::from_bytes(body.as_bytes().to_vec())?
        .with_status(status)
        .with_headers(headers))
}

fn html(status: u16, body: String) -> Result<Response> {
    let headers = Headers::new();
    headers.set("Content-Type", "text/html; charset=utf-8")?;
    Ok(Response::from_bytes(body.into_bytes())?
        .with_status(status)
        .with_headers(headers))
}

fn json(status: u16, body: impl Into<String>) -> Result<Response> {
    let headers = Headers::new();
    headers.set("Content-Type", "application/json")?;
    Ok(Response::from_bytes(body.into().into_bytes())?
        .with_status(status)
        .with_headers(headers))
}

fn redirect(location: &str) -> Result<Response> {
    let headers = Headers::new();
    headers.set("Location", location)?;
    Ok(Response::empty()?.with_status(302).with_headers(headers))
}

fn set_cookie(headers: &Headers, cookie: &str) -> Result<()> {
    headers.append("Set-Cookie", cookie)
}

fn clear_cookie(headers: &Headers, name: &str, path: &str) -> Result<()> {
    headers.append("Set-Cookie", &clear_cookie_header(name, path))
}

fn with_cleared_challenge(resp: Response) -> Result<Response> {
    clear_cookie(resp.headers(), CHALLENGE_COOKIE, "/admin")?;
    Ok(resp)
}

fn is_unique_violation(err: &worker::Error) -> bool {
    let s = err.to_string().to_ascii_lowercase();
    s.contains("unique") || s.contains("constraint")
}

async fn handle_home(req: &Request, db: &D1Database, site: &Site, now: u64) -> Result<Response> {
    let before = query(req, "before").and_then(|s| policy::parse_js_safe_id(&s));
    let posts = list_head_posts(db, 50, before).await?;
    let ids: Vec<i64> = posts.iter().map(|p| p.id).collect();
    let images = images_for_posts(db, &ids).await?;
    let replies = total_replies_by_head(db, &ids).await?;
    let page = index_view(
        &site.title,
        &site.url,
        &posts,
        &images,
        logged_in(req, site, now),
        &replies,
    );
    html(200, page)
}

async fn handle_post(
    req: &Request,
    db: &D1Database,
    site: &Site,
    now: u64,
    id: i64,
) -> Result<Response> {
    let Some(post) = get_post(db, id).await? else {
        return text(404, "not found");
    };
    let thread = get_thread(db, id).await?;
    let thread_posts = thread
        .as_ref()
        .map(|t| t.posts.clone())
        .unwrap_or_else(|| vec![post.clone()]);
    let head_id = thread.as_ref().map(|t| t.head.id).unwrap_or(post.id);
    let ids: Vec<i64> = thread_posts.iter().map(|p| p.id).collect();
    let images = images_for_posts(db, &ids).await?;
    let page = post_view(
        &site.title,
        &site.url,
        &post,
        &thread_posts,
        &images,
        logged_in(req, site, now),
        head_id,
    );
    html(200, page)
}

async fn handle_feed(db: &D1Database, site: &Site, now: u64) -> Result<Response> {
    let posts = list_all_posts(db, 50).await?;
    let ids: Vec<i64> = posts.iter().map(|p| p.id).collect();
    let images = images_for_posts(db, &ids).await?;
    let body = rss_feed(&site.title, &site.url, &posts, &images, now as i64);
    let headers = Headers::new();
    headers.set("Content-Type", "application/rss+xml; charset=utf-8")?;
    headers.set("Cache-Control", "public, max-age=300")?;
    Ok(Response::from_bytes(body.into_bytes())?
        .with_status(200)
        .with_headers(headers))
}

async fn handle_image(bucket: &Bucket, key: &str) -> Result<Response> {
    if !policy::is_allowed_image_key(key) {
        return text(404, "not found");
    }
    if let Some(obj) = bucket.get(key).execute().await? {
        let headers = Headers::new();
        if let Some(ct) = obj.http_metadata().content_type {
            headers.set("Content-Type", &ct)?;
        }
        headers.set("etag", &obj.http_etag())?;
        headers.set("Cache-Control", "public, max-age=31536000, immutable")?;
        let Some(body) = obj.body() else {
            return text(404, "not found");
        };
        return Ok(Response::from_body(body.response_body()?)?.with_headers(headers));
    }
    if key == PAPERCLIP_KEY {
        let headers = Headers::new();
        headers.set("Content-Type", "image/png")?;
        headers.set("etag", "\"paperclip\"")?;
        headers.set("Cache-Control", "public, max-age=31536000, immutable")?;
        return Ok(Response::from_bytes(PAPERCLIP_PNG.to_vec())?.with_headers(headers));
    }
    text(404, "not found")
}

async fn handle_subscribe_post(
    req: &mut Request,
    db: &D1Database,
    site: &Site,
    now: u64,
) -> Result<Response> {
    let ip = client_ip(req);
    let key = format!("subscribe:{ip}");
    if !rate_allow(
        db,
        &key,
        now,
        policy::SUBSCRIBE_RATE_WINDOW_SECS,
        policy::SUBSCRIBE_RATE_MAX,
    )
    .await?
    {
        return text(429, "too many attempts");
    }
    let form = match req.form_data().await {
        Ok(f) => f,
        Err(_) => return text(400, "invalid form"),
    };
    let email = form
        .get_field("email")
        .unwrap_or_default()
        .trim()
        .to_lowercase();
    if !is_valid_email(&email) {
        return text(400, "invalid email");
    }
    insert_interested(
        db,
        &email,
        now as i64,
        &crate::notify::new_subscriber_token(),
    )
    .await?;
    html(200, subscribe_thanks(&site.title))
}

async fn handle_unsubscribe_get(req: &Request, db: &D1Database, site: &Site) -> Result<Response> {
    let Some(token) = unsubscribe_token(req) else {
        return text(400, "missing token");
    };
    if !subscriber_token_exists(db, &token).await? {
        return text(404, "not found");
    }
    html(200, unsubscribe_confirm(&site.title, &token))
}

async fn handle_unsubscribe_post(req: &Request, db: &D1Database, site: &Site) -> Result<Response> {
    let Some(token) = unsubscribe_token(req) else {
        return text(400, "missing token");
    };
    if !unsubscribe_by_token(db, &token).await? {
        return text(404, "not found");
    }
    html(200, unsubscribe_done(&site.title))
}

fn unsubscribe_token(req: &Request) -> Option<String> {
    query(req, "token").filter(|t| !t.is_empty())
}

async fn handle_login_get(
    req: &Request,
    db: &D1Database,
    site: &Site,
    _now: u64,
) -> Result<Response> {
    let count = count_credentials(db).await?;
    let bootstrap = count == 0;
    let err = query(req, "err").is_some();
    html(200, login_page(&site.title, bootstrap, err))
}

async fn handle_login_post(
    req: &mut Request,
    db: &D1Database,
    site: &Site,
    now: u64,
) -> Result<Response> {
    if count_credentials(db).await? > 0 {
        return text(403, "password login disabled");
    }
    let ip = client_ip(req);
    let key = format!("login:{ip}");
    if rate_exceeded(
        db,
        &key,
        now,
        policy::LOGIN_RATE_WINDOW_SECS,
        policy::LOGIN_RATE_MAX,
    )
    .await?
    {
        return text(429, "too many attempts");
    }
    let form = match req.form_data().await {
        Ok(f) => f,
        Err(_) => return text(400, "invalid form"),
    };
    let password = form.get_field("password").unwrap_or_default();
    if !verify_password(&password, &site.password_hash) {
        rate_record(db, &key, now).await?;
        return redirect("/admin/login?err=1");
    }
    let value = make_session_cookie(&site.session_secret, now);
    let resp = redirect("/admin/passkeys?bootstrap=1")?;
    set_cookie(resp.headers(), &session_cookie_header(&value))?;
    Ok(resp)
}

async fn handle_login_passkey_options(
    req: &Request,
    db: &D1Database,
    site: &Site,
    now: u64,
) -> Result<Response> {
    let ip = client_ip(req);
    if !rate_allow(
        db,
        &format!("pkopt:{ip}"),
        now,
        policy::OPTIONS_RATE_WINDOW_SECS,
        policy::OPTIONS_RATE_MAX,
    )
    .await?
    {
        return text(429, "too many attempts");
    }
    let rp = match site.rp() {
        Ok(r) => r,
        Err(e) => return Err(worker::Error::RustError(e)),
    };
    let creds = list_credentials(db).await?;
    let opts = authentication_options(&rp, &creds);
    let challenge = opts
        .get("challenge")
        .and_then(|v| v.as_str())
        .unwrap_or("")
        .to_string();
    let cookie = make_challenge_cookie(&site.session_secret, &challenge, now);
    let resp = json(200, opts.to_string())?;
    set_cookie(resp.headers(), &challenge_cookie_header(&cookie))?;
    Ok(resp)
}

async fn take_challenge(
    req: &Request,
    db: &D1Database,
    site: &Site,
    now: u64,
) -> Result<std::result::Result<String, Response>> {
    let expected = verify_challenge_cookie(
        &site.session_secret,
        cookie(req, CHALLENGE_COOKIE).as_deref(),
        now,
    );
    let Some(expected) = expected else {
        worker::console_error!("webauthn: challenge cookie missing or invalid");
        return Ok(Err(with_cleared_challenge(text(
            400,
            "challenge expired",
        )?)?));
    };
    if !consume_challenge(db, &expected, now).await? {
        worker::console_error!("webauthn: challenge already used");
        return Ok(Err(with_cleared_challenge(text(
            400,
            "challenge expired",
        )?)?));
    }
    Ok(Ok(expected))
}

async fn handle_login_passkey_verify(
    req: &mut Request,
    db: &D1Database,
    site: &Site,
    now: u64,
) -> Result<Response> {
    let expected = match take_challenge(req, db, site, now).await? {
        Ok(c) => c,
        Err(resp) => return Ok(resp),
    };
    let body = req.text().await.unwrap_or_default();
    if policy::json_body_too_large(body.len()) {
        return with_cleared_challenge(text(400, "payload too large")?);
    }
    let parsed: AuthenticationResponse = match serde_json::from_str(&body) {
        Ok(v) => v,
        Err(_) => return with_cleared_challenge(text(400, "invalid json")?),
    };
    let rp = match site.rp() {
        Ok(r) => r,
        Err(e) => {
            worker::console_error!("{}", e);
            return with_cleared_challenge(text(500, "internal error")?);
        }
    };
    let Some(stored) = find_credential(db, &parsed.id).await? else {
        return with_cleared_challenge(text(400, "unknown credential")?);
    };
    match verify_authentication(&rp, &expected, &stored, &parsed) {
        Ok(info) => {
            if !update_counter(db, &stored.id, info.new_counter).await? {
                return with_cleared_challenge(text(
                    400,
                    "authenticator counter did not increase",
                )?);
            }
            let value = make_session_cookie(&site.session_secret, now);
            let resp = json(200, r#"{"ok":true}"#)?;
            set_cookie(resp.headers(), &session_cookie_header(&value))?;
            with_cleared_challenge(resp)
        }
        Err(e) => with_cleared_challenge(text(400, &e)?),
    }
}

async fn handle_admin_get(req: &Request, db: &D1Database, site: &Site) -> Result<Response> {
    let reply_to = match query(req, "reply_to").and_then(|s| policy::parse_js_safe_id(&s)) {
        Some(id) => get_post(db, id).await?,
        None => None,
    };
    let interest = count_interested(db).await?;
    html(200, admin_compose(&site.title, reply_to.as_ref(), interest))
}

async fn handle_passkeys_get(req: &Request, db: &D1Database, site: &Site) -> Result<Response> {
    let rows = list_credential_rows(db).await?;
    let bootstrap = query(req, "bootstrap").as_deref() == Some("1");
    html(200, passkeys_page(&site.title, &rows, bootstrap))
}

async fn handle_register_options(
    req: &Request,
    db: &D1Database,
    site: &Site,
    now: u64,
) -> Result<Response> {
    let ip = client_ip(req);
    if !rate_allow(
        db,
        &format!("pkreg:{ip}"),
        now,
        policy::OPTIONS_RATE_WINDOW_SECS,
        policy::OPTIONS_RATE_MAX,
    )
    .await?
    {
        return text(429, "too many attempts");
    }
    let rp = match site.rp() {
        Ok(r) => r,
        Err(e) => return Err(worker::Error::RustError(e)),
    };
    let creds = list_credentials(db).await?;
    let opts = registration_options(&rp, &creds);
    let challenge = opts
        .get("challenge")
        .and_then(|v| v.as_str())
        .unwrap_or("")
        .to_string();
    let cookie = make_challenge_cookie(&site.session_secret, &challenge, now);
    let resp = json(200, opts.to_string())?;
    set_cookie(resp.headers(), &challenge_cookie_header(&cookie))?;
    Ok(resp)
}

#[derive(Deserialize)]
struct RegisterBody {
    label: Option<String>,
    response: RegistrationResponse,
}

async fn handle_register_verify(
    req: &mut Request,
    db: &D1Database,
    site: &Site,
    now: u64,
) -> Result<Response> {
    let expected = match take_challenge(req, db, site, now).await? {
        Ok(c) => c,
        Err(resp) => return Ok(resp),
    };
    let body = req.text().await.unwrap_or_default();
    if policy::json_body_too_large(body.len()) {
        return with_cleared_challenge(text(400, "payload too large")?);
    }
    let parsed: RegisterBody = match serde_json::from_str(&body) {
        Ok(v) => v,
        Err(_) => return with_cleared_challenge(text(400, "invalid json")?),
    };
    let rp = match site.rp() {
        Ok(r) => r,
        Err(e) => {
            worker::console_error!("{}", e);
            return with_cleared_challenge(text(500, "internal error")?);
        }
    };
    match verify_registration(&rp, &expected, &parsed.response) {
        Ok(info) => {
            let label = crate::html::passkey_label(parsed.label.as_deref());
            match insert_credential(
                db,
                &info.credential_id,
                &info.public_key,
                info.counter,
                info.transports.as_ref().map(|t| t.join(",")),
                &label,
                now as i64,
            )
            .await
            {
                Ok(()) => with_cleared_challenge(json(200, r#"{"ok":true}"#)?),
                Err(e) if is_unique_violation(&e) => {
                    with_cleared_challenge(text(400, "duplicate passkey")?)
                }
                Err(e) => Err(e),
            }
        }
        Err(e) => with_cleared_challenge(text(400, &e)?),
    }
}

async fn handle_delete_passkey(db: &D1Database, id: i64) -> Result<Response> {
    let n = count_credentials(db).await?;
    if !policy::can_delete_passkey(n) {
        return text(400, "cannot delete the last passkey");
    }
    delete_credential(db, id).await?;
    redirect("/admin/passkeys")
}

async fn handle_create_post(
    req: &mut Request,
    db: &D1Database,
    bucket: &Bucket,
    now: u64,
) -> Result<Response> {
    let form = match req.form_data().await {
        Ok(f) => f,
        Err(_) => return text(400, "invalid multipart"),
    };
    let body = form
        .get_field("body")
        .unwrap_or_default()
        .trim()
        .to_string();
    let mut files: Vec<(String, Vec<u8>)> = Vec::new();
    let mut total: u64 = 0;
    if let Some(entries) = form.get_all("image") {
        for entry in entries {
            if let FormEntry::File(f) = entry {
                let size = f.size() as u64;
                if size == 0 {
                    continue;
                }
                if let Err(msg) = policy::check_image_upload(files.len(), size, total) {
                    return text(400, &msg);
                }
                let ty = f.type_();
                if !is_allowed_image_type(&ty) {
                    return text(400, &format!("unsupported image type: {ty}"));
                }
                files.push((ty, f.bytes().await?));
                total += size;
            }
        }
    }
    if let Err(msg) = validate_post_body(&body, !files.is_empty()) {
        return text(400, &msg);
    }
    let parent_id = match form.get_field("parent_id") {
        Some(s) if !s.is_empty() => {
            let Some(n) = policy::parse_js_safe_id(&s) else {
                return text(400, "bad parent_id");
            };
            if get_post(db, n).await?.is_none() {
                return text(400, "parent post not found");
            }
            Some(n)
        }
        _ => None,
    };
    let post_id = insert_post(
        db,
        &body,
        now as i64,
        parent_id,
        crate::notify::notify_at(now as i64),
    )
    .await?;
    let mut uploaded: Vec<String> = Vec::new();
    for (i, (ty, bytes)) in files.into_iter().enumerate() {
        let ext = image_ext_for(&ty).unwrap_or("bin");
        let key = format!("{post_id}/{i}.{ext}");
        if let Err(e) = bucket
            .put(&key, bytes)
            .http_metadata(worker::HttpMetadata {
                content_type: Some(ty.clone()),
                ..Default::default()
            })
            .execute()
            .await
        {
            cleanup_failed_create(db, bucket, post_id, &uploaded).await;
            return Err(e);
        }
        uploaded.push(key.clone());
        if let Err(e) = insert_post_image(db, post_id, &key, &ty, i as i64).await {
            cleanup_failed_create(db, bucket, post_id, &uploaded).await;
            return Err(e);
        }
    }
    redirect(&format!("/admin?reply_to={post_id}"))
}

async fn cleanup_failed_create(db: &D1Database, bucket: &Bucket, post_id: i64, keys: &[String]) {
    for key in keys {
        let _ = bucket.delete(key).await;
    }
    if let Ok(stmt) = db
        .prepare("DELETE FROM posts WHERE id = ?1")
        .bind(&[JsValue::from_f64(post_id as f64)])
    {
        let _ = stmt.run().await;
    }
}

async fn handle_delete_post(db: &D1Database, bucket: &Bucket, id: i64) -> Result<Response> {
    let imgs = images_for_posts(db, &[id]).await?;
    let keys: Vec<String> = imgs
        .into_iter()
        .flat_map(|(_, v)| v.into_iter().map(|i| i.r2_key))
        .collect();
    for key in &keys {
        bucket.delete(key).await?;
    }
    db.prepare("DELETE FROM posts WHERE id = ?1")
        .bind(&[JsValue::from_f64(id as f64)])?
        .run()
        .await?;
    redirect("/admin")
}

async fn handle_edit_get(db: &D1Database, site: &Site, id: i64) -> Result<Response> {
    let Some(post) = get_post(db, id).await? else {
        return text(404, "not found");
    };
    html(200, edit_page(&site.title, &post))
}

async fn handle_edit_post(req: &mut Request, db: &D1Database, id: i64) -> Result<Response> {
    if get_post(db, id).await?.is_none() {
        return text(404, "not found");
    }
    let form = match req.form_data().await {
        Ok(f) => f,
        Err(_) => return text(400, "invalid form"),
    };
    let body = form
        .get_field("body")
        .unwrap_or_default()
        .trim()
        .to_string();
    let grouped = images_for_posts(db, &[id]).await?;
    if let Err(msg) = validate_post_body(&body, grouped_has_images(&grouped, id)) {
        return text(400, &msg);
    }
    let result = db
        .prepare("UPDATE posts SET body = ?1 WHERE id = ?2")
        .bind(&[JsValue::from_str(&body), JsValue::from_f64(id as f64)])?
        .run()
        .await?;
    let changes = result.meta()?.and_then(|m| m.changes).unwrap_or(0);
    if changes == 0 {
        return text(404, "not found");
    }
    redirect(&format!("/post/{id}"))
}

// ---- D1 ----

#[derive(Deserialize)]
struct PostRow {
    id: i64,
    body: String,
    created_at: i64,
    parent_id: Option<i64>,
}

impl From<PostRow> for Post {
    fn from(r: PostRow) -> Self {
        Post {
            id: r.id,
            body: r.body,
            created_at: r.created_at,
            parent_id: r.parent_id,
        }
    }
}

#[derive(Deserialize)]
struct ImageRow {
    id: i64,
    post_id: i64,
    r2_key: String,
    content_type: String,
    width: Option<i64>,
    height: Option<i64>,
    alt: Option<String>,
    ordinal: i64,
}

#[derive(Deserialize)]
struct CountRow {
    n: i64,
}

#[derive(Deserialize)]
struct IdRow {
    id: i64,
}

#[derive(Deserialize)]
struct ChallengeClaimRow {
    challenge: String,
}

#[derive(Deserialize)]
struct ReplyRow {
    head: i64,
    reply_count: i64,
}

#[derive(Deserialize)]
struct CredRow {
    id: i64,
    credential_id: String,
    public_key_hex: String,
    counter: i64,
    transports: Option<String>,
    label: String,
    created_at: i64,
}

const POST_COLS: &str = "id, body, created_at, parent_id";

async fn list_head_posts(db: &D1Database, limit: i64, before: Option<i64>) -> Result<Vec<Post>> {
    let result = if let Some(ts) = before {
        db.prepare(format!(
            "SELECT {POST_COLS} FROM posts
             WHERE parent_id IS NULL AND created_at < ?1
             ORDER BY created_at DESC LIMIT ?2"
        ))
        .bind(&[
            JsValue::from_f64(ts as f64),
            JsValue::from_f64(limit as f64),
        ])?
        .all()
        .await?
    } else {
        db.prepare(format!(
            "SELECT {POST_COLS} FROM posts
             WHERE parent_id IS NULL
             ORDER BY created_at DESC LIMIT ?1"
        ))
        .bind(&[JsValue::from_f64(limit as f64)])?
        .all()
        .await?
    };
    Ok(result
        .results::<PostRow>()?
        .into_iter()
        .map(Post::from)
        .collect())
}

async fn list_all_posts(db: &D1Database, limit: i64) -> Result<Vec<Post>> {
    let result = db
        .prepare(format!(
            "SELECT {POST_COLS} FROM posts ORDER BY created_at DESC LIMIT ?1"
        ))
        .bind(&[JsValue::from_f64(limit as f64)])?
        .all()
        .await?;
    Ok(result
        .results::<PostRow>()?
        .into_iter()
        .map(Post::from)
        .collect())
}

async fn get_post(db: &D1Database, id: i64) -> Result<Option<Post>> {
    let row = db
        .prepare(format!("SELECT {POST_COLS} FROM posts WHERE id = ?1"))
        .bind(&[JsValue::from_f64(id as f64)])?
        .first::<PostRow>(None)
        .await?;
    Ok(row.map(Post::from))
}

struct Thread {
    head: Post,
    posts: Vec<Post>,
}

async fn get_thread(db: &D1Database, id: i64) -> Result<Option<Thread>> {
    let head = db
        .prepare(format!(
            "WITH RECURSIVE up AS (
               SELECT {POST_COLS} FROM posts WHERE id = ?1
               UNION ALL
               SELECT p.id, p.body, p.created_at, p.parent_id
                 FROM posts p JOIN up u ON p.id = u.parent_id
             )
             SELECT * FROM up WHERE parent_id IS NULL LIMIT 1"
        ))
        .bind(&[JsValue::from_f64(id as f64)])?
        .first::<PostRow>(None)
        .await?;
    let Some(head) = head.map(Post::from) else {
        return Ok(None);
    };
    let result = db
        .prepare(format!(
            "WITH RECURSIVE thread AS (
               SELECT {POST_COLS} FROM posts WHERE id = ?1
               UNION ALL
               SELECT p.id, p.body, p.created_at, p.parent_id
                 FROM posts p JOIN thread t ON p.parent_id = t.id
             )
             SELECT * FROM thread ORDER BY created_at ASC"
        ))
        .bind(&[JsValue::from_f64(head.id as f64)])?
        .all()
        .await?;
    Ok(Some(Thread {
        head,
        posts: result
            .results::<PostRow>()?
            .into_iter()
            .map(Post::from)
            .collect(),
    }))
}

async fn total_replies_by_head(db: &D1Database, head_ids: &[i64]) -> Result<Vec<(i64, i64)>> {
    let mut out: Vec<(i64, i64)> = head_ids.iter().map(|id| (*id, 0)).collect();
    if head_ids.is_empty() {
        return Ok(out);
    }
    let placeholders = (1..=head_ids.len())
        .map(|i| format!("?{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let binds: Vec<JsValue> = head_ids
        .iter()
        .map(|id| JsValue::from_f64(*id as f64))
        .collect();
    let result = db
        .prepare(format!(
            "WITH RECURSIVE chain(id, head) AS (
               SELECT id, id FROM posts WHERE id IN ({placeholders})
               UNION ALL
               SELECT p.id, c.head FROM posts p JOIN chain c ON p.parent_id = c.id
             )
             SELECT head, COUNT(*) - 1 AS reply_count FROM chain GROUP BY head"
        ))
        .bind(&binds)?
        .all()
        .await?;
    for row in result.results::<ReplyRow>()? {
        if let Some(slot) = out.iter_mut().find(|(id, _)| *id == row.head) {
            slot.1 = row.reply_count;
        }
    }
    Ok(out)
}

async fn images_for_posts(db: &D1Database, post_ids: &[i64]) -> Result<Vec<(i64, Vec<PostImage>)>> {
    let mut grouped: Vec<(i64, Vec<PostImage>)> =
        post_ids.iter().map(|id| (*id, Vec::new())).collect();
    if post_ids.is_empty() {
        return Ok(grouped);
    }
    let placeholders = (1..=post_ids.len())
        .map(|i| format!("?{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let binds: Vec<JsValue> = post_ids
        .iter()
        .map(|id| JsValue::from_f64(*id as f64))
        .collect();
    let result = db
        .prepare(format!(
            "SELECT id, post_id, r2_key, content_type, width, height, alt, ordinal
               FROM post_images
              WHERE post_id IN ({placeholders})
              ORDER BY post_id, ordinal"
        ))
        .bind(&binds)?
        .all()
        .await?;
    for row in result.results::<ImageRow>()? {
        if let Some((_, slot)) = grouped.iter_mut().find(|(id, _)| *id == row.post_id) {
            slot.push(PostImage {
                id: row.id,
                post_id: row.post_id,
                r2_key: row.r2_key,
                content_type: row.content_type,
                width: row.width,
                height: row.height,
                alt: row.alt,
                ordinal: row.ordinal,
            });
        }
    }
    Ok(grouped)
}

async fn insert_post(
    db: &D1Database,
    body: &str,
    created_at: i64,
    parent_id: Option<i64>,
    notify_at: i64,
) -> Result<i64> {
    let parent = match parent_id {
        Some(id) => JsValue::from_f64(id as f64),
        None => JsValue::NULL,
    };
    let row = db
        .prepare(
            "INSERT INTO posts (body, created_at, parent_id, notify_at)
             VALUES (?1, ?2, ?3, ?4) RETURNING id",
        )
        .bind(&[
            JsValue::from_str(body),
            JsValue::from_f64(created_at as f64),
            parent,
            JsValue::from_f64(notify_at as f64),
        ])?
        .first::<IdRow>(None)
        .await?
        .ok_or_else(|| worker::Error::RustError("insert post: no id".into()))?;
    policy::js_safe_id(row.id)
        .ok_or_else(|| worker::Error::RustError("insert post: id overflow".into()))
}

async fn insert_post_image(
    db: &D1Database,
    post_id: i64,
    key: &str,
    content_type: &str,
    ordinal: i64,
) -> Result<()> {
    db.prepare(
        "INSERT INTO post_images (post_id, r2_key, content_type, ordinal, alt)
         VALUES (?1, ?2, ?3, ?4, NULL)",
    )
    .bind(&[
        JsValue::from_f64(post_id as f64),
        JsValue::from_str(key),
        JsValue::from_str(content_type),
        JsValue::from_f64(ordinal as f64),
    ])?
    .run()
    .await?;
    Ok(())
}

async fn insert_interested(
    db: &D1Database,
    email: &str,
    created_at: i64,
    token: &str,
) -> Result<()> {
    db.prepare(
        "INSERT INTO subscribers (email, status, token, created_at)
         VALUES (?1, 'pending', ?2, ?3)
         ON CONFLICT(email) DO NOTHING",
    )
    .bind(&[
        JsValue::from_str(email),
        JsValue::from_str(token),
        JsValue::from_f64(created_at as f64),
    ])?
    .run()
    .await?;
    Ok(())
}

async fn count_interested(db: &D1Database) -> Result<i64> {
    let row = db
        .prepare("SELECT COUNT(*) AS n FROM subscribers WHERE status = 'pending'")
        .first::<CountRow>(None)
        .await?;
    Ok(row.map(|r| r.n).unwrap_or(0))
}

#[derive(Deserialize)]
struct RecipientRow {
    email: String,
    token: String,
    status: String,
}

async fn send_due_notifications(env: &Env) -> Result<()> {
    let site = Site::from_env(env)?;
    let from = crate::notify::sanitize_header(site.mail_from.trim());
    if from.is_empty() {
        return Ok(());
    }
    let email = match env.send_email("EMAIL") {
        Ok(e) => e,
        Err(e) => {
            worker::console_error!("notify: EMAIL binding: {e}");
            return Ok(());
        }
    };
    let db = env.d1("DB")?;
    let now = js_now() as i64;
    let posts = due_posts(&db, now).await?;
    if posts.is_empty() {
        return Ok(());
    }
    let recipients = list_recipients(&db).await?;
    for post in posts {
        for recip in &recipients {
            if !crate::notify::should_receive(&recip.status) {
                continue;
            }
            let token = ensure_subscriber_token(&db, &recip.email, &recip.token).await?;
            let to = crate::notify::sanitize_header(&recip.email);
            if to.is_empty() {
                continue;
            }
            let subject = crate::notify::post_subject(&site.title, &post.body);
            let unsub = crate::notify::unsubscribe_url(&site.url, &token);
            let body = crate::notify::post_text(&site.url, post.id, &post.body, &unsub);
            let msg = SendEmailBuilder::builder(&from, &to, &subject)
                .text(&body)
                .build();
            if let Err(e) = email.send_with_builder(&msg).await {
                worker::console_error!("notify: send {}: {:?}", recip.email, e);
            }
        }
        mark_notified(&db, post.id, now).await?;
    }
    Ok(())
}

async fn due_posts(db: &D1Database, now: i64) -> Result<Vec<Post>> {
    let result = db
        .prepare(format!(
            "SELECT {POST_COLS} FROM posts
              WHERE notify_at IS NOT NULL
                AND notified_at IS NULL
                AND notify_at <= ?1
              ORDER BY notify_at ASC"
        ))
        .bind(&[JsValue::from_f64(now as f64)])?
        .all()
        .await?;
    Ok(result
        .results::<PostRow>()?
        .into_iter()
        .map(Post::from)
        .collect())
}

async fn list_recipients(db: &D1Database) -> Result<Vec<RecipientRow>> {
    let result = db
        .prepare("SELECT email, token, status FROM subscribers ORDER BY id")
        .all()
        .await?;
    result.results::<RecipientRow>()
}

async fn ensure_subscriber_token(db: &D1Database, email: &str, token: &str) -> Result<String> {
    if !token.is_empty() {
        return Ok(token.to_string());
    }
    let token = crate::notify::new_subscriber_token();
    db.prepare("UPDATE subscribers SET token = ?1 WHERE email = ?2 AND token = ''")
        .bind(&[JsValue::from_str(&token), JsValue::from_str(email)])?
        .run()
        .await?;
    Ok(token)
}

async fn mark_notified(db: &D1Database, id: i64, now: i64) -> Result<()> {
    db.prepare("UPDATE posts SET notified_at = ?1 WHERE id = ?2 AND notified_at IS NULL")
        .bind(&[JsValue::from_f64(now as f64), JsValue::from_f64(id as f64)])?
        .run()
        .await?;
    Ok(())
}

async fn subscriber_token_exists(db: &D1Database, token: &str) -> Result<bool> {
    let row = db
        .prepare("SELECT COUNT(*) AS n FROM subscribers WHERE token = ?1 AND token != ''")
        .bind(&[JsValue::from_str(token)])?
        .first::<CountRow>(None)
        .await?;
    Ok(row.map(|r| r.n).unwrap_or(0) > 0)
}

async fn unsubscribe_by_token(db: &D1Database, token: &str) -> Result<bool> {
    let result = db
        .prepare("UPDATE subscribers SET status = 'unsubscribed' WHERE token = ?1 AND token != ''")
        .bind(&[JsValue::from_str(token)])?
        .run()
        .await?;
    Ok(result.meta()?.and_then(|m| m.changes).unwrap_or(0) > 0)
}

async fn count_credentials(db: &D1Database) -> Result<i64> {
    let row = db
        .prepare("SELECT COUNT(*) AS n FROM credentials")
        .first::<CountRow>(None)
        .await?;
    Ok(row.map(|r| r.n).unwrap_or(0))
}

fn cred_from_row(row: CredRow) -> Result<Credential> {
    let public_key = hex::decode(&row.public_key_hex)
        .map_err(|e| worker::Error::RustError(format!("credential blob: {e}")))?;
    let counter = policy::counter_from_i64(row.counter).map_err(worker::Error::RustError)?;
    Ok(Credential {
        id: row.credential_id,
        public_key,
        counter,
        transports: row.transports,
    })
}

async fn list_credential_rows(db: &D1Database) -> Result<Vec<(i64, String, i64)>> {
    let result = db
        .prepare(
            "SELECT id, credential_id, hex(public_key) as public_key_hex, counter, transports, label, created_at
             FROM credentials ORDER BY created_at",
        )
        .all()
        .await?;
    Ok(result
        .results::<CredRow>()?
        .into_iter()
        .map(|r| (r.id, r.label, r.created_at))
        .collect())
}

async fn list_credentials(db: &D1Database) -> Result<Vec<Credential>> {
    let result = db
        .prepare(
            "SELECT id, credential_id, hex(public_key) as public_key_hex, counter, transports, label, created_at
             FROM credentials ORDER BY created_at",
        )
        .all()
        .await?;
    result
        .results::<CredRow>()?
        .into_iter()
        .map(cred_from_row)
        .collect()
}

async fn find_credential(db: &D1Database, credential_id: &str) -> Result<Option<Credential>> {
    let row = db
        .prepare(
            "SELECT id, credential_id, hex(public_key) as public_key_hex, counter, transports, label, created_at
             FROM credentials WHERE credential_id = ?1",
        )
        .bind(&[JsValue::from_str(credential_id)])?
        .first::<CredRow>(None)
        .await?;
    match row {
        Some(r) => Ok(Some(cred_from_row(r)?)),
        None => Ok(None),
    }
}

async fn insert_credential(
    db: &D1Database,
    credential_id: &str,
    public_key: &[u8],
    counter: u32,
    transports: Option<String>,
    label: &str,
    created_at: i64,
) -> Result<()> {
    let array = worker::js_sys::Uint8Array::new_with_length(public_key.len() as u32);
    array.copy_from(public_key);
    let transports = match &transports {
        Some(s) => JsValue::from_str(s),
        None => JsValue::NULL,
    };
    db.prepare(
        "INSERT INTO credentials (credential_id, public_key, counter, transports, label, created_at)
         VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
    )
    .bind(&[
        JsValue::from_str(credential_id),
        array.into(),
        JsValue::from_f64(f64::from(counter)),
        transports,
        JsValue::from_str(label),
        JsValue::from_f64(created_at as f64),
    ])?
    .run()
    .await?;
    Ok(())
}

async fn update_counter(db: &D1Database, credential_id: &str, counter: u32) -> Result<bool> {
    let row = db
        .prepare(
            "UPDATE credentials SET counter = ?1
              WHERE credential_id = ?2 AND (counter = 0 OR counter < ?1)
              RETURNING id",
        )
        .bind(&[
            JsValue::from_f64(f64::from(counter)),
            JsValue::from_str(credential_id),
        ])?
        .first::<IdRow>(None)
        .await?;
    Ok(row.is_some())
}

async fn delete_credential(db: &D1Database, id: i64) -> Result<()> {
    db.prepare("DELETE FROM credentials WHERE id = ?1")
        .bind(&[JsValue::from_f64(id as f64)])?
        .run()
        .await?;
    Ok(())
}

async fn consume_challenge(db: &D1Database, challenge: &str, now: u64) -> Result<bool> {
    let cutoff = now.saturating_sub(crate::auth::CHALLENGE_TTL);
    db.prepare("DELETE FROM webauthn_used_challenges WHERE used_at < ?1")
        .bind(&[JsValue::from_f64(cutoff as f64)])?
        .run()
        .await?;
    let row = db
        .prepare(
            "INSERT INTO webauthn_used_challenges (challenge, used_at) VALUES (?1, ?2)
             ON CONFLICT(challenge) DO NOTHING
             RETURNING challenge",
        )
        .bind(&[JsValue::from_str(challenge), JsValue::from_f64(now as f64)])?
        .first::<ChallengeClaimRow>(None)
        .await?;
    let claimed = row.is_some_and(|r| r.challenge == challenge);
    Ok(policy::challenge_consumed(claimed as i64))
}

async fn rate_prune(db: &D1Database, key: &str, cutoff: u64) -> Result<()> {
    db.prepare("DELETE FROM rate_limits WHERE key = ?1 AND ts < ?2")
        .bind(&[JsValue::from_str(key), JsValue::from_f64(cutoff as f64)])?
        .run()
        .await?;
    Ok(())
}

async fn rate_count(db: &D1Database, key: &str, cutoff: u64) -> Result<i64> {
    let row = db
        .prepare("SELECT COUNT(*) AS n FROM rate_limits WHERE key = ?1 AND ts >= ?2")
        .bind(&[JsValue::from_str(key), JsValue::from_f64(cutoff as f64)])?
        .first::<CountRow>(None)
        .await?;
    Ok(row.map(|r| r.n).unwrap_or(0))
}

async fn rate_record(db: &D1Database, key: &str, now: u64) -> Result<()> {
    db.prepare("INSERT INTO rate_limits (key, ts) VALUES (?1, ?2)")
        .bind(&[JsValue::from_str(key), JsValue::from_f64(now as f64)])?
        .run()
        .await?;
    Ok(())
}

async fn rate_exceeded(
    db: &D1Database,
    key: &str,
    now: u64,
    window: u64,
    max: i64,
) -> Result<bool> {
    let cutoff = now.saturating_sub(window);
    rate_prune(db, key, cutoff).await?;
    let n = rate_count(db, key, cutoff).await?;
    Ok(policy::rate_limit_exceeded(n, max))
}

async fn rate_allow(db: &D1Database, key: &str, now: u64, window: u64, max: i64) -> Result<bool> {
    if rate_exceeded(db, key, now, window, max).await? {
        return Ok(false);
    }
    rate_record(db, key, now).await?;
    Ok(true)
}
